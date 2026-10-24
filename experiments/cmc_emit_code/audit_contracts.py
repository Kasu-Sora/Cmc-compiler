"""Independent source-contract mapping and model identity audit."""
from pathlib import Path
import hashlib,json,re
from audit_syntax import c_functions,coq_regions,line_span,coq_mask
R=Path(__file__).resolve().parent;Q=Path('/Users/nizitong/QCP/qcp-binary-democases')
c=(Q/'QCP_examples/QCP_demos_human/cmc_emit_code_migration.c').read_text();lib=(Q/'Rocq/examples/QCP_demos_human/cmc_emit_code_migration_lib.v').read_text()
sha=lambda s:hashlib.sha256(s.encode()).hexdigest();norm=lambda s:re.sub(r'\s+','',s)
f=next(f for f in c_functions(c) if not f['prototype']);body='\n'.join(re.findall(r'/\*@.*?\*/',c[f['start']:f['body_start']],re.S))
withs='(policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (functions_ptr : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)'
facts='cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && cm_concrete_functions_ready(policy, p, 0, cm_program_functions(p)) && cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) && cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560'
resources='cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(functions_ptr, cm_program_functions(p))';code='cm_model_code(policy, p)'
expected=f'/*@ With {withs} Require {facts} && {resources} * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app({code}, tail)) Ensure {facts} && {resources} * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, {code}), tail) */'
assert norm(body)==norm(expected),'Original BODY contract mapping drift'
source=(R/'baseline/cmc_concrete_emit_code.c').read_text();ls=source.splitlines();sf=next(x for x in json.loads((R/'metrics/source-functions.json').read_text()) if not x['prototype'])
ss='\n'.join(ls[i-1] for a,b in sf['specification'] for i in range(a,b+1));decl=[]
for x in coq_regions(lib):
 frag=lib[x['start']:x['end']];decl.append(dict(name=x.get('name'),kind=x['kind'],span=line_span(lib,x['start'],x['end']),sha256=sha(frag),nonblank_lines=sum(bool(l.strip())for l in coq_mask(frag).splitlines())))
models=[x for x in decl if x['kind'] in ['Definition','Fixpoint','Inductive','Record']]
assert {x['name']for x in models}=={'cm_model_code'}
mr=next(x for x in coq_regions(lib) if x.get('name')=='cm_model_code')
expected_model='Definition cm_model_code (policy : cm_lookup_policy) (p : cm_program) : list tvm_inst := cm_emit_prelude policy p ++ cm_emit_functions policy p 0 (cm_program_functions p).'
assert norm(coq_mask(lib[mr['start']:mr['end']]))==norm(expected_model),'Output model drift'
(R/'metrics/annotation-library-baseline.json').write_text(json.dumps(decl,indent=2)+'\n')
audit=dict(status='contract mapping reviewed; final model/proof review pending',contracts=[dict(function=f['name'],target_contract_sha256=sha(body),source_contract_sha256=sha(ss),status='reviewed',review='All original wf/typed/readiness/representation/size facts, full program context and program function-list resources preserved in pre/post. Exact complete code appended to arbitrary done, tail retained; no new precondition, existing policy/cg parameters unchanged.')],annotation_stage_model_declarations=models,annotation_stage_model_review={'cm_model_code':'Exact source composition: prelude followed by all program functions emitted from fid zero.'},additional_input_restrictions=False,source_to_target_meta_equivalence_theorem=False,source_model='baseline/cmc_codegen.c:1043',model_review='Precise prelude/functions composition; PC-zero must be proved internally, not added as caller assumption. Final merged proofs and any new helper require review.')
(R/'metrics/semantic-audit.json').write_text(json.dumps(audit,indent=2)+'\n');print('Original BODY contract and complete code model reviewed.')
