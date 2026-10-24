"""Freeze independent original-BODY mapping and reviewed model identities."""
from pathlib import Path
import hashlib,json,re
from audit_syntax import c_functions,coq_regions,line_span,coq_mask
R=Path(__file__).resolve().parent;Q=Path('/Users/nizitong/QCP/qcp-binary-democases')
c=(Q/'QCP_examples/QCP_demos_human/cmc_emit_functions_migration.c').read_text()
lib=(Q/'Rocq/examples/QCP_demos_human/cmc_emit_functions_migration_lib.v').read_text()
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
norm=lambda s:re.sub(r'\s+','',s)
specs={'cmc_emit_functions':dict(
 withs='(policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (functions : list cm_function_d) (functions_ptr : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)',
 facts='cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && function_pc == cm_function_pc(policy, p, fid) && cm_concrete_functions_ready(policy, p, fid, functions) && cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) && cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560',
 resources='cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(fn, functions)',
 code='cm_emit_functions(policy, p, fid, functions)')}
rows=[]
source=(R/'baseline/cmc_concrete_emit_functions.c').read_text()
sourcefs=json.loads((R/'metrics/source-functions.json').read_text())
for f in c_functions(c):
 if f['prototype']:continue
 x=specs[f['name']];body='\n'.join(re.findall(r'/\*@.*?\*/',c[f['start']:f['body_start']],re.S))
 expected=f"/*@ With {x['withs']} Require {x['facts']} && {x['resources']} * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app({x['code']}, tail)) Ensure {x['facts']} && {x['resources']} * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, {x['code']}), tail) */"
 assert norm(body)==norm(expected),'Original BODY contract mapping drift: '+f['name']
 sf=next(x for x in sourcefs if x['name']==f['name']);ls=source.splitlines()
 ss='\n'.join(ls[i-1] for a,b in sf['specification']for i in range(a,b+1))
 rows.append(dict(function=f['name'],target_contract_sha256=sha(body),source_contract_sha256=sha(ss),status='reviewed',review='All original wf/typed/readiness/PC/representation/size facts and program/function-list resources retained in pre/post; exact code output, arbitrary fid including empty-list domain, done/tail and existing policy/cg boundary preserved.'))
assert len(rows)==1
decl=[]
for x in coq_regions(lib):
 frag=lib[x['start']:x['end']]
 decl.append(dict(name=x.get('name'),kind=x['kind'],span=line_span(lib,x['start'],x['end']),sha256=sha(frag),nonblank_lines=sum(bool(l.strip())for l in coq_mask(frag).splitlines())))
models=[x for x in decl if x['kind'] in ['Definition','Fixpoint','Inductive','Record']]
assert {x['name'] for x in models}=={'cm_emit_functions','cm_emit_functions_tail'}
reviews={
 'cm_emit_functions':'Exact source nil/cons equations; head function at current fid, then tail at fid+1. The list element is intentionally unused in the code equation exactly as in the source; readiness ties it to lookup. No added input restriction.',
 'cm_emit_functions_tail':'Transparent total list tail; used only under nonempty list shape during recursion. No heap or operational assumption.'}
(R/'metrics/annotation-library-baseline.json').write_text(json.dumps(decl,indent=2)+'\n')
audit=dict(status='contract mapping reviewed; final model/proof review pending',contracts=rows,annotation_stage_model_declarations=models,annotation_stage_model_review=reviews,additional_input_restrictions=False,source_to_target_meta_equivalence_theorem=False,source_model='baseline/cmc_codegen.c:1023',model_review='Exact recursive emission equation independently compared with source; transparent tail used through constructor facts. Reused readiness normalization uses existing statement length equality. Final merged declarations and proofs require separate review.')
(R/'metrics/semantic-audit.json').write_text(json.dumps(audit,indent=2)+'\n')
print('Original BODY contract and two model declarations reviewed.')
