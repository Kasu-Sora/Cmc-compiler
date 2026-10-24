"""Independently compare original BODY semantics and freeze reviewed model."""
from pathlib import Path
import hashlib,json,re
from audit_syntax import c_functions,coq_regions,line_span,coq_mask
R=Path(__file__).resolve().parent;Q=Path('/Users/nizitong/QCP/qcp-binary-democases')
c=(Q/'QCP_examples/QCP_demos_human/cmc_emit_prelude_migration.c').read_text()
lib=(Q/'Rocq/examples/QCP_demos_human/cmc_emit_prelude_migration_lib.v').read_text()
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
norm=lambda s:re.sub(r'\s+','',s)
f=next(f for f in c_functions(c) if not f['prototype'])
body='\n'.join(re.findall(r'/\*@.*?\*/',c[f['start']:f['body_start']],re.S))
expected='''/*@ With (policy : cm_lookup_policy) (p : cm_program) (functions_ptr : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
Require cm_program_context_rep(program, p, functions_ptr) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_emit_prelude(policy, p), tail))
Ensure cm_program_context_rep(program, p, functions_ptr) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_emit_prelude(policy, p)), tail) */'''
assert norm(body)==norm(expected),'Original BODY contract mapping drift'
source=(R/'baseline/cmc_concrete_emit_prelude.c').read_text();ls=source.splitlines()
sf=next(x for x in json.loads((R/'metrics/source-functions.json').read_text()) if not x['prototype'])
ss='\n'.join(ls[i-1] for a,b in sf['specification'] for i in range(a,b+1))
decl=[]
for x in coq_regions(lib):
 frag=lib[x['start']:x['end']]
 decl.append(dict(name=x.get('name'),kind=x['kind'],span=line_span(lib,x['start'],x['end']),sha256=sha(frag),nonblank_lines=sum(bool(l.strip())for l in coq_mask(frag).splitlines())))
models=[x for x in decl if x['kind'] in ['Definition','Fixpoint','Inductive','Record']]
assert {x['name']for x in models}=={'cm_emit_prelude'}
model_region=next(x for x in coq_regions(lib) if x.get('name')=='cm_emit_prelude')
expected_model="""Definition cm_emit_prelude (policy : cm_lookup_policy) (p : cm_program) : list tvm_inst :=
 [TVMInst TVMPushOp 1048576; TVMInst TVMPushOp 8; TVMInst TVMStoreOp 0;
 TVMInst TVMCallOp (cm_function_pc policy p (cm_program_main p));
 TVMInst TVMPushOp 256; TVMInst TVMModOp 0; TVMInst TVMPushOp 256;
 TVMInst TVMAddOp 0; TVMInst TVMPushOp 256; TVMInst TVMModOp 0; TVMInst TVMHaltOp 0]."""
assert norm(coq_mask(lib[model_region['start']:model_region['end']]))==norm(expected_model)

(R/'metrics/annotation-library-baseline.json').write_text(json.dumps(decl,indent=2)+'\n')
audit=dict(status='contract mapping reviewed; final model/proof review pending',contracts=[dict(function=f['name'],target_contract_sha256=sha(body),source_contract_sha256=sha(ss),status='reviewed',review='Only context and emitter-plan resources required and preserved; exact 11-instruction code appended to done, arbitrary tail retained. Arbitrary represented main_id; no wf/typed/readiness/valid-main premise added.')],annotation_stage_model_declarations=models,annotation_stage_model_review={'cm_emit_prelude':'Compared exact 11 instruction source list and unrestricted total CALL lookup; no new assumptions.'},additional_input_restrictions=False,source_to_target_meta_equivalence_theorem=False,source_model='baseline/cmc_codegen.c:1034',model_review='Exact source opcode/immediate order and CALL total lookup; final merged proofs require separate review.')
(R/'metrics/semantic-audit.json').write_text(json.dumps(audit,indent=2)+'\n')
print('Original BODY contract and prelude model reviewed.')
