"""Record the reviewed original contract and exact reused helper/model identities."""
from pathlib import Path
import hashlib,json,re
from audit_syntax import c_functions,coq_regions,line_span
R=Path(__file__).resolve().parent
Q=Path('/Users/nizitong/QCP/qcp-binary-democases')
c=(Q/'QCP_examples/QCP_demos_human/cmc_emit_return_migration.c').read_text()
lib=(Q/'Rocq/examples/QCP_demos_human/cmc_emit_return_migration_lib.v').read_text()
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
norm=lambda s:re.sub(r'\s+','',s)
def contract(text,name,prototype):
 f=next(f for f in c_functions(text) if f['name']==name and f['prototype']==prototype)
 return '\n'.join(re.findall(r'/\*@.*?\*/',text[f['start']:f['body_start']],re.S))
body=contract(c,'cm_emit_return_epilogue_plan',False)
expected='''/*@ With (policy : cm_lookup_policy) (p : cm_program) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
Require cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_return_epilogue, tail))
Ensure cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_return_epilogue), tail)
*/'''
assert norm(body)==norm(expected),'Return contract drift'
helper=contract(c,'cm_emit_plan',True)
previous=contract((R/'baseline/reused/cmc_emit_plan_migration.c').read_text(),'cm_emit_plan',False)
assert norm(helper)==norm(previous),'Verified helper contract mismatch'
models=[]
for x in coq_regions(lib):
 if x['kind'] not in ['Definition','Fixpoint','Inductive','Record']:continue
 frag=lib[x['start']:x['end']]
 models.append(dict(name=x['name'],kind=x['kind'],span=line_span(lib,x['start'],x['end']),sha256=sha(frag),nonblank_lines=sum(bool(l.strip()) for l in frag.splitlines())))
assert [x['name'] for x in models]==['cm_return_epilogue']
expected_code=[('TVMPushOp','8'),('TVMLoadOp','0'),('TVMLoadOp','0'),('TVMPushOp','8'),('TVMStoreOp','0'),('TVMRetOp','0')]
assert re.findall(r'TVMInst\s+(\w+)\s+(\d+)',lib)==expected_code
source=(R/'baseline/cmc_codegen.c').read_text()
fragment=re.search(r'PROOF thm cm_return_epilogue_def =.*?`\);',source,re.S).group()
assert re.findall(r'TVMInst\s+(\w+)\s+(\d+)i',fragment)==expected_code
helper_row=dict(function='cm_emit_plan',target_contract_sha256=sha(helper),previous_body_contract_sha256=sha(previous),whitespace_normalized_identical=True,semantic_audit='passed')
(R/'metrics/helper-contract-audit.json').write_text(json.dumps([helper_row],indent=2)+'\n')
(R/'metrics/annotation-library-baseline.json').write_text(json.dumps(models,indent=2)+'\n')
audit=dict(status='contract/model semantic review passed; final proof pending',contracts=[dict(function='cm_emit_return_epilogue_plan',target_contract_sha256=sha(body),status='reviewed',review='Same arbitrary p/done/tail/out/capacity plan-to-plan contract; existing arbitrary policy parameter preserved. No additional pure preconditions; exact six-instruction output suffix and arbitrary tail retained.')],annotation_stage_model_declarations=models,additional_input_restrictions=False,source_to_target_meta_equivalence_theorem=False,model_review='Exact ordered six TVMInst constructors and immediates match the HOL definition; existing plan and resolved emitter models imported unchanged. This verifies emission, not execution of RET.')
(R/'metrics/semantic-audit.json').write_text(json.dumps(audit,indent=2)+'\n')
print('Reviewed original contract, reused BODY contract, and exact six-instruction model.')
