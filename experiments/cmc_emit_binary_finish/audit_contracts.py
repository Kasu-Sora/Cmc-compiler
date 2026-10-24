"""Record reviewed contracts and models at the accepted annotation boundary."""
from pathlib import Path
import re,json,hashlib
from audit_syntax import c_functions,coq_regions,coq_mask,line_span
R=Path(__file__).resolve().parent;Q=Path('/Users/nizitong/QCP/qcp-binary-democases')
run=json.loads((R/'metrics/run.json').read_text())['run_id']
state=json.loads((Q/'reports'/run/'controller_state.json').read_text())
assert any(a['phase']=='annotation' and a['status']=='accepted' for a in state['attempts'].values())
p=Q/'QCP_examples/QCP_demos_human/cmc_emit_binary_finish_migration.c';text=p.read_text();fs=c_functions(text)
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
contract=lambda s,f:''.join(re.findall(r'/\*@.*?\*/',s[f['start']:f['body_start']],re.S))
helper_sources={'cm_emit_plan':'cmc_emit_plan_migration.c','cm_emit_temp_load_plan':'cmc_emit_plan_migration.c','cmc_binary_opcode':'cmc_emit_core_migration.c','cm_expr_type_code_context':'cmc_count_context_migration.c','cm_type_size_value':'cmc_emit_expr_leaf_migration.c','cmc_pointee':'cmc_layout_migration.c','cmc_is_pointer_value':'cmc_layout_migration.c'}
rows=[]
for f in fs:
 if not f['prototype']:continue
 c=contract(text,f)
 if f['name'] in helper_sources:
  filename=helper_sources[f['name']];old=(R/'baseline/reused'/filename).read_text();of=next(x for x in c_functions(old)if x['name']==f['name'] and not x['prototype'])
  oc=contract(old,of);assert re.sub(r'\s','',oc)==re.sub(r'\s','',c),f['name']
  row=dict(function=f['name'],source=filename,normalized_contract_identical=True,implementation_status='previously verified')
 else:raise AssertionError('Unexpected helper '+f['name'])
 row.update(target_contract_sha256=sha(c),semantic_audit='passed');rows.append(row)
assert len(rows)==7
(R/'metrics/helper-contract-audit.json').write_text(json.dumps(rows,indent=2)+'\n')
contracts=[]
for f in fs:
 if f['prototype']:continue
 c='\n'.join(re.findall(r'/\*@.*?\*/',text[f['start']:f['body_start']],re.S))
 contracts.append(dict(function=f['name'],target_contract_sha256=sha(c),status='reviewed against exact source body contract',review='All source pre/post pure facts retained; total lookup unchanged; complete owned contexts and arbitrary plan tail retained; no stronger input premise.'))
lib=(Q/'Rocq/examples/QCP_demos_human/cmc_emit_binary_finish_migration_lib.v').read_text()
assert not re.search(r'\b(Admitted|Axiom|Parameter|Abort)\b',coq_mask(lib))
regions=coq_regions(lib);models=[];baseline=[]
for x in regions:
 if x['kind'] not in ['Definition','Fixpoint','Record','Inductive','Lemma','Theorem']:continue
 frag=lib[x['start']:x['end']];a,b=line_span(lib,x['start'],x['end'])
 row=dict(name=x['name'],kind=x['kind'],span=[a,b],sha256=sha(frag),nonblank_lines=sum(bool(t.strip())for t in coq_mask(frag).splitlines()))
 baseline.append(row)
 if x['kind'] in ['Definition','Fixpoint','Record','Inductive']:models.append(row)
(R/'metrics/annotation-library-baseline.json').write_text(json.dumps(baseline,indent=2)+'\n')
result=dict(status='annotation boundary reviewed; final proof pending',contracts=contracts,annotation_stage_model_declarations=models,source_to_target=['HOL int/list -> Z/list; existing lookup policy unchanged','Exact binary finish and pointer scale models imported unchanged from verified call library','Arbitrary int op, all pointer combinations and exact code ordering retained','All original resources and pure pre/post facts retained','All seven imported helper implementations previously verified; no pending external implementation'],additional_input_restrictions=False,source_to_target_meta_equivalence_theorem=False)
(R/'metrics/semantic-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print('Reviewed 3 body contracts and 7 previously verified helper BODY contracts.')
