"""Record reviewed contracts and models at the accepted annotation boundary."""
from pathlib import Path
import re,json,hashlib
from audit_syntax import c_functions,coq_regions,coq_mask,line_span
R=Path(__file__).resolve().parent;Q=Path('/Users/nizitong/QCP/qcp-binary-democases')
run=json.loads((R/'metrics/run.json').read_text())['run_id']
state=json.loads((Q/'reports'/run/'controller_state.json').read_text())
assert any(a['phase']=='annotation' and a['status']=='accepted' for a in state['attempts'].values())
p=Q/'QCP_examples/QCP_demos_human/cmc_emit_expr_migration.c';text=p.read_text();fs=c_functions(text)
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
contract=lambda s,f:''.join(re.findall(r'/\*@.*?\*/',s[f['start']:f['body_start']],re.S))
helper_sources={'cm_emit_binary_finish_plan': 'cmc_emit_binary_finish_migration.c', 'cm_emit_call_expr': 'cmc_emit_expr_call_migration.c', 'cm_emit_load_plan': 'cmc_emit_plan_migration.c', 'cm_emit_normalize_plan': 'cmc_emit_plan_migration.c', 'cm_emit_plan': 'cmc_emit_plan_migration.c', 'cm_emit_simple_expr': 'cmc_emit_expr_simple_migration.c', 'cm_emit_store_plan': 'cmc_emit_plan_migration.c', 'cm_emit_temp_load_plan': 'cmc_emit_plan_migration.c', 'cm_emit_temp_store_plan': 'cmc_emit_plan_migration.c', 'cm_expr_lvalue_count_context': 'cmc_count_context_migration.c', 'cm_expr_rvalue_count_context': 'cmc_count_context_migration.c', 'cm_expr_type_code_context': 'cmc_count_context_migration.c', 'cm_member_array_value_context': 'cmc_emit_expr_leaf_migration.c', 'cm_member_offset_value_context': 'cmc_emit_expr_leaf_migration.c', 'cm_type_size_value': 'cmc_emit_expr_leaf_migration.c'}
local_names={x['name'] for x in json.loads((R/'metrics/source-functions.json').read_text())}
rows=[]
for f in fs:
 if not f['prototype']:continue
 c=contract(text,f)
 if f['name'] in local_names:
  body=next(x for x in fs if x['name']==f['name'] and not x['prototype'])
  assert re.sub(r'\s','',c)==re.sub(r'\s','',contract(text,body)),f['name']
  continue
 if f['name'] in helper_sources:
  filename=helper_sources[f['name']];old=(R/'baseline/reused'/filename).read_text();of=next(x for x in c_functions(old)if x['name']==f['name'] and not x['prototype'])
  oc=contract(old,of);assert re.sub(r'\s','',oc)==re.sub(r'\s','',c),f['name']
  row=dict(function=f['name'],source=filename,normalized_contract_identical=True,implementation_status='previously verified')
 else:raise AssertionError('Unexpected helper '+f['name'])
 row.update(target_contract_sha256=sha(c),semantic_audit='passed');rows.append(row)
assert len(rows)==15
(R/'metrics/helper-contract-audit.json').write_text(json.dumps(rows,indent=2)+'\n')

# Close the exact external cm_emit_expr assumption used by the accepted call unit.
call_source=(R/'baseline/reused/cmc_emit_expr_call_migration.c').read_text()
call_decl=next(f for f in c_functions(call_source) if f['name']=='cm_emit_expr' and f['prototype'])
expr_body=next(f for f in fs if f['name']=='cm_emit_expr' and not f['prototype'])
assumed=contract(call_source,call_decl);implemented=contract(text,expr_body)
assert re.sub(r'\s','',assumed)==re.sub(r'\s','',implemented), 'Recursive boundary contract drift'
(R/'metrics/recursive-contract-link.json').write_text(json.dumps(dict(status='passed',previous_call_assumption_contract_sha256=sha(assumed),current_expr_body_contract_sha256=sha(implemented),whitespace_normalized_contract_identical=True,scope='Exact modular contract match; runtime bodies independently verified; no separate termination or module-linking metatheorem'),indent=2)+'\n')

# All static helpers add only their source constructor/classifier condition to the common BODY contract.
norm=lambda s:re.sub(r'\s','',s)
parts=lambda s:re.search(r'Require(.*?)Ensure(.*?)\*/',s,re.S).groups()
base_parts=tuple(map(norm,parts(implemented)))
shape_prefixes={'cm_emit_expr':'','cm_emit_intrinsic_expr':'cm_intrinsic_expr(e)&&','cm_emit_unary_expr':'e==CMUnaryE(op_,arg_,ty_)&&','cm_emit_index_expr':'e==CMIndexE(left_,right_,ty_)&&','cm_emit_assignment_expr':'e==CMAssignE(left_,right_,ty_)&&','cm_emit_binary_expr':'e==CMBinaryE(op_,left_,right_,ty_)&&','cm_emit_member_expr':'e==CMMemberE(arg_,mid_,ty_)&&'}
for f in fs:
 if f['prototype']:continue
 assert tuple(map(norm,parts(contract(text,f))))==tuple(shape_prefixes[f['name']]+part for part in base_parts),f['name']
contracts=[]
for f in fs:
 if f['prototype']:continue
 c='\n'.join(re.findall(r'/\*@.*?\*/',text[f['start']:f['body_start']],re.S))
 contracts.append(dict(function=f['name'],target_contract_sha256=sha(c),status='reviewed against exact source body contract',review='All source pre/post pure facts retained; total lookup unchanged; complete owned contexts and arbitrary plan tail retained; no stronger input premise.'))
lib=(Q/'Rocq/examples/QCP_demos_human/cmc_emit_expr_migration_lib.v').read_text()
assert not re.search(r'\b(Admitted|Axiom|Parameter|Abort)\b',coq_mask(lib))
regions=coq_regions(lib);models=[];baseline=[]
for x in regions:
 if x['kind'] not in ['Definition','Fixpoint','Record','Inductive','Lemma','Theorem']:continue
 frag=lib[x['start']:x['end']];a,b=line_span(lib,x['start'],x['end'])
 row=dict(name=x['name'],kind=x['kind'],span=[a,b],sha256=sha(frag),nonblank_lines=sum(bool(t.strip())for t in coq_mask(frag).splitlines()))
 baseline.append(row)
 if x['kind'] in ['Definition','Fixpoint','Record','Inductive']:models.append(row)
(R/'metrics/annotation-library-baseline.json').write_text(json.dumps(baseline,indent=2)+'\n')
result=dict(status='annotation boundary reviewed; final proof pending',contracts=contracts,annotation_stage_model_declarations=models,source_to_target=['HOL int/list -> Z/list; existing lookup policy unchanged','General expression code, temporary and count models imported unchanged from verified call library','Seven original constructor-specific domains, lvalue and exact code ordering retained','All original resources and pure pre/post facts retained','All fifteen imported helper implementations previously verified; mutual recursive implementation linkage audited separately'],additional_input_restrictions=False,source_to_target_meta_equivalence_theorem=False)
(R/'metrics/semantic-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print('Reviewed 7 body contracts and 15 previously verified helper BODY contracts.')
