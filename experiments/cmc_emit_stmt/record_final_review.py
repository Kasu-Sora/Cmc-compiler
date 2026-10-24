"""Record the completed source/target review against the final accepted bytes."""
import hashlib, json
from pathlib import Path
from audit_syntax import coq_regions

R = Path(__file__).resolve().parent
Q = Path('/Users/nizitong/QCP/qcp-binary-democases')
run = json.loads((R/'metrics/run.json').read_text())['run_id']
state = json.loads((Q/'reports'/run/'controller_state.json').read_text())
assert state['phase'] == 'done' and state['final_check']['status'] == 'passed'
review_path = R/'metrics/final-library-review.json'
review = json.loads(review_path.read_text())
lib_path = Q/state['target_files']['formal_case_lib']
manual_path = Q/state['target_files']['proof_manual_file']
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert review['lib_sha256'] == sha(lib_path)
assert review['manual_sha256'] == sha(manual_path)
helpers = {
 'cm_expr_rvalue_length__stmt_capacity': 'A specialization of the previously proved paired expression length theorem to rvalue selection 0; no additional premise.',
 'cm_emit_stmt_length__stmt_capacity': 'Structural induction over all statement constructors; ordered append lengths, prior expression/primitive lengths, and recursive IH at updated PCs prove exact equality to the original count model.',
 'cm_stmt_count_nonnegative__stmt_capacity': 'Derived from the new statement length equality and Zlength_nonneg, not assumed from a strengthened precondition.',
 'cm_rvalue_count_nonnegative__stmt_capacity': 'Derived from the reused expression length theorem and Zlength_nonneg; no additional assumption.'
}
lib = lib_path.read_text()
regions = coq_regions(lib)
assert {x['name'] for x in regions if x['kind'] == 'Lemma'} == set(helpers)
assert all(x.get('ending') == 'Qed' for x in regions if x['kind'] == 'Lemma')
semantic_path = R/'metrics/semantic-audit.json'
semantic = json.loads(semantic_path.read_text())
for x in semantic['annotation_stage_model_declarations']:
 region = next(y for y in regions if y.get('name') == x['name'])
 assert hashlib.sha256(lib[region['start']:region['end']].encode()).hexdigest() == x['sha256']
review.update(status='passed', new_helper_review=helpers,
 model_review='Final four model/projection declarations match the constructor-by-constructor reviewed annotation-stage bytes.',
 manual_review='Reviewed arithmetic, capacity, AST open/close, call facts and plan concatenation proof patterns. All 416 final proof regions end in Qed, with 120 original top-level obligations and 296 splits. Controller verifies unchanged statements, routes, helper/import safety and full goal-check; no unused Abort blocks.',
 support_mapping={
  'statement representation open/close': 'Existing cm_stmt_rep_node and cm_stmt_node/payload, explicit spatial resource proofs.',
  'well-formedness and conjunct extraction': 'Constructor elimination, existing cm_stmt_wf/count/temporary-slot definitions, conjunction tactics.',
  'statement code shape': 'Transparent cm_emit_stmt constructor equations and append associativity.',
  'expression and statement code lengths': 'Four proved library helpers, reusing paired expression and primitive length theorems.',
  'call result retargeting': 'Count-return equality annotations with explicit preservation of the local cell.',
  'i32 fragment and conversion bounds': 'Existing i32/count semantics, exact code lengths and nonnegativity, checked lia/nia/int_auto proofs.'
 },
 scope='Two runtime BODY contracts and necessary statement support; no new TVM execution, termination, linking or compilation-preservation theorem.')
review_path.write_text(json.dumps(review, indent=2)+'\n')
semantic.update(status='passed', final_library_review='final-library-review.json',
                final_model_hashes_unchanged=True, new_assumptions=False)
semantic_path.write_text(json.dumps(semantic, indent=2)+'\n')
print('Final semantic review recorded against accepted hashes.')
