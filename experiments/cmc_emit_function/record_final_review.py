"""Record the completed review against final controller-accepted bytes."""
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
 'cm_function_slots_size_snoc__param_transition': 'Induction over prefix proves additive size of prefix++[h], unconditionally; no prefix wf is assumed.',
 'cm_function_slots_prefix_app__param_emission': 'Induction over prefix, Zlength nonnegativity and the zero/nonzero index branches prove that indexing prefix++rest at its prefix length yields prefix size; no additional input restriction.',
 'cm_function_param_count_length__prologue_layout': 'List induction and scalar-type cases prove length <= parameter store count unconditionally; each element contributes nonnegative normalization count plus five.'
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
proofs = [r for r in coq_regions(manual_path.read_text()) if 'ending' in r]
assert len(proofs) == 125 and all(r['ending'] == 'Qed' for r in proofs)
review.update(status='passed', new_helper_review=helpers,
 model_review='Three exact emission definitions and two total head/tail observations retain their annotation-stage reviewed bytes.',
 manual_review='Reviewed all final proof regions: parameter arithmetic and observations, list/function resources, opcode computation, code concatenation, and function bounds. All 125 proof regions end in Qed, covering 41 original top-level obligations and 84 splits. Controller checks unchanged statements, routes, helper/import safety and full goal-check.',
 support_mapping={
  'prefix offset and snoc extension': 'Two unconditional list induction helpers, with original full/prefix/slot equations.',
  'parameter length bound': 'New unconditional length/count helper plus original representable count condition.',
  'semantic/encoded size agreement and nonnegativity': 'Reused verified size matching/nonnegative lemmas; indexed slots wf supplies required head/tail facts.',
  'parameter observations': 'Transparent head/tail computation and original cons shape, preserving all pure conditions.',
  'slot and function resources': 'Existing representations, null/cons reasoning and explicit resource opening/folding.',
  'emission order and sequence boundaries': 'Exact new models and append associativity, preserving arbitrary done/tail.',
  'integer, temporary-slot and PC bounds': 'Original bounds and reused nonnegative/length/count facts, checked arithmetic.'
 },
 scope='Three runtime BODY contracts and necessary function proof support; no new TVM execution, termination, linking or compilation-preservation theorem.')
review_path.write_text(json.dumps(review, indent=2)+'\n')
semantic.update(status='passed', final_library_review='final-library-review.json',
                final_model_hashes_unchanged=True, new_assumptions=False)
semantic_path.write_text(json.dumps(semantic, indent=2)+'\n')
print('Final semantic review recorded against accepted hashes.')
