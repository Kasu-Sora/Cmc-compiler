"""Bind the completed semantic review to the controller-accepted artifacts."""
from pathlib import Path
import hashlib, json
from audit_syntax import coq_regions

R = Path(__file__).resolve().parent
Q = Path('/Users/nizitong/QCP/qcp-binary-democases')
run = json.loads((R/'metrics/run.json').read_text())['run_id']
state = json.loads((Q/'reports'/run/'controller_state.json').read_text())
assert state['phase'] == 'done' and state['final_check']['status'] == 'passed'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
libpath = Q/state['target_files']['formal_case_lib']
manualpath = Q/state['target_files']['proof_manual_file']
path = R/'metrics/final-library-review.json'
review = json.loads(path.read_text())
assert review['lib_sha256'] == sha(libpath)
assert review['manual_sha256'] == sha(manualpath)
lib = libpath.read_text()
regions = coq_regions(lib)
helpers = {r['name']: r for r in regions if r['kind'] in ['Lemma', 'Theorem', 'Corollary']}
descriptions = {
    'cm_patch_arrays_open__array_open': 'Unconditional resource entailment opens a cons instruction into int opcode and int64 immediate cells plus the exact correlated tails. Uses standard full_unfold/seg_to_full with sizeof(INT) and sizeof(INT64), preserving arbitrary base addresses and adding no pure premise.',
    'cm_patch_arrays_cons__array_close': 'Reverse unconditional resource entailment joins the two head cells and shifted correlated tails into complete arrays for the cons instruction. Uses full_unfold/seg_0_shift and explicit resource cancellation; no program, validity, nonnull or numeric-range premise added.'
}
assert set(helpers) == set(descriptions)
assert all(r['ending'] == 'Qed' for r in helpers.values())
proofs = [r for r in coq_regions(manualpath.read_text()) if 'ending' in r]
assert len(proofs) == 10 and all(r['ending'] == 'Qed' for r in proofs)
sp = R/'metrics/semantic-audit.json'
semantic = json.loads(sp.read_text())
for x in semantic['annotation_stage_model_declarations']:
    region = next(r for r in regions if r.get('name') == x['name'])
    assert hashlib.sha256(lib[region['start']:region['end']].encode()).hexdigest() == x['sha256']
review.update(
    status='passed',
    new_helper_review={name: dict(review=description, sha256=hashlib.sha256(lib[helpers[name]['start']:helpers[name]['end']].encode()).hexdigest()) for name, description in descriptions.items()},
    model_review='Both annotation-stage transparent definitions retain their audited bytes: total tl and exactly IntArray.full ** Int64Array.full. Existing patch and resolved-emitter models remain unchanged.',
    manual_review='Reviewed all 10 final proof regions: empty/nonempty split, CALL and non-CALL recursive reconstruction, resolved-view opening, physical emitter restoration and four parent routes. All regions end in Qed. Controller separately verified original statements, routes, imports, annotation seal and complete goal-check.',
    proof_regions=len(proofs),
    support_mapping={
        'empty arrays': 'Zero length forces raw=nil; patch nil is definitional. No nonnull precondition is introduced.',
        'array opening': 'Positive length rules out nil; destructed instruction gives exact head projections and total tail. New opening helper uses the respective 4/8-byte widths.',
        'recursive returns': 'Existing cm_patch_code_length preserves tail length. Opcode equality/inequality selects the existing cm_patch_inst branch. CALL writes the previously verified total PC result, without restricting arbitrary signed64 target; the new cons helper recombines both resources.',
        'wrapper opening': 'Unfolds existential raw, retains patch raw=resolved, derives the signed32 capacity bound from its owned int cell using store_int_range, and rebases segments at zero. Projection lengths are proved locally by list induction.',
        'wrapper closing': 'Uses patch length and projection lengths to restore original pc, fields, capacity and undef suffixes. Does not assume raw=resolved or patch idempotence.',
        'program ownership': 'Original wf/code-ready, complete program context and full function-list ownership are framed throughout; no weaker postcondition or extra input requirement.'
    },
    scope='Two concrete CALL-patching implementation bodies with the established policy/cg parameterization; no new compiler preservation or TVM execution/termination theorem.'
)
path.write_text(json.dumps(review, indent=2)+'\n')
semantic.update(status='passed', final_library_review='final-library-review.json', final_model_hashes_unchanged=True, new_assumptions=False)
sp.write_text(json.dumps(semantic, indent=2)+'\n')
print('Final semantic review recorded against accepted artifact hashes.')
