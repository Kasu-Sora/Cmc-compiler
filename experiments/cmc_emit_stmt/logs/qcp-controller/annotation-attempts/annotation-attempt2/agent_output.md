# Annotation retry 2

The six reported final-emitter-folding witnesses were checked against the sealed original goal definitions. Their conclusions allocated stack cells absent from their antecedents. The repair preserves each relevant untouched C parameter as `parameter == parameter@pre` on both sides of the partial annotation.

The first retry symexec revealed that the matching initial code-expansion boundaries had already discarded those cells. Both the six initial expansions and the six final folds now preserve the same parameter bridges. No function specification, runtime body, public model or public lemma changed. No new public dependency cost is introduced in this retry.

## Checks and repair effort

- formal-case-lib-design: 2 calls, 2 passed, 0 failed.
- symexec: 2 calls; first failed (partial-solve resource mismatch at expression final fold), second passed in 33.574 seconds.
- post-lib: 1 call, passed, 0 failed.
- The failure is an annotation resource-flow defect, not a tool failure; no tool-retry rule applies.

## Semantic annotation review

No full ordinary Assert and no branch-control directive introduced. The paired `which implies` boundaries are function-call preparation and output-shape restoration. The added facts are actual unchanged-parameter bridges, not tautological `x == x` placeholders. All source contracts and exact instruction lists retain their original meaning.

## VC comparison

All six expanded goals were inspected. They now contain only emitter-plan resources on both sides; the formerly missing cells remain in the surrounding frame, and their unchanged entry values are universally quantified. Sealed/current top-level Lemma declarations were compared byte-for-byte equal, so the supplied normalized declaration digests are retained. This does not imply expanded goals are unchanged.

### proof_of_cmc_emit_stmt_which_implies_wit_10

- Current VC: proof_of_cmc_emit_stmt_which_implies_wit_10
- Old gap: Final emitter folding required right-only stack cells &break_pc, &continue_pc absent from the antecedent.
- Premises added: break_pc == break_pc@pre is retained on both sides of paired code expansion/folding annotations; continue_pc == continue_pc@pre is retained on both sides of paired code expansion/folding annotations
- Premises removed: none.
- Resources changed: The erroneous right-only &break_pc, &continue_pc stack cells and their existential value witnesses disappear from the local entailment. Matching unchanged cells stay in the surrounding frame; the emitted-plan resource is still transformed exactly.
- Conclusion changed: Same exact final emitter list and arbitrary tail; erroneous fresh-stack-cell existential replaced by captured unchanged entry parameter values.
- Sources of new facts: unchanged parameters from function entry and their preserved local stores; no new assumption.
- Judgement: provable.
- Reason: CMExprS code unfolds to the same emitted fragments. The break_pc, continue_pc values now occur as universally quantified *_pre parameters instead of existentially allocated stack cells. Constructor shape and existing numeric/model equalities still suffice for list association/code-shape equality; no missing heap allocation remains.
- Related VCs: none.
- Declaration digest: sealed/current Lemma declarations compared byte-for-byte equal; supplied normalized statement digest retained. Expanded goal definitions compared separately and changed as described.

### proof_of_cmc_emit_stmt_which_implies_wit_21

- Current VC: proof_of_cmc_emit_stmt_which_implies_wit_21
- Old gap: Final emitter folding required right-only stack cells &break_pc, &continue_pc absent from the antecedent.
- Premises added: break_pc == break_pc@pre is retained on both sides of paired code expansion/folding annotations; continue_pc == continue_pc@pre is retained on both sides of paired code expansion/folding annotations
- Premises removed: none.
- Resources changed: The erroneous right-only &break_pc, &continue_pc stack cells and their existential value witnesses disappear from the local entailment. Matching unchanged cells stay in the surrounding frame; the emitted-plan resource is still transformed exactly.
- Conclusion changed: Same exact final emitter list and arbitrary tail; erroneous fresh-stack-cell existential replaced by captured unchanged entry parameter values.
- Sources of new facts: unchanged parameters from function entry and their preserved local stores; no new assumption.
- Judgement: provable.
- Reason: CMInitS code unfolds to the same emitted fragments. The break_pc, continue_pc values now occur as universally quantified *_pre parameters instead of existentially allocated stack cells. Constructor shape and existing numeric/model equalities still suffice for list association/code-shape equality; no missing heap allocation remains.
- Related VCs: none.
- Declaration digest: sealed/current Lemma declarations compared byte-for-byte equal; supplied normalized statement digest retained. Expanded goal definitions compared separately and changed as described.

### proof_of_cmc_emit_stmt_which_implies_wit_43

- Current VC: proof_of_cmc_emit_stmt_which_implies_wit_43
- Old gap: Final emitter folding required right-only stack cells &break_pc, &continue_pc absent from the antecedent.
- Premises added: break_pc == break_pc@pre is retained on both sides of paired code expansion/folding annotations; continue_pc == continue_pc@pre is retained on both sides of paired code expansion/folding annotations
- Premises removed: none.
- Resources changed: The erroneous right-only &break_pc, &continue_pc stack cells and their existential value witnesses disappear from the local entailment. Matching unchanged cells stay in the surrounding frame; the emitted-plan resource is still transformed exactly.
- Conclusion changed: Same exact final emitter list and arbitrary tail; erroneous fresh-stack-cell existential replaced by captured unchanged entry parameter values.
- Sources of new facts: unchanged parameters from function entry and their preserved local stores; no new assumption.
- Judgement: provable.
- Reason: CMWhileS code unfolds to the same emitted fragments. The break_pc, continue_pc values now occur as universally quantified *_pre parameters instead of existentially allocated stack cells. Constructor shape and existing numeric/model equalities still suffice for list association/code-shape equality; no missing heap allocation remains.
- Related VCs: none.
- Declaration digest: sealed/current Lemma declarations compared byte-for-byte equal; supplied normalized statement digest retained. Expanded goal definitions compared separately and changed as described.

### proof_of_cmc_emit_stmt_which_implies_wit_48

- Current VC: proof_of_cmc_emit_stmt_which_implies_wit_48
- Old gap: Final emitter folding required right-only stack cells &fid, &pc, &temp, &continue_pc absent from the antecedent.
- Premises added: fid == fid@pre is retained on both sides of paired code expansion/folding annotations; pc == pc@pre is retained on both sides of paired code expansion/folding annotations; temp == temp@pre is retained on both sides of paired code expansion/folding annotations; continue_pc == continue_pc@pre is retained on both sides of paired code expansion/folding annotations
- Premises removed: none.
- Resources changed: The erroneous right-only &fid, &pc, &temp, &continue_pc stack cells and their existential value witnesses disappear from the local entailment. Matching unchanged cells stay in the surrounding frame; the emitted-plan resource is still transformed exactly.
- Conclusion changed: Same exact final emitter list and arbitrary tail; erroneous fresh-stack-cell existential replaced by captured unchanged entry parameter values.
- Sources of new facts: unchanged parameters from function entry and their preserved local stores; no new assumption.
- Judgement: provable.
- Reason: CMBreakS code unfolds to the same emitted fragments. The fid, pc, temp, continue_pc values now occur as universally quantified *_pre parameters instead of existentially allocated stack cells. Constructor shape and existing numeric/model equalities still suffice for list association/code-shape equality; no missing heap allocation remains.
- Related VCs: none.
- Declaration digest: sealed/current Lemma declarations compared byte-for-byte equal; supplied normalized statement digest retained. Expanded goal definitions compared separately and changed as described.

### proof_of_cmc_emit_stmt_which_implies_wit_53

- Current VC: proof_of_cmc_emit_stmt_which_implies_wit_53
- Old gap: Final emitter folding required right-only stack cells &fid, &pc, &temp, &break_pc absent from the antecedent.
- Premises added: fid == fid@pre is retained on both sides of paired code expansion/folding annotations; pc == pc@pre is retained on both sides of paired code expansion/folding annotations; temp == temp@pre is retained on both sides of paired code expansion/folding annotations; break_pc == break_pc@pre is retained on both sides of paired code expansion/folding annotations
- Premises removed: none.
- Resources changed: The erroneous right-only &fid, &pc, &temp, &break_pc stack cells and their existential value witnesses disappear from the local entailment. Matching unchanged cells stay in the surrounding frame; the emitted-plan resource is still transformed exactly.
- Conclusion changed: Same exact final emitter list and arbitrary tail; erroneous fresh-stack-cell existential replaced by captured unchanged entry parameter values.
- Sources of new facts: unchanged parameters from function entry and their preserved local stores; no new assumption.
- Judgement: provable.
- Reason: CMContinueS code unfolds to the same emitted fragments. The fid, pc, temp, break_pc values now occur as universally quantified *_pre parameters instead of existentially allocated stack cells. Constructor shape and existing numeric/model equalities still suffice for list association/code-shape equality; no missing heap allocation remains.
- Related VCs: none.
- Declaration digest: sealed/current Lemma declarations compared byte-for-byte equal; supplied normalized statement digest retained. Expanded goal definitions compared separately and changed as described.

### proof_of_cmc_emit_stmt_which_implies_wit_60

- Current VC: proof_of_cmc_emit_stmt_which_implies_wit_60
- Old gap: Final emitter folding required right-only stack cells &break_pc, &continue_pc absent from the antecedent.
- Premises added: break_pc == break_pc@pre is retained on both sides of paired code expansion/folding annotations; continue_pc == continue_pc@pre is retained on both sides of paired code expansion/folding annotations
- Premises removed: none.
- Resources changed: The erroneous right-only &break_pc, &continue_pc stack cells and their existential value witnesses disappear from the local entailment. Matching unchanged cells stay in the surrounding frame; the emitted-plan resource is still transformed exactly.
- Conclusion changed: Same exact final emitter list and arbitrary tail; erroneous fresh-stack-cell existential replaced by captured unchanged entry parameter values.
- Sources of new facts: unchanged parameters from function entry and their preserved local stores; no new assumption.
- Judgement: provable.
- Reason: CMReturnS code unfolds to the same emitted fragments. The break_pc, continue_pc values now occur as universally quantified *_pre parameters instead of existentially allocated stack cells. Constructor shape and existing numeric/model equalities still suffice for list association/code-shape equality; no missing heap allocation remains.
- Related VCs: none.
- Declaration digest: sealed/current Lemma declarations compared byte-for-byte equal; supplied normalized statement digest retained. Expanded goal definitions compared separately and changed as described.

## Delivery

Current generated manual: 120 top-level obligations, 296 splits. All six old blocker comparisons are provable; no proof manual edits were made.

## Delivery preflight repair

The first finalize rejected only fact-source coverage in the comparison plan. Updated each `fact_sources[].fact` to exactly match every `premises_added` and `resources_changed` entry. Formal C/lib/generated files and all verification results are unchanged; no additional design/symexec/post-lib calls.
