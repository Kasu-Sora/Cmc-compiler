# VC checking decision summary

## Outcome

No definite blocker. All 50 manual top-level obligations have a proving assignment; this is a provability review, not proof validation. No formal source was edited.

## Structural Blocker Scan

- Status: passed
- Top-level VCs scanned: 50
- No-split VCs checked first: 3
- Definite blockers: 0

Checked raw emitter entry and both temporary-context entries first. The owned code_capacity Int cell supplies its representable bound; function context supplies exactly the field addresses, nonzero root, and pp/lp witnesses requested at entry. Scalar current/pre values agree. All remaining top-level resource shapes retain their addresses and frames; no missing equality or resource countermodel was found.

## Annotation Comparison Review

First proving round: no annotation comparisons. The type discriminator is established at branch entailments from the public type-code contract; the temporary size bridge is established at both initial context entailments from slot wellformedness. Later offset equality comes from the helper return and that bridge. None is an unestablished new assumption.

## Proof-Mode Decisions

Completed the full split-only pass before deciding modes or strategies. All 54 split goals are provable. The 47 parents with splits use aggressive_pre_process; the three no-split parents use LLM_pre_process after whole-goal review. No split goal is assigned independently.

Split-only judgments in manual declaration order:

- `proof_of_cm_emit_raw_return_wit_1_split_goal_spatial`: provable.
- `proof_of_cm_emit_entail_wit_1_split_goal_1`: provable.
- `proof_of_cm_emit_entail_wit_1_split_goal_2`: provable.
- `proof_of_cm_emit_entail_wit_1_split_goal_spatial`: provable.
- `proof_of_cm_emit_return_wit_1_split_goal_spatial`: provable.
- `proof_of_cm_emit_normalize_entail_wit_1_split_goal_1`: provable.
- `proof_of_cm_emit_normalize_entail_wit_1_split_goal_spatial`: provable.
- `proof_of_cm_emit_normalize_return_wit_1_split_goal_spatial`: provable.
- `proof_of_cm_emit_normalize_return_wit_2_split_goal_spatial`: provable.
- `proof_of_cm_emit_normalize_partial_solve_wit_1_pure_split_goal_1`: provable.
- `proof_of_cm_emit_normalize_partial_solve_wit_2_pure_split_goal_1`: provable.
- `proof_of_cm_emit_normalize_partial_solve_wit_3_pure_split_goal_1`: provable.
- `proof_of_cm_emit_normalize_partial_solve_wit_4_pure_split_goal_1`: provable.
- `proof_of_cm_emit_normalize_partial_solve_wit_5_pure_split_goal_1`: provable.
- `proof_of_cm_emit_normalize_partial_solve_wit_6_pure_split_goal_1`: provable.
- `proof_of_cm_emit_load_entail_wit_1_split_goal_1`: provable.
- `proof_of_cm_emit_load_entail_wit_1_split_goal_spatial`: provable.
- `proof_of_cm_emit_load_entail_wit_2_split_goal_1`: provable.
- `proof_of_cm_emit_load_entail_wit_2_split_goal_spatial`: provable.
- `proof_of_cm_emit_load_return_wit_1_split_goal_spatial`: provable.
- `proof_of_cm_emit_load_return_wit_2_split_goal_spatial`: provable.
- `proof_of_cm_emit_load_partial_solve_wit_1_pure_split_goal_1`: provable.
- `proof_of_cm_emit_load_partial_solve_wit_2_pure_split_goal_1`: provable.
- `proof_of_cm_emit_store_entail_wit_1_split_goal_1`: provable.
- `proof_of_cm_emit_store_entail_wit_1_split_goal_spatial`: provable.
- `proof_of_cm_emit_store_entail_wit_2_split_goal_1`: provable.
- `proof_of_cm_emit_store_entail_wit_2_split_goal_spatial`: provable.
- `proof_of_cm_emit_store_return_wit_1_split_goal_spatial`: provable.
- `proof_of_cm_emit_store_return_wit_2_split_goal_spatial`: provable.
- `proof_of_cm_emit_store_partial_solve_wit_1_pure_split_goal_1`: provable.
- `proof_of_cm_emit_store_partial_solve_wit_2_pure_split_goal_1`: provable.
- `proof_of_cm_emit_fp_address_entail_wit_1_split_goal_spatial`: provable.
- `proof_of_cm_emit_fp_address_return_wit_1_split_goal_spatial`: provable.
- `proof_of_cm_emit_fp_address_partial_solve_wit_1_pure_split_goal_1`: provable.
- `proof_of_cm_emit_fp_address_partial_solve_wit_2_pure_split_goal_1`: provable.
- `proof_of_cm_emit_fp_address_partial_solve_wit_3_pure_split_goal_1`: provable.
- `proof_of_cm_emit_fp_address_partial_solve_wit_4_pure_split_goal_1`: provable.
- `proof_of_cm_emit_temp_store_entail_wit_2_split_goal_spatial`: provable.
- `proof_of_cm_emit_temp_store_return_wit_1_split_goal_spatial`: provable.
- `proof_of_cm_emit_temp_store_partial_solve_wit_3_pure_split_goal_1`: provable.
- `proof_of_cm_emit_temp_load_entail_wit_2_split_goal_spatial`: provable.
- `proof_of_cm_emit_temp_load_return_wit_1_split_goal_spatial`: provable.
- `proof_of_cm_emit_temp_load_partial_solve_wit_3_pure_split_goal_1`: provable.
- `proof_of_cmc_binary_opcode_return_wit_1_split_goal_1`: provable.
- `proof_of_cmc_binary_opcode_return_wit_2_split_goal_1`: provable.
- `proof_of_cmc_binary_opcode_return_wit_3_split_goal_1`: provable.
- `proof_of_cmc_binary_opcode_return_wit_4_split_goal_1`: provable.
- `proof_of_cmc_binary_opcode_return_wit_5_split_goal_1`: provable.
- `proof_of_cmc_binary_opcode_return_wit_6_split_goal_1`: provable.
- `proof_of_cmc_binary_opcode_return_wit_7_split_goal_1`: provable.
- `proof_of_cmc_binary_opcode_return_wit_8_split_goal_1`: provable.
- `proof_of_cmc_binary_opcode_return_wit_9_split_goal_1`: provable.
- `proof_of_cmc_binary_opcode_return_wit_10_split_goal_1`: provable.
- `proof_of_cmc_binary_opcode_return_wit_11_split_goal_1`: provable.

## Common Proof Patterns

- RAW: unfold cm_emitter_rep, preserve the five field cells and both initialized/undefined array pairs; instantiate its ops/imms witnesses from the existing cells. At entry derive capacity <= INT_MAX from the owned Int cell, retaining the same cell. At return use Zlength_app and singleton lengths to fold the new prefixes; equality of old lengths and strict capacity provide the new bounds.
- EMIT: unfold only cm_emitter_plan_rep, exposing its total-length bound and framing the emitter representation. cm_rep_ops/imms are maps: map length supplies Zlength done; map_app and singleton computation align the post-write prefixes with done ++ [instruction]. Nonnegative tail length proves one free cell.
- BRANCH: branch equality/inequality, ty=cm_type_encode model_ty, and cm_type_code_wf establish the char discriminator. For equality use the public char-encoding lemma planned in this group; for inequality contradict the encoding of CMCharTy. Rewrite the selected fragment, leaving the identical emitter plan as the spatial frame.
- RESULT: use the model-type equality/inequality already supplied by the branch (normalize non-char instead has ty<>1 plus its encoding equality). Destruct the type only as needed, reduce the fragment, normalize app associativity or app_nil_r, then cancel the unchanged plan. No new spatial witnesses.
- CONTEXT: use cm_slots_wf for params and locals and f=cm_function_at policy fid ... to establish the size/offset bridge. Unfold cm_function_context_rep to obtain nonzero fn and existing pp/lp, frame the entire emitter plan, and expose exactly the five fields and two slot lists. After cmc_temp_offset, retval equality and the established bridge retarget the fragment; refold context using the same pp/lp and normalize app associativity. All pure premises are explicit VC hypotheses or come from the unfolded representation.
- TEMP-RESULT: substitute offset=cm_temp_offset from the explicit premise; unfold the appropriate temp fragment, reassociate append, and commute/cancel the function-context frame. No size lemma or context opening is needed.
- FP: reduce cm_fp_relative_address_code. Entry is an identical plan after list reduction; return reassociates four singleton appends into done ++ fragment. All resources remain framed, with no existential or additional bounds.
- CONSTANT: compute tvm_opcode_code for the fixed constructor, introduce the reflexive pure equality under the unchanged spatial assertion. Local cells and emitter/function predicates impose no further premises.
- BINARY: unfold cm_binary_opcode and tvm_opcode_code. Concrete equality branches compute immediately; the default branch uses all ten explicit op<>2,...,11 premises to rewrite Z.eqb tests false. The selected split is purely mathematical and has no spatial resource.

## VC Deltas

- `proof_of_cm_emit_raw_entail_wit_1`: raw_emitter, whole-goal; 0 splits. Delta: cm_emit_raw_entail_wit_1. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cm_emit_raw_return_wit_1`: raw_emitter, aggressive; 1 splits. Delta: cm_emit_raw_return_wit_1. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cm_emit_entail_wit_1`: emit_plan, aggressive; 3 splits. Delta: cm_emit_entail_wit_1. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cm_emit_return_wit_1`: emit_plan, aggressive; 1 splits. Delta: cm_emit_return_wit_1. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cm_emit_normalize_entail_wit_1`: typed_branches, aggressive; 2 splits. Delta: cm_emit_normalize_entail_wit_1. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cm_emit_normalize_return_wit_1`: typed_results, aggressive; 1 splits. Delta: cm_emit_normalize_return_wit_1. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cm_emit_normalize_return_wit_2`: typed_results, aggressive; 1 splits. Delta: cm_emit_normalize_return_wit_2. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cm_emit_normalize_partial_solve_wit_1_pure`: normalize_constants, aggressive; 1 splits. Delta: cm_emit_normalize_partial_solve_wit_1_pure. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cm_emit_normalize_partial_solve_wit_2_pure`: normalize_constants, aggressive; 1 splits. Delta: cm_emit_normalize_partial_solve_wit_2_pure. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cm_emit_normalize_partial_solve_wit_3_pure`: normalize_constants, aggressive; 1 splits. Delta: cm_emit_normalize_partial_solve_wit_3_pure. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cm_emit_normalize_partial_solve_wit_4_pure`: normalize_constants, aggressive; 1 splits. Delta: cm_emit_normalize_partial_solve_wit_4_pure. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cm_emit_normalize_partial_solve_wit_5_pure`: normalize_constants, aggressive; 1 splits. Delta: cm_emit_normalize_partial_solve_wit_5_pure. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cm_emit_normalize_partial_solve_wit_6_pure`: normalize_constants, aggressive; 1 splits. Delta: cm_emit_normalize_partial_solve_wit_6_pure. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cm_emit_load_entail_wit_1`: typed_branches, aggressive; 2 splits. Delta: cm_emit_load_entail_wit_1. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cm_emit_load_entail_wit_2`: typed_branches, aggressive; 2 splits. Delta: cm_emit_load_entail_wit_2. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cm_emit_load_return_wit_1`: typed_results, aggressive; 1 splits. Delta: cm_emit_load_return_wit_1. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cm_emit_load_return_wit_2`: typed_results, aggressive; 1 splits. Delta: cm_emit_load_return_wit_2. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cm_emit_load_partial_solve_wit_1_pure`: memory_constants, aggressive; 1 splits. Delta: cm_emit_load_partial_solve_wit_1_pure. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cm_emit_load_partial_solve_wit_2_pure`: memory_constants, aggressive; 1 splits. Delta: cm_emit_load_partial_solve_wit_2_pure. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cm_emit_store_entail_wit_1`: typed_branches, aggressive; 2 splits. Delta: cm_emit_store_entail_wit_1. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cm_emit_store_entail_wit_2`: typed_branches, aggressive; 2 splits. Delta: cm_emit_store_entail_wit_2. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cm_emit_store_return_wit_1`: typed_results, aggressive; 1 splits. Delta: cm_emit_store_return_wit_1. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cm_emit_store_return_wit_2`: typed_results, aggressive; 1 splits. Delta: cm_emit_store_return_wit_2. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cm_emit_store_partial_solve_wit_1_pure`: memory_constants, aggressive; 1 splits. Delta: cm_emit_store_partial_solve_wit_1_pure. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cm_emit_store_partial_solve_wit_2_pure`: memory_constants, aggressive; 1 splits. Delta: cm_emit_store_partial_solve_wit_2_pure. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cm_emit_fp_address_entail_wit_1`: fp_address, aggressive; 1 splits. Delta: cm_emit_fp_address_entail_wit_1. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cm_emit_fp_address_return_wit_1`: fp_address, aggressive; 1 splits. Delta: cm_emit_fp_address_return_wit_1. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cm_emit_fp_address_partial_solve_wit_1_pure`: fp_address, aggressive; 1 splits. Delta: cm_emit_fp_address_partial_solve_wit_1_pure. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cm_emit_fp_address_partial_solve_wit_2_pure`: fp_address, aggressive; 1 splits. Delta: cm_emit_fp_address_partial_solve_wit_2_pure. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cm_emit_fp_address_partial_solve_wit_3_pure`: fp_address, aggressive; 1 splits. Delta: cm_emit_fp_address_partial_solve_wit_3_pure. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cm_emit_fp_address_partial_solve_wit_4_pure`: fp_address, aggressive; 1 splits. Delta: cm_emit_fp_address_partial_solve_wit_4_pure. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cm_emit_temp_store_entail_wit_1`: temp_context, whole-goal; 0 splits. Delta: cm_emit_temp_store_entail_wit_1. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cm_emit_temp_store_entail_wit_2`: temp_context, aggressive; 1 splits. Delta: cm_emit_temp_store_entail_wit_2. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cm_emit_temp_store_return_wit_1`: temp_results, aggressive; 1 splits. Delta: cm_emit_temp_store_return_wit_1. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cm_emit_temp_store_partial_solve_wit_3_pure`: temp_results, aggressive; 1 splits. Delta: cm_emit_temp_store_partial_solve_wit_3_pure. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cm_emit_temp_load_entail_wit_1`: temp_context, whole-goal; 0 splits. Delta: cm_emit_temp_load_entail_wit_1. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cm_emit_temp_load_entail_wit_2`: temp_context, aggressive; 1 splits. Delta: cm_emit_temp_load_entail_wit_2. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cm_emit_temp_load_return_wit_1`: temp_results, aggressive; 1 splits. Delta: cm_emit_temp_load_return_wit_1. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cm_emit_temp_load_partial_solve_wit_3_pure`: temp_results, aggressive; 1 splits. Delta: cm_emit_temp_load_partial_solve_wit_3_pure. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cmc_binary_opcode_return_wit_1`: binary_comparisons, aggressive; 1 splits. Delta: cmc_binary_opcode_return_wit_1. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cmc_binary_opcode_return_wit_2`: binary_comparisons, aggressive; 1 splits. Delta: cmc_binary_opcode_return_wit_2. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cmc_binary_opcode_return_wit_3`: binary_comparisons, aggressive; 1 splits. Delta: cmc_binary_opcode_return_wit_3. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cmc_binary_opcode_return_wit_4`: binary_comparisons, aggressive; 1 splits. Delta: cmc_binary_opcode_return_wit_4. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cmc_binary_opcode_return_wit_5`: binary_comparisons, aggressive; 1 splits. Delta: cmc_binary_opcode_return_wit_5. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cmc_binary_opcode_return_wit_6`: binary_comparisons, aggressive; 1 splits. Delta: cmc_binary_opcode_return_wit_6. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cmc_binary_opcode_return_wit_7`: binary_arithmetic, aggressive; 1 splits. Delta: cmc_binary_opcode_return_wit_7. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cmc_binary_opcode_return_wit_8`: binary_arithmetic, aggressive; 1 splits. Delta: cmc_binary_opcode_return_wit_8. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cmc_binary_opcode_return_wit_9`: binary_arithmetic, aggressive; 1 splits. Delta: cmc_binary_opcode_return_wit_9. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cmc_binary_opcode_return_wit_10`: binary_arithmetic, aggressive; 1 splits. Delta: cmc_binary_opcode_return_wit_10. Exact selected-target delta and strategy are in its plan entry.
- `proof_of_cmc_binary_opcode_return_wit_11`: binary_arithmetic, aggressive; 1 splits. Delta: cmc_binary_opcode_return_wit_11. Exact selected-target delta and strategy are in its plan entry.

## Grouping Decisions

Initial boundaries follow representation unfolding/folding, type-discriminator reasoning, fragment append normalization, and literal opcode computation. Second review separated final-result and constant-opcode work from both prospective tail groups. There are no single-witness or over-six-witness groups. All groups are independent and use the frozen case library; the planned public helper candidates are not sibling imports.

| Group | Top-level | Splits | New helpers | Difficulty |
|---|---:|---:|---:|---:|
| temp_context | 4 | 2 | 3 | 4 |
| raw_emitter | 2 | 1 | 0 | 3 |
| typed_branches | 5 | 10 | 1 | 3 |
| emit_plan | 2 | 4 | 0 | 2 |
| typed_results | 6 | 6 | 0 | 2 |
| temp_results | 4 | 4 | 0 | 1 |
| fp_address | 6 | 6 | 0 | 1 |
| normalize_constants | 6 | 6 | 0 | 1 |
| memory_constants | 4 | 4 | 0 | 1 |
| binary_comparisons | 6 | 6 | 0 | 1 |
| binary_arithmetic | 5 | 5 | 0 | 1 |

Critical-path review: temp_context has 4 parents, 2 aggressive spatial splits, 2 whole-goal context entries, and 3 pure size/offset helpers over the already imported slot model. Keep its two entries and two post-helper context folds together because their pp/lp and offset bridge bookkeeping is identical; independent returns and opcode facts are in temp_results. raw_emitter has 2 parents and 1 split with five fields and four array predicates; keeping entry/exit together preserves the emitter representation context, with no new helper expected. typed_branches has 5 parents, 10 splits, and one char-encoding helper; independent final fragments are in typed_results. emit_plan has 2 parents, 4 splits and only standard map/list equalities; no new length helper is needed. Remaining groups carry only definition reduction, existing app laws, cancellation, and literal equalities. No cross-group helper dependency is assumed.

## Risks or Blockers

No annotation/specification/dependency blocker found. The most substantial fresh mathematics is slot-indexed wellformedness implying aggregate size equality, explicitly owned by temp_context. The existing generated auto proof file contains Admitted statements and is not treated as additional proof evidence in this review. Controller/group checks still determine acceptance.
