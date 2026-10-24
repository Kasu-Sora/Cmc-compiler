# Outcome

All 150 current manual witnesses have a proof route. The plan contains 44 independent groups: 115 aggressive witnesses and 35 whole-goal witnesses. No proof has been claimed as completed by this analysis.

## Structural Blocker Scan

- Status: passed
- Top-level VCs scanned: 150
- No-split VCs checked first: 31
- Definite blockers: 0

The 31 no-split entailments were checked first. All 150 top-level obligations were scanned for address ownership, scalar/current-to-pre bridges and existential witnesses. Node fields use the same pre-addresses; decomposition witnesses come from the existing AST/list representations. Recursive count facts carry the original fid/index or the explicit index-plus-one equation. No whole-goal countermodel was found.

# Annotation Comparison Review

First proving round: no annotation comparisons were supplied. Current resource/premise sources were checked in the generated goal/manual and the active counts/layout definitions. The data-length bridge is explicitly a current contract premise, rather than an unproved helper inferred by this plan.

# Proof-Mode Decisions

The split-only pass judged 379 of 383 splits provable. The four unprovable splits are the `_split_goal_2` of the following parents:

- `proof_of_cmc_args_code_count_return_wit_1`
- `proof_of_cmc_param_stores_count_return_wit_1`
- `proof_of_cmc_function_prefix_count_return_wit_2`
- `proof_of_cmc_functions_code_size_count_return_wit_2`

Their pure premises permit a nonempty abstract list even though the concrete pointer is zero; the dropped list resource is the missing relationship. Each whole parent retains that resource, forces nil, and is provable. These four and all 31 no-split witnesses use `LLM_pre_process`; every other witness uses `aggressive_pre_process`. No aggressive parent received a whole-goal proof strategy. All generated splits were judged before these modes and the strategies were chosen.

# Common Proof Patterns

- **OPEN**: unfold node/context or list representation, take its existing existential addresses, use constructor/guard information, project well-formedness/representability, and cancel the unchanged frame. Function-list opening synchronizes header and body-pointer lists.
- **NULL-LIST**: retain the whole entailment, unfold the root list, rule out cons using root=0 versus root<>0, reduce the empty count, and retain the frame.
- **BOUND**: match a constructor recurrence and child count equations; parent representability bounds the total, nonnegative child counts bound intermediates, and guards select the encoded-type/count branch.
- **CALL-PRE**: derive only the required call premise from existing constructor equalities, 32-bit index bounds, list lengths and representability.
- **EXPR-RESULT**: splits 1–4 project parent count/type representability; splits 5–6 evaluate the constructor count using guards and child results; the spatial split folds the exact node/payload using the current child addresses.
- **STMT-RESULT**: project parent count bounds, compute the constructor sum, and fold its node/payload.
- **COUNT-RESULT**: unfold the selected list/function/model recurrence, rewrite returned values and existing representability; context/list spatial splits repack their original existential pointers.

# VC Deltas

## basic-projections

- `proof_of_cmc_expr_type_code_value_entail_wit_1` — OPEN; LLM_pre_process; whole-goal decomposition.
- `proof_of_cmc_expr_type_code_value_return_wit_1` — all 1 generated splits provable; COUNT-RESULT; aggressive_pre_process; 1 splits.
- `proof_of_cm_binding_address_count_value_return_wit_1` — all 2 generated splits provable; COUNT-RESULT; aggressive_pre_process; 2 splits.
- `proof_of_cm_binding_address_count_value_return_wit_2` — all 2 generated splits provable; COUNT-RESULT; aggressive_pre_process; 2 splits.

## argument-list

- `proof_of_cmc_args_code_count_safety_wit_3` — all 2 generated splits provable; BOUND; aggressive_pre_process; 2 splits; “ ((((cm_rvalue_code_count (policy) (p) (fid_pre) (head)) + 10 ) + (cm_args_code_count_of ((cm_args_code_counts (policy) (p) (fid_pre) (tail)))) ) <= INT_MAX) ”.
- `proof_of_cmc_args_code_count_safety_wit_4` — all 2 generated splits provable; BOUND; aggressive_pre_process; 2 splits; “ (((cm_rvalue_code_count (policy) (p) (fid_pre) (head)) + 10 ) <= INT_MAX) ”.
- `proof_of_cmc_args_code_count_entail_wit_1` — OPEN; LLM_pre_process; whole-goal decomposition.
- `proof_of_cmc_args_code_count_return_wit_1` — split_goal_1 provable; split_goal_2 unprovable; whole parent provable; NULL-LIST; LLM_pre_process; whole-goal resource retention.
- `proof_of_cmc_args_code_count_return_wit_2` — all 3 generated splits provable; COUNT-RESULT; aggressive_pre_process; 3 splits.

## expression-open-variable

- `proof_of_cm_expr_counts_entail_wit_1` — OPEN; LLM_pre_process; whole-goal decomposition.
- `proof_of_cm_expr_counts_entail_wit_2` — OPEN; LLM_pre_process; CMVarE; whole-goal decomposition.
- `proof_of_cm_expr_counts_partial_solve_wit_2_pure` — all 2 generated splits provable; CALL-PRE; aggressive_pre_process; CMVarE; 2 splits; call preconditions at this constructor/recursive step.

## expression-open-binary

- `proof_of_cm_expr_counts_entail_wit_3` — OPEN; LLM_pre_process; CMAssignE; whole-goal decomposition.
- `proof_of_cm_expr_counts_entail_wit_4` — OPEN; LLM_pre_process; CMBinaryE; whole-goal decomposition.
- `proof_of_cm_expr_counts_entail_wit_6` — OPEN; LLM_pre_process; CMIndexE; whole-goal decomposition.

## expression-open-unary

- `proof_of_cm_expr_counts_entail_wit_5` — OPEN; LLM_pre_process; CMUnaryE; whole-goal decomposition.
- `proof_of_cm_expr_counts_entail_wit_7` — OPEN; LLM_pre_process; CMMemberE; whole-goal decomposition.
- `proof_of_cm_expr_counts_entail_wit_9` — OPEN; LLM_pre_process; CMPutcE; whole-goal decomposition.
- `proof_of_cm_expr_counts_entail_wit_10` — OPEN; LLM_pre_process; CMPutiE; whole-goal decomposition.
- `proof_of_cm_expr_counts_entail_wit_11` — OPEN; LLM_pre_process; CMExitE; whole-goal decomposition.

## expression-call

- `proof_of_cm_expr_counts_entail_wit_8` — OPEN; LLM_pre_process; CMCallE; whole-goal decomposition.
- `proof_of_cm_expr_counts_return_wit_22` — all 7 generated splits provable; EXPR-RESULT; aggressive_pre_process; CMCallE; 7 splits.

## expression-member-safety

- `proof_of_cm_expr_counts_safety_wit_12` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMVarE; 2 splits; “ (((cm_binding_address_count ((cm_rep_expr_op (e)))) + 1 ) <= INT_MAX) ”.
- `proof_of_cm_expr_counts_safety_wit_64` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMMemberE; 2 splits; “ (((cm_rvalue_code_count (policy) (p) (fid_pre) (x)) + 2 ) <= INT_MAX) ”.
- `proof_of_cm_expr_counts_safety_wit_66` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMMemberE; 2 splits; “ ((((cm_rvalue_code_count (policy) (p) (fid_pre) (x)) + 2 ) + 1 ) <= INT_MAX) ”.
- `proof_of_cm_expr_counts_partial_solve_wit_19_pure` — all 6 generated splits provable; CALL-PRE; aggressive_pre_process; CMMemberE; 6 splits; call preconditions at this constructor/recursive step.

## expression-assignment-safety

- `proof_of_cm_expr_counts_safety_wit_15` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMAssignE; 2 splits; “ (((cm_lvalue_code_count (policy) (p) (fid_pre) (x)) + (5 + ((cm_rvalue_code_count (policy) (p) (fid_pre) (y)) + (retval + 12 ) ) ) ) <= INT_MAX) ”.
- `proof_of_cm_expr_counts_safety_wit_16` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMAssignE; 2 splits; “ ((5 + ((cm_rvalue_code_count (policy) (p) (fid_pre) (y)) + (retval + 12 ) ) ) <= INT_MAX) ”.
- `proof_of_cm_expr_counts_safety_wit_17` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMAssignE; 2 splits; “ (((cm_rvalue_code_count (policy) (p) (fid_pre) (y)) + (retval + 12 ) ) <= INT_MAX) ”.
- `proof_of_cm_expr_counts_safety_wit_18` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMAssignE; 2 splits; “ ((retval + 12 ) <= INT_MAX) ”.

## expression-logical-safety

- `proof_of_cm_expr_counts_safety_wit_23` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMBinaryE; 2 splits; “ (((cm_rvalue_code_count (policy) (p) (fid_pre) (x)) + ((cm_rvalue_code_count (policy) (p) (fid_pre) (y)) + 5 ) ) <= INT_MAX) ”.
- `proof_of_cm_expr_counts_safety_wit_24` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMBinaryE; 2 splits; “ (((cm_rvalue_code_count (policy) (p) (fid_pre) (y)) + 5 ) <= INT_MAX) ”.
- `proof_of_cm_expr_counts_safety_wit_27` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMBinaryE; 2 splits; “ (((cm_rvalue_code_count (policy) (p) (fid_pre) (x)) + ((cm_rvalue_code_count (policy) (p) (fid_pre) (y)) + 5 ) ) <= INT_MAX) ”.
- `proof_of_cm_expr_counts_safety_wit_28` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMBinaryE; 2 splits; “ (((cm_rvalue_code_count (policy) (p) (fid_pre) (y)) + 5 ) <= INT_MAX) ”.

## expression-add-safety

- `proof_of_cm_expr_counts_safety_wit_31` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMBinaryE; 2 splits; “ (((cm_rvalue_code_count (policy) (p) (fid_pre) (x)) + ((cm_rvalue_code_count (policy) (p) (fid_pre) (y)) + 14 ) ) <= INT_MAX) ”.
- `proof_of_cm_expr_counts_safety_wit_32` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMBinaryE; 2 splits; “ (((cm_rvalue_code_count (policy) (p) (fid_pre) (y)) + 14 ) <= INT_MAX) ”.
- `proof_of_cm_expr_counts_safety_wit_34` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMBinaryE; 2 splits; “ (((cm_rvalue_code_count (policy) (p) (fid_pre) (x)) + ((cm_rvalue_code_count (policy) (p) (fid_pre) (y)) + 14 ) ) <= INT_MAX) ”.
- `proof_of_cm_expr_counts_safety_wit_35` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMBinaryE; 2 splits; “ (((cm_rvalue_code_count (policy) (p) (fid_pre) (y)) + 14 ) <= INT_MAX) ”.
- `proof_of_cm_expr_counts_safety_wit_37` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMBinaryE; 2 splits; “ (((cm_rvalue_code_count (policy) (p) (fid_pre) (x)) + ((cm_rvalue_code_count (policy) (p) (fid_pre) (y)) + 12 ) ) <= INT_MAX) ”.
- `proof_of_cm_expr_counts_safety_wit_38` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMBinaryE; 2 splits; “ (((cm_rvalue_code_count (policy) (p) (fid_pre) (y)) + 12 ) <= INT_MAX) ”.

## expression-sub-safety

- `proof_of_cm_expr_counts_safety_wit_41` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMBinaryE; 2 splits; “ (((cm_rvalue_code_count (policy) (p) (fid_pre) (x)) + ((cm_rvalue_code_count (policy) (p) (fid_pre) (y)) + 14 ) ) <= INT_MAX) ”.
- `proof_of_cm_expr_counts_safety_wit_42` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMBinaryE; 2 splits; “ (((cm_rvalue_code_count (policy) (p) (fid_pre) (y)) + 14 ) <= INT_MAX) ”.
- `proof_of_cm_expr_counts_safety_wit_44` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMBinaryE; 2 splits; “ (((cm_rvalue_code_count (policy) (p) (fid_pre) (x)) + ((cm_rvalue_code_count (policy) (p) (fid_pre) (y)) + 12 ) ) <= INT_MAX) ”.
- `proof_of_cm_expr_counts_safety_wit_45` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMBinaryE; 2 splits; “ (((cm_rvalue_code_count (policy) (p) (fid_pre) (y)) + 12 ) <= INT_MAX) ”.
- `proof_of_cm_expr_counts_safety_wit_47` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMBinaryE; 2 splits; “ (((cm_rvalue_code_count (policy) (p) (fid_pre) (x)) + ((cm_rvalue_code_count (policy) (p) (fid_pre) (y)) + 12 ) ) <= INT_MAX) ”.
- `proof_of_cm_expr_counts_safety_wit_48` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMBinaryE; 2 splits; “ (((cm_rvalue_code_count (policy) (p) (fid_pre) (y)) + 12 ) <= INT_MAX) ”.

## expression-unary-index-safety

- `proof_of_cm_expr_counts_safety_wit_52` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMUnaryE; 2 splits; “ (((cm_rvalue_code_count (policy) (p) (fid_pre) (x)) + 1 ) <= INT_MAX) ”.
- `proof_of_cm_expr_counts_safety_wit_55` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMUnaryE; 2 splits; “ (((cm_rvalue_code_count (policy) (p) (fid_pre) (x)) + 2 ) <= INT_MAX) ”.
- `proof_of_cm_expr_counts_safety_wit_58` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMIndexE; 2 splits; “ (((cm_rvalue_code_count (policy) (p) (fid_pre) (x)) + ((cm_rvalue_code_count (policy) (p) (fid_pre) (y)) + 13 ) ) <= INT_MAX) ”.
- `proof_of_cm_expr_counts_safety_wit_59` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMIndexE; 2 splits; “ (((cm_rvalue_code_count (policy) (p) (fid_pre) (y)) + 13 ) <= INT_MAX) ”.
- `proof_of_cm_expr_counts_safety_wit_61` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMIndexE; 2 splits; “ ((((cm_rvalue_code_count (policy) (p) (fid_pre) (x)) + ((cm_rvalue_code_count (policy) (p) (fid_pre) (y)) + 13 ) ) + 1 ) <= INT_MAX) ”.

## expression-io-safety

- `proof_of_cm_expr_counts_safety_wit_70` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMPutcE; 2 splits; “ (((cm_rvalue_code_count (policy) (p) (fid_pre) (x)) + 2 ) <= INT_MAX) ”.
- `proof_of_cm_expr_counts_safety_wit_73` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMPutiE; 2 splits; “ (((cm_rvalue_code_count (policy) (p) (fid_pre) (x)) + 2 ) <= INT_MAX) ”.
- `proof_of_cm_expr_counts_safety_wit_75` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMExitE; 2 splits; “ (((cm_rvalue_code_count (policy) (p) (fid_pre) (x)) + 7 ) <= INT_MAX) ”.

## expression-leaf-results

- `proof_of_cm_expr_counts_return_wit_1` — all 7 generated splits provable; EXPR-RESULT; aggressive_pre_process; kind 0; 7 splits.
- `proof_of_cm_expr_counts_return_wit_2` — all 7 generated splits provable; EXPR-RESULT; aggressive_pre_process; kind 1; 7 splits.
- `proof_of_cm_expr_counts_return_wit_3` — all 7 generated splits provable; EXPR-RESULT; aggressive_pre_process; kind 9; 7 splits.
- `proof_of_cm_expr_counts_return_wit_4` — all 7 generated splits provable; EXPR-RESULT; aggressive_pre_process; kind 10; 7 splits.

## expression-variable-results

- `proof_of_cm_expr_counts_return_wit_5` — all 7 generated splits provable; EXPR-RESULT; aggressive_pre_process; CMVarE; 7 splits.
- `proof_of_cm_expr_counts_return_wit_6` — all 7 generated splits provable; EXPR-RESULT; aggressive_pre_process; CMVarE; 7 splits.

## expression-assignment-result

- `proof_of_cm_expr_counts_return_wit_7` — all 7 generated splits provable; EXPR-RESULT; aggressive_pre_process; CMAssignE; 7 splits.

## expression-logical-results

- `proof_of_cm_expr_counts_return_wit_8` — all 7 generated splits provable; EXPR-RESULT; aggressive_pre_process; CMBinaryE; 7 splits.
- `proof_of_cm_expr_counts_return_wit_9` — all 7 generated splits provable; EXPR-RESULT; aggressive_pre_process; CMBinaryE; 7 splits.

## expression-add-results

- `proof_of_cm_expr_counts_return_wit_10` — all 7 generated splits provable; EXPR-RESULT; aggressive_pre_process; CMBinaryE; 7 splits.
- `proof_of_cm_expr_counts_return_wit_11` — all 7 generated splits provable; EXPR-RESULT; aggressive_pre_process; CMBinaryE; 7 splits.
- `proof_of_cm_expr_counts_return_wit_12` — all 7 generated splits provable; EXPR-RESULT; aggressive_pre_process; CMBinaryE; 7 splits.

## expression-sub-results

- `proof_of_cm_expr_counts_return_wit_13` — all 7 generated splits provable; EXPR-RESULT; aggressive_pre_process; CMBinaryE; 7 splits.
- `proof_of_cm_expr_counts_return_wit_14` — all 7 generated splits provable; EXPR-RESULT; aggressive_pre_process; CMBinaryE; 7 splits.
- `proof_of_cm_expr_counts_return_wit_15` — all 7 generated splits provable; EXPR-RESULT; aggressive_pre_process; CMBinaryE; 7 splits.

## expression-unary-results

- `proof_of_cm_expr_counts_return_wit_16` — all 7 generated splits provable; EXPR-RESULT; aggressive_pre_process; CMUnaryE; 7 splits.
- `proof_of_cm_expr_counts_return_wit_17` — all 7 generated splits provable; EXPR-RESULT; aggressive_pre_process; CMUnaryE; 7 splits.
- `proof_of_cm_expr_counts_return_wit_18` — all 7 generated splits provable; EXPR-RESULT; aggressive_pre_process; CMUnaryE; 7 splits.

## expression-index-result

- `proof_of_cm_expr_counts_return_wit_19` — all 7 generated splits provable; EXPR-RESULT; aggressive_pre_process; CMIndexE; 7 splits.

## expression-member-results

- `proof_of_cm_expr_counts_return_wit_20` — all 7 generated splits provable; EXPR-RESULT; aggressive_pre_process; CMMemberE; 7 splits.
- `proof_of_cm_expr_counts_return_wit_21` — all 7 generated splits provable; EXPR-RESULT; aggressive_pre_process; CMMemberE; 7 splits.

## expression-io-results

- `proof_of_cm_expr_counts_return_wit_23` — all 7 generated splits provable; EXPR-RESULT; aggressive_pre_process; CMPutcE; 7 splits.
- `proof_of_cm_expr_counts_return_wit_24` — all 7 generated splits provable; EXPR-RESULT; aggressive_pre_process; CMPutiE; 7 splits.
- `proof_of_cm_expr_counts_return_wit_25` — all 7 generated splits provable; EXPR-RESULT; aggressive_pre_process; CMExitE; 7 splits.

## statement-open-expression

- `proof_of_cmc_stmt_code_count_entail_wit_1` — OPEN; LLM_pre_process; whole-goal decomposition.
- `proof_of_cmc_stmt_code_count_entail_wit_2` — OPEN; LLM_pre_process; CMExprS; whole-goal decomposition.
- `proof_of_cmc_stmt_code_count_entail_wit_3` — OPEN; LLM_pre_process; CMInitS; whole-goal decomposition.
- `proof_of_cmc_stmt_code_count_partial_solve_wit_2_pure` — all 1 generated splits provable; CALL-PRE; aggressive_pre_process; CMInitS; 1 splits; call preconditions at this constructor/recursive step.

## statement-open-control

- `proof_of_cmc_stmt_code_count_entail_wit_4` — OPEN; LLM_pre_process; CMSeqS; whole-goal decomposition.
- `proof_of_cmc_stmt_code_count_entail_wit_5` — OPEN; LLM_pre_process; CMBlockS; whole-goal decomposition.
- `proof_of_cmc_stmt_code_count_entail_wit_6` — OPEN; LLM_pre_process; CMIfS; whole-goal decomposition.
- `proof_of_cmc_stmt_code_count_entail_wit_7` — OPEN; LLM_pre_process; CMWhileS; whole-goal decomposition.
- `proof_of_cmc_stmt_code_count_entail_wit_8` — OPEN; LLM_pre_process; CMReturnS; whole-goal decomposition.

## statement-normalization-safety

- `proof_of_cmc_stmt_code_count_safety_wit_5` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMExprS; 2 splits; “ ((retval + 1 ) <= INT_MAX) ”.
- `proof_of_cmc_stmt_code_count_safety_wit_8` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMInitS; 2 splits; “ (((retval + retval_2 ) + 5 ) <= INT_MAX) ”.
- `proof_of_cmc_stmt_code_count_safety_wit_9` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMInitS; 2 splits; “ ((retval + retval_2 ) <= INT_MAX) ”.
- `proof_of_cmc_stmt_code_count_safety_wit_31` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMReturnS; 2 splits; “ (((retval + retval_2 ) + 6 ) <= INT_MAX) ”.
- `proof_of_cmc_stmt_code_count_safety_wit_32` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMReturnS; 2 splits; “ ((retval + retval_2 ) <= INT_MAX) ”.

## statement-sequence-if-safety

- `proof_of_cmc_stmt_code_count_safety_wit_12` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMSeqS; 2 splits; “ ((retval + retval_2 ) <= INT_MAX) ”.
- `proof_of_cmc_stmt_code_count_safety_wit_15` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMIfS; 2 splits; “ (((((retval + 1 ) + retval_2 ) + 1 ) + retval_3 ) <= INT_MAX) ”.
- `proof_of_cmc_stmt_code_count_safety_wit_16` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMIfS; 2 splits; “ ((((retval + 1 ) + retval_2 ) + 1 ) <= INT_MAX) ”.
- `proof_of_cmc_stmt_code_count_safety_wit_17` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMIfS; 2 splits; “ (((retval + 1 ) + retval_2 ) <= INT_MAX) ”.
- `proof_of_cmc_stmt_code_count_safety_wit_18` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMIfS; 2 splits; “ ((retval + 1 ) <= INT_MAX) ”.

## statement-while-safety

- `proof_of_cmc_stmt_code_count_safety_wit_22` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMWhileS; 2 splits; “ ((((retval + 1 ) + retval_2 ) + 1 ) <= INT_MAX) ”.
- `proof_of_cmc_stmt_code_count_safety_wit_23` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMWhileS; 2 splits; “ (((retval + 1 ) + retval_2 ) <= INT_MAX) ”.
- `proof_of_cmc_stmt_code_count_safety_wit_24` — all 2 generated splits provable; BOUND; aggressive_pre_process; CMWhileS; 2 splits; “ ((retval + 1 ) <= INT_MAX) ”.

## statement-leaf-results

- `proof_of_cmc_stmt_code_count_return_wit_1` — all 3 generated splits provable; STMT-RESULT; aggressive_pre_process; kind 0; 3 splits.
- `proof_of_cmc_stmt_code_count_return_wit_2` — all 3 generated splits provable; STMT-RESULT; aggressive_pre_process; kind 2; 3 splits.
- `proof_of_cmc_stmt_code_count_return_wit_9` — all 3 generated splits provable; STMT-RESULT; aggressive_pre_process; kind 8; 3 splits.
- `proof_of_cmc_stmt_code_count_return_wit_10` — all 3 generated splits provable; STMT-RESULT; aggressive_pre_process; kind 9; 3 splits.

## statement-expression-results

- `proof_of_cmc_stmt_code_count_return_wit_3` — all 3 generated splits provable; STMT-RESULT; aggressive_pre_process; CMExprS; 3 splits.
- `proof_of_cmc_stmt_code_count_return_wit_4` — all 3 generated splits provable; STMT-RESULT; aggressive_pre_process; CMInitS; 3 splits.
- `proof_of_cmc_stmt_code_count_return_wit_11` — all 3 generated splits provable; STMT-RESULT; aggressive_pre_process; CMReturnS; 3 splits.

## statement-control-results

- `proof_of_cmc_stmt_code_count_return_wit_5` — all 3 generated splits provable; STMT-RESULT; aggressive_pre_process; CMSeqS; 3 splits.
- `proof_of_cmc_stmt_code_count_return_wit_6` — all 3 generated splits provable; STMT-RESULT; aggressive_pre_process; CMBlockS; 3 splits.
- `proof_of_cmc_stmt_code_count_return_wit_7` — all 3 generated splits provable; STMT-RESULT; aggressive_pre_process; CMIfS; 3 splits.
- `proof_of_cmc_stmt_code_count_return_wit_8` — all 3 generated splits provable; STMT-RESULT; aggressive_pre_process; CMWhileS; 3 splits.

## parameter-stores

- `proof_of_cmc_param_stores_count_safety_wit_3` — all 2 generated splits provable; BOUND; aggressive_pre_process; 2 splits; “ (((retval_2 + retval ) + 5 ) <= INT_MAX) ”.
- `proof_of_cmc_param_stores_count_safety_wit_4` — all 2 generated splits provable; BOUND; aggressive_pre_process; 2 splits; “ ((retval_2 + retval ) <= INT_MAX) ”.
- `proof_of_cmc_param_stores_count_entail_wit_1` — OPEN; LLM_pre_process; whole-goal decomposition.
- `proof_of_cmc_param_stores_count_return_wit_1` — split_goal_1 provable; split_goal_2 unprovable; whole parent provable; NULL-LIST; LLM_pre_process; whole-goal resource retention.
- `proof_of_cmc_param_stores_count_return_wit_2` — all 3 generated splits provable; COUNT-RESULT; aggressive_pre_process; 3 splits.

## function-prologue

- `proof_of_cmc_function_prologue_count_safety_wit_1` — all 2 generated splits provable; BOUND; aggressive_pre_process; 2 splits; “ ((14 + retval ) <= INT_MAX) ”.
- `proof_of_cmc_function_prologue_count_entail_wit_1` — OPEN; LLM_pre_process; whole-goal decomposition.
- `proof_of_cmc_function_prologue_count_return_wit_1` — all 3 generated splits provable; COUNT-RESULT; aggressive_pre_process; 3 splits.

## function-body-count

- `proof_of_cmc_function_code_count_safety_wit_1` — all 2 generated splits provable; BOUND; aggressive_pre_process; 2 splits; “ (((prologue_count + retval ) + 7 ) <= INT_MAX) ”.
- `proof_of_cmc_function_code_count_safety_wit_2` — all 2 generated splits provable; BOUND; aggressive_pre_process; 2 splits; “ ((prologue_count + retval ) <= INT_MAX) ”.
- `proof_of_cmc_function_code_count_entail_wit_1` — OPEN; LLM_pre_process; whole-goal decomposition.
- `proof_of_cmc_function_code_count_return_wit_1` — all 3 generated splits provable; COUNT-RESULT; aggressive_pre_process; 3 splits.
- `proof_of_cmc_function_code_count_partial_solve_wit_1_pure` — all 2 generated splits provable; CALL-PRE; aggressive_pre_process; 2 splits; call preconditions at this constructor/recursive step.

## prefix-open

- `proof_of_cmc_function_prefix_count_entail_wit_1` — OPEN; LLM_pre_process; whole-goal decomposition.
- `proof_of_cmc_function_prefix_count_entail_wit_2` — OPEN; LLM_pre_process; whole-goal decomposition.

## prefix-transition

- `proof_of_cmc_function_prefix_count_safety_wit_9` — all 2 generated splits provable; BOUND; aggressive_pre_process; 2 splits; “ ((head_count + retval ) <= INT_MAX) ”.
- `proof_of_cmc_function_prefix_count_partial_solve_wit_2_pure` — all 3 generated splits provable; CALL-PRE; aggressive_pre_process; 3 splits; call preconditions at this constructor/recursive step.

## prefix-results

- `proof_of_cmc_function_prefix_count_return_wit_1` — all 3 generated splits provable; COUNT-RESULT; aggressive_pre_process; 3 splits.
- `proof_of_cmc_function_prefix_count_return_wit_2` — split_goal_1 provable; split_goal_2 unprovable; whole parent provable; NULL-LIST; LLM_pre_process; whole-goal resource retention.
- `proof_of_cmc_function_prefix_count_return_wit_3` — all 2 generated splits provable; COUNT-RESULT; aggressive_pre_process; 2 splits.

## function-pc

- `proof_of_cmc_function_pc_safety_wit_2` — all 2 generated splits provable; BOUND; aggressive_pre_process; 2 splits; “ ((11 + retval ) <= INT_MAX) ”.
- `proof_of_cmc_function_pc_entail_wit_1` — OPEN; LLM_pre_process; whole-goal decomposition.
- `proof_of_cmc_function_pc_entail_wit_2` — all 2 generated splits provable; OPEN; aggressive_pre_process; 2 splits.
- `proof_of_cmc_function_pc_return_wit_1` — all 1 generated splits provable; COUNT-RESULT; aggressive_pre_process; 1 splits.
- `proof_of_cmc_function_pc_partial_solve_wit_1_pure` — all 1 generated splits provable; CALL-PRE; aggressive_pre_process; 1 splits; call preconditions at this constructor/recursive step.

## functions-open

- `proof_of_cmc_functions_code_size_count_entail_wit_1` — OPEN; LLM_pre_process; whole-goal decomposition.
- `proof_of_cmc_functions_code_size_count_entail_wit_2` — OPEN; LLM_pre_process; whole-goal decomposition.

## functions-transition

- `proof_of_cmc_functions_code_size_count_safety_wit_3` — all 2 generated splits provable; BOUND; aggressive_pre_process; 2 splits; “ ((index_pre + 1 ) <= INT_MAX) ”.
- `proof_of_cmc_functions_code_size_count_safety_wit_5` — all 2 generated splits provable; BOUND; aggressive_pre_process; 2 splits; “ ((head_count + retval ) <= INT_MAX) ”.
- `proof_of_cmc_functions_code_size_count_partial_solve_wit_2_pure` — all 3 generated splits provable; CALL-PRE; aggressive_pre_process; 3 splits; call preconditions at this constructor/recursive step.

## functions-results

- `proof_of_cmc_functions_code_size_count_return_wit_1` — all 3 generated splits provable; COUNT-RESULT; aggressive_pre_process; 3 splits.
- `proof_of_cmc_functions_code_size_count_return_wit_2` — split_goal_1 provable; split_goal_2 unprovable; whole parent provable; NULL-LIST; LLM_pre_process; whole-goal resource retention.

## model-length-bound

- `proof_of_cmc_model_code_length_entail_wit_2` — all 4 generated splits provable; OPEN; aggressive_pre_process; 4 splits; positive per-function size bounds function-list length.

## model-code-results

- `proof_of_cmc_model_code_length_safety_wit_2` — all 2 generated splits provable; BOUND; aggressive_pre_process; 2 splits; “ ((11 + retval ) <= INT_MAX) ”.
- `proof_of_cmc_model_code_length_entail_wit_1` — OPEN; LLM_pre_process; whole-goal decomposition.
- `proof_of_cmc_model_code_length_return_wit_1` — all 2 generated splits provable; COUNT-RESULT; aggressive_pre_process; 2 splits.
- `proof_of_cmc_model_code_length_partial_solve_wit_1_pure` — all 1 generated splits provable; CALL-PRE; aggressive_pre_process; 1 splits; call preconditions at this constructor/recursive step.

## model-data-results

- `proof_of_cmc_model_data_length_entail_wit_1` — OPEN; LLM_pre_process; whole-goal decomposition.
- `proof_of_cmc_model_data_length_return_wit_1` — all 2 generated splits provable; COUNT-RESULT; aggressive_pre_process; 2 splits.

# Grouping Decisions

The initial partition followed AST constructors, count arithmetic, representation opening/folding, and recursive function-list stages. A second review separated every substantial result group from independent safety/transition work. No group exceeds six witnesses. All helper names carry the owner-group suffix and every planned declaration has explicit premises and a proof route in the plan; public helpers are candidates, never sibling dependencies.

The singleton assignment-result group owns normalization plus seven result splits; its final expression identity is independent of assignment safety. The singleton index-result group owns the paired lvalue/rvalue constructor result and seven splits, independent of its three intermediate arithmetic checks. The singleton model-length-bound group owns the new positivity/length helper chain, independent of model result equations and safety. These are separate final-result/helper families, not arbitrary witness-count splits.

## Load and critical path

| Group | Witnesses | Aggressive splits | New helper families | Difficulty |
|---|---:|---:|---:|---:|
| basic-projections | 4 | 5 | 0 | 1 |
| argument-list | 5 | 7 | 0 | 2 |
| expression-open-variable | 3 | 2 | 0 | 2 |
| expression-open-binary | 3 | 0 | 0 | 2 |
| expression-open-unary | 5 | 0 | 0 | 2 |
| expression-call | 2 | 7 | 0 | 2 |
| expression-member-safety | 4 | 12 | 0 | 3 |
| expression-assignment-safety | 4 | 8 | 1 | 3 |
| expression-logical-safety | 4 | 8 | 0 | 2 |
| expression-add-safety | 6 | 12 | 1 | 3 |
| expression-sub-safety | 6 | 12 | 1 | 3 |
| expression-unary-index-safety | 5 | 10 | 0 | 2 |
| expression-io-safety | 3 | 6 | 0 | 2 |
| expression-leaf-results | 4 | 28 | 0 | 2 |
| expression-variable-results | 2 | 14 | 0 | 3 |
| expression-assignment-result | 1 | 7 | 1 | 3 |
| expression-logical-results | 2 | 14 | 0 | 2 |
| expression-add-results | 3 | 21 | 1 | 4 |
| expression-sub-results | 3 | 21 | 1 | 4 |
| expression-unary-results | 3 | 21 | 0 | 2 |
| expression-index-result | 1 | 7 | 0 | 2 |
| expression-member-results | 2 | 14 | 0 | 3 |
| expression-io-results | 3 | 21 | 0 | 2 |
| statement-open-expression | 4 | 1 | 0 | 2 |
| statement-open-control | 5 | 0 | 0 | 2 |
| statement-normalization-safety | 5 | 10 | 1 | 3 |
| statement-sequence-if-safety | 5 | 10 | 0 | 2 |
| statement-while-safety | 3 | 6 | 0 | 2 |
| statement-leaf-results | 4 | 12 | 0 | 2 |
| statement-expression-results | 3 | 9 | 1 | 3 |
| statement-control-results | 4 | 12 | 0 | 2 |
| parameter-stores | 5 | 7 | 1 | 3 |
| function-prologue | 3 | 5 | 0 | 2 |
| function-body-count | 5 | 9 | 0 | 2 |
| prefix-open | 2 | 0 | 1 | 3 |
| prefix-transition | 2 | 5 | 1 | 4 |
| prefix-results | 3 | 5 | 1 | 3 |
| function-pc | 5 | 6 | 0 | 2 |
| functions-open | 2 | 0 | 1 | 3 |
| functions-transition | 3 | 7 | 0 | 2 |
| functions-results | 2 | 3 | 1 | 3 |
| model-length-bound | 1 | 4 | 3 | 4 |
| model-code-results | 4 | 5 | 0 | 2 |
| model-data-results | 2 | 2 | 0 | 2 |

Likely tails are expression-add-results and expression-sub-results (21 splits each, one encoded-pointer bridge each, shared AST/type/count context), prefix-transition (five splits, one inductive nonnegative-prefix lemma, list-length and count context), and model-length-bound (four splits, three small public positivity/length lemmas, program well-formedness context). Their independent safety, opening and final-result work is already split into other groups. The paired/triple result witnesses within each binary result group share exactly the same encoding lemma and branch-sensitive count definition; this is the retained coupling.

The encoding bridges, normalized-character bridge, function-list cons equivalence, prefix nonnegativity and positive function-size/length facts are public candidates. Since current-round workers have independent frozen inputs, each group that needs an unestablished encoding or list-cons fact has its own exact suffixed declaration; no group assumes another group has finished. No permutation, mask-clear or array-update mathematics is involved.

# Risks or Blockers

No annotation/specification/dependency blocker identified. The main proof risks are routine separation-logic reassociation for parallel header/body list representations, signed 32-bit cast normalization, and induction for type-encoding bounds or the function-list length bound. Their premises are present. The four failed pure splits are generation granularity issues handled by whole-goal modes. Generated source and case library were not edited; no raw compiler or alternate debug script was used.
