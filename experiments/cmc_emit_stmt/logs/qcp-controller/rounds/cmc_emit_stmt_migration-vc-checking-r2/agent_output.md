# Outcome
All 296 generated split goals are judged provable; 116 parents select aggressive_pre_process. The four no-split whole goals are provable and select LLM_pre_process. This is analysis, not completed Rocq proof. No formal files were modified and no debug/check commands were run.

## Structural Blocker Scan
- Status: passed
- Top-level VCs scanned: 120
- No-split VCs checked first: 4
- Definite blockers: 0

## Annotation Comparison Review
The six current stmt which-implies VCs 10, 21, 43, 48, 53, 60 were independently checked. Their new *_pre quantities are universally bound scalar parameters used identically in the two model expressions; no consequent requests absent stack cells. Constructor facts originate in branch guards/payload VCs (6, 16, 36, 45, 50, 55), with arithmetic count equalities originating in called count-context contracts. These revised VCs need model reduction/list association, not an additional mathematical premise. They form the first group for retry priority.

## Proof-Mode Decisions
The structural scan preceded the split pass. Split declarations 0–295 in manual order were each judged provable before any mode was selected. No failed split required whole-goal fallback. Four no-split goals (if/stmt entry and the two function context openings) are duplicated disjunctions of definitional resource unfoldings; select LLM mode. All other modes follow the all-splits-provable rule.

## Common Proof Patterns
- PLAN: keep the same emitter assertion, out/capacity and tail. Use the constructor equality to expose cm_emit_stmt without recursively rewriting s into its own projections; reduce constructor projections, substitute count/target equalities, normalize integer sums and list association. The two plan lists become equal; no resource is allocated.
- AST: destruct the statement constructor and eliminate incompatible kind codes using the actual guard. Unfold cm_stmt_payload in the surviving branch. Extract its pure pointer facts while retaining child expression/statement predicates; instantiate existential child pointers with the existing pointers. Close the selected pure fact or spatial child projection by separation cancellation.
- FOLD: expose cm_stmt_rep as its node/payload. Use the given nonnull statement pointer, constructor equation and child pointer equalities. Choose the existing xe/xa/xb as witnesses and reassemble the five fields and payload; preserve all child resources.
- PURE: simplify only constructor projections cm_stmt_expr/cm_stmt_first/cm_stmt_second/cm_rep_stmt_slot, then use the existing constructor equation, matching wf/count premises or return-value count equalities. For bounds unfold cm_i32_code_count, normalize sums, and use the corresponding existing endpoint premise. Frame resources are unchanged.
- SAFETY: substitute returned count equalities; unfold cm_i32_code_count. Use nonnegative pc and child counts and the already established parent/child endpoint bound. Reduce only the relevant statement count constructor and close the requested INT_MIN/INT_MAX inequality by linear arithmetic; retain/discard the heap frame through the pure entailment rule.
- CAP: derive constructor-specific wf/count facts from cm_stmt_wf and cm_stmt_counts_representable, and temp bounds from cm_stemps/max. Prove/use the public statement length-count identity with arbitrary pc/temp/break/continue. Rewrite complete and child lengths to counts; nonnegative component lengths/counts plus 0<=pc and the complete endpoint bound establish each subrange. Slot validity uses the init wf index range and zero array count; slot type encoding follows list lookup at that valid index. No new precondition is needed.
- RETURN: simplify nested constructor projections in the selected pure conclusion; rewrite the branch constructor equation backwards once to recover the original s. The unchanged original endpoint, temps, representable-count and wf premises establish the four selected facts respectively.
- OPEN/FUNCTION-FOLD: unpack or reassemble existing existential child/list pointers and exact field resources; never synthesize allocations.

## VC Deltas
- repaired_plan_returns: stmt_which_implies_wit_10, stmt_which_implies_wit_21, stmt_which_implies_wit_43, stmt_which_implies_wit_48, stmt_which_implies_wit_53, stmt_which_implies_wit_60. The ordered per-split delta and strategy is in group_plan.json.
- stmt_capacity: if_stmt_which_implies_wit_3, stmt_which_implies_wit_7, stmt_which_implies_wit_17, stmt_which_implies_wit_24, stmt_which_implies_wit_30, stmt_which_implies_wit_37, stmt_which_implies_wit_56. The ordered per-split delta and strategy is in group_plan.json.
- if_safety_prefix: if_stmt_safety_wit_10, if_stmt_safety_wit_11, if_stmt_safety_wit_13, if_stmt_safety_wit_14, if_stmt_safety_wit_15, if_stmt_safety_wit_16. The ordered per-split delta and strategy is in group_plan.json.
- if_safety_suffix: if_stmt_safety_wit_19, if_stmt_safety_wit_20, if_stmt_safety_wit_21, if_stmt_safety_wit_22, if_stmt_safety_wit_23. The ordered per-split delta and strategy is in group_plan.json.
- while_safety: stmt_safety_wit_15, stmt_safety_wit_16, stmt_safety_wit_18, stmt_safety_wit_19, stmt_safety_wit_20, stmt_safety_wit_21. The ordered per-split delta and strategy is in group_plan.json.
- return_leaf_facts: stmt_return_wit_2, stmt_return_wit_3, stmt_return_wit_4, stmt_return_wit_11. The ordered per-split delta and strategy is in group_plan.json.
- return_recursive_facts: stmt_return_wit_5, stmt_return_wit_6, stmt_return_wit_7, stmt_return_wit_8. The ordered per-split delta and strategy is in group_plan.json.
- expr_decl_pure: stmt_partial_solve_wit_8_pure, stmt_partial_solve_wit_10_pure, stmt_partial_solve_wit_12_pure, stmt_partial_solve_wit_13_pure, stmt_partial_solve_wit_16_pure. The ordered per-split delta and strategy is in group_plan.json.
- init_pure: stmt_partial_solve_wit_23_pure, stmt_partial_solve_wit_25_pure, stmt_partial_solve_wit_27_pure, stmt_partial_solve_wit_28_pure, stmt_partial_solve_wit_29_pure. The ordered per-split delta and strategy is in group_plan.json.
- seq_pure_safety: stmt_safety_wit_11, stmt_partial_solve_wit_34_pure, stmt_partial_solve_wit_35_pure, stmt_partial_solve_wit_37_pure, stmt_partial_solve_wit_38_pure. The ordered per-split delta and strategy is in group_plan.json.
- block_return_pure: stmt_partial_solve_wit_41_pure, stmt_partial_solve_wit_43_pure, stmt_partial_solve_wit_44_pure, stmt_partial_solve_wit_79_pure, stmt_partial_solve_wit_83_pure, stmt_partial_solve_wit_84_pure. The ordered per-split delta and strategy is in group_plan.json.
- while_call_facts: stmt_partial_solve_wit_54_pure, stmt_partial_solve_wit_55_pure, stmt_partial_solve_wit_56_pure, stmt_partial_solve_wit_58_pure. The ordered per-split delta and strategy is in group_plan.json.
- while_if_finish_facts: stmt_partial_solve_wit_59_pure, stmt_partial_solve_wit_61_pure, stmt_partial_solve_wit_62_pure, if_stmt_partial_solve_wit_17_pure. The ordered per-split delta and strategy is in group_plan.json.
- stmt_open_if_payload: if_stmt_which_implies_wit_1, if_stmt_which_implies_wit_2, if_stmt_which_implies_wit_11, stmt_which_implies_wit_1, stmt_which_implies_wit_34, stmt_which_implies_wit_35. The ordered per-split delta and strategy is in group_plan.json.
- function_open_close: stmt_which_implies_wit_18, stmt_which_implies_wit_19, stmt_which_implies_wit_57, stmt_which_implies_wit_58. The ordered per-split delta and strategy is in group_plan.json.
- leaf_ast_shapes: stmt_which_implies_wit_2, stmt_which_implies_wit_6, stmt_which_implies_wit_12, stmt_which_implies_wit_16. The ordered per-split delta and strategy is in group_plan.json.
- control_ast_shapes: stmt_which_implies_wit_23, stmt_which_implies_wit_29, stmt_which_implies_wit_36. The ordered per-split delta and strategy is in group_plan.json.
- jump_return_ast_shapes: stmt_which_implies_wit_45, stmt_which_implies_wit_50, stmt_which_implies_wit_55. The ordered per-split delta and strategy is in group_plan.json.
- leaf_ast_close: stmt_which_implies_wit_5, stmt_which_implies_wit_11, stmt_which_implies_wit_15, stmt_which_implies_wit_22. The ordered per-split delta and strategy is in group_plan.json.
- control_ast_close: stmt_which_implies_wit_28, stmt_which_implies_wit_33, stmt_which_implies_wit_44. The ordered per-split delta and strategy is in group_plan.json.
- jump_return_ast_close: stmt_which_implies_wit_49, stmt_which_implies_wit_54, stmt_which_implies_wit_61. The ordered per-split delta and strategy is in group_plan.json.
- if_plan_transitions: if_stmt_which_implies_wit_7, if_stmt_which_implies_wit_8, if_stmt_which_implies_wit_9, if_stmt_which_implies_wit_10. The ordered per-split delta and strategy is in group_plan.json.
- expr_init_plan_transitions: stmt_which_implies_wit_8, stmt_which_implies_wit_9, stmt_which_implies_wit_20, stmt_which_implies_wit_59. The ordered per-split delta and strategy is in group_plan.json.
- seq_block_plan_transitions: stmt_which_implies_wit_26, stmt_which_implies_wit_27, stmt_which_implies_wit_31, stmt_which_implies_wit_32. The ordered per-split delta and strategy is in group_plan.json.
- while_plan_transitions: stmt_which_implies_wit_40, stmt_which_implies_wit_41, stmt_which_implies_wit_42. The ordered per-split delta and strategy is in group_plan.json.
- empty_jump_plans: stmt_which_implies_wit_4, stmt_which_implies_wit_14, stmt_which_implies_wit_47, stmt_which_implies_wit_52. The ordered per-split delta and strategy is in group_plan.json.
- empty_jump_bounds: stmt_which_implies_wit_3, stmt_which_implies_wit_13, stmt_which_implies_wit_46, stmt_which_implies_wit_51. The ordered per-split delta and strategy is in group_plan.json.

## Grouping Decisions
The second load review separates 32 final-return pure splits, 36 integer safety splits, constructor resource operations and list-plan transitions from mathematical capacity derivation. There are no single-witness groups. All groups stay within the hard 45-parent cap.
The sole >6-parent group is stmt_capacity (7 parents, 71 splits, difficulty 5). Every parent requires the same new structural statement length/count theorem or its constructor specialization. Keeping these capacity derivations together establishes that public theorem once without depending on sibling outputs. Its additional wf/temp/type conjuncts share the same constructor context and are short projections; they are not unrelated program phases. This is the expected critical path: one induction over all statement constructors, expression/list length interface, then constructor endpoint inequalities. It owns exactly one new public helper; splitting by branch would duplicate its proof or create unavailable cross-group dependencies. All independently provable final-result, call-boundary and safety work has already been moved out.
The other likely tails are leaf_ast_shapes (4 parents, 30 splits) and jump_return_ast_shapes (3 parents, 23 splits): all use finite kind discrimination and payload extraction, no mathematical helper. Control AST shapes have 17 splits and use the same small representation context. Their corresponding closing VCs are separate groups. All plan-transition groups have <=6 one-split parents and no helper. No permutation/sum/mask-clear fact is needed.

Group loads:
- repaired_plan_returns: 6 parents, 6 splits, 0 helpers, difficulty 2.
- stmt_capacity: 7 parents, 71 splits, 1 helpers, difficulty 5.
- if_safety_prefix: 6 parents, 12 splits, 0 helpers, difficulty 2.
- if_safety_suffix: 5 parents, 10 splits, 0 helpers, difficulty 2.
- while_safety: 6 parents, 12 splits, 0 helpers, difficulty 2.
- return_leaf_facts: 4 parents, 16 splits, 0 helpers, difficulty 1.
- return_recursive_facts: 4 parents, 16 splits, 0 helpers, difficulty 2.
- expr_decl_pure: 5 parents, 5 splits, 0 helpers, difficulty 1.
- init_pure: 5 parents, 5 splits, 0 helpers, difficulty 1.
- seq_pure_safety: 5 parents, 7 splits, 0 helpers, difficulty 2.
- block_return_pure: 6 parents, 6 splits, 0 helpers, difficulty 1.
- while_call_facts: 4 parents, 10 splits, 0 helpers, difficulty 2.
- while_if_finish_facts: 4 parents, 7 splits, 0 helpers, difficulty 2.
- stmt_open_if_payload: 6 parents, 4 splits, 0 helpers, difficulty 2.
- function_open_close: 4 parents, 2 splits, 0 helpers, difficulty 1.
- leaf_ast_shapes: 4 parents, 30 splits, 0 helpers, difficulty 3.
- control_ast_shapes: 3 parents, 17 splits, 0 helpers, difficulty 3.
- jump_return_ast_shapes: 3 parents, 23 splits, 0 helpers, difficulty 3.
- leaf_ast_close: 4 parents, 4 splits, 0 helpers, difficulty 2.
- control_ast_close: 3 parents, 3 splits, 0 helpers, difficulty 2.
- jump_return_ast_close: 3 parents, 3 splits, 0 helpers, difficulty 2.
- if_plan_transitions: 4 parents, 4 splits, 0 helpers, difficulty 2.
- expr_init_plan_transitions: 4 parents, 4 splits, 0 helpers, difficulty 2.
- seq_block_plan_transitions: 4 parents, 4 splits, 0 helpers, difficulty 2.
- while_plan_transitions: 3 parents, 3 splits, 0 helpers, difficulty 2.
- empty_jump_plans: 4 parents, 4 splits, 0 helpers, difficulty 1.
- empty_jump_bounds: 4 parents, 8 splits, 0 helpers, difficulty 1.

## Risks or Blockers
No definite blocker. The mathematical length/count theorem is the principal proof risk, with no missing hypotheses: constructor equations give the same code and count sizes, including arbitrary loop targets. Avoid repeated rewriting of s = Constructor(projections s), which expands projections exponentially; destruct s or rewrite once and reduce projections. No witness reuse was analyzed.
