# VC checking decision summary

## Outcome

All 176 current top-level VCs are assigned. All 333 generated split goals were judged provable from their actual contexts before proof modes and strategies were chosen. The 164 split-bearing VCs use aggressive_pre_process; the 12 unsplit VCs use LLM_pre_process. This is a proofability analysis, not a completed Rocq proof.

## Structural Blocker Scan

- Status: passed
- Top-level VCs scanned: 176
- No-split VCs checked first: 12
- Definite blockers: 0

The initial scan checked every whole-VC address boundary and independently bound scalar against its entry-state counterpart. All node-open witnesses expose addresses from cm_expr_rep; node-closing witnesses retain the seven field cells and payload/children. No remaining top-level VC binds an unconstrained current scalar alongside its @pre counterpart. Emitter plan transitions preserve emitter/out/capacity and relate code indices by constructor equations. The no-split checks were the six constructor node openings, dispatch node opening, and five simple-view conversions.

## Annotation Comparison Review

The current which_implies witnesses 2, 4, 6, 19, 21 of cm_emit_expr have identical two-disjunct boundaries after pc/temp equality substitution. Their general code uses pc_pre/temp_pre; no independent current pc/temp binders remain. The CONST, STRING, VAR, SIZEOF and GETC guards force the respective constructors, whose code does not depend on pc/temp. The introduced simple view preserves source identity and the exact code list, including arbitrary lvalue. The C premises pc==pc@pre and temp==temp@pre are established by the unchanged local stores at these five dispatch points; the generated establishing obligations retain those same stores and normalize the equalities reflexively. The comparison introduces no case-lib assumption and no new resource. Auto blocks were inspected as generated text, not treated as proof evidence (they still contain generated Admitted placeholders). These five VCs occupy the first coherent group; none requires a substantial new mathematical lemma.

## Proof-Mode Decisions

The split-first pass covered every generated split in manual declaration order. No split required recovering a discarded existential or spatial fact from its parent. Arithmetic splits retain parent/child wf, representable counts, shape and branch guards; spatial splits retain the needed shape/kind and original ownership. Thus all 333 are provable. Only the 12 no-split whole VCs were then judged for whole-goal mode; constructor unfolding and existential view selection suffice. No whole-goal proof strategy was used for any aggressive parent.

## Common Proof Patterns

- OPEN/FOLD: expose or rebuild cm_expr_node using the same xa, xb and xargs and seven field cells; constructor payload equations preserve the children and zero-address facts.
- SIMPLE: discriminate expression kind, choose its unique simple-view constructor, and reduce exact general/simple code under the lvalue test.
- RESULT/PLAN: use the constructor code equation, branch guards, scalar equalities and append associativity to normalize the emitter plan index. RESULT also cancels the program/function/AST frame; PLAN only changes todo notation.
- FACT: project wf/count structure and constructor observations. Type-reference preservation needs the planned public induction theorem; temporary offset bounds use existing slot-size nonnegativity and linear arithmetic.
- BOUND: use code/count length equality, nonnegative prefix lengths, parent end-pc bounds and max-based temporary budgets. Planned public temporary nonnegativity handles shifted child scratch bounds in index/assignment/ordinary-binary groups; unary and short-circuit budgets only need constructor equations and max projections.
- CONST/SHAPE/CALL/GUARD: closed reduction, constructor discrimination, substitution into an existing call bound, or branch equality respectively. These do not introduce helpers.

## VC Deltas

- proof_of_cm_emit_intrinsic_expr_return_wit_1: 1 splits; RESULT.
- proof_of_cm_emit_intrinsic_expr_return_wit_2: 1 splits; RESULT.
- proof_of_cm_emit_intrinsic_expr_return_wit_3: 1 splits; RESULT.
- proof_of_cm_emit_intrinsic_expr_return_wit_4: 1 splits; RESULT.
- proof_of_cm_emit_intrinsic_expr_return_wit_5: 1 splits; RESULT.
- proof_of_cm_emit_intrinsic_expr_return_wit_6: 1 splits; RESULT.
- proof_of_cm_emit_intrinsic_expr_partial_solve_wit_7_pure: 2 splits; CONST; (2 = (tvm_opcode_code (TVMDupOp))) / ((tvm_opcode_code (TVMDupOp)) <> 22).
- proof_of_cm_emit_intrinsic_expr_partial_solve_wit_8_pure: 2 splits; CONST; (25 = (tvm_opcode_code (TVMPutcOp))) / ((tvm_opcode_code (TVMPutcOp)) <> 22).
- proof_of_cm_emit_intrinsic_expr_partial_solve_wit_13_pure: 2 splits; CONST; (2 = (tvm_opcode_code (TVMDupOp))) / ((tvm_opcode_code (TVMDupOp)) <> 22).
- proof_of_cm_emit_intrinsic_expr_partial_solve_wit_14_pure: 2 splits; CONST; (26 = (tvm_opcode_code (TVMPutiOp))) / ((tvm_opcode_code (TVMPutiOp)) <> 22).
- proof_of_cm_emit_intrinsic_expr_partial_solve_wit_19_pure: 2 splits; CONST; (1 = (cm_type_encode (CMCharTy))) / (cm_type_code_wf CMCharTy ).
- proof_of_cm_emit_intrinsic_expr_partial_solve_wit_20_pure: 2 splits; CONST; (27 = (tvm_opcode_code (TVMHaltOp))) / ((tvm_opcode_code (TVMHaltOp)) <> 22).
- proof_of_cm_emit_intrinsic_expr_which_implies_wit_1: whole goal; OPEN.
- proof_of_cm_emit_intrinsic_expr_which_implies_wit_2: 9 splits; FACT.
- proof_of_cm_emit_intrinsic_expr_which_implies_wit_3: 1 splits; SHAPE; (cm_expr_shape e (CMPutcE ((cm_expr_child (e))) ((cm_expr_type (e)))) ).
- proof_of_cm_emit_intrinsic_expr_which_implies_wit_4: 1 splits; PLAN.
- proof_of_cm_emit_intrinsic_expr_which_implies_wit_5: 2 splits; BOUND; (cm_i32_code_count (pc + (Zlength ((cm_expr_code_for (policy) (p) (fid) (pc) (temp) ((cm_expr_child (e))) (0)))) ) ) / ((temp + (cm_expr_temps_for ((cm_expr_child (e))) (0)) ) <= temp_limit).
- proof_of_cm_emit_intrinsic_expr_which_implies_wit_6: 1 splits; SHAPE; (cm_expr_shape e (CMPutiE ((cm_expr_child (e))) ((cm_expr_type (e)))) ).
- proof_of_cm_emit_intrinsic_expr_which_implies_wit_7: 1 splits; PLAN.
- proof_of_cm_emit_intrinsic_expr_which_implies_wit_8: 2 splits; BOUND; (cm_i32_code_count (pc + (Zlength ((cm_expr_code_for (policy) (p) (fid) (pc) (temp) ((cm_expr_child (e))) (0)))) ) ) / ((temp + (cm_expr_temps_for ((cm_expr_child (e))) (0)) ) <= temp_limit).
- proof_of_cm_emit_intrinsic_expr_which_implies_wit_9: 1 splits; SHAPE; (cm_expr_shape e (CMExitE ((cm_expr_child (e))) ((cm_expr_type (e)))) ).
- proof_of_cm_emit_intrinsic_expr_which_implies_wit_10: 1 splits; PLAN.
- proof_of_cm_emit_intrinsic_expr_which_implies_wit_11: 2 splits; BOUND; (cm_i32_code_count (pc + (Zlength ((cm_expr_code_for (policy) (p) (fid) (pc) (temp) ((cm_expr_child (e))) (0)))) ) ) / ((temp + (cm_expr_temps_for ((cm_expr_child (e))) (0)) ) <= temp_limit).
- proof_of_cm_emit_intrinsic_expr_which_implies_wit_12: 1 splits; FOLD.
- proof_of_cm_emit_unary_expr_return_wit_1: 1 splits; RESULT.
- proof_of_cm_emit_unary_expr_return_wit_2: 1 splits; RESULT.
- proof_of_cm_emit_unary_expr_return_wit_3: 1 splits; RESULT.
- proof_of_cm_emit_unary_expr_return_wit_4: 1 splits; RESULT.
- proof_of_cm_emit_unary_expr_return_wit_5: 1 splits; RESULT.
- proof_of_cm_emit_unary_expr_return_wit_6: 1 splits; RESULT.
- proof_of_cm_emit_unary_expr_return_wit_7: 1 splits; RESULT.
- proof_of_cm_emit_unary_expr_partial_solve_wit_1_pure: 2 splits; SHAPE; (cm_expr_shape e e ) / (cm_expr_shape e e ).
- proof_of_cm_emit_unary_expr_partial_solve_wit_3_pure: 2 splits; CALL/SHAPE; (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((CMUnaryE (2) (arg_) (ty_))) (0)))) ) ) / (cm_expr_shape (CMUnaryE (2) (arg_) (ty_)) (CMUnaryE (2) (arg_) ((cm_expr_type ((CMUnaryE (2) (arg_) (ty_)))))) ).
- proof_of_cm_emit_unary_expr_partial_solve_wit_7_pure: 2 splits; CALL/SHAPE; (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((CMUnaryE (2) (arg_) (ty_))) (lvalue_pre)))) ) ) / (cm_expr_shape (CMUnaryE (2) (arg_) (ty_)) (CMUnaryE (2) (arg_) ((cm_expr_type ((CMUnaryE (2) (arg_) (ty_)))))) ).
- proof_of_cm_emit_unary_expr_partial_solve_wit_10_pure: 2 splits; CALL/SHAPE; (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((CMUnaryE (3) (arg_) (ty_))) (0)))) ) ) / (cm_expr_shape (CMUnaryE (3) (arg_) (ty_)) (CMUnaryE (3) (arg_) ((cm_expr_type ((CMUnaryE (3) (arg_) (ty_)))))) ).
- proof_of_cm_emit_unary_expr_partial_solve_wit_13_pure: 2 splits; CALL/SHAPE; (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((CMUnaryE (0) (arg_) (ty_))) (0)))) ) ) / (cm_expr_shape (CMUnaryE (0) (arg_) (ty_)) (CMUnaryE (0) (arg_) ((cm_expr_type ((CMUnaryE (0) (arg_) (ty_)))))) ).
- proof_of_cm_emit_unary_expr_partial_solve_wit_16_pure: 2 splits; CONST; (0 = (tvm_opcode_code (TVMPushOp))) / ((tvm_opcode_code (TVMPushOp)) <> 22).
- proof_of_cm_emit_unary_expr_partial_solve_wit_17_pure: 2 splits; CONST; (10 = (tvm_opcode_code (TVMMulOp))) / ((tvm_opcode_code (TVMMulOp)) <> 22).
- proof_of_cm_emit_unary_expr_partial_solve_wit_21_pure: 2 splits; CONST; (0 = (tvm_opcode_code (TVMPushOp))) / ((tvm_opcode_code (TVMPushOp)) <> 22).
- proof_of_cm_emit_unary_expr_partial_solve_wit_22_pure: 2 splits; CONST; (13 = (tvm_opcode_code (TVMEqOp))) / ((tvm_opcode_code (TVMEqOp)) <> 22).
- proof_of_cm_emit_unary_expr_partial_solve_wit_25_pure: 1 splits; SHAPE; (cm_expr_shape (CMUnaryE (0) (arg_) (ty_)) (CMUnaryE (0) (arg_) ((cm_expr_type ((CMUnaryE (0) (arg_) (ty_)))))) ).
- proof_of_cm_emit_unary_expr_partial_solve_wit_26_pure: 1 splits; SHAPE; (cm_expr_shape (CMUnaryE (3) (arg_) (ty_)) (CMUnaryE (3) (arg_) ((cm_expr_type ((CMUnaryE (3) (arg_) (ty_)))))) ).
- proof_of_cm_emit_unary_expr_partial_solve_wit_27_pure: 1 splits; SHAPE; (cm_expr_shape (CMUnaryE (3) (arg_) (ty_)) (CMUnaryE (3) (arg_) ((cm_expr_type ((CMUnaryE (3) (arg_) (ty_)))))) ).
- proof_of_cm_emit_unary_expr_partial_solve_wit_28_pure: 1 splits; SHAPE; (cm_expr_shape (CMUnaryE (2) (arg_) (ty_)) (CMUnaryE (2) (arg_) ((cm_expr_type ((CMUnaryE (2) (arg_) (ty_)))))) ).
- proof_of_cm_emit_unary_expr_partial_solve_wit_29_pure: 1 splits; SHAPE; (cm_expr_shape (CMUnaryE (2) (arg_) (ty_)) (CMUnaryE (2) (arg_) ((cm_expr_type ((CMUnaryE (2) (arg_) (ty_)))))) ).
- proof_of_cm_emit_unary_expr_which_implies_wit_1: whole goal; OPEN.
- proof_of_cm_emit_unary_expr_which_implies_wit_2: 13 splits; FACT.
- proof_of_cm_emit_unary_expr_which_implies_wit_3: 1 splits; PLAN.
- proof_of_cm_emit_unary_expr_which_implies_wit_4: 2 splits; BOUND; (cm_i32_code_count (pc + (Zlength ((cm_expr_code_for (policy) (p) (fid) (pc) (temp) (arg_) (0)))) ) ) / ((temp + (cm_expr_temps_for (arg_) (0)) ) <= temp_limit).
- proof_of_cm_emit_unary_expr_which_implies_wit_5: 1 splits; PLAN.
- proof_of_cm_emit_unary_expr_which_implies_wit_6: 2 splits; BOUND; (cm_i32_code_count (pc + (Zlength ((cm_expr_code_for (policy) (p) (fid) (pc) (temp) (arg_) (0)))) ) ) / ((temp + (cm_expr_temps_for (arg_) (0)) ) <= temp_limit).
- proof_of_cm_emit_unary_expr_which_implies_wit_7: 1 splits; PLAN.
- proof_of_cm_emit_unary_expr_which_implies_wit_8: 2 splits; BOUND; (cm_i32_code_count (pc + (Zlength ((cm_expr_code_for (policy) (p) (fid) (pc) (temp) (arg_) (1)))) ) ) / ((temp + (cm_expr_temps_for (arg_) (1)) ) <= temp_limit).
- proof_of_cm_emit_unary_expr_which_implies_wit_9: 1 splits; PLAN.
- proof_of_cm_emit_unary_expr_which_implies_wit_10: 2 splits; BOUND; (cm_i32_code_count (pc + (Zlength ((cm_expr_code_for (policy) (p) (fid) (pc) (temp) (arg_) (0)))) ) ) / ((temp + (cm_expr_temps_for (arg_) (0)) ) <= temp_limit).
- proof_of_cm_emit_unary_expr_which_implies_wit_11: 1 splits; PLAN.
- proof_of_cm_emit_unary_expr_which_implies_wit_12: 2 splits; BOUND; (cm_i32_code_count (pc + (Zlength ((cm_expr_code_for (policy) (p) (fid) (pc) (temp) (arg_) (0)))) ) ) / ((temp + (cm_expr_temps_for (arg_) (0)) ) <= temp_limit).
- proof_of_cm_emit_unary_expr_which_implies_wit_13: 1 splits; FOLD.
- proof_of_cm_emit_index_expr_safety_wit_2: 2 splits; BOUND; ((pc_pre + ((cm_rvalue_code_count (policy) (p) (fid_pre) (left_)) + 5 ) ) <= INT_MAX) / ((INT_MIN) <= (pc_pre + ((cm_rvalue_code_count (policy) (p) (fid_pre) (left_)) + 5 ) )).
- proof_of_cm_emit_index_expr_safety_wit_3: 2 splits; BOUND; (((cm_rvalue_code_count (policy) (p) (fid_pre) (left_)) + 5 ) <= INT_MAX) / ((INT_MIN) <= ((cm_rvalue_code_count (policy) (p) (fid_pre) (left_)) + 5 )).
- proof_of_cm_emit_index_expr_safety_wit_5: 2 splits; BOUND; ((temp_pre + 1 ) <= INT_MAX) / ((INT_MIN) <= (temp_pre + 1 )).
- proof_of_cm_emit_index_expr_return_wit_1: 1 splits; RESULT.
- proof_of_cm_emit_index_expr_return_wit_2: 1 splits; RESULT.
- proof_of_cm_emit_index_expr_partial_solve_wit_1_pure: 2 splits; SHAPE; (cm_expr_shape e e ) / (cm_expr_shape e e ).
- proof_of_cm_emit_index_expr_partial_solve_wit_11_pure: 2 splits; CONST; (0 = (tvm_opcode_code (TVMPushOp))) / ((tvm_opcode_code (TVMPushOp)) <> 22).
- proof_of_cm_emit_index_expr_partial_solve_wit_12_pure: 2 splits; CONST; (10 = (tvm_opcode_code (TVMMulOp))) / ((tvm_opcode_code (TVMMulOp)) <> 22).
- proof_of_cm_emit_index_expr_partial_solve_wit_14_pure: 2 splits; CONST; (8 = (tvm_opcode_code (TVMAddOp))) / ((tvm_opcode_code (TVMAddOp)) <> 22).
- proof_of_cm_emit_index_expr_which_implies_wit_1: whole goal; OPEN.
- proof_of_cm_emit_index_expr_which_implies_wit_2: 17 splits; FACT.
- proof_of_cm_emit_index_expr_which_implies_wit_3: 1 splits; PLAN.
- proof_of_cm_emit_index_expr_which_implies_wit_4: 2 splits; BOUND; (cm_i32_code_count (pc + (Zlength ((cm_expr_code_for (policy) (p) (fid) (pc) (temp) (left_) (0)))) ) ) / ((temp + (cm_expr_temps_for (left_) (0)) ) <= temp_limit).
- proof_of_cm_emit_index_expr_which_implies_wit_5: 4 splits; BOUND.
- proof_of_cm_emit_index_expr_which_implies_wit_6: 1 splits; PLAN.
- proof_of_cm_emit_index_expr_which_implies_wit_7: 1 splits; FOLD.
- proof_of_cm_emit_assignment_expr_safety_wit_2: 2 splits; BOUND; ((pc_pre + ((cm_lvalue_code_count (policy) (p) (fid_pre) (left_)) + 5 ) ) <= INT_MAX) / ((INT_MIN) <= (pc_pre + ((cm_lvalue_code_count (policy) (p) (fid_pre) (left_)) + 5 ) )).
- proof_of_cm_emit_assignment_expr_safety_wit_3: 2 splits; BOUND; (((cm_lvalue_code_count (policy) (p) (fid_pre) (left_)) + 5 ) <= INT_MAX) / ((INT_MIN) <= ((cm_lvalue_code_count (policy) (p) (fid_pre) (left_)) + 5 )).
- proof_of_cm_emit_assignment_expr_safety_wit_5: 2 splits; BOUND; ((temp_pre + 1 ) <= INT_MAX) / ((INT_MIN) <= (temp_pre + 1 )).
- proof_of_cm_emit_assignment_expr_return_wit_1: 1 splits; RESULT.
- proof_of_cm_emit_assignment_expr_return_wit_2: 1 splits; RESULT.
- proof_of_cm_emit_assignment_expr_partial_solve_wit_1_pure: 2 splits; SHAPE; (cm_expr_shape e e ) / (cm_expr_shape e e ).
- proof_of_cm_emit_assignment_expr_which_implies_wit_1: whole goal; OPEN.
- proof_of_cm_emit_assignment_expr_which_implies_wit_2: 17 splits; FACT.
- proof_of_cm_emit_assignment_expr_which_implies_wit_3: 1 splits; PLAN.
- proof_of_cm_emit_assignment_expr_which_implies_wit_4: 2 splits; BOUND; (cm_i32_code_count (pc + (Zlength ((cm_expr_code_for (policy) (p) (fid) (pc) (temp) (left_) (1)))) ) ) / ((temp + (cm_expr_temps_for (left_) (1)) ) <= temp_limit).
- proof_of_cm_emit_assignment_expr_which_implies_wit_5: 4 splits; BOUND.
- proof_of_cm_emit_assignment_expr_which_implies_wit_6: 1 splits; FOLD.
- proof_of_cm_emit_binary_expr_safety_wit_23: 2 splits; BOUND; ((pc_pre + ((cm_rvalue_code_count (policy) (p) (fid_pre) (left_)) + 1 ) ) <= INT_MAX) / ((INT_MIN) <= (pc_pre + ((cm_rvalue_code_count (policy) (p) (fid_pre) (left_)) + 1 ) )).
- proof_of_cm_emit_binary_expr_safety_wit_24: 2 splits; BOUND; (((cm_rvalue_code_count (policy) (p) (fid_pre) (left_)) + 1 ) <= INT_MAX) / ((INT_MIN) <= ((cm_rvalue_code_count (policy) (p) (fid_pre) (left_)) + 1 )).
- proof_of_cm_emit_binary_expr_safety_wit_26: 2 splits; BOUND; ((pc_pre + ((cm_rvalue_code_count (policy) (p) (fid_pre) (left_)) + 1 ) ) <= INT_MAX) / ((INT_MIN) <= (pc_pre + ((cm_rvalue_code_count (policy) (p) (fid_pre) (left_)) + 1 ) )).
- proof_of_cm_emit_binary_expr_safety_wit_27: 2 splits; BOUND; (((cm_rvalue_code_count (policy) (p) (fid_pre) (left_)) + 1 ) <= INT_MAX) / ((INT_MIN) <= ((cm_rvalue_code_count (policy) (p) (fid_pre) (left_)) + 1 )).
- proof_of_cm_emit_binary_expr_safety_wit_66: 2 splits; BOUND; ((pc_pre + ((cm_rvalue_code_count (policy) (p) (fid_pre) (left_)) + 5 ) ) <= INT_MAX) / ((INT_MIN) <= (pc_pre + ((cm_rvalue_code_count (policy) (p) (fid_pre) (left_)) + 5 ) )).
- proof_of_cm_emit_binary_expr_safety_wit_67: 2 splits; BOUND; (((cm_rvalue_code_count (policy) (p) (fid_pre) (left_)) + 5 ) <= INT_MAX) / ((INT_MIN) <= ((cm_rvalue_code_count (policy) (p) (fid_pre) (left_)) + 5 )).
- proof_of_cm_emit_binary_expr_safety_wit_69: 2 splits; BOUND; ((temp_pre + 1 ) <= INT_MAX) / ((INT_MIN) <= (temp_pre + 1 )).
- proof_of_cm_emit_binary_expr_return_wit_1: 1 splits; RESULT.
- proof_of_cm_emit_binary_expr_return_wit_2: 1 splits; RESULT.
- proof_of_cm_emit_binary_expr_return_wit_3: 1 splits; RESULT.
- proof_of_cm_emit_binary_expr_return_wit_4: 1 splits; RESULT.
- proof_of_cm_emit_binary_expr_partial_solve_wit_1_pure: 2 splits; SHAPE; (cm_expr_shape e e ) / (cm_expr_shape e e ).
- proof_of_cm_emit_binary_expr_partial_solve_wit_5_pure: 2 splits; CALL/SHAPE; (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((CMBinaryE (1) (left_) (right_) (ty_))) (0)))) ) ) / (cm_expr_shape (CMBinaryE (1) (left_) (right_) (ty_)) (CMBinaryE (1) (left_) (right_) ((cm_expr_type ((CMBinaryE (1) (left_) (right_) (ty_)))))) ).
- proof_of_cm_emit_binary_expr_partial_solve_wit_6_pure: 2 splits; CALL/SHAPE; (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((CMBinaryE (0) (left_) (right_) (ty_))) (0)))) ) ) / (cm_expr_shape (CMBinaryE (0) (left_) (right_) (ty_)) (CMBinaryE (0) (left_) (right_) ((cm_expr_type ((CMBinaryE (0) (left_) (right_) (ty_)))))) ).
- proof_of_cm_emit_binary_expr_partial_solve_wit_11_pure: 4 splits; CONST.
- proof_of_cm_emit_binary_expr_partial_solve_wit_12_pure: 4 splits; CONST.
- proof_of_cm_emit_binary_expr_partial_solve_wit_17_pure: 2 splits; CONST; (0 = (tvm_opcode_code (TVMPushOp))) / ((tvm_opcode_code (TVMPushOp)) <> 22).
- proof_of_cm_emit_binary_expr_partial_solve_wit_18_pure: 2 splits; CONST; (0 = (tvm_opcode_code (TVMPushOp))) / ((tvm_opcode_code (TVMPushOp)) <> 22).
- proof_of_cm_emit_binary_expr_partial_solve_wit_19_pure: 2 splits; CONST; (14 = (tvm_opcode_code (TVMNeOp))) / ((tvm_opcode_code (TVMNeOp)) <> 22).
- proof_of_cm_emit_binary_expr_partial_solve_wit_20_pure: 2 splits; CONST; (14 = (tvm_opcode_code (TVMNeOp))) / ((tvm_opcode_code (TVMNeOp)) <> 22).
- proof_of_cm_emit_binary_expr_partial_solve_wit_21_pure: 2 splits; CONST; (19 = (tvm_opcode_code (TVMJmpOp))) / ((tvm_opcode_code (TVMJmpOp)) <> 22).
- proof_of_cm_emit_binary_expr_partial_solve_wit_22_pure: 2 splits; CONST; (19 = (tvm_opcode_code (TVMJmpOp))) / ((tvm_opcode_code (TVMJmpOp)) <> 22).
- proof_of_cm_emit_binary_expr_partial_solve_wit_23_pure: 4 splits; CONST.
- proof_of_cm_emit_binary_expr_partial_solve_wit_24_pure: 4 splits; CONST.
- proof_of_cm_emit_binary_expr_partial_solve_wit_25_pure: 2 splits; CONST; (0 = (tvm_opcode_code (TVMPushOp))) / ((tvm_opcode_code (TVMPushOp)) <> 22).
- proof_of_cm_emit_binary_expr_partial_solve_wit_26_pure: 2 splits; CONST; (0 = (tvm_opcode_code (TVMPushOp))) / ((tvm_opcode_code (TVMPushOp)) <> 22).
- proof_of_cm_emit_binary_expr_partial_solve_wit_36_pure: 1 splits; SHAPE; (cm_expr_shape (CMBinaryE (1) (left_) (right_) (ty_)) (CMBinaryE (1) (left_) (right_) ((cm_expr_type ((CMBinaryE (1) (left_) (right_) (ty_)))))) ).
- proof_of_cm_emit_binary_expr_partial_solve_wit_37_pure: 1 splits; SHAPE; (cm_expr_shape (CMBinaryE (0) (left_) (right_) (ty_)) (CMBinaryE (0) (left_) (right_) ((cm_expr_type ((CMBinaryE (0) (left_) (right_) (ty_)))))) ).
- proof_of_cm_emit_binary_expr_which_implies_wit_1: whole goal; OPEN.
- proof_of_cm_emit_binary_expr_which_implies_wit_2: 18 splits; FACT.
- proof_of_cm_emit_binary_expr_which_implies_wit_3: 1 splits; CONST.
- proof_of_cm_emit_binary_expr_which_implies_wit_4: 2 splits; BOUND; (cm_i32_code_count (pc + (Zlength ((cm_expr_code_for (policy) (p) (fid) (pc) (temp) (left_) (0)))) ) ) / ((temp + (cm_expr_temps_for (left_) (0)) ) <= temp_limit).
- proof_of_cm_emit_binary_expr_which_implies_wit_5: 3 splits; BOUND.
- proof_of_cm_emit_binary_expr_which_implies_wit_6: 3 splits; BOUND.
- proof_of_cm_emit_binary_expr_which_implies_wit_7: 1 splits; PLAN.
- proof_of_cm_emit_binary_expr_which_implies_wit_8: 1 splits; PLAN.
- proof_of_cm_emit_binary_expr_which_implies_wit_9: 2 splits; BOUND; (cm_i32_code_count (pc + (Zlength ((cm_expr_code_for (policy) (p) (fid) (pc) (temp) (left_) (0)))) ) ) / ((temp + (cm_expr_temps_for (left_) (0)) ) <= temp_limit).
- proof_of_cm_emit_binary_expr_which_implies_wit_10: 4 splits; BOUND.
- proof_of_cm_emit_binary_expr_which_implies_wit_11: 1 splits; FOLD.
- proof_of_cm_emit_member_expr_return_wit_1: 1 splits; RESULT.
- proof_of_cm_emit_member_expr_return_wit_2: 1 splits; RESULT.
- proof_of_cm_emit_member_expr_return_wit_3: 1 splits; RESULT.
- proof_of_cm_emit_member_expr_partial_solve_wit_1_pure: 2 splits; SHAPE; (cm_expr_shape e e ) / (cm_expr_shape e e ).
- proof_of_cm_emit_member_expr_partial_solve_wit_9_pure: 2 splits; CONST; (0 = (tvm_opcode_code (TVMPushOp))) / ((tvm_opcode_code (TVMPushOp)) <> 22).
- proof_of_cm_emit_member_expr_partial_solve_wit_10_pure: 2 splits; CONST; (8 = (tvm_opcode_code (TVMAddOp))) / ((tvm_opcode_code (TVMAddOp)) <> 22).
- proof_of_cm_emit_member_expr_partial_solve_wit_11_pure: 1 splits; GUARD; (0 = (cm_member_array_code (p) ((cm_expr_type (arg_))) (mid_))).
- proof_of_cm_emit_member_expr_which_implies_wit_1: whole goal; OPEN.
- proof_of_cm_emit_member_expr_which_implies_wit_2: 16 splits; FACT.
- proof_of_cm_emit_member_expr_which_implies_wit_3: 1 splits; PLAN.
- proof_of_cm_emit_member_expr_which_implies_wit_4: 2 splits; BOUND; (cm_i32_code_count (pc + (Zlength ((cm_expr_code_for (policy) (p) (fid) (pc) (temp) (arg_) (0)))) ) ) / ((temp + (cm_expr_temps_for (arg_) (0)) ) <= temp_limit).
- proof_of_cm_emit_member_expr_which_implies_wit_5: 1 splits; PLAN.
- proof_of_cm_emit_member_expr_which_implies_wit_6: 1 splits; FOLD.
- proof_of_cm_emit_expr_return_wit_1: 1 splits; RESULT.
- proof_of_cm_emit_expr_return_wit_2: 1 splits; RESULT.
- proof_of_cm_emit_expr_return_wit_3: 1 splits; RESULT.
- proof_of_cm_emit_expr_return_wit_10: 1 splits; RESULT.
- proof_of_cm_emit_expr_return_wit_11: 1 splits; RESULT.
- proof_of_cm_emit_expr_partial_solve_wit_13_pure: 1 splits; SHAPE; (e = (CMAssignE ((cm_expr_child (e))) ((cm_expr_second (e))) ((cm_expr_type (e))))).
- proof_of_cm_emit_expr_partial_solve_wit_16_pure: 1 splits; SHAPE; (e = (CMBinaryE ((cm_rep_expr_op (e))) ((cm_expr_child (e))) ((cm_expr_second (e))) ((cm_expr_type (e))))).
- proof_of_cm_emit_expr_partial_solve_wit_19_pure: 1 splits; SHAPE; (e = (CMUnaryE ((cm_rep_expr_op (e))) ((cm_expr_child (e))) ((cm_expr_type (e))))).
- proof_of_cm_emit_expr_partial_solve_wit_22_pure: 1 splits; SHAPE; (e = (CMIndexE ((cm_expr_child (e))) ((cm_expr_second (e))) ((cm_expr_type (e))))).
- proof_of_cm_emit_expr_partial_solve_wit_25_pure: 1 splits; SHAPE; (e = (CMMemberE ((cm_expr_child (e))) ((cm_rep_expr_value (e))) ((cm_expr_type (e))))).
- proof_of_cm_emit_expr_which_implies_wit_1: whole goal; OPEN.
- proof_of_cm_emit_expr_which_implies_wit_2: whole goal; SIMPLE.
- proof_of_cm_emit_expr_which_implies_wit_3: 1 splits; FOLD.
- proof_of_cm_emit_expr_which_implies_wit_4: whole goal; SIMPLE.
- proof_of_cm_emit_expr_which_implies_wit_5: 1 splits; FOLD.
- proof_of_cm_emit_expr_which_implies_wit_6: whole goal; SIMPLE.
- proof_of_cm_emit_expr_which_implies_wit_7: 1 splits; FOLD.
- proof_of_cm_emit_expr_which_implies_wit_8: 1 splits; SHAPE; (cm_expr_shape e (CMAssignE ((cm_expr_child (e))) ((cm_expr_second (e))) ((cm_expr_type (e)))) ).
- proof_of_cm_emit_expr_which_implies_wit_9: 1 splits; FOLD.
- proof_of_cm_emit_expr_which_implies_wit_10: 1 splits; SHAPE; (cm_expr_shape e (CMBinaryE ((cm_rep_expr_op (e))) ((cm_expr_child (e))) ((cm_expr_second (e))) ((cm_expr_type (e)))) ).
- proof_of_cm_emit_expr_which_implies_wit_11: 1 splits; FOLD.
- proof_of_cm_emit_expr_which_implies_wit_12: 1 splits; SHAPE; (cm_expr_shape e (CMUnaryE ((cm_rep_expr_op (e))) ((cm_expr_child (e))) ((cm_expr_type (e)))) ).
- proof_of_cm_emit_expr_which_implies_wit_13: 1 splits; FOLD.
- proof_of_cm_emit_expr_which_implies_wit_14: 1 splits; SHAPE; (cm_expr_shape e (CMIndexE ((cm_expr_child (e))) ((cm_expr_second (e))) ((cm_expr_type (e)))) ).
- proof_of_cm_emit_expr_which_implies_wit_15: 1 splits; FOLD.
- proof_of_cm_emit_expr_which_implies_wit_16: 1 splits; SHAPE; (cm_expr_shape e (CMMemberE ((cm_expr_child (e))) ((cm_rep_expr_value (e))) ((cm_expr_type (e)))) ).
- proof_of_cm_emit_expr_which_implies_wit_17: 1 splits; FOLD.
- proof_of_cm_emit_expr_which_implies_wit_18: 1 splits; FOLD.
- proof_of_cm_emit_expr_which_implies_wit_19: whole goal; SIMPLE.
- proof_of_cm_emit_expr_which_implies_wit_20: 1 splits; FOLD.
- proof_of_cm_emit_expr_which_implies_wit_21: whole goal; SIMPLE.
- proof_of_cm_emit_expr_which_implies_wit_22: 1 splits; FOLD.
- proof_of_cm_emit_expr_which_implies_wit_23: 1 splits; SHAPE; (cm_intrinsic_expr e ).
- proof_of_cm_emit_expr_which_implies_wit_24: 1 splits; FOLD.
- proof_of_cm_emit_expr_which_implies_wit_25: 1 splits; SHAPE; (cm_intrinsic_expr e ).
- proof_of_cm_emit_expr_which_implies_wit_26: 1 splits; FOLD.
- proof_of_cm_emit_expr_which_implies_wit_27: 1 splits; SHAPE; (cm_intrinsic_expr e ).
- proof_of_cm_emit_expr_which_implies_wit_28: 1 splits; FOLD.

## Grouping Decisions

The first grouping follows constructor family, exact plan transformation, node ownership, recursive bounds, and closed observations. A second review separates final emitted-prefix proofs from independently provable child-transition/safety facts. All groups contain 2–6 top-level witnesses; there are no singleton or oversized groups. All workers remain independent; public helper publication is optional acceleration and never a sibling dependency.

Expected critical path: constructor_facts_a/b/c each owns its own public expression type-reference lemma, keeping 22/34/34 aggressive splits and the same typed-program context together. The source induction is the dominant risk; its leaf/binding/member/call cases must consume the stated typed-program and slot-wf hypotheses. Three pairs avoid a single 90-split tail group. Public declarations have distinct owner suffixes so independently started groups remain valid. These groups contain no unrelated emit constants or final-result work.

The remaining likely tail groups are index_bounds, assignment_bounds and binary_regular_bounds: 12 splits each, one public temporary-nonnegativity helper, count-length and max-budget context; their final-result code assembly is assigned separately. Short-circuit bounds are split across two coherent branch groups (9 and 7 splits), use existing length facts, and require no new helper. unary_bounds has 10 splits and intrinsic_bounds has 6; both share only their own unary-child budget context and require no new helper. member_bounds_constants has 9 splits, of which 7 are immediate shape/opcode/guard facts and 2 are child bounds; this modest load avoids an isolated one-witness bounds group. All stable length and slot-size facts needed here already exist in imported libraries and are referenced without planning new duplicates. There is no permutation, mask or array-segment helper family in this case.

| Group | Witnesses | Aggressive splits | Helpers | Difficulty |
|---|---:|---:|---:|---:|
| simple_view_conversion | 5 | 0 | 0 | 2 |
| constructor_facts_a | 2 | 22 | 1 | 5 |
| constructor_facts_b | 2 | 34 | 1 | 5 |
| constructor_facts_c | 2 | 34 | 1 | 5 |
| node_opening | 6 | 0 | 0 | 2 |
| node_closing | 6 | 6 | 0 | 2 |
| intrinsic_results | 6 | 6 | 0 | 3 |
| intrinsic_constants | 6 | 12 | 0 | 1 |
| intrinsic_plans | 6 | 6 | 0 | 2 |
| intrinsic_bounds | 3 | 6 | 0 | 3 |
| unary_deref_address_results | 4 | 4 | 0 | 2 |
| unary_arithmetic_results | 3 | 3 | 0 | 2 |
| unary_call_bounds | 5 | 10 | 0 | 2 |
| unary_constants | 4 | 8 | 0 | 1 |
| unary_shapes | 5 | 5 | 0 | 1 |
| unary_plans | 5 | 5 | 0 | 2 |
| unary_bounds | 5 | 10 | 0 | 3 |
| index_results_plans | 4 | 4 | 0 | 3 |
| index_bounds | 5 | 12 | 1 | 3 |
| index_assignment_constants | 5 | 10 | 0 | 1 |
| assignment_results_plans | 3 | 3 | 0 | 3 |
| assignment_bounds | 5 | 12 | 1 | 3 |
| binary_short_results | 4 | 4 | 0 | 3 |
| binary_regular_results | 3 | 3 | 0 | 3 |
| binary_short_bounds_a | 4 | 9 | 0 | 3 |
| binary_short_bounds_b | 3 | 7 | 0 | 3 |
| binary_regular_bounds | 5 | 12 | 1 | 3 |
| binary_call_shapes | 5 | 8 | 0 | 2 |
| binary_branch_constants | 4 | 16 | 0 | 1 |
| binary_emit_constants_a | 4 | 8 | 0 | 1 |
| binary_emit_constants_b | 4 | 8 | 0 | 1 |
| member_results | 5 | 5 | 0 | 3 |
| member_bounds_constants | 5 | 9 | 0 | 3 |
| simple_results | 5 | 5 | 0 | 2 |
| dispatch_heap_a | 5 | 4 | 0 | 2 |
| dispatch_heap_b | 5 | 5 | 0 | 2 |
| dispatch_heap_c | 5 | 5 | 0 | 2 |
| dispatch_constructor_shapes | 5 | 5 | 0 | 1 |
| dispatch_call_shapes | 5 | 5 | 0 | 1 |
| dispatch_intrinsic_shapes | 3 | 3 | 0 | 1 |

## Risks or Blockers

No definite blocker. Inductive type-reference preservation and the nested call case of temporary nonnegativity are the substantive library work. The analysis never assumes raw cm_type_code_wf implies an INT_MAX encoding bound: encoding bounds come from cm_expr_counts_representable. No proof-reuse analysis was performed.

Effort accounting: 0 coq-debug invocations, 0 controller proof/check invocations, 0 command failures; no Show insertion was needed and no formal file was edited. Read-only inspection used current generated definitions and their imported model declarations. Controller acceptance and all group proof checks remain outstanding.
