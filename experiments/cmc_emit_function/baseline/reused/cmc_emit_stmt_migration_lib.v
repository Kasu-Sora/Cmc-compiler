(* Exact statement emission equations from cmc_codegen.c:891-978.
   Structural recursion defines the public code sequence, not a mirror of C locals. *)
From Coq Require Import ZArith List Lia.
From AUXLib Require Import ListLib.
Require Export SimpleC.EE.QCP_demos_human.cmc_emit_expr_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_emit_return_migration_lib.
Import ListNotations.
Local Open Scope Z_scope.
Fixpoint cm_emit_stmt policy p fid pc temp breakpc continuepc s : list tvm_inst :=
 match s with
 | CMSkipS | CMDeclS _ => []
 | CMExprS e => cm_expr_code_for policy p fid pc temp e 0 ++ [TVMInst TVMPopOp 0]
 | CMInitS slot e =>
   cm_expr_code_for policy p fid pc temp e 0 ++
   cm_char_normalize_code (cm_slot_ty (cm_slot_at slot (cm_function_locals (cm_function_at policy fid (cm_program_functions p))))) ++
   cm_fp_relative_address_code (cm_local_offset policy p fid slot) ++
   cm_store_code (cm_slot_ty (cm_slot_at slot (cm_function_locals (cm_function_at policy fid (cm_program_functions p)))))
 | CMSeqS a b => cm_emit_stmt policy p fid pc temp breakpc continuepc a ++
   cm_emit_stmt policy p fid (pc + cm_stmt_code_count policy p fid a) temp breakpc continuepc b
 | CMBlockS a => cm_emit_stmt policy p fid pc temp breakpc continuepc a
 | CMIfS e a b => cm_expr_code_for policy p fid pc temp e 0 ++
   [TVMInst TVMJzOp (pc + cm_rvalue_code_count policy p fid e + 1 + cm_stmt_code_count policy p fid a + 1)] ++
   cm_emit_stmt policy p fid (pc + cm_rvalue_code_count policy p fid e + 1) temp breakpc continuepc a ++
   [TVMInst TVMJmpOp (pc + cm_stmt_code_count policy p fid (CMIfS e a b))] ++
   cm_emit_stmt policy p fid (pc + cm_rvalue_code_count policy p fid e + 1 + cm_stmt_code_count policy p fid a + 1) temp breakpc continuepc b
 | CMWhileS e a => cm_expr_code_for policy p fid pc temp e 0 ++
   [TVMInst TVMJzOp (pc + cm_stmt_code_count policy p fid (CMWhileS e a))] ++
   cm_emit_stmt policy p fid (pc + cm_rvalue_code_count policy p fid e + 1) temp
     (pc + cm_stmt_code_count policy p fid (CMWhileS e a)) pc a ++ [TVMInst TVMJmpOp pc]
 | CMBreakS => [TVMInst TVMJmpOp breakpc]
 | CMContinueS => [TVMInst TVMJmpOp continuepc]
 | CMReturnS e => cm_expr_code_for policy p fid pc temp e 0 ++
   cm_char_normalize_code (cm_function_ret (cm_function_at policy fid (cm_program_functions p))) ++ cm_return_epilogue
 end.

(* Constructor projections expose stable AST observations for QCP annotations. *)
Definition cm_stmt_expr s := match s with
 | CMExprS e | CMInitS _ e | CMIfS e _ _ | CMWhileS e _ | CMReturnS e => e
 | _ => CMConstE 0 CMIntTy end.
Definition cm_stmt_first s := match s with
 | CMSeqS a _ | CMBlockS a | CMIfS _ a _ | CMWhileS _ a => a | _ => CMSkipS end.
Definition cm_stmt_second s := match s with
 | CMSeqS _ b | CMIfS _ _ b => b | _ => CMSkipS end.

Lemma cm_expr_rvalue_length__stmt_capacity policy p fid pc temp e :
 Zlength (cm_expr_code_for policy p fid pc temp e 0) = cm_rvalue_code_count policy p fid e.
Proof. apply (proj2 (cm_emit_pair_lengths__store_bounds policy p fid e pc temp)). Qed.
Lemma cm_emit_stmt_length__stmt_capacity : forall policy p fid s pc temp breakpc continuepc,
 Zlength (cm_emit_stmt policy p fid pc temp breakpc continuepc s) = cm_stmt_code_count policy p fid s.
Proof.
 intros policy p fid s; induction s; intros pc temp breakpc continuepc;
 cbn [cm_emit_stmt cm_stmt_code_count];
 repeat rewrite Zlength_app;
 rewrite ?cm_expr_rvalue_length__stmt_capacity;
 repeat match goal with
 | |- context [Zlength (cm_emit_stmt _ _ _ ?pc0 ?t ?b ?c _)] =>
   first [rewrite (IHs pc0 t b c) | rewrite (IHs1 pc0 t b c) | rewrite (IHs2 pc0 t b c)]
 | |- context [Zlength (cm_store_code ?ty)] =>
   rewrite (proj1 (proj2 (proj2 (proj2 (cm_primitive_lengths__store_bounds policy p fid temp ty)))))
 | |- context [Zlength (cm_char_normalize_code ?ty)] =>
   rewrite (proj2 (proj2 (proj2 (proj2 (cm_primitive_lengths__store_bounds policy p fid temp ty)))))
 end;
 unfold cm_fp_relative_address_code, cm_return_epilogue;
 repeat rewrite Zlength_cons; rewrite ?Zlength_nil; lia.
Qed.
Lemma cm_stmt_count_nonnegative__stmt_capacity policy p fid s :
 0 <= cm_stmt_code_count policy p fid s.
Proof. rewrite <- (cm_emit_stmt_length__stmt_capacity policy p fid s 0 0 0 0). apply Zlength_nonneg. Qed.
Lemma cm_rvalue_count_nonnegative__stmt_capacity policy p fid e :
 0 <= cm_rvalue_code_count policy p fid e.
Proof. rewrite <- (cm_expr_rvalue_length__stmt_capacity policy p fid 0 0 e). apply Zlength_nonneg. Qed.
