Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.QCP_demos_human Require Import cmc_count_context_migration_goal.
From SimpleC.EE.QCP_demos_human Require Import cmc_count_context_migration_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.cmc_count_context_migration_lib.
Local Open Scope sac.

Lemma proof_of_cm_expr_type_code_context_entail_wit_1 : cm_expr_type_code_context_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_expr_rep_node.
  unfold cm_expr_node.
  Intros a b args.
  Exists args b a.
  split_pure_spatial.
  - sepcon_right_assoc. cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_expr_type_code_context_return_wit_1_split_goal_spatial : cm_expr_type_code_context_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_expr_rep_node.
  unfold cm_expr_node.
  Exists pa pb pargs.
  split_pure_spatial.
  - sepcon_right_assoc. cancel.
  - dump_pre_spatial. exact PreH9.
Qed.

Lemma proof_of_cm_expr_type_code_context_return_wit_1 : cm_expr_type_code_context_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_expr_type_code_context_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cm_expr_lvalue_count_context_entail_wit_1 : cm_expr_lvalue_count_context_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_program_context_rep, cm_function_context_rep.
  Intros zs zg zt zp zl.
  Exists zl zp zt zg zs.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_cm_expr_lvalue_count_context_return_wit_1_split_goal_spatial : cm_expr_lvalue_count_context_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_program_context_rep, cm_function_context_rep.
  Exists zs zg zt zp zl.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_cm_expr_lvalue_count_context_return_wit_1 : cm_expr_lvalue_count_context_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_expr_lvalue_count_context_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cm_expr_rvalue_count_context_entail_wit_1 : cm_expr_rvalue_count_context_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_program_context_rep, cm_function_context_rep.
  Intros zs zg zt zp zl.
  Exists zl zp zt zg zs.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_cm_expr_rvalue_count_context_return_wit_1_split_goal_spatial : cm_expr_rvalue_count_context_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_program_context_rep, cm_function_context_rep.
  Exists zs zg zt zp zl.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_cm_expr_rvalue_count_context_return_wit_1 : cm_expr_rvalue_count_context_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_expr_rvalue_count_context_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cm_stmt_code_count_context_entail_wit_1 : cm_stmt_code_count_context_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_program_context_rep, cm_function_context_rep.
  Intros zs zg zt zp zl.
  Exists zl zp zt zg zs.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_cm_stmt_code_count_context_return_wit_1_split_goal_spatial : cm_stmt_code_count_context_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_program_context_rep, cm_function_context_rep.
  Exists zs zg zt zp zl.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_cm_stmt_code_count_context_return_wit_1 : cm_stmt_code_count_context_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_stmt_code_count_context_return_wit_1_split_goal_spatial.
Qed.

