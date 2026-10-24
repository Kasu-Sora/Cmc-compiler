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
From SimpleC.EE.QCP_demos_human Require Import cmc_emit_expr_var_migration_goal.
From SimpleC.EE.QCP_demos_human Require Import cmc_emit_expr_var_migration_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.cmc_emit_expr_var_migration_lib.
Local Open Scope sac.

Lemma proof_of_cm_emit_var_expr_return_wit_1_split_goal_spatial : cm_emit_var_expr_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e lvalue_pre.
  unfold cm_var_code_for, cm_var_rcode.
  rewrite PreH18. cbn beta iota zeta delta [Z.eqb].
  rewrite app_assoc.
  cancel (cm_program_context_rep program_pre p functions_ptr).
  cancel (cm_function_context_rep fn_pre f body next).
  cancel (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity
    ((done ++ cm_binding_address_code policy p fid_pre scope slot) ++ cm_load_code ty) tail).
  cbn [cm_expr_rep].
  unfold cm_expr_node.
  Exists 0 0 0.
  cbn [cm_rep_expr_kind cm_rep_expr_op cm_rep_expr_value cm_expr_type].
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_cm_emit_var_expr_return_wit_1 : cm_emit_var_expr_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_var_expr_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_var_expr_return_wit_2_split_goal_spatial : cm_emit_var_expr_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e lvalue_pre.
  unfold cm_var_code_for, cm_var_rcode.
  rewrite (proj2 (Z.eqb_neq _ _) PreH18).
  cbn beta iota zeta delta [Z.eqb].
  rewrite app_nil_r.
  cancel (cm_program_context_rep program_pre p functions_ptr).
  cancel (cm_function_context_rep fn_pre f body next).
  cancel (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity
    (done ++ cm_binding_address_code policy p fid_pre scope slot) tail).
  cbn [cm_expr_rep].
  unfold cm_expr_node.
  Exists 0 0 0.
  cbn [cm_rep_expr_kind cm_rep_expr_op cm_rep_expr_value cm_expr_type].
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_cm_emit_var_expr_return_wit_2 : cm_emit_var_expr_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_var_expr_return_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_var_expr_return_wit_3_split_goal_spatial : cm_emit_var_expr_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e.
  unfold cm_var_code_for, cm_var_lcode.
  rewrite (proj2 (Z.eqb_neq _ _) PreH17).
  cancel (cm_program_context_rep program_pre p functions_ptr).
  cancel (cm_function_context_rep fn_pre f body next).
  cancel (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity
    (done ++ cm_binding_address_code policy p fid_pre scope slot) tail).
  cbn [cm_expr_rep].
  unfold cm_expr_node.
  Exists 0 0 0.
  cbn [cm_rep_expr_kind cm_rep_expr_op cm_rep_expr_value cm_expr_type].
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_cm_emit_var_expr_return_wit_3 : cm_emit_var_expr_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_var_expr_return_wit_3_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_var_expr_which_implies_wit_1_split_goal_1 : cm_emit_var_expr_which_implies_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e. cbn [cm_expr_rep]. unfold cm_expr_node.
  Intros a b args.
  dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_emit_var_expr_which_implies_wit_1_split_goal_spatial : cm_emit_var_expr_which_implies_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e. cbn [cm_expr_rep]. unfold cm_expr_node.
  cbn [cm_rep_expr_kind cm_rep_expr_op cm_expr_type cm_rep_expr_value].
  Intros a b args. destruct H0 as [Ha [Hb Hargs]]. subst a b args.
  cancel.
Qed.

Lemma proof_of_cm_emit_var_expr_which_implies_wit_1 : cm_emit_var_expr_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_var_expr_which_implies_wit_1_split_goal_spatial.
  - Goal_apply proof_of_cm_emit_var_expr_which_implies_wit_1_split_goal_1.
Qed.

Lemma proof_of_cm_emit_var_expr_which_implies_wit_2 : cm_emit_var_expr_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_program_context_rep, cm_function_context_rep.
  Intros sp gp tp pp lp.
  Exists lp pp tp gp sp.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_cm_emit_var_expr_which_implies_wit_3_split_goal_spatial : cm_emit_var_expr_which_implies_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_program_context_rep, cm_function_context_rep.
  Exists sp gp tp pp lp.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_cm_emit_var_expr_which_implies_wit_3 : cm_emit_var_expr_which_implies_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_var_expr_which_implies_wit_3_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_var_expr_which_implies_wit_4_split_goal_spatial : cm_emit_var_expr_which_implies_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (lvalue = 0) by lia.
  subst lvalue.
  unfold cm_var_code_for, cm_var_rcode.
  rewrite PreH3.
  simpl Z.eqb.
  cbn beta iota zeta.
  rewrite <- app_assoc.
  reflexivity.
Qed.

Lemma proof_of_cm_emit_var_expr_which_implies_wit_4 : cm_emit_var_expr_which_implies_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_var_expr_which_implies_wit_4_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_var_expr_which_implies_wit_5_split_goal_spatial : cm_emit_var_expr_which_implies_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (lvalue = 0) by lia.
  subst lvalue.
  unfold cm_var_code_for, cm_var_rcode.
  assert (Z.eqb (cm_binding_array_code policy p fid scope slot) 0 = false)
    as Harray by (apply Z.eqb_neq; assumption).
  rewrite Harray.
  simpl Z.eqb.
  cbn beta iota zeta.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma proof_of_cm_emit_var_expr_which_implies_wit_5 : cm_emit_var_expr_which_implies_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_var_expr_which_implies_wit_5_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_var_expr_which_implies_wit_6_split_goal_spatial : cm_emit_var_expr_which_implies_wit_6_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_var_code_for, cm_var_lcode.
  assert (Z.eqb lvalue 0 = false) as Hlvalue
    by (apply Z.eqb_neq; assumption).
  rewrite Hlvalue.
  reflexivity.
Qed.

Lemma proof_of_cm_emit_var_expr_which_implies_wit_6 : cm_emit_var_expr_which_implies_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_var_expr_which_implies_wit_6_split_goal_spatial.
Qed.

