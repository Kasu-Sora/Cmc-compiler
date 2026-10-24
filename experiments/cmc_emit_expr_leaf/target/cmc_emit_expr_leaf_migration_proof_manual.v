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
From SimpleC.EE.QCP_demos_human Require Import cmc_emit_expr_leaf_migration_goal.
From SimpleC.EE.QCP_demos_human Require Import cmc_emit_expr_leaf_migration_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.cmc_emit_expr_leaf_migration_lib.
Local Open Scope sac.

Lemma proof_of_cmc_const_immediate_return_wit_1_split_goal_1 : cmc_const_immediate_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct model_ty; cbn [cm_const_immediate]; try reflexivity.
  cbv [cm_type_encode cm_type_depth cm_type_base_code] in PreH2.
  contradiction.
Qed.

Lemma proof_of_cmc_const_immediate_return_wit_1 : cmc_const_immediate_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_const_immediate_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_cmc_const_immediate_return_wit_2_split_goal_1 : cmc_const_immediate_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hchar : model_ty = CMCharTy).
  { apply (proj1 (cm_type_encode_char_iff__typed_branches model_ty PreH3)). lia. }
  subst model_ty.
  unfold cm_const_immediate, tower_u8, unsigned_last_nbits.
  change ((Z.rem (value_pre mod 18446744073709551616) 256) mod 256 = value_pre mod 256).
  rewrite Z.rem_mod_nonneg by (try lia; apply Z.mod_pos_bound; lia).
  rewrite Z.mod_mod by lia.
  rewrite (Z.mod_eq value_pre 18446744073709551616) by lia.
  rewrite Zminus_mod, Zmult_mod.
  change ((value_pre mod 256 - (0 * ((value_pre / 18446744073709551616) mod 256)) mod 256) mod 256 = value_pre mod 256).
  rewrite Z.mul_0_l, Z.mod_0_l, Z.sub_0_r by lia.
  apply Z.mod_mod. lia.
Qed.

Lemma proof_of_cmc_const_immediate_return_wit_2 : cmc_const_immediate_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_const_immediate_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_cm_emit_const_expr_entail_wit_1_split_goal_1 : cm_emit_const_expr_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e. cbn [cm_expr_rep]. unfold cm_expr_node.
  Intros a b args.
  dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_emit_const_expr_entail_wit_1_split_goal_spatial : cm_emit_const_expr_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e. cbn [cm_expr_rep]. unfold cm_expr_node.
  Intros a b args.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  subst a b args.
  cbn [cm_expr_type cm_rep_expr_value]. cancel.
Qed.

Lemma proof_of_cm_emit_const_expr_entail_wit_1 : cm_emit_const_expr_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_const_expr_entail_wit_1_split_goal_spatial.
  - Goal_apply proof_of_cm_emit_const_expr_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_cm_emit_const_expr_return_wit_1_split_goal_spatial : cm_emit_const_expr_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e lvalue_pre retval.
  unfold cm_leaf_code_for, cm_leaf_rvalue, cm_push_code.
  cbn [Z.eqb cm_expr_rep].
  unfold cm_expr_node. Exists 0 0 0.
  cbn [cm_expr_type cm_rep_expr_value].
  split_pure_spatial.
  - cancel (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity
      (done ++ (TVMInst TVMPushOp (cm_const_immediate ty n) :: nil)) tail).
    cancel.
  - split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_cm_emit_const_expr_return_wit_1 : cm_emit_const_expr_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_const_expr_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_const_expr_return_wit_2_split_goal_spatial : cm_emit_const_expr_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e. unfold cm_leaf_code_for.
  assert (Hlv : Z.eqb lvalue_pre 0 = false) by (apply Z.eqb_neq; lia).
  rewrite Hlv. simpl app. rewrite app_nil_r.
  cbn [cm_expr_rep]. unfold cm_expr_node. Exists 0 0 0.
  cbn [cm_expr_type cm_rep_expr_value].
  split_pure_spatial.
  - cancel (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done tail).
    cancel.
  - split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_cm_emit_const_expr_return_wit_2 : cm_emit_const_expr_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_const_expr_return_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_const_expr_which_implies_wit_1_split_goal_1 : cm_emit_const_expr_which_implies_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. cbn [tvm_opcode_code]. lia.
Qed.

Lemma proof_of_cm_emit_const_expr_which_implies_wit_1_split_goal_2 : cm_emit_const_expr_which_implies_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_cm_emit_const_expr_which_implies_wit_1_split_goal_spatial : cm_emit_const_expr_which_implies_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hlv : lvalue = 0) by lia. subst lvalue.
  unfold cm_leaf_code_for, cm_leaf_rvalue, cm_push_code.
  cbn [Z.eqb app]. cancel.
Qed.

Lemma proof_of_cm_emit_const_expr_which_implies_wit_1 : cm_emit_const_expr_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_const_expr_which_implies_wit_1_split_goal_spatial.
  - Goal_apply proof_of_cm_emit_const_expr_which_implies_wit_1_split_goal_1.
  - Goal_apply proof_of_cm_emit_const_expr_which_implies_wit_1_split_goal_2.
Qed.

Lemma proof_of_cm_emit_string_expr_entail_wit_1_split_goal_1 : cm_emit_string_expr_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e. cbn [cm_expr_rep]. unfold cm_expr_node.
  Intros a b args.
  dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_emit_string_expr_entail_wit_1_split_goal_spatial : cm_emit_string_expr_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e. cbn [cm_expr_rep]. unfold cm_expr_node.
  Intros a b args.
  destruct H0 as [Ha [Hb Hargs]]. subst a b args.
  cbn [cm_expr_type cm_rep_expr_value].
  cancel.
Qed.

Lemma proof_of_cm_emit_string_expr_entail_wit_1 : cm_emit_string_expr_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_string_expr_entail_wit_1_split_goal_spatial.
  - Goal_apply proof_of_cm_emit_string_expr_entail_wit_1_split_goal_1.

Qed. 

Lemma proof_of_cm_emit_string_expr_return_wit_1_split_goal_spatial : cm_emit_string_expr_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e lvalue_pre retval.
  unfold cm_leaf_code_for. cbn [Z.eqb cm_leaf_rvalue]. unfold cm_push_code.
  rewrite (cm_rep_string_address_matches policy p sid PreH11).
  unfold cm_program_context_rep. cbn [cm_expr_rep]. unfold cm_expr_node.
  Exists sp gp tp 0 0 0.
  cbn [cm_expr_type cm_rep_expr_value].
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_cm_emit_string_expr_return_wit_1 : cm_emit_string_expr_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_string_expr_return_wit_1_split_goal_spatial.

Qed. 

Lemma proof_of_cm_emit_string_expr_return_wit_2_split_goal_spatial : cm_emit_string_expr_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e.
  assert (Hlv : (Z.eqb lvalue_pre 0) = false) by (apply Z.eqb_neq; exact PreH9).
  unfold cm_leaf_code_for. rewrite Hlv. cbn [app]. rewrite app_nil_r.
  cbn [cm_expr_rep]. unfold cm_expr_node.
  Exists 0 0 0.
  cbn [cm_expr_type cm_rep_expr_value].
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_cm_emit_string_expr_return_wit_2 : cm_emit_string_expr_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_string_expr_return_wit_2_split_goal_spatial.

Qed. 

Lemma proof_of_cm_emit_string_expr_which_implies_wit_1 : cm_emit_string_expr_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_program_context_rep.
  Intros sp0 gp0 tp0.
  Exists tp0 gp0 sp0.
  split_pure_spatial.
  - repeat progress cancel.
  - dump_pre_spatial. assumption.
Qed. 

Lemma proof_of_cm_emit_string_expr_which_implies_wit_2_split_goal_1 : cm_emit_string_expr_which_implies_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. cbn [tvm_opcode_code]. lia.
Qed.

Lemma proof_of_cm_emit_string_expr_which_implies_wit_2_split_goal_2 : cm_emit_string_expr_which_implies_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cm_emit_string_expr_which_implies_wit_2_split_goal_spatial : cm_emit_string_expr_which_implies_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hlv : lvalue = 0) by lia. subst lvalue.
  unfold cm_leaf_code_for. cbn [Z.eqb cm_leaf_rvalue]. unfold cm_push_code. cbn [app].
  rewrite (cm_rep_string_address_matches policy p sid PreH1).
  cancel.
Qed.

Lemma proof_of_cm_emit_string_expr_which_implies_wit_2 : cm_emit_string_expr_which_implies_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_string_expr_which_implies_wit_2_split_goal_spatial.
  - Goal_apply proof_of_cm_emit_string_expr_which_implies_wit_2_split_goal_1.
  - Goal_apply proof_of_cm_emit_string_expr_which_implies_wit_2_split_goal_2.

Qed. 

Lemma proof_of_cm_emit_getc_expr_return_wit_1_split_goal_spatial : cm_emit_getc_expr_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst.
  rewrite cm_leaf_getc_source_equation.
  cbn [Z.eqb].
  cancel.
Qed.

Lemma proof_of_cm_emit_getc_expr_return_wit_1 : cm_emit_getc_expr_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_getc_expr_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_getc_expr_return_wit_2_split_goal_spatial : cm_emit_getc_expr_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace lvalue_pre with 1 by lia.
  rewrite !cm_leaf_getc_source_equation.
  cbn [Z.eqb app].
  rewrite app_nil_r.
  cancel.
Qed.

Lemma proof_of_cm_emit_getc_expr_return_wit_2 : cm_emit_getc_expr_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_getc_expr_return_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_getc_expr_which_implies_wit_1_split_goal_1 : cm_emit_getc_expr_which_implies_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  cbn [tvm_opcode_code].
  lia.
Qed.

Lemma proof_of_cm_emit_getc_expr_which_implies_wit_1_split_goal_2 : cm_emit_getc_expr_which_implies_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_cm_emit_getc_expr_which_implies_wit_1_split_goal_spatial : cm_emit_getc_expr_which_implies_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace lvalue with 0 by lia.
  rewrite cm_leaf_getc_source_equation.
  cbn [Z.eqb app].
  cancel.
Qed.

Lemma proof_of_cm_emit_getc_expr_which_implies_wit_1 : cm_emit_getc_expr_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_getc_expr_which_implies_wit_1_split_goal_spatial.
  - Goal_apply proof_of_cm_emit_getc_expr_which_implies_wit_1_split_goal_1.
  - Goal_apply proof_of_cm_emit_getc_expr_which_implies_wit_1_split_goal_2.
Qed.

Lemma proof_of_cm_sizeof_value_return_wit_1_split_goal_1 : cm_sizeof_value_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct asked; cbn [cm_type_size]; try reflexivity;
    unfold cm_type_encode in *;
    cbn [cm_type_depth cm_type_base_code cm_type_code_wf] in *; lia.
Qed.

Lemma proof_of_cm_sizeof_value_return_wit_1 : cm_sizeof_value_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_sizeof_value_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_cm_sizeof_value_return_wit_2_split_goal_1 : cm_sizeof_value_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst retval.
  apply cm_rep_type_size_matches; try assumption.
  match goal with H : cm_typed_program _ _ |- _ => exact (proj1 H) end.
Qed.

Lemma proof_of_cm_sizeof_value_return_wit_2_split_goal_spatial : cm_sizeof_value_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_program_context_rep.
  Exists sp gp tp.
  split_pure_spatial.
  - repeat progress cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_sizeof_value_return_wit_2 : cm_sizeof_value_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_sizeof_value_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_cm_sizeof_value_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_cm_sizeof_value_which_implies_wit_1_split_goal_1 : cm_sizeof_value_which_implies_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst code.
  pose proof (cm_type_depth_nonnegative__expression_assignment_safety asked).
  assert (0 <= cm_type_base_code asked < 1024) by
    (apply cm_type_base_bounds__expression_assignment_safety; assumption).
  unfold cm_type_encode. lia.
Qed.

Lemma proof_of_cm_sizeof_value_which_implies_wit_1 : cm_sizeof_value_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_sizeof_value_which_implies_wit_1_split_goal_1.
Qed.

Lemma proof_of_cm_sizeof_value_which_implies_wit_2 : cm_sizeof_value_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_program_context_rep.
  Intros structs_ptr globals_ptr strings_ptr.
  Exists strings_ptr globals_ptr structs_ptr.
  split_pure_spatial.
  - repeat progress cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_emit_sizeof_expr_entail_wit_1_split_goal_1 : cm_emit_sizeof_expr_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e. cbn [cm_expr_rep]. unfold cm_expr_node.
  Intros a b args.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_cm_emit_sizeof_expr_entail_wit_1_split_goal_spatial : cm_emit_sizeof_expr_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e. cbn [cm_expr_rep]. unfold cm_expr_node.
  Intros a b args.
  destruct H0 as [Ha [Hb Hargs]]. subst a b args.
  cbn [cm_expr_type cm_rep_expr_value]. cancel.
Qed.

Lemma proof_of_cm_emit_sizeof_expr_entail_wit_1 : cm_emit_sizeof_expr_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_sizeof_expr_entail_wit_1_split_goal_spatial.
  - Goal_apply proof_of_cm_emit_sizeof_expr_entail_wit_1_split_goal_1.
Qed. 

Lemma proof_of_cm_emit_sizeof_expr_return_wit_1_split_goal_spatial : cm_emit_sizeof_expr_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e lvalue_pre retval.
  unfold cm_leaf_code_for, cm_leaf_rvalue, cm_push_code.
  cbn [Z.eqb cm_expr_rep].
  unfold cm_expr_node. Exists 0 0 0.
  cbn [cm_expr_type cm_rep_expr_value].
  split_pure_spatial; [sepcon_assoc_change; cancel | split_pures; dump_pre_spatial; lia].


Qed.

Lemma proof_of_cm_emit_sizeof_expr_return_wit_1 : cm_emit_sizeof_expr_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_sizeof_expr_return_wit_1_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_sizeof_expr_return_wit_2_split_goal_spatial : cm_emit_sizeof_expr_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e. unfold cm_leaf_code_for.
  assert (Hlv : (Z.eqb lvalue_pre 0) = false) by (apply Z.eqb_neq; lia).
  rewrite Hlv. cbn [app]. rewrite app_nil_r.
  cbn [cm_expr_rep]. unfold cm_expr_node. Exists 0 0 0.
  cbn [cm_expr_type cm_rep_expr_value].
  split_pure_spatial; [sepcon_assoc_change; cancel | split_pures; dump_pre_spatial; lia].


Qed.

Lemma proof_of_cm_emit_sizeof_expr_return_wit_2 : cm_emit_sizeof_expr_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_sizeof_expr_return_wit_2_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_sizeof_expr_which_implies_wit_1_split_goal_1 : cm_emit_sizeof_expr_which_implies_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. cbn [tvm_opcode_code]. lia.
Qed.

Lemma proof_of_cm_emit_sizeof_expr_which_implies_wit_1_split_goal_2 : cm_emit_sizeof_expr_which_implies_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cm_emit_sizeof_expr_which_implies_wit_1_split_goal_spatial : cm_emit_sizeof_expr_which_implies_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (lvalue = 0) by lia. subst lvalue.
  unfold cm_leaf_code_for, cm_leaf_rvalue, cm_push_code.
  cbn [Z.eqb app]. cancel.
Qed.

Lemma proof_of_cm_emit_sizeof_expr_which_implies_wit_1 : cm_emit_sizeof_expr_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_sizeof_expr_which_implies_wit_1_split_goal_spatial.
  - Goal_apply proof_of_cm_emit_sizeof_expr_which_implies_wit_1_split_goal_1.
  - Goal_apply proof_of_cm_emit_sizeof_expr_which_implies_wit_1_split_goal_2.
Qed. 

Lemma proof_of_cm_member_array_value_context_entail_wit_1 : cm_member_array_value_context_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hbounds : 1024 <= base_ty_pre /\ 0 <= (base_ty_pre - 1024) % 1024 - 2 /\ 0 <= mid_pre).
  { pose proof PreH5 as Hvalid.
    unfold cm_member_valid in Hvalid.
    destruct base as [| |sid|u]; cbn [cm_is_pointer] in Hvalid; try tauto.
    destruct u as [| |sid|u]; cbn [cm_pointee cm_is_struct] in Hvalid; try tauto.
    cbn [cm_type_code_wf] in PreH4.
    cbn [cm_pointee cm_struct_id] in Hvalid.
    unfold cm_type_encode in PreH1.
    cbn [cm_type_depth cm_type_base_code] in PreH1.
    assert (E : (base_ty_pre - 1024) % 1024 = sid + 2).
    { replace (base_ty_pre - 1024) with (sid + 2) by lia.
      apply Z.rem_small. lia. }
    rewrite E. lia. }
  unfold cm_program_context_rep.
  Intros ss gg tt.
  Exists tt gg ss.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; unfold cm_i32_code_count in *; tauto || lia.
Qed. 

Lemma proof_of_cm_member_array_value_context_return_wit_1_split_goal_spatial : cm_member_array_value_context_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_program_context_rep.
  Exists sp gp tp.
  split_pure_spatial.
  - repeat progress cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_member_array_value_context_return_wit_1 : cm_member_array_value_context_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_member_array_value_context_return_wit_1_split_goal_spatial.
Qed. 

Lemma proof_of_cm_member_offset_value_context_safety_wit_1_split_goal_1 : cm_member_offset_value_context_safety_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (Z.rem_bound_pos retval 1024 ltac:(lia) ltac:(lia)) as Hmod.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_cm_member_offset_value_context_safety_wit_1_split_goal_2 : cm_member_offset_value_context_safety_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (Z.rem_bound_pos retval 1024 ltac:(lia) ltac:(lia)) as Hmod.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_cm_member_offset_value_context_safety_wit_1 : cm_member_offset_value_context_safety_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_member_offset_value_context_safety_wit_1_split_goal_1.
  - Goal_apply proof_of_cm_member_offset_value_context_safety_wit_1_split_goal_2.
Qed. 

Lemma proof_of_cm_member_offset_value_context_entail_wit_1 : cm_member_offset_value_context_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hbounds : 1024 <= base_ty_pre /\ 0 <= (base_ty_pre - 1024) % 1024 - 2 /\ 0 <= mid_pre).
  { pose proof PreH5 as Hvalid.
    unfold cm_member_valid in Hvalid.
    destruct base as [| |sid|u]; cbn [cm_is_pointer] in Hvalid; try tauto.
    destruct u as [| |sid|u]; cbn [cm_pointee cm_is_struct] in Hvalid; try tauto.
    cbn [cm_type_code_wf] in PreH4.
    cbn [cm_pointee cm_struct_id] in Hvalid.
    unfold cm_type_encode in PreH1.
    cbn [cm_type_depth cm_type_base_code] in PreH1.
    assert (E : (base_ty_pre - 1024) % 1024 = sid + 2).
    { replace (base_ty_pre - 1024) with (sid + 2) by lia.
      apply Z.rem_small. lia. }
    rewrite E. lia. }
  unfold cm_program_context_rep.
  Intros ss gg tt.
  Exists tt gg ss.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; unfold cm_i32_code_count in *; tauto || lia.
Qed. 

Lemma proof_of_cm_member_offset_value_context_return_wit_1_split_goal_1 : cm_member_offset_value_context_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst retval retval_2 base_ty_pre.
  destruct PreH15 as [Hp [Hs [Hsid Hmid]]].
  destruct base as [| |sid|base]; try contradiction.
  destruct base as [| |sid|base]; try contradiction.
  cbn [cm_type_code_wf] in PreH14.
  cbn [cm_pointee cm_struct_id] in Hsid |- *.
  unfold cm_type_encode.
  cbn [cm_type_depth cm_type_base_code].
  replace (1024 * (1 + 0) + (sid + 2) - 1024) with (sid + 2) by lia.
  rewrite Z.rem_small by lia.
  replace (sid + 2 - 2) with sid by lia.
  apply cm_rep_struct_member_prefix_matches; [exact Hsid|].
  destruct PreH13 as [Hstructs _].
  destruct (Hstructs sid Hsid) as [_ [Hslots _]].
  exact Hslots.
Qed.

Lemma proof_of_cm_member_offset_value_context_return_wit_1_split_goal_spatial : cm_member_offset_value_context_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_program_context_rep.
  Exists sp gp tp.
  split_pure_spatial.
  - repeat progress cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_member_offset_value_context_return_wit_1 : cm_member_offset_value_context_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_member_offset_value_context_return_wit_1_split_goal_spatial.
  Goal_apply proof_of_cm_member_offset_value_context_return_wit_1_split_goal_1.
Qed. 

