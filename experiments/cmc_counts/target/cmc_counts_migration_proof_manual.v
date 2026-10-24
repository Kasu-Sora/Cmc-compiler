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
From SimpleC.EE.QCP_demos_human Require Import cmc_counts_migration_goal.
From SimpleC.EE.QCP_demos_human Require Import cmc_counts_migration_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.cmc_counts_migration_lib.
Local Open Scope sac.

Lemma proof_of_cmc_expr_type_code_value_entail_wit_1 : cmc_expr_type_code_value_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_expr_rep_node. unfold cm_expr_node.
  Intros pa pb pargs.
  Exists pargs pb pa.
  split_pure_spatial.
  - repeat progress cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cmc_expr_type_code_value_return_wit_1_split_goal_spatial : cmc_expr_type_code_value_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_expr_rep_node. unfold cm_expr_node.
  Exists pa pb pargs.
  split_pure_spatial.
  - repeat progress cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cmc_expr_type_code_value_return_wit_1 : cmc_expr_type_code_value_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_expr_type_code_value_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cmc_args_code_count_safety_wit_3_split_goal_1 : cmc_args_code_count_safety_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst args.
  cbn [cm_args_counts_representable cm_args_code_counts cm_args_code_count_of] in PreH30.
  unfold cm_i32_code_count, cm_rvalue_code_count in *.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_cmc_args_code_count_safety_wit_3_split_goal_2 : cmc_args_code_count_safety_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst args.
  cbn [cm_args_counts_representable cm_args_code_counts cm_args_code_count_of] in PreH30.
  unfold cm_i32_code_count, cm_rvalue_code_count in *.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_cmc_args_code_count_safety_wit_3 : cmc_args_code_count_safety_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_args_code_count_safety_wit_3_split_goal_1.
  - Goal_apply proof_of_cmc_args_code_count_safety_wit_3_split_goal_2.
Qed. 

Lemma proof_of_cmc_args_code_count_safety_wit_4_split_goal_1 : cmc_args_code_count_safety_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst args.
  cbn [cm_args_counts_representable cm_args_code_counts cm_args_code_count_of] in PreH30.
  unfold cm_i32_code_count, cm_rvalue_code_count in *.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_cmc_args_code_count_safety_wit_4_split_goal_2 : cmc_args_code_count_safety_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst args.
  cbn [cm_args_counts_representable cm_args_code_counts cm_args_code_count_of] in PreH30.
  unfold cm_i32_code_count, cm_rvalue_code_count in *.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_cmc_args_code_count_safety_wit_4 : cmc_args_code_count_safety_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_args_code_count_safety_wit_4_split_goal_1.
  - Goal_apply proof_of_cmc_args_code_count_safety_wit_4_split_goal_2.
Qed. 

Lemma proof_of_cmc_args_code_count_entail_wit_1 : cmc_args_code_count_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct args as [|head tail].
  - cbn [cm_arg_list_rep]. Intros_p Hnull. contradiction.
  - destruct slots as [|sh st]; [cbn [cm_args_wf] in PreH8; contradiction|].
    cbn [cm_arg_list_rep]. Intros ep np.
    cbn [cm_args_wf] in PreH8.
    cbn [cm_args_counts_representable] in PreH9.
    Exists np ep sh st head tail.
    split_pure_spatial.
    + repeat progress cancel.
    + split_pures; dump_pre_spatial; cbn [cm_args_wf cm_args_counts_representable]; tauto.
Qed. 

Lemma proof_of_cmc_args_code_count_return_wit_1_split_goal_1 : cmc_args_code_count_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_cmc_args_code_count_return_wit_1_split_goal_2 : cmc_args_code_count_return_wit_1_split_goal_2.
Proof. Abort.

Lemma proof_of_cmc_args_code_count_return_wit_1 : cmc_args_code_count_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct args as [|head tail].
  - cbn [cm_args_code_counts cm_args_code_count_of].
    split_pure_spatial.
    + repeat progress cancel.
    + split_pures; dump_pre_spatial; try assumption; unfold cm_i32_code_count; lia.
  - cbn [cm_arg_list_rep]. Intros ep np. contradiction.
Qed. 

Lemma proof_of_cmc_args_code_count_return_wit_2_split_goal_1 : cmc_args_code_count_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. destruct args; exact (proj1 PreH30).
Qed.

Lemma proof_of_cmc_args_code_count_return_wit_2_split_goal_2 : cmc_args_code_count_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst args. dump_pre_spatial. reflexivity.
Qed.

Lemma proof_of_cmc_args_code_count_return_wit_2_split_goal_spatial : cmc_args_code_count_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst args. cbn [cm_arg_list_rep]. Exists ep np.
  split_pure_spatial.
  - repeat progress cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cmc_args_code_count_return_wit_2 : cmc_args_code_count_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_args_code_count_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_cmc_args_code_count_return_wit_2_split_goal_1.
  - Goal_apply proof_of_cmc_args_code_count_return_wit_2_split_goal_2.
Qed. 

Lemma proof_of_cm_binding_address_count_value_return_wit_1_split_goal_1 : cm_binding_address_count_value_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_i32_code_count, cm_binding_address_count. cbn. lia.
Qed.

Lemma proof_of_cm_binding_address_count_value_return_wit_1_split_goal_2 : cm_binding_address_count_value_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(reflexivity || lia || nia || int_auto).
Qed.

Lemma proof_of_cm_binding_address_count_value_return_wit_1 : cm_binding_address_count_value_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_binding_address_count_value_return_wit_1_split_goal_1.
  - Goal_apply proof_of_cm_binding_address_count_value_return_wit_1_split_goal_2.
Qed.

Lemma proof_of_cm_binding_address_count_value_return_wit_2_split_goal_1 : cm_binding_address_count_value_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_i32_code_count, cm_binding_address_count.
  destruct (Z.eqb scope_pre 0); lia.
Qed.

Lemma proof_of_cm_binding_address_count_value_return_wit_2_split_goal_2 : cm_binding_address_count_value_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_binding_address_count.
  rewrite (proj2 (Z.eqb_neq scope_pre 0) PreH1). reflexivity.
Qed.

Lemma proof_of_cm_binding_address_count_value_return_wit_2 : cm_binding_address_count_value_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_binding_address_count_value_return_wit_2_split_goal_1.
  - Goal_apply proof_of_cm_binding_address_count_value_return_wit_2_split_goal_2.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_12_split_goal_1 : cm_expr_counts_safety_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold cm_binding_address_count.
  destruct (Z.eqb (cm_rep_expr_op e) 0); lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_12_split_goal_2 : cm_expr_counts_safety_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold cm_binding_address_count.
  destruct (Z.eqb (cm_rep_expr_op e) 0); lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_12 : cm_expr_counts_safety_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_12_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_12_split_goal_2.
Qed. 

Lemma proof_of_cm_expr_counts_safety_wit_15_split_goal_1 : cm_expr_counts_safety_wit_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e retval.
  cbn [cm_expr_counts_representable] in PreH34.
  destruct PreH34 as [[Hcounts [Hty Hencode]] Hchildren].
  cbn [cm_expr_type] in Hty |- *.
  rewrite cm_normalize_encode__expression_assignment_safety by exact Hty.
  unfold cm_code_counts_representable in Hcounts.
  cbn [cm_expr_code_counts cm_lcount_of cm_rcount_of] in Hcounts.
  unfold cm_i32_code_count in Hcounts, PreH13, PreH24.
  unfold cm_lvalue_code_count, cm_rvalue_code_count in *.
  assert (0 <= cm_char_normalize_count ty) by (destruct ty; cbn; lia).
  lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_15_split_goal_2 : cm_expr_counts_safety_wit_15_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e retval.
  cbn [cm_expr_counts_representable] in PreH34.
  destruct PreH34 as [[Hcounts [Hty Hencode]] Hchildren].
  cbn [cm_expr_type] in Hty |- *.
  rewrite cm_normalize_encode__expression_assignment_safety by exact Hty.
  unfold cm_code_counts_representable in Hcounts.
  cbn [cm_expr_code_counts cm_lcount_of cm_rcount_of] in Hcounts.
  unfold cm_i32_code_count in Hcounts, PreH13, PreH24.
  unfold cm_lvalue_code_count, cm_rvalue_code_count in *.
  assert (0 <= cm_char_normalize_count ty) by (destruct ty; cbn; lia).
  lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_15 : cm_expr_counts_safety_wit_15.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_15_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_15_split_goal_2.
Qed. 

Lemma proof_of_cm_expr_counts_safety_wit_16_split_goal_1 : cm_expr_counts_safety_wit_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e retval.
  cbn [cm_expr_counts_representable] in PreH34.
  destruct PreH34 as [[Hcounts [Hty Hencode]] Hchildren].
  cbn [cm_expr_type] in Hty |- *.
  rewrite cm_normalize_encode__expression_assignment_safety by exact Hty.
  unfold cm_code_counts_representable in Hcounts.
  cbn [cm_expr_code_counts cm_lcount_of cm_rcount_of] in Hcounts.
  unfold cm_i32_code_count in Hcounts, PreH13, PreH24.
  unfold cm_lvalue_code_count, cm_rvalue_code_count in *.
  assert (0 <= cm_char_normalize_count ty) by (destruct ty; cbn; lia).
  lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_16_split_goal_2 : cm_expr_counts_safety_wit_16_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e retval.
  cbn [cm_expr_counts_representable] in PreH34.
  destruct PreH34 as [[Hcounts [Hty Hencode]] Hchildren].
  cbn [cm_expr_type] in Hty |- *.
  rewrite cm_normalize_encode__expression_assignment_safety by exact Hty.
  unfold cm_code_counts_representable in Hcounts.
  cbn [cm_expr_code_counts cm_lcount_of cm_rcount_of] in Hcounts.
  unfold cm_i32_code_count in Hcounts, PreH13, PreH24.
  unfold cm_lvalue_code_count, cm_rvalue_code_count in *.
  assert (0 <= cm_char_normalize_count ty) by (destruct ty; cbn; lia).
  lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_16 : cm_expr_counts_safety_wit_16.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_16_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_16_split_goal_2.
Qed. 

Lemma proof_of_cm_expr_counts_safety_wit_17_split_goal_1 : cm_expr_counts_safety_wit_17_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e retval.
  cbn [cm_expr_counts_representable] in PreH34.
  destruct PreH34 as [[Hcounts [Hty Hencode]] Hchildren].
  cbn [cm_expr_type] in Hty |- *.
  rewrite cm_normalize_encode__expression_assignment_safety by exact Hty.
  unfold cm_code_counts_representable in Hcounts.
  cbn [cm_expr_code_counts cm_lcount_of cm_rcount_of] in Hcounts.
  unfold cm_i32_code_count in Hcounts, PreH13, PreH24.
  unfold cm_lvalue_code_count, cm_rvalue_code_count in *.
  assert (0 <= cm_char_normalize_count ty) by (destruct ty; cbn; lia).
  lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_17_split_goal_2 : cm_expr_counts_safety_wit_17_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e retval.
  cbn [cm_expr_counts_representable] in PreH34.
  destruct PreH34 as [[Hcounts [Hty Hencode]] Hchildren].
  cbn [cm_expr_type] in Hty |- *.
  rewrite cm_normalize_encode__expression_assignment_safety by exact Hty.
  unfold cm_code_counts_representable in Hcounts.
  cbn [cm_expr_code_counts cm_lcount_of cm_rcount_of] in Hcounts.
  unfold cm_i32_code_count in Hcounts, PreH13, PreH24.
  unfold cm_lvalue_code_count, cm_rvalue_code_count in *.
  assert (0 <= cm_char_normalize_count ty) by (destruct ty; cbn; lia).
  lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_17 : cm_expr_counts_safety_wit_17.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_17_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_17_split_goal_2.
Qed. 

Lemma proof_of_cm_expr_counts_safety_wit_18_split_goal_1 : cm_expr_counts_safety_wit_18_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e retval.
  cbn [cm_expr_counts_representable] in PreH34.
  destruct PreH34 as [[Hcounts [Hty Hencode]] Hchildren].
  cbn [cm_expr_type] in Hty |- *.
  rewrite cm_normalize_encode__expression_assignment_safety by exact Hty.
  unfold cm_code_counts_representable in Hcounts.
  cbn [cm_expr_code_counts cm_lcount_of cm_rcount_of] in Hcounts.
  unfold cm_i32_code_count in Hcounts, PreH13, PreH24.
  unfold cm_lvalue_code_count, cm_rvalue_code_count in *.
  assert (0 <= cm_char_normalize_count ty) by (destruct ty; cbn; lia).
  lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_18_split_goal_2 : cm_expr_counts_safety_wit_18_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e retval.
  cbn [cm_expr_counts_representable] in PreH34.
  destruct PreH34 as [[Hcounts [Hty Hencode]] Hchildren].
  cbn [cm_expr_type] in Hty |- *.
  rewrite cm_normalize_encode__expression_assignment_safety by exact Hty.
  unfold cm_code_counts_representable in Hcounts.
  cbn [cm_expr_code_counts cm_lcount_of cm_rcount_of] in Hcounts.
  unfold cm_i32_code_count in Hcounts, PreH13, PreH24.
  unfold cm_lvalue_code_count, cm_rvalue_code_count in *.
  assert (0 <= cm_char_normalize_count ty) by (destruct ty; cbn; lia).
  lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_18 : cm_expr_counts_safety_wit_18.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_18_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_18_split_goal_2.
Qed. 

Lemma proof_of_cm_expr_counts_safety_wit_23_split_goal_1 : cm_expr_counts_safety_wit_23_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e. cbn [cm_rep_expr_op] in *. subst op.
  cbn [cm_expr_counts_representable] in PreH34.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH34.
  cbn [cm_expr_code_counts cm_lcount_of cm_rcount_of Z.eqb orb] in PreH34.
  unfold cm_i32_code_count, cm_rvalue_code_count in *.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_23_split_goal_2 : cm_expr_counts_safety_wit_23_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_i32_code_count in *.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_23 : cm_expr_counts_safety_wit_23.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_23_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_23_split_goal_2.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_24_split_goal_1 : cm_expr_counts_safety_wit_24_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e. cbn [cm_rep_expr_op] in *. subst op.
  cbn [cm_expr_counts_representable] in PreH34.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH34.
  cbn [cm_expr_code_counts cm_lcount_of cm_rcount_of Z.eqb orb] in PreH34.
  unfold cm_i32_code_count, cm_rvalue_code_count in *.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_24_split_goal_2 : cm_expr_counts_safety_wit_24_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_i32_code_count in *.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_24 : cm_expr_counts_safety_wit_24.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_24_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_24_split_goal_2.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_27_split_goal_1 : cm_expr_counts_safety_wit_27_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e. cbn [cm_rep_expr_op] in *. subst op.
  cbn [cm_expr_counts_representable] in PreH35.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH35.
  cbn [cm_expr_code_counts cm_lcount_of cm_rcount_of Z.eqb Pos.eqb orb] in PreH35.
  unfold cm_i32_code_count, cm_rvalue_code_count in *.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_27_split_goal_2 : cm_expr_counts_safety_wit_27_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_i32_code_count in *.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_27 : cm_expr_counts_safety_wit_27.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_27_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_27_split_goal_2.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_28_split_goal_1 : cm_expr_counts_safety_wit_28_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e. cbn [cm_rep_expr_op] in *. subst op.
  cbn [cm_expr_counts_representable] in PreH35.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH35.
  cbn [cm_expr_code_counts cm_lcount_of cm_rcount_of Z.eqb Pos.eqb orb] in PreH35.
  unfold cm_i32_code_count, cm_rvalue_code_count in *.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_28_split_goal_2 : cm_expr_counts_safety_wit_28_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_i32_code_count in *.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_28 : cm_expr_counts_safety_wit_28.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_28_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_28_split_goal_2.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_31_split_goal_1 : cm_expr_counts_safety_wit_31_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst.
  cbn [cm_rep_expr_op] in *.
  subst.
  match goal with
  | H : cm_expr_counts_representable _ _ _ (CMBinaryE _ _ _ _) |- _ =>
    pose proof (proj1 H) as Hnode
  end.
  try rewrite (cm_pointer_encode__expression_add_safety (cm_expr_type y) ltac:(assumption)) in *.
  try rewrite (cm_pointer_encode__expression_add_safety (cm_expr_type x) ltac:(assumption)) in *.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in Hnode.
  cbn [cm_expr_code_counts cm_rcount_of cm_lcount_of] in Hnode.
  unfold cm_binary_tail_count in Hnode.
  unfold cm_i32_code_count, cm_rvalue_code_count in *.
  destruct (cm_pointerb (cm_expr_type y)); destruct (cm_pointerb (cm_expr_type x));
  cbn in Hnode; lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_31_split_goal_2 : cm_expr_counts_safety_wit_31_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst.
  cbn [cm_rep_expr_op] in *.
  subst.
  match goal with
  | H : cm_expr_counts_representable _ _ _ (CMBinaryE _ _ _ _) |- _ =>
    pose proof (proj1 H) as Hnode
  end.
  try rewrite (cm_pointer_encode__expression_add_safety (cm_expr_type y) ltac:(assumption)) in *.
  try rewrite (cm_pointer_encode__expression_add_safety (cm_expr_type x) ltac:(assumption)) in *.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in Hnode.
  cbn [cm_expr_code_counts cm_rcount_of cm_lcount_of] in Hnode.
  unfold cm_binary_tail_count in Hnode.
  unfold cm_i32_code_count, cm_rvalue_code_count in *.
  destruct (cm_pointerb (cm_expr_type y)); destruct (cm_pointerb (cm_expr_type x));
  cbn in Hnode; lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_31 : cm_expr_counts_safety_wit_31.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_31_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_31_split_goal_2.
Qed. 

Lemma proof_of_cm_expr_counts_safety_wit_32_split_goal_1 : cm_expr_counts_safety_wit_32_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst.
  cbn [cm_rep_expr_op] in *.
  subst.
  match goal with
  | H : cm_expr_counts_representable _ _ _ (CMBinaryE _ _ _ _) |- _ =>
    pose proof (proj1 H) as Hnode
  end.
  try rewrite (cm_pointer_encode__expression_add_safety (cm_expr_type y) ltac:(assumption)) in *.
  try rewrite (cm_pointer_encode__expression_add_safety (cm_expr_type x) ltac:(assumption)) in *.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in Hnode.
  cbn [cm_expr_code_counts cm_rcount_of cm_lcount_of] in Hnode.
  unfold cm_binary_tail_count in Hnode.
  unfold cm_i32_code_count, cm_rvalue_code_count in *.
  destruct (cm_pointerb (cm_expr_type y)); destruct (cm_pointerb (cm_expr_type x));
  cbn in Hnode; lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_32_split_goal_2 : cm_expr_counts_safety_wit_32_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst.
  cbn [cm_rep_expr_op] in *.
  subst.
  match goal with
  | H : cm_expr_counts_representable _ _ _ (CMBinaryE _ _ _ _) |- _ =>
    pose proof (proj1 H) as Hnode
  end.
  try rewrite (cm_pointer_encode__expression_add_safety (cm_expr_type y) ltac:(assumption)) in *.
  try rewrite (cm_pointer_encode__expression_add_safety (cm_expr_type x) ltac:(assumption)) in *.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in Hnode.
  cbn [cm_expr_code_counts cm_rcount_of cm_lcount_of] in Hnode.
  unfold cm_binary_tail_count in Hnode.
  unfold cm_i32_code_count, cm_rvalue_code_count in *.
  destruct (cm_pointerb (cm_expr_type y)); destruct (cm_pointerb (cm_expr_type x));
  cbn in Hnode; lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_32 : cm_expr_counts_safety_wit_32.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_32_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_32_split_goal_2.
Qed. 

Lemma proof_of_cm_expr_counts_safety_wit_34_split_goal_1 : cm_expr_counts_safety_wit_34_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst.
  cbn [cm_rep_expr_op] in *.
  subst.
  match goal with
  | H : cm_expr_counts_representable _ _ _ (CMBinaryE _ _ _ _) |- _ =>
    pose proof (proj1 H) as Hnode
  end.
  try rewrite (cm_pointer_encode__expression_add_safety (cm_expr_type y) ltac:(assumption)) in *.
  try rewrite (cm_pointer_encode__expression_add_safety (cm_expr_type x) ltac:(assumption)) in *.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in Hnode.
  cbn [cm_expr_code_counts cm_rcount_of cm_lcount_of] in Hnode.
  unfold cm_binary_tail_count in Hnode.
  unfold cm_i32_code_count, cm_rvalue_code_count in *.
  destruct (cm_pointerb (cm_expr_type y)); destruct (cm_pointerb (cm_expr_type x));
  cbn in Hnode; lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_34_split_goal_2 : cm_expr_counts_safety_wit_34_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst.
  cbn [cm_rep_expr_op] in *.
  subst.
  match goal with
  | H : cm_expr_counts_representable _ _ _ (CMBinaryE _ _ _ _) |- _ =>
    pose proof (proj1 H) as Hnode
  end.
  try rewrite (cm_pointer_encode__expression_add_safety (cm_expr_type y) ltac:(assumption)) in *.
  try rewrite (cm_pointer_encode__expression_add_safety (cm_expr_type x) ltac:(assumption)) in *.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in Hnode.
  cbn [cm_expr_code_counts cm_rcount_of cm_lcount_of] in Hnode.
  unfold cm_binary_tail_count in Hnode.
  unfold cm_i32_code_count, cm_rvalue_code_count in *.
  destruct (cm_pointerb (cm_expr_type y)); destruct (cm_pointerb (cm_expr_type x));
  cbn in Hnode; lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_34 : cm_expr_counts_safety_wit_34.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_34_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_34_split_goal_2.
Qed. 

Lemma proof_of_cm_expr_counts_safety_wit_35_split_goal_1 : cm_expr_counts_safety_wit_35_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst.
  cbn [cm_rep_expr_op] in *.
  subst.
  match goal with
  | H : cm_expr_counts_representable _ _ _ (CMBinaryE _ _ _ _) |- _ =>
    pose proof (proj1 H) as Hnode
  end.
  try rewrite (cm_pointer_encode__expression_add_safety (cm_expr_type y) ltac:(assumption)) in *.
  try rewrite (cm_pointer_encode__expression_add_safety (cm_expr_type x) ltac:(assumption)) in *.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in Hnode.
  cbn [cm_expr_code_counts cm_rcount_of cm_lcount_of] in Hnode.
  unfold cm_binary_tail_count in Hnode.
  unfold cm_i32_code_count, cm_rvalue_code_count in *.
  destruct (cm_pointerb (cm_expr_type y)); destruct (cm_pointerb (cm_expr_type x));
  cbn in Hnode; lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_35_split_goal_2 : cm_expr_counts_safety_wit_35_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst.
  cbn [cm_rep_expr_op] in *.
  subst.
  match goal with
  | H : cm_expr_counts_representable _ _ _ (CMBinaryE _ _ _ _) |- _ =>
    pose proof (proj1 H) as Hnode
  end.
  try rewrite (cm_pointer_encode__expression_add_safety (cm_expr_type y) ltac:(assumption)) in *.
  try rewrite (cm_pointer_encode__expression_add_safety (cm_expr_type x) ltac:(assumption)) in *.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in Hnode.
  cbn [cm_expr_code_counts cm_rcount_of cm_lcount_of] in Hnode.
  unfold cm_binary_tail_count in Hnode.
  unfold cm_i32_code_count, cm_rvalue_code_count in *.
  destruct (cm_pointerb (cm_expr_type y)); destruct (cm_pointerb (cm_expr_type x));
  cbn in Hnode; lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_35 : cm_expr_counts_safety_wit_35.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_35_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_35_split_goal_2.
Qed. 

Lemma proof_of_cm_expr_counts_safety_wit_37_split_goal_1 : cm_expr_counts_safety_wit_37_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst.
  cbn [cm_rep_expr_op] in *.
  subst.
  match goal with
  | H : cm_expr_counts_representable _ _ _ (CMBinaryE _ _ _ _) |- _ =>
    pose proof (proj1 H) as Hnode
  end.
  try rewrite (cm_pointer_encode__expression_add_safety (cm_expr_type y) ltac:(assumption)) in *.
  try rewrite (cm_pointer_encode__expression_add_safety (cm_expr_type x) ltac:(assumption)) in *.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in Hnode.
  cbn [cm_expr_code_counts cm_rcount_of cm_lcount_of] in Hnode.
  unfold cm_binary_tail_count in Hnode.
  unfold cm_i32_code_count, cm_rvalue_code_count in *.
  destruct (cm_pointerb (cm_expr_type y)); destruct (cm_pointerb (cm_expr_type x));
  cbn in Hnode; lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_37_split_goal_2 : cm_expr_counts_safety_wit_37_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst.
  cbn [cm_rep_expr_op] in *.
  subst.
  match goal with
  | H : cm_expr_counts_representable _ _ _ (CMBinaryE _ _ _ _) |- _ =>
    pose proof (proj1 H) as Hnode
  end.
  try rewrite (cm_pointer_encode__expression_add_safety (cm_expr_type y) ltac:(assumption)) in *.
  try rewrite (cm_pointer_encode__expression_add_safety (cm_expr_type x) ltac:(assumption)) in *.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in Hnode.
  cbn [cm_expr_code_counts cm_rcount_of cm_lcount_of] in Hnode.
  unfold cm_binary_tail_count in Hnode.
  unfold cm_i32_code_count, cm_rvalue_code_count in *.
  destruct (cm_pointerb (cm_expr_type y)); destruct (cm_pointerb (cm_expr_type x));
  cbn in Hnode; lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_37 : cm_expr_counts_safety_wit_37.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_37_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_37_split_goal_2.
Qed. 

Lemma proof_of_cm_expr_counts_safety_wit_38_split_goal_1 : cm_expr_counts_safety_wit_38_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst.
  cbn [cm_rep_expr_op] in *.
  subst.
  match goal with
  | H : cm_expr_counts_representable _ _ _ (CMBinaryE _ _ _ _) |- _ =>
    pose proof (proj1 H) as Hnode
  end.
  try rewrite (cm_pointer_encode__expression_add_safety (cm_expr_type y) ltac:(assumption)) in *.
  try rewrite (cm_pointer_encode__expression_add_safety (cm_expr_type x) ltac:(assumption)) in *.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in Hnode.
  cbn [cm_expr_code_counts cm_rcount_of cm_lcount_of] in Hnode.
  unfold cm_binary_tail_count in Hnode.
  unfold cm_i32_code_count, cm_rvalue_code_count in *.
  destruct (cm_pointerb (cm_expr_type y)); destruct (cm_pointerb (cm_expr_type x));
  cbn in Hnode; lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_38_split_goal_2 : cm_expr_counts_safety_wit_38_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst.
  cbn [cm_rep_expr_op] in *.
  subst.
  match goal with
  | H : cm_expr_counts_representable _ _ _ (CMBinaryE _ _ _ _) |- _ =>
    pose proof (proj1 H) as Hnode
  end.
  try rewrite (cm_pointer_encode__expression_add_safety (cm_expr_type y) ltac:(assumption)) in *.
  try rewrite (cm_pointer_encode__expression_add_safety (cm_expr_type x) ltac:(assumption)) in *.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in Hnode.
  cbn [cm_expr_code_counts cm_rcount_of cm_lcount_of] in Hnode.
  unfold cm_binary_tail_count in Hnode.
  unfold cm_i32_code_count, cm_rvalue_code_count in *.
  destruct (cm_pointerb (cm_expr_type y)); destruct (cm_pointerb (cm_expr_type x));
  cbn in Hnode; lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_38 : cm_expr_counts_safety_wit_38.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_38_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_38_split_goal_2.
Qed. 

Lemma proof_of_cm_expr_counts_safety_wit_41_split_goal_1 : cm_expr_counts_safety_wit_41_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e. cbn [cm_rep_expr_op] in *.
  cbn [cm_expr_counts_representable] in PreH37.
  destruct PreH37 as [Hnode _].
  unfold cm_expr_count_node_representable, cm_code_counts_representable in Hnode.
  cbn [cm_expr_code_counts cm_lcount_of cm_rcount_of] in Hnode.
  rewrite (cm_pointer_encode__expression_sub_safety (cm_expr_type x) PreH25) in PreH46.
  destruct (cm_pointerb (cm_expr_type x)) eqn:Hptr; [|contradiction].
  unfold cm_binary_tail_count in Hnode.
  unfold cm_i32_code_count in *.
  unfold cm_rvalue_code_count in *.
  subst op. rewrite Hptr in Hnode.
  destruct (cm_pointerb (cm_expr_type y)); cbn in Hnode; lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_41_split_goal_2 : cm_expr_counts_safety_wit_41_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold cm_i32_code_count in *.
  lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_41 : cm_expr_counts_safety_wit_41.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_41_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_41_split_goal_2.
Qed. 

Lemma proof_of_cm_expr_counts_safety_wit_42_split_goal_1 : cm_expr_counts_safety_wit_42_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e. cbn [cm_rep_expr_op] in *.
  cbn [cm_expr_counts_representable] in PreH37.
  destruct PreH37 as [Hnode _].
  unfold cm_expr_count_node_representable, cm_code_counts_representable in Hnode.
  cbn [cm_expr_code_counts cm_lcount_of cm_rcount_of] in Hnode.
  rewrite (cm_pointer_encode__expression_sub_safety (cm_expr_type x) PreH25) in PreH46.
  destruct (cm_pointerb (cm_expr_type x)) eqn:Hptr; [|contradiction].
  unfold cm_binary_tail_count in Hnode.
  unfold cm_i32_code_count in *.
  unfold cm_rvalue_code_count in *.
  subst op. rewrite Hptr in Hnode.
  destruct (cm_pointerb (cm_expr_type y)); cbn in Hnode; lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_42_split_goal_2 : cm_expr_counts_safety_wit_42_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold cm_i32_code_count in *.
  lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_42 : cm_expr_counts_safety_wit_42.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_42_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_42_split_goal_2.
Qed. 

Lemma proof_of_cm_expr_counts_safety_wit_44_split_goal_1 : cm_expr_counts_safety_wit_44_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e. cbn [cm_rep_expr_op] in *.
  cbn [cm_expr_counts_representable] in PreH37.
  destruct PreH37 as [Hnode _].
  unfold cm_expr_count_node_representable, cm_code_counts_representable in Hnode.
  cbn [cm_expr_code_counts cm_lcount_of cm_rcount_of] in Hnode.
  unfold cm_binary_tail_count in Hnode.
  unfold cm_i32_code_count in *.
  unfold cm_rvalue_code_count in *.
  repeat match type of Hnode with
  | context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b); cbn in Hnode
  | context [cm_pointerb ?t] => destruct (cm_pointerb t); cbn in Hnode
  end; lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_44_split_goal_2 : cm_expr_counts_safety_wit_44_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold cm_i32_code_count in *.
  lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_44 : cm_expr_counts_safety_wit_44.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_44_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_44_split_goal_2.
Qed. 

Lemma proof_of_cm_expr_counts_safety_wit_45_split_goal_1 : cm_expr_counts_safety_wit_45_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e. cbn [cm_rep_expr_op] in *.
  cbn [cm_expr_counts_representable] in PreH37.
  destruct PreH37 as [Hnode _].
  unfold cm_expr_count_node_representable, cm_code_counts_representable in Hnode.
  cbn [cm_expr_code_counts cm_lcount_of cm_rcount_of] in Hnode.
  unfold cm_binary_tail_count in Hnode.
  unfold cm_i32_code_count in *.
  unfold cm_rvalue_code_count in *.
  repeat match type of Hnode with
  | context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b); cbn in Hnode
  | context [cm_pointerb ?t] => destruct (cm_pointerb t); cbn in Hnode
  end; lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_45_split_goal_2 : cm_expr_counts_safety_wit_45_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold cm_i32_code_count in *.
  lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_45 : cm_expr_counts_safety_wit_45.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_45_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_45_split_goal_2.
Qed. 

Lemma proof_of_cm_expr_counts_safety_wit_47_split_goal_1 : cm_expr_counts_safety_wit_47_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e. cbn [cm_rep_expr_op] in *.
  cbn [cm_expr_counts_representable] in PreH37.
  destruct PreH37 as [Hnode _].
  unfold cm_expr_count_node_representable, cm_code_counts_representable in Hnode.
  cbn [cm_expr_code_counts cm_lcount_of cm_rcount_of] in Hnode.
  unfold cm_binary_tail_count in Hnode.
  unfold cm_i32_code_count in *.
  unfold cm_rvalue_code_count in *.
  repeat match type of Hnode with
  | context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b); cbn in Hnode
  | context [cm_pointerb ?t] => destruct (cm_pointerb t); cbn in Hnode
  end; lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_47_split_goal_2 : cm_expr_counts_safety_wit_47_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold cm_i32_code_count in *.
  lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_47 : cm_expr_counts_safety_wit_47.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_47_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_47_split_goal_2.
Qed. 

Lemma proof_of_cm_expr_counts_safety_wit_48_split_goal_1 : cm_expr_counts_safety_wit_48_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e. cbn [cm_rep_expr_op] in *.
  cbn [cm_expr_counts_representable] in PreH37.
  destruct PreH37 as [Hnode _].
  unfold cm_expr_count_node_representable, cm_code_counts_representable in Hnode.
  cbn [cm_expr_code_counts cm_lcount_of cm_rcount_of] in Hnode.
  unfold cm_binary_tail_count in Hnode.
  unfold cm_i32_code_count in *.
  unfold cm_rvalue_code_count in *.
  repeat match type of Hnode with
  | context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b); cbn in Hnode
  | context [cm_pointerb ?t] => destruct (cm_pointerb t); cbn in Hnode
  end; lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_48_split_goal_2 : cm_expr_counts_safety_wit_48_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold cm_i32_code_count in *.
  lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_48 : cm_expr_counts_safety_wit_48.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_48_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_48_split_goal_2.
Qed. 

Lemma proof_of_cm_expr_counts_safety_wit_52_split_goal_1 : cm_expr_counts_safety_wit_52_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e.
  cbn [cm_rep_expr_op] in *.
  subst op.
  match goal with
  | H : cm_expr_counts_representable _ _ _ (CMUnaryE _ _ _) |- _ =>
      cbn [cm_expr_counts_representable] in H;
      unfold cm_expr_count_node_representable, cm_code_counts_representable,
        cm_i32_code_count in H;
      cbn [cm_expr_code_counts cm_lcount_of cm_rcount_of] in H;
      rewrite Z.eqb_refl in H;
      cbn [cm_lcount_of cm_rcount_of] in H
  end.
  dump_pre_spatial.
  unfold cm_rvalue_code_count.
  lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_52_split_goal_2 : cm_expr_counts_safety_wit_52_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold cm_i32_code_count in *.
  lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_52 : cm_expr_counts_safety_wit_52.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_52_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_52_split_goal_2.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_55_split_goal_1 : cm_expr_counts_safety_wit_55_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e.
  cbn [cm_rep_expr_op] in *.
  match goal with
  | H : cm_expr_counts_representable _ _ _ (CMUnaryE _ _ _) |- _ =>
      cbn [cm_expr_counts_representable] in H;
      unfold cm_expr_count_node_representable, cm_code_counts_representable,
        cm_i32_code_count in H;
      cbn [cm_expr_code_counts] in H
  end.
  assert (E2 : Z.eqb op 2 = false) by (apply Z.eqb_neq; assumption).
  assert (E3 : Z.eqb op 3 = false) by (apply Z.eqb_neq; assumption).
  rewrite E2, E3 in *.
  cbn [cm_lcount_of cm_rcount_of] in *.
  dump_pre_spatial.
  unfold cm_rvalue_code_count.
  lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_55_split_goal_2 : cm_expr_counts_safety_wit_55_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold cm_i32_code_count in *.
  lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_55 : cm_expr_counts_safety_wit_55.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_55_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_55_split_goal_2.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_58_split_goal_1 : cm_expr_counts_safety_wit_58_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e.
  match goal with
  | H : cm_expr_counts_representable _ _ _ (CMIndexE _ _ _) |- _ =>
      cbn [cm_expr_counts_representable] in H;
      unfold cm_expr_count_node_representable, cm_code_counts_representable,
        cm_i32_code_count in H;
      cbn [cm_expr_code_counts cm_lcount_of cm_rcount_of] in H
  end.
  dump_pre_spatial.
  unfold cm_rvalue_code_count.
  lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_58_split_goal_2 : cm_expr_counts_safety_wit_58_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold cm_i32_code_count in *.
  lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_58 : cm_expr_counts_safety_wit_58.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_58_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_58_split_goal_2.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_59_split_goal_1 : cm_expr_counts_safety_wit_59_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e.
  match goal with
  | H : cm_expr_counts_representable _ _ _ (CMIndexE _ _ _) |- _ =>
      cbn [cm_expr_counts_representable] in H;
      unfold cm_expr_count_node_representable, cm_code_counts_representable,
        cm_i32_code_count in H;
      cbn [cm_expr_code_counts cm_lcount_of cm_rcount_of] in H
  end.
  dump_pre_spatial.
  unfold cm_i32_code_count, cm_rvalue_code_count in *.
  lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_59_split_goal_2 : cm_expr_counts_safety_wit_59_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold cm_i32_code_count in *.
  lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_59 : cm_expr_counts_safety_wit_59.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_59_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_59_split_goal_2.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_61_split_goal_1 : cm_expr_counts_safety_wit_61_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e.
  match goal with
  | H : cm_expr_counts_representable _ _ _ (CMIndexE _ _ _) |- _ =>
      cbn [cm_expr_counts_representable] in H;
      unfold cm_expr_count_node_representable, cm_code_counts_representable,
        cm_i32_code_count in H;
      cbn [cm_expr_code_counts cm_lcount_of cm_rcount_of] in H
  end.
  dump_pre_spatial.
  unfold cm_rvalue_code_count.
  lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_61_split_goal_2 : cm_expr_counts_safety_wit_61_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold cm_i32_code_count in *.
  lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_61 : cm_expr_counts_safety_wit_61.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_61_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_61_split_goal_2.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_64_split_goal_1 : cm_expr_counts_safety_wit_64_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_expr_counts_representable] in PreH21.
  destruct PreH21 as [Hnode _].
  unfold cm_expr_count_node_representable, cm_code_counts_representable, cm_i32_code_count in Hnode.
  cbn [cm_expr_code_counts cm_lcount_of cm_rcount_of] in Hnode.
  unfold cm_rvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_64_split_goal_2 : cm_expr_counts_safety_wit_64_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold cm_i32_code_count in PreH12.
  lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_64 : cm_expr_counts_safety_wit_64.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_64_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_64_split_goal_2.
Qed. 

Lemma proof_of_cm_expr_counts_safety_wit_66_split_goal_1 : cm_expr_counts_safety_wit_66_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_member_base_type cm_rep_expr_value] in PreH1.
  rewrite signed_last_nbits_eq in PreH1 by (cbn; lia).
  cbn [cm_expr_counts_representable] in PreH31.
  destruct PreH31 as [Hnode _].
  unfold cm_expr_count_node_representable, cm_code_counts_representable, cm_i32_code_count in Hnode.
  cbn [cm_expr_code_counts cm_lcount_of cm_rcount_of] in Hnode.
  rewrite PreH1 in Hnode.
  cbn in Hnode.
  unfold cm_rvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_66_split_goal_2 : cm_expr_counts_safety_wit_66_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold cm_i32_code_count in PreH22.
  lia.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_66 : cm_expr_counts_safety_wit_66.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_66_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_66_split_goal_2.
Qed. 

Lemma proof_of_cm_expr_counts_safety_wit_70_split_goal_1 : cm_expr_counts_safety_wit_70_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst. dump_pre_spatial.
  unfold cm_rvalue_code_count.
  match goal with
  | H : cm_expr_counts_representable _ _ _ (CMPutcE _ _) |- _ =>
    cbn [cm_expr_counts_representable] in H;
    unfold cm_expr_count_node_representable, cm_code_counts_representable,
      cm_i32_code_count in H;
    cbn [cm_expr_code_counts cm_lcount_of cm_rcount_of] in H;
    intuition int_auto
  end.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_70_split_goal_2 : cm_expr_counts_safety_wit_70_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst. dump_pre_spatial.
  unfold cm_rvalue_code_count.
  match goal with
  | H : cm_expr_counts_representable _ _ _ (CMPutcE _ _) |- _ =>
    cbn [cm_expr_counts_representable] in H;
    unfold cm_expr_count_node_representable, cm_code_counts_representable,
      cm_i32_code_count in H;
    cbn [cm_expr_code_counts cm_lcount_of cm_rcount_of] in H;
    intuition int_auto
  end.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_70 : cm_expr_counts_safety_wit_70.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_70_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_70_split_goal_2.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_73_split_goal_1 : cm_expr_counts_safety_wit_73_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst. dump_pre_spatial.
  unfold cm_rvalue_code_count.
  match goal with
  | H : cm_expr_counts_representable _ _ _ (CMPutiE _ _) |- _ =>
    cbn [cm_expr_counts_representable] in H;
    unfold cm_expr_count_node_representable, cm_code_counts_representable,
      cm_i32_code_count in H;
    cbn [cm_expr_code_counts cm_lcount_of cm_rcount_of] in H;
    intuition int_auto
  end.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_73_split_goal_2 : cm_expr_counts_safety_wit_73_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst. dump_pre_spatial.
  unfold cm_rvalue_code_count.
  match goal with
  | H : cm_expr_counts_representable _ _ _ (CMPutiE _ _) |- _ =>
    cbn [cm_expr_counts_representable] in H;
    unfold cm_expr_count_node_representable, cm_code_counts_representable,
      cm_i32_code_count in H;
    cbn [cm_expr_code_counts cm_lcount_of cm_rcount_of] in H;
    intuition int_auto
  end.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_73 : cm_expr_counts_safety_wit_73.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_73_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_73_split_goal_2.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_75_split_goal_1 : cm_expr_counts_safety_wit_75_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst. dump_pre_spatial.
  unfold cm_rvalue_code_count.
  match goal with
  | H : cm_expr_counts_representable _ _ _ (CMExitE _ _) |- _ =>
    cbn [cm_expr_counts_representable] in H;
    unfold cm_expr_count_node_representable, cm_code_counts_representable,
      cm_i32_code_count in H;
    cbn [cm_expr_code_counts cm_lcount_of cm_rcount_of] in H;
    intuition int_auto
  end.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_75_split_goal_2 : cm_expr_counts_safety_wit_75_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst. dump_pre_spatial.
  unfold cm_rvalue_code_count.
  match goal with
  | H : cm_expr_counts_representable _ _ _ (CMExitE _ _) |- _ =>
    cbn [cm_expr_counts_representable] in H;
    unfold cm_expr_count_node_representable, cm_code_counts_representable,
      cm_i32_code_count in H;
    cbn [cm_expr_code_counts cm_lcount_of cm_rcount_of] in H;
    intuition int_auto
  end.
Qed.

Lemma proof_of_cm_expr_counts_safety_wit_75 : cm_expr_counts_safety_wit_75.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_75_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_safety_wit_75_split_goal_2.
Qed.

Lemma proof_of_cm_expr_counts_entail_wit_1 : cm_expr_counts_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_expr_rep_node. unfold cm_expr_node.
  Intros pa pb pargs.
  Exists pargs pb pa.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_cm_expr_counts_entail_wit_2 : cm_expr_counts_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn [cm_rep_expr_kind] in PreH1; try discriminate.
  match type of PreH13 with
  | cm_expr_wf _ _ _ (CMVarE ?scope ?slot ?ty) =>
      Exists pargs_2 pb_2 pa_2 scope slot ty
  end.
  cbn [cm_expr_wf] in PreH13.
  cbn [cm_expr_counts_representable] in PreH14.
  unfold cm_i32_code_count in PreH14.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial;
      cbn [cm_expr_wf cm_expr_counts_representable];
      unfold cm_i32_code_count; tauto.
Qed.

Lemma proof_of_cm_expr_counts_entail_wit_3 : cm_expr_counts_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn [cm_rep_expr_kind] in *; try discriminate.
  match goal with |- context [CMAssignE ?x ?y ?ty] =>
    Exists pb_2 pa_2 pargs_2 x y ty
  end.
  cbn [cm_expr_payload]. Intros.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial;
      cbn [cm_expr_wf cm_expr_counts_representable] in *; tauto.
Qed.

Lemma proof_of_cm_expr_counts_entail_wit_4 : cm_expr_counts_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn [cm_rep_expr_kind] in *; try discriminate.
  match goal with |- context [CMBinaryE ?op ?x ?y ?ty] =>
    Exists pb_2 pa_2 pargs_2 op x y ty
  end.
  cbn [cm_expr_payload]. Intros.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial;
      cbn [cm_expr_wf cm_expr_counts_representable] in *; tauto.
Qed.

Lemma proof_of_cm_expr_counts_entail_wit_5 : cm_expr_counts_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn [cm_rep_expr_kind] in *; try discriminate.
  Exists pargs_2 pb_2 pa_2 op e ty.
  cbn [cm_expr_payload].
  Intros_p Hpayload.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity;
    cbn [cm_expr_wf cm_expr_counts_representable] in *; tauto.
Qed.

Lemma proof_of_cm_expr_counts_entail_wit_6 : cm_expr_counts_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn [cm_rep_expr_kind] in *; try discriminate.
  match goal with |- context [CMIndexE ?x ?y ?ty] =>
    Exists pb_2 pa_2 pargs_2 x y ty
  end.
  cbn [cm_expr_payload]. Intros.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial;
      cbn [cm_expr_wf cm_expr_counts_representable] in *; tauto.
Qed.

Lemma proof_of_cm_expr_counts_entail_wit_7 : cm_expr_counts_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn [cm_rep_expr_kind] in *; try discriminate.
  Exists pargs_2 pb_2 pa_2 e mid ty.
  cbn [cm_expr_payload].
  Intros_p Hpayload.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity;
    cbn [cm_expr_wf cm_expr_counts_representable] in *;
    unfold cm_i32_code_count in *; tauto.
Qed.

Lemma proof_of_cm_expr_counts_entail_wit_8 : cm_expr_counts_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn [cm_rep_expr_kind] in *; try discriminate.
  match goal with
  | Hwf : cm_expr_wf _ _ _ (CMCallE _ _ _),
    Hrep : cm_expr_counts_representable _ _ _ (CMCallE _ _ _) |- _ =>
      apply cm_expr_wf_call in Hwf;
      apply cm_expr_counts_repr_call in Hrep;
      destruct Hwf as [? [? ?]];
      destruct Hrep as [? [? ?]]
  end.
  cbn [cm_expr_payload]. Intros.
  match goal with
  | H : cm_expr_count_node_representable _ _ _ (CMCallE ?callee ?args ?ty) |- _ =>
      Exists pargs_2 pb_2 pa_2 callee args ty
  end.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity;
      try (apply cm_expr_wf_call; tauto);
      try (apply cm_expr_counts_repr_call; tauto); tauto.
Qed.

Lemma proof_of_cm_expr_counts_entail_wit_9 : cm_expr_counts_entail_wit_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn [cm_rep_expr_kind] in *; try discriminate.
  Exists pargs_2 pb_2 pa_2 e ty.
  cbn [cm_expr_payload].
  Intros_p Hpayload.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity;
    cbn [cm_expr_wf cm_expr_counts_representable] in *; tauto.
Qed.

Lemma proof_of_cm_expr_counts_entail_wit_10 : cm_expr_counts_entail_wit_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn [cm_rep_expr_kind] in *; try discriminate.
  Exists pargs_2 pb_2 pa_2 e ty.
  cbn [cm_expr_payload].
  Intros_p Hpayload.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity;
    cbn [cm_expr_wf cm_expr_counts_representable] in *; tauto.
Qed.

Lemma proof_of_cm_expr_counts_entail_wit_11 : cm_expr_counts_entail_wit_11.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn [cm_rep_expr_kind] in *; try contradiction.
  Exists pargs_2 pb_2 pa_2 e ty.
  cbn [cm_expr_payload].
  Intros_p Hpayload.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity;
    cbn [cm_expr_wf cm_expr_counts_representable] in *; tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_1_split_goal_1 : cm_expr_counts_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  destruct e; cbn [cm_expr_counts_representable] in *;
    unfold cm_expr_count_node_representable, cm_code_counts_representable in *;
    unfold cm_lvalue_code_count, cm_rvalue_code_count in *; tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_1_split_goal_2 : cm_expr_counts_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  destruct e; cbn [cm_expr_counts_representable] in *;
    unfold cm_expr_count_node_representable, cm_code_counts_representable in *;
    unfold cm_lvalue_code_count, cm_rvalue_code_count in *; tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_1_split_goal_3 : cm_expr_counts_return_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  destruct e; cbn [cm_expr_counts_representable] in *;
    unfold cm_expr_count_node_representable, cm_code_counts_representable in *;
    unfold cm_lvalue_code_count, cm_rvalue_code_count in *; tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_1_split_goal_4 : cm_expr_counts_return_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  destruct e; cbn [cm_expr_counts_representable] in *;
    unfold cm_expr_count_node_representable, cm_code_counts_representable in *;
    unfold cm_lvalue_code_count, cm_rvalue_code_count in *; tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_1_split_goal_5 : cm_expr_counts_return_wit_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  destruct e; cbn [cm_rep_expr_kind] in *; try discriminate; reflexivity.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_1_split_goal_6 : cm_expr_counts_return_wit_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  destruct e; cbn [cm_rep_expr_kind] in *; try discriminate; reflexivity.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_1_split_goal_spatial : cm_expr_counts_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite cm_expr_rep_node.
  unfold cm_expr_node.
  Exists pa pb pargs.
  split_pure_spatial.
  - sepcon_right_assoc. cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_1 : cm_expr_counts_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_cm_expr_counts_return_wit_1_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_return_wit_1_split_goal_2.
  - Goal_apply proof_of_cm_expr_counts_return_wit_1_split_goal_3.
  - Goal_apply proof_of_cm_expr_counts_return_wit_1_split_goal_4.
  - Goal_apply proof_of_cm_expr_counts_return_wit_1_split_goal_5.
  - Goal_apply proof_of_cm_expr_counts_return_wit_1_split_goal_6.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_2_split_goal_1 : cm_expr_counts_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  destruct e; cbn [cm_expr_counts_representable] in *;
    unfold cm_expr_count_node_representable, cm_code_counts_representable in *;
    unfold cm_lvalue_code_count, cm_rvalue_code_count in *; tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_2_split_goal_2 : cm_expr_counts_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  destruct e; cbn [cm_expr_counts_representable] in *;
    unfold cm_expr_count_node_representable, cm_code_counts_representable in *;
    unfold cm_lvalue_code_count, cm_rvalue_code_count in *; tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_2_split_goal_3 : cm_expr_counts_return_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  destruct e; cbn [cm_expr_counts_representable] in *;
    unfold cm_expr_count_node_representable, cm_code_counts_representable in *;
    unfold cm_lvalue_code_count, cm_rvalue_code_count in *; tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_2_split_goal_4 : cm_expr_counts_return_wit_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  destruct e; cbn [cm_expr_counts_representable] in *;
    unfold cm_expr_count_node_representable, cm_code_counts_representable in *;
    unfold cm_lvalue_code_count, cm_rvalue_code_count in *; tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_2_split_goal_5 : cm_expr_counts_return_wit_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  destruct e; cbn [cm_rep_expr_kind] in *; try discriminate; reflexivity.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_2_split_goal_6 : cm_expr_counts_return_wit_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  destruct e; cbn [cm_rep_expr_kind] in *; try discriminate; reflexivity.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_2_split_goal_spatial : cm_expr_counts_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite cm_expr_rep_node.
  unfold cm_expr_node.
  Exists pa pb pargs.
  split_pure_spatial.
  - sepcon_right_assoc. cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_2 : cm_expr_counts_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_cm_expr_counts_return_wit_2_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_return_wit_2_split_goal_2.
  - Goal_apply proof_of_cm_expr_counts_return_wit_2_split_goal_3.
  - Goal_apply proof_of_cm_expr_counts_return_wit_2_split_goal_4.
  - Goal_apply proof_of_cm_expr_counts_return_wit_2_split_goal_5.
  - Goal_apply proof_of_cm_expr_counts_return_wit_2_split_goal_6.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_3_split_goal_1 : cm_expr_counts_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  destruct e; cbn [cm_expr_counts_representable] in *;
    unfold cm_expr_count_node_representable, cm_code_counts_representable in *;
    unfold cm_lvalue_code_count, cm_rvalue_code_count in *; tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_3_split_goal_2 : cm_expr_counts_return_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  destruct e; cbn [cm_expr_counts_representable] in *;
    unfold cm_expr_count_node_representable, cm_code_counts_representable in *;
    unfold cm_lvalue_code_count, cm_rvalue_code_count in *; tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_3_split_goal_3 : cm_expr_counts_return_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  destruct e; cbn [cm_expr_counts_representable] in *;
    unfold cm_expr_count_node_representable, cm_code_counts_representable in *;
    unfold cm_lvalue_code_count, cm_rvalue_code_count in *; tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_3_split_goal_4 : cm_expr_counts_return_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  destruct e; cbn [cm_expr_counts_representable] in *;
    unfold cm_expr_count_node_representable, cm_code_counts_representable in *;
    unfold cm_lvalue_code_count, cm_rvalue_code_count in *; tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_3_split_goal_5 : cm_expr_counts_return_wit_3_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  destruct e; cbn [cm_rep_expr_kind] in *; try discriminate; reflexivity.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_3_split_goal_6 : cm_expr_counts_return_wit_3_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  destruct e; cbn [cm_rep_expr_kind] in *; try discriminate; reflexivity.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_3_split_goal_spatial : cm_expr_counts_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite cm_expr_rep_node.
  unfold cm_expr_node.
  Exists pa pb pargs.
  split_pure_spatial.
  - sepcon_right_assoc. cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_3 : cm_expr_counts_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_return_wit_3_split_goal_spatial.
  - Goal_apply proof_of_cm_expr_counts_return_wit_3_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_return_wit_3_split_goal_2.
  - Goal_apply proof_of_cm_expr_counts_return_wit_3_split_goal_3.
  - Goal_apply proof_of_cm_expr_counts_return_wit_3_split_goal_4.
  - Goal_apply proof_of_cm_expr_counts_return_wit_3_split_goal_5.
  - Goal_apply proof_of_cm_expr_counts_return_wit_3_split_goal_6.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_4_split_goal_1 : cm_expr_counts_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  destruct e; cbn [cm_expr_counts_representable] in *;
    unfold cm_expr_count_node_representable, cm_code_counts_representable in *;
    unfold cm_lvalue_code_count, cm_rvalue_code_count in *; tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_4_split_goal_2 : cm_expr_counts_return_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  destruct e; cbn [cm_expr_counts_representable] in *;
    unfold cm_expr_count_node_representable, cm_code_counts_representable in *;
    unfold cm_lvalue_code_count, cm_rvalue_code_count in *; tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_4_split_goal_3 : cm_expr_counts_return_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  destruct e; cbn [cm_expr_counts_representable] in *;
    unfold cm_expr_count_node_representable, cm_code_counts_representable in *;
    unfold cm_lvalue_code_count, cm_rvalue_code_count in *; tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_4_split_goal_4 : cm_expr_counts_return_wit_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  destruct e; cbn [cm_expr_counts_representable] in *;
    unfold cm_expr_count_node_representable, cm_code_counts_representable in *;
    unfold cm_lvalue_code_count, cm_rvalue_code_count in *; tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_4_split_goal_5 : cm_expr_counts_return_wit_4_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  destruct e; cbn [cm_rep_expr_kind] in *; try discriminate; reflexivity.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_4_split_goal_6 : cm_expr_counts_return_wit_4_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  destruct e; cbn [cm_rep_expr_kind] in *; try discriminate; reflexivity.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_4_split_goal_spatial : cm_expr_counts_return_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite cm_expr_rep_node.
  unfold cm_expr_node.
  Exists pa pb pargs.
  split_pure_spatial.
  - sepcon_right_assoc. cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_4 : cm_expr_counts_return_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_return_wit_4_split_goal_spatial.
  - Goal_apply proof_of_cm_expr_counts_return_wit_4_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_return_wit_4_split_goal_2.
  - Goal_apply proof_of_cm_expr_counts_return_wit_4_split_goal_3.
  - Goal_apply proof_of_cm_expr_counts_return_wit_4_split_goal_4.
  - Goal_apply proof_of_cm_expr_counts_return_wit_4_split_goal_5.
  - Goal_apply proof_of_cm_expr_counts_return_wit_4_split_goal_6.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_5_split_goal_1 : cm_expr_counts_return_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_expr_counts_representable] in PreH24.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH24.
  unfold cm_rvalue_code_count, cm_lvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_5_split_goal_2 : cm_expr_counts_return_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_expr_counts_representable] in PreH24.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH24.
  unfold cm_rvalue_code_count, cm_lvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_5_split_goal_3 : cm_expr_counts_return_wit_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_expr_counts_representable] in PreH24.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH24.
  unfold cm_rvalue_code_count, cm_lvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_5_split_goal_4 : cm_expr_counts_return_wit_5_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_expr_counts_representable] in PreH24.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH24.
  unfold cm_rvalue_code_count, cm_lvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_5_split_goal_5 : cm_expr_counts_return_wit_5_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e. reflexivity.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_5_split_goal_6 : cm_expr_counts_return_wit_5_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_rep_expr_op cm_rep_expr_value] in PreH9.
  assert (Hslot : signed_last_nbits slot 32 = slot) by
    (apply signed_last_nbits_eq; [lia | cbn; lia]).
  rewrite Hslot in PreH9.
  cbn [cm_rvalue_code_count cm_expr_code_counts cm_rcount_of cm_rep_expr_op].
  rewrite PreH9. reflexivity.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_5_split_goal_spatial : cm_expr_counts_return_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_expr_rep_node. unfold cm_expr_node.
  Exists pa pb pargs.
  split_pure_spatial.
  - repeat progress cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_5 : cm_expr_counts_return_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_expr_counts_return_wit_5_split_goal_spatial.
  Goal_apply proof_of_cm_expr_counts_return_wit_5_split_goal_1.
  Goal_apply proof_of_cm_expr_counts_return_wit_5_split_goal_2.
  Goal_apply proof_of_cm_expr_counts_return_wit_5_split_goal_3.
  Goal_apply proof_of_cm_expr_counts_return_wit_5_split_goal_4.
  Goal_apply proof_of_cm_expr_counts_return_wit_5_split_goal_5.
  Goal_apply proof_of_cm_expr_counts_return_wit_5_split_goal_6.
Qed. 

Lemma proof_of_cm_expr_counts_return_wit_6_split_goal_1 : cm_expr_counts_return_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_expr_counts_representable] in PreH24.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH24.
  unfold cm_rvalue_code_count, cm_lvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_6_split_goal_2 : cm_expr_counts_return_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_expr_counts_representable] in PreH24.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH24.
  unfold cm_rvalue_code_count, cm_lvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_6_split_goal_3 : cm_expr_counts_return_wit_6_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_expr_counts_representable] in PreH24.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH24.
  unfold cm_rvalue_code_count, cm_lvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_6_split_goal_4 : cm_expr_counts_return_wit_6_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_expr_counts_representable] in PreH24.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH24.
  unfold cm_rvalue_code_count, cm_lvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_6_split_goal_5 : cm_expr_counts_return_wit_6_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e. reflexivity.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_6_split_goal_6 : cm_expr_counts_return_wit_6_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_rep_expr_op cm_rep_expr_value] in PreH9.
  assert (Hslot : signed_last_nbits slot 32 = slot) by
    (apply signed_last_nbits_eq; [lia | cbn; lia]).
  rewrite Hslot in PreH9.
  cbn [cm_rvalue_code_count cm_expr_code_counts cm_rcount_of cm_rep_expr_op].
  apply Z.eqb_neq in PreH9. rewrite PreH9. lia.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_6_split_goal_spatial : cm_expr_counts_return_wit_6_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_expr_rep_node. unfold cm_expr_node.
  Exists pa pb pargs.
  split_pure_spatial.
  - repeat progress cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_6 : cm_expr_counts_return_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_expr_counts_return_wit_6_split_goal_spatial.
  Goal_apply proof_of_cm_expr_counts_return_wit_6_split_goal_1.
  Goal_apply proof_of_cm_expr_counts_return_wit_6_split_goal_2.
  Goal_apply proof_of_cm_expr_counts_return_wit_6_split_goal_3.
  Goal_apply proof_of_cm_expr_counts_return_wit_6_split_goal_4.
  Goal_apply proof_of_cm_expr_counts_return_wit_6_split_goal_5.
  Goal_apply proof_of_cm_expr_counts_return_wit_6_split_goal_6.
Qed. 

Lemma proof_of_cm_expr_counts_return_wit_7_split_goal_1 : cm_expr_counts_return_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst e. exact (proj2 (proj1 (proj1 PreH42))).
Qed.

Lemma proof_of_cm_expr_counts_return_wit_7_split_goal_2 : cm_expr_counts_return_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst e. exact (proj1 (proj1 (proj1 PreH42))).
Qed.

Lemma proof_of_cm_expr_counts_return_wit_7_split_goal_3 : cm_expr_counts_return_wit_7_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst e. exact (proj2 (proj2 (proj1 PreH42))).
Qed.

Lemma proof_of_cm_expr_counts_return_wit_7_split_goal_4 : cm_expr_counts_return_wit_7_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst e. exact (proj1 (proj2 (proj1 PreH42))).
Qed.

Lemma proof_of_cm_expr_counts_return_wit_7_split_goal_5 : cm_expr_counts_return_wit_7_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst e. reflexivity.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_7_split_goal_6 : cm_expr_counts_return_wit_7_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst e.
  pose proof (proj1 (proj2 (proj1 PreH42))) as Hwf.
  cbn [cm_expr_type] in Hwf, PreH9.
  rewrite (cm_normalize_encode__expression_assignment_result ty Hwf) in PreH9.
  unfold cm_lvalue_code_count, cm_rvalue_code_count.
  cbn [cm_expr_code_counts cm_lcount_of cm_rcount_of]. lia.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_7_split_goal_spatial : cm_expr_counts_return_wit_7_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (cm_expr_rep_node expr_pre e). unfold cm_expr_node.
  Exists pa pb pargs.
  subst e. cbn [cm_expr_payload].
  split_pure_spatial.
  - sepcon_right_assoc. cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_7 : cm_expr_counts_return_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_expr_counts_return_wit_7_split_goal_spatial.
  Goal_apply proof_of_cm_expr_counts_return_wit_7_split_goal_1.
  Goal_apply proof_of_cm_expr_counts_return_wit_7_split_goal_2.
  Goal_apply proof_of_cm_expr_counts_return_wit_7_split_goal_3.
  Goal_apply proof_of_cm_expr_counts_return_wit_7_split_goal_4.
  Goal_apply proof_of_cm_expr_counts_return_wit_7_split_goal_5.
  Goal_apply proof_of_cm_expr_counts_return_wit_7_split_goal_6.
Qed. 

Lemma proof_of_cm_expr_counts_return_wit_8_split_goal_1 : cm_expr_counts_return_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct e; cbn [cm_expr_counts_representable] in PreH42;
  exact (proj2 (proj1 (proj1 PreH42))).
Qed.

Lemma proof_of_cm_expr_counts_return_wit_8_split_goal_2 : cm_expr_counts_return_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct e; cbn [cm_expr_counts_representable] in PreH42;
  exact (proj1 (proj1 (proj1 PreH42))).
Qed.

Lemma proof_of_cm_expr_counts_return_wit_8_split_goal_3 : cm_expr_counts_return_wit_8_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct e; cbn [cm_expr_counts_representable] in PreH42;
  exact (proj2 (proj2 (proj1 PreH42))).
Qed.

Lemma proof_of_cm_expr_counts_return_wit_8_split_goal_4 : cm_expr_counts_return_wit_8_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct e; cbn [cm_expr_counts_representable] in PreH42;
  exact (proj1 (proj2 (proj1 PreH42))).
Qed.

Lemma proof_of_cm_expr_counts_return_wit_8_split_goal_5 : cm_expr_counts_return_wit_8_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite PreH43. reflexivity.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_8_split_goal_6 : cm_expr_counts_return_wit_8_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e. cbn [cm_rep_expr_op] in PreH9. subst op.
  unfold cm_rvalue_code_count. cbn [cm_expr_code_counts cm_rcount_of Z.eqb Pos.eqb orb]. lia.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_8_split_goal_spatial : cm_expr_counts_return_wit_8_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (cm_expr_rep_node expr_pre e).
  unfold cm_expr_node.
  Exists pa pb pargs.
  rewrite PreH43.
  cbn [cm_expr_payload].
  split_pure_spatial.
  - sepcon_right_assoc. cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_8 : cm_expr_counts_return_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_return_wit_8_split_goal_spatial.
  - Goal_apply proof_of_cm_expr_counts_return_wit_8_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_return_wit_8_split_goal_2.
  - Goal_apply proof_of_cm_expr_counts_return_wit_8_split_goal_3.
  - Goal_apply proof_of_cm_expr_counts_return_wit_8_split_goal_4.
  - Goal_apply proof_of_cm_expr_counts_return_wit_8_split_goal_5.
  - Goal_apply proof_of_cm_expr_counts_return_wit_8_split_goal_6.
Qed. 

Lemma proof_of_cm_expr_counts_return_wit_9_split_goal_1 : cm_expr_counts_return_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct e; cbn [cm_expr_counts_representable] in PreH43;
  exact (proj2 (proj1 (proj1 PreH43))).
Qed.

Lemma proof_of_cm_expr_counts_return_wit_9_split_goal_2 : cm_expr_counts_return_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct e; cbn [cm_expr_counts_representable] in PreH43;
  exact (proj1 (proj1 (proj1 PreH43))).
Qed.

Lemma proof_of_cm_expr_counts_return_wit_9_split_goal_3 : cm_expr_counts_return_wit_9_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct e; cbn [cm_expr_counts_representable] in PreH43;
  exact (proj2 (proj2 (proj1 PreH43))).
Qed.

Lemma proof_of_cm_expr_counts_return_wit_9_split_goal_4 : cm_expr_counts_return_wit_9_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct e; cbn [cm_expr_counts_representable] in PreH43;
  exact (proj1 (proj2 (proj1 PreH43))).
Qed.

Lemma proof_of_cm_expr_counts_return_wit_9_split_goal_5 : cm_expr_counts_return_wit_9_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite PreH44. reflexivity.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_9_split_goal_6 : cm_expr_counts_return_wit_9_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e. cbn [cm_rep_expr_op] in PreH9. subst op.
  unfold cm_rvalue_code_count. cbn [cm_expr_code_counts cm_rcount_of Z.eqb Pos.eqb orb]. lia.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_9_split_goal_spatial : cm_expr_counts_return_wit_9_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (cm_expr_rep_node expr_pre e).
  unfold cm_expr_node.
  Exists pa pb pargs.
  rewrite PreH44.
  cbn [cm_expr_payload].
  split_pure_spatial.
  - sepcon_right_assoc. cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_9 : cm_expr_counts_return_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_return_wit_9_split_goal_spatial.
  - Goal_apply proof_of_cm_expr_counts_return_wit_9_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_return_wit_9_split_goal_2.
  - Goal_apply proof_of_cm_expr_counts_return_wit_9_split_goal_3.
  - Goal_apply proof_of_cm_expr_counts_return_wit_9_split_goal_4.
  - Goal_apply proof_of_cm_expr_counts_return_wit_9_split_goal_5.
  - Goal_apply proof_of_cm_expr_counts_return_wit_9_split_goal_6.
Qed. 

Lemma proof_of_cm_expr_counts_return_wit_10_split_goal_1 : cm_expr_counts_return_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_expr_counts_representable] in PreH44.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH44.
  unfold cm_rvalue_code_count, cm_lvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_10_split_goal_2 : cm_expr_counts_return_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_expr_counts_representable] in PreH44.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH44.
  unfold cm_rvalue_code_count, cm_lvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_10_split_goal_3 : cm_expr_counts_return_wit_10_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_expr_counts_representable] in PreH44.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH44.
  unfold cm_rvalue_code_count, cm_lvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_10_split_goal_4 : cm_expr_counts_return_wit_10_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_expr_counts_representable] in PreH44.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH44.
  unfold cm_rvalue_code_count, cm_lvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_10_split_goal_5 : cm_expr_counts_return_wit_10_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e. reflexivity.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_10_split_goal_6 : cm_expr_counts_return_wit_10_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e. cbn [cm_rep_expr_op] in PreH9. subst op.
  rewrite cm_pointer_encode__expression_add_results in PreH53 by assumption.
  unfold cm_rvalue_code_count.
  cbn [cm_expr_code_counts cm_rcount_of].
  unfold cm_binary_tail_count. cbn.
  destruct (cm_pointerb (cm_expr_type y)); cbn in *; lia.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_10_split_goal_spatial : cm_expr_counts_return_wit_10_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (cm_expr_rep_node expr_pre e).
  unfold cm_expr_node. Exists pa pb pargs.
  subst e. cbn [cm_expr_payload].
  split_pure_spatial; try (split_pures; dump_pre_spatial; lia).
  repeat progress cancel.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_10 : cm_expr_counts_return_wit_10.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_expr_counts_return_wit_10_split_goal_spatial.
  Goal_apply proof_of_cm_expr_counts_return_wit_10_split_goal_1.
  Goal_apply proof_of_cm_expr_counts_return_wit_10_split_goal_2.
  Goal_apply proof_of_cm_expr_counts_return_wit_10_split_goal_3.
  Goal_apply proof_of_cm_expr_counts_return_wit_10_split_goal_4.
  Goal_apply proof_of_cm_expr_counts_return_wit_10_split_goal_5.
  Goal_apply proof_of_cm_expr_counts_return_wit_10_split_goal_6.
Qed. 

Lemma proof_of_cm_expr_counts_return_wit_11_split_goal_1 : cm_expr_counts_return_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_expr_counts_representable] in PreH44.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH44.
  unfold cm_rvalue_code_count, cm_lvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_11_split_goal_2 : cm_expr_counts_return_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_expr_counts_representable] in PreH44.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH44.
  unfold cm_rvalue_code_count, cm_lvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_11_split_goal_3 : cm_expr_counts_return_wit_11_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_expr_counts_representable] in PreH44.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH44.
  unfold cm_rvalue_code_count, cm_lvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_11_split_goal_4 : cm_expr_counts_return_wit_11_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_expr_counts_representable] in PreH44.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH44.
  unfold cm_rvalue_code_count, cm_lvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_11_split_goal_5 : cm_expr_counts_return_wit_11_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e. reflexivity.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_11_split_goal_6 : cm_expr_counts_return_wit_11_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e. cbn [cm_rep_expr_op] in PreH9. subst op.
  rewrite cm_pointer_encode__expression_add_results in PreH53 by assumption.
  rewrite cm_pointer_encode__expression_add_results in PreH54 by assumption.
  unfold cm_rvalue_code_count.
  cbn [cm_expr_code_counts cm_rcount_of].
  unfold cm_binary_tail_count. cbn.
  destruct (cm_pointerb (cm_expr_type y)); destruct (cm_pointerb (cm_expr_type x)); cbn in *; lia.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_11_split_goal_spatial : cm_expr_counts_return_wit_11_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (cm_expr_rep_node expr_pre e).
  unfold cm_expr_node. Exists pa pb pargs.
  subst e. cbn [cm_expr_payload].
  split_pure_spatial; try (split_pures; dump_pre_spatial; lia).
  repeat progress cancel.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_11 : cm_expr_counts_return_wit_11.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_expr_counts_return_wit_11_split_goal_spatial.
  Goal_apply proof_of_cm_expr_counts_return_wit_11_split_goal_1.
  Goal_apply proof_of_cm_expr_counts_return_wit_11_split_goal_2.
  Goal_apply proof_of_cm_expr_counts_return_wit_11_split_goal_3.
  Goal_apply proof_of_cm_expr_counts_return_wit_11_split_goal_4.
  Goal_apply proof_of_cm_expr_counts_return_wit_11_split_goal_5.
  Goal_apply proof_of_cm_expr_counts_return_wit_11_split_goal_6.
Qed. 

Lemma proof_of_cm_expr_counts_return_wit_12_split_goal_1 : cm_expr_counts_return_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_expr_counts_representable] in PreH44.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH44.
  unfold cm_rvalue_code_count, cm_lvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_12_split_goal_2 : cm_expr_counts_return_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_expr_counts_representable] in PreH44.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH44.
  unfold cm_rvalue_code_count, cm_lvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_12_split_goal_3 : cm_expr_counts_return_wit_12_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_expr_counts_representable] in PreH44.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH44.
  unfold cm_rvalue_code_count, cm_lvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_12_split_goal_4 : cm_expr_counts_return_wit_12_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_expr_counts_representable] in PreH44.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH44.
  unfold cm_rvalue_code_count, cm_lvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_12_split_goal_5 : cm_expr_counts_return_wit_12_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e. reflexivity.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_12_split_goal_6 : cm_expr_counts_return_wit_12_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e. cbn [cm_rep_expr_op] in PreH9. subst op.
  rewrite cm_pointer_encode__expression_add_results in PreH53 by assumption.
  rewrite cm_pointer_encode__expression_add_results in PreH54 by assumption.
  unfold cm_rvalue_code_count.
  cbn [cm_expr_code_counts cm_rcount_of].
  unfold cm_binary_tail_count. cbn.
  destruct (cm_pointerb (cm_expr_type y)); destruct (cm_pointerb (cm_expr_type x)); cbn in *; lia.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_12_split_goal_spatial : cm_expr_counts_return_wit_12_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (cm_expr_rep_node expr_pre e).
  unfold cm_expr_node. Exists pa pb pargs.
  subst e. cbn [cm_expr_payload].
  split_pure_spatial; try (split_pures; dump_pre_spatial; lia).
  repeat progress cancel.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_12 : cm_expr_counts_return_wit_12.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_expr_counts_return_wit_12_split_goal_spatial.
  Goal_apply proof_of_cm_expr_counts_return_wit_12_split_goal_1.
  Goal_apply proof_of_cm_expr_counts_return_wit_12_split_goal_2.
  Goal_apply proof_of_cm_expr_counts_return_wit_12_split_goal_3.
  Goal_apply proof_of_cm_expr_counts_return_wit_12_split_goal_4.
  Goal_apply proof_of_cm_expr_counts_return_wit_12_split_goal_5.
  Goal_apply proof_of_cm_expr_counts_return_wit_12_split_goal_6.
Qed. 

Lemma proof_of_cm_expr_counts_return_wit_13_split_goal_1 : cm_expr_counts_return_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : cm_expr_counts_representable _ _ _ e |- _ =>
    destruct e; cbn [cm_expr_counts_representable] in H;
    unfold cm_expr_count_node_representable, cm_code_counts_representable in H;
    unfold cm_lvalue_code_count, cm_rvalue_code_count; tauto end.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_13_split_goal_2 : cm_expr_counts_return_wit_13_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : cm_expr_counts_representable _ _ _ e |- _ =>
    destruct e; cbn [cm_expr_counts_representable] in H;
    unfold cm_expr_count_node_representable, cm_code_counts_representable in H;
    unfold cm_lvalue_code_count, cm_rvalue_code_count; tauto end.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_13_split_goal_3 : cm_expr_counts_return_wit_13_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : cm_expr_counts_representable _ _ _ e |- _ =>
    destruct e; cbn [cm_expr_counts_representable] in H;
    unfold cm_expr_count_node_representable, cm_code_counts_representable in H;
    unfold cm_lvalue_code_count, cm_rvalue_code_count; tauto end.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_13_split_goal_4 : cm_expr_counts_return_wit_13_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : cm_expr_counts_representable _ _ _ e |- _ =>
    destruct e; cbn [cm_expr_counts_representable] in H;
    unfold cm_expr_count_node_representable, cm_code_counts_representable in H;
    unfold cm_lvalue_code_count, cm_rvalue_code_count; tauto end.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_13_split_goal_5 : cm_expr_counts_return_wit_13_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst e. reflexivity.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_13_split_goal_6 : cm_expr_counts_return_wit_13_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst e.
  cbn [cm_rep_expr_op] in *.
  unfold cm_rvalue_code_count; cbn [cm_expr_code_counts cm_rcount_of].
  unfold cm_binary_tail_count.
  subst op.
  rewrite (cm_pointer_encode__expression_sub_results (cm_expr_type x) PreH33) in PreH54.
  destruct (cm_pointerb (cm_expr_type x)) eqn:Ex; simpl in PreH54; try congruence;
  destruct (cm_pointerb (cm_expr_type y)); simpl; lia.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_13_split_goal_spatial : cm_expr_counts_return_wit_13_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (cm_expr_rep_node expr_pre e).
  unfold cm_expr_node. Exists pa pb pargs.
  subst e. unfold cm_expr_payload.
  split_pure_spatial.
  - cancel (cm_expr_rep pa x). cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_13 : cm_expr_counts_return_wit_13.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_expr_counts_return_wit_13_split_goal_spatial.
  Goal_apply proof_of_cm_expr_counts_return_wit_13_split_goal_1.
  Goal_apply proof_of_cm_expr_counts_return_wit_13_split_goal_2.
  Goal_apply proof_of_cm_expr_counts_return_wit_13_split_goal_3.
  Goal_apply proof_of_cm_expr_counts_return_wit_13_split_goal_4.
  Goal_apply proof_of_cm_expr_counts_return_wit_13_split_goal_5.
  Goal_apply proof_of_cm_expr_counts_return_wit_13_split_goal_6.
Qed. 

Lemma proof_of_cm_expr_counts_return_wit_14_split_goal_1 : cm_expr_counts_return_wit_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : cm_expr_counts_representable _ _ _ e |- _ =>
    destruct e; cbn [cm_expr_counts_representable] in H;
    unfold cm_expr_count_node_representable, cm_code_counts_representable in H;
    unfold cm_lvalue_code_count, cm_rvalue_code_count; tauto end.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_14_split_goal_2 : cm_expr_counts_return_wit_14_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : cm_expr_counts_representable _ _ _ e |- _ =>
    destruct e; cbn [cm_expr_counts_representable] in H;
    unfold cm_expr_count_node_representable, cm_code_counts_representable in H;
    unfold cm_lvalue_code_count, cm_rvalue_code_count; tauto end.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_14_split_goal_3 : cm_expr_counts_return_wit_14_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : cm_expr_counts_representable _ _ _ e |- _ =>
    destruct e; cbn [cm_expr_counts_representable] in H;
    unfold cm_expr_count_node_representable, cm_code_counts_representable in H;
    unfold cm_lvalue_code_count, cm_rvalue_code_count; tauto end.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_14_split_goal_4 : cm_expr_counts_return_wit_14_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : cm_expr_counts_representable _ _ _ e |- _ =>
    destruct e; cbn [cm_expr_counts_representable] in H;
    unfold cm_expr_count_node_representable, cm_code_counts_representable in H;
    unfold cm_lvalue_code_count, cm_rvalue_code_count; tauto end.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_14_split_goal_5 : cm_expr_counts_return_wit_14_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst e. reflexivity.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_14_split_goal_6 : cm_expr_counts_return_wit_14_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst e.
  cbn [cm_rep_expr_op] in *.
  unfold cm_rvalue_code_count; cbn [cm_expr_code_counts cm_rcount_of].
  unfold cm_binary_tail_count.
  subst op.
  rewrite (cm_pointer_encode__expression_sub_results (cm_expr_type x) PreH33) in PreH54.
  destruct (cm_pointerb (cm_expr_type x)) eqn:Ex; simpl in PreH54; try congruence;
  destruct (cm_pointerb (cm_expr_type y)); simpl; lia.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_14_split_goal_spatial : cm_expr_counts_return_wit_14_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (cm_expr_rep_node expr_pre e).
  unfold cm_expr_node. Exists pa pb pargs.
  subst e. unfold cm_expr_payload.
  split_pure_spatial.
  - cancel (cm_expr_rep pa x). cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_14 : cm_expr_counts_return_wit_14.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_expr_counts_return_wit_14_split_goal_spatial.
  Goal_apply proof_of_cm_expr_counts_return_wit_14_split_goal_1.
  Goal_apply proof_of_cm_expr_counts_return_wit_14_split_goal_2.
  Goal_apply proof_of_cm_expr_counts_return_wit_14_split_goal_3.
  Goal_apply proof_of_cm_expr_counts_return_wit_14_split_goal_4.
  Goal_apply proof_of_cm_expr_counts_return_wit_14_split_goal_5.
  Goal_apply proof_of_cm_expr_counts_return_wit_14_split_goal_6.
Qed. 

Lemma proof_of_cm_expr_counts_return_wit_15_split_goal_1 : cm_expr_counts_return_wit_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : cm_expr_counts_representable _ _ _ e |- _ =>
    destruct e; cbn [cm_expr_counts_representable] in H;
    unfold cm_expr_count_node_representable, cm_code_counts_representable in H;
    unfold cm_lvalue_code_count, cm_rvalue_code_count; tauto end.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_15_split_goal_2 : cm_expr_counts_return_wit_15_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : cm_expr_counts_representable _ _ _ e |- _ =>
    destruct e; cbn [cm_expr_counts_representable] in H;
    unfold cm_expr_count_node_representable, cm_code_counts_representable in H;
    unfold cm_lvalue_code_count, cm_rvalue_code_count; tauto end.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_15_split_goal_3 : cm_expr_counts_return_wit_15_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : cm_expr_counts_representable _ _ _ e |- _ =>
    destruct e; cbn [cm_expr_counts_representable] in H;
    unfold cm_expr_count_node_representable, cm_code_counts_representable in H;
    unfold cm_lvalue_code_count, cm_rvalue_code_count; tauto end.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_15_split_goal_4 : cm_expr_counts_return_wit_15_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with H : cm_expr_counts_representable _ _ _ e |- _ =>
    destruct e; cbn [cm_expr_counts_representable] in H;
    unfold cm_expr_count_node_representable, cm_code_counts_representable in H;
    unfold cm_lvalue_code_count, cm_rvalue_code_count; tauto end.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_15_split_goal_5 : cm_expr_counts_return_wit_15_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst e. reflexivity.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_15_split_goal_6 : cm_expr_counts_return_wit_15_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst e.
  cbn [cm_rep_expr_op] in *.
  unfold cm_rvalue_code_count; cbn [cm_expr_code_counts cm_rcount_of].
  unfold cm_binary_tail_count.
  assert (E0 : (Z.eqb op 0) = false) by (apply Z.eqb_neq; assumption).
  assert (E1 : (Z.eqb op 1) = false) by (apply Z.eqb_neq; assumption).
  assert (E8 : (Z.eqb op 8) = false) by (apply Z.eqb_neq; assumption).
  assert (E9 : (Z.eqb op 9) = false) by (apply Z.eqb_neq; assumption).
  rewrite E0, E1, E8, E9. simpl. lia.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_15_split_goal_spatial : cm_expr_counts_return_wit_15_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (cm_expr_rep_node expr_pre e).
  unfold cm_expr_node. Exists pa pb pargs.
  subst e. unfold cm_expr_payload.
  split_pure_spatial.
  - cancel (cm_expr_rep pa x). cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_15 : cm_expr_counts_return_wit_15.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_expr_counts_return_wit_15_split_goal_spatial.
  Goal_apply proof_of_cm_expr_counts_return_wit_15_split_goal_1.
  Goal_apply proof_of_cm_expr_counts_return_wit_15_split_goal_2.
  Goal_apply proof_of_cm_expr_counts_return_wit_15_split_goal_3.
  Goal_apply proof_of_cm_expr_counts_return_wit_15_split_goal_4.
  Goal_apply proof_of_cm_expr_counts_return_wit_15_split_goal_5.
  Goal_apply proof_of_cm_expr_counts_return_wit_15_split_goal_6.
Qed. 

Lemma proof_of_cm_expr_counts_return_wit_16_split_goal_1 : cm_expr_counts_return_wit_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  match goal with
  | H : cm_expr_counts_representable _ _ _ (CMUnaryE _ _ _) |- _ =>
      pose proof (proj1 H) as Hnode
  end.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in Hnode.
  unfold cm_lvalue_code_count, cm_rvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_16_split_goal_2 : cm_expr_counts_return_wit_16_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  match goal with
  | H : cm_expr_counts_representable _ _ _ (CMUnaryE _ _ _) |- _ =>
      pose proof (proj1 H) as Hnode
  end.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in Hnode.
  unfold cm_lvalue_code_count, cm_rvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_16_split_goal_3 : cm_expr_counts_return_wit_16_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  match goal with
  | H : cm_expr_counts_representable _ _ _ (CMUnaryE _ _ _) |- _ =>
      pose proof (proj1 H) as Hnode
  end.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in Hnode.
  unfold cm_lvalue_code_count, cm_rvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_16_split_goal_4 : cm_expr_counts_return_wit_16_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  match goal with
  | H : cm_expr_counts_representable _ _ _ (CMUnaryE _ _ _) |- _ =>
      pose proof (proj1 H) as Hnode
  end.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in Hnode.
  unfold cm_lvalue_code_count, cm_rvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_16_split_goal_5 : cm_expr_counts_return_wit_16_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_rep_expr_op] in *.
  unfold cm_lvalue_code_count, cm_rvalue_code_count.
  cbn [cm_expr_code_counts].
  repeat match goal with
  | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
  end; subst; cbn; congruence.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_16_split_goal_6 : cm_expr_counts_return_wit_16_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_rep_expr_op] in *.
  unfold cm_lvalue_code_count, cm_rvalue_code_count.
  cbn [cm_expr_code_counts].
  repeat match goal with
  | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
  end; subst; cbn; congruence.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_16_split_goal_spatial : cm_expr_counts_return_wit_16_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e.
  rewrite (cm_expr_rep_node expr_pre (CMUnaryE op x ty)).
  unfold cm_expr_node.
  Exists pa pb pargs.
  unfold cm_expr_payload.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_16 : cm_expr_counts_return_wit_16.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_return_wit_16_split_goal_spatial.
  - Goal_apply proof_of_cm_expr_counts_return_wit_16_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_return_wit_16_split_goal_2.
  - Goal_apply proof_of_cm_expr_counts_return_wit_16_split_goal_3.
  - Goal_apply proof_of_cm_expr_counts_return_wit_16_split_goal_4.
  - Goal_apply proof_of_cm_expr_counts_return_wit_16_split_goal_5.
  - Goal_apply proof_of_cm_expr_counts_return_wit_16_split_goal_6.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_17_split_goal_1 : cm_expr_counts_return_wit_17_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  match goal with
  | H : cm_expr_counts_representable _ _ _ (CMUnaryE _ _ _) |- _ =>
      pose proof (proj1 H) as Hnode
  end.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in Hnode.
  unfold cm_lvalue_code_count, cm_rvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_17_split_goal_2 : cm_expr_counts_return_wit_17_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  match goal with
  | H : cm_expr_counts_representable _ _ _ (CMUnaryE _ _ _) |- _ =>
      pose proof (proj1 H) as Hnode
  end.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in Hnode.
  unfold cm_lvalue_code_count, cm_rvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_17_split_goal_3 : cm_expr_counts_return_wit_17_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  match goal with
  | H : cm_expr_counts_representable _ _ _ (CMUnaryE _ _ _) |- _ =>
      pose proof (proj1 H) as Hnode
  end.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in Hnode.
  unfold cm_lvalue_code_count, cm_rvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_17_split_goal_4 : cm_expr_counts_return_wit_17_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  match goal with
  | H : cm_expr_counts_representable _ _ _ (CMUnaryE _ _ _) |- _ =>
      pose proof (proj1 H) as Hnode
  end.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in Hnode.
  unfold cm_lvalue_code_count, cm_rvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_17_split_goal_5 : cm_expr_counts_return_wit_17_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_rep_expr_op] in *.
  unfold cm_lvalue_code_count, cm_rvalue_code_count.
  cbn [cm_expr_code_counts].
  repeat match goal with
  | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
  end; subst; cbn; congruence.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_17_split_goal_6 : cm_expr_counts_return_wit_17_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_rep_expr_op] in *.
  unfold cm_lvalue_code_count, cm_rvalue_code_count.
  cbn [cm_expr_code_counts].
  repeat match goal with
  | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
  end; subst; cbn; congruence.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_17_split_goal_spatial : cm_expr_counts_return_wit_17_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e.
  rewrite (cm_expr_rep_node expr_pre (CMUnaryE op x ty)).
  unfold cm_expr_node.
  Exists pa pb pargs.
  unfold cm_expr_payload.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_17 : cm_expr_counts_return_wit_17.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_return_wit_17_split_goal_spatial.
  - Goal_apply proof_of_cm_expr_counts_return_wit_17_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_return_wit_17_split_goal_2.
  - Goal_apply proof_of_cm_expr_counts_return_wit_17_split_goal_3.
  - Goal_apply proof_of_cm_expr_counts_return_wit_17_split_goal_4.
  - Goal_apply proof_of_cm_expr_counts_return_wit_17_split_goal_5.
  - Goal_apply proof_of_cm_expr_counts_return_wit_17_split_goal_6.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_18_split_goal_1 : cm_expr_counts_return_wit_18_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  match goal with
  | H : cm_expr_counts_representable _ _ _ (CMUnaryE _ _ _) |- _ =>
      pose proof (proj1 H) as Hnode
  end.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in Hnode.
  unfold cm_lvalue_code_count, cm_rvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_18_split_goal_2 : cm_expr_counts_return_wit_18_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  match goal with
  | H : cm_expr_counts_representable _ _ _ (CMUnaryE _ _ _) |- _ =>
      pose proof (proj1 H) as Hnode
  end.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in Hnode.
  unfold cm_lvalue_code_count, cm_rvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_18_split_goal_3 : cm_expr_counts_return_wit_18_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  match goal with
  | H : cm_expr_counts_representable _ _ _ (CMUnaryE _ _ _) |- _ =>
      pose proof (proj1 H) as Hnode
  end.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in Hnode.
  unfold cm_lvalue_code_count, cm_rvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_18_split_goal_4 : cm_expr_counts_return_wit_18_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  match goal with
  | H : cm_expr_counts_representable _ _ _ (CMUnaryE _ _ _) |- _ =>
      pose proof (proj1 H) as Hnode
  end.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in Hnode.
  unfold cm_lvalue_code_count, cm_rvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_18_split_goal_5 : cm_expr_counts_return_wit_18_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_rep_expr_op] in *.
  unfold cm_lvalue_code_count, cm_rvalue_code_count.
  cbn [cm_expr_code_counts].
  repeat match goal with
  | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
  end; subst; cbn; congruence.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_18_split_goal_6 : cm_expr_counts_return_wit_18_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_rep_expr_op] in *.
  unfold cm_lvalue_code_count, cm_rvalue_code_count.
  cbn [cm_expr_code_counts].
  repeat match goal with
  | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
  end; subst; cbn; congruence.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_18_split_goal_spatial : cm_expr_counts_return_wit_18_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e.
  rewrite (cm_expr_rep_node expr_pre (CMUnaryE op x ty)).
  unfold cm_expr_node.
  Exists pa pb pargs.
  unfold cm_expr_payload.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_18 : cm_expr_counts_return_wit_18.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_return_wit_18_split_goal_spatial.
  - Goal_apply proof_of_cm_expr_counts_return_wit_18_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_return_wit_18_split_goal_2.
  - Goal_apply proof_of_cm_expr_counts_return_wit_18_split_goal_3.
  - Goal_apply proof_of_cm_expr_counts_return_wit_18_split_goal_4.
  - Goal_apply proof_of_cm_expr_counts_return_wit_18_split_goal_5.
  - Goal_apply proof_of_cm_expr_counts_return_wit_18_split_goal_6.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_19_split_goal_1 : cm_expr_counts_return_wit_19_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_expr_counts_representable] in PreH41.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH41.
  unfold cm_rvalue_code_count. tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_19_split_goal_2 : cm_expr_counts_return_wit_19_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_expr_counts_representable] in PreH41.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH41.
  unfold cm_lvalue_code_count. tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_19_split_goal_3 : cm_expr_counts_return_wit_19_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_expr_counts_representable] in PreH41.
  unfold cm_expr_count_node_representable in PreH41. tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_19_split_goal_4 : cm_expr_counts_return_wit_19_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_expr_counts_representable] in PreH41.
  unfold cm_expr_count_node_representable in PreH41. tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_19_split_goal_5 : cm_expr_counts_return_wit_19_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst e.
  unfold cm_lvalue_code_count, cm_rvalue_code_count.
  cbn [cm_expr_code_counts cm_lcount_of cm_rcount_of].
  lia.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_19_split_goal_6 : cm_expr_counts_return_wit_19_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst e.
  unfold cm_rvalue_code_count.
  cbn [cm_expr_code_counts cm_rcount_of].
  lia.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_19_split_goal_spatial : cm_expr_counts_return_wit_19_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (cm_expr_rep_node expr_pre e).
  unfold cm_expr_node.
  Exists pa pb pargs.
  subst e.
  cbn [cm_expr_payload].
  poly_store_unfold.
  split_pure_spatial.
  - sepcon_right_assoc. cancel.
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_19 : cm_expr_counts_return_wit_19.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_return_wit_19_split_goal_spatial.
  - Goal_apply proof_of_cm_expr_counts_return_wit_19_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_return_wit_19_split_goal_2.
  - Goal_apply proof_of_cm_expr_counts_return_wit_19_split_goal_3.
  - Goal_apply proof_of_cm_expr_counts_return_wit_19_split_goal_4.
  - Goal_apply proof_of_cm_expr_counts_return_wit_19_split_goal_5.
  - Goal_apply proof_of_cm_expr_counts_return_wit_19_split_goal_6.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_20_split_goal_1 : cm_expr_counts_return_wit_20_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_expr_counts_representable] in PreH39.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH39.
  unfold cm_rvalue_code_count, cm_lvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_20_split_goal_2 : cm_expr_counts_return_wit_20_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_expr_counts_representable] in PreH39.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH39.
  unfold cm_rvalue_code_count, cm_lvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_20_split_goal_3 : cm_expr_counts_return_wit_20_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_expr_counts_representable] in PreH39.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH39.
  unfold cm_rvalue_code_count, cm_lvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_20_split_goal_4 : cm_expr_counts_return_wit_20_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_expr_counts_representable] in PreH39.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH39.
  unfold cm_rvalue_code_count, cm_lvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_20_split_goal_5 : cm_expr_counts_return_wit_20_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e. reflexivity.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_20_split_goal_6 : cm_expr_counts_return_wit_20_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_member_base_type cm_rep_expr_value] in PreH9.
  assert (Hcast : signed_last_nbits mid 32 = mid) by (apply signed_last_nbits_eq; [lia | change (-2147483648 <= mid < 2147483648); change (mid <= 2147483647) in PreH45; lia]).
  rewrite Hcast in PreH9.
  unfold cm_rvalue_code_count.
  cbn [cm_expr_code_counts cm_rcount_of].
  rewrite PreH9. reflexivity.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_20_split_goal_spatial : cm_expr_counts_return_wit_20_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (cm_expr_rep_node expr_pre e).
  unfold cm_expr_node.
  Exists pa pb pargs.
  subst e.
  cbn [cm_expr_payload].
  split_pure_spatial.
  - sepcon_right_assoc. cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_20 : cm_expr_counts_return_wit_20.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_return_wit_20_split_goal_spatial.
  - Goal_apply proof_of_cm_expr_counts_return_wit_20_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_return_wit_20_split_goal_2.
  - Goal_apply proof_of_cm_expr_counts_return_wit_20_split_goal_3.
  - Goal_apply proof_of_cm_expr_counts_return_wit_20_split_goal_4.
  - Goal_apply proof_of_cm_expr_counts_return_wit_20_split_goal_5.
  - Goal_apply proof_of_cm_expr_counts_return_wit_20_split_goal_6.
Qed. 

Lemma proof_of_cm_expr_counts_return_wit_21_split_goal_1 : cm_expr_counts_return_wit_21_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_expr_counts_representable] in PreH39.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH39.
  unfold cm_rvalue_code_count, cm_lvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_21_split_goal_2 : cm_expr_counts_return_wit_21_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_expr_counts_representable] in PreH39.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH39.
  unfold cm_rvalue_code_count, cm_lvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_21_split_goal_3 : cm_expr_counts_return_wit_21_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_expr_counts_representable] in PreH39.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH39.
  unfold cm_rvalue_code_count, cm_lvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_21_split_goal_4 : cm_expr_counts_return_wit_21_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_expr_counts_representable] in PreH39.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH39.
  unfold cm_rvalue_code_count, cm_lvalue_code_count.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_21_split_goal_5 : cm_expr_counts_return_wit_21_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e. reflexivity.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_21_split_goal_6 : cm_expr_counts_return_wit_21_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_member_base_type cm_rep_expr_value] in PreH9.
  assert (Hcast : signed_last_nbits mid 32 = mid) by (apply signed_last_nbits_eq; [lia | change (-2147483648 <= mid < 2147483648); change (mid <= 2147483647) in PreH45; lia]).
  rewrite Hcast in PreH9.
  unfold cm_rvalue_code_count.
  cbn [cm_expr_code_counts cm_rcount_of].
  apply Z.eqb_neq in PreH9. rewrite PreH9. lia.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_21_split_goal_spatial : cm_expr_counts_return_wit_21_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (cm_expr_rep_node expr_pre e).
  unfold cm_expr_node.
  Exists pa pb pargs.
  subst e.
  cbn [cm_expr_payload].
  split_pure_spatial.
  - sepcon_right_assoc. cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_21 : cm_expr_counts_return_wit_21.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_return_wit_21_split_goal_spatial.
  - Goal_apply proof_of_cm_expr_counts_return_wit_21_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_return_wit_21_split_goal_2.
  - Goal_apply proof_of_cm_expr_counts_return_wit_21_split_goal_3.
  - Goal_apply proof_of_cm_expr_counts_return_wit_21_split_goal_4.
  - Goal_apply proof_of_cm_expr_counts_return_wit_21_split_goal_5.
  - Goal_apply proof_of_cm_expr_counts_return_wit_21_split_goal_6.
Qed. 

Lemma proof_of_cm_expr_counts_return_wit_22_split_goal_1 : cm_expr_counts_return_wit_22_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold cm_rvalue_code_count.
  destruct e; cbn [cm_expr_counts_representable] in *;
    unfold cm_expr_count_node_representable, cm_code_counts_representable in *; tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_22_split_goal_2 : cm_expr_counts_return_wit_22_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold cm_lvalue_code_count.
  destruct e; cbn [cm_expr_counts_representable] in *;
    unfold cm_expr_count_node_representable, cm_code_counts_representable in *; tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_22_split_goal_3 : cm_expr_counts_return_wit_22_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct e; cbn [cm_expr_counts_representable] in *;
    unfold cm_expr_count_node_representable in *; tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_22_split_goal_4 : cm_expr_counts_return_wit_22_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct e; cbn [cm_expr_counts_representable] in *;
    unfold cm_expr_count_node_representable in *; tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_22_split_goal_5 : cm_expr_counts_return_wit_22_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst e.
  unfold cm_lvalue_code_count. rewrite cm_expr_counts_call. reflexivity.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_22_split_goal_6 : cm_expr_counts_return_wit_22_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst e.
  unfold cm_rvalue_code_count. rewrite cm_expr_counts_call. reflexivity.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_22_split_goal_spatial : cm_expr_counts_return_wit_22_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_expr_rep_node. unfold cm_expr_node.
  Exists pa pb pargs.
  subst e. cbn [cm_expr_payload].
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_22 : cm_expr_counts_return_wit_22.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_return_wit_22_split_goal_spatial.
  - Goal_apply proof_of_cm_expr_counts_return_wit_22_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_return_wit_22_split_goal_2.
  - Goal_apply proof_of_cm_expr_counts_return_wit_22_split_goal_3.
  - Goal_apply proof_of_cm_expr_counts_return_wit_22_split_goal_4.
  - Goal_apply proof_of_cm_expr_counts_return_wit_22_split_goal_5.
  - Goal_apply proof_of_cm_expr_counts_return_wit_22_split_goal_6.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_23_split_goal_1 : cm_expr_counts_return_wit_23_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst e.
  unfold cm_rvalue_code_count.
  cbn [cm_expr_counts_representable cm_expr_count_node_representable cm_code_counts_representable] in *.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH29.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_23_split_goal_2 : cm_expr_counts_return_wit_23_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst e.
  unfold cm_lvalue_code_count.
  cbn [cm_expr_counts_representable cm_expr_count_node_representable cm_code_counts_representable] in *.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH29.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_23_split_goal_3 : cm_expr_counts_return_wit_23_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst e.
  cbn [cm_expr_counts_representable cm_expr_count_node_representable cm_code_counts_representable] in *.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH29.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_23_split_goal_4 : cm_expr_counts_return_wit_23_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst e.
  cbn [cm_expr_counts_representable cm_expr_count_node_representable cm_code_counts_representable] in *.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH29.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_23_split_goal_5 : cm_expr_counts_return_wit_23_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst e. reflexivity.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_23_split_goal_6 : cm_expr_counts_return_wit_23_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst e. reflexivity.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_23_split_goal_spatial : cm_expr_counts_return_wit_23_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e.
  rewrite (cm_expr_rep_node expr_pre (CMPutcE x ty)).
  unfold cm_expr_node.
  Exists pa pb pargs.
  cbn [cm_expr_payload].
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_23 : cm_expr_counts_return_wit_23.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_return_wit_23_split_goal_spatial.
  - Goal_apply proof_of_cm_expr_counts_return_wit_23_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_return_wit_23_split_goal_2.
  - Goal_apply proof_of_cm_expr_counts_return_wit_23_split_goal_3.
  - Goal_apply proof_of_cm_expr_counts_return_wit_23_split_goal_4.
  - Goal_apply proof_of_cm_expr_counts_return_wit_23_split_goal_5.
  - Goal_apply proof_of_cm_expr_counts_return_wit_23_split_goal_6.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_24_split_goal_1 : cm_expr_counts_return_wit_24_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst e.
  unfold cm_rvalue_code_count.
  cbn [cm_expr_counts_representable cm_expr_count_node_representable cm_code_counts_representable] in *.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH29.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_24_split_goal_2 : cm_expr_counts_return_wit_24_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst e.
  unfold cm_lvalue_code_count.
  cbn [cm_expr_counts_representable cm_expr_count_node_representable cm_code_counts_representable] in *.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH29.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_24_split_goal_3 : cm_expr_counts_return_wit_24_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst e.
  cbn [cm_expr_counts_representable cm_expr_count_node_representable cm_code_counts_representable] in *.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH29.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_24_split_goal_4 : cm_expr_counts_return_wit_24_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst e.
  cbn [cm_expr_counts_representable cm_expr_count_node_representable cm_code_counts_representable] in *.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH29.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_24_split_goal_5 : cm_expr_counts_return_wit_24_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst e. reflexivity.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_24_split_goal_6 : cm_expr_counts_return_wit_24_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst e. reflexivity.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_24_split_goal_spatial : cm_expr_counts_return_wit_24_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e.
  rewrite (cm_expr_rep_node expr_pre (CMPutiE x ty)).
  unfold cm_expr_node.
  Exists pa pb pargs.
  cbn [cm_expr_payload].
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_24 : cm_expr_counts_return_wit_24.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_return_wit_24_split_goal_spatial.
  - Goal_apply proof_of_cm_expr_counts_return_wit_24_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_return_wit_24_split_goal_2.
  - Goal_apply proof_of_cm_expr_counts_return_wit_24_split_goal_3.
  - Goal_apply proof_of_cm_expr_counts_return_wit_24_split_goal_4.
  - Goal_apply proof_of_cm_expr_counts_return_wit_24_split_goal_5.
  - Goal_apply proof_of_cm_expr_counts_return_wit_24_split_goal_6.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_25_split_goal_1 : cm_expr_counts_return_wit_25_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst e.
  unfold cm_rvalue_code_count.
  cbn [cm_expr_counts_representable cm_expr_count_node_representable cm_code_counts_representable] in *.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH29.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_25_split_goal_2 : cm_expr_counts_return_wit_25_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst e.
  unfold cm_lvalue_code_count.
  cbn [cm_expr_counts_representable cm_expr_count_node_representable cm_code_counts_representable] in *.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH29.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_25_split_goal_3 : cm_expr_counts_return_wit_25_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst e.
  cbn [cm_expr_counts_representable cm_expr_count_node_representable cm_code_counts_representable] in *.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH29.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_25_split_goal_4 : cm_expr_counts_return_wit_25_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst e.
  cbn [cm_expr_counts_representable cm_expr_count_node_representable cm_code_counts_representable] in *.
  unfold cm_expr_count_node_representable, cm_code_counts_representable in PreH29.
  tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_25_split_goal_5 : cm_expr_counts_return_wit_25_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst e. reflexivity.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_25_split_goal_6 : cm_expr_counts_return_wit_25_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst e. reflexivity.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_25_split_goal_spatial : cm_expr_counts_return_wit_25_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e.
  rewrite (cm_expr_rep_node expr_pre (CMExitE x ty)).
  unfold cm_expr_node.
  Exists pa pb pargs.
  cbn [cm_expr_payload].
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_cm_expr_counts_return_wit_25 : cm_expr_counts_return_wit_25.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_return_wit_25_split_goal_spatial.
  - Goal_apply proof_of_cm_expr_counts_return_wit_25_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_return_wit_25_split_goal_2.
  - Goal_apply proof_of_cm_expr_counts_return_wit_25_split_goal_3.
  - Goal_apply proof_of_cm_expr_counts_return_wit_25_split_goal_4.
  - Goal_apply proof_of_cm_expr_counts_return_wit_25_split_goal_5.
  - Goal_apply proof_of_cm_expr_counts_return_wit_25_split_goal_6.
Qed.

Lemma proof_of_cm_expr_counts_partial_solve_wit_2_pure_split_goal_1 : cm_expr_counts_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e. cbn [cm_rep_expr_value].
  rewrite signed_last_nbits_eq by (simpl; lia).
  dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_expr_counts_partial_solve_wit_2_pure_split_goal_2 : cm_expr_counts_partial_solve_wit_2_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e. cbn [cm_rep_expr_value cm_rep_expr_op].
  rewrite signed_last_nbits_eq by (simpl; lia).
  dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_expr_counts_partial_solve_wit_2_pure : cm_expr_counts_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_partial_solve_wit_2_pure_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_partial_solve_wit_2_pure_split_goal_2.
Qed.

Lemma proof_of_cm_expr_counts_partial_solve_wit_19_pure_split_goal_1 : cm_expr_counts_partial_solve_wit_19_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold cm_member_valid in PreH45.
  destruct (cm_expr_type x) as [| |sid|base]; cbn in PreH45; try tauto.
  destruct base as [| |sid|base]; cbn in PreH45; try tauto.
  cbn [cm_type_code_wf] in PreH29.
  unfold cm_type_encode; cbn [cm_type_depth cm_type_base_code].
  lia.
Qed.

Lemma proof_of_cm_expr_counts_partial_solve_wit_19_pure_split_goal_2 : cm_expr_counts_partial_solve_wit_19_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold cm_member_valid in PreH45.
  destruct (cm_expr_type x) as [| |sid|base]; cbn in PreH45; try tauto.
  destruct base as [| |sid|base]; cbn in PreH45; try tauto.
  cbn [cm_type_code_wf] in PreH29.
  unfold cm_type_encode; cbn [cm_type_depth cm_type_base_code].
  replace (1024 * (1 + 0) + (sid + 2) - 1024) with (sid+2) by lia.
  rewrite Z.rem_mod_nonneg by lia.
  rewrite Z.mod_small by lia.
  lia.
Qed.

Lemma proof_of_cm_expr_counts_partial_solve_wit_19_pure_split_goal_3 : cm_expr_counts_partial_solve_wit_19_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_rep_expr_value].
  rewrite signed_last_nbits_eq by (cbn; lia).
  exact PreH46.
Qed.

Lemma proof_of_cm_expr_counts_partial_solve_wit_19_pure_split_goal_4 : cm_expr_counts_partial_solve_wit_19_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  reflexivity.
Qed.

Lemma proof_of_cm_expr_counts_partial_solve_wit_19_pure_split_goal_5 : cm_expr_counts_partial_solve_wit_19_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  exact PreH29.
Qed.

Lemma proof_of_cm_expr_counts_partial_solve_wit_19_pure_split_goal_6 : cm_expr_counts_partial_solve_wit_19_pure_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst e.
  cbn [cm_member_base_type cm_rep_expr_value].
  rewrite signed_last_nbits_eq by (cbn; lia).
  exact PreH45.
Qed.

Lemma proof_of_cm_expr_counts_partial_solve_wit_19_pure : cm_expr_counts_partial_solve_wit_19_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_counts_partial_solve_wit_19_pure_split_goal_1.
  - Goal_apply proof_of_cm_expr_counts_partial_solve_wit_19_pure_split_goal_2.
  - Goal_apply proof_of_cm_expr_counts_partial_solve_wit_19_pure_split_goal_3.
  - Goal_apply proof_of_cm_expr_counts_partial_solve_wit_19_pure_split_goal_4.
  - Goal_apply proof_of_cm_expr_counts_partial_solve_wit_19_pure_split_goal_5.
  - Goal_apply proof_of_cm_expr_counts_partial_solve_wit_19_pure_split_goal_6.
Qed. 

Lemma proof_of_cmc_stmt_code_count_safety_wit_5_split_goal_1 : cmc_stmt_code_count_safety_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst.
  cbn [cm_stmt_counts_representable cm_stmt_code_count] in PreH19.
  unfold cm_i32_code_count in *.
  lia.
Qed.

Lemma proof_of_cmc_stmt_code_count_safety_wit_5_split_goal_2 : cmc_stmt_code_count_safety_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst.
  cbn [cm_stmt_counts_representable cm_stmt_code_count] in PreH19.
  unfold cm_i32_code_count in *.
  lia.
Qed.

Lemma proof_of_cmc_stmt_code_count_safety_wit_5 : cmc_stmt_code_count_safety_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_stmt_code_count_safety_wit_5_split_goal_1.
  - Goal_apply proof_of_cmc_stmt_code_count_safety_wit_5_split_goal_2.
Qed. 

Lemma proof_of_cmc_stmt_code_count_safety_wit_8_split_goal_1 : cmc_stmt_code_count_safety_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst.
  cbn [cm_rep_stmt_slot] in *.
  rewrite cm_slot_type_encode__statement_normalization_safety by lia.
  rewrite cm_normalize_encode__statement_normalization_safety by assumption.
  cbn [cm_stmt_counts_representable cm_stmt_code_count] in PreH22.
  unfold cm_i32_code_count in *.
  destruct (cm_slot_ty (cm_slot_at slot (cm_function_locals
    (cm_function_at policy fid_pre (cm_program_functions p)))));
    cbn [cm_char_normalize_count] in *; lia.
Qed.

Lemma proof_of_cmc_stmt_code_count_safety_wit_8_split_goal_2 : cmc_stmt_code_count_safety_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst.
  cbn [cm_rep_stmt_slot] in *.
  rewrite cm_slot_type_encode__statement_normalization_safety by lia.
  rewrite cm_normalize_encode__statement_normalization_safety by assumption.
  cbn [cm_stmt_counts_representable cm_stmt_code_count] in PreH22.
  unfold cm_i32_code_count in *.
  destruct (cm_slot_ty (cm_slot_at slot (cm_function_locals
    (cm_function_at policy fid_pre (cm_program_functions p)))));
    cbn [cm_char_normalize_count] in *; lia.
Qed.

Lemma proof_of_cmc_stmt_code_count_safety_wit_8 : cmc_stmt_code_count_safety_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_stmt_code_count_safety_wit_8_split_goal_1.
  - Goal_apply proof_of_cmc_stmt_code_count_safety_wit_8_split_goal_2.
Qed. 

Lemma proof_of_cmc_stmt_code_count_safety_wit_9_split_goal_1 : cmc_stmt_code_count_safety_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst.
  cbn [cm_rep_stmt_slot] in *.
  rewrite cm_slot_type_encode__statement_normalization_safety by lia.
  rewrite cm_normalize_encode__statement_normalization_safety by assumption.
  cbn [cm_stmt_counts_representable cm_stmt_code_count] in PreH22.
  unfold cm_i32_code_count in *.
  destruct (cm_slot_ty (cm_slot_at slot (cm_function_locals
    (cm_function_at policy fid_pre (cm_program_functions p)))));
    cbn [cm_char_normalize_count] in *; lia.
Qed.

Lemma proof_of_cmc_stmt_code_count_safety_wit_9_split_goal_2 : cmc_stmt_code_count_safety_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst.
  cbn [cm_rep_stmt_slot] in *.
  rewrite cm_slot_type_encode__statement_normalization_safety by lia.
  rewrite cm_normalize_encode__statement_normalization_safety by assumption.
  cbn [cm_stmt_counts_representable cm_stmt_code_count] in PreH22.
  unfold cm_i32_code_count in *.
  destruct (cm_slot_ty (cm_slot_at slot (cm_function_locals
    (cm_function_at policy fid_pre (cm_program_functions p)))));
    cbn [cm_char_normalize_count] in *; lia.
Qed.

Lemma proof_of_cmc_stmt_code_count_safety_wit_9 : cmc_stmt_code_count_safety_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_stmt_code_count_safety_wit_9_split_goal_1.
  - Goal_apply proof_of_cmc_stmt_code_count_safety_wit_9_split_goal_2.
Qed. 

Lemma proof_of_cmc_stmt_code_count_safety_wit_12_split_goal_1 : cmc_stmt_code_count_safety_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst.
  cbn [cm_stmt_counts_representable cm_stmt_code_count] in *.
  unfold cm_i32_code_count in *.
  lia || int_auto.
Qed.

Lemma proof_of_cmc_stmt_code_count_safety_wit_12_split_goal_2 : cmc_stmt_code_count_safety_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst.
  cbn [cm_stmt_counts_representable cm_stmt_code_count] in *.
  unfold cm_i32_code_count in *.
  lia || int_auto.
Qed.

Lemma proof_of_cmc_stmt_code_count_safety_wit_12 : cmc_stmt_code_count_safety_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_stmt_code_count_safety_wit_12_split_goal_1.
  - Goal_apply proof_of_cmc_stmt_code_count_safety_wit_12_split_goal_2.
Qed.

Lemma proof_of_cmc_stmt_code_count_safety_wit_15_split_goal_1 : cmc_stmt_code_count_safety_wit_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst.
  cbn [cm_stmt_counts_representable cm_stmt_code_count] in *.
  unfold cm_i32_code_count in *.
  lia || int_auto.
Qed.

Lemma proof_of_cmc_stmt_code_count_safety_wit_15_split_goal_2 : cmc_stmt_code_count_safety_wit_15_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst.
  cbn [cm_stmt_counts_representable cm_stmt_code_count] in *.
  unfold cm_i32_code_count in *.
  lia || int_auto.
Qed.

Lemma proof_of_cmc_stmt_code_count_safety_wit_15 : cmc_stmt_code_count_safety_wit_15.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_stmt_code_count_safety_wit_15_split_goal_1.
  - Goal_apply proof_of_cmc_stmt_code_count_safety_wit_15_split_goal_2.
Qed.

Lemma proof_of_cmc_stmt_code_count_safety_wit_16_split_goal_1 : cmc_stmt_code_count_safety_wit_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst.
  cbn [cm_stmt_counts_representable cm_stmt_code_count] in *.
  unfold cm_i32_code_count in *.
  lia || int_auto.
Qed.

Lemma proof_of_cmc_stmt_code_count_safety_wit_16_split_goal_2 : cmc_stmt_code_count_safety_wit_16_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst.
  cbn [cm_stmt_counts_representable cm_stmt_code_count] in *.
  unfold cm_i32_code_count in *.
  lia || int_auto.
Qed.

Lemma proof_of_cmc_stmt_code_count_safety_wit_16 : cmc_stmt_code_count_safety_wit_16.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_stmt_code_count_safety_wit_16_split_goal_1.
  - Goal_apply proof_of_cmc_stmt_code_count_safety_wit_16_split_goal_2.
Qed.

Lemma proof_of_cmc_stmt_code_count_safety_wit_17_split_goal_1 : cmc_stmt_code_count_safety_wit_17_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst.
  cbn [cm_stmt_counts_representable cm_stmt_code_count] in *.
  unfold cm_i32_code_count in *.
  lia || int_auto.
Qed.

Lemma proof_of_cmc_stmt_code_count_safety_wit_17_split_goal_2 : cmc_stmt_code_count_safety_wit_17_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst.
  cbn [cm_stmt_counts_representable cm_stmt_code_count] in *.
  unfold cm_i32_code_count in *.
  lia || int_auto.
Qed.

Lemma proof_of_cmc_stmt_code_count_safety_wit_17 : cmc_stmt_code_count_safety_wit_17.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_stmt_code_count_safety_wit_17_split_goal_1.
  - Goal_apply proof_of_cmc_stmt_code_count_safety_wit_17_split_goal_2.
Qed.

Lemma proof_of_cmc_stmt_code_count_safety_wit_18_split_goal_1 : cmc_stmt_code_count_safety_wit_18_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst.
  cbn [cm_stmt_counts_representable cm_stmt_code_count] in *.
  unfold cm_i32_code_count in *.
  lia || int_auto.
Qed.

Lemma proof_of_cmc_stmt_code_count_safety_wit_18_split_goal_2 : cmc_stmt_code_count_safety_wit_18_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst.
  cbn [cm_stmt_counts_representable cm_stmt_code_count] in *.
  unfold cm_i32_code_count in *.
  lia || int_auto.
Qed.

Lemma proof_of_cmc_stmt_code_count_safety_wit_18 : cmc_stmt_code_count_safety_wit_18.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_stmt_code_count_safety_wit_18_split_goal_1.
  - Goal_apply proof_of_cmc_stmt_code_count_safety_wit_18_split_goal_2.
Qed.

Lemma proof_of_cmc_stmt_code_count_safety_wit_22_split_goal_1 : cmc_stmt_code_count_safety_wit_22_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst.
  cbn [cm_stmt_counts_representable cm_stmt_code_count] in PreH29.
  unfold cm_i32_code_count in *.
  lia.
Qed.

Lemma proof_of_cmc_stmt_code_count_safety_wit_22_split_goal_2 : cmc_stmt_code_count_safety_wit_22_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst.
  cbn [cm_stmt_counts_representable cm_stmt_code_count] in PreH29.
  unfold cm_i32_code_count in *.
  lia.
Qed.

Lemma proof_of_cmc_stmt_code_count_safety_wit_22 : cmc_stmt_code_count_safety_wit_22.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_stmt_code_count_safety_wit_22_split_goal_1.
  - Goal_apply proof_of_cmc_stmt_code_count_safety_wit_22_split_goal_2.
Qed.

Lemma proof_of_cmc_stmt_code_count_safety_wit_23_split_goal_1 : cmc_stmt_code_count_safety_wit_23_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst.
  cbn [cm_stmt_counts_representable cm_stmt_code_count] in PreH29.
  unfold cm_i32_code_count in *.
  lia.
Qed.

Lemma proof_of_cmc_stmt_code_count_safety_wit_23_split_goal_2 : cmc_stmt_code_count_safety_wit_23_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst.
  cbn [cm_stmt_counts_representable cm_stmt_code_count] in PreH29.
  unfold cm_i32_code_count in *.
  lia.
Qed.

Lemma proof_of_cmc_stmt_code_count_safety_wit_23 : cmc_stmt_code_count_safety_wit_23.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_stmt_code_count_safety_wit_23_split_goal_1.
  - Goal_apply proof_of_cmc_stmt_code_count_safety_wit_23_split_goal_2.
Qed.

Lemma proof_of_cmc_stmt_code_count_safety_wit_24_split_goal_1 : cmc_stmt_code_count_safety_wit_24_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst.
  cbn [cm_stmt_counts_representable cm_stmt_code_count] in PreH29.
  unfold cm_i32_code_count in *.
  lia.
Qed.

Lemma proof_of_cmc_stmt_code_count_safety_wit_24_split_goal_2 : cmc_stmt_code_count_safety_wit_24_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst.
  cbn [cm_stmt_counts_representable cm_stmt_code_count] in PreH29.
  unfold cm_i32_code_count in *.
  lia.
Qed.

Lemma proof_of_cmc_stmt_code_count_safety_wit_24 : cmc_stmt_code_count_safety_wit_24.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_stmt_code_count_safety_wit_24_split_goal_1.
  - Goal_apply proof_of_cmc_stmt_code_count_safety_wit_24_split_goal_2.
Qed.

Lemma proof_of_cmc_stmt_code_count_safety_wit_31_split_goal_1 : cmc_stmt_code_count_safety_wit_31_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst.
  rewrite cm_normalize_encode__statement_normalization_safety by assumption.
  cbn [cm_stmt_counts_representable cm_stmt_code_count] in PreH20.
  unfold cm_i32_code_count in *.
  destruct (cm_function_ret (cm_function_at policy fid_pre (cm_program_functions p)));
    cbn [cm_char_normalize_count] in *; lia.
Qed.

Lemma proof_of_cmc_stmt_code_count_safety_wit_31_split_goal_2 : cmc_stmt_code_count_safety_wit_31_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst.
  rewrite cm_normalize_encode__statement_normalization_safety by assumption.
  cbn [cm_stmt_counts_representable cm_stmt_code_count] in PreH20.
  unfold cm_i32_code_count in *.
  destruct (cm_function_ret (cm_function_at policy fid_pre (cm_program_functions p)));
    cbn [cm_char_normalize_count] in *; lia.
Qed.

Lemma proof_of_cmc_stmt_code_count_safety_wit_31 : cmc_stmt_code_count_safety_wit_31.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_stmt_code_count_safety_wit_31_split_goal_1.
  - Goal_apply proof_of_cmc_stmt_code_count_safety_wit_31_split_goal_2.
Qed. 

Lemma proof_of_cmc_stmt_code_count_safety_wit_32_split_goal_1 : cmc_stmt_code_count_safety_wit_32_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst.
  rewrite cm_normalize_encode__statement_normalization_safety by assumption.
  cbn [cm_stmt_counts_representable cm_stmt_code_count] in PreH20.
  unfold cm_i32_code_count in *.
  destruct (cm_function_ret (cm_function_at policy fid_pre (cm_program_functions p)));
    cbn [cm_char_normalize_count] in *; lia.
Qed.

Lemma proof_of_cmc_stmt_code_count_safety_wit_32_split_goal_2 : cmc_stmt_code_count_safety_wit_32_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst.
  rewrite cm_normalize_encode__statement_normalization_safety by assumption.
  cbn [cm_stmt_counts_representable cm_stmt_code_count] in PreH20.
  unfold cm_i32_code_count in *.
  destruct (cm_function_ret (cm_function_at policy fid_pre (cm_program_functions p)));
    cbn [cm_char_normalize_count] in *; lia.
Qed.

Lemma proof_of_cmc_stmt_code_count_safety_wit_32 : cmc_stmt_code_count_safety_wit_32.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_stmt_code_count_safety_wit_32_split_goal_1.
  - Goal_apply proof_of_cmc_stmt_code_count_safety_wit_32_split_goal_2.
Qed. 

Lemma proof_of_cmc_stmt_code_count_entail_wit_1 : cmc_stmt_code_count_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_stmt_rep_node. unfold cm_stmt_node.
  Intros pe pa pb.
  Exists pb pa pe.
  split_pure_spatial; [repeat progress cancel | split_pures; dump_pre_spatial; auto].
Qed.

Lemma proof_of_cmc_stmt_code_count_entail_wit_2 : cmc_stmt_code_count_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct s; cbn [cm_rep_stmt_kind] in PreH1; try discriminate.
  Exists pb_2 pa_2 pe_2 e.
  cbn [cm_stmt_payload]. Intros_p Hpayload.
  split_pure_spatial; [repeat progress cancel |].
  split_pures; dump_pre_spatial; try assumption; try reflexivity;
    cbn [cm_stmt_wf cm_stmt_counts_representable] in *; tauto.
Qed.

Lemma proof_of_cmc_stmt_code_count_entail_wit_3 : cmc_stmt_code_count_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct s; cbn [cm_rep_stmt_kind] in PreH1; try discriminate.
  match type of PreH12 with
  | cm_stmt_wf _ _ _ _ (CMInitS ?slot ?x) => Exists pb_2 pa_2 pe_2 slot x
  end.
  cbn [cm_stmt_payload]. Intros_p Hpayload.
  assert (Hwf := PreH12).
  assert (Hrepr := PreH13).
  cbn [cm_stmt_wf] in Hwf.
  cbn [cm_stmt_counts_representable] in Hrepr.
  split_pure_spatial; [repeat progress cancel |].
  split_pures; dump_pre_spatial; try assumption; try reflexivity;
    rewrite ?PreH10, ?PreH7 in *; tauto.
Qed.

Lemma proof_of_cmc_stmt_code_count_entail_wit_4 : cmc_stmt_code_count_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct s as [ | x | slot | slot x | a b | a | x a b | x a | | | x ]; cbn [cm_rep_stmt_kind] in *; try contradiction; try discriminate.
  Exists pb_2 pa_2 pe_2 a b.
  cbn [cm_stmt_payload].
  Intros_p Hpe.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; cbn [cm_stmt_wf cm_stmt_counts_representable] in *; tauto.
Qed.

Lemma proof_of_cmc_stmt_code_count_entail_wit_5 : cmc_stmt_code_count_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct s as [ | x | slot | slot x | a b | a | x a b | x a | | | x ]; cbn [cm_rep_stmt_kind] in *; try contradiction; try discriminate.
  Exists pb_2 pa_2 pe_2 a.
  cbn [cm_stmt_payload].
  Intros_p Hpayload.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; cbn [cm_stmt_wf cm_stmt_counts_representable] in *; tauto.
Qed.

Lemma proof_of_cmc_stmt_code_count_entail_wit_6 : cmc_stmt_code_count_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct s as [ | x | slot | slot x | a b | a | x a b | x a | | | x ]; cbn [cm_rep_stmt_kind] in *; try contradiction; try discriminate.
  Exists pb_2 pa_2 pe_2 x a b.
  cbn [cm_stmt_payload].
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; cbn [cm_stmt_wf cm_stmt_counts_representable] in *; tauto.
Qed.

Lemma proof_of_cmc_stmt_code_count_entail_wit_7 : cmc_stmt_code_count_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct s as [ | x | slot | slot x | a b | a | x a b | x a | | | x ]; cbn [cm_rep_stmt_kind] in *; try contradiction; try discriminate.
  Exists pb_2 pa_2 pe_2 x a.
  cbn [cm_stmt_payload].
  Intros_p Hpayload.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; cbn [cm_stmt_wf cm_stmt_counts_representable] in *; tauto.
Qed.

Lemma proof_of_cmc_stmt_code_count_entail_wit_8 : cmc_stmt_code_count_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct s as [ | x | slot | slot x | a b | a | x a b | x a | | | x ]; cbn [cm_rep_stmt_kind] in *; try contradiction; try discriminate.
  Exists pb_2 pa_2 pe_2 x.
  cbn [cm_stmt_payload].
  Intros_p Hpayload.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; subst f; cbn [cm_stmt_wf cm_stmt_counts_representable] in *; tauto.
Qed.

Lemma proof_of_cmc_stmt_code_count_return_wit_1_split_goal_1 : cmc_stmt_code_count_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct s; simpl in *; tauto.
Qed.

Lemma proof_of_cmc_stmt_code_count_return_wit_1_split_goal_2 : cmc_stmt_code_count_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct s; simpl in *; congruence.
Qed.

Lemma proof_of_cmc_stmt_code_count_return_wit_1_split_goal_spatial : cmc_stmt_code_count_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_stmt_rep_node.
  unfold cm_stmt_node.
  Exists pe pa pb.
  split_pure_spatial.
  - cancel.
    cancel (&(stmt_pre # "cm_stmt" ->ₛ "kind") # Int |-> cm_rep_stmt_kind s).
    cancel (&(stmt_pre # "cm_stmt" ->ₛ "slot") # Int |-> cm_rep_stmt_slot s).
    cancel (&(stmt_pre # "cm_stmt" ->ₛ "expr") # Ptr |-> pe).
    cancel (&(stmt_pre # "cm_stmt" ->ₛ "a") # Ptr |-> pa).
    cancel (&(stmt_pre # "cm_stmt" ->ₛ "b") # Ptr |-> pb).
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cmc_stmt_code_count_return_wit_1 : cmc_stmt_code_count_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_stmt_code_count_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_cmc_stmt_code_count_return_wit_1_split_goal_1.
  - Goal_apply proof_of_cmc_stmt_code_count_return_wit_1_split_goal_2.
Qed. 

Lemma proof_of_cmc_stmt_code_count_return_wit_2_split_goal_1 : cmc_stmt_code_count_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct s; simpl in *; tauto.
Qed.

Lemma proof_of_cmc_stmt_code_count_return_wit_2_split_goal_2 : cmc_stmt_code_count_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct s; simpl in *; congruence.
Qed.

Lemma proof_of_cmc_stmt_code_count_return_wit_2_split_goal_spatial : cmc_stmt_code_count_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_stmt_rep_node.
  unfold cm_stmt_node.
  Exists pe pa pb.
  split_pure_spatial.
  - cancel.
    cancel (&(stmt_pre # "cm_stmt" ->ₛ "kind") # Int |-> cm_rep_stmt_kind s).
    cancel (&(stmt_pre # "cm_stmt" ->ₛ "slot") # Int |-> cm_rep_stmt_slot s).
    cancel (&(stmt_pre # "cm_stmt" ->ₛ "expr") # Ptr |-> pe).
    cancel (&(stmt_pre # "cm_stmt" ->ₛ "a") # Ptr |-> pa).
    cancel (&(stmt_pre # "cm_stmt" ->ₛ "b") # Ptr |-> pb).
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cmc_stmt_code_count_return_wit_2 : cmc_stmt_code_count_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_stmt_code_count_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_cmc_stmt_code_count_return_wit_2_split_goal_1.
  - Goal_apply proof_of_cmc_stmt_code_count_return_wit_2_split_goal_2.
Qed. 

Lemma proof_of_cmc_stmt_code_count_return_wit_3_split_goal_1 : cmc_stmt_code_count_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst s. exact (proj1 PreH23).
Qed.

Lemma proof_of_cmc_stmt_code_count_return_wit_3_split_goal_2 : cmc_stmt_code_count_return_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. rewrite PreH24, PreH13. reflexivity.
Qed.

Lemma proof_of_cmc_stmt_code_count_return_wit_3_split_goal_spatial : cmc_stmt_code_count_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_stmt_rep_node. unfold cm_stmt_node.
  Exists pe pa pb. rewrite PreH24. cbn [cm_stmt_payload].
  split_pure_spatial; [repeat progress cancel | split_pures; dump_pre_spatial; tauto].
Qed.

Lemma proof_of_cmc_stmt_code_count_return_wit_3 : cmc_stmt_code_count_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_stmt_code_count_return_wit_3_split_goal_spatial.
  - Goal_apply proof_of_cmc_stmt_code_count_return_wit_3_split_goal_1.
  - Goal_apply proof_of_cmc_stmt_code_count_return_wit_3_split_goal_2.

Qed. 

Lemma proof_of_cmc_stmt_code_count_return_wit_4_split_goal_1 : cmc_stmt_code_count_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst s. exact (proj1 PreH26).
Qed.

Lemma proof_of_cmc_stmt_code_count_return_wit_4_split_goal_2 : cmc_stmt_code_count_return_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. rewrite PreH27, PreH14, PreH5, PreH17, PreH27.
  cbn [cm_stmt_code_count cm_rep_stmt_slot].
  rewrite cm_slot_encode__statement_expression_results.
  - rewrite cm_normalize_encode__statement_expression_results.
    + rewrite PreH7. reflexivity.
    + rewrite <- PreH10. exact PreH31.
  - rewrite <- PreH10. lia.
Qed.

Lemma proof_of_cmc_stmt_code_count_return_wit_4_split_goal_spatial : cmc_stmt_code_count_return_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_stmt_rep_node. unfold cm_stmt_node.
  Exists pe pa pb. rewrite PreH27. cbn [cm_stmt_payload].
  split_pure_spatial; [repeat progress cancel | split_pures; dump_pre_spatial; tauto].
Qed.

Lemma proof_of_cmc_stmt_code_count_return_wit_4 : cmc_stmt_code_count_return_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_stmt_code_count_return_wit_4_split_goal_spatial.
  - Goal_apply proof_of_cmc_stmt_code_count_return_wit_4_split_goal_1.
  - Goal_apply proof_of_cmc_stmt_code_count_return_wit_4_split_goal_2.

Qed. 

Lemma proof_of_cmc_stmt_code_count_return_wit_5_split_goal_1 : cmc_stmt_code_count_return_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct s; exact (proj1 PreH33).
Qed.

Lemma proof_of_cmc_stmt_code_count_return_wit_5_split_goal_2 : cmc_stmt_code_count_return_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst s; cbn [cm_stmt_code_count]; congruence.
Qed.

Lemma proof_of_cmc_stmt_code_count_return_wit_5_split_goal_spatial : cmc_stmt_code_count_return_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (cm_stmt_rep_node stmt_pre s).
  unfold cm_stmt_node.
  Exists pe pa pb.
  subst s.
  cbn [cm_stmt_payload].
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_cmc_stmt_code_count_return_wit_5 : cmc_stmt_code_count_return_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_stmt_code_count_return_wit_5_split_goal_spatial.
  - Goal_apply proof_of_cmc_stmt_code_count_return_wit_5_split_goal_1.
  - Goal_apply proof_of_cmc_stmt_code_count_return_wit_5_split_goal_2.
Qed.

Lemma proof_of_cmc_stmt_code_count_return_wit_6_split_goal_1 : cmc_stmt_code_count_return_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct s; exact (proj1 PreH23).
Qed.

Lemma proof_of_cmc_stmt_code_count_return_wit_6_split_goal_2 : cmc_stmt_code_count_return_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst s; cbn [cm_stmt_code_count]; congruence.
Qed.

Lemma proof_of_cmc_stmt_code_count_return_wit_6_split_goal_spatial : cmc_stmt_code_count_return_wit_6_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (cm_stmt_rep_node stmt_pre s).
  unfold cm_stmt_node.
  Exists pe pa pb.
  subst s.
  cbn [cm_stmt_payload].
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_cmc_stmt_code_count_return_wit_6 : cmc_stmt_code_count_return_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_stmt_code_count_return_wit_6_split_goal_spatial.
  - Goal_apply proof_of_cmc_stmt_code_count_return_wit_6_split_goal_1.
  - Goal_apply proof_of_cmc_stmt_code_count_return_wit_6_split_goal_2.
Qed.

Lemma proof_of_cmc_stmt_code_count_return_wit_7_split_goal_1 : cmc_stmt_code_count_return_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct s; exact (proj1 PreH43).
Qed.

Lemma proof_of_cmc_stmt_code_count_return_wit_7_split_goal_2 : cmc_stmt_code_count_return_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst s; cbn [cm_stmt_code_count]; congruence.
Qed.

Lemma proof_of_cmc_stmt_code_count_return_wit_7_split_goal_spatial : cmc_stmt_code_count_return_wit_7_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (cm_stmt_rep_node stmt_pre s).
  unfold cm_stmt_node.
  Exists pe pa pb.
  subst s.
  cbn [cm_stmt_payload].
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_cmc_stmt_code_count_return_wit_7 : cmc_stmt_code_count_return_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_stmt_code_count_return_wit_7_split_goal_spatial.
  - Goal_apply proof_of_cmc_stmt_code_count_return_wit_7_split_goal_1.
  - Goal_apply proof_of_cmc_stmt_code_count_return_wit_7_split_goal_2.
Qed.

Lemma proof_of_cmc_stmt_code_count_return_wit_8_split_goal_1 : cmc_stmt_code_count_return_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct s; exact (proj1 PreH33).
Qed.

Lemma proof_of_cmc_stmt_code_count_return_wit_8_split_goal_2 : cmc_stmt_code_count_return_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst s; cbn [cm_stmt_code_count]; congruence.
Qed.

Lemma proof_of_cmc_stmt_code_count_return_wit_8_split_goal_spatial : cmc_stmt_code_count_return_wit_8_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (cm_stmt_rep_node stmt_pre s).
  unfold cm_stmt_node.
  Exists pe pa pb.
  subst s.
  cbn [cm_stmt_payload].
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_cmc_stmt_code_count_return_wit_8 : cmc_stmt_code_count_return_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_stmt_code_count_return_wit_8_split_goal_spatial.
  - Goal_apply proof_of_cmc_stmt_code_count_return_wit_8_split_goal_1.
  - Goal_apply proof_of_cmc_stmt_code_count_return_wit_8_split_goal_2.
Qed.

Lemma proof_of_cmc_stmt_code_count_return_wit_9_split_goal_1 : cmc_stmt_code_count_return_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct s; simpl in *; tauto.
Qed.

Lemma proof_of_cmc_stmt_code_count_return_wit_9_split_goal_2 : cmc_stmt_code_count_return_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct s; simpl in *; congruence.
Qed.

Lemma proof_of_cmc_stmt_code_count_return_wit_9_split_goal_spatial : cmc_stmt_code_count_return_wit_9_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_stmt_rep_node.
  unfold cm_stmt_node.
  Exists pe pa pb.
  split_pure_spatial.
  - cancel.
    cancel (&(stmt_pre # "cm_stmt" ->ₛ "kind") # Int |-> cm_rep_stmt_kind s).
    cancel (&(stmt_pre # "cm_stmt" ->ₛ "slot") # Int |-> cm_rep_stmt_slot s).
    cancel (&(stmt_pre # "cm_stmt" ->ₛ "expr") # Ptr |-> pe).
    cancel (&(stmt_pre # "cm_stmt" ->ₛ "a") # Ptr |-> pa).
    cancel (&(stmt_pre # "cm_stmt" ->ₛ "b") # Ptr |-> pb).
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cmc_stmt_code_count_return_wit_9 : cmc_stmt_code_count_return_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_stmt_code_count_return_wit_9_split_goal_spatial.
  - Goal_apply proof_of_cmc_stmt_code_count_return_wit_9_split_goal_1.
  - Goal_apply proof_of_cmc_stmt_code_count_return_wit_9_split_goal_2.
Qed. 

Lemma proof_of_cmc_stmt_code_count_return_wit_10_split_goal_1 : cmc_stmt_code_count_return_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct s; simpl in *; tauto.
Qed.

Lemma proof_of_cmc_stmt_code_count_return_wit_10_split_goal_2 : cmc_stmt_code_count_return_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct s; simpl in *; congruence.
Qed.

Lemma proof_of_cmc_stmt_code_count_return_wit_10_split_goal_spatial : cmc_stmt_code_count_return_wit_10_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_stmt_rep_node.
  unfold cm_stmt_node.
  Exists pe pa pb.
  split_pure_spatial.
  - cancel.
    cancel (&(stmt_pre # "cm_stmt" ->ₛ "kind") # Int |-> cm_rep_stmt_kind s).
    cancel (&(stmt_pre # "cm_stmt" ->ₛ "slot") # Int |-> cm_rep_stmt_slot s).
    cancel (&(stmt_pre # "cm_stmt" ->ₛ "expr") # Ptr |-> pe).
    cancel (&(stmt_pre # "cm_stmt" ->ₛ "a") # Ptr |-> pa).
    cancel (&(stmt_pre # "cm_stmt" ->ₛ "b") # Ptr |-> pb).
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cmc_stmt_code_count_return_wit_10 : cmc_stmt_code_count_return_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_stmt_code_count_return_wit_10_split_goal_spatial.
  - Goal_apply proof_of_cmc_stmt_code_count_return_wit_10_split_goal_1.
  - Goal_apply proof_of_cmc_stmt_code_count_return_wit_10_split_goal_2.
Qed. 

Lemma proof_of_cmc_stmt_code_count_return_wit_11_split_goal_1 : cmc_stmt_code_count_return_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst s. exact (proj1 PreH24).
Qed.

Lemma proof_of_cmc_stmt_code_count_return_wit_11_split_goal_2 : cmc_stmt_code_count_return_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. rewrite PreH25, PreH14, PreH5.
  rewrite cm_normalize_encode__statement_expression_results by exact PreH27.
  rewrite PreH7. reflexivity.
Qed.

Lemma proof_of_cmc_stmt_code_count_return_wit_11_split_goal_spatial : cmc_stmt_code_count_return_wit_11_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_stmt_rep_node. unfold cm_stmt_node.
  Exists pe pa pb. rewrite PreH25. cbn [cm_stmt_payload].
  split_pure_spatial; [repeat progress cancel | split_pures; dump_pre_spatial; tauto].
Qed.

Lemma proof_of_cmc_stmt_code_count_return_wit_11 : cmc_stmt_code_count_return_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_stmt_code_count_return_wit_11_split_goal_spatial.
  - Goal_apply proof_of_cmc_stmt_code_count_return_wit_11_split_goal_1.
  - Goal_apply proof_of_cmc_stmt_code_count_return_wit_11_split_goal_2.

Qed. 

Lemma proof_of_cmc_stmt_code_count_partial_solve_wit_2_pure_split_goal_1 : cmc_stmt_code_count_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst s. cbn [cm_rep_stmt_slot]. assumption.
Qed.

Lemma proof_of_cmc_stmt_code_count_partial_solve_wit_2_pure : cmc_stmt_code_count_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_stmt_code_count_partial_solve_wit_2_pure_split_goal_1.
Qed.

Lemma proof_of_cmc_param_stores_count_safety_wit_3_split_goal_1 : cmc_param_stores_count_safety_wit_3_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 dump_pre_spatial. subst.
 rewrite cm_normalize_encode__parameter_stores by assumption.
 cbn [cm_param_counts_representable cm_param_stores_count] in *.
 unfold cm_i32_code_count in *. lia.
Qed.

Lemma proof_of_cmc_param_stores_count_safety_wit_3_split_goal_2 : cmc_param_stores_count_safety_wit_3_split_goal_2.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 dump_pre_spatial. subst.
 rewrite cm_normalize_encode__parameter_stores by assumption.
 cbn [cm_param_counts_representable cm_param_stores_count] in *.
 unfold cm_i32_code_count in *. lia.
Qed.

Lemma proof_of_cmc_param_stores_count_safety_wit_3 : cmc_param_stores_count_safety_wit_3.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_cmc_param_stores_count_safety_wit_3_split_goal_1.
 Goal_apply proof_of_cmc_param_stores_count_safety_wit_3_split_goal_2.
Qed.

Lemma proof_of_cmc_param_stores_count_safety_wit_4_split_goal_1 : cmc_param_stores_count_safety_wit_4_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 dump_pre_spatial. subst.
 rewrite cm_normalize_encode__parameter_stores by assumption.
 cbn [cm_param_counts_representable cm_param_stores_count] in *.
 unfold cm_i32_code_count in *. lia.
Qed.

Lemma proof_of_cmc_param_stores_count_safety_wit_4_split_goal_2 : cmc_param_stores_count_safety_wit_4_split_goal_2.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 dump_pre_spatial. subst.
 rewrite cm_normalize_encode__parameter_stores by assumption.
 unfold cm_i32_code_count in *.
 unfold cm_char_normalize_count. destruct (cm_slot_ty h); lia.
Qed.

Lemma proof_of_cmc_param_stores_count_safety_wit_4 : cmc_param_stores_count_safety_wit_4.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_cmc_param_stores_count_safety_wit_4_split_goal_1.
 Goal_apply proof_of_cmc_param_stores_count_safety_wit_4_split_goal_2.
Qed.

Lemma proof_of_cmc_param_stores_count_entail_wit_1 : cmc_param_stores_count_entail_wit_1.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 destruct params as [|h t]; cbn [cm_slot_list_rep].
 - Intros_p Hp. contradiction.
 - Intros np. Exists np h t.
   split_pure_spatial; [repeat progress cancel |].
   split_pures; dump_pre_spatial;
     cbn [cm_param_counts_representable] in *; intuition.
Qed.

Lemma proof_of_cmc_param_stores_count_return_wit_1_split_goal_1 : cmc_param_stores_count_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_cmc_param_stores_count_return_wit_1_split_goal_2 : cmc_param_stores_count_return_wit_1_split_goal_2.
Proof. Abort.

Lemma proof_of_cmc_param_stores_count_return_wit_1 : cmc_param_stores_count_return_wit_1.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 destruct params as [|h t]; cbn [cm_slot_list_rep cm_param_stores_count].
 - Intros_p Hp. split_pure_spatial; [repeat progress cancel |].
   split_pures; dump_pre_spatial; unfold cm_i32_code_count; intuition lia.
 - Intros np. contradiction.
Qed.

Lemma proof_of_cmc_param_stores_count_return_wit_2_split_goal_1 : cmc_param_stores_count_return_wit_2_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 dump_pre_spatial. subst.
 rewrite cm_normalize_encode__parameter_stores by assumption.
 cbn [cm_param_counts_representable cm_param_stores_count] in *.
 tauto.
Qed.

Lemma proof_of_cmc_param_stores_count_return_wit_2_split_goal_2 : cmc_param_stores_count_return_wit_2_split_goal_2.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 dump_pre_spatial. subst.
 rewrite cm_normalize_encode__parameter_stores by assumption.
 reflexivity.
Qed.

Lemma proof_of_cmc_param_stores_count_return_wit_2_split_goal_spatial : cmc_param_stores_count_return_wit_2_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 subst params. cbn [cm_slot_list_rep]. Exists np.
 split_pure_spatial; [repeat progress cancel |].
 dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cmc_param_stores_count_return_wit_2 : cmc_param_stores_count_return_wit_2.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_cmc_param_stores_count_return_wit_2_split_goal_spatial.
 Goal_apply proof_of_cmc_param_stores_count_return_wit_2_split_goal_1.
 Goal_apply proof_of_cmc_param_stores_count_return_wit_2_split_goal_2.
Qed.

Lemma proof_of_cmc_function_prologue_count_safety_wit_1_split_goal_1 : cmc_function_prologue_count_safety_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold cm_i32_code_count, cm_function_prologue_count in *.
  subst; lia.
Qed.

Lemma proof_of_cmc_function_prologue_count_safety_wit_1_split_goal_2 : cmc_function_prologue_count_safety_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold cm_i32_code_count, cm_function_prologue_count in *.
  subst; lia.
Qed.

Lemma proof_of_cmc_function_prologue_count_safety_wit_1 : cmc_function_prologue_count_safety_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_function_prologue_count_safety_wit_1_split_goal_1.
  - Goal_apply proof_of_cmc_function_prologue_count_safety_wit_1_split_goal_2.
Qed.

Lemma proof_of_cmc_function_prologue_count_entail_wit_1 : cmc_function_prologue_count_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_function_context_rep.
  Intros pp lp.
  Exists lp pp.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_cmc_function_prologue_count_return_wit_1_split_goal_1 : cmc_function_prologue_count_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold cm_i32_code_count, cm_function_prologue_count in *.
  subst; lia.
Qed.

Lemma proof_of_cmc_function_prologue_count_return_wit_1_split_goal_2 : cmc_function_prologue_count_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold cm_function_prologue_count in *.
  subst; reflexivity.
Qed.

Lemma proof_of_cmc_function_prologue_count_return_wit_1_split_goal_spatial : cmc_function_prologue_count_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_function_context_rep.
  Exists pp lp.
  split_pure_spatial.
  - repeat progress cancel.
  - dump_pre_spatial; auto.
Qed.

Lemma proof_of_cmc_function_prologue_count_return_wit_1 : cmc_function_prologue_count_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_function_prologue_count_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_cmc_function_prologue_count_return_wit_1_split_goal_1.
  - Goal_apply proof_of_cmc_function_prologue_count_return_wit_1_split_goal_2.
Qed.

Lemma proof_of_cmc_function_code_count_safety_wit_1_split_goal_1 : cmc_function_code_count_safety_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold cm_function_counts_representable, cm_i32_code_count in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  subst. unfold cm_function_code_count in *. lia.
Qed.

Lemma proof_of_cmc_function_code_count_safety_wit_1_split_goal_2 : cmc_function_code_count_safety_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold cm_i32_code_count in *. lia.
Qed.

Lemma proof_of_cmc_function_code_count_safety_wit_1 : cmc_function_code_count_safety_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_function_code_count_safety_wit_1_split_goal_1.
  - Goal_apply proof_of_cmc_function_code_count_safety_wit_1_split_goal_2.
Qed.

Lemma proof_of_cmc_function_code_count_safety_wit_2_split_goal_1 : cmc_function_code_count_safety_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold cm_function_counts_representable, cm_i32_code_count in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  subst. unfold cm_function_code_count in *. lia.
Qed.

Lemma proof_of_cmc_function_code_count_safety_wit_2_split_goal_2 : cmc_function_code_count_safety_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold cm_i32_code_count in *. lia.
Qed.

Lemma proof_of_cmc_function_code_count_safety_wit_2 : cmc_function_code_count_safety_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_function_code_count_safety_wit_2_split_goal_1.
  - Goal_apply proof_of_cmc_function_code_count_safety_wit_2_split_goal_2.
Qed.

Lemma proof_of_cmc_function_code_count_entail_wit_1 : cmc_function_code_count_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_program_context_rep, cm_function_context_rep.
  Intros pp lp sp gp tp.
  Exists lp pp tp gp sp.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; unfold cm_function_counts_representable in *; tauto.
Qed.

Lemma proof_of_cmc_function_code_count_return_wit_1_split_goal_1 : cmc_function_code_count_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold cm_function_counts_representable, cm_i32_code_count in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  subst. unfold cm_function_code_count in *. lia.
Qed.

Lemma proof_of_cmc_function_code_count_return_wit_1_split_goal_2 : cmc_function_code_count_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst. unfold cm_function_code_count. reflexivity.
Qed.

Lemma proof_of_cmc_function_code_count_return_wit_1_split_goal_spatial : cmc_function_code_count_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_program_context_rep, cm_function_context_rep.
  Exists sp gp tp pp lp.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_cmc_function_code_count_return_wit_1 : cmc_function_code_count_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_function_code_count_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_cmc_function_code_count_return_wit_1_split_goal_1.
  - Goal_apply proof_of_cmc_function_code_count_return_wit_1_split_goal_2.
Qed.

Lemma proof_of_cmc_function_code_count_partial_solve_wit_1_pure_split_goal_1 : cmc_function_code_count_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. unfold cm_function_counts_representable in *. tauto.
Qed.

Lemma proof_of_cmc_function_code_count_partial_solve_wit_1_pure_split_goal_2 : cmc_function_code_count_partial_solve_wit_1_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. unfold cm_function_counts_representable in *. tauto.
Qed.

Lemma proof_of_cmc_function_code_count_partial_solve_wit_1_pure : cmc_function_code_count_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_function_code_count_partial_solve_wit_1_pure_split_goal_1.
  - Goal_apply proof_of_cmc_function_code_count_partial_solve_wit_1_pure_split_goal_2.
Qed.

Lemma proof_of_cmc_function_prefix_count_safety_wit_9_split_goal_1 : cmc_function_prefix_count_safety_wit_9_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 dump_pre_spatial.
 subst functions.
 cbn [cm_function_prefix] in PreH26.
 assert (Hguard : Z.eqb remaining_pre 0 = false) by (apply Z.eqb_neq; exact PreH17).
 rewrite Hguard, <- PreH21 in PreH26.
 unfold cm_i32_code_count in PreH26.
 subst head_count retval.
 int_auto.
Qed.

Lemma proof_of_cmc_function_prefix_count_safety_wit_9_split_goal_2 : cmc_function_prefix_count_safety_wit_9_split_goal_2.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 dump_pre_spatial.
 unfold cm_i32_code_count in PreH11, PreH28.
 int_auto.
Qed.

Lemma proof_of_cmc_function_prefix_count_safety_wit_9 : cmc_function_prefix_count_safety_wit_9.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_cmc_function_prefix_count_safety_wit_9_split_goal_1.
 - Goal_apply proof_of_cmc_function_prefix_count_safety_wit_9_split_goal_2.
Qed.

Lemma proof_of_cmc_function_prefix_count_entail_wit_1 : cmc_function_prefix_count_entail_wit_1.
Proof.
 LLM_pre_process ltac:(lia).
 destruct functions as [|f rest].
 - rewrite Zlength_nil in *. lia.
 - pose proof PreH7 as Hrepr.
   cbn [cm_functions_counts_representable] in Hrepr.
   destruct Hrepr as [_ [Hhead Htail]].
   assert (Hbound: 0<=index_pre<Zlength (cm_program_functions p)).
   { rewrite Zlength_cons in PreH6. pose proof (Zlength_nonneg rest). lia. }
   pose proof PreH3 as Htyped.
   unfold cm_wf_program, cm_codegen_admissible, cm_typed_program in Htyped.
   destruct Htyped as [[_ [_ [_ [Hfun _]]]] _].
   specialize (Hfun index_pre Hbound).
   pose proof (proj1 Hhead) as Heq.
   rewrite <- Heq in Hfun.
   unfold cm_function_wf in Hfun.
   assert (Hbody: cm_stmt_wf policy p f false (cm_function_body f)) by tauto.
   rewrite cm_function_list_cons__prefix_open.
   Intros bp np.
   Exists bp np f rest.
   split_pure_spatial.
   + repeat progress cancel; reflexivity.
   + split_pures; dump_pre_spatial; auto.
Qed. 

Lemma proof_of_cmc_function_prefix_count_entail_wit_2 : cmc_function_prefix_count_entail_wit_2.
Proof.
 LLM_pre_process ltac:(lia).
 unfold cm_function_context_rep.
 Intros pp lp.
 Exists np_2 bp_2 lp pp f_2 rest_2.
 split_pure_spatial.
 - repeat progress cancel; reflexivity.
 - split_pures; dump_pre_spatial; auto.
Qed. 

Lemma proof_of_cmc_function_prefix_count_return_wit_1_split_goal_1 : cmc_function_prefix_count_return_wit_1_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 dump_pre_spatial.
 subst functions head_count retval.
 assert (E : Z.eqb remaining_pre 0 = false) by (apply Z.eqb_neq; assumption).
 cbn [cm_function_prefix] in PreH28.
 rewrite E, <- PreH23 in PreH28.
 unfold cm_i32_code_count in *. lia.
Qed.

Lemma proof_of_cmc_function_prefix_count_return_wit_1_split_goal_2 : cmc_function_prefix_count_return_wit_1_split_goal_2.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 dump_pre_spatial.
 subst functions head_count retval.
 assert (E : Z.eqb remaining_pre 0 = false) by (apply Z.eqb_neq; assumption).
 cbn [cm_function_prefix]. rewrite E, <- PreH23. reflexivity.
Qed.

Lemma proof_of_cmc_function_prefix_count_return_wit_1_split_goal_spatial : cmc_function_prefix_count_return_wit_1_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 subst functions.
 rewrite cm_function_list_cons__prefix_results.
 Exists bp np.
 unfold cm_function_context_rep. Exists pp lp.
 split_pure_spatial.
 - repeat progress cancel.
 - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_cmc_function_prefix_count_return_wit_1 : cmc_function_prefix_count_return_wit_1.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_cmc_function_prefix_count_return_wit_1_split_goal_spatial.
 - Goal_apply proof_of_cmc_function_prefix_count_return_wit_1_split_goal_1.
 - Goal_apply proof_of_cmc_function_prefix_count_return_wit_1_split_goal_2.
Qed.

Lemma proof_of_cmc_function_prefix_count_return_wit_2_split_goal_1 : cmc_function_prefix_count_return_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_cmc_function_prefix_count_return_wit_2_split_goal_2 : cmc_function_prefix_count_return_wit_2_split_goal_2.
Proof. Abort.

Lemma proof_of_cmc_function_prefix_count_return_wit_2 : cmc_function_prefix_count_return_wit_2.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 destruct functions as [|f rest].
 - cbn [cm_function_prefix]. unfold cm_i32_code_count in *.
   split_pure_spatial; [repeat progress cancel | split_pures; dump_pre_spatial; auto; lia].
 - unfold cm_function_list_rep.
   Intros bs. cbn [cm_function_header_list_rep cm_function_body_list_rep].
   Intros b n bt b' bt'. exfalso. lia.
Qed.

Lemma proof_of_cmc_function_prefix_count_return_wit_3_split_goal_1 : cmc_function_prefix_count_return_wit_3_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 unfold cm_i32_code_count. lia.
Qed.

Lemma proof_of_cmc_function_prefix_count_return_wit_3_split_goal_2 : cmc_function_prefix_count_return_wit_3_split_goal_2.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 destruct functions; reflexivity.
Qed.

Lemma proof_of_cmc_function_prefix_count_return_wit_3 : cmc_function_prefix_count_return_wit_3.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_cmc_function_prefix_count_return_wit_3_split_goal_1.
 - Goal_apply proof_of_cmc_function_prefix_count_return_wit_3_split_goal_2.
Qed.

Lemma proof_of_cmc_function_prefix_count_partial_solve_wit_2_pure_split_goal_1 : cmc_function_prefix_count_partial_solve_wit_2_pure_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 dump_pre_spatial.
 subst functions. rewrite Zlength_cons in PreH18. lia.
Qed.

Lemma proof_of_cmc_function_prefix_count_partial_solve_wit_2_pure_split_goal_2 : cmc_function_prefix_count_partial_solve_wit_2_pure_split_goal_2.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 dump_pre_spatial.
 subst functions. rewrite Zlength_cons in PreH21. lia.
Qed.

Lemma proof_of_cmc_function_prefix_count_partial_solve_wit_2_pure_split_goal_3 : cmc_function_prefix_count_partial_solve_wit_2_pure_split_goal_3.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 dump_pre_spatial.
 subst functions.
 assert (Htailindex : index_pre + 1 = Zlength (cm_program_functions p) - Zlength rest).
 { rewrite Zlength_cons in PreH18. lia. }
 assert (Htailrange : 0 <= remaining_pre - 1 <= Zlength rest).
 { rewrite Zlength_cons in PreH21. lia. }
 pose proof (cm_function_prefix_nonnegative__prefix_transition policy p rest
   (index_pre + 1) (remaining_pre - 1) PreH13 Htailindex Htailrange) as Hnonneg.
 cbn [cm_function_prefix] in PreH23.
 assert (Hguard : Z.eqb remaining_pre 0 = false) by (apply Z.eqb_neq; exact PreH14).
 rewrite Hguard, <- PreH18 in PreH23.
 unfold cm_i32_code_count in *.
 lia.
Qed.

Lemma proof_of_cmc_function_prefix_count_partial_solve_wit_2_pure : cmc_function_prefix_count_partial_solve_wit_2_pure.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_cmc_function_prefix_count_partial_solve_wit_2_pure_split_goal_1.
 - Goal_apply proof_of_cmc_function_prefix_count_partial_solve_wit_2_pure_split_goal_2.
 - Goal_apply proof_of_cmc_function_prefix_count_partial_solve_wit_2_pure_split_goal_3.
Qed.

Lemma proof_of_cmc_function_pc_safety_wit_2_split_goal_1 : cmc_function_pc_safety_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_i32_code_count in *.
  subst retval. dump_pre_spatial. lia.
Qed.

Lemma proof_of_cmc_function_pc_safety_wit_2_split_goal_2 : cmc_function_pc_safety_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_i32_code_count in *.
  subst retval. dump_pre_spatial. lia.
Qed.

Lemma proof_of_cmc_function_pc_safety_wit_2 : cmc_function_pc_safety_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_function_pc_safety_wit_2_split_goal_1.
  - Goal_apply proof_of_cmc_function_pc_safety_wit_2_split_goal_2.
Qed. 

Lemma proof_of_cmc_function_pc_entail_wit_1 : cmc_function_pc_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_program_context_rep.
  Intros sp0 gp0 tp0.
  Exists tp0 gp0 sp0.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed. 

Lemma proof_of_cmc_function_pc_entail_wit_2_split_goal_1 : cmc_function_pc_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_wf_program, cm_codegen_admissible, cm_codegen_counts_representable in *.
  dump_pre_spatial. tauto.
Qed.

Lemma proof_of_cmc_function_pc_entail_wit_2_split_goal_spatial : cmc_function_pc_entail_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_program_context_rep.
  Exists sp gp tp.
  split_pure_spatial.
  - repeat progress cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cmc_function_pc_entail_wit_2 : cmc_function_pc_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_function_pc_entail_wit_2_split_goal_spatial.
  - Goal_apply proof_of_cmc_function_pc_entail_wit_2_split_goal_1.
Qed. 

Lemma proof_of_cmc_function_pc_return_wit_1_split_goal_1 : cmc_function_pc_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_function_pc. congruence.
Qed.

Lemma proof_of_cmc_function_pc_return_wit_1 : cmc_function_pc_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_function_pc_return_wit_1_split_goal_1.
Qed. 

Lemma proof_of_cmc_function_pc_partial_solve_wit_1_pure_split_goal_1 : cmc_function_pc_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cmc_function_pc_partial_solve_wit_1_pure : cmc_function_pc_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_function_pc_partial_solve_wit_1_pure_split_goal_1.
Qed. 

Lemma proof_of_cmc_functions_code_size_count_safety_wit_3_split_goal_1 : cmc_functions_code_size_count_safety_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst functions.
  rewrite Zlength_cons in *.
  pose proof (Zlength_nonneg rest).
  lia.
Qed.

Lemma proof_of_cmc_functions_code_size_count_safety_wit_3_split_goal_2 : cmc_functions_code_size_count_safety_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cmc_functions_code_size_count_safety_wit_3 : cmc_functions_code_size_count_safety_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_functions_code_size_count_safety_wit_3_split_goal_1.
  - Goal_apply proof_of_cmc_functions_code_size_count_safety_wit_3_split_goal_2.
Qed.

Lemma proof_of_cmc_functions_code_size_count_safety_wit_5_split_goal_1 : cmc_functions_code_size_count_safety_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst functions head_count retval.
  cbn [cm_functions_code_size] in *.
  unfold cm_i32_code_count in *.
  int_auto.
Qed.

Lemma proof_of_cmc_functions_code_size_count_safety_wit_5_split_goal_2 : cmc_functions_code_size_count_safety_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold cm_i32_code_count in *.
  int_auto.
Qed.

Lemma proof_of_cmc_functions_code_size_count_safety_wit_5 : cmc_functions_code_size_count_safety_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_functions_code_size_count_safety_wit_5_split_goal_1.
  - Goal_apply proof_of_cmc_functions_code_size_count_safety_wit_5_split_goal_2.
Qed.

Lemma proof_of_cmc_functions_code_size_count_entail_wit_1 : cmc_functions_code_size_count_entail_wit_1.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 destruct functions as [|f rest].
 - unfold cm_function_list_rep.
   cbn [cm_function_header_list_rep cm_function_body_list_rep].
   Intros bs.
   exfalso; tauto.
 - rewrite cm_function_list_cons__functions_open.
   Intros bp np.
   assert (Hhead : cm_function_counts_representable policy p index_pre f)
     by (cbn [cm_functions_counts_representable] in PreH6; tauto).
   assert (Htail : cm_functions_counts_representable policy p rest (index_pre+1))
     by (cbn [cm_functions_counts_representable] in PreH6; tauto).
   assert (Hbound : 0<=index_pre<Zlength (cm_program_functions p)).
   { rewrite Zlength_cons in PreH5.
     pose proof (Zlength_nonneg rest). lia. }
   assert (Hlookup : f=cm_function_at policy index_pre (cm_program_functions p))
     by (unfold cm_function_counts_representable in Hhead; tauto).
   assert (Hstmt : cm_stmt_wf policy p f false (cm_function_body f)).
   { unfold cm_wf_program, cm_codegen_admissible, cm_typed_program in PreH2.
     destruct PreH2 as [[Hs [Hg [Ht [Hf Hmore]]]] Hcg].
     specialize (Hf index_pre Hbound).
     rewrite <- Hlookup in Hf.
     unfold cm_function_wf in Hf; tauto. }
   Exists bp np f rest.
   split_pure_spatial.
   + repeat progress cancel; reflexivity.
   + split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_cmc_functions_code_size_count_entail_wit_2 : cmc_functions_code_size_count_entail_wit_2.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 unfold cm_function_context_rep.
 poly_store_unfold.
 Intros pp lp.
 Exists np_2 bp_2 lp pp f_2 rest_2.
 split_pure_spatial.
 - repeat progress cancel; reflexivity.
 - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_cmc_functions_code_size_count_return_wit_1_split_goal_1 : cmc_functions_code_size_count_return_wit_1_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 dump_pre_spatial. subst. cbn [cm_functions_code_size] in *. assumption.
Qed.

Lemma proof_of_cmc_functions_code_size_count_return_wit_1_split_goal_2 : cmc_functions_code_size_count_return_wit_1_split_goal_2.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 dump_pre_spatial. subst. reflexivity.
Qed.

Lemma proof_of_cmc_functions_code_size_count_return_wit_1_split_goal_spatial : cmc_functions_code_size_count_return_wit_1_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 subst functions.
 rewrite cm_function_list_cons__functions_results.
 Exists bp np.
 unfold cm_function_context_rep.
 Exists pp lp.
 split_pure_spatial.
 - repeat progress cancel.
 - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_cmc_functions_code_size_count_return_wit_1 : cmc_functions_code_size_count_return_wit_1.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_cmc_functions_code_size_count_return_wit_1_split_goal_spatial.
 - Goal_apply proof_of_cmc_functions_code_size_count_return_wit_1_split_goal_1.
 - Goal_apply proof_of_cmc_functions_code_size_count_return_wit_1_split_goal_2.
Qed. 

Lemma proof_of_cmc_functions_code_size_count_return_wit_2_split_goal_1 : cmc_functions_code_size_count_return_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_cmc_functions_code_size_count_return_wit_2_split_goal_2 : cmc_functions_code_size_count_return_wit_2_split_goal_2.
Proof. Abort.

Lemma proof_of_cmc_functions_code_size_count_return_wit_2 : cmc_functions_code_size_count_return_wit_2.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 destruct functions as [|f rest].
 - cbn [cm_functions_code_size].
   split_pure_spatial.
   + cancel.
   + split_pures; dump_pre_spatial; unfold cm_i32_code_count; auto; lia.
 - unfold cm_function_list_rep.
   Intros bs.
   cbn [cm_function_header_list_rep].
   Intros b n bt.
   exfalso. congruence.
Qed. 

Lemma proof_of_cmc_functions_code_size_count_partial_solve_wit_2_pure_split_goal_1 : cmc_functions_code_size_count_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst functions.
  rewrite Zlength_cons in *.
  lia.
Qed.

Lemma proof_of_cmc_functions_code_size_count_partial_solve_wit_2_pure_split_goal_2 : cmc_functions_code_size_count_partial_solve_wit_2_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst functions.
  rewrite Zlength_cons in *.
  lia.
Qed.

Lemma proof_of_cmc_functions_code_size_count_partial_solve_wit_2_pure_split_goal_3 : cmc_functions_code_size_count_partial_solve_wit_2_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct rest; cbn [cm_functions_code_size cm_functions_counts_representable] in *.
  - unfold cm_i32_code_count. lia.
  - tauto.
Qed.

Lemma proof_of_cmc_functions_code_size_count_partial_solve_wit_2_pure : cmc_functions_code_size_count_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_functions_code_size_count_partial_solve_wit_2_pure_split_goal_1.
  - Goal_apply proof_of_cmc_functions_code_size_count_partial_solve_wit_2_pure_split_goal_2.
  - Goal_apply proof_of_cmc_functions_code_size_count_partial_solve_wit_2_pure_split_goal_3.
Qed.

Lemma proof_of_cmc_model_code_length_safety_wit_2_split_goal_1 : cmc_model_code_length_safety_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold cm_i32_code_count, cm_model_code_length in *.
  subst; int_auto.
Qed.

Lemma proof_of_cmc_model_code_length_safety_wit_2_split_goal_2 : cmc_model_code_length_safety_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold cm_i32_code_count in *.
  int_auto.
Qed.

Lemma proof_of_cmc_model_code_length_safety_wit_2 : cmc_model_code_length_safety_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_model_code_length_safety_wit_2_split_goal_1.
  - Goal_apply proof_of_cmc_model_code_length_safety_wit_2_split_goal_2.
Qed.

Lemma proof_of_cmc_model_code_length_entail_wit_1 : cmc_model_code_length_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_program_context_rep.
  Intros sp0 gp0 tp0.
  Exists tp0 gp0 sp0.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_cmc_model_code_length_entail_wit_2_split_goal_1 : cmc_model_code_length_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold cm_wf_program, cm_codegen_admissible, cm_codegen_counts_representable in *.
  match goal with H : _ /\ _ |- _ =>
    assert (Hrep : cm_functions_counts_representable policy p (cm_program_functions p) 0) by tauto;
    assert (Hlength : 0 <= cm_model_code_length policy p <= 2147483647) by tauto
  end.
  pose proof (cm_functions_length_bound__model_length_bound policy p (cm_program_functions p) 0 Hrep).
  unfold cm_model_code_length in Hlength.
  change (Zlength (cm_program_functions p) <= 2147483647). lia.
Qed.

Lemma proof_of_cmc_model_code_length_entail_wit_2_split_goal_2 : cmc_model_code_length_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold cm_wf_program, cm_codegen_admissible, cm_i32_code_count in *.
  tauto.
Qed.

Lemma proof_of_cmc_model_code_length_entail_wit_2_split_goal_3 : cmc_model_code_length_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold cm_wf_program, cm_codegen_admissible, cm_codegen_counts_representable in *.
  tauto.
Qed.

Lemma proof_of_cmc_model_code_length_entail_wit_2_split_goal_spatial : cmc_model_code_length_entail_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_program_context_rep.
  Exists sp gp tp.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures. dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cmc_model_code_length_entail_wit_2 : cmc_model_code_length_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_model_code_length_entail_wit_2_split_goal_spatial.
  - Goal_apply proof_of_cmc_model_code_length_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_cmc_model_code_length_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_cmc_model_code_length_entail_wit_2_split_goal_3.
Qed.

Lemma proof_of_cmc_model_code_length_return_wit_1_split_goal_1 : cmc_model_code_length_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_model_code_length in *.
  subst; assumption.
Qed.

Lemma proof_of_cmc_model_code_length_return_wit_1_split_goal_2 : cmc_model_code_length_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_model_code_length in *.
  subst; reflexivity.
Qed.

Lemma proof_of_cmc_model_code_length_return_wit_1 : cmc_model_code_length_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_model_code_length_return_wit_1_split_goal_1.
  - Goal_apply proof_of_cmc_model_code_length_return_wit_1_split_goal_2.
Qed.

Lemma proof_of_cmc_model_code_length_partial_solve_wit_1_pure_split_goal_1 : cmc_model_code_length_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct (cm_program_functions p) as [|f fs].
  - simpl. unfold cm_i32_code_count; lia.
  - simpl in PreH4. exact (proj1 PreH4).
Qed.

Lemma proof_of_cmc_model_code_length_partial_solve_wit_1_pure : cmc_model_code_length_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_model_code_length_partial_solve_wit_1_pure_split_goal_1.
Qed.

Lemma proof_of_cmc_model_data_length_entail_wit_1 : cmc_model_data_length_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_program_context_rep.
  apply coq_prop_andp_left. intro Hroot.
  apply derivable1s_exp_l. intro s0.
  apply derivable1s_exp_l. intro g0.
  apply derivable1s_exp_l. intro t0.
  Exists t0 g0 s0.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_cmc_model_data_length_return_wit_1_split_goal_1 : cmc_model_data_length_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_i32_code_count.
  split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_cmc_model_data_length_return_wit_1_split_goal_spatial : cmc_model_data_length_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_program_context_rep.
  Exists sp gp tp.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - dump_pre_spatial. auto.
Qed.

Lemma proof_of_cmc_model_data_length_return_wit_1 : cmc_model_data_length_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_model_data_length_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_cmc_model_data_length_return_wit_1_split_goal_1.
Qed.

