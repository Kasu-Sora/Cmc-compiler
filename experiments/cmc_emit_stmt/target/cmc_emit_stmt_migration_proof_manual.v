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
From SimpleC.EE.QCP_demos_human Require Import cmc_emit_stmt_migration_goal.
From SimpleC.EE.QCP_demos_human Require Import cmc_emit_stmt_migration_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.cmc_emit_stmt_migration_lib.
Local Open Scope sac.

Lemma proof_of_cmc_emit_if_stmt_safety_wit_10_split_goal_1 : cmc_emit_if_stmt_safety_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  subst.
  unfold cm_i32_code_count in *.
  cbn [cm_stmt_code_count] in *.
  lia.
Qed.

Lemma proof_of_cmc_emit_if_stmt_safety_wit_10_split_goal_2 : cmc_emit_if_stmt_safety_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  subst.
  unfold cm_i32_code_count in *.
  cbn [cm_stmt_code_count] in *.
  lia.
Qed.

Lemma proof_of_cmc_emit_if_stmt_safety_wit_10 : cmc_emit_if_stmt_safety_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_if_stmt_safety_wit_10_split_goal_1.
  - Goal_apply proof_of_cmc_emit_if_stmt_safety_wit_10_split_goal_2.
Qed. 

Lemma proof_of_cmc_emit_if_stmt_safety_wit_11_split_goal_1 : cmc_emit_if_stmt_safety_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  subst.
  unfold cm_i32_code_count in *.
  cbn [cm_stmt_code_count] in *.
  lia.
Qed.

Lemma proof_of_cmc_emit_if_stmt_safety_wit_11_split_goal_2 : cmc_emit_if_stmt_safety_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  subst.
  unfold cm_i32_code_count in *.
  cbn [cm_stmt_code_count] in *.
  lia.
Qed.

Lemma proof_of_cmc_emit_if_stmt_safety_wit_11 : cmc_emit_if_stmt_safety_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_if_stmt_safety_wit_11_split_goal_1.
  - Goal_apply proof_of_cmc_emit_if_stmt_safety_wit_11_split_goal_2.
Qed. 

Lemma proof_of_cmc_emit_if_stmt_safety_wit_13_split_goal_1 : cmc_emit_if_stmt_safety_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  subst.
  unfold cm_i32_code_count in *.
  cbn [cm_stmt_code_count] in *.
  lia.
Qed.

Lemma proof_of_cmc_emit_if_stmt_safety_wit_13_split_goal_2 : cmc_emit_if_stmt_safety_wit_13_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  subst.
  unfold cm_i32_code_count in *.
  cbn [cm_stmt_code_count] in *.
  lia.
Qed.

Lemma proof_of_cmc_emit_if_stmt_safety_wit_13 : cmc_emit_if_stmt_safety_wit_13.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_if_stmt_safety_wit_13_split_goal_1.
  - Goal_apply proof_of_cmc_emit_if_stmt_safety_wit_13_split_goal_2.
Qed. 

Lemma proof_of_cmc_emit_if_stmt_safety_wit_14_split_goal_1 : cmc_emit_if_stmt_safety_wit_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  subst.
  unfold cm_i32_code_count in *.
  cbn [cm_stmt_code_count] in *.
  lia.
Qed.

Lemma proof_of_cmc_emit_if_stmt_safety_wit_14_split_goal_2 : cmc_emit_if_stmt_safety_wit_14_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  subst.
  unfold cm_i32_code_count in *.
  cbn [cm_stmt_code_count] in *.
  lia.
Qed.

Lemma proof_of_cmc_emit_if_stmt_safety_wit_14 : cmc_emit_if_stmt_safety_wit_14.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_if_stmt_safety_wit_14_split_goal_1.
  - Goal_apply proof_of_cmc_emit_if_stmt_safety_wit_14_split_goal_2.
Qed. 

Lemma proof_of_cmc_emit_if_stmt_safety_wit_15_split_goal_1 : cmc_emit_if_stmt_safety_wit_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  subst.
  unfold cm_i32_code_count in *.
  cbn [cm_stmt_code_count] in *.
  lia.
Qed.

Lemma proof_of_cmc_emit_if_stmt_safety_wit_15_split_goal_2 : cmc_emit_if_stmt_safety_wit_15_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  subst.
  unfold cm_i32_code_count in *.
  cbn [cm_stmt_code_count] in *.
  lia.
Qed.

Lemma proof_of_cmc_emit_if_stmt_safety_wit_15 : cmc_emit_if_stmt_safety_wit_15.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_if_stmt_safety_wit_15_split_goal_1.
  - Goal_apply proof_of_cmc_emit_if_stmt_safety_wit_15_split_goal_2.
Qed. 

Lemma proof_of_cmc_emit_if_stmt_safety_wit_16_split_goal_1 : cmc_emit_if_stmt_safety_wit_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  subst.
  unfold cm_i32_code_count in *.
  cbn [cm_stmt_code_count] in *.
  lia.
Qed.

Lemma proof_of_cmc_emit_if_stmt_safety_wit_16_split_goal_2 : cmc_emit_if_stmt_safety_wit_16_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  subst.
  unfold cm_i32_code_count in *.
  cbn [cm_stmt_code_count] in *.
  lia.
Qed.

Lemma proof_of_cmc_emit_if_stmt_safety_wit_16 : cmc_emit_if_stmt_safety_wit_16.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_if_stmt_safety_wit_16_split_goal_1.
  - Goal_apply proof_of_cmc_emit_if_stmt_safety_wit_16_split_goal_2.
Qed. 

Lemma proof_of_cmc_emit_if_stmt_safety_wit_19_split_goal_1 : cmc_emit_if_stmt_safety_wit_19_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  subst.
  unfold cm_i32_code_count in *.
  cbn [cm_stmt_code_count] in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_cmc_emit_if_stmt_safety_wit_19_split_goal_2 : cmc_emit_if_stmt_safety_wit_19_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  subst.
  unfold cm_i32_code_count in *.
  cbn [cm_stmt_code_count] in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_cmc_emit_if_stmt_safety_wit_19 : cmc_emit_if_stmt_safety_wit_19.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_if_stmt_safety_wit_19_split_goal_1.
  - Goal_apply proof_of_cmc_emit_if_stmt_safety_wit_19_split_goal_2.
Qed. 

Lemma proof_of_cmc_emit_if_stmt_safety_wit_20_split_goal_1 : cmc_emit_if_stmt_safety_wit_20_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  subst.
  unfold cm_i32_code_count in *.
  cbn [cm_stmt_code_count] in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_cmc_emit_if_stmt_safety_wit_20_split_goal_2 : cmc_emit_if_stmt_safety_wit_20_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  subst.
  unfold cm_i32_code_count in *.
  cbn [cm_stmt_code_count] in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_cmc_emit_if_stmt_safety_wit_20 : cmc_emit_if_stmt_safety_wit_20.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_if_stmt_safety_wit_20_split_goal_1.
  - Goal_apply proof_of_cmc_emit_if_stmt_safety_wit_20_split_goal_2.
Qed. 

Lemma proof_of_cmc_emit_if_stmt_safety_wit_21_split_goal_1 : cmc_emit_if_stmt_safety_wit_21_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  subst.
  unfold cm_i32_code_count in *.
  cbn [cm_stmt_code_count] in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_cmc_emit_if_stmt_safety_wit_21_split_goal_2 : cmc_emit_if_stmt_safety_wit_21_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  subst.
  unfold cm_i32_code_count in *.
  cbn [cm_stmt_code_count] in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_cmc_emit_if_stmt_safety_wit_21 : cmc_emit_if_stmt_safety_wit_21.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_if_stmt_safety_wit_21_split_goal_1.
  - Goal_apply proof_of_cmc_emit_if_stmt_safety_wit_21_split_goal_2.
Qed. 

Lemma proof_of_cmc_emit_if_stmt_safety_wit_22_split_goal_1 : cmc_emit_if_stmt_safety_wit_22_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  subst.
  unfold cm_i32_code_count in *.
  cbn [cm_stmt_code_count] in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_cmc_emit_if_stmt_safety_wit_22_split_goal_2 : cmc_emit_if_stmt_safety_wit_22_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  subst.
  unfold cm_i32_code_count in *.
  cbn [cm_stmt_code_count] in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_cmc_emit_if_stmt_safety_wit_22 : cmc_emit_if_stmt_safety_wit_22.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_if_stmt_safety_wit_22_split_goal_1.
  - Goal_apply proof_of_cmc_emit_if_stmt_safety_wit_22_split_goal_2.
Qed. 

Lemma proof_of_cmc_emit_if_stmt_safety_wit_23_split_goal_1 : cmc_emit_if_stmt_safety_wit_23_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  subst.
  unfold cm_i32_code_count in *.
  cbn [cm_stmt_code_count] in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_cmc_emit_if_stmt_safety_wit_23_split_goal_2 : cmc_emit_if_stmt_safety_wit_23_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  subst.
  unfold cm_i32_code_count in *.
  cbn [cm_stmt_code_count] in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_cmc_emit_if_stmt_safety_wit_23 : cmc_emit_if_stmt_safety_wit_23.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_if_stmt_safety_wit_23_split_goal_1.
  - Goal_apply proof_of_cmc_emit_if_stmt_safety_wit_23_split_goal_2.
Qed. 

Lemma proof_of_cmc_emit_if_stmt_partial_solve_wit_17_pure_split_goal_1 : cmc_emit_if_stmt_partial_solve_wit_17_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [cm_stmt_expr cm_stmt_first cm_stmt_second]; first [assumption | reflexivity | lia]).
  all: dump_pre_spatial.
  all: subst retval retval_2.
  all: replace (pc_pre + cm_rvalue_code_count policy p fid_pre guard_ + cm_stmt_code_count policy p fid_pre yes_ + 2) with (pc_pre + cm_rvalue_code_count policy p fid_pre guard_ + 1 + cm_stmt_code_count policy p fid_pre yes_ + 1) by lia.
  all: assumption.
Qed.

Lemma proof_of_cmc_emit_if_stmt_partial_solve_wit_17_pure_split_goal_2 : cmc_emit_if_stmt_partial_solve_wit_17_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn [cm_stmt_expr cm_stmt_first cm_stmt_second]; first [assumption | reflexivity | lia]).
  all: dump_pre_spatial.
  all: subst retval retval_2.
  all: replace (pc_pre + cm_rvalue_code_count policy p fid_pre guard_ + cm_stmt_code_count policy p fid_pre yes_ + 2) with (pc_pre + cm_rvalue_code_count policy p fid_pre guard_ + 1 + cm_stmt_code_count policy p fid_pre yes_ + 1) by lia.
  all: assumption.
Qed.

Lemma proof_of_cmc_emit_if_stmt_partial_solve_wit_17_pure_split_goal_3 : cmc_emit_if_stmt_partial_solve_wit_17_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(cbn [cm_stmt_expr cm_stmt_first cm_stmt_second]; first [assumption | reflexivity | lia]).
  all: dump_pre_spatial.
  all: subst retval retval_2.
  all: replace (pc_pre + cm_rvalue_code_count policy p fid_pre guard_ + cm_stmt_code_count policy p fid_pre yes_ + 2) with (pc_pre + cm_rvalue_code_count policy p fid_pre guard_ + 1 + cm_stmt_code_count policy p fid_pre yes_ + 1) by lia.
  all: assumption.
Qed.

Lemma proof_of_cmc_emit_if_stmt_partial_solve_wit_17_pure_split_goal_4 : cmc_emit_if_stmt_partial_solve_wit_17_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(cbn [cm_stmt_expr cm_stmt_first cm_stmt_second]; first [assumption | reflexivity | lia]).
  all: dump_pre_spatial.
  all: subst retval retval_2.
  all: replace (pc_pre + cm_rvalue_code_count policy p fid_pre guard_ + cm_stmt_code_count policy p fid_pre yes_ + 2) with (pc_pre + cm_rvalue_code_count policy p fid_pre guard_ + 1 + cm_stmt_code_count policy p fid_pre yes_ + 1) by lia.
  all: assumption.
Qed.

Lemma proof_of_cmc_emit_if_stmt_partial_solve_wit_17_pure : cmc_emit_if_stmt_partial_solve_wit_17_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_if_stmt_partial_solve_wit_17_pure_split_goal_1.
  - Goal_apply proof_of_cmc_emit_if_stmt_partial_solve_wit_17_pure_split_goal_2.
  - Goal_apply proof_of_cmc_emit_if_stmt_partial_solve_wit_17_pure_split_goal_3.
  - Goal_apply proof_of_cmc_emit_if_stmt_partial_solve_wit_17_pure_split_goal_4.
Qed. 

Lemma proof_of_cmc_emit_if_stmt_which_implies_wit_1 : cmc_emit_if_stmt_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (cm_stmt_rep_node stmt s). unfold cm_stmt_node.
  Intros e a b. Exists b a e.
  split_pure_spatial; [sepcon_assoc_change; cancel | dump_pre_spatial; auto].
Qed. 

Lemma proof_of_cmc_emit_if_stmt_which_implies_wit_2_split_goal_spatial : cmc_emit_if_stmt_which_implies_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst s. unfold cm_stmt_payload. sepcon_assoc_change; cancel.
Qed.

Lemma proof_of_cmc_emit_if_stmt_which_implies_wit_2 : cmc_emit_if_stmt_which_implies_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_if_stmt_which_implies_wit_2_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_if_stmt_which_implies_wit_3_split_goal_1 : cmc_emit_if_stmt_which_implies_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  all: cbn [tvm_opcode_code]; lia.
Qed.

Lemma proof_of_cmc_emit_if_stmt_which_implies_wit_3_split_goal_2 : cmc_emit_if_stmt_which_implies_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  all: cbn [tvm_opcode_code]; lia.
Qed.

Lemma proof_of_cmc_emit_if_stmt_which_implies_wit_3_split_goal_3 : cmc_emit_if_stmt_which_implies_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  all: cbn [tvm_opcode_code]; lia.
Qed.

Lemma proof_of_cmc_emit_if_stmt_which_implies_wit_3_split_goal_4 : cmc_emit_if_stmt_which_implies_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
  all: cbn [tvm_opcode_code]; lia.
Qed.

Lemma proof_of_cmc_emit_if_stmt_which_implies_wit_3_split_goal_5 : cmc_emit_if_stmt_which_implies_wit_3_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia).
  all: rewrite cm_emit_stmt_length__stmt_capacity in PreH22.
  all: exact PreH22.
Qed.

Lemma proof_of_cmc_emit_if_stmt_which_implies_wit_3_split_goal_6 : cmc_emit_if_stmt_which_implies_wit_3_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia).
  all: subst s.
  all: subst f.
  all: rewrite !cm_emit_stmt_length__stmt_capacity in *.
  all: rewrite ?cm_expr_rvalue_length__stmt_capacity.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try assumption.
  all: try (apply cm_slot_type_encode__statement_normalization_safety; lia).
  all: try (unfold cm_binding_valid; tauto).
  all: unfold cm_i32_code_count in *.
  all: unfold cm_imax in *.
  all: unfold cm_expr_temps_for; cbn [Z.eqb].
  all: repeat match goal with H : context [Z.max ?a ?b] |- _ => destruct (Z.max_spec a b) as [[? Hmax]|[? Hmax]]; rewrite Hmax in *; clear Hmax end.
  all: try lia.
  all: repeat match goal with
  | H : cm_stmt_counts_representable ?pol ?pr ?fi ?a |- _ =>
    let Hn := fresh in pose proof (cm_stmt_count_nonnegative__stmt_capacity pol pr fi a) as Hn; clear H
  | H : cm_expr_counts_representable ?pol ?pr ?fi ?e |- _ =>
    let Hn := fresh in pose proof (cm_rvalue_count_nonnegative__stmt_capacity pol pr fi e) as Hn; clear H
  end.
  all: try lia.
  all: repeat match goal with H : context [cm_char_normalize_count ?ty] |- _ => destruct ty; cbn [cm_char_normalize_count] in * end.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_if_stmt_which_implies_wit_3_split_goal_7 : cmc_emit_if_stmt_which_implies_wit_3_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia).
  all: subst s.
  all: subst f.
  all: rewrite !cm_emit_stmt_length__stmt_capacity in *.
  all: rewrite ?cm_expr_rvalue_length__stmt_capacity.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try assumption.
  all: try (apply cm_slot_type_encode__statement_normalization_safety; lia).
  all: try (unfold cm_binding_valid; tauto).
  all: unfold cm_i32_code_count in *.
  all: unfold cm_imax in *.
  all: unfold cm_expr_temps_for; cbn [Z.eqb].
  all: repeat match goal with H : context [Z.max ?a ?b] |- _ => destruct (Z.max_spec a b) as [[? Hmax]|[? Hmax]]; rewrite Hmax in *; clear Hmax end.
  all: try lia.
  all: repeat match goal with
  | H : cm_stmt_counts_representable ?pol ?pr ?fi ?a |- _ =>
    let Hn := fresh in pose proof (cm_stmt_count_nonnegative__stmt_capacity pol pr fi a) as Hn; clear H
  | H : cm_expr_counts_representable ?pol ?pr ?fi ?e |- _ =>
    let Hn := fresh in pose proof (cm_rvalue_count_nonnegative__stmt_capacity pol pr fi e) as Hn; clear H
  end.
  all: try lia.
  all: repeat match goal with H : context [cm_char_normalize_count ?ty] |- _ => destruct ty; cbn [cm_char_normalize_count] in * end.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_if_stmt_which_implies_wit_3_split_goal_8 : cmc_emit_if_stmt_which_implies_wit_3_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia).
  all: subst s.
  all: subst f.
  all: rewrite !cm_emit_stmt_length__stmt_capacity in *.
  all: rewrite ?cm_expr_rvalue_length__stmt_capacity.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try assumption.
  all: try (apply cm_slot_type_encode__statement_normalization_safety; lia).
  all: try (unfold cm_binding_valid; tauto).
  all: unfold cm_i32_code_count in *.
  all: unfold cm_imax in *.
  all: unfold cm_expr_temps_for; cbn [Z.eqb].
  all: repeat match goal with H : context [Z.max ?a ?b] |- _ => destruct (Z.max_spec a b) as [[? Hmax]|[? Hmax]]; rewrite Hmax in *; clear Hmax end.
  all: try lia.
  all: repeat match goal with
  | H : cm_stmt_counts_representable ?pol ?pr ?fi ?a |- _ =>
    let Hn := fresh in pose proof (cm_stmt_count_nonnegative__stmt_capacity pol pr fi a) as Hn; clear H
  | H : cm_expr_counts_representable ?pol ?pr ?fi ?e |- _ =>
    let Hn := fresh in pose proof (cm_rvalue_count_nonnegative__stmt_capacity pol pr fi e) as Hn; clear H
  end.
  all: try lia.
  all: repeat match goal with H : context [cm_char_normalize_count ?ty] |- _ => destruct ty; cbn [cm_char_normalize_count] in * end.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_if_stmt_which_implies_wit_3_split_goal_9 : cmc_emit_if_stmt_which_implies_wit_3_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia).
  all: subst s.
  all: subst f.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: assumption.
Qed.

Lemma proof_of_cmc_emit_if_stmt_which_implies_wit_3_split_goal_10 : cmc_emit_if_stmt_which_implies_wit_3_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia).
  all: subst s.
  all: subst f.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: assumption.
Qed.

Lemma proof_of_cmc_emit_if_stmt_which_implies_wit_3_split_goal_11 : cmc_emit_if_stmt_which_implies_wit_3_split_goal_11.
Proof.
  LLM_pre_process ltac:(lia).
  all: subst s.
  all: subst f.
  all: rewrite !cm_emit_stmt_length__stmt_capacity in *.
  all: rewrite ?cm_expr_rvalue_length__stmt_capacity.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try assumption.
  all: try (apply cm_slot_type_encode__statement_normalization_safety; lia).
  all: try (unfold cm_binding_valid; tauto).
  all: unfold cm_i32_code_count in *.
  all: unfold cm_imax in *.
  all: unfold cm_expr_temps_for; cbn [Z.eqb].
  all: repeat match goal with H : context [Z.max ?a ?b] |- _ => destruct (Z.max_spec a b) as [[? Hmax]|[? Hmax]]; rewrite Hmax in *; clear Hmax end.
  all: try lia.
  all: repeat match goal with
  | H : cm_stmt_counts_representable ?pol ?pr ?fi ?a |- _ =>
    let Hn := fresh in pose proof (cm_stmt_count_nonnegative__stmt_capacity pol pr fi a) as Hn; clear H
  | H : cm_expr_counts_representable ?pol ?pr ?fi ?e |- _ =>
    let Hn := fresh in pose proof (cm_rvalue_count_nonnegative__stmt_capacity pol pr fi e) as Hn; clear H
  end.
  all: try lia.
  all: repeat match goal with H : context [cm_char_normalize_count ?ty] |- _ => destruct ty; cbn [cm_char_normalize_count] in * end.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_if_stmt_which_implies_wit_3_split_goal_12 : cmc_emit_if_stmt_which_implies_wit_3_split_goal_12.
Proof.
  LLM_pre_process ltac:(lia).
  all: subst s.
  all: subst f.
  all: rewrite !cm_emit_stmt_length__stmt_capacity in *.
  all: rewrite ?cm_expr_rvalue_length__stmt_capacity.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try assumption.
  all: try (apply cm_slot_type_encode__statement_normalization_safety; lia).
  all: try (unfold cm_binding_valid; tauto).
  all: unfold cm_i32_code_count in *.
  all: unfold cm_imax in *.
  all: unfold cm_expr_temps_for; cbn [Z.eqb].
  all: repeat match goal with H : context [Z.max ?a ?b] |- _ => destruct (Z.max_spec a b) as [[? Hmax]|[? Hmax]]; rewrite Hmax in *; clear Hmax end.
  all: try lia.
  all: repeat match goal with
  | H : cm_stmt_counts_representable ?pol ?pr ?fi ?a |- _ =>
    let Hn := fresh in pose proof (cm_stmt_count_nonnegative__stmt_capacity pol pr fi a) as Hn; clear H
  | H : cm_expr_counts_representable ?pol ?pr ?fi ?e |- _ =>
    let Hn := fresh in pose proof (cm_rvalue_count_nonnegative__stmt_capacity pol pr fi e) as Hn; clear H
  end.
  all: try lia.
  all: repeat match goal with H : context [cm_char_normalize_count ?ty] |- _ => destruct ty; cbn [cm_char_normalize_count] in * end.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_if_stmt_which_implies_wit_3_split_goal_13 : cmc_emit_if_stmt_which_implies_wit_3_split_goal_13.
Proof.
  LLM_pre_process ltac:(lia).
  all: subst s.
  all: subst f.
  all: rewrite !cm_emit_stmt_length__stmt_capacity in *.
  all: rewrite ?cm_expr_rvalue_length__stmt_capacity.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try assumption.
  all: try (apply cm_slot_type_encode__statement_normalization_safety; lia).
  all: try (unfold cm_binding_valid; tauto).
  all: unfold cm_i32_code_count in *.
  all: unfold cm_imax in *.
  all: unfold cm_expr_temps_for; cbn [Z.eqb].
  all: repeat match goal with H : context [Z.max ?a ?b] |- _ => destruct (Z.max_spec a b) as [[? Hmax]|[? Hmax]]; rewrite Hmax in *; clear Hmax end.
  all: try lia.
  all: repeat match goal with
  | H : cm_stmt_counts_representable ?pol ?pr ?fi ?a |- _ =>
    let Hn := fresh in pose proof (cm_stmt_count_nonnegative__stmt_capacity pol pr fi a) as Hn; clear H
  | H : cm_expr_counts_representable ?pol ?pr ?fi ?e |- _ =>
    let Hn := fresh in pose proof (cm_rvalue_count_nonnegative__stmt_capacity pol pr fi e) as Hn; clear H
  end.
  all: try lia.
  all: repeat match goal with H : context [cm_char_normalize_count ?ty] |- _ => destruct ty; cbn [cm_char_normalize_count] in * end.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_if_stmt_which_implies_wit_3_split_goal_14 : cmc_emit_if_stmt_which_implies_wit_3_split_goal_14.
Proof.
  LLM_pre_process ltac:(lia).
  all: subst s.
  all: subst f.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: assumption.
Qed.

Lemma proof_of_cmc_emit_if_stmt_which_implies_wit_3_split_goal_15 : cmc_emit_if_stmt_which_implies_wit_3_split_goal_15.
Proof.
  LLM_pre_process ltac:(lia).
  all: subst s.
  all: subst f.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: assumption.
Qed.

Lemma proof_of_cmc_emit_if_stmt_which_implies_wit_3_split_goal_16 : cmc_emit_if_stmt_which_implies_wit_3_split_goal_16.
Proof.
  LLM_pre_process ltac:(lia).
  all: subst s.
  all: subst f.
  all: rewrite !cm_emit_stmt_length__stmt_capacity in *.
  all: rewrite ?cm_expr_rvalue_length__stmt_capacity.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try assumption.
  all: try (apply cm_slot_type_encode__statement_normalization_safety; lia).
  all: try (unfold cm_binding_valid; tauto).
  all: unfold cm_i32_code_count in *.
  all: unfold cm_imax in *.
  all: unfold cm_expr_temps_for; cbn [Z.eqb].
  all: repeat match goal with H : context [Z.max ?a ?b] |- _ => destruct (Z.max_spec a b) as [[? Hmax]|[? Hmax]]; rewrite Hmax in *; clear Hmax end.
  all: try lia.
  all: repeat match goal with
  | H : cm_stmt_counts_representable ?pol ?pr ?fi ?a |- _ =>
    let Hn := fresh in pose proof (cm_stmt_count_nonnegative__stmt_capacity pol pr fi a) as Hn; clear H
  | H : cm_expr_counts_representable ?pol ?pr ?fi ?e |- _ =>
    let Hn := fresh in pose proof (cm_rvalue_count_nonnegative__stmt_capacity pol pr fi e) as Hn; clear H
  end.
  all: try lia.
  all: repeat match goal with H : context [cm_char_normalize_count ?ty] |- _ => destruct ty; cbn [cm_char_normalize_count] in * end.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_if_stmt_which_implies_wit_3_split_goal_17 : cmc_emit_if_stmt_which_implies_wit_3_split_goal_17.
Proof.
  LLM_pre_process ltac:(lia).
  all: subst s.
  all: subst f.
  all: rewrite !cm_emit_stmt_length__stmt_capacity in *.
  all: rewrite ?cm_expr_rvalue_length__stmt_capacity.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try assumption.
  all: try (apply cm_slot_type_encode__statement_normalization_safety; lia).
  all: try (unfold cm_binding_valid; tauto).
  all: unfold cm_i32_code_count in *.
  all: unfold cm_imax in *.
  all: unfold cm_expr_temps_for; cbn [Z.eqb].
  all: repeat match goal with H : context [Z.max ?a ?b] |- _ => destruct (Z.max_spec a b) as [[? Hmax]|[? Hmax]]; rewrite Hmax in *; clear Hmax end.
  all: try lia.
  all: repeat match goal with
  | H : cm_stmt_counts_representable ?pol ?pr ?fi ?a |- _ =>
    let Hn := fresh in pose proof (cm_stmt_count_nonnegative__stmt_capacity pol pr fi a) as Hn; clear H
  | H : cm_expr_counts_representable ?pol ?pr ?fi ?e |- _ =>
    let Hn := fresh in pose proof (cm_rvalue_count_nonnegative__stmt_capacity pol pr fi e) as Hn; clear H
  end.
  all: try lia.
  all: repeat match goal with H : context [cm_char_normalize_count ?ty] |- _ => destruct ty; cbn [cm_char_normalize_count] in * end.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_if_stmt_which_implies_wit_3_split_goal_18 : cmc_emit_if_stmt_which_implies_wit_3_split_goal_18.
Proof.
  LLM_pre_process ltac:(lia).
  all: subst s.
  all: subst f.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: assumption.
Qed.

Lemma proof_of_cmc_emit_if_stmt_which_implies_wit_3_split_goal_19 : cmc_emit_if_stmt_which_implies_wit_3_split_goal_19.
Proof.
  LLM_pre_process ltac:(lia).
  all: subst s.
  all: subst f.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: assumption.
Qed.

Lemma proof_of_cmc_emit_if_stmt_which_implies_wit_3 : cmc_emit_if_stmt_which_implies_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_if_stmt_which_implies_wit_3_split_goal_1.
  - Goal_apply proof_of_cmc_emit_if_stmt_which_implies_wit_3_split_goal_2.
  - Goal_apply proof_of_cmc_emit_if_stmt_which_implies_wit_3_split_goal_3.
  - Goal_apply proof_of_cmc_emit_if_stmt_which_implies_wit_3_split_goal_4.
  - Goal_apply proof_of_cmc_emit_if_stmt_which_implies_wit_3_split_goal_5.
  - Goal_apply proof_of_cmc_emit_if_stmt_which_implies_wit_3_split_goal_6.
  - Goal_apply proof_of_cmc_emit_if_stmt_which_implies_wit_3_split_goal_7.
  - Goal_apply proof_of_cmc_emit_if_stmt_which_implies_wit_3_split_goal_8.
  - Goal_apply proof_of_cmc_emit_if_stmt_which_implies_wit_3_split_goal_9.
  - Goal_apply proof_of_cmc_emit_if_stmt_which_implies_wit_3_split_goal_10.
  - Goal_apply proof_of_cmc_emit_if_stmt_which_implies_wit_3_split_goal_11.
  - Goal_apply proof_of_cmc_emit_if_stmt_which_implies_wit_3_split_goal_12.
  - Goal_apply proof_of_cmc_emit_if_stmt_which_implies_wit_3_split_goal_13.
  - Goal_apply proof_of_cmc_emit_if_stmt_which_implies_wit_3_split_goal_14.
  - Goal_apply proof_of_cmc_emit_if_stmt_which_implies_wit_3_split_goal_15.
  - Goal_apply proof_of_cmc_emit_if_stmt_which_implies_wit_3_split_goal_16.
  - Goal_apply proof_of_cmc_emit_if_stmt_which_implies_wit_3_split_goal_17.
  - Goal_apply proof_of_cmc_emit_if_stmt_which_implies_wit_3_split_goal_18.
  - Goal_apply proof_of_cmc_emit_if_stmt_which_implies_wit_3_split_goal_19.
Qed. 

Lemma proof_of_cmc_emit_if_stmt_which_implies_wit_7_split_goal_spatial : cmc_emit_if_stmt_which_implies_wit_7_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst.
  cbn [cm_emit_stmt cm_stmt_code_count].
  replace (pc + cm_rvalue_code_count policy p fid guard_ + 1 + cm_stmt_code_count policy p fid yes_ + 1) with (pc + cm_rvalue_code_count policy p fid guard_ + cm_stmt_code_count policy p fid yes_ + 2) by lia.
  replace (pc + (cm_rvalue_code_count policy p fid guard_ + 1 + cm_stmt_code_count policy p fid yes_ + 1 + cm_stmt_code_count policy p fid no_)) with (pc + cm_rvalue_code_count policy p fid guard_ + cm_stmt_code_count policy p fid yes_ + cm_stmt_code_count policy p fid no_ + 2) by lia.
  repeat rewrite <- app_assoc.
  cbn [app].
  cancel.
Qed.

Lemma proof_of_cmc_emit_if_stmt_which_implies_wit_7 : cmc_emit_if_stmt_which_implies_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_if_stmt_which_implies_wit_7_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_if_stmt_which_implies_wit_8_split_goal_spatial : cmc_emit_if_stmt_which_implies_wit_8_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cmc_emit_if_stmt_which_implies_wit_8 : cmc_emit_if_stmt_which_implies_wit_8.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_if_stmt_which_implies_wit_8_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_if_stmt_which_implies_wit_9_split_goal_spatial : cmc_emit_if_stmt_which_implies_wit_9_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cmc_emit_if_stmt_which_implies_wit_9 : cmc_emit_if_stmt_which_implies_wit_9.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_if_stmt_which_implies_wit_9_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_if_stmt_which_implies_wit_10_split_goal_spatial : cmc_emit_if_stmt_which_implies_wit_10_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst.
  cbn [cm_emit_stmt cm_stmt_code_count].
  replace (pc + cm_rvalue_code_count policy p fid guard_ + 1 + cm_stmt_code_count policy p fid yes_ + 1) with (pc + cm_rvalue_code_count policy p fid guard_ + cm_stmt_code_count policy p fid yes_ + 2) by lia.
  replace (pc + (cm_rvalue_code_count policy p fid guard_ + 1 + cm_stmt_code_count policy p fid yes_ + 1 + cm_stmt_code_count policy p fid no_)) with (pc + cm_rvalue_code_count policy p fid guard_ + cm_stmt_code_count policy p fid yes_ + cm_stmt_code_count policy p fid no_ + 2) by lia.
  repeat rewrite <- app_assoc.
  cbn [app].
  cancel.
Qed.

Lemma proof_of_cmc_emit_if_stmt_which_implies_wit_10 : cmc_emit_if_stmt_which_implies_wit_10.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_if_stmt_which_implies_wit_10_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_if_stmt_which_implies_wit_11_split_goal_spatial : cmc_emit_if_stmt_which_implies_wit_11_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (cm_stmt_rep_node stmt s). unfold cm_stmt_node.
  Exists xe xa xb. subst s. unfold cm_stmt_payload.
  split_pure_spatial; [sepcon_assoc_change; cancel | dump_pre_spatial; auto].
Qed.

Lemma proof_of_cmc_emit_if_stmt_which_implies_wit_11 : cmc_emit_if_stmt_which_implies_wit_11.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_if_stmt_which_implies_wit_11_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_stmt_safety_wit_11_split_goal_1 : cmc_emit_stmt_safety_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  all: dump_pre_spatial.
  all: unfold cm_i32_code_count in *; lia.
Qed.

Lemma proof_of_cmc_emit_stmt_safety_wit_11_split_goal_2 : cmc_emit_stmt_safety_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  all: dump_pre_spatial.
  all: unfold cm_i32_code_count in *; lia.
Qed.

Lemma proof_of_cmc_emit_stmt_safety_wit_11 : cmc_emit_stmt_safety_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_safety_wit_11_split_goal_1.
  - Goal_apply proof_of_cmc_emit_stmt_safety_wit_11_split_goal_2.
Qed. 

Lemma proof_of_cmc_emit_stmt_safety_wit_15_split_goal_1 : cmc_emit_stmt_safety_wit_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  all: dump_pre_spatial.
  all: unfold cm_i32_code_count in *.
  all: cbn [cm_stmt_code_count] in *.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_stmt_safety_wit_15_split_goal_2 : cmc_emit_stmt_safety_wit_15_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  all: dump_pre_spatial.
  all: unfold cm_i32_code_count in *.
  all: cbn [cm_stmt_code_count] in *.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_stmt_safety_wit_15 : cmc_emit_stmt_safety_wit_15.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_safety_wit_15_split_goal_1.
  - Goal_apply proof_of_cmc_emit_stmt_safety_wit_15_split_goal_2.
Qed. 

Lemma proof_of_cmc_emit_stmt_safety_wit_16_split_goal_1 : cmc_emit_stmt_safety_wit_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  all: dump_pre_spatial.
  all: unfold cm_i32_code_count in *.
  all: cbn [cm_stmt_code_count] in *.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_stmt_safety_wit_16_split_goal_2 : cmc_emit_stmt_safety_wit_16_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  all: dump_pre_spatial.
  all: unfold cm_i32_code_count in *.
  all: cbn [cm_stmt_code_count] in *.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_stmt_safety_wit_16 : cmc_emit_stmt_safety_wit_16.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_safety_wit_16_split_goal_1.
  - Goal_apply proof_of_cmc_emit_stmt_safety_wit_16_split_goal_2.
Qed. 

Lemma proof_of_cmc_emit_stmt_safety_wit_18_split_goal_1 : cmc_emit_stmt_safety_wit_18_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  all: dump_pre_spatial.
  all: unfold cm_i32_code_count in *.
  all: cbn [cm_stmt_code_count] in *.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_stmt_safety_wit_18_split_goal_2 : cmc_emit_stmt_safety_wit_18_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  all: dump_pre_spatial.
  all: unfold cm_i32_code_count in *.
  all: cbn [cm_stmt_code_count] in *.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_stmt_safety_wit_18 : cmc_emit_stmt_safety_wit_18.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_safety_wit_18_split_goal_1.
  - Goal_apply proof_of_cmc_emit_stmt_safety_wit_18_split_goal_2.
Qed. 

Lemma proof_of_cmc_emit_stmt_safety_wit_19_split_goal_1 : cmc_emit_stmt_safety_wit_19_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  all: dump_pre_spatial.
  all: unfold cm_i32_code_count in *.
  all: cbn [cm_stmt_code_count] in *.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_stmt_safety_wit_19_split_goal_2 : cmc_emit_stmt_safety_wit_19_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  all: dump_pre_spatial.
  all: unfold cm_i32_code_count in *.
  all: cbn [cm_stmt_code_count] in *.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_stmt_safety_wit_19 : cmc_emit_stmt_safety_wit_19.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_safety_wit_19_split_goal_1.
  - Goal_apply proof_of_cmc_emit_stmt_safety_wit_19_split_goal_2.
Qed. 

Lemma proof_of_cmc_emit_stmt_safety_wit_20_split_goal_1 : cmc_emit_stmt_safety_wit_20_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  all: dump_pre_spatial.
  all: unfold cm_i32_code_count in *.
  all: cbn [cm_stmt_code_count] in *.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_stmt_safety_wit_20_split_goal_2 : cmc_emit_stmt_safety_wit_20_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  all: dump_pre_spatial.
  all: unfold cm_i32_code_count in *.
  all: cbn [cm_stmt_code_count] in *.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_stmt_safety_wit_20 : cmc_emit_stmt_safety_wit_20.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_safety_wit_20_split_goal_1.
  - Goal_apply proof_of_cmc_emit_stmt_safety_wit_20_split_goal_2.
Qed. 

Lemma proof_of_cmc_emit_stmt_safety_wit_21_split_goal_1 : cmc_emit_stmt_safety_wit_21_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  all: dump_pre_spatial.
  all: unfold cm_i32_code_count in *.
  all: cbn [cm_stmt_code_count] in *.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_stmt_safety_wit_21_split_goal_2 : cmc_emit_stmt_safety_wit_21_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  all: dump_pre_spatial.
  all: unfold cm_i32_code_count in *.
  all: cbn [cm_stmt_code_count] in *.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_stmt_safety_wit_21 : cmc_emit_stmt_safety_wit_21.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_safety_wit_21_split_goal_1.
  - Goal_apply proof_of_cmc_emit_stmt_safety_wit_21_split_goal_2.
Qed. 

Lemma proof_of_cmc_emit_stmt_return_wit_2_split_goal_1 : cmc_emit_stmt_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto);
    cbn [cm_stmt_expr cm_rep_stmt_slot];
    rewrite <- PreH1; assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_return_wit_2_split_goal_2 : cmc_emit_stmt_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto);
    cbn [cm_stmt_expr cm_rep_stmt_slot];
    rewrite <- PreH1; assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_return_wit_2_split_goal_3 : cmc_emit_stmt_return_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto);
    cbn [cm_stmt_expr cm_rep_stmt_slot];
    rewrite <- PreH1; assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_return_wit_2_split_goal_4 : cmc_emit_stmt_return_wit_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto);
    cbn [cm_stmt_expr cm_rep_stmt_slot];
    rewrite <- PreH1; assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_return_wit_2 : cmc_emit_stmt_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_return_wit_2_split_goal_1.
  - Goal_apply proof_of_cmc_emit_stmt_return_wit_2_split_goal_2.
  - Goal_apply proof_of_cmc_emit_stmt_return_wit_2_split_goal_3.
  - Goal_apply proof_of_cmc_emit_stmt_return_wit_2_split_goal_4.
Qed. 

Lemma proof_of_cmc_emit_stmt_return_wit_3_split_goal_1 : cmc_emit_stmt_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto);
    cbn [cm_stmt_expr cm_rep_stmt_slot];
    rewrite <- PreH1; assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_return_wit_3_split_goal_2 : cmc_emit_stmt_return_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto);
    cbn [cm_stmt_expr cm_rep_stmt_slot];
    rewrite <- PreH1; assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_return_wit_3_split_goal_3 : cmc_emit_stmt_return_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto);
    cbn [cm_stmt_expr cm_rep_stmt_slot];
    rewrite <- PreH1; assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_return_wit_3_split_goal_4 : cmc_emit_stmt_return_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto);
    cbn [cm_stmt_expr cm_rep_stmt_slot];
    rewrite <- PreH1; assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_return_wit_3 : cmc_emit_stmt_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_return_wit_3_split_goal_1.
  - Goal_apply proof_of_cmc_emit_stmt_return_wit_3_split_goal_2.
  - Goal_apply proof_of_cmc_emit_stmt_return_wit_3_split_goal_3.
  - Goal_apply proof_of_cmc_emit_stmt_return_wit_3_split_goal_4.
Qed. 

Lemma proof_of_cmc_emit_stmt_return_wit_4_split_goal_1 : cmc_emit_stmt_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto);
    cbn [cm_stmt_expr cm_rep_stmt_slot];
    rewrite <- PreH1; assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_return_wit_4_split_goal_2 : cmc_emit_stmt_return_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto);
    cbn [cm_stmt_expr cm_rep_stmt_slot];
    rewrite <- PreH1; assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_return_wit_4_split_goal_3 : cmc_emit_stmt_return_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto);
    cbn [cm_stmt_expr cm_rep_stmt_slot];
    rewrite <- PreH1; assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_return_wit_4_split_goal_4 : cmc_emit_stmt_return_wit_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto);
    cbn [cm_stmt_expr cm_rep_stmt_slot];
    rewrite <- PreH1; assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_return_wit_4 : cmc_emit_stmt_return_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_return_wit_4_split_goal_1.
  - Goal_apply proof_of_cmc_emit_stmt_return_wit_4_split_goal_2.
  - Goal_apply proof_of_cmc_emit_stmt_return_wit_4_split_goal_3.
  - Goal_apply proof_of_cmc_emit_stmt_return_wit_4_split_goal_4.
Qed. 

Lemma proof_of_cmc_emit_stmt_return_wit_5_split_goal_1 : cmc_emit_stmt_return_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto);
    cbn [cm_stmt_first cm_stmt_second cm_stmt_expr];
    rewrite <- PreH1; assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_return_wit_5_split_goal_2 : cmc_emit_stmt_return_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto);
    cbn [cm_stmt_first cm_stmt_second cm_stmt_expr];
    rewrite <- PreH1; assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_return_wit_5_split_goal_3 : cmc_emit_stmt_return_wit_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto);
    cbn [cm_stmt_first cm_stmt_second cm_stmt_expr];
    rewrite <- PreH1; assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_return_wit_5_split_goal_4 : cmc_emit_stmt_return_wit_5_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto);
    cbn [cm_stmt_first cm_stmt_second cm_stmt_expr];
    rewrite <- PreH1; assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_return_wit_5 : cmc_emit_stmt_return_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_return_wit_5_split_goal_1.
  - Goal_apply proof_of_cmc_emit_stmt_return_wit_5_split_goal_2.
  - Goal_apply proof_of_cmc_emit_stmt_return_wit_5_split_goal_3.
  - Goal_apply proof_of_cmc_emit_stmt_return_wit_5_split_goal_4.
Qed. 

Lemma proof_of_cmc_emit_stmt_return_wit_6_split_goal_1 : cmc_emit_stmt_return_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto);
    cbn [cm_stmt_first cm_stmt_second cm_stmt_expr];
    rewrite <- PreH1; assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_return_wit_6_split_goal_2 : cmc_emit_stmt_return_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto);
    cbn [cm_stmt_first cm_stmt_second cm_stmt_expr];
    rewrite <- PreH1; assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_return_wit_6_split_goal_3 : cmc_emit_stmt_return_wit_6_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto);
    cbn [cm_stmt_first cm_stmt_second cm_stmt_expr];
    rewrite <- PreH1; assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_return_wit_6_split_goal_4 : cmc_emit_stmt_return_wit_6_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto);
    cbn [cm_stmt_first cm_stmt_second cm_stmt_expr];
    rewrite <- PreH1; assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_return_wit_6 : cmc_emit_stmt_return_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_return_wit_6_split_goal_1.
  - Goal_apply proof_of_cmc_emit_stmt_return_wit_6_split_goal_2.
  - Goal_apply proof_of_cmc_emit_stmt_return_wit_6_split_goal_3.
  - Goal_apply proof_of_cmc_emit_stmt_return_wit_6_split_goal_4.
Qed. 

Lemma proof_of_cmc_emit_stmt_return_wit_7_split_goal_1 : cmc_emit_stmt_return_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto);
    cbn [cm_stmt_first cm_stmt_second cm_stmt_expr];
    rewrite <- PreH1; assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_return_wit_7_split_goal_2 : cmc_emit_stmt_return_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto);
    cbn [cm_stmt_first cm_stmt_second cm_stmt_expr];
    rewrite <- PreH1; assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_return_wit_7_split_goal_3 : cmc_emit_stmt_return_wit_7_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto);
    cbn [cm_stmt_first cm_stmt_second cm_stmt_expr];
    rewrite <- PreH1; assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_return_wit_7_split_goal_4 : cmc_emit_stmt_return_wit_7_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto);
    cbn [cm_stmt_first cm_stmt_second cm_stmt_expr];
    rewrite <- PreH1; assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_return_wit_7 : cmc_emit_stmt_return_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_return_wit_7_split_goal_1.
  - Goal_apply proof_of_cmc_emit_stmt_return_wit_7_split_goal_2.
  - Goal_apply proof_of_cmc_emit_stmt_return_wit_7_split_goal_3.
  - Goal_apply proof_of_cmc_emit_stmt_return_wit_7_split_goal_4.
Qed. 

Lemma proof_of_cmc_emit_stmt_return_wit_8_split_goal_1 : cmc_emit_stmt_return_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto);
    cbn [cm_stmt_first cm_stmt_second cm_stmt_expr];
    rewrite <- PreH1; assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_return_wit_8_split_goal_2 : cmc_emit_stmt_return_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto);
    cbn [cm_stmt_first cm_stmt_second cm_stmt_expr];
    rewrite <- PreH1; assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_return_wit_8_split_goal_3 : cmc_emit_stmt_return_wit_8_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto);
    cbn [cm_stmt_first cm_stmt_second cm_stmt_expr];
    rewrite <- PreH1; assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_return_wit_8_split_goal_4 : cmc_emit_stmt_return_wit_8_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto);
    cbn [cm_stmt_first cm_stmt_second cm_stmt_expr];
    rewrite <- PreH1; assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_return_wit_8 : cmc_emit_stmt_return_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_return_wit_8_split_goal_1.
  - Goal_apply proof_of_cmc_emit_stmt_return_wit_8_split_goal_2.
  - Goal_apply proof_of_cmc_emit_stmt_return_wit_8_split_goal_3.
  - Goal_apply proof_of_cmc_emit_stmt_return_wit_8_split_goal_4.
Qed. 

Lemma proof_of_cmc_emit_stmt_return_wit_11_split_goal_1 : cmc_emit_stmt_return_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto);
    cbn [cm_stmt_expr cm_rep_stmt_slot];
    rewrite <- PreH1; assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_return_wit_11_split_goal_2 : cmc_emit_stmt_return_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto);
    cbn [cm_stmt_expr cm_rep_stmt_slot];
    rewrite <- PreH1; assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_return_wit_11_split_goal_3 : cmc_emit_stmt_return_wit_11_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto);
    cbn [cm_stmt_expr cm_rep_stmt_slot];
    rewrite <- PreH1; assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_return_wit_11_split_goal_4 : cmc_emit_stmt_return_wit_11_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto);
    cbn [cm_stmt_expr cm_rep_stmt_slot];
    rewrite <- PreH1; assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_return_wit_11 : cmc_emit_stmt_return_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_return_wit_11_split_goal_1.
  - Goal_apply proof_of_cmc_emit_stmt_return_wit_11_split_goal_2.
  - Goal_apply proof_of_cmc_emit_stmt_return_wit_11_split_goal_3.
  - Goal_apply proof_of_cmc_emit_stmt_return_wit_11_split_goal_4.
Qed. 

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_8_pure_split_goal_1 : cmc_emit_stmt_partial_solve_wit_8_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [cm_stmt_expr cm_rep_stmt_slot] in *; congruence).
Qed.

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_8_pure : cmc_emit_stmt_partial_solve_wit_8_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_partial_solve_wit_8_pure_split_goal_1.
Qed. 

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_10_pure_split_goal_1 : cmc_emit_stmt_partial_solve_wit_10_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [cm_stmt_expr cm_rep_stmt_slot] in *; congruence).
Qed.

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_10_pure : cmc_emit_stmt_partial_solve_wit_10_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_partial_solve_wit_10_pure_split_goal_1.
Qed. 

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_12_pure_split_goal_1 : cmc_emit_stmt_partial_solve_wit_12_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [cm_stmt_expr cm_rep_stmt_slot] in *; congruence).
Qed.

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_12_pure : cmc_emit_stmt_partial_solve_wit_12_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_partial_solve_wit_12_pure_split_goal_1.
Qed. 

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_13_pure_split_goal_1 : cmc_emit_stmt_partial_solve_wit_13_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [cm_stmt_expr cm_rep_stmt_slot] in *; congruence).
Qed.

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_13_pure : cmc_emit_stmt_partial_solve_wit_13_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_partial_solve_wit_13_pure_split_goal_1.
Qed. 

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_16_pure_split_goal_1 : cmc_emit_stmt_partial_solve_wit_16_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [cm_stmt_expr cm_rep_stmt_slot] in *; congruence).
Qed.

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_16_pure : cmc_emit_stmt_partial_solve_wit_16_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_partial_solve_wit_16_pure_split_goal_1.
Qed. 

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_23_pure_split_goal_1 : cmc_emit_stmt_partial_solve_wit_23_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [cm_rep_stmt_slot cm_stmt_expr] in *; congruence).
Qed.

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_23_pure : cmc_emit_stmt_partial_solve_wit_23_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_partial_solve_wit_23_pure_split_goal_1.
Qed. 

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_25_pure_split_goal_1 : cmc_emit_stmt_partial_solve_wit_25_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [cm_rep_stmt_slot cm_stmt_expr] in *; congruence).
Qed.

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_25_pure : cmc_emit_stmt_partial_solve_wit_25_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_partial_solve_wit_25_pure_split_goal_1.
Qed. 

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_27_pure_split_goal_1 : cmc_emit_stmt_partial_solve_wit_27_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [cm_rep_stmt_slot cm_stmt_expr] in *; congruence).
Qed.

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_27_pure : cmc_emit_stmt_partial_solve_wit_27_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_partial_solve_wit_27_pure_split_goal_1.
Qed. 

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_28_pure_split_goal_1 : cmc_emit_stmt_partial_solve_wit_28_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [cm_rep_stmt_slot cm_stmt_expr] in *; congruence).
Qed.

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_28_pure : cmc_emit_stmt_partial_solve_wit_28_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_partial_solve_wit_28_pure_split_goal_1.
Qed. 

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_29_pure_split_goal_1 : cmc_emit_stmt_partial_solve_wit_29_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [cm_rep_stmt_slot cm_stmt_expr] in *; congruence).
Qed.

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_29_pure : cmc_emit_stmt_partial_solve_wit_29_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_partial_solve_wit_29_pure_split_goal_1.
Qed. 

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_34_pure_split_goal_1 : cmc_emit_stmt_partial_solve_wit_34_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  all: dump_pre_spatial.
  all: cbn [cm_stmt_first cm_stmt_second]; first [assumption | reflexivity].
Qed.

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_34_pure : cmc_emit_stmt_partial_solve_wit_34_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_partial_solve_wit_34_pure_split_goal_1.
Qed. 

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_35_pure_split_goal_1 : cmc_emit_stmt_partial_solve_wit_35_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  all: dump_pre_spatial.
  all: cbn [cm_stmt_first cm_stmt_second]; first [assumption | reflexivity].
Qed.

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_35_pure_split_goal_2 : cmc_emit_stmt_partial_solve_wit_35_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  all: dump_pre_spatial.
  all: cbn [cm_stmt_first cm_stmt_second]; first [assumption | reflexivity].
Qed.

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_35_pure : cmc_emit_stmt_partial_solve_wit_35_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_partial_solve_wit_35_pure_split_goal_1.
  - Goal_apply proof_of_cmc_emit_stmt_partial_solve_wit_35_pure_split_goal_2.
Qed. 

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_37_pure_split_goal_1 : cmc_emit_stmt_partial_solve_wit_37_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  all: dump_pre_spatial.
  all: cbn [cm_stmt_first cm_stmt_second]; first [assumption | reflexivity].
Qed.

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_37_pure : cmc_emit_stmt_partial_solve_wit_37_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_partial_solve_wit_37_pure_split_goal_1.
Qed. 

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_38_pure_split_goal_1 : cmc_emit_stmt_partial_solve_wit_38_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  all: dump_pre_spatial.
  all: cbn [cm_stmt_first cm_stmt_second]; first [assumption | reflexivity].
Qed.

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_38_pure : cmc_emit_stmt_partial_solve_wit_38_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_partial_solve_wit_38_pure_split_goal_1.
Qed. 

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_41_pure_split_goal_1 : cmc_emit_stmt_partial_solve_wit_41_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(first [assumption | reflexivity | lia]).
Qed.

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_41_pure : cmc_emit_stmt_partial_solve_wit_41_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_partial_solve_wit_41_pure_split_goal_1.
Qed. 

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_43_pure_split_goal_1 : cmc_emit_stmt_partial_solve_wit_43_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(first [assumption | reflexivity | lia]).
Qed.

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_43_pure : cmc_emit_stmt_partial_solve_wit_43_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_partial_solve_wit_43_pure_split_goal_1.
Qed. 

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_44_pure_split_goal_1 : cmc_emit_stmt_partial_solve_wit_44_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(first [assumption | reflexivity | lia]).
Qed.

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_44_pure : cmc_emit_stmt_partial_solve_wit_44_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_partial_solve_wit_44_pure_split_goal_1.
Qed. 

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_54_pure_split_goal_1 : cmc_emit_stmt_partial_solve_wit_54_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || assumption || reflexivity).
  all: try dump_pre_spatial.
  all: cbn [cm_stmt_expr cm_stmt_first] in *.
  all: assumption || reflexivity.
Qed.

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_54_pure : cmc_emit_stmt_partial_solve_wit_54_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_partial_solve_wit_54_pure_split_goal_1.
Qed. 

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_55_pure_split_goal_1 : cmc_emit_stmt_partial_solve_wit_55_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || assumption || reflexivity).
  all: try dump_pre_spatial.
  all: cbn [cm_stmt_expr cm_stmt_first] in *.
  all: assumption || reflexivity.
Qed.

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_55_pure_split_goal_2 : cmc_emit_stmt_partial_solve_wit_55_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || assumption || reflexivity).
  all: try dump_pre_spatial.
  all: cbn [cm_stmt_expr cm_stmt_first] in *.
  all: assumption || reflexivity.
Qed.

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_55_pure : cmc_emit_stmt_partial_solve_wit_55_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_partial_solve_wit_55_pure_split_goal_1.
  - Goal_apply proof_of_cmc_emit_stmt_partial_solve_wit_55_pure_split_goal_2.
Qed. 

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_56_pure_split_goal_1 : cmc_emit_stmt_partial_solve_wit_56_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || assumption || reflexivity).
  all: try dump_pre_spatial.
  all: cbn [cm_stmt_expr cm_stmt_first] in *.
  all: assumption || reflexivity.
Qed.

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_56_pure : cmc_emit_stmt_partial_solve_wit_56_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_partial_solve_wit_56_pure_split_goal_1.
Qed. 

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_58_pure_split_goal_1 : cmc_emit_stmt_partial_solve_wit_58_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || assumption || reflexivity).
  all: try dump_pre_spatial.
  all: cbn [cm_stmt_expr cm_stmt_first] in *.
  all: assumption || reflexivity.
Qed.

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_58_pure_split_goal_2 : cmc_emit_stmt_partial_solve_wit_58_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || assumption || reflexivity).
  all: try dump_pre_spatial.
  all: cbn [cm_stmt_expr cm_stmt_first] in *.
  all: assumption || reflexivity.
Qed.

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_58_pure_split_goal_3 : cmc_emit_stmt_partial_solve_wit_58_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || assumption || reflexivity).
  all: try dump_pre_spatial.
  all: cbn [cm_stmt_expr cm_stmt_first] in *.
  all: try subst retval retval_2.
  all: cbn [cm_stmt_code_count] in *.
  all: unfold cm_i32_code_count in *.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_58_pure_split_goal_4 : cmc_emit_stmt_partial_solve_wit_58_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || assumption || reflexivity).
  all: try dump_pre_spatial.
  all: cbn [cm_stmt_expr cm_stmt_first] in *.
  all: try subst retval retval_2.
  all: replace (pc_pre + cm_rvalue_code_count policy p fid_pre (cm_stmt_expr s) + cm_stmt_code_count policy p fid_pre (cm_stmt_first s) + 2) with (pc_pre + cm_stmt_code_count policy p fid_pre (CMWhileS (cm_stmt_expr s) (cm_stmt_first s))) by (cbn [cm_stmt_code_count]; lia).
  all: assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_58_pure_split_goal_5 : cmc_emit_stmt_partial_solve_wit_58_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || assumption || reflexivity).
  all: try dump_pre_spatial.
  all: cbn [cm_stmt_expr cm_stmt_first] in *.
  all: try subst retval retval_2.
  all: replace (pc_pre + cm_rvalue_code_count policy p fid_pre (cm_stmt_expr s) + cm_stmt_code_count policy p fid_pre (cm_stmt_first s) + 2) with (pc_pre + cm_stmt_code_count policy p fid_pre (CMWhileS (cm_stmt_expr s) (cm_stmt_first s))) by (cbn [cm_stmt_code_count]; lia).
  all: assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_58_pure_split_goal_6 : cmc_emit_stmt_partial_solve_wit_58_pure_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || assumption || reflexivity).
  all: try dump_pre_spatial.
  all: cbn [cm_stmt_expr cm_stmt_first] in *.
  all: try subst retval retval_2.
  all: cbn [cm_stmt_code_count] in *.
  all: unfold cm_i32_code_count in *.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_58_pure : cmc_emit_stmt_partial_solve_wit_58_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_partial_solve_wit_58_pure_split_goal_1.
  - Goal_apply proof_of_cmc_emit_stmt_partial_solve_wit_58_pure_split_goal_2.
  - Goal_apply proof_of_cmc_emit_stmt_partial_solve_wit_58_pure_split_goal_3.
  - Goal_apply proof_of_cmc_emit_stmt_partial_solve_wit_58_pure_split_goal_4.
  - Goal_apply proof_of_cmc_emit_stmt_partial_solve_wit_58_pure_split_goal_5.
  - Goal_apply proof_of_cmc_emit_stmt_partial_solve_wit_58_pure_split_goal_6.
Qed. 

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_59_pure_split_goal_1 : cmc_emit_stmt_partial_solve_wit_59_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [cm_stmt_expr cm_stmt_first cm_stmt_second]; first [assumption | reflexivity | lia]).
  all: dump_pre_spatial; reflexivity.
Qed.

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_59_pure : cmc_emit_stmt_partial_solve_wit_59_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_partial_solve_wit_59_pure_split_goal_1.
Qed. 

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_61_pure_split_goal_1 : cmc_emit_stmt_partial_solve_wit_61_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [cm_stmt_expr cm_stmt_first cm_stmt_second]; first [assumption | reflexivity | lia]).
  all: dump_pre_spatial; reflexivity.
Qed.

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_61_pure : cmc_emit_stmt_partial_solve_wit_61_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_partial_solve_wit_61_pure_split_goal_1.
Qed. 

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_62_pure_split_goal_1 : cmc_emit_stmt_partial_solve_wit_62_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [cm_stmt_expr cm_stmt_first cm_stmt_second]; first [assumption | reflexivity | lia]).
  all: dump_pre_spatial; reflexivity.
Qed.

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_62_pure : cmc_emit_stmt_partial_solve_wit_62_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_partial_solve_wit_62_pure_split_goal_1.
Qed. 

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_79_pure_split_goal_1 : cmc_emit_stmt_partial_solve_wit_79_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(first [assumption | reflexivity | lia]).
Qed.

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_79_pure : cmc_emit_stmt_partial_solve_wit_79_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_partial_solve_wit_79_pure_split_goal_1.
Qed. 

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_83_pure_split_goal_1 : cmc_emit_stmt_partial_solve_wit_83_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(first [assumption | reflexivity | lia]).
Qed.

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_83_pure : cmc_emit_stmt_partial_solve_wit_83_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_partial_solve_wit_83_pure_split_goal_1.
Qed. 

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_84_pure_split_goal_1 : cmc_emit_stmt_partial_solve_wit_84_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(first [assumption | reflexivity | lia]).
Qed.

Lemma proof_of_cmc_emit_stmt_partial_solve_wit_84_pure : cmc_emit_stmt_partial_solve_wit_84_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_partial_solve_wit_84_pure_split_goal_1.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_1 : cmc_emit_stmt_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (cm_stmt_rep_node stmt s). unfold cm_stmt_node.
  Intros e a b. Exists b a e.
  split_pure_spatial; [sepcon_assoc_change; cancel | dump_pre_spatial; auto].
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_2_split_goal_1 : cmc_emit_stmt_which_implies_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in PreH2; try discriminate.
  cbn [cm_stmt_payload cm_stmt_expr cm_rep_stmt_slot].
  Intros_p Hpayload.
  dump_pre_spatial. tauto.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_2_split_goal_2 : cmc_emit_stmt_which_implies_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in PreH2; try discriminate.
  cbn [cm_stmt_payload cm_stmt_expr cm_rep_stmt_slot].
  Intros_p Hpayload.
  dump_pre_spatial. tauto.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_2_split_goal_3 : cmc_emit_stmt_which_implies_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in PreH2; try discriminate.
  cbn [cm_stmt_payload cm_stmt_expr cm_rep_stmt_slot].
  Intros_p Hpayload.
  dump_pre_spatial. tauto.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_2_split_goal_4 : cmc_emit_stmt_which_implies_wit_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in PreH2; try discriminate.
  cbn [cm_stmt_payload cm_stmt_expr cm_rep_stmt_slot].
  Intros_p Hpayload.
  dump_pre_spatial. tauto.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_2_split_goal_5 : cmc_emit_stmt_which_implies_wit_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in PreH2; try discriminate.
  cbn [cm_stmt_payload cm_stmt_expr cm_rep_stmt_slot].
  Intros_p Hpayload.
  dump_pre_spatial. tauto.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_2_split_goal_6 : cmc_emit_stmt_which_implies_wit_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in PreH2; try discriminate.
  cbn [cm_stmt_payload cm_stmt_expr cm_rep_stmt_slot].
  Intros_p Hpayload.
  dump_pre_spatial. tauto.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_2_split_goal_7 : cmc_emit_stmt_which_implies_wit_2_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in PreH2; try discriminate.
  cbn [cm_stmt_payload cm_stmt_expr cm_rep_stmt_slot].
  Intros_p Hpayload.
  dump_pre_spatial. tauto.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_2_split_goal_spatial : cmc_emit_stmt_which_implies_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in PreH2; try discriminate.
  cbn [cm_stmt_payload cm_stmt_expr cm_rep_stmt_slot].
  Intros_p Hpayload.
  cancel.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_2 : cmc_emit_stmt_which_implies_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_2_split_goal_spatial.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_2_split_goal_1.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_2_split_goal_2.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_2_split_goal_3.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_2_split_goal_4.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_2_split_goal_5.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_2_split_goal_6.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_2_split_goal_7.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_3_split_goal_1 : cmc_emit_stmt_which_implies_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  try match goal with H : ?s = CMDeclS _ |- _ => rewrite H in * end.
  subst.
  cbn [cm_emit_stmt cm_stmt_code_count Zlength] in *.
  assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_3 : cmc_emit_stmt_which_implies_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_3_split_goal_1.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_4_split_goal_spatial : cmc_emit_stmt_which_implies_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH1. cbn [cm_emit_stmt app].
  rewrite ?app_nil_r.
  cancel (cm_resolved_emitter_plan_rep policy p emitter out capacity done tail).
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_4 : cmc_emit_stmt_which_implies_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_4_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_5_split_goal_spatial : cmc_emit_stmt_which_implies_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_stmt_rep_node. unfold cm_stmt_node.
  Exists xe xa xb.
  unfold cm_stmt_payload. rewrite PreH6.
  cbn [cm_stmt_expr cm_rep_stmt_kind cm_rep_stmt_slot].
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; repeat split; auto.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_5 : cmc_emit_stmt_which_implies_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_5_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_6_split_goal_1 : cmc_emit_stmt_which_implies_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in PreH2; try discriminate.
  cbn [cm_stmt_payload cm_stmt_expr cm_rep_stmt_slot].
  Intros_p Hpayload.
  dump_pre_spatial. tauto.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_6_split_goal_2 : cmc_emit_stmt_which_implies_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in PreH2; try discriminate.
  cbn [cm_stmt_payload cm_stmt_expr cm_rep_stmt_slot].
  Intros_p Hpayload.
  dump_pre_spatial. tauto.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_6_split_goal_3 : cmc_emit_stmt_which_implies_wit_6_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in PreH2; try discriminate.
  cbn [cm_stmt_payload cm_stmt_expr cm_rep_stmt_slot].
  Intros_p Hpayload.
  dump_pre_spatial. tauto.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_6_split_goal_4 : cmc_emit_stmt_which_implies_wit_6_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in PreH2; try discriminate.
  cbn [cm_stmt_payload cm_stmt_expr cm_rep_stmt_slot].
  Intros_p Hpayload.
  dump_pre_spatial. tauto.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_6_split_goal_5 : cmc_emit_stmt_which_implies_wit_6_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in PreH2; try discriminate.
  cbn [cm_stmt_payload cm_stmt_expr cm_rep_stmt_slot].
  Intros_p Hpayload.
  dump_pre_spatial. tauto.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_6_split_goal_6 : cmc_emit_stmt_which_implies_wit_6_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in PreH2; try discriminate.
  cbn [cm_stmt_payload cm_stmt_expr cm_rep_stmt_slot].
  Intros_p Hpayload.
  dump_pre_spatial. tauto.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_6_split_goal_spatial : cmc_emit_stmt_which_implies_wit_6_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in PreH2; try discriminate.
  cbn [cm_stmt_payload cm_stmt_expr cm_rep_stmt_slot].
  Intros_p Hpayload.
  cancel.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_6 : cmc_emit_stmt_which_implies_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_6_split_goal_spatial.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_6_split_goal_1.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_6_split_goal_2.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_6_split_goal_3.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_6_split_goal_4.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_6_split_goal_5.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_6_split_goal_6.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_7_split_goal_1 : cmc_emit_stmt_which_implies_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  all: cbn [tvm_opcode_code]; lia.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_7_split_goal_2 : cmc_emit_stmt_which_implies_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  all: cbn [tvm_opcode_code]; lia.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_7_split_goal_3 : cmc_emit_stmt_which_implies_wit_7_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  all: rewrite cm_emit_stmt_length__stmt_capacity in PreH22.
  all: exact PreH22.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_7_split_goal_4 : cmc_emit_stmt_which_implies_wit_7_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
  all: destruct s; cbn [cm_stmt_expr cm_stmt_first cm_stmt_second cm_rep_stmt_slot] in *; try discriminate.
  all: subst f.
  all: rewrite !cm_emit_stmt_length__stmt_capacity in *.
  all: rewrite ?cm_expr_rvalue_length__stmt_capacity.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try assumption.
  all: try (apply cm_slot_type_encode__statement_normalization_safety; lia).
  all: try (unfold cm_binding_valid; tauto).
  all: unfold cm_i32_code_count in *.
  all: unfold cm_imax in *.
  all: unfold cm_expr_temps_for; cbn [Z.eqb].
  all: repeat match goal with H : context [Z.max ?a ?b] |- _ => destruct (Z.max_spec a b) as [[? Hmax]|[? Hmax]]; rewrite Hmax in *; clear Hmax end.
  all: try lia.
  all: repeat match goal with
  | H : cm_stmt_counts_representable ?pol ?pr ?fi ?a |- _ =>
    let Hn := fresh in pose proof (cm_stmt_count_nonnegative__stmt_capacity pol pr fi a) as Hn; clear H
  | H : cm_expr_counts_representable ?pol ?pr ?fi ?e |- _ =>
    let Hn := fresh in pose proof (cm_rvalue_count_nonnegative__stmt_capacity pol pr fi e) as Hn; clear H
  end.
  all: try lia.
  all: repeat match goal with H : context [cm_char_normalize_count ?ty] |- _ => destruct ty; cbn [cm_char_normalize_count] in * end.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_7_split_goal_5 : cmc_emit_stmt_which_implies_wit_7_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia).
  all: destruct s; cbn [cm_stmt_expr cm_stmt_first cm_stmt_second cm_rep_stmt_slot] in *; try discriminate.
  all: subst f.
  all: rewrite !cm_emit_stmt_length__stmt_capacity in *.
  all: rewrite ?cm_expr_rvalue_length__stmt_capacity.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try assumption.
  all: try (apply cm_slot_type_encode__statement_normalization_safety; lia).
  all: try (unfold cm_binding_valid; tauto).
  all: unfold cm_i32_code_count in *.
  all: unfold cm_imax in *.
  all: unfold cm_expr_temps_for; cbn [Z.eqb].
  all: repeat match goal with H : context [Z.max ?a ?b] |- _ => destruct (Z.max_spec a b) as [[? Hmax]|[? Hmax]]; rewrite Hmax in *; clear Hmax end.
  all: try lia.
  all: repeat match goal with
  | H : cm_stmt_counts_representable ?pol ?pr ?fi ?a |- _ =>
    let Hn := fresh in pose proof (cm_stmt_count_nonnegative__stmt_capacity pol pr fi a) as Hn; clear H
  | H : cm_expr_counts_representable ?pol ?pr ?fi ?e |- _ =>
    let Hn := fresh in pose proof (cm_rvalue_count_nonnegative__stmt_capacity pol pr fi e) as Hn; clear H
  end.
  all: try lia.
  all: repeat match goal with H : context [cm_char_normalize_count ?ty] |- _ => destruct ty; cbn [cm_char_normalize_count] in * end.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_7_split_goal_6 : cmc_emit_stmt_which_implies_wit_7_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia).
  all: destruct s; cbn [cm_stmt_expr cm_stmt_first cm_stmt_second cm_rep_stmt_slot] in *; try discriminate.
  all: subst f.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_7_split_goal_7 : cmc_emit_stmt_which_implies_wit_7_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia).
  all: destruct s; cbn [cm_stmt_expr cm_stmt_first cm_stmt_second cm_rep_stmt_slot] in *; try discriminate.
  all: subst f.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_7 : cmc_emit_stmt_which_implies_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_7_split_goal_1.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_7_split_goal_2.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_7_split_goal_3.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_7_split_goal_4.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_7_split_goal_5.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_7_split_goal_6.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_7_split_goal_7.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_8_split_goal_spatial : cmc_emit_stmt_which_implies_wit_8_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; try discriminate.
  cbn [cm_emit_stmt cm_stmt_expr cm_rep_stmt_slot cm_binding_address_code].
  repeat rewrite <- app_assoc.
  cancel.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_8 : cmc_emit_stmt_which_implies_wit_8.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_8_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_9_split_goal_spatial : cmc_emit_stmt_which_implies_wit_9_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  all: cbn [app]; cancel.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_9 : cmc_emit_stmt_which_implies_wit_9.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_9_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_10_split_goal_spatial : cmc_emit_stmt_which_implies_wit_10_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct s; cbn [cm_stmt_expr cm_stmt_first cm_rep_stmt_slot] in PreH1; try discriminate.
  cbn [cm_emit_stmt cm_stmt_expr cm_stmt_first cm_rep_stmt_slot cm_binding_address_code Z.eqb].
  repeat rewrite <- List.app_assoc.
  reflexivity.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_10 : cmc_emit_stmt_which_implies_wit_10.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_10_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_11_split_goal_spatial : cmc_emit_stmt_which_implies_wit_11_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_stmt_rep_node. unfold cm_stmt_node.
  Exists xe xa xb.
  unfold cm_stmt_payload. rewrite PreH6.
  cbn [cm_stmt_expr cm_rep_stmt_kind cm_rep_stmt_slot].
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; repeat split; auto.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_11 : cmc_emit_stmt_which_implies_wit_11.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_11_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_12_split_goal_1 : cmc_emit_stmt_which_implies_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in PreH2; try discriminate.
  cbn [cm_stmt_payload cm_stmt_expr cm_rep_stmt_slot].
  Intros_p Hpayload.
  dump_pre_spatial. tauto.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_12_split_goal_2 : cmc_emit_stmt_which_implies_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in PreH2; try discriminate.
  cbn [cm_stmt_payload cm_stmt_expr cm_rep_stmt_slot].
  Intros_p Hpayload.
  dump_pre_spatial. tauto.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_12_split_goal_3 : cmc_emit_stmt_which_implies_wit_12_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in PreH2; try discriminate.
  cbn [cm_stmt_payload cm_stmt_expr cm_rep_stmt_slot].
  Intros_p Hpayload.
  dump_pre_spatial. tauto.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_12_split_goal_4 : cmc_emit_stmt_which_implies_wit_12_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in PreH2; try discriminate.
  cbn [cm_stmt_payload cm_stmt_expr cm_rep_stmt_slot].
  Intros_p Hpayload.
  dump_pre_spatial. tauto.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_12_split_goal_5 : cmc_emit_stmt_which_implies_wit_12_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in PreH2; try discriminate.
  cbn [cm_stmt_payload cm_stmt_expr cm_rep_stmt_slot].
  Intros_p Hpayload.
  dump_pre_spatial. tauto.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_12_split_goal_6 : cmc_emit_stmt_which_implies_wit_12_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in PreH2; try discriminate.
  cbn [cm_stmt_payload cm_stmt_expr cm_rep_stmt_slot].
  Intros_p Hpayload.
  dump_pre_spatial. tauto.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_12_split_goal_7 : cmc_emit_stmt_which_implies_wit_12_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in PreH2; try discriminate.
  cbn [cm_stmt_payload cm_stmt_expr cm_rep_stmt_slot].
  Intros_p Hpayload.
  dump_pre_spatial. tauto.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_12_split_goal_spatial : cmc_emit_stmt_which_implies_wit_12_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in PreH2; try discriminate.
  cbn [cm_stmt_payload cm_stmt_expr cm_rep_stmt_slot].
  Intros_p Hpayload.
  cancel.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_12 : cmc_emit_stmt_which_implies_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_12_split_goal_spatial.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_12_split_goal_1.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_12_split_goal_2.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_12_split_goal_3.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_12_split_goal_4.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_12_split_goal_5.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_12_split_goal_6.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_12_split_goal_7.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_13_split_goal_1 : cmc_emit_stmt_which_implies_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  try match goal with H : ?s = CMDeclS _ |- _ => rewrite H in * end.
  subst.
  cbn [cm_emit_stmt cm_stmt_code_count Zlength] in *.
  assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_13 : cmc_emit_stmt_which_implies_wit_13.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_13_split_goal_1.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_14_split_goal_spatial : cmc_emit_stmt_which_implies_wit_14_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH1. cbn [cm_emit_stmt app].
  rewrite ?app_nil_r.
  cancel (cm_resolved_emitter_plan_rep policy p emitter out capacity done tail).
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_14 : cmc_emit_stmt_which_implies_wit_14.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_14_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_15_split_goal_spatial : cmc_emit_stmt_which_implies_wit_15_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_stmt_rep_node. unfold cm_stmt_node.
  Exists xe xa xb.
  unfold cm_stmt_payload. rewrite PreH6.
  cbn [cm_stmt_expr cm_rep_stmt_kind cm_rep_stmt_slot].
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; repeat split; auto.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_15 : cmc_emit_stmt_which_implies_wit_15.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_15_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_16_split_goal_1 : cmc_emit_stmt_which_implies_wit_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in PreH2; try discriminate.
  cbn [cm_stmt_payload cm_stmt_expr cm_rep_stmt_slot].
  Intros_p Hpayload.
  dump_pre_spatial. tauto.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_16_split_goal_2 : cmc_emit_stmt_which_implies_wit_16_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in PreH2; try discriminate.
  cbn [cm_stmt_payload cm_stmt_expr cm_rep_stmt_slot].
  Intros_p Hpayload.
  dump_pre_spatial. tauto.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_16_split_goal_3 : cmc_emit_stmt_which_implies_wit_16_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in PreH2; try discriminate.
  cbn [cm_stmt_payload cm_stmt_expr cm_rep_stmt_slot].
  Intros_p Hpayload.
  dump_pre_spatial. tauto.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_16_split_goal_4 : cmc_emit_stmt_which_implies_wit_16_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in PreH2; try discriminate.
  cbn [cm_stmt_payload cm_stmt_expr cm_rep_stmt_slot].
  Intros_p Hpayload.
  dump_pre_spatial. tauto.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_16_split_goal_5 : cmc_emit_stmt_which_implies_wit_16_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in PreH2; try discriminate.
  cbn [cm_stmt_payload cm_stmt_expr cm_rep_stmt_slot].
  Intros_p Hpayload.
  dump_pre_spatial. tauto.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_16_split_goal_6 : cmc_emit_stmt_which_implies_wit_16_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in PreH2; try discriminate.
  cbn [cm_stmt_payload cm_stmt_expr cm_rep_stmt_slot].
  Intros_p Hpayload.
  dump_pre_spatial. tauto.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_16_split_goal_spatial : cmc_emit_stmt_which_implies_wit_16_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in PreH2; try discriminate.
  cbn [cm_stmt_payload cm_stmt_expr cm_rep_stmt_slot].
  Intros_p Hpayload.
  cancel.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_16 : cmc_emit_stmt_which_implies_wit_16.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_16_split_goal_spatial.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_16_split_goal_1.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_16_split_goal_2.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_16_split_goal_3.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_16_split_goal_4.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_16_split_goal_5.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_16_split_goal_6.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_17_split_goal_1 : cmc_emit_stmt_which_implies_wit_17_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  all: destruct s; cbn [cm_stmt_expr cm_stmt_first cm_stmt_second cm_rep_stmt_slot] in *; try discriminate.
  all: subst f.
  all: rewrite !cm_emit_stmt_length__stmt_capacity in *.
  all: rewrite ?cm_expr_rvalue_length__stmt_capacity.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try assumption.
  all: try (apply cm_slot_type_encode__statement_normalization_safety; lia).
  all: try (unfold cm_binding_valid; tauto).
  all: unfold cm_i32_code_count in *.
  all: unfold cm_imax in *.
  all: unfold cm_expr_temps_for; cbn [Z.eqb].
  all: repeat match goal with H : context [Z.max ?a ?b] |- _ => destruct (Z.max_spec a b) as [[? Hmax]|[? Hmax]]; rewrite Hmax in *; clear Hmax end.
  all: try lia.
  all: repeat match goal with
  | H : cm_stmt_counts_representable ?pol ?pr ?fi ?a |- _ =>
    let Hn := fresh in pose proof (cm_stmt_count_nonnegative__stmt_capacity pol pr fi a) as Hn; clear H
  | H : cm_expr_counts_representable ?pol ?pr ?fi ?e |- _ =>
    let Hn := fresh in pose proof (cm_rvalue_count_nonnegative__stmt_capacity pol pr fi e) as Hn; clear H
  end.
  all: try lia.
  all: repeat match goal with H : context [cm_char_normalize_count ?ty] |- _ => destruct ty; cbn [cm_char_normalize_count] in * end.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_17_split_goal_2 : cmc_emit_stmt_which_implies_wit_17_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  all: destruct s; cbn [cm_stmt_expr cm_stmt_first cm_stmt_second cm_rep_stmt_slot] in *; try discriminate.
  all: subst f.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_17_split_goal_3 : cmc_emit_stmt_which_implies_wit_17_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  all: destruct s; cbn [cm_stmt_expr cm_stmt_first cm_stmt_second cm_rep_stmt_slot] in *; try discriminate.
  all: subst f.
  all: rewrite !cm_emit_stmt_length__stmt_capacity in *.
  all: rewrite ?cm_expr_rvalue_length__stmt_capacity.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try assumption.
  all: try (apply cm_slot_type_encode__statement_normalization_safety; lia).
  all: try (unfold cm_binding_valid; tauto).
  all: unfold cm_i32_code_count in *.
  all: unfold cm_imax in *.
  all: unfold cm_expr_temps_for; cbn [Z.eqb].
  all: repeat match goal with H : context [Z.max ?a ?b] |- _ => destruct (Z.max_spec a b) as [[? Hmax]|[? Hmax]]; rewrite Hmax in *; clear Hmax end.
  all: try lia.
  all: repeat match goal with
  | H : cm_stmt_counts_representable ?pol ?pr ?fi ?a |- _ =>
    let Hn := fresh in pose proof (cm_stmt_count_nonnegative__stmt_capacity pol pr fi a) as Hn; clear H
  | H : cm_expr_counts_representable ?pol ?pr ?fi ?e |- _ =>
    let Hn := fresh in pose proof (cm_rvalue_count_nonnegative__stmt_capacity pol pr fi e) as Hn; clear H
  end.
  all: try lia.
  all: repeat match goal with H : context [cm_char_normalize_count ?ty] |- _ => destruct ty; cbn [cm_char_normalize_count] in * end.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_17_split_goal_4 : cmc_emit_stmt_which_implies_wit_17_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
  all: destruct s; cbn [cm_stmt_expr cm_stmt_first cm_stmt_second cm_rep_stmt_slot] in *; try discriminate.
  all: subst f.
  all: rewrite !cm_emit_stmt_length__stmt_capacity in *.
  all: rewrite ?cm_expr_rvalue_length__stmt_capacity.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try assumption.
  all: try (apply cm_slot_type_encode__statement_normalization_safety; lia).
  all: try (unfold cm_binding_valid; tauto).
  all: unfold cm_i32_code_count in *.
  all: unfold cm_imax in *.
  all: unfold cm_expr_temps_for; cbn [Z.eqb].
  all: repeat match goal with H : context [Z.max ?a ?b] |- _ => destruct (Z.max_spec a b) as [[? Hmax]|[? Hmax]]; rewrite Hmax in *; clear Hmax end.
  all: try lia.
  all: repeat match goal with
  | H : cm_stmt_counts_representable ?pol ?pr ?fi ?a |- _ =>
    let Hn := fresh in pose proof (cm_stmt_count_nonnegative__stmt_capacity pol pr fi a) as Hn; clear H
  | H : cm_expr_counts_representable ?pol ?pr ?fi ?e |- _ =>
    let Hn := fresh in pose proof (cm_rvalue_count_nonnegative__stmt_capacity pol pr fi e) as Hn; clear H
  end.
  all: try lia.
  all: repeat match goal with H : context [cm_char_normalize_count ?ty] |- _ => destruct ty; cbn [cm_char_normalize_count] in * end.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_17_split_goal_5 : cmc_emit_stmt_which_implies_wit_17_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia).
  all: rewrite cm_emit_stmt_length__stmt_capacity in PreH22.
  all: exact PreH22.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_17_split_goal_6 : cmc_emit_stmt_which_implies_wit_17_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia).
  all: destruct s; cbn [cm_stmt_expr cm_stmt_first cm_stmt_second cm_rep_stmt_slot] in *; try discriminate.
  all: subst f.
  all: rewrite !cm_emit_stmt_length__stmt_capacity in *.
  all: rewrite ?cm_expr_rvalue_length__stmt_capacity.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try assumption.
  all: try (apply cm_slot_type_encode__statement_normalization_safety; lia).
  all: try (unfold cm_binding_valid; tauto).
  all: unfold cm_i32_code_count in *.
  all: unfold cm_imax in *.
  all: unfold cm_expr_temps_for; cbn [Z.eqb].
  all: repeat match goal with H : context [Z.max ?a ?b] |- _ => destruct (Z.max_spec a b) as [[? Hmax]|[? Hmax]]; rewrite Hmax in *; clear Hmax end.
  all: try lia.
  all: repeat match goal with
  | H : cm_stmt_counts_representable ?pol ?pr ?fi ?a |- _ =>
    let Hn := fresh in pose proof (cm_stmt_count_nonnegative__stmt_capacity pol pr fi a) as Hn; clear H
  | H : cm_expr_counts_representable ?pol ?pr ?fi ?e |- _ =>
    let Hn := fresh in pose proof (cm_rvalue_count_nonnegative__stmt_capacity pol pr fi e) as Hn; clear H
  end.
  all: try lia.
  all: repeat match goal with H : context [cm_char_normalize_count ?ty] |- _ => destruct ty; cbn [cm_char_normalize_count] in * end.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_17_split_goal_7 : cmc_emit_stmt_which_implies_wit_17_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia).
  all: destruct s; cbn [cm_stmt_expr cm_stmt_first cm_stmt_second cm_rep_stmt_slot] in *; try discriminate.
  all: subst f.
  all: rewrite !cm_emit_stmt_length__stmt_capacity in *.
  all: rewrite ?cm_expr_rvalue_length__stmt_capacity.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try assumption.
  all: try (apply cm_slot_type_encode__statement_normalization_safety; lia).
  all: try (unfold cm_binding_valid; tauto).
  all: unfold cm_i32_code_count in *.
  all: unfold cm_imax in *.
  all: unfold cm_expr_temps_for; cbn [Z.eqb].
  all: repeat match goal with H : context [Z.max ?a ?b] |- _ => destruct (Z.max_spec a b) as [[? Hmax]|[? Hmax]]; rewrite Hmax in *; clear Hmax end.
  all: try lia.
  all: repeat match goal with
  | H : cm_stmt_counts_representable ?pol ?pr ?fi ?a |- _ =>
    let Hn := fresh in pose proof (cm_stmt_count_nonnegative__stmt_capacity pol pr fi a) as Hn; clear H
  | H : cm_expr_counts_representable ?pol ?pr ?fi ?e |- _ =>
    let Hn := fresh in pose proof (cm_rvalue_count_nonnegative__stmt_capacity pol pr fi e) as Hn; clear H
  end.
  all: try lia.
  all: repeat match goal with H : context [cm_char_normalize_count ?ty] |- _ => destruct ty; cbn [cm_char_normalize_count] in * end.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_17_split_goal_8 : cmc_emit_stmt_which_implies_wit_17_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia).
  all: destruct s; cbn [cm_stmt_expr cm_stmt_first cm_stmt_second cm_rep_stmt_slot] in *; try discriminate.
  all: subst f.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_17_split_goal_9 : cmc_emit_stmt_which_implies_wit_17_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia).
  all: destruct s; cbn [cm_stmt_expr cm_stmt_first cm_stmt_second cm_rep_stmt_slot] in *; try discriminate.
  all: subst f.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_17 : cmc_emit_stmt_which_implies_wit_17.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_17_split_goal_1.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_17_split_goal_2.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_17_split_goal_3.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_17_split_goal_4.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_17_split_goal_5.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_17_split_goal_6.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_17_split_goal_7.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_17_split_goal_8.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_17_split_goal_9.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_18 : cmc_emit_stmt_which_implies_wit_18.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_function_context_rep.
  Intros zp zl.
  Exists zl zp.
  split_pure_spatial; [repeat progress cancel | dump_pre_spatial; assumption].
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_19_split_goal_spatial : cmc_emit_stmt_which_implies_wit_19_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_function_context_rep.
  Exists zp zl.
  split_pure_spatial; [repeat progress cancel | dump_pre_spatial; assumption].
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_19 : cmc_emit_stmt_which_implies_wit_19.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_19_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_20_split_goal_spatial : cmc_emit_stmt_which_implies_wit_20_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; try discriminate.
  subst f.
  cbn [cm_emit_stmt cm_stmt_expr cm_rep_stmt_slot cm_binding_address_code].
  unfold cm_binding_address_code.
  cbn [Z.eqb Pos.eqb].
  repeat rewrite <- app_assoc.
  cancel.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_20 : cmc_emit_stmt_which_implies_wit_20.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_20_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_21_split_goal_spatial : cmc_emit_stmt_which_implies_wit_21_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct s; cbn [cm_stmt_expr cm_stmt_first cm_rep_stmt_slot] in PreH1; try discriminate.
  subst f.
  cbn [cm_emit_stmt cm_stmt_expr cm_stmt_first cm_rep_stmt_slot cm_binding_address_code Z.eqb].
  repeat rewrite <- List.app_assoc.
  reflexivity.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_21 : cmc_emit_stmt_which_implies_wit_21.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_21_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_22_split_goal_spatial : cmc_emit_stmt_which_implies_wit_22_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_stmt_rep_node. unfold cm_stmt_node.
  Exists xe xa xb.
  unfold cm_stmt_payload. rewrite PreH6.
  cbn [cm_stmt_expr cm_rep_stmt_kind cm_rep_stmt_slot].
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; repeat split; auto.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_22 : cmc_emit_stmt_which_implies_wit_22.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_22_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_23_split_goal_1 : cmc_emit_stmt_which_implies_wit_23_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || reflexivity).
  destruct s; cbn [cm_rep_stmt_kind] in *; try discriminate.
  cbn [cm_stmt_payload cm_stmt_first cm_stmt_second cm_stmt_expr].
  Intros_p Hpayload.
  dump_pre_spatial. first [reflexivity | tauto].
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_23_split_goal_2 : cmc_emit_stmt_which_implies_wit_23_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || reflexivity).
  destruct s; cbn [cm_rep_stmt_kind] in *; try discriminate.
  cbn [cm_stmt_payload cm_stmt_first cm_stmt_second cm_stmt_expr].
  Intros_p Hpayload.
  dump_pre_spatial. first [reflexivity | tauto].
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_23_split_goal_3 : cmc_emit_stmt_which_implies_wit_23_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || reflexivity).
  destruct s; cbn [cm_rep_stmt_kind] in *; try discriminate.
  cbn [cm_stmt_payload cm_stmt_first cm_stmt_second cm_stmt_expr].
  Intros_p Hpayload.
  dump_pre_spatial. first [reflexivity | tauto].
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_23_split_goal_spatial : cmc_emit_stmt_which_implies_wit_23_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || reflexivity).
  destruct s; cbn [cm_rep_stmt_kind] in *; try discriminate.
  cbn [cm_stmt_payload cm_stmt_first cm_stmt_second cm_stmt_expr].
  Intros_p Hpayload.
  cancel.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_23 : cmc_emit_stmt_which_implies_wit_23.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_23_split_goal_spatial.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_23_split_goal_1.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_23_split_goal_2.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_23_split_goal_3.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_24_split_goal_1 : cmc_emit_stmt_which_implies_wit_24_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  all: rewrite cm_emit_stmt_length__stmt_capacity in PreH22.
  all: exact PreH22.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_24_split_goal_2 : cmc_emit_stmt_which_implies_wit_24_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  all: destruct s; cbn [cm_stmt_expr cm_stmt_first cm_stmt_second cm_rep_stmt_slot] in *; try discriminate.
  all: subst f.
  all: rewrite !cm_emit_stmt_length__stmt_capacity in *.
  all: rewrite ?cm_expr_rvalue_length__stmt_capacity.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try assumption.
  all: try (apply cm_slot_type_encode__statement_normalization_safety; lia).
  all: try (unfold cm_binding_valid; tauto).
  all: unfold cm_i32_code_count in *.
  all: unfold cm_imax in *.
  all: unfold cm_expr_temps_for; cbn [Z.eqb].
  all: repeat match goal with H : context [Z.max ?a ?b] |- _ => destruct (Z.max_spec a b) as [[? Hmax]|[? Hmax]]; rewrite Hmax in *; clear Hmax end.
  all: try lia.
  all: repeat match goal with
  | H : cm_stmt_counts_representable ?pol ?pr ?fi ?a |- _ =>
    let Hn := fresh in pose proof (cm_stmt_count_nonnegative__stmt_capacity pol pr fi a) as Hn; clear H
  | H : cm_expr_counts_representable ?pol ?pr ?fi ?e |- _ =>
    let Hn := fresh in pose proof (cm_rvalue_count_nonnegative__stmt_capacity pol pr fi e) as Hn; clear H
  end.
  all: try lia.
  all: repeat match goal with H : context [cm_char_normalize_count ?ty] |- _ => destruct ty; cbn [cm_char_normalize_count] in * end.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_24_split_goal_3 : cmc_emit_stmt_which_implies_wit_24_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  all: destruct s; cbn [cm_stmt_expr cm_stmt_first cm_stmt_second cm_rep_stmt_slot] in *; try discriminate.
  all: subst f.
  all: rewrite !cm_emit_stmt_length__stmt_capacity in *.
  all: rewrite ?cm_expr_rvalue_length__stmt_capacity.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try assumption.
  all: try (apply cm_slot_type_encode__statement_normalization_safety; lia).
  all: try (unfold cm_binding_valid; tauto).
  all: unfold cm_i32_code_count in *.
  all: unfold cm_imax in *.
  all: unfold cm_expr_temps_for; cbn [Z.eqb].
  all: repeat match goal with H : context [Z.max ?a ?b] |- _ => destruct (Z.max_spec a b) as [[? Hmax]|[? Hmax]]; rewrite Hmax in *; clear Hmax end.
  all: try lia.
  all: repeat match goal with
  | H : cm_stmt_counts_representable ?pol ?pr ?fi ?a |- _ =>
    let Hn := fresh in pose proof (cm_stmt_count_nonnegative__stmt_capacity pol pr fi a) as Hn; clear H
  | H : cm_expr_counts_representable ?pol ?pr ?fi ?e |- _ =>
    let Hn := fresh in pose proof (cm_rvalue_count_nonnegative__stmt_capacity pol pr fi e) as Hn; clear H
  end.
  all: try lia.
  all: repeat match goal with H : context [cm_char_normalize_count ?ty] |- _ => destruct ty; cbn [cm_char_normalize_count] in * end.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_24_split_goal_4 : cmc_emit_stmt_which_implies_wit_24_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
  all: destruct s; cbn [cm_stmt_expr cm_stmt_first cm_stmt_second cm_rep_stmt_slot] in *; try discriminate.
  all: subst f.
  all: rewrite !cm_emit_stmt_length__stmt_capacity in *.
  all: rewrite ?cm_expr_rvalue_length__stmt_capacity.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try assumption.
  all: try (apply cm_slot_type_encode__statement_normalization_safety; lia).
  all: try (unfold cm_binding_valid; tauto).
  all: unfold cm_i32_code_count in *.
  all: unfold cm_imax in *.
  all: unfold cm_expr_temps_for; cbn [Z.eqb].
  all: repeat match goal with H : context [Z.max ?a ?b] |- _ => destruct (Z.max_spec a b) as [[? Hmax]|[? Hmax]]; rewrite Hmax in *; clear Hmax end.
  all: try lia.
  all: repeat match goal with
  | H : cm_stmt_counts_representable ?pol ?pr ?fi ?a |- _ =>
    let Hn := fresh in pose proof (cm_stmt_count_nonnegative__stmt_capacity pol pr fi a) as Hn; clear H
  | H : cm_expr_counts_representable ?pol ?pr ?fi ?e |- _ =>
    let Hn := fresh in pose proof (cm_rvalue_count_nonnegative__stmt_capacity pol pr fi e) as Hn; clear H
  end.
  all: try lia.
  all: repeat match goal with H : context [cm_char_normalize_count ?ty] |- _ => destruct ty; cbn [cm_char_normalize_count] in * end.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_24_split_goal_5 : cmc_emit_stmt_which_implies_wit_24_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia).
  all: destruct s; cbn [cm_stmt_expr cm_stmt_first cm_stmt_second cm_rep_stmt_slot] in *; try discriminate.
  all: subst f.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_24_split_goal_6 : cmc_emit_stmt_which_implies_wit_24_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia).
  all: destruct s; cbn [cm_stmt_expr cm_stmt_first cm_stmt_second cm_rep_stmt_slot] in *; try discriminate.
  all: subst f.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_24_split_goal_7 : cmc_emit_stmt_which_implies_wit_24_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia).
  all: destruct s; cbn [cm_stmt_expr cm_stmt_first cm_stmt_second cm_rep_stmt_slot] in *; try discriminate.
  all: subst f.
  all: rewrite !cm_emit_stmt_length__stmt_capacity in *.
  all: rewrite ?cm_expr_rvalue_length__stmt_capacity.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try assumption.
  all: try (apply cm_slot_type_encode__statement_normalization_safety; lia).
  all: try (unfold cm_binding_valid; tauto).
  all: unfold cm_i32_code_count in *.
  all: unfold cm_imax in *.
  all: unfold cm_expr_temps_for; cbn [Z.eqb].
  all: repeat match goal with H : context [Z.max ?a ?b] |- _ => destruct (Z.max_spec a b) as [[? Hmax]|[? Hmax]]; rewrite Hmax in *; clear Hmax end.
  all: try lia.
  all: repeat match goal with
  | H : cm_stmt_counts_representable ?pol ?pr ?fi ?a |- _ =>
    let Hn := fresh in pose proof (cm_stmt_count_nonnegative__stmt_capacity pol pr fi a) as Hn; clear H
  | H : cm_expr_counts_representable ?pol ?pr ?fi ?e |- _ =>
    let Hn := fresh in pose proof (cm_rvalue_count_nonnegative__stmt_capacity pol pr fi e) as Hn; clear H
  end.
  all: try lia.
  all: repeat match goal with H : context [cm_char_normalize_count ?ty] |- _ => destruct ty; cbn [cm_char_normalize_count] in * end.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_24_split_goal_8 : cmc_emit_stmt_which_implies_wit_24_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia).
  all: destruct s; cbn [cm_stmt_expr cm_stmt_first cm_stmt_second cm_rep_stmt_slot] in *; try discriminate.
  all: subst f.
  all: rewrite !cm_emit_stmt_length__stmt_capacity in *.
  all: rewrite ?cm_expr_rvalue_length__stmt_capacity.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try assumption.
  all: try (apply cm_slot_type_encode__statement_normalization_safety; lia).
  all: try (unfold cm_binding_valid; tauto).
  all: unfold cm_i32_code_count in *.
  all: unfold cm_imax in *.
  all: unfold cm_expr_temps_for; cbn [Z.eqb].
  all: repeat match goal with H : context [Z.max ?a ?b] |- _ => destruct (Z.max_spec a b) as [[? Hmax]|[? Hmax]]; rewrite Hmax in *; clear Hmax end.
  all: try lia.
  all: repeat match goal with
  | H : cm_stmt_counts_representable ?pol ?pr ?fi ?a |- _ =>
    let Hn := fresh in pose proof (cm_stmt_count_nonnegative__stmt_capacity pol pr fi a) as Hn; clear H
  | H : cm_expr_counts_representable ?pol ?pr ?fi ?e |- _ =>
    let Hn := fresh in pose proof (cm_rvalue_count_nonnegative__stmt_capacity pol pr fi e) as Hn; clear H
  end.
  all: try lia.
  all: repeat match goal with H : context [cm_char_normalize_count ?ty] |- _ => destruct ty; cbn [cm_char_normalize_count] in * end.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_24_split_goal_9 : cmc_emit_stmt_which_implies_wit_24_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia).
  all: destruct s; cbn [cm_stmt_expr cm_stmt_first cm_stmt_second cm_rep_stmt_slot] in *; try discriminate.
  all: subst f.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_24_split_goal_10 : cmc_emit_stmt_which_implies_wit_24_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia).
  all: destruct s; cbn [cm_stmt_expr cm_stmt_first cm_stmt_second cm_rep_stmt_slot] in *; try discriminate.
  all: subst f.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_24 : cmc_emit_stmt_which_implies_wit_24.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_24_split_goal_1.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_24_split_goal_2.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_24_split_goal_3.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_24_split_goal_4.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_24_split_goal_5.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_24_split_goal_6.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_24_split_goal_7.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_24_split_goal_8.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_24_split_goal_9.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_24_split_goal_10.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_26_split_goal_spatial : cmc_emit_stmt_which_implies_wit_26_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct s; cbn [cm_stmt_first cm_stmt_second] in *; try discriminate.
  cbn [cm_emit_stmt].
  repeat rewrite app_assoc.
  cancel.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_26 : cmc_emit_stmt_which_implies_wit_26.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_26_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_27_split_goal_spatial : cmc_emit_stmt_which_implies_wit_27_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct s; cbn [cm_stmt_first cm_stmt_second] in *; try discriminate.
  cbn [cm_emit_stmt].
  repeat rewrite app_assoc.
  cancel.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_27 : cmc_emit_stmt_which_implies_wit_27.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_27_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_28_split_goal_spatial : cmc_emit_stmt_which_implies_wit_28_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (cm_stmt_rep_node stmt s).
  unfold cm_stmt_node.
  Exists xe xa xb.
  unfold cm_stmt_payload.
  rewrite PreH6.
  cbn [cm_stmt_first cm_stmt_second cm_stmt_expr].
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_28 : cmc_emit_stmt_which_implies_wit_28.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_28_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_29_split_goal_1 : cmc_emit_stmt_which_implies_wit_29_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || reflexivity).
  destruct s; cbn [cm_rep_stmt_kind] in *; try discriminate.
  cbn [cm_stmt_payload cm_stmt_first cm_stmt_second cm_stmt_expr].
  Intros_p Hpayload.
  dump_pre_spatial. first [reflexivity | tauto].
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_29_split_goal_2 : cmc_emit_stmt_which_implies_wit_29_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || reflexivity).
  destruct s; cbn [cm_rep_stmt_kind] in *; try discriminate.
  cbn [cm_stmt_payload cm_stmt_first cm_stmt_second cm_stmt_expr].
  Intros_p Hpayload.
  dump_pre_spatial. first [reflexivity | tauto].
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_29_split_goal_3 : cmc_emit_stmt_which_implies_wit_29_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || reflexivity).
  destruct s; cbn [cm_rep_stmt_kind] in *; try discriminate.
  cbn [cm_stmt_payload cm_stmt_first cm_stmt_second cm_stmt_expr].
  Intros_p Hpayload.
  dump_pre_spatial. first [reflexivity | tauto].
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_29_split_goal_4 : cmc_emit_stmt_which_implies_wit_29_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || reflexivity).
  destruct s; cbn [cm_rep_stmt_kind] in *; try discriminate.
  cbn [cm_stmt_payload cm_stmt_first cm_stmt_second cm_stmt_expr].
  Intros_p Hpayload.
  dump_pre_spatial. first [reflexivity | tauto].
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_29_split_goal_5 : cmc_emit_stmt_which_implies_wit_29_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || reflexivity).
  destruct s; cbn [cm_rep_stmt_kind] in *; try discriminate.
  cbn [cm_stmt_payload cm_stmt_first cm_stmt_second cm_stmt_expr].
  Intros_p Hpayload.
  dump_pre_spatial. first [reflexivity | tauto].
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_29_split_goal_6 : cmc_emit_stmt_which_implies_wit_29_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || reflexivity).
  destruct s; cbn [cm_rep_stmt_kind] in *; try discriminate.
  cbn [cm_stmt_payload cm_stmt_first cm_stmt_second cm_stmt_expr].
  Intros_p Hpayload.
  dump_pre_spatial. first [reflexivity | tauto].
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_29_split_goal_spatial : cmc_emit_stmt_which_implies_wit_29_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || reflexivity).
  destruct s; cbn [cm_rep_stmt_kind] in *; try discriminate.
  cbn [cm_stmt_payload cm_stmt_first cm_stmt_second cm_stmt_expr].
  Intros_p Hpayload.
  cancel.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_29 : cmc_emit_stmt_which_implies_wit_29.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_29_split_goal_spatial.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_29_split_goal_1.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_29_split_goal_2.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_29_split_goal_3.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_29_split_goal_4.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_29_split_goal_5.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_29_split_goal_6.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_30_split_goal_1 : cmc_emit_stmt_which_implies_wit_30_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  all: rewrite cm_emit_stmt_length__stmt_capacity in PreH22.
  all: exact PreH22.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_30_split_goal_2 : cmc_emit_stmt_which_implies_wit_30_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  all: destruct s; cbn [cm_stmt_expr cm_stmt_first cm_stmt_second cm_rep_stmt_slot] in *; try discriminate.
  all: subst f.
  all: rewrite !cm_emit_stmt_length__stmt_capacity in *.
  all: rewrite ?cm_expr_rvalue_length__stmt_capacity.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try assumption.
  all: try (apply cm_slot_type_encode__statement_normalization_safety; lia).
  all: try (unfold cm_binding_valid; tauto).
  all: unfold cm_i32_code_count in *.
  all: unfold cm_imax in *.
  all: unfold cm_expr_temps_for; cbn [Z.eqb].
  all: repeat match goal with H : context [Z.max ?a ?b] |- _ => destruct (Z.max_spec a b) as [[? Hmax]|[? Hmax]]; rewrite Hmax in *; clear Hmax end.
  all: try lia.
  all: repeat match goal with
  | H : cm_stmt_counts_representable ?pol ?pr ?fi ?a |- _ =>
    let Hn := fresh in pose proof (cm_stmt_count_nonnegative__stmt_capacity pol pr fi a) as Hn; clear H
  | H : cm_expr_counts_representable ?pol ?pr ?fi ?e |- _ =>
    let Hn := fresh in pose proof (cm_rvalue_count_nonnegative__stmt_capacity pol pr fi e) as Hn; clear H
  end.
  all: try lia.
  all: repeat match goal with H : context [cm_char_normalize_count ?ty] |- _ => destruct ty; cbn [cm_char_normalize_count] in * end.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_30_split_goal_3 : cmc_emit_stmt_which_implies_wit_30_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  all: destruct s; cbn [cm_stmt_expr cm_stmt_first cm_stmt_second cm_rep_stmt_slot] in *; try discriminate.
  all: subst f.
  all: rewrite !cm_emit_stmt_length__stmt_capacity in *.
  all: rewrite ?cm_expr_rvalue_length__stmt_capacity.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try assumption.
  all: try (apply cm_slot_type_encode__statement_normalization_safety; lia).
  all: try (unfold cm_binding_valid; tauto).
  all: unfold cm_i32_code_count in *.
  all: unfold cm_imax in *.
  all: unfold cm_expr_temps_for; cbn [Z.eqb].
  all: repeat match goal with H : context [Z.max ?a ?b] |- _ => destruct (Z.max_spec a b) as [[? Hmax]|[? Hmax]]; rewrite Hmax in *; clear Hmax end.
  all: try lia.
  all: repeat match goal with
  | H : cm_stmt_counts_representable ?pol ?pr ?fi ?a |- _ =>
    let Hn := fresh in pose proof (cm_stmt_count_nonnegative__stmt_capacity pol pr fi a) as Hn; clear H
  | H : cm_expr_counts_representable ?pol ?pr ?fi ?e |- _ =>
    let Hn := fresh in pose proof (cm_rvalue_count_nonnegative__stmt_capacity pol pr fi e) as Hn; clear H
  end.
  all: try lia.
  all: repeat match goal with H : context [cm_char_normalize_count ?ty] |- _ => destruct ty; cbn [cm_char_normalize_count] in * end.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_30_split_goal_4 : cmc_emit_stmt_which_implies_wit_30_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
  all: destruct s; cbn [cm_stmt_expr cm_stmt_first cm_stmt_second cm_rep_stmt_slot] in *; try discriminate.
  all: subst f.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_30_split_goal_5 : cmc_emit_stmt_which_implies_wit_30_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia).
  all: destruct s; cbn [cm_stmt_expr cm_stmt_first cm_stmt_second cm_rep_stmt_slot] in *; try discriminate.
  all: subst f.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_30 : cmc_emit_stmt_which_implies_wit_30.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_30_split_goal_1.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_30_split_goal_2.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_30_split_goal_3.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_30_split_goal_4.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_30_split_goal_5.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_31_split_goal_spatial : cmc_emit_stmt_which_implies_wit_31_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct s; cbn [cm_stmt_first cm_stmt_second] in *; try discriminate.
  cbn [cm_emit_stmt].
  repeat rewrite app_assoc.
  cancel.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_31 : cmc_emit_stmt_which_implies_wit_31.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_31_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_32_split_goal_spatial : cmc_emit_stmt_which_implies_wit_32_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct s; cbn [cm_stmt_first cm_stmt_second] in *; try discriminate.
  cbn [cm_emit_stmt].
  repeat rewrite app_assoc.
  cancel.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_32 : cmc_emit_stmt_which_implies_wit_32.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_32_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_33_split_goal_spatial : cmc_emit_stmt_which_implies_wit_33_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (cm_stmt_rep_node stmt s).
  unfold cm_stmt_node.
  Exists xe xa xb.
  unfold cm_stmt_payload.
  rewrite PreH6.
  cbn [cm_stmt_first cm_stmt_second cm_stmt_expr].
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_33 : cmc_emit_stmt_which_implies_wit_33.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_33_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_34_split_goal_1 : cmc_emit_stmt_which_implies_wit_34_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct s; simpl in *; try lia; reflexivity.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_34 : cmc_emit_stmt_which_implies_wit_34.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_34_split_goal_1.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_35_split_goal_spatial : cmc_emit_stmt_which_implies_wit_35_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (cm_stmt_rep_node stmt s). unfold cm_stmt_node.
  Exists xe xa xb.
  split_pure_spatial; [sepcon_assoc_change; cancel | dump_pre_spatial; auto].
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_35 : cmc_emit_stmt_which_implies_wit_35.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_35_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_36_split_goal_1 : cmc_emit_stmt_which_implies_wit_36_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || reflexivity).
  destruct s; cbn [cm_rep_stmt_kind] in *; try discriminate.
  cbn [cm_stmt_payload cm_stmt_first cm_stmt_second cm_stmt_expr].
  Intros_p Hpayload.
  dump_pre_spatial. first [reflexivity | tauto].
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_36_split_goal_2 : cmc_emit_stmt_which_implies_wit_36_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || reflexivity).
  destruct s; cbn [cm_rep_stmt_kind] in *; try discriminate.
  cbn [cm_stmt_payload cm_stmt_first cm_stmt_second cm_stmt_expr].
  Intros_p Hpayload.
  dump_pre_spatial. first [reflexivity | tauto].
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_36_split_goal_3 : cmc_emit_stmt_which_implies_wit_36_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || reflexivity).
  destruct s; cbn [cm_rep_stmt_kind] in *; try discriminate.
  cbn [cm_stmt_payload cm_stmt_first cm_stmt_second cm_stmt_expr].
  Intros_p Hpayload.
  dump_pre_spatial. first [reflexivity | tauto].
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_36_split_goal_4 : cmc_emit_stmt_which_implies_wit_36_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || reflexivity).
  destruct s; cbn [cm_rep_stmt_kind] in *; try discriminate.
  cbn [cm_stmt_payload cm_stmt_first cm_stmt_second cm_stmt_expr].
  Intros_p Hpayload.
  dump_pre_spatial. first [reflexivity | tauto].
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_36_split_goal_5 : cmc_emit_stmt_which_implies_wit_36_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || reflexivity).
  destruct s; cbn [cm_rep_stmt_kind] in *; try discriminate.
  cbn [cm_stmt_payload cm_stmt_first cm_stmt_second cm_stmt_expr].
  Intros_p Hpayload.
  dump_pre_spatial. first [reflexivity | tauto].
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_36_split_goal_spatial : cmc_emit_stmt_which_implies_wit_36_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || reflexivity).
  destruct s; cbn [cm_rep_stmt_kind] in *; try discriminate.
  cbn [cm_stmt_payload cm_stmt_first cm_stmt_second cm_stmt_expr].
  Intros_p Hpayload.
  cancel.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_36 : cmc_emit_stmt_which_implies_wit_36.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_36_split_goal_spatial.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_36_split_goal_1.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_36_split_goal_2.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_36_split_goal_3.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_36_split_goal_4.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_36_split_goal_5.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_37_split_goal_1 : cmc_emit_stmt_which_implies_wit_37_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  all: cbn [tvm_opcode_code]; lia.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_37_split_goal_2 : cmc_emit_stmt_which_implies_wit_37_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  all: cbn [tvm_opcode_code]; lia.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_37_split_goal_3 : cmc_emit_stmt_which_implies_wit_37_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  all: cbn [tvm_opcode_code]; lia.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_37_split_goal_4 : cmc_emit_stmt_which_implies_wit_37_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
  all: cbn [tvm_opcode_code]; lia.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_37_split_goal_5 : cmc_emit_stmt_which_implies_wit_37_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia).
  all: rewrite cm_emit_stmt_length__stmt_capacity in PreH22.
  all: exact PreH22.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_37_split_goal_6 : cmc_emit_stmt_which_implies_wit_37_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia).
  all: destruct s; cbn [cm_stmt_expr cm_stmt_first cm_stmt_second cm_rep_stmt_slot] in *; try discriminate.
  all: subst f.
  all: rewrite !cm_emit_stmt_length__stmt_capacity in *.
  all: rewrite ?cm_expr_rvalue_length__stmt_capacity.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try assumption.
  all: try (apply cm_slot_type_encode__statement_normalization_safety; lia).
  all: try (unfold cm_binding_valid; tauto).
  all: unfold cm_i32_code_count in *.
  all: unfold cm_imax in *.
  all: unfold cm_expr_temps_for; cbn [Z.eqb].
  all: repeat match goal with H : context [Z.max ?a ?b] |- _ => destruct (Z.max_spec a b) as [[? Hmax]|[? Hmax]]; rewrite Hmax in *; clear Hmax end.
  all: try lia.
  all: repeat match goal with
  | H : cm_stmt_counts_representable ?pol ?pr ?fi ?a |- _ =>
    let Hn := fresh in pose proof (cm_stmt_count_nonnegative__stmt_capacity pol pr fi a) as Hn; clear H
  | H : cm_expr_counts_representable ?pol ?pr ?fi ?e |- _ =>
    let Hn := fresh in pose proof (cm_rvalue_count_nonnegative__stmt_capacity pol pr fi e) as Hn; clear H
  end.
  all: try lia.
  all: repeat match goal with H : context [cm_char_normalize_count ?ty] |- _ => destruct ty; cbn [cm_char_normalize_count] in * end.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_37_split_goal_7 : cmc_emit_stmt_which_implies_wit_37_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia).
  all: rewrite cm_emit_stmt_length__stmt_capacity in PreH22.
  all: exact PreH22.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_37_split_goal_8 : cmc_emit_stmt_which_implies_wit_37_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia).
  all: destruct s; cbn [cm_stmt_expr cm_stmt_first cm_stmt_second cm_rep_stmt_slot] in *; try discriminate.
  all: subst f.
  all: rewrite !cm_emit_stmt_length__stmt_capacity in *.
  all: rewrite ?cm_expr_rvalue_length__stmt_capacity.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try assumption.
  all: try (apply cm_slot_type_encode__statement_normalization_safety; lia).
  all: try (unfold cm_binding_valid; tauto).
  all: unfold cm_i32_code_count in *.
  all: unfold cm_imax in *.
  all: unfold cm_expr_temps_for; cbn [Z.eqb].
  all: repeat match goal with H : context [Z.max ?a ?b] |- _ => destruct (Z.max_spec a b) as [[? Hmax]|[? Hmax]]; rewrite Hmax in *; clear Hmax end.
  all: try lia.
  all: repeat match goal with
  | H : cm_stmt_counts_representable ?pol ?pr ?fi ?a |- _ =>
    let Hn := fresh in pose proof (cm_stmt_count_nonnegative__stmt_capacity pol pr fi a) as Hn; clear H
  | H : cm_expr_counts_representable ?pol ?pr ?fi ?e |- _ =>
    let Hn := fresh in pose proof (cm_rvalue_count_nonnegative__stmt_capacity pol pr fi e) as Hn; clear H
  end.
  all: try lia.
  all: repeat match goal with H : context [cm_char_normalize_count ?ty] |- _ => destruct ty; cbn [cm_char_normalize_count] in * end.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_37_split_goal_9 : cmc_emit_stmt_which_implies_wit_37_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia).
  all: destruct s; cbn [cm_stmt_expr cm_stmt_first cm_stmt_second cm_rep_stmt_slot] in *; try discriminate.
  all: subst f.
  all: rewrite !cm_emit_stmt_length__stmt_capacity in *.
  all: rewrite ?cm_expr_rvalue_length__stmt_capacity.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try assumption.
  all: try (apply cm_slot_type_encode__statement_normalization_safety; lia).
  all: try (unfold cm_binding_valid; tauto).
  all: unfold cm_i32_code_count in *.
  all: unfold cm_imax in *.
  all: unfold cm_expr_temps_for; cbn [Z.eqb].
  all: repeat match goal with H : context [Z.max ?a ?b] |- _ => destruct (Z.max_spec a b) as [[? Hmax]|[? Hmax]]; rewrite Hmax in *; clear Hmax end.
  all: try lia.
  all: repeat match goal with
  | H : cm_stmt_counts_representable ?pol ?pr ?fi ?a |- _ =>
    let Hn := fresh in pose proof (cm_stmt_count_nonnegative__stmt_capacity pol pr fi a) as Hn; clear H
  | H : cm_expr_counts_representable ?pol ?pr ?fi ?e |- _ =>
    let Hn := fresh in pose proof (cm_rvalue_count_nonnegative__stmt_capacity pol pr fi e) as Hn; clear H
  end.
  all: try lia.
  all: repeat match goal with H : context [cm_char_normalize_count ?ty] |- _ => destruct ty; cbn [cm_char_normalize_count] in * end.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_37_split_goal_10 : cmc_emit_stmt_which_implies_wit_37_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia).
  all: destruct s; cbn [cm_stmt_expr cm_stmt_first cm_stmt_second cm_rep_stmt_slot] in *; try discriminate.
  all: subst f.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_37_split_goal_11 : cmc_emit_stmt_which_implies_wit_37_split_goal_11.
Proof.
  LLM_pre_process ltac:(lia).
  all: destruct s; cbn [cm_stmt_expr cm_stmt_first cm_stmt_second cm_rep_stmt_slot] in *; try discriminate.
  all: subst f.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_37_split_goal_12 : cmc_emit_stmt_which_implies_wit_37_split_goal_12.
Proof.
  LLM_pre_process ltac:(lia).
  all: destruct s; cbn [cm_stmt_expr cm_stmt_first cm_stmt_second cm_rep_stmt_slot] in *; try discriminate.
  all: subst f.
  all: rewrite !cm_emit_stmt_length__stmt_capacity in *.
  all: rewrite ?cm_expr_rvalue_length__stmt_capacity.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try assumption.
  all: try (apply cm_slot_type_encode__statement_normalization_safety; lia).
  all: try (unfold cm_binding_valid; tauto).
  all: unfold cm_i32_code_count in *.
  all: unfold cm_imax in *.
  all: unfold cm_expr_temps_for; cbn [Z.eqb].
  all: repeat match goal with H : context [Z.max ?a ?b] |- _ => destruct (Z.max_spec a b) as [[? Hmax]|[? Hmax]]; rewrite Hmax in *; clear Hmax end.
  all: try lia.
  all: repeat match goal with
  | H : cm_stmt_counts_representable ?pol ?pr ?fi ?a |- _ =>
    let Hn := fresh in pose proof (cm_stmt_count_nonnegative__stmt_capacity pol pr fi a) as Hn; clear H
  | H : cm_expr_counts_representable ?pol ?pr ?fi ?e |- _ =>
    let Hn := fresh in pose proof (cm_rvalue_count_nonnegative__stmt_capacity pol pr fi e) as Hn; clear H
  end.
  all: try lia.
  all: repeat match goal with H : context [cm_char_normalize_count ?ty] |- _ => destruct ty; cbn [cm_char_normalize_count] in * end.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_37_split_goal_13 : cmc_emit_stmt_which_implies_wit_37_split_goal_13.
Proof.
  LLM_pre_process ltac:(lia).
  all: destruct s; cbn [cm_stmt_expr cm_stmt_first cm_stmt_second cm_rep_stmt_slot] in *; try discriminate.
  all: subst f.
  all: rewrite !cm_emit_stmt_length__stmt_capacity in *.
  all: rewrite ?cm_expr_rvalue_length__stmt_capacity.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try assumption.
  all: try (apply cm_slot_type_encode__statement_normalization_safety; lia).
  all: try (unfold cm_binding_valid; tauto).
  all: unfold cm_i32_code_count in *.
  all: unfold cm_imax in *.
  all: unfold cm_expr_temps_for; cbn [Z.eqb].
  all: repeat match goal with H : context [Z.max ?a ?b] |- _ => destruct (Z.max_spec a b) as [[? Hmax]|[? Hmax]]; rewrite Hmax in *; clear Hmax end.
  all: try lia.
  all: repeat match goal with
  | H : cm_stmt_counts_representable ?pol ?pr ?fi ?a |- _ =>
    let Hn := fresh in pose proof (cm_stmt_count_nonnegative__stmt_capacity pol pr fi a) as Hn; clear H
  | H : cm_expr_counts_representable ?pol ?pr ?fi ?e |- _ =>
    let Hn := fresh in pose proof (cm_rvalue_count_nonnegative__stmt_capacity pol pr fi e) as Hn; clear H
  end.
  all: try lia.
  all: repeat match goal with H : context [cm_char_normalize_count ?ty] |- _ => destruct ty; cbn [cm_char_normalize_count] in * end.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_37_split_goal_14 : cmc_emit_stmt_which_implies_wit_37_split_goal_14.
Proof.
  LLM_pre_process ltac:(lia).
  all: destruct s; cbn [cm_stmt_expr cm_stmt_first cm_stmt_second cm_rep_stmt_slot] in *; try discriminate.
  all: subst f.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_37_split_goal_15 : cmc_emit_stmt_which_implies_wit_37_split_goal_15.
Proof.
  LLM_pre_process ltac:(lia).
  all: destruct s; cbn [cm_stmt_expr cm_stmt_first cm_stmt_second cm_rep_stmt_slot] in *; try discriminate.
  all: subst f.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_37 : cmc_emit_stmt_which_implies_wit_37.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_37_split_goal_1.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_37_split_goal_2.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_37_split_goal_3.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_37_split_goal_4.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_37_split_goal_5.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_37_split_goal_6.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_37_split_goal_7.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_37_split_goal_8.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_37_split_goal_9.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_37_split_goal_10.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_37_split_goal_11.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_37_split_goal_12.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_37_split_goal_13.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_37_split_goal_14.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_37_split_goal_15.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_40_split_goal_spatial : cmc_emit_stmt_which_implies_wit_40_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct s; try discriminate.
  cbn [cm_stmt_expr cm_stmt_first] in *.
  subst guard_count body_count body_pc loop_end.
  cbn [cm_emit_stmt cm_stmt_code_count].
  match goal with
  | |- context [pc + (?a + 1 + ?b + 1)] =>
      replace (pc + (a + 1 + b + 1)) with (pc + a + b + 2) by lia
  end.
  repeat rewrite <- app_assoc.
  match goal with |- ?P |-- ?P => cancel P end.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_40 : cmc_emit_stmt_which_implies_wit_40.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_40_split_goal_spatial.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_41_split_goal_spatial : cmc_emit_stmt_which_implies_wit_41_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_41 : cmc_emit_stmt_which_implies_wit_41.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_41_split_goal_spatial.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_42_split_goal_spatial : cmc_emit_stmt_which_implies_wit_42_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_42 : cmc_emit_stmt_which_implies_wit_42.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_42_split_goal_spatial.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_43_split_goal_spatial : cmc_emit_stmt_which_implies_wit_43_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct s; cbn [cm_stmt_expr cm_stmt_first cm_rep_stmt_slot] in PreH1; try discriminate.
  cbn [cm_emit_stmt cm_stmt_expr cm_stmt_first cm_rep_stmt_slot cm_binding_address_code Z.eqb].
  cbn [cm_stmt_expr cm_stmt_first] in PreH2, PreH3.
  subst guard_count body_count body_pc loop_end.
  cbn [cm_stmt_code_count].
  match goal with |- context [pc + (?g + 1 + ?b + 1)] =>
    replace (pc + (g + 1 + b + 1)) with (pc + g + b + 2) by lia
  end.
  repeat rewrite <- List.app_assoc.
  reflexivity.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_43 : cmc_emit_stmt_which_implies_wit_43.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_43_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_44_split_goal_spatial : cmc_emit_stmt_which_implies_wit_44_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (cm_stmt_rep_node stmt s).
  unfold cm_stmt_node.
  Exists xe xa xb.
  unfold cm_stmt_payload.
  rewrite PreH6.
  cbn [cm_stmt_first cm_stmt_second cm_stmt_expr].
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_44 : cmc_emit_stmt_which_implies_wit_44.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_44_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_45_split_goal_1 : cmc_emit_stmt_which_implies_wit_45_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in *; try congruence.
  all: cbn [cm_stmt_payload cm_stmt_expr].
  all: Intros_p Hpayload.
  all: dump_pre_spatial.
  all: intuition congruence.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_45_split_goal_2 : cmc_emit_stmt_which_implies_wit_45_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in *; try congruence.
  all: cbn [cm_stmt_payload cm_stmt_expr].
  all: Intros_p Hpayload.
  all: dump_pre_spatial.
  all: intuition congruence.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_45_split_goal_3 : cmc_emit_stmt_which_implies_wit_45_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in *; try congruence.
  all: cbn [cm_stmt_payload cm_stmt_expr].
  all: Intros_p Hpayload.
  all: dump_pre_spatial.
  all: intuition congruence.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_45_split_goal_4 : cmc_emit_stmt_which_implies_wit_45_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in *; try congruence.
  all: cbn [cm_stmt_payload cm_stmt_expr].
  all: Intros_p Hpayload.
  all: dump_pre_spatial.
  all: intuition congruence.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_45_split_goal_5 : cmc_emit_stmt_which_implies_wit_45_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in *; try congruence.
  all: cbn [cm_stmt_payload cm_stmt_expr].
  all: Intros_p Hpayload.
  all: dump_pre_spatial.
  all: intuition congruence.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_45_split_goal_6 : cmc_emit_stmt_which_implies_wit_45_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in *; try congruence.
  all: cbn [cm_stmt_payload cm_stmt_expr].
  all: Intros_p Hpayload.
  all: dump_pre_spatial.
  all: intuition congruence.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_45_split_goal_7 : cmc_emit_stmt_which_implies_wit_45_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in *; try congruence.
  all: cbn [cm_stmt_payload cm_stmt_expr].
  all: Intros_p Hpayload.
  all: dump_pre_spatial.
  all: intuition congruence.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_45_split_goal_spatial : cmc_emit_stmt_which_implies_wit_45_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in *; try congruence.
  all: cbn [cm_stmt_payload cm_stmt_expr].
  all: Intros_p Hpayload.
  all: cancel.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_45 : cmc_emit_stmt_which_implies_wit_45.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_45_split_goal_spatial.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_45_split_goal_1.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_45_split_goal_2.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_45_split_goal_3.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_45_split_goal_4.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_45_split_goal_5.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_45_split_goal_6.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_45_split_goal_7.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_46_split_goal_1 : cmc_emit_stmt_which_implies_wit_46_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; congruence).
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_46_split_goal_2 : cmc_emit_stmt_which_implies_wit_46_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; congruence).
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_46_split_goal_3 : cmc_emit_stmt_which_implies_wit_46_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  try match goal with H : ?s = CMDeclS _ |- _ => rewrite H in * end.
  subst.
  cbn [cm_emit_stmt cm_stmt_code_count Zlength] in *.
  assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_46 : cmc_emit_stmt_which_implies_wit_46.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_46_split_goal_1.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_46_split_goal_2.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_46_split_goal_3.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_47_split_goal_spatial : cmc_emit_stmt_which_implies_wit_47_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH1. cbn [cm_emit_stmt app].
  rewrite ?app_nil_r.
  cancel (cm_resolved_emitter_plan_rep policy p emitter out capacity done (TVMInst TVMJmpOp break_pc :: tail)).
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_47 : cmc_emit_stmt_which_implies_wit_47.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_47_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_48_split_goal_spatial : cmc_emit_stmt_which_implies_wit_48_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct s; cbn [cm_stmt_expr cm_stmt_first cm_rep_stmt_slot] in PreH1; try discriminate.
  cbn [cm_emit_stmt cm_stmt_expr cm_stmt_first cm_rep_stmt_slot cm_binding_address_code Z.eqb].
  repeat rewrite <- List.app_assoc.
  reflexivity.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_48 : cmc_emit_stmt_which_implies_wit_48.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_48_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_49_split_goal_spatial : cmc_emit_stmt_which_implies_wit_49_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_stmt_rep_node. unfold cm_stmt_node.
  Exists xe xa xb.
  rewrite PreH6. cbn [cm_stmt_payload cm_stmt_expr].
  split_pure_spatial; try (repeat progress cancel); try (split_pures; dump_pre_spatial; intuition).
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_49 : cmc_emit_stmt_which_implies_wit_49.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_49_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_50_split_goal_1 : cmc_emit_stmt_which_implies_wit_50_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in *; try congruence.
  all: cbn [cm_stmt_payload cm_stmt_expr].
  all: Intros_p Hpayload.
  all: dump_pre_spatial.
  all: intuition congruence.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_50_split_goal_2 : cmc_emit_stmt_which_implies_wit_50_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in *; try congruence.
  all: cbn [cm_stmt_payload cm_stmt_expr].
  all: Intros_p Hpayload.
  all: dump_pre_spatial.
  all: intuition congruence.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_50_split_goal_3 : cmc_emit_stmt_which_implies_wit_50_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in *; try congruence.
  all: cbn [cm_stmt_payload cm_stmt_expr].
  all: Intros_p Hpayload.
  all: dump_pre_spatial.
  all: intuition congruence.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_50_split_goal_4 : cmc_emit_stmt_which_implies_wit_50_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in *; try congruence.
  all: cbn [cm_stmt_payload cm_stmt_expr].
  all: Intros_p Hpayload.
  all: dump_pre_spatial.
  all: intuition congruence.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_50_split_goal_5 : cmc_emit_stmt_which_implies_wit_50_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in *; try congruence.
  all: cbn [cm_stmt_payload cm_stmt_expr].
  all: Intros_p Hpayload.
  all: dump_pre_spatial.
  all: intuition congruence.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_50_split_goal_6 : cmc_emit_stmt_which_implies_wit_50_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in *; try congruence.
  all: cbn [cm_stmt_payload cm_stmt_expr].
  all: Intros_p Hpayload.
  all: dump_pre_spatial.
  all: intuition congruence.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_50_split_goal_7 : cmc_emit_stmt_which_implies_wit_50_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in *; try congruence.
  all: cbn [cm_stmt_payload cm_stmt_expr].
  all: Intros_p Hpayload.
  all: dump_pre_spatial.
  all: intuition congruence.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_50_split_goal_spatial : cmc_emit_stmt_which_implies_wit_50_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in *; try congruence.
  all: cbn [cm_stmt_payload cm_stmt_expr].
  all: Intros_p Hpayload.
  all: cancel.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_50 : cmc_emit_stmt_which_implies_wit_50.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_50_split_goal_spatial.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_50_split_goal_1.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_50_split_goal_2.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_50_split_goal_3.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_50_split_goal_4.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_50_split_goal_5.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_50_split_goal_6.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_50_split_goal_7.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_51_split_goal_1 : cmc_emit_stmt_which_implies_wit_51_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; congruence).
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_51_split_goal_2 : cmc_emit_stmt_which_implies_wit_51_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; congruence).
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_51_split_goal_3 : cmc_emit_stmt_which_implies_wit_51_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  try match goal with H : ?s = CMDeclS _ |- _ => rewrite H in * end.
  subst.
  cbn [cm_emit_stmt cm_stmt_code_count Zlength] in *.
  assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_51 : cmc_emit_stmt_which_implies_wit_51.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_51_split_goal_1.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_51_split_goal_2.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_51_split_goal_3.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_52_split_goal_spatial : cmc_emit_stmt_which_implies_wit_52_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH1. cbn [cm_emit_stmt app].
  rewrite ?app_nil_r.
  cancel (cm_resolved_emitter_plan_rep policy p emitter out capacity done (TVMInst TVMJmpOp continue_pc :: tail)).
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_52 : cmc_emit_stmt_which_implies_wit_52.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_52_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_53_split_goal_spatial : cmc_emit_stmt_which_implies_wit_53_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct s; cbn [cm_stmt_expr cm_stmt_first cm_rep_stmt_slot] in PreH1; try discriminate.
  cbn [cm_emit_stmt cm_stmt_expr cm_stmt_first cm_rep_stmt_slot cm_binding_address_code Z.eqb].
  repeat rewrite <- List.app_assoc.
  reflexivity.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_53 : cmc_emit_stmt_which_implies_wit_53.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_53_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_54_split_goal_spatial : cmc_emit_stmt_which_implies_wit_54_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_stmt_rep_node. unfold cm_stmt_node.
  Exists xe xa xb.
  rewrite PreH6. cbn [cm_stmt_payload cm_stmt_expr].
  split_pure_spatial; try (repeat progress cancel); try (split_pures; dump_pre_spatial; intuition).
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_54 : cmc_emit_stmt_which_implies_wit_54.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_54_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_55_split_goal_1 : cmc_emit_stmt_which_implies_wit_55_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in *; try congruence.
  all: cbn [cm_stmt_payload cm_stmt_expr].
  all: Intros_p Hpayload.
  all: dump_pre_spatial.
  all: intuition congruence.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_55_split_goal_2 : cmc_emit_stmt_which_implies_wit_55_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in *; try congruence.
  all: cbn [cm_stmt_payload cm_stmt_expr].
  all: Intros_p Hpayload.
  all: dump_pre_spatial.
  all: intuition congruence.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_55_split_goal_3 : cmc_emit_stmt_which_implies_wit_55_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in *; try congruence.
  all: cbn [cm_stmt_payload cm_stmt_expr].
  all: Intros_p Hpayload.
  all: dump_pre_spatial.
  all: intuition congruence.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_55_split_goal_4 : cmc_emit_stmt_which_implies_wit_55_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in *; try congruence.
  all: cbn [cm_stmt_payload cm_stmt_expr].
  all: Intros_p Hpayload.
  all: dump_pre_spatial.
  all: intuition congruence.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_55_split_goal_5 : cmc_emit_stmt_which_implies_wit_55_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in *; try congruence.
  all: cbn [cm_stmt_payload cm_stmt_expr].
  all: Intros_p Hpayload.
  all: dump_pre_spatial.
  all: intuition congruence.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_55_split_goal_6 : cmc_emit_stmt_which_implies_wit_55_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in *; try congruence.
  all: cbn [cm_stmt_payload cm_stmt_expr].
  all: Intros_p Hpayload.
  all: dump_pre_spatial.
  all: intuition congruence.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_55_split_goal_spatial : cmc_emit_stmt_which_implies_wit_55_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; cbn [cm_rep_stmt_kind] in *; try congruence.
  all: cbn [cm_stmt_payload cm_stmt_expr].
  all: Intros_p Hpayload.
  all: cancel.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_55 : cmc_emit_stmt_which_implies_wit_55.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_55_split_goal_spatial.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_55_split_goal_1.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_55_split_goal_2.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_55_split_goal_3.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_55_split_goal_4.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_55_split_goal_5.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_55_split_goal_6.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_56_split_goal_1 : cmc_emit_stmt_which_implies_wit_56_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  all: destruct s; cbn [cm_stmt_expr cm_stmt_first cm_stmt_second cm_rep_stmt_slot] in *; try discriminate.
  all: subst f.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_56_split_goal_2 : cmc_emit_stmt_which_implies_wit_56_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  all: rewrite cm_emit_stmt_length__stmt_capacity in PreH22.
  all: exact PreH22.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_56_split_goal_3 : cmc_emit_stmt_which_implies_wit_56_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  all: destruct s; cbn [cm_stmt_expr cm_stmt_first cm_stmt_second cm_rep_stmt_slot] in *; try discriminate.
  all: subst f.
  all: rewrite !cm_emit_stmt_length__stmt_capacity in *.
  all: rewrite ?cm_expr_rvalue_length__stmt_capacity.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try assumption.
  all: try (apply cm_slot_type_encode__statement_normalization_safety; lia).
  all: try (unfold cm_binding_valid; tauto).
  all: unfold cm_i32_code_count in *.
  all: unfold cm_imax in *.
  all: unfold cm_expr_temps_for; cbn [Z.eqb].
  all: repeat match goal with H : context [Z.max ?a ?b] |- _ => destruct (Z.max_spec a b) as [[? Hmax]|[? Hmax]]; rewrite Hmax in *; clear Hmax end.
  all: try lia.
  all: repeat match goal with
  | H : cm_stmt_counts_representable ?pol ?pr ?fi ?a |- _ =>
    let Hn := fresh in pose proof (cm_stmt_count_nonnegative__stmt_capacity pol pr fi a) as Hn; clear H
  | H : cm_expr_counts_representable ?pol ?pr ?fi ?e |- _ =>
    let Hn := fresh in pose proof (cm_rvalue_count_nonnegative__stmt_capacity pol pr fi e) as Hn; clear H
  end.
  all: try lia.
  all: repeat match goal with H : context [cm_char_normalize_count ?ty] |- _ => destruct ty; cbn [cm_char_normalize_count] in * end.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_56_split_goal_4 : cmc_emit_stmt_which_implies_wit_56_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
  all: destruct s; cbn [cm_stmt_expr cm_stmt_first cm_stmt_second cm_rep_stmt_slot] in *; try discriminate.
  all: subst f.
  all: rewrite !cm_emit_stmt_length__stmt_capacity in *.
  all: rewrite ?cm_expr_rvalue_length__stmt_capacity.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try assumption.
  all: try (apply cm_slot_type_encode__statement_normalization_safety; lia).
  all: try (unfold cm_binding_valid; tauto).
  all: unfold cm_i32_code_count in *.
  all: unfold cm_imax in *.
  all: unfold cm_expr_temps_for; cbn [Z.eqb].
  all: repeat match goal with H : context [Z.max ?a ?b] |- _ => destruct (Z.max_spec a b) as [[? Hmax]|[? Hmax]]; rewrite Hmax in *; clear Hmax end.
  all: try lia.
  all: repeat match goal with
  | H : cm_stmt_counts_representable ?pol ?pr ?fi ?a |- _ =>
    let Hn := fresh in pose proof (cm_stmt_count_nonnegative__stmt_capacity pol pr fi a) as Hn; clear H
  | H : cm_expr_counts_representable ?pol ?pr ?fi ?e |- _ =>
    let Hn := fresh in pose proof (cm_rvalue_count_nonnegative__stmt_capacity pol pr fi e) as Hn; clear H
  end.
  all: try lia.
  all: repeat match goal with H : context [cm_char_normalize_count ?ty] |- _ => destruct ty; cbn [cm_char_normalize_count] in * end.
  all: lia.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_56_split_goal_5 : cmc_emit_stmt_which_implies_wit_56_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia).
  all: destruct s; cbn [cm_stmt_expr cm_stmt_first cm_stmt_second cm_rep_stmt_slot] in *; try discriminate.
  all: subst f.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_56_split_goal_6 : cmc_emit_stmt_which_implies_wit_56_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia).
  all: destruct s; cbn [cm_stmt_expr cm_stmt_first cm_stmt_second cm_rep_stmt_slot] in *; try discriminate.
  all: subst f.
  all: cbn [cm_stmt_wf cm_stmt_counts_representable cm_stmt_code_count cm_stemps cm_expr_temps_for] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: assumption.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_56 : cmc_emit_stmt_which_implies_wit_56.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_56_split_goal_1.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_56_split_goal_2.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_56_split_goal_3.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_56_split_goal_4.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_56_split_goal_5.
  - Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_56_split_goal_6.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_57 : cmc_emit_stmt_which_implies_wit_57.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_function_context_rep.
  Intros zp zl.
  Exists zl zp.
  split_pure_spatial; [repeat progress cancel | dump_pre_spatial; assumption].
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_58_split_goal_spatial : cmc_emit_stmt_which_implies_wit_58_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_function_context_rep.
  Exists zp zl.
  split_pure_spatial; [repeat progress cancel | dump_pre_spatial; assumption].
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_58 : cmc_emit_stmt_which_implies_wit_58.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_58_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_59_split_goal_spatial : cmc_emit_stmt_which_implies_wit_59_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  destruct s; try discriminate.
  subst f.
  cbn [cm_emit_stmt cm_stmt_expr cm_rep_stmt_slot cm_binding_address_code].
  repeat rewrite <- app_assoc.
  cancel.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_59 : cmc_emit_stmt_which_implies_wit_59.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_59_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_60_split_goal_spatial : cmc_emit_stmt_which_implies_wit_60_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct s; cbn [cm_stmt_expr cm_stmt_first cm_rep_stmt_slot] in PreH1; try discriminate.
  subst f.
  cbn [cm_emit_stmt cm_stmt_expr cm_stmt_first cm_rep_stmt_slot cm_binding_address_code Z.eqb].
  repeat rewrite <- List.app_assoc.
  reflexivity.
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_60 : cmc_emit_stmt_which_implies_wit_60.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_60_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_stmt_which_implies_wit_61_split_goal_spatial : cmc_emit_stmt_which_implies_wit_61_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_stmt_rep_node. unfold cm_stmt_node.
  Exists xe xa xb.
  rewrite PreH6. cbn [cm_stmt_payload cm_stmt_expr].
  split_pure_spatial; try (repeat progress cancel); try (split_pures; dump_pre_spatial; intuition).
Qed.

Lemma proof_of_cmc_emit_stmt_which_implies_wit_61 : cmc_emit_stmt_which_implies_wit_61.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_stmt_which_implies_wit_61_split_goal_spatial.
Qed. 

