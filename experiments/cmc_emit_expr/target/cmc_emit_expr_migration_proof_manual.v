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
From SimpleC.EE.QCP_demos_human Require Import cmc_emit_expr_migration_goal.
From SimpleC.EE.QCP_demos_human Require Import cmc_emit_expr_migration_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.cmc_emit_expr_migration_lib.
Local Open Scope sac.

Lemma proof_of_cm_emit_intrinsic_expr_return_wit_1_split_goal_spatial : cm_emit_intrinsic_expr_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hlvalue : lvalue_pre = 0) by lia.
  subst lvalue_pre.
  destruct e; cbn [cm_intrinsic_expr cm_rep_expr_kind] in *;
    try contradiction; try discriminate; try congruence.
  unfold cm_expr_code_for.
  cbn [Z.eqb cm_emit_expr_pair cm_expr_child cm_rcode_of cm_lcode_of].
  repeat rewrite <- app_assoc.
  cbn [app].
  repeat rewrite app_nil_r.
  cancel.
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_return_wit_1 : cm_emit_intrinsic_expr_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_intrinsic_expr_return_wit_1_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_intrinsic_expr_return_wit_2_split_goal_spatial : cm_emit_intrinsic_expr_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hlvalue : lvalue_pre = 1) by lia.
  subst lvalue_pre.
  destruct e; cbn [cm_intrinsic_expr cm_rep_expr_kind] in *;
    try contradiction; try discriminate; try congruence.
  unfold cm_expr_code_for.
  cbn [Z.eqb cm_emit_expr_pair cm_expr_child cm_rcode_of cm_lcode_of].
  repeat rewrite <- app_assoc.
  cbn [app].
  repeat rewrite app_nil_r.
  cancel.
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_return_wit_2 : cm_emit_intrinsic_expr_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_intrinsic_expr_return_wit_2_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_intrinsic_expr_return_wit_3_split_goal_spatial : cm_emit_intrinsic_expr_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hlvalue : lvalue_pre = 0) by lia.
  subst lvalue_pre.
  destruct e; cbn [cm_intrinsic_expr cm_rep_expr_kind] in *;
    try contradiction; try discriminate; try congruence.
  unfold cm_expr_code_for.
  cbn [Z.eqb cm_emit_expr_pair cm_expr_child cm_rcode_of cm_lcode_of].
  repeat rewrite <- app_assoc.
  cbn [app].
  repeat rewrite app_nil_r.
  cancel.
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_return_wit_3 : cm_emit_intrinsic_expr_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_intrinsic_expr_return_wit_3_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_intrinsic_expr_return_wit_4_split_goal_spatial : cm_emit_intrinsic_expr_return_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hlvalue : lvalue_pre = 1) by lia.
  subst lvalue_pre.
  destruct e; cbn [cm_intrinsic_expr cm_rep_expr_kind] in *;
    try contradiction; try discriminate; try congruence.
  unfold cm_expr_code_for.
  cbn [Z.eqb cm_emit_expr_pair cm_expr_child cm_rcode_of cm_lcode_of].
  repeat rewrite <- app_assoc.
  cbn [app].
  repeat rewrite app_nil_r.
  cancel.
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_return_wit_4 : cm_emit_intrinsic_expr_return_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_intrinsic_expr_return_wit_4_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_intrinsic_expr_return_wit_5_split_goal_spatial : cm_emit_intrinsic_expr_return_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hlvalue : lvalue_pre = 0) by lia.
  subst lvalue_pre.
  destruct e; cbn [cm_intrinsic_expr cm_rep_expr_kind] in *;
    try contradiction; try discriminate; try congruence.
  unfold cm_expr_code_for.
  cbn [Z.eqb cm_emit_expr_pair cm_expr_child cm_rcode_of cm_lcode_of].
  repeat rewrite <- app_assoc.
  cbn [app].
  repeat rewrite app_nil_r.
  cancel.
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_return_wit_5 : cm_emit_intrinsic_expr_return_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_intrinsic_expr_return_wit_5_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_intrinsic_expr_return_wit_6_split_goal_spatial : cm_emit_intrinsic_expr_return_wit_6_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hlvalue : lvalue_pre = 1) by lia.
  subst lvalue_pre.
  destruct e; cbn [cm_intrinsic_expr cm_rep_expr_kind] in *;
    try contradiction; try discriminate; try congruence.
  unfold cm_expr_code_for.
  cbn [Z.eqb cm_emit_expr_pair cm_expr_child cm_rcode_of cm_lcode_of].
  repeat rewrite <- app_assoc.
  cbn [app].
  repeat rewrite app_nil_r.
  cancel.
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_return_wit_6 : cm_emit_intrinsic_expr_return_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_intrinsic_expr_return_wit_6_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_intrinsic_expr_partial_solve_wit_7_pure_split_goal_1 : cm_emit_intrinsic_expr_partial_solve_wit_7_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn; lia).
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_partial_solve_wit_7_pure_split_goal_2 : cm_emit_intrinsic_expr_partial_solve_wit_7_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn; lia).
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_partial_solve_wit_7_pure : cm_emit_intrinsic_expr_partial_solve_wit_7_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_intrinsic_expr_partial_solve_wit_7_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_intrinsic_expr_partial_solve_wit_7_pure_split_goal_2.
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_partial_solve_wit_8_pure_split_goal_1 : cm_emit_intrinsic_expr_partial_solve_wit_8_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn; lia).
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_partial_solve_wit_8_pure_split_goal_2 : cm_emit_intrinsic_expr_partial_solve_wit_8_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn; lia).
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_partial_solve_wit_8_pure : cm_emit_intrinsic_expr_partial_solve_wit_8_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_intrinsic_expr_partial_solve_wit_8_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_intrinsic_expr_partial_solve_wit_8_pure_split_goal_2.
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_partial_solve_wit_13_pure_split_goal_1 : cm_emit_intrinsic_expr_partial_solve_wit_13_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn; lia).
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_partial_solve_wit_13_pure_split_goal_2 : cm_emit_intrinsic_expr_partial_solve_wit_13_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn; lia).
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_partial_solve_wit_13_pure : cm_emit_intrinsic_expr_partial_solve_wit_13_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_intrinsic_expr_partial_solve_wit_13_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_intrinsic_expr_partial_solve_wit_13_pure_split_goal_2.
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_partial_solve_wit_14_pure_split_goal_1 : cm_emit_intrinsic_expr_partial_solve_wit_14_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn; lia).
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_partial_solve_wit_14_pure_split_goal_2 : cm_emit_intrinsic_expr_partial_solve_wit_14_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn; lia).
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_partial_solve_wit_14_pure : cm_emit_intrinsic_expr_partial_solve_wit_14_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_intrinsic_expr_partial_solve_wit_14_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_intrinsic_expr_partial_solve_wit_14_pure_split_goal_2.
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_partial_solve_wit_19_pure_split_goal_1 : cm_emit_intrinsic_expr_partial_solve_wit_19_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn; lia).
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_partial_solve_wit_19_pure_split_goal_2 : cm_emit_intrinsic_expr_partial_solve_wit_19_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn; lia).
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_partial_solve_wit_19_pure : cm_emit_intrinsic_expr_partial_solve_wit_19_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_intrinsic_expr_partial_solve_wit_19_pure_split_goal_1.
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_partial_solve_wit_20_pure_split_goal_1 : cm_emit_intrinsic_expr_partial_solve_wit_20_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn; lia).
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_partial_solve_wit_20_pure_split_goal_2 : cm_emit_intrinsic_expr_partial_solve_wit_20_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn; lia).
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_partial_solve_wit_20_pure : cm_emit_intrinsic_expr_partial_solve_wit_20_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_intrinsic_expr_partial_solve_wit_20_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_intrinsic_expr_partial_solve_wit_20_pure_split_goal_2.
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_which_implies_wit_1 : cm_emit_intrinsic_expr_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn [cm_intrinsic_expr] in *; try contradiction.
  all: rewrite cm_expr_rep_node; unfold cm_expr_node;
    cbn [cm_expr_payload cm_expr_child];
    Intros xa xb xargs; Exists xargs xb xa;
    split_pure_spatial; [repeat progress cancel | split_pures; dump_pre_spatial; tauto].
Qed. 

Lemma proof_of_cm_emit_intrinsic_expr_which_implies_wit_2_split_goal_1 : cm_emit_intrinsic_expr_which_implies_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  intros.
  destruct e; cbn [cm_intrinsic_expr] in PreH22; try contradiction;
  cbn [cm_expr_child cm_expr_type cm_expr_wf cm_expr_counts_representable] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try reflexivity; try assumption.
  all: try (eapply cm_expr_type_refs__constructor_facts_a; eauto).
  all: try match goal with H : cm_expr_counts_representable ?pol ?p ?fid ?e |- _ =>
    pose proof (cm_expr_node_facts__constructor_facts_a pol p fid e H) end.
  all: unfold cm_expr_count_node_representable in *; intuition subst; cbn in *; auto.
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_which_implies_wit_2_split_goal_2 : cm_emit_intrinsic_expr_which_implies_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  intros.
  destruct e; cbn [cm_intrinsic_expr] in PreH22; try contradiction;
  cbn [cm_expr_child cm_expr_type cm_expr_wf cm_expr_counts_representable] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try reflexivity; try assumption.
  all: try (eapply cm_expr_type_refs__constructor_facts_a; eauto).
  all: try match goal with H : cm_expr_counts_representable ?pol ?p ?fid ?e |- _ =>
    pose proof (cm_expr_node_facts__constructor_facts_a pol p fid e H) end.
  all: unfold cm_expr_count_node_representable in *; intuition subst; cbn in *; auto.
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_which_implies_wit_2_split_goal_3 : cm_emit_intrinsic_expr_which_implies_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  intros.
  destruct e; cbn [cm_intrinsic_expr] in PreH22; try contradiction;
  cbn [cm_expr_child cm_expr_type cm_expr_wf cm_expr_counts_representable] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try reflexivity; try assumption.
  all: try (eapply cm_expr_type_refs__constructor_facts_a; eauto).
  all: try match goal with H : cm_expr_counts_representable ?pol ?p ?fid ?e |- _ =>
    pose proof (cm_expr_node_facts__constructor_facts_a pol p fid e H) end.
  all: unfold cm_expr_count_node_representable in *; intuition subst; cbn in *; auto.
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_which_implies_wit_2_split_goal_4 : cm_emit_intrinsic_expr_which_implies_wit_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
  intros.
  destruct e; cbn [cm_intrinsic_expr] in PreH22; try contradiction;
  cbn [cm_expr_child cm_expr_type cm_expr_wf cm_expr_counts_representable] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try reflexivity; try assumption.
  all: try (eapply cm_expr_type_refs__constructor_facts_a; eauto).
  all: try match goal with H : cm_expr_counts_representable ?pol ?p ?fid ?e |- _ =>
    pose proof (cm_expr_node_facts__constructor_facts_a pol p fid e H) end.
  all: unfold cm_expr_count_node_representable in *; intuition subst; cbn in *; auto.
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_which_implies_wit_2_split_goal_5 : cm_emit_intrinsic_expr_which_implies_wit_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia).
  intros.
  destruct e; cbn [cm_intrinsic_expr] in PreH22; try contradiction;
  cbn [cm_expr_child cm_expr_type cm_expr_wf cm_expr_counts_representable] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try reflexivity; try assumption.
  all: try (eapply cm_expr_type_refs__constructor_facts_a; eauto).
  all: try match goal with H : cm_expr_counts_representable ?pol ?p ?fid ?e |- _ =>
    pose proof (cm_expr_node_facts__constructor_facts_a pol p fid e H) end.
  all: unfold cm_expr_count_node_representable in *; intuition subst; cbn in *; auto.
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_which_implies_wit_2_split_goal_6 : cm_emit_intrinsic_expr_which_implies_wit_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia).
  intros.
  destruct e; cbn [cm_intrinsic_expr] in PreH22; try contradiction;
  cbn [cm_expr_child cm_expr_type cm_expr_wf cm_expr_counts_representable] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try reflexivity; try assumption.
  all: try (eapply cm_expr_type_refs__constructor_facts_a; eauto).
  all: try match goal with H : cm_expr_counts_representable ?pol ?p ?fid ?e |- _ =>
    pose proof (cm_expr_node_facts__constructor_facts_a pol p fid e H) end.
  all: unfold cm_expr_count_node_representable in *; intuition subst; cbn in *; auto.
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_which_implies_wit_2_split_goal_7 : cm_emit_intrinsic_expr_which_implies_wit_2_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia).
  intros.
  destruct e; cbn [cm_intrinsic_expr] in PreH22; try contradiction;
  cbn [cm_expr_child cm_expr_type cm_expr_wf cm_expr_counts_representable] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try reflexivity; try assumption.
  all: try (eapply cm_expr_type_refs__constructor_facts_a; eauto).
  all: try match goal with H : cm_expr_counts_representable ?pol ?p ?fid ?e |- _ =>
    pose proof (cm_expr_node_facts__constructor_facts_a pol p fid e H) end.
  all: unfold cm_expr_count_node_representable in *; intuition subst; cbn in *; auto.
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_which_implies_wit_2_split_goal_8 : cm_emit_intrinsic_expr_which_implies_wit_2_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia).
  intros.
  unfold cm_temp_offset in *. lia.
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_which_implies_wit_2_split_goal_9 : cm_emit_intrinsic_expr_which_implies_wit_2_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia).
  intros.
  pose proof (cm_slots_size_nonnegative__call_bounds _ _ PreH6).
  pose proof (cm_slots_size_nonnegative__call_bounds _ _ PreH7).
  unfold cm_temp_offset in *. rewrite <- PreH5 in *. lia.
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_which_implies_wit_2 : cm_emit_intrinsic_expr_which_implies_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_intrinsic_expr_which_implies_wit_2_split_goal_1.
  - Goal_apply proof_of_cm_emit_intrinsic_expr_which_implies_wit_2_split_goal_2.
  - Goal_apply proof_of_cm_emit_intrinsic_expr_which_implies_wit_2_split_goal_3.
  - Goal_apply proof_of_cm_emit_intrinsic_expr_which_implies_wit_2_split_goal_4.
  - Goal_apply proof_of_cm_emit_intrinsic_expr_which_implies_wit_2_split_goal_5.
  - Goal_apply proof_of_cm_emit_intrinsic_expr_which_implies_wit_2_split_goal_6.
  - Goal_apply proof_of_cm_emit_intrinsic_expr_which_implies_wit_2_split_goal_7.
  - Goal_apply proof_of_cm_emit_intrinsic_expr_which_implies_wit_2_split_goal_8.
  - Goal_apply proof_of_cm_emit_intrinsic_expr_which_implies_wit_2_split_goal_9.
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_which_implies_wit_3_split_goal_1 : cm_emit_intrinsic_expr_which_implies_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn [cm_rep_expr_kind cm_intrinsic_expr] in *;
    try contradiction; try discriminate.
  unfold cm_expr_shape.
  reflexivity.
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_which_implies_wit_3 : cm_emit_intrinsic_expr_which_implies_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_intrinsic_expr_which_implies_wit_3_split_goal_1.
Qed. 

Lemma proof_of_cm_emit_intrinsic_expr_which_implies_wit_4_split_goal_spatial : cm_emit_intrinsic_expr_which_implies_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (lvalue = 0) by lia.
  subst lvalue.
  destruct e; cbn [cm_rep_expr_kind cm_intrinsic_expr] in *;
    try contradiction; try discriminate.
  unfold cm_expr_code_for.
  simpl Z.eqb.
  cbn [cm_emit_expr_pair cm_rcode_of cm_expr_child].
  repeat rewrite <- app_assoc.
  cbn [app].
  match goal with |- ?P |-- ?P => cancel P end.
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_which_implies_wit_4 : cm_emit_intrinsic_expr_which_implies_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_intrinsic_expr_which_implies_wit_4_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_intrinsic_expr_which_implies_wit_5_split_goal_1 : cm_emit_intrinsic_expr_which_implies_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (lvalue = 0) by lia. subst lvalue.
  destruct e; cbn [cm_intrinsic_expr] in PreH22; try contradiction;
    unfold cm_expr_code_for in *; rewrite Z.eqb_refl in *;
    cbn [cm_expr_child cm_emit_expr_pair cm_rcode_of] in *;
    unfold cm_i32_code_count in *;
    repeat rewrite Zlength_app in *;
    pose proof (Zlength_nonneg (cm_rcode_of (cm_emit_expr_pair policy p fid pc temp e)));
    repeat rewrite Zlength_cons in *; rewrite ?Zlength_nil in *;
    try (cbn [cm_char_normalize_code] in *;
      repeat rewrite Zlength_cons in *; rewrite ?Zlength_nil in *);
    lia.
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_which_implies_wit_5_split_goal_2 : cm_emit_intrinsic_expr_which_implies_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (lvalue = 0) by lia. subst lvalue.
  destruct e; cbn [cm_intrinsic_expr] in PreH22; try contradiction;
    unfold cm_expr_temps_for in *; rewrite Z.eqb_refl in *;
    cbn [cm_expr_child cm_rtemps cm_expr_tpair cm_tright] in *;
    exact PreH18.
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_which_implies_wit_5 : cm_emit_intrinsic_expr_which_implies_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_intrinsic_expr_which_implies_wit_5_split_goal_1.
  - Goal_apply proof_of_cm_emit_intrinsic_expr_which_implies_wit_5_split_goal_2.
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_which_implies_wit_6_split_goal_1 : cm_emit_intrinsic_expr_which_implies_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn [cm_rep_expr_kind cm_intrinsic_expr] in *;
    try contradiction; try discriminate.
  unfold cm_expr_shape.
  reflexivity.
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_which_implies_wit_6 : cm_emit_intrinsic_expr_which_implies_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_intrinsic_expr_which_implies_wit_6_split_goal_1.
Qed. 

Lemma proof_of_cm_emit_intrinsic_expr_which_implies_wit_7_split_goal_spatial : cm_emit_intrinsic_expr_which_implies_wit_7_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (lvalue = 0) by lia.
  subst lvalue.
  destruct e; cbn [cm_rep_expr_kind cm_intrinsic_expr] in *;
    try contradiction; try discriminate.
  unfold cm_expr_code_for.
  simpl Z.eqb.
  cbn [cm_emit_expr_pair cm_rcode_of cm_expr_child].
  repeat rewrite <- app_assoc.
  cbn [app].
  match goal with |- ?P |-- ?P => cancel P end.
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_which_implies_wit_7 : cm_emit_intrinsic_expr_which_implies_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_intrinsic_expr_which_implies_wit_7_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_intrinsic_expr_which_implies_wit_8_split_goal_1 : cm_emit_intrinsic_expr_which_implies_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (lvalue = 0) by lia. subst lvalue.
  destruct e; cbn [cm_intrinsic_expr] in PreH22; try contradiction;
    unfold cm_expr_code_for in *; rewrite Z.eqb_refl in *;
    cbn [cm_expr_child cm_emit_expr_pair cm_rcode_of] in *;
    unfold cm_i32_code_count in *;
    repeat rewrite Zlength_app in *;
    pose proof (Zlength_nonneg (cm_rcode_of (cm_emit_expr_pair policy p fid pc temp e)));
    repeat rewrite Zlength_cons in *; rewrite ?Zlength_nil in *;
    try (cbn [cm_char_normalize_code] in *;
      repeat rewrite Zlength_cons in *; rewrite ?Zlength_nil in *);
    lia.
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_which_implies_wit_8_split_goal_2 : cm_emit_intrinsic_expr_which_implies_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (lvalue = 0) by lia. subst lvalue.
  destruct e; cbn [cm_intrinsic_expr] in PreH22; try contradiction;
    unfold cm_expr_temps_for in *; rewrite Z.eqb_refl in *;
    cbn [cm_expr_child cm_rtemps cm_expr_tpair cm_tright] in *;
    exact PreH18.
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_which_implies_wit_8 : cm_emit_intrinsic_expr_which_implies_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_intrinsic_expr_which_implies_wit_8_split_goal_1.
  - Goal_apply proof_of_cm_emit_intrinsic_expr_which_implies_wit_8_split_goal_2.
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_which_implies_wit_9_split_goal_1 : cm_emit_intrinsic_expr_which_implies_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn [cm_rep_expr_kind cm_intrinsic_expr] in *;
    try contradiction; try discriminate.
  unfold cm_expr_shape.
  reflexivity.
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_which_implies_wit_9 : cm_emit_intrinsic_expr_which_implies_wit_9.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_intrinsic_expr_which_implies_wit_9_split_goal_1.
Qed. 

Lemma proof_of_cm_emit_intrinsic_expr_which_implies_wit_10_split_goal_spatial : cm_emit_intrinsic_expr_which_implies_wit_10_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (lvalue = 0) by lia.
  subst lvalue.
  destruct e; cbn [cm_rep_expr_kind cm_intrinsic_expr] in *;
    try contradiction; try discriminate.
  unfold cm_expr_code_for.
  simpl Z.eqb.
  cbn [cm_emit_expr_pair cm_rcode_of cm_expr_child].
  repeat rewrite <- app_assoc.
  cbn [app].
  match goal with |- ?P |-- ?P => cancel P end.
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_which_implies_wit_10 : cm_emit_intrinsic_expr_which_implies_wit_10.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_intrinsic_expr_which_implies_wit_10_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_intrinsic_expr_which_implies_wit_11_split_goal_1 : cm_emit_intrinsic_expr_which_implies_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (lvalue = 0) by lia. subst lvalue.
  destruct e; cbn [cm_intrinsic_expr] in PreH22; try contradiction;
    unfold cm_expr_code_for in *; rewrite Z.eqb_refl in *;
    cbn [cm_expr_child cm_emit_expr_pair cm_rcode_of] in *;
    unfold cm_i32_code_count in *;
    repeat rewrite Zlength_app in *;
    pose proof (Zlength_nonneg (cm_rcode_of (cm_emit_expr_pair policy p fid pc temp e)));
    repeat rewrite Zlength_cons in *; rewrite ?Zlength_nil in *;
    try (cbn [cm_char_normalize_code] in *;
      repeat rewrite Zlength_cons in *; rewrite ?Zlength_nil in *);
    lia.
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_which_implies_wit_11_split_goal_2 : cm_emit_intrinsic_expr_which_implies_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (lvalue = 0) by lia. subst lvalue.
  destruct e; cbn [cm_intrinsic_expr] in PreH22; try contradiction;
    unfold cm_expr_temps_for in *; rewrite Z.eqb_refl in *;
    cbn [cm_expr_child cm_rtemps cm_expr_tpair cm_tright] in *;
    exact PreH18.
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_which_implies_wit_11 : cm_emit_intrinsic_expr_which_implies_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_intrinsic_expr_which_implies_wit_11_split_goal_1.
  - Goal_apply proof_of_cm_emit_intrinsic_expr_which_implies_wit_11_split_goal_2.
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_which_implies_wit_12_split_goal_spatial : cm_emit_intrinsic_expr_which_implies_wit_12_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (cm_expr_rep_node expr0 e).
  unfold cm_expr_node.
  Exists xa xb xargs.
  split_pure_spatial.
  - idtac.
    cancel (&(expr0 # "cm_expr" ->ₛ "kind") # Int |-> cm_rep_expr_kind e).
    cancel (&(expr0 # "cm_expr" ->ₛ "op") # Int |-> cm_rep_expr_op e).
    cancel (&(expr0 # "cm_expr" ->ₛ "ty") # Int |-> cm_type_encode (cm_expr_type e)).
    cancel (&(expr0 # "cm_expr" ->ₛ "value") # Int64 |-> cm_rep_expr_value e).
    cancel (&(expr0 # "cm_expr" ->ₛ "a") # Ptr |-> xa).
    cancel (&(expr0 # "cm_expr" ->ₛ "b") # Ptr |-> xb).
    cancel (&(expr0 # "cm_expr" ->ₛ "args") # Ptr |-> xargs).
    destruct e; cbn [cm_intrinsic_expr] in PreH10; try contradiction;
      cbn [cm_expr_payload cm_expr_child];
      (split_pure_spatial; [cancel | split_pures; dump_pre_spatial; tauto]).
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_cm_emit_intrinsic_expr_which_implies_wit_12 : cm_emit_intrinsic_expr_which_implies_wit_12.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_intrinsic_expr_which_implies_wit_12_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_unary_expr_return_wit_1_split_goal_spatial : cm_emit_unary_expr_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e op_.
  assert (lvalue_pre = 0) by lia.
  subst lvalue_pre.
  assert (Hcode : cm_expr_code_for policy p fid_pre pc_pre temp_pre
    (CMUnaryE 2 arg_ ty_) 0 = cm_expr_code_for policy p fid_pre pc_pre temp_pre arg_ 0 ++ cm_load_code ty_) by reflexivity.
  rewrite Hcode.
  repeat rewrite app_assoc.
  try rewrite app_nil_r.
  cancel.
Qed.

Lemma proof_of_cm_emit_unary_expr_return_wit_1 : cm_emit_unary_expr_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_unary_expr_return_wit_1_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_unary_expr_return_wit_2_split_goal_spatial : cm_emit_unary_expr_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e op_.
  assert (lvalue_pre = 1) by lia.
  subst lvalue_pre.
  assert (Hcode : cm_expr_code_for policy p fid_pre pc_pre temp_pre
    (CMUnaryE 2 arg_ ty_) 1 = cm_expr_code_for policy p fid_pre pc_pre temp_pre arg_ 0) by reflexivity.
  rewrite Hcode.
  repeat rewrite app_assoc.
  try rewrite app_nil_r.
  cancel.
Qed.

Lemma proof_of_cm_emit_unary_expr_return_wit_2 : cm_emit_unary_expr_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_unary_expr_return_wit_2_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_unary_expr_return_wit_3_split_goal_spatial : cm_emit_unary_expr_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e op_.
  assert (lvalue_pre = 0) by lia.
  subst lvalue_pre.
  assert (Hcode : cm_expr_code_for policy p fid_pre pc_pre temp_pre
    (CMUnaryE 3 arg_ ty_) 0 = cm_expr_code_for policy p fid_pre pc_pre temp_pre arg_ 1) by reflexivity.
  rewrite Hcode.
  repeat rewrite app_assoc.
  try rewrite app_nil_r.
  cancel.
Qed.

Lemma proof_of_cm_emit_unary_expr_return_wit_3 : cm_emit_unary_expr_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_unary_expr_return_wit_3_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_unary_expr_return_wit_4_split_goal_spatial : cm_emit_unary_expr_return_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e op_.
  assert (lvalue_pre = 1) by lia.
  subst lvalue_pre.
  assert (Hcode : cm_expr_code_for policy p fid_pre pc_pre temp_pre
    (CMUnaryE 3 arg_ ty_) 1 = nil) by reflexivity.
  rewrite Hcode.
  repeat rewrite app_assoc.
  try rewrite app_nil_r.
  change (nil ++ tail) with tail.
  cancel.
Qed.

Lemma proof_of_cm_emit_unary_expr_return_wit_4 : cm_emit_unary_expr_return_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_unary_expr_return_wit_4_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_unary_expr_return_wit_5_split_goal_spatial : cm_emit_unary_expr_return_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in *.
  subst e op_ lvalue_pre.
  unfold cm_expr_code_for.
  cbn [cm_emit_expr_pair Z.eqb cm_rcode_of cm_lcode_of].
  repeat rewrite <- app_assoc.
  cbn [app].
  cancel.
Qed.

Lemma proof_of_cm_emit_unary_expr_return_wit_5 : cm_emit_unary_expr_return_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_unary_expr_return_wit_5_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_unary_expr_return_wit_6_split_goal_spatial : cm_emit_unary_expr_return_wit_6_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in *.
  subst e lvalue_pre.
  assert (H2 : Z.eqb op_ 2 = false) by (apply Z.eqb_neq; lia).
  assert (H3 : Z.eqb op_ 3 = false) by (apply Z.eqb_neq; lia).
  assert (H0 : Z.eqb op_ 0 = false) by (apply Z.eqb_neq; lia).
  unfold cm_expr_code_for.
  cbn [cm_emit_expr_pair].
  rewrite Z.eqb_refl.
  rewrite H2, H3, H0.
  cbn [cm_rcode_of].
  repeat rewrite <- app_assoc.
  cbn [app].
  cancel.
Qed.

Lemma proof_of_cm_emit_unary_expr_return_wit_6 : cm_emit_unary_expr_return_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_unary_expr_return_wit_6_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_unary_expr_return_wit_7_split_goal_spatial : cm_emit_unary_expr_return_wit_7_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in *.
  subst e.
  assert (H2 : Z.eqb op_ 2 = false) by (apply Z.eqb_neq; lia).
  assert (H3 : Z.eqb op_ 3 = false) by (apply Z.eqb_neq; lia).
  assert (HL : Z.eqb lvalue_pre 0 = false) by (apply Z.eqb_neq; lia).
  unfold cm_expr_code_for.
  cbn [cm_emit_expr_pair].
  rewrite HL, H2, H3.
  cbn [cm_lcode_of app].
  rewrite app_nil_r.
  cancel.
Qed.

Lemma proof_of_cm_emit_unary_expr_return_wit_7 : cm_emit_unary_expr_return_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_unary_expr_return_wit_7_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_unary_expr_partial_solve_wit_1_pure_split_goal_1 : cm_emit_unary_expr_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: (dump_pre_spatial; unfold cm_expr_shape; reflexivity).
Qed.

Lemma proof_of_cm_emit_unary_expr_partial_solve_wit_1_pure_split_goal_2 : cm_emit_unary_expr_partial_solve_wit_1_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: (dump_pre_spatial; unfold cm_expr_shape; reflexivity).
Qed.

Lemma proof_of_cm_emit_unary_expr_partial_solve_wit_1_pure : cm_emit_unary_expr_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_unary_expr_partial_solve_wit_1_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_unary_expr_partial_solve_wit_1_pure_split_goal_2.
Qed.

Lemma proof_of_cm_emit_unary_expr_partial_solve_wit_3_pure_split_goal_1 : cm_emit_unary_expr_partial_solve_wit_3_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: (dump_pre_spatial; unfold cm_expr_shape in *; subst; assumption).
Qed.

Lemma proof_of_cm_emit_unary_expr_partial_solve_wit_3_pure_split_goal_2 : cm_emit_unary_expr_partial_solve_wit_3_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: (dump_pre_spatial; unfold cm_expr_shape; reflexivity).
Qed.

Lemma proof_of_cm_emit_unary_expr_partial_solve_wit_3_pure : cm_emit_unary_expr_partial_solve_wit_3_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_unary_expr_partial_solve_wit_3_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_unary_expr_partial_solve_wit_3_pure_split_goal_2.
Qed.

Lemma proof_of_cm_emit_unary_expr_partial_solve_wit_7_pure_split_goal_1 : cm_emit_unary_expr_partial_solve_wit_7_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: (dump_pre_spatial; unfold cm_expr_shape in *; subst; assumption).
Qed.

Lemma proof_of_cm_emit_unary_expr_partial_solve_wit_7_pure_split_goal_2 : cm_emit_unary_expr_partial_solve_wit_7_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: (dump_pre_spatial; unfold cm_expr_shape; reflexivity).
Qed.

Lemma proof_of_cm_emit_unary_expr_partial_solve_wit_7_pure : cm_emit_unary_expr_partial_solve_wit_7_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_unary_expr_partial_solve_wit_7_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_unary_expr_partial_solve_wit_7_pure_split_goal_2.
Qed.

Lemma proof_of_cm_emit_unary_expr_partial_solve_wit_10_pure_split_goal_1 : cm_emit_unary_expr_partial_solve_wit_10_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: (dump_pre_spatial; unfold cm_expr_shape in *; subst; assumption).
Qed.

Lemma proof_of_cm_emit_unary_expr_partial_solve_wit_10_pure_split_goal_2 : cm_emit_unary_expr_partial_solve_wit_10_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: (dump_pre_spatial; unfold cm_expr_shape; reflexivity).
Qed.

Lemma proof_of_cm_emit_unary_expr_partial_solve_wit_10_pure : cm_emit_unary_expr_partial_solve_wit_10_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_unary_expr_partial_solve_wit_10_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_unary_expr_partial_solve_wit_10_pure_split_goal_2.
Qed.

Lemma proof_of_cm_emit_unary_expr_partial_solve_wit_13_pure_split_goal_1 : cm_emit_unary_expr_partial_solve_wit_13_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: (dump_pre_spatial; unfold cm_expr_shape in *; subst; assumption).
Qed.

Lemma proof_of_cm_emit_unary_expr_partial_solve_wit_13_pure_split_goal_2 : cm_emit_unary_expr_partial_solve_wit_13_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: (dump_pre_spatial; unfold cm_expr_shape; reflexivity).
Qed.

Lemma proof_of_cm_emit_unary_expr_partial_solve_wit_13_pure : cm_emit_unary_expr_partial_solve_wit_13_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_unary_expr_partial_solve_wit_13_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_unary_expr_partial_solve_wit_13_pure_split_goal_2.
Qed.

Lemma proof_of_cm_emit_unary_expr_partial_solve_wit_16_pure_split_goal_1 : cm_emit_unary_expr_partial_solve_wit_16_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cm_emit_unary_expr_partial_solve_wit_16_pure_split_goal_2 : cm_emit_unary_expr_partial_solve_wit_16_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cm_emit_unary_expr_partial_solve_wit_16_pure : cm_emit_unary_expr_partial_solve_wit_16_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_unary_expr_partial_solve_wit_16_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_unary_expr_partial_solve_wit_16_pure_split_goal_2.
Qed.

Lemma proof_of_cm_emit_unary_expr_partial_solve_wit_17_pure_split_goal_1 : cm_emit_unary_expr_partial_solve_wit_17_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cm_emit_unary_expr_partial_solve_wit_17_pure_split_goal_2 : cm_emit_unary_expr_partial_solve_wit_17_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cm_emit_unary_expr_partial_solve_wit_17_pure : cm_emit_unary_expr_partial_solve_wit_17_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_unary_expr_partial_solve_wit_17_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_unary_expr_partial_solve_wit_17_pure_split_goal_2.
Qed.

Lemma proof_of_cm_emit_unary_expr_partial_solve_wit_21_pure_split_goal_1 : cm_emit_unary_expr_partial_solve_wit_21_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cm_emit_unary_expr_partial_solve_wit_21_pure_split_goal_2 : cm_emit_unary_expr_partial_solve_wit_21_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cm_emit_unary_expr_partial_solve_wit_21_pure : cm_emit_unary_expr_partial_solve_wit_21_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_unary_expr_partial_solve_wit_21_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_unary_expr_partial_solve_wit_21_pure_split_goal_2.
Qed.

Lemma proof_of_cm_emit_unary_expr_partial_solve_wit_22_pure_split_goal_1 : cm_emit_unary_expr_partial_solve_wit_22_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cm_emit_unary_expr_partial_solve_wit_22_pure_split_goal_2 : cm_emit_unary_expr_partial_solve_wit_22_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cm_emit_unary_expr_partial_solve_wit_22_pure : cm_emit_unary_expr_partial_solve_wit_22_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_unary_expr_partial_solve_wit_22_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_unary_expr_partial_solve_wit_22_pure_split_goal_2.
Qed.

Lemma proof_of_cm_emit_unary_expr_partial_solve_wit_25_pure_split_goal_1 : cm_emit_unary_expr_partial_solve_wit_25_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cm_emit_unary_expr_partial_solve_wit_25_pure : cm_emit_unary_expr_partial_solve_wit_25_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_unary_expr_partial_solve_wit_25_pure_split_goal_1.
Qed.

Lemma proof_of_cm_emit_unary_expr_partial_solve_wit_26_pure_split_goal_1 : cm_emit_unary_expr_partial_solve_wit_26_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cm_emit_unary_expr_partial_solve_wit_26_pure : cm_emit_unary_expr_partial_solve_wit_26_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_unary_expr_partial_solve_wit_26_pure_split_goal_1.
Qed.

Lemma proof_of_cm_emit_unary_expr_partial_solve_wit_27_pure_split_goal_1 : cm_emit_unary_expr_partial_solve_wit_27_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cm_emit_unary_expr_partial_solve_wit_27_pure : cm_emit_unary_expr_partial_solve_wit_27_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_unary_expr_partial_solve_wit_27_pure_split_goal_1.
Qed.

Lemma proof_of_cm_emit_unary_expr_partial_solve_wit_28_pure_split_goal_1 : cm_emit_unary_expr_partial_solve_wit_28_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cm_emit_unary_expr_partial_solve_wit_28_pure : cm_emit_unary_expr_partial_solve_wit_28_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_unary_expr_partial_solve_wit_28_pure_split_goal_1.
Qed.

Lemma proof_of_cm_emit_unary_expr_partial_solve_wit_29_pure_split_goal_1 : cm_emit_unary_expr_partial_solve_wit_29_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cm_emit_unary_expr_partial_solve_wit_29_pure : cm_emit_unary_expr_partial_solve_wit_29_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_unary_expr_partial_solve_wit_29_pure_split_goal_1.
Qed.

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_1 : cm_emit_unary_expr_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in *; subst e.
  rewrite cm_expr_rep_node; unfold cm_expr_node.
  cbn [cm_expr_payload cm_rep_expr_op].
  Intros xa xb xargs.
  Exists xargs xb xa.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed. 

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_2_split_goal_1 : cm_emit_unary_expr_which_implies_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  intros.
  unfold cm_expr_shape in PreH22. subst e.
  cbn [cm_rep_expr_op cm_expr_type cm_expr_wf cm_expr_counts_representable] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try reflexivity; try assumption.
  all: try (eapply cm_expr_type_refs__constructor_facts_a; eauto).
  all: try match goal with H : cm_expr_counts_representable ?pol ?p ?fid ?e |- _ =>
    pose proof (cm_expr_node_facts__constructor_facts_a pol p fid e H) end.
  all: unfold cm_expr_count_node_representable in *; intuition subst; cbn in *; auto.
Qed.

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_2_split_goal_2 : cm_emit_unary_expr_which_implies_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  intros.
  pose proof (cm_expr_type_refs__constructor_facts_a policy p f e PreH4 PreH6 PreH7 PreH14) as Hrefs.
  unfold cm_expr_shape in PreH22. subst e.
  cbn [cm_rep_expr_op cm_expr_type cm_expr_wf cm_expr_counts_representable] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try reflexivity; try assumption.
  all: try (eapply cm_expr_type_refs__constructor_facts_a; eauto).
  all: try match goal with H : cm_expr_counts_representable ?pol ?p ?fid ?e |- _ =>
    pose proof (cm_expr_node_facts__constructor_facts_a pol p fid e H) end.
  all: unfold cm_expr_count_node_representable in *; intuition subst; cbn in *; auto.
Qed.

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_2_split_goal_3 : cm_emit_unary_expr_which_implies_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  intros.
  unfold cm_expr_shape in PreH22. subst e.
  cbn [cm_rep_expr_op cm_expr_type cm_expr_wf cm_expr_counts_representable] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try reflexivity; try assumption.
  all: try (eapply cm_expr_type_refs__constructor_facts_a; eauto).
  all: try match goal with H : cm_expr_counts_representable ?pol ?p ?fid ?e |- _ =>
    pose proof (cm_expr_node_facts__constructor_facts_a pol p fid e H) end.
  all: unfold cm_expr_count_node_representable in *; intuition subst; cbn in *; auto.
Qed.

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_2_split_goal_4 : cm_emit_unary_expr_which_implies_wit_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
  intros.
  unfold cm_expr_shape in PreH22. subst e.
  cbn [cm_rep_expr_op cm_expr_type cm_expr_wf cm_expr_counts_representable] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try reflexivity; try assumption.
  all: try (eapply cm_expr_type_refs__constructor_facts_a; eauto).
  all: try match goal with H : cm_expr_counts_representable ?pol ?p ?fid ?e |- _ =>
    pose proof (cm_expr_node_facts__constructor_facts_a pol p fid e H) end.
  all: unfold cm_expr_count_node_representable in *; intuition subst; cbn in *; auto.
Qed.

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_2_split_goal_5 : cm_emit_unary_expr_which_implies_wit_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia).
  intros.
  unfold cm_expr_shape in PreH22. subst e.
  cbn [cm_rep_expr_op cm_expr_type cm_expr_wf cm_expr_counts_representable] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try reflexivity; try assumption.
  all: try (eapply cm_expr_type_refs__constructor_facts_a; eauto).
  all: try match goal with H : cm_expr_counts_representable ?pol ?p ?fid ?e |- _ =>
    pose proof (cm_expr_node_facts__constructor_facts_a pol p fid e H) end.
  all: unfold cm_expr_count_node_representable in *; intuition subst; cbn in *; auto.
Qed.

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_2_split_goal_6 : cm_emit_unary_expr_which_implies_wit_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia).
  intros.
  unfold cm_expr_shape in PreH22. subst e.
  cbn [cm_rep_expr_op cm_expr_type cm_expr_wf cm_expr_counts_representable] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try reflexivity; try assumption.
  all: try (eapply cm_expr_type_refs__constructor_facts_a; eauto).
  all: try match goal with H : cm_expr_counts_representable ?pol ?p ?fid ?e |- _ =>
    pose proof (cm_expr_node_facts__constructor_facts_a pol p fid e H) end.
  all: unfold cm_expr_count_node_representable in *; intuition subst; cbn in *; auto.
Qed.

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_2_split_goal_7 : cm_emit_unary_expr_which_implies_wit_2_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia).
  intros.
  unfold cm_expr_shape in PreH22. subst e.
  cbn [cm_rep_expr_op cm_expr_type cm_expr_wf cm_expr_counts_representable] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try reflexivity; try assumption.
  all: try (eapply cm_expr_type_refs__constructor_facts_a; eauto).
  all: try match goal with H : cm_expr_counts_representable ?pol ?p ?fid ?e |- _ =>
    pose proof (cm_expr_node_facts__constructor_facts_a pol p fid e H) end.
  all: unfold cm_expr_count_node_representable in *; intuition subst; cbn in *; auto.
Qed.

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_2_split_goal_8 : cm_emit_unary_expr_which_implies_wit_2_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia).
  intros.
  unfold cm_expr_shape in PreH22. subst e.
  cbn [cm_rep_expr_op cm_expr_type cm_expr_wf cm_expr_counts_representable] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try reflexivity; try assumption.
  all: try (eapply cm_expr_type_refs__constructor_facts_a; eauto).
  all: try match goal with H : cm_expr_counts_representable ?pol ?p ?fid ?e |- _ =>
    pose proof (cm_expr_node_facts__constructor_facts_a pol p fid e H) end.
  all: unfold cm_expr_count_node_representable in *; intuition subst; cbn in *; auto.
Qed.

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_2_split_goal_9 : cm_emit_unary_expr_which_implies_wit_2_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia).
  intros.
  unfold cm_expr_shape in PreH22. subst e.
  cbn [cm_rep_expr_op cm_expr_type cm_expr_wf cm_expr_counts_representable] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try reflexivity; try assumption.
  all: try (eapply cm_expr_type_refs__constructor_facts_a; eauto).
  all: try match goal with H : cm_expr_counts_representable ?pol ?p ?fid ?e |- _ =>
    pose proof (cm_expr_node_facts__constructor_facts_a pol p fid e H) end.
  all: unfold cm_expr_count_node_representable in *; intuition subst; cbn in *; auto.
Qed.

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_2_split_goal_10 : cm_emit_unary_expr_which_implies_wit_2_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia).
  intros.
  pose proof (cm_expr_type_refs__constructor_facts_a policy p f e PreH4 PreH6 PreH7 PreH14) as Hrefs.
  unfold cm_expr_shape in PreH22. subst e.
  cbn [cm_rep_expr_op cm_expr_type cm_expr_wf cm_expr_counts_representable] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try reflexivity; try assumption.
  all: try (eapply cm_expr_type_refs__constructor_facts_a; eauto).
  all: try match goal with H : cm_expr_counts_representable ?pol ?p ?fid ?e |- _ =>
    pose proof (cm_expr_node_facts__constructor_facts_a pol p fid e H) end.
  all: unfold cm_expr_count_node_representable in *; intuition subst; cbn in *; auto.
Qed.

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_2_split_goal_11 : cm_emit_unary_expr_which_implies_wit_2_split_goal_11.
Proof.
  LLM_pre_process ltac:(lia).
  intros.
  unfold cm_expr_shape in PreH22. subst e.
  cbn [cm_rep_expr_op cm_expr_type cm_expr_wf cm_expr_counts_representable] in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try reflexivity; try assumption.
  all: try (eapply cm_expr_type_refs__constructor_facts_a; eauto).
  all: try match goal with H : cm_expr_counts_representable ?pol ?p ?fid ?e |- _ =>
    pose proof (cm_expr_node_facts__constructor_facts_a pol p fid e H) end.
  all: unfold cm_expr_count_node_representable in *; intuition subst; cbn in *; auto.
Qed.

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_2_split_goal_12 : cm_emit_unary_expr_which_implies_wit_2_split_goal_12.
Proof.
  LLM_pre_process ltac:(lia).
  intros.
  unfold cm_temp_offset in *. lia.
Qed.

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_2_split_goal_13 : cm_emit_unary_expr_which_implies_wit_2_split_goal_13.
Proof.
  LLM_pre_process ltac:(lia).
  intros.
  pose proof (cm_slots_size_nonnegative__call_bounds _ _ PreH6).
  pose proof (cm_slots_size_nonnegative__call_bounds _ _ PreH7).
  unfold cm_temp_offset in *. rewrite <- PreH5 in *. lia.
Qed.

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_2 : cm_emit_unary_expr_which_implies_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_unary_expr_which_implies_wit_2_split_goal_1.
  - Goal_apply proof_of_cm_emit_unary_expr_which_implies_wit_2_split_goal_2.
  - Goal_apply proof_of_cm_emit_unary_expr_which_implies_wit_2_split_goal_3.
  - Goal_apply proof_of_cm_emit_unary_expr_which_implies_wit_2_split_goal_4.
  - Goal_apply proof_of_cm_emit_unary_expr_which_implies_wit_2_split_goal_5.
  - Goal_apply proof_of_cm_emit_unary_expr_which_implies_wit_2_split_goal_6.
  - Goal_apply proof_of_cm_emit_unary_expr_which_implies_wit_2_split_goal_7.
  - Goal_apply proof_of_cm_emit_unary_expr_which_implies_wit_2_split_goal_8.
  - Goal_apply proof_of_cm_emit_unary_expr_which_implies_wit_2_split_goal_9.
  - Goal_apply proof_of_cm_emit_unary_expr_which_implies_wit_2_split_goal_10.
  - Goal_apply proof_of_cm_emit_unary_expr_which_implies_wit_2_split_goal_11.
  - Goal_apply proof_of_cm_emit_unary_expr_which_implies_wit_2_split_goal_12.
  - Goal_apply proof_of_cm_emit_unary_expr_which_implies_wit_2_split_goal_13.
Qed.

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_3_split_goal_spatial : cm_emit_unary_expr_which_implies_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in *.
  subst e.
  subst op_.
  assert (lvalue = 0) by lia.
  subst lvalue.
  unfold cm_expr_code_for.
  cbn [Z.eqb Pos.eqb cm_emit_expr_pair cm_rcode_of cm_lcode_of].
  repeat rewrite <- app_assoc.
  cbn [app].
  cancel.
Qed.

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_3 : cm_emit_unary_expr_which_implies_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_unary_expr_which_implies_wit_3_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_4_split_goal_1 : cm_emit_unary_expr_which_implies_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in PreH22; subst e.
  subst op_.
  assert (lvalue = 0) by lia; subst lvalue.
  pose proof (Zlength_nonneg (cm_expr_code_for policy p fid pc temp arg_ 0)) as Hnonneg.
  unfold cm_expr_code_for in PreH21, Hnonneg |- *; cbn [Z.eqb] in PreH21, Hnonneg |- *.
  rewrite (proj2 (cm_emit_pair_lengths__store_bounds policy p fid (CMUnaryE 2 arg_ ty_) pc temp)) in PreH21.
  rewrite (proj2 (cm_emit_pair_lengths__store_bounds policy p fid arg_ pc temp)) in Hnonneg |- *.
  unfold cm_lvalue_code_count, cm_rvalue_code_count in PreH21, Hnonneg |- *.
  cbn [Z.eqb Pos.eqb cm_expr_code_counts cm_lcount_of cm_rcount_of] in PreH21.
  unfold cm_i32_code_count in *; lia.
Qed.

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_4_split_goal_2 : cm_emit_unary_expr_which_implies_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in PreH22; subst e.
  subst op_.
  assert (lvalue = 0) by lia; subst lvalue.
  cbn [Z.eqb Pos.eqb cm_expr_temps_for cm_rtemps cm_ltemps cm_expr_tpair cm_tleft cm_tright] in PreH18 |- *.
  exact PreH18.
Qed.

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_4 : cm_emit_unary_expr_which_implies_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_unary_expr_which_implies_wit_4_split_goal_1.
  - Goal_apply proof_of_cm_emit_unary_expr_which_implies_wit_4_split_goal_2.
Qed. 

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_5_split_goal_spatial : cm_emit_unary_expr_which_implies_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in *.
  subst e.
  subst op_.
  assert (lvalue = 1) by lia.
  subst lvalue.
  unfold cm_expr_code_for.
  cbn [Z.eqb Pos.eqb cm_emit_expr_pair cm_rcode_of cm_lcode_of].
  repeat rewrite <- app_assoc.
  cbn [app].
  cancel.
Qed.

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_5 : cm_emit_unary_expr_which_implies_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_unary_expr_which_implies_wit_5_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_6_split_goal_1 : cm_emit_unary_expr_which_implies_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in PreH22; subst e.
  subst op_.
  assert (lvalue = 1) by lia; subst lvalue.
  pose proof (Zlength_nonneg (cm_expr_code_for policy p fid pc temp arg_ 0)) as Hnonneg.
  unfold cm_expr_code_for in PreH21, Hnonneg |- *; cbn [Z.eqb] in PreH21, Hnonneg |- *.
  rewrite (proj1 (cm_emit_pair_lengths__store_bounds policy p fid (CMUnaryE 2 arg_ ty_) pc temp)) in PreH21.
  rewrite (proj2 (cm_emit_pair_lengths__store_bounds policy p fid arg_ pc temp)) in Hnonneg |- *.
  unfold cm_lvalue_code_count, cm_rvalue_code_count in PreH21, Hnonneg |- *.
  cbn [Z.eqb Pos.eqb cm_expr_code_counts cm_lcount_of cm_rcount_of] in PreH21.
  unfold cm_i32_code_count in *; lia.
Qed.

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_6_split_goal_2 : cm_emit_unary_expr_which_implies_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in PreH22; subst e.
  subst op_.
  assert (lvalue = 1) by lia; subst lvalue.
  cbn [Z.eqb Pos.eqb cm_expr_temps_for cm_rtemps cm_ltemps cm_expr_tpair cm_tleft cm_tright] in PreH18 |- *.
  exact PreH18.
Qed.

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_6 : cm_emit_unary_expr_which_implies_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_unary_expr_which_implies_wit_6_split_goal_1.
  - Goal_apply proof_of_cm_emit_unary_expr_which_implies_wit_6_split_goal_2.
Qed. 

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_7_split_goal_spatial : cm_emit_unary_expr_which_implies_wit_7_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in *.
  subst e.
  subst op_.
  assert (lvalue = 0) by lia.
  subst lvalue.
  unfold cm_expr_code_for.
  cbn [Z.eqb Pos.eqb cm_emit_expr_pair cm_rcode_of cm_lcode_of].
  repeat rewrite <- app_assoc.
  cbn [app].
  cancel.
Qed.

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_7 : cm_emit_unary_expr_which_implies_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_unary_expr_which_implies_wit_7_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_8_split_goal_1 : cm_emit_unary_expr_which_implies_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in PreH22; subst e.
  subst op_.
  assert (lvalue = 0) by lia; subst lvalue.
  pose proof (Zlength_nonneg (cm_expr_code_for policy p fid pc temp arg_ 1)) as Hnonneg.
  unfold cm_expr_code_for in PreH21, Hnonneg |- *; cbn [Z.eqb] in PreH21, Hnonneg |- *.
  rewrite (proj2 (cm_emit_pair_lengths__store_bounds policy p fid (CMUnaryE 3 arg_ ty_) pc temp)) in PreH21.
  rewrite (proj1 (cm_emit_pair_lengths__store_bounds policy p fid arg_ pc temp)) in Hnonneg |- *.
  unfold cm_lvalue_code_count, cm_rvalue_code_count in PreH21, Hnonneg |- *.
  cbn [Z.eqb Pos.eqb cm_expr_code_counts cm_lcount_of cm_rcount_of] in PreH21.
  unfold cm_i32_code_count in *; lia.
Qed.

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_8_split_goal_2 : cm_emit_unary_expr_which_implies_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in PreH22; subst e.
  subst op_.
  assert (lvalue = 0) by lia; subst lvalue.
  cbn [Z.eqb Pos.eqb cm_expr_temps_for cm_rtemps cm_ltemps cm_expr_tpair cm_tleft cm_tright] in PreH18 |- *.
  exact PreH18.
Qed.

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_8 : cm_emit_unary_expr_which_implies_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_unary_expr_which_implies_wit_8_split_goal_1.
  - Goal_apply proof_of_cm_emit_unary_expr_which_implies_wit_8_split_goal_2.
Qed. 

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_9_split_goal_spatial : cm_emit_unary_expr_which_implies_wit_9_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in *.
  subst e.
  subst op_.
  assert (lvalue = 0) by lia.
  subst lvalue.
  unfold cm_expr_code_for.
  cbn [Z.eqb Pos.eqb cm_emit_expr_pair cm_rcode_of cm_lcode_of].
  repeat rewrite <- app_assoc.
  cbn [app].
  cancel.
Qed.

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_9 : cm_emit_unary_expr_which_implies_wit_9.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_unary_expr_which_implies_wit_9_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_10_split_goal_1 : cm_emit_unary_expr_which_implies_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in PreH22; subst e.
  subst op_.
  assert (lvalue = 0) by lia; subst lvalue.
  pose proof (Zlength_nonneg (cm_expr_code_for policy p fid pc temp arg_ 0)) as Hnonneg.
  unfold cm_expr_code_for in PreH21, Hnonneg |- *; cbn [Z.eqb] in PreH21, Hnonneg |- *.
  rewrite (proj2 (cm_emit_pair_lengths__store_bounds policy p fid (CMUnaryE 0 arg_ ty_) pc temp)) in PreH21.
  rewrite (proj2 (cm_emit_pair_lengths__store_bounds policy p fid arg_ pc temp)) in Hnonneg |- *.
  unfold cm_lvalue_code_count, cm_rvalue_code_count in PreH21, Hnonneg |- *.
  cbn [Z.eqb Pos.eqb cm_expr_code_counts cm_lcount_of cm_rcount_of] in PreH21.
  unfold cm_i32_code_count in *; lia.
Qed.

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_10_split_goal_2 : cm_emit_unary_expr_which_implies_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in PreH22; subst e.
  subst op_.
  assert (lvalue = 0) by lia; subst lvalue.
  cbn [Z.eqb Pos.eqb cm_expr_temps_for cm_rtemps cm_ltemps cm_expr_tpair cm_tleft cm_tright] in PreH18 |- *.
  exact PreH18.
Qed.

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_10 : cm_emit_unary_expr_which_implies_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_unary_expr_which_implies_wit_10_split_goal_1.
  - Goal_apply proof_of_cm_emit_unary_expr_which_implies_wit_10_split_goal_2.
Qed. 

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_11_split_goal_spatial : cm_emit_unary_expr_which_implies_wit_11_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in *.
  subst e.
  assert (lvalue = 0) by lia.
  subst lvalue.
  unfold cm_expr_code_for.
  cbn [Z.eqb Pos.eqb cm_emit_expr_pair cm_rcode_of cm_lcode_of].
  assert (Htwo : (Z.eqb op_ 2) = false) by (apply Z.eqb_neq; assumption).
  assert (Hthree : (Z.eqb op_ 3) = false) by (apply Z.eqb_neq; assumption).
  assert (Hzero : (Z.eqb op_ 0) = false) by (apply Z.eqb_neq; assumption).
  rewrite Htwo, Hthree, Hzero.
  cbn [cm_rcode_of].
  repeat rewrite <- app_assoc.
  cbn [app].
  cancel.
Qed.

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_11 : cm_emit_unary_expr_which_implies_wit_11.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_unary_expr_which_implies_wit_11_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_12_split_goal_1 : cm_emit_unary_expr_which_implies_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in PreH22; subst e.
  assert (lvalue = 0) by lia; subst lvalue.
  assert (Hop2 : (Z.eqb op_ 2) = false) by (apply Z.eqb_neq; exact PreH23).
  assert (Hop3 : (Z.eqb op_ 3) = false) by (apply Z.eqb_neq; exact PreH24).
  pose proof (Zlength_nonneg (cm_expr_code_for policy p fid pc temp arg_ 0)) as Hnonneg.
  unfold cm_expr_code_for in PreH21, Hnonneg |- *; cbn [Z.eqb] in PreH21, Hnonneg |- *.
  rewrite (proj2 (cm_emit_pair_lengths__store_bounds policy p fid (CMUnaryE op_ arg_ ty_) pc temp)) in PreH21.
  rewrite (proj2 (cm_emit_pair_lengths__store_bounds policy p fid arg_ pc temp)) in Hnonneg |- *.
  unfold cm_lvalue_code_count, cm_rvalue_code_count in PreH21, Hnonneg |- *.
  cbn [Z.eqb Pos.eqb cm_expr_code_counts cm_lcount_of cm_rcount_of] in PreH21.
  rewrite Hop2, Hop3 in PreH21; cbn [cm_rcount_of] in PreH21.
  unfold cm_i32_code_count in *; lia.
Qed.

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_12_split_goal_2 : cm_emit_unary_expr_which_implies_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in PreH22; subst e.
  assert (lvalue = 0) by lia; subst lvalue.
  assert (Hop2 : (Z.eqb op_ 2) = false) by (apply Z.eqb_neq; exact PreH23).
  assert (Hop3 : (Z.eqb op_ 3) = false) by (apply Z.eqb_neq; exact PreH24).
  unfold cm_expr_temps_for in PreH18 |- *.
  rewrite Z.eqb_refl in PreH18 |- *.
  unfold cm_rtemps in PreH18 |- *.
  cbn [cm_expr_tpair] in PreH18.
  rewrite Hop2, Hop3 in PreH18; cbn [cm_tright] in PreH18.
  exact PreH18.
Qed.

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_12 : cm_emit_unary_expr_which_implies_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_unary_expr_which_implies_wit_12_split_goal_1.
  - Goal_apply proof_of_cm_emit_unary_expr_which_implies_wit_12_split_goal_2.
Qed. 

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_13_split_goal_spatial : cm_emit_unary_expr_which_implies_wit_13_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (cm_expr_rep_node expr0 e).
  unfold cm_expr_node.
  Exists xa xb xargs.
  unfold cm_expr_shape in PreH10. subst e.
  cbn [cm_expr_payload cm_rep_expr_op].
  split_pure_spatial.
  - cancel.
    cancel (&(expr0 # "cm_expr" ->ₛ "kind") # Int |-> cm_rep_expr_kind (CMUnaryE op_ arg_ ty_)).
    cancel (&(expr0 # "cm_expr" ->ₛ "op") # Int |-> op_).
    cancel (&(expr0 # "cm_expr" ->ₛ "ty") # Int |-> cm_type_encode (cm_expr_type (CMUnaryE op_ arg_ ty_))).
    cancel (&(expr0 # "cm_expr" ->ₛ "value") # Int64 |-> cm_rep_expr_value (CMUnaryE op_ arg_ ty_)).
    cancel (&(expr0 # "cm_expr" ->ₛ "a") # Ptr |-> xa).
    cancel (&(expr0 # "cm_expr" ->ₛ "b") # Ptr |-> xb).
    cancel (&(expr0 # "cm_expr" ->ₛ "args") # Ptr |-> xargs).
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_cm_emit_unary_expr_which_implies_wit_13 : cm_emit_unary_expr_which_implies_wit_13.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_unary_expr_which_implies_wit_13_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_index_expr_safety_wit_2_split_goal_1 : cm_emit_index_expr_safety_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold cm_i32_code_count in *; lia).
  all: unfold cm_expr_shape in *; subst.
  all: pose proof (cm_index_code_bounds__index_bounds policy p fid_pre pc_pre temp_pre left_ right_ ty_ lvalue_pre) as Hbounds.
  all: specialize (Hbounds ltac:(assumption) ltac:(assumption)).
  all: unfold cm_i32_code_count in *; destruct Hbounds as [? [? ?]]; try dump_pre_spatial; lia.
Qed.

Lemma proof_of_cm_emit_index_expr_safety_wit_2_split_goal_2 : cm_emit_index_expr_safety_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(unfold cm_i32_code_count in *; lia).
  all: unfold cm_expr_shape in *; subst.
  all: pose proof (cm_index_code_bounds__index_bounds policy p fid_pre pc_pre temp_pre left_ right_ ty_ lvalue_pre) as Hbounds.
  all: specialize (Hbounds ltac:(assumption) ltac:(assumption)).
  all: unfold cm_i32_code_count in *; destruct Hbounds as [? [? ?]]; try dump_pre_spatial; lia.
Qed.

Lemma proof_of_cm_emit_index_expr_safety_wit_2 : cm_emit_index_expr_safety_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_index_expr_safety_wit_2_split_goal_1.
  - Goal_apply proof_of_cm_emit_index_expr_safety_wit_2_split_goal_2.
Qed. 

Lemma proof_of_cm_emit_index_expr_safety_wit_3_split_goal_1 : cm_emit_index_expr_safety_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold cm_i32_code_count in *; lia).
  all: unfold cm_expr_shape in *; subst.
  all: pose proof (cm_index_code_bounds__index_bounds policy p fid_pre pc_pre temp_pre left_ right_ ty_ lvalue_pre) as Hbounds.
  all: specialize (Hbounds ltac:(assumption) ltac:(assumption)).
  all: unfold cm_i32_code_count in *; destruct Hbounds as [? [? ?]]; try dump_pre_spatial; lia.
Qed.

Lemma proof_of_cm_emit_index_expr_safety_wit_3_split_goal_2 : cm_emit_index_expr_safety_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(unfold cm_i32_code_count in *; lia).
  all: unfold cm_expr_shape in *; subst.
  all: pose proof (cm_index_code_bounds__index_bounds policy p fid_pre pc_pre temp_pre left_ right_ ty_ lvalue_pre) as Hbounds.
  all: specialize (Hbounds ltac:(assumption) ltac:(assumption)).
  all: unfold cm_i32_code_count in *; destruct Hbounds as [? [? ?]]; try dump_pre_spatial; lia.
Qed.

Lemma proof_of_cm_emit_index_expr_safety_wit_3 : cm_emit_index_expr_safety_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_index_expr_safety_wit_3_split_goal_1.
  - Goal_apply proof_of_cm_emit_index_expr_safety_wit_3_split_goal_2.
Qed. 

Lemma proof_of_cm_emit_index_expr_safety_wit_5_split_goal_1 : cm_emit_index_expr_safety_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold cm_i32_code_count in *; lia).
  all: unfold cm_expr_shape in *; subst.
  all: pose proof (cm_index_temp_bounds__index_bounds left_ right_ ty_ lvalue_pre temp_pre temp_limit_pre) as Hbounds.
  all: specialize (Hbounds ltac:(assumption)).
  all: unfold cm_i32_code_count in *; destruct Hbounds as [? [? ?]]; try dump_pre_spatial; lia.
Qed.

Lemma proof_of_cm_emit_index_expr_safety_wit_5_split_goal_2 : cm_emit_index_expr_safety_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(unfold cm_i32_code_count in *; lia).
  all: unfold cm_expr_shape in *; subst.
  all: pose proof (cm_index_temp_bounds__index_bounds left_ right_ ty_ lvalue_pre temp_pre temp_limit_pre) as Hbounds.
  all: specialize (Hbounds ltac:(assumption)).
  all: unfold cm_i32_code_count in *; destruct Hbounds as [? [? ?]]; try dump_pre_spatial; lia.
Qed.

Lemma proof_of_cm_emit_index_expr_safety_wit_5 : cm_emit_index_expr_safety_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_index_expr_safety_wit_5_split_goal_1.
  - Goal_apply proof_of_cm_emit_index_expr_safety_wit_5_split_goal_2.
Qed. 

Lemma proof_of_cm_emit_index_expr_return_wit_1_split_goal_spatial : cm_emit_index_expr_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in *. subst e lvalue_pre.
  unfold cm_expr_code_for.
  cbn [Z.eqb cm_emit_expr_pair cm_rcode_of cm_lcode_of].
  replace (pc_pre + (cm_rvalue_code_count policy p fid_pre left_ + 5)) with
    (pc_pre + cm_rvalue_code_count policy p fid_pre left_ + 5) by lia.
  repeat rewrite <- app_assoc. cbn [app].
  cancel.
Qed.

Lemma proof_of_cm_emit_index_expr_return_wit_1 : cm_emit_index_expr_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_index_expr_return_wit_1_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_index_expr_return_wit_2_split_goal_spatial : cm_emit_index_expr_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in *. subst e.
  assert (Hl : lvalue_pre = 1) by lia. subst lvalue_pre.
  unfold cm_expr_code_for, cm_optional_load.
  cbn [Z.eqb cm_emit_expr_pair cm_rcode_of cm_lcode_of].
  replace (pc_pre + (cm_rvalue_code_count policy p fid_pre left_ + 5)) with
    (pc_pre + cm_rvalue_code_count policy p fid_pre left_ + 5) by lia.
  repeat rewrite <- app_assoc. cbn [app].
  cancel.
Qed.

Lemma proof_of_cm_emit_index_expr_return_wit_2 : cm_emit_index_expr_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_index_expr_return_wit_2_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_index_expr_partial_solve_wit_1_pure_split_goal_1 : cm_emit_index_expr_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold cm_expr_shape; reflexivity).
Qed.

Lemma proof_of_cm_emit_index_expr_partial_solve_wit_1_pure_split_goal_2 : cm_emit_index_expr_partial_solve_wit_1_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(unfold cm_expr_shape; reflexivity).
Qed.

Lemma proof_of_cm_emit_index_expr_partial_solve_wit_1_pure : cm_emit_index_expr_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_index_expr_partial_solve_wit_1_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_index_expr_partial_solve_wit_1_pure_split_goal_2.
Qed.

Lemma proof_of_cm_emit_index_expr_partial_solve_wit_11_pure_split_goal_1 : cm_emit_index_expr_partial_solve_wit_11_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; congruence).
Qed.

Lemma proof_of_cm_emit_index_expr_partial_solve_wit_11_pure_split_goal_2 : cm_emit_index_expr_partial_solve_wit_11_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; congruence).
Qed.

Lemma proof_of_cm_emit_index_expr_partial_solve_wit_11_pure : cm_emit_index_expr_partial_solve_wit_11_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_index_expr_partial_solve_wit_11_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_index_expr_partial_solve_wit_11_pure_split_goal_2.
Qed.

Lemma proof_of_cm_emit_index_expr_partial_solve_wit_12_pure_split_goal_1 : cm_emit_index_expr_partial_solve_wit_12_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; congruence).
Qed.

Lemma proof_of_cm_emit_index_expr_partial_solve_wit_12_pure_split_goal_2 : cm_emit_index_expr_partial_solve_wit_12_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; congruence).
Qed.

Lemma proof_of_cm_emit_index_expr_partial_solve_wit_12_pure : cm_emit_index_expr_partial_solve_wit_12_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_index_expr_partial_solve_wit_12_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_index_expr_partial_solve_wit_12_pure_split_goal_2.
Qed.

Lemma proof_of_cm_emit_index_expr_partial_solve_wit_14_pure_split_goal_1 : cm_emit_index_expr_partial_solve_wit_14_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; congruence).
Qed.

Lemma proof_of_cm_emit_index_expr_partial_solve_wit_14_pure_split_goal_2 : cm_emit_index_expr_partial_solve_wit_14_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; congruence).
Qed.

Lemma proof_of_cm_emit_index_expr_partial_solve_wit_14_pure : cm_emit_index_expr_partial_solve_wit_14_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_index_expr_partial_solve_wit_14_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_index_expr_partial_solve_wit_14_pure_split_goal_2.
Qed.

Lemma proof_of_cm_emit_index_expr_which_implies_wit_1 : cm_emit_index_expr_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in *; subst e.
  rewrite cm_expr_rep_node; unfold cm_expr_node.
  cbn [cm_expr_payload cm_rep_expr_op].
  Intros xa xb xargs.
  Exists xb xa xargs.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed. 

Lemma proof_of_cm_emit_index_expr_which_implies_wit_2_split_goal_1 : cm_emit_index_expr_which_implies_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros.
  unfold cm_expr_shape in PreH22. subst e.
  pose proof (cm_expr_type_refs__constructor_facts_b _ _ _ _ PreH4 PreH6 PreH7 PreH14) as Hrefs.
  exact Hrefs.
Qed.

Lemma proof_of_cm_emit_index_expr_which_implies_wit_2_split_goal_2 : cm_emit_index_expr_which_implies_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros.
  unfold cm_expr_shape in PreH22. subst e.
  cbn [cm_expr_counts_representable] in PreH15.
  unfold cm_expr_count_node_representable in PreH15. cbn [cm_expr_type] in *. tauto.
Qed.

Lemma proof_of_cm_emit_index_expr_which_implies_wit_2_split_goal_3 : cm_emit_index_expr_which_implies_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros.
  unfold cm_expr_shape in PreH22. subst e.
  reflexivity.
Qed.

Lemma proof_of_cm_emit_index_expr_which_implies_wit_2_split_goal_4 : cm_emit_index_expr_which_implies_wit_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros.
  unfold cm_expr_shape in PreH22. subst e.
  cbn [cm_expr_counts_representable] in PreH15.
  assert (Hchild : cm_expr_counts_representable policy p fid right_) by tauto.
  destruct right_; cbn [cm_expr_counts_representable] in Hchild; unfold cm_expr_count_node_representable in Hchild; tauto.
Qed.

Lemma proof_of_cm_emit_index_expr_which_implies_wit_2_split_goal_5 : cm_emit_index_expr_which_implies_wit_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros.
  unfold cm_expr_shape in PreH22. subst e.
  cbn [cm_expr_wf] in PreH14.
  apply (cm_expr_type_refs__constructor_facts_b policy p f right_ PreH4 PreH6 PreH7).
  tauto.
Qed.

Lemma proof_of_cm_emit_index_expr_which_implies_wit_2_split_goal_6 : cm_emit_index_expr_which_implies_wit_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros.
  unfold cm_expr_shape in PreH22. subst e.
  cbn [cm_expr_counts_representable] in PreH15.
  assert (Hchild : cm_expr_counts_representable policy p fid right_) by tauto.
  destruct right_; cbn [cm_expr_counts_representable] in Hchild; unfold cm_expr_count_node_representable in Hchild; tauto.
Qed.

Lemma proof_of_cm_emit_index_expr_which_implies_wit_2_split_goal_7 : cm_emit_index_expr_which_implies_wit_2_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros.
  unfold cm_expr_shape in PreH22. subst e.
  cbn [cm_expr_counts_representable] in PreH15.
  tauto.
Qed.

Lemma proof_of_cm_emit_index_expr_which_implies_wit_2_split_goal_8 : cm_emit_index_expr_which_implies_wit_2_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros.
  unfold cm_expr_shape in PreH22. subst e.
  cbn [cm_expr_wf] in PreH14. tauto.
Qed.

Lemma proof_of_cm_emit_index_expr_which_implies_wit_2_split_goal_9 : cm_emit_index_expr_which_implies_wit_2_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros.
  unfold cm_expr_shape in PreH22. subst e.
  cbn [cm_expr_counts_representable] in PreH15.
  assert (Hchild : cm_expr_counts_representable policy p fid left_) by tauto.
  destruct left_; cbn [cm_expr_counts_representable] in Hchild; unfold cm_expr_count_node_representable in Hchild; tauto.
Qed.

Lemma proof_of_cm_emit_index_expr_which_implies_wit_2_split_goal_10 : cm_emit_index_expr_which_implies_wit_2_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros.
  unfold cm_expr_shape in PreH22. subst e.
  cbn [cm_expr_wf] in PreH14.
  apply (cm_expr_type_refs__constructor_facts_b policy p f left_ PreH4 PreH6 PreH7).
  tauto.
Qed.

Lemma proof_of_cm_emit_index_expr_which_implies_wit_2_split_goal_11 : cm_emit_index_expr_which_implies_wit_2_split_goal_11.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros.
  unfold cm_expr_shape in PreH22. subst e.
  cbn [cm_expr_counts_representable] in PreH15.
  assert (Hchild : cm_expr_counts_representable policy p fid left_) by tauto.
  destruct left_; cbn [cm_expr_counts_representable] in Hchild; unfold cm_expr_count_node_representable in Hchild; tauto.
Qed.

Lemma proof_of_cm_emit_index_expr_which_implies_wit_2_split_goal_12 : cm_emit_index_expr_which_implies_wit_2_split_goal_12.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros.
  unfold cm_expr_shape in PreH22. subst e.
  cbn [cm_expr_counts_representable] in PreH15.
  tauto.
Qed.

Lemma proof_of_cm_emit_index_expr_which_implies_wit_2_split_goal_13 : cm_emit_index_expr_which_implies_wit_2_split_goal_13.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros.
  unfold cm_expr_shape in PreH22. subst e.
  cbn [cm_expr_wf] in PreH14. tauto.
Qed.

Lemma proof_of_cm_emit_index_expr_which_implies_wit_2_split_goal_14 : cm_emit_index_expr_which_implies_wit_2_split_goal_14.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros.
  unfold cm_expr_shape in PreH22. subst e.
  pose proof (cm_expr_type_refs__constructor_facts_b _ _ _ _ PreH4 PreH6 PreH7 PreH14) as Hrefs.
  exact Hrefs.
Qed.

Lemma proof_of_cm_emit_index_expr_which_implies_wit_2_split_goal_15 : cm_emit_index_expr_which_implies_wit_2_split_goal_15.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros.
  unfold cm_expr_shape in PreH22. subst e.
  cbn [cm_expr_counts_representable] in PreH15.
  unfold cm_expr_count_node_representable in PreH15. cbn [cm_expr_type] in *. tauto.
Qed.

Lemma proof_of_cm_emit_index_expr_which_implies_wit_2_split_goal_16 : cm_emit_index_expr_which_implies_wit_2_split_goal_16.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros.
  unfold cm_temp_offset in *.
  subst f.
  lia.
Qed.

Lemma proof_of_cm_emit_index_expr_which_implies_wit_2_split_goal_17 : cm_emit_index_expr_which_implies_wit_2_split_goal_17.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros.
  unfold cm_temp_offset in *.
  subst f.
  pose proof (cm_slots_size_nonnegative__call_bounds _ _ PreH6).
  pose proof (cm_slots_size_nonnegative__call_bounds _ _ PreH7).
  lia.
Qed.

Lemma proof_of_cm_emit_index_expr_which_implies_wit_2 : cm_emit_index_expr_which_implies_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_index_expr_which_implies_wit_2_split_goal_1.
  - Goal_apply proof_of_cm_emit_index_expr_which_implies_wit_2_split_goal_2.
  - Goal_apply proof_of_cm_emit_index_expr_which_implies_wit_2_split_goal_3.
  - Goal_apply proof_of_cm_emit_index_expr_which_implies_wit_2_split_goal_4.
  - Goal_apply proof_of_cm_emit_index_expr_which_implies_wit_2_split_goal_5.
  - Goal_apply proof_of_cm_emit_index_expr_which_implies_wit_2_split_goal_6.
  - Goal_apply proof_of_cm_emit_index_expr_which_implies_wit_2_split_goal_7.
  - Goal_apply proof_of_cm_emit_index_expr_which_implies_wit_2_split_goal_8.
  - Goal_apply proof_of_cm_emit_index_expr_which_implies_wit_2_split_goal_9.
  - Goal_apply proof_of_cm_emit_index_expr_which_implies_wit_2_split_goal_10.
  - Goal_apply proof_of_cm_emit_index_expr_which_implies_wit_2_split_goal_11.
  - Goal_apply proof_of_cm_emit_index_expr_which_implies_wit_2_split_goal_12.
  - Goal_apply proof_of_cm_emit_index_expr_which_implies_wit_2_split_goal_13.
  - Goal_apply proof_of_cm_emit_index_expr_which_implies_wit_2_split_goal_14.
  - Goal_apply proof_of_cm_emit_index_expr_which_implies_wit_2_split_goal_15.
  - Goal_apply proof_of_cm_emit_index_expr_which_implies_wit_2_split_goal_16.
  - Goal_apply proof_of_cm_emit_index_expr_which_implies_wit_2_split_goal_17.
Qed. 

Lemma proof_of_cm_emit_index_expr_which_implies_wit_3_split_goal_spatial : cm_emit_index_expr_which_implies_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in *. subst e base_count element_size.
  unfold cm_expr_code_for, cm_optional_load.
  destruct (Z.eqb lvalue 0); cbn [Z.eqb cm_emit_expr_pair cm_rcode_of cm_lcode_of].
  all: replace (pc + (cm_rvalue_code_count policy p fid left_ + 5)) with
    (pc + cm_rvalue_code_count policy p fid left_ + 5) by lia.
  all: repeat rewrite <- app_assoc; cbn [app]; try rewrite app_nil_r; cancel.
Qed.

Lemma proof_of_cm_emit_index_expr_which_implies_wit_3 : cm_emit_index_expr_which_implies_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_index_expr_which_implies_wit_3_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_index_expr_which_implies_wit_4_split_goal_1 : cm_emit_index_expr_which_implies_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold cm_i32_code_count in *; lia).
  all: unfold cm_expr_shape in *; subst.
  all: pose proof (cm_index_code_bounds__index_bounds policy p fid pc temp left_ right_ ty_ lvalue) as Hbounds.
  all: specialize (Hbounds ltac:(assumption) ltac:(assumption)).
  all: unfold cm_i32_code_count in *; destruct Hbounds as [? [? ?]]; try dump_pre_spatial; lia.
Qed.

Lemma proof_of_cm_emit_index_expr_which_implies_wit_4_split_goal_2 : cm_emit_index_expr_which_implies_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(unfold cm_i32_code_count in *; lia).
  all: unfold cm_expr_shape in *; subst.
  all: pose proof (cm_index_temp_bounds__index_bounds left_ right_ ty_ lvalue temp temp_limit) as Hbounds.
  all: specialize (Hbounds ltac:(assumption)).
  all: unfold cm_i32_code_count in *; destruct Hbounds as [? [? ?]]; try dump_pre_spatial; lia.
Qed.

Lemma proof_of_cm_emit_index_expr_which_implies_wit_4 : cm_emit_index_expr_which_implies_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_index_expr_which_implies_wit_4_split_goal_1.
  - Goal_apply proof_of_cm_emit_index_expr_which_implies_wit_4_split_goal_2.
Qed. 

Lemma proof_of_cm_emit_index_expr_which_implies_wit_5_split_goal_1 : cm_emit_index_expr_which_implies_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold cm_i32_code_count in *; lia).
  all: unfold cm_expr_shape in *; subst.
  all: pose proof (cm_index_code_bounds__index_bounds policy p fid pc temp left_ right_ ty_ lvalue) as Hbounds.
  all: specialize (Hbounds ltac:(assumption) ltac:(assumption)).
  all: unfold cm_i32_code_count in *; destruct Hbounds as [? [? ?]]; try dump_pre_spatial; lia.
Qed.

Lemma proof_of_cm_emit_index_expr_which_implies_wit_5_split_goal_2 : cm_emit_index_expr_which_implies_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(unfold cm_i32_code_count in *; lia).
  all: unfold cm_expr_shape in *; subst.
  all: pose proof (cm_index_code_bounds__index_bounds policy p fid pc temp left_ right_ ty_ lvalue) as Hbounds.
  all: specialize (Hbounds ltac:(assumption) ltac:(assumption)).
  all: unfold cm_i32_code_count in *; destruct Hbounds as [? [? ?]]; try dump_pre_spatial; lia.
Qed.

Lemma proof_of_cm_emit_index_expr_which_implies_wit_5_split_goal_3 : cm_emit_index_expr_which_implies_wit_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(unfold cm_i32_code_count in *; lia).
  all: unfold cm_expr_shape in *; subst.
  all: pose proof (cm_index_temp_bounds__index_bounds left_ right_ ty_ lvalue temp temp_limit) as Hbounds.
  all: specialize (Hbounds ltac:(assumption)).
  all: unfold cm_i32_code_count in *; destruct Hbounds as [? [? ?]]; try dump_pre_spatial; lia.
Qed.

Lemma proof_of_cm_emit_index_expr_which_implies_wit_5_split_goal_4 : cm_emit_index_expr_which_implies_wit_5_split_goal_4.
Proof.
  LLM_pre_process ltac:(unfold cm_i32_code_count in *; lia).
  all: unfold cm_expr_shape in *; subst.
  all: pose proof (cm_index_temp_bounds__index_bounds left_ right_ ty_ lvalue temp temp_limit) as Hbounds.
  all: specialize (Hbounds ltac:(assumption)).
  all: unfold cm_i32_code_count in *; destruct Hbounds as [? [? ?]]; try dump_pre_spatial; lia.
Qed.

Lemma proof_of_cm_emit_index_expr_which_implies_wit_5 : cm_emit_index_expr_which_implies_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_index_expr_which_implies_wit_5_split_goal_1.
  - Goal_apply proof_of_cm_emit_index_expr_which_implies_wit_5_split_goal_2.
  - Goal_apply proof_of_cm_emit_index_expr_which_implies_wit_5_split_goal_3.
  - Goal_apply proof_of_cm_emit_index_expr_which_implies_wit_5_split_goal_4.
Qed. 

Lemma proof_of_cm_emit_index_expr_which_implies_wit_6_split_goal_spatial : cm_emit_index_expr_which_implies_wit_6_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hl : lvalue = 0) by lia. subst lvalue.
  unfold cm_optional_load. cbn [Z.eqb]. cancel.
Qed.

Lemma proof_of_cm_emit_index_expr_which_implies_wit_6 : cm_emit_index_expr_which_implies_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_index_expr_which_implies_wit_6_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_index_expr_which_implies_wit_7_split_goal_spatial : cm_emit_index_expr_which_implies_wit_7_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (cm_expr_rep_node expr0 e).
  unfold cm_expr_node.
  Exists xa xb xargs.
  unfold cm_expr_shape in PreH10. subst e.
  cbn [cm_expr_payload cm_rep_expr_op].
  split_pure_spatial.
  - cancel.
    cancel (&(expr0 # "cm_expr" ->ₛ "kind") # Int |-> cm_rep_expr_kind (CMIndexE left_ right_ ty_)).
    cancel (&(expr0 # "cm_expr" ->ₛ "op") # Int |-> cm_rep_expr_op (CMIndexE left_ right_ ty_)).
    cancel (&(expr0 # "cm_expr" ->ₛ "ty") # Int |-> cm_type_encode (cm_expr_type (CMIndexE left_ right_ ty_))).
    cancel (&(expr0 # "cm_expr" ->ₛ "value") # Int64 |-> cm_rep_expr_value (CMIndexE left_ right_ ty_)).
    cancel (&(expr0 # "cm_expr" ->ₛ "a") # Ptr |-> xa).
    cancel (&(expr0 # "cm_expr" ->ₛ "b") # Ptr |-> xb).
    cancel (&(expr0 # "cm_expr" ->ₛ "args") # Ptr |-> xargs).
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_cm_emit_index_expr_which_implies_wit_7 : cm_emit_index_expr_which_implies_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_index_expr_which_implies_wit_7_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_assignment_expr_safety_wit_2_split_goal_1 : cm_emit_assignment_expr_safety_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  unfold cm_expr_shape in *. subst.
  unfold cm_i32_code_count in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lazymatch goal with
  | H : ?pc + Zlength (cm_expr_code_for ?pol ?p ?fid ?pc ?temp (CMAssignE ?a ?b ?ty) ?lv) <= _ |- _ =>
    assert (Hz : lv = 0) by lia; try rewrite Hz in *;
    let HB := fresh "Hbounds" in
    pose proof (cm_assignment_prefix_bounds__assignment_bounds pol p fid pc temp a b ty) as HB;
    specialize (HB ltac:(unfold cm_i32_code_count; split; lia) ltac:(unfold cm_i32_code_count; split; lia));
    destruct HB as [? [? ?]]
  end.
  unfold cm_expr_code_for; cbn [Z.eqb].
  repeat match goal with
  | |- context [Zlength (cm_lcode_of (cm_emit_expr_pair ?pol ?p ?fid ?pc ?temp ?a))] =>
    rewrite (proj1 (cm_emit_pair_lengths__store_bounds pol p fid a pc temp))
  end.
  unfold cm_i32_code_count in *; lia || int_auto.
Qed.

Lemma proof_of_cm_emit_assignment_expr_safety_wit_2_split_goal_2 : cm_emit_assignment_expr_safety_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  unfold cm_expr_shape in *. subst.
  unfold cm_i32_code_count in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lazymatch goal with
  | H : ?pc + Zlength (cm_expr_code_for ?pol ?p ?fid ?pc ?temp (CMAssignE ?a ?b ?ty) ?lv) <= _ |- _ =>
    assert (Hz : lv = 0) by lia; try rewrite Hz in *;
    let HB := fresh "Hbounds" in
    pose proof (cm_assignment_prefix_bounds__assignment_bounds pol p fid pc temp a b ty) as HB;
    specialize (HB ltac:(unfold cm_i32_code_count; split; lia) ltac:(unfold cm_i32_code_count; split; lia));
    destruct HB as [? [? ?]]
  end.
  unfold cm_expr_code_for; cbn [Z.eqb].
  repeat match goal with
  | |- context [Zlength (cm_lcode_of (cm_emit_expr_pair ?pol ?p ?fid ?pc ?temp ?a))] =>
    rewrite (proj1 (cm_emit_pair_lengths__store_bounds pol p fid a pc temp))
  end.
  unfold cm_i32_code_count in *; lia || int_auto.
Qed.

Lemma proof_of_cm_emit_assignment_expr_safety_wit_2 : cm_emit_assignment_expr_safety_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_assignment_expr_safety_wit_2_split_goal_1.
  - Goal_apply proof_of_cm_emit_assignment_expr_safety_wit_2_split_goal_2.
Qed. 

Lemma proof_of_cm_emit_assignment_expr_safety_wit_3_split_goal_1 : cm_emit_assignment_expr_safety_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  unfold cm_expr_shape in *. subst.
  unfold cm_i32_code_count in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lazymatch goal with
  | H : ?pc + Zlength (cm_expr_code_for ?pol ?p ?fid ?pc ?temp (CMAssignE ?a ?b ?ty) ?lv) <= _ |- _ =>
    assert (Hz : lv = 0) by lia; try rewrite Hz in *;
    let HB := fresh "Hbounds" in
    pose proof (cm_assignment_prefix_bounds__assignment_bounds pol p fid pc temp a b ty) as HB;
    specialize (HB ltac:(unfold cm_i32_code_count; split; lia) ltac:(unfold cm_i32_code_count; split; lia));
    destruct HB as [? [? ?]]
  end.
  unfold cm_expr_code_for; cbn [Z.eqb].
  repeat match goal with
  | |- context [Zlength (cm_lcode_of (cm_emit_expr_pair ?pol ?p ?fid ?pc ?temp ?a))] =>
    rewrite (proj1 (cm_emit_pair_lengths__store_bounds pol p fid a pc temp))
  end.
  unfold cm_i32_code_count in *; lia || int_auto.
Qed.

Lemma proof_of_cm_emit_assignment_expr_safety_wit_3_split_goal_2 : cm_emit_assignment_expr_safety_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  unfold cm_expr_shape in *. subst.
  unfold cm_i32_code_count in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lazymatch goal with
  | H : ?pc + Zlength (cm_expr_code_for ?pol ?p ?fid ?pc ?temp (CMAssignE ?a ?b ?ty) ?lv) <= _ |- _ =>
    assert (Hz : lv = 0) by lia; try rewrite Hz in *;
    let HB := fresh "Hbounds" in
    pose proof (cm_assignment_prefix_bounds__assignment_bounds pol p fid pc temp a b ty) as HB;
    specialize (HB ltac:(unfold cm_i32_code_count; split; lia) ltac:(unfold cm_i32_code_count; split; lia));
    destruct HB as [? [? ?]]
  end.
  unfold cm_expr_code_for; cbn [Z.eqb].
  repeat match goal with
  | |- context [Zlength (cm_lcode_of (cm_emit_expr_pair ?pol ?p ?fid ?pc ?temp ?a))] =>
    rewrite (proj1 (cm_emit_pair_lengths__store_bounds pol p fid a pc temp))
  end.
  unfold cm_i32_code_count in *; lia || int_auto.
Qed.

Lemma proof_of_cm_emit_assignment_expr_safety_wit_3 : cm_emit_assignment_expr_safety_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_assignment_expr_safety_wit_3_split_goal_1.
  - Goal_apply proof_of_cm_emit_assignment_expr_safety_wit_3_split_goal_2.
Qed. 

Lemma proof_of_cm_emit_assignment_expr_safety_wit_5_split_goal_1 : cm_emit_assignment_expr_safety_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  unfold cm_expr_shape in *. subst.
  try (assert (lvalue = 0) by lia; subst lvalue).
  pose proof (cm_expr_temps_nonnegative__assignment_bounds right_) as Hnonneg.
  unfold cm_expr_temps_for, cm_ltemps, cm_rtemps in *.
  repeat match goal with
  | H : context [if ?lv =? 0 then _ else _] |- _ =>
    let Hz := fresh "Hz" in assert (Hz : lv = 0) by lia; try rewrite Hz in H; cbn [Z.eqb] in H
  end.
  cbn [Z.eqb cm_expr_tpair cm_tleft cm_tright] in *.
  unfold cm_imax in *.
  pose proof (Z.le_max_l (cm_tleft (cm_expr_tpair left_)) (1+cm_tright (cm_expr_tpair right_))).
  pose proof (Z.le_max_r (cm_tleft (cm_expr_tpair left_)) (1+cm_tright (cm_expr_tpair right_))).
  lia || int_auto.
Qed.

Lemma proof_of_cm_emit_assignment_expr_safety_wit_5_split_goal_2 : cm_emit_assignment_expr_safety_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cm_emit_assignment_expr_safety_wit_5 : cm_emit_assignment_expr_safety_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_assignment_expr_safety_wit_5_split_goal_1.
  - Goal_apply proof_of_cm_emit_assignment_expr_safety_wit_5_split_goal_2.
Qed. 

Lemma proof_of_cm_emit_assignment_expr_return_wit_1_split_goal_spatial : cm_emit_assignment_expr_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in *.
  subst e.
  assert (lvalue_pre = 0) by lia.
  subst lvalue_pre.
  unfold cm_expr_code_for.
  simpl Z.eqb.
  cbn [cm_emit_expr_pair cm_lcode_of cm_rcode_of].
  repeat rewrite <- app_assoc.
  repeat rewrite <- Z.add_assoc.
  cancel.
Qed.

Lemma proof_of_cm_emit_assignment_expr_return_wit_1 : cm_emit_assignment_expr_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_assignment_expr_return_wit_1_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_assignment_expr_return_wit_2_split_goal_spatial : cm_emit_assignment_expr_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in *.
  subst e.
  assert (lvalue_pre = 1) by lia.
  subst lvalue_pre.
  unfold cm_expr_code_for.
  simpl Z.eqb.
  cbn [cm_emit_expr_pair cm_lcode_of cm_rcode_of].
  rewrite app_nil_r.
  cbn [app].
  cancel.
Qed.

Lemma proof_of_cm_emit_assignment_expr_return_wit_2 : cm_emit_assignment_expr_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_assignment_expr_return_wit_2_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_assignment_expr_partial_solve_wit_1_pure_split_goal_1 : cm_emit_assignment_expr_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold cm_expr_shape; reflexivity).
Qed.

Lemma proof_of_cm_emit_assignment_expr_partial_solve_wit_1_pure_split_goal_2 : cm_emit_assignment_expr_partial_solve_wit_1_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(unfold cm_expr_shape; reflexivity).
Qed.

Lemma proof_of_cm_emit_assignment_expr_partial_solve_wit_1_pure : cm_emit_assignment_expr_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_assignment_expr_partial_solve_wit_1_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_assignment_expr_partial_solve_wit_1_pure_split_goal_2.
Qed.

Lemma proof_of_cm_emit_assignment_expr_which_implies_wit_1 : cm_emit_assignment_expr_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in *; subst e.
  rewrite cm_expr_rep_node; unfold cm_expr_node.
  cbn [cm_expr_payload cm_rep_expr_op].
  Intros xa xb xargs.
  Exists xb xa xargs.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed. 

Lemma proof_of_cm_emit_assignment_expr_which_implies_wit_2_split_goal_1 : cm_emit_assignment_expr_which_implies_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros.
  unfold cm_expr_shape in PreH22. subst e.
  pose proof (cm_expr_type_refs__constructor_facts_b _ _ _ _ PreH4 PreH6 PreH7 PreH14) as Hrefs.
  exact Hrefs.
Qed.

Lemma proof_of_cm_emit_assignment_expr_which_implies_wit_2_split_goal_2 : cm_emit_assignment_expr_which_implies_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros.
  unfold cm_expr_shape in PreH22. subst e.
  cbn [cm_expr_counts_representable] in PreH15.
  unfold cm_expr_count_node_representable in PreH15. cbn [cm_expr_type] in *. tauto.
Qed.

Lemma proof_of_cm_emit_assignment_expr_which_implies_wit_2_split_goal_3 : cm_emit_assignment_expr_which_implies_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros.
  unfold cm_expr_shape in PreH22. subst e.
  reflexivity.
Qed.

Lemma proof_of_cm_emit_assignment_expr_which_implies_wit_2_split_goal_4 : cm_emit_assignment_expr_which_implies_wit_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros.
  unfold cm_expr_shape in PreH22. subst e.
  cbn [cm_expr_counts_representable] in PreH15.
  assert (Hchild : cm_expr_counts_representable policy p fid right_) by tauto.
  destruct right_; cbn [cm_expr_counts_representable] in Hchild; unfold cm_expr_count_node_representable in Hchild; tauto.
Qed.

Lemma proof_of_cm_emit_assignment_expr_which_implies_wit_2_split_goal_5 : cm_emit_assignment_expr_which_implies_wit_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros.
  unfold cm_expr_shape in PreH22. subst e.
  cbn [cm_expr_wf] in PreH14.
  apply (cm_expr_type_refs__constructor_facts_b policy p f right_ PreH4 PreH6 PreH7).
  tauto.
Qed.

Lemma proof_of_cm_emit_assignment_expr_which_implies_wit_2_split_goal_6 : cm_emit_assignment_expr_which_implies_wit_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros.
  unfold cm_expr_shape in PreH22. subst e.
  cbn [cm_expr_counts_representable] in PreH15.
  assert (Hchild : cm_expr_counts_representable policy p fid right_) by tauto.
  destruct right_; cbn [cm_expr_counts_representable] in Hchild; unfold cm_expr_count_node_representable in Hchild; tauto.
Qed.

Lemma proof_of_cm_emit_assignment_expr_which_implies_wit_2_split_goal_7 : cm_emit_assignment_expr_which_implies_wit_2_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros.
  unfold cm_expr_shape in PreH22. subst e.
  cbn [cm_expr_counts_representable] in PreH15.
  tauto.
Qed.

Lemma proof_of_cm_emit_assignment_expr_which_implies_wit_2_split_goal_8 : cm_emit_assignment_expr_which_implies_wit_2_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros.
  unfold cm_expr_shape in PreH22. subst e.
  cbn [cm_expr_wf] in PreH14. tauto.
Qed.

Lemma proof_of_cm_emit_assignment_expr_which_implies_wit_2_split_goal_9 : cm_emit_assignment_expr_which_implies_wit_2_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros.
  unfold cm_expr_shape in PreH22. subst e.
  cbn [cm_expr_counts_representable] in PreH15.
  assert (Hchild : cm_expr_counts_representable policy p fid left_) by tauto.
  destruct left_; cbn [cm_expr_counts_representable] in Hchild; unfold cm_expr_count_node_representable in Hchild; tauto.
Qed.

Lemma proof_of_cm_emit_assignment_expr_which_implies_wit_2_split_goal_10 : cm_emit_assignment_expr_which_implies_wit_2_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros.
  unfold cm_expr_shape in PreH22. subst e.
  cbn [cm_expr_wf] in PreH14.
  apply (cm_expr_type_refs__constructor_facts_b policy p f left_ PreH4 PreH6 PreH7).
  tauto.
Qed.

Lemma proof_of_cm_emit_assignment_expr_which_implies_wit_2_split_goal_11 : cm_emit_assignment_expr_which_implies_wit_2_split_goal_11.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros.
  unfold cm_expr_shape in PreH22. subst e.
  cbn [cm_expr_counts_representable] in PreH15.
  assert (Hchild : cm_expr_counts_representable policy p fid left_) by tauto.
  destruct left_; cbn [cm_expr_counts_representable] in Hchild; unfold cm_expr_count_node_representable in Hchild; tauto.
Qed.

Lemma proof_of_cm_emit_assignment_expr_which_implies_wit_2_split_goal_12 : cm_emit_assignment_expr_which_implies_wit_2_split_goal_12.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros.
  unfold cm_expr_shape in PreH22. subst e.
  cbn [cm_expr_counts_representable] in PreH15.
  tauto.
Qed.

Lemma proof_of_cm_emit_assignment_expr_which_implies_wit_2_split_goal_13 : cm_emit_assignment_expr_which_implies_wit_2_split_goal_13.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros.
  unfold cm_expr_shape in PreH22. subst e.
  cbn [cm_expr_wf] in PreH14. tauto.
Qed.

Lemma proof_of_cm_emit_assignment_expr_which_implies_wit_2_split_goal_14 : cm_emit_assignment_expr_which_implies_wit_2_split_goal_14.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros.
  unfold cm_expr_shape in PreH22. subst e.
  pose proof (cm_expr_type_refs__constructor_facts_b _ _ _ _ PreH4 PreH6 PreH7 PreH14) as Hrefs.
  exact Hrefs.
Qed.

Lemma proof_of_cm_emit_assignment_expr_which_implies_wit_2_split_goal_15 : cm_emit_assignment_expr_which_implies_wit_2_split_goal_15.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros.
  unfold cm_expr_shape in PreH22. subst e.
  cbn [cm_expr_counts_representable] in PreH15.
  unfold cm_expr_count_node_representable in PreH15. cbn [cm_expr_type] in *. tauto.
Qed.

Lemma proof_of_cm_emit_assignment_expr_which_implies_wit_2_split_goal_16 : cm_emit_assignment_expr_which_implies_wit_2_split_goal_16.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros.
  unfold cm_temp_offset in *.
  subst f.
  lia.
Qed.

Lemma proof_of_cm_emit_assignment_expr_which_implies_wit_2_split_goal_17 : cm_emit_assignment_expr_which_implies_wit_2_split_goal_17.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros.
  unfold cm_temp_offset in *.
  subst f.
  pose proof (cm_slots_size_nonnegative__call_bounds _ _ PreH6).
  pose proof (cm_slots_size_nonnegative__call_bounds _ _ PreH7).
  lia.
Qed.

Lemma proof_of_cm_emit_assignment_expr_which_implies_wit_2 : cm_emit_assignment_expr_which_implies_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_assignment_expr_which_implies_wit_2_split_goal_1.
  - Goal_apply proof_of_cm_emit_assignment_expr_which_implies_wit_2_split_goal_2.
  - Goal_apply proof_of_cm_emit_assignment_expr_which_implies_wit_2_split_goal_3.
  - Goal_apply proof_of_cm_emit_assignment_expr_which_implies_wit_2_split_goal_4.
  - Goal_apply proof_of_cm_emit_assignment_expr_which_implies_wit_2_split_goal_5.
  - Goal_apply proof_of_cm_emit_assignment_expr_which_implies_wit_2_split_goal_6.
  - Goal_apply proof_of_cm_emit_assignment_expr_which_implies_wit_2_split_goal_7.
  - Goal_apply proof_of_cm_emit_assignment_expr_which_implies_wit_2_split_goal_8.
  - Goal_apply proof_of_cm_emit_assignment_expr_which_implies_wit_2_split_goal_9.
  - Goal_apply proof_of_cm_emit_assignment_expr_which_implies_wit_2_split_goal_10.
  - Goal_apply proof_of_cm_emit_assignment_expr_which_implies_wit_2_split_goal_11.
  - Goal_apply proof_of_cm_emit_assignment_expr_which_implies_wit_2_split_goal_12.
  - Goal_apply proof_of_cm_emit_assignment_expr_which_implies_wit_2_split_goal_13.
  - Goal_apply proof_of_cm_emit_assignment_expr_which_implies_wit_2_split_goal_14.
  - Goal_apply proof_of_cm_emit_assignment_expr_which_implies_wit_2_split_goal_15.
  - Goal_apply proof_of_cm_emit_assignment_expr_which_implies_wit_2_split_goal_16.
  - Goal_apply proof_of_cm_emit_assignment_expr_which_implies_wit_2_split_goal_17.
Qed. 

Lemma proof_of_cm_emit_assignment_expr_which_implies_wit_3_split_goal_spatial : cm_emit_assignment_expr_which_implies_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in *.
  subst e left_count.
  assert (lvalue = 0) by lia.
  subst lvalue.
  unfold cm_expr_code_for.
  simpl Z.eqb.
  cbn [cm_emit_expr_pair cm_lcode_of cm_rcode_of].
  repeat rewrite <- app_assoc.
  repeat rewrite <- Z.add_assoc.
  cancel.
Qed.

Lemma proof_of_cm_emit_assignment_expr_which_implies_wit_3 : cm_emit_assignment_expr_which_implies_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_assignment_expr_which_implies_wit_3_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_assignment_expr_which_implies_wit_4_split_goal_1 : cm_emit_assignment_expr_which_implies_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  unfold cm_expr_shape in *. subst.
  unfold cm_i32_code_count in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lazymatch goal with
  | H : ?pc + Zlength (cm_expr_code_for ?pol ?p ?fid ?pc ?temp (CMAssignE ?a ?b ?ty) ?lv) <= _ |- _ =>
    assert (Hz : lv = 0) by lia; try rewrite Hz in *;
    let HB := fresh "Hbounds" in
    pose proof (cm_assignment_prefix_bounds__assignment_bounds pol p fid pc temp a b ty) as HB;
    specialize (HB ltac:(unfold cm_i32_code_count; split; lia) ltac:(unfold cm_i32_code_count; split; lia));
    destruct HB as [? [? ?]]
  end.
  unfold cm_expr_code_for; cbn [Z.eqb].
  repeat match goal with
  | |- context [Zlength (cm_lcode_of (cm_emit_expr_pair ?pol ?p ?fid ?pc ?temp ?a))] =>
    rewrite (proj1 (cm_emit_pair_lengths__store_bounds pol p fid a pc temp))
  end.
  unfold cm_i32_code_count in *; lia || int_auto.
Qed.

Lemma proof_of_cm_emit_assignment_expr_which_implies_wit_4_split_goal_2 : cm_emit_assignment_expr_which_implies_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  unfold cm_expr_shape in *. subst.
  try (assert (lvalue = 0) by lia; subst lvalue).
  pose proof (cm_expr_temps_nonnegative__assignment_bounds right_) as Hnonneg.
  unfold cm_expr_temps_for, cm_ltemps, cm_rtemps in *.
  repeat match goal with
  | H : context [if ?lv =? 0 then _ else _] |- _ =>
    let Hz := fresh "Hz" in assert (Hz : lv = 0) by lia; try rewrite Hz in H; cbn [Z.eqb] in H
  end.
  cbn [Z.eqb cm_expr_tpair cm_tleft cm_tright] in *.
  unfold cm_imax in *.
  pose proof (Z.le_max_l (cm_tleft (cm_expr_tpair left_)) (1+cm_tright (cm_expr_tpair right_))).
  pose proof (Z.le_max_r (cm_tleft (cm_expr_tpair left_)) (1+cm_tright (cm_expr_tpair right_))).
  lia || int_auto.
Qed.

Lemma proof_of_cm_emit_assignment_expr_which_implies_wit_4 : cm_emit_assignment_expr_which_implies_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_assignment_expr_which_implies_wit_4_split_goal_1.
  - Goal_apply proof_of_cm_emit_assignment_expr_which_implies_wit_4_split_goal_2.
Qed. 

Lemma proof_of_cm_emit_assignment_expr_which_implies_wit_5_split_goal_1 : cm_emit_assignment_expr_which_implies_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  unfold cm_expr_shape in *. subst.
  unfold cm_i32_code_count in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lazymatch goal with
  | H : ?pc + Zlength (cm_expr_code_for ?pol ?p ?fid ?pc ?temp (CMAssignE ?a ?b ?ty) ?lv) <= _ |- _ =>
    assert (Hz : lv = 0) by lia; try rewrite Hz in *;
    let HB := fresh "Hbounds" in
    pose proof (cm_assignment_prefix_bounds__assignment_bounds pol p fid pc temp a b ty) as HB;
    specialize (HB ltac:(unfold cm_i32_code_count; split; lia) ltac:(unfold cm_i32_code_count; split; lia));
    destruct HB as [? [? ?]]
  end.
  unfold cm_expr_code_for; cbn [Z.eqb].
  repeat match goal with
  | |- context [Zlength (cm_lcode_of (cm_emit_expr_pair ?pol ?p ?fid ?pc ?temp ?a))] =>
    rewrite (proj1 (cm_emit_pair_lengths__store_bounds pol p fid a pc temp))
  end.
  unfold cm_i32_code_count in *; lia || int_auto.
Qed.

Lemma proof_of_cm_emit_assignment_expr_which_implies_wit_5_split_goal_2 : cm_emit_assignment_expr_which_implies_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  unfold cm_expr_shape in *. subst.
  unfold cm_i32_code_count in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  lazymatch goal with
  | H : ?pc + Zlength (cm_expr_code_for ?pol ?p ?fid ?pc ?temp (CMAssignE ?a ?b ?ty) ?lv) <= _ |- _ =>
    assert (Hz : lv = 0) by lia; try rewrite Hz in *;
    let HB := fresh "Hbounds" in
    pose proof (cm_assignment_prefix_bounds__assignment_bounds pol p fid pc temp a b ty) as HB;
    specialize (HB ltac:(unfold cm_i32_code_count; split; lia) ltac:(unfold cm_i32_code_count; split; lia));
    destruct HB as [? [? ?]]
  end.
  unfold cm_expr_code_for; cbn [Z.eqb].
  repeat match goal with
  | |- context [Zlength (cm_lcode_of (cm_emit_expr_pair ?pol ?p ?fid ?pc ?temp ?a))] =>
    rewrite (proj1 (cm_emit_pair_lengths__store_bounds pol p fid a pc temp))
  end.
  unfold cm_i32_code_count in *; lia || int_auto.
Qed.

Lemma proof_of_cm_emit_assignment_expr_which_implies_wit_5_split_goal_3 : cm_emit_assignment_expr_which_implies_wit_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  unfold cm_expr_shape in *. subst.
  try (assert (lvalue = 0) by lia; subst lvalue).
  pose proof (cm_expr_temps_nonnegative__assignment_bounds right_) as Hnonneg.
  unfold cm_expr_temps_for, cm_ltemps, cm_rtemps in *.
  repeat match goal with
  | H : context [if ?lv =? 0 then _ else _] |- _ =>
    let Hz := fresh "Hz" in assert (Hz : lv = 0) by lia; try rewrite Hz in H; cbn [Z.eqb] in H
  end.
  cbn [Z.eqb cm_expr_tpair cm_tleft cm_tright] in *.
  unfold cm_imax in *.
  pose proof (Z.le_max_l (cm_tleft (cm_expr_tpair left_)) (1+cm_tright (cm_expr_tpair right_))).
  pose proof (Z.le_max_r (cm_tleft (cm_expr_tpair left_)) (1+cm_tright (cm_expr_tpair right_))).
  lia || int_auto.
Qed.

Lemma proof_of_cm_emit_assignment_expr_which_implies_wit_5_split_goal_4 : cm_emit_assignment_expr_which_implies_wit_5_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  unfold cm_expr_shape in *. subst.
  try (assert (lvalue = 0) by lia; subst lvalue).
  pose proof (cm_expr_temps_nonnegative__assignment_bounds right_) as Hnonneg.
  unfold cm_expr_temps_for, cm_ltemps, cm_rtemps in *.
  repeat match goal with
  | H : context [if ?lv =? 0 then _ else _] |- _ =>
    let Hz := fresh "Hz" in assert (Hz : lv = 0) by lia; try rewrite Hz in H; cbn [Z.eqb] in H
  end.
  cbn [Z.eqb cm_expr_tpair cm_tleft cm_tright] in *.
  unfold cm_imax in *.
  pose proof (Z.le_max_l (cm_tleft (cm_expr_tpair left_)) (1+cm_tright (cm_expr_tpair right_))).
  pose proof (Z.le_max_r (cm_tleft (cm_expr_tpair left_)) (1+cm_tright (cm_expr_tpair right_))).
  lia || int_auto.
Qed.

Lemma proof_of_cm_emit_assignment_expr_which_implies_wit_5 : cm_emit_assignment_expr_which_implies_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_assignment_expr_which_implies_wit_5_split_goal_1.
  - Goal_apply proof_of_cm_emit_assignment_expr_which_implies_wit_5_split_goal_2.
  - Goal_apply proof_of_cm_emit_assignment_expr_which_implies_wit_5_split_goal_3.
  - Goal_apply proof_of_cm_emit_assignment_expr_which_implies_wit_5_split_goal_4.
Qed. 

Lemma proof_of_cm_emit_assignment_expr_which_implies_wit_6_split_goal_spatial : cm_emit_assignment_expr_which_implies_wit_6_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (cm_expr_rep_node expr0 e).
  unfold cm_expr_node.
  Exists xa xb xargs.
  unfold cm_expr_shape in PreH10. subst e.
  cbn [cm_expr_payload cm_rep_expr_op].
  split_pure_spatial.
  - cancel.
    cancel (&(expr0 # "cm_expr" ->ₛ "kind") # Int |-> cm_rep_expr_kind (CMAssignE left_ right_ ty_)).
    cancel (&(expr0 # "cm_expr" ->ₛ "op") # Int |-> cm_rep_expr_op (CMAssignE left_ right_ ty_)).
    cancel (&(expr0 # "cm_expr" ->ₛ "ty") # Int |-> cm_type_encode (cm_expr_type (CMAssignE left_ right_ ty_))).
    cancel (&(expr0 # "cm_expr" ->ₛ "value") # Int64 |-> cm_rep_expr_value (CMAssignE left_ right_ ty_)).
    cancel (&(expr0 # "cm_expr" ->ₛ "a") # Ptr |-> xa).
    cancel (&(expr0 # "cm_expr" ->ₛ "b") # Ptr |-> xb).
    cancel (&(expr0 # "cm_expr" ->ₛ "args") # Ptr |-> xargs).
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_cm_emit_assignment_expr_which_implies_wit_6 : cm_emit_assignment_expr_which_implies_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_assignment_expr_which_implies_wit_6_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_binary_expr_safety_wit_23_split_goal_1 : cm_emit_binary_expr_safety_wit_23_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e op_ lvalue_pre.
  unfold cm_expr_code_for in PreH117.
  cbn [Z.eqb] in PreH117.
  rewrite (proj2 (cm_emit_pair_lengths__store_bounds policy p fid_pre (CMBinaryE 0 left_ right_ ty_) pc_pre temp_pre)) in PreH117.
  unfold cm_rvalue_code_count in PreH117.
  cbn [cm_expr_code_counts cm_rcount_of Z.eqb Pos.eqb orb] in PreH117.
  unfold cm_i32_code_count in *.
  unfold cm_rvalue_code_count in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_cm_emit_binary_expr_safety_wit_23_split_goal_2 : cm_emit_binary_expr_safety_wit_23_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_i32_code_count in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_cm_emit_binary_expr_safety_wit_23 : cm_emit_binary_expr_safety_wit_23.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_expr_safety_wit_23_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_expr_safety_wit_23_split_goal_2.
Qed. 

Lemma proof_of_cm_emit_binary_expr_safety_wit_24_split_goal_1 : cm_emit_binary_expr_safety_wit_24_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e op_ lvalue_pre.
  unfold cm_expr_code_for in PreH117.
  cbn [Z.eqb] in PreH117.
  rewrite (proj2 (cm_emit_pair_lengths__store_bounds policy p fid_pre (CMBinaryE 0 left_ right_ ty_) pc_pre temp_pre)) in PreH117.
  unfold cm_rvalue_code_count in PreH117.
  cbn [cm_expr_code_counts cm_rcount_of Z.eqb Pos.eqb orb] in PreH117.
  unfold cm_i32_code_count in *.
  unfold cm_rvalue_code_count in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_cm_emit_binary_expr_safety_wit_24_split_goal_2 : cm_emit_binary_expr_safety_wit_24_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_i32_code_count in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_cm_emit_binary_expr_safety_wit_24 : cm_emit_binary_expr_safety_wit_24.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_expr_safety_wit_24_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_expr_safety_wit_24_split_goal_2.
Qed. 

Lemma proof_of_cm_emit_binary_expr_safety_wit_26_split_goal_1 : cm_emit_binary_expr_safety_wit_26_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  unfold cm_expr_shape in *.
  subst.
  all: pose proof (Zlength_nonneg (cm_rcode_of (cm_emit_expr_pair policy p fid_pre pc_pre temp_pre left_))) as Hl;
    pose proof (Zlength_nonneg (cm_rcode_of (cm_emit_expr_pair policy p fid_pre pc_pre temp_pre right_))) as Hr;
    unfold cm_expr_code_for in *; cbn [Z.eqb] in *;
    repeat match goal with
    | H : context [Zlength (cm_rcode_of (cm_emit_expr_pair ?pol ?pr ?f ?pc0 ?t ?a))] |- _ =>
      rewrite (proj2 (cm_emit_pair_lengths__store_bounds pol pr f a pc0 t)) in H
    | |- context [Zlength (cm_rcode_of (cm_emit_expr_pair ?pol ?pr ?f ?pc0 ?t ?a))] =>
      rewrite (proj2 (cm_emit_pair_lengths__store_bounds pol pr f a pc0 t))
    end;
    unfold cm_rvalue_code_count in *;
    cbn [cm_expr_code_counts cm_rcount_of Z.eqb Pos.eqb orb] in *;
    unfold cm_i32_code_count in *; lia.
Qed.

Lemma proof_of_cm_emit_binary_expr_safety_wit_26_split_goal_2 : cm_emit_binary_expr_safety_wit_26_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  unfold cm_expr_shape in *.
  subst.
  all: pose proof (Zlength_nonneg (cm_rcode_of (cm_emit_expr_pair policy p fid_pre pc_pre temp_pre left_))) as Hl;
    pose proof (Zlength_nonneg (cm_rcode_of (cm_emit_expr_pair policy p fid_pre pc_pre temp_pre right_))) as Hr;
    unfold cm_expr_code_for in *; cbn [Z.eqb] in *;
    repeat match goal with
    | H : context [Zlength (cm_rcode_of (cm_emit_expr_pair ?pol ?pr ?f ?pc0 ?t ?a))] |- _ =>
      rewrite (proj2 (cm_emit_pair_lengths__store_bounds pol pr f a pc0 t)) in H
    | |- context [Zlength (cm_rcode_of (cm_emit_expr_pair ?pol ?pr ?f ?pc0 ?t ?a))] =>
      rewrite (proj2 (cm_emit_pair_lengths__store_bounds pol pr f a pc0 t))
    end;
    unfold cm_rvalue_code_count in *;
    cbn [cm_expr_code_counts cm_rcount_of Z.eqb Pos.eqb orb] in *;
    unfold cm_i32_code_count in *; lia.
Qed.

Lemma proof_of_cm_emit_binary_expr_safety_wit_26 : cm_emit_binary_expr_safety_wit_26.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_expr_safety_wit_26_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_expr_safety_wit_26_split_goal_2.
Qed. 

Lemma proof_of_cm_emit_binary_expr_safety_wit_27_split_goal_1 : cm_emit_binary_expr_safety_wit_27_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  unfold cm_expr_shape in *.
  subst.
  all: pose proof (Zlength_nonneg (cm_rcode_of (cm_emit_expr_pair policy p fid_pre pc_pre temp_pre left_))) as Hl;
    pose proof (Zlength_nonneg (cm_rcode_of (cm_emit_expr_pair policy p fid_pre pc_pre temp_pre right_))) as Hr;
    unfold cm_expr_code_for in *; cbn [Z.eqb] in *;
    repeat match goal with
    | H : context [Zlength (cm_rcode_of (cm_emit_expr_pair ?pol ?pr ?f ?pc0 ?t ?a))] |- _ =>
      rewrite (proj2 (cm_emit_pair_lengths__store_bounds pol pr f a pc0 t)) in H
    | |- context [Zlength (cm_rcode_of (cm_emit_expr_pair ?pol ?pr ?f ?pc0 ?t ?a))] =>
      rewrite (proj2 (cm_emit_pair_lengths__store_bounds pol pr f a pc0 t))
    end;
    unfold cm_rvalue_code_count in *;
    cbn [cm_expr_code_counts cm_rcount_of Z.eqb Pos.eqb orb] in *;
    unfold cm_i32_code_count in *; lia.
Qed.

Lemma proof_of_cm_emit_binary_expr_safety_wit_27_split_goal_2 : cm_emit_binary_expr_safety_wit_27_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  unfold cm_expr_shape in *.
  subst.
  all: pose proof (Zlength_nonneg (cm_rcode_of (cm_emit_expr_pair policy p fid_pre pc_pre temp_pre left_))) as Hl;
    pose proof (Zlength_nonneg (cm_rcode_of (cm_emit_expr_pair policy p fid_pre pc_pre temp_pre right_))) as Hr;
    unfold cm_expr_code_for in *; cbn [Z.eqb] in *;
    repeat match goal with
    | H : context [Zlength (cm_rcode_of (cm_emit_expr_pair ?pol ?pr ?f ?pc0 ?t ?a))] |- _ =>
      rewrite (proj2 (cm_emit_pair_lengths__store_bounds pol pr f a pc0 t)) in H
    | |- context [Zlength (cm_rcode_of (cm_emit_expr_pair ?pol ?pr ?f ?pc0 ?t ?a))] =>
      rewrite (proj2 (cm_emit_pair_lengths__store_bounds pol pr f a pc0 t))
    end;
    unfold cm_rvalue_code_count in *;
    cbn [cm_expr_code_counts cm_rcount_of Z.eqb Pos.eqb orb] in *;
    unfold cm_i32_code_count in *; lia.
Qed.

Lemma proof_of_cm_emit_binary_expr_safety_wit_27 : cm_emit_binary_expr_safety_wit_27.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_expr_safety_wit_27_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_expr_safety_wit_27_split_goal_2.
Qed. 

Lemma proof_of_cm_emit_binary_expr_safety_wit_66_split_goal_1 : cm_emit_binary_expr_safety_wit_66_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold cm_expr_shape in *; subst e.
  assert (lvalue_pre = 0) by lia; subst lvalue_pre.
  pose proof (cm_binary_regular_code_bounds__binary_regular_bounds policy p fid_pre pc_pre temp_pre op_ left_ right_ ty_) as Hbounds.
  specialize (Hbounds ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  dump_pre_spatial.
  unfold cm_i32_code_count in *; lia.
Qed.

Lemma proof_of_cm_emit_binary_expr_safety_wit_66_split_goal_2 : cm_emit_binary_expr_safety_wit_66_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  unfold cm_expr_shape in *; subst e.
  assert (lvalue_pre = 0) by lia; subst lvalue_pre.
  pose proof (cm_binary_regular_code_bounds__binary_regular_bounds policy p fid_pre pc_pre temp_pre op_ left_ right_ ty_) as Hbounds.
  specialize (Hbounds ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  dump_pre_spatial.
  unfold cm_i32_code_count in *; lia.
Qed.

Lemma proof_of_cm_emit_binary_expr_safety_wit_66 : cm_emit_binary_expr_safety_wit_66.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_expr_safety_wit_66_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_expr_safety_wit_66_split_goal_2.
Qed. 

Lemma proof_of_cm_emit_binary_expr_safety_wit_67_split_goal_1 : cm_emit_binary_expr_safety_wit_67_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold cm_expr_shape in *; subst e.
  assert (lvalue_pre = 0) by lia; subst lvalue_pre.
  pose proof (cm_binary_regular_code_bounds__binary_regular_bounds policy p fid_pre pc_pre temp_pre op_ left_ right_ ty_) as Hbounds.
  specialize (Hbounds ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  dump_pre_spatial.
  unfold cm_i32_code_count in *; lia.
Qed.

Lemma proof_of_cm_emit_binary_expr_safety_wit_67_split_goal_2 : cm_emit_binary_expr_safety_wit_67_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  unfold cm_expr_shape in *; subst e.
  assert (lvalue_pre = 0) by lia; subst lvalue_pre.
  pose proof (cm_binary_regular_code_bounds__binary_regular_bounds policy p fid_pre pc_pre temp_pre op_ left_ right_ ty_) as Hbounds.
  specialize (Hbounds ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  dump_pre_spatial.
  unfold cm_i32_code_count in *; lia.
Qed.

Lemma proof_of_cm_emit_binary_expr_safety_wit_67 : cm_emit_binary_expr_safety_wit_67.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_expr_safety_wit_67_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_expr_safety_wit_67_split_goal_2.
Qed. 

Lemma proof_of_cm_emit_binary_expr_safety_wit_69_split_goal_1 : cm_emit_binary_expr_safety_wit_69_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold cm_expr_shape in *; subst e.
  assert (lvalue_pre = 0) by lia; subst lvalue_pre.
  pose proof (cm_binary_regular_temp_bounds__binary_regular_bounds op_ left_ right_ ty_ temp_pre temp_limit_pre) as Hbounds.
  specialize (Hbounds ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  dump_pre_spatial.
  unfold cm_i32_code_count in *; lia.
Qed.

Lemma proof_of_cm_emit_binary_expr_safety_wit_69_split_goal_2 : cm_emit_binary_expr_safety_wit_69_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_cm_emit_binary_expr_safety_wit_69 : cm_emit_binary_expr_safety_wit_69.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_expr_safety_wit_69_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_expr_safety_wit_69_split_goal_2.
Qed. 

Lemma proof_of_cm_emit_binary_expr_return_wit_1_split_goal_spatial : cm_emit_binary_expr_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in *.
  subst e op_ lvalue_pre.
  unfold cm_expr_code_for, cm_short_opcode; try unfold cm_short_value; cbn [cm_emit_expr_pair cm_rcode_of Z.eqb Pos.eqb orb].
  repeat rewrite <- app_assoc.
  cbn [app].
  repeat rewrite Z.add_assoc.
  cancel.
Qed.

Lemma proof_of_cm_emit_binary_expr_return_wit_1 : cm_emit_binary_expr_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_binary_expr_return_wit_1_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_binary_expr_return_wit_2_split_goal_spatial : cm_emit_binary_expr_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hop : op_ = 1) by lia.
  unfold cm_expr_shape in *.
  subst e op_ lvalue_pre.
  unfold cm_expr_code_for, cm_short_opcode; try unfold cm_short_value; cbn [cm_emit_expr_pair cm_rcode_of Z.eqb Pos.eqb orb].
  repeat rewrite <- app_assoc.
  cbn [app].
  repeat rewrite Z.add_assoc.
  cancel.
Qed.

Lemma proof_of_cm_emit_binary_expr_return_wit_2 : cm_emit_binary_expr_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_binary_expr_return_wit_2_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_binary_expr_return_wit_3_split_goal_spatial : cm_emit_binary_expr_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in *. subst e.
  assert (lvalue_pre = 0) by lia. subst lvalue_pre.
  assert (H0 : (Z.eqb op_ 0) = false) by (apply Z.eqb_neq; lia).
  assert (H1 : (Z.eqb op_ 1) = false) by (apply Z.eqb_neq; lia).
  unfold cm_expr_code_for. rewrite Z.eqb_refl.
  cbn [cm_emit_expr_pair cm_rcode_of].
  rewrite H0, H1. cbn [orb cm_rcode_of].
  repeat rewrite <- app_assoc.
  repeat rewrite Z.add_assoc.
  cancel.
Qed.

Lemma proof_of_cm_emit_binary_expr_return_wit_3 : cm_emit_binary_expr_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_binary_expr_return_wit_3_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_binary_expr_return_wit_4_split_goal_spatial : cm_emit_binary_expr_return_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in *. subst e.
  assert (Hlv : (Z.eqb lvalue_pre 0) = false) by (apply Z.eqb_neq; lia).
  unfold cm_expr_code_for. rewrite Hlv.
  cbn [cm_emit_expr_pair cm_lcode_of app]. rewrite app_nil_r.
  cancel.
Qed.

Lemma proof_of_cm_emit_binary_expr_return_wit_4 : cm_emit_binary_expr_return_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_binary_expr_return_wit_4_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_1_pure_split_goal_1 : cm_emit_binary_expr_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: (dump_pre_spatial; unfold cm_expr_shape; reflexivity).
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_1_pure_split_goal_2 : cm_emit_binary_expr_partial_solve_wit_1_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: (dump_pre_spatial; unfold cm_expr_shape; reflexivity).
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_1_pure : cm_emit_binary_expr_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_1_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_1_pure_split_goal_2.
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_5_pure_split_goal_1 : cm_emit_binary_expr_partial_solve_wit_5_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: (dump_pre_spatial; unfold cm_expr_shape in *; subst; assumption).
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_5_pure_split_goal_2 : cm_emit_binary_expr_partial_solve_wit_5_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: (dump_pre_spatial; unfold cm_expr_shape; reflexivity).
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_5_pure : cm_emit_binary_expr_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_5_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_5_pure_split_goal_2.
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_6_pure_split_goal_1 : cm_emit_binary_expr_partial_solve_wit_6_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: (dump_pre_spatial; unfold cm_expr_shape in *; subst; assumption).
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_6_pure_split_goal_2 : cm_emit_binary_expr_partial_solve_wit_6_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: (dump_pre_spatial; unfold cm_expr_shape; reflexivity).
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_6_pure : cm_emit_binary_expr_partial_solve_wit_6_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_6_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_6_pure_split_goal_2.
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_11_pure_split_goal_1 : cm_emit_binary_expr_partial_solve_wit_11_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: vm_compute; congruence.
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_11_pure_split_goal_2 : cm_emit_binary_expr_partial_solve_wit_11_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: vm_compute; congruence.
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_11_pure_split_goal_3 : cm_emit_binary_expr_partial_solve_wit_11_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: vm_compute; congruence.
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_11_pure_split_goal_4 : cm_emit_binary_expr_partial_solve_wit_11_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: vm_compute; congruence.
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_11_pure : cm_emit_binary_expr_partial_solve_wit_11_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_11_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_11_pure_split_goal_2.
  - Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_11_pure_split_goal_3.
  - Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_11_pure_split_goal_4.
Qed. 

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_12_pure_split_goal_1 : cm_emit_binary_expr_partial_solve_wit_12_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: vm_compute; congruence.
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_12_pure_split_goal_2 : cm_emit_binary_expr_partial_solve_wit_12_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: vm_compute; congruence.
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_12_pure_split_goal_3 : cm_emit_binary_expr_partial_solve_wit_12_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: vm_compute; congruence.
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_12_pure_split_goal_4 : cm_emit_binary_expr_partial_solve_wit_12_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: vm_compute; congruence.
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_12_pure : cm_emit_binary_expr_partial_solve_wit_12_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_12_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_12_pure_split_goal_2.
  - Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_12_pure_split_goal_3.
  - Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_12_pure_split_goal_4.
Qed. 

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_17_pure_split_goal_1 : cm_emit_binary_expr_partial_solve_wit_17_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; congruence).
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_17_pure_split_goal_2 : cm_emit_binary_expr_partial_solve_wit_17_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; congruence).
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_17_pure : cm_emit_binary_expr_partial_solve_wit_17_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_17_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_17_pure_split_goal_2.
Qed. 

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_18_pure_split_goal_1 : cm_emit_binary_expr_partial_solve_wit_18_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; congruence).
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_18_pure_split_goal_2 : cm_emit_binary_expr_partial_solve_wit_18_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; congruence).
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_18_pure : cm_emit_binary_expr_partial_solve_wit_18_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_18_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_18_pure_split_goal_2.
Qed. 

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_19_pure_split_goal_1 : cm_emit_binary_expr_partial_solve_wit_19_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; congruence).
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_19_pure_split_goal_2 : cm_emit_binary_expr_partial_solve_wit_19_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; congruence).
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_19_pure : cm_emit_binary_expr_partial_solve_wit_19_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_19_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_19_pure_split_goal_2.
Qed. 

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_20_pure_split_goal_1 : cm_emit_binary_expr_partial_solve_wit_20_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; congruence).
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_20_pure_split_goal_2 : cm_emit_binary_expr_partial_solve_wit_20_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; congruence).
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_20_pure : cm_emit_binary_expr_partial_solve_wit_20_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_20_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_20_pure_split_goal_2.
Qed. 

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_21_pure_split_goal_1 : cm_emit_binary_expr_partial_solve_wit_21_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_21_pure_split_goal_2 : cm_emit_binary_expr_partial_solve_wit_21_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_21_pure : cm_emit_binary_expr_partial_solve_wit_21_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_21_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_21_pure_split_goal_2.
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_22_pure_split_goal_1 : cm_emit_binary_expr_partial_solve_wit_22_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_22_pure_split_goal_2 : cm_emit_binary_expr_partial_solve_wit_22_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_22_pure : cm_emit_binary_expr_partial_solve_wit_22_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_22_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_22_pure_split_goal_2.
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_23_pure_split_goal_1 : cm_emit_binary_expr_partial_solve_wit_23_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: vm_compute; congruence.
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_23_pure_split_goal_2 : cm_emit_binary_expr_partial_solve_wit_23_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: vm_compute; congruence.
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_23_pure_split_goal_3 : cm_emit_binary_expr_partial_solve_wit_23_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: vm_compute; congruence.
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_23_pure_split_goal_4 : cm_emit_binary_expr_partial_solve_wit_23_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: vm_compute; congruence.
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_23_pure : cm_emit_binary_expr_partial_solve_wit_23_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_23_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_23_pure_split_goal_2.
  - Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_23_pure_split_goal_3.
  - Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_23_pure_split_goal_4.
Qed. 

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_24_pure_split_goal_1 : cm_emit_binary_expr_partial_solve_wit_24_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: vm_compute; congruence.
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_24_pure_split_goal_2 : cm_emit_binary_expr_partial_solve_wit_24_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: vm_compute; congruence.
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_24_pure_split_goal_3 : cm_emit_binary_expr_partial_solve_wit_24_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: vm_compute; congruence.
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_24_pure_split_goal_4 : cm_emit_binary_expr_partial_solve_wit_24_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: vm_compute; congruence.
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_24_pure : cm_emit_binary_expr_partial_solve_wit_24_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_24_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_24_pure_split_goal_2.
  - Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_24_pure_split_goal_3.
  - Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_24_pure_split_goal_4.
Qed. 

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_25_pure_split_goal_1 : cm_emit_binary_expr_partial_solve_wit_25_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_25_pure_split_goal_2 : cm_emit_binary_expr_partial_solve_wit_25_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_25_pure : cm_emit_binary_expr_partial_solve_wit_25_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_25_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_25_pure_split_goal_2.
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_26_pure_split_goal_1 : cm_emit_binary_expr_partial_solve_wit_26_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_26_pure_split_goal_2 : cm_emit_binary_expr_partial_solve_wit_26_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_26_pure : cm_emit_binary_expr_partial_solve_wit_26_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_26_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_26_pure_split_goal_2.
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_36_pure_split_goal_1 : cm_emit_binary_expr_partial_solve_wit_36_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: (dump_pre_spatial; unfold cm_expr_shape; reflexivity).
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_36_pure : cm_emit_binary_expr_partial_solve_wit_36_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_36_pure_split_goal_1.
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_37_pure_split_goal_1 : cm_emit_binary_expr_partial_solve_wit_37_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: (dump_pre_spatial; unfold cm_expr_shape; reflexivity).
Qed.

Lemma proof_of_cm_emit_binary_expr_partial_solve_wit_37_pure : cm_emit_binary_expr_partial_solve_wit_37_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_binary_expr_partial_solve_wit_37_pure_split_goal_1.
Qed.

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_1 : cm_emit_binary_expr_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in *; subst e.
  rewrite cm_expr_rep_node; unfold cm_expr_node.
  cbn [cm_expr_payload cm_rep_expr_op].
  Intros xa xb xargs.
  Exists xb xa xargs.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed. 

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_2_split_goal_1 : cm_emit_binary_expr_which_implies_wit_2_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia).
 intros. unfold cm_expr_shape in *. subst e.
 reflexivity.
Qed.

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_2_split_goal_2 : cm_emit_binary_expr_which_implies_wit_2_split_goal_2.
Proof.
 LLM_pre_process ltac:(lia).
 intros. unfold cm_expr_shape in *. subst e.
 exact (cm_expr_type_refs__constructor_facts_c policy p f _ PreH4 PreH6 PreH7 PreH14).
Qed.

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_2_split_goal_3 : cm_emit_binary_expr_which_implies_wit_2_split_goal_3.
Proof.
 LLM_pre_process ltac:(lia).
 intros. unfold cm_expr_shape in *. subst e.
 exact (proj1 (cm_count_node__constructor_facts_c policy p fid _ PreH15)).
Qed.

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_2_split_goal_4 : cm_emit_binary_expr_which_implies_wit_2_split_goal_4.
Proof.
 LLM_pre_process ltac:(lia).
 intros. unfold cm_expr_shape in *. subst e.
 reflexivity.
Qed.

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_2_split_goal_5 : cm_emit_binary_expr_which_implies_wit_2_split_goal_5.
Proof.
 LLM_pre_process ltac:(lia).
 intros. unfold cm_expr_shape in *. subst e.
 exact (proj2 (cm_count_node__constructor_facts_c policy p fid _ (proj2 (proj2 PreH15)))).
Qed.

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_2_split_goal_6 : cm_emit_binary_expr_which_implies_wit_2_split_goal_6.
Proof.
 LLM_pre_process ltac:(lia).
 intros. unfold cm_expr_shape in *. subst e.
 exact (cm_expr_type_refs__constructor_facts_c policy p f _ PreH4 PreH6 PreH7 (proj1 (proj2 PreH14))).
Qed.

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_2_split_goal_7 : cm_emit_binary_expr_which_implies_wit_2_split_goal_7.
Proof.
 LLM_pre_process ltac:(lia).
 intros. unfold cm_expr_shape in *. subst e.
 exact (proj1 (cm_count_node__constructor_facts_c policy p fid _ (proj2 (proj2 PreH15)))).
Qed.

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_2_split_goal_8 : cm_emit_binary_expr_which_implies_wit_2_split_goal_8.
Proof.
 LLM_pre_process ltac:(lia).
 intros. unfold cm_expr_shape in *. subst e.
 exact (proj2 (proj2 PreH15)).
Qed.

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_2_split_goal_9 : cm_emit_binary_expr_which_implies_wit_2_split_goal_9.
Proof.
 LLM_pre_process ltac:(lia).
 intros. unfold cm_expr_shape in *. subst e.
 exact (proj1 (proj2 PreH14)).
Qed.

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_2_split_goal_10 : cm_emit_binary_expr_which_implies_wit_2_split_goal_10.
Proof.
 LLM_pre_process ltac:(lia).
 intros. unfold cm_expr_shape in *. subst e.
 exact (proj2 (cm_count_node__constructor_facts_c policy p fid _ (proj1 (proj2 PreH15)))).
Qed.

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_2_split_goal_11 : cm_emit_binary_expr_which_implies_wit_2_split_goal_11.
Proof.
 LLM_pre_process ltac:(lia).
 intros. unfold cm_expr_shape in *. subst e.
 exact (cm_expr_type_refs__constructor_facts_c policy p f _ PreH4 PreH6 PreH7 (proj1 PreH14)).
Qed.

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_2_split_goal_12 : cm_emit_binary_expr_which_implies_wit_2_split_goal_12.
Proof.
 LLM_pre_process ltac:(lia).
 intros. unfold cm_expr_shape in *. subst e.
 exact (proj1 (cm_count_node__constructor_facts_c policy p fid _ (proj1 (proj2 PreH15)))).
Qed.

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_2_split_goal_13 : cm_emit_binary_expr_which_implies_wit_2_split_goal_13.
Proof.
 LLM_pre_process ltac:(lia).
 intros. unfold cm_expr_shape in *. subst e.
 exact (proj1 (proj2 PreH15)).
Qed.

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_2_split_goal_14 : cm_emit_binary_expr_which_implies_wit_2_split_goal_14.
Proof.
 LLM_pre_process ltac:(lia).
 intros. unfold cm_expr_shape in *. subst e.
 exact (proj1 PreH14).
Qed.

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_2_split_goal_15 : cm_emit_binary_expr_which_implies_wit_2_split_goal_15.
Proof.
 LLM_pre_process ltac:(lia).
 intros. unfold cm_expr_shape in *. subst e.
 exact (cm_expr_type_refs__constructor_facts_c policy p f _ PreH4 PreH6 PreH7 PreH14).
Qed.

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_2_split_goal_16 : cm_emit_binary_expr_which_implies_wit_2_split_goal_16.
Proof.
 LLM_pre_process ltac:(lia).
 intros. unfold cm_expr_shape in *. subst e.
 exact (proj1 (cm_count_node__constructor_facts_c policy p fid _ PreH15)).
Qed.

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_2_split_goal_17 : cm_emit_binary_expr_which_implies_wit_2_split_goal_17.
Proof.
 LLM_pre_process ltac:(lia).
 intros. unfold cm_expr_shape in *. subst e.
 exact (proj1 (cm_temp_bounds__constructor_facts_c policy p fid f temp temp_limit INT_MAX PreH5 PreH6 PreH7 PreH16 PreH17 PreH19)).
Qed.

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_2_split_goal_18 : cm_emit_binary_expr_which_implies_wit_2_split_goal_18.
Proof.
 LLM_pre_process ltac:(lia).
 intros. unfold cm_expr_shape in *. subst e.
 exact (proj2 (cm_temp_bounds__constructor_facts_c policy p fid f temp temp_limit INT_MAX PreH5 PreH6 PreH7 PreH16 PreH17 PreH19)).
Qed.

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_2 : cm_emit_binary_expr_which_implies_wit_2.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_cm_emit_binary_expr_which_implies_wit_2_split_goal_1.
 - Goal_apply proof_of_cm_emit_binary_expr_which_implies_wit_2_split_goal_2.
 - Goal_apply proof_of_cm_emit_binary_expr_which_implies_wit_2_split_goal_3.
 - Goal_apply proof_of_cm_emit_binary_expr_which_implies_wit_2_split_goal_4.
 - Goal_apply proof_of_cm_emit_binary_expr_which_implies_wit_2_split_goal_5.
 - Goal_apply proof_of_cm_emit_binary_expr_which_implies_wit_2_split_goal_6.
 - Goal_apply proof_of_cm_emit_binary_expr_which_implies_wit_2_split_goal_7.
 - Goal_apply proof_of_cm_emit_binary_expr_which_implies_wit_2_split_goal_8.
 - Goal_apply proof_of_cm_emit_binary_expr_which_implies_wit_2_split_goal_9.
 - Goal_apply proof_of_cm_emit_binary_expr_which_implies_wit_2_split_goal_10.
 - Goal_apply proof_of_cm_emit_binary_expr_which_implies_wit_2_split_goal_11.
 - Goal_apply proof_of_cm_emit_binary_expr_which_implies_wit_2_split_goal_12.
 - Goal_apply proof_of_cm_emit_binary_expr_which_implies_wit_2_split_goal_13.
 - Goal_apply proof_of_cm_emit_binary_expr_which_implies_wit_2_split_goal_14.
 - Goal_apply proof_of_cm_emit_binary_expr_which_implies_wit_2_split_goal_15.
 - Goal_apply proof_of_cm_emit_binary_expr_which_implies_wit_2_split_goal_16.
 - Goal_apply proof_of_cm_emit_binary_expr_which_implies_wit_2_split_goal_17.
 - Goal_apply proof_of_cm_emit_binary_expr_which_implies_wit_2_split_goal_18.
Qed. 

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_3_split_goal_spatial : cm_emit_binary_expr_which_implies_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hlv : lvalue = 0) by lia.
  assert (Hop : op_ = 0 \/ op_ = 1) by lia.
  unfold cm_expr_shape in *.
  subst e lvalue left_count right_count.
  destruct Hop as [Hop | Hop]; subst op_;
    unfold cm_expr_code_for, cm_short_opcode; try unfold cm_short_value; cbn [cm_emit_expr_pair cm_rcode_of Z.eqb Pos.eqb orb];
    repeat rewrite <- app_assoc;
    cbn [app];
    repeat rewrite Z.add_assoc;
    cancel.
Qed.

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_3 : cm_emit_binary_expr_which_implies_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_binary_expr_which_implies_wit_3_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_4_split_goal_1 : cm_emit_binary_expr_which_implies_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in PreH22. subst e.
  assert (lvalue = 0) by lia. subst lvalue.
  assert (op_ = 0 \/ op_ = 1) as Hop by lia.
  destruct Hop; subst op_.
  all: unfold cm_expr_code_for in *; cbn [Z.eqb] in *.
  all: rewrite (proj2 (cm_emit_pair_lengths__store_bounds policy p fid _ pc temp)) in PreH21.
  all: pose proof (Zlength_nonneg (cm_rcode_of (cm_emit_expr_pair policy p fid pc temp left_))) as HL;
       pose proof (Zlength_nonneg (cm_rcode_of (cm_emit_expr_pair policy p fid pc temp right_))) as HR.
  all: rewrite (proj2 (cm_emit_pair_lengths__store_bounds policy p fid left_ pc temp)) in HL;
       rewrite (proj2 (cm_emit_pair_lengths__store_bounds policy p fid right_ pc temp)) in HR.
  all: repeat match goal with
       | |- context [Zlength (cm_rcode_of (cm_emit_expr_pair ?pol ?pr ?f ?pos ?t ?a))] =>
         rewrite (proj2 (cm_emit_pair_lengths__store_bounds pol pr f a pos t))
       end.
  all: unfold cm_i32_code_count, cm_rvalue_code_count in *;
       cbn [cm_expr_code_counts cm_rcount_of Z.eqb Pos.eqb orb] in PreH21;
       lia.
Qed.

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_4_split_goal_2 : cm_emit_binary_expr_which_implies_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in PreH22. subst e.
  assert (lvalue = 0) by lia. subst lvalue.
  assert (op_ = 0 \/ op_ = 1) as Hop by lia.
  destruct Hop; subst op_.
  all: cbn [cm_expr_temps_for cm_rtemps cm_expr_tpair cm_tright Z.eqb Pos.eqb orb] in PreH18 |- *;
       unfold cm_imax in PreH18;
       unfold cm_rtemps;
       pose proof (Z.le_max_l (cm_tright (cm_expr_tpair left_)) (cm_tright (cm_expr_tpair right_)));
       lia.
Qed.

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_4 : cm_emit_binary_expr_which_implies_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_expr_which_implies_wit_4_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_expr_which_implies_wit_4_split_goal_2.
Qed. 

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_5_split_goal_1 : cm_emit_binary_expr_which_implies_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in PreH22. subst e.
  assert (lvalue = 0) by lia. subst lvalue.
  assert (op_ = 0 \/ op_ = 1) as Hop by lia.
  destruct Hop; subst op_.
  all: unfold cm_expr_code_for in *; cbn [Z.eqb] in *.
  all: rewrite (proj2 (cm_emit_pair_lengths__store_bounds policy p fid _ pc temp)) in PreH21.
  all: pose proof (Zlength_nonneg (cm_rcode_of (cm_emit_expr_pair policy p fid pc temp left_))) as HL;
       pose proof (Zlength_nonneg (cm_rcode_of (cm_emit_expr_pair policy p fid pc temp right_))) as HR.
  all: rewrite (proj2 (cm_emit_pair_lengths__store_bounds policy p fid left_ pc temp)) in HL;
       rewrite (proj2 (cm_emit_pair_lengths__store_bounds policy p fid right_ pc temp)) in HR.
  all: repeat match goal with
       | |- context [Zlength (cm_rcode_of (cm_emit_expr_pair ?pol ?pr ?f ?pos ?t ?a))] =>
         rewrite (proj2 (cm_emit_pair_lengths__store_bounds pol pr f a pos t))
       end.
  all: unfold cm_i32_code_count, cm_rvalue_code_count in *;
       cbn [cm_expr_code_counts cm_rcount_of Z.eqb Pos.eqb orb] in PreH21;
       lia.
Qed.

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_5_split_goal_2 : cm_emit_binary_expr_which_implies_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in PreH22. subst e.
  assert (lvalue = 0) by lia. subst lvalue.
  assert (op_ = 0 \/ op_ = 1) as Hop by lia.
  destruct Hop; subst op_.
  all: unfold cm_expr_code_for in *; cbn [Z.eqb] in *.
  all: rewrite (proj2 (cm_emit_pair_lengths__store_bounds policy p fid _ pc temp)) in PreH21.
  all: pose proof (Zlength_nonneg (cm_rcode_of (cm_emit_expr_pair policy p fid pc temp left_))) as HL;
       pose proof (Zlength_nonneg (cm_rcode_of (cm_emit_expr_pair policy p fid pc temp right_))) as HR.
  all: rewrite (proj2 (cm_emit_pair_lengths__store_bounds policy p fid left_ pc temp)) in HL;
       rewrite (proj2 (cm_emit_pair_lengths__store_bounds policy p fid right_ pc temp)) in HR.
  all: repeat match goal with
       | |- context [Zlength (cm_rcode_of (cm_emit_expr_pair ?pol ?pr ?f ?pos ?t ?a))] =>
         rewrite (proj2 (cm_emit_pair_lengths__store_bounds pol pr f a pos t))
       end.
  all: unfold cm_i32_code_count, cm_rvalue_code_count in *;
       cbn [cm_expr_code_counts cm_rcount_of Z.eqb Pos.eqb orb] in PreH21;
       lia.
Qed.

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_5_split_goal_3 : cm_emit_binary_expr_which_implies_wit_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in PreH22. subst e.
  assert (lvalue = 0) by lia. subst lvalue.
  assert (op_ = 0 \/ op_ = 1) as Hop by lia.
  destruct Hop; subst op_.
  all: cbn [cm_expr_temps_for cm_rtemps cm_expr_tpair cm_tright Z.eqb Pos.eqb orb] in PreH18 |- *;
       unfold cm_imax in PreH18;
       unfold cm_rtemps;
       pose proof (Z.le_max_r (cm_tright (cm_expr_tpair left_)) (cm_tright (cm_expr_tpair right_)));
       lia.
Qed.

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_5 : cm_emit_binary_expr_which_implies_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_expr_which_implies_wit_5_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_expr_which_implies_wit_5_split_goal_2.
  - Goal_apply proof_of_cm_emit_binary_expr_which_implies_wit_5_split_goal_3.
Qed. 

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_6_split_goal_1 : cm_emit_binary_expr_which_implies_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  unfold cm_expr_shape in *.
  subst.
  assert (lvalue = 0) by lia. subst lvalue.
  assert (op_ = 0 \/ op_ = 1) as Hop by lia.
  destruct Hop; subst op_.
  all: pose proof (Zlength_nonneg (cm_rcode_of (cm_emit_expr_pair policy p fid pc temp left_))) as Hl;
    pose proof (Zlength_nonneg (cm_rcode_of (cm_emit_expr_pair policy p fid pc temp right_))) as Hr;
    unfold cm_expr_code_for in *; cbn [Z.eqb] in *;
    repeat match goal with
    | H : context [Zlength (cm_rcode_of (cm_emit_expr_pair ?pol ?pr ?f ?pc0 ?t ?a))] |- _ =>
      rewrite (proj2 (cm_emit_pair_lengths__store_bounds pol pr f a pc0 t)) in H
    | |- context [Zlength (cm_rcode_of (cm_emit_expr_pair ?pol ?pr ?f ?pc0 ?t ?a))] =>
      rewrite (proj2 (cm_emit_pair_lengths__store_bounds pol pr f a pc0 t))
    end;
    unfold cm_rvalue_code_count in *;
    cbn [cm_expr_code_counts cm_rcount_of Z.eqb Pos.eqb orb] in *;
    unfold cm_i32_code_count in *; lia.
Qed.

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_6_split_goal_2 : cm_emit_binary_expr_which_implies_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  unfold cm_expr_shape in *.
  subst.
  assert (lvalue = 0) by lia. subst lvalue.
  assert (op_ = 0 \/ op_ = 1) as Hop by lia.
  destruct Hop; subst op_.
  all: pose proof (Zlength_nonneg (cm_rcode_of (cm_emit_expr_pair policy p fid pc temp left_))) as Hl;
    pose proof (Zlength_nonneg (cm_rcode_of (cm_emit_expr_pair policy p fid pc temp right_))) as Hr;
    unfold cm_expr_code_for in *; cbn [Z.eqb] in *;
    repeat match goal with
    | H : context [Zlength (cm_rcode_of (cm_emit_expr_pair ?pol ?pr ?f ?pc0 ?t ?a))] |- _ =>
      rewrite (proj2 (cm_emit_pair_lengths__store_bounds pol pr f a pc0 t)) in H
    | |- context [Zlength (cm_rcode_of (cm_emit_expr_pair ?pol ?pr ?f ?pc0 ?t ?a))] =>
      rewrite (proj2 (cm_emit_pair_lengths__store_bounds pol pr f a pc0 t))
    end;
    unfold cm_rvalue_code_count in *;
    cbn [cm_expr_code_counts cm_rcount_of Z.eqb Pos.eqb orb] in *;
    unfold cm_i32_code_count in *; lia.
Qed.

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_6_split_goal_3 : cm_emit_binary_expr_which_implies_wit_6_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  try dump_pre_spatial.
  unfold cm_expr_shape in *.
  subst.
  assert (lvalue = 0) by lia. subst lvalue.
  assert (op_ = 0 \/ op_ = 1) as Hop by lia.
  destruct Hop; subst op_.
  all: unfold cm_expr_temps_for, cm_rtemps in *;
    cbn [Z.eqb Pos.eqb orb cm_expr_tpair cm_tright] in *;
    unfold cm_imax in *;
    pose proof (Z.le_max_r (cm_tright (cm_expr_tpair left_)) (cm_tright (cm_expr_tpair right_))); lia.
Qed.

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_6 : cm_emit_binary_expr_which_implies_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_expr_which_implies_wit_6_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_expr_which_implies_wit_6_split_goal_2.
  - Goal_apply proof_of_cm_emit_binary_expr_which_implies_wit_6_split_goal_3.
Qed. 

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_7_split_goal_spatial : cm_emit_binary_expr_which_implies_wit_7_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_7 : cm_emit_binary_expr_which_implies_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_binary_expr_which_implies_wit_7_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_8_split_goal_spatial : cm_emit_binary_expr_which_implies_wit_8_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in *. subst e left_count right_count.
  assert (lvalue = 0) by lia. subst lvalue.
  assert (H0 : (Z.eqb op_ 0) = false) by (apply Z.eqb_neq; lia).
  assert (H1 : (Z.eqb op_ 1) = false) by (apply Z.eqb_neq; lia).
  unfold cm_expr_code_for. rewrite Z.eqb_refl.
  cbn [cm_emit_expr_pair cm_rcode_of].
  rewrite H0, H1. cbn [orb cm_rcode_of].
  repeat rewrite <- app_assoc.
  repeat rewrite Z.add_assoc.
  cancel.
Qed.

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_8 : cm_emit_binary_expr_which_implies_wit_8.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_binary_expr_which_implies_wit_8_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_9_split_goal_1 : cm_emit_binary_expr_which_implies_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold cm_expr_shape in *; subst e.
  assert (lvalue = 0) by lia; subst lvalue.
  pose proof (cm_binary_regular_code_bounds__binary_regular_bounds policy p fid pc temp op_ left_ right_ ty_) as Hbounds.
  specialize (Hbounds ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  unfold cm_expr_code_for; cbn [Z.eqb].
  repeat match goal with
  | |- context [Zlength (cm_rcode_of (cm_emit_expr_pair ?pol ?pr ?f ?q ?t ?a))] =>
    rewrite (proj2 (cm_emit_pair_lengths__store_bounds pol pr f a q t))
  end.
  unfold cm_i32_code_count in *; lia.
Qed.

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_9_split_goal_2 : cm_emit_binary_expr_which_implies_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  unfold cm_expr_shape in *; subst e.
  assert (lvalue = 0) by lia; subst lvalue.
  pose proof (cm_binary_regular_temp_bounds__binary_regular_bounds op_ left_ right_ ty_ temp temp_limit) as Hbounds.
  specialize (Hbounds ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  unfold cm_i32_code_count in *; lia.
Qed.

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_9 : cm_emit_binary_expr_which_implies_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_expr_which_implies_wit_9_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_expr_which_implies_wit_9_split_goal_2.
Qed. 

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_10_split_goal_1 : cm_emit_binary_expr_which_implies_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold cm_expr_shape in *; subst e.
  assert (lvalue = 0) by lia; subst lvalue.
  pose proof (cm_binary_regular_code_bounds__binary_regular_bounds policy p fid pc temp op_ left_ right_ ty_) as Hbounds.
  specialize (Hbounds ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  unfold cm_expr_code_for; cbn [Z.eqb].
  repeat match goal with
  | |- context [Zlength (cm_rcode_of (cm_emit_expr_pair ?pol ?pr ?f ?q ?t ?a))] =>
    rewrite (proj2 (cm_emit_pair_lengths__store_bounds pol pr f a q t))
  end.
  unfold cm_i32_code_count in *; lia.
Qed.

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_10_split_goal_2 : cm_emit_binary_expr_which_implies_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  unfold cm_expr_shape in *; subst e.
  assert (lvalue = 0) by lia; subst lvalue.
  pose proof (cm_binary_regular_code_bounds__binary_regular_bounds policy p fid pc temp op_ left_ right_ ty_) as Hbounds.
  specialize (Hbounds ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  unfold cm_expr_code_for; cbn [Z.eqb].
  repeat match goal with
  | |- context [Zlength (cm_rcode_of (cm_emit_expr_pair ?pol ?pr ?f ?q ?t ?a))] =>
    rewrite (proj2 (cm_emit_pair_lengths__store_bounds pol pr f a q t))
  end.
  unfold cm_i32_code_count in *; lia.
Qed.

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_10_split_goal_3 : cm_emit_binary_expr_which_implies_wit_10_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  unfold cm_expr_shape in *; subst e.
  assert (lvalue = 0) by lia; subst lvalue.
  pose proof (cm_binary_regular_temp_bounds__binary_regular_bounds op_ left_ right_ ty_ temp temp_limit) as Hbounds.
  specialize (Hbounds ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  unfold cm_i32_code_count in *; lia.
Qed.

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_10_split_goal_4 : cm_emit_binary_expr_which_implies_wit_10_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
  unfold cm_expr_shape in *; subst e.
  assert (lvalue = 0) by lia; subst lvalue.
  pose proof (cm_binary_regular_temp_bounds__binary_regular_bounds op_ left_ right_ ty_ temp temp_limit) as Hbounds.
  specialize (Hbounds ltac:(assumption) ltac:(assumption) ltac:(assumption)).
  unfold cm_i32_code_count in *; lia.
Qed.

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_10 : cm_emit_binary_expr_which_implies_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_expr_which_implies_wit_10_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_expr_which_implies_wit_10_split_goal_2.
  - Goal_apply proof_of_cm_emit_binary_expr_which_implies_wit_10_split_goal_3.
  - Goal_apply proof_of_cm_emit_binary_expr_which_implies_wit_10_split_goal_4.
Qed. 

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_11_split_goal_spatial : cm_emit_binary_expr_which_implies_wit_11_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (cm_expr_rep_node expr0 e).
  unfold cm_expr_node.
  Exists xa xb xargs.
  unfold cm_expr_shape in PreH10. subst e.
  cbn [cm_expr_payload cm_rep_expr_op].
  split_pure_spatial.
  - cancel.
    cancel (&(expr0 # "cm_expr" ->ₛ "kind") # Int |-> cm_rep_expr_kind (CMBinaryE op_ left_ right_ ty_)).
    cancel (&(expr0 # "cm_expr" ->ₛ "op") # Int |-> op_).
    cancel (&(expr0 # "cm_expr" ->ₛ "ty") # Int |-> cm_type_encode (cm_expr_type (CMBinaryE op_ left_ right_ ty_))).
    cancel (&(expr0 # "cm_expr" ->ₛ "value") # Int64 |-> cm_rep_expr_value (CMBinaryE op_ left_ right_ ty_)).
    cancel (&(expr0 # "cm_expr" ->ₛ "a") # Ptr |-> xa).
    cancel (&(expr0 # "cm_expr" ->ₛ "b") # Ptr |-> xb).
    cancel (&(expr0 # "cm_expr" ->ₛ "args") # Ptr |-> xargs).
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_cm_emit_binary_expr_which_implies_wit_11 : cm_emit_binary_expr_which_implies_wit_11.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_binary_expr_which_implies_wit_11_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_member_expr_return_wit_1_split_goal_spatial : cm_emit_member_expr_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in *; subst.
  unfold cm_expr_code_for, cm_member_load_suffix.
  cbn [cm_emit_expr_pair cm_rcode_of cm_lcode_of cm_rep_expr_value] in *.
  repeat match goal with
  | |- context [Z.eqb ?a 0] =>
      let H := fresh "Hguard" in destruct (Z.eqb a 0) eqn:H;
      [apply Z.eqb_eq in H | apply Z.eqb_neq in H]; try lia
  end.
  all: repeat rewrite <- app_assoc; cbn [app]; rewrite ?app_nil_r; cancel.
Qed.

Lemma proof_of_cm_emit_member_expr_return_wit_1 : cm_emit_member_expr_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_member_expr_return_wit_1_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_member_expr_return_wit_2_split_goal_spatial : cm_emit_member_expr_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in *; subst.
  unfold cm_expr_code_for, cm_member_load_suffix.
  cbn [cm_emit_expr_pair cm_rcode_of cm_lcode_of cm_rep_expr_value] in *.
  repeat match goal with
  | |- context [Z.eqb ?a 0] =>
      let H := fresh "Hguard" in destruct (Z.eqb a 0) eqn:H;
      [apply Z.eqb_eq in H | apply Z.eqb_neq in H]; try lia
  end.
  all: repeat rewrite <- app_assoc; cbn [app]; rewrite ?app_nil_r; cancel.
Qed.

Lemma proof_of_cm_emit_member_expr_return_wit_2 : cm_emit_member_expr_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_member_expr_return_wit_2_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_member_expr_return_wit_3_split_goal_spatial : cm_emit_member_expr_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in *; subst.
  unfold cm_expr_code_for, cm_member_load_suffix.
  cbn [cm_emit_expr_pair cm_rcode_of cm_lcode_of cm_rep_expr_value] in *.
  repeat match goal with
  | |- context [Z.eqb ?a 0] =>
      let H := fresh "Hguard" in destruct (Z.eqb a 0) eqn:H;
      [apply Z.eqb_eq in H | apply Z.eqb_neq in H]; try lia
  end.
  all: repeat rewrite <- app_assoc; cbn [app]; rewrite ?app_nil_r; cancel.
Qed.

Lemma proof_of_cm_emit_member_expr_return_wit_3 : cm_emit_member_expr_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_member_expr_return_wit_3_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_member_expr_partial_solve_wit_1_pure_split_goal_1 : cm_emit_member_expr_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold cm_expr_shape; reflexivity).
  all: dump_pre_spatial; unfold cm_expr_shape; reflexivity.
Qed.

Lemma proof_of_cm_emit_member_expr_partial_solve_wit_1_pure_split_goal_2 : cm_emit_member_expr_partial_solve_wit_1_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(unfold cm_expr_shape; reflexivity).
  all: dump_pre_spatial; unfold cm_expr_shape; reflexivity.
Qed.

Lemma proof_of_cm_emit_member_expr_partial_solve_wit_1_pure : cm_emit_member_expr_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_member_expr_partial_solve_wit_1_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_member_expr_partial_solve_wit_1_pure_split_goal_2.
Qed. 

Lemma proof_of_cm_emit_member_expr_partial_solve_wit_9_pure_split_goal_1 : cm_emit_member_expr_partial_solve_wit_9_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
  all: dump_pre_spatial; cbn [tvm_opcode_code]; lia.
Qed.

Lemma proof_of_cm_emit_member_expr_partial_solve_wit_9_pure_split_goal_2 : cm_emit_member_expr_partial_solve_wit_9_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
  all: dump_pre_spatial; cbn [tvm_opcode_code]; lia.
Qed.

Lemma proof_of_cm_emit_member_expr_partial_solve_wit_9_pure : cm_emit_member_expr_partial_solve_wit_9_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_member_expr_partial_solve_wit_9_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_member_expr_partial_solve_wit_9_pure_split_goal_2.
Qed. 

Lemma proof_of_cm_emit_member_expr_partial_solve_wit_10_pure_split_goal_1 : cm_emit_member_expr_partial_solve_wit_10_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
  all: dump_pre_spatial; cbn [tvm_opcode_code]; lia.
Qed.

Lemma proof_of_cm_emit_member_expr_partial_solve_wit_10_pure_split_goal_2 : cm_emit_member_expr_partial_solve_wit_10_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
  all: dump_pre_spatial; cbn [tvm_opcode_code]; lia.
Qed.

Lemma proof_of_cm_emit_member_expr_partial_solve_wit_10_pure : cm_emit_member_expr_partial_solve_wit_10_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_member_expr_partial_solve_wit_10_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_member_expr_partial_solve_wit_10_pure_split_goal_2.
Qed. 

Lemma proof_of_cm_emit_member_expr_partial_solve_wit_11_pure_split_goal_1 : cm_emit_member_expr_partial_solve_wit_11_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(congruence).
  all: dump_pre_spatial; congruence.
Qed.

Lemma proof_of_cm_emit_member_expr_partial_solve_wit_11_pure : cm_emit_member_expr_partial_solve_wit_11_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_member_expr_partial_solve_wit_11_pure_split_goal_1.
Qed. 

Lemma proof_of_cm_emit_member_expr_which_implies_wit_1 : cm_emit_member_expr_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in *; subst e.
  rewrite cm_expr_rep_node; unfold cm_expr_node.
  cbn [cm_expr_payload cm_rep_expr_op].
  Intros xa xb xargs.
  Exists xargs xb xa.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed. 

Lemma proof_of_cm_emit_member_expr_which_implies_wit_2_split_goal_1 : cm_emit_member_expr_which_implies_wit_2_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia).
 intros. unfold cm_expr_shape in *. subst e.
 exact (cm_expr_type_refs__constructor_facts_c policy p f _ PreH4 PreH6 PreH7 PreH14).
Qed.

Lemma proof_of_cm_emit_member_expr_which_implies_wit_2_split_goal_2 : cm_emit_member_expr_which_implies_wit_2_split_goal_2.
Proof.
 LLM_pre_process ltac:(lia).
 intros. unfold cm_expr_shape in *. subst e.
 exact (proj1 (cm_count_node__constructor_facts_c policy p fid _ PreH15)).
Qed.

Lemma proof_of_cm_emit_member_expr_which_implies_wit_2_split_goal_3 : cm_emit_member_expr_which_implies_wit_2_split_goal_3.
Proof.
 LLM_pre_process ltac:(lia).
 intros. unfold cm_expr_shape in *. subst e.
 reflexivity.
Qed.

Lemma proof_of_cm_emit_member_expr_which_implies_wit_2_split_goal_4 : cm_emit_member_expr_which_implies_wit_2_split_goal_4.
Proof.
 LLM_pre_process ltac:(lia).
 intros. unfold cm_expr_shape in *. subst e.
 reflexivity.
Qed.

Lemma proof_of_cm_emit_member_expr_which_implies_wit_2_split_goal_5 : cm_emit_member_expr_which_implies_wit_2_split_goal_5.
Proof.
 LLM_pre_process ltac:(lia).
 intros. unfold cm_expr_shape in *. subst e.
 exact (proj1 (proj2 PreH14)).
Qed.

Lemma proof_of_cm_emit_member_expr_which_implies_wit_2_split_goal_6 : cm_emit_member_expr_which_implies_wit_2_split_goal_6.
Proof.
 LLM_pre_process ltac:(lia).
 intros. unfold cm_expr_shape in *. subst e.
 pose proof (proj1 (proj2 PreH15)) as Hmid. unfold cm_i32_code_count in Hmid. change (mid_ <= 2147483647). lia.
Qed.

Lemma proof_of_cm_emit_member_expr_which_implies_wit_2_split_goal_7 : cm_emit_member_expr_which_implies_wit_2_split_goal_7.
Proof.
 LLM_pre_process ltac:(lia).
 intros. unfold cm_expr_shape in *. subst e.
 pose proof (proj1 (proj2 PreH15)) as Hmid. unfold cm_i32_code_count in Hmid. lia.
Qed.

Lemma proof_of_cm_emit_member_expr_which_implies_wit_2_split_goal_8 : cm_emit_member_expr_which_implies_wit_2_split_goal_8.
Proof.
 LLM_pre_process ltac:(lia).
 intros. unfold cm_expr_shape in *. subst e.
 exact (proj2 (cm_count_node__constructor_facts_c policy p fid _ (proj2 (proj2 PreH15)))).
Qed.

Lemma proof_of_cm_emit_member_expr_which_implies_wit_2_split_goal_9 : cm_emit_member_expr_which_implies_wit_2_split_goal_9.
Proof.
 LLM_pre_process ltac:(lia).
 intros. unfold cm_expr_shape in *. subst e.
 exact (cm_expr_type_refs__constructor_facts_c policy p f _ PreH4 PreH6 PreH7 (proj1 PreH14)).
Qed.

Lemma proof_of_cm_emit_member_expr_which_implies_wit_2_split_goal_10 : cm_emit_member_expr_which_implies_wit_2_split_goal_10.
Proof.
 LLM_pre_process ltac:(lia).
 intros. unfold cm_expr_shape in *. subst e.
 exact (proj1 (cm_count_node__constructor_facts_c policy p fid _ (proj2 (proj2 PreH15)))).
Qed.

Lemma proof_of_cm_emit_member_expr_which_implies_wit_2_split_goal_11 : cm_emit_member_expr_which_implies_wit_2_split_goal_11.
Proof.
 LLM_pre_process ltac:(lia).
 intros. unfold cm_expr_shape in *. subst e.
 exact (proj2 (proj2 PreH15)).
Qed.

Lemma proof_of_cm_emit_member_expr_which_implies_wit_2_split_goal_12 : cm_emit_member_expr_which_implies_wit_2_split_goal_12.
Proof.
 LLM_pre_process ltac:(lia).
 intros. unfold cm_expr_shape in *. subst e.
 exact (proj1 PreH14).
Qed.

Lemma proof_of_cm_emit_member_expr_which_implies_wit_2_split_goal_13 : cm_emit_member_expr_which_implies_wit_2_split_goal_13.
Proof.
 LLM_pre_process ltac:(lia).
 intros. unfold cm_expr_shape in *. subst e.
 exact (cm_expr_type_refs__constructor_facts_c policy p f _ PreH4 PreH6 PreH7 PreH14).
Qed.

Lemma proof_of_cm_emit_member_expr_which_implies_wit_2_split_goal_14 : cm_emit_member_expr_which_implies_wit_2_split_goal_14.
Proof.
 LLM_pre_process ltac:(lia).
 intros. unfold cm_expr_shape in *. subst e.
 exact (proj1 (cm_count_node__constructor_facts_c policy p fid _ PreH15)).
Qed.

Lemma proof_of_cm_emit_member_expr_which_implies_wit_2_split_goal_15 : cm_emit_member_expr_which_implies_wit_2_split_goal_15.
Proof.
 LLM_pre_process ltac:(lia).
 intros. unfold cm_expr_shape in *. subst e.
 exact (proj1 (cm_temp_bounds__constructor_facts_c policy p fid f temp temp_limit INT_MAX PreH5 PreH6 PreH7 PreH16 PreH17 PreH19)).
Qed.

Lemma proof_of_cm_emit_member_expr_which_implies_wit_2_split_goal_16 : cm_emit_member_expr_which_implies_wit_2_split_goal_16.
Proof.
 LLM_pre_process ltac:(lia).
 intros. unfold cm_expr_shape in *. subst e.
 exact (proj2 (cm_temp_bounds__constructor_facts_c policy p fid f temp temp_limit INT_MAX PreH5 PreH6 PreH7 PreH16 PreH17 PreH19)).
Qed.

Lemma proof_of_cm_emit_member_expr_which_implies_wit_2 : cm_emit_member_expr_which_implies_wit_2.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_cm_emit_member_expr_which_implies_wit_2_split_goal_1.
 - Goal_apply proof_of_cm_emit_member_expr_which_implies_wit_2_split_goal_2.
 - Goal_apply proof_of_cm_emit_member_expr_which_implies_wit_2_split_goal_3.
 - Goal_apply proof_of_cm_emit_member_expr_which_implies_wit_2_split_goal_4.
 - Goal_apply proof_of_cm_emit_member_expr_which_implies_wit_2_split_goal_5.
 - Goal_apply proof_of_cm_emit_member_expr_which_implies_wit_2_split_goal_6.
 - Goal_apply proof_of_cm_emit_member_expr_which_implies_wit_2_split_goal_7.
 - Goal_apply proof_of_cm_emit_member_expr_which_implies_wit_2_split_goal_8.
 - Goal_apply proof_of_cm_emit_member_expr_which_implies_wit_2_split_goal_9.
 - Goal_apply proof_of_cm_emit_member_expr_which_implies_wit_2_split_goal_10.
 - Goal_apply proof_of_cm_emit_member_expr_which_implies_wit_2_split_goal_11.
 - Goal_apply proof_of_cm_emit_member_expr_which_implies_wit_2_split_goal_12.
 - Goal_apply proof_of_cm_emit_member_expr_which_implies_wit_2_split_goal_13.
 - Goal_apply proof_of_cm_emit_member_expr_which_implies_wit_2_split_goal_14.
 - Goal_apply proof_of_cm_emit_member_expr_which_implies_wit_2_split_goal_15.
 - Goal_apply proof_of_cm_emit_member_expr_which_implies_wit_2_split_goal_16.
Qed. 

Lemma proof_of_cm_emit_member_expr_which_implies_wit_3_split_goal_spatial : cm_emit_member_expr_which_implies_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_expr_shape in *; subst.
  unfold cm_expr_code_for, cm_member_load_suffix.
  cbn [cm_emit_expr_pair cm_rcode_of cm_lcode_of Z.eqb].
  destruct (Z.eqb lvalue 0); repeat rewrite <- app_assoc; cbn [app]; rewrite ?app_nil_r; cancel.
Qed.

Lemma proof_of_cm_emit_member_expr_which_implies_wit_3 : cm_emit_member_expr_which_implies_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_member_expr_which_implies_wit_3_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_member_expr_which_implies_wit_4_split_goal_1 : cm_emit_member_expr_which_implies_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold cm_expr_shape in *; subst e.
  unfold cm_expr_code_for in *.
  cbn [cm_emit_expr_pair cm_lcode_of cm_rcode_of] in PreH21.
  destruct (Z.eqb lvalue 0) eqn:Hl;
    cbn [Z.eqb] in *;
    repeat rewrite Zlength_app in PreH21;
    unfold cm_i32_code_count in *.
  all: pose proof (Zlength_nonneg (cm_rcode_of (cm_emit_expr_pair policy p fid pc temp arg_))).
  all: repeat match type of PreH21 with
    | context [Zlength ?l] => let H := fresh "Hlen" in pose proof (Zlength_nonneg l) as H; let n := fresh "n" in set (n := Zlength l) in *
    end.
  all: lia.
Qed.

Lemma proof_of_cm_emit_member_expr_which_implies_wit_4_split_goal_2 : cm_emit_member_expr_which_implies_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  unfold cm_expr_shape in *; subst e.
  unfold cm_expr_temps_for, cm_rtemps, cm_ltemps in *.
  cbn [cm_expr_tpair cm_tleft cm_tright] in PreH18.
  destruct (Z.eqb lvalue 0); cbn; exact PreH18.
Qed.

Lemma proof_of_cm_emit_member_expr_which_implies_wit_4 : cm_emit_member_expr_which_implies_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_member_expr_which_implies_wit_4_split_goal_1.
  - Goal_apply proof_of_cm_emit_member_expr_which_implies_wit_4_split_goal_2.
Qed. 

Lemma proof_of_cm_emit_member_expr_which_implies_wit_5_split_goal_spatial : cm_emit_member_expr_which_implies_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (lvalue = 0) by lia; subst lvalue.
  unfold cm_member_load_suffix.
  assert (Ha : cm_member_array_code p (cm_expr_type arg_) mid_ = 0) by lia.
  rewrite Ha; cbn [Z.eqb]; cancel.
Qed.

Lemma proof_of_cm_emit_member_expr_which_implies_wit_5 : cm_emit_member_expr_which_implies_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_member_expr_which_implies_wit_5_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_member_expr_which_implies_wit_6_split_goal_spatial : cm_emit_member_expr_which_implies_wit_6_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (cm_expr_rep_node expr0 e).
  unfold cm_expr_node.
  Exists xa xb xargs.
  unfold cm_expr_shape in PreH10. subst e.
  cbn [cm_expr_payload cm_rep_expr_op].
  split_pure_spatial.
  - cancel.
    cancel (&(expr0 # "cm_expr" ->ₛ "kind") # Int |-> cm_rep_expr_kind (CMMemberE arg_ mid_ ty_)).
    cancel (&(expr0 # "cm_expr" ->ₛ "op") # Int |-> cm_rep_expr_op (CMMemberE arg_ mid_ ty_)).
    cancel (&(expr0 # "cm_expr" ->ₛ "ty") # Int |-> cm_type_encode (cm_expr_type (CMMemberE arg_ mid_ ty_))).
    cancel (&(expr0 # "cm_expr" ->ₛ "value") # Int64 |-> cm_rep_expr_value (CMMemberE arg_ mid_ ty_)).
    cancel (&(expr0 # "cm_expr" ->ₛ "a") # Ptr |-> xa).
    cancel (&(expr0 # "cm_expr" ->ₛ "b") # Ptr |-> xb).
    cancel (&(expr0 # "cm_expr" ->ₛ "args") # Ptr |-> xargs).
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_cm_emit_member_expr_which_implies_wit_6 : cm_emit_member_expr_which_implies_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_member_expr_which_implies_wit_6_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_expr_return_wit_1_split_goal_spatial : cm_emit_expr_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e.
  assert (Hcode : cm_simple_code_for policy p fid_pre simple lvalue_pre =
    cm_expr_code_for policy p fid_pre pc_pre temp_pre (cm_simple_source_expr simple) lvalue_pre).
  { destruct simple as [leaf | scope slot ty];
      [destruct leaf | ];
      unfold cm_simple_code_for, cm_simple_source_expr, cm_leaf_code_for,
        cm_leaf_source_expr, cm_leaf_rvalue, cm_expr_code_for, cm_var_code_for;
      destruct (Z.eqb lvalue_pre 0); reflexivity. }
  rewrite Hcode.
  cancel.
Qed.

Lemma proof_of_cm_emit_expr_return_wit_1 : cm_emit_expr_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_expr_return_wit_1_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_expr_return_wit_2_split_goal_spatial : cm_emit_expr_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e.
  assert (Hcode : cm_simple_code_for policy p fid_pre simple lvalue_pre =
    cm_expr_code_for policy p fid_pre pc_pre temp_pre (cm_simple_source_expr simple) lvalue_pre).
  { destruct simple as [leaf | scope slot ty];
      [destruct leaf | ];
      unfold cm_simple_code_for, cm_simple_source_expr, cm_leaf_code_for,
        cm_leaf_source_expr, cm_leaf_rvalue, cm_expr_code_for, cm_var_code_for;
      destruct (Z.eqb lvalue_pre 0); reflexivity. }
  rewrite Hcode.
  cancel.
Qed.

Lemma proof_of_cm_emit_expr_return_wit_2 : cm_emit_expr_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_expr_return_wit_2_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_expr_return_wit_3_split_goal_spatial : cm_emit_expr_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e.
  assert (Hcode : cm_simple_code_for policy p fid_pre simple lvalue_pre =
    cm_expr_code_for policy p fid_pre pc_pre temp_pre (cm_simple_source_expr simple) lvalue_pre).
  { destruct simple as [leaf | scope slot ty];
      [destruct leaf | ];
      unfold cm_simple_code_for, cm_simple_source_expr, cm_leaf_code_for,
        cm_leaf_source_expr, cm_leaf_rvalue, cm_expr_code_for, cm_var_code_for;
      destruct (Z.eqb lvalue_pre 0); reflexivity. }
  rewrite Hcode.
  cancel.
Qed.

Lemma proof_of_cm_emit_expr_return_wit_3 : cm_emit_expr_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_expr_return_wit_3_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_expr_return_wit_10_split_goal_spatial : cm_emit_expr_return_wit_10_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e.
  assert (Hcode : cm_simple_code_for policy p fid_pre simple lvalue_pre =
    cm_expr_code_for policy p fid_pre pc_pre temp_pre (cm_simple_source_expr simple) lvalue_pre).
  { destruct simple as [leaf | scope slot ty];
      [destruct leaf | ];
      unfold cm_simple_code_for, cm_simple_source_expr, cm_leaf_code_for,
        cm_leaf_source_expr, cm_leaf_rvalue, cm_expr_code_for, cm_var_code_for;
      destruct (Z.eqb lvalue_pre 0); reflexivity. }
  rewrite Hcode.
  cancel.
Qed.

Lemma proof_of_cm_emit_expr_return_wit_10 : cm_emit_expr_return_wit_10.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_expr_return_wit_10_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_expr_return_wit_11_split_goal_spatial : cm_emit_expr_return_wit_11_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e.
  assert (Hcode : cm_simple_code_for policy p fid_pre simple lvalue_pre =
    cm_expr_code_for policy p fid_pre pc_pre temp_pre (cm_simple_source_expr simple) lvalue_pre).
  { destruct simple as [leaf | scope slot ty];
      [destruct leaf | ];
      unfold cm_simple_code_for, cm_simple_source_expr, cm_leaf_code_for,
        cm_leaf_source_expr, cm_leaf_rvalue, cm_expr_code_for, cm_var_code_for;
      destruct (Z.eqb lvalue_pre 0); reflexivity. }
  rewrite Hcode.
  cancel.
Qed.

Lemma proof_of_cm_emit_expr_return_wit_11 : cm_emit_expr_return_wit_11.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_expr_return_wit_11_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_expr_partial_solve_wit_13_pure_split_goal_1 : cm_emit_expr_partial_solve_wit_13_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold cm_expr_shape in *; assumption).
Qed.

Lemma proof_of_cm_emit_expr_partial_solve_wit_13_pure : cm_emit_expr_partial_solve_wit_13_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_expr_partial_solve_wit_13_pure_split_goal_1.
Qed.

Lemma proof_of_cm_emit_expr_partial_solve_wit_16_pure_split_goal_1 : cm_emit_expr_partial_solve_wit_16_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold cm_expr_shape in *; assumption).
Qed.

Lemma proof_of_cm_emit_expr_partial_solve_wit_16_pure : cm_emit_expr_partial_solve_wit_16_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_expr_partial_solve_wit_16_pure_split_goal_1.
Qed.

Lemma proof_of_cm_emit_expr_partial_solve_wit_19_pure_split_goal_1 : cm_emit_expr_partial_solve_wit_19_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold cm_expr_shape in *; assumption).
Qed.

Lemma proof_of_cm_emit_expr_partial_solve_wit_19_pure : cm_emit_expr_partial_solve_wit_19_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_expr_partial_solve_wit_19_pure_split_goal_1.
Qed.

Lemma proof_of_cm_emit_expr_partial_solve_wit_22_pure_split_goal_1 : cm_emit_expr_partial_solve_wit_22_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold cm_expr_shape in *; assumption).
Qed.

Lemma proof_of_cm_emit_expr_partial_solve_wit_22_pure : cm_emit_expr_partial_solve_wit_22_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_expr_partial_solve_wit_22_pure_split_goal_1.
Qed.

Lemma proof_of_cm_emit_expr_partial_solve_wit_25_pure_split_goal_1 : cm_emit_expr_partial_solve_wit_25_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold cm_expr_shape in *; assumption).
Qed.

Lemma proof_of_cm_emit_expr_partial_solve_wit_25_pure : cm_emit_expr_partial_solve_wit_25_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_expr_partial_solve_wit_25_pure_split_goal_1.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_1 : cm_emit_expr_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_expr_rep_node. unfold cm_expr_node.
  Intros a b args.
  Exists args b a.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_2 : cm_emit_expr_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn [cm_rep_expr_kind] in *; try discriminate.
  Exists (CMSimpleLeaf (CMLeafConst n ty)).
  split_pure_spatial.
  - unfold cm_expr_code_for, cm_simple_code_for, cm_leaf_code_for.
    destruct (Z.eqb lvalue 0);
      cbn [cm_emit_expr_pair cm_rcode_of cm_lcode_of cm_leaf_rvalue]; cancel.
  - split_pures; dump_pre_spatial; try reflexivity.
    unfold cm_simple_expr, cm_dispatch_leaf.
    cbn [cm_rep_expr_kind]. tauto.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_3_split_goal_spatial : cm_emit_expr_which_implies_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_expr_rep_node. unfold cm_expr_node.
  Exists xa xb xargs.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_3 : cm_emit_expr_which_implies_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_expr_which_implies_wit_3_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_4 : cm_emit_expr_which_implies_wit_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn [cm_rep_expr_kind] in *; try discriminate.
  Exists (CMSimpleLeaf (CMLeafString sid ty)).
  split_pure_spatial.
  - unfold cm_expr_code_for, cm_simple_code_for, cm_leaf_code_for.
    destruct (Z.eqb lvalue 0);
      cbn [cm_emit_expr_pair cm_rcode_of cm_lcode_of cm_leaf_rvalue]; cancel.
  - split_pures; dump_pre_spatial; try reflexivity.
    unfold cm_simple_expr, cm_dispatch_leaf.
    cbn [cm_rep_expr_kind]. tauto.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_5_split_goal_spatial : cm_emit_expr_which_implies_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_expr_rep_node. unfold cm_expr_node.
  Exists xa xb xargs.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_5 : cm_emit_expr_which_implies_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_expr_which_implies_wit_5_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_6 : cm_emit_expr_which_implies_wit_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn [cm_rep_expr_kind] in *; try discriminate.
  Exists (CMSimpleVar scope slot ty).
  split_pure_spatial.
  - unfold cm_expr_code_for, cm_simple_code_for, cm_var_code_for.
    destruct (Z.eqb lvalue 0);
      cbn [cm_emit_expr_pair cm_rcode_of cm_lcode_of]; cancel.
  - split_pures; dump_pre_spatial; try reflexivity.
    unfold cm_simple_expr, cm_dispatch_leaf.
    cbn [cm_rep_expr_kind]. tauto.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_7_split_goal_spatial : cm_emit_expr_which_implies_wit_7_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_expr_rep_node. unfold cm_expr_node.
  Exists xa xb xargs.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_7 : cm_emit_expr_which_implies_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_expr_which_implies_wit_7_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_8_split_goal_1 : cm_emit_expr_which_implies_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn in *; try discriminate; reflexivity.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_8 : cm_emit_expr_which_implies_wit_8.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_expr_which_implies_wit_8_split_goal_1.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_9_split_goal_spatial : cm_emit_expr_which_implies_wit_9_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_expr_rep_node. unfold cm_expr_node.
  Exists xa xb xargs.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_9 : cm_emit_expr_which_implies_wit_9.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_expr_which_implies_wit_9_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_10_split_goal_1 : cm_emit_expr_which_implies_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn in *; try discriminate; reflexivity.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_10 : cm_emit_expr_which_implies_wit_10.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_expr_which_implies_wit_10_split_goal_1.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_11_split_goal_spatial : cm_emit_expr_which_implies_wit_11_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_expr_rep_node. unfold cm_expr_node.
  Exists xa xb xargs.
  split_pure_spatial.
  - repeat progress cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_11 : cm_emit_expr_which_implies_wit_11.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_expr_which_implies_wit_11_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_12_split_goal_1 : cm_emit_expr_which_implies_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn in *; try discriminate; reflexivity.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_12 : cm_emit_expr_which_implies_wit_12.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_expr_which_implies_wit_12_split_goal_1.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_13_split_goal_spatial : cm_emit_expr_which_implies_wit_13_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_expr_rep_node. unfold cm_expr_node.
  Exists xa xb xargs.
  split_pure_spatial.
  - repeat progress cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_13 : cm_emit_expr_which_implies_wit_13.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_expr_which_implies_wit_13_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_14_split_goal_1 : cm_emit_expr_which_implies_wit_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn in *; try discriminate; reflexivity.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_14 : cm_emit_expr_which_implies_wit_14.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_expr_which_implies_wit_14_split_goal_1.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_15_split_goal_spatial : cm_emit_expr_which_implies_wit_15_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_expr_rep_node. unfold cm_expr_node.
  Exists xa xb xargs.
  split_pure_spatial.
  - repeat progress cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_15 : cm_emit_expr_which_implies_wit_15.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_expr_which_implies_wit_15_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_16_split_goal_1 : cm_emit_expr_which_implies_wit_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn in *; try discriminate; reflexivity.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_16 : cm_emit_expr_which_implies_wit_16.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_expr_which_implies_wit_16_split_goal_1.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_17_split_goal_spatial : cm_emit_expr_which_implies_wit_17_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_expr_rep_node. unfold cm_expr_node.
  Exists xa xb xargs.
  split_pure_spatial.
  - repeat progress cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_17 : cm_emit_expr_which_implies_wit_17.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_expr_which_implies_wit_17_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_18_split_goal_spatial : cm_emit_expr_which_implies_wit_18_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_expr_rep_node. unfold cm_expr_node.
  Exists xa xb xargs.
  split_pure_spatial.
  - repeat progress cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_18 : cm_emit_expr_which_implies_wit_18.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_expr_which_implies_wit_18_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_19 : cm_emit_expr_which_implies_wit_19.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn [cm_rep_expr_kind] in *; try discriminate.
  Exists (CMSimpleLeaf (CMLeafSizeof asked ty)).
  split_pure_spatial.
  - unfold cm_expr_code_for, cm_simple_code_for, cm_leaf_code_for.
    destruct (Z.eqb lvalue 0);
      cbn [cm_emit_expr_pair cm_rcode_of cm_lcode_of cm_leaf_rvalue]; cancel.
  - split_pures; dump_pre_spatial; try reflexivity.
    unfold cm_simple_expr, cm_dispatch_leaf.
    cbn [cm_rep_expr_kind]. tauto.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_20_split_goal_spatial : cm_emit_expr_which_implies_wit_20_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_expr_rep_node. unfold cm_expr_node.
  Exists xa xb xargs.
  split_pure_spatial.
  - repeat progress cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_20 : cm_emit_expr_which_implies_wit_20.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_expr_which_implies_wit_20_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_21 : cm_emit_expr_which_implies_wit_21.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn [cm_rep_expr_kind] in *; try discriminate.
  Exists (CMSimpleLeaf (CMLeafGetc ty)).
  split_pure_spatial.
  - unfold cm_expr_code_for, cm_simple_code_for, cm_leaf_code_for.
    destruct (Z.eqb lvalue 0);
      cbn [cm_emit_expr_pair cm_rcode_of cm_lcode_of cm_leaf_rvalue]; cancel.
  - split_pures; dump_pre_spatial; try reflexivity.
    unfold cm_simple_expr, cm_dispatch_leaf.
    cbn [cm_rep_expr_kind]. tauto.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_22_split_goal_spatial : cm_emit_expr_which_implies_wit_22_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_expr_rep_node. unfold cm_expr_node.
  Exists xa xb xargs.
  split_pure_spatial.
  - repeat progress cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_22 : cm_emit_expr_which_implies_wit_22.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_expr_which_implies_wit_22_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_23_split_goal_1 : cm_emit_expr_which_implies_wit_23_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; simpl in *; intuition discriminate.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_23 : cm_emit_expr_which_implies_wit_23.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_expr_which_implies_wit_23_split_goal_1.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_24_split_goal_spatial : cm_emit_expr_which_implies_wit_24_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_expr_rep_node. unfold cm_expr_node.
  Exists xa xb xargs.
  split_pure_spatial.
  - repeat progress cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_24 : cm_emit_expr_which_implies_wit_24.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_expr_which_implies_wit_24_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_25_split_goal_1 : cm_emit_expr_which_implies_wit_25_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; simpl in *; intuition discriminate.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_25 : cm_emit_expr_which_implies_wit_25.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_expr_which_implies_wit_25_split_goal_1.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_26_split_goal_spatial : cm_emit_expr_which_implies_wit_26_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_expr_rep_node. unfold cm_expr_node.
  Exists xa xb xargs.
  split_pure_spatial.
  - repeat progress cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_26 : cm_emit_expr_which_implies_wit_26.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_expr_which_implies_wit_26_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_27_split_goal_1 : cm_emit_expr_which_implies_wit_27_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; simpl in *; intuition discriminate.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_27 : cm_emit_expr_which_implies_wit_27.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_expr_which_implies_wit_27_split_goal_1.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_28_split_goal_spatial : cm_emit_expr_which_implies_wit_28_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_expr_rep_node. unfold cm_expr_node.
  Exists xa xb xargs.
  split_pure_spatial.
  - repeat progress cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_emit_expr_which_implies_wit_28 : cm_emit_expr_which_implies_wit_28.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_expr_which_implies_wit_28_split_goal_spatial.
Qed.

