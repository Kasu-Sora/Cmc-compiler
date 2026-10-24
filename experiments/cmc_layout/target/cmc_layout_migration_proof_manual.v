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
From SimpleC.EE.QCP_demos_human Require Import cmc_layout_migration_goal.
From SimpleC.EE.QCP_demos_human Require Import cmc_layout_migration_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.cmc_layout_migration_lib.
Local Open Scope sac.

Lemma proof_of_cm_max_return_wit_1_split_goal_1 : cm_max_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold cm_imax. rewrite Z.max_r by lia. reflexivity.
Qed.

Lemma proof_of_cm_max_return_wit_1 : cm_max_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_max_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_cm_max_return_wit_2_split_goal_1 : cm_max_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold cm_imax. rewrite Z.max_l by lia. reflexivity.
Qed.

Lemma proof_of_cm_max_return_wit_2 : cm_max_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_max_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_cmc_is_pointer_return_wit_1_split_goal_1 : cmc_is_pointer_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold cm_rep_is_pointer_code.
  destruct (Z.leb 1024 ty_pre) eqn:Hguard; [reflexivity |].
  apply Z.leb_gt in Hguard. lia.
Qed.

Lemma proof_of_cmc_is_pointer_return_wit_1 : cmc_is_pointer_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_is_pointer_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_cmc_is_pointer_return_wit_2_split_goal_1 : cmc_is_pointer_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold cm_rep_is_pointer_code.
  destruct (Z.leb 1024 ty_pre) eqn:Hguard; [| reflexivity].
  apply Z.leb_le in Hguard. lia.
Qed.

Lemma proof_of_cmc_is_pointer_return_wit_2 : cmc_is_pointer_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_is_pointer_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_cmc_leaf_size_return_wit_1_split_goal_1 : cmc_leaf_size_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: unfold cm_rep_leaf_size.
  all: destruct (Z.leb 1024 ty_pre) eqn:Hguard.
  all: try reflexivity.
  all: apply Z.leb_gt in Hguard; lia.
Qed.

Lemma proof_of_cmc_leaf_size_return_wit_1 : cmc_leaf_size_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_leaf_size_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_cmc_leaf_size_return_wit_2_split_goal_1 : cmc_leaf_size_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: reflexivity.
Qed.

Lemma proof_of_cmc_leaf_size_return_wit_2 : cmc_leaf_size_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_leaf_size_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_cmc_leaf_size_return_wit_3_split_goal_1 : cmc_leaf_size_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: reflexivity.
Qed.

Lemma proof_of_cmc_leaf_size_return_wit_3 : cmc_leaf_size_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_leaf_size_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_cmc_leaf_size_return_wit_4_split_goal_1 : cmc_leaf_size_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: unfold cm_rep_leaf_size.
  all: destruct (Z.leb 1024 ty_pre) eqn:Hguard.
  all: try (apply Z.leb_le in Hguard; lia).
  all: destruct (Z.eqb ty_pre 0) eqn:Hzero.
  all: try (apply Z.eqb_eq in Hzero; lia).
  all: destruct (Z.eqb ty_pre 1) eqn:Hone.
  all: try (apply Z.eqb_eq in Hone; lia).
  all: reflexivity.
Qed.

Lemma proof_of_cmc_leaf_size_return_wit_4 : cmc_leaf_size_return_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_leaf_size_return_wit_4_split_goal_1.
Qed.

Lemma proof_of_cmc_code_slot_size_return_wit_1_split_goal_1 : cmc_code_slot_size_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: unfold cm_rep_code_slot_size; cbn; assumption.
Qed.

Lemma proof_of_cmc_code_slot_size_return_wit_1 : cmc_code_slot_size_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_code_slot_size_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_cmc_code_slot_size_return_wit_2_split_goal_1 : cmc_code_slot_size_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: unfold cm_rep_code_slot_size.
  all: destruct (Z.eqb count_pre 0) eqn:Hcount.
  all: try (apply Z.eqb_eq in Hcount; lia).
  all: subst; reflexivity.
Qed.

Lemma proof_of_cmc_code_slot_size_return_wit_2 : cmc_code_slot_size_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_code_slot_size_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_cmc_members_size_safety_wit_3_split_goal_1 : cmc_members_size_safety_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst. cbn [cm_rep_members_safe cm_rep_members_size] in *.
  unfold cm_rep_member_size in *.
  int_auto.
Qed.

Lemma proof_of_cmc_members_size_safety_wit_3_split_goal_2 : cmc_members_size_safety_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst. cbn [cm_rep_members_safe cm_rep_members_size] in *.
  unfold cm_rep_member_size in *.
  int_auto.
Qed.

Lemma proof_of_cmc_members_size_safety_wit_3 : cmc_members_size_safety_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_members_size_safety_wit_3_split_goal_1.
  - Goal_apply proof_of_cmc_members_size_safety_wit_3_split_goal_2.
Qed.

Lemma proof_of_cmc_members_size_entail_wit_1 : cmc_members_size_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct members as [|head tail].
  - cbn [cm_member_list_rep]. Intros_p Hzero. contradiction.
  - cbn [cm_member_list_rep]. Intros nextp.
    Exists nextp head tail.
    split_pure_spatial.
    + cancel (cm_member_list_rep nextp tail).
      cancel (&(member_pre # "cm_member" ->ₛ "ty") # Int |-> cm_type_encode (cm_slot_ty head)).
      cancel (&(member_pre # "cm_member" ->ₛ "count") # Int |-> cm_slot_count head).
      cancel (&(member_pre # "cm_member" ->ₛ "next") # Ptr |-> nextp).
    + split_pures; dump_pre_spatial; cbn [cm_rep_members_safe] in *; tauto.
Qed.

Lemma proof_of_cmc_members_size_return_wit_1_split_goal_1 : cmc_members_size_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_cmc_members_size_return_wit_1 : cmc_members_size_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct members as [|head tail].
  - split_pure_spatial.
    + cancel.
    + split_pures; dump_pre_spatial; cbn [cm_rep_members_safe cm_rep_members_size]; auto.
  - cbn [cm_member_list_rep]. Intros nextp. contradiction.
Qed.

Lemma proof_of_cmc_members_size_return_wit_2_split_goal_1 : cmc_members_size_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst. reflexivity.
Qed.

Lemma proof_of_cmc_members_size_return_wit_2_split_goal_spatial : cmc_members_size_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst members. cbn [cm_member_list_rep].
  Exists nextp.
  split_pure_spatial.
  - cancel (cm_member_list_rep nextp tail).
    cancel (&(member_pre # "cm_member" ->ₛ "ty") # Int |-> cm_type_encode (cm_slot_ty head)).
    cancel (&(member_pre # "cm_member" ->ₛ "count") # Int |-> cm_slot_count head).
    cancel (&(member_pre # "cm_member" ->ₛ "next") # Ptr |-> nextp).
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cmc_members_size_return_wit_2 : cmc_members_size_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_members_size_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_cmc_members_size_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_cmc_struct_size_at_entail_wit_1 : cmc_struct_size_at_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct structs as [|head tail].
  - cbn [cm_struct_list_rep]. Intros_p Hnull. contradiction.
  - cbn [cm_struct_list_rep]. Intros memberp nextp.
    Exists nextp memberp head tail.
    split_pure_spatial.
    + repeat progress cancel.
    + simpl in *. split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_cmc_struct_size_at_return_wit_1_split_goal_1 : cmc_struct_size_at_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_cmc_struct_size_at_return_wit_1 : cmc_struct_size_at_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct structs as [|head tail].
  - cbn [cm_rep_struct_size]. split_pure_spatial.
    + repeat progress cancel.
    + split_pures; dump_pre_spatial; auto.
  - cbn [cm_struct_list_rep]. Intros memberp nextp. contradiction.
Qed.

Lemma proof_of_cmc_struct_size_at_return_wit_2_split_goal_1 : cmc_struct_size_at_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst. reflexivity.
Qed.

Lemma proof_of_cmc_struct_size_at_return_wit_2_split_goal_spatial : cmc_struct_size_at_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst structs. cbn [cm_struct_list_rep].
  Exists memberp nextp.
  split_pure_spatial.
  - repeat progress cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cmc_struct_size_at_return_wit_2 : cmc_struct_size_at_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_struct_size_at_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_cmc_struct_size_at_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_cmc_struct_size_at_return_wit_3_split_goal_1 : cmc_struct_size_at_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst structs. cbn [cm_rep_struct_size].
  assert (Hindex : Z.eqb sid_pre 0 = false) by (apply Z.eqb_neq; assumption).
  rewrite Hindex. assumption.
Qed.

Lemma proof_of_cmc_struct_size_at_return_wit_3_split_goal_spatial : cmc_struct_size_at_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst structs. cbn [cm_struct_list_rep].
  Exists memberp nextp.
  split_pure_spatial.
  - repeat progress cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cmc_struct_size_at_return_wit_3 : cmc_struct_size_at_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_struct_size_at_return_wit_3_split_goal_spatial.
  - Goal_apply proof_of_cmc_struct_size_at_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_cmc_nonzero_return_wit_1_split_goal_1 : cmc_nonzero_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_cmc_nonzero_return_wit_1 : cmc_nonzero_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_nonzero_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_cmc_nonzero_return_wit_2_split_goal_1 : cmc_nonzero_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold cm_rep_nonzero.
  destruct (Z.eqb n_pre 0) eqn:Hguard; [| reflexivity].
  apply Z.eqb_eq in Hguard. lia.
Qed.

Lemma proof_of_cmc_nonzero_return_wit_2 : cmc_nonzero_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_nonzero_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_cmc_global_array_at_entail_wit_1 : cmc_global_array_at_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct globals as [|h t].
  - simpl cm_global_list_rep. Intros_p Hzero. contradiction.
  - simpl cm_global_list_rep. Intros n.
    Exists n h t. split_pure_spatial.
    + entailer_with ltac:(lia || nia || int_auto).
    + split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_cmc_global_array_at_return_wit_1_split_goal_1 : cmc_global_array_at_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_cmc_global_array_at_return_wit_1 : cmc_global_array_at_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct globals as [|h t].
  - simpl cm_rep_global_array. split_pure_spatial.
    + cancel.
    + split_pures; dump_pre_spatial; auto.
  - simpl cm_global_list_rep. Intros n. contradiction.
Qed.

Lemma proof_of_cmc_global_array_at_return_wit_2_split_goal_1 : cmc_global_array_at_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst globals. simpl cm_rep_global_array. assumption.
Qed.

Lemma proof_of_cmc_global_array_at_return_wit_2_split_goal_spatial : cmc_global_array_at_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst globals. simpl cm_global_list_rep. Exists nextp.
  split_pure_spatial.
  - entailer_with ltac:(lia || nia || int_auto).
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cmc_global_array_at_return_wit_2 : cmc_global_array_at_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_global_array_at_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_cmc_global_array_at_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_cmc_global_array_at_return_wit_3_split_goal_1 : cmc_global_array_at_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst globals. simpl cm_rep_global_array.
  destruct (Z.eqb_spec index_pre 0); [contradiction|assumption].
Qed.

Lemma proof_of_cmc_global_array_at_return_wit_3_split_goal_spatial : cmc_global_array_at_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst globals. simpl cm_global_list_rep. Exists nextp.
  split_pure_spatial.
  - entailer_with ltac:(lia || nia || int_auto).
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cmc_global_array_at_return_wit_3 : cmc_global_array_at_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_global_array_at_return_wit_3_split_goal_spatial.
  - Goal_apply proof_of_cmc_global_array_at_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_cmc_slot_array_at_entail_wit_1 : cmc_slot_array_at_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct slots as [|head tail]; simpl cm_slot_list_rep.
  - Intros_p Hnull. contradiction.
  - Intros nextp.
    Exists nextp head tail.
    split_pure_spatial.
    + sepcon_right_assoc. cancel.
    + split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_cmc_slot_array_at_return_wit_1_split_goal_1 : cmc_slot_array_at_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_cmc_slot_array_at_return_wit_1 : cmc_slot_array_at_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct slots as [|head tail]; simpl cm_slot_list_rep.
  - Intros_p Hnull. simpl cm_rep_member_array.
    split_pure_spatial.
    + sepcon_right_assoc. cancel.
    + split_pures; dump_pre_spatial; auto.
  - Intros nextp. contradiction.
Qed.

Lemma proof_of_cmc_slot_array_at_return_wit_2_split_goal_1 : cmc_slot_array_at_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst. reflexivity.
Qed.

Lemma proof_of_cmc_slot_array_at_return_wit_2_split_goal_spatial : cmc_slot_array_at_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst slots. simpl cm_slot_list_rep. Exists nextp.
  split_pure_spatial.
  - sepcon_right_assoc. cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cmc_slot_array_at_return_wit_2 : cmc_slot_array_at_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_slot_array_at_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_cmc_slot_array_at_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_cmc_slot_array_at_return_wit_3_split_goal_1 : cmc_slot_array_at_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst slots. simpl cm_rep_member_array.
  destruct (Z.eqb_spec index_pre 0); [contradiction|assumption].
Qed.

Lemma proof_of_cmc_slot_array_at_return_wit_3_split_goal_spatial : cmc_slot_array_at_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst slots. simpl cm_slot_list_rep. Exists nextp.
  split_pure_spatial.
  - sepcon_right_assoc. cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cmc_slot_array_at_return_wit_3 : cmc_slot_array_at_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_slot_array_at_return_wit_3_split_goal_spatial.
  - Goal_apply proof_of_cmc_slot_array_at_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_cmc_slot_type_at_entail_wit_1 : cmc_slot_type_at_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct slots as [|head tail].
  - cbn [cm_slot_list_rep]. Intros_p Hzero. contradiction.
  - cbn [cm_slot_list_rep]. Intros nextp.
    Exists nextp head tail.
    entailer_with ltac:(lia || reflexivity || assumption).
Qed.

Lemma proof_of_cmc_slot_type_at_return_wit_1_split_goal_1 : cmc_slot_type_at_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_cmc_slot_type_at_return_wit_1 : cmc_slot_type_at_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct slots as [|head tail].
  - cbn [cm_rep_slot_type]. entailer_with ltac:(lia || reflexivity || assumption).
  - cbn [cm_slot_list_rep]. Intros nextp. contradiction.
Qed.

Lemma proof_of_cmc_slot_type_at_return_wit_2_split_goal_1 : cmc_slot_type_at_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst slots. cbn [cm_rep_slot_type]. entailer_with ltac:(lia || reflexivity || assumption).
Qed.

Lemma proof_of_cmc_slot_type_at_return_wit_2_split_goal_spatial : cmc_slot_type_at_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst slots. cbn [cm_slot_list_rep]. Exists nextp. entailer_with ltac:(lia || reflexivity || assumption).
Qed.

Lemma proof_of_cmc_slot_type_at_return_wit_2 : cmc_slot_type_at_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_slot_type_at_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_cmc_slot_type_at_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_cmc_slot_type_at_return_wit_3_split_goal_1 : cmc_slot_type_at_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst slots. cbn [cm_rep_slot_type].
  destruct (Z.eqb_spec index_pre 0); [contradiction|].
  entailer_with ltac:(lia || reflexivity || assumption).
Qed.

Lemma proof_of_cmc_slot_type_at_return_wit_3_split_goal_spatial : cmc_slot_type_at_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst slots. cbn [cm_slot_list_rep]. Exists nextp. entailer_with ltac:(lia || reflexivity || assumption).
Qed.

Lemma proof_of_cmc_slot_type_at_return_wit_3 : cmc_slot_type_at_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_slot_type_at_return_wit_3_split_goal_spatial.
  - Goal_apply proof_of_cmc_slot_type_at_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_cmc_member_array_at_entail_wit_1 : cmc_member_array_at_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct members as [|h t].
  - simpl cm_member_list_rep. Intros_p Hz. contradiction.
  - simpl cm_member_list_rep. Intros n.
    Exists n h t. split_pure_spatial; try (repeat progress cancel); try (split_pures; dump_pre_spatial; auto).
Qed. 

Lemma proof_of_cmc_member_array_at_return_wit_1_split_goal_1 : cmc_member_array_at_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_cmc_member_array_at_return_wit_1 : cmc_member_array_at_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct members as [|h t].
  - simpl cm_rep_member_array. split_pure_spatial; try (repeat progress cancel); try (split_pures; dump_pre_spatial; auto).
  - simpl cm_member_list_rep. Intros n. contradiction.
Qed. 

Lemma proof_of_cmc_member_array_at_return_wit_2_split_goal_1 : cmc_member_array_at_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst members. simpl cm_rep_member_array. dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cmc_member_array_at_return_wit_2_split_goal_spatial : cmc_member_array_at_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst members. simpl cm_member_list_rep. Exists nextp. split_pure_spatial; try (repeat progress cancel); try (split_pures; dump_pre_spatial; auto).
Qed.

Lemma proof_of_cmc_member_array_at_return_wit_2 : cmc_member_array_at_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_member_array_at_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_cmc_member_array_at_return_wit_2_split_goal_1.
Qed. 

Lemma proof_of_cmc_member_array_at_return_wit_3_split_goal_1 : cmc_member_array_at_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst members. simpl cm_rep_member_array.
  destruct (Z.eqb_spec index_pre 0); [contradiction|]. dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cmc_member_array_at_return_wit_3_split_goal_spatial : cmc_member_array_at_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst members. simpl cm_member_list_rep. Exists nextp. split_pure_spatial; try (repeat progress cancel); try (split_pures; dump_pre_spatial; auto).
Qed.

Lemma proof_of_cmc_member_array_at_return_wit_3 : cmc_member_array_at_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_member_array_at_return_wit_3_split_goal_spatial.
  - Goal_apply proof_of_cmc_member_array_at_return_wit_3_split_goal_1.
Qed. 

Lemma proof_of_cmc_type_size_at_return_wit_1_split_goal_1 : cmc_type_size_at_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold cm_rep_type_size.
  destruct (Z.leb_spec 1024 ty_pre); [reflexivity | lia].
Qed.

Lemma proof_of_cmc_type_size_at_return_wit_1 : cmc_type_size_at_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_type_size_at_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_cmc_type_size_at_return_wit_2_split_goal_1 : cmc_type_size_at_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_cmc_type_size_at_return_wit_2 : cmc_type_size_at_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_type_size_at_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_cmc_type_size_at_return_wit_3_split_goal_1 : cmc_type_size_at_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_cmc_type_size_at_return_wit_3 : cmc_type_size_at_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_type_size_at_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_cmc_type_size_at_return_wit_4_split_goal_1 : cmc_type_size_at_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold cm_rep_type_size.
  destruct (Z.leb_spec 1024 ty_pre); [lia |].
  destruct (Z.eqb_spec ty_pre 0); [lia |].
  destruct (Z.eqb_spec ty_pre 1); lia.
Qed.

Lemma proof_of_cmc_type_size_at_return_wit_4 : cmc_type_size_at_return_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_type_size_at_return_wit_4_split_goal_1.
Qed.

Lemma proof_of_cmc_slots_size_safety_wit_3_split_goal_1 : cmc_slots_size_safety_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial. subst.
  cbn [cm_rep_members_safe cm_rep_members_size] in *.
  unfold cm_rep_member_size in *.
  lia.
Qed.

Lemma proof_of_cmc_slots_size_safety_wit_3_split_goal_2 : cmc_slots_size_safety_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial. subst.
  cbn [cm_rep_members_safe cm_rep_members_size] in *.
  unfold cm_rep_member_size in *.
  lia.
Qed.

Lemma proof_of_cmc_slots_size_safety_wit_3 : cmc_slots_size_safety_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_slots_size_safety_wit_3_split_goal_1.
  - Goal_apply proof_of_cmc_slots_size_safety_wit_3_split_goal_2.
Qed.

Lemma proof_of_cmc_slots_size_entail_wit_1 : cmc_slots_size_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia).
  destruct slots as [|h t].
  - cbn [cm_slot_list_rep]. Intros_p Hzero. contradiction.
  - cbn [cm_slot_list_rep]. Intros n.
    Exists n h t.
    split_pure_spatial.
    + entailer_with ltac:(lia).
    + split_pures; dump_pre_spatial; cbn [cm_rep_members_safe] in *; tauto.
Qed.

Lemma proof_of_cmc_slots_size_return_wit_1_split_goal_1 : cmc_slots_size_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_cmc_slots_size_return_wit_1 : cmc_slots_size_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia).
  destruct slots as [|h t].
  - cbn [cm_rep_members_size].
    split_pure_spatial.
    + entailer_with ltac:(lia).
    + split_pures; dump_pre_spatial; auto; lia.
  - cbn [cm_slot_list_rep]. Intros n. contradiction.
Qed.

Lemma proof_of_cmc_slots_size_return_wit_2_split_goal_1 : cmc_slots_size_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial. subst.
  cbn [cm_rep_members_safe cm_rep_members_size] in *.
  unfold cm_rep_member_size in *. lia.
Qed.

Lemma proof_of_cmc_slots_size_return_wit_2_split_goal_2 : cmc_slots_size_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial. subst.
  cbn [cm_rep_members_safe cm_rep_members_size] in *.
  unfold cm_rep_member_size in *. lia.
Qed.

Lemma proof_of_cmc_slots_size_return_wit_2_split_goal_3 : cmc_slots_size_return_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial. subst.
  cbn [cm_rep_members_size]. unfold cm_rep_member_size. reflexivity.
Qed.

Lemma proof_of_cmc_slots_size_return_wit_2_split_goal_spatial : cmc_slots_size_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  subst slots. cbn [cm_slot_list_rep].
  Exists nextp. split_pure_spatial.
  - entailer_with ltac:(lia).
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cmc_slots_size_return_wit_2 : cmc_slots_size_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_slots_size_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_cmc_slots_size_return_wit_2_split_goal_1.
  - Goal_apply proof_of_cmc_slots_size_return_wit_2_split_goal_2.
  - Goal_apply proof_of_cmc_slots_size_return_wit_2_split_goal_3.
Qed.

Lemma proof_of_cmc_slots_prefix_safety_wit_7_split_goal_1 : cmc_slots_prefix_safety_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst slots; try subst retval; cbn [cm_rep_members_safe cm_rep_members_size] in *;
  unfold cm_rep_member_size in *; lia.
Qed.

Lemma proof_of_cmc_slots_prefix_safety_wit_7_split_goal_2 : cmc_slots_prefix_safety_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst slots; try subst retval; cbn [cm_rep_members_safe cm_rep_members_size] in *;
  unfold cm_rep_member_size in *; lia.
Qed.

Lemma proof_of_cmc_slots_prefix_safety_wit_7 : cmc_slots_prefix_safety_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_slots_prefix_safety_wit_7_split_goal_1.
  - Goal_apply proof_of_cmc_slots_prefix_safety_wit_7_split_goal_2.

Qed. 

Lemma proof_of_cmc_slots_prefix_entail_wit_1 : cmc_slots_prefix_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct slots as [|h t].
  - cbn [cm_slot_list_rep]. Intros_p Hzero. contradiction.
  - cbn [cm_slot_list_rep]. Intros n.
    Exists n h t. split_pure_spatial.
    + sepcon_right_assoc. cancel.
    + split_pures; dump_pre_spatial; cbn [cm_rep_members_safe] in *; tauto.
Qed. 

Lemma proof_of_cmc_slots_prefix_return_wit_1_split_goal_1 : cmc_slots_prefix_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_cmc_slots_prefix_return_wit_1_split_goal_2 : cmc_slots_prefix_return_wit_1_split_goal_2.
Proof. Abort.

Lemma proof_of_cmc_slots_prefix_return_wit_1 : cmc_slots_prefix_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct slots as [|h t].
  - cbn [cm_rep_member_prefix cm_rep_members_size cm_rep_members_safe].
    split_pure_spatial.
    + sepcon_right_assoc. cancel.
    + split_pures; dump_pre_spatial; auto; lia.
  - cbn [cm_slot_list_rep]. Intros n. contradiction.
Qed. 

Lemma proof_of_cmc_slots_prefix_return_wit_2_split_goal_1 : cmc_slots_prefix_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst slots; try subst retval; cbn [cm_rep_members_safe cm_rep_members_size] in *;
  unfold cm_rep_member_size in *; lia.
Qed.

Lemma proof_of_cmc_slots_prefix_return_wit_2_split_goal_2 : cmc_slots_prefix_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst slots. reflexivity.
Qed.

Lemma proof_of_cmc_slots_prefix_return_wit_2_split_goal_spatial : cmc_slots_prefix_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst slots. cbn [cm_slot_list_rep].
  Exists nextp. split_pure_spatial.
  - sepcon_right_assoc. cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cmc_slots_prefix_return_wit_2 : cmc_slots_prefix_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_slots_prefix_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_cmc_slots_prefix_return_wit_2_split_goal_1.
  - Goal_apply proof_of_cmc_slots_prefix_return_wit_2_split_goal_2.

Qed. 

Lemma proof_of_cmc_slots_prefix_return_wit_3_split_goal_1 : cmc_slots_prefix_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst slots; try subst retval; cbn [cm_rep_members_safe cm_rep_members_size] in *;
  unfold cm_rep_member_size in *; lia.
Qed.

Lemma proof_of_cmc_slots_prefix_return_wit_3_split_goal_2 : cmc_slots_prefix_return_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst slots; try subst retval; cbn [cm_rep_members_safe cm_rep_members_size] in *;
  unfold cm_rep_member_size in *; lia.
Qed.

Lemma proof_of_cmc_slots_prefix_return_wit_3_split_goal_3 : cmc_slots_prefix_return_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  subst slots; try subst retval; cbn [cm_rep_members_safe cm_rep_members_size] in *;
  unfold cm_rep_member_size in *; lia.
Qed.

Lemma proof_of_cmc_slots_prefix_return_wit_3_split_goal_4 : cmc_slots_prefix_return_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst slots retval retval_2.
  cbn [cm_rep_member_prefix].
  destruct (Z.eqb index_pre 0) eqn:E; [apply Z.eqb_eq in E; contradiction|reflexivity].
Qed.

Lemma proof_of_cmc_slots_prefix_return_wit_3_split_goal_spatial : cmc_slots_prefix_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst slots. cbn [cm_slot_list_rep].
  Exists nextp. split_pure_spatial.
  - sepcon_right_assoc. cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cmc_slots_prefix_return_wit_3 : cmc_slots_prefix_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_slots_prefix_return_wit_3_split_goal_spatial.
  - Goal_apply proof_of_cmc_slots_prefix_return_wit_3_split_goal_1.
  - Goal_apply proof_of_cmc_slots_prefix_return_wit_3_split_goal_2.
  - Goal_apply proof_of_cmc_slots_prefix_return_wit_3_split_goal_3.
  - Goal_apply proof_of_cmc_slots_prefix_return_wit_3_split_goal_4.

Qed. 

Lemma proof_of_cmc_members_prefix_safety_wit_7_split_goal_1 : cmc_members_prefix_safety_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst members.
  cbn [cm_rep_members_safe cm_rep_members_size] in *.
  unfold cm_rep_member_size in *.
  int_auto.
Qed.

Lemma proof_of_cmc_members_prefix_safety_wit_7_split_goal_2 : cmc_members_prefix_safety_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst members.
  cbn [cm_rep_members_safe cm_rep_members_size] in *.
  unfold cm_rep_member_size in *.
  int_auto.
Qed.

Lemma proof_of_cmc_members_prefix_safety_wit_7 : cmc_members_prefix_safety_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_members_prefix_safety_wit_7_split_goal_1.
  - Goal_apply proof_of_cmc_members_prefix_safety_wit_7_split_goal_2.
Qed. 

Lemma proof_of_cmc_members_prefix_entail_wit_1 : cmc_members_prefix_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct members as [|h t].
  - cbn [cm_member_list_rep]. Intros_p Hnull. contradiction.
  - cbn [cm_member_list_rep]. Intros n.
    Exists n h t. split_pure_spatial; [sepcon_right_assoc; cancel|].
    split_pures; dump_pre_spatial; cbn [cm_rep_members_safe] in *; tauto.
Qed. 

Lemma proof_of_cmc_members_prefix_return_wit_1_split_goal_1 : cmc_members_prefix_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_cmc_members_prefix_return_wit_1_split_goal_2 : cmc_members_prefix_return_wit_1_split_goal_2.
Proof. Abort.

Lemma proof_of_cmc_members_prefix_return_wit_1 : cmc_members_prefix_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct members as [|h t].
  - cbn [cm_rep_member_prefix cm_rep_members_size].
    split_pure_spatial; [sepcon_right_assoc; cancel|]. split_pures; dump_pre_spatial; auto; lia.
  - cbn [cm_member_list_rep]. Intros n. contradiction.
Qed. 

Lemma proof_of_cmc_members_prefix_return_wit_2_split_goal_1 : cmc_members_prefix_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst members.
  cbn [cm_rep_members_safe cm_rep_members_size] in *.
  unfold cm_rep_member_size in *.
  lia.
Qed.

Lemma proof_of_cmc_members_prefix_return_wit_2_split_goal_2 : cmc_members_prefix_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst members. reflexivity.
Qed.

Lemma proof_of_cmc_members_prefix_return_wit_2_split_goal_spatial : cmc_members_prefix_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst members. cbn [cm_member_list_rep].
  Exists nextp. split_pure_spatial; [sepcon_right_assoc; cancel|dump_pre_spatial; assumption].
Qed.

Lemma proof_of_cmc_members_prefix_return_wit_2 : cmc_members_prefix_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_members_prefix_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_cmc_members_prefix_return_wit_2_split_goal_1.
  - Goal_apply proof_of_cmc_members_prefix_return_wit_2_split_goal_2.
Qed. 

Lemma proof_of_cmc_members_prefix_return_wit_3_split_goal_1 : cmc_members_prefix_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst members.
  cbn [cm_rep_members_safe cm_rep_members_size] in *.
  unfold cm_rep_member_size in *.
  lia.
Qed.

Lemma proof_of_cmc_members_prefix_return_wit_3_split_goal_2 : cmc_members_prefix_return_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst members.
  cbn [cm_rep_members_safe cm_rep_members_size] in *.
  unfold cm_rep_member_size in *.
  lia.
Qed.

Lemma proof_of_cmc_members_prefix_return_wit_3_split_goal_3 : cmc_members_prefix_return_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst members.
  cbn [cm_rep_members_safe cm_rep_members_size] in *.
  unfold cm_rep_member_size in *.
  lia.
Qed.

Lemma proof_of_cmc_members_prefix_return_wit_3_split_goal_4 : cmc_members_prefix_return_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst members. cbn [cm_rep_member_prefix].
  destruct (Z.eqb_spec index_pre 0); [contradiction|].
  unfold cm_rep_member_size. lia.
Qed.

Lemma proof_of_cmc_members_prefix_return_wit_3_split_goal_spatial : cmc_members_prefix_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst members. cbn [cm_member_list_rep].
  Exists nextp. split_pure_spatial; [sepcon_right_assoc; cancel|dump_pre_spatial; assumption].
Qed.

Lemma proof_of_cmc_members_prefix_return_wit_3 : cmc_members_prefix_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_members_prefix_return_wit_3_split_goal_spatial.
  - Goal_apply proof_of_cmc_members_prefix_return_wit_3_split_goal_1.
  - Goal_apply proof_of_cmc_members_prefix_return_wit_3_split_goal_2.
  - Goal_apply proof_of_cmc_members_prefix_return_wit_3_split_goal_3.
  - Goal_apply proof_of_cmc_members_prefix_return_wit_3_split_goal_4.
Qed. 

Lemma proof_of_cmc_member_offset_at_entail_wit_1 : cmc_member_offset_at_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct structs as [|head tail].
  - cbn [cm_struct_list_rep]. Intros_p Hnil. contradiction.
  - cbn [cm_struct_list_rep]. Intros memberp nextp.
    Exists nextp memberp head tail.
    split_pure_spatial.
    + sepcon_right_assoc. cancel.
    + split_pures; dump_pre_spatial; cbn [cm_rep_structs_safe] in *; tauto.
Qed. 

Lemma proof_of_cmc_member_offset_at_return_wit_1_split_goal_1 : cmc_member_offset_at_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_cmc_member_offset_at_return_wit_1 : cmc_member_offset_at_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct structs as [|head tail].
  - cbn [cm_rep_struct_member_prefix].
    split_pure_spatial.
    + sepcon_right_assoc. cancel.
    + split_pures; dump_pre_spatial; auto; lia.
  - cbn [cm_struct_list_rep]. Intros memberp nextp. contradiction.
Qed. 

Lemma proof_of_cmc_member_offset_at_return_wit_2_split_goal_1 : cmc_member_offset_at_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst. cbn [cm_rep_struct_member_prefix]. reflexivity.
Qed.

Lemma proof_of_cmc_member_offset_at_return_wit_2_split_goal_spatial : cmc_member_offset_at_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst structs. cbn [cm_struct_list_rep].
  Exists memberp nextp. split_pure_spatial.
  - sepcon_right_assoc. cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cmc_member_offset_at_return_wit_2 : cmc_member_offset_at_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_member_offset_at_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_cmc_member_offset_at_return_wit_2_split_goal_1.
Qed. 

Lemma proof_of_cmc_member_offset_at_return_wit_3_split_goal_1 : cmc_member_offset_at_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst structs retval.
  cbn [cm_rep_struct_member_prefix].
  destruct (Z.eqb sid_pre 0) eqn:Hsid.
  - apply Z.eqb_eq in Hsid. contradiction.
  - reflexivity.
Qed.

Lemma proof_of_cmc_member_offset_at_return_wit_3_split_goal_spatial : cmc_member_offset_at_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst structs. cbn [cm_struct_list_rep].
  Exists memberp nextp. split_pure_spatial.
  - sepcon_right_assoc. cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cmc_member_offset_at_return_wit_3 : cmc_member_offset_at_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_member_offset_at_return_wit_3_split_goal_spatial.
  - Goal_apply proof_of_cmc_member_offset_at_return_wit_3_split_goal_1.
Qed. 

Lemma proof_of_cmc_struct_member_array_at_entail_wit_1 : cmc_struct_member_array_at_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct structs as [|head tail].
  - cbn [cm_struct_list_rep]. Intros_p Hnull. contradiction.
  - cbn [cm_struct_list_rep]. Intros memberp nextp.
    Exists nextp memberp head tail.
    split_pure_spatial.
    + repeat progress cancel.
    + cbn [cm_rep_structs_safe] in *.
      split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_cmc_struct_member_array_at_return_wit_1_split_goal_1 : cmc_struct_member_array_at_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_cmc_struct_member_array_at_return_wit_1 : cmc_struct_member_array_at_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct structs as [|head tail].
  - cbn [cm_rep_struct_member_array]. split_pure_spatial.
    + repeat progress cancel.
    + split_pures; dump_pre_spatial; auto.
  - cbn [cm_struct_list_rep]. Intros memberp nextp. contradiction.
Qed.

Lemma proof_of_cmc_struct_member_array_at_return_wit_2_split_goal_1 : cmc_struct_member_array_at_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst. reflexivity.
Qed.

Lemma proof_of_cmc_struct_member_array_at_return_wit_2_split_goal_spatial : cmc_struct_member_array_at_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst structs. cbn [cm_struct_list_rep]. Exists memberp nextp.
  split_pure_spatial.
  - repeat progress cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cmc_struct_member_array_at_return_wit_2 : cmc_struct_member_array_at_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_struct_member_array_at_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_cmc_struct_member_array_at_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_cmc_struct_member_array_at_return_wit_3_split_goal_1 : cmc_struct_member_array_at_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst structs. cbn [cm_rep_struct_member_array].
  destruct (Z.eqb_spec sid_pre 0); [contradiction|assumption].
Qed.

Lemma proof_of_cmc_struct_member_array_at_return_wit_3_split_goal_spatial : cmc_struct_member_array_at_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst structs. cbn [cm_struct_list_rep]. Exists memberp nextp.
  split_pure_spatial.
  - repeat progress cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cmc_struct_member_array_at_return_wit_3 : cmc_struct_member_array_at_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_struct_member_array_at_return_wit_3_split_goal_spatial.
  - Goal_apply proof_of_cmc_struct_member_array_at_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_cmc_globals_size_safety_wit_3_split_goal_1 : cmc_globals_size_safety_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  subst; simpl in *; unfold cm_rep_global_size in *; lia.
Qed.

Lemma proof_of_cmc_globals_size_safety_wit_3_split_goal_2 : cmc_globals_size_safety_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  subst; simpl in *; unfold cm_rep_global_size in *; lia.
Qed.

Lemma proof_of_cmc_globals_size_safety_wit_3 : cmc_globals_size_safety_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_globals_size_safety_wit_3_split_goal_1.
  - Goal_apply proof_of_cmc_globals_size_safety_wit_3_split_goal_2.
Qed.

Lemma proof_of_cmc_globals_size_entail_wit_1 : cmc_globals_size_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia).
  destruct globals as [|h t].
  - simpl cm_global_list_rep. Intros_p Hzero. contradiction.
  - simpl cm_global_list_rep. Intros n.
    Exists n h t.
    split_pure_spatial.
    + sepcon_right_assoc; cancel.
    + split_pures; dump_pre_spatial; simpl in *; intuition.
Qed.

Lemma proof_of_cmc_globals_size_return_wit_1_split_goal_1 : cmc_globals_size_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_cmc_globals_size_return_wit_1 : cmc_globals_size_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia).
  destruct globals as [|h t].
  - split_pure_spatial.
    + cancel.
    + split_pures; dump_pre_spatial; simpl; auto; lia.
  - simpl cm_global_list_rep. Intros n. contradiction.
Qed.

Lemma proof_of_cmc_globals_size_return_wit_2_split_goal_1 : cmc_globals_size_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  subst; simpl in *; unfold cm_rep_global_size in *; lia.
Qed.

Lemma proof_of_cmc_globals_size_return_wit_2_split_goal_2 : cmc_globals_size_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  subst; simpl in *; unfold cm_rep_global_size in *; lia.
Qed.

Lemma proof_of_cmc_globals_size_return_wit_2_split_goal_3 : cmc_globals_size_return_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  subst; simpl; unfold cm_rep_global_size; reflexivity.
Qed.

Lemma proof_of_cmc_globals_size_return_wit_2_split_goal_spatial : cmc_globals_size_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  subst globals. simpl cm_global_list_rep.
  Exists nextp. split_pure_spatial.
  - sepcon_right_assoc; cancel.
  - dump_pre_spatial; assumption.
Qed.

Lemma proof_of_cmc_globals_size_return_wit_2 : cmc_globals_size_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_globals_size_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_cmc_globals_size_return_wit_2_split_goal_1.
  - Goal_apply proof_of_cmc_globals_size_return_wit_2_split_goal_2.
  - Goal_apply proof_of_cmc_globals_size_return_wit_2_split_goal_3.
Qed.

Lemma proof_of_cmc_globals_prefix_safety_wit_7_split_goal_1 : cmc_globals_prefix_safety_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst globals retval.
  cbn [cm_rep_globals_safe cm_rep_globals_size] in *.
  unfold cm_rep_global_size in *.
  change (cm_rep_code_slot_size (cm_type_encode (cm_global_ty head)) (cm_global_count head) + retval_2 <= 9223372036854775807). lia.
Qed.

Lemma proof_of_cmc_globals_prefix_safety_wit_7_split_goal_2 : cmc_globals_prefix_safety_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst globals retval.
  cbn [cm_rep_globals_safe cm_rep_globals_size] in *.
  unfold cm_rep_global_size in *.
  change (-9223372036854775808 <= cm_rep_code_slot_size (cm_type_encode (cm_global_ty head)) (cm_global_count head) + retval_2). lia.
Qed.

Lemma proof_of_cmc_globals_prefix_safety_wit_7 : cmc_globals_prefix_safety_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_globals_prefix_safety_wit_7_split_goal_1.
  - Goal_apply proof_of_cmc_globals_prefix_safety_wit_7_split_goal_2.
Qed.

Lemma proof_of_cmc_globals_prefix_entail_wit_1 : cmc_globals_prefix_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct globals as [|head tail].
  - cbn [cm_global_list_rep]. Intros_p Hzero. contradiction.
  - cbn [cm_global_list_rep]. Intros nextp.
    Exists nextp head tail.
    split_pure_spatial.
    + sepcon_right_assoc. cancel.
    + split_pures; dump_pre_spatial; cbn [cm_rep_globals_safe] in *; tauto.
Qed.

Lemma proof_of_cmc_globals_prefix_return_wit_1_split_goal_1 : cmc_globals_prefix_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_cmc_globals_prefix_return_wit_1_split_goal_2 : cmc_globals_prefix_return_wit_1_split_goal_2.
Proof. Abort.

Lemma proof_of_cmc_globals_prefix_return_wit_1 : cmc_globals_prefix_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct globals as [|head tail].
  - cbn [cm_rep_globals_prefix cm_rep_globals_size cm_rep_globals_safe].
    split_pure_spatial.
    + cancel.
    + split_pures; dump_pre_spatial; auto; lia.
  - cbn [cm_global_list_rep]. Intros nextp. contradiction.
Qed.

Lemma proof_of_cmc_globals_prefix_return_wit_2_split_goal_1 : cmc_globals_prefix_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst globals.
  cbn [cm_rep_globals_safe cm_rep_globals_size] in *. lia.
Qed.

Lemma proof_of_cmc_globals_prefix_return_wit_2_split_goal_2 : cmc_globals_prefix_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst globals. reflexivity.
Qed.

Lemma proof_of_cmc_globals_prefix_return_wit_2_split_goal_spatial : cmc_globals_prefix_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst globals. cbn [cm_global_list_rep].
  Exists nextp.
  split_pure_spatial.
  - sepcon_right_assoc. cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cmc_globals_prefix_return_wit_2 : cmc_globals_prefix_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_globals_prefix_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_cmc_globals_prefix_return_wit_2_split_goal_1.
  - Goal_apply proof_of_cmc_globals_prefix_return_wit_2_split_goal_2.
Qed.

Lemma proof_of_cmc_globals_prefix_return_wit_3_split_goal_1 : cmc_globals_prefix_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst globals retval.
  cbn [cm_rep_globals_safe cm_rep_globals_size] in *.
  unfold cm_rep_global_size in *. lia.
Qed.

Lemma proof_of_cmc_globals_prefix_return_wit_3_split_goal_2 : cmc_globals_prefix_return_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst globals retval.
  cbn [cm_rep_globals_safe cm_rep_globals_size] in *.
  unfold cm_rep_global_size in *. lia.
Qed.

Lemma proof_of_cmc_globals_prefix_return_wit_3_split_goal_3 : cmc_globals_prefix_return_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst globals retval.
  cbn [cm_rep_globals_safe cm_rep_globals_size] in *.
  unfold cm_rep_global_size in *. lia.
Qed.

Lemma proof_of_cmc_globals_prefix_return_wit_3_split_goal_4 : cmc_globals_prefix_return_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst globals retval retval_2.
  cbn [cm_rep_globals_prefix].
  destruct (Z.eqb_spec index_pre 0); [contradiction|reflexivity].
Qed.

Lemma proof_of_cmc_globals_prefix_return_wit_3_split_goal_spatial : cmc_globals_prefix_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst globals. cbn [cm_global_list_rep].
  Exists nextp.
  split_pure_spatial.
  - sepcon_right_assoc. cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cmc_globals_prefix_return_wit_3 : cmc_globals_prefix_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_globals_prefix_return_wit_3_split_goal_spatial.
  - Goal_apply proof_of_cmc_globals_prefix_return_wit_3_split_goal_1.
  - Goal_apply proof_of_cmc_globals_prefix_return_wit_3_split_goal_2.
  - Goal_apply proof_of_cmc_globals_prefix_return_wit_3_split_goal_3.
  - Goal_apply proof_of_cmc_globals_prefix_return_wit_3_split_goal_4.
Qed.

Lemma proof_of_cmc_strings_size_entail_wit_1 : cmc_strings_size_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia).
  destruct strings as [|head tail].
  - cbn [cm_string_list_rep]. Intros_p Hzero. contradiction.
  - cbn [cm_string_list_rep]. Intros bytesp nextp.
    Exists nextp bytesp head tail.
    split_pure_spatial.
    + repeat progress cancel; auto.
    + cbn [cm_rep_strings_safe] in *. split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_cmc_strings_size_return_wit_1_split_goal_1 : cmc_strings_size_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_cmc_strings_size_return_wit_1 : cmc_strings_size_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia).
  destruct strings as [|head tail].
  - cbn [cm_rep_strings_size]. split_pure_spatial.
    + repeat progress cancel; auto.
    + split_pures; dump_pre_spatial; auto; lia.
  - cbn [cm_string_list_rep]. Intros bytesp nextp. contradiction.
Qed.

Lemma proof_of_cmc_strings_size_return_wit_2_split_goal_1 : cmc_strings_size_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial. subst strings retval.
  cbn [cm_rep_strings_safe cm_rep_strings_size] in *.
  unfold cm_rep_string_size in *. tauto.
Qed.

Lemma proof_of_cmc_strings_size_return_wit_2_split_goal_2 : cmc_strings_size_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial. subst strings retval.
  cbn [cm_rep_strings_safe cm_rep_strings_size] in *.
  unfold cm_rep_string_size in *. lia.
Qed.

Lemma proof_of_cmc_strings_size_return_wit_2_split_goal_3 : cmc_strings_size_return_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial. subst strings retval.
  cbn [cm_rep_strings_size]. unfold cm_rep_string_size. reflexivity.
Qed.

Lemma proof_of_cmc_strings_size_return_wit_2_split_goal_spatial : cmc_strings_size_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  subst strings. cbn [cm_string_list_rep].
  Exists bytesp nextp.
  split_pure_spatial.
  - repeat progress cancel; auto.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cmc_strings_size_return_wit_2 : cmc_strings_size_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_strings_size_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_cmc_strings_size_return_wit_2_split_goal_1.
  - Goal_apply proof_of_cmc_strings_size_return_wit_2_split_goal_2.
  - Goal_apply proof_of_cmc_strings_size_return_wit_2_split_goal_3.
Qed.

Lemma proof_of_cmc_strings_prefix_entail_wit_1 : cmc_strings_prefix_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct strings as [|h t].
  - cbn [cm_string_list_rep]. Intros_p Hz. contradiction.
  - cbn [cm_string_list_rep]. Intros b n.
    Exists n b h t.
    split_pure_spatial.
    + repeat progress cancel.
    + split_pures; dump_pre_spatial; try assumption; try reflexivity.
      cbn [cm_rep_strings_safe] in PreH3. tauto.
Qed. 

Lemma proof_of_cmc_strings_prefix_return_wit_1_split_goal_1 : cmc_strings_prefix_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_cmc_strings_prefix_return_wit_1_split_goal_2 : cmc_strings_prefix_return_wit_1_split_goal_2.
Proof. Abort.

Lemma proof_of_cmc_strings_prefix_return_wit_1 : cmc_strings_prefix_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct strings as [|h t].
  - cbn [cm_rep_strings_prefix cm_rep_strings_size].
    split_pure_spatial.
    + repeat progress cancel.
    + split_pures; dump_pre_spatial; auto; lia.
  - cbn [cm_string_list_rep]. Intros b n. contradiction.
Qed. 

Lemma proof_of_cmc_strings_prefix_return_wit_2_split_goal_1 : cmc_strings_prefix_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst strings.
  cbn [cm_rep_strings_safe cm_rep_strings_size] in *.
  lia.
Qed.

Lemma proof_of_cmc_strings_prefix_return_wit_2_split_goal_2 : cmc_strings_prefix_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst strings. reflexivity.
Qed.

Lemma proof_of_cmc_strings_prefix_return_wit_2_split_goal_spatial : cmc_strings_prefix_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst strings. cbn [cm_string_list_rep].
  Exists bytesp nextp.
  split_pure_spatial.
  - repeat progress cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cmc_strings_prefix_return_wit_2 : cmc_strings_prefix_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_strings_prefix_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_cmc_strings_prefix_return_wit_2_split_goal_1.
  - Goal_apply proof_of_cmc_strings_prefix_return_wit_2_split_goal_2.
Qed. 

Lemma proof_of_cmc_strings_prefix_return_wit_3_split_goal_1 : cmc_strings_prefix_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst strings.
  cbn [cm_rep_strings_safe cm_rep_strings_size] in *.
  unfold cm_rep_string_size in *. lia.
Qed.

Lemma proof_of_cmc_strings_prefix_return_wit_3_split_goal_2 : cmc_strings_prefix_return_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst strings.
  cbn [cm_rep_strings_safe cm_rep_strings_size] in *.
  unfold cm_rep_string_size in *. lia.
Qed.

Lemma proof_of_cmc_strings_prefix_return_wit_3_split_goal_3 : cmc_strings_prefix_return_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst strings.
  cbn [cm_rep_strings_safe cm_rep_strings_size] in *.
  unfold cm_rep_string_size in *. lia.
Qed.

Lemma proof_of_cmc_strings_prefix_return_wit_3_split_goal_4 : cmc_strings_prefix_return_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst strings.
  cbn [cm_rep_strings_prefix].
  destruct (Z.eqb_spec index_pre 0); [contradiction |].
  unfold cm_rep_string_size. lia.
Qed.

Lemma proof_of_cmc_strings_prefix_return_wit_3_split_goal_spatial : cmc_strings_prefix_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst strings. cbn [cm_string_list_rep].
  Exists bytesp nextp.
  split_pure_spatial.
  - repeat progress cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cmc_strings_prefix_return_wit_3 : cmc_strings_prefix_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_strings_prefix_return_wit_3_split_goal_spatial.
  - Goal_apply proof_of_cmc_strings_prefix_return_wit_3_split_goal_1.
  - Goal_apply proof_of_cmc_strings_prefix_return_wit_3_split_goal_2.
  - Goal_apply proof_of_cmc_strings_prefix_return_wit_3_split_goal_3.
  - Goal_apply proof_of_cmc_strings_prefix_return_wit_3_split_goal_4.
Qed. 

Lemma proof_of_cmc_global_address_return_wit_1_split_goal_1 : cmc_global_address_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold cm_rep_global_address; congruence).
Qed.

Lemma proof_of_cmc_global_address_return_wit_1 : cmc_global_address_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_global_address_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_cmc_string_address_return_wit_1_split_goal_1 : cmc_string_address_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold cm_rep_string_address; congruence).
Qed.

Lemma proof_of_cmc_string_address_return_wit_1 : cmc_string_address_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_string_address_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_cmc_binding_array_value_return_wit_1_split_goal_1 : cmc_binding_array_value_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst. unfold cm_binding_array_code. simpl Z.eqb.
  apply cm_rep_global_array_nth__lookup_bridge.
  unfold cm_binding_valid in *. intuition lia.
Qed.

Lemma proof_of_cmc_binding_array_value_return_wit_1 : cmc_binding_array_value_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_binding_array_value_return_wit_1_split_goal_1.
Qed. 

Lemma proof_of_cmc_binding_array_value_return_wit_2_split_goal_1 : cmc_binding_array_value_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst. unfold cm_binding_array_code. simpl Z.eqb.
  apply cm_rep_member_array_nth__lookup_bridge.
  unfold cm_binding_valid in *. intuition lia.
Qed.

Lemma proof_of_cmc_binding_array_value_return_wit_2 : cmc_binding_array_value_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_binding_array_value_return_wit_2_split_goal_1.
Qed. 

Lemma proof_of_cmc_binding_array_value_return_wit_3_split_goal_1 : cmc_binding_array_value_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_binding_array_code.
  destruct (Z.eqb_spec scope_pre 0); [contradiction|].
  destruct (Z.eqb_spec scope_pre 1); [contradiction|reflexivity].
Qed.

Lemma proof_of_cmc_binding_array_value_return_wit_3 : cmc_binding_array_value_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_binding_array_value_return_wit_3_split_goal_1.
Qed. 

Lemma proof_of_cmc_member_array_safety_wit_1_split_goal_1 : cmc_member_array_safety_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (Z.mod_pos_bound retval 1024 ltac:(lia)).
  rewrite Z.rem_mod_nonneg by lia.
  int_auto.
Qed.

Lemma proof_of_cmc_member_array_safety_wit_1_split_goal_2 : cmc_member_array_safety_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (Z.mod_pos_bound retval 1024 ltac:(lia)).
  rewrite Z.rem_mod_nonneg by lia.
  int_auto.
Qed.

Lemma proof_of_cmc_member_array_safety_wit_1 : cmc_member_array_safety_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_member_array_safety_wit_1_split_goal_1.
  Goal_apply proof_of_cmc_member_array_safety_wit_1_split_goal_2.
Qed. 

Lemma proof_of_cmc_member_array_return_wit_1_split_goal_1 : cmc_member_array_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst.
  unfold cm_member_valid in PreH13.
  destruct base; simpl in PreH13; try tauto.
  destruct base; simpl in PreH13; try tauto.
  change (0 <= sid < 1022) in PreH12.
  change (cm_rep_struct_member_array (cm_program_structs p)
    (Z.rem (1024 + (sid+2) - 1024) 1024 - 2) mid_pre =
    cm_member_array_code p (CMPtrTy (CMStructTy sid)) mid_pre).
  replace (1024 + (sid+2) - 1024) with (sid+2) by lia.
  rewrite Z.rem_mod_nonneg by lia.
  rewrite Z.mod_small by lia.
  replace (sid+2-2) with sid by lia.
  unfold cm_member_array_code. cbn [cm_pointee cm_struct_id].
  apply cm_rep_struct_member_array_nth__lookup_bridge; tauto.
Qed.

Lemma proof_of_cmc_member_array_return_wit_1 : cmc_member_array_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_member_array_return_wit_1_split_goal_1.
Qed. 

Lemma proof_of_cm_args_length_safety_wit_3_split_goal_1 : cm_args_length_safety_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst. simpl in *. lia.
Qed.

Lemma proof_of_cm_args_length_safety_wit_3_split_goal_2 : cm_args_length_safety_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst. simpl in *. lia.
Qed.

Lemma proof_of_cm_args_length_safety_wit_3 : cm_args_length_safety_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_args_length_safety_wit_3_split_goal_1.
  - Goal_apply proof_of_cm_args_length_safety_wit_3_split_goal_2.
Qed. 

Lemma proof_of_cm_args_length_entail_wit_1 : cm_args_length_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct args as [|h t].
  - simpl cm_arg_list_rep. Intros_p Hzero. contradiction.
  - simpl cm_arg_list_rep. Intros q n.
    Exists n q h t.
    split_pure_spatial.
    + repeat progress cancel.
    + split_pures; dump_pre_spatial; simpl in *; tauto.
Qed. 

Lemma proof_of_cm_args_length_return_wit_1_split_goal_1 : cm_args_length_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_cm_args_length_return_wit_1 : cm_args_length_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct args as [|h t].
  - split_pure_spatial.
    + repeat progress cancel.
    + split_pures; dump_pre_spatial; auto.
  - simpl cm_arg_list_rep. Intros q n. subst. contradiction.
Qed. 

Lemma proof_of_cm_args_length_return_wit_2_split_goal_1 : cm_args_length_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst. unfold cm_rep_args_length.
  rewrite Zlength_cons. lia.
Qed.

Lemma proof_of_cm_args_length_return_wit_2_split_goal_spatial : cm_args_length_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst args. simpl cm_arg_list_rep.
  Exists ep np. split_pure_spatial.
  - repeat progress cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_args_length_return_wit_2 : cm_args_length_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_args_length_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_cm_args_length_return_wit_2_split_goal_1.
Qed. 

Lemma proof_of_cmc_args_tpair_safety_wit_4_split_goal_1 : cmc_args_tpair_safety_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst args.
  cbn [cm_rep_args_temps_safe] in *.
  change (cm_acount (cm_args_apair tail) + 1 <= 2147483647). lia.
Qed.

Lemma proof_of_cmc_args_tpair_safety_wit_4_split_goal_2 : cmc_args_tpair_safety_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct tail; cbn [cm_rep_args_temps_safe cm_args_apair cm_acount] in *;
  unfold cm_rep_apair_safe in *; cbn [cm_acount cm_adepth] in *; lia.
Qed.

Lemma proof_of_cmc_args_tpair_safety_wit_4 : cmc_args_tpair_safety_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_args_tpair_safety_wit_4_split_goal_1.
  - Goal_apply proof_of_cmc_args_tpair_safety_wit_4_split_goal_2.
Qed. 

Lemma proof_of_cmc_args_tpair_entail_wit_1 : cmc_args_tpair_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct args as [|head tail].
  - cbn [cm_arg_list_rep]. Intros_p Hzero. contradiction.
  - cbn [cm_arg_list_rep]. Intros ep np.
    Exists np ep head tail.
    split_pure_spatial.
    + repeat progress cancel.
    + split_pures; dump_pre_spatial; try reflexivity; try assumption;
      cbn [cm_rep_args_temps_safe] in *; tauto.
Qed. 

Lemma proof_of_cmc_args_tpair_return_wit_1_split_goal_1 : cmc_args_tpair_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_cmc_args_tpair_return_wit_1_split_goal_2 : cmc_args_tpair_return_wit_1_split_goal_2.
Proof. Abort.

Lemma proof_of_cmc_args_tpair_return_wit_1 : cmc_args_tpair_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct args as [|head tail].
  - cbn [cm_args_apair cm_acount cm_adepth].
    split_pure_spatial; [repeat progress cancel | split_pures; dump_pre_spatial; assumption].
  - cbn [cm_arg_list_rep]. Intros ep np. contradiction.
Qed. 

Lemma proof_of_cmc_args_tpair_return_wit_2_split_goal_1 : cmc_args_tpair_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst args. cbn [cm_args_apair cm_acount]. lia.
Qed.

Lemma proof_of_cmc_args_tpair_return_wit_2_split_goal_2 : cmc_args_tpair_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst args. cbn [cm_args_apair cm_adepth]. assumption.
Qed.

Lemma proof_of_cmc_args_tpair_return_wit_2_split_goal_spatial : cmc_args_tpair_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst args. cbn [cm_arg_list_rep]. Exists ep np.
  split_pure_spatial; [repeat progress cancel | dump_pre_spatial; assumption].
Qed.

Lemma proof_of_cmc_args_tpair_return_wit_2 : cmc_args_tpair_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_args_tpair_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_cmc_args_tpair_return_wit_2_split_goal_1.
  - Goal_apply proof_of_cmc_args_tpair_return_wit_2_split_goal_2.
Qed. 

Lemma proof_of_cm_expr_temps_safety_wit_4_split_goal_1 : cm_expr_temps_safety_wit_4_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 dump_pre_spatial.
 subst e.
 cbn [cm_rep_expr_temps_safe] in PreH4.
 destruct PreH4 as [_ [Hstrict _]].
 unfold cm_rtemps in Hstrict.
 int_auto.
Qed.

Lemma proof_of_cm_expr_temps_safety_wit_4_split_goal_2 : cm_expr_temps_safety_wit_4_split_goal_2.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 dump_pre_spatial.
 pose proof (cm_expr_pair_safe__expr_safety y PreH1) as Hsafe.
 unfold cm_rep_tpair_safe in Hsafe.
 int_auto.
Qed.

Lemma proof_of_cm_expr_temps_safety_wit_4 : cm_expr_temps_safety_wit_4.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_cm_expr_temps_safety_wit_4_split_goal_1.
 - Goal_apply proof_of_cm_expr_temps_safety_wit_4_split_goal_2.
Qed.

Lemma proof_of_cm_expr_temps_safety_wit_9_split_goal_1 : cm_expr_temps_safety_wit_9_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 dump_pre_spatial.
 subst e.
 cbn [cm_rep_expr_temps_safe] in PreH6.
 destruct PreH6 as [_ [Hstrict _]].
 unfold cm_rtemps in Hstrict.
 int_auto.
Qed.

Lemma proof_of_cm_expr_temps_safety_wit_9_split_goal_2 : cm_expr_temps_safety_wit_9_split_goal_2.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 dump_pre_spatial.
 pose proof (cm_expr_pair_safe__expr_safety y PreH3) as Hsafe.
 unfold cm_rep_tpair_safe in Hsafe.
 int_auto.
Qed.

Lemma proof_of_cm_expr_temps_safety_wit_9 : cm_expr_temps_safety_wit_9.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_cm_expr_temps_safety_wit_9_split_goal_1.
 - Goal_apply proof_of_cm_expr_temps_safety_wit_9_split_goal_2.
Qed.

Lemma proof_of_cm_expr_temps_safety_wit_15_split_goal_1 : cm_expr_temps_safety_wit_15_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 dump_pre_spatial.
 subst e.
 cbn [cm_rep_expr_temps_safe] in PreH4.
 destruct PreH4 as [_ [Hstrict _]].
 unfold cm_rtemps in Hstrict.
 int_auto.
Qed.

Lemma proof_of_cm_expr_temps_safety_wit_15_split_goal_2 : cm_expr_temps_safety_wit_15_split_goal_2.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 dump_pre_spatial.
 pose proof (cm_expr_pair_safe__expr_safety y PreH1) as Hsafe.
 unfold cm_rep_tpair_safe in Hsafe.
 int_auto.
Qed.

Lemma proof_of_cm_expr_temps_safety_wit_15 : cm_expr_temps_safety_wit_15.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_cm_expr_temps_safety_wit_15_split_goal_1.
 - Goal_apply proof_of_cm_expr_temps_safety_wit_15_split_goal_2.
Qed.

Lemma proof_of_cm_expr_temps_safety_wit_19_split_goal_1 : cm_expr_temps_safety_wit_19_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 dump_pre_spatial.
 pose proof (cm_args_pair_safe__expr_safety eargs PreH1) as Hsafe.
 unfold cm_rep_apair_safe in Hsafe.
 int_auto.
Qed.

Lemma proof_of_cm_expr_temps_safety_wit_19_split_goal_2 : cm_expr_temps_safety_wit_19_split_goal_2.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 dump_pre_spatial.
 pose proof (cm_args_pair_safe__expr_safety eargs PreH1) as Hsafe.
 unfold cm_rep_apair_safe in Hsafe.
 int_auto.
Qed.

Lemma proof_of_cm_expr_temps_safety_wit_19 : cm_expr_temps_safety_wit_19.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_cm_expr_temps_safety_wit_19_split_goal_1.
 - Goal_apply proof_of_cm_expr_temps_safety_wit_19_split_goal_2.
Qed.

Lemma proof_of_cm_expr_temps_entail_wit_1 : cm_expr_temps_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_expr_rep_node. unfold cm_expr_node.
  Intros pa pb pargs.
  Exists pargs pb pa.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_cm_expr_temps_entail_wit_2 : cm_expr_temps_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn [cm_rep_expr_kind] in *; try discriminate.
  cbn [cm_expr_payload]. Intros_p Hargs.
  Exists pb_2 pa_2 pargs_2 e1 e2 ty.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; try reflexivity; try assumption;
      cbn [cm_rep_expr_temps_safe] in *; tauto.
Qed.

Lemma proof_of_cm_expr_temps_entail_wit_3 : cm_expr_temps_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn [cm_rep_expr_kind] in *; try discriminate.
  cbn [cm_expr_payload]. Intros_p Hargs.
  Exists pb_2 pa_2 pargs_2 op e1 e2 ty.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; try reflexivity; try assumption;
      cbn [cm_rep_expr_temps_safe] in *; tauto.
Qed.

Lemma proof_of_cm_expr_temps_entail_wit_4 : cm_expr_temps_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn [cm_rep_expr_kind] in *; try discriminate.
  Exists pargs_2 pb_2 pa_2 op e ty.
  unfold cm_expr_payload.
  Intros.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; simpl in *; tauto.
Qed.

Lemma proof_of_cm_expr_temps_entail_wit_5 : cm_expr_temps_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; simpl in PreH1; try discriminate.
  cbn [cm_expr_payload].
  Intros.
  match goal with
  | H : cm_rep_expr_temps_safe (CMIndexE ?x ?y ?t) |- _ =>
      Exists pb_2 pa_2 pargs_2 x y t
  end.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity;
      cbn [cm_rep_expr_temps_safe] in PreH6; tauto.
Qed.

Lemma proof_of_cm_expr_temps_entail_wit_6 : cm_expr_temps_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn [cm_rep_expr_kind] in *; try discriminate.
  Exists pargs_2 pb_2 pa_2 e mid ty.
  unfold cm_expr_payload.
  Intros.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; simpl in *; tauto.
Qed.

Lemma proof_of_cm_expr_temps_entail_wit_7 : cm_expr_temps_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e as [n ty|sid ty|scope slot ty|dst src ty|op a b ty|op a ty|a b ty|a mid ty|fid args ty|asked ty|ty|a ty|a ty|a ty]; cbn [cm_rep_expr_kind] in *; try discriminate.
  unfold cm_expr_payload.
  Intros.
  Exists pargs_2 pb_2 pa_2 fid args ty.
  pose proof (proj2 (proj1 (cm_expr_safe_call fid args ty) PreH8)) as Hargs.
  split_pure_spatial; [repeat cancel | split_pures; dump_pre_spatial; tauto].
Qed. 

Lemma proof_of_cm_expr_temps_entail_wit_8 : cm_expr_temps_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn [cm_rep_expr_kind] in *; try discriminate.
  Exists pargs_2 pb_2 pa_2 e ty.
  unfold cm_expr_payload.
  Intros.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; simpl in *; tauto.
Qed.

Lemma proof_of_cm_expr_temps_entail_wit_9 : cm_expr_temps_entail_wit_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn [cm_rep_expr_kind] in *; try discriminate.
  Exists pargs_2 pb_2 pa_2 e ty.
  unfold cm_expr_payload.
  Intros.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; simpl in *; tauto.
Qed.

Lemma proof_of_cm_expr_temps_entail_wit_10 : cm_expr_temps_entail_wit_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn [cm_rep_expr_kind] in *; try discriminate.
  Exists pargs_2 pb_2 pa_2 e ty.
  unfold cm_expr_payload.
  Intros.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; simpl in *; tauto.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_1_split_goal_1 : cm_expr_temps_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(subst; cbn [cm_expr_tpair cm_tleft cm_tright]; congruence).
Qed.

Lemma proof_of_cm_expr_temps_return_wit_1_split_goal_2 : cm_expr_temps_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(subst; cbn [cm_expr_tpair cm_tleft cm_tright]; congruence).
Qed.

Lemma proof_of_cm_expr_temps_return_wit_1_split_goal_spatial : cm_expr_temps_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (cm_expr_rep_node expr_pre e). unfold cm_expr_node.
  Exists pa pb pargs.
  subst e. cbn [cm_expr_payload].
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_1 : cm_expr_temps_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_temps_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_cm_expr_temps_return_wit_1_split_goal_1.
  - Goal_apply proof_of_cm_expr_temps_return_wit_1_split_goal_2.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_2_split_goal_1 : cm_expr_temps_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e. dump_pre_spatial. reflexivity.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_2_split_goal_2 : cm_expr_temps_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e. dump_pre_spatial.
  cbn [cm_rep_expr_op] in *.
  cbn [cm_expr_tpair cm_tright].
  subst op. cbn. assumption.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_2_split_goal_spatial : cm_expr_temps_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (cm_expr_rep_node expr_pre e).
  unfold cm_expr_node.
  Exists pa pb pargs.
  subst e. cbn [cm_expr_payload].
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_2 : cm_expr_temps_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_temps_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_cm_expr_temps_return_wit_2_split_goal_1.
  - Goal_apply proof_of_cm_expr_temps_return_wit_2_split_goal_2.
Qed. 

Lemma proof_of_cm_expr_temps_return_wit_3_split_goal_1 : cm_expr_temps_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e. dump_pre_spatial. reflexivity.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_3_split_goal_2 : cm_expr_temps_return_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e. dump_pre_spatial.
  cbn [cm_rep_expr_op] in *.
  cbn [cm_expr_tpair cm_tright].
  subst op. cbn. assumption.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_3_split_goal_spatial : cm_expr_temps_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (cm_expr_rep_node expr_pre e).
  unfold cm_expr_node.
  Exists pa pb pargs.
  subst e. cbn [cm_expr_payload].
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_3 : cm_expr_temps_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_temps_return_wit_3_split_goal_spatial.
  - Goal_apply proof_of_cm_expr_temps_return_wit_3_split_goal_1.
  - Goal_apply proof_of_cm_expr_temps_return_wit_3_split_goal_2.
Qed. 

Lemma proof_of_cm_expr_temps_return_wit_4_split_goal_1 : cm_expr_temps_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e. dump_pre_spatial. reflexivity.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_4_split_goal_2 : cm_expr_temps_return_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e. dump_pre_spatial.
  cbn [cm_rep_expr_op] in *.
  cbn [cm_expr_tpair cm_tright].
  assert (H0 : (Z.eqb op 0) = false) by (apply Z.eqb_neq; assumption).
  assert (H1 : (Z.eqb op 1) = false) by (apply Z.eqb_neq; assumption).
  rewrite H0, H1. cbn. assumption.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_4_split_goal_spatial : cm_expr_temps_return_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (cm_expr_rep_node expr_pre e).
  unfold cm_expr_node.
  Exists pa pb pargs.
  subst e. cbn [cm_expr_payload].
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_4 : cm_expr_temps_return_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_temps_return_wit_4_split_goal_spatial.
  - Goal_apply proof_of_cm_expr_temps_return_wit_4_split_goal_1.
  - Goal_apply proof_of_cm_expr_temps_return_wit_4_split_goal_2.
Qed. 

Lemma proof_of_cm_expr_temps_return_wit_5_split_goal_1 : cm_expr_temps_return_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  subst e. cbn [cm_rep_expr_op] in *. subst op.
  dump_pre_spatial. reflexivity.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_5_split_goal_2 : cm_expr_temps_return_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  subst e. cbn [cm_rep_expr_op] in *. subst op.
  dump_pre_spatial. reflexivity.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_5_split_goal_spatial : cm_expr_temps_return_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  subst e. rewrite (cm_expr_rep_node expr_pre _).
  unfold cm_expr_node. Exists pa pb pargs.
  cbn [cm_expr_payload].
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_5 : cm_expr_temps_return_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_temps_return_wit_5_split_goal_spatial.
  - Goal_apply proof_of_cm_expr_temps_return_wit_5_split_goal_1.
  - Goal_apply proof_of_cm_expr_temps_return_wit_5_split_goal_2.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_6_split_goal_1 : cm_expr_temps_return_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  subst e. cbn [cm_rep_expr_op] in *. subst op.
  dump_pre_spatial. reflexivity.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_6_split_goal_2 : cm_expr_temps_return_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  subst e. cbn [cm_rep_expr_op] in *. subst op.
  dump_pre_spatial. reflexivity.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_6_split_goal_spatial : cm_expr_temps_return_wit_6_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  subst e. rewrite (cm_expr_rep_node expr_pre _).
  unfold cm_expr_node. Exists pa pb pargs.
  cbn [cm_expr_payload].
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_6 : cm_expr_temps_return_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_temps_return_wit_6_split_goal_spatial.
  - Goal_apply proof_of_cm_expr_temps_return_wit_6_split_goal_1.
  - Goal_apply proof_of_cm_expr_temps_return_wit_6_split_goal_2.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_7_split_goal_1 : cm_expr_temps_return_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  subst e. cbn [cm_rep_expr_op] in *.
  dump_pre_spatial. cbn [cm_expr_tpair].
  destruct (Z.eqb op 2) eqn:H2; [apply Z.eqb_eq in H2; contradiction|].
  reflexivity.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_7_split_goal_2 : cm_expr_temps_return_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  subst e. cbn [cm_rep_expr_op] in *.
  dump_pre_spatial. cbn [cm_expr_tpair].
  destruct (Z.eqb op 2) eqn:H2; [apply Z.eqb_eq in H2; contradiction|].
  destruct (Z.eqb op 3) eqn:H3; [apply Z.eqb_eq in H3; contradiction|].
  reflexivity.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_7_split_goal_spatial : cm_expr_temps_return_wit_7_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  subst e. rewrite (cm_expr_rep_node expr_pre _).
  unfold cm_expr_node. Exists pa pb pargs.
  cbn [cm_expr_payload].
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_7 : cm_expr_temps_return_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_temps_return_wit_7_split_goal_spatial.
  - Goal_apply proof_of_cm_expr_temps_return_wit_7_split_goal_1.
  - Goal_apply proof_of_cm_expr_temps_return_wit_7_split_goal_2.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_8_split_goal_1 : cm_expr_temps_return_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(subst; cbn [cm_expr_tpair cm_tleft cm_tright]; congruence).
Qed.

Lemma proof_of_cm_expr_temps_return_wit_8_split_goal_2 : cm_expr_temps_return_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(subst; cbn [cm_expr_tpair cm_tleft cm_tright]; congruence).
Qed.

Lemma proof_of_cm_expr_temps_return_wit_8_split_goal_spatial : cm_expr_temps_return_wit_8_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (cm_expr_rep_node expr_pre e). unfold cm_expr_node.
  Exists pa pb pargs.
  subst e. cbn [cm_expr_payload].
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_8 : cm_expr_temps_return_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_temps_return_wit_8_split_goal_spatial.
  - Goal_apply proof_of_cm_expr_temps_return_wit_8_split_goal_1.
  - Goal_apply proof_of_cm_expr_temps_return_wit_8_split_goal_2.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_9_split_goal_1 : cm_expr_temps_return_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  subst e. dump_pre_spatial. reflexivity.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_9_split_goal_2 : cm_expr_temps_return_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  subst e. dump_pre_spatial. reflexivity.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_9_split_goal_spatial : cm_expr_temps_return_wit_9_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  subst e. rewrite (cm_expr_rep_node expr_pre _).
  unfold cm_expr_node. Exists pa pb pargs.
  cbn [cm_expr_payload].
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_9 : cm_expr_temps_return_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_temps_return_wit_9_split_goal_spatial.
  - Goal_apply proof_of_cm_expr_temps_return_wit_9_split_goal_1.
  - Goal_apply proof_of_cm_expr_temps_return_wit_9_split_goal_2.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_10_split_goal_1 : cm_expr_temps_return_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e. dump_pre_spatial. reflexivity.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_10_split_goal_2 : cm_expr_temps_return_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e. dump_pre_spatial. reflexivity.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_10_split_goal_spatial : cm_expr_temps_return_wit_10_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_expr_rep_node. unfold cm_expr_node.
  Exists pa pb pargs.
  subst e. unfold cm_expr_payload.
  split_pure_spatial; [repeat cancel | split_pures; dump_pre_spatial; tauto].
Qed.

Lemma proof_of_cm_expr_temps_return_wit_10 : cm_expr_temps_return_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_temps_return_wit_10_split_goal_spatial.
  - Goal_apply proof_of_cm_expr_temps_return_wit_10_split_goal_1.
  - Goal_apply proof_of_cm_expr_temps_return_wit_10_split_goal_2.
Qed. 

Lemma proof_of_cm_expr_temps_return_wit_11_split_goal_1 : cm_expr_temps_return_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(subst; simpl; lia).
Qed.

Lemma proof_of_cm_expr_temps_return_wit_11_split_goal_2 : cm_expr_temps_return_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(subst; simpl; lia).
Qed.

Lemma proof_of_cm_expr_temps_return_wit_11_split_goal_spatial : cm_expr_temps_return_wit_11_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite (cm_expr_rep_node expr_pre e).
  unfold cm_expr_node.
  Exists pa pb pargs.
  subst e.
  cbn [cm_expr_payload].
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_11 : cm_expr_temps_return_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_temps_return_wit_11_split_goal_spatial.
  - Goal_apply proof_of_cm_expr_temps_return_wit_11_split_goal_1.
  - Goal_apply proof_of_cm_expr_temps_return_wit_11_split_goal_2.
Qed. 

Lemma proof_of_cm_expr_temps_return_wit_12_split_goal_1 : cm_expr_temps_return_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(subst; simpl; lia).
Qed.

Lemma proof_of_cm_expr_temps_return_wit_12_split_goal_2 : cm_expr_temps_return_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(subst; simpl; lia).
Qed.

Lemma proof_of_cm_expr_temps_return_wit_12_split_goal_spatial : cm_expr_temps_return_wit_12_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite (cm_expr_rep_node expr_pre e).
  unfold cm_expr_node.
  Exists pa pb pargs.
  subst e.
  cbn [cm_expr_payload].
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_12 : cm_expr_temps_return_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_temps_return_wit_12_split_goal_spatial.
  - Goal_apply proof_of_cm_expr_temps_return_wit_12_split_goal_1.
  - Goal_apply proof_of_cm_expr_temps_return_wit_12_split_goal_2.
Qed. 

Lemma proof_of_cm_expr_temps_return_wit_13_split_goal_1 : cm_expr_temps_return_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(subst; simpl; lia).
Qed.

Lemma proof_of_cm_expr_temps_return_wit_13_split_goal_2 : cm_expr_temps_return_wit_13_split_goal_2.
Proof.
  LLM_pre_process ltac:(subst; simpl; lia).
Qed.

Lemma proof_of_cm_expr_temps_return_wit_13_split_goal_spatial : cm_expr_temps_return_wit_13_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite (cm_expr_rep_node expr_pre e).
  unfold cm_expr_node.
  Exists pa pb pargs.
  subst e.
  cbn [cm_expr_payload].
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_13 : cm_expr_temps_return_wit_13.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_temps_return_wit_13_split_goal_spatial.
  - Goal_apply proof_of_cm_expr_temps_return_wit_13_split_goal_1.
  - Goal_apply proof_of_cm_expr_temps_return_wit_13_split_goal_2.
Qed. 

Lemma proof_of_cm_expr_temps_return_wit_14_split_goal_1 : cm_expr_temps_return_wit_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct e; simpl in *; try discriminate; reflexivity.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_14_split_goal_2 : cm_expr_temps_return_wit_14_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct e; simpl in *; try discriminate; reflexivity.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_14_split_goal_spatial : cm_expr_temps_return_wit_14_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_expr_rep_node.
  unfold cm_expr_node.
  Exists pa pb pargs.
  split_pure_spatial.
  - repeat progress cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_14 : cm_expr_temps_return_wit_14.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_temps_return_wit_14_split_goal_spatial.
  - Goal_apply proof_of_cm_expr_temps_return_wit_14_split_goal_1.
  - Goal_apply proof_of_cm_expr_temps_return_wit_14_split_goal_2.
Qed. 

Lemma proof_of_cm_expr_temps_return_wit_15_split_goal_1 : cm_expr_temps_return_wit_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct e; simpl in *; try discriminate; reflexivity.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_15_split_goal_2 : cm_expr_temps_return_wit_15_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct e; simpl in *; try discriminate; reflexivity.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_15_split_goal_spatial : cm_expr_temps_return_wit_15_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_expr_rep_node.
  unfold cm_expr_node.
  Exists pa pb pargs.
  split_pure_spatial.
  - repeat progress cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_15 : cm_expr_temps_return_wit_15.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_temps_return_wit_15_split_goal_spatial.
  - Goal_apply proof_of_cm_expr_temps_return_wit_15_split_goal_1.
  - Goal_apply proof_of_cm_expr_temps_return_wit_15_split_goal_2.
Qed. 

Lemma proof_of_cm_expr_temps_return_wit_16_split_goal_1 : cm_expr_temps_return_wit_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct e; simpl in *; try discriminate; reflexivity.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_16_split_goal_2 : cm_expr_temps_return_wit_16_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct e; simpl in *; try discriminate; reflexivity.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_16_split_goal_spatial : cm_expr_temps_return_wit_16_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_expr_rep_node.
  unfold cm_expr_node.
  Exists pa pb pargs.
  split_pure_spatial.
  - repeat progress cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_16 : cm_expr_temps_return_wit_16.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_temps_return_wit_16_split_goal_spatial.
  - Goal_apply proof_of_cm_expr_temps_return_wit_16_split_goal_1.
  - Goal_apply proof_of_cm_expr_temps_return_wit_16_split_goal_2.
Qed. 

Lemma proof_of_cm_expr_temps_return_wit_17_split_goal_1 : cm_expr_temps_return_wit_17_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct e; cbn [cm_rep_expr_kind] in *; try discriminate; reflexivity.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_17_split_goal_2 : cm_expr_temps_return_wit_17_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct e; cbn [cm_rep_expr_kind] in *; try discriminate; reflexivity.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_17_split_goal_spatial : cm_expr_temps_return_wit_17_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_expr_rep_node. unfold cm_expr_node.
  Exists pa pb pargs.
  split_pure_spatial.
  - sepcon_right_assoc. cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_17 : cm_expr_temps_return_wit_17.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_temps_return_wit_17_split_goal_spatial.
  - Goal_apply proof_of_cm_expr_temps_return_wit_17_split_goal_1.
  - Goal_apply proof_of_cm_expr_temps_return_wit_17_split_goal_2.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_18_split_goal_1 : cm_expr_temps_return_wit_18_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct e; cbn [cm_rep_expr_kind] in *; try discriminate; reflexivity.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_18_split_goal_2 : cm_expr_temps_return_wit_18_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct e; cbn [cm_rep_expr_kind] in *; try discriminate; reflexivity.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_18_split_goal_spatial : cm_expr_temps_return_wit_18_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_expr_rep_node. unfold cm_expr_node.
  Exists pa pb pargs.
  split_pure_spatial.
  - sepcon_right_assoc. cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_18 : cm_expr_temps_return_wit_18.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_temps_return_wit_18_split_goal_spatial.
  - Goal_apply proof_of_cm_expr_temps_return_wit_18_split_goal_1.
  - Goal_apply proof_of_cm_expr_temps_return_wit_18_split_goal_2.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_19_split_goal_1 : cm_expr_temps_return_wit_19_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn [cm_rep_expr_kind] in *; contradiction.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_19_split_goal_2 : cm_expr_temps_return_wit_19_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn [cm_rep_expr_kind] in *; contradiction.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_19_split_goal_spatial : cm_expr_temps_return_wit_19_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn [cm_rep_expr_kind] in *; contradiction.
Qed.

Lemma proof_of_cm_expr_temps_return_wit_19 : cm_expr_temps_return_wit_19.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_expr_temps_return_wit_19_split_goal_spatial.
  - Goal_apply proof_of_cm_expr_temps_return_wit_19_split_goal_1.
  - Goal_apply proof_of_cm_expr_temps_return_wit_19_split_goal_2.
Qed.

Lemma proof_of_cmc_stmt_temps_entail_wit_1 : cmc_stmt_temps_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_stmt_rep_node. unfold cm_stmt_node.
  Intros pe pa pb.
  Exists pb pa pe.
  split_pure_spatial; [repeat progress cancel | split_pures; dump_pre_spatial; assumption].
Qed.

Lemma proof_of_cmc_stmt_temps_entail_wit_2 : cmc_stmt_temps_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct s as [|x|slot|slot x|a b|a|x a b|x a| | |x];
    cbn [cm_rep_stmt_kind] in *; try discriminate.
  cbn [cm_stmt_payload]. Intros_p Hp.
  Exists pb_2 pa_2 pe_2 x.
  split_pure_spatial; [repeat progress cancel | split_pures; dump_pre_spatial; auto; try tauto].
  exact (proj2 PreH3).
Qed.

Lemma proof_of_cmc_stmt_temps_entail_wit_3 : cmc_stmt_temps_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct s as [|x|slot|slot x|a b|a|x a b|x a| | |x];
    cbn [cm_rep_stmt_kind] in *; try discriminate.
  cbn [cm_stmt_payload]. Intros_p Hp.
  Exists pb_2 pa_2 pe_2 slot x.
  split_pure_spatial; [repeat progress cancel | split_pures; dump_pre_spatial; auto; try tauto].
  exact (proj2 PreH4).
Qed.

Lemma proof_of_cmc_stmt_temps_entail_wit_4 : cmc_stmt_temps_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct s as [|x|slot|slot x|a b|a|x a b|x a| | |x];
    cbn [cm_rep_stmt_kind] in *; try discriminate.
  cbn [cm_stmt_payload]. Intros_p Hp.
  Exists pb_2 pa_2 pe_2 x.
  split_pure_spatial; [repeat progress cancel | split_pures; dump_pre_spatial; auto; try tauto].
  exact (proj2 PreH5).
Qed.

Lemma proof_of_cmc_stmt_temps_entail_wit_5 : cmc_stmt_temps_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct s as [ | e | n | n e | a b | a | e a b | e a | | | e ];
    cbn [cm_rep_stmt_kind] in *; try discriminate.
  cbn [cm_stmt_payload].
  Intros_p Hpayload.
  Exists pb_2 pa_2 pe_2 a b.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial;
      unfold cm_rep_stmt_temps_safe in *;
      cbn [cm_rep_stmt_children_safe] in *; intuition.
Qed.

Lemma proof_of_cmc_stmt_temps_entail_wit_6 : cmc_stmt_temps_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct s as [ | e | n | n e | a b | a | e a b | e a | | | e ];
    cbn [cm_rep_stmt_kind] in *; try discriminate.
  cbn [cm_stmt_payload].
  Intros_p Hpayload.
  Exists pb_2 pa_2 pe_2 a.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial;
      unfold cm_rep_stmt_temps_safe in *;
      cbn [cm_rep_stmt_children_safe] in *; intuition.
Qed.

Lemma proof_of_cmc_stmt_temps_entail_wit_7 : cmc_stmt_temps_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct s as [ | e | n | n e | a b | a | e a b | e a | | | e ];
    cbn [cm_rep_stmt_kind] in *; try discriminate.
  cbn [cm_stmt_payload].
  Exists pb_2 pa_2 pe_2 e a b.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial;
      unfold cm_rep_stmt_temps_safe in *;
      cbn [cm_rep_stmt_children_safe] in *; intuition.
Qed.

Lemma proof_of_cmc_stmt_temps_entail_wit_8 : cmc_stmt_temps_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct s as [ | e | n | n e | a b | a | e a b | e a | | | e ];
    cbn [cm_rep_stmt_kind] in *; try discriminate.
  cbn [cm_stmt_payload].
  Intros_p Hpayload.
  Exists pb_2 pa_2 pe_2 e a.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial;
      unfold cm_rep_stmt_temps_safe in *;
      cbn [cm_rep_stmt_children_safe] in *; intuition.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_1_split_goal_1 : cmc_stmt_temps_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold cm_rep_stmt_temps_safe in *; lia).
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_1_split_goal_2 : cmc_stmt_temps_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(unfold cm_rep_stmt_temps_safe in *; lia).
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_1_split_goal_3 : cmc_stmt_temps_return_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(subst; reflexivity).
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_1_split_goal_spatial : cmc_stmt_temps_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst s.
  rewrite cm_stmt_rep_node.
  unfold cm_stmt_node.
  Exists pe pa pb.
  cbn [cm_stmt_payload].
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_1 : cmc_stmt_temps_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_1_split_goal_1.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_1_split_goal_2.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_1_split_goal_3.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_2_split_goal_1 : cmc_stmt_temps_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold cm_rep_stmt_temps_safe in *; lia).
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_2_split_goal_2 : cmc_stmt_temps_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(unfold cm_rep_stmt_temps_safe in *; lia).
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_2_split_goal_3 : cmc_stmt_temps_return_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(subst; reflexivity).
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_2_split_goal_spatial : cmc_stmt_temps_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst s.
  rewrite cm_stmt_rep_node.
  unfold cm_stmt_node.
  Exists pe pa pb.
  cbn [cm_stmt_payload].
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_2 : cmc_stmt_temps_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_2_split_goal_1.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_2_split_goal_2.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_2_split_goal_3.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_3_split_goal_1 : cmc_stmt_temps_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold cm_rep_stmt_temps_safe in *; lia).
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_3_split_goal_2 : cmc_stmt_temps_return_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(unfold cm_rep_stmt_temps_safe in *; lia).
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_3_split_goal_3 : cmc_stmt_temps_return_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(subst; reflexivity).
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_3_split_goal_spatial : cmc_stmt_temps_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst s.
  rewrite cm_stmt_rep_node.
  unfold cm_stmt_node.
  Exists pe pa pb.
  cbn [cm_stmt_payload].
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_3 : cmc_stmt_temps_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_3_split_goal_spatial.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_3_split_goal_1.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_3_split_goal_2.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_3_split_goal_3.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_4_split_goal_1 : cmc_stmt_temps_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  all: dump_pre_spatial; unfold cm_rep_stmt_temps_safe in *; lia.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_4_split_goal_2 : cmc_stmt_temps_return_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(unfold cm_rep_stmt_temps_safe in *; lia).
  all: dump_pre_spatial; unfold cm_rep_stmt_temps_safe in *; lia.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_4_split_goal_3 : cmc_stmt_temps_return_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(subst; reflexivity).
  all: dump_pre_spatial; subst; reflexivity.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_4_split_goal_spatial : cmc_stmt_temps_return_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite (cm_stmt_rep_node stmt_pre s). unfold cm_stmt_node.
  Exists pe pa pb.
  subst s. cbn [cm_stmt_payload].
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_4 : cmc_stmt_temps_return_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_4_split_goal_spatial.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_4_split_goal_1.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_4_split_goal_2.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_4_split_goal_3.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_5_split_goal_1 : cmc_stmt_temps_return_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  all: dump_pre_spatial; unfold cm_rep_stmt_temps_safe in *; lia.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_5_split_goal_2 : cmc_stmt_temps_return_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(unfold cm_rep_stmt_temps_safe in *; lia).
  all: dump_pre_spatial; unfold cm_rep_stmt_temps_safe in *; lia.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_5_split_goal_3 : cmc_stmt_temps_return_wit_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(subst; reflexivity).
  all: dump_pre_spatial; subst; reflexivity.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_5_split_goal_spatial : cmc_stmt_temps_return_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite (cm_stmt_rep_node stmt_pre s). unfold cm_stmt_node.
  Exists pe pa pb.
  subst s. cbn [cm_stmt_payload].
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_5 : cmc_stmt_temps_return_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_5_split_goal_spatial.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_5_split_goal_1.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_5_split_goal_2.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_5_split_goal_3.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_6_split_goal_1 : cmc_stmt_temps_return_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  all: dump_pre_spatial; unfold cm_rep_stmt_temps_safe in *; lia.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_6_split_goal_2 : cmc_stmt_temps_return_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(unfold cm_rep_stmt_temps_safe in *; lia).
  all: dump_pre_spatial; unfold cm_rep_stmt_temps_safe in *; lia.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_6_split_goal_3 : cmc_stmt_temps_return_wit_6_split_goal_3.
Proof.
  LLM_pre_process ltac:(subst; reflexivity).
  all: dump_pre_spatial; subst; reflexivity.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_6_split_goal_spatial : cmc_stmt_temps_return_wit_6_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite (cm_stmt_rep_node stmt_pre s). unfold cm_stmt_node.
  Exists pe pa pb.
  subst s. cbn [cm_stmt_payload].
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_6 : cmc_stmt_temps_return_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_6_split_goal_spatial.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_6_split_goal_1.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_6_split_goal_2.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_6_split_goal_3.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_7_split_goal_1 : cmc_stmt_temps_return_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  all: dump_pre_spatial; unfold cm_rep_stmt_temps_safe in *; lia.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_7_split_goal_2 : cmc_stmt_temps_return_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(unfold cm_rep_stmt_temps_safe in *; lia).
  all: dump_pre_spatial; unfold cm_rep_stmt_temps_safe in *; lia.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_7_split_goal_3 : cmc_stmt_temps_return_wit_7_split_goal_3.
Proof.
  LLM_pre_process ltac:(subst; reflexivity).
  all: dump_pre_spatial; subst; reflexivity.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_7_split_goal_spatial : cmc_stmt_temps_return_wit_7_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite (cm_stmt_rep_node stmt_pre s). unfold cm_stmt_node.
  Exists pe pa pb.
  subst s. cbn [cm_stmt_payload].
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_7 : cmc_stmt_temps_return_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_7_split_goal_spatial.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_7_split_goal_1.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_7_split_goal_2.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_7_split_goal_3.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_8_split_goal_1 : cmc_stmt_temps_return_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial. unfold cm_rep_stmt_temps_safe in *; lia.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_8_split_goal_2 : cmc_stmt_temps_return_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial. unfold cm_rep_stmt_temps_safe in *; lia.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_8_split_goal_3 : cmc_stmt_temps_return_wit_8_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial. destruct s; simpl in *; lia.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_8_split_goal_spatial : cmc_stmt_temps_return_wit_8_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite cm_stmt_rep_node. unfold cm_stmt_node.
  Exists pe pa pb.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_8 : cmc_stmt_temps_return_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_8_split_goal_spatial.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_8_split_goal_1.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_8_split_goal_2.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_8_split_goal_3.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_9_split_goal_1 : cmc_stmt_temps_return_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial. unfold cm_rep_stmt_temps_safe in *; lia.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_9_split_goal_2 : cmc_stmt_temps_return_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial. unfold cm_rep_stmt_temps_safe in *; lia.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_9_split_goal_3 : cmc_stmt_temps_return_wit_9_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial. destruct s; simpl in *; lia.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_9_split_goal_spatial : cmc_stmt_temps_return_wit_9_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite cm_stmt_rep_node. unfold cm_stmt_node.
  Exists pe pa pb.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_9 : cmc_stmt_temps_return_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_9_split_goal_spatial.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_9_split_goal_1.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_9_split_goal_2.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_9_split_goal_3.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_10_split_goal_1 : cmc_stmt_temps_return_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial. unfold cm_rep_stmt_temps_safe in *; lia.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_10_split_goal_2 : cmc_stmt_temps_return_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial. unfold cm_rep_stmt_temps_safe in *; lia.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_10_split_goal_3 : cmc_stmt_temps_return_wit_10_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial. destruct s; simpl in *; lia.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_10_split_goal_spatial : cmc_stmt_temps_return_wit_10_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite cm_stmt_rep_node. unfold cm_stmt_node.
  Exists pe pa pb.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_10 : cmc_stmt_temps_return_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_10_split_goal_spatial.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_10_split_goal_1.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_10_split_goal_2.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_10_split_goal_3.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_11_split_goal_1 : cmc_stmt_temps_return_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial. unfold cm_rep_stmt_temps_safe in *; lia.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_11_split_goal_2 : cmc_stmt_temps_return_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial. unfold cm_rep_stmt_temps_safe in *; lia.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_11_split_goal_3 : cmc_stmt_temps_return_wit_11_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial. destruct s; simpl in *; lia.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_11_split_goal_spatial : cmc_stmt_temps_return_wit_11_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite cm_stmt_rep_node. unfold cm_stmt_node.
  Exists pe pa pb.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_11 : cmc_stmt_temps_return_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_11_split_goal_spatial.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_11_split_goal_1.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_11_split_goal_2.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_11_split_goal_3.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_12_split_goal_1 : cmc_stmt_temps_return_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial. unfold cm_rep_stmt_temps_safe in *; lia.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_12_split_goal_2 : cmc_stmt_temps_return_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial. unfold cm_rep_stmt_temps_safe in *; lia.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_12_split_goal_3 : cmc_stmt_temps_return_wit_12_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial. destruct s; simpl in *; lia.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_12_split_goal_spatial : cmc_stmt_temps_return_wit_12_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia).
  rewrite cm_stmt_rep_node. unfold cm_stmt_node.
  Exists pe pa pb.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cmc_stmt_temps_return_wit_12 : cmc_stmt_temps_return_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_12_split_goal_spatial.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_12_split_goal_1.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_12_split_goal_2.
  - Goal_apply proof_of_cmc_stmt_temps_return_wit_12_split_goal_3.
Qed.

Lemma proof_of_cm_normalize_count_return_wit_1_split_goal_1 : cm_normalize_count_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_cm_normalize_count_return_wit_1 : cm_normalize_count_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_normalize_count_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_cm_normalize_count_return_wit_2_split_goal_1 : cm_normalize_count_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold cm_normalize_code_value.
  destruct (Z.eqb_spec ty_pre 1); [lia | reflexivity].
Qed.

Lemma proof_of_cm_normalize_count_return_wit_2 : cm_normalize_count_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_normalize_count_return_wit_2_split_goal_1.
Qed.

