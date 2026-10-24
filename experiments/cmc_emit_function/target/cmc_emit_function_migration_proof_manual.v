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
From SimpleC.EE.QCP_demos_human Require Import cmc_emit_function_migration_goal.
From SimpleC.EE.QCP_demos_human Require Import cmc_emit_function_migration_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.cmc_emit_function_migration_lib.
Local Open Scope sac.

Lemma proof_of_cmc_emit_param_stores_from_return_wit_1_split_goal_spatial : cmc_emit_param_stores_from_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct params as [| h t].
  - cbn [cm_emit_param_stores app]. rewrite app_nil_r. cancel.
  - cbn [cm_slot_list_rep]. Intros np. contradiction.
Qed.

Lemma proof_of_cmc_emit_param_stores_from_return_wit_1 : cmc_emit_param_stores_from_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_param_stores_from_return_wit_1_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_param_stores_from_return_wit_2_split_goal_1 : cmc_emit_param_stores_from_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || assumption || reflexivity).
  all: try dump_pre_spatial.
  all: destruct params as [|h t];
    cbn [cm_emit_params_head cm_emit_params_tail cm_slot_at Z.to_nat nth tl] in *;
    first [discriminate | assumption | reflexivity | lia].
Qed.

Lemma proof_of_cmc_emit_param_stores_from_return_wit_2_split_goal_2 : cmc_emit_param_stores_from_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || assumption || reflexivity).
  all: try dump_pre_spatial.
  all: destruct params as [|h t];
    cbn [cm_emit_params_head cm_emit_params_tail cm_slot_at Z.to_nat nth tl] in *;
    first [discriminate | assumption | reflexivity | lia].
Qed.

Lemma proof_of_cmc_emit_param_stores_from_return_wit_2_split_goal_3 : cmc_emit_param_stores_from_return_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || assumption || reflexivity).
  all: try dump_pre_spatial.
  all: destruct params as [|h t];
    cbn [cm_emit_params_head cm_emit_params_tail cm_slot_at Z.to_nat nth tl] in *;
    first [discriminate | assumption | reflexivity | lia].
Qed.

Lemma proof_of_cmc_emit_param_stores_from_return_wit_2_split_goal_4 : cmc_emit_param_stores_from_return_wit_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || assumption || reflexivity).
  all: try dump_pre_spatial.
  all: destruct params as [|h t];
    cbn [cm_emit_params_head cm_emit_params_tail cm_slot_at Z.to_nat nth tl] in *;
    first [discriminate | assumption | reflexivity | lia].
Qed.

Lemma proof_of_cmc_emit_param_stores_from_return_wit_2_split_goal_5 : cmc_emit_param_stores_from_return_wit_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || assumption || reflexivity).
  all: try dump_pre_spatial.
  all: destruct params as [|h t];
    cbn [cm_emit_params_head cm_emit_params_tail cm_slot_at Z.to_nat nth tl] in *;
    first [discriminate | assumption | reflexivity | lia].
Qed.

Lemma proof_of_cmc_emit_param_stores_from_return_wit_2 : cmc_emit_param_stores_from_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_param_stores_from_return_wit_2_split_goal_1.
  - Goal_apply proof_of_cmc_emit_param_stores_from_return_wit_2_split_goal_2.
  - Goal_apply proof_of_cmc_emit_param_stores_from_return_wit_2_split_goal_3.
  - Goal_apply proof_of_cmc_emit_param_stores_from_return_wit_2_split_goal_4.
  - Goal_apply proof_of_cmc_emit_param_stores_from_return_wit_2_split_goal_5.
Qed. 

Lemma proof_of_cmc_emit_param_stores_from_partial_solve_wit_5_pure_split_goal_1 : cmc_emit_param_stores_from_partial_solve_wit_5_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || assumption || reflexivity).
  all: try dump_pre_spatial.
  all: destruct params as [|h t];
    cbn [cm_emit_params_head cm_emit_params_tail cm_slot_at Z.to_nat nth tl] in *;
    first [discriminate | assumption | reflexivity | lia].
Qed.

Lemma proof_of_cmc_emit_param_stores_from_partial_solve_wit_5_pure_split_goal_2 : cmc_emit_param_stores_from_partial_solve_wit_5_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || assumption || reflexivity).
  all: try dump_pre_spatial.
  all: destruct params as [|h t];
    cbn [cm_emit_params_head cm_emit_params_tail cm_slot_at Z.to_nat nth tl] in *;
    first [discriminate | assumption | reflexivity | lia].
Qed.

Lemma proof_of_cmc_emit_param_stores_from_partial_solve_wit_5_pure_split_goal_3 : cmc_emit_param_stores_from_partial_solve_wit_5_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || assumption || reflexivity).
  all: try dump_pre_spatial.
  all: destruct params as [|h t];
    cbn [cm_emit_params_head cm_emit_params_tail cm_slot_at Z.to_nat nth tl] in *;
    first [discriminate | assumption | reflexivity | lia].
Qed.

Lemma proof_of_cmc_emit_param_stores_from_partial_solve_wit_5_pure_split_goal_4 : cmc_emit_param_stores_from_partial_solve_wit_5_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || assumption || reflexivity).
  all: try dump_pre_spatial.
  all: destruct params as [|h t];
    cbn [cm_emit_params_head cm_emit_params_tail cm_slot_at Z.to_nat nth tl] in *;
    first [discriminate | assumption | reflexivity | lia].
Qed.

Lemma proof_of_cmc_emit_param_stores_from_partial_solve_wit_5_pure_split_goal_5 : cmc_emit_param_stores_from_partial_solve_wit_5_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || assumption || reflexivity).
  all: try dump_pre_spatial.
  all: destruct params as [|h t];
    cbn [cm_emit_params_head cm_emit_params_tail cm_slot_at Z.to_nat nth tl] in *;
    first [discriminate | assumption | reflexivity | lia].
Qed.

Lemma proof_of_cmc_emit_param_stores_from_partial_solve_wit_5_pure : cmc_emit_param_stores_from_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_param_stores_from_partial_solve_wit_5_pure_split_goal_1.
  - Goal_apply proof_of_cmc_emit_param_stores_from_partial_solve_wit_5_pure_split_goal_2.
  - Goal_apply proof_of_cmc_emit_param_stores_from_partial_solve_wit_5_pure_split_goal_3.
  - Goal_apply proof_of_cmc_emit_param_stores_from_partial_solve_wit_5_pure_split_goal_4.
  - Goal_apply proof_of_cmc_emit_param_stores_from_partial_solve_wit_5_pure_split_goal_5.
Qed. 

Lemma proof_of_cmc_emit_param_stores_from_partial_solve_wit_6_pure_split_goal_1 : cmc_emit_param_stores_from_partial_solve_wit_6_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || assumption || reflexivity).
  all: try dump_pre_spatial.
  all: destruct params as [|h t];
    cbn [cm_emit_params_head cm_emit_params_tail cm_slot_at Z.to_nat nth tl] in *;
    first [discriminate | assumption | reflexivity | lia].
Qed.

Lemma proof_of_cmc_emit_param_stores_from_partial_solve_wit_6_pure_split_goal_2 : cmc_emit_param_stores_from_partial_solve_wit_6_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || assumption || reflexivity).
  all: try dump_pre_spatial.
  all: destruct params as [|h t];
    cbn [cm_emit_params_head cm_emit_params_tail cm_slot_at Z.to_nat nth tl] in *;
    first [discriminate | assumption | reflexivity | lia].
Qed.

Lemma proof_of_cmc_emit_param_stores_from_partial_solve_wit_6_pure_split_goal_3 : cmc_emit_param_stores_from_partial_solve_wit_6_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || assumption || reflexivity).
  all: try dump_pre_spatial.
  all: destruct params as [|h t];
    cbn [cm_emit_params_head cm_emit_params_tail cm_slot_at Z.to_nat nth tl] in *;
    first [discriminate | assumption | reflexivity | lia].
Qed.

Lemma proof_of_cmc_emit_param_stores_from_partial_solve_wit_6_pure : cmc_emit_param_stores_from_partial_solve_wit_6_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_param_stores_from_partial_solve_wit_6_pure_split_goal_1.
  - Goal_apply proof_of_cmc_emit_param_stores_from_partial_solve_wit_6_pure_split_goal_2.
  - Goal_apply proof_of_cmc_emit_param_stores_from_partial_solve_wit_6_pure_split_goal_3.
Qed. 

Lemma proof_of_cmc_emit_param_stores_from_partial_solve_wit_10_pure_split_goal_1 : cmc_emit_param_stores_from_partial_solve_wit_10_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || assumption || reflexivity).
  all: try dump_pre_spatial.
  all: destruct params as [|h t];
    cbn [cm_emit_params_head cm_emit_params_tail cm_slot_at Z.to_nat nth tl] in *;
    first [discriminate | assumption | reflexivity | lia].
Qed.

Lemma proof_of_cmc_emit_param_stores_from_partial_solve_wit_10_pure_split_goal_2 : cmc_emit_param_stores_from_partial_solve_wit_10_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || assumption || reflexivity).
  all: try dump_pre_spatial.
  all: destruct params as [|h t];
    cbn [cm_emit_params_head cm_emit_params_tail cm_slot_at Z.to_nat nth tl] in *;
    first [discriminate | assumption | reflexivity | lia].
Qed.

Lemma proof_of_cmc_emit_param_stores_from_partial_solve_wit_10_pure_split_goal_3 : cmc_emit_param_stores_from_partial_solve_wit_10_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || assumption || reflexivity).
  all: try dump_pre_spatial.
  all: destruct params as [|h t];
    cbn [cm_emit_params_head cm_emit_params_tail cm_slot_at Z.to_nat nth tl] in *;
    first [discriminate | assumption | reflexivity | lia].
Qed.

Lemma proof_of_cmc_emit_param_stores_from_partial_solve_wit_10_pure_split_goal_4 : cmc_emit_param_stores_from_partial_solve_wit_10_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || assumption || reflexivity).
  all: try dump_pre_spatial.
  all: destruct params as [|h t];
    cbn [cm_emit_params_head cm_emit_params_tail cm_slot_at Z.to_nat nth tl] in *;
    first [discriminate | assumption | reflexivity | lia].
Qed.

Lemma proof_of_cmc_emit_param_stores_from_partial_solve_wit_10_pure_split_goal_5 : cmc_emit_param_stores_from_partial_solve_wit_10_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || assumption || reflexivity).
  all: try dump_pre_spatial.
  all: destruct params as [|h t];
    cbn [cm_emit_params_head cm_emit_params_tail cm_slot_at Z.to_nat nth tl] in *;
    first [discriminate | assumption | reflexivity | lia].
Qed.

Lemma proof_of_cmc_emit_param_stores_from_partial_solve_wit_10_pure_split_goal_6 : cmc_emit_param_stores_from_partial_solve_wit_10_pure_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || assumption || reflexivity).
  all: try dump_pre_spatial.
  all: destruct params as [|h t];
    cbn [cm_emit_params_head cm_emit_params_tail cm_slot_at Z.to_nat nth tl] in *;
    first [discriminate | assumption | reflexivity | lia].
Qed.

Lemma proof_of_cmc_emit_param_stores_from_partial_solve_wit_10_pure : cmc_emit_param_stores_from_partial_solve_wit_10_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_param_stores_from_partial_solve_wit_10_pure_split_goal_1.
  - Goal_apply proof_of_cmc_emit_param_stores_from_partial_solve_wit_10_pure_split_goal_2.
  - Goal_apply proof_of_cmc_emit_param_stores_from_partial_solve_wit_10_pure_split_goal_3.
  - Goal_apply proof_of_cmc_emit_param_stores_from_partial_solve_wit_10_pure_split_goal_4.
  - Goal_apply proof_of_cmc_emit_param_stores_from_partial_solve_wit_10_pure_split_goal_5.
  - Goal_apply proof_of_cmc_emit_param_stores_from_partial_solve_wit_10_pure_split_goal_6.
Qed. 

Lemma proof_of_cmc_emit_param_stores_from_partial_solve_wit_11_pure_split_goal_1 : cmc_emit_param_stores_from_partial_solve_wit_11_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || assumption || reflexivity).
  all: try dump_pre_spatial.
  all: destruct params as [|h t];
    cbn [cm_emit_params_head cm_emit_params_tail cm_slot_at Z.to_nat nth tl] in *;
    first [discriminate | assumption | reflexivity | lia].
Qed.

Lemma proof_of_cmc_emit_param_stores_from_partial_solve_wit_11_pure : cmc_emit_param_stores_from_partial_solve_wit_11_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_param_stores_from_partial_solve_wit_11_pure_split_goal_1.
Qed. 

Lemma proof_of_cmc_emit_param_stores_from_which_implies_wit_1 : cmc_emit_param_stores_from_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct params as [| h t].
  - cbn [cm_slot_list_rep]. Intros_p Hzero. contradiction.
  - cbn [cm_slot_list_rep cm_emit_params_head cm_slot_at cm_emit_params_tail].
    Intros np. Exists np.
    unfold cm_emit_params_head, cm_emit_params_tail, cm_slot_at. cbn [Z.to_nat nth tl].
    split_pure_spatial.
    + cancel (&(param # "cm_slot" ->ₛ "ty") # Int |-> cm_type_encode (cm_slot_ty h)).
      cancel (&(param # "cm_slot" ->ₛ "count") # Int |-> cm_slot_count h).
      cancel (&(param # "cm_slot" ->ₛ "next") # Ptr |-> np).
      cancel.
    + split_pures; dump_pre_spatial; auto.
Qed. 

Lemma proof_of_cmc_emit_param_stores_from_which_implies_wit_2_split_goal_1 : cmc_emit_param_stores_from_which_implies_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hhead : cm_slot_wf structs (cm_emit_params_head params)).
  { apply (PreH2 0). rewrite PreH1 at 1. rewrite Zlength_cons.
    pose proof (Zlength_nonneg (cm_emit_params_tail params)). lia. }
  rewrite PreH3. change (cm_rep_member_size (cm_emit_params_head params) = cm_slot_size structs (cm_emit_params_head params)).
  apply cm_slot_size_matches__temp_context. exact Hhead.
Qed.

Lemma proof_of_cmc_emit_param_stores_from_which_implies_wit_2 : cmc_emit_param_stores_from_which_implies_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_param_stores_from_which_implies_wit_2_split_goal_1.
Qed. 

Lemma proof_of_cmc_emit_param_stores_from_which_implies_wit_3_split_goal_1 : cmc_emit_param_stores_from_which_implies_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH14 in PreH13 at 1.
  cbn [cm_param_counts_representable] in PreH13. tauto.
Qed.

Lemma proof_of_cmc_emit_param_stores_from_which_implies_wit_3_split_goal_2 : cmc_emit_param_stores_from_which_implies_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH14 in PreH13 at 1.
  cbn [cm_param_counts_representable] in PreH13. tauto.
Qed.

Lemma proof_of_cmc_emit_param_stores_from_which_implies_wit_3_split_goal_3 : cmc_emit_param_stores_from_which_implies_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH14 in PreH12 at 1.
  cbn [cm_rep_members_safe] in PreH12. tauto.
Qed.

Lemma proof_of_cmc_emit_param_stores_from_which_implies_wit_3_split_goal_4 : cmc_emit_param_stores_from_which_implies_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Htail : cm_slots_wf structs (cm_emit_params_tail params)).
  { intros i Hi. pose proof PreH11 as Hwf. rewrite PreH14 in Hwf at 1.
    specialize (Hwf (i+1)).
    assert (Hb : 0 <= i+1 < Zlength (cm_emit_params_head params :: cm_emit_params_tail params))
      by (rewrite Zlength_cons; lia).
    specialize (Hwf Hb). unfold cm_slot_at in Hwf |- *.
    replace (i+1) with (Z.succ i) in Hwf by lia.
    rewrite Z2Nat.inj_succ in Hwf by lia. exact Hwf. }
  exact Htail.
Qed.

Lemma proof_of_cmc_emit_param_stores_from_which_implies_wit_3_split_goal_5 : cmc_emit_param_stores_from_which_implies_wit_3_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH14 in PreH10 at 1. cbn [cm_slots_size] in PreH10. lia.
Qed.

Lemma proof_of_cmc_emit_param_stores_from_which_implies_wit_3_split_goal_6 : cmc_emit_param_stores_from_which_implies_wit_3_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Htail : cm_slots_wf structs (cm_emit_params_tail params)).
  { intros i Hi. pose proof PreH11 as Hwf. rewrite PreH14 in Hwf at 1.
    specialize (Hwf (i+1)).
    assert (Hb : 0 <= i+1 < Zlength (cm_emit_params_head params :: cm_emit_params_tail params))
      by (rewrite Zlength_cons; lia).
    specialize (Hwf Hb). unfold cm_slot_at in Hwf |- *.
    replace (i+1) with (Z.succ i) in Hwf by lia.
    rewrite Z2Nat.inj_succ in Hwf by lia. exact Hwf. }
  pose proof (cm_slots_size_nonnegative__call_bounds structs _ Htail).
  rewrite PreH14 in PreH10 at 1. cbn [cm_slots_size] in PreH10. lia.
Qed.

Lemma proof_of_cmc_emit_param_stores_from_which_implies_wit_3_split_goal_7 : cmc_emit_param_stores_from_which_implies_wit_3_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hhead : cm_slot_wf structs (cm_emit_params_head params)).
  { apply (PreH11 0). rewrite PreH14 at 1. rewrite Zlength_cons.
    pose proof (Zlength_nonneg (cm_emit_params_tail params)). lia. }
  unfold cm_slot_wf in Hhead. lia.
Qed.

Lemma proof_of_cmc_emit_param_stores_from_which_implies_wit_3_split_goal_8 : cmc_emit_param_stores_from_which_implies_wit_3_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH14 in PreH8 at 1. rewrite Zlength_cons in PreH8. lia.
Qed.

Lemma proof_of_cmc_emit_param_stores_from_which_implies_wit_3_split_goal_9 : cmc_emit_param_stores_from_which_implies_wit_3_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH14 in PreH8 at 1. rewrite Zlength_cons in PreH8.
  pose proof (Zlength_nonneg (cm_emit_params_tail params)). lia.
Qed.

Lemma proof_of_cmc_emit_param_stores_from_which_implies_wit_3_split_goal_10 : cmc_emit_param_stores_from_which_implies_wit_3_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_function_slots_size_snoc__param_transition. lia.
Qed.

Lemma proof_of_cmc_emit_param_stores_from_which_implies_wit_3_split_goal_11 : cmc_emit_param_stores_from_which_implies_wit_3_split_goal_11.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_cmc_emit_param_stores_from_which_implies_wit_3_split_goal_12 : cmc_emit_param_stores_from_which_implies_wit_3_split_goal_12.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite <- app_assoc. cbn [app]. rewrite <- PreH14. exact PreH4.
Qed.

Lemma proof_of_cmc_emit_param_stores_from_which_implies_wit_3 : cmc_emit_param_stores_from_which_implies_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_param_stores_from_which_implies_wit_3_split_goal_1.
  - Goal_apply proof_of_cmc_emit_param_stores_from_which_implies_wit_3_split_goal_2.
  - Goal_apply proof_of_cmc_emit_param_stores_from_which_implies_wit_3_split_goal_3.
  - Goal_apply proof_of_cmc_emit_param_stores_from_which_implies_wit_3_split_goal_4.
  - Goal_apply proof_of_cmc_emit_param_stores_from_which_implies_wit_3_split_goal_5.
  - Goal_apply proof_of_cmc_emit_param_stores_from_which_implies_wit_3_split_goal_6.
  - Goal_apply proof_of_cmc_emit_param_stores_from_which_implies_wit_3_split_goal_7.
  - Goal_apply proof_of_cmc_emit_param_stores_from_which_implies_wit_3_split_goal_8.
  - Goal_apply proof_of_cmc_emit_param_stores_from_which_implies_wit_3_split_goal_9.
  - Goal_apply proof_of_cmc_emit_param_stores_from_which_implies_wit_3_split_goal_10.
  - Goal_apply proof_of_cmc_emit_param_stores_from_which_implies_wit_3_split_goal_11.
  - Goal_apply proof_of_cmc_emit_param_stores_from_which_implies_wit_3_split_goal_12.
Qed. 

Lemma proof_of_cmc_emit_param_stores_from_which_implies_wit_4_split_goal_spatial : cmc_emit_param_stores_from_which_implies_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hoffset : cm_param_offset policy p fid slot_pre = offset_pre).
  { unfold cm_param_offset. rewrite <- PreH2, <- PreH3, PreH4, PreH5, <- PreH1.
    rewrite cm_function_slots_prefix_app__param_emission. exact (eq_sym PreH6). }
  destruct params as [|h t].
  - discriminate PreH14.
  - cbn [cm_emit_params_head cm_slot_at cm_emit_params_tail tl cm_emit_param_stores].
    unfold cm_emit_params_head, cm_slot_at. cbn [Z.to_nat nth].
    rewrite Hoffset. repeat rewrite <- app_assoc.
    cancel.
Qed.

Lemma proof_of_cmc_emit_param_stores_from_which_implies_wit_4 : cmc_emit_param_stores_from_which_implies_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_param_stores_from_which_implies_wit_4_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_param_stores_from_which_implies_wit_5_split_goal_spatial : cmc_emit_param_stores_from_which_implies_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hoffset : cm_param_offset policy p fid slot_pre = offset_pre).
  { unfold cm_param_offset. rewrite <- PreH2, <- PreH3, PreH4, PreH5, <- PreH1.
    rewrite cm_function_slots_prefix_app__param_emission. exact (eq_sym PreH6). }
  destruct params as [|h t].
  - discriminate PreH14.
  - cbn [cm_emit_params_head cm_slot_at cm_emit_params_tail tl cm_emit_param_stores].
    unfold cm_emit_params_head, cm_slot_at. cbn [Z.to_nat nth].
    rewrite Hoffset. repeat rewrite <- app_assoc.
    cancel.
Qed.

Lemma proof_of_cmc_emit_param_stores_from_which_implies_wit_5 : cmc_emit_param_stores_from_which_implies_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_param_stores_from_which_implies_wit_5_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_param_stores_from_which_implies_wit_6_split_goal_spatial : cmc_emit_param_stores_from_which_implies_wit_6_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct params as [| h t]; [discriminate PreH5 |].
  unfold cm_emit_params_head, cm_emit_params_tail, cm_slot_at. cbn [Z.to_nat nth tl cm_slot_list_rep].
  Exists np. split_pure_spatial.
  - cancel (&(param # "cm_slot" ->ₛ "ty") # Int |-> cm_type_encode (cm_slot_ty h)).
    cancel (&(param # "cm_slot" ->ₛ "count") # Int |-> cm_slot_count h).
    cancel (&(param # "cm_slot" ->ₛ "next") # Ptr |-> np).
    cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cmc_emit_param_stores_from_which_implies_wit_6 : cmc_emit_param_stores_from_which_implies_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_param_stores_from_which_implies_wit_6_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_5_pure_split_goal_1 : cmc_emit_prologue_partial_solve_wit_5_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_5_pure_split_goal_2 : cmc_emit_prologue_partial_solve_wit_5_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_5_pure : cmc_emit_prologue_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_prologue_partial_solve_wit_5_pure_split_goal_1.
  - Goal_apply proof_of_cmc_emit_prologue_partial_solve_wit_5_pure_split_goal_2.
Qed. 

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_6_pure_split_goal_1 : cmc_emit_prologue_partial_solve_wit_6_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_6_pure_split_goal_2 : cmc_emit_prologue_partial_solve_wit_6_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_6_pure : cmc_emit_prologue_partial_solve_wit_6_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_prologue_partial_solve_wit_6_pure_split_goal_1.
  - Goal_apply proof_of_cmc_emit_prologue_partial_solve_wit_6_pure_split_goal_2.
Qed. 

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_7_pure_split_goal_1 : cmc_emit_prologue_partial_solve_wit_7_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_7_pure_split_goal_2 : cmc_emit_prologue_partial_solve_wit_7_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_7_pure : cmc_emit_prologue_partial_solve_wit_7_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_prologue_partial_solve_wit_7_pure_split_goal_1.
  - Goal_apply proof_of_cmc_emit_prologue_partial_solve_wit_7_pure_split_goal_2.
Qed. 

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_8_pure_split_goal_1 : cmc_emit_prologue_partial_solve_wit_8_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_8_pure_split_goal_2 : cmc_emit_prologue_partial_solve_wit_8_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_8_pure : cmc_emit_prologue_partial_solve_wit_8_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_prologue_partial_solve_wit_8_pure_split_goal_1.
  - Goal_apply proof_of_cmc_emit_prologue_partial_solve_wit_8_pure_split_goal_2.
Qed. 

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_9_pure_split_goal_1 : cmc_emit_prologue_partial_solve_wit_9_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_9_pure_split_goal_2 : cmc_emit_prologue_partial_solve_wit_9_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_9_pure : cmc_emit_prologue_partial_solve_wit_9_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_prologue_partial_solve_wit_9_pure_split_goal_1.
  - Goal_apply proof_of_cmc_emit_prologue_partial_solve_wit_9_pure_split_goal_2.
Qed. 

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_10_pure_split_goal_1 : cmc_emit_prologue_partial_solve_wit_10_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_10_pure_split_goal_2 : cmc_emit_prologue_partial_solve_wit_10_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  cbn [tvm_opcode_code].
  lia.
Qed.

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_10_pure : cmc_emit_prologue_partial_solve_wit_10_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_prologue_partial_solve_wit_10_pure_split_goal_1.
  - Goal_apply proof_of_cmc_emit_prologue_partial_solve_wit_10_pure_split_goal_2.
Qed. 

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_11_pure_split_goal_1 : cmc_emit_prologue_partial_solve_wit_11_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_11_pure_split_goal_2 : cmc_emit_prologue_partial_solve_wit_11_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  cbn [tvm_opcode_code].
  lia.
Qed.

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_11_pure : cmc_emit_prologue_partial_solve_wit_11_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_prologue_partial_solve_wit_11_pure_split_goal_1.
  - Goal_apply proof_of_cmc_emit_prologue_partial_solve_wit_11_pure_split_goal_2.
Qed. 

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_12_pure_split_goal_1 : cmc_emit_prologue_partial_solve_wit_12_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_12_pure_split_goal_2 : cmc_emit_prologue_partial_solve_wit_12_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  cbn [tvm_opcode_code].
  lia.
Qed.

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_12_pure : cmc_emit_prologue_partial_solve_wit_12_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_prologue_partial_solve_wit_12_pure_split_goal_1.
  - Goal_apply proof_of_cmc_emit_prologue_partial_solve_wit_12_pure_split_goal_2.
Qed. 

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_13_pure_split_goal_1 : cmc_emit_prologue_partial_solve_wit_13_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_13_pure_split_goal_2 : cmc_emit_prologue_partial_solve_wit_13_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  cbn [tvm_opcode_code].
  lia.
Qed.

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_13_pure : cmc_emit_prologue_partial_solve_wit_13_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_prologue_partial_solve_wit_13_pure_split_goal_1.
  - Goal_apply proof_of_cmc_emit_prologue_partial_solve_wit_13_pure_split_goal_2.
Qed. 

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_14_pure_split_goal_1 : cmc_emit_prologue_partial_solve_wit_14_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_14_pure_split_goal_2 : cmc_emit_prologue_partial_solve_wit_14_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  cbn [tvm_opcode_code].
  lia.
Qed.

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_14_pure : cmc_emit_prologue_partial_solve_wit_14_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_prologue_partial_solve_wit_14_pure_split_goal_1.
  - Goal_apply proof_of_cmc_emit_prologue_partial_solve_wit_14_pure_split_goal_2.
Qed. 

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_15_pure_split_goal_1 : cmc_emit_prologue_partial_solve_wit_15_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_15_pure_split_goal_2 : cmc_emit_prologue_partial_solve_wit_15_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_15_pure : cmc_emit_prologue_partial_solve_wit_15_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_prologue_partial_solve_wit_15_pure_split_goal_1.
  - Goal_apply proof_of_cmc_emit_prologue_partial_solve_wit_15_pure_split_goal_2.
Qed. 

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_16_pure_split_goal_1 : cmc_emit_prologue_partial_solve_wit_16_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_16_pure_split_goal_2 : cmc_emit_prologue_partial_solve_wit_16_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_16_pure : cmc_emit_prologue_partial_solve_wit_16_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_prologue_partial_solve_wit_16_pure_split_goal_1.
  - Goal_apply proof_of_cmc_emit_prologue_partial_solve_wit_16_pure_split_goal_2.
Qed. 

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_17_pure_split_goal_1 : cmc_emit_prologue_partial_solve_wit_17_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_17_pure_split_goal_2 : cmc_emit_prologue_partial_solve_wit_17_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_17_pure : cmc_emit_prologue_partial_solve_wit_17_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_prologue_partial_solve_wit_17_pure_split_goal_1.
  - Goal_apply proof_of_cmc_emit_prologue_partial_solve_wit_17_pure_split_goal_2.
Qed. 

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_18_pure_split_goal_1 : cmc_emit_prologue_partial_solve_wit_18_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_18_pure_split_goal_2 : cmc_emit_prologue_partial_solve_wit_18_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_18_pure : cmc_emit_prologue_partial_solve_wit_18_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_prologue_partial_solve_wit_18_pure_split_goal_1.
  - Goal_apply proof_of_cmc_emit_prologue_partial_solve_wit_18_pure_split_goal_2.
Qed. 

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_20_pure_split_goal_1 : cmc_emit_prologue_partial_solve_wit_20_pure_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_20_pure_split_goal_2 : cmc_emit_prologue_partial_solve_wit_20_pure_split_goal_2.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_20_pure_split_goal_3 : cmc_emit_prologue_partial_solve_wit_20_pure_split_goal_3.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cmc_emit_prologue_partial_solve_wit_20_pure : cmc_emit_prologue_partial_solve_wit_20_pure.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_cmc_emit_prologue_partial_solve_wit_20_pure_split_goal_1.
 Goal_apply proof_of_cmc_emit_prologue_partial_solve_wit_20_pure_split_goal_2.
 Goal_apply proof_of_cmc_emit_prologue_partial_solve_wit_20_pure_split_goal_3.

Qed. 

Lemma proof_of_cmc_emit_prologue_which_implies_wit_1 : cmc_emit_prologue_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_function_context_rep.
  Intros params locals.
  Exists locals params.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_cmc_emit_prologue_which_implies_wit_2_split_goal_1 : cmc_emit_prologue_which_implies_wit_2_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 unfold cm_frame_size, cm_temp_slots.
 rewrite <- (cm_slots_size_matches__temp_context _ _ PreH4),
   <- (cm_slots_size_matches__temp_context _ _ PreH5).
 rewrite <- PreH3. exact PreH11.
Qed.

Lemma proof_of_cmc_emit_prologue_which_implies_wit_2 : cmc_emit_prologue_which_implies_wit_2.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_cmc_emit_prologue_which_implies_wit_2_split_goal_1.

Qed. 

Lemma proof_of_cmc_emit_prologue_which_implies_wit_3_split_goal_spatial : cmc_emit_prologue_which_implies_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst f frame_size.
  unfold cm_emit_prologue.
  cbn [List.app].
  cancel.
Qed.

Lemma proof_of_cmc_emit_prologue_which_implies_wit_3 : cmc_emit_prologue_which_implies_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_prologue_which_implies_wit_3_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_prologue_which_implies_wit_4_split_goal_1 : cmc_emit_prologue_which_implies_wit_4_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 rewrite <- (cm_slots_size_matches__temp_context _ _ PreH4).
 destruct (cm_function_params f) as [|h t] eqn:Hp.
 - cbn [cm_rep_members_size]. lia.
 - cbn [cm_rep_members_safe] in PreH6. lia.
Qed.

Lemma proof_of_cmc_emit_prologue_which_implies_wit_4_split_goal_2 : cmc_emit_prologue_which_implies_wit_4_split_goal_2.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 pose proof (cm_function_param_count_length__prologue_layout (cm_function_params f)) as Hlen.
 destruct (cm_function_params f) as [|h t] eqn:Hp.
 - rewrite Zlength_nil. lia.
 - cbn [cm_param_counts_representable] in PreH10.
   unfold cm_i32_code_count in PreH10. lia.
Qed.

Lemma proof_of_cmc_emit_prologue_which_implies_wit_4 : cmc_emit_prologue_which_implies_wit_4.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_cmc_emit_prologue_which_implies_wit_4_split_goal_1.
 Goal_apply proof_of_cmc_emit_prologue_which_implies_wit_4_split_goal_2.

Qed. 

Lemma proof_of_cmc_emit_prologue_which_implies_wit_5_split_goal_spatial : cmc_emit_prologue_which_implies_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst f frame_size.
  unfold cm_emit_prologue.
  repeat rewrite <- app_assoc.
  cbn [List.app].
  cancel.
Qed.

Lemma proof_of_cmc_emit_prologue_which_implies_wit_5 : cmc_emit_prologue_which_implies_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_prologue_which_implies_wit_5_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_prologue_which_implies_wit_6_split_goal_spatial : cmc_emit_prologue_which_implies_wit_6_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_function_context_rep.
  Exists zp zl.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_cmc_emit_prologue_which_implies_wit_6 : cmc_emit_prologue_which_implies_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_prologue_which_implies_wit_6_split_goal_spatial.
Qed.

Lemma proof_of_cmc_emit_function_safety_wit_1_split_goal_1 : cmc_emit_function_safety_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: unfold cm_i32_code_count in *.
  all: subst; lia.
Qed.

Lemma proof_of_cmc_emit_function_safety_wit_1_split_goal_2 : cmc_emit_function_safety_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: unfold cm_i32_code_count in *.
  all: subst; lia.
Qed.

Lemma proof_of_cmc_emit_function_safety_wit_1 : cmc_emit_function_safety_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_function_safety_wit_1_split_goal_1.
  - Goal_apply proof_of_cmc_emit_function_safety_wit_1_split_goal_2.
Qed. 

Lemma proof_of_cmc_emit_function_partial_solve_wit_9_pure_split_goal_1 : cmc_emit_function_partial_solve_wit_9_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: unfold cm_i32_code_count; lia.
Qed.

Lemma proof_of_cmc_emit_function_partial_solve_wit_9_pure_split_goal_2 : cmc_emit_function_partial_solve_wit_9_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: unfold cm_i32_code_count; lia.
Qed.

Lemma proof_of_cmc_emit_function_partial_solve_wit_9_pure : cmc_emit_function_partial_solve_wit_9_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_function_partial_solve_wit_9_pure_split_goal_1.
  - Goal_apply proof_of_cmc_emit_function_partial_solve_wit_9_pure_split_goal_2.
Qed. 

Lemma proof_of_cmc_emit_function_partial_solve_wit_11_pure_split_goal_1 : cmc_emit_function_partial_solve_wit_11_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: cbn [tvm_opcode_code]; lia.
Qed.

Lemma proof_of_cmc_emit_function_partial_solve_wit_11_pure_split_goal_2 : cmc_emit_function_partial_solve_wit_11_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: cbn [tvm_opcode_code]; lia.
Qed.

Lemma proof_of_cmc_emit_function_partial_solve_wit_11_pure : cmc_emit_function_partial_solve_wit_11_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_function_partial_solve_wit_11_pure_split_goal_1.
  - Goal_apply proof_of_cmc_emit_function_partial_solve_wit_11_pure_split_goal_2.
Qed. 

Lemma proof_of_cmc_emit_function_which_implies_wit_2 : cmc_emit_function_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_function_context_rep.
  Intros params locals.
  Exists locals params.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_cmc_emit_function_which_implies_wit_3_split_goal_spatial : cmc_emit_function_which_implies_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_function_context_rep.
  Exists zp zl.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_cmc_emit_function_which_implies_wit_3 : cmc_emit_function_which_implies_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_function_which_implies_wit_3_split_goal_spatial.
Qed.

Lemma proof_of_cmc_emit_function_which_implies_wit_5_split_goal_spatial : cmc_emit_function_which_implies_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst f s body_pc.
  unfold cm_emit_function.
  repeat rewrite <- app_assoc.
  cancel.
Qed.

Lemma proof_of_cmc_emit_function_which_implies_wit_5 : cmc_emit_function_which_implies_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_function_which_implies_wit_5_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_function_which_implies_wit_6_split_goal_spatial : cmc_emit_function_which_implies_wit_6_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cmc_emit_function_which_implies_wit_6 : cmc_emit_function_which_implies_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_function_which_implies_wit_6_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_function_which_implies_wit_7_split_goal_spatial : cmc_emit_function_which_implies_wit_7_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst f s body_pc.
  unfold cm_emit_function.
  repeat rewrite <- app_assoc.
  cancel.
Qed.

Lemma proof_of_cmc_emit_function_which_implies_wit_7 : cmc_emit_function_which_implies_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_function_which_implies_wit_7_split_goal_spatial.
Qed. 

