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
From SimpleC.EE.QCP_demos_human Require Import cmc_patch_calls_migration_goal.
From SimpleC.EE.QCP_demos_human Require Import cmc_patch_calls_migration_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.cmc_patch_calls_migration_lib.
Local Open Scope sac.

Lemma proof_of_cmc_patch_code_arrays_entail_wit_1 : cmc_patch_code_arrays_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct raw as [|[opcode immediate] rest].
  - rewrite Zlength_nil in PreH6. lia.
  - Exists opcode immediate.
    unfold cm_patch_tail. simpl tl.
    rewrite Zlength_cons in PreH6.
    replace length_pre with (1 + Zlength rest) by lia.
    replace (1 + Zlength rest - 1) with (Zlength rest) by lia.
    split_pure_spatial.
    + sep_apply_l_atomic (cm_patch_arrays_open__array_open ops_pre imms_pre opcode immediate rest).
      replace (ops_pre + 1 * sizeof(INT)) with (ops_pre + sizeof(INT)) by lia.
      replace (imms_pre + 1 * sizeof(INT64)) with (imms_pre + sizeof(INT64)) by lia.
      cancel.
    + split_pures; dump_pre_spatial; try rewrite Zlength_cons; auto; lia.
Qed. 

Lemma proof_of_cmc_patch_code_arrays_return_wit_1_split_goal_spatial : cmc_patch_code_arrays_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct raw as [|head rest].
  - unfold cm_patch_code. simpl map. cancel.
  - rewrite Zlength_cons in PreH6. pose proof (Zlength_nonneg rest). lia.
Qed.

Lemma proof_of_cmc_patch_code_arrays_return_wit_1 : cmc_patch_code_arrays_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_patch_code_arrays_return_wit_1_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_patch_code_arrays_return_wit_2_split_goal_spatial : cmc_patch_code_arrays_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hlen : Zlength (cm_patch_code policy p (cm_patch_tail raw)) = length_pre - 1).
  { rewrite cm_patch_code_length. lia. }
  assert (Hpatch : cm_patch_code policy p raw =
    TVMInst opcode (cm_function_pc policy p model_imm) :: cm_patch_code policy p (cm_patch_tail raw)).
  { rewrite PreH20 at 1. unfold cm_patch_code at 1; simpl map.
    unfold cm_patch_inst at 1. rewrite (proj2 (Z.eqb_eq _ _) PreH14). reflexivity. }
  rewrite Hpatch.
  replace length_pre with (1 + Zlength (cm_patch_code policy p (cm_patch_tail raw))) at 2 by lia.
  replace (length_pre - 1) with (Zlength (cm_patch_code policy p (cm_patch_tail raw))) by lia.
  replace (ops_pre + 1 * sizeof(INT)) with (ops_pre + sizeof(INT)) by lia.
  replace (imms_pre + 1 * sizeof(INT64)) with (imms_pre + sizeof(INT64)) by lia.
  rewrite PreH12.
  sep_apply_l_atomic (cm_patch_arrays_cons__array_close ops_pre imms_pre opcode (cm_function_pc policy p model_imm)
    (cm_patch_code policy p (cm_patch_tail raw))).
  repeat cancel.
Qed.

Lemma proof_of_cmc_patch_code_arrays_return_wit_2 : cmc_patch_code_arrays_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_patch_code_arrays_return_wit_2_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_patch_code_arrays_return_wit_3_split_goal_spatial : cmc_patch_code_arrays_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hlen : Zlength (cm_patch_code policy p (cm_patch_tail raw)) = length_pre - 1).
  { rewrite cm_patch_code_length. lia. }
  assert (Hpatch : cm_patch_code policy p raw =
    TVMInst opcode (model_imm) :: cm_patch_code policy p (cm_patch_tail raw)).
  { rewrite PreH16 at 1. unfold cm_patch_code at 1; simpl map.
    unfold cm_patch_inst at 1. rewrite (proj2 (Z.eqb_neq _ _) PreH10). reflexivity. }
  rewrite Hpatch.
  replace length_pre with (1 + Zlength (cm_patch_code policy p (cm_patch_tail raw))) at 2 by lia.
  replace (length_pre - 1) with (Zlength (cm_patch_code policy p (cm_patch_tail raw))) by lia.
  replace (ops_pre + 1 * sizeof(INT)) with (ops_pre + sizeof(INT)) by lia.
  replace (imms_pre + 1 * sizeof(INT64)) with (imms_pre + sizeof(INT64)) by lia.
  
  sep_apply_l_atomic (cm_patch_arrays_cons__array_close ops_pre imms_pre opcode (model_imm)
    (cm_patch_code policy p (cm_patch_tail raw))).
  repeat cancel.
Qed.

Lemma proof_of_cmc_patch_code_arrays_return_wit_3 : cmc_patch_code_arrays_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_patch_code_arrays_return_wit_3_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_patch_resolved_calls_entail_wit_1 : cmc_patch_resolved_calls_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_resolved_emitter_rep, cm_emitter_rep.
  Intros raw ops imms.
  assert (Hop : Zlength (cm_rep_ops raw) = Zlength raw).
  { unfold cm_rep_ops. clear - raw. induction raw; [reflexivity|]. simpl map. rewrite !Zlength_cons. lia. }
  assert (Himm : Zlength (cm_rep_imms raw) = Zlength raw).
  { unfold cm_rep_imms. clear - raw. induction raw; [reflexivity|]. simpl map. rewrite !Zlength_cons. lia. }
  rewrite Hop in *.
  prop_apply_p (store_int_range (&(out # "cm_output" ->ₛ "code_capacity")) capacity).
  Intros_p Hcap.
  Exists imms ops raw.
  unfold cm_patch_arrays_rep.
  sep_apply_l_atomic (IntArray.seg_to_full ops 0 (Zlength raw) (cm_rep_ops raw)).
  sep_apply_l_atomic (Int64Array.seg_to_full imms 0 (Zlength raw) (cm_rep_imms raw)).
  rewrite !Z.mul_0_l, !Z.add_0_r, !Z.sub_0_r.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; intuition (try int_auto; try lia).
Qed.

Lemma proof_of_cmc_patch_resolved_calls_return_wit_1_split_goal_spatial : cmc_patch_resolved_calls_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_patch_arrays_rep, cm_emitter_rep.
  Exists ops_ptr imms_ptr.
  assert (Hlen : Zlength resolved = Zlength raw_prefix).
  { rewrite <- PreH11. apply cm_patch_code_length. }
  assert (Hop : Zlength (cm_rep_ops resolved) = Zlength raw_prefix).
  { rewrite <- Hlen. unfold cm_rep_ops. clear - resolved. induction resolved; [reflexivity|]. simpl map. rewrite !Zlength_cons. lia. }
  assert (Himm : Zlength (cm_rep_imms resolved) = Zlength raw_prefix).
  { rewrite <- Hlen. unfold cm_rep_imms. clear - resolved. induction resolved; [reflexivity|]. simpl map. rewrite !Zlength_cons. lia. }
  rewrite PreH11, Hop, Himm.
  sep_apply_l_atomic (IntArray.full_to_seg ops_ptr (Zlength raw_prefix) (cm_rep_ops resolved)).
  sep_apply_l_atomic (Int64Array.full_to_seg imms_ptr (Zlength raw_prefix) (cm_rep_imms resolved)).
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; intuition lia.
Qed.

Lemma proof_of_cmc_patch_resolved_calls_return_wit_1 : cmc_patch_resolved_calls_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_patch_resolved_calls_return_wit_1_split_goal_spatial.
Qed.
