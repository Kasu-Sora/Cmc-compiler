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
From SimpleC.EE.QCP_demos_human Require Import cmc_copy_bytes_migration_goal.
From SimpleC.EE.QCP_demos_human Require Import cmc_copy_bytes_migration_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.cmc_copy_bytes_migration_lib.
Local Open Scope sac.

Lemma proof_of_cmc_copy_bytes_entail_wit_1_split_goal_1 : cmc_copy_bytes_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cmc_uint8_buffer_nonnull in PreH7.
  dump_pre_spatial.
  destruct PreH7 as [Hempty | Hnonnull].
  - subst bytes. rewrite Zlength_nil in PreH3. lia.
  - exact Hnonnull.
Qed.

Lemma proof_of_cmc_copy_bytes_entail_wit_1_split_goal_spatial : cmc_copy_bytes_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  change (UCharArray.seg data_pre 0 cursor_pre prefix |--
    UCharArray.seg data_pre 0 (cursor_pre + 0) (prefix ++ nil)).
  rewrite app_nil_r, Z.add_0_r.
  cancel (UCharArray.seg data_pre 0 cursor_pre prefix).
Qed.

Lemma proof_of_cmc_copy_bytes_entail_wit_1 : cmc_copy_bytes_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_copy_bytes_entail_wit_1_split_goal_spatial.
  - Goal_apply proof_of_cmc_copy_bytes_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_cmc_copy_bytes_entail_wit_2_split_goal_spatial : cmc_copy_bytes_entail_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (sublist_split 0 (index + 1) index bytes) by lia.
  rewrite (sublist_single 0 index bytes) by lia.
  rewrite app_assoc.
  replace ((cursor_pre + index) + 1) with (cursor_pre + (index + 1)) by lia.
  reflexivity.
Qed.

Lemma proof_of_cmc_copy_bytes_entail_wit_2 : cmc_copy_bytes_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_copy_bytes_entail_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_cmc_copy_bytes_return_wit_1_split_goal_spatial : cmc_copy_bytes_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hbytes : bytes = nil).
  { destruct bytes as [|b rest].
    - reflexivity.
    - rewrite Zlength_cons in PreH3.
      pose proof (Zlength_nonneg rest). lia. }
  subst length_pre bytes.
  rewrite app_nil_r, Z.add_0_r.
  cancel (UCharArray.seg data_pre 0 cursor_pre prefix).
Qed.

Lemma proof_of_cmc_copy_bytes_return_wit_1 : cmc_copy_bytes_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_copy_bytes_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cmc_copy_bytes_return_wit_2_split_goal_1 : cmc_copy_bytes_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold cmc_uint8_buffer_nonnull.
  right. exact PreH4.
Qed.

Lemma proof_of_cmc_copy_bytes_return_wit_2_split_goal_spatial : cmc_copy_bytes_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hindex : index = length_pre) by lia.
  subst index.
  rewrite sublist_self by lia.
  cancel (UCharArray.seg data_pre 0 (cursor_pre + length_pre) (prefix ++ bytes)).
Qed.

Lemma proof_of_cmc_copy_bytes_return_wit_2 : cmc_copy_bytes_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_copy_bytes_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_cmc_copy_bytes_return_wit_2_split_goal_1.
Qed.

