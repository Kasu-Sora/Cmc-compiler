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
From SimpleC.EE.QCP_demos_human Require Import cmc_write_zeroes_migration_goal.
From SimpleC.EE.QCP_demos_human Require Import cmc_write_zeroes_migration_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_cmc_write_zeroes_entail_wit_1_split_goal_spatial : cmc_write_zeroes_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  change (zeros 0) with (@nil Z).
  rewrite app_nil_r, Z.add_0_r.
  cancel (UCharArray.seg data_pre 0 cursor_pre prefix).
Qed.

Lemma proof_of_cmc_write_zeroes_entail_wit_1 : cmc_write_zeroes_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_write_zeroes_entail_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cmc_write_zeroes_entail_wit_2_split_goal_spatial : cmc_write_zeroes_entail_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace ((cursor_pre + index) + 1) with (cursor_pre + (index + 1)) by lia.
  unfold zeros.
  rewrite Z2Nat.inj_add by lia.
  rewrite repeat_app.
  simpl Z.to_nat.
  rewrite app_assoc.
  reflexivity.
Qed.

Lemma proof_of_cmc_write_zeroes_entail_wit_2 : cmc_write_zeroes_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_write_zeroes_entail_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_cmc_write_zeroes_return_wit_1_split_goal_spatial : cmc_write_zeroes_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH1.
  cancel (UCharArray.seg data_pre 0 (cursor_pre + count_pre) (prefix ++ zeros count_pre)).
Qed.

Lemma proof_of_cmc_write_zeroes_return_wit_1 : cmc_write_zeroes_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_write_zeroes_return_wit_1_split_goal_spatial.
Qed.

