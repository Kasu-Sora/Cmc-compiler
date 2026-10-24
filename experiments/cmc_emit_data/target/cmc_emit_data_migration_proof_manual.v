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
From SimpleC.EE.QCP_demos_human Require Import cmc_emit_data_migration_goal.
From SimpleC.EE.QCP_demos_human Require Import cmc_emit_data_migration_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.cmc_emit_data_migration_lib.
Local Open Scope sac.

Lemma proof_of_cmc_emit_data_entail_wit_1_split_goal_spatial : cmc_emit_data_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cmc_emit_data_entail_wit_1 : cmc_emit_data_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_data_entail_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cmc_emit_data_return_wit_1_split_goal_1 : cmc_emit_data_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cmc_emit_data_return_wit_1_split_goal_spatial : cmc_emit_data_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH5.
  cancel.
Qed.

Lemma proof_of_cmc_emit_data_return_wit_1 : cmc_emit_data_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_data_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_cmc_emit_data_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_cmc_emit_data_partial_solve_wit_1_pure_split_goal_1 : cmc_emit_data_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || reflexivity).
Qed.

Lemma proof_of_cmc_emit_data_partial_solve_wit_1_pure : cmc_emit_data_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_data_partial_solve_wit_1_pure_split_goal_1.
Qed.

Lemma proof_of_cmc_emit_data_partial_solve_wit_3_pure_split_goal_1 : cmc_emit_data_partial_solve_wit_3_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || reflexivity).
Qed.

Lemma proof_of_cmc_emit_data_partial_solve_wit_3_pure : cmc_emit_data_partial_solve_wit_3_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_data_partial_solve_wit_3_pure_split_goal_1.
Qed.

