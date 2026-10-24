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
From SimpleC.EE.QCP_demos_human Require Import cmc_emit_code_migration_goal.
From SimpleC.EE.QCP_demos_human Require Import cmc_emit_code_migration_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.cmc_emit_code_migration_lib.
Local Open Scope sac.

Lemma proof_of_cmc_emit_code_entail_wit_1 : cmc_emit_code_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_program_context_rep.
  Intros sp0 gp0 tp0.
  Exists tp0 gp0 sp0.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_cmc_emit_code_entail_wit_2_split_goal_1 : cmc_emit_code_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold cm_function_pc.
  destruct (cm_program_functions p); reflexivity.
Qed.

Lemma proof_of_cmc_emit_code_entail_wit_2_split_goal_spatial : cmc_emit_code_entail_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_model_code.
  rewrite app_assoc.
  unfold cm_program_context_rep.
  Exists sp gp tp.
  split_pure_spatial.
  - repeat progress cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cmc_emit_code_entail_wit_2 : cmc_emit_code_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_code_entail_wit_2_split_goal_spatial.
  - Goal_apply proof_of_cmc_emit_code_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_cmc_emit_code_return_wit_1_split_goal_spatial : cmc_emit_code_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_model_code.
  rewrite app_assoc.
  repeat progress cancel.
Qed.

Lemma proof_of_cmc_emit_code_return_wit_1 : cmc_emit_code_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_code_return_wit_1_split_goal_spatial.
Qed.

