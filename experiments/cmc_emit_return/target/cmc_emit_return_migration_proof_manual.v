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
From SimpleC.EE.QCP_demos_human Require Import cmc_emit_return_migration_goal.
From SimpleC.EE.QCP_demos_human Require Import cmc_emit_return_migration_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.cmc_emit_return_migration_lib.
Local Open Scope sac.

Lemma proof_of_cm_emit_return_epilogue_plan_entail_wit_1_split_goal_1 : cm_emit_return_epilogue_plan_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cm_emit_return_epilogue_plan_entail_wit_1_split_goal_2 : cm_emit_return_epilogue_plan_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_cm_emit_return_epilogue_plan_entail_wit_1_split_goal_3 : cm_emit_return_epilogue_plan_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cm_emit_return_epilogue_plan_entail_wit_1_split_goal_4 : cm_emit_return_epilogue_plan_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_cm_emit_return_epilogue_plan_entail_wit_1_split_goal_5 : cm_emit_return_epilogue_plan_entail_wit_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cm_emit_return_epilogue_plan_entail_wit_1_split_goal_6 : cm_emit_return_epilogue_plan_entail_wit_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_cm_emit_return_epilogue_plan_entail_wit_1_split_goal_7 : cm_emit_return_epilogue_plan_entail_wit_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cm_emit_return_epilogue_plan_entail_wit_1_split_goal_8 : cm_emit_return_epilogue_plan_entail_wit_1_split_goal_8.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_cm_emit_return_epilogue_plan_entail_wit_1_split_goal_spatial : cm_emit_return_epilogue_plan_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto);
  unfold cm_return_epilogue;
  cbn [app];
  reflexivity.
Qed.

Lemma proof_of_cm_emit_return_epilogue_plan_entail_wit_1 : cm_emit_return_epilogue_plan_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_return_epilogue_plan_entail_wit_1_split_goal_spatial.
  - Goal_apply proof_of_cm_emit_return_epilogue_plan_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_cm_emit_return_epilogue_plan_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_cm_emit_return_epilogue_plan_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_cm_emit_return_epilogue_plan_entail_wit_1_split_goal_4.
  - Goal_apply proof_of_cm_emit_return_epilogue_plan_entail_wit_1_split_goal_5.
  - Goal_apply proof_of_cm_emit_return_epilogue_plan_entail_wit_1_split_goal_6.
  - Goal_apply proof_of_cm_emit_return_epilogue_plan_entail_wit_1_split_goal_7.
  - Goal_apply proof_of_cm_emit_return_epilogue_plan_entail_wit_1_split_goal_8.
Qed.

Lemma proof_of_cm_emit_return_epilogue_plan_return_wit_1_split_goal_spatial : cm_emit_return_epilogue_plan_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_return_epilogue.
  repeat rewrite <- List.app_assoc.
  cbn [List.app].
  reflexivity.
Qed.

Lemma proof_of_cm_emit_return_epilogue_plan_return_wit_1 : cm_emit_return_epilogue_plan_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_return_epilogue_plan_return_wit_1_split_goal_spatial.
Qed.

