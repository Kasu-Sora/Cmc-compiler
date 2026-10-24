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
From SimpleC.EE.QCP_demos_human Require Import cmc_emit_resolved_migration_goal.
From SimpleC.EE.QCP_demos_human Require Import cmc_emit_resolved_migration_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.cmc_emit_resolved_migration_lib.
Local Open Scope sac.

Lemma proof_of_cm_emit_resolved_entail_wit_1 : cm_emit_resolved_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || reflexivity).
  unfold cm_resolved_emitter_rep.
  Intros raw_prefix. rename H into Hpatch.
  Exists raw_prefix.
  unfold cm_emitter_plan_rep.
  pose proof (cm_patch_code_length policy p raw_prefix) as Hlength.
  rewrite Hpatch in Hlength.
  split_pure_spatial.
  - cancel (cm_emitter_rep emitter_pre out capacity
      (cm_rep_ops raw_prefix) (cm_rep_imms raw_prefix)).
  - split_pures; dump_pre_spatial; auto;
      rewrite Zlength_cons, Zlength_nil; lia.
Qed.

Lemma proof_of_cm_emit_resolved_return_wit_1_split_goal_spatial : cm_emit_resolved_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_emitter_plan_rep, cm_resolved_emitter_rep.
  Intros_p Hbound.
  Exists (raw_prefix ++ (TVMInst opcode immediate_pre :: nil)).
  split_pure_spatial.
  - cancel (cm_emitter_rep emitter_pre out capacity
      (cm_rep_ops (raw_prefix ++ (TVMInst opcode immediate_pre :: nil)))
      (cm_rep_imms (raw_prefix ++ (TVMInst opcode immediate_pre :: nil)))).
  - dump_pre_spatial.
    rewrite cm_patch_code_append, cm_patch_noncall by exact PreH2.
    rewrite PreH3. reflexivity.
Qed.

Lemma proof_of_cm_emit_resolved_return_wit_1 : cm_emit_resolved_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_resolved_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_resolved_call_entail_wit_1 : cm_emit_resolved_call_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || reflexivity).
  unfold cm_resolved_emitter_rep.
  Intros raw_prefix. rename H into Hpatch.
  Exists raw_prefix.
  unfold cm_emitter_plan_rep.
  pose proof (cm_patch_code_length policy p raw_prefix) as Hlength.
  rewrite Hpatch in Hlength.
  split_pure_spatial.
  - cancel (cm_emitter_rep emitter_pre out capacity
      (cm_rep_ops raw_prefix) (cm_rep_imms raw_prefix)).
  - split_pures; dump_pre_spatial; auto;
      rewrite Zlength_cons, Zlength_nil; lia.
Qed.

Lemma proof_of_cm_emit_resolved_call_return_wit_1_split_goal_spatial : cm_emit_resolved_call_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_emitter_plan_rep, cm_resolved_emitter_rep.
  Intros_p Hbound.
  Exists (raw_prefix ++ (TVMInst TVMCallOp function_id_pre :: nil)).
  split_pure_spatial.
  - cancel (cm_emitter_rep emitter_pre out capacity
      (cm_rep_ops (raw_prefix ++ (TVMInst TVMCallOp function_id_pre :: nil)))
      (cm_rep_imms (raw_prefix ++ (TVMInst TVMCallOp function_id_pre :: nil)))).
  - dump_pre_spatial.
    rewrite cm_patch_code_append, cm_patch_call, PreH2. reflexivity.
Qed.

Lemma proof_of_cm_emit_resolved_call_return_wit_1 : cm_emit_resolved_call_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_resolved_call_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_resolved_normalize_entail_wit_1 : cm_emit_resolved_normalize_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || reflexivity).
  unfold cm_resolved_emitter_rep.
  Intros raw_prefix. rename H into Hpatch.
  Exists raw_prefix.
  unfold cm_emitter_plan_rep. rewrite app_nil_r.
  pose proof (cm_patch_code_length policy p raw_prefix) as Hlength.
  rewrite Hpatch in Hlength.
  split_pure_spatial.
  - cancel (cm_emitter_rep emitter_pre out capacity
      (cm_rep_ops raw_prefix) (cm_rep_imms raw_prefix)).
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_cm_emit_resolved_normalize_return_wit_1_split_goal_spatial : cm_emit_resolved_normalize_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_emitter_plan_rep, cm_resolved_emitter_rep.
  Intros_p Hbound.
  Exists (raw_prefix ++ cm_char_normalize_code model_ty).
  split_pure_spatial.
  - cancel (cm_emitter_rep emitter_pre out capacity
      (cm_rep_ops (raw_prefix ++ cm_char_normalize_code model_ty))
      (cm_rep_imms (raw_prefix ++ cm_char_normalize_code model_ty))).
  - dump_pre_spatial.
    rewrite cm_patch_code_append, cm_patch_char_normalize, PreH3. reflexivity.
Qed.

Lemma proof_of_cm_emit_resolved_normalize_return_wit_1 : cm_emit_resolved_normalize_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_resolved_normalize_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_resolved_load_entail_wit_1 : cm_emit_resolved_load_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || reflexivity).
  unfold cm_resolved_emitter_rep.
  Intros raw_prefix. rename H into Hpatch.
  Exists raw_prefix.
  unfold cm_emitter_plan_rep. rewrite app_nil_r.
  pose proof (cm_patch_code_length policy p raw_prefix) as Hlength.
  rewrite Hpatch in Hlength.
  split_pure_spatial.
  - cancel (cm_emitter_rep emitter_pre out capacity
      (cm_rep_ops raw_prefix) (cm_rep_imms raw_prefix)).
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_cm_emit_resolved_load_return_wit_1_split_goal_spatial : cm_emit_resolved_load_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_emitter_plan_rep, cm_resolved_emitter_rep.
  Intros_p Hbound.
  Exists (raw_prefix ++ cm_load_code model_ty).
  split_pure_spatial.
  - cancel (cm_emitter_rep emitter_pre out capacity
      (cm_rep_ops (raw_prefix ++ cm_load_code model_ty))
      (cm_rep_imms (raw_prefix ++ cm_load_code model_ty))).
  - dump_pre_spatial.
    rewrite cm_patch_code_append, cm_patch_load, PreH3. reflexivity.
Qed.

Lemma proof_of_cm_emit_resolved_load_return_wit_1 : cm_emit_resolved_load_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_resolved_load_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_resolved_store_entail_wit_1 : cm_emit_resolved_store_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || reflexivity).
  unfold cm_resolved_emitter_rep.
  Intros raw_prefix. rename H into Hpatch.
  Exists raw_prefix.
  unfold cm_emitter_plan_rep. rewrite app_nil_r.
  pose proof (cm_patch_code_length policy p raw_prefix) as Hlength.
  rewrite Hpatch in Hlength.
  split_pure_spatial.
  - cancel (cm_emitter_rep emitter_pre out capacity
      (cm_rep_ops raw_prefix) (cm_rep_imms raw_prefix)).
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_cm_emit_resolved_store_return_wit_1_split_goal_spatial : cm_emit_resolved_store_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_emitter_plan_rep, cm_resolved_emitter_rep.
  Intros_p Hbound.
  Exists (raw_prefix ++ cm_store_code model_ty).
  split_pure_spatial.
  - cancel (cm_emitter_rep emitter_pre out capacity
      (cm_rep_ops (raw_prefix ++ cm_store_code model_ty))
      (cm_rep_imms (raw_prefix ++ cm_store_code model_ty))).
  - dump_pre_spatial.
    rewrite cm_patch_code_append, cm_patch_store, PreH3. reflexivity.
Qed.

Lemma proof_of_cm_emit_resolved_store_return_wit_1 : cm_emit_resolved_store_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_resolved_store_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_resolved_fp_address_entail_wit_1 : cm_emit_resolved_fp_address_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || reflexivity).
  unfold cm_resolved_emitter_rep.
  Intros raw_prefix. rename H into Hpatch.
  Exists raw_prefix.
  unfold cm_emitter_plan_rep. rewrite app_nil_r.
  pose proof (cm_patch_code_length policy p raw_prefix) as Hlength.
  rewrite Hpatch in Hlength.
  split_pure_spatial.
  - cancel (cm_emitter_rep emitter_pre out capacity
      (cm_rep_ops raw_prefix) (cm_rep_imms raw_prefix)).
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_cm_emit_resolved_fp_address_return_wit_1_split_goal_spatial : cm_emit_resolved_fp_address_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_emitter_plan_rep, cm_resolved_emitter_rep.
  Intros_p Hbound.
  Exists (raw_prefix ++ cm_fp_relative_address_code offset_pre).
  split_pure_spatial.
  - cancel (cm_emitter_rep emitter_pre out capacity
      (cm_rep_ops (raw_prefix ++ cm_fp_relative_address_code offset_pre))
      (cm_rep_imms (raw_prefix ++ cm_fp_relative_address_code offset_pre))).
  - dump_pre_spatial.
    rewrite cm_patch_code_append, cm_patch_fp_address, PreH1. reflexivity.
Qed.

Lemma proof_of_cm_emit_resolved_fp_address_return_wit_1 : cm_emit_resolved_fp_address_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_resolved_fp_address_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_resolved_temp_store_entail_wit_1 : cm_emit_resolved_temp_store_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_resolved_emitter_rep.
  Intros raw_prefix.
  match goal with H : cm_patch_code _ _ raw_prefix = _ |- _ => rename H into Hpatch end.
  Exists raw_prefix.
  unfold cm_emitter_plan_rep.
  rewrite app_nil_r.
  rewrite <- Hpatch, cm_patch_code_length in PreH9.
  entailer_with ltac:(auto).
Qed.

Lemma proof_of_cm_emit_resolved_temp_store_return_wit_1_split_goal_spatial : cm_emit_resolved_temp_store_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_emitter_plan_rep, cm_resolved_emitter_rep.
  Intros_p Hplan.
  Exists (raw_prefix ++ cm_temp_store_code policy p fid temp_pre).
  split_pure_spatial.
  - cancel (cm_function_context_rep fn_pre f body next).
    cancel (cm_emitter_rep emitter_pre out capacity
      (cm_rep_ops (raw_prefix ++ cm_temp_store_code policy p fid temp_pre))
      (cm_rep_imms (raw_prefix ++ cm_temp_store_code policy p fid temp_pre))).
  - dump_pre_spatial.
    rewrite cm_patch_code_append, cm_patch_temp_store.
    congruence.
Qed.

Lemma proof_of_cm_emit_resolved_temp_store_return_wit_1 : cm_emit_resolved_temp_store_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_resolved_temp_store_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_resolved_temp_load_entail_wit_1 : cm_emit_resolved_temp_load_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_resolved_emitter_rep.
  Intros raw_prefix.
  match goal with H : cm_patch_code _ _ raw_prefix = _ |- _ => rename H into Hpatch end.
  Exists raw_prefix.
  unfold cm_emitter_plan_rep.
  rewrite app_nil_r.
  rewrite <- Hpatch, cm_patch_code_length in PreH9.
  entailer_with ltac:(auto).
Qed.

Lemma proof_of_cm_emit_resolved_temp_load_return_wit_1_split_goal_spatial : cm_emit_resolved_temp_load_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_emitter_plan_rep, cm_resolved_emitter_rep.
  Intros_p Hplan.
  Exists (raw_prefix ++ cm_temp_load_code policy p fid temp_pre).
  split_pure_spatial.
  - cancel (cm_function_context_rep fn_pre f body next).
    cancel (cm_emitter_rep emitter_pre out capacity
      (cm_rep_ops (raw_prefix ++ cm_temp_load_code policy p fid temp_pre))
      (cm_rep_imms (raw_prefix ++ cm_temp_load_code policy p fid temp_pre))).
  - dump_pre_spatial.
    rewrite cm_patch_code_append, cm_patch_temp_load.
    congruence.
Qed.

Lemma proof_of_cm_emit_resolved_temp_load_return_wit_1 : cm_emit_resolved_temp_load_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_resolved_temp_load_return_wit_1_split_goal_spatial.
Qed.

