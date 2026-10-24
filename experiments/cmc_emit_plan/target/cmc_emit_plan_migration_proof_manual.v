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
From SimpleC.EE.QCP_demos_human Require Import cmc_emit_plan_migration_goal.
From SimpleC.EE.QCP_demos_human Require Import cmc_emit_plan_migration_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.cmc_emit_plan_migration_lib.
Local Open Scope sac.

Lemma proof_of_cm_emit_plan_entail_wit_1_split_goal_1 : cm_emit_plan_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_resolved_emitter_plan_rep.
  Intros_p Hbudget.
  dump_pre_spatial.
  rewrite Zlength_cons in Hbudget.
  pose proof (Zlength_nonneg tail).
  lia.
Qed.

Lemma proof_of_cm_emit_plan_entail_wit_1_split_goal_2 : cm_emit_plan_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_resolved_emitter_plan_rep.
  Intros_p Hbudget.
  dump_pre_spatial.
  rewrite Zlength_cons in Hbudget.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma proof_of_cm_emit_plan_entail_wit_1_split_goal_spatial : cm_emit_plan_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cm_emit_plan_entail_wit_1 : cm_emit_plan_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_plan_entail_wit_1_split_goal_spatial.
  - Goal_apply proof_of_cm_emit_plan_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_cm_emit_plan_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_cm_emit_plan_return_wit_1_split_goal_spatial : cm_emit_plan_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_resolved_emitter_plan_rep.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial. exact PreH1.
Qed.

Lemma proof_of_cm_emit_plan_return_wit_1 : cm_emit_plan_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_plan_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_call_plan_entail_wit_1_split_goal_1 : cm_emit_call_plan_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_resolved_emitter_plan_rep.
  Intros_p Hbudget.
  dump_pre_spatial.
  rewrite Zlength_cons in Hbudget.
  pose proof (Zlength_nonneg tail).
  lia.
Qed.

Lemma proof_of_cm_emit_call_plan_entail_wit_1_split_goal_2 : cm_emit_call_plan_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_resolved_emitter_plan_rep.
  Intros_p Hbudget.
  dump_pre_spatial.
  rewrite Zlength_cons in Hbudget.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma proof_of_cm_emit_call_plan_entail_wit_1_split_goal_spatial : cm_emit_call_plan_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cm_emit_call_plan_entail_wit_1 : cm_emit_call_plan_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_call_plan_entail_wit_1_split_goal_spatial.
  - Goal_apply proof_of_cm_emit_call_plan_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_cm_emit_call_plan_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_cm_emit_call_plan_return_wit_1_split_goal_spatial : cm_emit_call_plan_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_resolved_emitter_plan_rep.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial. exact PreH1.
Qed.

Lemma proof_of_cm_emit_call_plan_return_wit_1 : cm_emit_call_plan_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_call_plan_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_normalize_plan_entail_wit_1_split_goal_1 : cm_emit_normalize_plan_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_resolved_emitter_plan_rep.
  Intros_p Hbudget.
  dump_pre_spatial.
  exact (proj1 (cm_plan_fragment_capacity done (cm_char_normalize_code model_ty) tail capacity Hbudget)).
Qed.

Lemma proof_of_cm_emit_normalize_plan_entail_wit_1_split_goal_2 : cm_emit_normalize_plan_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_resolved_emitter_plan_rep.
  Intros_p Hbudget.
  dump_pre_spatial.
  exact (proj2 (cm_plan_fragment_capacity done (cm_char_normalize_code model_ty) tail capacity Hbudget)).
Qed.

Lemma proof_of_cm_emit_normalize_plan_entail_wit_1_split_goal_spatial : cm_emit_normalize_plan_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cm_emit_normalize_plan_entail_wit_1 : cm_emit_normalize_plan_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_cm_emit_normalize_plan_entail_wit_1_split_goal_spatial ty_pre emitter_pre model_ty capacity out tail done p policy PreH1 PreH2).
  - Goal_apply (proof_of_cm_emit_normalize_plan_entail_wit_1_split_goal_1 ty_pre emitter_pre model_ty capacity out tail done p policy PreH1 PreH2).
  - Goal_apply (proof_of_cm_emit_normalize_plan_entail_wit_1_split_goal_2 ty_pre emitter_pre model_ty capacity out tail done p policy PreH1 PreH2).
Qed.

Lemma proof_of_cm_emit_normalize_plan_return_wit_1_split_goal_spatial : cm_emit_normalize_plan_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_resolved_emitter_plan_rep.
  split_pure_spatial.
  - cancel (cm_resolved_emitter_rep policy p emitter_pre out capacity (done ++ cm_char_normalize_code model_ty)).
  - dump_pre_spatial. exact PreH1.
Qed.

Lemma proof_of_cm_emit_normalize_plan_return_wit_1 : cm_emit_normalize_plan_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply (proof_of_cm_emit_normalize_plan_return_wit_1_split_goal_spatial ty_pre emitter_pre model_ty capacity out tail done p policy PreH1 PreH2 PreH3 PreH4).
Qed.

Lemma proof_of_cm_emit_load_plan_entail_wit_1_split_goal_1 : cm_emit_load_plan_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_resolved_emitter_plan_rep.
  Intros_p Hbudget.
  dump_pre_spatial.
  exact (proj1 (cm_plan_fragment_capacity done (cm_load_code model_ty) tail capacity Hbudget)).
Qed.

Lemma proof_of_cm_emit_load_plan_entail_wit_1_split_goal_2 : cm_emit_load_plan_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_resolved_emitter_plan_rep.
  Intros_p Hbudget.
  dump_pre_spatial.
  exact (proj2 (cm_plan_fragment_capacity done (cm_load_code model_ty) tail capacity Hbudget)).
Qed.

Lemma proof_of_cm_emit_load_plan_entail_wit_1_split_goal_spatial : cm_emit_load_plan_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cm_emit_load_plan_entail_wit_1 : cm_emit_load_plan_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_load_plan_entail_wit_1_split_goal_spatial.
  - Goal_apply proof_of_cm_emit_load_plan_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_cm_emit_load_plan_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_cm_emit_load_plan_return_wit_1_split_goal_spatial : cm_emit_load_plan_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_resolved_emitter_plan_rep.
  split_pure_spatial.
  - cancel (cm_resolved_emitter_rep policy p emitter_pre out capacity (done ++ cm_load_code model_ty)).
  - dump_pre_spatial. exact PreH1.
Qed.

Lemma proof_of_cm_emit_load_plan_return_wit_1 : cm_emit_load_plan_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_load_plan_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_store_plan_entail_wit_1_split_goal_1 : cm_emit_store_plan_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_resolved_emitter_plan_rep.
  Intros_p Hbudget.
  dump_pre_spatial.
  exact (proj1 (cm_plan_fragment_capacity done (cm_store_code model_ty) tail capacity Hbudget)).
Qed.

Lemma proof_of_cm_emit_store_plan_entail_wit_1_split_goal_2 : cm_emit_store_plan_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_resolved_emitter_plan_rep.
  Intros_p Hbudget.
  dump_pre_spatial.
  exact (proj2 (cm_plan_fragment_capacity done (cm_store_code model_ty) tail capacity Hbudget)).
Qed.

Lemma proof_of_cm_emit_store_plan_entail_wit_1_split_goal_spatial : cm_emit_store_plan_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cm_emit_store_plan_entail_wit_1 : cm_emit_store_plan_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_store_plan_entail_wit_1_split_goal_spatial.
  - Goal_apply proof_of_cm_emit_store_plan_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_cm_emit_store_plan_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_cm_emit_store_plan_return_wit_1_split_goal_spatial : cm_emit_store_plan_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_resolved_emitter_plan_rep.
  split_pure_spatial.
  - cancel (cm_resolved_emitter_rep policy p emitter_pre out capacity (done ++ cm_store_code model_ty)).
  - dump_pre_spatial. exact PreH1.
Qed.

Lemma proof_of_cm_emit_store_plan_return_wit_1 : cm_emit_store_plan_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_store_plan_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_fp_address_plan_entail_wit_1_split_goal_1 : cm_emit_fp_address_plan_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_resolved_emitter_plan_rep.
  Intros_p Hbudget.
  dump_pre_spatial.
  exact (proj1 (cm_plan_fragment_capacity done (cm_fp_relative_address_code offset_pre) tail capacity Hbudget)).
Qed.

Lemma proof_of_cm_emit_fp_address_plan_entail_wit_1_split_goal_2 : cm_emit_fp_address_plan_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_resolved_emitter_plan_rep.
  Intros_p Hbudget.
  dump_pre_spatial.
  exact (proj2 (cm_plan_fragment_capacity done (cm_fp_relative_address_code offset_pre) tail capacity Hbudget)).
Qed.

Lemma proof_of_cm_emit_fp_address_plan_entail_wit_1_split_goal_spatial : cm_emit_fp_address_plan_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cm_emit_fp_address_plan_entail_wit_1 : cm_emit_fp_address_plan_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply (proof_of_cm_emit_fp_address_plan_entail_wit_1_split_goal_spatial offset_pre emitter_pre capacity out tail done p policy).
  - Goal_apply (proof_of_cm_emit_fp_address_plan_entail_wit_1_split_goal_1 offset_pre emitter_pre capacity out tail done p policy).
  - Goal_apply (proof_of_cm_emit_fp_address_plan_entail_wit_1_split_goal_2 offset_pre emitter_pre capacity out tail done p policy).
Qed.

Lemma proof_of_cm_emit_fp_address_plan_return_wit_1_split_goal_spatial : cm_emit_fp_address_plan_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_resolved_emitter_plan_rep.
  split_pure_spatial.
  - cancel (cm_resolved_emitter_rep policy p emitter_pre out capacity (done ++ cm_fp_relative_address_code offset_pre)).
  - dump_pre_spatial. exact PreH1.
Qed.

Lemma proof_of_cm_emit_fp_address_plan_return_wit_1 : cm_emit_fp_address_plan_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply (proof_of_cm_emit_fp_address_plan_return_wit_1_split_goal_spatial offset_pre emitter_pre capacity out tail done p policy PreH1 PreH2).
Qed.

Lemma proof_of_cm_emit_temp_store_plan_entail_wit_1_split_goal_1 : cm_emit_temp_store_plan_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_resolved_emitter_plan_rep.
  Intros_p Hbudget.
  dump_pre_spatial.
  exact (proj1 (cm_plan_fragment_capacity done (cm_temp_store_code policy p fid temp_pre) tail capacity Hbudget)).
Qed.

Lemma proof_of_cm_emit_temp_store_plan_entail_wit_1_split_goal_2 : cm_emit_temp_store_plan_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_resolved_emitter_plan_rep.
  Intros_p Hbudget.
  dump_pre_spatial.
  exact (proj2 (cm_plan_fragment_capacity done (cm_temp_store_code policy p fid temp_pre) tail capacity Hbudget)).
Qed.

Lemma proof_of_cm_emit_temp_store_plan_entail_wit_1_split_goal_spatial : cm_emit_temp_store_plan_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_resolved_emitter_plan_rep.
  Intros_p Hbudget.
  cancel.
Qed.

Lemma proof_of_cm_emit_temp_store_plan_entail_wit_1 : cm_emit_temp_store_plan_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_temp_store_plan_entail_wit_1_split_goal_spatial.
  - Goal_apply proof_of_cm_emit_temp_store_plan_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_cm_emit_temp_store_plan_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_cm_emit_temp_store_plan_return_wit_1_split_goal_spatial : cm_emit_temp_store_plan_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_resolved_emitter_plan_rep.
  split_pure_spatial.
  - cancel.
  - split_pures.
    dump_pre_spatial. exact PreH9.
Qed.

Lemma proof_of_cm_emit_temp_store_plan_return_wit_1 : cm_emit_temp_store_plan_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_temp_store_plan_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_temp_load_plan_entail_wit_1_split_goal_1 : cm_emit_temp_load_plan_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_resolved_emitter_plan_rep.
  Intros_p Hbudget.
  dump_pre_spatial.
  exact (proj1 (cm_plan_fragment_capacity done (cm_temp_load_code policy p fid temp_pre) tail capacity Hbudget)).
Qed.

Lemma proof_of_cm_emit_temp_load_plan_entail_wit_1_split_goal_2 : cm_emit_temp_load_plan_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_resolved_emitter_plan_rep.
  Intros_p Hbudget.
  dump_pre_spatial.
  exact (proj2 (cm_plan_fragment_capacity done (cm_temp_load_code policy p fid temp_pre) tail capacity Hbudget)).
Qed.

Lemma proof_of_cm_emit_temp_load_plan_entail_wit_1_split_goal_spatial : cm_emit_temp_load_plan_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_resolved_emitter_plan_rep.
  Intros_p Hbudget.
  cancel.
Qed.

Lemma proof_of_cm_emit_temp_load_plan_entail_wit_1 : cm_emit_temp_load_plan_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_temp_load_plan_entail_wit_1_split_goal_spatial.
  - Goal_apply proof_of_cm_emit_temp_load_plan_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_cm_emit_temp_load_plan_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_cm_emit_temp_load_plan_return_wit_1_split_goal_spatial : cm_emit_temp_load_plan_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_resolved_emitter_plan_rep.
  split_pure_spatial.
  - cancel.
  - split_pures.
    dump_pre_spatial. exact PreH9.
Qed.

Lemma proof_of_cm_emit_temp_load_plan_return_wit_1 : cm_emit_temp_load_plan_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_temp_load_plan_return_wit_1_split_goal_spatial.
Qed.

