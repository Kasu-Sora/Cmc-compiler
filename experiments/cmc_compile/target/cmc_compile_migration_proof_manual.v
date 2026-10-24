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
From SimpleC.EE.QCP_demos_human Require Import cmc_compile_migration_goal.
From SimpleC.EE.QCP_demos_human Require Import cmc_compile_migration_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.cmc_compile_migration_lib.
Local Open Scope sac.

Lemma proof_of_cmc_compile_entail_wit_1 : cmc_compile_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_program_rep, cm_program_heap_rep, cm_output_pre.
  Intros functions ops imms bytes old_code old_data old_entry.
  unfold cm_program_context_rep.
  Intros structs globals strings.
  match goal with H : cm_semantic_wf_program _ _ |- _ =>
    pose proof H as Hwf; unfold cm_semantic_wf_program in Hwf
  end.
  pose proof (proj1 Hwf) as Htyped.
  pose proof (cmc_data_ready_from_typed _ _ Htyped) as Hdata.
  unfold cm_concrete_data_ready in Hdata.
  destruct Hdata as [Hg [Hgw [Hs [Hgpos [Hspos [Hsize Hlen]]]]]].
  pose proof (cmc_structs_ready_from_typed _ _ Htyped) as Hstructs.
  pose proof (cm_concrete_code_ready_from_wf _ _ _ Hwf) as Hcode.
  pose proof (cm_concrete_functions_ready_from_wf _ _ _ Hwf) as Hfunctions.
  prop_apply_p (store_int_range (&(output_pre # "cm_output" ->ₛ "code_capacity")) code_capacity).
  prop_apply_p (store_int_range (&(output_pre # "cm_output" ->ₛ "data_capacity")) data_capacity).
  Intros.
  Exists old_entry old_data old_code bytes imms ops functions.
  Exists structs globals strings.
  entailer_with ltac:(eauto; int_auto).
Qed. 

Lemma proof_of_cmc_compile_entail_wit_2 : cmc_compile_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hcounts : cm_functions_counts_representable (cm_source_function_policy sp) p (cm_program_functions p) 0).
  { unfold cm_wf_program, cm_codegen_admissible, cm_codegen_counts_representable in *. tauto. }
  pose proof (cm_functions_length_bound__model_length_bound _ _ _ _ Hcounts) as Hlength.
  pose proof (Zlength_nonneg (cm_program_functions p)) as Hnonneg.
  assert (Hcodepos : 0 < code_capacity).
  { unfold cm_model_code_length in *. lia. }
  assert (Hdatapos : 0 < data_capacity) by lia.
  assert (Hcodeb : (Z.eqb code_capacity 0) = false) by (apply Z.eqb_neq; lia).
  assert (Hdatab : (Z.eqb data_capacity 0) = false) by (apply Z.eqb_neq; lia).
  unfold cm_undef_int_buffer, cm_undef_int64_buffer, cm_undef_uint8_buffer.
  rewrite Hcodeb, Hdatab.
  Intros.
  Exists functions_ptr_2 data_ptr_2 imms_ptr_2 ops_ptr_2.
  rewrite (IntArray.seg_empty ops_ptr_2 0 0), (Int64Array.seg_empty imms_ptr_2 0 0), (UCharArray.seg_empty data_ptr_2 0 0).
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg ops_ptr_2 code_capacity).
  sep_apply_l_atomic (Int64Array.undef_full_to_undef_seg imms_ptr_2 code_capacity).
  sep_apply_l_atomic (UCharArray.undef_full_to_undef_seg data_ptr_2 data_capacity).
  unfold cm_i32_code_count in *.
  entailer_with ltac:(eauto; lia).
Qed. 

Lemma proof_of_cmc_compile_entail_wit_3 : cmc_compile_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists functions_ptr_2 data_ptr_2.
  unfold cm_resolved_emitter_plan_rep, cm_resolved_emitter_rep.
  Exists (@nil tvm_inst).
  unfold cm_emitter_rep.
  Exists ops_ptr imms_ptr.
  cbn [cm_patch_code cm_rep_ops cm_rep_imms map].
  rewrite app_nil_r, !Zlength_nil, cm_compile_model_length__emitter_transitions.
  split_pure_spatial.
  - repeat progress cancel.
    rewrite (eval_addr (RE_addr_of (LE_var "emitter")) (FET_alias "cm_emitter")).
    repeat progress cancel.
  - split_pures; dump_pre_spatial;
      first [assumption | reflexivity | lia | repeat split; auto; lia].
Qed.

Lemma proof_of_cmc_compile_entail_wit_4 : cmc_compile_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  cbn [app].
  unfold cm_resolved_emitter_plan_rep.
  Intros_p Hbudget.
  Exists functions_ptr_2 data_ptr_2.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_cmc_compile_entail_wit_5 : cmc_compile_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_program_context_rep.
  Intros structs globals strings.
  Exists functions_ptr_2 strings globals structs data_ptr_2.
  entailer_with ltac:(eauto; lia).
Qed. 

Lemma proof_of_cmc_compile_entail_wit_6 : cmc_compile_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_emitter_rep.
  Intros ops imms.
  assert (Hlength : Zlength (cm_rep_ops (cm_model_code (cm_source_function_policy sp) p)) = code_length).
  { unfold cm_rep_ops.
    rewrite Zlength_correct, map_length, <- Zlength_correct.
    rewrite cm_compile_model_length__emitter_transitions. lia. }
  rewrite Hlength.
  assert (Hdata : 8 + cm_rep_globals_size (cm_program_globals p) +
    cm_rep_strings_size (cm_program_strings p) = data_length) by lia.
  rewrite Hdata.
  Exists functions_ptr_2 imms ops.
  unfold cm_program_context_rep.
  Exists structs_ptr globals_ptr strings_ptr.
  unfold cm_model_data_bytes.
  change (zeros 8) with (repeat 0 8).
  rewrite app_assoc.
  split_pure_spatial.
  - repeat progress cancel.
    rewrite (eval_addr (RE_addr_of (LE_var "emitter")) (FET_alias "cm_emitter")).
    repeat progress cancel.
  - split_pures; dump_pre_spatial;
      first [assumption | reflexivity | lia | tauto].
Qed.

Lemma proof_of_cmc_compile_return_wit_1_split_goal_spatial : cmc_compile_return_wit_1_split_goal_spatial.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 sep_apply_l_atomic (cm_compile_int_prefix__success_result ops_ptr code_capacity code_length (cm_rep_ops (cm_model_code (cm_source_function_policy sp) p)) PreH13 (conj PreH18 PreH19)).
 sep_apply_l_atomic (cm_compile_int64_prefix__success_result imms_ptr code_capacity code_length (cm_rep_imms (cm_model_code (cm_source_function_policy sp) p)) PreH14 (conj PreH18 PreH19)).
 sep_apply_l_atomic (cm_compile_uint8_prefix__success_result data_ptr data_capacity data_length (cm_model_data_bytes p) PreH15 (conj PreH20 PreH21)).
 unfold cm_program_rep, cm_program_heap_rep, cm_output_ok.
 Exists functions_ptr ops_ptr imms_ptr data_ptr.
 rewrite PreH16, PreH17.
 split_pure_spatial.
 - repeat progress cancel.
 - split_pures; dump_pre_spatial; try lia; try assumption.
   split; [exact PreH12 |].
   split; [lia |].
   split; [lia |].
   intros. eapply cmc_compile_success_bridge; eauto.
Qed.

Lemma proof_of_cmc_compile_return_wit_1 : cmc_compile_return_wit_1.
Proof.
 aggressive_pre_process.
 Goal_apply proof_of_cmc_compile_return_wit_1_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_compile_return_wit_2_split_goal_spatial : cmc_compile_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_program_rep, cm_program_heap_rep, cm_output_capacity.
  Exists functions_ptr ops_ptr imms_ptr data_ptr.
  subst retval retval_2.
  split_pure_spatial.
  - repeat (progress cancel).
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_cmc_compile_return_wit_2 : cmc_compile_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_compile_return_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_cmc_compile_return_wit_3_split_goal_spatial : cmc_compile_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_program_rep, cm_program_heap_rep, cm_output_capacity.
  Exists functions_ptr ops_ptr imms_ptr data_ptr.
  subst retval retval_2.
  split_pure_spatial.
  - repeat (progress cancel).
  - split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_cmc_compile_return_wit_3 : cmc_compile_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_compile_return_wit_3_split_goal_spatial.
Qed.

