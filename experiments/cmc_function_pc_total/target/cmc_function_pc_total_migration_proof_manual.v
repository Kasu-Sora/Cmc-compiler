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
From SimpleC.EE.QCP_demos_human Require Import cmc_function_pc_total_migration_goal.
From SimpleC.EE.QCP_demos_human Require Import cmc_function_pc_total_migration_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.cmc_function_pc_total_migration_lib.
Local Open Scope sac.

Lemma proof_of_cmc_function_prefix_total_safety_wit_4_split_goal_1 : cmc_function_prefix_total_safety_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: unfold cm_i32_code_count in *.
  all: cbn in *; lia.
Qed.

Lemma proof_of_cmc_function_prefix_total_safety_wit_4_split_goal_2 : cmc_function_prefix_total_safety_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: cbn in *; lia.
Qed.

Lemma proof_of_cmc_function_prefix_total_safety_wit_4 : cmc_function_prefix_total_safety_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_function_prefix_total_safety_wit_4_split_goal_1.
  - Goal_apply proof_of_cmc_function_prefix_total_safety_wit_4_split_goal_2.
Qed.

Lemma proof_of_cmc_function_prefix_total_safety_wit_6_split_goal_1 : cmc_function_prefix_total_safety_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (cm_function_prefix_total_bounds policy rest p
    (target_pre - (index_pre + 1))) as Hprefix.
  rewrite <- PreH4 in Hprefix.
  rewrite PreH12 in PreH23.
  cbn [cm_functions_counts_representable] in PreH23.
  destruct PreH23 as [Hsize _].
  unfold cm_i32_code_count in Hsize.
  cbn [cm_functions_code_size] in Hsize.
  dump_pre_spatial.
  rewrite PreH25, PreH8.
  lia.
Qed.

Lemma proof_of_cmc_function_prefix_total_safety_wit_6_split_goal_2 : cmc_function_prefix_total_safety_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_i32_code_count in PreH9, PreH26.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_cmc_function_prefix_total_safety_wit_6 : cmc_function_prefix_total_safety_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_function_prefix_total_safety_wit_6_split_goal_1.
  - Goal_apply proof_of_cmc_function_prefix_total_safety_wit_6_split_goal_2.
Qed.

Lemma proof_of_cmc_function_prefix_total_entail_wit_1 : cmc_function_prefix_total_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct functions as [|f rest].
  - unfold cm_function_list_rep.
    cbn [cm_function_header_list_rep cm_function_body_list_rep].
    Intros bs. exfalso; tauto.
  - sep_apply_l_atomic (proj1 (cm_function_list_cons__prefix_open fn_pre f rest)).
    Intros bp np.
    Exists bp np f rest.
    split_pure_spatial.
    + cancel (cm_program_context_rep program_pre p functions_ptr).
      cancel (cm_function_context_rep fn_pre f bp np).
      cancel (cm_stmt_rep bp (cm_function_body f)).
      cancel (cm_function_list_rep np rest).
    + cbn [cm_functions_counts_representable] in *.
      cbn [cm_concrete_functions_ready] in *.
      unfold cm_concrete_function_ready in *.
      split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_cmc_function_prefix_total_entail_wit_2 : cmc_function_prefix_total_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_function_context_rep.
  Intros params locals.
  Exists np_2 bp_2 locals params f_2 rest_2.
  split_pure_spatial.
  - cancel (cm_program_context_rep program_pre p functions_ptr).
    cancel (cm_stmt_rep bp_2 (cm_function_body f_2)).
    cancel (cm_function_list_rep np_2 rest_2).
    cancel (cm_slot_list_rep params (cm_function_params f_2)).
    cancel (cm_slot_list_rep locals (cm_function_locals f_2)).
    cancel.
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_cmc_function_prefix_total_return_wit_1_split_goal_1 : cmc_function_prefix_total_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (cm_function_prefix_total_bounds policy rest p (target_pre - (index_pre + 1))) as Hbounds.
  rewrite <- PreH6 in Hbounds.
  rewrite PreH14 in PreH25.
  cbn [cm_functions_counts_representable] in PreH25.
  destruct PreH25 as [Hsize _].
  cbn [cm_functions_code_size] in Hsize.
  unfold cm_i32_code_count in *.
  rewrite <- PreH10 in Hbounds.
  rewrite <- PreH27 in Hsize.
  lia.
Qed.

Lemma proof_of_cmc_function_prefix_total_return_wit_1_split_goal_2 : cmc_function_prefix_total_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite PreH14, PreH27, PreH10.
  cbn [cm_function_prefix].
  assert (Hne : Z.eqb (target_pre - index_pre) 0 = false) by (apply Z.eqb_neq; lia).
  rewrite Hne.
  rewrite PreH14 in PreH23.
  rewrite <- PreH23.
  replace (target_pre - index_pre - 1) with (target_pre - (index_pre + 1)) by lia.
  reflexivity.
Qed.

Lemma proof_of_cmc_function_prefix_total_return_wit_1_split_goal_spatial : cmc_function_prefix_total_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH14.
  cancel (cm_program_context_rep program_pre p functions_ptr).
  sep_apply_r_atomic (proj2 (cm_function_list_cons__prefix_results fn_pre f rest)).
  Exists bp np.
  unfold cm_function_context_rep.
  Exists pp lp.
  split_pure_spatial.
  - cancel. cancel (cm_slot_list_rep lp (cm_function_locals f)). reflexivity.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_cmc_function_prefix_total_return_wit_1 : cmc_function_prefix_total_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_function_prefix_total_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_cmc_function_prefix_total_return_wit_1_split_goal_1.
  - Goal_apply proof_of_cmc_function_prefix_total_return_wit_1_split_goal_2.
Qed.

Lemma proof_of_cmc_function_prefix_total_return_wit_2_split_goal_1 : cmc_function_prefix_total_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: unfold cm_i32_code_count; lia.
Qed.

Lemma proof_of_cmc_function_prefix_total_return_wit_2_split_goal_2 : cmc_function_prefix_total_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: rewrite Z.sub_diag; destruct functions; reflexivity.
Qed.

Lemma proof_of_cmc_function_prefix_total_return_wit_2 : cmc_function_prefix_total_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_function_prefix_total_return_wit_2_split_goal_1.
  - Goal_apply proof_of_cmc_function_prefix_total_return_wit_2_split_goal_2.
Qed.

Lemma proof_of_cmc_function_prefix_total_return_wit_3_split_goal_1 : cmc_function_prefix_total_return_wit_3_split_goal_1.
Proof. Abort.

Lemma proof_of_cmc_function_prefix_total_return_wit_3_split_goal_2 : cmc_function_prefix_total_return_wit_3_split_goal_2.
Proof. Abort.

Lemma proof_of_cmc_function_prefix_total_return_wit_3 : cmc_function_prefix_total_return_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct functions as [|f rest].
  - split_pure_spatial.
    + cancel (cm_program_context_rep program_pre p functions_ptr).
      cancel (cm_function_list_rep fn_pre nil).
    + split_pures; dump_pre_spatial; try assumption;
        cbn [cm_function_prefix]; unfold cm_i32_code_count; lia.
  - unfold cm_function_list_rep.
    cbn [cm_function_header_list_rep].
    Intros bs bp np bt. exfalso; tauto.
Qed.

Lemma proof_of_cmc_function_prefix_total_partial_solve_wit_2_pure_split_goal_1 : cmc_function_prefix_total_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: rewrite PreH11, Zlength_cons in PreH20; lia.
Qed.

Lemma proof_of_cmc_function_prefix_total_partial_solve_wit_2_pure_split_goal_2 : cmc_function_prefix_total_partial_solve_wit_2_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: rewrite PreH11, Zlength_cons in PreH21; lia.
Qed.

Lemma proof_of_cmc_function_prefix_total_partial_solve_wit_2_pure : cmc_function_prefix_total_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_function_prefix_total_partial_solve_wit_2_pure_split_goal_1.
  - Goal_apply proof_of_cmc_function_prefix_total_partial_solve_wit_2_pure_split_goal_2.
Qed.

Lemma proof_of_cmc_function_pc_total_safety_wit_2_split_goal_1 : cmc_function_pc_total_safety_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (proj1 (proj2 PreH1)) as Hmodel.
  unfold cm_model_code_length in Hmodel.
  pose proof (cm_function_prefix_total_bounds policy (cm_program_functions p) p
    (target_pre - 0)) as Hprefix.
  rewrite Z.sub_diag in Hprefix.
  dump_pre_spatial.
  rewrite PreH8.
  lia.
Qed.

Lemma proof_of_cmc_function_pc_total_safety_wit_2_split_goal_2 : cmc_function_pc_total_safety_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_i32_code_count in PreH9.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_cmc_function_pc_total_safety_wit_2 : cmc_function_pc_total_safety_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_function_pc_total_safety_wit_2_split_goal_1.
  - Goal_apply proof_of_cmc_function_pc_total_safety_wit_2_split_goal_2.
Qed.

Lemma proof_of_cmc_function_pc_total_entail_wit_1 : cmc_function_pc_total_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hcounts : cm_functions_counts_representable policy p (cm_program_functions p) 0).
  { unfold cm_wf_program, cm_codegen_admissible, cm_codegen_counts_representable in *. tauto. }
  assert (Hbound : Zlength (cm_program_functions p) <= INT_MAX).
  { pose proof (cm_functions_length_bound__model_length_bound policy p
      (cm_program_functions p) 0 Hcounts).
    unfold cm_wf_program, cm_codegen_admissible, cm_model_code_length in *.
    lia. }
  assert (Hstructs : cm_rep_structs_safe (cm_program_structs p)).
  { unfold cm_concrete_code_ready, cm_concrete_structs_ready in *. tauto. }
  assert (Hready : cm_concrete_functions_ready policy p 0 (cm_program_functions p)).
  { unfold cm_concrete_code_ready in *. tauto. }
  unfold cm_program_context_rep.
  Intros struct_ptr global_ptr string_ptr.
  Exists string_ptr global_ptr struct_ptr.
  split_pure_spatial.
  - repeat (progress cancel).
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_cmc_function_pc_total_entail_wit_2_split_goal_spatial : cmc_function_pc_total_entail_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_program_context_rep.
  Exists sp gp tp.
  split_pure_spatial.
  - repeat (progress cancel).
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cmc_function_pc_total_entail_wit_2 : cmc_function_pc_total_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_function_pc_total_entail_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_cmc_function_pc_total_return_wit_1_split_goal_1 : cmc_function_pc_total_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros.
  pose proof (proj1 (proj2 PreH1)) as Hmodel.
  unfold cm_model_code_length in Hmodel.
  pose proof (cm_function_prefix_total_bounds policy (cm_program_functions p) p (target_pre - 0)) as Hbounds.
  rewrite Z.sub_diag in Hbounds.
  rewrite <- PreH8 in Hbounds.
  unfold cm_i32_code_count.
  lia.
Qed.

Lemma proof_of_cmc_function_pc_total_return_wit_1_split_goal_2 : cmc_function_pc_total_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  intros.
  rewrite PreH8, Z.sub_0_r.
  unfold cm_function_pc.
  reflexivity.
Qed.

Lemma proof_of_cmc_function_pc_total_return_wit_1 : cmc_function_pc_total_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_function_pc_total_return_wit_1_split_goal_1.
  - Goal_apply proof_of_cmc_function_pc_total_return_wit_1_split_goal_2.
Qed.

