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
From SimpleC.EE.QCP_demos_human Require Import cmc_emit_functions_migration_goal.
From SimpleC.EE.QCP_demos_human Require Import cmc_emit_functions_migration_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.cmc_emit_functions_migration_lib.
Local Open Scope sac.

Lemma proof_of_cmc_emit_functions_safety_wit_2_split_goal_1 : cmc_emit_functions_safety_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_i32_code_count in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_cmc_emit_functions_safety_wit_2_split_goal_2 : cmc_emit_functions_safety_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_i32_code_count in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_cmc_emit_functions_safety_wit_2 : cmc_emit_functions_safety_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_functions_safety_wit_2_split_goal_1.
  - Goal_apply proof_of_cmc_emit_functions_safety_wit_2_split_goal_2.
Qed. 

Lemma proof_of_cmc_emit_functions_safety_wit_3_split_goal_1 : cmc_emit_functions_safety_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_i32_code_count in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_cmc_emit_functions_safety_wit_3_split_goal_2 : cmc_emit_functions_safety_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_i32_code_count in *.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_cmc_emit_functions_safety_wit_3 : cmc_emit_functions_safety_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_functions_safety_wit_3_split_goal_1.
  - Goal_apply proof_of_cmc_emit_functions_safety_wit_3_split_goal_2.
Qed. 

Lemma proof_of_cmc_emit_functions_return_wit_1_split_goal_spatial : cmc_emit_functions_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct functions as [|f fs].
  - cbn [cm_emit_functions app]. rewrite app_nil_r. cancel.
  - unfold cm_function_list_rep at 1. Intros bs.
    cbn [cm_function_header_list_rep]. Intros b n bt.
    exfalso; tauto.
Qed.

Lemma proof_of_cmc_emit_functions_return_wit_1 : cmc_emit_functions_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_functions_return_wit_1_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_functions_return_wit_2_split_goal_spatial : cmc_emit_functions_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  cancel (cm_program_context_rep program_pre p functions_ptr).
  cancel (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (done ++ cm_emit_functions policy p fid_pre functions) tail).
  rewrite PreH1 at 2.
  unfold cm_function_list_rep. Intros bs. Exists (bp :: bs).
  cbn [cm_function_header_list_rep cm_function_body_list_rep].
  Exists bp np bs bp bs.
  split_pure_spatial; [repeat progress cancel | split_pures; dump_pre_spatial; auto; try lia].
Qed.

Lemma proof_of_cmc_emit_functions_return_wit_2 : cmc_emit_functions_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_functions_return_wit_2_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_functions_partial_solve_wit_5_pure_split_goal_1 : cmc_emit_functions_partial_solve_wit_5_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cmc_emit_functions_partial_solve_wit_5_pure : cmc_emit_functions_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_functions_partial_solve_wit_5_pure_split_goal_1.
Qed. 

Lemma proof_of_cmc_emit_functions_partial_solve_wit_10_pure_split_goal_1 : cmc_emit_functions_partial_solve_wit_10_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial; reflexivity.
Qed.

Lemma proof_of_cmc_emit_functions_partial_solve_wit_10_pure : cmc_emit_functions_partial_solve_wit_10_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_functions_partial_solve_wit_10_pure_split_goal_1.
Qed. 

Lemma proof_of_cmc_emit_functions_which_implies_wit_1 : cmc_emit_functions_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct functions as [|f fs].
  - unfold cm_function_list_rep. Intros bs.
    cbn [cm_function_header_list_rep]. Intros.
    exfalso; tauto.
  - assert (Hhead : f = cm_function_at policy fid (cm_program_functions p)).
    { cbn [cm_concrete_functions_ready] in PreH2. unfold cm_concrete_function_ready in PreH2. tauto. }
    subst f. unfold cm_function_list_rep at 1. Intros bs.
    cbn [cm_function_header_list_rep cm_function_body_list_rep].
    Intros bp np bt bp' bt'.
    assert (Hsame : bp = bp' /\ bt = bt') by (split; congruence).
    destruct Hsame as [-> ->].
    Exists bp' np. unfold cm_emit_functions_tail; cbn [tl].
    unfold cm_function_list_rep. Exists bt'.
    split_pure_spatial; [repeat progress cancel | split_pures; dump_pre_spatial; auto; try lia].
Qed. 

Lemma proof_of_cmc_emit_functions_which_implies_wit_2_split_goal_1 : cmc_emit_functions_which_implies_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH9 in PreH4.
  cbn [cm_concrete_functions_ready] in PreH4.
  unfold cm_concrete_function_ready in PreH4.
  tauto.
Qed.

Lemma proof_of_cmc_emit_functions_which_implies_wit_2_split_goal_2 : cmc_emit_functions_which_implies_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH9 in PreH4.
  cbn [cm_concrete_functions_ready] in PreH4.
  unfold cm_concrete_function_ready in PreH4.
  rewrite PreH3.
  tauto.
Qed.

Lemma proof_of_cmc_emit_functions_which_implies_wit_2_split_goal_3 : cmc_emit_functions_which_implies_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH9 in PreH4.
  cbn [cm_concrete_functions_ready] in PreH4.
  unfold cm_concrete_function_ready in PreH4.
  tauto.
Qed.

Lemma proof_of_cmc_emit_functions_which_implies_wit_2_split_goal_4 : cmc_emit_functions_which_implies_wit_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH9 in PreH4.
  cbn [cm_concrete_functions_ready] in PreH4.
  unfold cm_concrete_function_ready in PreH4.
  tauto.
Qed.

Lemma proof_of_cmc_emit_functions_which_implies_wit_2_split_goal_5 : cmc_emit_functions_which_implies_wit_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH9 in PreH4.
  cbn [cm_concrete_functions_ready] in PreH4.
  unfold cm_concrete_function_ready in PreH4.
  tauto.
Qed.

Lemma proof_of_cmc_emit_functions_which_implies_wit_2_split_goal_6 : cmc_emit_functions_which_implies_wit_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH9 in PreH4.
  cbn [cm_concrete_functions_ready] in PreH4.
  unfold cm_concrete_function_ready in PreH4.
  tauto.
Qed.

Lemma proof_of_cmc_emit_functions_which_implies_wit_2_split_goal_7 : cmc_emit_functions_which_implies_wit_2_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH9 in PreH4.
  cbn [cm_concrete_functions_ready] in PreH4.
  unfold cm_concrete_function_ready in PreH4.
  tauto.
Qed.

Lemma proof_of_cmc_emit_functions_which_implies_wit_2_split_goal_8 : cmc_emit_functions_which_implies_wit_2_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH9 in PreH4.
  cbn [cm_concrete_functions_ready] in PreH4.
  unfold cm_concrete_function_ready in PreH4.
  tauto.
Qed.

Lemma proof_of_cmc_emit_functions_which_implies_wit_2_split_goal_9 : cmc_emit_functions_which_implies_wit_2_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH9 in PreH4.
  cbn [cm_concrete_functions_ready] in PreH4.
  unfold cm_concrete_function_ready in PreH4.
  tauto.
Qed.

Lemma proof_of_cmc_emit_functions_which_implies_wit_2_split_goal_10 : cmc_emit_functions_which_implies_wit_2_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH9 in PreH4.
  cbn [cm_concrete_functions_ready] in PreH4.
  unfold cm_concrete_function_ready in PreH4.
  tauto.
Qed.

Lemma proof_of_cmc_emit_functions_which_implies_wit_2_split_goal_11 : cmc_emit_functions_which_implies_wit_2_split_goal_11.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH9 in PreH4.
  cbn [cm_concrete_functions_ready] in PreH4.
  unfold cm_concrete_function_ready in PreH4.
  tauto.
Qed.

Lemma proof_of_cmc_emit_functions_which_implies_wit_2_split_goal_12 : cmc_emit_functions_which_implies_wit_2_split_goal_12.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH9 in PreH4.
  cbn [cm_concrete_functions_ready] in PreH4.
  unfold cm_concrete_function_ready in PreH4.
  rewrite PreH3.
  rewrite cm_emit_stmt_length__stmt_capacity.
  tauto.
Qed.

Lemma proof_of_cmc_emit_functions_which_implies_wit_2_split_goal_13 : cmc_emit_functions_which_implies_wit_2_split_goal_13.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH9 in PreH4.
  cbn [cm_concrete_functions_ready] in PreH4.
  unfold cm_concrete_function_ready in PreH4.
  rewrite PreH3.
  tauto.
Qed.

Lemma proof_of_cmc_emit_functions_which_implies_wit_2_split_goal_14 : cmc_emit_functions_which_implies_wit_2_split_goal_14.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH9 in PreH4.
  cbn [cm_concrete_functions_ready] in PreH4.
  unfold cm_concrete_function_ready in PreH4.
  rewrite PreH3.
  tauto.
Qed.

Lemma proof_of_cmc_emit_functions_which_implies_wit_2_split_goal_15 : cmc_emit_functions_which_implies_wit_2_split_goal_15.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH9 in PreH4.
  cbn [cm_concrete_functions_ready] in PreH4.
  unfold cm_concrete_function_ready in PreH4.
  tauto.
Qed.

Lemma proof_of_cmc_emit_functions_which_implies_wit_2_split_goal_16 : cmc_emit_functions_which_implies_wit_2_split_goal_16.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH9 in PreH4.
  cbn [cm_concrete_functions_ready] in PreH4.
  unfold cm_concrete_function_ready in PreH4.
  tauto.
Qed.

Lemma proof_of_cmc_emit_functions_which_implies_wit_2_split_goal_17 : cmc_emit_functions_which_implies_wit_2_split_goal_17.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH9 in PreH4.
  cbn [cm_concrete_functions_ready] in PreH4.
  unfold cm_concrete_function_ready in PreH4.
  tauto.
Qed.

Lemma proof_of_cmc_emit_functions_which_implies_wit_2_split_goal_18 : cmc_emit_functions_which_implies_wit_2_split_goal_18.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH9 in PreH4.
  cbn [cm_concrete_functions_ready] in PreH4.
  unfold cm_concrete_function_ready in PreH4.
  tauto.
Qed.

Lemma proof_of_cmc_emit_functions_which_implies_wit_2_split_goal_19 : cmc_emit_functions_which_implies_wit_2_split_goal_19.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH9 in PreH4.
  cbn [cm_concrete_functions_ready] in PreH4.
  unfold cm_concrete_function_ready in PreH4.
  tauto.
Qed.

Lemma proof_of_cmc_emit_functions_which_implies_wit_2 : cmc_emit_functions_which_implies_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_functions_which_implies_wit_2_split_goal_1.
  - Goal_apply proof_of_cmc_emit_functions_which_implies_wit_2_split_goal_2.
  - Goal_apply proof_of_cmc_emit_functions_which_implies_wit_2_split_goal_3.
  - Goal_apply proof_of_cmc_emit_functions_which_implies_wit_2_split_goal_4.
  - Goal_apply proof_of_cmc_emit_functions_which_implies_wit_2_split_goal_5.
  - Goal_apply proof_of_cmc_emit_functions_which_implies_wit_2_split_goal_6.
  - Goal_apply proof_of_cmc_emit_functions_which_implies_wit_2_split_goal_7.
  - Goal_apply proof_of_cmc_emit_functions_which_implies_wit_2_split_goal_8.
  - Goal_apply proof_of_cmc_emit_functions_which_implies_wit_2_split_goal_9.
  - Goal_apply proof_of_cmc_emit_functions_which_implies_wit_2_split_goal_10.
  - Goal_apply proof_of_cmc_emit_functions_which_implies_wit_2_split_goal_11.
  - Goal_apply proof_of_cmc_emit_functions_which_implies_wit_2_split_goal_12.
  - Goal_apply proof_of_cmc_emit_functions_which_implies_wit_2_split_goal_13.
  - Goal_apply proof_of_cmc_emit_functions_which_implies_wit_2_split_goal_14.
  - Goal_apply proof_of_cmc_emit_functions_which_implies_wit_2_split_goal_15.
  - Goal_apply proof_of_cmc_emit_functions_which_implies_wit_2_split_goal_16.
  - Goal_apply proof_of_cmc_emit_functions_which_implies_wit_2_split_goal_17.
  - Goal_apply proof_of_cmc_emit_functions_which_implies_wit_2_split_goal_18.
  - Goal_apply proof_of_cmc_emit_functions_which_implies_wit_2_split_goal_19.
Qed. 

Lemma proof_of_cmc_emit_functions_which_implies_wit_4_split_goal_spatial : cmc_emit_functions_which_implies_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (E : cm_emit_functions policy p fid_pre functions =
    cm_emit_function policy p fid_pre ++
    cm_emit_functions policy p (fid_pre + 1) (cm_emit_functions_tail functions)).
  { rewrite PreH1 at 1. reflexivity. }
  rewrite E.
  repeat rewrite <- app_assoc.
  cancel (cm_resolved_emitter_plan_rep policy p emitter out capacity done
    (cm_emit_function policy p fid_pre ++
      (cm_emit_functions policy p (fid_pre + 1) (cm_emit_functions_tail functions) ++ tail))).
Qed.

Lemma proof_of_cmc_emit_functions_which_implies_wit_4 : cmc_emit_functions_which_implies_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_functions_which_implies_wit_4_split_goal_spatial.
Qed. 

Lemma proof_of_cmc_emit_functions_which_implies_wit_5 : cmc_emit_functions_which_implies_wit_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_function_context_rep. Intros pp lp.
  Exists np_2 bp_2 lp pp.
  split_pure_spatial; [repeat progress cancel | split_pures; dump_pre_spatial; auto; try lia].
Qed. 

Lemma proof_of_cmc_emit_functions_which_implies_wit_6 : cmc_emit_functions_which_implies_wit_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists bp_2. unfold cm_function_context_rep.
  Exists pp lp. split_pure_spatial; [repeat progress cancel | split_pures; dump_pre_spatial; auto; try lia].
Qed. 

Lemma proof_of_cmc_emit_functions_which_implies_wit_7_split_goal_spatial : cmc_emit_functions_which_implies_wit_7_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (E : cm_emit_functions policy p fid_pre functions =
    cm_emit_function policy p fid_pre ++
    cm_emit_functions policy p (fid_pre + 1) (cm_emit_functions_tail functions)).
  { rewrite PreH1 at 1. reflexivity. }
  rewrite E.
  repeat rewrite <- app_assoc.
  cancel (cm_resolved_emitter_plan_rep policy p emitter out capacity
    (done ++ (cm_emit_function policy p fid_pre ++
      cm_emit_functions policy p (fid_pre + 1) (cm_emit_functions_tail functions))) tail).
Qed.

Lemma proof_of_cmc_emit_functions_which_implies_wit_7 : cmc_emit_functions_which_implies_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_functions_which_implies_wit_7_split_goal_spatial.
Qed. 

