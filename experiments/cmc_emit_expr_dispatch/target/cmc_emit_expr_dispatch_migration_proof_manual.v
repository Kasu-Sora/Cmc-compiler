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
From SimpleC.EE.QCP_demos_human Require Import cmc_emit_expr_dispatch_migration_goal.
From SimpleC.EE.QCP_demos_human Require Import cmc_emit_expr_dispatch_migration_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.cmc_emit_expr_dispatch_migration_lib.
Local Open Scope sac.

Lemma proof_of_cm_emit_leaf_expr_return_wit_1_split_goal_1 : cm_emit_leaf_expr_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(assumption).
Qed.

Lemma proof_of_cm_emit_leaf_expr_return_wit_1 : cm_emit_leaf_expr_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_leaf_expr_return_wit_1_split_goal_1.
Qed. 

Lemma proof_of_cm_emit_leaf_expr_return_wit_2_split_goal_1 : cm_emit_leaf_expr_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(assumption).
Qed.

Lemma proof_of_cm_emit_leaf_expr_return_wit_2 : cm_emit_leaf_expr_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_leaf_expr_return_wit_2_split_goal_1.
Qed. 

Lemma proof_of_cm_emit_leaf_expr_return_wit_3_split_goal_1 : cm_emit_leaf_expr_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(assumption).
Qed.

Lemma proof_of_cm_emit_leaf_expr_return_wit_3 : cm_emit_leaf_expr_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_leaf_expr_return_wit_3_split_goal_1.
Qed. 

Lemma proof_of_cm_emit_leaf_expr_return_wit_4_split_goal_1 : cm_emit_leaf_expr_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(assumption).
Qed.

Lemma proof_of_cm_emit_leaf_expr_return_wit_4 : cm_emit_leaf_expr_return_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_leaf_expr_return_wit_4_split_goal_1.
Qed. 

Lemma proof_of_cm_emit_leaf_expr_which_implies_wit_1 : cm_emit_leaf_expr_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn [cm_expr_rep]; unfold cm_expr_node, cm_expr_payload;
    Intros node_a node_b node_args; Exists node_args node_b node_a;
    (split_pure_spatial; [unfold cm_arg_list_rep; sepcon_assoc_change; cancel | split_pures; dump_pre_spatial; tauto]).
Qed. 

Lemma proof_of_cm_emit_leaf_expr_which_implies_wit_2 : cm_emit_leaf_expr_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e. destruct leaf; cbn [cm_leaf_source_expr cm_rep_expr_kind] in PreH3; try discriminate.
  pose proof PreH4 as Hinteger.
  cbn [cm_leaf_source_expr cm_expr_wf] in Hinteger.
  assert (Hty : cm_type_code_wf ty).
  { destruct Hinteger as [-> | ->]; exact I. }
  Exists n ty.
  split_pure_spatial.
  - cancel (cm_resolved_emitter_plan_rep policy p emitter out capacity done
      (cm_leaf_code_for p (CMLeafConst n ty) lvalue ++ tail)).
  - split_pures; dump_pre_spatial; auto.
Qed. 

Lemma proof_of_cm_emit_leaf_expr_which_implies_wit_3_split_goal_spatial : cm_emit_leaf_expr_which_implies_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn [cm_expr_rep]; unfold cm_expr_node, cm_expr_payload;
    Intros; Exists xa xb xargs;
    (split_pure_spatial; [unfold cm_arg_list_rep; sepcon_assoc_change; cancel | split_pures; dump_pre_spatial; tauto]).
Qed.

Lemma proof_of_cm_emit_leaf_expr_which_implies_wit_3 : cm_emit_leaf_expr_which_implies_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_leaf_expr_which_implies_wit_3_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_leaf_expr_which_implies_wit_4 : cm_emit_leaf_expr_which_implies_wit_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e. destruct leaf; cbn [cm_leaf_source_expr cm_rep_expr_kind] in PreH3; try discriminate.
  pose proof PreH5 as Hcounts.
  cbn [cm_leaf_source_expr cm_expr_counts_representable] in Hcounts.
  destruct Hcounts as [_ Hsid]. unfold cm_i32_code_count in Hsid.
  Exists sid ty.
  split_pure_spatial.
  - cancel (cm_resolved_emitter_plan_rep policy p emitter out capacity done
      (cm_leaf_code_for p (CMLeafString sid ty) lvalue ++ tail)).
  - split_pures; dump_pre_spatial; auto; cbn; lia.
Qed. 

Lemma proof_of_cm_emit_leaf_expr_which_implies_wit_5_split_goal_spatial : cm_emit_leaf_expr_which_implies_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn [cm_expr_rep]; unfold cm_expr_node, cm_expr_payload;
    Intros; Exists xa xb xargs;
    (split_pure_spatial; [unfold cm_arg_list_rep; sepcon_assoc_change; cancel | split_pures; dump_pre_spatial; tauto]).
Qed.

Lemma proof_of_cm_emit_leaf_expr_which_implies_wit_5 : cm_emit_leaf_expr_which_implies_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_leaf_expr_which_implies_wit_5_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_leaf_expr_which_implies_wit_6 : cm_emit_leaf_expr_which_implies_wit_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e. destruct leaf; cbn [cm_leaf_source_expr cm_rep_expr_kind] in PreH3; try discriminate.
  pose proof PreH4 as Hasked.
  cbn [cm_leaf_source_expr cm_expr_wf] in Hasked.
  destruct Hasked as [Hcode [Hrefs Htype]].
  Exists asked ty.
  split_pure_spatial.
  - cancel (cm_resolved_emitter_plan_rep policy p emitter out capacity done
      (cm_leaf_code_for p (CMLeafSizeof asked ty) lvalue ++ tail)).
  - split_pures; dump_pre_spatial; auto.
Qed. 

Lemma proof_of_cm_emit_leaf_expr_which_implies_wit_7_split_goal_spatial : cm_emit_leaf_expr_which_implies_wit_7_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn [cm_expr_rep]; unfold cm_expr_node, cm_expr_payload;
    Intros; Exists xa xb xargs;
    (split_pure_spatial; [unfold cm_arg_list_rep; sepcon_assoc_change; cancel | split_pures; dump_pre_spatial; tauto]).
Qed.

Lemma proof_of_cm_emit_leaf_expr_which_implies_wit_7 : cm_emit_leaf_expr_which_implies_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_leaf_expr_which_implies_wit_7_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_leaf_expr_which_implies_wit_8 : cm_emit_leaf_expr_which_implies_wit_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst e. destruct leaf;
    cbn [cm_leaf_source_expr cm_rep_expr_kind] in PreH3, PreH4, PreH5;
    try contradiction.
  Exists ty.
  split_pure_spatial.
  - cancel (cm_resolved_emitter_plan_rep policy p emitter out capacity done
      (cm_leaf_code_for p (CMLeafGetc ty) lvalue ++ tail)).
  - split_pures; dump_pre_spatial; auto.
Qed. 

Lemma proof_of_cm_emit_leaf_expr_which_implies_wit_9_split_goal_spatial : cm_emit_leaf_expr_which_implies_wit_9_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn [cm_expr_rep]; unfold cm_expr_node, cm_expr_payload;
    Intros; Exists xa xb xargs;
    (split_pure_spatial; [unfold cm_arg_list_rep; sepcon_assoc_change; cancel | split_pures; dump_pre_spatial; tauto]).
Qed.

Lemma proof_of_cm_emit_leaf_expr_which_implies_wit_9 : cm_emit_leaf_expr_which_implies_wit_9.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_leaf_expr_which_implies_wit_9_split_goal_spatial.
Qed. 

