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
From SimpleC.EE.QCP_demos_human Require Import cmc_emit_expr_simple_migration_goal.
From SimpleC.EE.QCP_demos_human Require Import cmc_emit_expr_simple_migration_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.cmc_emit_expr_simple_migration_lib.
Local Open Scope sac.

Lemma proof_of_cm_emit_simple_expr_return_wit_1_split_goal_spatial : cm_emit_simple_expr_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst simple.
  cbn [cm_simple_code_for].
  cancel.
Qed.

Lemma proof_of_cm_emit_simple_expr_return_wit_1 : cm_emit_simple_expr_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_simple_expr_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_simple_expr_return_wit_2_split_goal_spatial : cm_emit_simple_expr_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst simple.
  cbn [cm_simple_code_for].
  cancel.
Qed.

Lemma proof_of_cm_emit_simple_expr_return_wit_2 : cm_emit_simple_expr_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_simple_expr_return_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_simple_expr_which_implies_wit_1 : cm_emit_simple_expr_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_expr_rep_node. unfold cm_expr_node.
  Intros a b args.
  Exists args b a.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_emit_simple_expr_which_implies_wit_2 : cm_emit_simple_expr_which_implies_wit_2.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 subst e. destruct simple as [leaf|scope slot ty].
 - destruct leaf; cbn [cm_simple_source_expr cm_leaf_source_expr cm_rep_expr_kind] in PreH3; discriminate.
 - cbn [cm_simple_source_expr] in *.
   pose proof (proj1 PreH4) as Hvalid.
   pose proof (proj1 (proj2 (proj1 PreH5))) as Htype.
   pose proof (proj2 PreH5) as Hslot.
   unfold cm_i32_code_count in Hslot.
   Exists scope slot ty.
   cbn [cm_simple_code_for].
   split_pure_spatial.
   + cancel (cm_resolved_emitter_plan_rep policy p emitter out capacity done
       (cm_var_code_for policy p fid scope slot ty lvalue ++ tail)).
   + split_pures; dump_pre_spatial; try reflexivity; try assumption; lia.
Qed. 

Lemma proof_of_cm_emit_simple_expr_which_implies_wit_3_split_goal_spatial : cm_emit_simple_expr_which_implies_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_expr_rep_node. unfold cm_expr_node.
  Exists xa xb xargs.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_emit_simple_expr_which_implies_wit_3 : cm_emit_simple_expr_which_implies_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_simple_expr_which_implies_wit_3_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_simple_expr_which_implies_wit_4 : cm_emit_simple_expr_which_implies_wit_4.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 subst e. destruct simple as [leaf|scope slot ty].
 - cbn [cm_simple_source_expr] in *.
   assert (Hleaf : cm_dispatch_leaf (cm_leaf_source_expr leaf)).
   { apply cm_dispatch_leaf_coverage. exists leaf. reflexivity. }
   Exists leaf. cbn [cm_simple_code_for].
   split_pure_spatial.
   + cancel (cm_resolved_emitter_plan_rep policy p emitter out capacity done
       (cm_leaf_code_for p leaf lvalue ++ tail)).
   + split_pures; dump_pre_spatial; try reflexivity; assumption.
 - cbn [cm_simple_source_expr cm_rep_expr_kind] in PreH3. contradiction.
Qed. 

Lemma proof_of_cm_emit_simple_expr_which_implies_wit_5_split_goal_spatial : cm_emit_simple_expr_which_implies_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite cm_expr_rep_node. unfold cm_expr_node.
  Exists xa xb xargs.
  split_pure_spatial.
  - sepcon_assoc_change. cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_emit_simple_expr_which_implies_wit_5 : cm_emit_simple_expr_which_implies_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_simple_expr_which_implies_wit_5_split_goal_spatial.
Qed.

