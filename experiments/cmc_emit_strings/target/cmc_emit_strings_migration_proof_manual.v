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
From SimpleC.EE.QCP_demos_human Require Import cmc_emit_strings_migration_goal.
From SimpleC.EE.QCP_demos_human Require Import cmc_emit_strings_migration_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.cmc_emit_strings_migration_lib.
Local Open Scope sac.

Lemma proof_of_cmc_emit_strings_entail_wit_1 : cmc_emit_strings_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct strings as [|head tail].
  - cbn [cm_string_list_rep]. Intros_p Hnull. exfalso; lia.
  - cbn [cm_string_list_rep]. Intros sourcep nextp.
    Exists nextp sourcep head tail.
    pose proof PreH2 as Hsafe.
    cbn [cm_rep_strings_safe] in Hsafe.
    destruct Hsafe as [Hhead [Htail [Hlimit Hsafetail]]].
    cbn [cm_rep_strings_size] in PreH4.
    unfold cm_rep_string_size in PreH4.
    pose proof (Zlength_nonneg (cm_string_bytes head)) as Hlength.
    unfold cm_uint8_buffer.
    destruct (cm_string_bytes head) as [|b bs] eqn:Hbytes.
    + unfold cm_rep_string_length. rewrite Hbytes.
      rewrite UCharArray.full_empty.
      split_pure_spatial.
      * repeat progress cancel.
      * split_pures; dump_pre_spatial;
          unfold cmc_uint8_buffer_nonnull, cm_rep_string_length in *;
          rewrite Hbytes in *; rewrite ?Zlength_nil in *; try tauto; try lia.
    + Intros_p Hbuffer.
      unfold cm_rep_string_length. rewrite Hbytes.
      split_pure_spatial.
      * repeat progress cancel.
      * split_pures; dump_pre_spatial;
          unfold cm_rep_string_length in *; rewrite Hbytes in *;
          try assumption; try reflexivity; try lia.
Qed. 

Lemma proof_of_cmc_emit_strings_return_wit_1_split_goal_1 : cmc_emit_strings_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst strings. cbn [cm_rep_strings_size]. unfold cm_rep_string_size.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_cmc_emit_strings_return_wit_1_split_goal_spatial : cmc_emit_strings_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst strings. cbn [cm_rep_strings_size cm_strings_bytes]. unfold cm_rep_string_size.
  replace (cursor_pre + (cm_rep_string_length head + 1 + cm_rep_strings_size tail))
    with (cursor_pre + cm_rep_string_length head + 1 + cm_rep_strings_size tail) by lia.
  repeat rewrite app_assoc.
  cbn [cm_string_list_rep].
  Exists sourcep nextp.
  split_pure_spatial.
  - rewrite PreH13.
    destruct (cm_string_bytes head) as [|b bs] eqn:Hbytes.
    + cbn [cm_uint8_buffer Zlength].
      unfold UCharArray.full. cbn.
      Intros. cancel.
    + cbn [cm_uint8_buffer].
      split_pure_spatial.
      * cancel (cm_string_list_rep nextp tail).
        cancel (UCharArray.full sourcep (Zlength (b :: bs)) (b :: bs)).
        cancel.
      * dump_pre_spatial. assumption.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_cmc_emit_strings_return_wit_1 : cmc_emit_strings_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_strings_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_cmc_emit_strings_return_wit_1_split_goal_1.
Qed. 

Lemma proof_of_cmc_emit_strings_return_wit_2_split_goal_1 : cmc_emit_strings_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst node_pre. destruct strings as [|h t].
  - cbn [cm_rep_strings_size]. dump_pre_spatial. lia.
  - cbn [cm_string_list_rep]. Intros b n. contradiction.
Qed.

Lemma proof_of_cmc_emit_strings_return_wit_2_split_goal_spatial : cmc_emit_strings_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst node_pre. destruct strings as [|h t].
  - cbn [cm_rep_strings_size cm_strings_bytes].
    rewrite app_nil_r, Z.add_0_r. cancel.
  - cbn [cm_string_list_rep]. Intros b n. contradiction.
Qed.

Lemma proof_of_cmc_emit_strings_return_wit_2 : cmc_emit_strings_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_strings_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_cmc_emit_strings_return_wit_2_split_goal_1.
Qed. 

