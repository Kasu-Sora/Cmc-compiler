(* Pure readiness support; no runtime C verification unit is introduced. *)
From Coq Require Import ZArith List Bool Lia.
From AUXLib Require Import ListLib.
Require Export SimpleC.EE.QCP_demos_human.cmc_emit_expr_leaf_migration_lib.
Import ListNotations.
Local Open Scope Z_scope.

Definition cm_concrete_data_ready (p : cm_program) : Prop :=
  cm_rep_globals_safe (cm_program_globals p) /\
  cm_data_globals_wf (cm_program_structs p) (cm_program_globals p) /\
  cm_rep_strings_safe (cm_program_strings p) /\
  0 <= cm_rep_globals_size (cm_program_globals p) /\
  0 <= cm_rep_strings_size (cm_program_strings p) /\
  cm_rep_globals_size (cm_program_globals p) +
    cm_rep_strings_size (cm_program_strings p) <= 1048560 /\
  cm_model_data_length p =
    (8 + cm_rep_globals_size (cm_program_globals p)) +
      cm_rep_strings_size (cm_program_strings p).

Lemma cm_data_globals_from_indexed structs globals :
  (forall i, 0 <= i < Zlength globals ->
    cm_global_wf structs (cm_global_at i globals)) ->
  cm_data_globals_wf structs globals.
Proof.
  induction globals as [|h t IH]; intros H; [exact I|].
  split.
  - apply (H 0). rewrite Zlength_cons. pose proof (Zlength_nonneg t). lia.
  - apply IH. intros i Hi. specialize (H (i + 1)).
    unfold cm_global_at in *.
    replace (i + 1) with (Z.succ i) in H by lia.
    rewrite Z2Nat.inj_succ in H by lia. simpl nth in H.
    apply H. rewrite Zlength_cons. lia.
Qed.

Lemma cm_ready_globals_nonnegative structs globals :
  cm_data_globals_wf structs globals -> 0 <= cm_rep_globals_size globals.
Proof.
  induction globals as [|h t IH]; intros H; [cbn; lia|].
  destruct H as [Hh Ht]. specialize (IH Ht).
  cbn [cm_rep_globals_size]. rewrite (cm_rep_global_size_matches _ _ Hh).
  destruct Hh as [_ [_ [Hsize _]]]. lia.
Qed.

Lemma cm_ready_globals_safe structs globals :
  cm_data_globals_wf structs globals ->
  cm_rep_globals_size globals <= 1048560 -> cm_rep_globals_safe globals.
Proof.
  induction globals as [|h t IH]; intros H Hbound; [exact I|].
  destruct H as [Hh Ht].
  pose proof (cm_ready_globals_nonnegative _ _ Ht) as Htail.
  pose proof (cm_rep_global_size_matches _ _ Hh) as Hmatch.
  destruct Hh as [_ [_ [Hsize _]]].
  cbn [cm_rep_globals_size] in Hbound.
  cbn [cm_rep_globals_safe cm_rep_globals_size]. repeat split; try lia.
  apply IH; [exact Ht|lia].
Qed.

Lemma cm_ready_strings_nonnegative strings : 0 <= cm_rep_strings_size strings.
Proof.
  induction strings as [|h t IH]; [cbn; lia|].
  cbn [cm_rep_strings_size]. unfold cm_rep_string_size, cm_rep_string_length.
  pose proof (Zlength_nonneg (cm_string_bytes h)). lia.
Qed.

Lemma cm_ready_strings_safe strings :
  cm_rep_strings_size strings <= 1048560 -> cm_rep_strings_safe strings.
Proof.
  induction strings as [|h t IH]; intros Hbound; [exact I|].
  pose proof (cm_ready_strings_nonnegative t) as Htail.
  assert (Hhead : 0 <= cm_rep_string_size h).
  { unfold cm_rep_string_size, cm_rep_string_length.
    pose proof (Zlength_nonneg (cm_string_bytes h)). lia. }
  cbn [cm_rep_strings_size] in Hbound.
  cbn [cm_rep_strings_safe cm_rep_strings_size]. repeat split; try lia.
  apply IH. lia.
Qed.

Lemma cm_ready_global_bytes_length structs g :
  0 <= cm_global_size structs g ->
  Zlength (cm_global_bytes structs g) = cm_global_size structs g.
Proof.
  intros Hsize. unfold cm_global_bytes.
  assert (Hnonneg : (0 <=? cm_global_size structs g) = true) by (apply Z.leb_le; lia).
  rewrite Hnonneg.
  destruct (cm_global_has_init g &&
    (Zlength (cm_global_init_bytes g) <=? cm_global_size structs g))%bool eqn:Hinit.
  - apply andb_true_iff in Hinit. destruct Hinit as [_ Hfit]. apply Z.leb_le in Hfit.
    rewrite Zlength_app.
    rewrite (Zlength_correct (repeat 0 _)), repeat_length, Z2Nat.id by lia. lia.
  - rewrite Zlength_correct, repeat_length, Z2Nat.id by lia. reflexivity.
Qed.

Lemma cm_ready_globals_bytes_length structs globals :
  cm_data_globals_wf structs globals ->
  Zlength (cm_globals_bytes structs globals) = cm_rep_globals_size globals.
Proof.
  induction globals as [|h t IH]; intros H; [reflexivity|].
  destruct H as [Hh Ht]. cbn [cm_globals_bytes cm_rep_globals_size].
  rewrite Zlength_app, (IH Ht), (cm_rep_global_size_matches _ _ Hh).
  rewrite cm_ready_global_bytes_length; [reflexivity|].
  destruct Hh as [_ [_ [Hsize _]]]. lia.
Qed.

Lemma cm_ready_strings_bytes_length strings :
  Zlength (cm_strings_bytes strings) = cm_rep_strings_size strings.
Proof.
  induction strings as [|h t IH]; [reflexivity|].
  cbn [cm_strings_bytes cm_rep_strings_size].
  rewrite !Zlength_app, IH.
  unfold cm_rep_string_size, cm_rep_string_length.
  rewrite Zlength_cons, Zlength_nil. lia.
Qed.

Theorem cmc_data_ready_from_typed policy p :
  cm_typed_program policy p -> cm_concrete_data_ready p.
Proof.
  intros Htyped.
  assert (Hindexed : forall i, 0 <= i < Zlength (cm_program_globals p) ->
    cm_global_wf (cm_program_structs p) (cm_global_at i (cm_program_globals p))).
  { destruct Htyped as [_ [H _]]. exact H. }
  assert (Hstatic : cm_static_size p <= 1048576).
  { unfold cm_typed_program in Htyped. tauto. }
  pose proof (cm_data_globals_from_indexed _ _ Hindexed) as Hglobals.
  pose proof (cm_ready_globals_nonnegative _ _ Hglobals) as Hgpos.
  pose proof (cm_ready_strings_nonnegative (cm_program_strings p)) as Hspos.
  pose proof (cm_rep_globals_size_matches _ _ Hindexed) as Hmatch.
  unfold cm_static_size, cm_strings_size in Hstatic. rewrite <- Hmatch in Hstatic.
  unfold cm_concrete_data_ready. repeat split; try lia.
  - apply (cm_ready_globals_safe _ _ Hglobals). lia.
  - exact Hglobals.
  - apply cm_ready_strings_safe. lia.
  - unfold cm_model_data_length, cm_model_data_bytes.
    rewrite !Zlength_app, (cm_ready_globals_bytes_length _ _ Hglobals), cm_ready_strings_bytes_length.
    assert (Hzero : Zlength (repeat 0 8) = 8) by reflexivity.
    rewrite Hzero. lia.
Qed.
