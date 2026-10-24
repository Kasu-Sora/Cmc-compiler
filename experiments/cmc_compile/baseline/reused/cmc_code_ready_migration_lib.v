(* Pure code-readiness support; reuse the existing structs-ready definition. *)
From Coq Require Import ZArith List Lia.
From AUXLib Require Import ListLib.
Require Export SimpleC.EE.QCP_demos_human.cmc_program_ready_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_emit_expr_call_migration_lib.
Import ListNotations.
Local Open Scope Z_scope.

Lemma cm_slots_nonnegative structs slots :
  cm_slots_wf structs slots -> 0 <= cm_rep_members_size slots.
Proof.
  intros Hwf. rewrite (cm_slots_size_matches__temp_context _ _ Hwf).
  apply cm_slots_size_nonnegative__call_bounds. exact Hwf.
Qed.

Lemma cm_slots_safe structs slots :
  cm_slots_wf structs slots ->
  cm_rep_members_size slots <= 1048576 -> cm_rep_members_safe slots.
Proof.
  induction slots as [|h t IH]; intros Hwf Hbound; [exact I|].
  assert (Hhead : cm_slot_wf structs h).
  { apply (Hwf 0). rewrite Zlength_cons. pose proof (Zlength_nonneg t). lia. }
  assert (Htail : cm_slots_wf structs t).
  { intros i Hi. specialize (Hwf (i + 1)). unfold cm_slot_at in *.
    replace (i + 1) with (Z.succ i) in Hwf by lia.
    rewrite Z2Nat.inj_succ in Hwf by lia. simpl nth in Hwf.
    apply Hwf. rewrite Zlength_cons. lia. }
  pose proof (cm_slots_nonnegative _ _ Htail) as Hnonneg.
  pose proof (cm_slot_size_matches__temp_context _ _ Hhead) as Hmatch.
  destruct Hhead as [_ [_ Hsize]].
  cbn [cm_rep_members_size] in Hbound.
  cbn [cm_rep_members_safe cm_rep_members_size]. repeat split; try lia.
  apply IH; [exact Htail|lia].
Qed.

Lemma cm_structs_wf_head structs head tail :
  (forall i, 0 <= i < Zlength (head :: tail) ->
    cm_struct_wf structs (cm_struct_at i (head :: tail))) ->
  cm_struct_wf structs head.
Proof.
  intros H. apply (H 0). rewrite Zlength_cons.
  pose proof (Zlength_nonneg tail). lia.
Qed.

Lemma cm_structs_wf_tail structs head tail :
  (forall i, 0 <= i < Zlength (head :: tail) ->
    cm_struct_wf structs (cm_struct_at i (head :: tail))) ->
  (forall i, 0 <= i < Zlength tail ->
    cm_struct_wf structs (cm_struct_at i tail)).
Proof.
  intros H i Hi. specialize (H (i + 1)). unfold cm_struct_at in *.
  replace (i + 1) with (Z.succ i) in H by lia.
  rewrite Z2Nat.inj_succ in H by lia. simpl nth in H.
  apply H. rewrite Zlength_cons. lia.
Qed.

Lemma cm_structs_safe structs items :
  (forall i, 0 <= i < Zlength items ->
    cm_struct_wf structs (cm_struct_at i items)) -> cm_rep_structs_safe items.
Proof.
  induction items as [|h t IH]; intros H; [exact I|].
  pose proof (cm_structs_wf_head _ _ _ H) as Hhead.
  pose proof (cm_structs_wf_tail _ _ _ H) as Htail.
  destruct Hhead as [_ [Hslots Hsize]]. split.
  - apply (cm_slots_safe _ _ Hslots).
    rewrite (cm_slots_size_matches__temp_context _ _ Hslots),
      (cm_slots_struct_size_matches _ _ Hslots). lia.
  - apply IH. exact Htail.
Qed.

Theorem cmc_structs_ready_from_typed policy p :
  cm_typed_program policy p -> cm_concrete_structs_ready p.
Proof.
  intros [Hstructs _]. unfold cm_concrete_structs_ready.
  apply (cm_structs_safe (cm_program_structs p)). exact Hstructs.
Qed.
