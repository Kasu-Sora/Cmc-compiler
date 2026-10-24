Require Export SimpleC.EE.QCP_demos_human.cmc_target_call_execution_migration_lib.
From AUXLib Require Import ListLib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_call_sim_length mem frames calls :cm_call_frames_sim mem frames calls ->Zlength frames=Zlength calls.
Proof.
 revert calls;induction frames as[|f fs IH];intros calls SIM;[cbn[cm_call_frames_sim]in SIM;subst;reflexivity|].
 destruct SIM as[N[_[_ T]]];destruct calls as[|c cs];[contradiction|];rewrite !Zlength_cons;specialize(IH cs T);lia.
Qed.
Lemma cm_saved_layout_call_depth sp ap p code fid cursors calls :cm_saved_layout sp ap p code fid cursors calls ->
 Zlength calls=cm_call_depth(cm_cursor_frames cursors).
Proof.
 revert fid calls;induction cursors as[|[phase owner ob oc]tail IH];intros fid calls L.
 - cbn[cm_saved_layout]in L;subst;reflexivity.
 - cbn[cm_saved_layout cm_cursor_phase]in L;destruct L as[SITE REST].
   destruct phase;cbn[cm_phase_is_call cm_phase_caller cm_phase_frame cm_cursor_frames map cm_cursor_phase cm_call_depth cm_is_call_frame]in *;try(now apply IH in REST).
   destruct SITE as[N _];destruct calls as[|c cs];[contradiction|];cbn[tl]in REST;apply IH in REST;unfold cm_cursor_frames in REST;rewrite Zlength_cons;lia.
Qed.
