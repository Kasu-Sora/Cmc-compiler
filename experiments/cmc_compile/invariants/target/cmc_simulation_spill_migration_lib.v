Require Export SimpleC.EE.QCP_demos_human.cmc_simulation_coordinate_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
(* cmc_preservation_spill_semantic.c: the newest argument is stored last. *)
Fixpoint cm_staged_spills base values spills : Prop := match values with
 | []=>True | value::rest=>cm_spill_holds (base+Zlength rest) value spills /\ cm_staged_spills base rest spills end.
Definition cm_phase_is_call phase := match phase with CACallP _ _ _ _ _=>true | _=>false end.
Definition cm_phase_spill_consistent limit owner phase spills : Prop := match phase with
 | CAAssignRP v _ | CAIndexRP v _=>owner<limit /\ cm_spill_holds owner v spills
 | CABinRP op _ _ v _=>owner<=limit /\ ((op=0 \/ op=1) \/ (owner<limit /\ cm_spill_holds owner v spills))
 | CAArgP callee rest values ret all_args base current scratch=>owner<=limit /\ base=owner /\
   current=base+Zlength values /\ scratch=base+Zlength all_args /\
   Zlength all_args=Zlength values+1+Zlength rest /\ current<=limit /\ cm_staged_spills base values spills
 | CACallP _ _ _ _ _=>True
 | _=>owner<=limit end.
Fixpoint cm_cursors_spill_consistent ap limit cursors spills saved : Prop := match cursors with
 | []=>True | cursor::rest=>cm_phase_spill_consistent limit (cm_cursor_temp cursor) (cm_cursor_phase cursor) spills /\
   (if cm_phase_is_call (cm_cursor_phase cursor) then saved<>[] /\
      cm_cursors_spill_consistent ap (cm_cursor_temp cursor) rest (cm_spill_frame_spills (hd (cm_saved_nil ap) saved)) (tl saved)
    else cm_cursors_spill_consistent ap (cm_cursor_temp cursor) rest spills saved) end.
Definition cm_annotation_spill_consistent ap ann := cm_cursors_spill_consistent ap (cm_ann_temp ann) (cm_ann_cursors ann) (cm_ann_spills ann) (cm_ann_saved ann).
Lemma cm_spill_holds_remove_other slot other value spills : other<>slot -> cm_spill_holds other value spills -> cm_spill_holds other value (cm_spill_remove slot spills).
Proof.
 intros H; induction spills as [|[s v] xs IH]; cbn; [tauto|].
 destruct (s =? slot) eqn:E; destruct (s =? other) eqn:F; cbn; try rewrite F; auto.
 apply Z.eqb_eq in E; apply Z.eqb_eq in F; congruence.
Qed.
Lemma cm_spill_holds_put_other slot new_value other value spills : other<>slot -> cm_spill_holds other value spills -> cm_spill_holds other value (cm_spill_put slot new_value spills).
Proof. intros H V; cbn; assert (E:(slot =? other)=false) by (apply Z.eqb_neq; congruence); rewrite E. now apply cm_spill_holds_remove_other. Qed.
Lemma cm_staged_spills_put_above base values spills slot v :
 cm_staged_spills base values spills -> base+Zlength values<=slot -> cm_staged_spills base values (cm_spill_put slot v spills).
Proof.
 induction values as [|a xs IH]; cbn [cm_staged_spills]; [tauto|].
 rewrite Zlength_cons; intros [H T] B; split; [apply cm_spill_holds_put_other; [lia|exact H]|apply IH; [exact T|lia]].
Qed.
Lemma cm_phase_spill_consistent_owner_bound phase limit owner spills :
 cm_phase_is_call phase=false -> cm_phase_spill_consistent limit owner phase spills -> owner<=limit.
Proof. destruct phase; cbn; intros; try discriminate; intuition lia. Qed.
Lemma cm_phase_spill_consistent_put_above limit owner phase spills slot v :
 cm_phase_spill_consistent limit owner phase spills -> limit<=slot -> cm_phase_spill_consistent limit owner phase (cm_spill_put slot v spills).
Proof.
 destruct phase; cbn [cm_phase_spill_consistent]; intros H B; try exact H.
 - destruct H; split; [assumption|apply cm_spill_holds_put_other; [lia|assumption]].
 - destruct H as [H [S|[L V]]]; split; auto; right; split; [exact L|apply cm_spill_holds_put_other; [lia|exact V]].
 - destruct H; split; [assumption|apply cm_spill_holds_put_other; [lia|assumption]].
 - repeat match goal with H:_ /\ _ |- _=>destruct H end. repeat split; try assumption.
   apply cm_staged_spills_put_above; [assumption|lia].
Qed.
Lemma cm_cursors_spill_consistent_put_above ap cursors limit spills saved slot v :
 cm_cursors_spill_consistent ap limit cursors spills saved -> limit<=slot ->
 cm_cursors_spill_consistent ap limit cursors (cm_spill_put slot v spills) saved.
Proof.
 revert limit spills saved; induction cursors as [|cursor rest IH]; intros limit spills saved; cbn [cm_cursors_spill_consistent]; [tauto|].
 intros [P T] B; split; [eapply cm_phase_spill_consistent_put_above; eauto|].
 destruct (cm_phase_is_call (cm_cursor_phase cursor)) eqn:C; [exact T|].
 apply IH; [exact T|pose proof (cm_phase_spill_consistent_owner_bound _ _ _ _ C P); lia].
Qed.
Lemma cm_annotation_spill_consistent_initial ap : cm_annotation_spill_consistent ap cm_initial_annotation.
Proof. exact I. Qed.
(* Monotonicity changes only the active interval; saved caller frames are unchanged. *)
Lemma cm_phase_spill_consistent_limit limit upper owner phase spills : limit<=upper ->
 cm_phase_spill_consistent limit owner phase spills -> cm_phase_spill_consistent upper owner phase spills.
Proof. destruct phase; cbn; intros B H; intuition lia. Qed.
Lemma cm_cursors_spill_consistent_limit ap limit upper cursors spills saved : limit<=upper ->
 cm_cursors_spill_consistent ap limit cursors spills saved -> cm_cursors_spill_consistent ap upper cursors spills saved.
Proof. destruct cursors; cbn; [tauto|]. intros B [H T]; split; [eapply cm_phase_spill_consistent_limit; eauto|exact T]. Qed.
Lemma cm_staged_spills_cons base values spills v : cm_staged_spills base values spills ->
 cm_staged_spills base (v::values) (cm_spill_put (base+Zlength values) v spills).
Proof. intro H; split; [apply cm_spill_put_holds|apply cm_staged_spills_put_above; [exact H|lia]]. Qed.
