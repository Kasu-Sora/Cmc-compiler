Require Export SimpleC.EE.QCP_demos_human.cmc_simulation_spill_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_done_error_not_succeeds sp st error status : ~cm_task_succeeds sp (CMDoneTask st (CMError error) status).
Proof.
 intros [st' [ctl [status' [H S]]]].
 pose proof (cm_exec_deterministic sp _ _ _ H (cm_exec_done sp st (CMError error) status)) as E.
 inversion E; subst; destruct S; discriminate.
Qed.
Lemma cm_error_not_succeeds sp p fid st error ks : ~cm_task_succeeds sp (CMCTask p fid (CMError error) st ks).
Proof.
 revert fid st; induction ks as [|frame rest IH]; intros fid st H; apply cm_succeeds_step_total in H.
 - eapply cm_done_error_not_succeeds; exact H.
 - destruct frame; cbn [cm_step cm_capply cm_control_kind] in H;
   try (eapply cm_done_error_not_succeeds; exact H); eapply IH; exact H.
Qed.
Ltac cm_spill_reduce := repeat progress (cm_coord_reduce;
 cbv beta iota zeta delta [cm_annotation_spill_consistent cm_cursors_spill_consistent cm_phase_spill_consistent cm_phase_is_call cm_spill_frame_spills] in *).
Ltac cm_spill_cases := cm_spill_reduce;
 repeat match goal with |- context[if ?b then _ else _]=>cm_ann_bool b; cm_spill_reduce end.
Ltac cm_spill_finish := repeat match goal with H:_ /\ _ |- _=>destruct H end;
 repeat match goal with H:true=true -> _ |- _=>specialize (H eq_refl) end;
 repeat match goal with H:_ /\ _ |- _=>destruct H end;
 subst; repeat split; try assumption; try congruence; try lia;
 try (apply cm_spill_put_holds);
 try (eapply cm_cursors_spill_consistent_put_above; [eassumption|lia]).
Lemma cm_update_r_spill_consistent sp ap p fid expr st ann : cm_annotation_spill_consistent ap ann ->
 cm_annotation_spill_consistent ap (cm_update_annotation (cm_update_r sp ap p fid st ann expr)).
Proof.
 destruct expr; try match goal with xs:list cm_expr |- _=>destruct xs end; intro H; cm_spill_cases;
 cbn [cm_staged_spills]; rewrite ?Zlength_cons,?Zlength_nil; try cm_spill_finish.
 all: rewrite Zlength_correct; lia.
Qed.
Lemma cm_update_l_spill_consistent sp ap p fid expr st ann : cm_annotation_spill_consistent ap ann ->
 cm_annotation_spill_consistent ap (cm_update_annotation (cm_update_l sp ap p fid st ann expr)).
Proof. destruct expr; intro H; cm_spill_cases; cm_spill_finish. Qed.
Lemma cm_update_s_spill_consistent sp ap p fid stmt st ann : cm_annotation_spill_consistent ap ann ->
 cm_annotation_spill_consistent ap (cm_update_annotation (cm_update_s sp ap p fid st ann stmt)).
Proof. destruct stmt; intro H; cm_spill_cases; cm_spill_finish. Qed.
Lemma cm_update_v_spill_coordinate sp ap p fid v st phase pc temp b c pt pb pk rest spills saved calls :
 let ann:=CMAnnotation pc temp b c (CMACursor phase pt pb pk::rest) spills saved calls in
 cm_phase_is_call phase=false ->
 cm_annotation_child_ready (cm_source_function_policy sp) p fid ann ->
 cm_annotation_spill_consistent ap ann ->
 cm_annotation_spill_consistent ap (cm_update_annotation (cm_update_v sp ap p fid v st ann phase)).
Proof.
 cbn zeta; destruct phase; intros NC HC HS; cm_spill_cases; try discriminate; try cm_spill_finish.
 all: try match goal with H:(?x =? ?y)=true |- _=>apply Z.eqb_eq in H end; try cm_spill_finish.
 all: try match goal with |- context[match ?xs with []=>_ | _::_=>_ end]=>destruct xs; cm_spill_cases; try cm_spill_finish end.
  all: try (left; match goal with H:(if ?op =? 0 then true else ?op =? 1)=true |- _=>
   destruct (op =? 0) eqn:E; [left; now apply Z.eqb_eq|right; now apply Z.eqb_eq] end).
 all: try (right; split; [lia|apply cm_spill_put_holds]).
 all: rewrite ?Zlength_cons,?Zlength_nil in *.
 all: try lia.
 all: try (apply cm_staged_spills_put_above; [assumption|lia]).
 all: try (eapply cm_cursors_spill_consistent_put_above; [eassumption|rewrite Zlength_correct; lia]).
 all: rewrite !Zlength_correct in *; lia.
Qed.
Lemma cm_update_c_spill_consistent sp ap p fid ctl st phase pc temp b c pt pb pk rest spills saved calls :
 let ann:=CMAnnotation pc temp b c (CMACursor phase pt pb pk::rest) spills saved calls in
 cm_annotation_spill_consistent ap ann ->
 cm_annotation_spill_consistent ap (cm_update_annotation (cm_update_c sp ap p fid ctl st ann phase)).
Proof. cbn zeta; destruct phase; intro H; cm_spill_cases; cm_spill_finish. Qed.
(* This version uses already proved coordinates and successful execution.
   It is not the source's layout-ready-only theorem under a new name. *)
Lemma cm_annotation_step_spill_coordinate sp ap p task ann :
 cm_task_succeeds sp task -> cm_annotation_erases task ann ->
 cm_task_coordinate_ready (cm_source_function_policy sp) p task ann ->
 cm_annotation_spill_consistent ap ann ->
 cm_annotation_spill_consistent ap (cm_update_annotation (cm_annotation_step sp ap task ann)).
Proof.
 destruct task as [q input|q fid expr st ks|q fid expr st ks|q fid stmt st ks|q fid v st ks|q fid ctl st ks|st ctl status]; intros S E C H.
 - cbv beta iota zeta delta [cm_annotation_step].
   destruct (cm_call_ok sp q (cm_program_main q) [] (cm_initial_state sp q input) && (cm_call_depth [CMHaltK] <? 65536)); cm_spill_reduce; intuition discriminate.
 - now apply cm_update_r_spill_consistent.
 - now apply cm_update_l_spill_consistent.
 - now apply cm_update_s_spill_consistent.
 - destruct C as [-> C]; destruct ann as [pc temp b c cursors spills saved calls]; cbn [cm_annotation_erases cm_ann_cursors] in E; subst ks.
   destruct cursors as [|[phase pt pb pk] rest]; [exact H|].
   apply cm_update_v_spill_coordinate; try assumption.
   destruct phase; try reflexivity.
   apply cm_succeeds_step_total in S; exfalso; eapply cm_error_not_succeeds; exact S.
 - destruct ann as [pc temp b c cursors spills saved calls].
   cbv beta iota zeta delta [cm_annotation_step cm_ann_cursors].
   destruct (cm_control_kind ctl =? 4); [exact I|].
   destruct cursors as [|[phase pt pb pk] rest]; [exact H|now apply cm_update_c_spill_consistent].
 - exact H.
Qed.
Lemma cm_annotated_iter_spill_coordinate sp ap p n ast :
 cm_task_succeeds sp (cm_astate_task ast) ->
 cm_annotation_erases (cm_astate_task ast) (cm_astate_annotation ast) /\ cm_annotation_rooted (cm_astate_annotation ast) ->
 cm_task_coordinate_ready (cm_source_function_policy sp) p (cm_astate_task ast) (cm_astate_annotation ast) ->
 cm_annotation_spill_consistent ap (cm_astate_annotation ast) ->
 cm_annotation_spill_consistent ap (cm_astate_annotation (cm_annotated_iter sp ap n ast)).
Proof.
 revert ast; induction n; intros ast S E C H; [exact H|].
 apply IHn.
 - now apply cm_succeeds_step_total.
 - now apply cm_annotated_step_invariant.
 - apply cm_task_coordinate_step; [exact (proj1 E)|exact C].
 - eapply cm_annotation_step_spill_coordinate; eauto; exact (proj1 E).
Qed.
Lemma cm_annotated_start_iter_spill_consistent sp ap p input n :
 cm_task_succeeds sp (CMStartTask p input) ->
 cm_annotation_spill_consistent ap (cm_astate_annotation
   (cm_annotated_iter sp ap n (cm_annotated_start (cm_source_function_policy sp) p input))).
Proof.
 intro H; eapply cm_annotated_iter_spill_coordinate; [exact H| |apply cm_task_coordinate_initial|apply cm_annotation_spill_consistent_initial].
 split; [apply cm_annotated_start_erases|apply cm_annotated_start_rooted].
Qed.
