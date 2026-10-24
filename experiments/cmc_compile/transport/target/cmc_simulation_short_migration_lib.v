Require Export SimpleC.EE.QCP_demos_human.cmc_simulation_region_transport_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
(* Original cmc_preservation_short_defs.c predicates. *)
Definition cm_frame_short_ready st frame : Prop := match frame with
 | CMBinRK op lhs _=>(op=0 -> cm_truth st lhs=false) /\ (op=1 -> cm_truth st lhs=true) | _=>True end.
Fixpoint cm_frames_short_ready st frames : Prop := match frames with []=>True | f::rest=>cm_frame_short_ready st f /\ cm_frames_short_ready st rest end.
Definition cm_task_short_ready task : Prop := match task with
 | CMRTask _ _ _ st ks | CMLTask _ _ _ st ks | CMSTask _ _ _ st ks | CMVTask _ _ _ st ks | CMCTask _ _ _ st ks=>cm_frames_short_ready st ks | _=>True end.
Lemma cm_value_number_bases v old new limit : cm_region_bases_below_equal (cm_state_regions new) (cm_state_regions old) limit -> cm_value_generation_below limit v -> cm_value_number new v=cm_value_number old v.
Proof. destruct v; intros B G; try reflexivity; cbn [cm_value_number]; now rewrite (B gen G). Qed.
Lemma cm_truth_bases v old new limit : cm_region_bases_below_equal (cm_state_regions new) (cm_state_regions old) limit -> cm_value_generation_below limit v -> cm_truth new v=cm_truth old v.
Proof. intros B G; unfold cm_truth; now rewrite (cm_value_number_bases v old new limit B G). Qed.
Lemma cm_frames_short_bases policy p fid frames old new limit : cm_region_bases_below_equal (cm_state_regions new) (cm_state_regions old) limit -> cm_frames_generation_below policy p fid limit frames -> cm_frames_short_ready old frames -> cm_frames_short_ready new frames.
Proof.
 intros B; revert fid; induction frames; intros fid G H; [exact I|]; destruct G as [G GS]; destruct H as [H HS]; split.
 - destruct a; cbn [cm_frame_short_ready] in *; try exact I; rewrite (cm_truth_bases value old new limit B G); exact H.
 - eapply IHframes; eauto.
Qed.
Lemma cm_enter_call_bases sp p fid values st : cm_region_bases_below_equal (cm_state_regions (cm_enter_call sp p fid values st)) (cm_state_regions st) (cm_state_nextgen st).
Proof. unfold cm_enter_call; rewrite cm_store_params_regions; apply cm_regions_for_slots_bases; lia. Qed.
Lemma cm_activate_local_bases sp p fid slot st : cm_region_bases_below_equal (cm_state_regions (cm_activate_local sp p fid slot st)) (cm_state_regions st) (cm_state_nextgen st).
Proof. apply cm_region_bases_cons_fresh; reflexivity. Qed.
Lemma cm_restore_call_bases st env fp regions limit : cm_region_generations_incl regions (cm_state_regions st) -> cm_region_bases_below_equal (cm_state_regions (cm_restore_call st env fp regions)) (cm_state_regions st) limit.
Proof. apply cm_restore_regions_bases_transport. Qed.
Ltac cm_short_reduce := repeat progress (cm_ann_reduce;
 cbn [cm_task_short_ready cm_frames_short_ready cm_frame_short_ready cm_frames_generation_below cm_frame_generation_below cm_frame_parent_fid cm_task_saved_generations cm_frames_saved_generations cm_frame_saved_generations cm_control_kind] in *).
Ltac cm_short_cases := cm_short_reduce;
 repeat match goal with |- context[if ?b then _ else _]=>cm_ann_bool b; cm_short_reduce end.
Ltac cm_short_transport := match goal with
 | |- cm_frames_short_ready (cm_enter_call ?sp ?p ?fid ?vs ?st) ?ks=>
 eapply cm_frames_short_bases with (old:=st) (limit:=cm_state_nextgen st); [apply cm_enter_call_bases|eassumption|assumption]
 | |- cm_frames_short_ready (cm_activate_local ?sp ?p ?fid ?slot ?st) ?ks=>
 eapply cm_frames_short_bases with (old:=st) (limit:=cm_state_nextgen st); [apply cm_activate_local_bases|eassumption|assumption]
 | |- cm_frames_short_ready (cm_restore_call ?st ?env ?fp ?rs) ?ks=>
 eapply cm_frames_short_bases with (old:=st) (limit:=cm_state_nextgen st); [apply cm_restore_call_bases; assumption|eassumption|assumption]
 | |- cm_frames_short_ready (cm_restore_scope ?st ?env ?rs) ?ks=>
 unfold cm_restore_scope; eapply cm_frames_short_bases with (old:=st) (limit:=cm_state_nextgen st); [apply cm_restore_call_bases; assumption|eassumption|assumption]
 end.
Ltac cm_short_finish := repeat match goal with H:_ /\ _ |- _=>destruct H end;
 repeat first [assumption | exact I | cm_short_transport | match goal with |- _ /\ _=>split end].
Lemma cm_frames_short_io st input output frames : cm_frames_short_ready st frames -> cm_frames_short_ready (cm_state_io st input output) frames.
Proof. induction frames; cbn; [auto|destruct a; cbn; intuition]. Qed.
Lemma cm_frames_short_store st ty ptr v frames : cm_frames_short_ready st frames -> cm_frames_short_ready (cm_state_store ty ptr v st) frames.
Proof. induction frames; cbn; [auto|destruct a; cbn; intuition]. Qed.
Lemma cm_r_short_step sp p fid expr st ks : cm_frames_generation_below (cm_source_function_policy sp) p fid (cm_state_nextgen st) ks -> cm_frames_short_ready st ks -> cm_task_short_ready (cm_rstart sp p fid expr st ks).
Proof.
 destruct expr; intros G H; cm_short_cases; try cm_short_finish.
 all: try match goal with |- context[match ?xs with []=>_ | _::_=>_ end]=>destruct xs; cm_short_cases; try cm_short_finish end.
 all: now apply cm_frames_short_io.
Qed.
Lemma cm_l_short_step sp p fid expr st ks : cm_frames_short_ready st ks -> cm_task_short_ready (cm_lstart sp p fid expr st ks).
Proof. destruct expr; intro H; cm_short_cases; cm_short_finish. Qed.
Lemma cm_s_short_step sp p fid stmt st ks : cm_frames_generation_below (cm_source_function_policy sp) p fid (cm_state_nextgen st) ks -> cm_frames_short_ready st ks -> cm_task_short_ready (cm_sstart sp p fid stmt st ks).
Proof. destruct stmt; intros G H; cm_short_cases; cm_short_finish. Qed.
Lemma cm_v_short_step sp p fid frame v st ks : cm_frames_generation_below (cm_source_function_policy sp) p fid (cm_state_nextgen st) (frame::ks) -> cm_frames_saved_generations (cm_state_regions st) (frame::ks) -> cm_frames_short_ready st (frame::ks) -> cm_task_short_ready (cm_vapply sp p fid frame v st ks).
Proof.
 destruct frame; intros G SAVED H; cm_short_cases; try cm_short_finish.
 all: try solve [now apply cm_frames_short_io | now apply cm_frames_short_store].
 all: try match goal with |- context[match ?xs with []=>_ | _::_=>_ end]=>destruct xs; cm_short_cases; try cm_short_finish end.
 all: try (intro E; subst op; cbn in *; congruence).
 all: intro E; subst op; change (negb (cm_truth st v)=false) in Heqb0; now apply Bool.negb_false_iff in Heqb0.
Qed.
Lemma cm_c_short_step sp p fid frame ctl st ks : cm_frames_generation_below (cm_source_function_policy sp) p fid (cm_state_nextgen st) (frame::ks) -> cm_frames_saved_generations (cm_state_regions st) (frame::ks) -> cm_frames_short_ready st (frame::ks) -> cm_task_short_ready (cm_capply sp p fid frame ctl st ks).
Proof. destruct frame; intros G SAVED H; cm_short_cases; cm_short_finish. Qed.
Lemma cm_task_short_step_generation sp p task : cm_task_generation_below (cm_source_function_policy sp) p task ->
 cm_task_saved_generations task -> cm_task_short_ready task -> cm_task_short_ready (cm_step sp task).
Proof.
 destruct task as [q input|q fid expr st ks|q fid expr st ks|q fid stmt st ks|q fid v st ks|q fid ctl st ks|st ctl status]; intros G SAVED H.
 - cbv beta iota zeta delta [cm_step cm_begin_call]; cm_short_cases; cm_short_finish.
 - destruct G as [-> [ST KS]]; now apply cm_r_short_step.
 - now apply cm_l_short_step.
 - destruct G as [-> [ST KS]]; now apply cm_s_short_step.
 - destruct G as [-> [ST [V KS]]]; destruct ks; [exact I|now apply cm_v_short_step].
 - destruct G as [-> [ST [V KS]]]; cbv beta iota zeta delta [cm_step]; destruct (cm_control_kind ctl=?4); [exact I|].
   destruct ks; [destruct (cm_control_kind ctl=?5); exact I|now apply cm_c_short_step].
 - exact I.
Qed.
Definition cm_short_support_invariants sp ap p ast : Prop := cm_base_support_invariants sp ap p ast /\ cm_task_saved_generations (cm_astate_task ast) /\ cm_task_short_ready (cm_astate_task ast).
Lemma cm_short_support_initial sp ap p input : cm_task_succeeds sp (CMStartTask p input) -> cm_short_support_invariants sp ap p (cm_annotated_start (cm_source_function_policy sp) p input).
Proof. intro S; split; [now apply cm_base_support_initial|now split]. Qed.
Lemma cm_short_support_step sp ap p ast : cm_semantic_wf_program (cm_source_function_policy sp) p -> cm_short_support_invariants sp ap p ast -> cm_short_support_invariants sp ap p (cm_annotated_step sp ap ast).
Proof.
 intros WF [BASE [SAVED SHORT]]; split; [now apply cm_base_support_step|]. split; [now apply cm_task_saved_generations_step|].
 eapply cm_task_short_step_generation; [exact (proj1 (proj2 (proj2 (proj2 (proj1 BASE)))))|exact SAVED|exact SHORT].
Qed.
Lemma cm_short_support_iter sp ap p n ast : cm_semantic_wf_program (cm_source_function_policy sp) p -> cm_short_support_invariants sp ap p ast -> cm_short_support_invariants sp ap p (cm_annotated_iter sp ap n ast).
Proof. intro WF; revert ast; induction n; intros ast H; [exact H|apply IHn; now apply cm_short_support_step]. Qed.
Theorem cm_source_termination_short_invariants sp ap p input output status n :
 cm_semantic_wf_program (cm_source_function_policy sp) p -> cm_source_terminates sp p input output status ->
 cm_short_support_invariants sp ap p (cm_annotated_iter sp ap n (cm_annotated_start (cm_source_function_policy sp) p input)).
Proof.
 intros WF [INPUT [STATUS [st [ctl [RUN [SUCCESS OUTPUT]]]]]]; apply cm_short_support_iter; [exact WF|].
 apply cm_short_support_initial; exists st,ctl,status; auto.
Qed.
Theorem cm_source_termination_short_ready sp ap p input output status n :
 cm_semantic_wf_program (cm_source_function_policy sp) p -> cm_source_terminates sp p input output status ->
 cm_task_short_ready (cm_astate_task (cm_annotated_iter sp ap n (cm_annotated_start (cm_source_function_policy sp) p input))).
Proof. intros WF TERM; exact (proj2 (proj2 (cm_source_termination_short_invariants sp ap p input output status n WF TERM))). Qed.
