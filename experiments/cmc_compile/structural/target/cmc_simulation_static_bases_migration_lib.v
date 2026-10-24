Require Export SimpleC.EE.QCP_demos_human.cmc_simulation_generation_annotation_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Definition cm_region_bases_below_equal left right limit : Prop := forall gen,gen<limit -> cm_region_base left gen=cm_region_base right gen.
Definition cm_static_regions p := cm_global_regions p (cm_program_globals p) 0 ++ cm_string_regions p (cm_program_strings p) 0.
Definition cm_task_static_bases p task : Prop := match task with
 | CMStartTask q _=>q=p
 | CMRTask q _ _ st _ | CMLTask q _ _ st _ | CMSTask q _ _ st _ | CMVTask q _ _ st _ | CMCTask q _ _ st _=>q=p /\ cm_region_bases_below_equal (cm_state_regions st) (cm_static_regions p) (cm_first_dynamic_generation p)
 | CMDoneTask st _ _=>cm_region_bases_below_equal (cm_state_regions st) (cm_static_regions p) (cm_first_dynamic_generation p) end.
(* A proved local refinement records the same property for saved regions.
   It is initialized from Start, not added to the original C contract. *)
Definition cm_frame_saved_static_bases p frame : Prop := match frame with
 | CMBlockK _ regions | CMWhileBodyK _ _ _ regions | CMCallK _ _ _ regions _=>cm_region_bases_below_equal regions (cm_static_regions p) (cm_first_dynamic_generation p) | _=>True end.
Fixpoint cm_frames_saved_static_bases p frames : Prop := match frames with []=>True | frame::rest=>cm_frame_saved_static_bases p frame /\ cm_frames_saved_static_bases p rest end.
Definition cm_task_saved_static_bases p task : Prop := match task with
 | CMRTask _ _ _ _ ks | CMLTask _ _ _ _ ks | CMSTask _ _ _ _ ks | CMVTask _ _ _ _ ks | CMCTask _ _ _ _ ks=>cm_frames_saved_static_bases p ks | _=>True end.
Lemma cm_region_bases_refl regions limit : cm_region_bases_below_equal regions regions limit.
Proof. intros g H; reflexivity. Qed.
Lemma cm_region_bases_trans a b c limit : cm_region_bases_below_equal a b limit -> cm_region_bases_below_equal b c limit -> cm_region_bases_below_equal a c limit.
Proof. intros A B g H; rewrite (A g H); now apply B. Qed.
Lemma cm_region_bases_cons_fresh r rest limit : limit<=cm_region_gen r -> cm_region_bases_below_equal (r::rest) rest limit.
Proof. intros B g H; cbn [cm_region_base]; destruct (cm_region_gen r=?g) eqn:E; [apply Z.eqb_eq in E; lia|reflexivity]. Qed.
Lemma cm_regions_for_slots_bases structs slots first base rest limit : limit<=first ->
 cm_region_bases_below_equal (cm_regions_for_slots structs slots first base++rest) rest limit.
Proof.
 revert first base; induction slots; intros first base H; [apply cm_region_bases_refl|].
 cbn [cm_regions_for_slots app]; eapply cm_region_bases_trans; [apply cm_region_bases_cons_fresh; exact H|apply IHslots; lia].
Qed.
Lemma cm_restore_regions_base_common current old gen value :
 cm_region_base current gen=value -> cm_region_base old gen=value -> cm_region_base (cm_restore_regions current old) gen=value.
Proof.
 induction current as [|[g b l h w live] rest IH]; intros C O; [exact O|].
 cbn [cm_restore_regions]; destruct (cm_regions_eqb _ old); [exact O|].
 cbn [cm_region_base cm_retire_region cm_region_gen cm_region_base_field] in *.
 destruct (g=?gen); [exact C|now apply IH].
Qed.
Lemma cm_restore_regions_bases_common current old reference limit :
 cm_region_bases_below_equal current reference limit -> cm_region_bases_below_equal old reference limit ->
 cm_region_bases_below_equal (cm_restore_regions current old) reference limit.
Proof. intros C O g B; apply cm_restore_regions_base_common; [apply C|apply O]; exact B. Qed.
Lemma cm_store_params_regions sp p fid values index st : cm_state_regions (cm_store_params sp p fid values index st)=cm_state_regions st.
Proof. revert index st; induction values; intros; cbn [cm_store_params]; [reflexivity|rewrite IHvalues; reflexivity]. Qed.
Lemma cm_enter_call_static_bases sp p fid values st : cm_first_dynamic_generation p<=cm_state_nextgen st ->
 cm_region_bases_below_equal (cm_state_regions st) (cm_static_regions p) (cm_first_dynamic_generation p) ->
 cm_region_bases_below_equal (cm_state_regions (cm_enter_call sp p fid values st)) (cm_static_regions p) (cm_first_dynamic_generation p).
Proof.
 intros LOW BASE; unfold cm_enter_call; rewrite cm_store_params_regions.
 change (cm_region_bases_below_equal (cm_regions_for_slots (cm_program_structs p) (cm_function_params (cm_source_function_at sp fid p)) (cm_state_nextgen st)
 (cm_state_fp st-cm_frame_size (cm_program_structs p) (cm_source_function_at sp fid p)+8)++cm_state_regions st) (cm_static_regions p) (cm_first_dynamic_generation p)).
 eapply cm_region_bases_trans; [apply cm_regions_for_slots_bases; exact LOW|exact BASE].
Qed.
Lemma cm_activate_local_static_bases sp p fid slot st : cm_first_dynamic_generation p<=cm_state_nextgen st ->
 cm_region_bases_below_equal (cm_state_regions st) (cm_static_regions p) (cm_first_dynamic_generation p) ->
 cm_region_bases_below_equal (cm_state_regions (cm_activate_local sp p fid slot st)) (cm_static_regions p) (cm_first_dynamic_generation p).
Proof.
 intros LOW BASE; unfold cm_activate_local; cbv beta iota zeta delta [cm_state_regions];
 eapply cm_region_bases_trans; [apply cm_region_bases_cons_fresh; exact LOW|exact BASE].
Qed.
Lemma cm_restore_call_static_bases p st env fp regions :
 cm_region_bases_below_equal (cm_state_regions st) (cm_static_regions p) (cm_first_dynamic_generation p) ->
 cm_region_bases_below_equal regions (cm_static_regions p) (cm_first_dynamic_generation p) ->
 cm_region_bases_below_equal (cm_state_regions (cm_restore_call st env fp regions)) (cm_static_regions p) (cm_first_dynamic_generation p).
Proof. apply cm_restore_regions_bases_common. Qed.
Ltac cm_bases_reduce := repeat progress (cm_ann_reduce;
 cbv beta iota zeta delta [cm_task_static_bases cm_task_saved_static_bases cm_frames_saved_static_bases cm_frame_saved_static_bases cm_control_kind] in *).
Ltac cm_bases_cases := cm_bases_reduce;
 repeat match goal with |- context[if ?b then _ else _]=>cm_ann_bool b; cm_bases_reduce end.
Ltac cm_bases_finish := repeat match goal with H:_ /\ _ |- _=>destruct H end;
 repeat first [assumption | reflexivity | exact I |
 match goal with
 | |- cm_region_bases_below_equal (cm_state_regions (cm_enter_call _ _ _ _ _)) _ _=>apply cm_enter_call_static_bases
 | |- cm_region_bases_below_equal (cm_state_regions (cm_activate_local _ _ _ _ _)) _ _=>apply cm_activate_local_static_bases
 | |- cm_region_bases_below_equal (cm_state_regions (cm_restore_call _ _ _ _)) _ _=>apply cm_restore_call_static_bases
 | |- cm_region_bases_below_equal (cm_state_regions (cm_restore_scope _ _ _)) _ _=>unfold cm_restore_scope; apply cm_restore_call_static_bases
 | |- _ /\ _=>split end].
Lemma cm_r_static_bases_step sp p fid expr st ks : cm_first_dynamic_generation p<=cm_state_nextgen st ->
 cm_region_bases_below_equal (cm_state_regions st) (cm_static_regions p) (cm_first_dynamic_generation p) -> cm_frames_saved_static_bases p ks ->
 cm_task_static_bases p (cm_rstart sp p fid expr st ks) /\ cm_task_saved_static_bases p (cm_rstart sp p fid expr st ks).
Proof.
 destruct expr; intros LOW BASE SAVED; cm_bases_cases; try cm_bases_finish.
 all: match goal with |- context[match ?xs with []=>_ | _::_=>_ end]=>destruct xs; cm_bases_cases; cm_bases_finish end.
Qed.
Lemma cm_l_static_bases_step sp p fid expr st ks :
 cm_region_bases_below_equal (cm_state_regions st) (cm_static_regions p) (cm_first_dynamic_generation p) -> cm_frames_saved_static_bases p ks ->
 cm_task_static_bases p (cm_lstart sp p fid expr st ks) /\ cm_task_saved_static_bases p (cm_lstart sp p fid expr st ks).
Proof. destruct expr; intros BASE SAVED; cm_bases_cases; cm_bases_finish. Qed.
Lemma cm_s_static_bases_step sp p fid stmt st ks : cm_first_dynamic_generation p<=cm_state_nextgen st ->
 cm_region_bases_below_equal (cm_state_regions st) (cm_static_regions p) (cm_first_dynamic_generation p) -> cm_frames_saved_static_bases p ks ->
 cm_task_static_bases p (cm_sstart sp p fid stmt st ks) /\ cm_task_saved_static_bases p (cm_sstart sp p fid stmt st ks).
Proof. destruct stmt; intros LOW BASE SAVED; cm_bases_cases; cm_bases_finish. Qed.
Lemma cm_v_static_bases_step sp p fid frame v st ks : cm_first_dynamic_generation p<=cm_state_nextgen st ->
 cm_region_bases_below_equal (cm_state_regions st) (cm_static_regions p) (cm_first_dynamic_generation p) -> cm_frames_saved_static_bases p (frame::ks) ->
 cm_task_static_bases p (cm_vapply sp p fid frame v st ks) /\ cm_task_saved_static_bases p (cm_vapply sp p fid frame v st ks).
Proof.
 destruct frame; intros LOW BASE SAVED; cm_bases_cases; try cm_bases_finish.
 all: match goal with |- context[match ?xs with []=>_ | _::_=>_ end]=>destruct xs; cm_bases_cases; cm_bases_finish end.
Qed.
Lemma cm_c_static_bases_step sp p fid frame ctl st ks :
 cm_region_bases_below_equal (cm_state_regions st) (cm_static_regions p) (cm_first_dynamic_generation p) -> cm_frames_saved_static_bases p (frame::ks) ->
 cm_task_static_bases p (cm_capply sp p fid frame ctl st ks) /\ cm_task_saved_static_bases p (cm_capply sp p fid frame ctl st ks).
Proof. destruct frame; intros BASE SAVED; cm_bases_cases; cm_bases_finish. Qed.
Lemma cm_task_static_bases_step_generation sp p task : cm_task_generation_below (cm_source_function_policy sp) p task ->
 cm_task_static_bases p task -> cm_task_saved_static_bases p task ->
 cm_task_static_bases p (cm_step sp task) /\ cm_task_saved_static_bases p (cm_step sp task).
Proof.
 destruct task as [q input|q fid expr st ks|q fid expr st ks|q fid stmt st ks|q fid v st ks|q fid ctl st ks|st ctl status]; intros G B S.
 - change (q=p) in B; subst q; cbv beta iota zeta delta [cm_step cm_begin_call]; cm_bases_cases; cm_bases_finish.
   all: try apply cm_region_bases_refl; try reflexivity.
 - destruct B as [-> B]; apply cm_r_static_bases_step; auto; exact (proj1 (proj1 (proj2 G))).
 - destruct B as [-> B]; now apply cm_l_static_bases_step.
 - destruct B as [-> B]; apply cm_s_static_bases_step; auto; exact (proj1 (proj1 (proj2 G))).
 - destruct B as [-> B]; destruct ks as [|frame ks]; [now split|apply cm_v_static_bases_step; auto; exact (proj1 (proj1 (proj2 G)))].
 - destruct B as [-> B]; cbv beta iota zeta delta [cm_step]; destruct (cm_control_kind ctl=?4); [now split|].
   destruct ks as [|frame ks]; [destruct (cm_control_kind ctl=?5); now split|now apply cm_c_static_bases_step].
 - now split.
Qed.
Definition cm_base_support_invariants sp ap p ast := cm_structural_support_invariants sp ap p ast /\
 cm_task_static_bases p (cm_astate_task ast) /\ cm_task_saved_static_bases p (cm_astate_task ast).
Lemma cm_base_support_initial sp ap p input : cm_task_succeeds sp (CMStartTask p input) -> cm_base_support_invariants sp ap p (cm_annotated_start (cm_source_function_policy sp) p input).
Proof. intro S; split; [now apply cm_structural_support_initial|split; [reflexivity|exact I]]. Qed.
Lemma cm_base_support_step sp ap p ast : cm_semantic_wf_program (cm_source_function_policy sp) p -> cm_base_support_invariants sp ap p ast -> cm_base_support_invariants sp ap p (cm_annotated_step sp ap ast).
Proof. intros WF [SUP [B S]]; split; [now apply cm_structural_support_step|]. apply cm_task_static_bases_step_generation; auto; exact (proj1 (proj2 (proj2 (proj2 SUP)))). Qed.
Lemma cm_base_support_iter sp ap p n ast : cm_semantic_wf_program (cm_source_function_policy sp) p -> cm_base_support_invariants sp ap p ast -> cm_base_support_invariants sp ap p (cm_annotated_iter sp ap n ast).
Proof. intro WF; revert ast; induction n; intros ast H; [exact H|apply IHn; now apply cm_base_support_step]. Qed.
Theorem cm_source_termination_base_invariants sp ap p input output status n :
 cm_semantic_wf_program (cm_source_function_policy sp) p -> cm_source_terminates sp p input output status ->
 cm_base_support_invariants sp ap p (cm_annotated_iter sp ap n (cm_annotated_start (cm_source_function_policy sp) p input)).
Proof.
 intros WF [INPUT [STATUS [st [ctl [RUN [SUCCESS OUTPUT]]]]]]; apply cm_base_support_iter; [exact WF|].
 apply cm_base_support_initial; exists st,ctl,status; auto.
Qed.
Theorem cm_source_termination_static_bases sp ap p input output status n :
 cm_semantic_wf_program (cm_source_function_policy sp) p -> cm_source_terminates sp p input output status ->
 cm_task_static_bases p (cm_astate_task (cm_annotated_iter sp ap n (cm_annotated_start (cm_source_function_policy sp) p input))).
Proof. intros WF TERM; exact (proj1 (proj2 (cm_source_termination_base_invariants sp ap p input output status n WF TERM))). Qed.
