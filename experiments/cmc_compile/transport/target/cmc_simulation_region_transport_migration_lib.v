Require Export SimpleC.EE.QCP_demos_human.cmc_simulation_static_bases_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
(* Local support: saved generations are already present in the current list.
   Live flags need not agree, and we impose no new source/C precondition. *)
Definition cm_region_generations_incl old current := incl (map cm_region_gen old) (map cm_region_gen current).
Definition cm_frame_saved_generations current frame : Prop := match frame with
 | CMBlockK _ old | CMWhileBodyK _ _ _ old | CMCallK _ _ _ old _=>cm_region_generations_incl old current | _=>True end.
Fixpoint cm_frames_saved_generations current frames : Prop := match frames with []=>True | f::rest=>cm_frame_saved_generations current f /\ cm_frames_saved_generations current rest end.
Definition cm_task_saved_generations task : Prop := match task with
 | CMRTask _ _ _ st ks | CMLTask _ _ _ st ks | CMSTask _ _ _ st ks | CMVTask _ _ _ st ks | CMCTask _ _ _ st ks=>cm_frames_saved_generations (cm_state_regions st) ks | _=>True end.
Lemma cm_region_generations_refl regions : cm_region_generations_incl regions regions.
Proof. intros g H; exact H. Qed.
Lemma cm_region_generations_trans a b c : cm_region_generations_incl a b -> cm_region_generations_incl b c -> cm_region_generations_incl a c.
Proof. intros A B g H; apply B,A,H. Qed.
Lemma cm_region_generations_prepend prefix old : cm_region_generations_incl old (prefix++old).
Proof. intros g H; rewrite map_app; apply in_or_app; now right. Qed.
Lemma cm_region_generations_cons r old : cm_region_generations_incl old (r::old).
Proof. intros g H; now right. Qed.
Lemma cm_restore_regions_generations current old : cm_region_generations_incl current (cm_restore_regions current old).
Proof.
 induction current as [|r rest IH]; [intros g H; inversion H|].
 cbn [cm_restore_regions]; destruct (cm_regions_eqb (r::rest) old) eqn:E.
 - apply cm_regions_eqb_spec in E; subst; apply cm_region_generations_refl.
 - intros g [H|H]; cbn [map]; [left; destruct r; exact H|right; now apply IH].
Qed.
Lemma cm_region_base_absent regions gen : ~In gen (map cm_region_gen regions) -> cm_region_base regions gen=gen.
Proof.
 induction regions as [|r rest IH]; intro H; [reflexivity|]. cbn [cm_region_base]; destruct (cm_region_gen r=?gen) eqn:E.
 - apply Z.eqb_eq in E; exfalso; apply H; now left.
 - apply IH; intro IN; apply H; now right.
Qed.
Lemma cm_restore_regions_base_present current old gen : In gen (map cm_region_gen current) -> cm_region_base (cm_restore_regions current old) gen=cm_region_base current gen.
Proof.
 induction current as [|r rest IH]; intro IN; [inversion IN|]. cbn [cm_restore_regions]; destruct (cm_regions_eqb (r::rest) old) eqn:E.
 - apply cm_regions_eqb_spec in E; now subst.
 - destruct r; cbn [cm_retire_region cm_region_base cm_region_gen cm_region_base_field].
   destruct (gen0=?gen) eqn:G; [reflexivity|]. apply IH; destruct IN as [IN|IN]; [cbn in IN; apply Z.eqb_neq in G; congruence|exact IN].
Qed.
Lemma cm_restore_regions_base_absent current old gen : ~In gen (map cm_region_gen current) -> ~In gen (map cm_region_gen old) -> cm_region_base (cm_restore_regions current old) gen=gen.
Proof.
 induction current as [|r rest IH]; intros C O; [now apply cm_region_base_absent|].
 cbn [cm_restore_regions]; destruct (cm_regions_eqb (r::rest) old); [now apply cm_region_base_absent|].
 destruct r; cbn [cm_retire_region cm_region_base cm_region_gen cm_region_base_field].
 destruct (gen0=?gen) eqn:G; [apply Z.eqb_eq in G; exfalso; apply C; now left|].
 apply IH; [intro H; apply C; now right|exact O].
Qed.
Lemma cm_restore_regions_base_transport current old gen : cm_region_generations_incl old current -> cm_region_base (cm_restore_regions current old) gen=cm_region_base current gen.
Proof.
 intro SUB; destruct (in_dec Z.eq_dec gen (map cm_region_gen current)) as [IN|OUT]; [now apply cm_restore_regions_base_present|].
 rewrite (cm_region_base_absent current gen OUT). apply cm_restore_regions_base_absent; [exact OUT|intro H; apply OUT,SUB,H].
Qed.
Lemma cm_restore_regions_bases_transport current old limit : cm_region_generations_incl old current -> cm_region_bases_below_equal (cm_restore_regions current old) current limit.
Proof. intros H g B; now apply cm_restore_regions_base_transport. Qed.
Lemma cm_frames_saved_generations_mono frames old new : cm_region_generations_incl old new -> cm_frames_saved_generations old frames -> cm_frames_saved_generations new frames.
Proof. intro SUB; induction frames; cbn; auto; destruct a; cbn; intuition eauto using cm_region_generations_trans. Qed.
Lemma cm_enter_call_generations sp p fid values st : cm_region_generations_incl (cm_state_regions st) (cm_state_regions (cm_enter_call sp p fid values st)).
Proof. unfold cm_enter_call; rewrite cm_store_params_regions; apply cm_region_generations_prepend. Qed.
Lemma cm_activate_local_generations sp p fid slot st : cm_region_generations_incl (cm_state_regions st) (cm_state_regions (cm_activate_local sp p fid slot st)).
Proof. apply cm_region_generations_cons. Qed.
Lemma cm_restore_call_generations st env fp regions : cm_region_generations_incl (cm_state_regions st) (cm_state_regions (cm_restore_call st env fp regions)).
Proof. apply cm_restore_regions_generations. Qed.
Ltac cm_saved_reduce := repeat progress (cm_ann_reduce;
 cbn [cm_task_saved_generations cm_frames_saved_generations cm_frame_saved_generations cm_control_kind] in *).
Ltac cm_saved_cases := cm_saved_reduce;
 repeat match goal with |- context[if ?b then _ else _]=>cm_ann_bool b; cm_saved_reduce end.
Ltac cm_saved_transport := match goal with
 | |- cm_frames_saved_generations (cm_state_regions (cm_enter_call ?sp ?p ?fid ?vs ?st)) ?ks=>
 eapply (cm_frames_saved_generations_mono ks (cm_state_regions st)); [apply cm_enter_call_generations|assumption]
 | |- cm_frames_saved_generations (cm_state_regions (cm_activate_local ?sp ?p ?fid ?slot ?st)) ?ks=>
 eapply (cm_frames_saved_generations_mono ks (cm_state_regions st)); [apply cm_activate_local_generations|assumption]
 | |- cm_frames_saved_generations (cm_state_regions (cm_restore_call ?st ?env ?fp ?rs)) ?ks=>
 eapply (cm_frames_saved_generations_mono ks (cm_state_regions st)); [apply cm_restore_call_generations|assumption]
 | |- cm_frames_saved_generations (cm_state_regions (cm_restore_scope ?st ?env ?rs)) ?ks=>
 unfold cm_restore_scope; eapply (cm_frames_saved_generations_mono ks (cm_state_regions st)); [apply cm_restore_call_generations|assumption]
 end.
Ltac cm_saved_finish := repeat match goal with H:_ /\ _ |- _=>destruct H end;
 repeat first [assumption | exact I | solve [apply cm_region_generations_refl] | cm_saved_transport |
 solve [apply cm_enter_call_generations] | match goal with |- _ /\ _=>split end].
Lemma cm_r_saved_generations_step sp p fid expr st ks : cm_frames_saved_generations (cm_state_regions st) ks -> cm_task_saved_generations (cm_rstart sp p fid expr st ks).
Proof.
 destruct expr; intro H; cm_saved_cases; try cm_saved_finish.
 all: match goal with |- context[match ?xs with []=>_ | _::_=>_ end]=>destruct xs; cm_saved_cases; cm_saved_finish end.
Qed.
Lemma cm_l_saved_generations_step sp p fid expr st ks : cm_frames_saved_generations (cm_state_regions st) ks -> cm_task_saved_generations (cm_lstart sp p fid expr st ks).
Proof. destruct expr; intro H; cm_saved_cases; cm_saved_finish. Qed.
Lemma cm_s_saved_generations_step sp p fid stmt st ks : cm_frames_saved_generations (cm_state_regions st) ks -> cm_task_saved_generations (cm_sstart sp p fid stmt st ks).
Proof. destruct stmt; intro H; cm_saved_cases; cm_saved_finish. Qed.
Lemma cm_v_saved_generations_step sp p fid frame v st ks : cm_frames_saved_generations (cm_state_regions st) (frame::ks) -> cm_task_saved_generations (cm_vapply sp p fid frame v st ks).
Proof.
 destruct frame; intro H; cm_saved_cases; try cm_saved_finish.
 all: match goal with |- context[match ?xs with []=>_ | _::_=>_ end]=>destruct xs; cm_saved_cases; cm_saved_finish end.
Qed.
Lemma cm_c_saved_generations_step sp p fid frame ctl st ks : cm_frames_saved_generations (cm_state_regions st) (frame::ks) -> cm_task_saved_generations (cm_capply sp p fid frame ctl st ks).
Proof. destruct frame; intro H; cm_saved_cases; cm_saved_finish. Qed.
Lemma cm_task_saved_generations_step sp task : cm_task_saved_generations task -> cm_task_saved_generations (cm_step sp task).
Proof.
 destruct task as [p input|p fid expr st ks|p fid expr st ks|p fid stmt st ks|p fid v st ks|p fid ctl st ks|st ctl status]; intro H.
 - cbv beta iota zeta delta [cm_step cm_begin_call]; cm_saved_cases; cm_saved_finish.
 - now apply cm_r_saved_generations_step.
 - now apply cm_l_saved_generations_step.
 - now apply cm_s_saved_generations_step.
 - destruct ks; [exact I|now apply cm_v_saved_generations_step].
 - cbv beta iota zeta delta [cm_step]; destruct (cm_control_kind ctl=?4); [exact I|].
   destruct ks; [destruct (cm_control_kind ctl=?5); exact I|now apply cm_c_saved_generations_step].
 - exact I.
Qed.
Theorem cm_start_iter_saved_generations sp ap policy p input n : cm_task_saved_generations (cm_astate_task (cm_annotated_iter sp ap n (cm_annotated_start policy p input))).
Proof.
 assert (GEN : forall ast, cm_task_saved_generations (cm_astate_task ast) -> cm_task_saved_generations (cm_astate_task (cm_annotated_iter sp ap n ast))).
 { induction n; intros ast H; [exact H|apply IHn; now apply cm_task_saved_generations_step]. }
 apply GEN; exact I.
Qed.
