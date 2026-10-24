Require Export SimpleC.EE.QCP_demos_human.cmc_runtime_regions_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
(* Exact runtime predicates from cmc_preservation_invariant.c. Total HD uses
   the same explicit interpretation policy as annotation updates. *)
Definition cm_phase_is_halt phase := match phase with CAHaltP=>true | _=>false end.
Definition cm_phase_is_scope phase := match phase with CABlockP _ _ _ _ | CAWhileBodyP _ _ _ _ _ _=>true | _=>false end.
Definition cm_phase_oldfp phase := match phase with CACallP _ _ fp _ _=>fp | _=>0 end.
Definition cm_phase_caller phase := match phase with CACallP caller _ _ _ _=>caller | _=> -1 end.
Definition cm_phase_oldregions phase := match phase with CABlockP _ rs _ _ | CAWhileBodyP _ _ _ rs _ _ | CACallP _ _ _ rs _=>rs | _=>[] end.
Definition cm_region_frame_safe policy p all fid fp region : Prop := cm_region_live region=false \/
 (0<=cm_region_lo region /\ cm_region_lo region<=cm_region_hi region /\
 fp+8<=cm_region_base all (cm_region_gen region)+cm_region_lo region /\
 cm_region_base all (cm_region_gen region)+cm_region_hi region<=fp+cm_temp_offset policy p fid 0).
Fixpoint cm_region_prefix_safe policy p all fid fp active old : Prop := match active with
 | []=>old=[] | r::rest=>if cm_regions_eqb active old then True else cm_region_frame_safe policy p all fid fp r /\ cm_region_prefix_safe policy p all fid fp rest old end.
Fixpoint cm_region_dead_prefix active old : Prop := match active with
 | []=>old=[] | r::rest=>if cm_regions_eqb active old then True else cm_region_live r=false /\ cm_region_dead_prefix rest old end.
Definition cm_static_regions_layout p all : Prop := forall r, In r (cm_static_regions p) -> cm_region_live r=true ->
 0<=cm_region_lo r /\ cm_region_lo r<=cm_region_hi r /\ 16<=cm_region_base all (cm_region_gen r)+cm_region_lo r /\ cm_region_base all (cm_region_gen r)+cm_region_hi r<=cm_static_size p.
Definition cm_frame_segment policy p fid fp oldfp : Prop :=
 0<=fid /\ fid<Zlength (cm_program_functions p) /\ 16<=cm_static_size p /\ cm_static_size p<=fp /\
 fp+cm_frame_size (cm_program_structs p) (cm_function_at policy fid (cm_program_functions p))=oldfp /\
 fp+8<=fp+cm_temp_offset policy p fid 0 /\ fp+cm_temp_offset policy p fid 0<=oldfp /\ oldfp<=1048576.
Fixpoint cm_spills_within_frame policy p fid fp oldfp spills : Prop := match spills with []=>True | s::rest=>
 fp+cm_temp_offset policy p fid 0<=fp+cm_temp_offset policy p fid (cm_spill_slot s) /\
 fp+cm_temp_offset policy p fid (cm_spill_slot s)+8<=oldfp /\ cm_spills_within_frame policy p fid fp oldfp rest end.
Fixpoint cm_call_frames_lower lower calls : Prop := match calls with []=>True | f::rest=>lower<=cm_call_sim_base f /\ cm_call_frames_lower lower rest end.
Fixpoint cm_spill_list_lower policy p lower fid fp spills : Prop := match spills with []=>True | s::rest=>lower<=fp+cm_temp_offset policy p fid (cm_spill_slot s) /\ cm_spill_list_lower policy p lower fid fp rest end.
Fixpoint cm_spill_frames_lower policy p lower frames : Prop := match frames with []=>True | f::rest=>cm_spill_list_lower policy p lower (cm_spill_frame_fid f) (cm_spill_frame_fp f) (cm_spill_frame_spills f) /\ cm_spill_frames_lower policy p lower rest end.
Fixpoint cm_runtime_stack policy ap p all fid fp active cursors spills saved calls : Prop := match cursors with
 | []=>False
 | c::rest=>if cm_phase_is_call (cm_cursor_phase c) then
 cm_region_prefix_safe policy p all fid fp active (cm_phase_oldregions (cm_cursor_phase c)) /\
 cm_frame_segment policy p fid fp (cm_phase_oldfp (cm_cursor_phase c)) /\
 cm_spills_within_frame policy p fid fp (cm_phase_oldfp (cm_cursor_phase c)) spills /\
 saved<>[] /\ calls<>[] /\ cm_call_sim_base (hd (cm_call_nil ap) calls)=fp /\
 cm_call_sim_saved (hd (cm_call_nil ap) calls)=cm_phase_oldfp (cm_cursor_phase c) /\
 cm_spill_frame_fid (hd (cm_saved_nil ap) saved)=cm_phase_caller (cm_cursor_phase c) /\
 cm_spill_frame_fp (hd (cm_saved_nil ap) saved)=cm_phase_oldfp (cm_cursor_phase c) /\
 cm_runtime_stack policy ap p all (cm_phase_caller (cm_cursor_phase c)) (cm_phase_oldfp (cm_cursor_phase c)) (cm_phase_oldregions (cm_cursor_phase c)) rest (cm_spill_frame_spills (hd (cm_saved_nil ap) saved)) (tl saved) (tl calls)
 else if cm_phase_is_scope (cm_cursor_phase c) then 0<=fid /\
 cm_region_prefix_safe policy p all fid fp active (cm_phase_oldregions (cm_cursor_phase c)) /\
 cm_runtime_stack policy ap p all fid fp (cm_phase_oldregions (cm_cursor_phase c)) rest spills saved calls
 else if cm_phase_is_halt (cm_cursor_phase c) then fid= -1 /\ fp=1048576 /\ cm_region_dead_prefix active (cm_static_regions p) /\ 16<=cm_static_size p /\ cm_static_size p<=1048576 /\ rest=[] /\ spills=[] /\ saved=[] /\ calls=[] /\ cm_static_regions_layout p all
 else cm_runtime_stack policy ap p all fid fp active rest spills saved calls end.
Definition cm_task_runtime_invariant policy ap p task ann : Prop := match task with
 | CMStartTask q _=>q=p /\ ann=cm_initial_annotation
 | CMRTask q fid _ st _ | CMLTask q fid _ st _ | CMSTask q fid _ st _ | CMVTask q fid _ st _ | CMCTask q fid _ st _=>q=p /\ cm_regions_before (cm_state_regions st) (cm_state_nextgen st) /\ cm_runtime_stack policy ap p (cm_state_regions st) fid (cm_state_fp st) (cm_state_regions st) (cm_ann_cursors ann) (cm_ann_spills ann) (cm_ann_saved ann) (cm_ann_calls ann)
 | CMDoneTask st _ _=>cm_regions_before (cm_state_regions st) (cm_state_nextgen st) end.
Lemma cm_region_prefix_safe_refl policy p all fid fp regions : cm_region_prefix_safe policy p all fid fp regions regions.
Proof. destruct regions; [reflexivity|cbn [cm_region_prefix_safe]; assert (E:cm_regions_eqb (c::regions) (c::regions)=true) by (apply cm_regions_eqb_spec; reflexivity); now rewrite E]. Qed.
Lemma cm_region_dead_prefix_refl regions : cm_region_dead_prefix regions regions.
Proof. destruct regions; [reflexivity|cbn [cm_region_dead_prefix]; assert (E:cm_regions_eqb (c::regions) (c::regions)=true) by (apply cm_regions_eqb_spec; reflexivity); now rewrite E]. Qed.
Lemma cm_region_prefix_member policy p all fid fp active old region : cm_region_prefix_safe policy p all fid fp active old -> In region active -> In region old \/ cm_region_frame_safe policy p all fid fp region.
Proof.
 induction active as [|r rs IH]; cbn [cm_region_prefix_safe]; [intros H IN; inversion IN|].
 destruct (cm_regions_eqb (r::rs) old) eqn:E.
 - apply cm_regions_eqb_spec in E; intros H IN; left; now rewrite <- E.
 - intros [R RS] [->|IN]; [now right|now apply IH].
Qed.
Lemma cm_region_dead_member active old region : cm_region_dead_prefix active old -> In region active -> In region old \/ cm_region_live region=false.
Proof.
 induction active as [|r rs IH]; cbn [cm_region_dead_prefix]; [intros H IN; inversion IN|].
 destruct (cm_regions_eqb (r::rs) old) eqn:E.
 - apply cm_regions_eqb_spec in E; intros H IN; left; now rewrite <- E.
 - intros [R RS] [->|IN]; [now right|now apply IH].
Qed.
Lemma cm_restore_regions_dead_prefix active old : cm_region_dead_prefix (cm_restore_regions active old) old.
Proof.
 induction active as [|r rs IH]; cbn [cm_restore_regions]; [apply cm_region_dead_prefix_refl|].
 destruct (cm_regions_eqb (r::rs) old); [apply cm_region_dead_prefix_refl|].
 cbn [cm_region_dead_prefix]; destruct (cm_regions_eqb (cm_retire_region r::cm_restore_regions rs old) old); [exact I|].
 split; [destruct r; reflexivity|exact IH].
Qed.
Lemma cm_frame_segment_bounds policy p fid fp oldfp : cm_frame_segment policy p fid fp oldfp -> 16<=cm_static_size p /\ cm_static_size p<=fp /\ fp+8<=oldfp /\ oldfp<=1048576.
Proof. unfold cm_frame_segment; intros; repeat split; intuition lia. Qed.
Lemma cm_call_frames_lower_mono calls upper lower : lower<=upper -> cm_call_frames_lower upper calls -> cm_call_frames_lower lower calls.
Proof. intro L; induction calls; cbn; [auto|intros [H T]; split; [lia|now apply IHcalls]]. Qed.
Lemma cm_spill_list_lower_mono policy p fid fp spills upper lower : lower<=upper -> cm_spill_list_lower policy p upper fid fp spills -> cm_spill_list_lower policy p lower fid fp spills.
Proof. intro L; induction spills; cbn; [auto|intros [H T]; split; [lia|now apply IHspills]]. Qed.
Lemma cm_spill_frames_lower_mono policy p frames upper lower : lower<=upper -> cm_spill_frames_lower policy p upper frames -> cm_spill_frames_lower policy p lower frames.
Proof. intro L; induction frames; cbn; [auto|intros [H T]; split; [eapply cm_spill_list_lower_mono; eauto|now apply IHframes]]. Qed.
Lemma cm_spills_within_lower policy p fid fp oldfp spills : fp<=fp+cm_temp_offset policy p fid 0 -> cm_spills_within_frame policy p fid fp oldfp spills -> cm_spill_list_lower policy p fp fid fp spills.
Proof. intro B; induction spills; cbn; [auto|intros [L [U T]]; split; [lia|now apply IHspills]]. Qed.
Lemma cm_runtime_stack_fp_bounds policy ap p all cursors fid fp active spills saved calls :
 cm_runtime_stack policy ap p all fid fp active cursors spills saved calls -> 16<=cm_static_size p /\ cm_static_size p<=fp /\ fp<=1048576.
Proof.
 revert fid fp active spills saved calls; induction cursors as [|c rest IH]; intros fid fp active spills saved calls H; [contradiction|].
 cbn [cm_runtime_stack] in H; destruct (cm_phase_is_call (cm_cursor_phase c)).
 - destruct H as [_ [SEG _]]; pose proof (cm_frame_segment_bounds _ _ _ _ _ SEG); intuition lia.
 - destruct (cm_phase_is_scope (cm_cursor_phase c)); [destruct H as [_ [_ H]]; eapply IH; exact H|].
   destruct (cm_phase_is_halt (cm_cursor_phase c)); [intuition lia|eapply IH; exact H].
Qed.
Lemma cm_runtime_stack_lower policy ap p all cursors fid fp active spills saved calls :
 cm_runtime_stack policy ap p all fid fp active cursors spills saved calls -> cm_call_frames_lower fp calls /\ cm_spill_list_lower policy p fp fid fp spills /\ cm_spill_frames_lower policy p fp saved.
Proof.
 revert fid fp active spills saved calls; induction cursors as [|c rest IH]; intros fid fp active spills saved calls H; [contradiction|].
 cbn [cm_runtime_stack] in H; destruct (cm_phase_is_call (cm_cursor_phase c)).
 - destruct H as [PREFIX [SEG [SPILLS [S [C [BASE [SAVED [FID [FP REC]]]]]]]]].
   destruct saved as [|sf ss]; [contradiction|]; destruct calls as [|cf cs]; [contradiction|]; cbn in BASE,SAVED,FID,FP,REC.
   pose proof (IH _ _ _ _ _ _ REC) as [CL [SL SFL]].
   pose proof (cm_frame_segment_bounds _ _ _ _ _ SEG) as [_ [_ [B _]]].
   split; [split; [lia|eapply cm_call_frames_lower_mono; [|exact CL]; lia]|].
   split; [eapply cm_spills_within_lower; [|exact SPILLS]; unfold cm_frame_segment in SEG; intuition lia|].
   split; [rewrite FID,FP; eapply cm_spill_list_lower_mono; [|exact SL]; lia|eapply cm_spill_frames_lower_mono; [|exact SFL]; lia].
 - destruct (cm_phase_is_scope (cm_cursor_phase c)); [destruct H as [_ [_ H]]; eapply IH; exact H|].
   destruct (cm_phase_is_halt (cm_cursor_phase c)).
   + destruct H as [_ [_ [_ [_ [_ [_ [-> [-> [-> _]]]]]]]]]; repeat split; exact I.
   + eapply IH; exact H.
Qed.
Lemma cm_runtime_stack_nonempty policy ap p all fid fp active cursors spills saved calls : cm_runtime_stack policy ap p all fid fp active cursors spills saved calls -> cursors<>[].
Proof. intros H ->; exact H. Qed.
Lemma cm_task_runtime_initial policy ap p input : cm_task_runtime_invariant policy ap p (CMStartTask p input) cm_initial_annotation.
Proof. now split. Qed.
Lemma cm_runtime_stack_frame_ceiling policy ap p all cursors fid fp active spills saved calls : cm_runtime_stack policy ap p all fid fp active cursors spills saved calls -> fid= -1 \/ fp+cm_temp_offset policy p fid 0<=1048576.
Proof.
 revert fid fp active spills saved calls; induction cursors as [|c rest IH]; intros fid fp active spills saved calls H; [contradiction|].
 cbn [cm_runtime_stack] in H; destruct (cm_phase_is_call (cm_cursor_phase c)).
 - destruct H as [_ [SEG _]]; unfold cm_frame_segment in SEG; right; intuition lia.
 - destruct (cm_phase_is_scope (cm_cursor_phase c)); [destruct H as [_ [_ H]]; eapply IH; exact H|].
   destruct (cm_phase_is_halt (cm_cursor_phase c)); [left; apply H|eapply IH; exact H].
Qed.
Lemma cm_runtime_stack_region_bounds policy ap p all cursors fid fp active spills saved calls region :
 cm_runtime_stack policy ap p all fid fp active cursors spills saved calls -> In region active -> cm_region_live region=true ->
 0<=cm_region_lo region /\ cm_region_lo region<=cm_region_hi region /\
 16<=cm_region_base all (cm_region_gen region)+cm_region_lo region /\
 cm_region_base all (cm_region_gen region)+cm_region_hi region<=1048576 /\
 (cm_region_base all (cm_region_gen region)+cm_region_hi region<=cm_static_size p \/ fp+8<=cm_region_base all (cm_region_gen region)+cm_region_lo region).
Proof.
 revert fid fp active spills saved calls; induction cursors as [|c rest IH]; intros fid fp active spills saved calls H IN LIVE; [contradiction|].
 cbn [cm_runtime_stack] in H; destruct (cm_phase_is_call (cm_cursor_phase c)).
 - destruct H as [PREFIX [SEG [_ [_ [_ [_ [_ [_ [_ REC]]]]]]]]].
   pose proof (cm_region_prefix_member _ _ _ _ _ _ _ _ PREFIX IN) as [OLD|NEW].
   + pose proof (IH _ _ _ _ _ _ REC OLD LIVE) as B; pose proof (cm_frame_segment_bounds _ _ _ _ _ SEG); intuition lia.
   + unfold cm_region_frame_safe in NEW; destruct NEW as [DEAD|B]; [congruence|]. unfold cm_frame_segment in SEG; intuition lia.
 - destruct (cm_phase_is_scope (cm_cursor_phase c)).
   + destruct H as [FID [PREFIX REC]].
     pose proof (cm_region_prefix_member _ _ _ _ _ _ _ _ PREFIX IN) as [OLD|NEW].
     * eapply IH; eauto.
     * pose proof (cm_runtime_stack_fp_bounds _ _ _ _ _ _ _ _ _ _ _ REC) as B.
       pose proof (cm_runtime_stack_frame_ceiling _ _ _ _ _ _ _ _ _ _ _ REC) as CEIL.
       unfold cm_region_frame_safe in NEW; destruct NEW as [DEAD|NEW]; [congruence|]; intuition lia.
   + destruct (cm_phase_is_halt (cm_cursor_phase c)).
     * destruct H as [FID [FP [DEAD [LOW [UP [_ [_ [_ [_ STATIC]]]]]]]]].
       pose proof (cm_region_dead_member _ _ _ DEAD IN) as [OLD|NOTLIVE]; [|congruence].
       specialize (STATIC region OLD LIVE); intuition lia.
     * eapply IH; eauto.
Qed.
Lemma cm_spills_within_temp_lower policy p fid fp oldfp spills : cm_spills_within_frame policy p fid fp oldfp spills -> cm_spill_list_lower policy p (fp+cm_temp_offset policy p fid 0) fid fp spills.
Proof. induction spills; cbn; intuition. Qed.
Lemma cm_runtime_stack_current_machine_lower policy ap p all cursors fid fp active spills saved calls :
 cm_runtime_stack policy ap p all fid fp active cursors spills saved calls -> 0<=fid ->
 calls<>[] /\ cm_call_sim_base (hd (cm_call_nil ap) calls)=fp /\
 cm_call_frames_lower (fp+cm_temp_offset policy p fid 0) (tl calls) /\
 cm_spill_list_lower policy p (fp+cm_temp_offset policy p fid 0) fid fp spills /\
 cm_spill_frames_lower policy p (fp+cm_temp_offset policy p fid 0) saved.
Proof.
 revert fid fp active spills saved calls; induction cursors as [|c rest IH]; intros fid fp active spills saved calls H FID; [contradiction|].
 cbn [cm_runtime_stack] in H; destruct (cm_phase_is_call (cm_cursor_phase c)).
 - destruct H as [PREFIX [SEG [SPILLS [S [C [BASE [SAVED [SFID [SFP REC]]]]]]]]].
   pose proof (cm_runtime_stack_lower _ _ _ _ _ _ _ _ _ _ _ REC) as [CL [SL SFL]].
   assert (B: fp+cm_temp_offset policy p fid 0<=cm_phase_oldfp (cm_cursor_phase c)) by (unfold cm_frame_segment in SEG; intuition).
   split; [exact C|]; split; [exact BASE|]; split; [eapply cm_call_frames_lower_mono; eauto|].
   split; [eapply cm_spills_within_temp_lower; eauto|].
   destruct saved as [|sf ss]; [contradiction|]; cbn in SFID,SFP,SL,SFL; split.
   + rewrite SFID,SFP; eapply cm_spill_list_lower_mono; eauto.
   + eapply cm_spill_frames_lower_mono; eauto.
 - destruct (cm_phase_is_scope (cm_cursor_phase c)); [destruct H as [_ [_ H]]; eapply IH; eauto|].
   destruct (cm_phase_is_halt (cm_cursor_phase c)); [destruct H as [BAD _]; lia|eapply IH; eauto].
Qed.
