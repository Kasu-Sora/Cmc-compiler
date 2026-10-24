Require Export SimpleC.EE.QCP_demos_human.cmc_runtime_transport_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Definition cm_runtime_core policy ap p fid st ann : Prop := cm_regions_before (cm_state_regions st) (cm_state_nextgen st) /\
 cm_runtime_stack policy ap p (cm_state_regions st) fid (cm_state_fp st) (cm_state_regions st) (cm_ann_cursors ann) (cm_ann_spills ann) (cm_ann_saved ann) (cm_ann_calls ann).
Lemma cm_runtime_core_fields policy ap p fid st ann st2 ann2 : cm_runtime_core policy ap p fid st ann ->
 cm_state_fp st2=cm_state_fp st -> cm_state_nextgen st2=cm_state_nextgen st -> cm_state_regions st2=cm_state_regions st ->
 cm_ann_cursors ann2=cm_ann_cursors ann -> cm_ann_spills ann2=cm_ann_spills ann -> cm_ann_saved ann2=cm_ann_saved ann -> cm_ann_calls ann2=cm_ann_calls ann -> cm_runtime_core policy ap p fid st2 ann2.
Proof. unfold cm_runtime_core; intros H FP GEN REG CUR SP SV CL; now rewrite FP,GEN,REG,CUR,SP,SV,CL. Qed.
Lemma cm_runtime_core_plain policy ap p fid st ann pc temp breakpc continuepc : cm_runtime_core policy ap p fid st ann -> cm_runtime_core policy ap p fid st (cm_ann_plain pc temp breakpc continuepc ann).
Proof. exact (fun H=>H). Qed.
Lemma cm_runtime_core_linear policy ap p fid st ann code : cm_runtime_core policy ap p fid st ann -> cm_runtime_core policy ap p fid st (cm_ann_linear code ann).
Proof. exact (fun H=>H). Qed.
Lemma cm_runtime_core_io policy ap p fid st ann input output : cm_runtime_core policy ap p fid st ann -> cm_runtime_core policy ap p fid (cm_state_io st input output) ann.
Proof. exact (fun H=>H). Qed.
Lemma cm_runtime_core_store policy ap p fid st ann ty ptr value : cm_runtime_core policy ap p fid st ann -> cm_runtime_core policy ap p fid (cm_state_store ty ptr value st) ann.
Proof. exact (fun H=>H). Qed.
Lemma cm_runtime_core_push_plain policy ap p fid st ann phase pc temp breakpc continuepc : cm_phase_is_call phase=false -> cm_phase_is_scope phase=false -> cm_phase_is_halt phase=false -> cm_runtime_core policy ap p fid st ann -> cm_runtime_core policy ap p fid st (cm_ann_push phase pc temp breakpc continuepc ann).
Proof.
 intros C S H [B R]; split; [exact B|]. cbn [cm_ann_push cm_ann_cursors cm_ann_spills cm_ann_saved cm_ann_calls cm_runtime_stack cm_cursor_phase]; now rewrite C,S,H.
Qed.
Lemma cm_runtime_core_pop_plain policy ap p fid st ann phase owner ob oc rest pc : cm_ann_cursors ann=CMACursor phase owner ob oc::rest -> cm_phase_is_call phase=false -> cm_phase_is_scope phase=false -> cm_phase_is_halt phase=false -> cm_runtime_core policy ap p fid st ann -> cm_runtime_core policy ap p fid st (cm_ann_pop ap pc ann).
Proof.
 intros CUR C S H [B R]; rewrite CUR in R; cbn [cm_runtime_stack cm_cursor_phase] in R; rewrite C,S,H in R.
 split; [exact B|]; cbn [cm_ann_pop cm_ann_cursors cm_ann_spills cm_ann_saved cm_ann_calls]; now rewrite CUR.
Qed.
Lemma cm_runtime_core_replace_plain policy ap p fid st ann oldphase newphase owner ob oc rest pc temp breakpc continuepc : cm_ann_cursors ann=CMACursor oldphase owner ob oc::rest -> cm_phase_is_call oldphase=false -> cm_phase_is_scope oldphase=false -> cm_phase_is_halt oldphase=false -> cm_phase_is_call newphase=false -> cm_phase_is_scope newphase=false -> cm_phase_is_halt newphase=false -> cm_runtime_core policy ap p fid st ann -> cm_runtime_core policy ap p fid st (cm_ann_replace ap newphase pc temp breakpc continuepc ann).
Proof.
 intros CUR C S H NC NS NH [B R]; rewrite CUR in R; cbn [cm_runtime_stack cm_cursor_phase] in R; rewrite C,S,H in R.
 split; [exact B|]; cbn [cm_ann_replace cm_ann_cursors cm_ann_spills cm_ann_saved cm_ann_calls]; rewrite CUR; cbn [hd tl cm_runtime_stack cm_cursor_phase]; now rewrite NC,NS,NH.
Qed.
Lemma cm_runtime_core_enter_scope policy ap p fid st ann phase pc temp breakpc continuepc : 0<=fid -> cm_phase_is_scope phase=true -> cm_phase_is_call phase=false -> cm_phase_oldregions phase=cm_state_regions st -> cm_runtime_core policy ap p fid st ann -> cm_runtime_core policy ap p fid st (cm_ann_push phase pc temp breakpc continuepc ann).
Proof.
 intros F S C OLD [B R]; split; [exact B|].
 cbn [cm_ann_push cm_ann_cursors cm_ann_spills cm_ann_saved cm_ann_calls cm_runtime_stack cm_cursor_phase]; rewrite C,S,OLD; split; [exact F|]; split; [apply cm_region_prefix_safe_refl|exact R].
Qed.
Lemma cm_region_prefix_generations_incl policy p all fid fp active old : cm_region_prefix_safe policy p all fid fp active old -> cm_region_generations_incl old active.
Proof. intros H g IN; apply in_map_iff in IN; destruct IN as [r [<- IN]]; apply in_map; eapply cm_region_prefix_suffix_incl; eauto. Qed.
Lemma cm_runtime_core_leave_scope policy ap p fid st ann phase env old owner ob oc rest pc :
 cm_ann_cursors ann=CMACursor phase owner ob oc::rest -> cm_phase_is_scope phase=true -> cm_phase_is_call phase=false -> cm_phase_oldregions phase=old -> cm_runtime_core policy ap p fid st ann -> cm_runtime_core policy ap p fid (cm_restore_scope st env old) (cm_ann_pop ap pc ann).
Proof.
 intros CUR S C OLD [B R]; rewrite CUR in R; cbn [cm_runtime_stack cm_cursor_phase] in R; rewrite C,S,OLD in R; destruct R as [FID [PREFIX R]].
 pose proof (cm_region_prefix_generations_incl _ _ _ _ _ _ _ PREFIX) as INC; split.
 - now apply cm_restore_call_regions_before.
 - cbn [cm_ann_pop cm_ann_cursors cm_ann_spills cm_ann_saved cm_ann_calls]; rewrite CUR; cbn [tl]. apply cm_runtime_stack_restore_incl; assumption.
Qed.
Lemma cm_spills_within_remove policy p fid fp oldfp spills slot : cm_spills_within_frame policy p fid fp oldfp spills -> cm_spills_within_frame policy p fid fp oldfp (cm_spill_remove slot spills).
Proof. induction spills; [auto|intros [L [U T]]; cbn [cm_spill_remove]; destruct (cm_spill_slot a=?slot); [now apply IHspills|split; [exact L|]; split; [exact U|now apply IHspills]]]. Qed.
Lemma cm_spills_within_put policy p fid fp oldfp spills slot value : cm_frame_segment policy p fid fp oldfp -> 0<=slot<cm_temp_slots (cm_function_at policy fid (cm_program_functions p)) -> cm_spills_within_frame policy p fid fp oldfp spills -> cm_spills_within_frame policy p fid fp oldfp (cm_spill_put slot value spills).
Proof.
 intros SEG SLOT H; cbn [cm_spill_put cm_spills_within_frame cm_spill_slot]; split.
 - unfold cm_temp_offset; lia.
 - split; [unfold cm_frame_segment,cm_frame_size,cm_temp_offset in *; intuition lia|now apply cm_spills_within_remove].
Qed.
Lemma cm_runtime_stack_spill_put policy ap p all cursors fid fp active spills saved calls slot value : 0<=fid -> 0<=slot<cm_temp_slots (cm_function_at policy fid (cm_program_functions p)) -> cm_runtime_stack policy ap p all fid fp active cursors spills saved calls -> cm_runtime_stack policy ap p all fid fp active cursors (cm_spill_put slot value spills) saved calls.
Proof.
 revert fid fp active spills saved calls; induction cursors as [|c rest IH]; intros fid fp active spills saved calls F SLOT H; [contradiction|].
 cbn [cm_runtime_stack] in *; destruct (cm_phase_is_call (cm_cursor_phase c)).
 - destruct H as [PRE [SEG [SP T]]]; split; [exact PRE|]; split; [exact SEG|]; split; [eapply cm_spills_within_put; eauto|exact T].
 - destruct (cm_phase_is_scope (cm_cursor_phase c)).
   + destruct H as [FID [PRE R]]; split; [exact FID|]; split; [exact PRE|eapply IH; eauto].
   + destruct (cm_phase_is_halt (cm_cursor_phase c)); [destruct H as [BAD _]; lia|eapply IH; eauto].
Qed.
Lemma cm_runtime_core_spill_put policy ap p fid st ann slot value : 0<=fid -> 0<=slot -> slot<cm_temp_slots (cm_function_at policy fid (cm_program_functions p)) -> cm_runtime_core policy ap p fid st ann -> cm_runtime_core policy ap p fid st (cm_ann_put_spill slot value ann).
Proof. intros F L U [B R]; split; [exact B|]; eapply cm_runtime_stack_spill_put; eauto; lia. Qed.
Lemma cm_runtime_core_leave_call policy ap p fid caller st ann env fp regions ret owner ob oc rest caller_spills saved returnpc calls targetpc :
 cm_ann_cursors ann=CMACursor (CACallP caller env fp regions ret) owner ob oc::rest ->
 cm_ann_saved ann=CMSpillFrame caller fp caller_spills::saved -> cm_ann_calls ann=CMCallSimFrame (cm_state_fp st) fp returnpc::calls ->
 cm_runtime_core policy ap p fid st ann -> cm_runtime_core policy ap p caller (cm_restore_call st env fp regions) (cm_ann_leave_call ap targetpc ann).
Proof.
 intros CUR SAVED CALLS [B R]; rewrite CUR,SAVED,CALLS in R.
 cbn [cm_runtime_stack cm_cursor_phase cm_phase_is_call cm_phase_oldregions cm_phase_caller cm_phase_oldfp hd tl cm_spill_frame_spills] in R.
 destruct R as [PREFIX [SEG [SP [S [C [BASE [SV [FID [FP REC]]]]]]]]].
 pose proof (cm_region_prefix_generations_incl _ _ _ _ _ _ _ PREFIX) as INC; split; [now apply cm_restore_call_regions_before|].
 cbn [cm_ann_leave_call cm_ann_cursors cm_ann_spills cm_ann_saved cm_ann_calls]; rewrite CUR,SAVED,CALLS; cbn [hd tl cm_spill_frame_spills]; now apply cm_runtime_stack_restore_incl.
Qed.
