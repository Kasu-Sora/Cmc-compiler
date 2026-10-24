Require Export SimpleC.EE.QCP_demos_human.cmc_runtime_start_step_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_ann_replace_as_push_pop ap ann oldphase owner ob oc rest phase pc temp breakpc continuepc : cm_ann_cursors ann=CMACursor oldphase owner ob oc::rest ->
 cm_ann_replace ap phase pc temp breakpc continuepc ann=cm_ann_push phase pc temp breakpc continuepc (cm_ann_pop ap pc ann).
Proof. intro CUR; unfold cm_ann_replace,cm_ann_push,cm_ann_pop; rewrite CUR; reflexivity. Qed.
Lemma cm_runtime_core_leave_call_cursor policy ap p fid caller st ann env fp regions ret owner ob oc rest targetpc :
 cm_ann_cursors ann=CMACursor (CACallP caller env fp regions ret) owner ob oc::rest -> cm_runtime_core policy ap p fid st ann ->
 cm_runtime_core policy ap p caller (cm_restore_call st env fp regions) (cm_ann_leave_call ap targetpc ann).
Proof.
 intros CUR CORE; destruct CORE as [B R]; pose proof R as OLD; rewrite CUR in R.
 cbn [cm_runtime_stack cm_cursor_phase cm_phase_is_call cm_phase_oldregions cm_phase_oldfp cm_phase_caller] in R.
 destruct R as [PRE [SEG [SP [S [C [BASE [FP [FID [SFP REC]]]]]]]]].
 destruct (cm_ann_saved ann) as [|[sfid sfp vs] saved] eqn:SV; [contradiction|].
 destruct (cm_ann_calls ann) as [|[base oldfp returnpc] calls] eqn:CL; [contradiction|].
 cbn [hd cm_spill_frame_fid cm_spill_frame_fp cm_call_sim_base cm_call_sim_saved] in BASE,FP,FID,SFP; subst sfid sfp base oldfp.
 eapply cm_runtime_core_leave_call; [exact CUR|exact SV|exact CL|].
 split; [exact B|rewrite SV,CL; exact OLD].
Qed.
Lemma cm_runtime_core_enter_arg sp ap p fid callee rest values ret all_args base current scratch owner ob oc tail v st ann returnpc parent_temp parent_break parent_continue :
 cm_typed_program (cm_source_function_policy sp) p -> 0<=fid -> 0<=current<cm_temp_slots (cm_function_at (cm_source_function_policy sp) fid (cm_program_functions p)) ->
 cm_ann_cursors ann=CMACursor (CAArgP callee rest values ret all_args base current scratch) owner ob oc::tail ->
 cm_call_ok sp p callee (rev (v::values)) st=true -> cm_runtime_core (cm_source_function_policy sp) ap p fid st ann ->
 cm_runtime_core (cm_source_function_policy sp) ap p callee (cm_enter_call sp p callee (rev (v::values)) st)
 (cm_ann_enter_call sp p fid callee st ret returnpc parent_temp parent_break parent_continue tail (cm_spill_put current v (cm_ann_spills ann)) (cm_ann_saved ann) (cm_ann_calls ann)).
Proof.
 intros WF F [L U] CUR OK CORE.
 replace tail with (tl (cm_ann_cursors ann)) by (rewrite CUR; reflexivity).
 apply cm_runtime_core_enter_call with (ann:=cm_ann_put_spill current v (cm_ann_pop ap returnpc ann)); [exact WF|exact OK|].
 apply cm_runtime_core_spill_put; [exact F|exact L|exact U|].
 eapply cm_runtime_core_pop_plain; [exact CUR|reflexivity|reflexivity|reflexivity|exact CORE].
Qed.
Ltac cm_rt_conj H := lazymatch type of H with _ /\ _=>let A:=fresh "bound" in let B:=fresh "bound" in destruct H as [A B]; cm_rt_conj A; cm_rt_conj B | _=>idtac end.
Ltac cm_rt_spill_bounds := first [assumption|lia|match goal with H:context[cm_rtemps ?e]|-_=>pose proof (cm_expr_temps_nonnegative__index_bounds e); lia end].
Ltac cm_rt_apply_atom := first [cm_rt_atom | match goal with
 | CUR:cm_ann_cursors ?ann=CMACursor ?old ?owner ?ob ?oc::?rest |- cm_runtime_core ?pol ?ap ?p ?fid ?st (cm_ann_replace ?ap ?phase ?pc ?temp ?breakpc ?continuepc ?ann)=>rewrite (cm_ann_replace_as_push_pop ap ann old owner ob oc rest phase pc temp breakpc continuepc CUR)
 | CUR:cm_ann_cursors ?ann=CMACursor ?old ?owner ?ob ?oc::?rest |- cm_runtime_core _ ?ap _ _ (cm_restore_scope _ _ _) (cm_ann_pop ?ap _ ?ann)=>eapply cm_runtime_core_leave_scope; [exact CUR|reflexivity|reflexivity|reflexivity|]
 | CUR:cm_ann_cursors ?ann=CMACursor ?old ?owner ?ob ?oc::?rest |- cm_runtime_core _ ?ap _ _ _ (cm_ann_pop ?ap _ ?ann)=>eapply cm_runtime_core_pop_plain; [exact CUR|reflexivity|reflexivity|reflexivity|]
 | CUR:cm_ann_cursors ?ann=CMACursor ?old ?owner ?ob ?oc::?rest |- cm_runtime_core _ ?ap _ _ (cm_restore_call _ _ _ _) (cm_ann_leave_call ?ap _ ?ann)=>eapply cm_runtime_core_leave_call_cursor; [exact CUR|]
 | |- cm_runtime_core _ _ _ _ _ (cm_ann_put_spill _ _ _)=>apply cm_runtime_core_spill_put; [lia|cm_rt_spill_bounds|cm_rt_spill_bounds|]
 end].
Ltac cm_rt_apply_finish := repeat first [assumption|reflexivity|exact I|cm_rt_task|cm_rt_apply_atom|
 match goal with H:cm_task_succeeds ?sp (CMCTask ?p ?fid (CMError ?error) ?st ?ks)|-_=>exfalso; exact (cm_error_not_succeeds sp p fid st error ks H) end].
