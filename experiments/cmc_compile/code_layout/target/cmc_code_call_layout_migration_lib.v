Require Export SimpleC.EE.QCP_demos_human.cmc_code_function_sites_migration_lib.
From Coq Require Import ZArith List Bool Lia.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_layout_enter_call sp ap p caller callee st values ret returnpc temp breakpc continuepc tail spills saved calls :
 0<=callee<Zlength (cm_program_functions p) ->
 cm_code_at (cm_model_code (cm_source_function_policy sp) p) returnpc (cm_cont_code sp p caller returnpc temp tail) ->
 cm_saved_layout sp ap p (cm_model_code (cm_source_function_policy sp) p) caller tail calls ->
 cm_task_layout sp ap p (CMSTask p callee (cm_function_body (cm_source_function_at sp callee p)) (cm_enter_call sp p callee values st) (CMCallK caller (cm_state_env st) (cm_state_fp st) (cm_state_regions st) ret::cm_cursor_frames tail))
 (cm_ann_enter_call sp p caller callee st ret returnpc temp breakpc continuepc tail spills saved calls).
Proof.
 intros B RETURN SAVED.
 pose proof (cm_model_function_body_tail_at (cm_source_function_policy sp) p callee B) as BODY.
 cbv beta iota zeta delta [cm_task_layout cm_task_code cm_task_fid cm_ann_enter_call cm_ann_pc cm_ann_temp cm_ann_break cm_ann_continue cm_ann_cursors cm_ann_calls cm_normal_cont_code cm_cursor_code cm_cursor_phase cm_cursor_temp cm_cursor_break cm_cursor_continue cm_normal_phase_code cm_normal_phase_stops cm_saved_layout cm_phase_site cm_phase_is_call cm_phase_caller cm_call_sim_return hd tl].
 repeat rewrite app_nil_r; repeat split; try assumption; try discriminate.
Qed.
Lemma cm_model_status_tail_at sp p : cm_code_at (cm_model_code (cm_source_function_policy sp) p) 4 cm_status_tail_code.
Proof. exists [TVMInst TVMPushOp 1048576;TVMInst TVMPushOp 8;TVMInst TVMStoreOp 0;TVMInst TVMCallOp (cm_function_pc (cm_source_function_policy sp) p (cm_program_main p))],(cm_emit_functions (cm_source_function_policy sp) p 0 (cm_program_functions p)); split; reflexivity. Qed.
Lemma cm_start_task_layout_step sp ap p input : cm_call_ok sp p (cm_program_main p) [] (cm_initial_state sp p input)=true ->
 cm_task_layout sp ap p (cm_step sp (CMStartTask p input)) (cm_update_annotation (cm_annotation_step sp ap (CMStartTask p input) cm_initial_annotation)).
Proof.
 intro OK; pose proof (cm_call_ok_fid_bounds _ _ _ _ _ OK) as B.
 cbv beta iota zeta delta [cm_step cm_begin_call cm_annotation_step cm_call_depth cm_update_annotation cm_list_empty Z.ltb Z.compare Pos.compare Pos.compare_cont andb].
 rewrite OK; cbn [andb]. eapply cm_layout_enter_call with (values:=[]); [exact B| |split; [exact I|reflexivity]].
 cbn [cm_cont_code cm_cursor_code cm_cursor_phase cm_cursor_temp cm_cursor_break cm_cursor_continue cm_value_phase_code cm_phase_stops]; rewrite app_nil_r; apply cm_model_status_tail_at.
Qed.
Lemma cm_r_call_nil_layout_step sp ap p fid callee ty st ann :
 cm_call_ok sp p callee [] st=true -> cm_call_depth (cm_cursor_frames (cm_ann_cursors ann))<65536 ->
 cm_task_layout sp ap p (CMRTask p fid (CMCallE callee [] ty) st (cm_cursor_frames (cm_ann_cursors ann))) ann ->
 cm_task_layout sp ap p (cm_rstart sp p fid (CMCallE callee [] ty) st (cm_cursor_frames (cm_ann_cursors ann))) (cm_update_annotation (cm_update_r sp ap p fid st ann (CMCallE callee [] ty))).
Proof.
 intros OK DEPTH [CODE SAVED]; pose proof (cm_call_ok_fid_bounds _ _ _ _ _ OK) as B.
 apply Z.ltb_lt in DEPTH.
 cbv beta iota zeta delta [cm_rstart cm_args_start cm_begin_call cm_update_r cm_list_empty]; rewrite OK,DEPTH; cbn [andb cm_update_annotation].
 eapply cm_layout_enter_call with (values:=[]); [exact B| |exact SAVED].
 cbn [cm_task_code] in CODE.
 change (cm_code_at (cm_model_code (cm_source_function_policy sp) p) (cm_ann_pc ann) ([TVMInst TVMCallOp (cm_function_pc (cm_source_function_policy sp) p callee)]++cm_cont_code sp p fid (cm_ann_pc ann+1) (cm_ann_temp ann) (cm_ann_cursors ann))) in CODE.
 exact (cm_code_at_append_right _ _ _ _ CODE).
Qed.
