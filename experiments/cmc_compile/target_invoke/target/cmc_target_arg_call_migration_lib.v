Require Export SimpleC.EE.QCP_demos_human.cmc_target_args_stack_migration_lib.
From AUXLib Require Import ListLib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_target_v_arg_nil_step sp ap p fid callee values ty all_args base current scratch v st pc temp b c owner ob oc tail spills saved calls target :
 let ann:=CMAnnotation pc temp b c(CMACursor(CAArgP callee[]values ty all_args base current scratch)owner ob oc::tail)spills saved calls in
 cm_semantic_wf_program(cm_source_function_policy sp)p ->
 cm_runtime_core(cm_source_function_policy sp)ap p fid st ann ->cm_tagged_span_valid st ->
 0<=cm_state_nextgen st ->cm_tags_generation_below(cm_state_nextgen st)(cm_state_tags st) ->
 cm_spill_frames_generation_below(cm_state_nextgen st)(cm_active_spill_frames fid st ann) ->
 cm_values_generation_below(cm_state_nextgen st)(v::values) ->0<=fid ->0<=base ->
 current=base+Zlength values ->0<=current<cm_temp_slots(cm_source_function_at sp fid p) ->
 Zlength all_args=Zlength(v::values) ->cm_staged_spills base values spills ->
 cm_call_ok sp p callee(rev(v::values))st=true ->cm_call_depth(cm_cursor_frames tail)<65536 ->
 cm_task_layout sp ap p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))ann ->
 cm_task_target_sim(cm_source_function_policy sp)p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))target ann ->
 cm_target_step_result sp ap p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))target ann.
Proof.
 cbn zeta;intros WF RT TAG GEN TG FG VG FID BASE CUR SLOT LEN STAGED OK DEPTH[CODE SAVED][_ SIM].
 set(ann:=CMAnnotation pc temp b c(CMACursor(CAArgP callee[]values ty all_args base current scratch)owner ob oc::tail)spills saved calls)in *.
 unfold ann in CODE;cbn[cm_task_code cm_cont_code cm_cursor_code cm_ann_pc cm_ann_temp cm_ann_cursors cm_cursor_phase cm_cursor_temp cm_cursor_break cm_cursor_continue cm_value_phase_code cm_phase_stops cm_phase_yields_normal cm_emit_args_store orb]in CODE;repeat rewrite <-app_assoc in CODE;cbn[app]in CODE.
 pose proof(cm_target_temp_store_sim sp ap p fid st v current ann target _ RT FID SLOT TAG CODE SIM)as FIRST.
 set(a1:=cm_ann_put_spill current v(cm_ann_linear(cm_temp_store_code(cm_source_function_policy sp)p fid current)ann))in *.
 assert(RT1:cm_runtime_core(cm_source_function_policy sp)ap p fid st a1).
 { apply cm_runtime_core_spill_put;[exact FID|exact(proj1 SLOT)|exact(proj2 SLOT)|apply cm_runtime_core_linear;exact RT]. }
 pose proof(cm_code_at_append_right _ _ _ _ CODE)as RELOAD.
 assert(CAP:Zlength(v::values)+1<65536).
 { pose proof(cm_call_ok_arity _ _ _ _ _ OK)as ARITY;rewrite Zlength_correct,length_rev,<-Zlength_correct in ARITY.
   pose proof(cm_function_arity_stack_bound(cm_source_function_policy sp)p callee ltac:(apply cm_call_ok_fid_bounds in OK;exact OK) ltac:(destruct WF as[_[_[_[[_ BCAP]_]]]];exact BCAP))as BND;unfold cm_source_function_at in ARITY;lia. }
 assert(STAGED1:cm_staged_spills base(v::values)(cm_ann_spills a1)).
 { change(cm_staged_spills base(v::values)(cm_spill_put current v spills));rewrite CUR;now apply cm_staged_spills_cons. }
 pose proof(cm_target_reload_staged sp ap p fid st a1(tvm_iter 5 target)base all_args(v::values)_ RT1 FID BASE ltac:(rewrite LEN,Zlength_cons;lia) LEN CAP STAGED1 RELOAD FIRST)as SECOND.
 set(a2:=cm_ann_linear(cm_emit_args_reload(cm_source_function_policy sp)p fid base all_args)a1)in *.
 destruct SECOND as[vm[EXEC[PC SIM2]]].
 assert(RT2:cm_runtime_core(cm_source_function_policy sp)ap p fid st a2)by(apply cm_runtime_core_linear;exact RT1).
 assert(FG2:cm_spill_frames_generation_below(cm_state_nextgen st)(cm_active_spill_frames fid st a2)).
 { destruct FG as[FS REST];split;[apply cm_spill_put_generation;[exact(proj1 VG)|exact FS]|exact REST]. }
 pose proof SIM2 as[_[_[_[CALLSIM _]]]];pose proof(cm_call_sim_length _ _ _ CALLSIM)as CLEN.
 pose proof(cm_saved_layout_call_depth _ _ _ _ _ _ _ SAVED)as CD.
 assert(VD:Zlength(tvm_calls vm)<65536).
 { change(Zlength calls=cm_call_depth(cm_cursor_frames tail))in CD;change(Zlength calls=Zlength(tvm_calls vm))in CLEN;lia. }
 pose proof(cm_code_at_append_right _ _ _ _ RELOAD)as CALL.
 change(pc+Zlength(cm_temp_store_code(cm_source_function_policy sp)p fid current)+Zlength(cm_emit_args_reload(cm_source_function_policy sp)p fid base all_args))with(cm_ann_pc a2)in CALL;rewrite <-PC in CALL.
 pose proof(cm_model_function_at(cm_source_function_policy sp)p callee(cm_call_ok_fid_bounds _ _ _ _ _ OK))as PROLOGUE;unfold cm_emit_function in PROLOGUE.
 assert(SIMREV:cm_machine_state_sim(cm_source_function_policy sp)p st vm(cm_ann_calls a2)(cm_active_spill_frames fid st a2)(rev(rev(v::values)))[])by(now rewrite rev_involutive).
 destruct(cm_tvm_invoke_function sp ap p fid callee st(rev(v::values))a2(cm_compile_model(cm_source_function_policy sp)p)vm _ _ WF OK RT2 TAG GEN TG FG2 (cm_values_generation_below_reverse _ _ VG) VD SIMREV CALL PROLOGUE)as[next[INVOKE[NPC NEXT]]].
 assert(D:(cm_call_depth(cm_cursor_frames tail)<?65536)=true)by(now apply Z.ltb_lt).
 unfold cm_target_step_result;cbv beta iota zeta delta[cm_step cm_cursor_frames cm_cursor_phase cm_phase_frame map cm_ann_cursors cm_annotation_step cm_update_v cm_vapply cm_begin_call cm_list_empty ann hd tl];cbv beta iota zeta delta[cm_cursor_frames cm_cursor_phase cm_phase_frame map]in D;rewrite OK,D;cbn[andb cm_update_steps cm_update_annotation cm_task_target_sim].
 unfold cm_arg_final_code;rewrite !cm_code_steps_append.
 change(cm_code_steps(cm_temp_store_code(cm_source_function_policy sp)p fid current))with 5%nat.
 change(cm_code_steps[TVMInst TVMCallOp(cm_function_pc(cm_source_function_policy sp)p callee)])with 1%nat.
 replace(5+(cm_code_steps(cm_emit_args_reload(cm_source_function_policy sp)p fid base all_args)+(1+cm_code_steps(cm_emit_prologue(cm_source_function_policy sp)p callee))))%nat with((5+cm_code_steps(cm_emit_args_reload(cm_source_function_policy sp)p fid base all_args))+S(cm_code_steps(cm_emit_prologue(cm_source_function_policy sp)p callee)))%nat by lia.
 rewrite !tvm_iter_add,EXEC,INVOKE;split;[reflexivity|];exists next;split;[reflexivity|];split;[exact NPC|].
 unfold cm_ann_enter_call;cbn[cm_ann_calls cm_ann_saved cm_ann_spills];rewrite PC in NEXT;unfold a2,a1,ann,cm_ann_linear,cm_ann_plain,cm_ann_put_spill in NEXT;cbn[cm_ann_pc cm_ann_calls cm_active_spill_frames cm_ann_spills cm_ann_saved]in NEXT.
 cbn[cm_cursor_temp cm_cursor_break cm_cursor_continue cm_ann_pc cm_ann_saved cm_ann_spills cm_ann_calls]in *;unfold cm_active_spill_frames,cm_enter_call;rewrite cm_store_params_fp;exact NEXT.
Qed.
