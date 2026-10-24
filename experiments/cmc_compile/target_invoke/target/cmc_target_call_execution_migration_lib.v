Require Export SimpleC.EE.QCP_demos_human.cmc_target_call_runtime_migration_lib.
From AUXLib Require Import ListLib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_tvm_call_step obj st dest rest :
 cm_code_at(tvm_object_code obj)(tvm_pc st)(TVMInst TVMCallOp dest::rest) ->
 tvm_target_valid(tvm_object_code obj)dest ->Zlength(tvm_calls st)<65536 ->
 tvm_step(TVMRunTask obj st)=TVMRunTask obj(tvm_jump_state st dest(tvm_stack st)(tvm_pc st+1::tvm_calls st)(tvm_mem st)(tvm_input st)(tvm_output st)).
Proof.
 intros CODE VALID CAP;eapply cm_tvm_state_step;[exact CODE|];cbn[tvm_inst_step].
 apply tvm_target_validb_spec in VALID;rewrite VALID.
 assert(C:(Zlength(tvm_calls st)<?65536)=true)by(now apply Z.ltb_lt);rewrite C;reflexivity.
Qed.
Lemma cm_call_ok_arity sp p fid values st :cm_call_ok sp p fid values st=true ->Zlength values=Zlength(cm_function_params(cm_source_function_at sp fid p)).
Proof. unfold cm_call_ok;intro OK;repeat rewrite andb_true_iff in OK;apply Z.eqb_eq;tauto. Qed.
Lemma cm_prologue_target_valid policy p fid obj pc rest :
 cm_code_at(tvm_object_code obj)pc(cm_emit_prologue policy p fid++rest) ->tvm_target_valid(tvm_object_code obj)pc.
Proof.
 intro CODE;pose proof(cm_code_at_bounds _ _ _ CODE)as[L H].
 rewrite cm_emit_prologue_prefix,!Zlength_app in H.
 change(Zlength(cm_prologue_prefix(cm_frame_size(cm_program_structs p)(cm_function_at policy fid(cm_program_functions p)))) )with 14 in H.
 pose proof(Zlength_nonneg(cm_emit_param_stores policy p fid 0(cm_function_params(cm_function_at policy fid(cm_program_functions p))))).
 pose proof(Zlength_nonneg rest);unfold tvm_target_valid;lia.
Qed.
Lemma cm_tvm_invoke_function sp ap p caller callee st values ann obj vm callrest bodyrest :
 cm_semantic_wf_program(cm_source_function_policy sp)p ->cm_call_ok sp p callee values st=true ->
 cm_runtime_core(cm_source_function_policy sp)ap p caller st ann ->cm_tagged_span_valid st ->
 0<=cm_state_nextgen st ->cm_tags_generation_below(cm_state_nextgen st)(cm_state_tags st) ->
 cm_spill_frames_generation_below(cm_state_nextgen st)(CMSpillFrame caller(cm_state_fp st)(cm_ann_spills ann)::cm_ann_saved ann) ->
 cm_values_generation_below(cm_state_nextgen st)values ->Zlength(tvm_calls vm)<65536 ->
 cm_machine_state_sim(cm_source_function_policy sp)p st vm(cm_ann_calls ann)(CMSpillFrame caller(cm_state_fp st)(cm_ann_spills ann)::cm_ann_saved ann)(rev values)[] ->
 cm_code_at(tvm_object_code obj)(tvm_pc vm)(TVMInst TVMCallOp(cm_function_pc(cm_source_function_policy sp)p callee)::callrest) ->
 cm_code_at(tvm_object_code obj)(cm_function_pc(cm_source_function_policy sp)p callee)(cm_emit_prologue(cm_source_function_policy sp)p callee++bodyrest) ->
 exists next,tvm_iter(S(cm_code_steps(cm_emit_prologue(cm_source_function_policy sp)p callee)))(TVMRunTask obj vm)=TVMRunTask obj next /\
 tvm_pc next=cm_call_body_pc sp p callee /\
 cm_machine_state_sim(cm_source_function_policy sp)p(cm_enter_call sp p callee values st)next
 (CMCallSimFrame(cm_state_fp(cm_call_base_state sp p callee st))(cm_state_fp st)(tvm_pc vm+1)::cm_ann_calls ann)
 (CMSpillFrame callee(cm_state_fp(cm_call_base_state sp p callee st))[]::CMSpillFrame caller(cm_state_fp st)(cm_ann_spills ann)::cm_ann_saved ann)[][].
Proof.
 intros WF OK RT TAG GEN TGEN FGEN VGEN DEPTH SIM CALL PROLOGUE.
 pose proof WF as[TYPED[_[_[[BC BCAP]_]]]].
 pose proof(cm_call_ok_function_wf _ _ _ _ _ TYPED OK)as FW.
 pose proof(cm_call_frame_segment _ _ _ _ _ TYPED OK)as SEG.
 pose proof(cm_frame_segment_bounds _ _ _ _ _ SEG)as[SL[BL[BH FU]]].
 pose proof(cm_call_ok_arity _ _ _ _ _ OK)as ARITY.
 pose proof RT as[BEFORE STACK].
 pose proof(cm_runtime_new_frame_range _ _ _ _ _ _(cm_state_fp(cm_call_base_state sp p callee st))RT BL BH)as[OUT SAFE].
 pose proof(cm_runtime_stack_memory_layout _ _ _ _ _ _ _ _ _ STACK)as MEM.
 pose proof(cm_runtime_return_slot_safe _ _ _ _ _ _ _ _ _ STACK)as[CR SR].
 assert(OUT8:forall a,cm_live_address st a ->a<8 \/16<=a)by(intros;eapply cm_runtime_fp_slot_disjoint;eassumption).
 assert(BSIGN:tower_signed64(cm_state_fp(cm_call_base_state sp p callee st)))by(unfold tower_signed64;cbn[cm_call_base_state cm_state_fp];lia).
 assert(FSIGN:tower_signed64(cm_state_fp st))by(unfold tower_signed64;lia).
 pose proof(cm_machine_prologue_pending sp p callee st vm(cm_ann_calls ann)(CMSpillFrame caller(cm_state_fp st)(cm_ann_spills ann)::cm_ann_saved ann)(rev values)(tvm_pc vm+1)(cm_function_pc(cm_source_function_policy sp)p callee+14)
 FW BEFORE TGEN FGEN TAG OUT OUT8 SAFE CR SR BSIGN FSIGN SIM)as PENDING.
 pose proof(cm_call_pending_encode_values sp p callee st(rev values)(cm_values_generation_below_reverse _ _ VGEN))as ENC.
 pose proof(cm_call_pending_runtime sp ap p caller callee st values ann(tvm_pc vm+1)TYPED OK RT)as PMEM.
 pose proof PROLOGUE as PARAMS;rewrite cm_emit_prologue_prefix,<-app_assoc in PARAMS;apply cm_code_at_append_right in PARAMS.
 change(Zlength(cm_prologue_prefix(cm_frame_size(cm_program_structs p)(cm_source_function_at sp callee p))))with 14 in PARAMS.
 destruct(cm_tvm_pending_parameters_complete sp p callee st values obj _ _ _ bodyrest FW SEG GEN BCAP ARITY PMEM PENDING PARAMS)as[next[PARAMEXEC[PC RESULT]]].
 exists next;split.
 - cbn[tvm_iter];rewrite(cm_tvm_call_step _ _ _ _ CALL(cm_prologue_target_valid _ _ _ _ _ _ PROLOGUE)DEPTH).
   rewrite cm_emit_prologue_prefix,cm_code_steps_append.
   change(cm_code_steps(cm_prologue_prefix(cm_frame_size(cm_program_structs p)(cm_source_function_at sp callee p))))with 14%nat.
   rewrite tvm_iter_add.
   pose proof SIM as[_[_[FP[_[_[_[_ OPERANDS]]]]]]].
   unfold cm_operand_suffix_sim in OPERANDS;rewrite app_nil_r in OPERANDS.
   unfold tvm_jump_state.
   rewrite OPERANDS.
   pose proof FW as[_[_[_[_[_[_[_ FRAME]]]]]]].
   replace(cm_code_steps(cm_prologue_prefix(cm_frame_size(cm_program_structs p)(cm_function_at(cm_source_function_policy sp)callee(cm_program_functions p)))))with 14%nat by reflexivity.
   rewrite(cm_tvm_prologue_prefix obj (cm_function_pc(cm_source_function_policy sp)p callee)(cm_frame_size(cm_program_structs p)(cm_source_function_at sp callee p))(cm_state_fp st)(cm_encode_values st(rev values))(tvm_pc vm+1::tvm_calls vm)(tvm_mem vm)(tvm_input vm)(tvm_output vm)_
    ltac:(unfold tower_signed64;lia)BSIGN ltac:(lia)ltac:(unfold tower_word_valid;lia)FP
    ltac:(unfold cm_encode_values;rewrite Zlength_correct,length_map,length_rev,<-Zlength_correct,ARITY;apply cm_function_arity_stack_bound;[unfold cm_frame_segment in SEG;tauto|exact BCAP])
    ltac:(rewrite cm_emit_prologue_prefix,<-app_assoc in PROLOGUE;exact PROLOGUE)).
   rewrite <-ENC;exact PARAMEXEC.
 - split;[|exact RESULT].
   cbn[tvm_pc]in PC;unfold cm_source_function_at in PC;unfold cm_call_body_pc,cm_source_function_at;rewrite <-cm_layout_prologue_length;rewrite cm_emit_prologue_prefix,Zlength_app;replace(Zlength(cm_prologue_prefix(cm_frame_size(cm_program_structs p)(cm_function_at(cm_source_function_policy sp)callee(cm_program_functions p)))))with 14 by reflexivity;lia.
Qed.
