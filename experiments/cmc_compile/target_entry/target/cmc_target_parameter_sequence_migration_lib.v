Require Export SimpleC.EE.QCP_demos_human.cmc_target_parameter_ready_migration_lib.
From AUXLib Require Import ListLib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_tvm_parameter_sequence sp p fid params values index st obj vm calls frames held rest :
 length params=length values ->cm_parameters_ready sp p fid st index params ->
 cm_runtime_memory_layout(cm_source_function_policy sp)p st calls frames ->
 Zlength values+Zlength held+2<65536 ->
 cm_machine_state_sim(cm_source_function_policy sp)p st vm calls frames(rev values++held)[] ->
 cm_code_at(tvm_object_code obj)(tvm_pc vm)(cm_emit_param_stores(cm_source_function_policy sp)p fid index params++rest) ->
 exists next,tvm_iter(cm_code_steps(cm_emit_param_stores(cm_source_function_policy sp)p fid index params))(TVMRunTask obj vm)=TVMRunTask obj next /\
 tvm_pc next=tvm_pc vm+Zlength(cm_emit_param_stores(cm_source_function_policy sp)p fid index params) /\
 cm_machine_state_sim(cm_source_function_policy sp)p(cm_store_params_reverse sp p fid values index st)next calls frames held[].
Proof.
 revert values index st vm held rest;induction params as[|s params IH];intros values index st vm held rest LEN READY RT CAP SIM CODE.
 - destruct values;cbn in LEN;[|discriminate]. exists vm;cbn[cm_emit_param_stores cm_store_params_reverse cm_code_steps];split;[reflexivity|];split;[rewrite Z.add_0_r;reflexivity|exact SIM].
 - destruct values as[|v values];cbn in LEN;[discriminate|];injection LEN as LEN.
   destruct READY as[HEAD TAIL]. cbn[cm_emit_param_stores]in CODE.
   rewrite <-app_assoc in CODE.
   assert(SIM0:cm_machine_state_sim(cm_source_function_policy sp)p st vm calls frames(rev values++v::held)[]).
   { cbn[rev]in SIM;rewrite <-app_assoc in SIM;exact SIM. }
   destruct(IH values(index+1)st vm(v::held)((cm_char_normalize_code(cm_slot_ty s)++cm_fp_relative_address_code(cm_param_offset(cm_source_function_policy sp)p fid index)++cm_store_code(cm_slot_ty s))++rest)
    LEN TAIL RT ltac:(rewrite Zlength_cons in CAP|-*;lia)SIM0 CODE)as[mid[RUN[PC MSIM]]].
   pose proof(cm_code_at_append_right _ _ _ _ CODE)as LAST.
   rewrite <-PC in LAST.
   set(after:=cm_store_params_reverse sp p fid values(index+1)st)in *.
   destruct(cm_parameter_ready_reverse sp p fid st values(index+1)index(cm_slot_ty s)HEAD)as[TY[OK NUM]].
   change(cm_store_ok(cm_slot_ty s)(cm_state_env after 2 index)after=true)in OK.
   change(cm_value_number after(cm_state_env after 2 index)=tower_wrap64(cm_state_fp after+cm_param_offset(cm_source_function_policy sp)p fid index))in NUM.
   destruct mid as[pc stack vcalls mem input output].
   pose proof MSIM as[_[_[_[_[_[_[_ STACK]]]]]]]. unfold cm_operand_suffix_sim in STACK;cbn[tvm_stack]in STACK;rewrite app_nil_r in STACK;subst stack.
   pose proof(cm_parameter_store_step(cm_source_function_policy sp)p after obj pc calls frames vcalls mem input output v held(cm_slot_ty s)(cm_state_env after 2 index)(cm_param_offset(cm_source_function_policy sp)p fid index)rest
    (cm_runtime_reverse_params sp p fid st values(index+1)calls frames RT)OK NUM ltac:(pose proof(Zlength_nonneg values);rewrite Zlength_cons in CAP;lia)MSIM LAST)as[EXEC RESULT].
   eexists;split.
   + cbn[cm_emit_param_stores];rewrite cm_code_steps_append,tvm_iter_add,RUN;exact EXEC.
   + split;[cbn[tvm_pc]in *;cbn[cm_emit_param_stores];rewrite !Zlength_app;lia|].
     cbn[cm_store_params_reverse];fold after;rewrite <-TY;exact RESULT.
Qed.
