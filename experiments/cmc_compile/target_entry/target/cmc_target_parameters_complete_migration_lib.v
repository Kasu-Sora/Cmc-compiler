Require Export SimpleC.EE.QCP_demos_human.cmc_target_parameter_geometry_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_target_parameter_sequence_migration_lib.
From AUXLib Require Import ListLib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_slot_cons_successor h t j :0<=j ->cm_slot_at(j+1)(h::t)=cm_slot_at j t.
Proof. intro J;unfold cm_slot_at;rewrite Z2Nat.inj_add by lia;replace(Z.to_nat j+Z.to_nat 1)%nat with(S(Z.to_nat j))by(cbn;lia);reflexivity. Qed.
Lemma cm_parameters_ready_indexed sp p fid st index params :
 (forall j,0<=j<Zlength params ->cm_parameter_ready sp p fid st(index+j)(cm_slot_ty(cm_slot_at j params))) ->cm_parameters_ready sp p fid st index params.
Proof.
 revert index;induction params as[|s params IH];intros index FACT;[constructor|];cbn[cm_parameters_ready];split.
 - specialize(FACT 0 ltac:(rewrite Zlength_cons;pose proof(Zlength_nonneg params);lia));rewrite Z.add_0_r in FACT;exact FACT.
 - apply IH;intros j J;specialize(FACT(j+1)ltac:(rewrite Zlength_cons;lia));rewrite cm_slot_cons_successor in FACT by lia;replace(index+(j+1))with(index+1+j)in FACT by lia;exact FACT.
Qed.
Lemma cm_pending_parameters_ready sp p fid st :
 cm_function_wf(cm_source_function_policy sp)p(cm_source_function_at sp fid p) ->
 cm_frame_segment(cm_source_function_policy sp)p fid(cm_state_fp st-cm_frame_size(cm_program_structs p)(cm_source_function_at sp fid p))(cm_state_fp st) ->0<=cm_state_nextgen st ->
 cm_parameters_ready sp p fid(cm_call_pending_base sp p fid st)0(cm_function_params(cm_source_function_at sp fid p)).
Proof.
 intros FW SEG GEN;apply cm_parameters_ready_indexed;intros j J;rewrite Z.add_0_l,<- (cm_source_slot_at_valid sp _ j J);now apply cm_pending_parameter_ready.
Qed.
Lemma cm_function_arity_bound_nat fs n f :nth_error fs n=Some f ->Zlength(cm_function_params f)<=cm_max_function_arity_from fs.
Proof.
 revert n;induction fs as[|h fs IH];intros[|n]N;cbn in N;try discriminate;cbn[cm_max_function_arity_from].
 - inversion N;subst;apply Z.le_max_l.
 - eapply Z.le_trans;[exact(IH n N)|apply Z.le_max_r].
Qed.
Lemma cm_function_arity_stack_bound policy p fid :0<=fid<Zlength(cm_program_functions p) ->
 cm_stack_bound_model p<=65536 ->Zlength(cm_function_params(cm_function_at policy fid(cm_program_functions p)))+2<65536.
Proof.
 intros FID CAP.
 destruct(nth_error(cm_program_functions p)(Z.to_nat fid))as[f|]eqn:N.
 - rewrite(cm_function_at_valid policy fid _ f ltac:(lia)N);pose proof(cm_function_arity_bound_nat _ _ _ N);unfold cm_stack_bound_model in CAP;lia.
 - apply nth_error_None in N;rewrite Zlength_correct in FID;lia.
Qed.
Lemma cm_tvm_pending_parameters_complete sp p fid st values obj vm calls frames rest :
 cm_function_wf(cm_source_function_policy sp)p(cm_source_function_at sp fid p) ->
 cm_frame_segment(cm_source_function_policy sp)p fid(cm_state_fp st-cm_frame_size(cm_program_structs p)(cm_source_function_at sp fid p))(cm_state_fp st) ->
 0<=cm_state_nextgen st ->cm_stack_bound_model p<=65536 ->Zlength values=Zlength(cm_function_params(cm_source_function_at sp fid p)) ->
 cm_runtime_memory_layout(cm_source_function_policy sp)p(cm_call_pending_base sp p fid st)calls frames ->
 cm_machine_state_sim(cm_source_function_policy sp)p(cm_call_pending_base sp p fid st)vm calls frames(rev values)[] ->
 cm_code_at(tvm_object_code obj)(tvm_pc vm)(cm_emit_param_stores(cm_source_function_policy sp)p fid 0(cm_function_params(cm_source_function_at sp fid p))++rest) ->
 exists next,tvm_iter(cm_code_steps(cm_emit_param_stores(cm_source_function_policy sp)p fid 0(cm_function_params(cm_source_function_at sp fid p))))(TVMRunTask obj vm)=TVMRunTask obj next /\
 tvm_pc next=tvm_pc vm+Zlength(cm_emit_param_stores(cm_source_function_policy sp)p fid 0(cm_function_params(cm_source_function_at sp fid p))) /\
 cm_machine_state_sim(cm_source_function_policy sp)p(cm_enter_call sp p fid values st)next calls frames[][].
Proof.
 intros FW SEG GEN CAP ARITY RT SIM CODE.
 pose proof SEG as[FID[UP _]].
 pose proof(cm_tvm_parameter_sequence sp p fid(cm_function_params(cm_source_function_at sp fid p))values 0(cm_call_pending_base sp p fid st)obj vm calls frames[]rest
 ltac:(rewrite !Zlength_correct in ARITY;lia)(cm_pending_parameters_ready sp p fid st FW SEG GEN)RT
 ltac:(rewrite Zlength_nil,Z.add_0_r,ARITY;now apply cm_function_arity_stack_bound)
 ltac:(rewrite app_nil_r;exact SIM)CODE)as[next[RUN[PC MSIM]]].
 exists next;split;[exact RUN|];split;[exact PC|].
 eapply cm_pointwise_machine_sim;[now apply cm_call_params_reverse_complete|exact MSIM].
Qed.
