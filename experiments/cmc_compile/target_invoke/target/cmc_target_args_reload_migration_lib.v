Require Export SimpleC.EE.QCP_demos_human.cmc_target_r_total_migration_lib.
From AUXLib Require Import ListLib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_tvm_fp_load_stack obj pc stack calls mem input output offset rest :
 Zlength stack+1<65536 ->tower_word_valid(tower_getw mem 8+offset) ->
 cm_code_at(tvm_object_code obj)pc(cm_fp_relative_address_code offset++TVMInst TVMLoadOp 0::rest) ->
 tvm_iter 5(TVMRunTask obj(TVMState pc stack calls mem input output))=
 TVMRunTask obj(TVMState(pc+5)(tower_getw mem(tower_getw mem 8+offset)::stack)calls mem input output).
Proof.
 intros CAP ADDR CODE;destruct stack as[|v stack];[eapply cm_tvm_fp_load_empty;eassumption|].
 pose proof(cm_code_at_append_right _ _ _ _ CODE)as LOAD.
 change(cm_code_at(tvm_object_code obj)(pc+4)(TVMInst TVMLoadOp 0::rest))in LOAD.
 change(tvm_step(tvm_iter 4(TVMRunTask obj(TVMState pc(v::stack)calls mem input output)))=TVMRunTask obj(TVMState(pc+5)(tower_getw mem(tower_getw mem 8+offset)::v::stack)calls mem input output)).
 rewrite(cm_tvm_fp_address_stack obj pc v stack calls mem input output offset (TVMInst TVMLoadOp 0::rest) ltac:(rewrite Zlength_cons in CAP;lia) CODE).
 rewrite tower_wrap64_fixed by(unfold tower_signed64,tower_word_valid in *;lia).
 rewrite(cm_tvm_load_step obj(TVMState(pc+4)(tower_getw mem 8+offset::v::stack)calls mem input output)(tower_getw mem 8+offset)(v::stack)_ LOAD eq_refl ADDR).
 cbv beta iota zeta delta[tvm_next_state tvm_pc tvm_stack tvm_calls tvm_mem tvm_input tvm_output];f_equal;f_equal;lia.
Qed.
Lemma cm_args_reload_app policy p fid base left right :
 cm_emit_args_reload policy p fid base(left++right)=cm_emit_args_reload policy p fid base left++cm_emit_args_reload policy p fid(base+Zlength left)right.
Proof.
 revert base;induction left as[|a rest IH];intro base;cbn[cm_emit_args_reload app];[now rewrite Z.add_0_r|].
 rewrite IH,app_assoc,Zlength_cons;f_equal;f_equal;lia.
Qed.
Lemma cm_args_reload_snoc policy p fid base args a :
 cm_emit_args_reload policy p fid base(args++[a])=cm_emit_args_reload policy p fid base args++cm_temp_load_code policy p fid(base+Zlength args).
Proof. rewrite cm_args_reload_app;cbn[cm_emit_args_reload];now rewrite app_nil_r. Qed.
Lemma cm_tvm_reload_staged policy p fid st vm spills base args values held pc rest :
 Zlength args=Zlength values ->0<=base ->base+Zlength args<=cm_temp_slots(cm_function_at policy fid(cm_program_functions p)) ->
 Zlength values+Zlength held+1<65536 ->
 (forall slot,base<=slot<base+Zlength args ->tower_word_valid(tower_getw(tvm_mem vm)8+cm_temp_offset policy p fid slot)) ->
 cm_spill_list_sim policy p st(tvm_mem vm)fid(tower_getw(tvm_mem vm)8)spills ->cm_staged_spills base values spills ->
 cm_code_at(tvm_object_code(cm_compile_model policy p))pc(cm_emit_args_reload policy p fid base args++rest) ->
 tvm_iter(cm_code_steps(cm_emit_args_reload policy p fid base args))(TVMRunTask(cm_compile_model policy p)(TVMState pc held(tvm_calls vm)(tvm_mem vm)(tvm_input vm)(tvm_output vm)))=
 TVMRunTask(cm_compile_model policy p)(TVMState(pc+Zlength(cm_emit_args_reload policy p fid base args))(cm_encode_values st values++held)(tvm_calls vm)(tvm_mem vm)(tvm_input vm)(tvm_output vm)).
Proof.
 revert values pc rest;induction args using rev_ind;intros values pc rest LEN BASE BOUND CAP VALID SIM STAGED CODE.
 - destruct values;[cbn[cm_emit_args_reload cm_code_steps Zlength cm_encode_values map app tvm_iter];now rewrite Z.add_0_r|rewrite Zlength_nil,Zlength_cons in LEN;pose proof(Zlength_nonneg values);lia].
 - destruct values as[|v values];[rewrite Zlength_app,Zlength_nil in LEN;change(Zlength[x])with 1 in LEN;pose proof(Zlength_nonneg args);lia|].
   rewrite Zlength_app,!Zlength_cons,Zlength_nil in LEN;assert(L:Zlength args=Zlength values)by lia.
   destruct STAGED as[HOLD STAGED].
   rewrite cm_args_reload_snoc in CODE|-*;rewrite cm_code_steps_append,tvm_iter_add.
   rewrite <-app_assoc in CODE.
   rewrite(IHargs values pc _ L BASE ltac:(rewrite Zlength_app in BOUND;change(Zlength[x])with 1 in BOUND;lia) ltac:(rewrite Zlength_cons in CAP;lia) ltac:(intros;apply VALID;rewrite Zlength_app;change(Zlength[x])with 1;pose proof(Zlength_nonneg args);lia) SIM STAGED CODE).
   pose proof(cm_code_at_append_right _ _ _ _ CODE)as LAST.
   unfold cm_temp_load_code in LAST;rewrite <-app_assoc in LAST.
   change(cm_code_steps(cm_temp_load_code policy p fid(base+Zlength args)))with 5%nat.
   rewrite(cm_tvm_fp_load_stack (cm_compile_model policy p) (pc+Zlength(cm_emit_args_reload policy p fid base args)) (cm_encode_values st values++held) (tvm_calls vm)(tvm_mem vm)(tvm_input vm)(tvm_output vm)(cm_temp_offset policy p fid(base+Zlength args)) rest ltac:(unfold cm_encode_values;rewrite Zlength_app,Zlength_correct,length_map,<-Zlength_correct;rewrite Zlength_cons in CAP;lia) ltac:(apply VALID;rewrite Zlength_app;change(Zlength[x])with 1;pose proof(Zlength_nonneg args);lia) LAST).
   rewrite L,(cm_spill_sim_holds _ _ _ _ _ _ _ _ _ SIM HOLD).
   rewrite Zlength_app;change(Zlength(cm_temp_load_code policy p fid(base+Zlength values)))with 5.
   cbn[cm_encode_values map app];f_equal;f_equal;lia.
Qed.
