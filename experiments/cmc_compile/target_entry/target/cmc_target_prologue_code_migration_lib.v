Require Export SimpleC.EE.QCP_demos_human.cmc_target_prologue_ops_migration_lib.
From Coq Require Import ZArith List Bool Lia.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Definition cm_prologue_prefix frame :=
 [TVMInst TVMPushOp 8;TVMInst TVMLoadOp 0;TVMInst TVMDupOp 0;TVMInst TVMPushOp frame;TVMInst TVMSubOp 0;TVMInst TVMStoreOp 0;
 TVMInst TVMPushOp 8;TVMInst TVMLoadOp 0;TVMInst TVMPushOp frame;TVMInst TVMSubOp 0;TVMInst TVMDupOp 0;TVMInst TVMPushOp 8;TVMInst TVMStoreOp 0;TVMInst TVMPopOp 0].
Lemma cm_emit_prologue_prefix policy p fid :cm_emit_prologue policy p fid=
 cm_prologue_prefix(cm_frame_size(cm_program_structs p)(cm_function_at policy fid(cm_program_functions p)))++cm_emit_param_stores policy p fid 0(cm_function_params(cm_function_at policy fid(cm_program_functions p))).
Proof. reflexivity. Qed.
Lemma cm_tvm_prologue_prefix obj pc frame fp args calls mem input output rest :
 tower_signed64 frame ->tower_signed64(fp-frame) ->16<=fp-frame ->tower_word_valid(fp-frame) ->
 tower_getw mem 8=fp ->Zlength args+2<65536 ->
 cm_code_at(tvm_object_code obj)pc(cm_prologue_prefix frame++rest) ->
 tvm_iter 14(TVMRunTask obj(TVMState pc args calls mem input output))=
 TVMRunTask obj(TVMState(pc+14)args calls(tower_setw(tower_setw mem(fp-frame)fp)8(fp-frame))input output).
Proof.
 intros FRAME NEW LOW VALID FP CAP CODE.
 assert(WF:tower_wrap64 frame=frame)by(now apply tower_wrap64_fixed).
 assert(SUB:tower_sub fp frame=fp-frame)by(unfold tower_sub;now apply tower_wrap64_fixed).
 assert(LOAD:tower_getw(tower_setw mem(fp-frame)fp)8=fp).
 { rewrite tower_getw_setw_outside;[exact FP|unfold cm_range_disjoint;lia]. }
 cbn[cm_prologue_prefix app]in CODE.
 pose proof(cm_code_at_tail _ _ _ _ CODE)as C1.
 pose proof(cm_code_at_tail _ _ _ _ C1)as C2.
 pose proof(cm_code_at_tail _ _ _ _ C2)as C3.
 pose proof(cm_code_at_tail _ _ _ _ C3)as C4.
 pose proof(cm_code_at_tail _ _ _ _ C4)as C5.
 pose proof(cm_code_at_tail _ _ _ _ C5)as C6.
 pose proof(cm_code_at_tail _ _ _ _ C6)as C7.
 pose proof(cm_code_at_tail _ _ _ _ C7)as C8.
 pose proof(cm_code_at_tail _ _ _ _ C8)as C9.
 pose proof(cm_code_at_tail _ _ _ _ C9)as C10.
 pose proof(cm_code_at_tail _ _ _ _ C10)as C11.
 pose proof(cm_code_at_tail _ _ _ _ C11)as C12.
 pose proof(cm_code_at_tail _ _ _ _ C12)as C13.
 cbn[tvm_iter].
 rewrite(cm_tvm_push_step obj (TVMState(pc)args calls mem input output) _ _ CODE ltac:(cbn[tvm_stack];rewrite ?Zlength_cons;lia)).
 cbv beta iota zeta delta [tvm_next_state tvm_pc tvm_stack tvm_calls tvm_mem tvm_input tvm_output].
 change(tower_wrap64 8)with 8.
 rewrite(cm_tvm_load_step obj (TVMState(pc+1)(8::args) calls mem input output) 8 args _ C1 eq_refl ltac:(unfold tower_word_valid;lia)).
 cbv beta iota zeta delta [tvm_next_state tvm_pc tvm_stack tvm_calls tvm_mem tvm_input tvm_output].
 rewrite FP.
 rewrite(cm_tvm_dup_step obj (TVMState(pc+1+1)(fp::args) calls mem input output) fp args _ C2 eq_refl ltac:(lia)).
 cbv beta iota zeta delta [tvm_next_state tvm_pc tvm_stack tvm_calls tvm_mem tvm_input tvm_output].
 rewrite(cm_tvm_push_step obj (TVMState(pc+1+1+1)(fp::fp::args) calls mem input output) _ _ C3 ltac:(cbn[tvm_stack];rewrite ?Zlength_cons;lia)).
 cbv beta iota zeta delta [tvm_next_state tvm_pc tvm_stack tvm_calls tvm_mem tvm_input tvm_output].
 rewrite WF.
 rewrite(cm_tvm_sub_step obj (TVMState(pc+1+1+1+1)(frame::fp::fp::args) calls mem input output) fp frame (fp::args) _ C4 eq_refl).
 cbv beta iota zeta delta [tvm_next_state tvm_pc tvm_stack tvm_calls tvm_mem tvm_input tvm_output].
 rewrite SUB.
 rewrite(cm_tvm_store_step obj (TVMState(pc+1+1+1+1+1)((fp-frame)::fp::args) calls mem input output) (fp-frame) fp args _ C5 eq_refl VALID).
 cbv beta iota zeta delta [tvm_next_state tvm_pc tvm_stack tvm_calls tvm_mem tvm_input tvm_output].
 rewrite(cm_tvm_push_step obj (TVMState(pc+1+1+1+1+1+1)args calls (tower_setw mem(fp-frame)fp) input output) _ _ C6 ltac:(cbn[tvm_stack];rewrite ?Zlength_cons;lia)).
 cbv beta iota zeta delta [tvm_next_state tvm_pc tvm_stack tvm_calls tvm_mem tvm_input tvm_output].
 change(tower_wrap64 8)with 8.
 rewrite(cm_tvm_load_step obj (TVMState(pc+1+1+1+1+1+1+1)(8::args) calls (tower_setw mem(fp-frame)fp) input output) 8 args _ C7 eq_refl ltac:(unfold tower_word_valid;lia)).
 cbv beta iota zeta delta [tvm_next_state tvm_pc tvm_stack tvm_calls tvm_mem tvm_input tvm_output].
 rewrite LOAD.
 rewrite(cm_tvm_push_step obj (TVMState(pc+1+1+1+1+1+1+1+1)(fp::args) calls (tower_setw mem(fp-frame)fp) input output) _ _ C8 ltac:(cbn[tvm_stack];rewrite ?Zlength_cons;lia)).
 cbv beta iota zeta delta [tvm_next_state tvm_pc tvm_stack tvm_calls tvm_mem tvm_input tvm_output].
 rewrite WF.
 rewrite(cm_tvm_sub_step obj (TVMState(pc+1+1+1+1+1+1+1+1+1)(frame::fp::args) calls (tower_setw mem(fp-frame)fp) input output) fp frame args _ C9 eq_refl).
 cbv beta iota zeta delta [tvm_next_state tvm_pc tvm_stack tvm_calls tvm_mem tvm_input tvm_output].
 rewrite SUB.
 rewrite(cm_tvm_dup_step obj (TVMState(pc+1+1+1+1+1+1+1+1+1+1)((fp-frame)::args) calls (tower_setw mem(fp-frame)fp) input output) (fp-frame) args _ C10 eq_refl ltac:(lia)).
 cbv beta iota zeta delta [tvm_next_state tvm_pc tvm_stack tvm_calls tvm_mem tvm_input tvm_output].
 rewrite(cm_tvm_push_step obj (TVMState(pc+1+1+1+1+1+1+1+1+1+1+1)((fp-frame)::(fp-frame)::args) calls (tower_setw mem(fp-frame)fp) input output) _ _ C11 ltac:(cbn[tvm_stack];rewrite ?Zlength_cons;lia)).
 cbv beta iota zeta delta [tvm_next_state tvm_pc tvm_stack tvm_calls tvm_mem tvm_input tvm_output].
 change(tower_wrap64 8)with 8.
 rewrite(cm_tvm_store_step obj (TVMState(pc+1+1+1+1+1+1+1+1+1+1+1+1)(8::(fp-frame)::(fp-frame)::args) calls (tower_setw mem(fp-frame)fp) input output) 8 (fp-frame) ((fp-frame)::args) _ C12 eq_refl ltac:(unfold tower_word_valid;lia)).
 cbv beta iota zeta delta [tvm_next_state tvm_pc tvm_stack tvm_calls tvm_mem tvm_input tvm_output].
 rewrite(cm_tvm_pop_step obj (TVMState(pc+1+1+1+1+1+1+1+1+1+1+1+1+1)((fp-frame)::args) calls (tower_setw(tower_setw mem(fp-frame)fp)8(fp-frame)) input output) (fp-frame) args _ C13 eq_refl).
 cbv beta iota zeta delta [tvm_next_state tvm_pc tvm_stack tvm_calls tvm_mem tvm_input tvm_output].
 replace(pc+1+1+1+1+1+1+1+1+1+1+1+1+1+1)with(pc+14)by lia;reflexivity.
Qed.
