Require Export SimpleC.EE.QCP_demos_human.cmc_target_prologue_code_migration_lib.
From AUXLib Require Import ListLib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_tvm_normalize_pair_stack obj pc value stack calls mem input output (add:bool) rest :
 Zlength stack+1<65536 ->
 cm_code_at(tvm_object_code obj)pc([TVMInst TVMPushOp 256;TVMInst(if add then TVMAddOp else TVMModOp)0]++rest) ->
 tvm_iter 2(TVMRunTask obj(TVMState pc(value::stack)calls mem input output))=
 TVMRunTask obj(TVMState(pc+2)((if add then tower_add value 256 else tower_mod value 256)::stack)calls mem input output).
Proof.
 intros CAP CODE;cbn[app]in CODE;pose proof(cm_code_at_tail _ _ _ _ CODE)as C1.
 cbn[tvm_iter];rewrite(cm_tvm_push_step obj(TVMState pc(value::stack)calls mem input output)_ _ CODE ltac:(cbn[tvm_stack];rewrite Zlength_cons;lia)).
 cbv beta iota zeta delta [tvm_next_state tvm_pc tvm_stack tvm_calls tvm_mem tvm_input tvm_output];change(tower_wrap64 256)with 256.
 rewrite(cm_tvm_code_step obj(TVMState(pc+1)(256::value::stack)calls mem input output)_ _ _ C1).
 assert(N:(2<=?Zlength(256::value::stack))=true)by(apply Z.leb_le;rewrite !Zlength_cons;pose proof(Zlength_nonneg stack);lia).
 destruct add;cbn[tvm_inst_step tvm_stack];rewrite N;
 cbv beta iota zeta delta [tvm_action_task tvm_next_state tvm_pc tvm_calls tvm_mem tvm_input tvm_output hd tl];cbn;
 f_equal;f_equal;lia.
Qed.
Lemma cm_tvm_char_normalize_stack obj pc value stack calls mem input output rest :
 Zlength stack+1<65536 ->
 cm_code_at(tvm_object_code obj)pc(cm_char_normalize_code CMCharTy++rest) ->
 tvm_iter 6(TVMRunTask obj(TVMState pc(value::stack)calls mem input output))=
 TVMRunTask obj(TVMState(pc+6)(tower_u8 value::stack)calls mem input output).
Proof.
 intros CAP CODE;cbn[cm_char_normalize_code app]in CODE.
 pose proof(cm_code_at_tail _ _ _ _ CODE)as C1;pose proof(cm_code_at_tail _ _ _ _ C1)as C2.
 pose proof(cm_code_at_tail _ _ _ _ C2)as C3;pose proof(cm_code_at_tail _ _ _ _ C3)as C4.
 replace(pc+1+1)with(pc+2)in C2 by lia;replace(pc+1+1+1+1)with(pc+4)in C4 by lia.
 change(tvm_iter 2(tvm_iter 2(tvm_iter 2(TVMRunTask obj(TVMState pc(value::stack)calls mem input output))))=TVMRunTask obj(TVMState(pc+6)(tower_u8 value::stack)calls mem input output)).
 rewrite(cm_tvm_normalize_pair_stack obj pc value stack calls mem input output false _ CAP CODE).
 rewrite(cm_tvm_normalize_pair_stack obj(pc+2)(tower_mod value 256)stack calls mem input output true _ CAP C2).
 replace(pc+2+2)with(pc+4)by lia.
 rewrite(cm_tvm_normalize_pair_stack obj(pc+4)(tower_add(tower_mod value 256)256)stack calls mem input output false _ CAP C4).
 rewrite tower_char_normalize_number;f_equal;f_equal;lia.
Qed.
