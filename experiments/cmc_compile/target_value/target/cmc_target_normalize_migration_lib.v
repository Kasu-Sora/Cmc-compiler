Require Export SimpleC.EE.QCP_demos_human.cmc_target_normalize_arithmetic_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_tvm_normalize_pair obj pc value calls mem input output (add:bool) rest :
 cm_code_at(tvm_object_code obj)pc([TVMInst TVMPushOp 256;TVMInst(if add then TVMAddOp else TVMModOp)0]++rest) ->
 tvm_iter 2(TVMRunTask obj(TVMState pc[value]calls mem input output))=
 TVMRunTask obj(TVMState(pc+2)[if add then tower_add value 256 else tower_mod value 256]calls mem input output).
Proof.
 intro CODE;cbn[app]in CODE;pose proof(cm_code_at_tail _ _ _ _ CODE)as C1.
 cbn[tvm_iter];rewrite(cm_tvm_push_step obj(TVMState pc[value]calls mem input output)_ _ CODE ltac:(change(1<65536);lia)).
 cbv beta iota zeta delta [tvm_next_state tvm_pc tvm_stack tvm_calls tvm_mem tvm_input tvm_output];change(tower_wrap64 256)with 256.
 rewrite(cm_tvm_code_step obj(TVMState(pc+1)[256;value]calls mem input output)_ _ _ C1).
 destruct add;cbn[tvm_inst_step tvm_stack];change(2<=?Zlength[256;value])with true;
 cbv beta iota zeta delta [tvm_action_task tvm_next_state tvm_pc tvm_calls tvm_mem tvm_input tvm_output hd tl];cbn;
 f_equal;f_equal;lia.
Qed.
Lemma cm_tvm_char_normalize obj pc value calls mem input output rest :
 cm_code_at(tvm_object_code obj)pc(cm_char_normalize_code CMCharTy++rest) ->
 tvm_iter 6(TVMRunTask obj(TVMState pc[value]calls mem input output))=
 TVMRunTask obj(TVMState(pc+6)[tower_u8 value]calls mem input output).
Proof.
 intro CODE;cbn[cm_char_normalize_code app]in CODE.
 pose proof(cm_code_at_tail _ _ _ _ CODE)as C1;pose proof(cm_code_at_tail _ _ _ _ C1)as C2.
 pose proof(cm_code_at_tail _ _ _ _ C2)as C3;pose proof(cm_code_at_tail _ _ _ _ C3)as C4.
 replace(pc+1+1)with(pc+2)in C2 by lia;replace(pc+1+1+1+1)with(pc+4)in C4 by lia.
 change(tvm_iter 2(tvm_iter 2(tvm_iter 2(TVMRunTask obj(TVMState pc[value]calls mem input output))))=TVMRunTask obj(TVMState(pc+6)[tower_u8 value]calls mem input output)).
 rewrite(cm_tvm_normalize_pair obj pc value calls mem input output false _ CODE).
 rewrite(cm_tvm_normalize_pair obj(pc+2)(tower_mod value 256)calls mem input output true _ C2).
 replace(pc+2+2)with(pc+4)by lia.
 rewrite(cm_tvm_normalize_pair obj(pc+4)(tower_add(tower_mod value 256)256)calls mem input output false _ C4).
 rewrite tower_char_normalize_number;f_equal;f_equal;lia.
Qed.
Lemma cm_tvm_status_tail obj pc value calls mem input output :
 cm_code_at(tvm_object_code obj)pc cm_status_tail_code ->
 tvm_iter 7(TVMRunTask obj(TVMState pc[value]calls mem input output))=
 TVMDoneTask(TVMState(pc+6)[]calls mem input output)(tower_status value)0.
Proof.
 intro CODE;pose proof(cm_code_at_append_right _ _ _ _ CODE)as HALT.
 change(cm_code_at(tvm_object_code obj)(pc+6)[TVMInst TVMHaltOp 0])in HALT.
 change(tvm_step(tvm_iter 6(TVMRunTask obj(TVMState pc[value]calls mem input output)))=TVMDoneTask(TVMState(pc+6)[]calls mem input output)(tower_status value)0).
 rewrite(cm_tvm_char_normalize _ _ _ _ _ _ _ _ CODE).
 rewrite(cm_tvm_code_step obj(TVMState(pc+6)[tower_u8 value]calls mem input output)_ _ _ HALT).
 cbn[tvm_inst_step tvm_stack];change(1<=?Zlength[tower_u8 value])with true.
 assert(B:tower_byte_valueb(tower_u8 value)=true)by(apply tower_byte_valueb_spec;apply tower_u8_range).
 cbn[hd andb];rewrite B;reflexivity.
Qed.
