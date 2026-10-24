Require Export SimpleC.EE.QCP_demos_human.cmc_target_binary_numeric_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_tvm_mul_pair obj pc value bottom calls mem input output imm rest :
 cm_code_at(tvm_object_code obj)pc([TVMInst TVMPushOp imm;TVMInst TVMMulOp 0]++rest) ->
 tvm_iter 2(TVMRunTask obj(TVMState pc[value;bottom]calls mem input output))=
 TVMRunTask obj(TVMState(pc+2)[tower_mul value imm;bottom]calls mem input output).
Proof.
 intro CODE;cbn[app]in CODE;pose proof(cm_code_at_tail _ _ _ _ CODE)as C1.
 cbn[tvm_iter];rewrite(cm_tvm_push_step obj(TVMState pc[value;bottom]calls mem input output)_ _ CODE ltac:(change(2<65536);lia)).
 cbv beta iota zeta delta [tvm_next_state tvm_pc tvm_stack tvm_calls tvm_mem tvm_input tvm_output].
 rewrite(cm_tvm_code_step obj(TVMState(pc+1)[tower_wrap64 imm;value;bottom]calls mem input output)_ _ _ C1).
 cbn[tvm_inst_step tvm_stack];change(2<=?Zlength[tower_wrap64 imm;value;bottom])with true.
 cbv beta iota zeta delta [tvm_action_task tvm_next_state tvm_pc tvm_calls tvm_mem tvm_input tvm_output hd tl].
 unfold tower_mul;rewrite tower_wrap64_mul_right;f_equal;f_equal;lia.
Qed.
Lemma cm_tvm_scale_left obj pc l r calls mem input output size op rest : op=8 \/ op=9 ->
 cm_code_at(tvm_object_code obj)pc([TVMInst TVMSwapOp 0;TVMInst TVMPushOp size;TVMInst TVMMulOp 0;TVMInst(cm_binary_opcode op)0]++rest) ->
 tvm_iter 4(TVMRunTask obj(TVMState pc[l;r]calls mem input output))=
 TVMRunTask obj(TVMState(pc+4)[cm_binary_number op l(tower_mul r size)]calls mem input output).
Proof.
 intros OPS CODE;cbn[app]in CODE;pose proof(cm_code_at_tail _ _ _ _ CODE)as C1.
 pose proof(cm_code_at_tail _ _ _ _ C1)as C2;pose proof(cm_code_at_tail _ _ _ _ C2)as C3.
 change(tvm_step(tvm_iter 2(tvm_step(TVMRunTask obj(TVMState pc[l;r]calls mem input output))))=TVMRunTask obj(TVMState(pc+4)[cm_binary_number op l(tower_mul r size)]calls mem input output)).
 rewrite(cm_tvm_swap_pair _ _ _ _ _ _ _ _ _ CODE),(cm_tvm_mul_pair _ _ _ _ _ _ _ _ _ _ C1).
 replace(pc+1+1+1)with(pc+1+2)in C3 by lia.
 rewrite(cm_tvm_binary_number_total _ _ _ _ _ _ _ _ op _ ltac:(intros H;destruct OPS,H;lia)ltac:(destruct OPS;lia)C3);f_equal;f_equal;lia.
Qed.
Lemma cm_tvm_scale_right obj pc l r calls mem input output size rest :
 cm_code_at(tvm_object_code obj)pc([TVMInst TVMPushOp size;TVMInst TVMMulOp 0;TVMInst TVMSwapOp 0;TVMInst TVMAddOp 0]++rest) ->
 tvm_iter 4(TVMRunTask obj(TVMState pc[l;r]calls mem input output))=
 TVMRunTask obj(TVMState(pc+4)[tower_add r(tower_mul l size)]calls mem input output).
Proof.
 intro CODE;cbn[app]in CODE;pose proof(cm_code_at_tail _ _ _ _ CODE)as C1.
 pose proof(cm_code_at_tail _ _ _ _ C1)as C2;pose proof(cm_code_at_tail _ _ _ _ C2)as C3.
 replace(pc+1+1)with(pc+2)in C2 by lia;replace(pc+1+1+1)with(pc+2+1)in C3 by lia.
 change(tvm_step(tvm_step(tvm_iter 2(TVMRunTask obj(TVMState pc[l;r]calls mem input output))))=TVMRunTask obj(TVMState(pc+4)[tower_add r(tower_mul l size)]calls mem input output)).
 rewrite(cm_tvm_mul_pair _ _ _ _ _ _ _ _ _ _ CODE),(cm_tvm_swap_pair _ _ _ _ _ _ _ _ _ C2).
 rewrite(cm_tvm_binary_number_total _ _ _ _ _ _ _ _ 8 _ ltac:(lia)ltac:(lia)C3).
 cbn[cm_binary_number Z.eqb Pos.eqb];unfold tower_add;rewrite(Z.add_comm(tower_mul l size)r);f_equal;f_equal;lia.
Qed.
Lemma cm_tvm_ptr_difference obj pc l r calls mem input output size rest : tower_signed64 size ->size<>0 ->
 cm_code_at(tvm_object_code obj)pc([TVMInst TVMSwapOp 0;TVMInst TVMSubOp 0;TVMInst TVMPushOp size;TVMInst TVMDivOp 0]++rest) ->
 tvm_iter 4(TVMRunTask obj(TVMState pc[l;r]calls mem input output))=
 TVMRunTask obj(TVMState(pc+4)[tower_div(tower_sub l r)size]calls mem input output).
Proof.
 intros SIGN NZ CODE;cbn[app]in CODE;pose proof(cm_code_at_tail _ _ _ _ CODE)as C1.
 pose proof(cm_code_at_tail _ _ _ _ C1)as C2;pose proof(cm_code_at_tail _ _ _ _ C2)as C3.
 cbn[tvm_iter];rewrite(cm_tvm_swap_pair _ _ _ _ _ _ _ _ _ CODE).
 rewrite(cm_tvm_binary_number_total _ _ _ _ _ _ _ _ 9 _ ltac:(lia)ltac:(lia)C1);cbn[cm_binary_number Z.eqb Pos.eqb].
 rewrite(cm_tvm_push_step obj(TVMState(pc+1+1)[tower_sub l r]calls mem input output)_ _ C2 ltac:(change(1<65536);lia)).
 cbv beta iota zeta delta [tvm_next_state tvm_pc tvm_stack tvm_calls tvm_mem tvm_input tvm_output];rewrite(tower_wrap64_fixed size SIGN).
 rewrite(cm_tvm_binary_number_total _ _ _ _ _ _ _ _ 11 _ (fun _=>NZ)ltac:(lia)C3);cbn[cm_binary_number Z.eqb Pos.eqb];f_equal;f_equal;lia.
Qed.
