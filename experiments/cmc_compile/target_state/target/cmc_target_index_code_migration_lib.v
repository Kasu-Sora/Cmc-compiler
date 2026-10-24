Require Export SimpleC.EE.QCP_demos_human.cmc_target_temp_load_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma tower_wrap64_mul_right a b : tower_wrap64(a*tower_wrap64 b)=tower_wrap64(a*b).
Proof.
 replace(a*tower_wrap64 b)with(a*b+(-a*((b+9223372036854775808)/18446744073709551616))*18446744073709551616).
 - apply tower_wrap64_periodic.
 - unfold tower_wrap64;pose proof(Z.div_mod(b+9223372036854775808)18446744073709551616 ltac:(lia));nia.
Qed.
Lemma cm_tvm_mul_immediate obj pc value calls mem input output imm rest :
 cm_code_at(tvm_object_code obj)pc([TVMInst TVMPushOp imm;TVMInst TVMMulOp 0]++rest) ->
 tvm_iter 2(TVMRunTask obj(TVMState pc[value]calls mem input output))=
 TVMRunTask obj(TVMState(pc+2)[tower_mul value imm]calls mem input output).
Proof.
 intro CODE;cbn[app]in CODE;pose proof(cm_code_at_tail _ _ _ _ CODE)as C1.
 cbn[tvm_iter];rewrite(cm_tvm_push_step obj(TVMState pc[value]calls mem input output)_ _ CODE ltac:(change(1<65536);lia)).
 cbv beta iota zeta delta [tvm_next_state tvm_pc tvm_stack tvm_calls tvm_mem tvm_input tvm_output].
 rewrite(cm_tvm_code_step obj(TVMState(pc+1)[tower_wrap64 imm;value]calls mem input output)_ _ _ C1).
 cbn[tvm_inst_step tvm_stack];change(2<=?Zlength[tower_wrap64 imm;value])with true.
 cbv beta iota zeta delta [tvm_action_task tvm_next_state tvm_pc tvm_calls tvm_mem tvm_input tvm_output hd tl].
 unfold tower_mul;rewrite tower_wrap64_mul_right;f_equal;f_equal;lia.
Qed.
Lemma cm_tvm_index_tail policy p fid ty slot obj pc value calls mem input output rest :
 tower_word_valid(tower_getw mem 8+cm_temp_offset policy p fid slot) ->
 cm_code_at(tvm_object_code obj)pc(cm_index_tail_code policy p fid ty slot++rest) ->
 tvm_iter 8(TVMRunTask obj(TVMState pc[value]calls mem input output))=
 TVMRunTask obj(TVMState(pc+8)[tower_add(tower_getw mem(tower_getw mem 8+cm_temp_offset policy p fid slot))(tower_mul value(cm_type_size(cm_program_structs p)ty))]calls mem input output).
Proof.
 intros ADDR CODE;cbn[cm_index_tail_code cm_temp_load_code cm_fp_relative_address_code app]in CODE.
 pose proof(cm_code_at_tail _ _ _ _ CODE)as C1;pose proof(cm_code_at_tail _ _ _ _ C1)as C2.
 pose proof(cm_code_at_tail _ _ _ _ C2)as C3;pose proof(cm_code_at_tail _ _ _ _ C3)as C4.
 pose proof(cm_code_at_tail _ _ _ _ C4)as C5;pose proof(cm_code_at_tail _ _ _ _ C5)as C6;pose proof(cm_code_at_tail _ _ _ _ C6)as C7.
 replace(pc+1+1)with(pc+2)in C2 by lia;replace(pc+1+1+1+1+1+1+1)with(pc+7)in C7 by lia.
 change(tvm_step(tvm_iter 5(tvm_iter 2(TVMRunTask obj(TVMState pc[value]calls mem input output))))=
 TVMRunTask obj(TVMState(pc+8)[tower_add(tower_getw mem(tower_getw mem 8+cm_temp_offset policy p fid slot))(tower_mul value(cm_type_size(cm_program_structs p)ty))]calls mem input output)).
 rewrite(cm_tvm_mul_immediate _ _ _ _ _ _ _ _ _ CODE).
 rewrite(cm_tvm_fp_load_value _ _ _ _ _ _ _ _ _ ADDR C2);replace(pc+2+5)with(pc+7)by lia.
 rewrite(cm_tvm_code_step obj(TVMState(pc+7)[tower_getw mem(tower_getw mem 8+cm_temp_offset policy p fid slot);tower_mul value(cm_type_size(cm_program_structs p)ty)]calls mem input output)_ _ _ C7).
 cbn[tvm_inst_step tvm_stack];change(2<=?Zlength[_;_])with true.
 cbv beta iota zeta delta [tvm_action_task tvm_next_state tvm_pc tvm_calls tvm_mem tvm_input tvm_output hd tl].
 unfold tower_add;rewrite(Z.add_comm(tower_mul value(cm_type_size(cm_program_structs p)ty)));f_equal;f_equal;lia.
Qed.
Lemma cm_ptr_add_number_bridge p st ptr ty index : cm_value_type_compatible ptr(CMPtrTy ty) -> cm_ptr_shift_ok(cm_program_structs p)ptr index st=true ->
 cm_value_number st(cm_ptr_add(cm_program_structs p)ptr index)=tower_add(cm_value_number st ptr)(tower_mul index(cm_type_size(cm_program_structs p)ty)).
Proof.
 intros TYPE OK;unfold cm_ptr_shift_ok in OK;repeat rewrite andb_true_iff in OK;destruct OK as[[[LIVE _]_]_].
 destruct ptr;cbn[cm_pointer_live cm_ptr_gen]in LIVE;try discriminate.
 destruct TYPE as[TYPE|[BAD _]];[|discriminate];cbn[cm_value_type]in TYPE;injection TYPE as EQ;subst ty.
 cbn[cm_ptr_add cm_ptr_gen cm_ptr_lo cm_ptr_hi cm_ptr_offset cm_ptr_view cm_value_number];unfold tower_add,tower_mul;
 rewrite tower_wrap64_add_left,tower_wrap64_add_right;f_equal;ring.
Qed.
