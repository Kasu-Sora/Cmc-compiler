Require Export SimpleC.EE.QCP_demos_human.cmc_target_temp_runtime_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_tvm_fp_address_value obj pc value calls mem input output offset rest :
 cm_code_at(tvm_object_code obj)pc(cm_fp_relative_address_code offset++rest) ->
 tvm_iter 4(TVMRunTask obj(TVMState pc[value]calls mem input output))=
 TVMRunTask obj(TVMState(pc+4)[tower_wrap64(tower_getw mem 8+offset);value]calls mem input output).
Proof.
 intro CODE;cbn[cm_fp_relative_address_code app]in CODE.
 pose proof(cm_code_at_tail _ _ _ _ CODE)as C1;pose proof(cm_code_at_tail _ _ _ _ C1)as C2;pose proof(cm_code_at_tail _ _ _ _ C2)as C3.
 cbn[tvm_iter].
 rewrite(cm_tvm_push_step obj(TVMState pc[value]calls mem input output)_ _ CODE ltac:(change(1<65536);lia)).
 cbv beta iota zeta delta [tvm_next_state tvm_stack tvm_pc tvm_calls tvm_mem tvm_input tvm_output];change(tower_wrap64 8)with 8.
 rewrite(cm_tvm_load_step obj(TVMState(pc+1)[8;value]calls mem input output)8[value]_ C1 eq_refl ltac:(unfold tower_word_valid;lia)).
 cbv beta iota zeta delta [tvm_next_state tvm_stack tvm_pc tvm_calls tvm_mem tvm_input tvm_output].
 rewrite(cm_tvm_push_step obj(TVMState(pc+1+1)[tower_getw mem 8;value]calls mem input output)_ _ C2 ltac:(change(2<65536);lia)).
 cbv beta iota zeta delta [tvm_next_state tvm_stack tvm_pc tvm_calls tvm_mem tvm_input tvm_output].
 rewrite(cm_tvm_code_step obj(TVMState(pc+1+1+1)[tower_wrap64 offset;tower_getw mem 8;value]calls mem input output)_ _ _ C3).
 cbn[tvm_inst_step tvm_stack];change(2<=?Zlength[tower_wrap64 offset;tower_getw mem 8;value])with true.
 cbv beta iota zeta delta [tvm_action_task tvm_next_state tvm_pc tvm_calls tvm_mem tvm_input tvm_output hd tl].
 unfold tower_add;rewrite tower_wrap64_add_right;f_equal;f_equal;lia.
Qed.
Lemma cm_tvm_fp_store obj pc value calls mem input output offset rest :
 tower_word_valid(tower_getw mem 8+offset) ->
 cm_code_at(tvm_object_code obj)pc(cm_fp_relative_address_code offset++TVMInst TVMStoreOp 0::rest) ->
 tvm_iter 5(TVMRunTask obj(TVMState pc[value]calls mem input output))=
 TVMRunTask obj(TVMState(pc+5)[]calls(tower_setw mem(tower_getw mem 8+offset)value)input output).
Proof.
 intros ADDR CODE;pose proof(cm_code_at_append_right _ _ _ _ CODE)as STORE.
 change(cm_code_at(tvm_object_code obj)(pc+4)(TVMInst TVMStoreOp 0::rest))in STORE.
 change(tvm_step(tvm_iter 4(TVMRunTask obj(TVMState pc[value]calls mem input output)))=TVMRunTask obj(TVMState(pc+5)[]calls(tower_setw mem(tower_getw mem 8+offset)value)input output)).
 rewrite(cm_tvm_fp_address_value _ _ _ _ _ _ _ _ _ CODE).
 rewrite tower_wrap64_fixed by(unfold tower_signed64,tower_word_valid in *;lia).
 rewrite(cm_tvm_code_step obj(TVMState(pc+4)[tower_getw mem 8+offset;value]calls mem input output)_ _ _ STORE).
 cbn[tvm_inst_step tvm_stack];change(2<=?Zlength[tower_getw mem 8+offset;value])with true.
 apply tower_word_validb_spec in ADDR;cbn[hd andb];rewrite ADDR.
 cbv beta iota zeta delta [tvm_action_task tvm_next_state tvm_pc tvm_calls tvm_mem tvm_input tvm_output hd tl];f_equal;f_equal;lia.
Qed.
