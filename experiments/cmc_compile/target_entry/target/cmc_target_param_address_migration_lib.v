Require Export SimpleC.EE.QCP_demos_human.cmc_target_temp_runtime_migration_lib.
From AUXLib Require Import ListLib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_tvm_fp_address_stack obj pc value stack calls mem input output offset rest :
 Zlength stack+2<65536 ->
 cm_code_at(tvm_object_code obj)pc(cm_fp_relative_address_code offset++rest) ->
 tvm_iter 4(TVMRunTask obj(TVMState pc(value::stack)calls mem input output))=
 TVMRunTask obj(TVMState(pc+4)(tower_wrap64(tower_getw mem 8+offset)::value::stack)calls mem input output).
Proof.
 intros CAP CODE;cbn[cm_fp_relative_address_code app]in CODE.
 pose proof(cm_code_at_tail _ _ _ _ CODE)as C1;pose proof(cm_code_at_tail _ _ _ _ C1)as C2;pose proof(cm_code_at_tail _ _ _ _ C2)as C3.
 cbn[tvm_iter].
 rewrite(cm_tvm_push_step obj(TVMState pc(value::stack)calls mem input output)_ _ CODE ltac:(cbn[tvm_stack];rewrite !Zlength_cons;lia)).
 cbv beta iota zeta delta [tvm_next_state tvm_stack tvm_pc tvm_calls tvm_mem tvm_input tvm_output];change(tower_wrap64 8)with 8.
 rewrite(cm_tvm_load_step obj(TVMState(pc+1)(8::value::stack)calls mem input output)8(value::stack)_ C1 eq_refl ltac:(unfold tower_word_valid;lia)).
 cbv beta iota zeta delta [tvm_next_state tvm_stack tvm_pc tvm_calls tvm_mem tvm_input tvm_output].
 rewrite(cm_tvm_push_step obj(TVMState(pc+1+1)(tower_getw mem 8::value::stack)calls mem input output)_ _ C2 ltac:(cbn[tvm_stack];rewrite !Zlength_cons;lia)).
 cbv beta iota zeta delta [tvm_next_state tvm_stack tvm_pc tvm_calls tvm_mem tvm_input tvm_output].
 rewrite(cm_tvm_code_step obj(TVMState(pc+1+1+1)(tower_wrap64 offset::tower_getw mem 8::value::stack)calls mem input output)_ _ _ C3).
 cbn[tvm_inst_step tvm_stack];assert(N:(2<=?Zlength(tower_wrap64 offset::tower_getw mem 8::value::stack))=true)by(apply Z.leb_le;rewrite !Zlength_cons;pose proof(Zlength_nonneg stack);lia);rewrite N.
 cbv beta iota zeta delta [tvm_action_task tvm_next_state tvm_pc tvm_calls tvm_mem tvm_input tvm_output hd tl].
 unfold tower_add;rewrite tower_wrap64_add_right;f_equal;f_equal;lia.
Qed.
