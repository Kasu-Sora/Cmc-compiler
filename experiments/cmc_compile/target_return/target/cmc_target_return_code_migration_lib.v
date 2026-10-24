Require Export SimpleC.EE.QCP_demos_human.cmc_target_binary_dispatch_migration_lib.
From Coq Require Import ZArith List Bool Lia.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_tvm_return_epilogue obj pc value ret calls mem input output rest :
 tower_word_valid(tower_getw mem 8) ->cm_code_at(tvm_object_code obj)pc(cm_return_epilogue++rest) ->
 tvm_iter 6(TVMRunTask obj(TVMState pc[value](ret::calls)mem input output))=
 TVMRunTask obj(TVMState ret[value]calls(tower_setw mem 8(tower_getw mem(tower_getw mem 8)))input output).
Proof.
 intros FP CODE;cbn[cm_return_epilogue app]in CODE;pose proof(cm_code_at_tail _ _ _ _ CODE)as C1;pose proof(cm_code_at_tail _ _ _ _ C1)as C2.
 pose proof(cm_code_at_tail _ _ _ _ C2)as C3;pose proof(cm_code_at_tail _ _ _ _ C3)as C4;pose proof(cm_code_at_tail _ _ _ _ C4)as C5.
 cbn[tvm_iter];rewrite(cm_tvm_push_step obj(TVMState pc[value](ret::calls)mem input output)_ _ CODE ltac:(change(1<65536);lia)).
 cbv beta iota zeta delta [tvm_next_state tvm_pc tvm_stack tvm_calls tvm_mem tvm_input tvm_output];change(tower_wrap64 8)with 8.
 rewrite(cm_tvm_load_step obj(TVMState(pc+1)[8;value](ret::calls)mem input output)8[value]_ C1 eq_refl ltac:(unfold tower_word_valid;lia)).
 cbv beta iota zeta delta [tvm_next_state tvm_pc tvm_stack tvm_calls tvm_mem tvm_input tvm_output].
 rewrite(cm_tvm_load_step obj(TVMState(pc+1+1)[tower_getw mem 8;value](ret::calls)mem input output)(tower_getw mem 8)[value]_ C2 eq_refl FP).
 cbv beta iota zeta delta [tvm_next_state tvm_pc tvm_stack tvm_calls tvm_mem tvm_input tvm_output].
 rewrite(cm_tvm_push_step obj(TVMState(pc+1+1+1)[tower_getw mem(tower_getw mem 8);value](ret::calls)mem input output)_ _ C3 ltac:(change(2<65536);lia)).
 cbv beta iota zeta delta [tvm_next_state tvm_pc tvm_stack tvm_calls tvm_mem tvm_input tvm_output];change(tower_wrap64 8)with 8.
 rewrite(cm_tvm_code_step obj(TVMState(pc+1+1+1+1)[8;tower_getw mem(tower_getw mem 8);value](ret::calls)mem input output)_ _ _ C4).
 cbn[tvm_inst_step tvm_stack];change(2<=?Zlength[8;tower_getw mem(tower_getw mem 8);value])with true.
 cbv beta iota zeta delta [tvm_action_task tvm_next_state tvm_pc tvm_stack tvm_calls tvm_mem tvm_input tvm_output hd tl andb];change(tower_word_validb 8)with true;cbv beta iota zeta delta [tvm_action_task].
 rewrite(cm_tvm_code_step obj(TVMState(pc+1+1+1+1+1)[value](ret::calls)(tower_setw mem 8(tower_getw mem(tower_getw mem 8)))input output)_ _ _ C5).
 cbn[tvm_inst_step tvm_calls];assert(N:(1<=?Zlength(ret::calls))=true)by(apply Z.leb_le;change(1<=Zlength(ret::calls));pose proof(Zlength_nonneg calls);rewrite Zlength_cons;lia);rewrite N;reflexivity.
Qed.
Lemma cm_tvm_return_value st v ty obj pc ret calls mem input output rest :
 tower_word_valid(tower_getw mem 8) ->cm_code_at(tvm_object_code obj)pc((cm_char_normalize_code ty++cm_return_epilogue)++rest) ->
 tvm_iter(cm_code_steps(cm_char_normalize_code ty++cm_return_epilogue))(TVMRunTask obj(TVMState pc[cm_value_number st v](ret::calls)mem input output))=
 TVMRunTask obj(TVMState ret[cm_value_number st(cm_convert_value st ty v)]calls(tower_setw mem 8(tower_getw mem(tower_getw mem 8)))input output).
Proof.
 intros FP CODE;rewrite <-app_assoc in CODE;pose proof(cm_code_at_append_right _ _ _ _ CODE)as RET.
 rewrite cm_code_steps_append,tvm_iter_add,(cm_tvm_convert _ _ _ _ _ _ _ _ _ _ CODE).
 change(cm_code_steps cm_return_epilogue)with 6%nat;now rewrite(cm_tvm_return_epilogue _ _ _ _ _ _ _ _ _ FP RET).
Qed.
Lemma cm_tvm_return_zero obj pc ret calls mem input output rest :
 tower_word_valid(tower_getw mem 8) ->cm_code_at(tvm_object_code obj)pc(cm_fallthrough_tail_code++rest) ->
 tvm_iter 7(TVMRunTask obj(TVMState pc[](ret::calls)mem input output))=
 TVMRunTask obj(TVMState ret[0]calls(tower_setw mem 8(tower_getw mem(tower_getw mem 8)))input output).
Proof.
 intros FP CODE;cbn[cm_fallthrough_tail_code app]in CODE;pose proof(cm_code_at_tail _ _ _ _ CODE)as RET.
 change(tvm_iter 6(tvm_step(TVMRunTask obj(TVMState pc[](ret::calls)mem input output)))=TVMRunTask obj(TVMState ret[0]calls(tower_setw mem 8(tower_getw mem(tower_getw mem 8)))input output)).
 rewrite(cm_tvm_push_step obj(TVMState pc[](ret::calls)mem input output)_ _ CODE ltac:(change(0<65536);lia)).
 cbv beta iota zeta delta [tvm_next_state tvm_pc tvm_stack tvm_calls tvm_mem tvm_input tvm_output];change(tower_wrap64 0)with 0;now rewrite(cm_tvm_return_epilogue _ _ _ _ _ _ _ _ _ FP RET).
Qed.
