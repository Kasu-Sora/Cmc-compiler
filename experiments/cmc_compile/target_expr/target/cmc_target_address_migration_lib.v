Require Export SimpleC.EE.QCP_demos_human.cmc_target_string_migration_lib.
From Coq Require Import ZArith List Bool Lia.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Lemma tower_wrap64_add_right a b : tower_wrap64(a+tower_wrap64 b)=tower_wrap64(a+b).
Proof.
 replace (a+tower_wrap64 b) with (a+b+(-((b+9223372036854775808)/18446744073709551616))*18446744073709551616).
 - apply tower_wrap64_periodic.
 - unfold tower_wrap64; pose proof(Z.div_mod (b+9223372036854775808) 18446744073709551616 ltac:(lia)); lia.
Qed.
Lemma cm_tvm_fp_address obj pc calls mem input output offset rest :
 cm_code_at (tvm_object_code obj) pc (cm_fp_relative_address_code offset++rest) ->
 tvm_iter 4 (TVMRunTask obj (TVMState pc [] calls mem input output))=
 TVMRunTask obj (TVMState (pc+4) [tower_wrap64(tower_getw mem 8+offset)] calls mem input output).
Proof.
 intro CODE; cbn [cm_fp_relative_address_code app]in CODE.
 pose proof(cm_code_at_tail _ _ _ _ CODE)as C1; pose proof(cm_code_at_tail _ _ _ _ C1)as C2; pose proof(cm_code_at_tail _ _ _ _ C2)as C3.
 cbn [tvm_iter].
 rewrite(cm_tvm_push_step obj (TVMState pc [] calls mem input output) _ _ CODE ltac:(change(0<65536); lia)).
 cbv beta iota zeta delta [tvm_next_state tvm_stack tvm_pc tvm_calls tvm_mem tvm_input tvm_output]. change(tower_wrap64 8)with 8.
 rewrite(cm_tvm_load_step obj (TVMState (pc+1) [8] calls mem input output) 8 [] _ C1 eq_refl ltac:(unfold tower_word_valid; lia)).
 cbv beta iota zeta delta [tvm_next_state tvm_stack tvm_pc tvm_calls tvm_mem tvm_input tvm_output].
 rewrite(cm_tvm_push_step obj (TVMState (pc+1+1) [tower_getw mem 8] calls mem input output) _ _ C2 ltac:(change(1<65536); lia)).
 cbv beta iota zeta delta [tvm_next_state tvm_stack tvm_pc tvm_calls tvm_mem tvm_input tvm_output].
 rewrite(cm_tvm_code_step obj (TVMState (pc+1+1+1) [tower_wrap64 offset;tower_getw mem 8] calls mem input output) _ _ _ C3).
 cbn [tvm_inst_step tvm_stack]; change(2<=?Zlength [tower_wrap64 offset;tower_getw mem 8])with true.
 cbv beta iota zeta delta [tvm_action_task tvm_next_state tvm_pc tvm_calls tvm_mem tvm_input tvm_output hd tl].
 unfold tower_add; rewrite tower_wrap64_add_right; f_equal; f_equal; lia.
Qed.
