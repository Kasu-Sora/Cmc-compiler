Require Export SimpleC.EE.QCP_demos_human.cmc_target_param_normalize_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_target_param_address_migration_lib.
From AUXLib Require Import ListLib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_tvm_convert_stack st v ty obj pc stack calls mem input output rest :
 Zlength stack+2<65536 ->
 cm_code_at(tvm_object_code obj)pc(cm_char_normalize_code ty++rest) ->
 tvm_iter(cm_code_steps(cm_char_normalize_code ty))(TVMRunTask obj(TVMState pc(cm_value_number st v::stack)calls mem input output))=
 TVMRunTask obj(TVMState(pc+Zlength(cm_char_normalize_code ty))(cm_value_number st(cm_convert_value st ty v)::stack)calls mem input output).
Proof.
 intros CAP CODE;rewrite cm_convert_number;destruct ty;cbn[cm_type_eqb cm_type_dec cm_char_normalize_code cm_code_steps];try(rewrite Z.add_0_r;reflexivity).
 eapply cm_tvm_char_normalize_stack;[lia|exact CODE].
Qed.
Lemma cm_tvm_typed_store_stack obj pc addr value stack calls mem input output ty rest : tower_wrap64 value=value ->
 (match ty with CMCharTy=>tower_addr_valid addr|_=>tower_word_valid addr end) ->
 cm_code_at(tvm_object_code obj)pc(cm_store_code ty++rest) ->
 tvm_step(TVMRunTask obj(TVMState pc(addr::value::stack)calls mem input output))=
 TVMRunTask obj(TVMState(pc+1)stack calls(cm_store_mem ty addr value mem)input output).
Proof.
 intros WRAP ADDR CODE;assert(N:(2<=?Zlength(addr::value::stack))=true)by(apply Z.leb_le;rewrite !Zlength_cons;pose proof(Zlength_nonneg stack);lia);destruct ty;
 rewrite(cm_tvm_code_step obj(TVMState pc(addr::value::stack)calls mem input output)_ _ _ CODE);
 cbn[tvm_inst_step tvm_stack];rewrite N;
 first[apply tower_word_validb_spec in ADDR|apply tower_addr_validb_spec in ADDR];cbn[hd andb];rewrite ADDR;
 cbv beta iota zeta delta [tvm_action_task tvm_next_state tvm_pc tvm_calls tvm_mem tvm_input tvm_output hd tl cm_store_mem];try rewrite WRAP;try reflexivity;unfold tower_setb;rewrite tower_u8_idempotent;reflexivity.
Qed.
Lemma cm_tvm_address_store_stack obj pc value stack calls mem input output ty offset rest : Zlength stack+2<65536 -> tower_wrap64 value=value ->
 (match ty with CMCharTy=>tower_addr_valid(tower_wrap64(tower_getw mem 8+offset))|_=>tower_word_valid(tower_wrap64(tower_getw mem 8+offset))end) ->
 cm_code_at(tvm_object_code obj)pc(cm_fp_relative_address_code offset++cm_store_code ty++rest) ->
 tvm_iter 5(TVMRunTask obj(TVMState pc(value::stack)calls mem input output))=
 TVMRunTask obj(TVMState(pc+5)stack calls(cm_store_mem ty(tower_wrap64(tower_getw mem 8+offset))value mem)input output).
Proof.
 intros CAP WRAP ADDR CODE;pose proof(cm_code_at_append_right _ _ _ _ CODE)as STORE.
 change(cm_code_at(tvm_object_code obj)(pc+4)(cm_store_code ty++rest))in STORE.
 change(tvm_step(tvm_iter 4(TVMRunTask obj(TVMState pc(value::stack)calls mem input output)))=TVMRunTask obj(TVMState(pc+5)stack calls(cm_store_mem ty(tower_wrap64(tower_getw mem 8+offset))value mem)input output)).
 rewrite(cm_tvm_fp_address_stack _ _ _ _ _ _ _ _ _ _ CAP CODE).
 rewrite(cm_tvm_typed_store_stack _ _ _ _ _ _ _ _ _ _ _ WRAP ADDR STORE);f_equal;f_equal;lia.
Qed.
Lemma cm_tvm_init_code_stack st v ty obj pc stack calls mem input output offset rest : Zlength stack+2<65536 ->
 (match ty with CMCharTy=>tower_addr_valid(tower_wrap64(tower_getw mem 8+offset))|_=>tower_word_valid(tower_wrap64(tower_getw mem 8+offset))end) ->
 cm_code_at(tvm_object_code obj)pc(cm_char_normalize_code ty++cm_fp_relative_address_code offset++cm_store_code ty++rest) ->
 tvm_iter(cm_code_steps(cm_char_normalize_code ty++cm_fp_relative_address_code offset++cm_store_code ty))(TVMRunTask obj(TVMState pc(cm_value_number st v::stack)calls mem input output))=
 TVMRunTask obj(TVMState(pc+Zlength(cm_char_normalize_code ty++cm_fp_relative_address_code offset++cm_store_code ty))stack calls(cm_store_mem ty(tower_wrap64(tower_getw mem 8+offset))(cm_value_number st(cm_convert_value st ty v))mem)input output).
Proof.
 intros CAP ADDR CODE;pose proof(cm_code_at_append_right _ _ _ _ CODE)as TAIL.
 pose proof(cm_tvm_convert_stack st v ty obj pc stack calls mem input output _ CAP CODE)as CONV.
 pose proof(cm_tvm_address_store_stack obj(pc+Zlength(cm_char_normalize_code ty))(cm_value_number st(cm_convert_value st ty v))stack calls mem input output ty offset rest CAP (cm_value_number_wrap _ _)ADDR TAIL)as STORE.
 assert(N:cm_code_steps(cm_char_normalize_code ty++cm_fp_relative_address_code offset++cm_store_code ty)=(cm_code_steps(cm_char_normalize_code ty)+5)%nat)by(destruct ty;reflexivity).
 rewrite N,tvm_iter_add,CONV,STORE;f_equal;f_equal;destruct ty;cbv beta iota zeta delta [cm_char_normalize_code cm_type_eqb cm_type_dec cm_fp_relative_address_code cm_store_code app Zlength Zlength_aux length];lia.
Qed.
