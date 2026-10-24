Require Export SimpleC.EE.QCP_demos_human.cmc_target_init_migration_lib.
From Coq Require Import ZArith List Bool Lia.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_code_steps_append a b : cm_code_steps(a++b)=(cm_code_steps a+cm_code_steps b)%nat.
Proof. unfold cm_code_steps;rewrite Zlength_app;apply Z2Nat.inj_add;apply Zlength_nonneg. Qed.
Lemma cm_tvm_fp_load_empty obj pc calls mem input output offset rest :
 tower_word_valid(tower_getw mem 8+offset) ->
 cm_code_at(tvm_object_code obj)pc(cm_fp_relative_address_code offset++TVMInst TVMLoadOp 0::rest) ->
 tvm_iter 5(TVMRunTask obj(TVMState pc[]calls mem input output))=
 TVMRunTask obj(TVMState(pc+5)[tower_getw mem(tower_getw mem 8+offset)]calls mem input output).
Proof.
 intros ADDR CODE;pose proof(cm_code_at_append_right _ _ _ _ CODE)as LOAD.
 change(cm_code_at(tvm_object_code obj)(pc+4)(TVMInst TVMLoadOp 0::rest))in LOAD.
 change(tvm_step(tvm_iter 4(TVMRunTask obj(TVMState pc[]calls mem input output)))=TVMRunTask obj(TVMState(pc+5)[tower_getw mem(tower_getw mem 8+offset)]calls mem input output)).
 rewrite(cm_tvm_fp_address _ _ _ _ _ _ _ _ CODE).
 rewrite tower_wrap64_fixed by(unfold tower_signed64,tower_word_valid in *;lia).
 rewrite(cm_tvm_load_step obj(TVMState(pc+4)[tower_getw mem 8+offset]calls mem input output)(tower_getw mem 8+offset)[]_ LOAD eq_refl ADDR).
 cbv beta iota zeta delta [tvm_next_state tvm_pc tvm_stack tvm_calls tvm_mem tvm_input tvm_output];f_equal;f_equal;lia.
Qed.
Lemma cm_store_reload_number st ty v mem addr :
 (match ty with CMCharTy=>tower_getb(cm_store_mem ty addr(cm_value_number st(cm_convert_value st ty v))mem)addr|_=>tower_getw(cm_store_mem ty addr(cm_value_number st(cm_convert_value st ty v))mem)addr end)=cm_value_number st(cm_convert_value st ty v).
Proof.
 destruct ty;cbn[cm_store_mem];try(rewrite tower_getw_setw,tower_wrap64_idempotent;apply cm_value_number_wrap).
 rewrite tower_getb_setb_same,tower_u8_idempotent;rewrite cm_convert_number;apply tower_u8_idempotent.
Qed.
Lemma cm_tvm_assign_tail policy p fid ty slot st v obj pc calls mem input output rest :
 let offset:=cm_temp_offset policy p fid slot in let ptr:=tower_getw mem(tower_getw mem 8+offset)in
 tower_word_valid(tower_getw mem 8+offset) ->
 (match ty with CMCharTy=>tower_addr_valid ptr|_=>tower_word_valid ptr end) ->
 cm_range_disjoint ptr(cm_store_width ty)8 8 -> cm_range_disjoint ptr(cm_store_width ty)(tower_getw mem 8+offset)8 ->
 cm_code_at(tvm_object_code obj)pc(cm_assign_tail_code policy p fid ty slot++rest) ->
 tvm_iter(cm_code_steps(cm_assign_tail_code policy p fid ty slot))(TVMRunTask obj(TVMState pc[cm_value_number st v]calls mem input output))=
 TVMRunTask obj(TVMState(pc+Zlength(cm_assign_tail_code policy p fid ty slot))[cm_value_number st(cm_convert_value st ty v)]calls(cm_store_mem ty ptr(cm_value_number st(cm_convert_value st ty v))mem)input output).
Proof.
 cbn zeta;intros SLOT ADDR FP DIS CODE;unfold cm_assign_tail_code in CODE|-*;repeat rewrite <-app_assoc in CODE.
 pose proof(cm_code_at_append_right _ _ _ _ CODE)as C1.
 pose proof(cm_code_at_append_right _ _ _ _ C1)as C2.
 pose proof(cm_code_at_append_right _ _ _ _ C2)as C3.
 pose proof(cm_code_at_append_right _ _ _ _ C3)as C4.
 rewrite ?cm_layout_temp_load_length,?cm_layout_store_length in C2,C3,C4.
 assert(FPNEW: tower_getw(cm_store_mem ty(tower_getw mem(tower_getw mem 8+cm_temp_offset policy p fid slot))(cm_value_number st(cm_convert_value st ty v))mem)8=tower_getw mem 8)by(apply cm_store_mem_word_outside;unfold cm_range_disjoint in FP;tauto).
 assert(PTRNEW: tower_getw(cm_store_mem ty(tower_getw mem(tower_getw mem 8+cm_temp_offset policy p fid slot))(cm_value_number st(cm_convert_value st ty v))mem)(tower_getw mem 8+cm_temp_offset policy p fid slot)=tower_getw mem(tower_getw mem 8+cm_temp_offset policy p fid slot))by(apply cm_store_mem_word_outside;unfold cm_range_disjoint in DIS;tauto).
 repeat rewrite cm_code_steps_append;repeat rewrite tvm_iter_add.
 rewrite(cm_tvm_convert _ _ _ _ _ _ _ _ _ _ CODE).
 unfold cm_temp_load_code in C1;rewrite <-app_assoc in C1.
 change(cm_code_steps(cm_temp_load_code policy p fid slot))with 5%nat.
 rewrite(cm_tvm_fp_load_value _ _ _ _ _ _ _ _ _ SLOT C1).
 assert(STORESTEPS:cm_code_steps(cm_store_code ty)=1%nat)by(destruct ty;reflexivity);rewrite STORESTEPS;change(tvm_iter 1)with tvm_step.
 rewrite(cm_tvm_typed_store _ _ _ _ _ _ _ _ _ _ (cm_value_number_wrap _ _)ADDR C2).
 unfold cm_temp_load_code in C3;rewrite <-app_assoc in C3.
 rewrite(cm_tvm_fp_load_empty _ _ _ _ _ _ _ _ ltac:(rewrite FPNEW;exact SLOT)C3),FPNEW,PTRNEW.
 assert(LOADSTEPS:cm_code_steps(cm_load_code ty)=1%nat)by(destruct ty;reflexivity);rewrite LOADSTEPS;change(tvm_iter 1)with tvm_step.
 rewrite(cm_tvm_typed_load _ _ _ _ _ _ _ _ _ ADDR C4),cm_store_reload_number.
 f_equal;f_equal;repeat rewrite Zlength_app;rewrite !cm_layout_temp_load_length,cm_layout_store_length,cm_layout_load_length;lia.
Qed.
