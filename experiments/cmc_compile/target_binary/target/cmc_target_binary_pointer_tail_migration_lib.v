Require Export SimpleC.EE.QCP_demos_human.cmc_target_binary_pointer_code_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_tvm_binary_left_pointer_tail policy p fid op lhs rhs slot obj pc right calls mem input output rest :
 op=8 \/ op=9 -> cm_pointerb(cm_expr_type lhs)=true ->cm_pointerb(cm_expr_type rhs)=false ->
 tower_word_valid(tower_getw mem 8+cm_temp_offset policy p fid slot) ->
 cm_code_at(tvm_object_code obj)pc(cm_binary_finish_code policy p fid op lhs rhs slot++rest) ->
 tvm_iter(cm_code_steps(cm_binary_finish_code policy p fid op lhs rhs slot))(TVMRunTask obj(TVMState pc[right]calls mem input output))=
 TVMRunTask obj(TVMState(pc+9)[cm_binary_number op(tower_getw mem(tower_getw mem 8+cm_temp_offset policy p fid slot))(tower_mul right(cm_pointer_scale p lhs))]calls mem input output).
Proof.
 intros OPS LP RP ADDR CODE.
 assert(FIN:cm_binary_finish_code policy p fid op lhs rhs slot=cm_temp_load_code policy p fid slot++[TVMInst TVMSwapOp 0;TVMInst TVMPushOp(cm_pointer_scale p lhs);TVMInst TVMMulOp 0;TVMInst(cm_binary_opcode op)0]).
 { unfold cm_binary_finish_code;destruct OPS as[-> | ->];cbn[Z.eqb Pos.eqb andb];rewrite LP,RP;reflexivity. }
 rewrite FIN in CODE|-*;rewrite <-app_assoc in CODE;pose proof(cm_code_at_append_right _ _ _ _ CODE)as C5;rewrite cm_layout_temp_load_length in C5.
 change(cm_code_steps(cm_temp_load_code policy p fid slot++[TVMInst TVMSwapOp 0;TVMInst TVMPushOp(cm_pointer_scale p lhs);TVMInst TVMMulOp 0;TVMInst(cm_binary_opcode op)0]))with 9%nat.
 change(tvm_iter 4(tvm_iter 5(TVMRunTask obj(TVMState pc[right]calls mem input output)))=TVMRunTask obj(TVMState(pc+9)[cm_binary_number op(tower_getw mem(tower_getw mem 8+cm_temp_offset policy p fid slot))(tower_mul right(cm_pointer_scale p lhs))]calls mem input output)).
 unfold cm_temp_load_code in CODE;rewrite <-app_assoc in CODE;rewrite(cm_tvm_fp_load_value _ _ _ _ _ _ _ _ _ ADDR CODE).
 rewrite(cm_tvm_scale_left _ _ _ _ _ _ _ _ _ op _ OPS C5);f_equal;f_equal;lia.
Qed.
Lemma cm_tvm_binary_right_pointer_tail policy p fid  lhs rhs slot obj pc right calls mem input output rest :
 cm_pointerb(cm_expr_type rhs)=true ->
 tower_word_valid(tower_getw mem 8+cm_temp_offset policy p fid slot) ->
 cm_code_at(tvm_object_code obj)pc(cm_binary_finish_code policy p fid 8 lhs rhs slot++rest) ->
 tvm_iter(cm_code_steps(cm_binary_finish_code policy p fid 8 lhs rhs slot))(TVMRunTask obj(TVMState pc[right]calls mem input output))=
 TVMRunTask obj(TVMState(pc+9)[tower_add right(tower_mul(tower_getw mem(tower_getw mem 8+cm_temp_offset policy p fid slot))(cm_pointer_scale p rhs))]calls mem input output).
Proof.
 intros RP ADDR CODE.
 assert(FIN:cm_binary_finish_code policy p fid 8 lhs rhs slot=cm_temp_load_code policy p fid slot++[TVMInst TVMPushOp(cm_pointer_scale p rhs);TVMInst TVMMulOp 0;TVMInst TVMSwapOp 0;TVMInst TVMAddOp 0]).
 { unfold cm_binary_finish_code;cbn[Z.eqb Pos.eqb andb];rewrite RP;reflexivity. }
 rewrite FIN in CODE|-*;rewrite <-app_assoc in CODE;pose proof(cm_code_at_append_right _ _ _ _ CODE)as C5;rewrite cm_layout_temp_load_length in C5.
 change(cm_code_steps(cm_temp_load_code policy p fid slot++[TVMInst TVMPushOp(cm_pointer_scale p rhs);TVMInst TVMMulOp 0;TVMInst TVMSwapOp 0;TVMInst TVMAddOp 0]))with 9%nat.
 change(tvm_iter 4(tvm_iter 5(TVMRunTask obj(TVMState pc[right]calls mem input output)))=TVMRunTask obj(TVMState(pc+9)[tower_add right(tower_mul(tower_getw mem(tower_getw mem 8+cm_temp_offset policy p fid slot))(cm_pointer_scale p rhs))]calls mem input output)).
 unfold cm_temp_load_code in CODE;rewrite <-app_assoc in CODE;rewrite(cm_tvm_fp_load_value _ _ _ _ _ _ _ _ _ ADDR CODE).
 rewrite(cm_tvm_scale_right _ _ _ _ _ _ _ _ _ _  C5);f_equal;f_equal;lia.
Qed.
Lemma cm_tvm_binary_difference_pointer_tail policy p fid  lhs rhs slot obj pc right calls mem input output rest :
 cm_pointerb(cm_expr_type lhs)=true ->cm_pointerb(cm_expr_type rhs)=true -> tower_signed64(cm_pointer_scale p lhs) ->cm_pointer_scale p lhs<>0 ->
 tower_word_valid(tower_getw mem 8+cm_temp_offset policy p fid slot) ->
 cm_code_at(tvm_object_code obj)pc(cm_binary_finish_code policy p fid 9 lhs rhs slot++rest) ->
 tvm_iter(cm_code_steps(cm_binary_finish_code policy p fid 9 lhs rhs slot))(TVMRunTask obj(TVMState pc[right]calls mem input output))=
 TVMRunTask obj(TVMState(pc+9)[tower_div(tower_sub(tower_getw mem(tower_getw mem 8+cm_temp_offset policy p fid slot))right)(cm_pointer_scale p lhs)]calls mem input output).
Proof.
 intros LP RP SIGN NZ ADDR CODE.
 assert(FIN:cm_binary_finish_code policy p fid 9 lhs rhs slot=cm_temp_load_code policy p fid slot++[TVMInst TVMSwapOp 0;TVMInst TVMSubOp 0;TVMInst TVMPushOp(cm_pointer_scale p lhs);TVMInst TVMDivOp 0]).
 { unfold cm_binary_finish_code;cbn[Z.eqb Pos.eqb andb];rewrite LP,RP;reflexivity. }
 rewrite FIN in CODE|-*;rewrite <-app_assoc in CODE;pose proof(cm_code_at_append_right _ _ _ _ CODE)as C5;rewrite cm_layout_temp_load_length in C5.
 change(cm_code_steps(cm_temp_load_code policy p fid slot++[TVMInst TVMSwapOp 0;TVMInst TVMSubOp 0;TVMInst TVMPushOp(cm_pointer_scale p lhs);TVMInst TVMDivOp 0]))with 9%nat.
 change(tvm_iter 4(tvm_iter 5(TVMRunTask obj(TVMState pc[right]calls mem input output)))=TVMRunTask obj(TVMState(pc+9)[tower_div(tower_sub(tower_getw mem(tower_getw mem 8+cm_temp_offset policy p fid slot))right)(cm_pointer_scale p lhs)]calls mem input output)).
 unfold cm_temp_load_code in CODE;rewrite <-app_assoc in CODE;rewrite(cm_tvm_fp_load_value _ _ _ _ _ _ _ _ _ ADDR CODE).
 rewrite(cm_tvm_ptr_difference _ _ _ _ _ _ _ _ _ _ SIGN NZ C5);f_equal;f_equal;lia.
Qed.
