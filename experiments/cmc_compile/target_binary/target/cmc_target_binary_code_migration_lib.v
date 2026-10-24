Require Export SimpleC.EE.QCP_demos_human.cmc_target_binary_scalar_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_binary_finish_numeric policy p fid op lhs rhs temp :
 (op=8 \/ op=9 -> cm_pointerb(cm_expr_type lhs)=false /\ cm_pointerb(cm_expr_type rhs)=false) ->
 cm_binary_finish_code policy p fid op lhs rhs temp=
 cm_temp_load_code policy p fid temp++[TVMInst TVMSwapOp 0;TVMInst(cm_binary_opcode op)0].
Proof.
 intro SCALAR;unfold cm_binary_finish_code;destruct(op=?8)eqn:E8, (op=?9)eqn:E9;cbn[andb];try reflexivity.
 all: first[apply Z.eqb_eq in E8;destruct(SCALAR(or_introl E8))as[L R]|apply Z.eqb_eq in E9;destruct(SCALAR(or_intror E9))as[L R]];rewrite L,R;reflexivity.
Qed.
Lemma cm_tvm_swap_pair obj pc a b calls mem input output rest :
 cm_code_at(tvm_object_code obj)pc(TVMInst TVMSwapOp 0::rest) ->
 tvm_step(TVMRunTask obj(TVMState pc[a;b]calls mem input output))=
 TVMRunTask obj(TVMState(pc+1)[b;a]calls mem input output).
Proof.
 intro CODE;rewrite(cm_tvm_code_step obj(TVMState pc[a;b]calls mem input output)_ _ _ CODE).
 cbn[tvm_inst_step tvm_stack];change(2<=?Zlength[a;b])with true;reflexivity.
Qed.
Lemma cm_tvm_binary_numeric_tail policy p fid op lhs rhs slot obj pc right calls mem input output rest :
 (op=8 \/ op=9 -> cm_pointerb(cm_expr_type lhs)=false /\ cm_pointerb(cm_expr_type rhs)=false) ->
 2<=op<=12 -> (op=11 \/ op=12 ->right<>0) -> tower_word_valid(tower_getw mem 8+cm_temp_offset policy p fid slot) ->
 cm_code_at(tvm_object_code obj)pc(cm_binary_finish_code policy p fid op lhs rhs slot++rest) ->
 tvm_iter(cm_code_steps(cm_binary_finish_code policy p fid op lhs rhs slot))(TVMRunTask obj(TVMState pc[right]calls mem input output))=
 TVMRunTask obj(TVMState(pc+7)[cm_binary_number op(tower_getw mem(tower_getw mem 8+cm_temp_offset policy p fid slot))right]calls mem input output).
Proof.
 intros SCALAR BOUND NZ ADDR CODE;rewrite(cm_binary_finish_numeric _ _ _ _ _ _ _ SCALAR)in CODE|-*.
 rewrite <-app_assoc in CODE;pose proof(cm_code_at_append_right _ _ _ _ CODE)as C5.
 rewrite cm_layout_temp_load_length in C5;pose proof(cm_code_at_tail _ _ _ _ C5)as C6.
 change(cm_code_steps(cm_temp_load_code policy p fid slot++[TVMInst TVMSwapOp 0;TVMInst(cm_binary_opcode op)0]))with 7%nat.
 change(tvm_step(tvm_step(tvm_iter 5(TVMRunTask obj(TVMState pc[right]calls mem input output))))=TVMRunTask obj(TVMState(pc+7)[cm_binary_number op(tower_getw mem(tower_getw mem 8+cm_temp_offset policy p fid slot))right]calls mem input output)).
 unfold cm_temp_load_code in CODE;rewrite <-app_assoc in CODE.
 rewrite(cm_tvm_fp_load_value _ _ _ _ _ _ _ _ _ ADDR CODE), (cm_tvm_swap_pair _ _ _ _ _ _ _ _ _ C5), (cm_tvm_binary_number_total _ _ _ _ _ _ _ _ _ _ NZ BOUND C6).
 f_equal;f_equal;lia.
Qed.
