Require Export SimpleC.EE.QCP_demos_human.cmc_target_expr_dispatch_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_target_control_structural_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_machine_sim_stack policy p st vm frames spills oldvals oldsuffix vals suffix pc :
 cm_machine_state_sim policy p st vm frames spills oldvals oldsuffix ->
 cm_machine_state_sim policy p st
 (TVMState pc (cm_encode_values st vals++suffix) (tvm_calls vm) (tvm_mem vm) (tvm_input vm) (tvm_output vm)) frames spills vals suffix.
Proof.
 intros [MEM [PROV [FP [CALL [SPILLS [INPUT [OUTPUT STACK]]]]]]]; unfold cm_machine_state_sim.
 do 7(split; [assumption|]); reflexivity.
Qed.
Lemma tower_wrap64_bool b : tower_wrap64(tower_bool b)=tower_bool b.
Proof. destruct b; reflexivity. Qed.
Lemma cm_unary_number op v st : cm_value_number st (cm_unary_value op v st)=
 if op=?0 then tower_neg(cm_value_number st v) else tower_bool(cm_value_number st v=?0).
Proof.
 unfold cm_unary_value; destruct(op=?0); cbn [cm_value_number].
 - apply tower_wrap64_idempotent.
 - unfold cm_truth; rewrite negb_involutive; apply tower_wrap64_bool.
Qed.
Lemma cm_tvm_unary obj pc value calls mem input output op rest :
 cm_code_at (tvm_object_code obj) pc ([TVMInst TVMPushOp (if op=?0 then -1 else 0);TVMInst (if op=?0 then TVMMulOp else TVMEqOp) 0]++rest) ->
 tvm_iter 2 (TVMRunTask obj (TVMState pc [value] calls mem input output))=
 TVMRunTask obj (TVMState (pc+2) [if op=?0 then tower_neg value else tower_bool(value=?0)] calls mem input output).
Proof.
 intro CODE; cbn [app]in CODE; pose proof(cm_code_at_tail _ _ _ _ CODE)as C1.
 cbn [tvm_iter]; rewrite(cm_tvm_push_step obj (TVMState pc [value] calls mem input output) _ _ CODE ltac:(change(1<65536);lia)).
 cbv beta iota zeta delta [tvm_next_state tvm_pc tvm_stack tvm_calls tvm_mem tvm_input tvm_output].
 rewrite(cm_tvm_code_step obj (TVMState (pc+1) [tower_wrap64(if op=?0 then -1 else 0);value] calls mem input output) _ _ _ C1).
 destruct(op=?0); cbn [tvm_inst_step tvm_stack]; change(2<=?Zlength [_;_])with true;
 cbv beta iota zeta delta [tvm_action_task tvm_next_state tvm_pc tvm_calls tvm_mem tvm_input tvm_output hd tl].
 - change(tower_wrap64 (-1))with (-1); unfold tower_mul,tower_neg; replace(value * -1)with(-value)by ring; f_equal; f_equal; lia.
 - change(tower_wrap64 0)with 0; f_equal; f_equal; lia.
Qed.
