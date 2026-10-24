Require Export SimpleC.EE.QCP_demos_human.cmc_param_pending_complete_migration_lib.
From Coq Require Import ZArith List Bool Lia.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_tvm_dup_step obj st value stack rest :cm_code_at(tvm_object_code obj)(tvm_pc st)(TVMInst TVMDupOp 0::rest) ->tvm_stack st=value::stack ->Zlength stack+1<65536 ->
 tvm_step(TVMRunTask obj st)=TVMRunTask obj(tvm_next_state st(value::value::stack)(tvm_calls st)(tvm_mem st)(tvm_input st)(tvm_output st)).
Proof.
 intros CODE STACK CAP;eapply cm_tvm_state_step;[exact CODE|];cbn[tvm_inst_step];rewrite STACK.
 assert(A:(1<=?Zlength(value::stack))=true)by(apply Z.leb_le;rewrite Zlength_cons;pose proof(Zlength_nonneg stack);lia).
 assert(B:(Zlength(value::stack)<?65536)=true)by(apply Z.ltb_lt;rewrite Zlength_cons;lia).
 rewrite A,B;reflexivity.
Qed.
Lemma cm_tvm_sub_step obj st left right stack rest :cm_code_at(tvm_object_code obj)(tvm_pc st)(TVMInst TVMSubOp 0::rest) ->tvm_stack st=right::left::stack ->
 tvm_step(TVMRunTask obj st)=TVMRunTask obj(tvm_next_state st(tower_sub left right::stack)(tvm_calls st)(tvm_mem st)(tvm_input st)(tvm_output st)).
Proof.
 intros CODE STACK;eapply cm_tvm_state_step;[exact CODE|];cbn[tvm_inst_step];rewrite STACK.
 assert(A:(2<=?Zlength(right::left::stack))=true)by(apply Z.leb_le;rewrite !Zlength_cons;pose proof(Zlength_nonneg stack);lia).
 rewrite A;reflexivity.
Qed.
