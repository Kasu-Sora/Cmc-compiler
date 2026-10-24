Require Export SimpleC.EE.QCP_demos_human.cmc_target_assign_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Definition cm_binary_number op l r :=
 if op=?2 then tower_bool(l=?r) else if op=?3 then tower_bool(negb(l=?r))
 else if op=?4 then tower_bool(l<?r) else if op=?5 then tower_bool(l<=?r)
 else if op=?6 then tower_bool(r<?l) else if op=?7 then tower_bool(r<=?l)
 else if op=?8 then tower_add l r else if op=?9 then tower_sub l r
 else if op=?10 then tower_mul l r else if op=?11 then tower_div l r else tower_mod l r.
Lemma cm_binary_number_wrap op l r : tower_wrap64(cm_binary_number op l r)=cm_binary_number op l r.
Proof.
 unfold cm_binary_number;repeat match goal with |-context[if ?b then _ else _]=>destruct b end;
 first[apply tower_wrap64_bool|apply tower_wrap64_idempotent].
Qed.
Lemma cm_tvm_binary_number_total obj pc l r calls mem input output op rest :
 (op=11 \/ op=12 -> r<>0) -> 2<=op<=12 ->
 cm_code_at(tvm_object_code obj)pc(TVMInst(cm_binary_opcode op)0::rest) ->
 tvm_step(TVMRunTask obj(TVMState pc[r;l]calls mem input output))=
 TVMRunTask obj(TVMState(pc+1)[cm_binary_number op l r]calls mem input output).
Proof.
 intros NONZERO BOUND CODE;assert(OPS:op=2 \/ op=3 \/ op=4 \/ op=5 \/ op=6 \/ op=7 \/ op=8 \/ op=9 \/ op=10 \/ op=11 \/ op=12)by lia.
 destruct OPS as[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]]];
 rewrite(cm_tvm_code_step obj(TVMState pc[r;l]calls mem input output)_ _ _ CODE);
 cbn[cm_binary_opcode cm_binary_number Z.eqb Pos.eqb tvm_inst_step tvm_stack];change(2<=?Zlength[r;l])with true;
 cbv beta iota zeta delta [andb hd tl];try reflexivity;
 assert(NZ:(r=?0)=false)by(apply Z.eqb_neq;apply NONZERO;auto);rewrite NZ;reflexivity.
Qed.
Lemma cm_binary_scalar_number p st op left right ty : 2<=op<=12 ->
 (op=8 \/ op=9 -> cm_is_pointerb(cm_value_type left)=false /\ cm_is_pointerb(cm_value_type right)=false) ->
 cm_value_number st(cm_binary_value p op left right ty st)=cm_binary_number op(cm_value_number st left)(cm_value_number st right).
Proof.
 intros BOUND SCALAR;assert(OPS:op=2 \/ op=3 \/ op=4 \/ op=5 \/ op=6 \/ op=7 \/ op=8 \/ op=9 \/ op=10 \/ op=11 \/ op=12)by lia.
 destruct OPS as[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]]];
 cbn[cm_binary_value cm_binary_number Z.eqb Pos.eqb andb cm_value_number];try apply tower_wrap64_bool;try apply tower_wrap64_idempotent.
 all: destruct(SCALAR ltac:(auto))as[L R];rewrite L,R;cbn[andb cm_value_number];apply tower_wrap64_idempotent.
Qed.
Lemma cm_binary_divisor p st op left right : 2<=op<=12 ->cm_binary_ok p op left right st=true ->
 op=11 \/ op=12 ->cm_value_number st right<>0.
Proof.
 intros B O[-> | ->];cbn[cm_binary_ok Z.eqb Pos.eqb Z.leb Z.compare Pos.compare Pos.compare_cont orb andb]in O;apply negb_true_iff in O;now apply Z.eqb_neq.
Qed.
