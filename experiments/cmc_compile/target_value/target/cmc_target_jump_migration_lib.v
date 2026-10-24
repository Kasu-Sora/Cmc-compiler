Require Export SimpleC.EE.QCP_demos_human.cmc_target_stack_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_code_at_target_valid code pc op imm rest : tvm_targets_valid code -> tvm_opcode_is_target op=true -> cm_code_at code pc (TVMInst op imm::rest) -> tvm_target_validb code imm=true.
Proof.
 intros VALID OP [before [after [CODE PC]]]; apply tvm_target_validb_spec.
 unfold tvm_targets_valid in VALID; rewrite Forall_forall in VALID; apply(VALID (TVMInst op imm));[rewrite CODE; apply in_or_app; right; now left|exact OP].
Qed.
Lemma cm_model_jump_targets policy p : cm_semantic_wf_program policy p -> tvm_targets_valid(cm_model_code policy p).
Proof. intro WF; exact(proj2(proj2(cm_compile_model_wf policy p WF))). Qed.
Lemma cm_tvm_jz obj pc value calls mem input output dest rest :
 tvm_targets_valid(tvm_object_code obj) -> cm_code_at(tvm_object_code obj)pc(TVMInst TVMJzOp dest::rest) ->
 tvm_step(TVMRunTask obj(TVMState pc [value] calls mem input output))=
 TVMRunTask obj(TVMState(if value=?0 then dest else pc+1)[] calls mem input output).
Proof.
 intros VALID CODE; pose proof(cm_code_at_target_valid _ _ TVMJzOp _ _ VALID eq_refl CODE)as DEST.
 rewrite(cm_tvm_code_step obj (TVMState pc [value] calls mem input output) _ _ _ CODE).
 cbn [tvm_inst_step tvm_stack]; change(1<=?Zlength[value])with true.
 cbv beta iota zeta delta [hd tl]; rewrite DEST; destruct(value=?0); reflexivity.
Qed.
Lemma cm_tvm_jmp obj pc stack calls mem input output dest rest :
 tvm_targets_valid(tvm_object_code obj) -> cm_code_at(tvm_object_code obj)pc(TVMInst TVMJmpOp dest::rest) ->
 tvm_step(TVMRunTask obj(TVMState pc stack calls mem input output))=
 TVMRunTask obj(TVMState dest stack calls mem input output).
Proof.
 intros VALID CODE; pose proof(cm_code_at_target_valid _ _ TVMJmpOp _ _ VALID eq_refl CODE)as DEST.
 rewrite(cm_tvm_code_step obj (TVMState pc stack calls mem input output) _ _ _ CODE).
 cbn [tvm_inst_step]; rewrite DEST; reflexivity.
Qed.
