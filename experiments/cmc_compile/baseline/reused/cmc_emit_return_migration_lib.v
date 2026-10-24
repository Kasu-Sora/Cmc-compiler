From Coq Require Import ZArith List.
Require Export SimpleC.EE.QCP_demos_human.cmc_emit_plan_migration_lib.
Import ListNotations.
Local Open Scope Z_scope.

(* Exact return sequence from cmc_codegen.c: cm_return_epilogue_def. *)
Definition cm_return_epilogue : list tvm_inst :=
  [TVMInst TVMPushOp 8; TVMInst TVMLoadOp 0;
   TVMInst TVMLoadOp 0; TVMInst TVMPushOp 8;
   TVMInst TVMStoreOp 0; TVMInst TVMRetOp 0].
