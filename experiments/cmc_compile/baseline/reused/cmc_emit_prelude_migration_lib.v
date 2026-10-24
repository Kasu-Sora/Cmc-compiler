Require Export SimpleC.EE.QCP_demos_human.cmc_emit_plan_migration_lib.
From Coq Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.

(* The source compiler's specified prelude instruction fragment. *)
Definition cm_emit_prelude (policy : cm_lookup_policy) (p : cm_program) : list tvm_inst :=
  [TVMInst TVMPushOp 1048576; TVMInst TVMPushOp 8; TVMInst TVMStoreOp 0;
   TVMInst TVMCallOp (cm_function_pc policy p (cm_program_main p));
   TVMInst TVMPushOp 256; TVMInst TVMModOp 0; TVMInst TVMPushOp 256;
   TVMInst TVMAddOp 0; TVMInst TVMPushOp 256; TVMInst TVMModOp 0;
   TVMInst TVMHaltOp 0].
