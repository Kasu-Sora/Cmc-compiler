Require Export SimpleC.EE.QCP_demos_human.cmc_emit_prelude_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_emit_functions_migration_lib.
From Coq Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.

(* Source compiler code fragment: the prelude followed by all functions. *)
Definition cm_model_code (policy : cm_lookup_policy) (p : cm_program) : list tvm_inst :=
  cm_emit_prelude policy p ++ cm_emit_functions policy p 0 (cm_program_functions p).
