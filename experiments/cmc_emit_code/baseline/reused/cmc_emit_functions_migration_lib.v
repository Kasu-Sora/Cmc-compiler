From Coq Require Import ZArith List.
Require Export SimpleC.EE.QCP_demos_human.cmc_emit_function_migration_lib.
Import ListNotations.
Local Open Scope Z_scope.

(* Exact source cmc_codegen.c:1023-1032: concatenation of function code in list order. *)
Fixpoint cm_emit_functions policy p fid (functions : list cm_function_d) : list tvm_inst :=
  match functions with
  | [] => []
  | _ :: rest => cm_emit_function policy p fid ++ cm_emit_functions policy p (fid + 1) rest
  end.

(* Transparent list observation; no added validity assumption. *)
Definition cm_emit_functions_tail (functions : list cm_function_d) := tl functions.
