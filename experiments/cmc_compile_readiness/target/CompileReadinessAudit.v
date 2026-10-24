Require Import SimpleC.EE.QCP_demos_human.cmc_compile_ready_migration_lib.
From Coq Require Import ZArith.
Local Open Scope Z_scope.
(* Exact source definition, including functions starting at ID zero. *)
Lemma compile_ready_original_definition : forall policy p,
 cm_concrete_code_ready policy p <->
 cm_concrete_structs_ready p /\ cm_concrete_functions_ready policy p 0 (cm_program_functions p).
Proof. reflexivity. Qed.
Check (cm_concrete_code_ready_from_wf : forall policy cg p,
 cm_wf_program policy cg p -> cm_concrete_code_ready policy p).
Print Assumptions cm_concrete_code_ready_from_wf.
Print Assumptions compile_ready_original_definition.
