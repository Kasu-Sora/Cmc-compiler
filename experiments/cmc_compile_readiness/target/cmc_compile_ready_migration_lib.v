(* Pure compile-readiness composition. The existing code-ready definition is
   reused, with its original conjunction and arbitrary lookup/codegen parameters. *)
Require Export SimpleC.EE.QCP_demos_human.cmc_function_ready_migration_lib.

Theorem cm_concrete_code_ready_from_wf policy cg p :
 cm_wf_program policy cg p -> cm_concrete_code_ready policy p.
Proof.
 intro Hwf. split.
 - apply (cmc_structs_ready_from_typed policy p). exact (proj1 Hwf).
 - exact (cm_concrete_functions_ready_from_wf policy cg p Hwf).
Qed.
