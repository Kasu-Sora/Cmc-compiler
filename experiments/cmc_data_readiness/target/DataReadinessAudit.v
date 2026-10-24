(* Validation harness only: not a new production definition or helper. *)
Require Import SimpleC.EE.QCP_demos_human.cmc_program_ready_migration_lib.
From Coq Require Import List ZArith.
Import ListNotations.
Local Open Scope Z_scope.
Goal forall structs, cm_data_globals_wf structs [] <-> True.
Proof. reflexivity. Qed.
Goal forall structs g rest,
  cm_data_globals_wf structs (g :: rest) <->
  cm_global_wf structs g /\ cm_data_globals_wf structs rest.
Proof. reflexivity. Qed.
Goal forall p, cm_concrete_data_ready p <->
  cm_rep_globals_safe (cm_program_globals p) /\
  cm_data_globals_wf (cm_program_structs p) (cm_program_globals p) /\
  cm_rep_strings_safe (cm_program_strings p) /\
  0 <= cm_rep_globals_size (cm_program_globals p) /\
  0 <= cm_rep_strings_size (cm_program_strings p) /\
  cm_rep_globals_size (cm_program_globals p) + cm_rep_strings_size (cm_program_strings p) <= 1048560 /\
  cm_model_data_length p = (8 + cm_rep_globals_size (cm_program_globals p)) + cm_rep_strings_size (cm_program_strings p).
Proof. reflexivity. Qed.
Check (cmc_data_ready_from_typed : forall policy p,
  cm_typed_program policy p -> cm_concrete_data_ready p).
Print Assumptions cm_data_globals_from_indexed.
Print Assumptions cm_ready_globals_nonnegative.
Print Assumptions cm_ready_globals_safe.
Print Assumptions cm_ready_strings_nonnegative.
Print Assumptions cm_ready_strings_safe.
Print Assumptions cm_ready_global_bytes_length.
Print Assumptions cm_ready_globals_bytes_length.
Print Assumptions cm_ready_strings_bytes_length.
Print Assumptions cmc_data_ready_from_typed.
