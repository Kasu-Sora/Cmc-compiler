(* Validation of source exports and retained private support statements. *)
Require Import SimpleC.EE.QCP_demos_human.cmc_code_ready_migration_lib.
From Coq Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.
Goal forall p, cm_concrete_structs_ready p <-> cm_rep_structs_safe (cm_program_structs p).
Proof. reflexivity. Qed.
Check (cm_slots_nonnegative : forall structs slots,
  cm_slots_wf structs slots -> 0 <= cm_rep_members_size slots).
Check (cm_slots_safe : forall structs slots,
  cm_slots_wf structs slots -> cm_rep_members_size slots <= 1048576 -> cm_rep_members_safe slots).
Check (cm_structs_wf_head : forall structs h t,
  (forall i, 0 <= i < Zlength (h :: t) -> cm_struct_wf structs (cm_struct_at i (h :: t))) ->
  cm_struct_wf structs h).
Check (cm_structs_wf_tail : forall structs h t,
  (forall i, 0 <= i < Zlength (h :: t) -> cm_struct_wf structs (cm_struct_at i (h :: t))) ->
  (forall i, 0 <= i < Zlength t -> cm_struct_wf structs (cm_struct_at i t))).
Check (cm_structs_safe : forall structs items,
  (forall i, 0 <= i < Zlength items -> cm_struct_wf structs (cm_struct_at i items)) -> cm_rep_structs_safe items).
Check (cmc_structs_ready_from_typed : forall policy p,
  cm_typed_program policy p -> cm_concrete_structs_ready p).
Print Assumptions cm_slots_nonnegative.
Print Assumptions cm_slots_safe.
Print Assumptions cm_structs_wf_head.
Print Assumptions cm_structs_wf_tail.
Print Assumptions cm_structs_safe.
Print Assumptions cmc_structs_ready_from_typed.
