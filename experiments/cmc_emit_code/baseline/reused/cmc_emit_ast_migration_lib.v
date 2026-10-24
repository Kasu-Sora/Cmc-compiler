(* Binding-address fragments and layout bridges from cmc_lang.c and cmc_codegen.c.
   Both prefixes recurse over lists at arbitrary Z indices, including negatives.
   The existing total lookup policy and complete codegen-obligation record are
   inherited unchanged; source HOL choices and emitter predicates instantiate
   those records. This is implementation verification, not compiler preservation. *)
From Coq Require Import ZArith List Lia.
From AUXLib Require Import ListLib.
Require Export SimpleC.EE.QCP_demos_human.cmc_emit_plan_migration_lib.
Import ListNotations.
Local Open Scope Z_scope.

Fixpoint cm_slots_prefix (structs:list cm_struct_d) (slots:list cm_slot_d)
    (index:Z) : Z :=
  match slots with
  | [] => 0
  | s::rest => if Z.eqb index 0 then 0
               else cm_slot_size structs s + cm_slots_prefix structs rest (index-1)
  end.
Fixpoint cm_globals_prefix (structs:list cm_struct_d) (globals:list cm_global_d)
    (index:Z) : Z :=
  match globals with
  | [] => 0
  | g::rest => if Z.eqb index 0 then 0
               else cm_global_size structs g + cm_globals_prefix structs rest (index-1)
  end.
Definition cm_global_address p index :=
  16 + cm_globals_prefix (cm_program_structs p) (cm_program_globals p) index.
Definition cm_param_offset policy p fid slot :=
  8 + cm_slots_prefix (cm_program_structs p)
    (cm_function_params (cm_function_at policy fid (cm_program_functions p))) slot.
Definition cm_local_offset policy p fid slot :=
  8 + cm_slots_size (cm_program_structs p)
    (cm_function_params (cm_function_at policy fid (cm_program_functions p))) +
  cm_slots_prefix (cm_program_structs p)
    (cm_function_locals (cm_function_at policy fid (cm_program_functions p))) slot.
Definition cm_push_code (value:Z) := [TVMInst TVMPushOp value].
Definition cm_binding_address_code policy p fid scope slot :=
  if Z.eqb scope 0 then cm_push_code (cm_global_address p slot)
  else cm_fp_relative_address_code
    (if Z.eqb scope 1 then cm_local_offset policy p fid slot
     else cm_param_offset policy p fid slot).

(* New shared source closure: these two prefix matches reuse existing size
   bridges rather than reproving their implementation dependencies. *)
Lemma cm_rep_member_prefix_matches structs slots index :
  cm_slots_wf structs slots ->
  cm_rep_member_prefix slots index = cm_slots_prefix structs slots index.
Proof.
  revert index; induction slots as [|h t IH]; intros index Hwf; [reflexivity|].
  assert (Hhead : cm_slot_wf structs h).
  { apply (Hwf 0). rewrite Zlength_cons. pose proof (Zlength_nonneg t). lia. }
  assert (Htail : cm_slots_wf structs t).
  { intros i Hi. specialize (Hwf (i+1)).
    assert (Hb : 0 <= i+1 < Zlength (h::t)) by (rewrite Zlength_cons; lia).
    specialize (Hwf Hb). unfold cm_slot_at in *.
    replace (i+1) with (Z.succ i) in Hwf by lia.
    rewrite Z2Nat.inj_succ in Hwf by lia. simpl nth in Hwf. exact Hwf. }
  cbn [cm_rep_member_prefix cm_slots_prefix]. destruct (Z.eqb index 0); [reflexivity|].
  rewrite (cm_slot_size_matches__temp_context structs h Hhead), (IH _ Htail).
  reflexivity.
Qed.
Lemma cm_rep_globals_prefix_matches structs globals index :
  (forall i, 0 <= i < Zlength globals -> cm_global_wf structs (cm_global_at i globals)) ->
  cm_rep_globals_prefix globals index = cm_globals_prefix structs globals index.
Proof.
  revert index; induction globals as [|h t IH]; intros index Hwf; [reflexivity|].
  assert (Hhead : cm_global_wf structs h).
  { apply (Hwf 0). rewrite Zlength_cons. pose proof (Zlength_nonneg t). lia. }
  assert (Htail : forall i, 0 <= i < Zlength t -> cm_global_wf structs (cm_global_at i t)).
  { intros i Hi. specialize (Hwf (i+1)).
    assert (Hb : 0 <= i+1 < Zlength (h::t)) by (rewrite Zlength_cons; lia).
    specialize (Hwf Hb). unfold cm_global_at in *.
    replace (i+1) with (Z.succ i) in Hwf by lia.
    rewrite Z2Nat.inj_succ in Hwf by lia. simpl nth in Hwf. exact Hwf. }
  cbn [cm_rep_globals_prefix cm_globals_prefix]. destruct (Z.eqb index 0); [reflexivity|].
  rewrite (cm_rep_global_size_matches structs h Hhead), (IH _ Htail).
  reflexivity.
Qed.
