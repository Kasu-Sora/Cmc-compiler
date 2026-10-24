(* Physical patching reuses the established total CALL-resolution model. *)
From Coq Require Import ZArith List.
From SimpleC.SL Require Import Mem SeparationLogic ArrayLib.
Require Import Logic.LogicGenerator.demo932.Interface.
Import naive_C_Rules.
Require Export SimpleC.EE.QCP_demos_human.cmc_emit_resolved_migration_lib.
Import ListNotations.
Local Open Scope Z_scope.
Definition cm_patch_tail (raw : list tvm_inst) : list tvm_inst := tl raw.
Local Open Scope sac.
Definition cm_patch_arrays_rep (ops imms length : Z) (raw : list tvm_inst) : Assertion :=
  IntArray.full ops length (cm_rep_ops raw) **
  Int64Array.full imms length (cm_rep_imms raw).

From Coq Require Import Lia.
Lemma cm_patch_arrays_open__array_open : forall ops imms opcode immediate rest,
  cm_patch_arrays_rep ops imms (1 + Zlength rest) (TVMInst opcode immediate :: rest) |--
  (ops # Int |-> tvm_opcode_code opcode) **
  (imms # Int64 |-> immediate) **
  cm_patch_arrays_rep (ops + sizeof(INT)) (imms + sizeof(INT64)) (Zlength rest) rest.
Proof.
  intros. unfold cm_patch_arrays_rep, cm_rep_ops, cm_rep_imms.
  simpl map. simpl tvm_inst_op. simpl tvm_inst_imm.
  rewrite IntArray.full_unfold, Int64Array.full_unfold.
  sep_apply_l_atomic (IntArray.seg_to_full ops 1 (1 + Zlength rest)
    (map (fun i => tvm_opcode_code (tvm_inst_op i)) rest)).
  sep_apply_l_atomic (Int64Array.seg_to_full imms 1 (1 + Zlength rest)
    (map tvm_inst_imm rest)).
  unfold StoreIntAsElement.storeA, StoreInt64AsElement.storeA,
    StoreIntAsElement.sizeA, StoreInt64AsElement.sizeA.
  replace (1 + Zlength rest - 1) with (Zlength rest) by lia.
  replace (ops + 0 * sizeof(INT)) with ops by lia.
  replace (imms + 0 * sizeof(INT64)) with imms by lia.
  replace (ops + 1 * sizeof(INT)) with (ops + sizeof(INT)) by lia.
  replace (imms + 1 * sizeof(INT64)) with (imms + sizeof(INT64)) by lia.
  cancel.
Qed.
Lemma cm_patch_arrays_cons__array_close (ops imms : Z) (opcode : tvm_opcode)
    (immediate : Z) (rest : list tvm_inst) :
  (ops # Int |-> tvm_opcode_code opcode) **
  (imms # Int64 |-> immediate) **
  cm_patch_arrays_rep (ops + sizeof(INT)) (imms + sizeof(INT64))
    (Zlength rest) rest |--
  cm_patch_arrays_rep ops imms (1 + Zlength rest)
    (TVMInst opcode immediate :: rest).
Proof.
  unfold cm_patch_arrays_rep, cm_rep_ops, cm_rep_imms.
  simpl map; simpl tvm_inst_op; simpl tvm_inst_imm.
  rewrite IntArray.full_unfold, Int64Array.full_unfold.
  rewrite (IntArray.seg_0_shift ops 1 (1 + Zlength rest)).
  rewrite (Int64Array.seg_0_shift imms 1 (1 + Zlength rest)).
  unfold StoreIntAsElement.storeA, StoreInt64AsElement.storeA,
    StoreIntAsElement.sizeA, StoreInt64AsElement.sizeA.
  replace (1 + Zlength rest - 1) with (Zlength rest) by lia.
  replace (ops + 0 * sizeof(INT)) with ops by lia.
  replace (imms + 0 * sizeof(INT64)) with imms by lia.
  replace (ops + 1 * sizeof(INT)) with (ops + sizeof(INT)) by lia.
  replace (imms + 1 * sizeof(INT64)) with (imms + sizeof(INT64)) by lia.
  change (IntArray.seg _ 0 _ _) with
    (IntArray.full (ops + sizeof(INT)) (Zlength rest) (map (fun i => tvm_opcode_code (tvm_inst_op i)) rest)).
  change (Int64Array.seg _ 0 _ _) with
    (Int64Array.full (imms + sizeof(INT64)) (Zlength rest) (map tvm_inst_imm rest)).
  cancel (ops # Int |-> tvm_opcode_code opcode).
  cancel (imms # Int64 |-> immediate).
  cancel (IntArray.full (ops + sizeof(INT)) (Zlength rest) (map (fun i => tvm_opcode_code (tvm_inst_op i)) rest)).
  cancel (Int64Array.full (imms + sizeof(INT64)) (Zlength rest) (map tvm_inst_imm rest)).
Qed.
