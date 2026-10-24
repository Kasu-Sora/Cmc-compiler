(* Logical resolution of raw emitted CALL operands; physical buffers remain raw. *)
From Coq Require Import ZArith List Bool String Lia.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic ArrayLib.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export SimpleC.EE.QCP_demos_human.cmc_emit_core_migration_lib.
Import ListNotations naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac.
Local Open Scope list_scope.

Definition cm_patch_inst (policy : cm_lookup_policy) (p : cm_program)
    (inst : tvm_inst) : tvm_inst :=
  match inst with TVMInst op imm =>
    TVMInst op (if Z.eqb (tvm_opcode_code op) 22
                then cm_function_pc policy p imm else imm)
  end.
Definition cm_patch_code policy p (code : list tvm_inst) : list tvm_inst :=
  map (cm_patch_inst policy p) code.
Definition cm_resolved_emitter_rep policy p (emitter out capacity : Z)
    (resolved_prefix : list tvm_inst) : Assertion :=
  EX raw_prefix : list tvm_inst,
    “cm_patch_code policy p raw_prefix = resolved_prefix” &&
    cm_emitter_rep emitter out capacity
      (cm_rep_ops raw_prefix) (cm_rep_imms raw_prefix).

Lemma cm_patch_code_length policy p code :
  Zlength (cm_patch_code policy p code) = Zlength code.
Proof.
  unfold cm_patch_code. induction code as [|inst rest IH]; [reflexivity|].
  simpl map. rewrite !Zlength_cons, IH. reflexivity.
Qed.
Lemma cm_patch_code_append policy p left right :
  cm_patch_code policy p (left ++ right) =
  cm_patch_code policy p left ++ cm_patch_code policy p right.
Proof. unfold cm_patch_code. apply map_app. Qed.
Lemma cm_patch_noncall policy p op imm :
  tvm_opcode_code op <> 22 ->
  cm_patch_code policy p [TVMInst op imm] = [TVMInst op imm].
Proof.
  intros H. unfold cm_patch_code, cm_patch_inst; simpl.
  apply Z.eqb_neq in H. rewrite H. reflexivity.
Qed.
Lemma cm_patch_call policy p fid :
  cm_patch_code policy p [TVMInst TVMCallOp fid] =
  [TVMInst TVMCallOp (cm_function_pc policy p fid)].
Proof. reflexivity. Qed.
Lemma cm_patch_char_normalize policy p ty :
  cm_patch_code policy p (cm_char_normalize_code ty) = cm_char_normalize_code ty.
Proof. destruct ty; reflexivity. Qed.
Lemma cm_patch_load policy p ty :
  cm_patch_code policy p (cm_load_code ty) = cm_load_code ty.
Proof. destruct ty; reflexivity. Qed.
Lemma cm_patch_store policy p ty :
  cm_patch_code policy p (cm_store_code ty) = cm_store_code ty.
Proof. destruct ty; reflexivity. Qed.
Lemma cm_patch_fp_address policy p offset :
  cm_patch_code policy p (cm_fp_relative_address_code offset) =
  cm_fp_relative_address_code offset.
Proof. reflexivity. Qed.
Lemma cm_patch_temp_store policy p fid temp :
  cm_patch_code policy p (cm_temp_store_code policy p fid temp) =
  cm_temp_store_code policy p fid temp.
Proof. reflexivity. Qed.
Lemma cm_patch_temp_load policy p fid temp :
  cm_patch_code policy p (cm_temp_load_code policy p fid temp) =
  cm_temp_load_code policy p fid temp.
Proof. reflexivity. Qed.
