(* Exact source instruction and emitter models; fragments describe the source
   compiler contract, not a mirror of the concrete emitter implementation. *)
From Coq Require Import ZArith List Bool String Lia.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic ArrayLib.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export SimpleC.EE.QCP_demos_human.cmc_function_pc_total_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_emit_globals_migration_lib.
Import ListNotations naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac.
Local Open Scope list_scope.

Inductive tvm_opcode := TVMPushOp | TVMPopOp | TVMDupOp | TVMSwapOp | TVMLoadOp | TVMStoreOp | TVMLoadBOp | TVMStoreBOp | TVMAddOp | TVMSubOp | TVMMulOp | TVMDivOp | TVMModOp | TVMEqOp | TVMNeOp | TVMLtOp | TVMLeOp | TVMGtOp | TVMGeOp | TVMJmpOp | TVMJzOp | TVMJnzOp | TVMCallOp | TVMRetOp | TVMGetcOp | TVMPutcOp | TVMPutiOp | TVMHaltOp.
Definition tvm_opcode_code (op:tvm_opcode) : Z := match op with
 | TVMPushOp => 0
 | TVMPopOp => 1
 | TVMDupOp => 2
 | TVMSwapOp => 3
 | TVMLoadOp => 4
 | TVMStoreOp => 5
 | TVMLoadBOp => 6
 | TVMStoreBOp => 7
 | TVMAddOp => 8
 | TVMSubOp => 9
 | TVMMulOp => 10
 | TVMDivOp => 11
 | TVMModOp => 12
 | TVMEqOp => 13
 | TVMNeOp => 14
 | TVMLtOp => 15
 | TVMLeOp => 16
 | TVMGtOp => 17
 | TVMGeOp => 18
 | TVMJmpOp => 19
 | TVMJzOp => 20
 | TVMJnzOp => 21
 | TVMCallOp => 22
 | TVMRetOp => 23
 | TVMGetcOp => 24
 | TVMPutcOp => 25
 | TVMPutiOp => 26
 | TVMHaltOp => 27
 end.
Inductive tvm_inst := TVMInst (opcode:tvm_opcode) (immediate:Z).
Definition tvm_inst_op i := match i with TVMInst op _ => op end.
Definition tvm_inst_imm i := match i with TVMInst _ imm => imm end.
Definition cm_rep_ops (code:list tvm_inst) := map (fun i => tvm_opcode_code (tvm_inst_op i)) code.
Definition cm_rep_imms (code:list tvm_inst) := map tvm_inst_imm code.
Definition cm_emitter_rep (emitter out capacity:Z) (ops_prefix imms_prefix:list Z) : Assertion :=
 EX ops imms:Z,
 “out<>0 /\ ops<>0 /\ imms<>0 /\
   Zlength ops_prefix = Zlength imms_prefix /\
   0 <= Zlength ops_prefix <= capacity” &&
 &(emitter # "cm_emitter" ->ₛ "output") # Ptr |-> out **
 &(emitter # "cm_emitter" ->ₛ "pc") # Int |-> Zlength ops_prefix **
 &(out # "cm_output" ->ₛ "ops") # Ptr |-> ops **
 &(out # "cm_output" ->ₛ "imms") # Ptr |-> imms **
 &(out # "cm_output" ->ₛ "code_capacity") # Int |-> capacity **
 IntArray.seg ops 0 (Zlength ops_prefix) ops_prefix **
 IntArray.undef_seg ops (Zlength ops_prefix) capacity **
 Int64Array.seg imms 0 (Zlength ops_prefix) imms_prefix **
 Int64Array.undef_seg imms (Zlength ops_prefix) capacity.
Definition cm_emitter_plan_rep (emitter out capacity:Z) (done todo:list tvm_inst) : Assertion :=
 “Zlength done + Zlength todo <= capacity” &&
 cm_emitter_rep emitter out capacity (cm_rep_ops done) (cm_rep_imms done).
Definition cm_char_normalize_code (ty:cm_type) : list tvm_inst :=
 match ty with CMCharTy =>
 [TVMInst TVMPushOp 256; TVMInst TVMModOp 0;
  TVMInst TVMPushOp 256; TVMInst TVMAddOp 0;
  TVMInst TVMPushOp 256; TVMInst TVMModOp 0]
 | _ => [] end.
Definition cm_load_code (ty:cm_type) : list tvm_inst :=
 [TVMInst (match ty with CMCharTy => TVMLoadBOp | _ => TVMLoadOp end) 0].
Definition cm_store_code (ty:cm_type) : list tvm_inst :=
 [TVMInst (match ty with CMCharTy => TVMStoreBOp | _ => TVMStoreOp end) 0].
Definition cm_fp_relative_address_code (offset:Z) : list tvm_inst :=
 [TVMInst TVMPushOp 8; TVMInst TVMLoadOp 0; TVMInst TVMPushOp offset; TVMInst TVMAddOp 0].
Definition cm_temp_store_code policy p fid temp :=
 cm_fp_relative_address_code (cm_temp_offset policy p fid temp) ++ [TVMInst TVMStoreOp 0].
Definition cm_temp_load_code policy p fid temp :=
 cm_fp_relative_address_code (cm_temp_offset policy p fid temp) ++ [TVMInst TVMLoadOp 0].
Definition cm_binary_opcode (op:Z) : tvm_opcode :=
 if Z.eqb op 2 then TVMEqOp else if Z.eqb op 3 then TVMNeOp else
 if Z.eqb op 4 then TVMLtOp else if Z.eqb op 5 then TVMLeOp else
 if Z.eqb op 6 then TVMGtOp else if Z.eqb op 7 then TVMGeOp else
 if Z.eqb op 8 then TVMAddOp else if Z.eqb op 9 then TVMSubOp else
 if Z.eqb op 10 then TVMMulOp else if Z.eqb op 11 then TVMDivOp else TVMModOp.

Lemma cm_slot_size_matches__temp_context structs s :
 cm_slot_wf structs s -> cm_rep_member_size s = cm_slot_size structs s.
Proof.
 intros [_ [Hscalar _]].
 unfold cm_rep_member_size, cm_rep_code_slot_size, cm_slot_size.
 rewrite (cm_scalar_rep_leaf_size structs (cm_slot_ty s) Hscalar).
 reflexivity.
Qed.
Lemma cm_slots_size_matches__temp_context structs slots :
 cm_slots_wf structs slots -> cm_rep_members_size slots = cm_slots_size structs slots.
Proof.
 induction slots as [|h t IH]; intros Hwf; [reflexivity|].
 assert (Hhead : cm_slot_wf structs h).
 { apply (Hwf 0). rewrite Zlength_cons. pose proof (Zlength_nonneg t). lia. }
 assert (Htail : cm_slots_wf structs t).
 { intros i Hi. specialize (Hwf (i+1)).
   assert (Hb : 0 <= i+1 < Zlength (h::t)) by (rewrite Zlength_cons; lia).
   specialize (Hwf Hb). unfold cm_slot_at in *.
   replace (i+1) with (Z.succ i) in Hwf by lia.
   rewrite Z2Nat.inj_succ in Hwf by lia. simpl nth in Hwf. exact Hwf. }
 cbn [cm_rep_members_size cm_slots_size].
 rewrite (cm_slot_size_matches__temp_context structs h Hhead), (IH Htail).
 reflexivity.
Qed.
Lemma cm_temp_offset_matches__temp_context policy p fid temp f :
 f = cm_function_at policy fid (cm_program_functions p) ->
 cm_slots_wf (cm_program_structs p) (cm_function_params f) ->
 cm_slots_wf (cm_program_structs p) (cm_function_locals f) ->
 8 + cm_rep_members_size (cm_function_params f) +
 cm_rep_members_size (cm_function_locals f) + 8*temp = cm_temp_offset policy p fid temp.
Proof.
 intros Hf Hp Hl. unfold cm_temp_offset. rewrite <- Hf.
 rewrite (cm_slots_size_matches__temp_context _ _ Hp),
   (cm_slots_size_matches__temp_context _ _ Hl). reflexivity.
Qed.
Lemma cm_type_encode_char_iff__typed_branches (ty : cm_type) :
  cm_type_code_wf ty -> (cm_type_encode ty = 1 <-> ty = CMCharTy).
Proof.
  intros Hwf. split.
  - intros Hcode. destruct ty as [| |sid|u]; try reflexivity.
    + cbv [cm_type_encode cm_type_depth cm_type_base_code] in Hcode. lia.
    + cbn [cm_type_code_wf] in Hwf.
      cbv [cm_type_encode cm_type_depth cm_type_base_code] in Hcode. lia.
    + pose proof (cm_type_depth_nonnegative__expression_assignment_safety u) as Hd.
      pose proof (cm_type_base_bounds__expression_assignment_safety u Hwf) as Hb.
      unfold cm_type_encode in Hcode.
      cbn [cm_type_depth cm_type_base_code] in Hcode. lia.
  - intros Hchar. subst ty. reflexivity.
Qed.
