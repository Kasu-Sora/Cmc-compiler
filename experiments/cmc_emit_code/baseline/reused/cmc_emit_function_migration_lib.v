(* Exact C* public instruction-sequence equations from cmc_codegen.c:981-1026. *)
From Coq Require Import ZArith List Lia.
From AUXLib Require Import ListLib.
Require Export SimpleC.EE.QCP_demos_human.cmc_emit_stmt_migration_lib.
Import ListNotations.
Local Open Scope Z_scope.
Fixpoint cm_emit_param_stores policy p fid slot params : list tvm_inst :=
 match params with
 | [] => []
 | h::t => cm_emit_param_stores policy p fid (slot+1) t ++
   cm_char_normalize_code (cm_slot_ty h) ++
   cm_fp_relative_address_code (cm_param_offset policy p fid slot) ++
   cm_store_code (cm_slot_ty h)
 end.
Definition cm_emit_prologue policy p fid : list tvm_inst :=
 let f := cm_function_at policy fid (cm_program_functions p) in
 let frame := cm_frame_size (cm_program_structs p) f in
 [TVMInst TVMPushOp 8; TVMInst TVMLoadOp 0; TVMInst TVMDupOp 0;
  TVMInst TVMPushOp frame; TVMInst TVMSubOp 0; TVMInst TVMStoreOp 0;
  TVMInst TVMPushOp 8; TVMInst TVMLoadOp 0; TVMInst TVMPushOp frame;
  TVMInst TVMSubOp 0; TVMInst TVMDupOp 0; TVMInst TVMPushOp 8;
  TVMInst TVMStoreOp 0; TVMInst TVMPopOp 0] ++
 cm_emit_param_stores policy p fid 0 (cm_function_params f).
Definition cm_emit_function policy p fid : list tvm_inst :=
 let f := cm_function_at policy fid (cm_program_functions p) in
 cm_emit_prologue policy p fid ++
 cm_emit_stmt policy p fid (cm_function_pc policy p fid + cm_function_prologue_count f)
   0 0 0 (cm_function_body f) ++ [TVMInst TVMPushOp 0] ++ cm_return_epilogue.
(* Total observations; their only use on a nonempty list is paired with its shape. *)
Definition cm_emit_params_head params := cm_slot_at 0 params.
Definition cm_emit_params_tail (params:list cm_slot_d) := tl params.

Lemma cm_function_slots_size_snoc__param_transition structs prefix h :
 cm_slots_size structs (prefix ++ [h]) = cm_slots_size structs prefix + cm_slot_size structs h.
Proof.
 induction prefix as [|x xs IH]; cbn [app cm_slots_size]; [lia|].
 rewrite IH. lia.
Qed.
Lemma cm_function_slots_prefix_app__param_emission : forall structs prefix rest,
  cm_slots_prefix structs (prefix ++ rest) (Zlength prefix) =
  cm_slots_size structs prefix.
Proof.
  intros structs prefix; induction prefix as [|h t IH]; intros rest.
  - simpl. destruct rest; reflexivity.
  - rewrite Zlength_cons. cbn [app cm_slots_prefix cm_slots_size].
    assert (Hnonneg : 0 <= Zlength t) by apply Zlength_nonneg.
    match goal with |- context [?n =? 0] => destruct (Z.eqb n 0) eqn:Htest end.
    + apply Z.eqb_eq in Htest. lia.
    + rewrite <- (IH rest). f_equal. f_equal. lia.
Qed.
Lemma cm_function_param_count_length__prologue_layout params :
 Zlength params <= cm_param_stores_count params.
Proof.
 induction params as [|h t IH].
 - rewrite Zlength_nil. cbn [cm_param_stores_count]. lia.
 - rewrite Zlength_cons. cbn [cm_param_stores_count].
   unfold cm_char_normalize_count. destruct (cm_slot_ty h); lia.
Qed.
