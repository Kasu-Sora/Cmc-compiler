(* Top-level CMC contract. Shared preservation and readiness proofs are imported,
   not duplicated or assumed by this implementation case. *)
Require Export SimpleC.EE.QCP_demos_human.cmc_preservation_complete_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_compile_ready_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_program_ready_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_patch_calls_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_emit_data_migration_lib.
From Coq Require Import ZArith List String.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic ArrayLib.
Require Import Logic.LogicGenerator.demo932.Interface.
Import ListNotations naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac.
Local Open Scope list_scope.

Definition cm_program_heap_rep (root:Z) p : Assertion :=
 EX functions:Z, cm_program_context_rep root p functions **
 cm_function_list_rep functions (cm_program_functions p).
Definition cm_program_rep policy (root:Z) p : Assertion :=
 “cm_semantic_wf_program policy p” && cm_program_heap_rep root p.
Definition cm_undef_int_buffer (ptr capacity:Z) : Assertion :=
 if Z.eqb capacity 0 then emp else “ptr<>0” && IntArray.undef_full ptr capacity.
Definition cm_int_prefix_buffer (ptr capacity:Z) (values:list Z) : Assertion :=
 let n:=Zlength values in
 if Z.eqb n 0 then cm_undef_int_buffer ptr capacity else
 “ptr<>0” && IntArray.full ptr n values **
 IntArray.undef_full (ptr+n*4) (capacity-n).
Definition cm_undef_int64_buffer (ptr capacity:Z) : Assertion :=
 if Z.eqb capacity 0 then emp else “ptr<>0” && Int64Array.undef_full ptr capacity.
Definition cm_int64_prefix_buffer (ptr capacity:Z) (values:list Z) : Assertion :=
 let n:=Zlength values in
 if Z.eqb n 0 then cm_undef_int64_buffer ptr capacity else
 “ptr<>0” && Int64Array.full ptr n values **
 Int64Array.undef_full (ptr+n*8) (capacity-n).
Definition cm_undef_uint8_buffer (ptr capacity:Z) : Assertion :=
 if Z.eqb capacity 0 then emp else “ptr<>0” && UCharArray.undef_full ptr capacity.
Definition cm_uint8_prefix_buffer (ptr capacity:Z) (values:list Z) : Assertion :=
 let n:=Zlength values in
 if Z.eqb n 0 then cm_undef_uint8_buffer ptr capacity else
 “ptr<>0” && UCharArray.full ptr n values **
 UCharArray.undef_full (ptr+n*1) (capacity-n).
Definition cm_output_pre (out code_capacity data_capacity:Z) : Assertion :=
 EX ops imms bytes old_code old_data old_entry:Z,
 “out<>0 /\ 0<=code_capacity /\ 0<=data_capacity” &&
 &(out # "cm_output" ->ₛ "ops") # Ptr |-> ops **
 &(out # "cm_output" ->ₛ "imms") # Ptr |-> imms **
 &(out # "cm_output" ->ₛ "data") # Ptr |-> bytes **
 &(out # "cm_output" ->ₛ "code_capacity") # Int |-> code_capacity **
 &(out # "cm_output" ->ₛ "data_capacity") # Int |-> data_capacity **
 &(out # "cm_output" ->ₛ "code_length") # Int |-> old_code **
 &(out # "cm_output" ->ₛ "data_length") # Int |-> old_data **
 &(out # "cm_output" ->ₛ "entry") # Int |-> old_entry **
 cm_undef_int_buffer ops code_capacity **
 cm_undef_int64_buffer imms code_capacity **
 cm_undef_uint8_buffer bytes data_capacity.
Definition cm_output_capacity policy (out code_capacity data_capacity:Z) p : Assertion :=
 EX ops imms bytes:Z,
 “out<>0 /\ 0<=code_capacity /\ 0<=data_capacity /\
   (cm_model_code_length policy p>code_capacity \/ cm_model_data_length p>data_capacity)” &&
 &(out # "cm_output" ->ₛ "ops") # Ptr |-> ops **
 &(out # "cm_output" ->ₛ "imms") # Ptr |-> imms **
 &(out # "cm_output" ->ₛ "data") # Ptr |-> bytes **
 &(out # "cm_output" ->ₛ "code_capacity") # Int |-> code_capacity **
 &(out # "cm_output" ->ₛ "data_capacity") # Int |-> data_capacity **
 &(out # "cm_output" ->ₛ "code_length") # Int |-> (cm_model_code_length policy p) **
 &(out # "cm_output" ->ₛ "data_length") # Int |-> (cm_model_data_length p) **
 &(out # "cm_output" ->ₛ "entry") # Int |-> (-1) **
 cm_undef_int_buffer ops code_capacity **
 cm_undef_int64_buffer imms code_capacity **
 cm_undef_uint8_buffer bytes data_capacity.
Definition cm_output_ok sp (out code_capacity data_capacity:Z) p : Assertion :=
 let policy:=cm_source_function_policy sp in
 EX ops imms bytes:Z,
 “out<>0 /\ 0<=cm_model_code_length policy p<=code_capacity /\
   0<=cm_model_data_length p<=data_capacity /\
   (forall obj input trace status,
     cm_source_terminates sp p input trace status ->
     cm_output_decodes 0 (cm_rep_ops(cm_model_code policy p))
       (cm_rep_imms(cm_model_code policy p)) (cm_model_data_bytes p) obj ->
     tvm_terminates obj input trace status)” &&
 &(out # "cm_output" ->ₛ "ops") # Ptr |-> ops **
 &(out # "cm_output" ->ₛ "imms") # Ptr |-> imms **
 &(out # "cm_output" ->ₛ "data") # Ptr |-> bytes **
 &(out # "cm_output" ->ₛ "code_capacity") # Int |-> code_capacity **
 &(out # "cm_output" ->ₛ "data_capacity") # Int |-> data_capacity **
 &(out # "cm_output" ->ₛ "code_length") # Int |-> (cm_model_code_length policy p) **
 &(out # "cm_output" ->ₛ "data_length") # Int |-> (cm_model_data_length p) **
 &(out # "cm_output" ->ₛ "entry") # Int |-> 0 **
 cm_int_prefix_buffer ops code_capacity (cm_rep_ops(cm_model_code policy p)) **
 cm_int64_prefix_buffer imms code_capacity (cm_rep_imms(cm_model_code policy p)) **
 cm_uint8_prefix_buffer bytes data_capacity (cm_model_data_bytes p).

From Coq Require Import Lia.
Lemma cm_compile_functions_length__emitter_transitions policy p functions fid :
  Zlength (cm_emit_functions policy p fid functions) =
  cm_functions_code_size policy p functions fid.
Proof.
  revert fid. induction functions as [|f rest IH]; intro fid.
  - reflexivity.
  - cbn [cm_emit_functions cm_functions_code_size].
    rewrite Zlength_app, cm_layout_function_length, IH. reflexivity.
Qed.
Lemma cm_compile_model_length__emitter_transitions policy p :
  Zlength (cm_model_code policy p) = cm_model_code_length policy p.
Proof.
  unfold cm_model_code, cm_model_code_length.
  rewrite Zlength_app, cm_compile_functions_length__emitter_transitions.
  change (Zlength (cm_emit_prelude policy p)) with 11. reflexivity.
Qed.
Lemma cm_compile_int_prefix__success_result : forall ptr capacity n values,
 ptr<>0 -> 0<=n<=capacity ->
 IntArray.seg ptr 0 n values ** IntArray.undef_seg ptr n capacity |--
 cm_int_prefix_buffer ptr capacity values.
Proof.
 intros ptr capacity n values Hptr Hbounds.
 prop_apply_p (IntArray.seg_Zlength ptr 0 n values).
 Intros_p Hlen.
 assert (Hlength : Zlength values = n) by lia.
 unfold cm_int_prefix_buffer. rewrite Hlength.
 destruct (Z.eqb n 0) eqn:Hn.
 - apply Z.eqb_eq in Hn. rewrite Hn in *.
   sep_apply_l_atomic (IntArray.seg_nil ptr 0 values).
   Intros_p Hnil.
   unfold cm_undef_int_buffer.
   destruct (Z.eqb capacity 0) eqn:Hcap.
   + apply Z.eqb_eq in Hcap. subst capacity.
     rewrite IntArray.undef_seg_empty. cancel.
   + sep_apply_l_atomic (IntArray.undef_seg_to_undef_full ptr 0 capacity).
     cbn [sizeof_front_end_type sizeof_front_end_type_of_ptr_size].
   replace (ptr + 0 * 4) with ptr by lia.
     replace (capacity - 0) with capacity by lia.
     cbn [sizeof_front_end_type sizeof_front_end_type_of_ptr_size].
   split_pure_spatial; [cancel | dump_pre_spatial; exact Hptr].
 - sep_apply_l_atomic (IntArray.seg_to_full ptr 0 n values).
   cbn [sizeof_front_end_type sizeof_front_end_type_of_ptr_size].
   replace (ptr + 0 * 4) with ptr by lia.
   replace (n - 0) with n by lia.
   sep_apply_l_atomic (IntArray.undef_seg_to_undef_full ptr n capacity).
   cbn [sizeof_front_end_type sizeof_front_end_type_of_ptr_size].
   split_pure_spatial; [cancel | dump_pre_spatial; exact Hptr].
Qed.
Lemma cm_compile_int64_prefix__success_result : forall ptr capacity n values,
 ptr<>0 -> 0<=n<=capacity ->
 Int64Array.seg ptr 0 n values ** Int64Array.undef_seg ptr n capacity |--
 cm_int64_prefix_buffer ptr capacity values.
Proof.
 intros ptr capacity n values Hptr Hbounds.
 prop_apply_p (Int64Array.seg_Zlength ptr 0 n values).
 Intros_p Hlen.
 assert (Hlength : Zlength values = n) by lia.
 unfold cm_int64_prefix_buffer. rewrite Hlength.
 destruct (Z.eqb n 0) eqn:Hn.
 - apply Z.eqb_eq in Hn. rewrite Hn in *.
   sep_apply_l_atomic (Int64Array.seg_nil ptr 0 values).
   Intros_p Hnil.
   unfold cm_undef_int64_buffer.
   destruct (Z.eqb capacity 0) eqn:Hcap.
   + apply Z.eqb_eq in Hcap. subst capacity.
     rewrite Int64Array.undef_seg_empty. cancel.
   + sep_apply_l_atomic (Int64Array.undef_seg_to_undef_full ptr 0 capacity).
     cbn [sizeof_front_end_type sizeof_front_end_type_of_ptr_size].
   replace (ptr + 0 * 8) with ptr by lia.
     replace (capacity - 0) with capacity by lia.
     cbn [sizeof_front_end_type sizeof_front_end_type_of_ptr_size].
   split_pure_spatial; [cancel | dump_pre_spatial; exact Hptr].
 - sep_apply_l_atomic (Int64Array.seg_to_full ptr 0 n values).
   cbn [sizeof_front_end_type sizeof_front_end_type_of_ptr_size].
   replace (ptr + 0 * 8) with ptr by lia.
   replace (n - 0) with n by lia.
   sep_apply_l_atomic (Int64Array.undef_seg_to_undef_full ptr n capacity).
   cbn [sizeof_front_end_type sizeof_front_end_type_of_ptr_size].
   split_pure_spatial; [cancel | dump_pre_spatial; exact Hptr].
Qed.
Lemma cm_compile_uint8_prefix__success_result : forall ptr capacity n values,
 ptr<>0 -> 0<=n<=capacity ->
 UCharArray.seg ptr 0 n values ** UCharArray.undef_seg ptr n capacity |--
 cm_uint8_prefix_buffer ptr capacity values.
Proof.
 intros ptr capacity n values Hptr Hbounds.
 prop_apply_p (UCharArray.seg_Zlength ptr 0 n values).
 Intros_p Hlen.
 assert (Hlength : Zlength values = n) by lia.
 unfold cm_uint8_prefix_buffer. rewrite Hlength.
 destruct (Z.eqb n 0) eqn:Hn.
 - apply Z.eqb_eq in Hn. rewrite Hn in *.
   sep_apply_l_atomic (UCharArray.seg_nil ptr 0 values).
   Intros_p Hnil.
   unfold cm_undef_uint8_buffer.
   destruct (Z.eqb capacity 0) eqn:Hcap.
   + apply Z.eqb_eq in Hcap. subst capacity.
     rewrite UCharArray.undef_seg_empty. cancel.
   + sep_apply_l_atomic (UCharArray.undef_seg_to_undef_full ptr 0 capacity).
     cbn [sizeof_front_end_type sizeof_front_end_type_of_ptr_size].
   replace (ptr + 0 * 1) with ptr by lia.
     replace (capacity - 0) with capacity by lia.
     cbn [sizeof_front_end_type sizeof_front_end_type_of_ptr_size].
   split_pure_spatial; [cancel | dump_pre_spatial; exact Hptr].
 - sep_apply_l_atomic (UCharArray.seg_to_full ptr 0 n values).
   cbn [sizeof_front_end_type sizeof_front_end_type_of_ptr_size].
   replace (ptr + 0 * 1) with ptr by lia.
   replace (n - 0) with n by lia.
   sep_apply_l_atomic (UCharArray.undef_seg_to_undef_full ptr n capacity).
   cbn [sizeof_front_end_type sizeof_front_end_type_of_ptr_size].
   split_pure_spatial; [cancel | dump_pre_spatial; exact Hptr].
Qed.
