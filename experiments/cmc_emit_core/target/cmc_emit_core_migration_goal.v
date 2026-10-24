Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.cmc_emit_core_migration_lib.
Local Open Scope sac.

(*----- Function cm_emit_raw -----*)

Definition cm_emit_raw_safety_wit_1 := 
forall (immediate_pre: Z) (op_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (imms_prefix: (@list Z)) (ops_prefix: (@list Z)) (ops: Z) (imms: Z) (PreH1 : (out <> 0)) (PreH2 : (ops <> 0)) (PreH3 : (imms <> 0)) (PreH4 : ((Zlength (ops_prefix)) = (Zlength (imms_prefix)))) (PreH5 : (0 <= (Zlength (ops_prefix)))) (PreH6 : ((Zlength (ops_prefix)) < capacity)) (PreH7 : (capacity <= INT_MAX)) ,
  (Int64Array.seg imms 0 ((Zlength (ops_prefix)) + 1 ) (app (imms_prefix) ((cons (immediate_pre) ((@nil Z))))) )
  **  (Int64Array.undef_seg imms ((Zlength (ops_prefix)) + 1 ) capacity )
  **  (IntArray.seg ops 0 ((Zlength (ops_prefix)) + 1 ) (app (ops_prefix) ((cons (op_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg ops ((Zlength (ops_prefix)) + 1 ) capacity )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "immediate" ) )) # Int64  |-> immediate_pre)
  **  ((&((emitter_pre)  # "cm_emitter" ->ₛ "output")) # Ptr  |-> out)
  **  ((&((emitter_pre)  # "cm_emitter" ->ₛ "pc")) # Int  |-> (Zlength (ops_prefix)))
  **  ((&((out)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops)
  **  ((&((out)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms)
  **  ((&((out)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> capacity)
|--
  “ (((Zlength (ops_prefix)) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Zlength (ops_prefix)) + 1 )) ”
.

Definition cm_emit_raw_safety_wit_2 := 
forall (immediate_pre: Z) (op_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (imms_prefix: (@list Z)) (ops_prefix: (@list Z)) (ops: Z) (imms: Z) (PreH1 : (out <> 0)) (PreH2 : (ops <> 0)) (PreH3 : (imms <> 0)) (PreH4 : ((Zlength (ops_prefix)) = (Zlength (imms_prefix)))) (PreH5 : (0 <= (Zlength (ops_prefix)))) (PreH6 : ((Zlength (ops_prefix)) < capacity)) (PreH7 : (capacity <= INT_MAX)) ,
  (Int64Array.seg imms 0 ((Zlength (ops_prefix)) + 1 ) (app (imms_prefix) ((cons (immediate_pre) ((@nil Z))))) )
  **  (Int64Array.undef_seg imms ((Zlength (ops_prefix)) + 1 ) capacity )
  **  (IntArray.seg ops 0 ((Zlength (ops_prefix)) + 1 ) (app (ops_prefix) ((cons (op_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg ops ((Zlength (ops_prefix)) + 1 ) capacity )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "immediate" ) )) # Int64  |-> immediate_pre)
  **  ((&((emitter_pre)  # "cm_emitter" ->ₛ "output")) # Ptr  |-> out)
  **  ((&((emitter_pre)  # "cm_emitter" ->ₛ "pc")) # Int  |-> (Zlength (ops_prefix)))
  **  ((&((out)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops)
  **  ((&((out)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms)
  **  ((&((out)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> capacity)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cm_emit_raw_entail_wit_1 := 
(
forall (emitter_pre: Z) (capacity: Z) (out: Z) (imms_prefix: (@list Z)) (ops_prefix: (@list Z)) (PreH1 : ((Zlength (ops_prefix)) < capacity)) ,
  (cm_emitter_rep emitter_pre out capacity ops_prefix imms_prefix )
|--
  EX (imms: Z)  (ops: Z) ,
  “ (out <> 0) ” 
  &&  “ (ops <> 0) ” 
  &&  “ (imms <> 0) ” 
  &&  “ ((Zlength (ops_prefix)) = (Zlength (imms_prefix))) ” 
  &&  “ (0 <= (Zlength (ops_prefix))) ” 
  &&  “ ((Zlength (ops_prefix)) < capacity) ” 
  &&  “ (capacity <= INT_MAX) ”
  &&  ((&((emitter_pre)  # "cm_emitter" ->ₛ "output")) # Ptr  |-> out)
  **  ((&((emitter_pre)  # "cm_emitter" ->ₛ "pc")) # Int  |-> (Zlength (ops_prefix)))
  **  ((&((out)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops)
  **  ((&((out)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms)
  **  ((&((out)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> capacity)
  **  (IntArray.seg ops 0 (Zlength (ops_prefix)) ops_prefix )
  **  (IntArray.undef_seg ops (Zlength (ops_prefix)) capacity )
  **  (Int64Array.seg imms 0 (Zlength (ops_prefix)) imms_prefix )
  **  (Int64Array.undef_seg imms (Zlength (ops_prefix)) capacity )
) \/
(
forall (emitter_pre: Z) (capacity: Z) (out: Z) (imms_prefix: (@list Z)) (ops_prefix: (@list Z)) (PreH1 : ((Zlength (ops_prefix)) < capacity)) ,
  (cm_emitter_rep emitter_pre out capacity ops_prefix imms_prefix )
|--
  EX (imms: Z)  (ops: Z) ,
  “ (out <> 0) ” 
  &&  “ (ops <> 0) ” 
  &&  “ (imms <> 0) ” 
  &&  “ ((Zlength (ops_prefix)) = (Zlength (imms_prefix))) ” 
  &&  “ (0 <= (Zlength (ops_prefix))) ” 
  &&  “ ((Zlength (ops_prefix)) < capacity) ” 
  &&  “ (capacity <= INT_MAX) ”
  &&  ((&((emitter_pre)  # "cm_emitter" ->ₛ "output")) # Ptr  |-> out)
  **  ((&((emitter_pre)  # "cm_emitter" ->ₛ "pc")) # Int  |-> (Zlength (ops_prefix)))
  **  ((&((out)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops)
  **  ((&((out)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms)
  **  ((&((out)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> capacity)
  **  (IntArray.seg ops 0 (Zlength (ops_prefix)) ops_prefix )
  **  (IntArray.undef_seg ops (Zlength (ops_prefix)) capacity )
  **  (Int64Array.seg imms 0 (Zlength (ops_prefix)) imms_prefix )
  **  (Int64Array.undef_seg imms (Zlength (ops_prefix)) capacity )
).

Definition cm_emit_raw_return_wit_1 := 
(
forall (immediate_pre: Z) (op_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (imms_prefix: (@list Z)) (ops_prefix: (@list Z)) (ops: Z) (imms: Z) (PreH1 : (out <> 0)) (PreH2 : (ops <> 0)) (PreH3 : (imms <> 0)) (PreH4 : ((Zlength (ops_prefix)) = (Zlength (imms_prefix)))) (PreH5 : (0 <= (Zlength (ops_prefix)))) (PreH6 : ((Zlength (ops_prefix)) < capacity)) (PreH7 : (capacity <= INT_MAX)) ,
  (Int64Array.seg imms 0 ((Zlength (ops_prefix)) + 1 ) (app (imms_prefix) ((cons (immediate_pre) ((@nil Z))))) )
  **  (Int64Array.undef_seg imms ((Zlength (ops_prefix)) + 1 ) capacity )
  **  (IntArray.seg ops 0 ((Zlength (ops_prefix)) + 1 ) (app (ops_prefix) ((cons (op_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg ops ((Zlength (ops_prefix)) + 1 ) capacity )
  **  ((&((emitter_pre)  # "cm_emitter" ->ₛ "output")) # Ptr  |-> out)
  **  ((&((emitter_pre)  # "cm_emitter" ->ₛ "pc")) # Int  |-> ((Zlength (ops_prefix)) + 1 ))
  **  ((&((out)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops)
  **  ((&((out)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms)
  **  ((&((out)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> capacity)
|--
  (cm_emitter_rep emitter_pre out capacity (app (ops_prefix) ((cons (op_pre) ((@nil Z))))) (app (imms_prefix) ((cons (immediate_pre) ((@nil Z))))) )
) \/
(
forall (immediate_pre: Z) (op_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (imms_prefix: (@list Z)) (ops_prefix: (@list Z)) (ops: Z) (imms: Z) (PreH1 : (capacity <= INT_MAX)) (PreH2 : (((Zlength (ops_prefix)) + 1 ) <= INT_MAX)) (PreH3 : (capacity >= INT_MIN)) (PreH4 : (((Zlength (ops_prefix)) + 1 ) >= INT_MIN)) (PreH5 : (out <> 0)) (PreH6 : (ops <> 0)) (PreH7 : (imms <> 0)) (PreH8 : ((Zlength (ops_prefix)) = (Zlength (imms_prefix)))) (PreH9 : (0 <= (Zlength (ops_prefix)))) (PreH10 : ((Zlength (ops_prefix)) < capacity)) (PreH11 : (capacity <= INT_MAX)) ,
  (Int64Array.seg imms 0 ((Zlength (ops_prefix)) + 1 ) (app (imms_prefix) ((cons (immediate_pre) ((@nil Z))))) )
  **  (Int64Array.undef_seg imms ((Zlength (ops_prefix)) + 1 ) capacity )
  **  (IntArray.seg ops 0 ((Zlength (ops_prefix)) + 1 ) (app (ops_prefix) ((cons (op_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg ops ((Zlength (ops_prefix)) + 1 ) capacity )
  **  ((&((emitter_pre)  # "cm_emitter" ->ₛ "output")) # Ptr  |-> out)
  **  ((&((emitter_pre)  # "cm_emitter" ->ₛ "pc")) # Int  |-> ((Zlength (ops_prefix)) + 1 ))
  **  ((&((out)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops)
  **  ((&((out)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms)
  **  ((&((out)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> capacity)
|--
  (cm_emitter_rep emitter_pre out capacity (app (ops_prefix) ((cons (op_pre) ((@nil Z))))) (app (imms_prefix) ((cons (immediate_pre) ((@nil Z))))) )
).

Definition cm_emit_raw_return_wit_1_split_goal_spatial := 
forall (immediate_pre: Z) (op_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (imms_prefix: (@list Z)) (ops_prefix: (@list Z)) (ops: Z) (imms: Z) (PreH1 : (capacity <= INT_MAX)) (PreH2 : (((Zlength (ops_prefix)) + 1 ) <= INT_MAX)) (PreH3 : (capacity >= INT_MIN)) (PreH4 : (((Zlength (ops_prefix)) + 1 ) >= INT_MIN)) (PreH5 : (out <> 0)) (PreH6 : (ops <> 0)) (PreH7 : (imms <> 0)) (PreH8 : ((Zlength (ops_prefix)) = (Zlength (imms_prefix)))) (PreH9 : (0 <= (Zlength (ops_prefix)))) (PreH10 : ((Zlength (ops_prefix)) < capacity)) (PreH11 : (capacity <= INT_MAX)) ,
  (Int64Array.seg imms 0 ((Zlength (ops_prefix)) + 1 ) (app (imms_prefix) ((cons (immediate_pre) ((@nil Z))))) )
  **  (Int64Array.undef_seg imms ((Zlength (ops_prefix)) + 1 ) capacity )
  **  (IntArray.seg ops 0 ((Zlength (ops_prefix)) + 1 ) (app (ops_prefix) ((cons (op_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg ops ((Zlength (ops_prefix)) + 1 ) capacity )
  **  ((&((emitter_pre)  # "cm_emitter" ->ₛ "output")) # Ptr  |-> out)
  **  ((&((emitter_pre)  # "cm_emitter" ->ₛ "pc")) # Int  |-> ((Zlength (ops_prefix)) + 1 ))
  **  ((&((out)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops)
  **  ((&((out)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms)
  **  ((&((out)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> capacity)
|--
  (cm_emitter_rep emitter_pre out capacity (app (ops_prefix) ((cons (op_pre) ((@nil Z))))) (app (imms_prefix) ((cons (immediate_pre) ((@nil Z))))) )
.

Definition cm_emit_raw_partial_solve_wit_1 := 
forall (emitter_pre: Z) (capacity: Z) (out: Z) (imms_prefix: (@list Z)) (ops_prefix: (@list Z)) (ops: Z) (imms: Z) (PreH1 : (out <> 0)) (PreH2 : (ops <> 0)) (PreH3 : (imms <> 0)) (PreH4 : ((Zlength (ops_prefix)) = (Zlength (imms_prefix)))) (PreH5 : (0 <= (Zlength (ops_prefix)))) (PreH6 : ((Zlength (ops_prefix)) < capacity)) (PreH7 : (capacity <= INT_MAX)) ,
  ((&((emitter_pre)  # "cm_emitter" ->ₛ "output")) # Ptr  |-> out)
  **  ((&((emitter_pre)  # "cm_emitter" ->ₛ "pc")) # Int  |-> (Zlength (ops_prefix)))
  **  ((&((out)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops)
  **  ((&((out)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms)
  **  ((&((out)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> capacity)
  **  (IntArray.seg ops 0 (Zlength (ops_prefix)) ops_prefix )
  **  (IntArray.undef_seg ops (Zlength (ops_prefix)) capacity )
  **  (Int64Array.seg imms 0 (Zlength (ops_prefix)) imms_prefix )
  **  (Int64Array.undef_seg imms (Zlength (ops_prefix)) capacity )
|--
  “ (out <> 0) ” 
  &&  “ (ops <> 0) ” 
  &&  “ (imms <> 0) ” 
  &&  “ ((Zlength (ops_prefix)) = (Zlength (imms_prefix))) ” 
  &&  “ (0 <= (Zlength (ops_prefix))) ” 
  &&  “ ((Zlength (ops_prefix)) < capacity) ” 
  &&  “ (capacity <= INT_MAX) ”
  &&  (((ops + ((Zlength (ops_prefix)) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ops ((Zlength (ops_prefix)) + 1 ) capacity )
  **  ((&((emitter_pre)  # "cm_emitter" ->ₛ "output")) # Ptr  |-> out)
  **  ((&((emitter_pre)  # "cm_emitter" ->ₛ "pc")) # Int  |-> (Zlength (ops_prefix)))
  **  ((&((out)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops)
  **  ((&((out)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms)
  **  ((&((out)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> capacity)
  **  (IntArray.seg ops 0 (Zlength (ops_prefix)) ops_prefix )
  **  (Int64Array.seg imms 0 (Zlength (ops_prefix)) imms_prefix )
  **  (Int64Array.undef_seg imms (Zlength (ops_prefix)) capacity )
.

Definition cm_emit_raw_partial_solve_wit_2 := 
forall (op_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (imms_prefix: (@list Z)) (ops_prefix: (@list Z)) (ops: Z) (imms: Z) (PreH1 : (out <> 0)) (PreH2 : (ops <> 0)) (PreH3 : (imms <> 0)) (PreH4 : ((Zlength (ops_prefix)) = (Zlength (imms_prefix)))) (PreH5 : (0 <= (Zlength (ops_prefix)))) (PreH6 : ((Zlength (ops_prefix)) < capacity)) (PreH7 : (capacity <= INT_MAX)) ,
  (IntArray.seg ops 0 ((Zlength (ops_prefix)) + 1 ) (app (ops_prefix) ((cons (op_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg ops ((Zlength (ops_prefix)) + 1 ) capacity )
  **  ((&((emitter_pre)  # "cm_emitter" ->ₛ "output")) # Ptr  |-> out)
  **  ((&((emitter_pre)  # "cm_emitter" ->ₛ "pc")) # Int  |-> (Zlength (ops_prefix)))
  **  ((&((out)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops)
  **  ((&((out)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms)
  **  ((&((out)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> capacity)
  **  (Int64Array.seg imms 0 (Zlength (ops_prefix)) imms_prefix )
  **  (Int64Array.undef_seg imms (Zlength (ops_prefix)) capacity )
|--
  “ (out <> 0) ” 
  &&  “ (ops <> 0) ” 
  &&  “ (imms <> 0) ” 
  &&  “ ((Zlength (ops_prefix)) = (Zlength (imms_prefix))) ” 
  &&  “ (0 <= (Zlength (ops_prefix))) ” 
  &&  “ ((Zlength (ops_prefix)) < capacity) ” 
  &&  “ (capacity <= INT_MAX) ”
  &&  (((imms + ((Zlength (ops_prefix)) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg imms ((Zlength (ops_prefix)) + 1 ) capacity )
  **  (IntArray.seg ops 0 ((Zlength (ops_prefix)) + 1 ) (app (ops_prefix) ((cons (op_pre) ((@nil Z))))) )
  **  (IntArray.undef_seg ops ((Zlength (ops_prefix)) + 1 ) capacity )
  **  ((&((emitter_pre)  # "cm_emitter" ->ₛ "output")) # Ptr  |-> out)
  **  ((&((emitter_pre)  # "cm_emitter" ->ₛ "pc")) # Int  |-> (Zlength (ops_prefix)))
  **  ((&((out)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops)
  **  ((&((out)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms)
  **  ((&((out)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> capacity)
  **  (Int64Array.seg imms 0 (Zlength (ops_prefix)) imms_prefix )
.

(*----- Function cm_emit -----*)

Definition cm_emit_entail_wit_1 := 
(
forall (immediate_pre: Z) (op_pre: Z) (emitter_pre: Z) (opcode: tvm_opcode) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (op_pre = (tvm_opcode_code (opcode)))) ,
  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (opcode) (immediate_pre))) (tail)) )
|--
  “ (op_pre = (tvm_opcode_code (opcode))) ” 
  &&  “ ((((Zlength (done)) + 1 ) + (Zlength (tail)) ) <= capacity) ” 
  &&  “ ((Zlength ((cm_rep_ops (done)))) < capacity) ”
  &&  (cm_emitter_rep emitter_pre out capacity (cm_rep_ops (done)) (cm_rep_imms (done)) )
) \/
(
forall (immediate_pre: Z) (op_pre: Z) (emitter_pre: Z) (opcode: tvm_opcode) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (op_pre = (tvm_opcode_code (opcode)))) ,
  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (opcode) (immediate_pre))) (tail)) )
|--
  “ ((Zlength ((cm_rep_ops (done)))) < capacity) ” 
  &&  “ ((((Zlength (done)) + 1 ) + (Zlength (tail)) ) <= capacity) ”
  &&  (cm_emitter_rep emitter_pre out capacity (cm_rep_ops (done)) (cm_rep_imms (done)) )
).

Definition cm_emit_entail_wit_1_split_goal_1 := 
forall (immediate_pre: Z) (op_pre: Z) (emitter_pre: Z) (opcode: tvm_opcode) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (op_pre = (tvm_opcode_code (opcode)))) ,
  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (opcode) (immediate_pre))) (tail)) )
|--
  “ ((Zlength ((cm_rep_ops (done)))) < capacity) ”
.

Definition cm_emit_entail_wit_1_split_goal_2 := 
forall (immediate_pre: Z) (op_pre: Z) (emitter_pre: Z) (opcode: tvm_opcode) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (op_pre = (tvm_opcode_code (opcode)))) ,
  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (opcode) (immediate_pre))) (tail)) )
|--
  “ ((((Zlength (done)) + 1 ) + (Zlength (tail)) ) <= capacity) ”
.

Definition cm_emit_entail_wit_1_split_goal_spatial := 
forall (immediate_pre: Z) (op_pre: Z) (emitter_pre: Z) (opcode: tvm_opcode) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (op_pre = (tvm_opcode_code (opcode)))) ,
  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (opcode) (immediate_pre))) (tail)) )
|--
  (cm_emitter_rep emitter_pre out capacity (cm_rep_ops (done)) (cm_rep_imms (done)) )
.

Definition cm_emit_return_wit_1 := 
(
forall (immediate_pre: Z) (op_pre: Z) (emitter_pre: Z) (opcode: tvm_opcode) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (op_pre = (tvm_opcode_code (opcode)))) (PreH2 : ((((Zlength (done)) + 1 ) + (Zlength (tail)) ) <= capacity)) (PreH3 : ((Zlength ((cm_rep_ops (done)))) < capacity)) ,
  (cm_emitter_rep emitter_pre out capacity (app ((cm_rep_ops (done))) ((cons (op_pre) ((@nil Z))))) (app ((cm_rep_imms (done))) ((cons (immediate_pre) ((@nil Z))))) )
|--
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cons ((TVMInst (opcode) (immediate_pre))) ((@nil tvm_inst))))) tail )
) \/
(
forall (immediate_pre: Z) (op_pre: Z) (emitter_pre: Z) (opcode: tvm_opcode) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (op_pre = (tvm_opcode_code (opcode)))) (PreH2 : ((((Zlength (done)) + 1 ) + (Zlength (tail)) ) <= capacity)) (PreH3 : ((Zlength ((cm_rep_ops (done)))) < capacity)) ,
  (cm_emitter_rep emitter_pre out capacity (app ((cm_rep_ops (done))) ((cons (op_pre) ((@nil Z))))) (app ((cm_rep_imms (done))) ((cons (immediate_pre) ((@nil Z))))) )
|--
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cons ((TVMInst (opcode) (immediate_pre))) ((@nil tvm_inst))))) tail )
).

Definition cm_emit_return_wit_1_split_goal_spatial := 
forall (immediate_pre: Z) (op_pre: Z) (emitter_pre: Z) (opcode: tvm_opcode) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (op_pre = (tvm_opcode_code (opcode)))) (PreH2 : ((((Zlength (done)) + 1 ) + (Zlength (tail)) ) <= capacity)) (PreH3 : ((Zlength ((cm_rep_ops (done)))) < capacity)) ,
  (cm_emitter_rep emitter_pre out capacity (app ((cm_rep_ops (done))) ((cons (op_pre) ((@nil Z))))) (app ((cm_rep_imms (done))) ((cons (immediate_pre) ((@nil Z))))) )
|--
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cons ((TVMInst (opcode) (immediate_pre))) ((@nil tvm_inst))))) tail )
.

Definition cm_emit_partial_solve_wit_1_pure := 
forall (immediate_pre: Z) (op_pre: Z) (emitter_pre: Z) (opcode: tvm_opcode) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (op_pre = (tvm_opcode_code (opcode)))) (PreH2 : ((((Zlength (done)) + 1 ) + (Zlength (tail)) ) <= capacity)) (PreH3 : ((Zlength ((cm_rep_ops (done)))) < capacity)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "immediate" ) )) # Int64  |-> immediate_pre)
  **  (cm_emitter_rep emitter_pre out capacity (cm_rep_ops (done)) (cm_rep_imms (done)) )
|--
  “ ((Zlength ((cm_rep_ops (done)))) < capacity) ”
.

Definition cm_emit_partial_solve_wit_1_aux := 
forall (op_pre: Z) (emitter_pre: Z) (opcode: tvm_opcode) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (op_pre = (tvm_opcode_code (opcode)))) (PreH2 : ((((Zlength (done)) + 1 ) + (Zlength (tail)) ) <= capacity)) (PreH3 : ((Zlength ((cm_rep_ops (done)))) < capacity)) ,
  (cm_emitter_rep emitter_pre out capacity (cm_rep_ops (done)) (cm_rep_imms (done)) )
|--
  “ ((Zlength ((cm_rep_ops (done)))) < capacity) ” 
  &&  “ (op_pre = (tvm_opcode_code (opcode))) ” 
  &&  “ ((((Zlength (done)) + 1 ) + (Zlength (tail)) ) <= capacity) ” 
  &&  “ ((Zlength ((cm_rep_ops (done)))) < capacity) ”
  &&  (cm_emitter_rep emitter_pre out capacity (cm_rep_ops (done)) (cm_rep_imms (done)) )
.

Definition cm_emit_partial_solve_wit_1 := cm_emit_partial_solve_wit_1_pure -> cm_emit_partial_solve_wit_1_aux.

(*----- Function cm_emit_normalize -----*)

Definition cm_emit_normalize_safety_wit_1 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_char_normalize_code (model_ty))) (tail)) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cm_emit_normalize_safety_wit_2 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) (tail)))))))))))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_emit_normalize_safety_wit_3 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) (tail)))))))))))) )
|--
  “ (256 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 256) ”
.

Definition cm_emit_normalize_safety_wit_4 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) (tail)))))))))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (12 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 12) ”
.

Definition cm_emit_normalize_safety_wit_5 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) (tail)))))))))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_emit_normalize_safety_wit_6 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app (done) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) (tail)))))))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_emit_normalize_safety_wit_7 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app (done) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) (tail)))))))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (256 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 256) ”
.

Definition cm_emit_normalize_safety_wit_8 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) (tail)))))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition cm_emit_normalize_safety_wit_9 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) (tail)))))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_emit_normalize_safety_wit_10 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMAddOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) (tail)))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_emit_normalize_safety_wit_11 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMAddOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) (tail)))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (256 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 256) ”
.

Definition cm_emit_normalize_safety_wit_12 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMAddOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMModOp) (0))) (tail)) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (12 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 12) ”
.

Definition cm_emit_normalize_safety_wit_13 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMAddOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMModOp) (0))) (tail)) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_emit_normalize_entail_wit_1 := 
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre = 1)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) ,
  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_char_normalize_code (model_ty))) (tail)) )
|--
  “ (model_ty = CMCharTy) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) (tail)))))))))))) )
) \/
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre = 1)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) ,
  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_char_normalize_code (model_ty))) (tail)) )
|--
  “ (model_ty = CMCharTy) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) (tail)))))))))))) )
).

Definition cm_emit_normalize_entail_wit_1_split_goal_1 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre = 1)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) ,
  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_char_normalize_code (model_ty))) (tail)) )
|--
  “ (model_ty = CMCharTy) ”
.

Definition cm_emit_normalize_entail_wit_1_split_goal_spatial := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre = 1)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) ,
  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_char_normalize_code (model_ty))) (tail)) )
|--
  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) (tail)))))))))))) )
.

Definition cm_emit_normalize_return_wit_1 := 
(
forall (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMAddOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst))))) tail )
|--
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_char_normalize_code (model_ty)))) tail )
) \/
(
forall (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMAddOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst))))) tail )
|--
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_char_normalize_code (model_ty)))) tail )
).

Definition cm_emit_normalize_return_wit_1_split_goal_spatial := 
forall (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMAddOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst))))) tail )
|--
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_char_normalize_code (model_ty)))) tail )
.

Definition cm_emit_normalize_return_wit_2 := 
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre <> 1)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) ,
  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_char_normalize_code (model_ty))) (tail)) )
|--
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_char_normalize_code (model_ty)))) tail )
) \/
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre <> 1)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) ,
  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_char_normalize_code (model_ty))) (tail)) )
|--
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_char_normalize_code (model_ty)))) tail )
).

Definition cm_emit_normalize_return_wit_2_split_goal_spatial := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre <> 1)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) ,
  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_char_normalize_code (model_ty))) (tail)) )
|--
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_char_normalize_code (model_ty)))) tail )
.

Definition cm_emit_normalize_partial_solve_wit_1_pure := 
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) (tail)))))))))))) )
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ”
) \/
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre <= INT_MAX)) (PreH2 : (ty_pre >= INT_MIN)) (PreH3 : (model_ty = CMCharTy)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) (tail)))))))))))) )
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ”
).

Definition cm_emit_normalize_partial_solve_wit_1_pure_split_goal_1 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre <= INT_MAX)) (PreH2 : (ty_pre >= INT_MIN)) (PreH3 : (model_ty = CMCharTy)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) (tail)))))))))))) )
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ”
.

Definition cm_emit_normalize_partial_solve_wit_1_aux := 
forall (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) (tail)))))))))))) )
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ” 
  &&  “ (model_ty = CMCharTy) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) (tail)))))))))))) )
.

Definition cm_emit_normalize_partial_solve_wit_1 := cm_emit_normalize_partial_solve_wit_1_pure -> cm_emit_normalize_partial_solve_wit_1_aux.

Definition cm_emit_normalize_partial_solve_wit_2_pure := 
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) (tail)))))))))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (12 = (tvm_opcode_code (TVMModOp))) ”
) \/
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre <= INT_MAX)) (PreH2 : (ty_pre >= INT_MIN)) (PreH3 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) (tail)))))))))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (12 = (tvm_opcode_code (TVMModOp))) ”
).

Definition cm_emit_normalize_partial_solve_wit_2_pure_split_goal_1 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre <= INT_MAX)) (PreH2 : (ty_pre >= INT_MIN)) (PreH3 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) (tail)))))))))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (12 = (tvm_opcode_code (TVMModOp))) ”
.

Definition cm_emit_normalize_partial_solve_wit_2_aux := 
forall (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) (tail)))))))))) )
|--
  “ (12 = (tvm_opcode_code (TVMModOp))) ” 
  &&  “ (model_ty = CMCharTy) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) (tail)))))))))) )
.

Definition cm_emit_normalize_partial_solve_wit_2 := cm_emit_normalize_partial_solve_wit_2_pure -> cm_emit_normalize_partial_solve_wit_2_aux.

Definition cm_emit_normalize_partial_solve_wit_3_pure := 
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app (done) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) (tail)))))))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ”
) \/
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre <= INT_MAX)) (PreH2 : (ty_pre >= INT_MIN)) (PreH3 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app (done) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) (tail)))))))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ”
).

Definition cm_emit_normalize_partial_solve_wit_3_pure_split_goal_1 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre <= INT_MAX)) (PreH2 : (ty_pre >= INT_MIN)) (PreH3 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app (done) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) (tail)))))))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ”
.

Definition cm_emit_normalize_partial_solve_wit_3_aux := 
forall (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app (done) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) (tail)))))))) )
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ” 
  &&  “ (model_ty = CMCharTy) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity (app ((app (done) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) (tail)))))))) )
.

Definition cm_emit_normalize_partial_solve_wit_3 := cm_emit_normalize_partial_solve_wit_3_pure -> cm_emit_normalize_partial_solve_wit_3_aux.

Definition cm_emit_normalize_partial_solve_wit_4_pure := 
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) (tail)))))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (8 = (tvm_opcode_code (TVMAddOp))) ”
) \/
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre <= INT_MAX)) (PreH2 : (ty_pre >= INT_MIN)) (PreH3 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) (tail)))))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (8 = (tvm_opcode_code (TVMAddOp))) ”
).

Definition cm_emit_normalize_partial_solve_wit_4_pure_split_goal_1 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre <= INT_MAX)) (PreH2 : (ty_pre >= INT_MIN)) (PreH3 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) (tail)))))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (8 = (tvm_opcode_code (TVMAddOp))) ”
.

Definition cm_emit_normalize_partial_solve_wit_4_aux := 
forall (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) (tail)))))) )
|--
  “ (8 = (tvm_opcode_code (TVMAddOp))) ” 
  &&  “ (model_ty = CMCharTy) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity (app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) (tail)))))) )
.

Definition cm_emit_normalize_partial_solve_wit_4 := cm_emit_normalize_partial_solve_wit_4_pure -> cm_emit_normalize_partial_solve_wit_4_aux.

Definition cm_emit_normalize_partial_solve_wit_5_pure := 
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMAddOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) (tail)))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ”
) \/
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre <= INT_MAX)) (PreH2 : (ty_pre >= INT_MIN)) (PreH3 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMAddOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) (tail)))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ”
).

Definition cm_emit_normalize_partial_solve_wit_5_pure_split_goal_1 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre <= INT_MAX)) (PreH2 : (ty_pre >= INT_MIN)) (PreH3 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMAddOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) (tail)))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ”
.

Definition cm_emit_normalize_partial_solve_wit_5_aux := 
forall (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMAddOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) (tail)))) )
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ” 
  &&  “ (model_ty = CMCharTy) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity (app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMAddOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) (tail)))) )
.

Definition cm_emit_normalize_partial_solve_wit_5 := cm_emit_normalize_partial_solve_wit_5_pure -> cm_emit_normalize_partial_solve_wit_5_aux.

Definition cm_emit_normalize_partial_solve_wit_6_pure := 
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMAddOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMModOp) (0))) (tail)) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (12 = (tvm_opcode_code (TVMModOp))) ”
) \/
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre <= INT_MAX)) (PreH2 : (ty_pre >= INT_MIN)) (PreH3 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMAddOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMModOp) (0))) (tail)) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (12 = (tvm_opcode_code (TVMModOp))) ”
).

Definition cm_emit_normalize_partial_solve_wit_6_pure_split_goal_1 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre <= INT_MAX)) (PreH2 : (ty_pre >= INT_MIN)) (PreH3 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMAddOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMModOp) (0))) (tail)) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (12 = (tvm_opcode_code (TVMModOp))) ”
.

Definition cm_emit_normalize_partial_solve_wit_6_aux := 
forall (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMAddOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMModOp) (0))) (tail)) )
|--
  “ (12 = (tvm_opcode_code (TVMModOp))) ” 
  &&  “ (model_ty = CMCharTy) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity (app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMAddOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMModOp) (0))) (tail)) )
.

Definition cm_emit_normalize_partial_solve_wit_6 := cm_emit_normalize_partial_solve_wit_6_pure -> cm_emit_normalize_partial_solve_wit_6_aux.

(*----- Function cm_emit_load -----*)

Definition cm_emit_load_safety_wit_1 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_load_code (model_ty))) (tail)) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cm_emit_load_safety_wit_2 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMLoadBOp) (0))) (tail)) )
|--
  “ (6 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 6) ”
.

Definition cm_emit_load_safety_wit_3 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMLoadBOp) (0))) (tail)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_emit_load_safety_wit_4 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty <> CMCharTy)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMLoadOp) (0))) (tail)) )
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition cm_emit_load_safety_wit_5 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty <> CMCharTy)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMLoadOp) (0))) (tail)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_emit_load_entail_wit_1 := 
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre = 1)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) ,
  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_load_code (model_ty))) (tail)) )
|--
  “ (model_ty = CMCharTy) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMLoadBOp) (0))) (tail)) )
) \/
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre = 1)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) ,
  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_load_code (model_ty))) (tail)) )
|--
  “ (model_ty = CMCharTy) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMLoadBOp) (0))) (tail)) )
).

Definition cm_emit_load_entail_wit_1_split_goal_1 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre = 1)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) ,
  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_load_code (model_ty))) (tail)) )
|--
  “ (model_ty = CMCharTy) ”
.

Definition cm_emit_load_entail_wit_1_split_goal_spatial := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre = 1)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) ,
  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_load_code (model_ty))) (tail)) )
|--
  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMLoadBOp) (0))) (tail)) )
.

Definition cm_emit_load_entail_wit_2 := 
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre <> 1)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) ,
  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_load_code (model_ty))) (tail)) )
|--
  “ (model_ty <> CMCharTy) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMLoadOp) (0))) (tail)) )
) \/
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre <> 1)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) ,
  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_load_code (model_ty))) (tail)) )
|--
  “ (model_ty <> CMCharTy) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMLoadOp) (0))) (tail)) )
).

Definition cm_emit_load_entail_wit_2_split_goal_1 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre <> 1)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) ,
  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_load_code (model_ty))) (tail)) )
|--
  “ (model_ty <> CMCharTy) ”
.

Definition cm_emit_load_entail_wit_2_split_goal_spatial := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre <> 1)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) ,
  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_load_code (model_ty))) (tail)) )
|--
  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMLoadOp) (0))) (tail)) )
.

Definition cm_emit_load_return_wit_1 := 
(
forall (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMLoadBOp) (0))) ((@nil tvm_inst))))) tail )
|--
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_load_code (model_ty)))) tail )
) \/
(
forall (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMLoadBOp) (0))) ((@nil tvm_inst))))) tail )
|--
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_load_code (model_ty)))) tail )
).

Definition cm_emit_load_return_wit_1_split_goal_spatial := 
forall (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMLoadBOp) (0))) ((@nil tvm_inst))))) tail )
|--
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_load_code (model_ty)))) tail )
.

Definition cm_emit_load_return_wit_2 := 
(
forall (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty <> CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst))))) tail )
|--
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_load_code (model_ty)))) tail )
) \/
(
forall (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty <> CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst))))) tail )
|--
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_load_code (model_ty)))) tail )
).

Definition cm_emit_load_return_wit_2_split_goal_spatial := 
forall (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty <> CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst))))) tail )
|--
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_load_code (model_ty)))) tail )
.

Definition cm_emit_load_partial_solve_wit_1_pure := 
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMLoadBOp) (0))) (tail)) )
|--
  “ (6 = (tvm_opcode_code (TVMLoadBOp))) ”
) \/
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre <= INT_MAX)) (PreH2 : (ty_pre >= INT_MIN)) (PreH3 : (model_ty = CMCharTy)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMLoadBOp) (0))) (tail)) )
|--
  “ (6 = (tvm_opcode_code (TVMLoadBOp))) ”
).

Definition cm_emit_load_partial_solve_wit_1_pure_split_goal_1 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre <= INT_MAX)) (PreH2 : (ty_pre >= INT_MIN)) (PreH3 : (model_ty = CMCharTy)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMLoadBOp) (0))) (tail)) )
|--
  “ (6 = (tvm_opcode_code (TVMLoadBOp))) ”
.

Definition cm_emit_load_partial_solve_wit_1_aux := 
forall (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMLoadBOp) (0))) (tail)) )
|--
  “ (6 = (tvm_opcode_code (TVMLoadBOp))) ” 
  &&  “ (model_ty = CMCharTy) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMLoadBOp) (0))) (tail)) )
.

Definition cm_emit_load_partial_solve_wit_1 := cm_emit_load_partial_solve_wit_1_pure -> cm_emit_load_partial_solve_wit_1_aux.

Definition cm_emit_load_partial_solve_wit_2_pure := 
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty <> CMCharTy)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMLoadOp) (0))) (tail)) )
|--
  “ (4 = (tvm_opcode_code (TVMLoadOp))) ”
) \/
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre <= INT_MAX)) (PreH2 : (ty_pre >= INT_MIN)) (PreH3 : (model_ty <> CMCharTy)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMLoadOp) (0))) (tail)) )
|--
  “ (4 = (tvm_opcode_code (TVMLoadOp))) ”
).

Definition cm_emit_load_partial_solve_wit_2_pure_split_goal_1 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre <= INT_MAX)) (PreH2 : (ty_pre >= INT_MIN)) (PreH3 : (model_ty <> CMCharTy)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMLoadOp) (0))) (tail)) )
|--
  “ (4 = (tvm_opcode_code (TVMLoadOp))) ”
.

Definition cm_emit_load_partial_solve_wit_2_aux := 
forall (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty <> CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMLoadOp) (0))) (tail)) )
|--
  “ (4 = (tvm_opcode_code (TVMLoadOp))) ” 
  &&  “ (model_ty <> CMCharTy) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMLoadOp) (0))) (tail)) )
.

Definition cm_emit_load_partial_solve_wit_2 := cm_emit_load_partial_solve_wit_2_pure -> cm_emit_load_partial_solve_wit_2_aux.

(*----- Function cm_emit_store -----*)

Definition cm_emit_store_safety_wit_1 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_store_code (model_ty))) (tail)) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cm_emit_store_safety_wit_2 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMStoreBOp) (0))) (tail)) )
|--
  “ (7 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 7) ”
.

Definition cm_emit_store_safety_wit_3 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMStoreBOp) (0))) (tail)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_emit_store_safety_wit_4 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty <> CMCharTy)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMStoreOp) (0))) (tail)) )
|--
  “ (5 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 5) ”
.

Definition cm_emit_store_safety_wit_5 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty <> CMCharTy)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMStoreOp) (0))) (tail)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_emit_store_entail_wit_1 := 
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre = 1)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) ,
  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_store_code (model_ty))) (tail)) )
|--
  “ (model_ty = CMCharTy) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMStoreBOp) (0))) (tail)) )
) \/
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre = 1)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) ,
  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_store_code (model_ty))) (tail)) )
|--
  “ (model_ty = CMCharTy) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMStoreBOp) (0))) (tail)) )
).

Definition cm_emit_store_entail_wit_1_split_goal_1 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre = 1)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) ,
  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_store_code (model_ty))) (tail)) )
|--
  “ (model_ty = CMCharTy) ”
.

Definition cm_emit_store_entail_wit_1_split_goal_spatial := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre = 1)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) ,
  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_store_code (model_ty))) (tail)) )
|--
  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMStoreBOp) (0))) (tail)) )
.

Definition cm_emit_store_entail_wit_2 := 
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre <> 1)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) ,
  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_store_code (model_ty))) (tail)) )
|--
  “ (model_ty <> CMCharTy) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMStoreOp) (0))) (tail)) )
) \/
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre <> 1)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) ,
  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_store_code (model_ty))) (tail)) )
|--
  “ (model_ty <> CMCharTy) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMStoreOp) (0))) (tail)) )
).

Definition cm_emit_store_entail_wit_2_split_goal_1 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre <> 1)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) ,
  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_store_code (model_ty))) (tail)) )
|--
  “ (model_ty <> CMCharTy) ”
.

Definition cm_emit_store_entail_wit_2_split_goal_spatial := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre <> 1)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) ,
  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_store_code (model_ty))) (tail)) )
|--
  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMStoreOp) (0))) (tail)) )
.

Definition cm_emit_store_return_wit_1 := 
(
forall (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMStoreBOp) (0))) ((@nil tvm_inst))))) tail )
|--
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_store_code (model_ty)))) tail )
) \/
(
forall (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMStoreBOp) (0))) ((@nil tvm_inst))))) tail )
|--
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_store_code (model_ty)))) tail )
).

Definition cm_emit_store_return_wit_1_split_goal_spatial := 
forall (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMStoreBOp) (0))) ((@nil tvm_inst))))) tail )
|--
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_store_code (model_ty)))) tail )
.

Definition cm_emit_store_return_wit_2 := 
(
forall (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty <> CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst))))) tail )
|--
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_store_code (model_ty)))) tail )
) \/
(
forall (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty <> CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst))))) tail )
|--
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_store_code (model_ty)))) tail )
).

Definition cm_emit_store_return_wit_2_split_goal_spatial := 
forall (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty <> CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst))))) tail )
|--
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_store_code (model_ty)))) tail )
.

Definition cm_emit_store_partial_solve_wit_1_pure := 
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMStoreBOp) (0))) (tail)) )
|--
  “ (7 = (tvm_opcode_code (TVMStoreBOp))) ”
) \/
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre <= INT_MAX)) (PreH2 : (ty_pre >= INT_MIN)) (PreH3 : (model_ty = CMCharTy)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMStoreBOp) (0))) (tail)) )
|--
  “ (7 = (tvm_opcode_code (TVMStoreBOp))) ”
).

Definition cm_emit_store_partial_solve_wit_1_pure_split_goal_1 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre <= INT_MAX)) (PreH2 : (ty_pre >= INT_MIN)) (PreH3 : (model_ty = CMCharTy)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMStoreBOp) (0))) (tail)) )
|--
  “ (7 = (tvm_opcode_code (TVMStoreBOp))) ”
.

Definition cm_emit_store_partial_solve_wit_1_aux := 
forall (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty = CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMStoreBOp) (0))) (tail)) )
|--
  “ (7 = (tvm_opcode_code (TVMStoreBOp))) ” 
  &&  “ (model_ty = CMCharTy) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMStoreBOp) (0))) (tail)) )
.

Definition cm_emit_store_partial_solve_wit_1 := cm_emit_store_partial_solve_wit_1_pure -> cm_emit_store_partial_solve_wit_1_aux.

Definition cm_emit_store_partial_solve_wit_2_pure := 
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty <> CMCharTy)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMStoreOp) (0))) (tail)) )
|--
  “ (5 = (tvm_opcode_code (TVMStoreOp))) ”
) \/
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre <= INT_MAX)) (PreH2 : (ty_pre >= INT_MIN)) (PreH3 : (model_ty <> CMCharTy)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMStoreOp) (0))) (tail)) )
|--
  “ (5 = (tvm_opcode_code (TVMStoreOp))) ”
).

Definition cm_emit_store_partial_solve_wit_2_pure_split_goal_1 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (ty_pre <= INT_MAX)) (PreH2 : (ty_pre >= INT_MIN)) (PreH3 : (model_ty <> CMCharTy)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMStoreOp) (0))) (tail)) )
|--
  “ (5 = (tvm_opcode_code (TVMStoreOp))) ”
.

Definition cm_emit_store_partial_solve_wit_2_aux := 
forall (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (model_ty <> CMCharTy)) ,
  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMStoreOp) (0))) (tail)) )
|--
  “ (5 = (tvm_opcode_code (TVMStoreOp))) ” 
  &&  “ (model_ty <> CMCharTy) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMStoreOp) (0))) (tail)) )
.

Definition cm_emit_store_partial_solve_wit_2 := cm_emit_store_partial_solve_wit_2_pure -> cm_emit_store_partial_solve_wit_2_aux.

(*----- Function cm_emit_fp_address -----*)

Definition cm_emit_fp_address_safety_wit_1 := 
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "offset" ) )) # Int64  |-> offset_pre)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMPushOp) (offset_pre))) ((cons ((TVMInst (TVMAddOp) (0))) (tail)))))))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_emit_fp_address_safety_wit_2 := 
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "offset" ) )) # Int64  |-> offset_pre)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMPushOp) (offset_pre))) ((cons ((TVMInst (TVMAddOp) (0))) (tail)))))))) )
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition cm_emit_fp_address_safety_wit_3 := 
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMPushOp) (offset_pre))) ((cons ((TVMInst (TVMAddOp) (0))) (tail)))))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "offset" ) )) # Int64  |-> offset_pre)
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition cm_emit_fp_address_safety_wit_4 := 
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMPushOp) (offset_pre))) ((cons ((TVMInst (TVMAddOp) (0))) (tail)))))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "offset" ) )) # Int64  |-> offset_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_emit_fp_address_safety_wit_5 := 
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (offset_pre))) ((cons ((TVMInst (TVMAddOp) (0))) (tail)))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "offset" ) )) # Int64  |-> offset_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_emit_fp_address_safety_wit_6 := 
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (offset_pre))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMAddOp) (0))) (tail)) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "offset" ) )) # Int64  |-> offset_pre)
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition cm_emit_fp_address_safety_wit_7 := 
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (offset_pre))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMAddOp) (0))) (tail)) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "offset" ) )) # Int64  |-> offset_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_emit_fp_address_entail_wit_1 := 
(
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) ,
  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_fp_relative_address_code (offset_pre))) (tail)) )
|--
  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMPushOp) (offset_pre))) ((cons ((TVMInst (TVMAddOp) (0))) (tail)))))))) )
) \/
(
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) ,
  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_fp_relative_address_code (offset_pre))) (tail)) )
|--
  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMPushOp) (offset_pre))) ((cons ((TVMInst (TVMAddOp) (0))) (tail)))))))) )
).

Definition cm_emit_fp_address_entail_wit_1_split_goal_spatial := 
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) ,
  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_fp_relative_address_code (offset_pre))) (tail)) )
|--
  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMPushOp) (offset_pre))) ((cons ((TVMInst (TVMAddOp) (0))) (tail)))))))) )
.

Definition cm_emit_fp_address_return_wit_1 := 
(
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (offset_pre))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMAddOp) (0))) ((@nil tvm_inst))))) tail )
|--
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_fp_relative_address_code (offset_pre)))) tail )
) \/
(
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (offset_pre))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMAddOp) (0))) ((@nil tvm_inst))))) tail )
|--
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_fp_relative_address_code (offset_pre)))) tail )
).

Definition cm_emit_fp_address_return_wit_1_split_goal_spatial := 
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (offset_pre))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMAddOp) (0))) ((@nil tvm_inst))))) tail )
|--
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_fp_relative_address_code (offset_pre)))) tail )
.

Definition cm_emit_fp_address_partial_solve_wit_1_pure := 
(
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "offset" ) )) # Int64  |-> offset_pre)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMPushOp) (offset_pre))) ((cons ((TVMInst (TVMAddOp) (0))) (tail)))))))) )
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ”
) \/
(
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (offset_pre <= INT64_MAX)) (PreH2 : (offset_pre >= INT64_MIN)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "offset" ) )) # Int64  |-> offset_pre)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMPushOp) (offset_pre))) ((cons ((TVMInst (TVMAddOp) (0))) (tail)))))))) )
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ”
).

Definition cm_emit_fp_address_partial_solve_wit_1_pure_split_goal_1 := 
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (offset_pre <= INT64_MAX)) (PreH2 : (offset_pre >= INT64_MIN)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "offset" ) )) # Int64  |-> offset_pre)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMPushOp) (offset_pre))) ((cons ((TVMInst (TVMAddOp) (0))) (tail)))))))) )
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ”
.

Definition cm_emit_fp_address_partial_solve_wit_1_aux := 
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) ,
  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMPushOp) (offset_pre))) ((cons ((TVMInst (TVMAddOp) (0))) (tail)))))))) )
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMPushOp) (offset_pre))) ((cons ((TVMInst (TVMAddOp) (0))) (tail)))))))) )
.

Definition cm_emit_fp_address_partial_solve_wit_1 := cm_emit_fp_address_partial_solve_wit_1_pure -> cm_emit_fp_address_partial_solve_wit_1_aux.

Definition cm_emit_fp_address_partial_solve_wit_2_pure := 
(
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMPushOp) (offset_pre))) ((cons ((TVMInst (TVMAddOp) (0))) (tail)))))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "offset" ) )) # Int64  |-> offset_pre)
|--
  “ (4 = (tvm_opcode_code (TVMLoadOp))) ”
) \/
(
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (offset_pre <= INT64_MAX)) (PreH2 : (offset_pre >= INT64_MIN)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMPushOp) (offset_pre))) ((cons ((TVMInst (TVMAddOp) (0))) (tail)))))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "offset" ) )) # Int64  |-> offset_pre)
|--
  “ (4 = (tvm_opcode_code (TVMLoadOp))) ”
).

Definition cm_emit_fp_address_partial_solve_wit_2_pure_split_goal_1 := 
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (offset_pre <= INT64_MAX)) (PreH2 : (offset_pre >= INT64_MIN)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMPushOp) (offset_pre))) ((cons ((TVMInst (TVMAddOp) (0))) (tail)))))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "offset" ) )) # Int64  |-> offset_pre)
|--
  “ (4 = (tvm_opcode_code (TVMLoadOp))) ”
.

Definition cm_emit_fp_address_partial_solve_wit_2_aux := 
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMPushOp) (offset_pre))) ((cons ((TVMInst (TVMAddOp) (0))) (tail)))))) )
|--
  “ (4 = (tvm_opcode_code (TVMLoadOp))) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMPushOp) (offset_pre))) ((cons ((TVMInst (TVMAddOp) (0))) (tail)))))) )
.

Definition cm_emit_fp_address_partial_solve_wit_2 := cm_emit_fp_address_partial_solve_wit_2_pure -> cm_emit_fp_address_partial_solve_wit_2_aux.

Definition cm_emit_fp_address_partial_solve_wit_3_pure := 
(
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (offset_pre))) ((cons ((TVMInst (TVMAddOp) (0))) (tail)))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "offset" ) )) # Int64  |-> offset_pre)
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ”
) \/
(
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (offset_pre <= INT64_MAX)) (PreH2 : (offset_pre >= INT64_MIN)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (offset_pre))) ((cons ((TVMInst (TVMAddOp) (0))) (tail)))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "offset" ) )) # Int64  |-> offset_pre)
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ”
).

Definition cm_emit_fp_address_partial_solve_wit_3_pure_split_goal_1 := 
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (offset_pre <= INT64_MAX)) (PreH2 : (offset_pre >= INT64_MIN)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (offset_pre))) ((cons ((TVMInst (TVMAddOp) (0))) (tail)))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "offset" ) )) # Int64  |-> offset_pre)
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ”
.

Definition cm_emit_fp_address_partial_solve_wit_3_aux := 
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (offset_pre))) ((cons ((TVMInst (TVMAddOp) (0))) (tail)))) )
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity (app ((app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (offset_pre))) ((cons ((TVMInst (TVMAddOp) (0))) (tail)))) )
.

Definition cm_emit_fp_address_partial_solve_wit_3 := cm_emit_fp_address_partial_solve_wit_3_pure -> cm_emit_fp_address_partial_solve_wit_3_aux.

Definition cm_emit_fp_address_partial_solve_wit_4_pure := 
(
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (offset_pre))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMAddOp) (0))) (tail)) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "offset" ) )) # Int64  |-> offset_pre)
|--
  “ (8 = (tvm_opcode_code (TVMAddOp))) ”
) \/
(
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (offset_pre <= INT64_MAX)) (PreH2 : (offset_pre >= INT64_MIN)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (offset_pre))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMAddOp) (0))) (tail)) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "offset" ) )) # Int64  |-> offset_pre)
|--
  “ (8 = (tvm_opcode_code (TVMAddOp))) ”
).

Definition cm_emit_fp_address_partial_solve_wit_4_pure_split_goal_1 := 
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (PreH1 : (offset_pre <= INT64_MAX)) (PreH2 : (offset_pre >= INT64_MIN)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (offset_pre))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMAddOp) (0))) (tail)) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "offset" ) )) # Int64  |-> offset_pre)
|--
  “ (8 = (tvm_opcode_code (TVMAddOp))) ”
.

Definition cm_emit_fp_address_partial_solve_wit_4_aux := 
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (offset_pre))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMAddOp) (0))) (tail)) )
|--
  “ (8 = (tvm_opcode_code (TVMAddOp))) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity (app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (offset_pre))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMAddOp) (0))) (tail)) )
.

Definition cm_emit_fp_address_partial_solve_wit_4 := cm_emit_fp_address_partial_solve_wit_4_pure -> cm_emit_fp_address_partial_solve_wit_4_aux.

(*----- Function cm_emit_temp_store -----*)

Definition cm_emit_temp_store_safety_wit_1 := 
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (offset: Z) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH9 : (offset = (cm_temp_offset (policy) (p) (fid) (temp_pre)))) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_fp_relative_address_code (offset)))) (cons ((TVMInst (TVMStoreOp) (0))) (tail)) )
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "offset" ) )) # Int64  |-> offset)
  **  (cm_function_context_rep fn_pre f body next )
|--
  “ (5 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 5) ”
.

Definition cm_emit_temp_store_safety_wit_2 := 
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (offset: Z) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH9 : (offset = (cm_temp_offset (policy) (p) (fid) (temp_pre)))) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_fp_relative_address_code (offset)))) (cons ((TVMInst (TVMStoreOp) (0))) (tail)) )
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "offset" ) )) # Int64  |-> offset)
  **  (cm_function_context_rep fn_pre f body next )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_emit_temp_store_entail_wit_1 := 
(
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_temp_store_code (policy) (p) (fid) (temp_pre))) (tail)) )
|--
  EX (lp: Z)  (pp: Z) ,
  “ (fn_pre <> 0) ” 
  &&  “ (0 <= temp_pre) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX) ” 
  &&  “ ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) = (cm_temp_offset (policy) (p) (fid) (temp_pre))) ” 
  &&  “ ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) <= INT_MAX) ”
  &&  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_temp_store_code (policy) (p) (fid) (temp_pre))) (tail)) )
) \/
(
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_temp_store_code (policy) (p) (fid) (temp_pre))) (tail)) )
|--
  EX (lp: Z)  (pp: Z) ,
  “ (fn_pre <> 0) ” 
  &&  “ (0 <= temp_pre) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX) ” 
  &&  “ ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) = (cm_temp_offset (policy) (p) (fid) (temp_pre))) ” 
  &&  “ ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) <= INT_MAX) ”
  &&  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_temp_store_code (policy) (p) (fid) (temp_pre))) (tail)) )
).

Definition cm_emit_temp_store_entail_wit_2 := 
(
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (pp: Z) (lp: Z) (retval: Z) (PreH1 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH2 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH3 : (0 <= temp_pre)) (PreH4 : ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) <= INT_MAX)) (PreH5 : (retval = (((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ))) (PreH6 : (fn_pre <> 0)) (PreH7 : (0 <= temp_pre)) (PreH8 : (structs = (cm_program_structs (p)))) (PreH9 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH10 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH11 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH12 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH13 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH14 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH15 : ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) = (cm_temp_offset (policy) (p) (fid) (temp_pre)))) (PreH16 : ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) <= INT_MAX)) ,
  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_temp_store_code (policy) (p) (fid) (temp_pre))) (tail)) )
|--
  “ (0 <= temp_pre) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX) ” 
  &&  “ (retval = (cm_temp_offset (policy) (p) (fid) (temp_pre))) ”
  &&  (cm_function_context_rep fn_pre f body next )
  **  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_fp_relative_address_code (retval))) ((cons ((TVMInst (TVMStoreOp) (0))) (tail)))) )
) \/
(
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (pp: Z) (lp: Z) (retval: Z) (PreH1 : ((cm_type_encode ((cm_function_ret (f)))) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_function_ret (f)))) >= INT_MIN)) (PreH3 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH4 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH5 : (0 <= temp_pre)) (PreH6 : ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) <= INT_MAX)) (PreH7 : (retval = (((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ))) (PreH8 : (fn_pre <> 0)) (PreH9 : (0 <= temp_pre)) (PreH10 : (structs = (cm_program_structs (p)))) (PreH11 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH12 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH13 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH14 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH15 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH16 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH17 : ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) = (cm_temp_offset (policy) (p) (fid) (temp_pre)))) (PreH18 : ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) <= INT_MAX)) ,
  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_temp_store_code (policy) (p) (fid) (temp_pre))) (tail)) )
|--
  (cm_function_context_rep fn_pre f body next )
  **  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_fp_relative_address_code (retval))) ((cons ((TVMInst (TVMStoreOp) (0))) (tail)))) )
).

Definition cm_emit_temp_store_entail_wit_2_split_goal_spatial := 
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (pp: Z) (lp: Z) (retval: Z) (PreH1 : ((cm_type_encode ((cm_function_ret (f)))) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_function_ret (f)))) >= INT_MIN)) (PreH3 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH4 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH5 : (0 <= temp_pre)) (PreH6 : ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) <= INT_MAX)) (PreH7 : (retval = (((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ))) (PreH8 : (fn_pre <> 0)) (PreH9 : (0 <= temp_pre)) (PreH10 : (structs = (cm_program_structs (p)))) (PreH11 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH12 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH13 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH14 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH15 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH16 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH17 : ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) = (cm_temp_offset (policy) (p) (fid) (temp_pre)))) (PreH18 : ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) <= INT_MAX)) ,
  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_temp_store_code (policy) (p) (fid) (temp_pre))) (tail)) )
|--
  (cm_function_context_rep fn_pre f body next )
  **  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_fp_relative_address_code (retval))) ((cons ((TVMInst (TVMStoreOp) (0))) (tail)))) )
.

Definition cm_emit_temp_store_return_wit_1 := 
(
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (offset: Z) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH9 : (offset = (cm_temp_offset (policy) (p) (fid) (temp_pre)))) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app (done) ((cm_fp_relative_address_code (offset))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst))))) tail )
  **  (cm_function_context_rep fn_pre f body next )
|--
  “ (0 <= temp_pre) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX) ”
  &&  (cm_function_context_rep fn_pre f body next )
  **  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_temp_store_code (policy) (p) (fid) (temp_pre)))) tail )
) \/
(
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (offset: Z) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH9 : (offset = (cm_temp_offset (policy) (p) (fid) (temp_pre)))) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app (done) ((cm_fp_relative_address_code (offset))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst))))) tail )
  **  (cm_function_context_rep fn_pre f body next )
|--
  (cm_function_context_rep fn_pre f body next )
  **  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_temp_store_code (policy) (p) (fid) (temp_pre)))) tail )
).

Definition cm_emit_temp_store_return_wit_1_split_goal_spatial := 
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (offset: Z) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH9 : (offset = (cm_temp_offset (policy) (p) (fid) (temp_pre)))) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app (done) ((cm_fp_relative_address_code (offset))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst))))) tail )
  **  (cm_function_context_rep fn_pre f body next )
|--
  (cm_function_context_rep fn_pre f body next )
  **  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_temp_store_code (policy) (p) (fid) (temp_pre)))) tail )
.

Definition cm_emit_temp_store_partial_solve_wit_1_pure := 
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (pp: Z) (lp: Z) (PreH1 : (fn_pre <> 0)) (PreH2 : (0 <= temp_pre)) (PreH3 : (structs = (cm_program_structs (p)))) (PreH4 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH5 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH6 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH8 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH9 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH10 : ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) = (cm_temp_offset (policy) (p) (fid) (temp_pre)))) (PreH11 : ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) <= INT_MAX)) ,
  ((( &( "offset" ) )) # Int64  |->_)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_temp_store_code (policy) (p) (fid) (temp_pre))) (tail)) )
|--
  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (0 <= temp_pre) ” 
  &&  “ ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) <= INT_MAX) ”
.

Definition cm_emit_temp_store_partial_solve_wit_1_aux := 
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (pp: Z) (lp: Z) (PreH1 : (fn_pre <> 0)) (PreH2 : (0 <= temp_pre)) (PreH3 : (structs = (cm_program_structs (p)))) (PreH4 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH5 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH6 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH8 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH9 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH10 : ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) = (cm_temp_offset (policy) (p) (fid) (temp_pre)))) (PreH11 : ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) <= INT_MAX)) ,
  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_temp_store_code (policy) (p) (fid) (temp_pre))) (tail)) )
|--
  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (0 <= temp_pre) ” 
  &&  “ ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) <= INT_MAX) ” 
  &&  “ (fn_pre <> 0) ” 
  &&  “ (0 <= temp_pre) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX) ” 
  &&  “ ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) = (cm_temp_offset (policy) (p) (fid) (temp_pre))) ” 
  &&  “ ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) <= INT_MAX) ”
  &&  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_temp_store_code (policy) (p) (fid) (temp_pre))) (tail)) )
.

Definition cm_emit_temp_store_partial_solve_wit_1 := cm_emit_temp_store_partial_solve_wit_1_pure -> cm_emit_temp_store_partial_solve_wit_1_aux.

Definition cm_emit_temp_store_partial_solve_wit_2 := 
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (offset: Z) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH9 : (offset = (cm_temp_offset (policy) (p) (fid) (temp_pre)))) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_fp_relative_address_code (offset))) ((cons ((TVMInst (TVMStoreOp) (0))) (tail)))) )
|--
  “ (0 <= temp_pre) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX) ” 
  &&  “ (offset = (cm_temp_offset (policy) (p) (fid) (temp_pre))) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_fp_relative_address_code (offset))) ((cons ((TVMInst (TVMStoreOp) (0))) (tail)))) )
  **  (cm_function_context_rep fn_pre f body next )
.

Definition cm_emit_temp_store_partial_solve_wit_3_pure := 
(
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (offset: Z) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH9 : (offset = (cm_temp_offset (policy) (p) (fid) (temp_pre)))) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_fp_relative_address_code (offset)))) (cons ((TVMInst (TVMStoreOp) (0))) (tail)) )
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "offset" ) )) # Int64  |-> offset)
  **  (cm_function_context_rep fn_pre f body next )
|--
  “ (5 = (tvm_opcode_code (TVMStoreOp))) ”
) \/
(
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (offset: Z) (PreH1 : (offset <= INT64_MAX)) (PreH2 : (offset >= INT64_MIN)) (PreH3 : (temp_pre <= INT_MAX)) (PreH4 : (temp_pre >= INT_MIN)) (PreH5 : (0 <= temp_pre)) (PreH6 : (structs = (cm_program_structs (p)))) (PreH7 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH8 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH9 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH10 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH11 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH12 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH13 : (offset = (cm_temp_offset (policy) (p) (fid) (temp_pre)))) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_fp_relative_address_code (offset)))) (cons ((TVMInst (TVMStoreOp) (0))) (tail)) )
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "offset" ) )) # Int64  |-> offset)
  **  (cm_function_context_rep fn_pre f body next )
|--
  “ (5 = (tvm_opcode_code (TVMStoreOp))) ”
).

Definition cm_emit_temp_store_partial_solve_wit_3_pure_split_goal_1 := 
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (offset: Z) (PreH1 : (offset <= INT64_MAX)) (PreH2 : (offset >= INT64_MIN)) (PreH3 : (temp_pre <= INT_MAX)) (PreH4 : (temp_pre >= INT_MIN)) (PreH5 : (0 <= temp_pre)) (PreH6 : (structs = (cm_program_structs (p)))) (PreH7 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH8 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH9 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH10 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH11 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH12 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH13 : (offset = (cm_temp_offset (policy) (p) (fid) (temp_pre)))) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_fp_relative_address_code (offset)))) (cons ((TVMInst (TVMStoreOp) (0))) (tail)) )
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "offset" ) )) # Int64  |-> offset)
  **  (cm_function_context_rep fn_pre f body next )
|--
  “ (5 = (tvm_opcode_code (TVMStoreOp))) ”
.

Definition cm_emit_temp_store_partial_solve_wit_3_aux := 
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (offset: Z) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH9 : (offset = (cm_temp_offset (policy) (p) (fid) (temp_pre)))) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_fp_relative_address_code (offset)))) (cons ((TVMInst (TVMStoreOp) (0))) (tail)) )
  **  (cm_function_context_rep fn_pre f body next )
|--
  “ (5 = (tvm_opcode_code (TVMStoreOp))) ” 
  &&  “ (0 <= temp_pre) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX) ” 
  &&  “ (offset = (cm_temp_offset (policy) (p) (fid) (temp_pre))) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_fp_relative_address_code (offset)))) (cons ((TVMInst (TVMStoreOp) (0))) (tail)) )
  **  (cm_function_context_rep fn_pre f body next )
.

Definition cm_emit_temp_store_partial_solve_wit_3 := cm_emit_temp_store_partial_solve_wit_3_pure -> cm_emit_temp_store_partial_solve_wit_3_aux.

(*----- Function cm_emit_temp_load -----*)

Definition cm_emit_temp_load_safety_wit_1 := 
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (offset: Z) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH9 : (offset = (cm_temp_offset (policy) (p) (fid) (temp_pre)))) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_fp_relative_address_code (offset)))) (cons ((TVMInst (TVMLoadOp) (0))) (tail)) )
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "offset" ) )) # Int64  |-> offset)
  **  (cm_function_context_rep fn_pre f body next )
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition cm_emit_temp_load_safety_wit_2 := 
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (offset: Z) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH9 : (offset = (cm_temp_offset (policy) (p) (fid) (temp_pre)))) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_fp_relative_address_code (offset)))) (cons ((TVMInst (TVMLoadOp) (0))) (tail)) )
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "offset" ) )) # Int64  |-> offset)
  **  (cm_function_context_rep fn_pre f body next )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_emit_temp_load_entail_wit_1 := 
(
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_temp_load_code (policy) (p) (fid) (temp_pre))) (tail)) )
|--
  EX (lp: Z)  (pp: Z) ,
  “ (fn_pre <> 0) ” 
  &&  “ (0 <= temp_pre) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX) ” 
  &&  “ ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) = (cm_temp_offset (policy) (p) (fid) (temp_pre))) ” 
  &&  “ ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) <= INT_MAX) ”
  &&  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_temp_load_code (policy) (p) (fid) (temp_pre))) (tail)) )
) \/
(
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_temp_load_code (policy) (p) (fid) (temp_pre))) (tail)) )
|--
  EX (lp: Z)  (pp: Z) ,
  “ (fn_pre <> 0) ” 
  &&  “ (0 <= temp_pre) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX) ” 
  &&  “ ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) = (cm_temp_offset (policy) (p) (fid) (temp_pre))) ” 
  &&  “ ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) <= INT_MAX) ”
  &&  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_temp_load_code (policy) (p) (fid) (temp_pre))) (tail)) )
).

Definition cm_emit_temp_load_entail_wit_2 := 
(
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (pp: Z) (lp: Z) (retval: Z) (PreH1 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH2 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH3 : (0 <= temp_pre)) (PreH4 : ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) <= INT_MAX)) (PreH5 : (retval = (((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ))) (PreH6 : (fn_pre <> 0)) (PreH7 : (0 <= temp_pre)) (PreH8 : (structs = (cm_program_structs (p)))) (PreH9 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH10 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH11 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH12 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH13 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH14 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH15 : ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) = (cm_temp_offset (policy) (p) (fid) (temp_pre)))) (PreH16 : ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) <= INT_MAX)) ,
  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_temp_load_code (policy) (p) (fid) (temp_pre))) (tail)) )
|--
  “ (0 <= temp_pre) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX) ” 
  &&  “ (retval = (cm_temp_offset (policy) (p) (fid) (temp_pre))) ”
  &&  (cm_function_context_rep fn_pre f body next )
  **  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_fp_relative_address_code (retval))) ((cons ((TVMInst (TVMLoadOp) (0))) (tail)))) )
) \/
(
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (pp: Z) (lp: Z) (retval: Z) (PreH1 : ((cm_type_encode ((cm_function_ret (f)))) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_function_ret (f)))) >= INT_MIN)) (PreH3 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH4 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH5 : (0 <= temp_pre)) (PreH6 : ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) <= INT_MAX)) (PreH7 : (retval = (((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ))) (PreH8 : (fn_pre <> 0)) (PreH9 : (0 <= temp_pre)) (PreH10 : (structs = (cm_program_structs (p)))) (PreH11 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH12 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH13 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH14 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH15 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH16 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH17 : ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) = (cm_temp_offset (policy) (p) (fid) (temp_pre)))) (PreH18 : ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) <= INT_MAX)) ,
  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_temp_load_code (policy) (p) (fid) (temp_pre))) (tail)) )
|--
  (cm_function_context_rep fn_pre f body next )
  **  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_fp_relative_address_code (retval))) ((cons ((TVMInst (TVMLoadOp) (0))) (tail)))) )
).

Definition cm_emit_temp_load_entail_wit_2_split_goal_spatial := 
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (pp: Z) (lp: Z) (retval: Z) (PreH1 : ((cm_type_encode ((cm_function_ret (f)))) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_function_ret (f)))) >= INT_MIN)) (PreH3 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH4 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH5 : (0 <= temp_pre)) (PreH6 : ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) <= INT_MAX)) (PreH7 : (retval = (((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ))) (PreH8 : (fn_pre <> 0)) (PreH9 : (0 <= temp_pre)) (PreH10 : (structs = (cm_program_structs (p)))) (PreH11 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH12 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH13 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH14 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH15 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH16 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH17 : ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) = (cm_temp_offset (policy) (p) (fid) (temp_pre)))) (PreH18 : ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) <= INT_MAX)) ,
  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_temp_load_code (policy) (p) (fid) (temp_pre))) (tail)) )
|--
  (cm_function_context_rep fn_pre f body next )
  **  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_fp_relative_address_code (retval))) ((cons ((TVMInst (TVMLoadOp) (0))) (tail)))) )
.

Definition cm_emit_temp_load_return_wit_1 := 
(
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (offset: Z) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH9 : (offset = (cm_temp_offset (policy) (p) (fid) (temp_pre)))) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app (done) ((cm_fp_relative_address_code (offset))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst))))) tail )
  **  (cm_function_context_rep fn_pre f body next )
|--
  “ (0 <= temp_pre) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX) ”
  &&  (cm_function_context_rep fn_pre f body next )
  **  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_temp_load_code (policy) (p) (fid) (temp_pre)))) tail )
) \/
(
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (offset: Z) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH9 : (offset = (cm_temp_offset (policy) (p) (fid) (temp_pre)))) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app (done) ((cm_fp_relative_address_code (offset))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst))))) tail )
  **  (cm_function_context_rep fn_pre f body next )
|--
  (cm_function_context_rep fn_pre f body next )
  **  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_temp_load_code (policy) (p) (fid) (temp_pre)))) tail )
).

Definition cm_emit_temp_load_return_wit_1_split_goal_spatial := 
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (offset: Z) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH9 : (offset = (cm_temp_offset (policy) (p) (fid) (temp_pre)))) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app ((app (done) ((cm_fp_relative_address_code (offset))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst))))) tail )
  **  (cm_function_context_rep fn_pre f body next )
|--
  (cm_function_context_rep fn_pre f body next )
  **  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_temp_load_code (policy) (p) (fid) (temp_pre)))) tail )
.

Definition cm_emit_temp_load_partial_solve_wit_1_pure := 
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (pp: Z) (lp: Z) (PreH1 : (fn_pre <> 0)) (PreH2 : (0 <= temp_pre)) (PreH3 : (structs = (cm_program_structs (p)))) (PreH4 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH5 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH6 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH8 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH9 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH10 : ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) = (cm_temp_offset (policy) (p) (fid) (temp_pre)))) (PreH11 : ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) <= INT_MAX)) ,
  ((( &( "offset" ) )) # Int64  |->_)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_temp_load_code (policy) (p) (fid) (temp_pre))) (tail)) )
|--
  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (0 <= temp_pre) ” 
  &&  “ ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) <= INT_MAX) ”
.

Definition cm_emit_temp_load_partial_solve_wit_1_aux := 
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (pp: Z) (lp: Z) (PreH1 : (fn_pre <> 0)) (PreH2 : (0 <= temp_pre)) (PreH3 : (structs = (cm_program_structs (p)))) (PreH4 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH5 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH6 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH8 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH9 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH10 : ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) = (cm_temp_offset (policy) (p) (fid) (temp_pre)))) (PreH11 : ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) <= INT_MAX)) ,
  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_temp_load_code (policy) (p) (fid) (temp_pre))) (tail)) )
|--
  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (0 <= temp_pre) ” 
  &&  “ ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) <= INT_MAX) ” 
  &&  “ (fn_pre <> 0) ” 
  &&  “ (0 <= temp_pre) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX) ” 
  &&  “ ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) = (cm_temp_offset (policy) (p) (fid) (temp_pre))) ” 
  &&  “ ((((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_members_size ((cm_function_locals (f)))) ) + (8 * temp_pre ) ) <= INT_MAX) ”
  &&  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_temp_load_code (policy) (p) (fid) (temp_pre))) (tail)) )
.

Definition cm_emit_temp_load_partial_solve_wit_1 := cm_emit_temp_load_partial_solve_wit_1_pure -> cm_emit_temp_load_partial_solve_wit_1_aux.

Definition cm_emit_temp_load_partial_solve_wit_2 := 
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (offset: Z) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH9 : (offset = (cm_temp_offset (policy) (p) (fid) (temp_pre)))) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_fp_relative_address_code (offset))) ((cons ((TVMInst (TVMLoadOp) (0))) (tail)))) )
|--
  “ (0 <= temp_pre) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX) ” 
  &&  “ (offset = (cm_temp_offset (policy) (p) (fid) (temp_pre))) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity done (app ((cm_fp_relative_address_code (offset))) ((cons ((TVMInst (TVMLoadOp) (0))) (tail)))) )
  **  (cm_function_context_rep fn_pre f body next )
.

Definition cm_emit_temp_load_partial_solve_wit_3_pure := 
(
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (offset: Z) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH9 : (offset = (cm_temp_offset (policy) (p) (fid) (temp_pre)))) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_fp_relative_address_code (offset)))) (cons ((TVMInst (TVMLoadOp) (0))) (tail)) )
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "offset" ) )) # Int64  |-> offset)
  **  (cm_function_context_rep fn_pre f body next )
|--
  “ (4 = (tvm_opcode_code (TVMLoadOp))) ”
) \/
(
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (offset: Z) (PreH1 : (offset <= INT64_MAX)) (PreH2 : (offset >= INT64_MIN)) (PreH3 : (temp_pre <= INT_MAX)) (PreH4 : (temp_pre >= INT_MIN)) (PreH5 : (0 <= temp_pre)) (PreH6 : (structs = (cm_program_structs (p)))) (PreH7 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH8 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH9 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH10 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH11 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH12 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH13 : (offset = (cm_temp_offset (policy) (p) (fid) (temp_pre)))) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_fp_relative_address_code (offset)))) (cons ((TVMInst (TVMLoadOp) (0))) (tail)) )
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "offset" ) )) # Int64  |-> offset)
  **  (cm_function_context_rep fn_pre f body next )
|--
  “ (4 = (tvm_opcode_code (TVMLoadOp))) ”
).

Definition cm_emit_temp_load_partial_solve_wit_3_pure_split_goal_1 := 
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (offset: Z) (PreH1 : (offset <= INT64_MAX)) (PreH2 : (offset >= INT64_MIN)) (PreH3 : (temp_pre <= INT_MAX)) (PreH4 : (temp_pre >= INT_MIN)) (PreH5 : (0 <= temp_pre)) (PreH6 : (structs = (cm_program_structs (p)))) (PreH7 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH8 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH9 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH10 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH11 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH12 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH13 : (offset = (cm_temp_offset (policy) (p) (fid) (temp_pre)))) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_fp_relative_address_code (offset)))) (cons ((TVMInst (TVMLoadOp) (0))) (tail)) )
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "offset" ) )) # Int64  |-> offset)
  **  (cm_function_context_rep fn_pre f body next )
|--
  “ (4 = (tvm_opcode_code (TVMLoadOp))) ”
.

Definition cm_emit_temp_load_partial_solve_wit_3_aux := 
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (offset: Z) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH9 : (offset = (cm_temp_offset (policy) (p) (fid) (temp_pre)))) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_fp_relative_address_code (offset)))) (cons ((TVMInst (TVMLoadOp) (0))) (tail)) )
  **  (cm_function_context_rep fn_pre f body next )
|--
  “ (4 = (tvm_opcode_code (TVMLoadOp))) ” 
  &&  “ (0 <= temp_pre) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX) ” 
  &&  “ (offset = (cm_temp_offset (policy) (p) (fid) (temp_pre))) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity (app (done) ((cm_fp_relative_address_code (offset)))) (cons ((TVMInst (TVMLoadOp) (0))) (tail)) )
  **  (cm_function_context_rep fn_pre f body next )
.

Definition cm_emit_temp_load_partial_solve_wit_3 := cm_emit_temp_load_partial_solve_wit_3_pure -> cm_emit_temp_load_partial_solve_wit_3_aux.

(*----- Function cmc_binary_opcode -----*)

Definition cmc_binary_opcode_safety_wit_1 := 
forall (op_pre: Z) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition cmc_binary_opcode_safety_wit_2 := 
forall (op_pre: Z) (PreH1 : (op_pre = 2)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
|--
  “ (13 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 13) ”
.

Definition cmc_binary_opcode_safety_wit_3 := 
forall (op_pre: Z) (PreH1 : (op_pre <> 2)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition cmc_binary_opcode_safety_wit_4 := 
forall (op_pre: Z) (PreH1 : (op_pre = 3)) (PreH2 : (op_pre <> 2)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
|--
  “ (14 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 14) ”
.

Definition cmc_binary_opcode_safety_wit_5 := 
forall (op_pre: Z) (PreH1 : (op_pre <> 3)) (PreH2 : (op_pre <> 2)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition cmc_binary_opcode_safety_wit_6 := 
forall (op_pre: Z) (PreH1 : (op_pre = 4)) (PreH2 : (op_pre <> 3)) (PreH3 : (op_pre <> 2)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
|--
  “ (15 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 15) ”
.

Definition cmc_binary_opcode_safety_wit_7 := 
forall (op_pre: Z) (PreH1 : (op_pre <> 4)) (PreH2 : (op_pre <> 3)) (PreH3 : (op_pre <> 2)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
|--
  “ (5 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 5) ”
.

Definition cmc_binary_opcode_safety_wit_8 := 
forall (op_pre: Z) (PreH1 : (op_pre = 5)) (PreH2 : (op_pre <> 4)) (PreH3 : (op_pre <> 3)) (PreH4 : (op_pre <> 2)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
|--
  “ (16 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 16) ”
.

Definition cmc_binary_opcode_safety_wit_9 := 
forall (op_pre: Z) (PreH1 : (op_pre <> 5)) (PreH2 : (op_pre <> 4)) (PreH3 : (op_pre <> 3)) (PreH4 : (op_pre <> 2)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
|--
  “ (6 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 6) ”
.

Definition cmc_binary_opcode_safety_wit_10 := 
forall (op_pre: Z) (PreH1 : (op_pre = 6)) (PreH2 : (op_pre <> 5)) (PreH3 : (op_pre <> 4)) (PreH4 : (op_pre <> 3)) (PreH5 : (op_pre <> 2)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
|--
  “ (17 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 17) ”
.

Definition cmc_binary_opcode_safety_wit_11 := 
forall (op_pre: Z) (PreH1 : (op_pre <> 6)) (PreH2 : (op_pre <> 5)) (PreH3 : (op_pre <> 4)) (PreH4 : (op_pre <> 3)) (PreH5 : (op_pre <> 2)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
|--
  “ (7 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 7) ”
.

Definition cmc_binary_opcode_safety_wit_12 := 
forall (op_pre: Z) (PreH1 : (op_pre = 7)) (PreH2 : (op_pre <> 6)) (PreH3 : (op_pre <> 5)) (PreH4 : (op_pre <> 4)) (PreH5 : (op_pre <> 3)) (PreH6 : (op_pre <> 2)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
|--
  “ (18 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 18) ”
.

Definition cmc_binary_opcode_safety_wit_13 := 
forall (op_pre: Z) (PreH1 : (op_pre <> 7)) (PreH2 : (op_pre <> 6)) (PreH3 : (op_pre <> 5)) (PreH4 : (op_pre <> 4)) (PreH5 : (op_pre <> 3)) (PreH6 : (op_pre <> 2)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition cmc_binary_opcode_safety_wit_14 := 
forall (op_pre: Z) (PreH1 : (op_pre = 8)) (PreH2 : (op_pre <> 7)) (PreH3 : (op_pre <> 6)) (PreH4 : (op_pre <> 5)) (PreH5 : (op_pre <> 4)) (PreH6 : (op_pre <> 3)) (PreH7 : (op_pre <> 2)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition cmc_binary_opcode_safety_wit_15 := 
forall (op_pre: Z) (PreH1 : (op_pre <> 8)) (PreH2 : (op_pre <> 7)) (PreH3 : (op_pre <> 6)) (PreH4 : (op_pre <> 5)) (PreH5 : (op_pre <> 4)) (PreH6 : (op_pre <> 3)) (PreH7 : (op_pre <> 2)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
|--
  “ (9 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 9) ”
.

Definition cmc_binary_opcode_safety_wit_16 := 
forall (op_pre: Z) (PreH1 : (op_pre = 9)) (PreH2 : (op_pre <> 8)) (PreH3 : (op_pre <> 7)) (PreH4 : (op_pre <> 6)) (PreH5 : (op_pre <> 5)) (PreH6 : (op_pre <> 4)) (PreH7 : (op_pre <> 3)) (PreH8 : (op_pre <> 2)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
|--
  “ (9 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 9) ”
.

Definition cmc_binary_opcode_safety_wit_17 := 
forall (op_pre: Z) (PreH1 : (op_pre <> 9)) (PreH2 : (op_pre <> 8)) (PreH3 : (op_pre <> 7)) (PreH4 : (op_pre <> 6)) (PreH5 : (op_pre <> 5)) (PreH6 : (op_pre <> 4)) (PreH7 : (op_pre <> 3)) (PreH8 : (op_pre <> 2)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition cmc_binary_opcode_safety_wit_18 := 
forall (op_pre: Z) (PreH1 : (op_pre = 10)) (PreH2 : (op_pre <> 9)) (PreH3 : (op_pre <> 8)) (PreH4 : (op_pre <> 7)) (PreH5 : (op_pre <> 6)) (PreH6 : (op_pre <> 5)) (PreH7 : (op_pre <> 4)) (PreH8 : (op_pre <> 3)) (PreH9 : (op_pre <> 2)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition cmc_binary_opcode_safety_wit_19 := 
forall (op_pre: Z) (PreH1 : (op_pre <> 10)) (PreH2 : (op_pre <> 9)) (PreH3 : (op_pre <> 8)) (PreH4 : (op_pre <> 7)) (PreH5 : (op_pre <> 6)) (PreH6 : (op_pre <> 5)) (PreH7 : (op_pre <> 4)) (PreH8 : (op_pre <> 3)) (PreH9 : (op_pre <> 2)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
|--
  “ (11 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 11) ”
.

Definition cmc_binary_opcode_safety_wit_20 := 
forall (op_pre: Z) (PreH1 : (op_pre = 11)) (PreH2 : (op_pre <> 10)) (PreH3 : (op_pre <> 9)) (PreH4 : (op_pre <> 8)) (PreH5 : (op_pre <> 7)) (PreH6 : (op_pre <> 6)) (PreH7 : (op_pre <> 5)) (PreH8 : (op_pre <> 4)) (PreH9 : (op_pre <> 3)) (PreH10 : (op_pre <> 2)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
|--
  “ (11 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 11) ”
.

Definition cmc_binary_opcode_safety_wit_21 := 
forall (op_pre: Z) (PreH1 : (op_pre <> 11)) (PreH2 : (op_pre <> 10)) (PreH3 : (op_pre <> 9)) (PreH4 : (op_pre <> 8)) (PreH5 : (op_pre <> 7)) (PreH6 : (op_pre <> 6)) (PreH7 : (op_pre <> 5)) (PreH8 : (op_pre <> 4)) (PreH9 : (op_pre <> 3)) (PreH10 : (op_pre <> 2)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
|--
  “ (12 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 12) ”
.

Definition cmc_binary_opcode_return_wit_1 := 
(
forall (op_pre: Z) (PreH1 : (op_pre = 2)) ,
  TT && emp 
|--
  “ (13 = (tvm_opcode_code ((cm_binary_opcode (op_pre))))) ” 
  &&  “ (13 <> 22) ”
  &&  emp
) \/
(
forall (op_pre: Z) (PreH1 : (op_pre = 2)) ,
  TT && emp 
|--
  “ (13 = (tvm_opcode_code ((cm_binary_opcode (2))))) ”
  &&  emp
).

Definition cmc_binary_opcode_return_wit_1_split_goal_1 := 
forall (op_pre: Z) (PreH1 : (op_pre = 2)) ,
  (13 = (tvm_opcode_code ((cm_binary_opcode (2)))))
.

Definition cmc_binary_opcode_return_wit_2 := 
(
forall (op_pre: Z) (PreH1 : (op_pre = 3)) (PreH2 : (op_pre <> 2)) ,
  TT && emp 
|--
  “ (14 = (tvm_opcode_code ((cm_binary_opcode (op_pre))))) ” 
  &&  “ (14 <> 22) ”
  &&  emp
) \/
(
forall (op_pre: Z) (PreH1 : (op_pre = 3)) (PreH2 : (op_pre <> 2)) ,
  TT && emp 
|--
  “ (14 = (tvm_opcode_code ((cm_binary_opcode (3))))) ”
  &&  emp
).

Definition cmc_binary_opcode_return_wit_2_split_goal_1 := 
forall (op_pre: Z) (PreH1 : (op_pre = 3)) (PreH2 : (op_pre <> 2)) ,
  (14 = (tvm_opcode_code ((cm_binary_opcode (3)))))
.

Definition cmc_binary_opcode_return_wit_3 := 
(
forall (op_pre: Z) (PreH1 : (op_pre = 4)) (PreH2 : (op_pre <> 3)) (PreH3 : (op_pre <> 2)) ,
  TT && emp 
|--
  “ (15 = (tvm_opcode_code ((cm_binary_opcode (op_pre))))) ” 
  &&  “ (15 <> 22) ”
  &&  emp
) \/
(
forall (op_pre: Z) (PreH1 : (op_pre = 4)) (PreH2 : (op_pre <> 3)) (PreH3 : (op_pre <> 2)) ,
  TT && emp 
|--
  “ (15 = (tvm_opcode_code ((cm_binary_opcode (4))))) ”
  &&  emp
).

Definition cmc_binary_opcode_return_wit_3_split_goal_1 := 
forall (op_pre: Z) (PreH1 : (op_pre = 4)) (PreH2 : (op_pre <> 3)) (PreH3 : (op_pre <> 2)) ,
  (15 = (tvm_opcode_code ((cm_binary_opcode (4)))))
.

Definition cmc_binary_opcode_return_wit_4 := 
(
forall (op_pre: Z) (PreH1 : (op_pre = 5)) (PreH2 : (op_pre <> 4)) (PreH3 : (op_pre <> 3)) (PreH4 : (op_pre <> 2)) ,
  TT && emp 
|--
  “ (16 = (tvm_opcode_code ((cm_binary_opcode (op_pre))))) ” 
  &&  “ (16 <> 22) ”
  &&  emp
) \/
(
forall (op_pre: Z) (PreH1 : (op_pre = 5)) (PreH2 : (op_pre <> 4)) (PreH3 : (op_pre <> 3)) (PreH4 : (op_pre <> 2)) ,
  TT && emp 
|--
  “ (16 = (tvm_opcode_code ((cm_binary_opcode (5))))) ”
  &&  emp
).

Definition cmc_binary_opcode_return_wit_4_split_goal_1 := 
forall (op_pre: Z) (PreH1 : (op_pre = 5)) (PreH2 : (op_pre <> 4)) (PreH3 : (op_pre <> 3)) (PreH4 : (op_pre <> 2)) ,
  (16 = (tvm_opcode_code ((cm_binary_opcode (5)))))
.

Definition cmc_binary_opcode_return_wit_5 := 
(
forall (op_pre: Z) (PreH1 : (op_pre = 6)) (PreH2 : (op_pre <> 5)) (PreH3 : (op_pre <> 4)) (PreH4 : (op_pre <> 3)) (PreH5 : (op_pre <> 2)) ,
  TT && emp 
|--
  “ (17 = (tvm_opcode_code ((cm_binary_opcode (op_pre))))) ” 
  &&  “ (17 <> 22) ”
  &&  emp
) \/
(
forall (op_pre: Z) (PreH1 : (op_pre = 6)) (PreH2 : (op_pre <> 5)) (PreH3 : (op_pre <> 4)) (PreH4 : (op_pre <> 3)) (PreH5 : (op_pre <> 2)) ,
  TT && emp 
|--
  “ (17 = (tvm_opcode_code ((cm_binary_opcode (6))))) ”
  &&  emp
).

Definition cmc_binary_opcode_return_wit_5_split_goal_1 := 
forall (op_pre: Z) (PreH1 : (op_pre = 6)) (PreH2 : (op_pre <> 5)) (PreH3 : (op_pre <> 4)) (PreH4 : (op_pre <> 3)) (PreH5 : (op_pre <> 2)) ,
  (17 = (tvm_opcode_code ((cm_binary_opcode (6)))))
.

Definition cmc_binary_opcode_return_wit_6 := 
(
forall (op_pre: Z) (PreH1 : (op_pre = 7)) (PreH2 : (op_pre <> 6)) (PreH3 : (op_pre <> 5)) (PreH4 : (op_pre <> 4)) (PreH5 : (op_pre <> 3)) (PreH6 : (op_pre <> 2)) ,
  TT && emp 
|--
  “ (18 = (tvm_opcode_code ((cm_binary_opcode (op_pre))))) ” 
  &&  “ (18 <> 22) ”
  &&  emp
) \/
(
forall (op_pre: Z) (PreH1 : (op_pre = 7)) (PreH2 : (op_pre <> 6)) (PreH3 : (op_pre <> 5)) (PreH4 : (op_pre <> 4)) (PreH5 : (op_pre <> 3)) (PreH6 : (op_pre <> 2)) ,
  TT && emp 
|--
  “ (18 = (tvm_opcode_code ((cm_binary_opcode (7))))) ”
  &&  emp
).

Definition cmc_binary_opcode_return_wit_6_split_goal_1 := 
forall (op_pre: Z) (PreH1 : (op_pre = 7)) (PreH2 : (op_pre <> 6)) (PreH3 : (op_pre <> 5)) (PreH4 : (op_pre <> 4)) (PreH5 : (op_pre <> 3)) (PreH6 : (op_pre <> 2)) ,
  (18 = (tvm_opcode_code ((cm_binary_opcode (7)))))
.

Definition cmc_binary_opcode_return_wit_7 := 
(
forall (op_pre: Z) (PreH1 : (op_pre = 8)) (PreH2 : (op_pre <> 7)) (PreH3 : (op_pre <> 6)) (PreH4 : (op_pre <> 5)) (PreH5 : (op_pre <> 4)) (PreH6 : (op_pre <> 3)) (PreH7 : (op_pre <> 2)) ,
  TT && emp 
|--
  “ (8 = (tvm_opcode_code ((cm_binary_opcode (op_pre))))) ” 
  &&  “ (8 <> 22) ”
  &&  emp
) \/
(
forall (op_pre: Z) (PreH1 : (op_pre = 8)) (PreH2 : (op_pre <> 7)) (PreH3 : (op_pre <> 6)) (PreH4 : (op_pre <> 5)) (PreH5 : (op_pre <> 4)) (PreH6 : (op_pre <> 3)) (PreH7 : (op_pre <> 2)) ,
  TT && emp 
|--
  “ (8 = (tvm_opcode_code ((cm_binary_opcode (8))))) ”
  &&  emp
).

Definition cmc_binary_opcode_return_wit_7_split_goal_1 := 
forall (op_pre: Z) (PreH1 : (op_pre = 8)) (PreH2 : (op_pre <> 7)) (PreH3 : (op_pre <> 6)) (PreH4 : (op_pre <> 5)) (PreH5 : (op_pre <> 4)) (PreH6 : (op_pre <> 3)) (PreH7 : (op_pre <> 2)) ,
  (8 = (tvm_opcode_code ((cm_binary_opcode (8)))))
.

Definition cmc_binary_opcode_return_wit_8 := 
(
forall (op_pre: Z) (PreH1 : (op_pre = 9)) (PreH2 : (op_pre <> 8)) (PreH3 : (op_pre <> 7)) (PreH4 : (op_pre <> 6)) (PreH5 : (op_pre <> 5)) (PreH6 : (op_pre <> 4)) (PreH7 : (op_pre <> 3)) (PreH8 : (op_pre <> 2)) ,
  TT && emp 
|--
  “ (9 = (tvm_opcode_code ((cm_binary_opcode (op_pre))))) ” 
  &&  “ (9 <> 22) ”
  &&  emp
) \/
(
forall (op_pre: Z) (PreH1 : (op_pre = 9)) (PreH2 : (op_pre <> 8)) (PreH3 : (op_pre <> 7)) (PreH4 : (op_pre <> 6)) (PreH5 : (op_pre <> 5)) (PreH6 : (op_pre <> 4)) (PreH7 : (op_pre <> 3)) (PreH8 : (op_pre <> 2)) ,
  TT && emp 
|--
  “ (9 = (tvm_opcode_code ((cm_binary_opcode (9))))) ”
  &&  emp
).

Definition cmc_binary_opcode_return_wit_8_split_goal_1 := 
forall (op_pre: Z) (PreH1 : (op_pre = 9)) (PreH2 : (op_pre <> 8)) (PreH3 : (op_pre <> 7)) (PreH4 : (op_pre <> 6)) (PreH5 : (op_pre <> 5)) (PreH6 : (op_pre <> 4)) (PreH7 : (op_pre <> 3)) (PreH8 : (op_pre <> 2)) ,
  (9 = (tvm_opcode_code ((cm_binary_opcode (9)))))
.

Definition cmc_binary_opcode_return_wit_9 := 
(
forall (op_pre: Z) (PreH1 : (op_pre = 10)) (PreH2 : (op_pre <> 9)) (PreH3 : (op_pre <> 8)) (PreH4 : (op_pre <> 7)) (PreH5 : (op_pre <> 6)) (PreH6 : (op_pre <> 5)) (PreH7 : (op_pre <> 4)) (PreH8 : (op_pre <> 3)) (PreH9 : (op_pre <> 2)) ,
  TT && emp 
|--
  “ (10 = (tvm_opcode_code ((cm_binary_opcode (op_pre))))) ” 
  &&  “ (10 <> 22) ”
  &&  emp
) \/
(
forall (op_pre: Z) (PreH1 : (op_pre = 10)) (PreH2 : (op_pre <> 9)) (PreH3 : (op_pre <> 8)) (PreH4 : (op_pre <> 7)) (PreH5 : (op_pre <> 6)) (PreH6 : (op_pre <> 5)) (PreH7 : (op_pre <> 4)) (PreH8 : (op_pre <> 3)) (PreH9 : (op_pre <> 2)) ,
  TT && emp 
|--
  “ (10 = (tvm_opcode_code ((cm_binary_opcode (10))))) ”
  &&  emp
).

Definition cmc_binary_opcode_return_wit_9_split_goal_1 := 
forall (op_pre: Z) (PreH1 : (op_pre = 10)) (PreH2 : (op_pre <> 9)) (PreH3 : (op_pre <> 8)) (PreH4 : (op_pre <> 7)) (PreH5 : (op_pre <> 6)) (PreH6 : (op_pre <> 5)) (PreH7 : (op_pre <> 4)) (PreH8 : (op_pre <> 3)) (PreH9 : (op_pre <> 2)) ,
  (10 = (tvm_opcode_code ((cm_binary_opcode (10)))))
.

Definition cmc_binary_opcode_return_wit_10 := 
(
forall (op_pre: Z) (PreH1 : (op_pre = 11)) (PreH2 : (op_pre <> 10)) (PreH3 : (op_pre <> 9)) (PreH4 : (op_pre <> 8)) (PreH5 : (op_pre <> 7)) (PreH6 : (op_pre <> 6)) (PreH7 : (op_pre <> 5)) (PreH8 : (op_pre <> 4)) (PreH9 : (op_pre <> 3)) (PreH10 : (op_pre <> 2)) ,
  TT && emp 
|--
  “ (11 = (tvm_opcode_code ((cm_binary_opcode (op_pre))))) ” 
  &&  “ (11 <> 22) ”
  &&  emp
) \/
(
forall (op_pre: Z) (PreH1 : (op_pre = 11)) (PreH2 : (op_pre <> 10)) (PreH3 : (op_pre <> 9)) (PreH4 : (op_pre <> 8)) (PreH5 : (op_pre <> 7)) (PreH6 : (op_pre <> 6)) (PreH7 : (op_pre <> 5)) (PreH8 : (op_pre <> 4)) (PreH9 : (op_pre <> 3)) (PreH10 : (op_pre <> 2)) ,
  TT && emp 
|--
  “ (11 = (tvm_opcode_code ((cm_binary_opcode (11))))) ”
  &&  emp
).

Definition cmc_binary_opcode_return_wit_10_split_goal_1 := 
forall (op_pre: Z) (PreH1 : (op_pre = 11)) (PreH2 : (op_pre <> 10)) (PreH3 : (op_pre <> 9)) (PreH4 : (op_pre <> 8)) (PreH5 : (op_pre <> 7)) (PreH6 : (op_pre <> 6)) (PreH7 : (op_pre <> 5)) (PreH8 : (op_pre <> 4)) (PreH9 : (op_pre <> 3)) (PreH10 : (op_pre <> 2)) ,
  (11 = (tvm_opcode_code ((cm_binary_opcode (11)))))
.

Definition cmc_binary_opcode_return_wit_11 := 
(
forall (op_pre: Z) (PreH1 : (op_pre <> 11)) (PreH2 : (op_pre <> 10)) (PreH3 : (op_pre <> 9)) (PreH4 : (op_pre <> 8)) (PreH5 : (op_pre <> 7)) (PreH6 : (op_pre <> 6)) (PreH7 : (op_pre <> 5)) (PreH8 : (op_pre <> 4)) (PreH9 : (op_pre <> 3)) (PreH10 : (op_pre <> 2)) ,
  TT && emp 
|--
  “ (12 = (tvm_opcode_code ((cm_binary_opcode (op_pre))))) ” 
  &&  “ (12 <> 22) ”
  &&  emp
) \/
(
forall (op_pre: Z) (PreH1 : (op_pre <> 11)) (PreH2 : (op_pre <> 10)) (PreH3 : (op_pre <> 9)) (PreH4 : (op_pre <> 8)) (PreH5 : (op_pre <> 7)) (PreH6 : (op_pre <> 6)) (PreH7 : (op_pre <> 5)) (PreH8 : (op_pre <> 4)) (PreH9 : (op_pre <> 3)) (PreH10 : (op_pre <> 2)) ,
  TT && emp 
|--
  “ (12 = (tvm_opcode_code ((cm_binary_opcode (op_pre))))) ”
  &&  emp
).

Definition cmc_binary_opcode_return_wit_11_split_goal_1 := 
forall (op_pre: Z) (PreH1 : (op_pre <> 11)) (PreH2 : (op_pre <> 10)) (PreH3 : (op_pre <> 9)) (PreH4 : (op_pre <> 8)) (PreH5 : (op_pre <> 7)) (PreH6 : (op_pre <> 6)) (PreH7 : (op_pre <> 5)) (PreH8 : (op_pre <> 4)) (PreH9 : (op_pre <> 3)) (PreH10 : (op_pre <> 2)) ,
  (12 = (tvm_opcode_code ((cm_binary_opcode (op_pre)))))
.

Module Type VC_Correct.


Axiom proof_of_cm_emit_raw_safety_wit_1 : cm_emit_raw_safety_wit_1.
Axiom proof_of_cm_emit_raw_safety_wit_2 : cm_emit_raw_safety_wit_2.
Axiom proof_of_cm_emit_raw_entail_wit_1 : cm_emit_raw_entail_wit_1.
Axiom proof_of_cm_emit_raw_return_wit_1 : cm_emit_raw_return_wit_1.
Axiom proof_of_cm_emit_raw_partial_solve_wit_1 : cm_emit_raw_partial_solve_wit_1.
Axiom proof_of_cm_emit_raw_partial_solve_wit_2 : cm_emit_raw_partial_solve_wit_2.
Axiom proof_of_cm_emit_entail_wit_1 : cm_emit_entail_wit_1.
Axiom proof_of_cm_emit_return_wit_1 : cm_emit_return_wit_1.
Axiom proof_of_cm_emit_partial_solve_wit_1_pure : cm_emit_partial_solve_wit_1_pure.
Axiom proof_of_cm_emit_partial_solve_wit_1 : cm_emit_partial_solve_wit_1.
Axiom proof_of_cm_emit_normalize_safety_wit_1 : cm_emit_normalize_safety_wit_1.
Axiom proof_of_cm_emit_normalize_safety_wit_2 : cm_emit_normalize_safety_wit_2.
Axiom proof_of_cm_emit_normalize_safety_wit_3 : cm_emit_normalize_safety_wit_3.
Axiom proof_of_cm_emit_normalize_safety_wit_4 : cm_emit_normalize_safety_wit_4.
Axiom proof_of_cm_emit_normalize_safety_wit_5 : cm_emit_normalize_safety_wit_5.
Axiom proof_of_cm_emit_normalize_safety_wit_6 : cm_emit_normalize_safety_wit_6.
Axiom proof_of_cm_emit_normalize_safety_wit_7 : cm_emit_normalize_safety_wit_7.
Axiom proof_of_cm_emit_normalize_safety_wit_8 : cm_emit_normalize_safety_wit_8.
Axiom proof_of_cm_emit_normalize_safety_wit_9 : cm_emit_normalize_safety_wit_9.
Axiom proof_of_cm_emit_normalize_safety_wit_10 : cm_emit_normalize_safety_wit_10.
Axiom proof_of_cm_emit_normalize_safety_wit_11 : cm_emit_normalize_safety_wit_11.
Axiom proof_of_cm_emit_normalize_safety_wit_12 : cm_emit_normalize_safety_wit_12.
Axiom proof_of_cm_emit_normalize_safety_wit_13 : cm_emit_normalize_safety_wit_13.
Axiom proof_of_cm_emit_normalize_entail_wit_1 : cm_emit_normalize_entail_wit_1.
Axiom proof_of_cm_emit_normalize_return_wit_1 : cm_emit_normalize_return_wit_1.
Axiom proof_of_cm_emit_normalize_return_wit_2 : cm_emit_normalize_return_wit_2.
Axiom proof_of_cm_emit_normalize_partial_solve_wit_1_pure : cm_emit_normalize_partial_solve_wit_1_pure.
Axiom proof_of_cm_emit_normalize_partial_solve_wit_1 : cm_emit_normalize_partial_solve_wit_1.
Axiom proof_of_cm_emit_normalize_partial_solve_wit_2_pure : cm_emit_normalize_partial_solve_wit_2_pure.
Axiom proof_of_cm_emit_normalize_partial_solve_wit_2 : cm_emit_normalize_partial_solve_wit_2.
Axiom proof_of_cm_emit_normalize_partial_solve_wit_3_pure : cm_emit_normalize_partial_solve_wit_3_pure.
Axiom proof_of_cm_emit_normalize_partial_solve_wit_3 : cm_emit_normalize_partial_solve_wit_3.
Axiom proof_of_cm_emit_normalize_partial_solve_wit_4_pure : cm_emit_normalize_partial_solve_wit_4_pure.
Axiom proof_of_cm_emit_normalize_partial_solve_wit_4 : cm_emit_normalize_partial_solve_wit_4.
Axiom proof_of_cm_emit_normalize_partial_solve_wit_5_pure : cm_emit_normalize_partial_solve_wit_5_pure.
Axiom proof_of_cm_emit_normalize_partial_solve_wit_5 : cm_emit_normalize_partial_solve_wit_5.
Axiom proof_of_cm_emit_normalize_partial_solve_wit_6_pure : cm_emit_normalize_partial_solve_wit_6_pure.
Axiom proof_of_cm_emit_normalize_partial_solve_wit_6 : cm_emit_normalize_partial_solve_wit_6.
Axiom proof_of_cm_emit_load_safety_wit_1 : cm_emit_load_safety_wit_1.
Axiom proof_of_cm_emit_load_safety_wit_2 : cm_emit_load_safety_wit_2.
Axiom proof_of_cm_emit_load_safety_wit_3 : cm_emit_load_safety_wit_3.
Axiom proof_of_cm_emit_load_safety_wit_4 : cm_emit_load_safety_wit_4.
Axiom proof_of_cm_emit_load_safety_wit_5 : cm_emit_load_safety_wit_5.
Axiom proof_of_cm_emit_load_entail_wit_1 : cm_emit_load_entail_wit_1.
Axiom proof_of_cm_emit_load_entail_wit_2 : cm_emit_load_entail_wit_2.
Axiom proof_of_cm_emit_load_return_wit_1 : cm_emit_load_return_wit_1.
Axiom proof_of_cm_emit_load_return_wit_2 : cm_emit_load_return_wit_2.
Axiom proof_of_cm_emit_load_partial_solve_wit_1_pure : cm_emit_load_partial_solve_wit_1_pure.
Axiom proof_of_cm_emit_load_partial_solve_wit_1 : cm_emit_load_partial_solve_wit_1.
Axiom proof_of_cm_emit_load_partial_solve_wit_2_pure : cm_emit_load_partial_solve_wit_2_pure.
Axiom proof_of_cm_emit_load_partial_solve_wit_2 : cm_emit_load_partial_solve_wit_2.
Axiom proof_of_cm_emit_store_safety_wit_1 : cm_emit_store_safety_wit_1.
Axiom proof_of_cm_emit_store_safety_wit_2 : cm_emit_store_safety_wit_2.
Axiom proof_of_cm_emit_store_safety_wit_3 : cm_emit_store_safety_wit_3.
Axiom proof_of_cm_emit_store_safety_wit_4 : cm_emit_store_safety_wit_4.
Axiom proof_of_cm_emit_store_safety_wit_5 : cm_emit_store_safety_wit_5.
Axiom proof_of_cm_emit_store_entail_wit_1 : cm_emit_store_entail_wit_1.
Axiom proof_of_cm_emit_store_entail_wit_2 : cm_emit_store_entail_wit_2.
Axiom proof_of_cm_emit_store_return_wit_1 : cm_emit_store_return_wit_1.
Axiom proof_of_cm_emit_store_return_wit_2 : cm_emit_store_return_wit_2.
Axiom proof_of_cm_emit_store_partial_solve_wit_1_pure : cm_emit_store_partial_solve_wit_1_pure.
Axiom proof_of_cm_emit_store_partial_solve_wit_1 : cm_emit_store_partial_solve_wit_1.
Axiom proof_of_cm_emit_store_partial_solve_wit_2_pure : cm_emit_store_partial_solve_wit_2_pure.
Axiom proof_of_cm_emit_store_partial_solve_wit_2 : cm_emit_store_partial_solve_wit_2.
Axiom proof_of_cm_emit_fp_address_safety_wit_1 : cm_emit_fp_address_safety_wit_1.
Axiom proof_of_cm_emit_fp_address_safety_wit_2 : cm_emit_fp_address_safety_wit_2.
Axiom proof_of_cm_emit_fp_address_safety_wit_3 : cm_emit_fp_address_safety_wit_3.
Axiom proof_of_cm_emit_fp_address_safety_wit_4 : cm_emit_fp_address_safety_wit_4.
Axiom proof_of_cm_emit_fp_address_safety_wit_5 : cm_emit_fp_address_safety_wit_5.
Axiom proof_of_cm_emit_fp_address_safety_wit_6 : cm_emit_fp_address_safety_wit_6.
Axiom proof_of_cm_emit_fp_address_safety_wit_7 : cm_emit_fp_address_safety_wit_7.
Axiom proof_of_cm_emit_fp_address_entail_wit_1 : cm_emit_fp_address_entail_wit_1.
Axiom proof_of_cm_emit_fp_address_return_wit_1 : cm_emit_fp_address_return_wit_1.
Axiom proof_of_cm_emit_fp_address_partial_solve_wit_1_pure : cm_emit_fp_address_partial_solve_wit_1_pure.
Axiom proof_of_cm_emit_fp_address_partial_solve_wit_1 : cm_emit_fp_address_partial_solve_wit_1.
Axiom proof_of_cm_emit_fp_address_partial_solve_wit_2_pure : cm_emit_fp_address_partial_solve_wit_2_pure.
Axiom proof_of_cm_emit_fp_address_partial_solve_wit_2 : cm_emit_fp_address_partial_solve_wit_2.
Axiom proof_of_cm_emit_fp_address_partial_solve_wit_3_pure : cm_emit_fp_address_partial_solve_wit_3_pure.
Axiom proof_of_cm_emit_fp_address_partial_solve_wit_3 : cm_emit_fp_address_partial_solve_wit_3.
Axiom proof_of_cm_emit_fp_address_partial_solve_wit_4_pure : cm_emit_fp_address_partial_solve_wit_4_pure.
Axiom proof_of_cm_emit_fp_address_partial_solve_wit_4 : cm_emit_fp_address_partial_solve_wit_4.
Axiom proof_of_cm_emit_temp_store_safety_wit_1 : cm_emit_temp_store_safety_wit_1.
Axiom proof_of_cm_emit_temp_store_safety_wit_2 : cm_emit_temp_store_safety_wit_2.
Axiom proof_of_cm_emit_temp_store_entail_wit_1 : cm_emit_temp_store_entail_wit_1.
Axiom proof_of_cm_emit_temp_store_entail_wit_2 : cm_emit_temp_store_entail_wit_2.
Axiom proof_of_cm_emit_temp_store_return_wit_1 : cm_emit_temp_store_return_wit_1.
Axiom proof_of_cm_emit_temp_store_partial_solve_wit_1_pure : cm_emit_temp_store_partial_solve_wit_1_pure.
Axiom proof_of_cm_emit_temp_store_partial_solve_wit_1 : cm_emit_temp_store_partial_solve_wit_1.
Axiom proof_of_cm_emit_temp_store_partial_solve_wit_2 : cm_emit_temp_store_partial_solve_wit_2.
Axiom proof_of_cm_emit_temp_store_partial_solve_wit_3_pure : cm_emit_temp_store_partial_solve_wit_3_pure.
Axiom proof_of_cm_emit_temp_store_partial_solve_wit_3 : cm_emit_temp_store_partial_solve_wit_3.
Axiom proof_of_cm_emit_temp_load_safety_wit_1 : cm_emit_temp_load_safety_wit_1.
Axiom proof_of_cm_emit_temp_load_safety_wit_2 : cm_emit_temp_load_safety_wit_2.
Axiom proof_of_cm_emit_temp_load_entail_wit_1 : cm_emit_temp_load_entail_wit_1.
Axiom proof_of_cm_emit_temp_load_entail_wit_2 : cm_emit_temp_load_entail_wit_2.
Axiom proof_of_cm_emit_temp_load_return_wit_1 : cm_emit_temp_load_return_wit_1.
Axiom proof_of_cm_emit_temp_load_partial_solve_wit_1_pure : cm_emit_temp_load_partial_solve_wit_1_pure.
Axiom proof_of_cm_emit_temp_load_partial_solve_wit_1 : cm_emit_temp_load_partial_solve_wit_1.
Axiom proof_of_cm_emit_temp_load_partial_solve_wit_2 : cm_emit_temp_load_partial_solve_wit_2.
Axiom proof_of_cm_emit_temp_load_partial_solve_wit_3_pure : cm_emit_temp_load_partial_solve_wit_3_pure.
Axiom proof_of_cm_emit_temp_load_partial_solve_wit_3 : cm_emit_temp_load_partial_solve_wit_3.
Axiom proof_of_cmc_binary_opcode_safety_wit_1 : cmc_binary_opcode_safety_wit_1.
Axiom proof_of_cmc_binary_opcode_safety_wit_2 : cmc_binary_opcode_safety_wit_2.
Axiom proof_of_cmc_binary_opcode_safety_wit_3 : cmc_binary_opcode_safety_wit_3.
Axiom proof_of_cmc_binary_opcode_safety_wit_4 : cmc_binary_opcode_safety_wit_4.
Axiom proof_of_cmc_binary_opcode_safety_wit_5 : cmc_binary_opcode_safety_wit_5.
Axiom proof_of_cmc_binary_opcode_safety_wit_6 : cmc_binary_opcode_safety_wit_6.
Axiom proof_of_cmc_binary_opcode_safety_wit_7 : cmc_binary_opcode_safety_wit_7.
Axiom proof_of_cmc_binary_opcode_safety_wit_8 : cmc_binary_opcode_safety_wit_8.
Axiom proof_of_cmc_binary_opcode_safety_wit_9 : cmc_binary_opcode_safety_wit_9.
Axiom proof_of_cmc_binary_opcode_safety_wit_10 : cmc_binary_opcode_safety_wit_10.
Axiom proof_of_cmc_binary_opcode_safety_wit_11 : cmc_binary_opcode_safety_wit_11.
Axiom proof_of_cmc_binary_opcode_safety_wit_12 : cmc_binary_opcode_safety_wit_12.
Axiom proof_of_cmc_binary_opcode_safety_wit_13 : cmc_binary_opcode_safety_wit_13.
Axiom proof_of_cmc_binary_opcode_safety_wit_14 : cmc_binary_opcode_safety_wit_14.
Axiom proof_of_cmc_binary_opcode_safety_wit_15 : cmc_binary_opcode_safety_wit_15.
Axiom proof_of_cmc_binary_opcode_safety_wit_16 : cmc_binary_opcode_safety_wit_16.
Axiom proof_of_cmc_binary_opcode_safety_wit_17 : cmc_binary_opcode_safety_wit_17.
Axiom proof_of_cmc_binary_opcode_safety_wit_18 : cmc_binary_opcode_safety_wit_18.
Axiom proof_of_cmc_binary_opcode_safety_wit_19 : cmc_binary_opcode_safety_wit_19.
Axiom proof_of_cmc_binary_opcode_safety_wit_20 : cmc_binary_opcode_safety_wit_20.
Axiom proof_of_cmc_binary_opcode_safety_wit_21 : cmc_binary_opcode_safety_wit_21.
Axiom proof_of_cmc_binary_opcode_return_wit_1 : cmc_binary_opcode_return_wit_1.
Axiom proof_of_cmc_binary_opcode_return_wit_2 : cmc_binary_opcode_return_wit_2.
Axiom proof_of_cmc_binary_opcode_return_wit_3 : cmc_binary_opcode_return_wit_3.
Axiom proof_of_cmc_binary_opcode_return_wit_4 : cmc_binary_opcode_return_wit_4.
Axiom proof_of_cmc_binary_opcode_return_wit_5 : cmc_binary_opcode_return_wit_5.
Axiom proof_of_cmc_binary_opcode_return_wit_6 : cmc_binary_opcode_return_wit_6.
Axiom proof_of_cmc_binary_opcode_return_wit_7 : cmc_binary_opcode_return_wit_7.
Axiom proof_of_cmc_binary_opcode_return_wit_8 : cmc_binary_opcode_return_wit_8.
Axiom proof_of_cmc_binary_opcode_return_wit_9 : cmc_binary_opcode_return_wit_9.
Axiom proof_of_cmc_binary_opcode_return_wit_10 : cmc_binary_opcode_return_wit_10.
Axiom proof_of_cmc_binary_opcode_return_wit_11 : cmc_binary_opcode_return_wit_11.

End VC_Correct.
