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
Require Import SimpleC.EE.QCP_demos_human.cmc_emit_plan_migration_lib.
Local Open Scope sac.

(*----- Function cm_emit_plan -----*)

Definition cm_emit_plan_entail_wit_1 := 
(
forall (immediate_pre: Z) (op_pre: Z) (emitter_pre: Z) (opcode: tvm_opcode) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (op_pre = (tvm_opcode_code (opcode)))) (PreH2 : ((tvm_opcode_code (opcode)) <> 22)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (opcode) (immediate_pre))) (tail)) )
|--
  “ (((Zlength ((app (done) ((cons ((TVMInst (opcode) (immediate_pre))) ((@nil tvm_inst))))))) + (Zlength (tail)) ) <= capacity) ” 
  &&  “ (op_pre = (tvm_opcode_code (opcode))) ” 
  &&  “ ((tvm_opcode_code (opcode)) <> 22) ” 
  &&  “ (((Zlength (done)) + 1 ) <= capacity) ”
  &&  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
) \/
(
forall (immediate_pre: Z) (op_pre: Z) (emitter_pre: Z) (opcode: tvm_opcode) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (op_pre = (tvm_opcode_code (opcode)))) (PreH2 : ((tvm_opcode_code (opcode)) <> 22)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (opcode) (immediate_pre))) (tail)) )
|--
  “ (((Zlength (done)) + 1 ) <= capacity) ” 
  &&  “ (((Zlength ((app (done) ((cons ((TVMInst (opcode) (immediate_pre))) ((@nil tvm_inst))))))) + (Zlength (tail)) ) <= capacity) ”
  &&  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
).

Definition cm_emit_plan_entail_wit_1_split_goal_1 := 
forall (immediate_pre: Z) (op_pre: Z) (emitter_pre: Z) (opcode: tvm_opcode) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (op_pre = (tvm_opcode_code (opcode)))) (PreH2 : ((tvm_opcode_code (opcode)) <> 22)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (opcode) (immediate_pre))) (tail)) )
|--
  “ (((Zlength (done)) + 1 ) <= capacity) ”
.

Definition cm_emit_plan_entail_wit_1_split_goal_2 := 
forall (immediate_pre: Z) (op_pre: Z) (emitter_pre: Z) (opcode: tvm_opcode) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (op_pre = (tvm_opcode_code (opcode)))) (PreH2 : ((tvm_opcode_code (opcode)) <> 22)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (opcode) (immediate_pre))) (tail)) )
|--
  “ (((Zlength ((app (done) ((cons ((TVMInst (opcode) (immediate_pre))) ((@nil tvm_inst))))))) + (Zlength (tail)) ) <= capacity) ”
.

Definition cm_emit_plan_entail_wit_1_split_goal_spatial := 
forall (immediate_pre: Z) (op_pre: Z) (emitter_pre: Z) (opcode: tvm_opcode) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (op_pre = (tvm_opcode_code (opcode)))) (PreH2 : ((tvm_opcode_code (opcode)) <> 22)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (opcode) (immediate_pre))) (tail)) )
|--
  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
.

Definition cm_emit_plan_return_wit_1 := 
(
forall (immediate_pre: Z) (op_pre: Z) (emitter_pre: Z) (opcode: tvm_opcode) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (((Zlength ((app (done) ((cons ((TVMInst (opcode) (immediate_pre))) ((@nil tvm_inst))))))) + (Zlength (tail)) ) <= capacity)) (PreH2 : (op_pre = (tvm_opcode_code (opcode)))) (PreH3 : ((tvm_opcode_code (opcode)) <> 22)) (PreH4 : (((Zlength (done)) + 1 ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (opcode) (immediate_pre))) ((@nil tvm_inst))))) )
|--
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (opcode) (immediate_pre))) ((@nil tvm_inst))))) tail )
) \/
(
forall (immediate_pre: Z) (op_pre: Z) (emitter_pre: Z) (opcode: tvm_opcode) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (((Zlength ((app (done) ((cons ((TVMInst (opcode) (immediate_pre))) ((@nil tvm_inst))))))) + (Zlength (tail)) ) <= capacity)) (PreH2 : (op_pre = (tvm_opcode_code (opcode)))) (PreH3 : ((tvm_opcode_code (opcode)) <> 22)) (PreH4 : (((Zlength (done)) + 1 ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (opcode) (immediate_pre))) ((@nil tvm_inst))))) )
|--
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (opcode) (immediate_pre))) ((@nil tvm_inst))))) tail )
).

Definition cm_emit_plan_return_wit_1_split_goal_spatial := 
forall (immediate_pre: Z) (op_pre: Z) (emitter_pre: Z) (opcode: tvm_opcode) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (((Zlength ((app (done) ((cons ((TVMInst (opcode) (immediate_pre))) ((@nil tvm_inst))))))) + (Zlength (tail)) ) <= capacity)) (PreH2 : (op_pre = (tvm_opcode_code (opcode)))) (PreH3 : ((tvm_opcode_code (opcode)) <> 22)) (PreH4 : (((Zlength (done)) + 1 ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (opcode) (immediate_pre))) ((@nil tvm_inst))))) )
|--
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (opcode) (immediate_pre))) ((@nil tvm_inst))))) tail )
.

Definition cm_emit_plan_partial_solve_wit_1_pure := 
forall (immediate_pre: Z) (op_pre: Z) (emitter_pre: Z) (opcode: tvm_opcode) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (((Zlength ((app (done) ((cons ((TVMInst (opcode) (immediate_pre))) ((@nil tvm_inst))))))) + (Zlength (tail)) ) <= capacity)) (PreH2 : (op_pre = (tvm_opcode_code (opcode)))) (PreH3 : ((tvm_opcode_code (opcode)) <> 22)) (PreH4 : (((Zlength (done)) + 1 ) <= capacity)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "immediate" ) )) # Int64  |-> immediate_pre)
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (op_pre = (tvm_opcode_code (opcode))) ” 
  &&  “ ((tvm_opcode_code (opcode)) <> 22) ” 
  &&  “ (((Zlength (done)) + 1 ) <= capacity) ”
.

Definition cm_emit_plan_partial_solve_wit_1_aux := 
forall (immediate_pre: Z) (op_pre: Z) (emitter_pre: Z) (opcode: tvm_opcode) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (((Zlength ((app (done) ((cons ((TVMInst (opcode) (immediate_pre))) ((@nil tvm_inst))))))) + (Zlength (tail)) ) <= capacity)) (PreH2 : (op_pre = (tvm_opcode_code (opcode)))) (PreH3 : ((tvm_opcode_code (opcode)) <> 22)) (PreH4 : (((Zlength (done)) + 1 ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (op_pre = (tvm_opcode_code (opcode))) ” 
  &&  “ ((tvm_opcode_code (opcode)) <> 22) ” 
  &&  “ (((Zlength (done)) + 1 ) <= capacity) ” 
  &&  “ (((Zlength ((app (done) ((cons ((TVMInst (opcode) (immediate_pre))) ((@nil tvm_inst))))))) + (Zlength (tail)) ) <= capacity) ” 
  &&  “ (op_pre = (tvm_opcode_code (opcode))) ” 
  &&  “ ((tvm_opcode_code (opcode)) <> 22) ” 
  &&  “ (((Zlength (done)) + 1 ) <= capacity) ”
  &&  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
.

Definition cm_emit_plan_partial_solve_wit_1 := cm_emit_plan_partial_solve_wit_1_pure -> cm_emit_plan_partial_solve_wit_1_aux.

(*----- Function cm_emit_call_plan -----*)

Definition cm_emit_call_plan_entail_wit_1 := 
(
forall (function_id_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (function_id_pre))))) (tail)) )
|--
  “ (((Zlength ((app (done) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (function_id_pre))))) ((@nil tvm_inst))))))) + (Zlength (tail)) ) <= capacity) ” 
  &&  “ (((Zlength (done)) + 1 ) <= capacity) ”
  &&  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
) \/
(
forall (function_id_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (function_id_pre))))) (tail)) )
|--
  “ (((Zlength (done)) + 1 ) <= capacity) ” 
  &&  “ (((Zlength ((app (done) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (function_id_pre))))) ((@nil tvm_inst))))))) + (Zlength (tail)) ) <= capacity) ”
  &&  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
).

Definition cm_emit_call_plan_entail_wit_1_split_goal_1 := 
forall (function_id_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (function_id_pre))))) (tail)) )
|--
  “ (((Zlength (done)) + 1 ) <= capacity) ”
.

Definition cm_emit_call_plan_entail_wit_1_split_goal_2 := 
forall (function_id_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (function_id_pre))))) (tail)) )
|--
  “ (((Zlength ((app (done) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (function_id_pre))))) ((@nil tvm_inst))))))) + (Zlength (tail)) ) <= capacity) ”
.

Definition cm_emit_call_plan_entail_wit_1_split_goal_spatial := 
forall (function_id_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (function_id_pre))))) (tail)) )
|--
  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
.

Definition cm_emit_call_plan_return_wit_1 := 
(
forall (function_id_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (((Zlength ((app (done) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (function_id_pre))))) ((@nil tvm_inst))))))) + (Zlength (tail)) ) <= capacity)) (PreH2 : (((Zlength (done)) + 1 ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (function_id_pre))))) ((@nil tvm_inst))))) )
|--
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (function_id_pre))))) ((@nil tvm_inst))))) tail )
) \/
(
forall (function_id_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (((Zlength ((app (done) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (function_id_pre))))) ((@nil tvm_inst))))))) + (Zlength (tail)) ) <= capacity)) (PreH2 : (((Zlength (done)) + 1 ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (function_id_pre))))) ((@nil tvm_inst))))) )
|--
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (function_id_pre))))) ((@nil tvm_inst))))) tail )
).

Definition cm_emit_call_plan_return_wit_1_split_goal_spatial := 
forall (function_id_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (((Zlength ((app (done) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (function_id_pre))))) ((@nil tvm_inst))))))) + (Zlength (tail)) ) <= capacity)) (PreH2 : (((Zlength (done)) + 1 ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (function_id_pre))))) ((@nil tvm_inst))))) )
|--
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (function_id_pre))))) ((@nil tvm_inst))))) tail )
.

Definition cm_emit_call_plan_partial_solve_wit_1_pure := 
forall (function_id_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (((Zlength ((app (done) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (function_id_pre))))) ((@nil tvm_inst))))))) + (Zlength (tail)) ) <= capacity)) (PreH2 : (((Zlength (done)) + 1 ) <= capacity)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "function_id" ) )) # Int  |-> function_id_pre)
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (((Zlength (done)) + 1 ) <= capacity) ”
.

Definition cm_emit_call_plan_partial_solve_wit_1_aux := 
forall (function_id_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (((Zlength ((app (done) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (function_id_pre))))) ((@nil tvm_inst))))))) + (Zlength (tail)) ) <= capacity)) (PreH2 : (((Zlength (done)) + 1 ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (((Zlength (done)) + 1 ) <= capacity) ” 
  &&  “ (((Zlength ((app (done) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (function_id_pre))))) ((@nil tvm_inst))))))) + (Zlength (tail)) ) <= capacity) ” 
  &&  “ (((Zlength (done)) + 1 ) <= capacity) ”
  &&  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
.

Definition cm_emit_call_plan_partial_solve_wit_1 := cm_emit_call_plan_partial_solve_wit_1_pure -> cm_emit_call_plan_partial_solve_wit_1_aux.

(*----- Function cm_emit_normalize_plan -----*)

Definition cm_emit_normalize_plan_entail_wit_1 := 
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_char_normalize_code (model_ty))) (tail)) )
|--
  “ (((Zlength ((app (done) ((cm_char_normalize_code (model_ty)))))) + (Zlength (tail)) ) <= capacity) ” 
  &&  “ (ty_pre = (cm_type_encode (model_ty))) ” 
  &&  “ (cm_type_code_wf model_ty ) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_char_normalize_code (model_ty)))) ) <= capacity) ”
  &&  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
) \/
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_char_normalize_code (model_ty))) (tail)) )
|--
  “ (((Zlength (done)) + (Zlength ((cm_char_normalize_code (model_ty)))) ) <= capacity) ” 
  &&  “ (((Zlength ((app (done) ((cm_char_normalize_code (model_ty)))))) + (Zlength (tail)) ) <= capacity) ”
  &&  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
).

Definition cm_emit_normalize_plan_entail_wit_1_split_goal_1 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_char_normalize_code (model_ty))) (tail)) )
|--
  “ (((Zlength (done)) + (Zlength ((cm_char_normalize_code (model_ty)))) ) <= capacity) ”
.

Definition cm_emit_normalize_plan_entail_wit_1_split_goal_2 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_char_normalize_code (model_ty))) (tail)) )
|--
  “ (((Zlength ((app (done) ((cm_char_normalize_code (model_ty)))))) + (Zlength (tail)) ) <= capacity) ”
.

Definition cm_emit_normalize_plan_entail_wit_1_split_goal_spatial := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_char_normalize_code (model_ty))) (tail)) )
|--
  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
.

Definition cm_emit_normalize_plan_return_wit_1 := 
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (((Zlength ((app (done) ((cm_char_normalize_code (model_ty)))))) + (Zlength (tail)) ) <= capacity)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) (PreH4 : (((Zlength (done)) + (Zlength ((cm_char_normalize_code (model_ty)))) ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_char_normalize_code (model_ty)))) )
|--
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_char_normalize_code (model_ty)))) tail )
) \/
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (((Zlength ((app (done) ((cm_char_normalize_code (model_ty)))))) + (Zlength (tail)) ) <= capacity)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) (PreH4 : (((Zlength (done)) + (Zlength ((cm_char_normalize_code (model_ty)))) ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_char_normalize_code (model_ty)))) )
|--
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_char_normalize_code (model_ty)))) tail )
).

Definition cm_emit_normalize_plan_return_wit_1_split_goal_spatial := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (((Zlength ((app (done) ((cm_char_normalize_code (model_ty)))))) + (Zlength (tail)) ) <= capacity)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) (PreH4 : (((Zlength (done)) + (Zlength ((cm_char_normalize_code (model_ty)))) ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_char_normalize_code (model_ty)))) )
|--
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_char_normalize_code (model_ty)))) tail )
.

Definition cm_emit_normalize_plan_partial_solve_wit_1_pure := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (((Zlength ((app (done) ((cm_char_normalize_code (model_ty)))))) + (Zlength (tail)) ) <= capacity)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) (PreH4 : (((Zlength (done)) + (Zlength ((cm_char_normalize_code (model_ty)))) ) <= capacity)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (ty_pre = (cm_type_encode (model_ty))) ” 
  &&  “ (cm_type_code_wf model_ty ) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_char_normalize_code (model_ty)))) ) <= capacity) ”
.

Definition cm_emit_normalize_plan_partial_solve_wit_1_aux := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (((Zlength ((app (done) ((cm_char_normalize_code (model_ty)))))) + (Zlength (tail)) ) <= capacity)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) (PreH4 : (((Zlength (done)) + (Zlength ((cm_char_normalize_code (model_ty)))) ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (ty_pre = (cm_type_encode (model_ty))) ” 
  &&  “ (cm_type_code_wf model_ty ) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_char_normalize_code (model_ty)))) ) <= capacity) ” 
  &&  “ (((Zlength ((app (done) ((cm_char_normalize_code (model_ty)))))) + (Zlength (tail)) ) <= capacity) ” 
  &&  “ (ty_pre = (cm_type_encode (model_ty))) ” 
  &&  “ (cm_type_code_wf model_ty ) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_char_normalize_code (model_ty)))) ) <= capacity) ”
  &&  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
.

Definition cm_emit_normalize_plan_partial_solve_wit_1 := cm_emit_normalize_plan_partial_solve_wit_1_pure -> cm_emit_normalize_plan_partial_solve_wit_1_aux.

(*----- Function cm_emit_load_plan -----*)

Definition cm_emit_load_plan_entail_wit_1 := 
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_load_code (model_ty))) (tail)) )
|--
  “ (((Zlength ((app (done) ((cm_load_code (model_ty)))))) + (Zlength (tail)) ) <= capacity) ” 
  &&  “ (ty_pre = (cm_type_encode (model_ty))) ” 
  &&  “ (cm_type_code_wf model_ty ) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_load_code (model_ty)))) ) <= capacity) ”
  &&  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
) \/
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_load_code (model_ty))) (tail)) )
|--
  “ (((Zlength (done)) + (Zlength ((cm_load_code (model_ty)))) ) <= capacity) ” 
  &&  “ (((Zlength ((app (done) ((cm_load_code (model_ty)))))) + (Zlength (tail)) ) <= capacity) ”
  &&  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
).

Definition cm_emit_load_plan_entail_wit_1_split_goal_1 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_load_code (model_ty))) (tail)) )
|--
  “ (((Zlength (done)) + (Zlength ((cm_load_code (model_ty)))) ) <= capacity) ”
.

Definition cm_emit_load_plan_entail_wit_1_split_goal_2 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_load_code (model_ty))) (tail)) )
|--
  “ (((Zlength ((app (done) ((cm_load_code (model_ty)))))) + (Zlength (tail)) ) <= capacity) ”
.

Definition cm_emit_load_plan_entail_wit_1_split_goal_spatial := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_load_code (model_ty))) (tail)) )
|--
  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
.

Definition cm_emit_load_plan_return_wit_1 := 
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (((Zlength ((app (done) ((cm_load_code (model_ty)))))) + (Zlength (tail)) ) <= capacity)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) (PreH4 : (((Zlength (done)) + (Zlength ((cm_load_code (model_ty)))) ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_load_code (model_ty)))) )
|--
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_load_code (model_ty)))) tail )
) \/
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (((Zlength ((app (done) ((cm_load_code (model_ty)))))) + (Zlength (tail)) ) <= capacity)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) (PreH4 : (((Zlength (done)) + (Zlength ((cm_load_code (model_ty)))) ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_load_code (model_ty)))) )
|--
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_load_code (model_ty)))) tail )
).

Definition cm_emit_load_plan_return_wit_1_split_goal_spatial := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (((Zlength ((app (done) ((cm_load_code (model_ty)))))) + (Zlength (tail)) ) <= capacity)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) (PreH4 : (((Zlength (done)) + (Zlength ((cm_load_code (model_ty)))) ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_load_code (model_ty)))) )
|--
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_load_code (model_ty)))) tail )
.

Definition cm_emit_load_plan_partial_solve_wit_1_pure := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (((Zlength ((app (done) ((cm_load_code (model_ty)))))) + (Zlength (tail)) ) <= capacity)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) (PreH4 : (((Zlength (done)) + (Zlength ((cm_load_code (model_ty)))) ) <= capacity)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (ty_pre = (cm_type_encode (model_ty))) ” 
  &&  “ (cm_type_code_wf model_ty ) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_load_code (model_ty)))) ) <= capacity) ”
.

Definition cm_emit_load_plan_partial_solve_wit_1_aux := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (((Zlength ((app (done) ((cm_load_code (model_ty)))))) + (Zlength (tail)) ) <= capacity)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) (PreH4 : (((Zlength (done)) + (Zlength ((cm_load_code (model_ty)))) ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (ty_pre = (cm_type_encode (model_ty))) ” 
  &&  “ (cm_type_code_wf model_ty ) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_load_code (model_ty)))) ) <= capacity) ” 
  &&  “ (((Zlength ((app (done) ((cm_load_code (model_ty)))))) + (Zlength (tail)) ) <= capacity) ” 
  &&  “ (ty_pre = (cm_type_encode (model_ty))) ” 
  &&  “ (cm_type_code_wf model_ty ) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_load_code (model_ty)))) ) <= capacity) ”
  &&  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
.

Definition cm_emit_load_plan_partial_solve_wit_1 := cm_emit_load_plan_partial_solve_wit_1_pure -> cm_emit_load_plan_partial_solve_wit_1_aux.

(*----- Function cm_emit_store_plan -----*)

Definition cm_emit_store_plan_entail_wit_1 := 
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_store_code (model_ty))) (tail)) )
|--
  “ (((Zlength ((app (done) ((cm_store_code (model_ty)))))) + (Zlength (tail)) ) <= capacity) ” 
  &&  “ (ty_pre = (cm_type_encode (model_ty))) ” 
  &&  “ (cm_type_code_wf model_ty ) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_store_code (model_ty)))) ) <= capacity) ”
  &&  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
) \/
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_store_code (model_ty))) (tail)) )
|--
  “ (((Zlength (done)) + (Zlength ((cm_store_code (model_ty)))) ) <= capacity) ” 
  &&  “ (((Zlength ((app (done) ((cm_store_code (model_ty)))))) + (Zlength (tail)) ) <= capacity) ”
  &&  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
).

Definition cm_emit_store_plan_entail_wit_1_split_goal_1 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_store_code (model_ty))) (tail)) )
|--
  “ (((Zlength (done)) + (Zlength ((cm_store_code (model_ty)))) ) <= capacity) ”
.

Definition cm_emit_store_plan_entail_wit_1_split_goal_2 := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_store_code (model_ty))) (tail)) )
|--
  “ (((Zlength ((app (done) ((cm_store_code (model_ty)))))) + (Zlength (tail)) ) <= capacity) ”
.

Definition cm_emit_store_plan_entail_wit_1_split_goal_spatial := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_store_code (model_ty))) (tail)) )
|--
  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
.

Definition cm_emit_store_plan_return_wit_1 := 
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (((Zlength ((app (done) ((cm_store_code (model_ty)))))) + (Zlength (tail)) ) <= capacity)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) (PreH4 : (((Zlength (done)) + (Zlength ((cm_store_code (model_ty)))) ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_store_code (model_ty)))) )
|--
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_store_code (model_ty)))) tail )
) \/
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (((Zlength ((app (done) ((cm_store_code (model_ty)))))) + (Zlength (tail)) ) <= capacity)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) (PreH4 : (((Zlength (done)) + (Zlength ((cm_store_code (model_ty)))) ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_store_code (model_ty)))) )
|--
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_store_code (model_ty)))) tail )
).

Definition cm_emit_store_plan_return_wit_1_split_goal_spatial := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (((Zlength ((app (done) ((cm_store_code (model_ty)))))) + (Zlength (tail)) ) <= capacity)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) (PreH4 : (((Zlength (done)) + (Zlength ((cm_store_code (model_ty)))) ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_store_code (model_ty)))) )
|--
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_store_code (model_ty)))) tail )
.

Definition cm_emit_store_plan_partial_solve_wit_1_pure := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (((Zlength ((app (done) ((cm_store_code (model_ty)))))) + (Zlength (tail)) ) <= capacity)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) (PreH4 : (((Zlength (done)) + (Zlength ((cm_store_code (model_ty)))) ) <= capacity)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (ty_pre = (cm_type_encode (model_ty))) ” 
  &&  “ (cm_type_code_wf model_ty ) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_store_code (model_ty)))) ) <= capacity) ”
.

Definition cm_emit_store_plan_partial_solve_wit_1_aux := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (((Zlength ((app (done) ((cm_store_code (model_ty)))))) + (Zlength (tail)) ) <= capacity)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) (PreH4 : (((Zlength (done)) + (Zlength ((cm_store_code (model_ty)))) ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (ty_pre = (cm_type_encode (model_ty))) ” 
  &&  “ (cm_type_code_wf model_ty ) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_store_code (model_ty)))) ) <= capacity) ” 
  &&  “ (((Zlength ((app (done) ((cm_store_code (model_ty)))))) + (Zlength (tail)) ) <= capacity) ” 
  &&  “ (ty_pre = (cm_type_encode (model_ty))) ” 
  &&  “ (cm_type_code_wf model_ty ) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_store_code (model_ty)))) ) <= capacity) ”
  &&  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
.

Definition cm_emit_store_plan_partial_solve_wit_1 := cm_emit_store_plan_partial_solve_wit_1_pure -> cm_emit_store_plan_partial_solve_wit_1_aux.

(*----- Function cm_emit_fp_address_plan -----*)

Definition cm_emit_fp_address_plan_entail_wit_1 := 
(
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_fp_relative_address_code (offset_pre))) (tail)) )
|--
  “ (((Zlength ((app (done) ((cm_fp_relative_address_code (offset_pre)))))) + (Zlength (tail)) ) <= capacity) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_fp_relative_address_code (offset_pre)))) ) <= capacity) ”
  &&  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
) \/
(
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_fp_relative_address_code (offset_pre))) (tail)) )
|--
  “ (((Zlength (done)) + (Zlength ((cm_fp_relative_address_code (offset_pre)))) ) <= capacity) ” 
  &&  “ (((Zlength ((app (done) ((cm_fp_relative_address_code (offset_pre)))))) + (Zlength (tail)) ) <= capacity) ”
  &&  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
).

Definition cm_emit_fp_address_plan_entail_wit_1_split_goal_1 := 
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_fp_relative_address_code (offset_pre))) (tail)) )
|--
  “ (((Zlength (done)) + (Zlength ((cm_fp_relative_address_code (offset_pre)))) ) <= capacity) ”
.

Definition cm_emit_fp_address_plan_entail_wit_1_split_goal_2 := 
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_fp_relative_address_code (offset_pre))) (tail)) )
|--
  “ (((Zlength ((app (done) ((cm_fp_relative_address_code (offset_pre)))))) + (Zlength (tail)) ) <= capacity) ”
.

Definition cm_emit_fp_address_plan_entail_wit_1_split_goal_spatial := 
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_fp_relative_address_code (offset_pre))) (tail)) )
|--
  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
.

Definition cm_emit_fp_address_plan_return_wit_1 := 
(
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (((Zlength ((app (done) ((cm_fp_relative_address_code (offset_pre)))))) + (Zlength (tail)) ) <= capacity)) (PreH2 : (((Zlength (done)) + (Zlength ((cm_fp_relative_address_code (offset_pre)))) ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_fp_relative_address_code (offset_pre)))) )
|--
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_fp_relative_address_code (offset_pre)))) tail )
) \/
(
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (((Zlength ((app (done) ((cm_fp_relative_address_code (offset_pre)))))) + (Zlength (tail)) ) <= capacity)) (PreH2 : (((Zlength (done)) + (Zlength ((cm_fp_relative_address_code (offset_pre)))) ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_fp_relative_address_code (offset_pre)))) )
|--
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_fp_relative_address_code (offset_pre)))) tail )
).

Definition cm_emit_fp_address_plan_return_wit_1_split_goal_spatial := 
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (((Zlength ((app (done) ((cm_fp_relative_address_code (offset_pre)))))) + (Zlength (tail)) ) <= capacity)) (PreH2 : (((Zlength (done)) + (Zlength ((cm_fp_relative_address_code (offset_pre)))) ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_fp_relative_address_code (offset_pre)))) )
|--
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_fp_relative_address_code (offset_pre)))) tail )
.

Definition cm_emit_fp_address_plan_partial_solve_wit_1_pure := 
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (((Zlength ((app (done) ((cm_fp_relative_address_code (offset_pre)))))) + (Zlength (tail)) ) <= capacity)) (PreH2 : (((Zlength (done)) + (Zlength ((cm_fp_relative_address_code (offset_pre)))) ) <= capacity)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "offset" ) )) # Int64  |-> offset_pre)
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (((Zlength (done)) + (Zlength ((cm_fp_relative_address_code (offset_pre)))) ) <= capacity) ”
.

Definition cm_emit_fp_address_plan_partial_solve_wit_1_aux := 
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (((Zlength ((app (done) ((cm_fp_relative_address_code (offset_pre)))))) + (Zlength (tail)) ) <= capacity)) (PreH2 : (((Zlength (done)) + (Zlength ((cm_fp_relative_address_code (offset_pre)))) ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (((Zlength (done)) + (Zlength ((cm_fp_relative_address_code (offset_pre)))) ) <= capacity) ” 
  &&  “ (((Zlength ((app (done) ((cm_fp_relative_address_code (offset_pre)))))) + (Zlength (tail)) ) <= capacity) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_fp_relative_address_code (offset_pre)))) ) <= capacity) ”
  &&  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
.

Definition cm_emit_fp_address_plan_partial_solve_wit_1 := cm_emit_fp_address_plan_partial_solve_wit_1_pure -> cm_emit_fp_address_plan_partial_solve_wit_1_aux.

(*----- Function cm_emit_temp_store_plan -----*)

Definition cm_emit_temp_store_plan_entail_wit_1 := 
(
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_temp_store_code (policy) (p) (fid) (temp_pre))) (tail)) )
|--
  “ (((Zlength ((app (done) ((cm_temp_store_code (policy) (p) (fid) (temp_pre)))))) + (Zlength (tail)) ) <= capacity) ” 
  &&  “ (0 <= temp_pre) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_temp_store_code (policy) (p) (fid) (temp_pre)))) ) <= capacity) ”
  &&  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
) \/
(
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_temp_store_code (policy) (p) (fid) (temp_pre))) (tail)) )
|--
  “ (((Zlength (done)) + (Zlength ((cm_temp_store_code (policy) (p) (fid) (temp_pre)))) ) <= capacity) ” 
  &&  “ (((Zlength ((app (done) ((cm_temp_store_code (policy) (p) (fid) (temp_pre)))))) + (Zlength (tail)) ) <= capacity) ”
  &&  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
).

Definition cm_emit_temp_store_plan_entail_wit_1_split_goal_1 := 
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_temp_store_code (policy) (p) (fid) (temp_pre))) (tail)) )
|--
  “ (((Zlength (done)) + (Zlength ((cm_temp_store_code (policy) (p) (fid) (temp_pre)))) ) <= capacity) ”
.

Definition cm_emit_temp_store_plan_entail_wit_1_split_goal_2 := 
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_temp_store_code (policy) (p) (fid) (temp_pre))) (tail)) )
|--
  “ (((Zlength ((app (done) ((cm_temp_store_code (policy) (p) (fid) (temp_pre)))))) + (Zlength (tail)) ) <= capacity) ”
.

Definition cm_emit_temp_store_plan_entail_wit_1_split_goal_spatial := 
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_temp_store_code (policy) (p) (fid) (temp_pre))) (tail)) )
|--
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
.

Definition cm_emit_temp_store_plan_return_wit_1 := 
(
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH9 : (((Zlength ((app (done) ((cm_temp_store_code (policy) (p) (fid) (temp_pre)))))) + (Zlength (tail)) ) <= capacity)) (PreH10 : (0 <= temp_pre)) (PreH11 : (structs = (cm_program_structs (p)))) (PreH12 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH13 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH14 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH15 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH16 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH17 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH18 : (((Zlength (done)) + (Zlength ((cm_temp_store_code (policy) (p) (fid) (temp_pre)))) ) <= capacity)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_temp_store_code (policy) (p) (fid) (temp_pre)))) )
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
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_temp_store_code (policy) (p) (fid) (temp_pre)))) tail )
) \/
(
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH9 : (((Zlength ((app (done) ((cm_temp_store_code (policy) (p) (fid) (temp_pre)))))) + (Zlength (tail)) ) <= capacity)) (PreH10 : (0 <= temp_pre)) (PreH11 : (structs = (cm_program_structs (p)))) (PreH12 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH13 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH14 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH15 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH16 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH17 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH18 : (((Zlength (done)) + (Zlength ((cm_temp_store_code (policy) (p) (fid) (temp_pre)))) ) <= capacity)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_temp_store_code (policy) (p) (fid) (temp_pre)))) )
|--
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_temp_store_code (policy) (p) (fid) (temp_pre)))) tail )
).

Definition cm_emit_temp_store_plan_return_wit_1_split_goal_spatial := 
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH9 : (((Zlength ((app (done) ((cm_temp_store_code (policy) (p) (fid) (temp_pre)))))) + (Zlength (tail)) ) <= capacity)) (PreH10 : (0 <= temp_pre)) (PreH11 : (structs = (cm_program_structs (p)))) (PreH12 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH13 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH14 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH15 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH16 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH17 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH18 : (((Zlength (done)) + (Zlength ((cm_temp_store_code (policy) (p) (fid) (temp_pre)))) ) <= capacity)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_temp_store_code (policy) (p) (fid) (temp_pre)))) )
|--
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_temp_store_code (policy) (p) (fid) (temp_pre)))) tail )
.

Definition cm_emit_temp_store_plan_partial_solve_wit_1_pure := 
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (((Zlength ((app (done) ((cm_temp_store_code (policy) (p) (fid) (temp_pre)))))) + (Zlength (tail)) ) <= capacity)) (PreH2 : (0 <= temp_pre)) (PreH3 : (structs = (cm_program_structs (p)))) (PreH4 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH5 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH6 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH8 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH9 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH10 : (((Zlength (done)) + (Zlength ((cm_temp_store_code (policy) (p) (fid) (temp_pre)))) ) <= capacity)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (0 <= temp_pre) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_temp_store_code (policy) (p) (fid) (temp_pre)))) ) <= capacity) ”
.

Definition cm_emit_temp_store_plan_partial_solve_wit_1_aux := 
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (((Zlength ((app (done) ((cm_temp_store_code (policy) (p) (fid) (temp_pre)))))) + (Zlength (tail)) ) <= capacity)) (PreH2 : (0 <= temp_pre)) (PreH3 : (structs = (cm_program_structs (p)))) (PreH4 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH5 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH6 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH8 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH9 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH10 : (((Zlength (done)) + (Zlength ((cm_temp_store_code (policy) (p) (fid) (temp_pre)))) ) <= capacity)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (0 <= temp_pre) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_temp_store_code (policy) (p) (fid) (temp_pre)))) ) <= capacity) ” 
  &&  “ (((Zlength ((app (done) ((cm_temp_store_code (policy) (p) (fid) (temp_pre)))))) + (Zlength (tail)) ) <= capacity) ” 
  &&  “ (0 <= temp_pre) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_temp_store_code (policy) (p) (fid) (temp_pre)))) ) <= capacity) ”
  &&  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
.

Definition cm_emit_temp_store_plan_partial_solve_wit_1 := cm_emit_temp_store_plan_partial_solve_wit_1_pure -> cm_emit_temp_store_plan_partial_solve_wit_1_aux.

(*----- Function cm_emit_temp_load_plan -----*)

Definition cm_emit_temp_load_plan_entail_wit_1 := 
(
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_temp_load_code (policy) (p) (fid) (temp_pre))) (tail)) )
|--
  “ (((Zlength ((app (done) ((cm_temp_load_code (policy) (p) (fid) (temp_pre)))))) + (Zlength (tail)) ) <= capacity) ” 
  &&  “ (0 <= temp_pre) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_temp_load_code (policy) (p) (fid) (temp_pre)))) ) <= capacity) ”
  &&  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
) \/
(
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_temp_load_code (policy) (p) (fid) (temp_pre))) (tail)) )
|--
  “ (((Zlength (done)) + (Zlength ((cm_temp_load_code (policy) (p) (fid) (temp_pre)))) ) <= capacity) ” 
  &&  “ (((Zlength ((app (done) ((cm_temp_load_code (policy) (p) (fid) (temp_pre)))))) + (Zlength (tail)) ) <= capacity) ”
  &&  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
).

Definition cm_emit_temp_load_plan_entail_wit_1_split_goal_1 := 
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_temp_load_code (policy) (p) (fid) (temp_pre))) (tail)) )
|--
  “ (((Zlength (done)) + (Zlength ((cm_temp_load_code (policy) (p) (fid) (temp_pre)))) ) <= capacity) ”
.

Definition cm_emit_temp_load_plan_entail_wit_1_split_goal_2 := 
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_temp_load_code (policy) (p) (fid) (temp_pre))) (tail)) )
|--
  “ (((Zlength ((app (done) ((cm_temp_load_code (policy) (p) (fid) (temp_pre)))))) + (Zlength (tail)) ) <= capacity) ”
.

Definition cm_emit_temp_load_plan_entail_wit_1_split_goal_spatial := 
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_temp_load_code (policy) (p) (fid) (temp_pre))) (tail)) )
|--
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
.

Definition cm_emit_temp_load_plan_return_wit_1 := 
(
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH9 : (((Zlength ((app (done) ((cm_temp_load_code (policy) (p) (fid) (temp_pre)))))) + (Zlength (tail)) ) <= capacity)) (PreH10 : (0 <= temp_pre)) (PreH11 : (structs = (cm_program_structs (p)))) (PreH12 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH13 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH14 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH15 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH16 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH17 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH18 : (((Zlength (done)) + (Zlength ((cm_temp_load_code (policy) (p) (fid) (temp_pre)))) ) <= capacity)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_temp_load_code (policy) (p) (fid) (temp_pre)))) )
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
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_temp_load_code (policy) (p) (fid) (temp_pre)))) tail )
) \/
(
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH9 : (((Zlength ((app (done) ((cm_temp_load_code (policy) (p) (fid) (temp_pre)))))) + (Zlength (tail)) ) <= capacity)) (PreH10 : (0 <= temp_pre)) (PreH11 : (structs = (cm_program_structs (p)))) (PreH12 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH13 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH14 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH15 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH16 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH17 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH18 : (((Zlength (done)) + (Zlength ((cm_temp_load_code (policy) (p) (fid) (temp_pre)))) ) <= capacity)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_temp_load_code (policy) (p) (fid) (temp_pre)))) )
|--
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_temp_load_code (policy) (p) (fid) (temp_pre)))) tail )
).

Definition cm_emit_temp_load_plan_return_wit_1_split_goal_spatial := 
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH9 : (((Zlength ((app (done) ((cm_temp_load_code (policy) (p) (fid) (temp_pre)))))) + (Zlength (tail)) ) <= capacity)) (PreH10 : (0 <= temp_pre)) (PreH11 : (structs = (cm_program_structs (p)))) (PreH12 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH13 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH14 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH15 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH16 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH17 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH18 : (((Zlength (done)) + (Zlength ((cm_temp_load_code (policy) (p) (fid) (temp_pre)))) ) <= capacity)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_temp_load_code (policy) (p) (fid) (temp_pre)))) )
|--
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_temp_load_code (policy) (p) (fid) (temp_pre)))) tail )
.

Definition cm_emit_temp_load_plan_partial_solve_wit_1_pure := 
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (((Zlength ((app (done) ((cm_temp_load_code (policy) (p) (fid) (temp_pre)))))) + (Zlength (tail)) ) <= capacity)) (PreH2 : (0 <= temp_pre)) (PreH3 : (structs = (cm_program_structs (p)))) (PreH4 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH5 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH6 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH8 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH9 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH10 : (((Zlength (done)) + (Zlength ((cm_temp_load_code (policy) (p) (fid) (temp_pre)))) ) <= capacity)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (0 <= temp_pre) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_temp_load_code (policy) (p) (fid) (temp_pre)))) ) <= capacity) ”
.

Definition cm_emit_temp_load_plan_partial_solve_wit_1_aux := 
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (((Zlength ((app (done) ((cm_temp_load_code (policy) (p) (fid) (temp_pre)))))) + (Zlength (tail)) ) <= capacity)) (PreH2 : (0 <= temp_pre)) (PreH3 : (structs = (cm_program_structs (p)))) (PreH4 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH5 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH6 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH8 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH9 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH10 : (((Zlength (done)) + (Zlength ((cm_temp_load_code (policy) (p) (fid) (temp_pre)))) ) <= capacity)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (0 <= temp_pre) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_temp_load_code (policy) (p) (fid) (temp_pre)))) ) <= capacity) ” 
  &&  “ (((Zlength ((app (done) ((cm_temp_load_code (policy) (p) (fid) (temp_pre)))))) + (Zlength (tail)) ) <= capacity) ” 
  &&  “ (0 <= temp_pre) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_temp_load_code (policy) (p) (fid) (temp_pre)))) ) <= capacity) ”
  &&  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
.

Definition cm_emit_temp_load_plan_partial_solve_wit_1 := cm_emit_temp_load_plan_partial_solve_wit_1_pure -> cm_emit_temp_load_plan_partial_solve_wit_1_aux.

Module Type VC_Correct.


Axiom proof_of_cm_emit_plan_entail_wit_1 : cm_emit_plan_entail_wit_1.
Axiom proof_of_cm_emit_plan_return_wit_1 : cm_emit_plan_return_wit_1.
Axiom proof_of_cm_emit_plan_partial_solve_wit_1_pure : cm_emit_plan_partial_solve_wit_1_pure.
Axiom proof_of_cm_emit_plan_partial_solve_wit_1 : cm_emit_plan_partial_solve_wit_1.
Axiom proof_of_cm_emit_call_plan_entail_wit_1 : cm_emit_call_plan_entail_wit_1.
Axiom proof_of_cm_emit_call_plan_return_wit_1 : cm_emit_call_plan_return_wit_1.
Axiom proof_of_cm_emit_call_plan_partial_solve_wit_1_pure : cm_emit_call_plan_partial_solve_wit_1_pure.
Axiom proof_of_cm_emit_call_plan_partial_solve_wit_1 : cm_emit_call_plan_partial_solve_wit_1.
Axiom proof_of_cm_emit_normalize_plan_entail_wit_1 : cm_emit_normalize_plan_entail_wit_1.
Axiom proof_of_cm_emit_normalize_plan_return_wit_1 : cm_emit_normalize_plan_return_wit_1.
Axiom proof_of_cm_emit_normalize_plan_partial_solve_wit_1_pure : cm_emit_normalize_plan_partial_solve_wit_1_pure.
Axiom proof_of_cm_emit_normalize_plan_partial_solve_wit_1 : cm_emit_normalize_plan_partial_solve_wit_1.
Axiom proof_of_cm_emit_load_plan_entail_wit_1 : cm_emit_load_plan_entail_wit_1.
Axiom proof_of_cm_emit_load_plan_return_wit_1 : cm_emit_load_plan_return_wit_1.
Axiom proof_of_cm_emit_load_plan_partial_solve_wit_1_pure : cm_emit_load_plan_partial_solve_wit_1_pure.
Axiom proof_of_cm_emit_load_plan_partial_solve_wit_1 : cm_emit_load_plan_partial_solve_wit_1.
Axiom proof_of_cm_emit_store_plan_entail_wit_1 : cm_emit_store_plan_entail_wit_1.
Axiom proof_of_cm_emit_store_plan_return_wit_1 : cm_emit_store_plan_return_wit_1.
Axiom proof_of_cm_emit_store_plan_partial_solve_wit_1_pure : cm_emit_store_plan_partial_solve_wit_1_pure.
Axiom proof_of_cm_emit_store_plan_partial_solve_wit_1 : cm_emit_store_plan_partial_solve_wit_1.
Axiom proof_of_cm_emit_fp_address_plan_entail_wit_1 : cm_emit_fp_address_plan_entail_wit_1.
Axiom proof_of_cm_emit_fp_address_plan_return_wit_1 : cm_emit_fp_address_plan_return_wit_1.
Axiom proof_of_cm_emit_fp_address_plan_partial_solve_wit_1_pure : cm_emit_fp_address_plan_partial_solve_wit_1_pure.
Axiom proof_of_cm_emit_fp_address_plan_partial_solve_wit_1 : cm_emit_fp_address_plan_partial_solve_wit_1.
Axiom proof_of_cm_emit_temp_store_plan_entail_wit_1 : cm_emit_temp_store_plan_entail_wit_1.
Axiom proof_of_cm_emit_temp_store_plan_return_wit_1 : cm_emit_temp_store_plan_return_wit_1.
Axiom proof_of_cm_emit_temp_store_plan_partial_solve_wit_1_pure : cm_emit_temp_store_plan_partial_solve_wit_1_pure.
Axiom proof_of_cm_emit_temp_store_plan_partial_solve_wit_1 : cm_emit_temp_store_plan_partial_solve_wit_1.
Axiom proof_of_cm_emit_temp_load_plan_entail_wit_1 : cm_emit_temp_load_plan_entail_wit_1.
Axiom proof_of_cm_emit_temp_load_plan_return_wit_1 : cm_emit_temp_load_plan_return_wit_1.
Axiom proof_of_cm_emit_temp_load_plan_partial_solve_wit_1_pure : cm_emit_temp_load_plan_partial_solve_wit_1_pure.
Axiom proof_of_cm_emit_temp_load_plan_partial_solve_wit_1 : cm_emit_temp_load_plan_partial_solve_wit_1.

End VC_Correct.
