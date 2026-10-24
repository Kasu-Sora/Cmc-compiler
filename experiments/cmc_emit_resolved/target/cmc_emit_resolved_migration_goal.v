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
Require Import SimpleC.EE.QCP_demos_human.cmc_emit_resolved_migration_lib.
Local Open Scope sac.

(*----- Function cm_emit_resolved -----*)

Definition cm_emit_resolved_entail_wit_1 := 
(
forall (immediate_pre: Z) (op_pre: Z) (emitter_pre: Z) (opcode: tvm_opcode) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (op_pre = (tvm_opcode_code (opcode)))) (PreH2 : ((tvm_opcode_code (opcode)) <> 22)) (PreH3 : (((Zlength (done)) + 1 ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  EX (raw_prefix: (@list tvm_inst)) ,
  “ (op_pre = (tvm_opcode_code (opcode))) ” 
  &&  “ ((tvm_opcode_code (opcode)) <> 22) ” 
  &&  “ ((cm_patch_code (policy) (p) (raw_prefix)) = done) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (cons ((TVMInst (opcode) (immediate_pre))) ((@nil tvm_inst))) )
) \/
(
forall (immediate_pre: Z) (op_pre: Z) (emitter_pre: Z) (opcode: tvm_opcode) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (op_pre = (tvm_opcode_code (opcode)))) (PreH2 : ((tvm_opcode_code (opcode)) <> 22)) (PreH3 : (((Zlength (done)) + 1 ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  EX (raw_prefix: (@list tvm_inst)) ,
  “ (op_pre = (tvm_opcode_code (opcode))) ” 
  &&  “ ((tvm_opcode_code (opcode)) <> 22) ” 
  &&  “ ((cm_patch_code (policy) (p) (raw_prefix)) = done) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (cons ((TVMInst (opcode) (immediate_pre))) ((@nil tvm_inst))) )
).

Definition cm_emit_resolved_return_wit_1 := 
(
forall (immediate_pre: Z) (op_pre: Z) (emitter_pre: Z) (opcode: tvm_opcode) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : (op_pre = (tvm_opcode_code (opcode)))) (PreH2 : ((tvm_opcode_code (opcode)) <> 22)) (PreH3 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (raw_prefix) ((cons ((TVMInst (opcode) (immediate_pre))) ((@nil tvm_inst))))) (@nil tvm_inst) )
|--
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (opcode) (immediate_pre))) ((@nil tvm_inst))))) )
) \/
(
forall (immediate_pre: Z) (op_pre: Z) (emitter_pre: Z) (opcode: tvm_opcode) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : (op_pre = (tvm_opcode_code (opcode)))) (PreH2 : ((tvm_opcode_code (opcode)) <> 22)) (PreH3 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (raw_prefix) ((cons ((TVMInst (opcode) (immediate_pre))) ((@nil tvm_inst))))) (@nil tvm_inst) )
|--
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (opcode) (immediate_pre))) ((@nil tvm_inst))))) )
).

Definition cm_emit_resolved_return_wit_1_split_goal_spatial := 
forall (immediate_pre: Z) (op_pre: Z) (emitter_pre: Z) (opcode: tvm_opcode) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : (op_pre = (tvm_opcode_code (opcode)))) (PreH2 : ((tvm_opcode_code (opcode)) <> 22)) (PreH3 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (raw_prefix) ((cons ((TVMInst (opcode) (immediate_pre))) ((@nil tvm_inst))))) (@nil tvm_inst) )
|--
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (opcode) (immediate_pre))) ((@nil tvm_inst))))) )
.

Definition cm_emit_resolved_partial_solve_wit_1_pure := 
forall (immediate_pre: Z) (op_pre: Z) (emitter_pre: Z) (opcode: tvm_opcode) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : (op_pre = (tvm_opcode_code (opcode)))) (PreH2 : ((tvm_opcode_code (opcode)) <> 22)) (PreH3 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "op" ) )) # Int  |-> op_pre)
  **  ((( &( "immediate" ) )) # Int64  |-> immediate_pre)
  **  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (cons ((TVMInst (opcode) (immediate_pre))) ((@nil tvm_inst))) )
|--
  “ (op_pre = (tvm_opcode_code (opcode))) ”
.

Definition cm_emit_resolved_partial_solve_wit_1_aux := 
forall (immediate_pre: Z) (op_pre: Z) (emitter_pre: Z) (opcode: tvm_opcode) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : (op_pre = (tvm_opcode_code (opcode)))) (PreH2 : ((tvm_opcode_code (opcode)) <> 22)) (PreH3 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (cons ((TVMInst (opcode) (immediate_pre))) ((@nil tvm_inst))) )
|--
  “ (op_pre = (tvm_opcode_code (opcode))) ” 
  &&  “ (op_pre = (tvm_opcode_code (opcode))) ” 
  &&  “ ((tvm_opcode_code (opcode)) <> 22) ” 
  &&  “ ((cm_patch_code (policy) (p) (raw_prefix)) = done) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (cons ((TVMInst (opcode) (immediate_pre))) ((@nil tvm_inst))) )
.

Definition cm_emit_resolved_partial_solve_wit_1 := cm_emit_resolved_partial_solve_wit_1_pure -> cm_emit_resolved_partial_solve_wit_1_aux.

(*----- Function cm_emit_resolved_call -----*)

Definition cm_emit_resolved_call_safety_wit_1 := 
forall (function_id_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : (22 = (tvm_opcode_code (TVMCallOp)))) (PreH2 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "function_id" ) )) # Int  |-> function_id_pre)
  **  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (cons ((TVMInst (TVMCallOp) (function_id_pre))) ((@nil tvm_inst))) )
|--
  “ (22 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 22) ”
.

Definition cm_emit_resolved_call_entail_wit_1 := 
(
forall (function_id_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (((Zlength (done)) + 1 ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  EX (raw_prefix: (@list tvm_inst)) ,
  “ (22 = (tvm_opcode_code (TVMCallOp))) ” 
  &&  “ ((cm_patch_code (policy) (p) (raw_prefix)) = done) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (cons ((TVMInst (TVMCallOp) (function_id_pre))) ((@nil tvm_inst))) )
) \/
(
forall (function_id_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (((Zlength (done)) + 1 ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  EX (raw_prefix: (@list tvm_inst)) ,
  “ (22 = (tvm_opcode_code (TVMCallOp))) ” 
  &&  “ ((cm_patch_code (policy) (p) (raw_prefix)) = done) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (cons ((TVMInst (TVMCallOp) (function_id_pre))) ((@nil tvm_inst))) )
).

Definition cm_emit_resolved_call_return_wit_1 := 
(
forall (function_id_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : (22 = (tvm_opcode_code (TVMCallOp)))) (PreH2 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (raw_prefix) ((cons ((TVMInst (TVMCallOp) (function_id_pre))) ((@nil tvm_inst))))) (@nil tvm_inst) )
|--
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (function_id_pre))))) ((@nil tvm_inst))))) )
) \/
(
forall (function_id_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : (22 = (tvm_opcode_code (TVMCallOp)))) (PreH2 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (raw_prefix) ((cons ((TVMInst (TVMCallOp) (function_id_pre))) ((@nil tvm_inst))))) (@nil tvm_inst) )
|--
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (function_id_pre))))) ((@nil tvm_inst))))) )
).

Definition cm_emit_resolved_call_return_wit_1_split_goal_spatial := 
forall (function_id_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : (22 = (tvm_opcode_code (TVMCallOp)))) (PreH2 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (raw_prefix) ((cons ((TVMInst (TVMCallOp) (function_id_pre))) ((@nil tvm_inst))))) (@nil tvm_inst) )
|--
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (function_id_pre))))) ((@nil tvm_inst))))) )
.

Definition cm_emit_resolved_call_partial_solve_wit_1_pure := 
forall (function_id_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : (22 = (tvm_opcode_code (TVMCallOp)))) (PreH2 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "function_id" ) )) # Int  |-> function_id_pre)
  **  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (cons ((TVMInst (TVMCallOp) (function_id_pre))) ((@nil tvm_inst))) )
|--
  “ (22 = (tvm_opcode_code (TVMCallOp))) ”
.

Definition cm_emit_resolved_call_partial_solve_wit_1_aux := 
forall (function_id_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : (22 = (tvm_opcode_code (TVMCallOp)))) (PreH2 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (cons ((TVMInst (TVMCallOp) (function_id_pre))) ((@nil tvm_inst))) )
|--
  “ (22 = (tvm_opcode_code (TVMCallOp))) ” 
  &&  “ (22 = (tvm_opcode_code (TVMCallOp))) ” 
  &&  “ ((cm_patch_code (policy) (p) (raw_prefix)) = done) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (cons ((TVMInst (TVMCallOp) (function_id_pre))) ((@nil tvm_inst))) )
.

Definition cm_emit_resolved_call_partial_solve_wit_1 := cm_emit_resolved_call_partial_solve_wit_1_pure -> cm_emit_resolved_call_partial_solve_wit_1_aux.

(*----- Function cm_emit_resolved_normalize -----*)

Definition cm_emit_resolved_normalize_entail_wit_1 := 
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) (PreH3 : (((Zlength (done)) + (Zlength ((cm_char_normalize_code (model_ty)))) ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  EX (raw_prefix: (@list tvm_inst)) ,
  “ (ty_pre = (cm_type_encode (model_ty))) ” 
  &&  “ (cm_type_code_wf model_ty ) ” 
  &&  “ ((cm_patch_code (policy) (p) (raw_prefix)) = done) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (app ((cm_char_normalize_code (model_ty))) ((@nil tvm_inst))) )
) \/
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) (PreH3 : (((Zlength (done)) + (Zlength ((cm_char_normalize_code (model_ty)))) ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  EX (raw_prefix: (@list tvm_inst)) ,
  “ (ty_pre = (cm_type_encode (model_ty))) ” 
  &&  “ (cm_type_code_wf model_ty ) ” 
  &&  “ ((cm_patch_code (policy) (p) (raw_prefix)) = done) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (app ((cm_char_normalize_code (model_ty))) ((@nil tvm_inst))) )
).

Definition cm_emit_resolved_normalize_return_wit_1 := 
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) (PreH3 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (raw_prefix) ((cm_char_normalize_code (model_ty)))) (@nil tvm_inst) )
|--
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_char_normalize_code (model_ty)))) )
) \/
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) (PreH3 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (raw_prefix) ((cm_char_normalize_code (model_ty)))) (@nil tvm_inst) )
|--
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_char_normalize_code (model_ty)))) )
).

Definition cm_emit_resolved_normalize_return_wit_1_split_goal_spatial := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) (PreH3 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (raw_prefix) ((cm_char_normalize_code (model_ty)))) (@nil tvm_inst) )
|--
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_char_normalize_code (model_ty)))) )
.

Definition cm_emit_resolved_normalize_partial_solve_wit_1_pure := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) (PreH3 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (app ((cm_char_normalize_code (model_ty))) ((@nil tvm_inst))) )
|--
  “ (ty_pre = (cm_type_encode (model_ty))) ” 
  &&  “ (cm_type_code_wf model_ty ) ”
.

Definition cm_emit_resolved_normalize_partial_solve_wit_1_aux := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) (PreH3 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (app ((cm_char_normalize_code (model_ty))) ((@nil tvm_inst))) )
|--
  “ (ty_pre = (cm_type_encode (model_ty))) ” 
  &&  “ (cm_type_code_wf model_ty ) ” 
  &&  “ (ty_pre = (cm_type_encode (model_ty))) ” 
  &&  “ (cm_type_code_wf model_ty ) ” 
  &&  “ ((cm_patch_code (policy) (p) (raw_prefix)) = done) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (app ((cm_char_normalize_code (model_ty))) ((@nil tvm_inst))) )
.

Definition cm_emit_resolved_normalize_partial_solve_wit_1 := cm_emit_resolved_normalize_partial_solve_wit_1_pure -> cm_emit_resolved_normalize_partial_solve_wit_1_aux.

(*----- Function cm_emit_resolved_load -----*)

Definition cm_emit_resolved_load_entail_wit_1 := 
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) (PreH3 : (((Zlength (done)) + (Zlength ((cm_load_code (model_ty)))) ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  EX (raw_prefix: (@list tvm_inst)) ,
  “ (ty_pre = (cm_type_encode (model_ty))) ” 
  &&  “ (cm_type_code_wf model_ty ) ” 
  &&  “ ((cm_patch_code (policy) (p) (raw_prefix)) = done) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (app ((cm_load_code (model_ty))) ((@nil tvm_inst))) )
) \/
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) (PreH3 : (((Zlength (done)) + (Zlength ((cm_load_code (model_ty)))) ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  EX (raw_prefix: (@list tvm_inst)) ,
  “ (ty_pre = (cm_type_encode (model_ty))) ” 
  &&  “ (cm_type_code_wf model_ty ) ” 
  &&  “ ((cm_patch_code (policy) (p) (raw_prefix)) = done) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (app ((cm_load_code (model_ty))) ((@nil tvm_inst))) )
).

Definition cm_emit_resolved_load_return_wit_1 := 
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) (PreH3 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (raw_prefix) ((cm_load_code (model_ty)))) (@nil tvm_inst) )
|--
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_load_code (model_ty)))) )
) \/
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) (PreH3 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (raw_prefix) ((cm_load_code (model_ty)))) (@nil tvm_inst) )
|--
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_load_code (model_ty)))) )
).

Definition cm_emit_resolved_load_return_wit_1_split_goal_spatial := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) (PreH3 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (raw_prefix) ((cm_load_code (model_ty)))) (@nil tvm_inst) )
|--
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_load_code (model_ty)))) )
.

Definition cm_emit_resolved_load_partial_solve_wit_1_pure := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) (PreH3 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (app ((cm_load_code (model_ty))) ((@nil tvm_inst))) )
|--
  “ (ty_pre = (cm_type_encode (model_ty))) ” 
  &&  “ (cm_type_code_wf model_ty ) ”
.

Definition cm_emit_resolved_load_partial_solve_wit_1_aux := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) (PreH3 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (app ((cm_load_code (model_ty))) ((@nil tvm_inst))) )
|--
  “ (ty_pre = (cm_type_encode (model_ty))) ” 
  &&  “ (cm_type_code_wf model_ty ) ” 
  &&  “ (ty_pre = (cm_type_encode (model_ty))) ” 
  &&  “ (cm_type_code_wf model_ty ) ” 
  &&  “ ((cm_patch_code (policy) (p) (raw_prefix)) = done) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (app ((cm_load_code (model_ty))) ((@nil tvm_inst))) )
.

Definition cm_emit_resolved_load_partial_solve_wit_1 := cm_emit_resolved_load_partial_solve_wit_1_pure -> cm_emit_resolved_load_partial_solve_wit_1_aux.

(*----- Function cm_emit_resolved_store -----*)

Definition cm_emit_resolved_store_entail_wit_1 := 
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) (PreH3 : (((Zlength (done)) + (Zlength ((cm_store_code (model_ty)))) ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  EX (raw_prefix: (@list tvm_inst)) ,
  “ (ty_pre = (cm_type_encode (model_ty))) ” 
  &&  “ (cm_type_code_wf model_ty ) ” 
  &&  “ ((cm_patch_code (policy) (p) (raw_prefix)) = done) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (app ((cm_store_code (model_ty))) ((@nil tvm_inst))) )
) \/
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) (PreH3 : (((Zlength (done)) + (Zlength ((cm_store_code (model_ty)))) ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  EX (raw_prefix: (@list tvm_inst)) ,
  “ (ty_pre = (cm_type_encode (model_ty))) ” 
  &&  “ (cm_type_code_wf model_ty ) ” 
  &&  “ ((cm_patch_code (policy) (p) (raw_prefix)) = done) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (app ((cm_store_code (model_ty))) ((@nil tvm_inst))) )
).

Definition cm_emit_resolved_store_return_wit_1 := 
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) (PreH3 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (raw_prefix) ((cm_store_code (model_ty)))) (@nil tvm_inst) )
|--
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_store_code (model_ty)))) )
) \/
(
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) (PreH3 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (raw_prefix) ((cm_store_code (model_ty)))) (@nil tvm_inst) )
|--
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_store_code (model_ty)))) )
).

Definition cm_emit_resolved_store_return_wit_1_split_goal_spatial := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) (PreH3 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (raw_prefix) ((cm_store_code (model_ty)))) (@nil tvm_inst) )
|--
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_store_code (model_ty)))) )
.

Definition cm_emit_resolved_store_partial_solve_wit_1_pure := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) (PreH3 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (app ((cm_store_code (model_ty))) ((@nil tvm_inst))) )
|--
  “ (ty_pre = (cm_type_encode (model_ty))) ” 
  &&  “ (cm_type_code_wf model_ty ) ”
.

Definition cm_emit_resolved_store_partial_solve_wit_1_aux := 
forall (ty_pre: Z) (emitter_pre: Z) (model_ty: cm_type) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) (PreH3 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (app ((cm_store_code (model_ty))) ((@nil tvm_inst))) )
|--
  “ (ty_pre = (cm_type_encode (model_ty))) ” 
  &&  “ (cm_type_code_wf model_ty ) ” 
  &&  “ (ty_pre = (cm_type_encode (model_ty))) ” 
  &&  “ (cm_type_code_wf model_ty ) ” 
  &&  “ ((cm_patch_code (policy) (p) (raw_prefix)) = done) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (app ((cm_store_code (model_ty))) ((@nil tvm_inst))) )
.

Definition cm_emit_resolved_store_partial_solve_wit_1 := cm_emit_resolved_store_partial_solve_wit_1_pure -> cm_emit_resolved_store_partial_solve_wit_1_aux.

(*----- Function cm_emit_resolved_fp_address -----*)

Definition cm_emit_resolved_fp_address_entail_wit_1 := 
(
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (((Zlength (done)) + (Zlength ((cm_fp_relative_address_code (offset_pre)))) ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  EX (raw_prefix: (@list tvm_inst)) ,
  “ ((cm_patch_code (policy) (p) (raw_prefix)) = done) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (app ((cm_fp_relative_address_code (offset_pre))) ((@nil tvm_inst))) )
) \/
(
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (((Zlength (done)) + (Zlength ((cm_fp_relative_address_code (offset_pre)))) ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  EX (raw_prefix: (@list tvm_inst)) ,
  “ ((cm_patch_code (policy) (p) (raw_prefix)) = done) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (app ((cm_fp_relative_address_code (offset_pre))) ((@nil tvm_inst))) )
).

Definition cm_emit_resolved_fp_address_return_wit_1 := 
(
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (raw_prefix) ((cm_fp_relative_address_code (offset_pre)))) (@nil tvm_inst) )
|--
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_fp_relative_address_code (offset_pre)))) )
) \/
(
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (raw_prefix) ((cm_fp_relative_address_code (offset_pre)))) (@nil tvm_inst) )
|--
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_fp_relative_address_code (offset_pre)))) )
).

Definition cm_emit_resolved_fp_address_return_wit_1_split_goal_spatial := 
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  (cm_emitter_plan_rep emitter_pre out capacity (app (raw_prefix) ((cm_fp_relative_address_code (offset_pre)))) (@nil tvm_inst) )
|--
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_fp_relative_address_code (offset_pre)))) )
.

Definition cm_emit_resolved_fp_address_partial_solve_wit_1 := 
forall (offset_pre: Z) (emitter_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (app ((cm_fp_relative_address_code (offset_pre))) ((@nil tvm_inst))) )
|--
  “ ((cm_patch_code (policy) (p) (raw_prefix)) = done) ”
  &&  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (app ((cm_fp_relative_address_code (offset_pre))) ((@nil tvm_inst))) )
.

(*----- Function cm_emit_resolved_temp_store -----*)

Definition cm_emit_resolved_temp_store_entail_wit_1 := 
(
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH9 : (((Zlength (done)) + (Zlength ((cm_temp_store_code (policy) (p) (fid) (temp_pre)))) ) <= capacity)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  EX (raw_prefix: (@list tvm_inst)) ,
  “ (0 <= temp_pre) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX) ” 
  &&  “ ((cm_patch_code (policy) (p) (raw_prefix)) = done) ”
  &&  (cm_function_context_rep fn_pre f body next )
  **  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (app ((cm_temp_store_code (policy) (p) (fid) (temp_pre))) ((@nil tvm_inst))) )
) \/
(
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH9 : (((Zlength (done)) + (Zlength ((cm_temp_store_code (policy) (p) (fid) (temp_pre)))) ) <= capacity)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  EX (raw_prefix: (@list tvm_inst)) ,
  “ (0 <= temp_pre) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX) ” 
  &&  “ ((cm_patch_code (policy) (p) (raw_prefix)) = done) ”
  &&  (cm_function_context_rep fn_pre f body next )
  **  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (app ((cm_temp_store_code (policy) (p) (fid) (temp_pre))) ((@nil tvm_inst))) )
).

Definition cm_emit_resolved_temp_store_return_wit_1 := 
(
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH9 : (0 <= temp_pre)) (PreH10 : (structs = (cm_program_structs (p)))) (PreH11 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH12 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH13 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH14 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH15 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH16 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH17 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_emitter_plan_rep emitter_pre out capacity (app (raw_prefix) ((cm_temp_store_code (policy) (p) (fid) (temp_pre)))) (@nil tvm_inst) )
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
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_temp_store_code (policy) (p) (fid) (temp_pre)))) )
) \/
(
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH9 : (0 <= temp_pre)) (PreH10 : (structs = (cm_program_structs (p)))) (PreH11 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH12 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH13 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH14 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH15 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH16 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH17 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_emitter_plan_rep emitter_pre out capacity (app (raw_prefix) ((cm_temp_store_code (policy) (p) (fid) (temp_pre)))) (@nil tvm_inst) )
|--
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_temp_store_code (policy) (p) (fid) (temp_pre)))) )
).

Definition cm_emit_resolved_temp_store_return_wit_1_split_goal_spatial := 
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH9 : (0 <= temp_pre)) (PreH10 : (structs = (cm_program_structs (p)))) (PreH11 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH12 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH13 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH14 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH15 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH16 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH17 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_emitter_plan_rep emitter_pre out capacity (app (raw_prefix) ((cm_temp_store_code (policy) (p) (fid) (temp_pre)))) (@nil tvm_inst) )
|--
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_temp_store_code (policy) (p) (fid) (temp_pre)))) )
.

Definition cm_emit_resolved_temp_store_partial_solve_wit_1_pure := 
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH9 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (app ((cm_temp_store_code (policy) (p) (fid) (temp_pre))) ((@nil tvm_inst))) )
|--
  “ (0 <= temp_pre) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX) ”
.

Definition cm_emit_resolved_temp_store_partial_solve_wit_1_aux := 
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH9 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (app ((cm_temp_store_code (policy) (p) (fid) (temp_pre))) ((@nil tvm_inst))) )
|--
  “ (0 <= temp_pre) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX) ” 
  &&  “ (0 <= temp_pre) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX) ” 
  &&  “ ((cm_patch_code (policy) (p) (raw_prefix)) = done) ”
  &&  (cm_function_context_rep fn_pre f body next )
  **  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (app ((cm_temp_store_code (policy) (p) (fid) (temp_pre))) ((@nil tvm_inst))) )
.

Definition cm_emit_resolved_temp_store_partial_solve_wit_1 := cm_emit_resolved_temp_store_partial_solve_wit_1_pure -> cm_emit_resolved_temp_store_partial_solve_wit_1_aux.

(*----- Function cm_emit_resolved_temp_load -----*)

Definition cm_emit_resolved_temp_load_entail_wit_1 := 
(
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH9 : (((Zlength (done)) + (Zlength ((cm_temp_load_code (policy) (p) (fid) (temp_pre)))) ) <= capacity)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  EX (raw_prefix: (@list tvm_inst)) ,
  “ (0 <= temp_pre) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX) ” 
  &&  “ ((cm_patch_code (policy) (p) (raw_prefix)) = done) ”
  &&  (cm_function_context_rep fn_pre f body next )
  **  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (app ((cm_temp_load_code (policy) (p) (fid) (temp_pre))) ((@nil tvm_inst))) )
) \/
(
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH9 : (((Zlength (done)) + (Zlength ((cm_temp_load_code (policy) (p) (fid) (temp_pre)))) ) <= capacity)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  EX (raw_prefix: (@list tvm_inst)) ,
  “ (0 <= temp_pre) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX) ” 
  &&  “ ((cm_patch_code (policy) (p) (raw_prefix)) = done) ”
  &&  (cm_function_context_rep fn_pre f body next )
  **  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (app ((cm_temp_load_code (policy) (p) (fid) (temp_pre))) ((@nil tvm_inst))) )
).

Definition cm_emit_resolved_temp_load_return_wit_1 := 
(
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH9 : (0 <= temp_pre)) (PreH10 : (structs = (cm_program_structs (p)))) (PreH11 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH12 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH13 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH14 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH15 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH16 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH17 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_emitter_plan_rep emitter_pre out capacity (app (raw_prefix) ((cm_temp_load_code (policy) (p) (fid) (temp_pre)))) (@nil tvm_inst) )
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
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_temp_load_code (policy) (p) (fid) (temp_pre)))) )
) \/
(
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH9 : (0 <= temp_pre)) (PreH10 : (structs = (cm_program_structs (p)))) (PreH11 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH12 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH13 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH14 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH15 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH16 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH17 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_emitter_plan_rep emitter_pre out capacity (app (raw_prefix) ((cm_temp_load_code (policy) (p) (fid) (temp_pre)))) (@nil tvm_inst) )
|--
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_temp_load_code (policy) (p) (fid) (temp_pre)))) )
).

Definition cm_emit_resolved_temp_load_return_wit_1_split_goal_spatial := 
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH9 : (0 <= temp_pre)) (PreH10 : (structs = (cm_program_structs (p)))) (PreH11 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH12 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH13 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH14 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH15 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH16 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH17 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_emitter_plan_rep emitter_pre out capacity (app (raw_prefix) ((cm_temp_load_code (policy) (p) (fid) (temp_pre)))) (@nil tvm_inst) )
|--
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_temp_load_code (policy) (p) (fid) (temp_pre)))) )
.

Definition cm_emit_resolved_temp_load_partial_solve_wit_1_pure := 
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH9 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (app ((cm_temp_load_code (policy) (p) (fid) (temp_pre))) ((@nil tvm_inst))) )
|--
  “ (0 <= temp_pre) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX) ”
.

Definition cm_emit_resolved_temp_load_partial_solve_wit_1_aux := 
forall (emitter_pre: Z) (temp_pre: Z) (fn_pre: Z) (next: Z) (body: Z) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (PreH1 : (0 <= temp_pre)) (PreH2 : (structs = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH5 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX)) (PreH9 : ((cm_patch_code (policy) (p) (raw_prefix)) = done)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (app ((cm_temp_load_code (policy) (p) (fid) (temp_pre))) ((@nil tvm_inst))) )
|--
  “ (0 <= temp_pre) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX) ” 
  &&  “ (0 <= temp_pre) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_pre)) <= INT_MAX) ” 
  &&  “ ((cm_patch_code (policy) (p) (raw_prefix)) = done) ”
  &&  (cm_function_context_rep fn_pre f body next )
  **  (cm_emitter_plan_rep emitter_pre out capacity raw_prefix (app ((cm_temp_load_code (policy) (p) (fid) (temp_pre))) ((@nil tvm_inst))) )
.

Definition cm_emit_resolved_temp_load_partial_solve_wit_1 := cm_emit_resolved_temp_load_partial_solve_wit_1_pure -> cm_emit_resolved_temp_load_partial_solve_wit_1_aux.

Module Type VC_Correct.


Axiom proof_of_cm_emit_resolved_entail_wit_1 : cm_emit_resolved_entail_wit_1.
Axiom proof_of_cm_emit_resolved_return_wit_1 : cm_emit_resolved_return_wit_1.
Axiom proof_of_cm_emit_resolved_partial_solve_wit_1_pure : cm_emit_resolved_partial_solve_wit_1_pure.
Axiom proof_of_cm_emit_resolved_partial_solve_wit_1 : cm_emit_resolved_partial_solve_wit_1.
Axiom proof_of_cm_emit_resolved_call_safety_wit_1 : cm_emit_resolved_call_safety_wit_1.
Axiom proof_of_cm_emit_resolved_call_entail_wit_1 : cm_emit_resolved_call_entail_wit_1.
Axiom proof_of_cm_emit_resolved_call_return_wit_1 : cm_emit_resolved_call_return_wit_1.
Axiom proof_of_cm_emit_resolved_call_partial_solve_wit_1_pure : cm_emit_resolved_call_partial_solve_wit_1_pure.
Axiom proof_of_cm_emit_resolved_call_partial_solve_wit_1 : cm_emit_resolved_call_partial_solve_wit_1.
Axiom proof_of_cm_emit_resolved_normalize_entail_wit_1 : cm_emit_resolved_normalize_entail_wit_1.
Axiom proof_of_cm_emit_resolved_normalize_return_wit_1 : cm_emit_resolved_normalize_return_wit_1.
Axiom proof_of_cm_emit_resolved_normalize_partial_solve_wit_1_pure : cm_emit_resolved_normalize_partial_solve_wit_1_pure.
Axiom proof_of_cm_emit_resolved_normalize_partial_solve_wit_1 : cm_emit_resolved_normalize_partial_solve_wit_1.
Axiom proof_of_cm_emit_resolved_load_entail_wit_1 : cm_emit_resolved_load_entail_wit_1.
Axiom proof_of_cm_emit_resolved_load_return_wit_1 : cm_emit_resolved_load_return_wit_1.
Axiom proof_of_cm_emit_resolved_load_partial_solve_wit_1_pure : cm_emit_resolved_load_partial_solve_wit_1_pure.
Axiom proof_of_cm_emit_resolved_load_partial_solve_wit_1 : cm_emit_resolved_load_partial_solve_wit_1.
Axiom proof_of_cm_emit_resolved_store_entail_wit_1 : cm_emit_resolved_store_entail_wit_1.
Axiom proof_of_cm_emit_resolved_store_return_wit_1 : cm_emit_resolved_store_return_wit_1.
Axiom proof_of_cm_emit_resolved_store_partial_solve_wit_1_pure : cm_emit_resolved_store_partial_solve_wit_1_pure.
Axiom proof_of_cm_emit_resolved_store_partial_solve_wit_1 : cm_emit_resolved_store_partial_solve_wit_1.
Axiom proof_of_cm_emit_resolved_fp_address_entail_wit_1 : cm_emit_resolved_fp_address_entail_wit_1.
Axiom proof_of_cm_emit_resolved_fp_address_return_wit_1 : cm_emit_resolved_fp_address_return_wit_1.
Axiom proof_of_cm_emit_resolved_fp_address_partial_solve_wit_1 : cm_emit_resolved_fp_address_partial_solve_wit_1.
Axiom proof_of_cm_emit_resolved_temp_store_entail_wit_1 : cm_emit_resolved_temp_store_entail_wit_1.
Axiom proof_of_cm_emit_resolved_temp_store_return_wit_1 : cm_emit_resolved_temp_store_return_wit_1.
Axiom proof_of_cm_emit_resolved_temp_store_partial_solve_wit_1_pure : cm_emit_resolved_temp_store_partial_solve_wit_1_pure.
Axiom proof_of_cm_emit_resolved_temp_store_partial_solve_wit_1 : cm_emit_resolved_temp_store_partial_solve_wit_1.
Axiom proof_of_cm_emit_resolved_temp_load_entail_wit_1 : cm_emit_resolved_temp_load_entail_wit_1.
Axiom proof_of_cm_emit_resolved_temp_load_return_wit_1 : cm_emit_resolved_temp_load_return_wit_1.
Axiom proof_of_cm_emit_resolved_temp_load_partial_solve_wit_1_pure : cm_emit_resolved_temp_load_partial_solve_wit_1_pure.
Axiom proof_of_cm_emit_resolved_temp_load_partial_solve_wit_1 : cm_emit_resolved_temp_load_partial_solve_wit_1.

End VC_Correct.
