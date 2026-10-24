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
Require Import SimpleC.EE.QCP_demos_human.cmc_emit_expr_leaf_migration_lib.
Local Open Scope sac.

(*----- Function cmc_const_immediate -----*)

Definition cmc_const_immediate_safety_wit_1 := 
forall (ty_pre: Z) (value_pre: Z) (model_ty: cm_type) (PreH1 : (ty_pre = (cm_type_encode (model_ty)))) (PreH2 : (cm_type_code_wf model_ty )) ,
  ((( &( "value" ) )) # Int64  |-> value_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmc_const_immediate_safety_wit_2 := 
forall (ty_pre: Z) (value_pre: Z) (model_ty: cm_type) (PreH1 : (ty_pre = 1)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) ,
  ((( &( "byte" ) )) # UChar  |->_)
  **  ((( &( "bits" ) )) # UInt64  |-> (unsigned_last_nbits (value_pre) (64)))
  **  ((( &( "value" ) )) # Int64  |-> value_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (256 <> 0) ”
.

Definition cmc_const_immediate_return_wit_1 := 
(
forall (ty_pre: Z) (value_pre: Z) (model_ty: cm_type) (PreH1 : (ty_pre <> 1)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) ,
  TT && emp 
|--
  “ (ty_pre = (cm_type_encode (model_ty))) ” 
  &&  “ (cm_type_code_wf model_ty ) ” 
  &&  “ (value_pre = (cm_const_immediate (model_ty) (value_pre))) ”
  &&  emp
) \/
(
forall (ty_pre: Z) (value_pre: Z) (model_ty: cm_type) (PreH1 : (ty_pre <> 1)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) ,
  TT && emp 
|--
  “ (value_pre = (cm_const_immediate (model_ty) (value_pre))) ”
  &&  emp
).

Definition cmc_const_immediate_return_wit_1_split_goal_1 := 
forall (ty_pre: Z) (value_pre: Z) (model_ty: cm_type) (PreH1 : (ty_pre <> 1)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) ,
  (value_pre = (cm_const_immediate (model_ty) (value_pre)))
.

Definition cmc_const_immediate_return_wit_2 := 
(
forall (ty_pre: Z) (value_pre: Z) (model_ty: cm_type) (PreH1 : (ty_pre = 1)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) ,
  TT && emp 
|--
  “ (ty_pre = (cm_type_encode (model_ty))) ” 
  &&  “ (cm_type_code_wf model_ty ) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (value_pre) (64)) % ( 256 ) )) (8)) = (cm_const_immediate (model_ty) (value_pre))) ”
  &&  emp
) \/
(
forall (ty_pre: Z) (value_pre: Z) (model_ty: cm_type) (PreH1 : (ty_pre = 1)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) ,
  TT && emp 
|--
  “ ((unsigned_last_nbits (((unsigned_last_nbits (value_pre) (64)) % ( 256 ) )) (8)) = (cm_const_immediate (model_ty) (value_pre))) ”
  &&  emp
).

Definition cmc_const_immediate_return_wit_2_split_goal_1 := 
forall (ty_pre: Z) (value_pre: Z) (model_ty: cm_type) (PreH1 : (ty_pre = 1)) (PreH2 : (ty_pre = (cm_type_encode (model_ty)))) (PreH3 : (cm_type_code_wf model_ty )) ,
  ((unsigned_last_nbits (((unsigned_last_nbits (value_pre) (64)) % ( 256 ) )) (8)) = (cm_const_immediate (model_ty) (value_pre)))
.

(*----- Function cm_emit_const_expr -----*)

Definition cm_emit_const_expr_safety_wit_1 := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (n: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (lvalue_pre = 0)) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH4 : (cm_type_code_wf ty )) (PreH5 : (retval = (cm_const_immediate (ty) (n)))) (PreH6 : (lvalue_pre = 0)) (PreH7 : (expr_pre <> 0)) (PreH8 : (0 <= lvalue_pre)) (PreH9 : (lvalue_pre <= 1)) (PreH10 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH11 : (e = (CMConstE (n) (ty)))) (PreH12 : (cm_type_code_wf ty )) ,
  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) ((cm_const_immediate (ty) (n))))) (tail)) )
  **  ((( &( "immediate" ) )) # Int64  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> n)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_emit_const_expr_entail_wit_1 := 
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (n: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= lvalue_pre)) (PreH2 : (lvalue_pre <= 1)) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (e = (CMConstE (n) (ty)))) (PreH5 : (cm_type_code_wf ty )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafConst (n) (ty))) (lvalue_pre))) (tail)) )
|--
  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (e = (CMConstE (n) (ty))) ” 
  &&  “ (cm_type_code_wf ty ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> n)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafConst (n) (ty))) (lvalue_pre))) (tail)) )
) \/
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (n: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= lvalue_pre)) (PreH2 : (lvalue_pre <= 1)) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (e = (CMConstE (n) (ty)))) (PreH5 : (cm_type_code_wf ty )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafConst (n) (ty))) (lvalue_pre))) (tail)) )
|--
  “ (expr_pre <> 0) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> n)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafConst (n) (ty))) (lvalue_pre))) (tail)) )
).

Definition cm_emit_const_expr_entail_wit_1_split_goal_1 := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (n: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= lvalue_pre)) (PreH2 : (lvalue_pre <= 1)) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (e = (CMConstE (n) (ty)))) (PreH5 : (cm_type_code_wf ty )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafConst (n) (ty))) (lvalue_pre))) (tail)) )
|--
  “ (expr_pre <> 0) ”
.

Definition cm_emit_const_expr_entail_wit_1_split_goal_spatial := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (n: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= lvalue_pre)) (PreH2 : (lvalue_pre <= 1)) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (e = (CMConstE (n) (ty)))) (PreH5 : (cm_type_code_wf ty )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafConst (n) (ty))) (lvalue_pre))) (tail)) )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> n)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafConst (n) (ty))) (lvalue_pre))) (tail)) )
.

Definition cm_emit_const_expr_return_wit_1 := 
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (n: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (lvalue_pre = 0)) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH4 : (cm_type_code_wf ty )) (PreH5 : (retval = (cm_const_immediate (ty) (n)))) (PreH6 : (lvalue_pre = 0)) (PreH7 : (expr_pre <> 0)) (PreH8 : (0 <= lvalue_pre)) (PreH9 : (lvalue_pre <= 1)) (PreH10 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH11 : (e = (CMConstE (n) (ty)))) (PreH12 : (cm_type_code_wf ty )) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMPushOp) (retval))) ((@nil tvm_inst))))) tail )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> n)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
|--
  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (e = (CMConstE (n) (ty))) ” 
  &&  “ (cm_type_code_wf ty ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_leaf_code_for (p) ((CMLeafConst (n) (ty))) (lvalue_pre)))) tail )
) \/
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (n: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (n <= INT64_MAX)) (PreH2 : (n >= INT64_MIN)) (PreH3 : ((cm_type_encode (ty)) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode (ty)) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (lvalue_pre = 0)) (PreH10 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH11 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH12 : (cm_type_code_wf ty )) (PreH13 : (retval = (cm_const_immediate (ty) (n)))) (PreH14 : (lvalue_pre = 0)) (PreH15 : (expr_pre <> 0)) (PreH16 : (0 <= lvalue_pre)) (PreH17 : (lvalue_pre <= 1)) (PreH18 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH19 : (e = (CMConstE (n) (ty)))) (PreH20 : (cm_type_code_wf ty )) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMPushOp) (retval))) ((@nil tvm_inst))))) tail )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> n)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_leaf_code_for (p) ((CMLeafConst (n) (ty))) (lvalue_pre)))) tail )
).

Definition cm_emit_const_expr_return_wit_1_split_goal_spatial := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (n: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (n <= INT64_MAX)) (PreH2 : (n >= INT64_MIN)) (PreH3 : ((cm_type_encode (ty)) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode (ty)) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (lvalue_pre = 0)) (PreH10 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH11 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH12 : (cm_type_code_wf ty )) (PreH13 : (retval = (cm_const_immediate (ty) (n)))) (PreH14 : (lvalue_pre = 0)) (PreH15 : (expr_pre <> 0)) (PreH16 : (0 <= lvalue_pre)) (PreH17 : (lvalue_pre <= 1)) (PreH18 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH19 : (e = (CMConstE (n) (ty)))) (PreH20 : (cm_type_code_wf ty )) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMPushOp) (retval))) ((@nil tvm_inst))))) tail )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> n)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_leaf_code_for (p) ((CMLeafConst (n) (ty))) (lvalue_pre)))) tail )
.

Definition cm_emit_const_expr_return_wit_2 := 
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (n: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (lvalue_pre <> 0)) (PreH2 : (expr_pre <> 0)) (PreH3 : (0 <= lvalue_pre)) (PreH4 : (lvalue_pre <= 1)) (PreH5 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH6 : (e = (CMConstE (n) (ty)))) (PreH7 : (cm_type_code_wf ty )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> n)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafConst (n) (ty))) (lvalue_pre))) (tail)) )
|--
  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (e = (CMConstE (n) (ty))) ” 
  &&  “ (cm_type_code_wf ty ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_leaf_code_for (p) ((CMLeafConst (n) (ty))) (lvalue_pre)))) tail )
) \/
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (n: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (n <= INT64_MAX)) (PreH2 : (n >= INT64_MIN)) (PreH3 : ((cm_type_encode (ty)) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode (ty)) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (lvalue_pre <> 0)) (PreH10 : (expr_pre <> 0)) (PreH11 : (0 <= lvalue_pre)) (PreH12 : (lvalue_pre <= 1)) (PreH13 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH14 : (e = (CMConstE (n) (ty)))) (PreH15 : (cm_type_code_wf ty )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> n)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafConst (n) (ty))) (lvalue_pre))) (tail)) )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_leaf_code_for (p) ((CMLeafConst (n) (ty))) (lvalue_pre)))) tail )
).

Definition cm_emit_const_expr_return_wit_2_split_goal_spatial := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (n: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (n <= INT64_MAX)) (PreH2 : (n >= INT64_MIN)) (PreH3 : ((cm_type_encode (ty)) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode (ty)) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (lvalue_pre <> 0)) (PreH10 : (expr_pre <> 0)) (PreH11 : (0 <= lvalue_pre)) (PreH12 : (lvalue_pre <= 1)) (PreH13 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH14 : (e = (CMConstE (n) (ty)))) (PreH15 : (cm_type_code_wf ty )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> n)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafConst (n) (ty))) (lvalue_pre))) (tail)) )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_leaf_code_for (p) ((CMLeafConst (n) (ty))) (lvalue_pre)))) tail )
.

Definition cm_emit_const_expr_partial_solve_wit_1_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (n: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (lvalue_pre = 0)) (PreH2 : (expr_pre <> 0)) (PreH3 : (0 <= lvalue_pre)) (PreH4 : (lvalue_pre <= 1)) (PreH5 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH6 : (e = (CMConstE (n) (ty)))) (PreH7 : (cm_type_code_wf ty )) ,
  ((( &( "immediate" ) )) # Int64  |->_)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> n)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafConst (n) (ty))) (lvalue_pre))) (tail)) )
|--
  “ ((cm_type_encode (ty)) = (cm_type_encode (ty))) ” 
  &&  “ (cm_type_code_wf ty ) ”
.

Definition cm_emit_const_expr_partial_solve_wit_1_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (n: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (lvalue_pre = 0)) (PreH2 : (expr_pre <> 0)) (PreH3 : (0 <= lvalue_pre)) (PreH4 : (lvalue_pre <= 1)) (PreH5 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH6 : (e = (CMConstE (n) (ty)))) (PreH7 : (cm_type_code_wf ty )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> n)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafConst (n) (ty))) (lvalue_pre))) (tail)) )
|--
  “ ((cm_type_encode (ty)) = (cm_type_encode (ty))) ” 
  &&  “ (cm_type_code_wf ty ) ” 
  &&  “ (lvalue_pre = 0) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (e = (CMConstE (n) (ty))) ” 
  &&  “ (cm_type_code_wf ty ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> n)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafConst (n) (ty))) (lvalue_pre))) (tail)) )
.

Definition cm_emit_const_expr_partial_solve_wit_1 := cm_emit_const_expr_partial_solve_wit_1_pure -> cm_emit_const_expr_partial_solve_wit_1_aux.

Definition cm_emit_const_expr_partial_solve_wit_2_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (n: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (retval: Z) (PreH1 : ((cm_type_encode (ty)) = (cm_type_encode (ty)))) (PreH2 : (cm_type_code_wf ty )) (PreH3 : (retval = (cm_const_immediate (ty) (n)))) (PreH4 : (lvalue_pre = 0)) (PreH5 : (expr_pre <> 0)) (PreH6 : (0 <= lvalue_pre)) (PreH7 : (lvalue_pre <= 1)) (PreH8 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH9 : (e = (CMConstE (n) (ty)))) (PreH10 : (cm_type_code_wf ty )) ,
  ((( &( "immediate" ) )) # Int64  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> n)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafConst (n) (ty))) (lvalue_pre))) (tail)) )
|--
  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 0) ”
.

Definition cm_emit_const_expr_partial_solve_wit_2_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (n: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (retval: Z) (PreH1 : ((cm_type_encode (ty)) = (cm_type_encode (ty)))) (PreH2 : (cm_type_code_wf ty )) (PreH3 : (retval = (cm_const_immediate (ty) (n)))) (PreH4 : (lvalue_pre = 0)) (PreH5 : (expr_pre <> 0)) (PreH6 : (0 <= lvalue_pre)) (PreH7 : (lvalue_pre <= 1)) (PreH8 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH9 : (e = (CMConstE (n) (ty)))) (PreH10 : (cm_type_code_wf ty )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> n)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafConst (n) (ty))) (lvalue_pre))) (tail)) )
|--
  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 0) ” 
  &&  “ (cm_type_code_wf ty ) ” 
  &&  “ (retval = (cm_const_immediate (ty) (n))) ” 
  &&  “ (lvalue_pre = 0) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (e = (CMConstE (n) (ty))) ” 
  &&  “ (cm_type_code_wf ty ) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafConst (n) (ty))) (lvalue_pre))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> n)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
.

Definition cm_emit_const_expr_partial_solve_wit_2 := cm_emit_const_expr_partial_solve_wit_2_pure -> cm_emit_const_expr_partial_solve_wit_2_aux.

Definition cm_emit_const_expr_partial_solve_wit_3_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (n: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (lvalue_pre = 0)) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH4 : (cm_type_code_wf ty )) (PreH5 : (retval = (cm_const_immediate (ty) (n)))) (PreH6 : (lvalue_pre = 0)) (PreH7 : (expr_pre <> 0)) (PreH8 : (0 <= lvalue_pre)) (PreH9 : (lvalue_pre <= 1)) (PreH10 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH11 : (e = (CMConstE (n) (ty)))) (PreH12 : (cm_type_code_wf ty )) ,
  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) ((cm_const_immediate (ty) (n))))) (tail)) )
  **  ((( &( "immediate" ) )) # Int64  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> n)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ”
.

Definition cm_emit_const_expr_partial_solve_wit_3_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (n: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (lvalue_pre = 0)) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH4 : (cm_type_code_wf ty )) (PreH5 : (retval = (cm_const_immediate (ty) (n)))) (PreH6 : (lvalue_pre = 0)) (PreH7 : (expr_pre <> 0)) (PreH8 : (0 <= lvalue_pre)) (PreH9 : (lvalue_pre <= 1)) (PreH10 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH11 : (e = (CMConstE (n) (ty)))) (PreH12 : (cm_type_code_wf ty )) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) ((cm_const_immediate (ty) (n))))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> n)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ” 
  &&  “ (lvalue_pre = 0) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) = 0) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ” 
  &&  “ (cm_type_code_wf ty ) ” 
  &&  “ (retval = (cm_const_immediate (ty) (n))) ” 
  &&  “ (lvalue_pre = 0) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (e = (CMConstE (n) (ty))) ” 
  &&  “ (cm_type_code_wf ty ) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) (retval))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> n)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
.

Definition cm_emit_const_expr_partial_solve_wit_3 := cm_emit_const_expr_partial_solve_wit_3_pure -> cm_emit_const_expr_partial_solve_wit_3_aux.

Definition cm_emit_const_expr_which_implies_wit_1 := 
(
forall (n: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (ty: cm_type) (p: cm_program) (policy: cm_lookup_policy) (lvalue: Z) (emitter: Z) (PreH1 : (0 <= lvalue)) (PreH2 : (lvalue <= 0)) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_leaf_code_for (p) ((CMLeafConst (n) (ty))) (lvalue))) (tail)) )
|--
  “ (lvalue = 0) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) = 0) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (cons ((TVMInst (TVMPushOp) ((cm_const_immediate (ty) (n))))) (tail)) )
) \/
(
forall (n: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (ty: cm_type) (p: cm_program) (policy: cm_lookup_policy) (lvalue: Z) (emitter: Z) (PreH1 : (0 <= lvalue)) (PreH2 : (lvalue <= 0)) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_leaf_code_for (p) ((CMLeafConst (n) (ty))) (lvalue))) (tail)) )
|--
  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) = 0) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (cons ((TVMInst (TVMPushOp) ((cm_const_immediate (ty) (n))))) (tail)) )
).

Definition cm_emit_const_expr_which_implies_wit_1_split_goal_1 := 
forall (n: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (ty: cm_type) (p: cm_program) (policy: cm_lookup_policy) (lvalue: Z) (emitter: Z) (PreH1 : (0 <= lvalue)) (PreH2 : (lvalue <= 0)) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_leaf_code_for (p) ((CMLeafConst (n) (ty))) (lvalue))) (tail)) )
|--
  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ”
.

Definition cm_emit_const_expr_which_implies_wit_1_split_goal_2 := 
forall (n: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (ty: cm_type) (p: cm_program) (policy: cm_lookup_policy) (lvalue: Z) (emitter: Z) (PreH1 : (0 <= lvalue)) (PreH2 : (lvalue <= 0)) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_leaf_code_for (p) ((CMLeafConst (n) (ty))) (lvalue))) (tail)) )
|--
  “ ((tvm_opcode_code (TVMPushOp)) = 0) ”
.

Definition cm_emit_const_expr_which_implies_wit_1_split_goal_spatial := 
forall (n: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (ty: cm_type) (p: cm_program) (policy: cm_lookup_policy) (lvalue: Z) (emitter: Z) (PreH1 : (0 <= lvalue)) (PreH2 : (lvalue <= 0)) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_leaf_code_for (p) ((CMLeafConst (n) (ty))) (lvalue))) (tail)) )
|--
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (cons ((TVMInst (TVMPushOp) ((cm_const_immediate (ty) (n))))) (tail)) )
.

(*----- Function cm_emit_string_expr -----*)

Definition cm_emit_string_expr_safety_wit_1 := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (sid: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (tp: Z) (gp: Z) (sp: Z) (retval: Z) (PreH1 : (cm_typed_program policy p )) (PreH2 : (lvalue_pre = 0)) (PreH3 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH4 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH5 : (0 <= sid)) (PreH6 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH7 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH8 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH9 : (retval = (cm_rep_string_address ((cm_program_globals (p))) ((cm_program_strings (p))) (sid)))) (PreH10 : (16 <= retval)) (PreH11 : (retval <= 1048576)) (PreH12 : (program_pre <> 0)) (PreH13 : (lvalue_pre = 0)) (PreH14 : (expr_pre <> 0)) (PreH15 : (0 <= lvalue_pre)) (PreH16 : (lvalue_pre <= 1)) (PreH17 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH18 : (e = (CMStringE (sid) (ty)))) (PreH19 : (0 <= sid)) (PreH20 : (sid <= INT_MAX)) (PreH21 : (cm_typed_program policy p )) (PreH22 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH23 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH24 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) ((cm_rep_string_address ((cm_program_globals (p))) ((cm_program_strings (p))) (sid))))) (tail)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((( &( "address" ) )) # Int64  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  ((( &( "string_id" ) )) # Int  |-> sid)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> sid)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_emit_string_expr_entail_wit_1 := 
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (sid: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= lvalue_pre)) (PreH2 : (lvalue_pre <= 1)) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (e = (CMStringE (sid) (ty)))) (PreH5 : (0 <= sid)) (PreH6 : (sid <= INT_MAX)) (PreH7 : (cm_typed_program policy p )) (PreH8 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH9 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH10 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafString (sid) (ty))) (lvalue_pre))) (tail)) )
|--
  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (e = (CMStringE (sid) (ty))) ” 
  &&  “ (0 <= sid) ” 
  &&  “ (sid <= INT_MAX) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> sid)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafString (sid) (ty))) (lvalue_pre))) (tail)) )
) \/
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (sid: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= lvalue_pre)) (PreH2 : (lvalue_pre <= 1)) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (e = (CMStringE (sid) (ty)))) (PreH5 : (0 <= sid)) (PreH6 : (sid <= INT_MAX)) (PreH7 : (cm_typed_program policy p )) (PreH8 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH9 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH10 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafString (sid) (ty))) (lvalue_pre))) (tail)) )
|--
  “ (expr_pre <> 0) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> sid)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafString (sid) (ty))) (lvalue_pre))) (tail)) )
).

Definition cm_emit_string_expr_entail_wit_1_split_goal_1 := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (sid: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= lvalue_pre)) (PreH2 : (lvalue_pre <= 1)) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (e = (CMStringE (sid) (ty)))) (PreH5 : (0 <= sid)) (PreH6 : (sid <= INT_MAX)) (PreH7 : (cm_typed_program policy p )) (PreH8 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH9 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH10 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafString (sid) (ty))) (lvalue_pre))) (tail)) )
|--
  “ (expr_pre <> 0) ”
.

Definition cm_emit_string_expr_entail_wit_1_split_goal_spatial := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (sid: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= lvalue_pre)) (PreH2 : (lvalue_pre <= 1)) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (e = (CMStringE (sid) (ty)))) (PreH5 : (0 <= sid)) (PreH6 : (sid <= INT_MAX)) (PreH7 : (cm_typed_program policy p )) (PreH8 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH9 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH10 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafString (sid) (ty))) (lvalue_pre))) (tail)) )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> sid)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafString (sid) (ty))) (lvalue_pre))) (tail)) )
.

Definition cm_emit_string_expr_return_wit_1 := 
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (sid: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (tp: Z) (gp: Z) (sp: Z) (retval: Z) (PreH1 : (cm_typed_program policy p )) (PreH2 : (lvalue_pre = 0)) (PreH3 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH4 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH5 : (0 <= sid)) (PreH6 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH7 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH8 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH9 : (retval = (cm_rep_string_address ((cm_program_globals (p))) ((cm_program_strings (p))) (sid)))) (PreH10 : (16 <= retval)) (PreH11 : (retval <= 1048576)) (PreH12 : (program_pre <> 0)) (PreH13 : (lvalue_pre = 0)) (PreH14 : (expr_pre <> 0)) (PreH15 : (0 <= lvalue_pre)) (PreH16 : (lvalue_pre <= 1)) (PreH17 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH18 : (e = (CMStringE (sid) (ty)))) (PreH19 : (0 <= sid)) (PreH20 : (sid <= INT_MAX)) (PreH21 : (cm_typed_program policy p )) (PreH22 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH23 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH24 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMPushOp) (retval))) ((@nil tvm_inst))))) tail )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> sid)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
|--
  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (e = (CMStringE (sid) (ty))) ” 
  &&  “ (0 <= sid) ” 
  &&  “ (sid <= INT_MAX) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_leaf_code_for (p) ((CMLeafString (sid) (ty))) (lvalue_pre)))) tail )
) \/
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (sid: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (tp: Z) (gp: Z) (sp: Z) (retval: Z) (PreH1 : (sid <= INT64_MAX)) (PreH2 : (sid >= INT64_MIN)) (PreH3 : ((cm_type_encode (ty)) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_program_main (p)) <= INT_MAX)) (PreH7 : ((cm_type_encode (ty)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH10 : ((cm_program_main (p)) >= INT_MIN)) (PreH11 : (cm_typed_program policy p )) (PreH12 : (lvalue_pre = 0)) (PreH13 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH14 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH15 : (0 <= sid)) (PreH16 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH17 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH18 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH19 : (retval = (cm_rep_string_address ((cm_program_globals (p))) ((cm_program_strings (p))) (sid)))) (PreH20 : (16 <= retval)) (PreH21 : (retval <= 1048576)) (PreH22 : (program_pre <> 0)) (PreH23 : (lvalue_pre = 0)) (PreH24 : (expr_pre <> 0)) (PreH25 : (0 <= lvalue_pre)) (PreH26 : (lvalue_pre <= 1)) (PreH27 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH28 : (e = (CMStringE (sid) (ty)))) (PreH29 : (0 <= sid)) (PreH30 : (sid <= INT_MAX)) (PreH31 : (cm_typed_program policy p )) (PreH32 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH33 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH34 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMPushOp) (retval))) ((@nil tvm_inst))))) tail )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> sid)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_leaf_code_for (p) ((CMLeafString (sid) (ty))) (lvalue_pre)))) tail )
).

Definition cm_emit_string_expr_return_wit_1_split_goal_spatial := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (sid: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (tp: Z) (gp: Z) (sp: Z) (retval: Z) (PreH1 : (sid <= INT64_MAX)) (PreH2 : (sid >= INT64_MIN)) (PreH3 : ((cm_type_encode (ty)) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_program_main (p)) <= INT_MAX)) (PreH7 : ((cm_type_encode (ty)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH10 : ((cm_program_main (p)) >= INT_MIN)) (PreH11 : (cm_typed_program policy p )) (PreH12 : (lvalue_pre = 0)) (PreH13 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH14 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH15 : (0 <= sid)) (PreH16 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH17 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH18 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH19 : (retval = (cm_rep_string_address ((cm_program_globals (p))) ((cm_program_strings (p))) (sid)))) (PreH20 : (16 <= retval)) (PreH21 : (retval <= 1048576)) (PreH22 : (program_pre <> 0)) (PreH23 : (lvalue_pre = 0)) (PreH24 : (expr_pre <> 0)) (PreH25 : (0 <= lvalue_pre)) (PreH26 : (lvalue_pre <= 1)) (PreH27 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH28 : (e = (CMStringE (sid) (ty)))) (PreH29 : (0 <= sid)) (PreH30 : (sid <= INT_MAX)) (PreH31 : (cm_typed_program policy p )) (PreH32 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH33 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH34 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMPushOp) (retval))) ((@nil tvm_inst))))) tail )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> sid)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_leaf_code_for (p) ((CMLeafString (sid) (ty))) (lvalue_pre)))) tail )
.

Definition cm_emit_string_expr_return_wit_2 := 
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (sid: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (lvalue_pre <> 0)) (PreH2 : (expr_pre <> 0)) (PreH3 : (0 <= lvalue_pre)) (PreH4 : (lvalue_pre <= 1)) (PreH5 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH6 : (e = (CMStringE (sid) (ty)))) (PreH7 : (0 <= sid)) (PreH8 : (sid <= INT_MAX)) (PreH9 : (cm_typed_program policy p )) (PreH10 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH11 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH12 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> sid)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafString (sid) (ty))) (lvalue_pre))) (tail)) )
|--
  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (e = (CMStringE (sid) (ty))) ” 
  &&  “ (0 <= sid) ” 
  &&  “ (sid <= INT_MAX) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_leaf_code_for (p) ((CMLeafString (sid) (ty))) (lvalue_pre)))) tail )
) \/
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (sid: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (sid <= INT64_MAX)) (PreH2 : (sid >= INT64_MIN)) (PreH3 : ((cm_type_encode (ty)) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode (ty)) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (lvalue_pre <> 0)) (PreH10 : (expr_pre <> 0)) (PreH11 : (0 <= lvalue_pre)) (PreH12 : (lvalue_pre <= 1)) (PreH13 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH14 : (e = (CMStringE (sid) (ty)))) (PreH15 : (0 <= sid)) (PreH16 : (sid <= INT_MAX)) (PreH17 : (cm_typed_program policy p )) (PreH18 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH19 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH20 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> sid)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafString (sid) (ty))) (lvalue_pre))) (tail)) )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_leaf_code_for (p) ((CMLeafString (sid) (ty))) (lvalue_pre)))) tail )
).

Definition cm_emit_string_expr_return_wit_2_split_goal_spatial := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (sid: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (sid <= INT64_MAX)) (PreH2 : (sid >= INT64_MIN)) (PreH3 : ((cm_type_encode (ty)) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode (ty)) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (lvalue_pre <> 0)) (PreH10 : (expr_pre <> 0)) (PreH11 : (0 <= lvalue_pre)) (PreH12 : (lvalue_pre <= 1)) (PreH13 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH14 : (e = (CMStringE (sid) (ty)))) (PreH15 : (0 <= sid)) (PreH16 : (sid <= INT_MAX)) (PreH17 : (cm_typed_program policy p )) (PreH18 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH19 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH20 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> sid)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafString (sid) (ty))) (lvalue_pre))) (tail)) )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_leaf_code_for (p) ((CMLeafString (sid) (ty))) (lvalue_pre)))) tail )
.

Definition cm_emit_string_expr_partial_solve_wit_1 := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (sid: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (lvalue_pre = 0)) (PreH2 : (expr_pre <> 0)) (PreH3 : (0 <= lvalue_pre)) (PreH4 : (lvalue_pre <= 1)) (PreH5 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH6 : (e = (CMStringE (sid) (ty)))) (PreH7 : (0 <= sid)) (PreH8 : (sid <= INT_MAX)) (PreH9 : (cm_typed_program policy p )) (PreH10 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH11 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH12 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> sid)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafString (sid) (ty))) (lvalue_pre))) (tail)) )
|--
  “ (lvalue_pre = 0) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (e = (CMStringE (sid) (ty))) ” 
  &&  “ (0 <= sid) ” 
  &&  “ (sid <= INT_MAX) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> sid)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafString (sid) (ty))) (lvalue_pre))) (tail)) )
.

Definition cm_emit_string_expr_partial_solve_wit_2_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (sid: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (tp: Z) (gp: Z) (sp: Z) (PreH1 : (program_pre <> 0)) (PreH2 : (lvalue_pre = 0)) (PreH3 : (expr_pre <> 0)) (PreH4 : (0 <= lvalue_pre)) (PreH5 : (lvalue_pre <= 1)) (PreH6 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH7 : (e = (CMStringE (sid) (ty)))) (PreH8 : (0 <= sid)) (PreH9 : (sid <= INT_MAX)) (PreH10 : (cm_typed_program policy p )) (PreH11 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH12 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH13 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  ((( &( "address" ) )) # Int64  |->_)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((( &( "string_id" ) )) # Int  |-> sid)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> sid)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafString (sid) (ty))) (lvalue_pre))) (tail)) )
|--
  “ (0 <= sid) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ”
.

Definition cm_emit_string_expr_partial_solve_wit_2_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (sid: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (tp: Z) (gp: Z) (sp: Z) (PreH1 : (program_pre <> 0)) (PreH2 : (lvalue_pre = 0)) (PreH3 : (expr_pre <> 0)) (PreH4 : (0 <= lvalue_pre)) (PreH5 : (lvalue_pre <= 1)) (PreH6 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH7 : (e = (CMStringE (sid) (ty)))) (PreH8 : (0 <= sid)) (PreH9 : (sid <= INT_MAX)) (PreH10 : (cm_typed_program policy p )) (PreH11 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH12 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH13 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> sid)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafString (sid) (ty))) (lvalue_pre))) (tail)) )
|--
  “ (0 <= sid) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (program_pre <> 0) ” 
  &&  “ (lvalue_pre = 0) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (e = (CMStringE (sid) (ty))) ” 
  &&  “ (0 <= sid) ” 
  &&  “ (sid <= INT_MAX) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ”
  &&  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> sid)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafString (sid) (ty))) (lvalue_pre))) (tail)) )
.

Definition cm_emit_string_expr_partial_solve_wit_2 := cm_emit_string_expr_partial_solve_wit_2_pure -> cm_emit_string_expr_partial_solve_wit_2_aux.

Definition cm_emit_string_expr_partial_solve_wit_3_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (sid: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (tp: Z) (gp: Z) (sp: Z) (retval: Z) (PreH1 : (0 <= sid)) (PreH2 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH3 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH4 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH5 : (retval = (cm_rep_string_address ((cm_program_globals (p))) ((cm_program_strings (p))) (sid)))) (PreH6 : (16 <= retval)) (PreH7 : (retval <= 1048576)) (PreH8 : (program_pre <> 0)) (PreH9 : (lvalue_pre = 0)) (PreH10 : (expr_pre <> 0)) (PreH11 : (0 <= lvalue_pre)) (PreH12 : (lvalue_pre <= 1)) (PreH13 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH14 : (e = (CMStringE (sid) (ty)))) (PreH15 : (0 <= sid)) (PreH16 : (sid <= INT_MAX)) (PreH17 : (cm_typed_program policy p )) (PreH18 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH19 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH20 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((( &( "address" ) )) # Int64  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  ((( &( "string_id" ) )) # Int  |-> sid)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> sid)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafString (sid) (ty))) (lvalue_pre))) (tail)) )
|--
  “ (cm_typed_program policy p ) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 0) ”
.

Definition cm_emit_string_expr_partial_solve_wit_3_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (sid: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (tp: Z) (gp: Z) (sp: Z) (retval: Z) (PreH1 : (0 <= sid)) (PreH2 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH3 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH4 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH5 : (retval = (cm_rep_string_address ((cm_program_globals (p))) ((cm_program_strings (p))) (sid)))) (PreH6 : (16 <= retval)) (PreH7 : (retval <= 1048576)) (PreH8 : (program_pre <> 0)) (PreH9 : (lvalue_pre = 0)) (PreH10 : (expr_pre <> 0)) (PreH11 : (0 <= lvalue_pre)) (PreH12 : (lvalue_pre <= 1)) (PreH13 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH14 : (e = (CMStringE (sid) (ty)))) (PreH15 : (0 <= sid)) (PreH16 : (sid <= INT_MAX)) (PreH17 : (cm_typed_program policy p )) (PreH18 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH19 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH20 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> sid)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafString (sid) (ty))) (lvalue_pre))) (tail)) )
|--
  “ (cm_typed_program policy p ) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 0) ” 
  &&  “ (0 <= sid) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (retval = (cm_rep_string_address ((cm_program_globals (p))) ((cm_program_strings (p))) (sid))) ” 
  &&  “ (16 <= retval) ” 
  &&  “ (retval <= 1048576) ” 
  &&  “ (program_pre <> 0) ” 
  &&  “ (lvalue_pre = 0) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (e = (CMStringE (sid) (ty))) ” 
  &&  “ (0 <= sid) ” 
  &&  “ (sid <= INT_MAX) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafString (sid) (ty))) (lvalue_pre))) (tail)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> sid)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
.

Definition cm_emit_string_expr_partial_solve_wit_3 := cm_emit_string_expr_partial_solve_wit_3_pure -> cm_emit_string_expr_partial_solve_wit_3_aux.

Definition cm_emit_string_expr_partial_solve_wit_4_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (sid: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (tp: Z) (gp: Z) (sp: Z) (retval: Z) (PreH1 : (cm_typed_program policy p )) (PreH2 : (lvalue_pre = 0)) (PreH3 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH4 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH5 : (0 <= sid)) (PreH6 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH7 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH8 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH9 : (retval = (cm_rep_string_address ((cm_program_globals (p))) ((cm_program_strings (p))) (sid)))) (PreH10 : (16 <= retval)) (PreH11 : (retval <= 1048576)) (PreH12 : (program_pre <> 0)) (PreH13 : (lvalue_pre = 0)) (PreH14 : (expr_pre <> 0)) (PreH15 : (0 <= lvalue_pre)) (PreH16 : (lvalue_pre <= 1)) (PreH17 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH18 : (e = (CMStringE (sid) (ty)))) (PreH19 : (0 <= sid)) (PreH20 : (sid <= INT_MAX)) (PreH21 : (cm_typed_program policy p )) (PreH22 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH23 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH24 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) ((cm_rep_string_address ((cm_program_globals (p))) ((cm_program_strings (p))) (sid))))) (tail)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((( &( "address" ) )) # Int64  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  ((( &( "string_id" ) )) # Int  |-> sid)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> sid)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ”
.

Definition cm_emit_string_expr_partial_solve_wit_4_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (sid: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (tp: Z) (gp: Z) (sp: Z) (retval: Z) (PreH1 : (cm_typed_program policy p )) (PreH2 : (lvalue_pre = 0)) (PreH3 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH4 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH5 : (0 <= sid)) (PreH6 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH7 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH8 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH9 : (retval = (cm_rep_string_address ((cm_program_globals (p))) ((cm_program_strings (p))) (sid)))) (PreH10 : (16 <= retval)) (PreH11 : (retval <= 1048576)) (PreH12 : (program_pre <> 0)) (PreH13 : (lvalue_pre = 0)) (PreH14 : (expr_pre <> 0)) (PreH15 : (0 <= lvalue_pre)) (PreH16 : (lvalue_pre <= 1)) (PreH17 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH18 : (e = (CMStringE (sid) (ty)))) (PreH19 : (0 <= sid)) (PreH20 : (sid <= INT_MAX)) (PreH21 : (cm_typed_program policy p )) (PreH22 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH23 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH24 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) ((cm_rep_string_address ((cm_program_globals (p))) ((cm_program_strings (p))) (sid))))) (tail)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> sid)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (lvalue_pre = 0) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) = 0) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ” 
  &&  “ (0 <= sid) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (retval = (cm_rep_string_address ((cm_program_globals (p))) ((cm_program_strings (p))) (sid))) ” 
  &&  “ (16 <= retval) ” 
  &&  “ (retval <= 1048576) ” 
  &&  “ (program_pre <> 0) ” 
  &&  “ (lvalue_pre = 0) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (e = (CMStringE (sid) (ty))) ” 
  &&  “ (0 <= sid) ” 
  &&  “ (sid <= INT_MAX) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) (retval))) (tail)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> sid)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
.

Definition cm_emit_string_expr_partial_solve_wit_4 := cm_emit_string_expr_partial_solve_wit_4_pure -> cm_emit_string_expr_partial_solve_wit_4_aux.

Definition cm_emit_string_expr_which_implies_wit_1 := 
(
forall (functions_ptr: Z) (p: cm_program) (program: Z) ,
  (cm_program_context_rep program p functions_ptr )
|--
  EX (tp: Z)  (gp: Z)  (sp: Z) ,
  “ (program <> 0) ”
  &&  ((&((program)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
) \/
(
forall (functions_ptr: Z) (p: cm_program) (program: Z) ,
  (cm_program_context_rep program p functions_ptr )
|--
  EX (tp: Z)  (gp: Z)  (sp: Z) ,
  “ (program <> 0) ”
  &&  ((&((program)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
).

Definition cm_emit_string_expr_which_implies_wit_2 := 
(
forall (sid: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (ty: cm_type) (p: cm_program) (policy: cm_lookup_policy) (lvalue: Z) (emitter: Z) (PreH1 : (cm_typed_program policy p )) (PreH2 : (0 <= lvalue)) (PreH3 : (lvalue <= 0)) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_leaf_code_for (p) ((CMLeafString (sid) (ty))) (lvalue))) (tail)) )
|--
  “ (cm_typed_program policy p ) ” 
  &&  “ (lvalue = 0) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) = 0) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (cons ((TVMInst (TVMPushOp) ((cm_rep_string_address ((cm_program_globals (p))) ((cm_program_strings (p))) (sid))))) (tail)) )
) \/
(
forall (sid: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (ty: cm_type) (p: cm_program) (policy: cm_lookup_policy) (lvalue: Z) (emitter: Z) (PreH1 : (cm_typed_program policy p )) (PreH2 : (0 <= lvalue)) (PreH3 : (lvalue <= 0)) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_leaf_code_for (p) ((CMLeafString (sid) (ty))) (lvalue))) (tail)) )
|--
  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) = 0) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (cons ((TVMInst (TVMPushOp) ((cm_rep_string_address ((cm_program_globals (p))) ((cm_program_strings (p))) (sid))))) (tail)) )
).

Definition cm_emit_string_expr_which_implies_wit_2_split_goal_1 := 
forall (sid: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (ty: cm_type) (p: cm_program) (policy: cm_lookup_policy) (lvalue: Z) (emitter: Z) (PreH1 : (cm_typed_program policy p )) (PreH2 : (0 <= lvalue)) (PreH3 : (lvalue <= 0)) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_leaf_code_for (p) ((CMLeafString (sid) (ty))) (lvalue))) (tail)) )
|--
  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ”
.

Definition cm_emit_string_expr_which_implies_wit_2_split_goal_2 := 
forall (sid: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (ty: cm_type) (p: cm_program) (policy: cm_lookup_policy) (lvalue: Z) (emitter: Z) (PreH1 : (cm_typed_program policy p )) (PreH2 : (0 <= lvalue)) (PreH3 : (lvalue <= 0)) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_leaf_code_for (p) ((CMLeafString (sid) (ty))) (lvalue))) (tail)) )
|--
  “ ((tvm_opcode_code (TVMPushOp)) = 0) ”
.

Definition cm_emit_string_expr_which_implies_wit_2_split_goal_spatial := 
forall (sid: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (ty: cm_type) (p: cm_program) (policy: cm_lookup_policy) (lvalue: Z) (emitter: Z) (PreH1 : (cm_typed_program policy p )) (PreH2 : (0 <= lvalue)) (PreH3 : (lvalue <= 0)) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_leaf_code_for (p) ((CMLeafString (sid) (ty))) (lvalue))) (tail)) )
|--
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (cons ((TVMInst (TVMPushOp) ((cm_rep_string_address ((cm_program_globals (p))) ((cm_program_strings (p))) (sid))))) (tail)) )
.

(*----- Function cm_emit_getc_expr -----*)

Definition cm_emit_getc_expr_safety_wit_1 := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (lvalue_pre = 0)) (PreH2 : ((tvm_opcode_code (TVMGetcOp)) = 24)) (PreH3 : ((tvm_opcode_code (TVMGetcOp)) <> 22)) (PreH4 : (lvalue_pre = 0)) (PreH5 : (0 <= lvalue_pre)) (PreH6 : (lvalue_pre <= 1)) (PreH7 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH8 : (e = (CMGetcE (ty)))) ,
  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (TVMGetcOp) (0))) (tail)) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
|--
  “ (24 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 24) ”
.

Definition cm_emit_getc_expr_safety_wit_2 := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (lvalue_pre = 0)) (PreH2 : ((tvm_opcode_code (TVMGetcOp)) = 24)) (PreH3 : ((tvm_opcode_code (TVMGetcOp)) <> 22)) (PreH4 : (lvalue_pre = 0)) (PreH5 : (0 <= lvalue_pre)) (PreH6 : (lvalue_pre <= 1)) (PreH7 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH8 : (e = (CMGetcE (ty)))) ,
  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (TVMGetcOp) (0))) (tail)) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_emit_getc_expr_return_wit_1 := 
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (lvalue_pre = 0)) (PreH2 : ((tvm_opcode_code (TVMGetcOp)) = 24)) (PreH3 : ((tvm_opcode_code (TVMGetcOp)) <> 22)) (PreH4 : (lvalue_pre = 0)) (PreH5 : (0 <= lvalue_pre)) (PreH6 : (lvalue_pre <= 1)) (PreH7 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH8 : (e = (CMGetcE (ty)))) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMGetcOp) (0))) ((@nil tvm_inst))))) tail )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
|--
  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (e = (CMGetcE (ty))) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_leaf_code_for (p) ((CMLeafGetc (ty))) (lvalue_pre)))) tail )
) \/
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (lvalue_pre = 0)) (PreH2 : ((tvm_opcode_code (TVMGetcOp)) = 24)) (PreH3 : ((tvm_opcode_code (TVMGetcOp)) <> 22)) (PreH4 : (lvalue_pre = 0)) (PreH5 : (0 <= lvalue_pre)) (PreH6 : (lvalue_pre <= 1)) (PreH7 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH8 : (e = (CMGetcE (ty)))) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMGetcOp) (0))) ((@nil tvm_inst))))) tail )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_leaf_code_for (p) ((CMLeafGetc (ty))) (lvalue_pre)))) tail )
).

Definition cm_emit_getc_expr_return_wit_1_split_goal_spatial := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (lvalue_pre = 0)) (PreH2 : ((tvm_opcode_code (TVMGetcOp)) = 24)) (PreH3 : ((tvm_opcode_code (TVMGetcOp)) <> 22)) (PreH4 : (lvalue_pre = 0)) (PreH5 : (0 <= lvalue_pre)) (PreH6 : (lvalue_pre <= 1)) (PreH7 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH8 : (e = (CMGetcE (ty)))) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMGetcOp) (0))) ((@nil tvm_inst))))) tail )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_leaf_code_for (p) ((CMLeafGetc (ty))) (lvalue_pre)))) tail )
.

Definition cm_emit_getc_expr_return_wit_2 := 
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (lvalue_pre <> 0)) (PreH2 : (0 <= lvalue_pre)) (PreH3 : (lvalue_pre <= 1)) (PreH4 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH5 : (e = (CMGetcE (ty)))) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafGetc (ty))) (lvalue_pre))) (tail)) )
|--
  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (e = (CMGetcE (ty))) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_leaf_code_for (p) ((CMLeafGetc (ty))) (lvalue_pre)))) tail )
) \/
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (lvalue_pre <> 0)) (PreH2 : (0 <= lvalue_pre)) (PreH3 : (lvalue_pre <= 1)) (PreH4 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH5 : (e = (CMGetcE (ty)))) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafGetc (ty))) (lvalue_pre))) (tail)) )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_leaf_code_for (p) ((CMLeafGetc (ty))) (lvalue_pre)))) tail )
).

Definition cm_emit_getc_expr_return_wit_2_split_goal_spatial := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (lvalue_pre <> 0)) (PreH2 : (0 <= lvalue_pre)) (PreH3 : (lvalue_pre <= 1)) (PreH4 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH5 : (e = (CMGetcE (ty)))) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafGetc (ty))) (lvalue_pre))) (tail)) )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_leaf_code_for (p) ((CMLeafGetc (ty))) (lvalue_pre)))) tail )
.

Definition cm_emit_getc_expr_partial_solve_wit_1_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (lvalue_pre = 0)) (PreH2 : (0 <= lvalue_pre)) (PreH3 : (lvalue_pre <= 1)) (PreH4 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH5 : (e = (CMGetcE (ty)))) ,
  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafGetc (ty))) (lvalue_pre))) (tail)) )
|--
  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 0) ”
.

Definition cm_emit_getc_expr_partial_solve_wit_1_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (lvalue_pre = 0)) (PreH2 : (0 <= lvalue_pre)) (PreH3 : (lvalue_pre <= 1)) (PreH4 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH5 : (e = (CMGetcE (ty)))) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafGetc (ty))) (lvalue_pre))) (tail)) )
|--
  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 0) ” 
  &&  “ (lvalue_pre = 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (e = (CMGetcE (ty))) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafGetc (ty))) (lvalue_pre))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
.

Definition cm_emit_getc_expr_partial_solve_wit_1 := cm_emit_getc_expr_partial_solve_wit_1_pure -> cm_emit_getc_expr_partial_solve_wit_1_aux.

Definition cm_emit_getc_expr_partial_solve_wit_2_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (lvalue_pre = 0)) (PreH2 : ((tvm_opcode_code (TVMGetcOp)) = 24)) (PreH3 : ((tvm_opcode_code (TVMGetcOp)) <> 22)) (PreH4 : (lvalue_pre = 0)) (PreH5 : (0 <= lvalue_pre)) (PreH6 : (lvalue_pre <= 1)) (PreH7 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH8 : (e = (CMGetcE (ty)))) ,
  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (TVMGetcOp) (0))) (tail)) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
|--
  “ (24 = (tvm_opcode_code (TVMGetcOp))) ” 
  &&  “ ((tvm_opcode_code (TVMGetcOp)) <> 22) ”
.

Definition cm_emit_getc_expr_partial_solve_wit_2_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (lvalue_pre = 0)) (PreH2 : ((tvm_opcode_code (TVMGetcOp)) = 24)) (PreH3 : ((tvm_opcode_code (TVMGetcOp)) <> 22)) (PreH4 : (lvalue_pre = 0)) (PreH5 : (0 <= lvalue_pre)) (PreH6 : (lvalue_pre <= 1)) (PreH7 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH8 : (e = (CMGetcE (ty)))) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (TVMGetcOp) (0))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
|--
  “ (24 = (tvm_opcode_code (TVMGetcOp))) ” 
  &&  “ ((tvm_opcode_code (TVMGetcOp)) <> 22) ” 
  &&  “ (lvalue_pre = 0) ” 
  &&  “ ((tvm_opcode_code (TVMGetcOp)) = 24) ” 
  &&  “ ((tvm_opcode_code (TVMGetcOp)) <> 22) ” 
  &&  “ (lvalue_pre = 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (e = (CMGetcE (ty))) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (TVMGetcOp) (0))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
.

Definition cm_emit_getc_expr_partial_solve_wit_2 := cm_emit_getc_expr_partial_solve_wit_2_pure -> cm_emit_getc_expr_partial_solve_wit_2_aux.

Definition cm_emit_getc_expr_which_implies_wit_1 := 
(
forall (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (ty: cm_type) (p: cm_program) (policy: cm_lookup_policy) (lvalue: Z) (emitter: Z) (PreH1 : (0 <= lvalue)) (PreH2 : (lvalue <= 0)) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_leaf_code_for (p) ((CMLeafGetc (ty))) (lvalue))) (tail)) )
|--
  “ (lvalue = 0) ” 
  &&  “ ((tvm_opcode_code (TVMGetcOp)) = 24) ” 
  &&  “ ((tvm_opcode_code (TVMGetcOp)) <> 22) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (cons ((TVMInst (TVMGetcOp) (0))) (tail)) )
) \/
(
forall (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (ty: cm_type) (p: cm_program) (policy: cm_lookup_policy) (lvalue: Z) (emitter: Z) (PreH1 : (0 <= lvalue)) (PreH2 : (lvalue <= 0)) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_leaf_code_for (p) ((CMLeafGetc (ty))) (lvalue))) (tail)) )
|--
  “ ((tvm_opcode_code (TVMGetcOp)) <> 22) ” 
  &&  “ ((tvm_opcode_code (TVMGetcOp)) = 24) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (cons ((TVMInst (TVMGetcOp) (0))) (tail)) )
).

Definition cm_emit_getc_expr_which_implies_wit_1_split_goal_1 := 
forall (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (ty: cm_type) (p: cm_program) (policy: cm_lookup_policy) (lvalue: Z) (emitter: Z) (PreH1 : (0 <= lvalue)) (PreH2 : (lvalue <= 0)) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_leaf_code_for (p) ((CMLeafGetc (ty))) (lvalue))) (tail)) )
|--
  “ ((tvm_opcode_code (TVMGetcOp)) <> 22) ”
.

Definition cm_emit_getc_expr_which_implies_wit_1_split_goal_2 := 
forall (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (ty: cm_type) (p: cm_program) (policy: cm_lookup_policy) (lvalue: Z) (emitter: Z) (PreH1 : (0 <= lvalue)) (PreH2 : (lvalue <= 0)) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_leaf_code_for (p) ((CMLeafGetc (ty))) (lvalue))) (tail)) )
|--
  “ ((tvm_opcode_code (TVMGetcOp)) = 24) ”
.

Definition cm_emit_getc_expr_which_implies_wit_1_split_goal_spatial := 
forall (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (ty: cm_type) (p: cm_program) (policy: cm_lookup_policy) (lvalue: Z) (emitter: Z) (PreH1 : (0 <= lvalue)) (PreH2 : (lvalue <= 0)) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_leaf_code_for (p) ((CMLeafGetc (ty))) (lvalue))) (tail)) )
|--
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (cons ((TVMInst (TVMGetcOp) (0))) (tail)) )
.

(*----- Function cm_sizeof_value -----*)

Definition cm_sizeof_value_safety_wit_1 := 
forall (code_pre: Z) (program_pre: Z) (functions_ptr: Z) (asked: cm_type) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (code_pre = (cm_type_encode (asked)))) (PreH2 : (cm_typed_program policy p )) (PreH3 : (cm_type_code_wf asked )) (PreH4 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH5 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  ((( &( "result" ) )) # Int64  |->_)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "code" ) )) # Int64  |-> code_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (1024 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1024) ”
.

Definition cm_sizeof_value_safety_wit_2 := 
forall (code_pre: Z) (program_pre: Z) (functions_ptr: Z) (asked: cm_type) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (code_pre >= 1024)) (PreH2 : (code_pre = (cm_type_encode (asked)))) (PreH3 : (cm_typed_program policy p )) (PreH4 : (cm_type_code_wf asked )) (PreH5 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH6 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  ((( &( "result" ) )) # Int64  |->_)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "code" ) )) # Int64  |-> code_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition cm_sizeof_value_return_wit_1 := 
(
forall (code_pre: Z) (program_pre: Z) (functions_ptr: Z) (asked: cm_type) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (code_pre >= 1024)) (PreH2 : (code_pre = (cm_type_encode (asked)))) (PreH3 : (cm_typed_program policy p )) (PreH4 : (cm_type_code_wf asked )) (PreH5 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH6 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (code_pre = (cm_type_encode (asked))) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_type_code_wf asked ) ” 
  &&  “ (cm_type_refs (cm_program_structs (p)) asked ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (8 = (cm_type_size ((cm_program_structs (p))) (asked))) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
) \/
(
forall (code_pre: Z) (asked: cm_type) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (code_pre >= 1024)) (PreH2 : (code_pre = (cm_type_encode (asked)))) (PreH3 : (cm_typed_program policy p )) (PreH4 : (cm_type_code_wf asked )) (PreH5 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH6 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  TT && emp 
|--
  “ (8 = (cm_type_size ((cm_program_structs (p))) (asked))) ”
  &&  emp
).

Definition cm_sizeof_value_return_wit_1_split_goal_1 := 
forall (code_pre: Z) (asked: cm_type) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (code_pre >= 1024)) (PreH2 : (code_pre = (cm_type_encode (asked)))) (PreH3 : (cm_typed_program policy p )) (PreH4 : (cm_type_code_wf asked )) (PreH5 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH6 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  (8 = (cm_type_size ((cm_program_structs (p))) (asked)))
.

Definition cm_sizeof_value_return_wit_2 := 
(
forall (code_pre: Z) (program_pre: Z) (functions_ptr: Z) (asked: cm_type) (p: cm_program) (policy: cm_lookup_policy) (tp: Z) (gp: Z) (sp: Z) (retval: Z) (PreH1 : (0 <= (cm_type_encode (asked)))) (PreH2 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH3 : (retval = (cm_rep_type_size ((cm_program_structs (p))) ((cm_type_encode (asked)))))) (PreH4 : (program_pre <> 0)) (PreH5 : (cm_type_code_wf asked )) (PreH6 : (0 <= (cm_type_encode (asked)))) (PreH7 : (code_pre < 1024)) (PreH8 : (code_pre = (cm_type_encode (asked)))) (PreH9 : (cm_typed_program policy p )) (PreH10 : (cm_type_code_wf asked )) (PreH11 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH12 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
|--
  “ (code_pre = (cm_type_encode (asked))) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_type_code_wf asked ) ” 
  &&  “ (cm_type_refs (cm_program_structs (p)) asked ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (retval = (cm_type_size ((cm_program_structs (p))) (asked))) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
) \/
(
forall (code_pre: Z) (program_pre: Z) (functions_ptr: Z) (asked: cm_type) (p: cm_program) (policy: cm_lookup_policy) (tp: Z) (gp: Z) (sp: Z) (retval: Z) (PreH1 : ((cm_program_main (p)) <= INT_MAX)) (PreH2 : ((cm_program_main (p)) >= INT_MIN)) (PreH3 : (0 <= (cm_type_encode (asked)))) (PreH4 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH5 : (retval = (cm_rep_type_size ((cm_program_structs (p))) ((cm_type_encode (asked)))))) (PreH6 : (program_pre <> 0)) (PreH7 : (cm_type_code_wf asked )) (PreH8 : (0 <= (cm_type_encode (asked)))) (PreH9 : (code_pre < 1024)) (PreH10 : (code_pre = (cm_type_encode (asked)))) (PreH11 : (cm_typed_program policy p )) (PreH12 : (cm_type_code_wf asked )) (PreH13 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH14 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
|--
  “ (retval = (cm_type_size ((cm_program_structs (p))) (asked))) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
).

Definition cm_sizeof_value_return_wit_2_split_goal_1 := 
forall (code_pre: Z) (program_pre: Z) (functions_ptr: Z) (asked: cm_type) (p: cm_program) (policy: cm_lookup_policy) (tp: Z) (gp: Z) (sp: Z) (retval: Z) (PreH1 : ((cm_program_main (p)) <= INT_MAX)) (PreH2 : ((cm_program_main (p)) >= INT_MIN)) (PreH3 : (0 <= (cm_type_encode (asked)))) (PreH4 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH5 : (retval = (cm_rep_type_size ((cm_program_structs (p))) ((cm_type_encode (asked)))))) (PreH6 : (program_pre <> 0)) (PreH7 : (cm_type_code_wf asked )) (PreH8 : (0 <= (cm_type_encode (asked)))) (PreH9 : (code_pre < 1024)) (PreH10 : (code_pre = (cm_type_encode (asked)))) (PreH11 : (cm_typed_program policy p )) (PreH12 : (cm_type_code_wf asked )) (PreH13 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH14 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
|--
  “ (retval = (cm_type_size ((cm_program_structs (p))) (asked))) ”
.

Definition cm_sizeof_value_return_wit_2_split_goal_spatial := 
forall (code_pre: Z) (program_pre: Z) (functions_ptr: Z) (asked: cm_type) (p: cm_program) (policy: cm_lookup_policy) (tp: Z) (gp: Z) (sp: Z) (retval: Z) (PreH1 : ((cm_program_main (p)) <= INT_MAX)) (PreH2 : ((cm_program_main (p)) >= INT_MIN)) (PreH3 : (0 <= (cm_type_encode (asked)))) (PreH4 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH5 : (retval = (cm_rep_type_size ((cm_program_structs (p))) ((cm_type_encode (asked)))))) (PreH6 : (program_pre <> 0)) (PreH7 : (cm_type_code_wf asked )) (PreH8 : (0 <= (cm_type_encode (asked)))) (PreH9 : (code_pre < 1024)) (PreH10 : (code_pre = (cm_type_encode (asked)))) (PreH11 : (cm_typed_program policy p )) (PreH12 : (cm_type_code_wf asked )) (PreH13 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH14 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
|--
  (cm_program_context_rep program_pre p functions_ptr )
.

Definition cm_sizeof_value_partial_solve_wit_1_pure := 
forall (code_pre: Z) (program_pre: Z) (functions_ptr: Z) (asked: cm_type) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (code_pre < 1024)) (PreH2 : (code_pre = (cm_type_encode (asked)))) (PreH3 : (cm_typed_program policy p )) (PreH4 : (cm_type_code_wf asked )) (PreH5 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH6 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  ((( &( "result" ) )) # Int64  |->_)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "code" ) )) # Int64  |-> code_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (cm_type_code_wf asked ) ” 
  &&  “ ((cm_type_encode (asked)) = (cm_type_encode (asked))) ”
.

Definition cm_sizeof_value_partial_solve_wit_1_aux := 
forall (code_pre: Z) (program_pre: Z) (functions_ptr: Z) (asked: cm_type) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (code_pre < 1024)) (PreH2 : (code_pre = (cm_type_encode (asked)))) (PreH3 : (cm_typed_program policy p )) (PreH4 : (cm_type_code_wf asked )) (PreH5 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH6 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  ((( &( "code" ) )) # Int64  |-> code_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (cm_type_code_wf asked ) ” 
  &&  “ ((cm_type_encode (asked)) = (cm_type_encode (asked))) ” 
  &&  “ (code_pre < 1024) ” 
  &&  “ (code_pre = (cm_type_encode (asked))) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_type_code_wf asked ) ” 
  &&  “ (cm_type_refs (cm_program_structs (p)) asked ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ”
  &&  ((( &( "code" ) )) # Int64  |-> (cm_type_encode (asked)))
  **  (cm_program_context_rep program_pre p functions_ptr )
.

Definition cm_sizeof_value_partial_solve_wit_1 := cm_sizeof_value_partial_solve_wit_1_pure -> cm_sizeof_value_partial_solve_wit_1_aux.

Definition cm_sizeof_value_partial_solve_wit_2 := 
forall (code_pre: Z) (program_pre: Z) (functions_ptr: Z) (asked: cm_type) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (cm_type_code_wf asked )) (PreH2 : ((cm_type_encode (asked)) = (cm_type_encode (asked)))) (PreH3 : (0 <= (cm_type_encode (asked)))) (PreH4 : (code_pre < 1024)) (PreH5 : (code_pre = (cm_type_encode (asked)))) (PreH6 : (cm_typed_program policy p )) (PreH7 : (cm_type_code_wf asked )) (PreH8 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH9 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (cm_type_code_wf asked ) ” 
  &&  “ (0 <= (cm_type_encode (asked))) ” 
  &&  “ (code_pre < 1024) ” 
  &&  “ (code_pre = (cm_type_encode (asked))) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_type_code_wf asked ) ” 
  &&  “ (cm_type_refs (cm_program_structs (p)) asked ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
.

Definition cm_sizeof_value_partial_solve_wit_3_pure := 
forall (code_pre: Z) (program_pre: Z) (functions_ptr: Z) (asked: cm_type) (p: cm_program) (policy: cm_lookup_policy) (tp: Z) (gp: Z) (sp: Z) (PreH1 : (program_pre <> 0)) (PreH2 : (cm_type_code_wf asked )) (PreH3 : (0 <= (cm_type_encode (asked)))) (PreH4 : (code_pre < 1024)) (PreH5 : (code_pre = (cm_type_encode (asked)))) (PreH6 : (cm_typed_program policy p )) (PreH7 : (cm_type_code_wf asked )) (PreH8 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH9 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((( &( "narrowed" ) )) # Int  |-> (cm_type_encode (asked)))
  **  ((( &( "code" ) )) # Int64  |-> (cm_type_encode (asked)))
  **  ((( &( "result" ) )) # Int64  |->_)
|--
  “ (0 <= (cm_type_encode (asked))) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ”
.

Definition cm_sizeof_value_partial_solve_wit_3_aux := 
forall (code_pre: Z) (program_pre: Z) (functions_ptr: Z) (asked: cm_type) (p: cm_program) (policy: cm_lookup_policy) (tp: Z) (gp: Z) (sp: Z) (PreH1 : (program_pre <> 0)) (PreH2 : (cm_type_code_wf asked )) (PreH3 : (0 <= (cm_type_encode (asked)))) (PreH4 : (code_pre < 1024)) (PreH5 : (code_pre = (cm_type_encode (asked)))) (PreH6 : (cm_typed_program policy p )) (PreH7 : (cm_type_code_wf asked )) (PreH8 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH9 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
|--
  “ (0 <= (cm_type_encode (asked))) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (program_pre <> 0) ” 
  &&  “ (cm_type_code_wf asked ) ” 
  &&  “ (0 <= (cm_type_encode (asked))) ” 
  &&  “ (code_pre < 1024) ” 
  &&  “ (code_pre = (cm_type_encode (asked))) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_type_code_wf asked ) ” 
  &&  “ (cm_type_refs (cm_program_structs (p)) asked ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ”
  &&  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
.

Definition cm_sizeof_value_partial_solve_wit_3 := cm_sizeof_value_partial_solve_wit_3_pure -> cm_sizeof_value_partial_solve_wit_3_aux.

Definition cm_sizeof_value_which_implies_wit_1 := 
(
forall (asked: cm_type) (code: Z) (PreH1 : (cm_type_code_wf asked )) (PreH2 : (code = (cm_type_encode (asked)))) ,
  TT && emp 
|--
  “ (cm_type_code_wf asked ) ” 
  &&  “ (code = (cm_type_encode (asked))) ” 
  &&  “ (0 <= code) ”
  &&  emp
) \/
(
forall (asked: cm_type) (code: Z) (PreH1 : (cm_type_code_wf asked )) (PreH2 : (code = (cm_type_encode (asked)))) ,
  TT && emp 
|--
  “ (0 <= code) ”
  &&  emp
).

Definition cm_sizeof_value_which_implies_wit_1_split_goal_1 := 
forall (asked: cm_type) (code: Z) (PreH1 : (cm_type_code_wf asked )) (PreH2 : (code = (cm_type_encode (asked)))) ,
  (0 <= code)
.

Definition cm_sizeof_value_which_implies_wit_2 := 
(
forall (functions_ptr: Z) (p: cm_program) (program: Z) ,
  (cm_program_context_rep program p functions_ptr )
|--
  EX (tp: Z)  (gp: Z)  (sp: Z) ,
  “ (program <> 0) ”
  &&  ((&((program)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
) \/
(
forall (functions_ptr: Z) (p: cm_program) (program: Z) ,
  (cm_program_context_rep program p functions_ptr )
|--
  EX (tp: Z)  (gp: Z)  (sp: Z) ,
  “ (program <> 0) ”
  &&  ((&((program)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
).

(*----- Function cm_type_size_value -----*)

Definition cm_type_size_value_return_wit_1 := 
forall (code_pre: Z) (program_pre: Z) (functions_ptr: Z) (asked: cm_type) (p: cm_program) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (code_pre = (cm_type_encode (asked)))) (PreH2 : (cm_typed_program policy p )) (PreH3 : (cm_type_code_wf asked )) (PreH4 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH5 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH6 : (retval = (cm_type_size ((cm_program_structs (p))) (asked)))) (PreH7 : (code_pre = (cm_type_encode (asked)))) (PreH8 : (cm_typed_program policy p )) (PreH9 : (cm_type_code_wf asked )) (PreH10 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH11 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (code_pre = (cm_type_encode (asked))) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_type_code_wf asked ) ” 
  &&  “ (cm_type_refs (cm_program_structs (p)) asked ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (retval = (cm_type_size ((cm_program_structs (p))) (asked))) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
.

Definition cm_type_size_value_partial_solve_wit_1_pure := 
forall (code_pre: Z) (program_pre: Z) (functions_ptr: Z) (asked: cm_type) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (code_pre = (cm_type_encode (asked)))) (PreH2 : (cm_typed_program policy p )) (PreH3 : (cm_type_code_wf asked )) (PreH4 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH5 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "code" ) )) # Int64  |-> code_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (code_pre = (cm_type_encode (asked))) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_type_code_wf asked ) ” 
  &&  “ (cm_type_refs (cm_program_structs (p)) asked ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ”
.

Definition cm_type_size_value_partial_solve_wit_1_aux := 
forall (code_pre: Z) (program_pre: Z) (functions_ptr: Z) (asked: cm_type) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (code_pre = (cm_type_encode (asked)))) (PreH2 : (cm_typed_program policy p )) (PreH3 : (cm_type_code_wf asked )) (PreH4 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH5 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (code_pre = (cm_type_encode (asked))) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_type_code_wf asked ) ” 
  &&  “ (cm_type_refs (cm_program_structs (p)) asked ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (code_pre = (cm_type_encode (asked))) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_type_code_wf asked ) ” 
  &&  “ (cm_type_refs (cm_program_structs (p)) asked ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
.

Definition cm_type_size_value_partial_solve_wit_1 := cm_type_size_value_partial_solve_wit_1_pure -> cm_type_size_value_partial_solve_wit_1_aux.

(*----- Function cm_emit_sizeof_expr -----*)

Definition cm_emit_sizeof_expr_safety_wit_1 := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (asked: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (lvalue_pre = 0)) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH4 : (cm_typed_program policy p )) (PreH5 : (cm_type_code_wf asked )) (PreH6 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH7 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH8 : (retval = (cm_type_size ((cm_program_structs (p))) (asked)))) (PreH9 : (lvalue_pre = 0)) (PreH10 : (expr_pre <> 0)) (PreH11 : (0 <= lvalue_pre)) (PreH12 : (lvalue_pre <= 1)) (PreH13 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH14 : (e = (CMSizeofE (asked) (ty)))) (PreH15 : (cm_typed_program policy p )) (PreH16 : (cm_type_code_wf asked )) (PreH17 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH18 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) ((cm_type_size ((cm_program_structs (p))) (asked))))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  ((( &( "size" ) )) # Int64  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_type_encode (asked)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_emit_sizeof_expr_entail_wit_1 := 
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (asked: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= lvalue_pre)) (PreH2 : (lvalue_pre <= 1)) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (e = (CMSizeofE (asked) (ty)))) (PreH5 : (cm_typed_program policy p )) (PreH6 : (cm_type_code_wf asked )) (PreH7 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH8 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafSizeof (asked) (ty))) (lvalue_pre))) (tail)) )
|--
  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (e = (CMSizeofE (asked) (ty))) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_type_code_wf asked ) ” 
  &&  “ (cm_type_refs (cm_program_structs (p)) asked ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_type_encode (asked)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafSizeof (asked) (ty))) (lvalue_pre))) (tail)) )
) \/
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (asked: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= lvalue_pre)) (PreH2 : (lvalue_pre <= 1)) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (e = (CMSizeofE (asked) (ty)))) (PreH5 : (cm_typed_program policy p )) (PreH6 : (cm_type_code_wf asked )) (PreH7 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH8 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafSizeof (asked) (ty))) (lvalue_pre))) (tail)) )
|--
  “ (expr_pre <> 0) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_type_encode (asked)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafSizeof (asked) (ty))) (lvalue_pre))) (tail)) )
).

Definition cm_emit_sizeof_expr_entail_wit_1_split_goal_1 := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (asked: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= lvalue_pre)) (PreH2 : (lvalue_pre <= 1)) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (e = (CMSizeofE (asked) (ty)))) (PreH5 : (cm_typed_program policy p )) (PreH6 : (cm_type_code_wf asked )) (PreH7 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH8 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafSizeof (asked) (ty))) (lvalue_pre))) (tail)) )
|--
  “ (expr_pre <> 0) ”
.

Definition cm_emit_sizeof_expr_entail_wit_1_split_goal_spatial := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (asked: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= lvalue_pre)) (PreH2 : (lvalue_pre <= 1)) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (e = (CMSizeofE (asked) (ty)))) (PreH5 : (cm_typed_program policy p )) (PreH6 : (cm_type_code_wf asked )) (PreH7 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH8 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafSizeof (asked) (ty))) (lvalue_pre))) (tail)) )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_type_encode (asked)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafSizeof (asked) (ty))) (lvalue_pre))) (tail)) )
.

Definition cm_emit_sizeof_expr_return_wit_1 := 
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (asked: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (lvalue_pre = 0)) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH4 : (cm_typed_program policy p )) (PreH5 : (cm_type_code_wf asked )) (PreH6 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH7 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH8 : (retval = (cm_type_size ((cm_program_structs (p))) (asked)))) (PreH9 : (lvalue_pre = 0)) (PreH10 : (expr_pre <> 0)) (PreH11 : (0 <= lvalue_pre)) (PreH12 : (lvalue_pre <= 1)) (PreH13 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH14 : (e = (CMSizeofE (asked) (ty)))) (PreH15 : (cm_typed_program policy p )) (PreH16 : (cm_type_code_wf asked )) (PreH17 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH18 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMPushOp) (retval))) ((@nil tvm_inst))))) tail )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_type_encode (asked)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
|--
  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (e = (CMSizeofE (asked) (ty))) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_type_code_wf asked ) ” 
  &&  “ (cm_type_refs (cm_program_structs (p)) asked ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_leaf_code_for (p) ((CMLeafSizeof (asked) (ty))) (lvalue_pre)))) tail )
) \/
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (asked: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (retval: Z) (PreH1 : ((cm_type_encode (asked)) <= INT64_MAX)) (PreH2 : ((cm_type_encode (asked)) >= INT64_MIN)) (PreH3 : ((cm_type_encode (ty)) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode (ty)) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (lvalue_pre = 0)) (PreH10 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH11 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH12 : (cm_typed_program policy p )) (PreH13 : (cm_type_code_wf asked )) (PreH14 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH15 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH16 : (retval = (cm_type_size ((cm_program_structs (p))) (asked)))) (PreH17 : (lvalue_pre = 0)) (PreH18 : (expr_pre <> 0)) (PreH19 : (0 <= lvalue_pre)) (PreH20 : (lvalue_pre <= 1)) (PreH21 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH22 : (e = (CMSizeofE (asked) (ty)))) (PreH23 : (cm_typed_program policy p )) (PreH24 : (cm_type_code_wf asked )) (PreH25 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH26 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMPushOp) (retval))) ((@nil tvm_inst))))) tail )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_type_encode (asked)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_leaf_code_for (p) ((CMLeafSizeof (asked) (ty))) (lvalue_pre)))) tail )
).

Definition cm_emit_sizeof_expr_return_wit_1_split_goal_spatial := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (asked: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (retval: Z) (PreH1 : ((cm_type_encode (asked)) <= INT64_MAX)) (PreH2 : ((cm_type_encode (asked)) >= INT64_MIN)) (PreH3 : ((cm_type_encode (ty)) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode (ty)) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (lvalue_pre = 0)) (PreH10 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH11 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH12 : (cm_typed_program policy p )) (PreH13 : (cm_type_code_wf asked )) (PreH14 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH15 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH16 : (retval = (cm_type_size ((cm_program_structs (p))) (asked)))) (PreH17 : (lvalue_pre = 0)) (PreH18 : (expr_pre <> 0)) (PreH19 : (0 <= lvalue_pre)) (PreH20 : (lvalue_pre <= 1)) (PreH21 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH22 : (e = (CMSizeofE (asked) (ty)))) (PreH23 : (cm_typed_program policy p )) (PreH24 : (cm_type_code_wf asked )) (PreH25 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH26 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMPushOp) (retval))) ((@nil tvm_inst))))) tail )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_type_encode (asked)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_leaf_code_for (p) ((CMLeafSizeof (asked) (ty))) (lvalue_pre)))) tail )
.

Definition cm_emit_sizeof_expr_return_wit_2 := 
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (asked: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (lvalue_pre <> 0)) (PreH2 : (expr_pre <> 0)) (PreH3 : (0 <= lvalue_pre)) (PreH4 : (lvalue_pre <= 1)) (PreH5 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH6 : (e = (CMSizeofE (asked) (ty)))) (PreH7 : (cm_typed_program policy p )) (PreH8 : (cm_type_code_wf asked )) (PreH9 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH10 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_type_encode (asked)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafSizeof (asked) (ty))) (lvalue_pre))) (tail)) )
|--
  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (e = (CMSizeofE (asked) (ty))) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_type_code_wf asked ) ” 
  &&  “ (cm_type_refs (cm_program_structs (p)) asked ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_leaf_code_for (p) ((CMLeafSizeof (asked) (ty))) (lvalue_pre)))) tail )
) \/
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (asked: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : ((cm_type_encode (asked)) <= INT64_MAX)) (PreH2 : ((cm_type_encode (asked)) >= INT64_MIN)) (PreH3 : ((cm_type_encode (ty)) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode (ty)) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (lvalue_pre <> 0)) (PreH10 : (expr_pre <> 0)) (PreH11 : (0 <= lvalue_pre)) (PreH12 : (lvalue_pre <= 1)) (PreH13 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH14 : (e = (CMSizeofE (asked) (ty)))) (PreH15 : (cm_typed_program policy p )) (PreH16 : (cm_type_code_wf asked )) (PreH17 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH18 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_type_encode (asked)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafSizeof (asked) (ty))) (lvalue_pre))) (tail)) )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_leaf_code_for (p) ((CMLeafSizeof (asked) (ty))) (lvalue_pre)))) tail )
).

Definition cm_emit_sizeof_expr_return_wit_2_split_goal_spatial := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (asked: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : ((cm_type_encode (asked)) <= INT64_MAX)) (PreH2 : ((cm_type_encode (asked)) >= INT64_MIN)) (PreH3 : ((cm_type_encode (ty)) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode (ty)) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (lvalue_pre <> 0)) (PreH10 : (expr_pre <> 0)) (PreH11 : (0 <= lvalue_pre)) (PreH12 : (lvalue_pre <= 1)) (PreH13 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH14 : (e = (CMSizeofE (asked) (ty)))) (PreH15 : (cm_typed_program policy p )) (PreH16 : (cm_type_code_wf asked )) (PreH17 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH18 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_type_encode (asked)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafSizeof (asked) (ty))) (lvalue_pre))) (tail)) )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_leaf_code_for (p) ((CMLeafSizeof (asked) (ty))) (lvalue_pre)))) tail )
.

Definition cm_emit_sizeof_expr_partial_solve_wit_1_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (asked: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (lvalue_pre = 0)) (PreH2 : (expr_pre <> 0)) (PreH3 : (0 <= lvalue_pre)) (PreH4 : (lvalue_pre <= 1)) (PreH5 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH6 : (e = (CMSizeofE (asked) (ty)))) (PreH7 : (cm_typed_program policy p )) (PreH8 : (cm_type_code_wf asked )) (PreH9 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH10 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  ((( &( "size" ) )) # Int64  |->_)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_type_encode (asked)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafSizeof (asked) (ty))) (lvalue_pre))) (tail)) )
|--
  “ ((cm_type_encode (asked)) = (cm_type_encode (asked))) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_type_code_wf asked ) ” 
  &&  “ (cm_type_refs (cm_program_structs (p)) asked ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ”
.

Definition cm_emit_sizeof_expr_partial_solve_wit_1_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (asked: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (lvalue_pre = 0)) (PreH2 : (expr_pre <> 0)) (PreH3 : (0 <= lvalue_pre)) (PreH4 : (lvalue_pre <= 1)) (PreH5 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH6 : (e = (CMSizeofE (asked) (ty)))) (PreH7 : (cm_typed_program policy p )) (PreH8 : (cm_type_code_wf asked )) (PreH9 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH10 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_type_encode (asked)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafSizeof (asked) (ty))) (lvalue_pre))) (tail)) )
|--
  “ ((cm_type_encode (asked)) = (cm_type_encode (asked))) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_type_code_wf asked ) ” 
  &&  “ (cm_type_refs (cm_program_structs (p)) asked ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (lvalue_pre = 0) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (e = (CMSizeofE (asked) (ty))) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_type_code_wf asked ) ” 
  &&  “ (cm_type_refs (cm_program_structs (p)) asked ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_type_encode (asked)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafSizeof (asked) (ty))) (lvalue_pre))) (tail)) )
.

Definition cm_emit_sizeof_expr_partial_solve_wit_1 := cm_emit_sizeof_expr_partial_solve_wit_1_pure -> cm_emit_sizeof_expr_partial_solve_wit_1_aux.

Definition cm_emit_sizeof_expr_partial_solve_wit_2_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (asked: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (retval: Z) (PreH1 : ((cm_type_encode (asked)) = (cm_type_encode (asked)))) (PreH2 : (cm_typed_program policy p )) (PreH3 : (cm_type_code_wf asked )) (PreH4 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH5 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH6 : (retval = (cm_type_size ((cm_program_structs (p))) (asked)))) (PreH7 : (lvalue_pre = 0)) (PreH8 : (expr_pre <> 0)) (PreH9 : (0 <= lvalue_pre)) (PreH10 : (lvalue_pre <= 1)) (PreH11 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH12 : (e = (CMSizeofE (asked) (ty)))) (PreH13 : (cm_typed_program policy p )) (PreH14 : (cm_type_code_wf asked )) (PreH15 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH16 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  ((( &( "size" ) )) # Int64  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_type_encode (asked)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafSizeof (asked) (ty))) (lvalue_pre))) (tail)) )
|--
  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 0) ”
.

Definition cm_emit_sizeof_expr_partial_solve_wit_2_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (asked: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (retval: Z) (PreH1 : ((cm_type_encode (asked)) = (cm_type_encode (asked)))) (PreH2 : (cm_typed_program policy p )) (PreH3 : (cm_type_code_wf asked )) (PreH4 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH5 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH6 : (retval = (cm_type_size ((cm_program_structs (p))) (asked)))) (PreH7 : (lvalue_pre = 0)) (PreH8 : (expr_pre <> 0)) (PreH9 : (0 <= lvalue_pre)) (PreH10 : (lvalue_pre <= 1)) (PreH11 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH12 : (e = (CMSizeofE (asked) (ty)))) (PreH13 : (cm_typed_program policy p )) (PreH14 : (cm_type_code_wf asked )) (PreH15 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH16 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_type_encode (asked)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafSizeof (asked) (ty))) (lvalue_pre))) (tail)) )
|--
  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 0) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_type_code_wf asked ) ” 
  &&  “ (cm_type_refs (cm_program_structs (p)) asked ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (retval = (cm_type_size ((cm_program_structs (p))) (asked))) ” 
  &&  “ (lvalue_pre = 0) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (e = (CMSizeofE (asked) (ty))) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_type_code_wf asked ) ” 
  &&  “ (cm_type_refs (cm_program_structs (p)) asked ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafSizeof (asked) (ty))) (lvalue_pre))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_type_encode (asked)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
.

Definition cm_emit_sizeof_expr_partial_solve_wit_2 := cm_emit_sizeof_expr_partial_solve_wit_2_pure -> cm_emit_sizeof_expr_partial_solve_wit_2_aux.

Definition cm_emit_sizeof_expr_partial_solve_wit_3_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (asked: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (lvalue_pre = 0)) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH4 : (cm_typed_program policy p )) (PreH5 : (cm_type_code_wf asked )) (PreH6 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH7 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH8 : (retval = (cm_type_size ((cm_program_structs (p))) (asked)))) (PreH9 : (lvalue_pre = 0)) (PreH10 : (expr_pre <> 0)) (PreH11 : (0 <= lvalue_pre)) (PreH12 : (lvalue_pre <= 1)) (PreH13 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH14 : (e = (CMSizeofE (asked) (ty)))) (PreH15 : (cm_typed_program policy p )) (PreH16 : (cm_type_code_wf asked )) (PreH17 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH18 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) ((cm_type_size ((cm_program_structs (p))) (asked))))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  ((( &( "size" ) )) # Int64  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_type_encode (asked)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ”
.

Definition cm_emit_sizeof_expr_partial_solve_wit_3_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (asked: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (lvalue_pre = 0)) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH4 : (cm_typed_program policy p )) (PreH5 : (cm_type_code_wf asked )) (PreH6 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH7 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH8 : (retval = (cm_type_size ((cm_program_structs (p))) (asked)))) (PreH9 : (lvalue_pre = 0)) (PreH10 : (expr_pre <> 0)) (PreH11 : (0 <= lvalue_pre)) (PreH12 : (lvalue_pre <= 1)) (PreH13 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH14 : (e = (CMSizeofE (asked) (ty)))) (PreH15 : (cm_typed_program policy p )) (PreH16 : (cm_type_code_wf asked )) (PreH17 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH18 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) ((cm_type_size ((cm_program_structs (p))) (asked))))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_type_encode (asked)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ” 
  &&  “ (lvalue_pre = 0) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) = 0) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_type_code_wf asked ) ” 
  &&  “ (cm_type_refs (cm_program_structs (p)) asked ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (retval = (cm_type_size ((cm_program_structs (p))) (asked))) ” 
  &&  “ (lvalue_pre = 0) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (e = (CMSizeofE (asked) (ty))) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_type_code_wf asked ) ” 
  &&  “ (cm_type_refs (cm_program_structs (p)) asked ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) (retval))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_type_encode (asked)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
.

Definition cm_emit_sizeof_expr_partial_solve_wit_3 := cm_emit_sizeof_expr_partial_solve_wit_3_pure -> cm_emit_sizeof_expr_partial_solve_wit_3_aux.

Definition cm_emit_sizeof_expr_which_implies_wit_1 := 
(
forall (asked: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (ty: cm_type) (p: cm_program) (policy: cm_lookup_policy) (lvalue: Z) (emitter: Z) (PreH1 : (0 <= lvalue)) (PreH2 : (lvalue <= 0)) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_leaf_code_for (p) ((CMLeafSizeof (asked) (ty))) (lvalue))) (tail)) )
|--
  “ (lvalue = 0) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) = 0) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (cons ((TVMInst (TVMPushOp) ((cm_type_size ((cm_program_structs (p))) (asked))))) (tail)) )
) \/
(
forall (asked: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (ty: cm_type) (p: cm_program) (policy: cm_lookup_policy) (lvalue: Z) (emitter: Z) (PreH1 : (0 <= lvalue)) (PreH2 : (lvalue <= 0)) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_leaf_code_for (p) ((CMLeafSizeof (asked) (ty))) (lvalue))) (tail)) )
|--
  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) = 0) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (cons ((TVMInst (TVMPushOp) ((cm_type_size ((cm_program_structs (p))) (asked))))) (tail)) )
).

Definition cm_emit_sizeof_expr_which_implies_wit_1_split_goal_1 := 
forall (asked: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (ty: cm_type) (p: cm_program) (policy: cm_lookup_policy) (lvalue: Z) (emitter: Z) (PreH1 : (0 <= lvalue)) (PreH2 : (lvalue <= 0)) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_leaf_code_for (p) ((CMLeafSizeof (asked) (ty))) (lvalue))) (tail)) )
|--
  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ”
.

Definition cm_emit_sizeof_expr_which_implies_wit_1_split_goal_2 := 
forall (asked: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (ty: cm_type) (p: cm_program) (policy: cm_lookup_policy) (lvalue: Z) (emitter: Z) (PreH1 : (0 <= lvalue)) (PreH2 : (lvalue <= 0)) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_leaf_code_for (p) ((CMLeafSizeof (asked) (ty))) (lvalue))) (tail)) )
|--
  “ ((tvm_opcode_code (TVMPushOp)) = 0) ”
.

Definition cm_emit_sizeof_expr_which_implies_wit_1_split_goal_spatial := 
forall (asked: cm_type) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (ty: cm_type) (p: cm_program) (policy: cm_lookup_policy) (lvalue: Z) (emitter: Z) (PreH1 : (0 <= lvalue)) (PreH2 : (lvalue <= 0)) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_leaf_code_for (p) ((CMLeafSizeof (asked) (ty))) (lvalue))) (tail)) )
|--
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (cons ((TVMInst (TVMPushOp) ((cm_type_size ((cm_program_structs (p))) (asked))))) (tail)) )
.

(*----- Function cm_member_array_value_context -----*)

Definition cm_member_array_value_context_entail_wit_1 := 
(
forall (mid_pre: Z) (base_ty_pre: Z) (program_pre: Z) (functions_ptr: Z) (base: cm_type) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (base_ty_pre = (cm_type_encode (base)))) (PreH2 : (cm_i32_code_count base_ty_pre )) (PreH3 : (cm_typed_program policy p )) (PreH4 : (cm_type_code_wf base )) (PreH5 : (cm_member_valid p base mid_pre )) (PreH6 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
|--
  EX (tp: Z)  (gp: Z)  (sp: Z) ,
  “ (program_pre <> 0) ” 
  &&  “ (base_ty_pre = (cm_type_encode (base))) ” 
  &&  “ (cm_i32_code_count base_ty_pre ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_type_code_wf base ) ” 
  &&  “ (cm_member_valid p base mid_pre ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (1024 <= base_ty_pre) ” 
  &&  “ (base_ty_pre <= INT_MAX) ” 
  &&  “ (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 )) ” 
  &&  “ (0 <= mid_pre) ”
  &&  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
) \/
(
forall (mid_pre: Z) (base_ty_pre: Z) (program_pre: Z) (functions_ptr: Z) (base: cm_type) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (base_ty_pre = (cm_type_encode (base)))) (PreH2 : (cm_i32_code_count base_ty_pre )) (PreH3 : (cm_typed_program policy p )) (PreH4 : (cm_type_code_wf base )) (PreH5 : (cm_member_valid p base mid_pre )) (PreH6 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
|--
  EX (tp: Z)  (gp: Z)  (sp: Z) ,
  “ (program_pre <> 0) ” 
  &&  “ (base_ty_pre = (cm_type_encode (base))) ” 
  &&  “ (cm_i32_code_count base_ty_pre ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_type_code_wf base ) ” 
  &&  “ (cm_member_valid p base mid_pre ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (1024 <= base_ty_pre) ” 
  &&  “ (base_ty_pre <= INT_MAX) ” 
  &&  “ (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 )) ” 
  &&  “ (0 <= mid_pre) ”
  &&  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
).

Definition cm_member_array_value_context_return_wit_1 := 
(
forall (mid_pre: Z) (base_ty_pre: Z) (program_pre: Z) (functions_ptr: Z) (base: cm_type) (p: cm_program) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (retval: Z) (PreH1 : (1024 <= base_ty_pre)) (PreH2 : (base_ty_pre <= INT_MAX)) (PreH3 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH4 : (0 <= mid_pre)) (PreH5 : ((cm_program_structs (p)) = (cm_program_structs (p)))) (PreH6 : (base_ty_pre = (cm_type_encode (base)))) (PreH7 : (cm_type_code_wf base )) (PreH8 : (cm_member_valid p base mid_pre )) (PreH9 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH10 : (retval = (cm_member_array_code (p) (base) (mid_pre)))) (PreH11 : (program_pre <> 0)) (PreH12 : (base_ty_pre = (cm_type_encode (base)))) (PreH13 : (cm_i32_code_count base_ty_pre )) (PreH14 : (cm_typed_program policy p )) (PreH15 : (cm_type_code_wf base )) (PreH16 : (cm_member_valid p base mid_pre )) (PreH17 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH18 : (1024 <= base_ty_pre)) (PreH19 : (base_ty_pre <= INT_MAX)) (PreH20 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH21 : (0 <= mid_pre)) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
|--
  “ (base_ty_pre = (cm_type_encode (base))) ” 
  &&  “ (cm_i32_code_count base_ty_pre ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_type_code_wf base ) ” 
  &&  “ (cm_member_valid p base mid_pre ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (retval = (cm_member_array_code (p) (base) (mid_pre))) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
) \/
(
forall (mid_pre: Z) (base_ty_pre: Z) (program_pre: Z) (functions_ptr: Z) (base: cm_type) (p: cm_program) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (retval: Z) (PreH1 : ((cm_program_main (p)) <= INT_MAX)) (PreH2 : ((cm_program_main (p)) >= INT_MIN)) (PreH3 : (1024 <= base_ty_pre)) (PreH4 : (base_ty_pre <= INT_MAX)) (PreH5 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH6 : (0 <= mid_pre)) (PreH7 : (base_ty_pre = (cm_type_encode (base)))) (PreH8 : (cm_type_code_wf base )) (PreH9 : (cm_member_valid p base mid_pre )) (PreH10 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH11 : (retval = (cm_member_array_code (p) (base) (mid_pre)))) (PreH12 : (program_pre <> 0)) (PreH13 : (base_ty_pre = (cm_type_encode (base)))) (PreH14 : (cm_i32_code_count base_ty_pre )) (PreH15 : (cm_typed_program policy p )) (PreH16 : (cm_type_code_wf base )) (PreH17 : (cm_member_valid p base mid_pre )) (PreH18 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH19 : (1024 <= base_ty_pre)) (PreH20 : (base_ty_pre <= INT_MAX)) (PreH21 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH22 : (0 <= mid_pre)) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
|--
  (cm_program_context_rep program_pre p functions_ptr )
).

Definition cm_member_array_value_context_return_wit_1_split_goal_spatial := 
forall (mid_pre: Z) (base_ty_pre: Z) (program_pre: Z) (functions_ptr: Z) (base: cm_type) (p: cm_program) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (retval: Z) (PreH1 : ((cm_program_main (p)) <= INT_MAX)) (PreH2 : ((cm_program_main (p)) >= INT_MIN)) (PreH3 : (1024 <= base_ty_pre)) (PreH4 : (base_ty_pre <= INT_MAX)) (PreH5 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH6 : (0 <= mid_pre)) (PreH7 : (base_ty_pre = (cm_type_encode (base)))) (PreH8 : (cm_type_code_wf base )) (PreH9 : (cm_member_valid p base mid_pre )) (PreH10 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH11 : (retval = (cm_member_array_code (p) (base) (mid_pre)))) (PreH12 : (program_pre <> 0)) (PreH13 : (base_ty_pre = (cm_type_encode (base)))) (PreH14 : (cm_i32_code_count base_ty_pre )) (PreH15 : (cm_typed_program policy p )) (PreH16 : (cm_type_code_wf base )) (PreH17 : (cm_member_valid p base mid_pre )) (PreH18 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH19 : (1024 <= base_ty_pre)) (PreH20 : (base_ty_pre <= INT_MAX)) (PreH21 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH22 : (0 <= mid_pre)) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
|--
  (cm_program_context_rep program_pre p functions_ptr )
.

Definition cm_member_array_value_context_partial_solve_wit_1_pure := 
forall (mid_pre: Z) (base_ty_pre: Z) (program_pre: Z) (functions_ptr: Z) (base: cm_type) (p: cm_program) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (PreH1 : (program_pre <> 0)) (PreH2 : (base_ty_pre = (cm_type_encode (base)))) (PreH3 : (cm_i32_code_count base_ty_pre )) (PreH4 : (cm_typed_program policy p )) (PreH5 : (cm_type_code_wf base )) (PreH6 : (cm_member_valid p base mid_pre )) (PreH7 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH8 : (1024 <= base_ty_pre)) (PreH9 : (base_ty_pre <= INT_MAX)) (PreH10 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH11 : (0 <= mid_pre)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "base_ty" ) )) # Int  |-> base_ty_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
|--
  “ (1024 <= base_ty_pre) ” 
  &&  “ (base_ty_pre <= INT_MAX) ” 
  &&  “ (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 )) ” 
  &&  “ (0 <= mid_pre) ” 
  &&  “ ((cm_program_structs (p)) = (cm_program_structs (p))) ” 
  &&  “ (base_ty_pre = (cm_type_encode (base))) ” 
  &&  “ (cm_type_code_wf base ) ” 
  &&  “ (cm_member_valid p base mid_pre ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ”
.

Definition cm_member_array_value_context_partial_solve_wit_1_aux := 
forall (mid_pre: Z) (base_ty_pre: Z) (program_pre: Z) (functions_ptr: Z) (base: cm_type) (p: cm_program) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (PreH1 : (program_pre <> 0)) (PreH2 : (base_ty_pre = (cm_type_encode (base)))) (PreH3 : (cm_i32_code_count base_ty_pre )) (PreH4 : (cm_typed_program policy p )) (PreH5 : (cm_type_code_wf base )) (PreH6 : (cm_member_valid p base mid_pre )) (PreH7 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH8 : (1024 <= base_ty_pre)) (PreH9 : (base_ty_pre <= INT_MAX)) (PreH10 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH11 : (0 <= mid_pre)) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
|--
  “ (1024 <= base_ty_pre) ” 
  &&  “ (base_ty_pre <= INT_MAX) ” 
  &&  “ (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 )) ” 
  &&  “ (0 <= mid_pre) ” 
  &&  “ ((cm_program_structs (p)) = (cm_program_structs (p))) ” 
  &&  “ (base_ty_pre = (cm_type_encode (base))) ” 
  &&  “ (cm_type_code_wf base ) ” 
  &&  “ (cm_member_valid p base mid_pre ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (program_pre <> 0) ” 
  &&  “ (base_ty_pre = (cm_type_encode (base))) ” 
  &&  “ (cm_i32_code_count base_ty_pre ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_type_code_wf base ) ” 
  &&  “ (cm_member_valid p base mid_pre ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (1024 <= base_ty_pre) ” 
  &&  “ (base_ty_pre <= INT_MAX) ” 
  &&  “ (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 )) ” 
  &&  “ (0 <= mid_pre) ”
  &&  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
.

Definition cm_member_array_value_context_partial_solve_wit_1 := cm_member_array_value_context_partial_solve_wit_1_pure -> cm_member_array_value_context_partial_solve_wit_1_aux.

(*----- Function cm_member_offset_value_context -----*)

Definition cm_member_offset_value_context_safety_wit_1 := 
(
forall (mid_pre: Z) (base_ty_pre: Z) (program_pre: Z) (functions_ptr: Z) (base: cm_type) (p: cm_program) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (retval: Z) (PreH1 : (retval = (base_ty_pre - 1024 ))) (PreH2 : (program_pre <> 0)) (PreH3 : (base_ty_pre = (cm_type_encode (base)))) (PreH4 : (cm_i32_code_count base_ty_pre )) (PreH5 : (cm_typed_program policy p )) (PreH6 : (cm_type_code_wf base )) (PreH7 : (cm_member_valid p base mid_pre )) (PreH8 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH9 : (1024 <= base_ty_pre)) (PreH10 : (base_ty_pre <= INT_MAX)) (PreH11 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH12 : (0 <= mid_pre)) ,
  ((( &( "sid" ) )) # Int  |->_)
  **  ((( &( "pointee" ) )) # Int  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "base_ty" ) )) # Int  |-> base_ty_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
|--
  “ (((retval % ( 1024 ) ) - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((retval % ( 1024 ) ) - 2 )) ”
) \/
(
forall (mid_pre: Z) (base_ty_pre: Z) (program_pre: Z) (functions_ptr: Z) (base: cm_type) (p: cm_program) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (retval: Z) (PreH1 : (retval = (base_ty_pre - 1024 ))) (PreH2 : (program_pre <> 0)) (PreH3 : (base_ty_pre = (cm_type_encode (base)))) (PreH4 : (cm_i32_code_count base_ty_pre )) (PreH5 : (cm_typed_program policy p )) (PreH6 : (cm_type_code_wf base )) (PreH7 : (cm_member_valid p base mid_pre )) (PreH8 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH9 : (1024 <= base_ty_pre)) (PreH10 : (base_ty_pre <= INT_MAX)) (PreH11 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH12 : (0 <= mid_pre)) ,
  ((( &( "sid" ) )) # Int  |->_)
  **  ((( &( "pointee" ) )) # Int  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "base_ty" ) )) # Int  |-> base_ty_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
|--
  “ (((retval % ( 1024 ) ) - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((retval % ( 1024 ) ) - 2 )) ”
).

Definition cm_member_offset_value_context_safety_wit_1_split_goal_1 := 
forall (mid_pre: Z) (base_ty_pre: Z) (program_pre: Z) (functions_ptr: Z) (base: cm_type) (p: cm_program) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (retval: Z) (PreH1 : (retval = (base_ty_pre - 1024 ))) (PreH2 : (program_pre <> 0)) (PreH3 : (base_ty_pre = (cm_type_encode (base)))) (PreH4 : (cm_i32_code_count base_ty_pre )) (PreH5 : (cm_typed_program policy p )) (PreH6 : (cm_type_code_wf base )) (PreH7 : (cm_member_valid p base mid_pre )) (PreH8 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH9 : (1024 <= base_ty_pre)) (PreH10 : (base_ty_pre <= INT_MAX)) (PreH11 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH12 : (0 <= mid_pre)) ,
  ((( &( "sid" ) )) # Int  |->_)
  **  ((( &( "pointee" ) )) # Int  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "base_ty" ) )) # Int  |-> base_ty_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
|--
  “ (((retval % ( 1024 ) ) - 2 ) <= INT_MAX) ”
.

Definition cm_member_offset_value_context_safety_wit_1_split_goal_2 := 
forall (mid_pre: Z) (base_ty_pre: Z) (program_pre: Z) (functions_ptr: Z) (base: cm_type) (p: cm_program) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (retval: Z) (PreH1 : (retval = (base_ty_pre - 1024 ))) (PreH2 : (program_pre <> 0)) (PreH3 : (base_ty_pre = (cm_type_encode (base)))) (PreH4 : (cm_i32_code_count base_ty_pre )) (PreH5 : (cm_typed_program policy p )) (PreH6 : (cm_type_code_wf base )) (PreH7 : (cm_member_valid p base mid_pre )) (PreH8 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH9 : (1024 <= base_ty_pre)) (PreH10 : (base_ty_pre <= INT_MAX)) (PreH11 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH12 : (0 <= mid_pre)) ,
  ((( &( "sid" ) )) # Int  |->_)
  **  ((( &( "pointee" ) )) # Int  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "base_ty" ) )) # Int  |-> base_ty_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
|--
  “ ((INT_MIN) <= ((retval % ( 1024 ) ) - 2 )) ”
.

Definition cm_member_offset_value_context_safety_wit_2 := 
forall (mid_pre: Z) (base_ty_pre: Z) (program_pre: Z) (functions_ptr: Z) (base: cm_type) (p: cm_program) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (retval: Z) (PreH1 : (retval = (base_ty_pre - 1024 ))) (PreH2 : (program_pre <> 0)) (PreH3 : (base_ty_pre = (cm_type_encode (base)))) (PreH4 : (cm_i32_code_count base_ty_pre )) (PreH5 : (cm_typed_program policy p )) (PreH6 : (cm_type_code_wf base )) (PreH7 : (cm_member_valid p base mid_pre )) (PreH8 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH9 : (1024 <= base_ty_pre)) (PreH10 : (base_ty_pre <= INT_MAX)) (PreH11 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH12 : (0 <= mid_pre)) ,
  ((( &( "sid" ) )) # Int  |->_)
  **  ((( &( "pointee" ) )) # Int  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "base_ty" ) )) # Int  |-> base_ty_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
|--
  “ ((retval <> (INT_MIN)) \/ (1024 <> (-1))) ” 
  &&  “ (1024 <> 0) ”
.

Definition cm_member_offset_value_context_safety_wit_3 := 
forall (mid_pre: Z) (base_ty_pre: Z) (program_pre: Z) (functions_ptr: Z) (base: cm_type) (p: cm_program) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (retval: Z) (PreH1 : (retval = (base_ty_pre - 1024 ))) (PreH2 : (program_pre <> 0)) (PreH3 : (base_ty_pre = (cm_type_encode (base)))) (PreH4 : (cm_i32_code_count base_ty_pre )) (PreH5 : (cm_typed_program policy p )) (PreH6 : (cm_type_code_wf base )) (PreH7 : (cm_member_valid p base mid_pre )) (PreH8 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH9 : (1024 <= base_ty_pre)) (PreH10 : (base_ty_pre <= INT_MAX)) (PreH11 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH12 : (0 <= mid_pre)) ,
  ((( &( "sid" ) )) # Int  |->_)
  **  ((( &( "pointee" ) )) # Int  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "base_ty" ) )) # Int  |-> base_ty_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
|--
  “ (1024 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1024) ”
.

Definition cm_member_offset_value_context_safety_wit_4 := 
forall (mid_pre: Z) (base_ty_pre: Z) (program_pre: Z) (functions_ptr: Z) (base: cm_type) (p: cm_program) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (retval: Z) (PreH1 : (retval = (base_ty_pre - 1024 ))) (PreH2 : (program_pre <> 0)) (PreH3 : (base_ty_pre = (cm_type_encode (base)))) (PreH4 : (cm_i32_code_count base_ty_pre )) (PreH5 : (cm_typed_program policy p )) (PreH6 : (cm_type_code_wf base )) (PreH7 : (cm_member_valid p base mid_pre )) (PreH8 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH9 : (1024 <= base_ty_pre)) (PreH10 : (base_ty_pre <= INT_MAX)) (PreH11 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH12 : (0 <= mid_pre)) ,
  ((( &( "sid" ) )) # Int  |->_)
  **  ((( &( "pointee" ) )) # Int  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "base_ty" ) )) # Int  |-> base_ty_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition cm_member_offset_value_context_entail_wit_1 := 
(
forall (mid_pre: Z) (base_ty_pre: Z) (program_pre: Z) (functions_ptr: Z) (base: cm_type) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (base_ty_pre = (cm_type_encode (base)))) (PreH2 : (cm_i32_code_count base_ty_pre )) (PreH3 : (cm_typed_program policy p )) (PreH4 : (cm_type_code_wf base )) (PreH5 : (cm_member_valid p base mid_pre )) (PreH6 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
|--
  EX (tp: Z)  (gp: Z)  (sp: Z) ,
  “ (program_pre <> 0) ” 
  &&  “ (base_ty_pre = (cm_type_encode (base))) ” 
  &&  “ (cm_i32_code_count base_ty_pre ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_type_code_wf base ) ” 
  &&  “ (cm_member_valid p base mid_pre ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (1024 <= base_ty_pre) ” 
  &&  “ (base_ty_pre <= INT_MAX) ” 
  &&  “ (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 )) ” 
  &&  “ (0 <= mid_pre) ”
  &&  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
) \/
(
forall (mid_pre: Z) (base_ty_pre: Z) (program_pre: Z) (functions_ptr: Z) (base: cm_type) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (base_ty_pre = (cm_type_encode (base)))) (PreH2 : (cm_i32_code_count base_ty_pre )) (PreH3 : (cm_typed_program policy p )) (PreH4 : (cm_type_code_wf base )) (PreH5 : (cm_member_valid p base mid_pre )) (PreH6 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
|--
  EX (tp: Z)  (gp: Z)  (sp: Z) ,
  “ (program_pre <> 0) ” 
  &&  “ (base_ty_pre = (cm_type_encode (base))) ” 
  &&  “ (cm_i32_code_count base_ty_pre ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_type_code_wf base ) ” 
  &&  “ (cm_member_valid p base mid_pre ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (1024 <= base_ty_pre) ” 
  &&  “ (base_ty_pre <= INT_MAX) ” 
  &&  “ (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 )) ” 
  &&  “ (0 <= mid_pre) ”
  &&  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
).

Definition cm_member_offset_value_context_return_wit_1 := 
(
forall (mid_pre: Z) (base_ty_pre: Z) (program_pre: Z) (functions_ptr: Z) (base: cm_type) (p: cm_program) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= ((retval_2 % ( 1024 ) ) - 2 ))) (PreH2 : (0 <= mid_pre)) (PreH3 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH4 : (retval = (cm_rep_struct_member_prefix ((cm_program_structs (p))) (((retval_2 % ( 1024 ) ) - 2 )) (mid_pre)))) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1048576)) (PreH7 : (retval_2 = (base_ty_pre - 1024 ))) (PreH8 : (program_pre <> 0)) (PreH9 : (base_ty_pre = (cm_type_encode (base)))) (PreH10 : (cm_i32_code_count base_ty_pre )) (PreH11 : (cm_typed_program policy p )) (PreH12 : (cm_type_code_wf base )) (PreH13 : (cm_member_valid p base mid_pre )) (PreH14 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH15 : (1024 <= base_ty_pre)) (PreH16 : (base_ty_pre <= INT_MAX)) (PreH17 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH18 : (0 <= mid_pre)) ,
  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
|--
  “ (base_ty_pre = (cm_type_encode (base))) ” 
  &&  “ (cm_i32_code_count base_ty_pre ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_type_code_wf base ) ” 
  &&  “ (cm_member_valid p base mid_pre ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (retval = (cm_member_offset ((cm_program_structs (p))) ((cm_struct_id ((cm_pointee (base))))) (mid_pre))) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
) \/
(
forall (mid_pre: Z) (base_ty_pre: Z) (program_pre: Z) (functions_ptr: Z) (base: cm_type) (p: cm_program) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (retval_2: Z) (retval: Z) (PreH1 : ((cm_program_main (p)) <= INT_MAX)) (PreH2 : ((cm_program_main (p)) >= INT_MIN)) (PreH3 : (0 <= ((retval_2 % ( 1024 ) ) - 2 ))) (PreH4 : (0 <= mid_pre)) (PreH5 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH6 : (retval = (cm_rep_struct_member_prefix ((cm_program_structs (p))) (((retval_2 % ( 1024 ) ) - 2 )) (mid_pre)))) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1048576)) (PreH9 : (retval_2 = (base_ty_pre - 1024 ))) (PreH10 : (program_pre <> 0)) (PreH11 : (base_ty_pre = (cm_type_encode (base)))) (PreH12 : (cm_i32_code_count base_ty_pre )) (PreH13 : (cm_typed_program policy p )) (PreH14 : (cm_type_code_wf base )) (PreH15 : (cm_member_valid p base mid_pre )) (PreH16 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH17 : (1024 <= base_ty_pre)) (PreH18 : (base_ty_pre <= INT_MAX)) (PreH19 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH20 : (0 <= mid_pre)) ,
  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
|--
  “ (retval = (cm_member_offset ((cm_program_structs (p))) ((cm_struct_id ((cm_pointee (base))))) (mid_pre))) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
).

Definition cm_member_offset_value_context_return_wit_1_split_goal_1 := 
forall (mid_pre: Z) (base_ty_pre: Z) (program_pre: Z) (functions_ptr: Z) (base: cm_type) (p: cm_program) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (retval_2: Z) (retval: Z) (PreH1 : ((cm_program_main (p)) <= INT_MAX)) (PreH2 : ((cm_program_main (p)) >= INT_MIN)) (PreH3 : (0 <= ((retval_2 % ( 1024 ) ) - 2 ))) (PreH4 : (0 <= mid_pre)) (PreH5 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH6 : (retval = (cm_rep_struct_member_prefix ((cm_program_structs (p))) (((retval_2 % ( 1024 ) ) - 2 )) (mid_pre)))) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1048576)) (PreH9 : (retval_2 = (base_ty_pre - 1024 ))) (PreH10 : (program_pre <> 0)) (PreH11 : (base_ty_pre = (cm_type_encode (base)))) (PreH12 : (cm_i32_code_count base_ty_pre )) (PreH13 : (cm_typed_program policy p )) (PreH14 : (cm_type_code_wf base )) (PreH15 : (cm_member_valid p base mid_pre )) (PreH16 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH17 : (1024 <= base_ty_pre)) (PreH18 : (base_ty_pre <= INT_MAX)) (PreH19 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH20 : (0 <= mid_pre)) ,
  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
|--
  “ (retval = (cm_member_offset ((cm_program_structs (p))) ((cm_struct_id ((cm_pointee (base))))) (mid_pre))) ”
.

Definition cm_member_offset_value_context_return_wit_1_split_goal_spatial := 
forall (mid_pre: Z) (base_ty_pre: Z) (program_pre: Z) (functions_ptr: Z) (base: cm_type) (p: cm_program) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (retval_2: Z) (retval: Z) (PreH1 : ((cm_program_main (p)) <= INT_MAX)) (PreH2 : ((cm_program_main (p)) >= INT_MIN)) (PreH3 : (0 <= ((retval_2 % ( 1024 ) ) - 2 ))) (PreH4 : (0 <= mid_pre)) (PreH5 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH6 : (retval = (cm_rep_struct_member_prefix ((cm_program_structs (p))) (((retval_2 % ( 1024 ) ) - 2 )) (mid_pre)))) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1048576)) (PreH9 : (retval_2 = (base_ty_pre - 1024 ))) (PreH10 : (program_pre <> 0)) (PreH11 : (base_ty_pre = (cm_type_encode (base)))) (PreH12 : (cm_i32_code_count base_ty_pre )) (PreH13 : (cm_typed_program policy p )) (PreH14 : (cm_type_code_wf base )) (PreH15 : (cm_member_valid p base mid_pre )) (PreH16 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH17 : (1024 <= base_ty_pre)) (PreH18 : (base_ty_pre <= INT_MAX)) (PreH19 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH20 : (0 <= mid_pre)) ,
  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
|--
  (cm_program_context_rep program_pre p functions_ptr )
.

Definition cm_member_offset_value_context_partial_solve_wit_1_pure := 
forall (mid_pre: Z) (base_ty_pre: Z) (program_pre: Z) (functions_ptr: Z) (base: cm_type) (p: cm_program) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (PreH1 : (program_pre <> 0)) (PreH2 : (base_ty_pre = (cm_type_encode (base)))) (PreH3 : (cm_i32_code_count base_ty_pre )) (PreH4 : (cm_typed_program policy p )) (PreH5 : (cm_type_code_wf base )) (PreH6 : (cm_member_valid p base mid_pre )) (PreH7 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH8 : (1024 <= base_ty_pre)) (PreH9 : (base_ty_pre <= INT_MAX)) (PreH10 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH11 : (0 <= mid_pre)) ,
  ((( &( "pointee" ) )) # Int  |->_)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "base_ty" ) )) # Int  |-> base_ty_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
|--
  “ (1024 <= base_ty_pre) ” 
  &&  “ (base_ty_pre <= INT_MAX) ”
.

Definition cm_member_offset_value_context_partial_solve_wit_1_aux := 
forall (mid_pre: Z) (base_ty_pre: Z) (program_pre: Z) (functions_ptr: Z) (base: cm_type) (p: cm_program) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (PreH1 : (program_pre <> 0)) (PreH2 : (base_ty_pre = (cm_type_encode (base)))) (PreH3 : (cm_i32_code_count base_ty_pre )) (PreH4 : (cm_typed_program policy p )) (PreH5 : (cm_type_code_wf base )) (PreH6 : (cm_member_valid p base mid_pre )) (PreH7 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH8 : (1024 <= base_ty_pre)) (PreH9 : (base_ty_pre <= INT_MAX)) (PreH10 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH11 : (0 <= mid_pre)) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
|--
  “ (1024 <= base_ty_pre) ” 
  &&  “ (base_ty_pre <= INT_MAX) ” 
  &&  “ (program_pre <> 0) ” 
  &&  “ (base_ty_pre = (cm_type_encode (base))) ” 
  &&  “ (cm_i32_code_count base_ty_pre ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_type_code_wf base ) ” 
  &&  “ (cm_member_valid p base mid_pre ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (1024 <= base_ty_pre) ” 
  &&  “ (base_ty_pre <= INT_MAX) ” 
  &&  “ (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 )) ” 
  &&  “ (0 <= mid_pre) ”
  &&  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
.

Definition cm_member_offset_value_context_partial_solve_wit_1 := cm_member_offset_value_context_partial_solve_wit_1_pure -> cm_member_offset_value_context_partial_solve_wit_1_aux.

Definition cm_member_offset_value_context_partial_solve_wit_2_pure := 
forall (mid_pre: Z) (base_ty_pre: Z) (program_pre: Z) (functions_ptr: Z) (base: cm_type) (p: cm_program) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (retval: Z) (PreH1 : (retval = (base_ty_pre - 1024 ))) (PreH2 : (program_pre <> 0)) (PreH3 : (base_ty_pre = (cm_type_encode (base)))) (PreH4 : (cm_i32_code_count base_ty_pre )) (PreH5 : (cm_typed_program policy p )) (PreH6 : (cm_type_code_wf base )) (PreH7 : (cm_member_valid p base mid_pre )) (PreH8 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH9 : (1024 <= base_ty_pre)) (PreH10 : (base_ty_pre <= INT_MAX)) (PreH11 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH12 : (0 <= mid_pre)) ,
  ((( &( "result" ) )) # Int64  |->_)
  **  ((( &( "sid" ) )) # Int  |-> ((retval % ( 1024 ) ) - 2 ))
  **  ((( &( "pointee" ) )) # Int  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "base_ty" ) )) # Int  |-> base_ty_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
|--
  “ (0 <= ((retval % ( 1024 ) ) - 2 )) ” 
  &&  “ (0 <= mid_pre) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ”
.

Definition cm_member_offset_value_context_partial_solve_wit_2_aux := 
forall (mid_pre: Z) (base_ty_pre: Z) (program_pre: Z) (functions_ptr: Z) (base: cm_type) (p: cm_program) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (retval: Z) (PreH1 : (retval = (base_ty_pre - 1024 ))) (PreH2 : (program_pre <> 0)) (PreH3 : (base_ty_pre = (cm_type_encode (base)))) (PreH4 : (cm_i32_code_count base_ty_pre )) (PreH5 : (cm_typed_program policy p )) (PreH6 : (cm_type_code_wf base )) (PreH7 : (cm_member_valid p base mid_pre )) (PreH8 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH9 : (1024 <= base_ty_pre)) (PreH10 : (base_ty_pre <= INT_MAX)) (PreH11 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH12 : (0 <= mid_pre)) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
|--
  “ (0 <= ((retval % ( 1024 ) ) - 2 )) ” 
  &&  “ (0 <= mid_pre) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (retval = (base_ty_pre - 1024 )) ” 
  &&  “ (program_pre <> 0) ” 
  &&  “ (base_ty_pre = (cm_type_encode (base))) ” 
  &&  “ (cm_i32_code_count base_ty_pre ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_type_code_wf base ) ” 
  &&  “ (cm_member_valid p base mid_pre ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (1024 <= base_ty_pre) ” 
  &&  “ (base_ty_pre <= INT_MAX) ” 
  &&  “ (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 )) ” 
  &&  “ (0 <= mid_pre) ”
  &&  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
.

Definition cm_member_offset_value_context_partial_solve_wit_2 := cm_member_offset_value_context_partial_solve_wit_2_pure -> cm_member_offset_value_context_partial_solve_wit_2_aux.

Module Type VC_Correct.


Axiom proof_of_cmc_const_immediate_safety_wit_1 : cmc_const_immediate_safety_wit_1.
Axiom proof_of_cmc_const_immediate_safety_wit_2 : cmc_const_immediate_safety_wit_2.
Axiom proof_of_cmc_const_immediate_return_wit_1 : cmc_const_immediate_return_wit_1.
Axiom proof_of_cmc_const_immediate_return_wit_2 : cmc_const_immediate_return_wit_2.
Axiom proof_of_cm_emit_const_expr_safety_wit_1 : cm_emit_const_expr_safety_wit_1.
Axiom proof_of_cm_emit_const_expr_entail_wit_1 : cm_emit_const_expr_entail_wit_1.
Axiom proof_of_cm_emit_const_expr_return_wit_1 : cm_emit_const_expr_return_wit_1.
Axiom proof_of_cm_emit_const_expr_return_wit_2 : cm_emit_const_expr_return_wit_2.
Axiom proof_of_cm_emit_const_expr_partial_solve_wit_1_pure : cm_emit_const_expr_partial_solve_wit_1_pure.
Axiom proof_of_cm_emit_const_expr_partial_solve_wit_1 : cm_emit_const_expr_partial_solve_wit_1.
Axiom proof_of_cm_emit_const_expr_partial_solve_wit_2_pure : cm_emit_const_expr_partial_solve_wit_2_pure.
Axiom proof_of_cm_emit_const_expr_partial_solve_wit_2 : cm_emit_const_expr_partial_solve_wit_2.
Axiom proof_of_cm_emit_const_expr_partial_solve_wit_3_pure : cm_emit_const_expr_partial_solve_wit_3_pure.
Axiom proof_of_cm_emit_const_expr_partial_solve_wit_3 : cm_emit_const_expr_partial_solve_wit_3.
Axiom proof_of_cm_emit_const_expr_which_implies_wit_1 : cm_emit_const_expr_which_implies_wit_1.
Axiom proof_of_cm_emit_string_expr_safety_wit_1 : cm_emit_string_expr_safety_wit_1.
Axiom proof_of_cm_emit_string_expr_entail_wit_1 : cm_emit_string_expr_entail_wit_1.
Axiom proof_of_cm_emit_string_expr_return_wit_1 : cm_emit_string_expr_return_wit_1.
Axiom proof_of_cm_emit_string_expr_return_wit_2 : cm_emit_string_expr_return_wit_2.
Axiom proof_of_cm_emit_string_expr_partial_solve_wit_1 : cm_emit_string_expr_partial_solve_wit_1.
Axiom proof_of_cm_emit_string_expr_partial_solve_wit_2_pure : cm_emit_string_expr_partial_solve_wit_2_pure.
Axiom proof_of_cm_emit_string_expr_partial_solve_wit_2 : cm_emit_string_expr_partial_solve_wit_2.
Axiom proof_of_cm_emit_string_expr_partial_solve_wit_3_pure : cm_emit_string_expr_partial_solve_wit_3_pure.
Axiom proof_of_cm_emit_string_expr_partial_solve_wit_3 : cm_emit_string_expr_partial_solve_wit_3.
Axiom proof_of_cm_emit_string_expr_partial_solve_wit_4_pure : cm_emit_string_expr_partial_solve_wit_4_pure.
Axiom proof_of_cm_emit_string_expr_partial_solve_wit_4 : cm_emit_string_expr_partial_solve_wit_4.
Axiom proof_of_cm_emit_string_expr_which_implies_wit_1 : cm_emit_string_expr_which_implies_wit_1.
Axiom proof_of_cm_emit_string_expr_which_implies_wit_2 : cm_emit_string_expr_which_implies_wit_2.
Axiom proof_of_cm_emit_getc_expr_safety_wit_1 : cm_emit_getc_expr_safety_wit_1.
Axiom proof_of_cm_emit_getc_expr_safety_wit_2 : cm_emit_getc_expr_safety_wit_2.
Axiom proof_of_cm_emit_getc_expr_return_wit_1 : cm_emit_getc_expr_return_wit_1.
Axiom proof_of_cm_emit_getc_expr_return_wit_2 : cm_emit_getc_expr_return_wit_2.
Axiom proof_of_cm_emit_getc_expr_partial_solve_wit_1_pure : cm_emit_getc_expr_partial_solve_wit_1_pure.
Axiom proof_of_cm_emit_getc_expr_partial_solve_wit_1 : cm_emit_getc_expr_partial_solve_wit_1.
Axiom proof_of_cm_emit_getc_expr_partial_solve_wit_2_pure : cm_emit_getc_expr_partial_solve_wit_2_pure.
Axiom proof_of_cm_emit_getc_expr_partial_solve_wit_2 : cm_emit_getc_expr_partial_solve_wit_2.
Axiom proof_of_cm_emit_getc_expr_which_implies_wit_1 : cm_emit_getc_expr_which_implies_wit_1.
Axiom proof_of_cm_sizeof_value_safety_wit_1 : cm_sizeof_value_safety_wit_1.
Axiom proof_of_cm_sizeof_value_safety_wit_2 : cm_sizeof_value_safety_wit_2.
Axiom proof_of_cm_sizeof_value_return_wit_1 : cm_sizeof_value_return_wit_1.
Axiom proof_of_cm_sizeof_value_return_wit_2 : cm_sizeof_value_return_wit_2.
Axiom proof_of_cm_sizeof_value_partial_solve_wit_1_pure : cm_sizeof_value_partial_solve_wit_1_pure.
Axiom proof_of_cm_sizeof_value_partial_solve_wit_1 : cm_sizeof_value_partial_solve_wit_1.
Axiom proof_of_cm_sizeof_value_partial_solve_wit_2 : cm_sizeof_value_partial_solve_wit_2.
Axiom proof_of_cm_sizeof_value_partial_solve_wit_3_pure : cm_sizeof_value_partial_solve_wit_3_pure.
Axiom proof_of_cm_sizeof_value_partial_solve_wit_3 : cm_sizeof_value_partial_solve_wit_3.
Axiom proof_of_cm_sizeof_value_which_implies_wit_1 : cm_sizeof_value_which_implies_wit_1.
Axiom proof_of_cm_sizeof_value_which_implies_wit_2 : cm_sizeof_value_which_implies_wit_2.
Axiom proof_of_cm_type_size_value_return_wit_1 : cm_type_size_value_return_wit_1.
Axiom proof_of_cm_type_size_value_partial_solve_wit_1_pure : cm_type_size_value_partial_solve_wit_1_pure.
Axiom proof_of_cm_type_size_value_partial_solve_wit_1 : cm_type_size_value_partial_solve_wit_1.
Axiom proof_of_cm_emit_sizeof_expr_safety_wit_1 : cm_emit_sizeof_expr_safety_wit_1.
Axiom proof_of_cm_emit_sizeof_expr_entail_wit_1 : cm_emit_sizeof_expr_entail_wit_1.
Axiom proof_of_cm_emit_sizeof_expr_return_wit_1 : cm_emit_sizeof_expr_return_wit_1.
Axiom proof_of_cm_emit_sizeof_expr_return_wit_2 : cm_emit_sizeof_expr_return_wit_2.
Axiom proof_of_cm_emit_sizeof_expr_partial_solve_wit_1_pure : cm_emit_sizeof_expr_partial_solve_wit_1_pure.
Axiom proof_of_cm_emit_sizeof_expr_partial_solve_wit_1 : cm_emit_sizeof_expr_partial_solve_wit_1.
Axiom proof_of_cm_emit_sizeof_expr_partial_solve_wit_2_pure : cm_emit_sizeof_expr_partial_solve_wit_2_pure.
Axiom proof_of_cm_emit_sizeof_expr_partial_solve_wit_2 : cm_emit_sizeof_expr_partial_solve_wit_2.
Axiom proof_of_cm_emit_sizeof_expr_partial_solve_wit_3_pure : cm_emit_sizeof_expr_partial_solve_wit_3_pure.
Axiom proof_of_cm_emit_sizeof_expr_partial_solve_wit_3 : cm_emit_sizeof_expr_partial_solve_wit_3.
Axiom proof_of_cm_emit_sizeof_expr_which_implies_wit_1 : cm_emit_sizeof_expr_which_implies_wit_1.
Axiom proof_of_cm_member_array_value_context_entail_wit_1 : cm_member_array_value_context_entail_wit_1.
Axiom proof_of_cm_member_array_value_context_return_wit_1 : cm_member_array_value_context_return_wit_1.
Axiom proof_of_cm_member_array_value_context_partial_solve_wit_1_pure : cm_member_array_value_context_partial_solve_wit_1_pure.
Axiom proof_of_cm_member_array_value_context_partial_solve_wit_1 : cm_member_array_value_context_partial_solve_wit_1.
Axiom proof_of_cm_member_offset_value_context_safety_wit_1 : cm_member_offset_value_context_safety_wit_1.
Axiom proof_of_cm_member_offset_value_context_safety_wit_2 : cm_member_offset_value_context_safety_wit_2.
Axiom proof_of_cm_member_offset_value_context_safety_wit_3 : cm_member_offset_value_context_safety_wit_3.
Axiom proof_of_cm_member_offset_value_context_safety_wit_4 : cm_member_offset_value_context_safety_wit_4.
Axiom proof_of_cm_member_offset_value_context_entail_wit_1 : cm_member_offset_value_context_entail_wit_1.
Axiom proof_of_cm_member_offset_value_context_return_wit_1 : cm_member_offset_value_context_return_wit_1.
Axiom proof_of_cm_member_offset_value_context_partial_solve_wit_1_pure : cm_member_offset_value_context_partial_solve_wit_1_pure.
Axiom proof_of_cm_member_offset_value_context_partial_solve_wit_1 : cm_member_offset_value_context_partial_solve_wit_1.
Axiom proof_of_cm_member_offset_value_context_partial_solve_wit_2_pure : cm_member_offset_value_context_partial_solve_wit_2_pure.
Axiom proof_of_cm_member_offset_value_context_partial_solve_wit_2 : cm_member_offset_value_context_partial_solve_wit_2.

End VC_Correct.
