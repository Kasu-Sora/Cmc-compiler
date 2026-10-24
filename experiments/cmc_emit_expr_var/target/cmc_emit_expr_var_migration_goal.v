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
Require Import SimpleC.EE.QCP_demos_human.cmc_emit_expr_var_migration_lib.
Local Open Scope sac.

(*----- Function cm_emit_var_expr -----*)

Definition cm_emit_var_expr_safety_wit_1 := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (slot: Z) (scope: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (lvalue_pre = 0)) (PreH2 : (0 <= slot)) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (cm_binding_valid p f scope slot )) (PreH5 : (retval = (cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)))) (PreH6 : (program_pre <> 0)) (PreH7 : (fn_pre <> 0)) (PreH8 : (e = (CMVarE (scope) (slot) (ty)))) (PreH9 : (expr_pre <> 0)) (PreH10 : (0 <= lvalue_pre)) (PreH11 : (lvalue_pre <= 1)) (PreH12 : (e = (CMVarE (scope) (slot) (ty)))) (PreH13 : (cm_wf_program policy cg p )) (PreH14 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH15 : (0 <= slot)) (PreH16 : (slot <= INT_MAX)) (PreH17 : (cm_binding_valid p f scope slot )) (PreH18 : (cm_type_code_wf ty )) (PreH19 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH20 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH21 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH22 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH23 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  (cm_function_context_rep fn_pre f body next )
  **  ((( &( "array" ) )) # Int  |-> retval)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_var_code_for (policy) (p) (fid_pre) (scope) (slot) (ty) (lvalue_pre))) (tail)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_emit_var_expr_return_wit_1 := 
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (slot: Z) (scope: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH3 : (cm_binding_valid p f scope slot )) (PreH4 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH5 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH6 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH7 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH8 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH9 : (lvalue_pre = 0)) (PreH10 : ((cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)) = 0)) (PreH11 : (retval = 0)) (PreH12 : (lvalue_pre = 0)) (PreH13 : (0 <= slot)) (PreH14 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH15 : (cm_binding_valid p f scope slot )) (PreH16 : (retval = (cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)))) (PreH17 : (program_pre <> 0)) (PreH18 : (fn_pre <> 0)) (PreH19 : (e = (CMVarE (scope) (slot) (ty)))) (PreH20 : (expr_pre <> 0)) (PreH21 : (0 <= lvalue_pre)) (PreH22 : (lvalue_pre <= 1)) (PreH23 : (e = (CMVarE (scope) (slot) (ty)))) (PreH24 : (cm_wf_program policy cg p )) (PreH25 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH26 : (0 <= slot)) (PreH27 : (slot <= INT_MAX)) (PreH28 : (cm_binding_valid p f scope slot )) (PreH29 : (cm_type_code_wf ty )) (PreH30 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH31 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH32 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH33 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH34 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app (done) ((cm_binding_address_code (policy) (p) (fid_pre) (scope) (slot))))) ((cm_load_code (ty)))) tail )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
|--
  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (e = (CMVarE (scope) (slot) (ty))) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (0 <= slot) ” 
  &&  “ (slot <= INT_MAX) ” 
  &&  “ (cm_binding_valid p f scope slot ) ” 
  &&  “ (cm_type_code_wf ty ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_var_code_for (policy) (p) (fid_pre) (scope) (slot) (ty) (lvalue_pre)))) tail )
) \/
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (slot: Z) (scope: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (slot <= INT64_MAX)) (PreH2 : (slot >= INT64_MIN)) (PreH3 : ((cm_type_encode (ty)) <= INT_MAX)) (PreH4 : (scope <= INT_MAX)) (PreH5 : (2 <= INT_MAX)) (PreH6 : ((cm_type_encode (ty)) >= INT_MIN)) (PreH7 : (scope >= INT_MIN)) (PreH8 : (2 >= INT_MIN)) (PreH9 : (cm_wf_program policy cg p )) (PreH10 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH11 : (cm_binding_valid p f scope slot )) (PreH12 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH13 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH14 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH15 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH16 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH17 : (lvalue_pre = 0)) (PreH18 : ((cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)) = 0)) (PreH19 : (retval = 0)) (PreH20 : (lvalue_pre = 0)) (PreH21 : (0 <= slot)) (PreH22 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH23 : (cm_binding_valid p f scope slot )) (PreH24 : (retval = (cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)))) (PreH25 : (program_pre <> 0)) (PreH26 : (fn_pre <> 0)) (PreH27 : (e = (CMVarE (scope) (slot) (ty)))) (PreH28 : (expr_pre <> 0)) (PreH29 : (0 <= lvalue_pre)) (PreH30 : (lvalue_pre <= 1)) (PreH31 : (e = (CMVarE (scope) (slot) (ty)))) (PreH32 : (cm_wf_program policy cg p )) (PreH33 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH34 : (0 <= slot)) (PreH35 : (slot <= INT_MAX)) (PreH36 : (cm_binding_valid p f scope slot )) (PreH37 : (cm_type_code_wf ty )) (PreH38 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH39 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH40 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH41 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH42 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app (done) ((cm_binding_address_code (policy) (p) (fid_pre) (scope) (slot))))) ((cm_load_code (ty)))) tail )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_var_code_for (policy) (p) (fid_pre) (scope) (slot) (ty) (lvalue_pre)))) tail )
).

Definition cm_emit_var_expr_return_wit_1_split_goal_spatial := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (slot: Z) (scope: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (slot <= INT64_MAX)) (PreH2 : (slot >= INT64_MIN)) (PreH3 : ((cm_type_encode (ty)) <= INT_MAX)) (PreH4 : (scope <= INT_MAX)) (PreH5 : (2 <= INT_MAX)) (PreH6 : ((cm_type_encode (ty)) >= INT_MIN)) (PreH7 : (scope >= INT_MIN)) (PreH8 : (2 >= INT_MIN)) (PreH9 : (cm_wf_program policy cg p )) (PreH10 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH11 : (cm_binding_valid p f scope slot )) (PreH12 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH13 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH14 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH15 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH16 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH17 : (lvalue_pre = 0)) (PreH18 : ((cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)) = 0)) (PreH19 : (retval = 0)) (PreH20 : (lvalue_pre = 0)) (PreH21 : (0 <= slot)) (PreH22 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH23 : (cm_binding_valid p f scope slot )) (PreH24 : (retval = (cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)))) (PreH25 : (program_pre <> 0)) (PreH26 : (fn_pre <> 0)) (PreH27 : (e = (CMVarE (scope) (slot) (ty)))) (PreH28 : (expr_pre <> 0)) (PreH29 : (0 <= lvalue_pre)) (PreH30 : (lvalue_pre <= 1)) (PreH31 : (e = (CMVarE (scope) (slot) (ty)))) (PreH32 : (cm_wf_program policy cg p )) (PreH33 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH34 : (0 <= slot)) (PreH35 : (slot <= INT_MAX)) (PreH36 : (cm_binding_valid p f scope slot )) (PreH37 : (cm_type_code_wf ty )) (PreH38 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH39 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH40 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH41 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH42 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app (done) ((cm_binding_address_code (policy) (p) (fid_pre) (scope) (slot))))) ((cm_load_code (ty)))) tail )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_var_code_for (policy) (p) (fid_pre) (scope) (slot) (ty) (lvalue_pre)))) tail )
.

Definition cm_emit_var_expr_return_wit_2 := 
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (slot: Z) (scope: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH3 : ((cm_program_structs (p)) = (cm_program_structs (p)))) (PreH4 : ((cm_program_globals (p)) = (cm_program_globals (p)))) (PreH5 : (cm_binding_valid p f scope slot )) (PreH6 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH7 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH8 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH9 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH10 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH11 : (lvalue_pre = 0)) (PreH12 : ((cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)) <> 0)) (PreH13 : (retval <> 0)) (PreH14 : (lvalue_pre = 0)) (PreH15 : (0 <= slot)) (PreH16 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH17 : (cm_binding_valid p f scope slot )) (PreH18 : (retval = (cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)))) (PreH19 : (program_pre <> 0)) (PreH20 : (fn_pre <> 0)) (PreH21 : (e = (CMVarE (scope) (slot) (ty)))) (PreH22 : (expr_pre <> 0)) (PreH23 : (0 <= lvalue_pre)) (PreH24 : (lvalue_pre <= 1)) (PreH25 : (e = (CMVarE (scope) (slot) (ty)))) (PreH26 : (cm_wf_program policy cg p )) (PreH27 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH28 : (0 <= slot)) (PreH29 : (slot <= INT_MAX)) (PreH30 : (cm_binding_valid p f scope slot )) (PreH31 : (cm_type_code_wf ty )) (PreH32 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH33 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH34 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH35 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH36 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_binding_address_code (policy) (p) (fid_pre) (scope) (slot)))) tail )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
|--
  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (e = (CMVarE (scope) (slot) (ty))) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (0 <= slot) ” 
  &&  “ (slot <= INT_MAX) ” 
  &&  “ (cm_binding_valid p f scope slot ) ” 
  &&  “ (cm_type_code_wf ty ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_var_code_for (policy) (p) (fid_pre) (scope) (slot) (ty) (lvalue_pre)))) tail )
) \/
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (slot: Z) (scope: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (slot <= INT64_MAX)) (PreH2 : (slot >= INT64_MIN)) (PreH3 : ((cm_type_encode (ty)) <= INT_MAX)) (PreH4 : (scope <= INT_MAX)) (PreH5 : (2 <= INT_MAX)) (PreH6 : ((cm_type_encode (ty)) >= INT_MIN)) (PreH7 : (scope >= INT_MIN)) (PreH8 : (2 >= INT_MIN)) (PreH9 : (cm_wf_program policy cg p )) (PreH10 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH11 : (cm_binding_valid p f scope slot )) (PreH12 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH13 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH14 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH15 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH16 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH17 : (lvalue_pre = 0)) (PreH18 : ((cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)) <> 0)) (PreH19 : (retval <> 0)) (PreH20 : (lvalue_pre = 0)) (PreH21 : (0 <= slot)) (PreH22 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH23 : (cm_binding_valid p f scope slot )) (PreH24 : (retval = (cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)))) (PreH25 : (program_pre <> 0)) (PreH26 : (fn_pre <> 0)) (PreH27 : (e = (CMVarE (scope) (slot) (ty)))) (PreH28 : (expr_pre <> 0)) (PreH29 : (0 <= lvalue_pre)) (PreH30 : (lvalue_pre <= 1)) (PreH31 : (e = (CMVarE (scope) (slot) (ty)))) (PreH32 : (cm_wf_program policy cg p )) (PreH33 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH34 : (0 <= slot)) (PreH35 : (slot <= INT_MAX)) (PreH36 : (cm_binding_valid p f scope slot )) (PreH37 : (cm_type_code_wf ty )) (PreH38 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH39 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH40 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH41 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH42 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_binding_address_code (policy) (p) (fid_pre) (scope) (slot)))) tail )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_var_code_for (policy) (p) (fid_pre) (scope) (slot) (ty) (lvalue_pre)))) tail )
).

Definition cm_emit_var_expr_return_wit_2_split_goal_spatial := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (slot: Z) (scope: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (slot <= INT64_MAX)) (PreH2 : (slot >= INT64_MIN)) (PreH3 : ((cm_type_encode (ty)) <= INT_MAX)) (PreH4 : (scope <= INT_MAX)) (PreH5 : (2 <= INT_MAX)) (PreH6 : ((cm_type_encode (ty)) >= INT_MIN)) (PreH7 : (scope >= INT_MIN)) (PreH8 : (2 >= INT_MIN)) (PreH9 : (cm_wf_program policy cg p )) (PreH10 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH11 : (cm_binding_valid p f scope slot )) (PreH12 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH13 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH14 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH15 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH16 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH17 : (lvalue_pre = 0)) (PreH18 : ((cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)) <> 0)) (PreH19 : (retval <> 0)) (PreH20 : (lvalue_pre = 0)) (PreH21 : (0 <= slot)) (PreH22 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH23 : (cm_binding_valid p f scope slot )) (PreH24 : (retval = (cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)))) (PreH25 : (program_pre <> 0)) (PreH26 : (fn_pre <> 0)) (PreH27 : (e = (CMVarE (scope) (slot) (ty)))) (PreH28 : (expr_pre <> 0)) (PreH29 : (0 <= lvalue_pre)) (PreH30 : (lvalue_pre <= 1)) (PreH31 : (e = (CMVarE (scope) (slot) (ty)))) (PreH32 : (cm_wf_program policy cg p )) (PreH33 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH34 : (0 <= slot)) (PreH35 : (slot <= INT_MAX)) (PreH36 : (cm_binding_valid p f scope slot )) (PreH37 : (cm_type_code_wf ty )) (PreH38 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH39 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH40 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH41 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH42 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_binding_address_code (policy) (p) (fid_pre) (scope) (slot)))) tail )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_var_code_for (policy) (p) (fid_pre) (scope) (slot) (ty) (lvalue_pre)))) tail )
.

Definition cm_emit_var_expr_return_wit_3 := 
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (slot: Z) (scope: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH3 : ((cm_program_structs (p)) = (cm_program_structs (p)))) (PreH4 : ((cm_program_globals (p)) = (cm_program_globals (p)))) (PreH5 : (cm_binding_valid p f scope slot )) (PreH6 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH7 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH8 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH9 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH10 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH11 : (lvalue_pre <> 0)) (PreH12 : (lvalue_pre <> 0)) (PreH13 : (0 <= slot)) (PreH14 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH15 : (cm_binding_valid p f scope slot )) (PreH16 : (retval = (cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)))) (PreH17 : (program_pre <> 0)) (PreH18 : (fn_pre <> 0)) (PreH19 : (e = (CMVarE (scope) (slot) (ty)))) (PreH20 : (expr_pre <> 0)) (PreH21 : (0 <= lvalue_pre)) (PreH22 : (lvalue_pre <= 1)) (PreH23 : (e = (CMVarE (scope) (slot) (ty)))) (PreH24 : (cm_wf_program policy cg p )) (PreH25 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH26 : (0 <= slot)) (PreH27 : (slot <= INT_MAX)) (PreH28 : (cm_binding_valid p f scope slot )) (PreH29 : (cm_type_code_wf ty )) (PreH30 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH31 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH32 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH33 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH34 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_binding_address_code (policy) (p) (fid_pre) (scope) (slot)))) tail )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
|--
  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (e = (CMVarE (scope) (slot) (ty))) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (0 <= slot) ” 
  &&  “ (slot <= INT_MAX) ” 
  &&  “ (cm_binding_valid p f scope slot ) ” 
  &&  “ (cm_type_code_wf ty ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_var_code_for (policy) (p) (fid_pre) (scope) (slot) (ty) (lvalue_pre)))) tail )
) \/
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (slot: Z) (scope: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (slot <= INT64_MAX)) (PreH2 : (slot >= INT64_MIN)) (PreH3 : ((cm_type_encode (ty)) <= INT_MAX)) (PreH4 : (scope <= INT_MAX)) (PreH5 : (2 <= INT_MAX)) (PreH6 : ((cm_type_encode (ty)) >= INT_MIN)) (PreH7 : (scope >= INT_MIN)) (PreH8 : (2 >= INT_MIN)) (PreH9 : (cm_wf_program policy cg p )) (PreH10 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH11 : (cm_binding_valid p f scope slot )) (PreH12 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH13 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH14 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH15 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH16 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH17 : (lvalue_pre <> 0)) (PreH18 : (lvalue_pre <> 0)) (PreH19 : (0 <= slot)) (PreH20 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH21 : (cm_binding_valid p f scope slot )) (PreH22 : (retval = (cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)))) (PreH23 : (program_pre <> 0)) (PreH24 : (fn_pre <> 0)) (PreH25 : (e = (CMVarE (scope) (slot) (ty)))) (PreH26 : (expr_pre <> 0)) (PreH27 : (0 <= lvalue_pre)) (PreH28 : (lvalue_pre <= 1)) (PreH29 : (e = (CMVarE (scope) (slot) (ty)))) (PreH30 : (cm_wf_program policy cg p )) (PreH31 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH32 : (0 <= slot)) (PreH33 : (slot <= INT_MAX)) (PreH34 : (cm_binding_valid p f scope slot )) (PreH35 : (cm_type_code_wf ty )) (PreH36 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH37 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH38 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH39 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH40 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_binding_address_code (policy) (p) (fid_pre) (scope) (slot)))) tail )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_var_code_for (policy) (p) (fid_pre) (scope) (slot) (ty) (lvalue_pre)))) tail )
).

Definition cm_emit_var_expr_return_wit_3_split_goal_spatial := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (slot: Z) (scope: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (slot <= INT64_MAX)) (PreH2 : (slot >= INT64_MIN)) (PreH3 : ((cm_type_encode (ty)) <= INT_MAX)) (PreH4 : (scope <= INT_MAX)) (PreH5 : (2 <= INT_MAX)) (PreH6 : ((cm_type_encode (ty)) >= INT_MIN)) (PreH7 : (scope >= INT_MIN)) (PreH8 : (2 >= INT_MIN)) (PreH9 : (cm_wf_program policy cg p )) (PreH10 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH11 : (cm_binding_valid p f scope slot )) (PreH12 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH13 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH14 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH15 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH16 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH17 : (lvalue_pre <> 0)) (PreH18 : (lvalue_pre <> 0)) (PreH19 : (0 <= slot)) (PreH20 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH21 : (cm_binding_valid p f scope slot )) (PreH22 : (retval = (cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)))) (PreH23 : (program_pre <> 0)) (PreH24 : (fn_pre <> 0)) (PreH25 : (e = (CMVarE (scope) (slot) (ty)))) (PreH26 : (expr_pre <> 0)) (PreH27 : (0 <= lvalue_pre)) (PreH28 : (lvalue_pre <= 1)) (PreH29 : (e = (CMVarE (scope) (slot) (ty)))) (PreH30 : (cm_wf_program policy cg p )) (PreH31 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH32 : (0 <= slot)) (PreH33 : (slot <= INT_MAX)) (PreH34 : (cm_binding_valid p f scope slot )) (PreH35 : (cm_type_code_wf ty )) (PreH36 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH37 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH38 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH39 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH40 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_binding_address_code (policy) (p) (fid_pre) (scope) (slot)))) tail )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_var_code_for (policy) (p) (fid_pre) (scope) (slot) (ty) (lvalue_pre)))) tail )
.

Definition cm_emit_var_expr_partial_solve_wit_1_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (slot: Z) (scope: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (0 <= lvalue_pre)) (PreH2 : (lvalue_pre <= 1)) (PreH3 : (e = (CMVarE (scope) (slot) (ty)))) (PreH4 : (cm_wf_program policy cg p )) (PreH5 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH6 : (0 <= slot)) (PreH7 : (slot <= INT_MAX)) (PreH8 : (cm_binding_valid p f scope slot )) (PreH9 : (cm_type_code_wf ty )) (PreH10 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH11 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH12 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH13 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH14 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
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
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_var_code_for (policy) (p) (fid_pre) (scope) (slot) (ty) (lvalue_pre))) (tail)) )
|--
  “ (e = (CMVarE (scope) (slot) (ty))) ”
.

Definition cm_emit_var_expr_partial_solve_wit_1_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (slot: Z) (scope: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (0 <= lvalue_pre)) (PreH2 : (lvalue_pre <= 1)) (PreH3 : (e = (CMVarE (scope) (slot) (ty)))) (PreH4 : (cm_wf_program policy cg p )) (PreH5 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH6 : (0 <= slot)) (PreH7 : (slot <= INT_MAX)) (PreH8 : (cm_binding_valid p f scope slot )) (PreH9 : (cm_type_code_wf ty )) (PreH10 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH11 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH12 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH13 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH14 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_var_code_for (policy) (p) (fid_pre) (scope) (slot) (ty) (lvalue_pre))) (tail)) )
|--
  “ (e = (CMVarE (scope) (slot) (ty))) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (e = (CMVarE (scope) (slot) (ty))) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (0 <= slot) ” 
  &&  “ (slot <= INT_MAX) ” 
  &&  “ (cm_binding_valid p f scope slot ) ” 
  &&  “ (cm_type_code_wf ty ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ”
  &&  (cm_expr_rep expr_pre e )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_var_code_for (policy) (p) (fid_pre) (scope) (slot) (ty) (lvalue_pre))) (tail)) )
.

Definition cm_emit_var_expr_partial_solve_wit_1 := cm_emit_var_expr_partial_solve_wit_1_pure -> cm_emit_var_expr_partial_solve_wit_1_aux.

Definition cm_emit_var_expr_partial_solve_wit_2 := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (slot: Z) (scope: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (e = (CMVarE (scope) (slot) (ty)))) (PreH2 : (expr_pre <> 0)) (PreH3 : (0 <= lvalue_pre)) (PreH4 : (lvalue_pre <= 1)) (PreH5 : (e = (CMVarE (scope) (slot) (ty)))) (PreH6 : (cm_wf_program policy cg p )) (PreH7 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH8 : (0 <= slot)) (PreH9 : (slot <= INT_MAX)) (PreH10 : (cm_binding_valid p f scope slot )) (PreH11 : (cm_type_code_wf ty )) (PreH12 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH13 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH14 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH15 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH16 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_var_code_for (policy) (p) (fid_pre) (scope) (slot) (ty) (lvalue_pre))) (tail)) )
|--
  “ (e = (CMVarE (scope) (slot) (ty))) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (e = (CMVarE (scope) (slot) (ty))) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (0 <= slot) ” 
  &&  “ (slot <= INT_MAX) ” 
  &&  “ (cm_binding_valid p f scope slot ) ” 
  &&  “ (cm_type_code_wf ty ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_var_code_for (policy) (p) (fid_pre) (scope) (slot) (ty) (lvalue_pre))) (tail)) )
.

Definition cm_emit_var_expr_partial_solve_wit_3_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (slot: Z) (scope: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (lp: Z) (pp: Z) (tp: Z) (gp: Z) (sp: Z) (PreH1 : (program_pre <> 0)) (PreH2 : (fn_pre <> 0)) (PreH3 : (e = (CMVarE (scope) (slot) (ty)))) (PreH4 : (expr_pre <> 0)) (PreH5 : (0 <= lvalue_pre)) (PreH6 : (lvalue_pre <= 1)) (PreH7 : (e = (CMVarE (scope) (slot) (ty)))) (PreH8 : (cm_wf_program policy cg p )) (PreH9 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH10 : (0 <= slot)) (PreH11 : (slot <= INT_MAX)) (PreH12 : (cm_binding_valid p f scope slot )) (PreH13 : (cm_type_code_wf ty )) (PreH14 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH15 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH16 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH17 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH18 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  ((( &( "array" ) )) # Int  |->_)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_var_code_for (policy) (p) (fid_pre) (scope) (slot) (ty) (lvalue_pre))) (tail)) )
|--
  “ (0 <= slot) ” 
  &&  “ ((cm_program_globals (p)) = (cm_program_globals (p))) ” 
  &&  “ ((cm_function_locals (f)) = (cm_function_locals (f))) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_binding_valid p f scope slot ) ”
.

Definition cm_emit_var_expr_partial_solve_wit_3_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (slot: Z) (scope: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (lp: Z) (pp: Z) (tp: Z) (gp: Z) (sp: Z) (PreH1 : (program_pre <> 0)) (PreH2 : (fn_pre <> 0)) (PreH3 : (e = (CMVarE (scope) (slot) (ty)))) (PreH4 : (expr_pre <> 0)) (PreH5 : (0 <= lvalue_pre)) (PreH6 : (lvalue_pre <= 1)) (PreH7 : (e = (CMVarE (scope) (slot) (ty)))) (PreH8 : (cm_wf_program policy cg p )) (PreH9 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH10 : (0 <= slot)) (PreH11 : (slot <= INT_MAX)) (PreH12 : (cm_binding_valid p f scope slot )) (PreH13 : (cm_type_code_wf ty )) (PreH14 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH15 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH16 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH17 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH18 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_var_code_for (policy) (p) (fid_pre) (scope) (slot) (ty) (lvalue_pre))) (tail)) )
|--
  “ (0 <= slot) ” 
  &&  “ ((cm_program_globals (p)) = (cm_program_globals (p))) ” 
  &&  “ ((cm_function_locals (f)) = (cm_function_locals (f))) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_binding_valid p f scope slot ) ” 
  &&  “ (program_pre <> 0) ” 
  &&  “ (fn_pre <> 0) ” 
  &&  “ (e = (CMVarE (scope) (slot) (ty))) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (e = (CMVarE (scope) (slot) (ty))) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (0 <= slot) ” 
  &&  “ (slot <= INT_MAX) ” 
  &&  “ (cm_binding_valid p f scope slot ) ” 
  &&  “ (cm_type_code_wf ty ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ”
  &&  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_var_code_for (policy) (p) (fid_pre) (scope) (slot) (ty) (lvalue_pre))) (tail)) )
.

Definition cm_emit_var_expr_partial_solve_wit_3 := cm_emit_var_expr_partial_solve_wit_3_pure -> cm_emit_var_expr_partial_solve_wit_3_aux.

Definition cm_emit_var_expr_partial_solve_wit_4_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (slot: Z) (scope: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (lp: Z) (pp: Z) (tp: Z) (gp: Z) (sp: Z) (retval: Z) (PreH1 : (0 <= slot)) (PreH2 : ((cm_program_globals (p)) = (cm_program_globals (p)))) (PreH3 : ((cm_function_locals (f)) = (cm_function_locals (f)))) (PreH4 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH5 : (cm_binding_valid p f scope slot )) (PreH6 : (retval = (cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)))) (PreH7 : (program_pre <> 0)) (PreH8 : (fn_pre <> 0)) (PreH9 : (e = (CMVarE (scope) (slot) (ty)))) (PreH10 : (expr_pre <> 0)) (PreH11 : (0 <= lvalue_pre)) (PreH12 : (lvalue_pre <= 1)) (PreH13 : (e = (CMVarE (scope) (slot) (ty)))) (PreH14 : (cm_wf_program policy cg p )) (PreH15 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH16 : (0 <= slot)) (PreH17 : (slot <= INT_MAX)) (PreH18 : (cm_binding_valid p f scope slot )) (PreH19 : (cm_type_code_wf ty )) (PreH20 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH21 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH22 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH23 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH24 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  ((( &( "array" ) )) # Int  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_var_code_for (policy) (p) (fid_pre) (scope) (slot) (ty) (lvalue_pre))) (tail)) )
|--
  “ (program_pre <> 0) ” 
  &&  “ (fn_pre <> 0) ”
.

Definition cm_emit_var_expr_partial_solve_wit_4_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (slot: Z) (scope: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (lp: Z) (pp: Z) (tp: Z) (gp: Z) (sp: Z) (retval: Z) (PreH1 : (0 <= slot)) (PreH2 : ((cm_program_globals (p)) = (cm_program_globals (p)))) (PreH3 : ((cm_function_locals (f)) = (cm_function_locals (f)))) (PreH4 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH5 : (cm_binding_valid p f scope slot )) (PreH6 : (retval = (cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)))) (PreH7 : (program_pre <> 0)) (PreH8 : (fn_pre <> 0)) (PreH9 : (e = (CMVarE (scope) (slot) (ty)))) (PreH10 : (expr_pre <> 0)) (PreH11 : (0 <= lvalue_pre)) (PreH12 : (lvalue_pre <= 1)) (PreH13 : (e = (CMVarE (scope) (slot) (ty)))) (PreH14 : (cm_wf_program policy cg p )) (PreH15 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH16 : (0 <= slot)) (PreH17 : (slot <= INT_MAX)) (PreH18 : (cm_binding_valid p f scope slot )) (PreH19 : (cm_type_code_wf ty )) (PreH20 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH21 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH22 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH23 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH24 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_var_code_for (policy) (p) (fid_pre) (scope) (slot) (ty) (lvalue_pre))) (tail)) )
|--
  “ (program_pre <> 0) ” 
  &&  “ (fn_pre <> 0) ” 
  &&  “ (0 <= slot) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_binding_valid p f scope slot ) ” 
  &&  “ (retval = (cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot))) ” 
  &&  “ (program_pre <> 0) ” 
  &&  “ (fn_pre <> 0) ” 
  &&  “ (e = (CMVarE (scope) (slot) (ty))) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (e = (CMVarE (scope) (slot) (ty))) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (0 <= slot) ” 
  &&  “ (slot <= INT_MAX) ” 
  &&  “ (cm_binding_valid p f scope slot ) ” 
  &&  “ (cm_type_code_wf ty ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ”
  &&  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_var_code_for (policy) (p) (fid_pre) (scope) (slot) (ty) (lvalue_pre))) (tail)) )
.

Definition cm_emit_var_expr_partial_solve_wit_4 := cm_emit_var_expr_partial_solve_wit_4_pure -> cm_emit_var_expr_partial_solve_wit_4_aux.

Definition cm_emit_var_expr_partial_solve_wit_5_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (slot: Z) (scope: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (lvalue_pre = 0)) (PreH3 : (0 <= slot)) (PreH4 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH5 : (cm_binding_valid p f scope slot )) (PreH6 : (retval = (cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)))) (PreH7 : (program_pre <> 0)) (PreH8 : (fn_pre <> 0)) (PreH9 : (e = (CMVarE (scope) (slot) (ty)))) (PreH10 : (expr_pre <> 0)) (PreH11 : (0 <= lvalue_pre)) (PreH12 : (lvalue_pre <= 1)) (PreH13 : (e = (CMVarE (scope) (slot) (ty)))) (PreH14 : (cm_wf_program policy cg p )) (PreH15 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH16 : (0 <= slot)) (PreH17 : (slot <= INT_MAX)) (PreH18 : (cm_binding_valid p f scope slot )) (PreH19 : (cm_type_code_wf ty )) (PreH20 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH21 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH22 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH23 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH24 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  (cm_function_context_rep fn_pre f body next )
  **  ((( &( "array" ) )) # Int  |-> retval)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_var_code_for (policy) (p) (fid_pre) (scope) (slot) (ty) (lvalue_pre))) (tail)) )
|--
  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 0) ” 
  &&  “ ((cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)) = 0) ”
.

Definition cm_emit_var_expr_partial_solve_wit_5_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (slot: Z) (scope: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (lvalue_pre = 0)) (PreH3 : (0 <= slot)) (PreH4 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH5 : (cm_binding_valid p f scope slot )) (PreH6 : (retval = (cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)))) (PreH7 : (program_pre <> 0)) (PreH8 : (fn_pre <> 0)) (PreH9 : (e = (CMVarE (scope) (slot) (ty)))) (PreH10 : (expr_pre <> 0)) (PreH11 : (0 <= lvalue_pre)) (PreH12 : (lvalue_pre <= 1)) (PreH13 : (e = (CMVarE (scope) (slot) (ty)))) (PreH14 : (cm_wf_program policy cg p )) (PreH15 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH16 : (0 <= slot)) (PreH17 : (slot <= INT_MAX)) (PreH18 : (cm_binding_valid p f scope slot )) (PreH19 : (cm_type_code_wf ty )) (PreH20 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH21 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH22 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH23 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH24 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_var_code_for (policy) (p) (fid_pre) (scope) (slot) (ty) (lvalue_pre))) (tail)) )
|--
  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 0) ” 
  &&  “ ((cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)) = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (lvalue_pre = 0) ” 
  &&  “ (0 <= slot) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_binding_valid p f scope slot ) ” 
  &&  “ (retval = (cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot))) ” 
  &&  “ (program_pre <> 0) ” 
  &&  “ (fn_pre <> 0) ” 
  &&  “ (e = (CMVarE (scope) (slot) (ty))) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (e = (CMVarE (scope) (slot) (ty))) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (0 <= slot) ” 
  &&  “ (slot <= INT_MAX) ” 
  &&  “ (cm_binding_valid p f scope slot ) ” 
  &&  “ (cm_type_code_wf ty ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_var_code_for (policy) (p) (fid_pre) (scope) (slot) (ty) (lvalue_pre))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
.

Definition cm_emit_var_expr_partial_solve_wit_5 := cm_emit_var_expr_partial_solve_wit_5_pure -> cm_emit_var_expr_partial_solve_wit_5_aux.

Definition cm_emit_var_expr_partial_solve_wit_6_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (slot: Z) (scope: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (lvalue_pre = 0)) (PreH2 : ((cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)) = 0)) (PreH3 : (retval = 0)) (PreH4 : (lvalue_pre = 0)) (PreH5 : (0 <= slot)) (PreH6 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH7 : (cm_binding_valid p f scope slot )) (PreH8 : (retval = (cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)))) (PreH9 : (program_pre <> 0)) (PreH10 : (fn_pre <> 0)) (PreH11 : (e = (CMVarE (scope) (slot) (ty)))) (PreH12 : (expr_pre <> 0)) (PreH13 : (0 <= lvalue_pre)) (PreH14 : (lvalue_pre <= 1)) (PreH15 : (e = (CMVarE (scope) (slot) (ty)))) (PreH16 : (cm_wf_program policy cg p )) (PreH17 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH18 : (0 <= slot)) (PreH19 : (slot <= INT_MAX)) (PreH20 : (cm_binding_valid p f scope slot )) (PreH21 : (cm_type_code_wf ty )) (PreH22 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH23 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH24 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH25 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH26 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_binding_address_code (policy) (p) (fid_pre) (scope) (slot))) ((app ((cm_load_code (ty))) (tail)))) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  (cm_function_context_rep fn_pre f body next )
  **  ((( &( "array" ) )) # Int  |-> retval)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ ((cm_program_structs (p)) = (cm_program_structs (p))) ” 
  &&  “ ((cm_program_globals (p)) = (cm_program_globals (p))) ” 
  &&  “ (cm_binding_valid p f scope slot ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ”
.

Definition cm_emit_var_expr_partial_solve_wit_6_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (slot: Z) (scope: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (lvalue_pre = 0)) (PreH2 : ((cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)) = 0)) (PreH3 : (retval = 0)) (PreH4 : (lvalue_pre = 0)) (PreH5 : (0 <= slot)) (PreH6 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH7 : (cm_binding_valid p f scope slot )) (PreH8 : (retval = (cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)))) (PreH9 : (program_pre <> 0)) (PreH10 : (fn_pre <> 0)) (PreH11 : (e = (CMVarE (scope) (slot) (ty)))) (PreH12 : (expr_pre <> 0)) (PreH13 : (0 <= lvalue_pre)) (PreH14 : (lvalue_pre <= 1)) (PreH15 : (e = (CMVarE (scope) (slot) (ty)))) (PreH16 : (cm_wf_program policy cg p )) (PreH17 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH18 : (0 <= slot)) (PreH19 : (slot <= INT_MAX)) (PreH20 : (cm_binding_valid p f scope slot )) (PreH21 : (cm_type_code_wf ty )) (PreH22 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH23 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH24 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH25 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH26 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_binding_address_code (policy) (p) (fid_pre) (scope) (slot))) ((app ((cm_load_code (ty))) (tail)))) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ ((cm_program_structs (p)) = (cm_program_structs (p))) ” 
  &&  “ ((cm_program_globals (p)) = (cm_program_globals (p))) ” 
  &&  “ (cm_binding_valid p f scope slot ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (lvalue_pre = 0) ” 
  &&  “ ((cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)) = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (lvalue_pre = 0) ” 
  &&  “ (0 <= slot) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_binding_valid p f scope slot ) ” 
  &&  “ (retval = (cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot))) ” 
  &&  “ (program_pre <> 0) ” 
  &&  “ (fn_pre <> 0) ” 
  &&  “ (e = (CMVarE (scope) (slot) (ty))) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (e = (CMVarE (scope) (slot) (ty))) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (0 <= slot) ” 
  &&  “ (slot <= INT_MAX) ” 
  &&  “ (cm_binding_valid p f scope slot ) ” 
  &&  “ (cm_type_code_wf ty ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_binding_address_code (policy) (p) (fid_pre) (scope) (slot))) ((app ((cm_load_code (ty))) (tail)))) )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
.

Definition cm_emit_var_expr_partial_solve_wit_6 := cm_emit_var_expr_partial_solve_wit_6_pure -> cm_emit_var_expr_partial_solve_wit_6_aux.

Definition cm_emit_var_expr_partial_solve_wit_7_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (slot: Z) (scope: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH3 : ((cm_program_structs (p)) = (cm_program_structs (p)))) (PreH4 : ((cm_program_globals (p)) = (cm_program_globals (p)))) (PreH5 : (cm_binding_valid p f scope slot )) (PreH6 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH7 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH8 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH9 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH10 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH11 : (lvalue_pre = 0)) (PreH12 : ((cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)) = 0)) (PreH13 : (retval = 0)) (PreH14 : (lvalue_pre = 0)) (PreH15 : (0 <= slot)) (PreH16 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH17 : (cm_binding_valid p f scope slot )) (PreH18 : (retval = (cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)))) (PreH19 : (program_pre <> 0)) (PreH20 : (fn_pre <> 0)) (PreH21 : (e = (CMVarE (scope) (slot) (ty)))) (PreH22 : (expr_pre <> 0)) (PreH23 : (0 <= lvalue_pre)) (PreH24 : (lvalue_pre <= 1)) (PreH25 : (e = (CMVarE (scope) (slot) (ty)))) (PreH26 : (cm_wf_program policy cg p )) (PreH27 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH28 : (0 <= slot)) (PreH29 : (slot <= INT_MAX)) (PreH30 : (cm_binding_valid p f scope slot )) (PreH31 : (cm_type_code_wf ty )) (PreH32 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH33 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH34 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH35 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH36 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_binding_address_code (policy) (p) (fid_pre) (scope) (slot)))) (app ((cm_load_code (ty))) (tail)) )
  **  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "array" ) )) # Int  |-> retval)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
|--
  “ ((cm_type_encode (ty)) = (cm_type_encode (ty))) ” 
  &&  “ (cm_type_code_wf ty ) ”
.

Definition cm_emit_var_expr_partial_solve_wit_7_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (slot: Z) (scope: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH3 : ((cm_program_structs (p)) = (cm_program_structs (p)))) (PreH4 : ((cm_program_globals (p)) = (cm_program_globals (p)))) (PreH5 : (cm_binding_valid p f scope slot )) (PreH6 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH7 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH8 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH9 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH10 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH11 : (lvalue_pre = 0)) (PreH12 : ((cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)) = 0)) (PreH13 : (retval = 0)) (PreH14 : (lvalue_pre = 0)) (PreH15 : (0 <= slot)) (PreH16 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH17 : (cm_binding_valid p f scope slot )) (PreH18 : (retval = (cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)))) (PreH19 : (program_pre <> 0)) (PreH20 : (fn_pre <> 0)) (PreH21 : (e = (CMVarE (scope) (slot) (ty)))) (PreH22 : (expr_pre <> 0)) (PreH23 : (0 <= lvalue_pre)) (PreH24 : (lvalue_pre <= 1)) (PreH25 : (e = (CMVarE (scope) (slot) (ty)))) (PreH26 : (cm_wf_program policy cg p )) (PreH27 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH28 : (0 <= slot)) (PreH29 : (slot <= INT_MAX)) (PreH30 : (cm_binding_valid p f scope slot )) (PreH31 : (cm_type_code_wf ty )) (PreH32 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH33 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH34 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH35 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH36 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_binding_address_code (policy) (p) (fid_pre) (scope) (slot)))) (app ((cm_load_code (ty))) (tail)) )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
|--
  “ ((cm_type_encode (ty)) = (cm_type_encode (ty))) ” 
  &&  “ (cm_type_code_wf ty ) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_binding_valid p f scope slot ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (lvalue_pre = 0) ” 
  &&  “ ((cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)) = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (lvalue_pre = 0) ” 
  &&  “ (0 <= slot) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_binding_valid p f scope slot ) ” 
  &&  “ (retval = (cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot))) ” 
  &&  “ (program_pre <> 0) ” 
  &&  “ (fn_pre <> 0) ” 
  &&  “ (e = (CMVarE (scope) (slot) (ty))) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (e = (CMVarE (scope) (slot) (ty))) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (0 <= slot) ” 
  &&  “ (slot <= INT_MAX) ” 
  &&  “ (cm_binding_valid p f scope slot ) ” 
  &&  “ (cm_type_code_wf ty ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_binding_address_code (policy) (p) (fid_pre) (scope) (slot)))) (app ((cm_load_code (ty))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
.

Definition cm_emit_var_expr_partial_solve_wit_7 := cm_emit_var_expr_partial_solve_wit_7_pure -> cm_emit_var_expr_partial_solve_wit_7_aux.

Definition cm_emit_var_expr_partial_solve_wit_8_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (slot: Z) (scope: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (lvalue_pre = 0)) (PreH3 : (0 <= slot)) (PreH4 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH5 : (cm_binding_valid p f scope slot )) (PreH6 : (retval = (cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)))) (PreH7 : (program_pre <> 0)) (PreH8 : (fn_pre <> 0)) (PreH9 : (e = (CMVarE (scope) (slot) (ty)))) (PreH10 : (expr_pre <> 0)) (PreH11 : (0 <= lvalue_pre)) (PreH12 : (lvalue_pre <= 1)) (PreH13 : (e = (CMVarE (scope) (slot) (ty)))) (PreH14 : (cm_wf_program policy cg p )) (PreH15 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH16 : (0 <= slot)) (PreH17 : (slot <= INT_MAX)) (PreH18 : (cm_binding_valid p f scope slot )) (PreH19 : (cm_type_code_wf ty )) (PreH20 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH21 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH22 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH23 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH24 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  (cm_function_context_rep fn_pre f body next )
  **  ((( &( "array" ) )) # Int  |-> retval)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_var_code_for (policy) (p) (fid_pre) (scope) (slot) (ty) (lvalue_pre))) (tail)) )
|--
  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 0) ” 
  &&  “ ((cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)) <> 0) ”
.

Definition cm_emit_var_expr_partial_solve_wit_8_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (slot: Z) (scope: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (lvalue_pre = 0)) (PreH3 : (0 <= slot)) (PreH4 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH5 : (cm_binding_valid p f scope slot )) (PreH6 : (retval = (cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)))) (PreH7 : (program_pre <> 0)) (PreH8 : (fn_pre <> 0)) (PreH9 : (e = (CMVarE (scope) (slot) (ty)))) (PreH10 : (expr_pre <> 0)) (PreH11 : (0 <= lvalue_pre)) (PreH12 : (lvalue_pre <= 1)) (PreH13 : (e = (CMVarE (scope) (slot) (ty)))) (PreH14 : (cm_wf_program policy cg p )) (PreH15 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH16 : (0 <= slot)) (PreH17 : (slot <= INT_MAX)) (PreH18 : (cm_binding_valid p f scope slot )) (PreH19 : (cm_type_code_wf ty )) (PreH20 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH21 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH22 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH23 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH24 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_var_code_for (policy) (p) (fid_pre) (scope) (slot) (ty) (lvalue_pre))) (tail)) )
|--
  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 0) ” 
  &&  “ ((cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)) <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (lvalue_pre = 0) ” 
  &&  “ (0 <= slot) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_binding_valid p f scope slot ) ” 
  &&  “ (retval = (cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot))) ” 
  &&  “ (program_pre <> 0) ” 
  &&  “ (fn_pre <> 0) ” 
  &&  “ (e = (CMVarE (scope) (slot) (ty))) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (e = (CMVarE (scope) (slot) (ty))) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (0 <= slot) ” 
  &&  “ (slot <= INT_MAX) ” 
  &&  “ (cm_binding_valid p f scope slot ) ” 
  &&  “ (cm_type_code_wf ty ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_var_code_for (policy) (p) (fid_pre) (scope) (slot) (ty) (lvalue_pre))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
.

Definition cm_emit_var_expr_partial_solve_wit_8 := cm_emit_var_expr_partial_solve_wit_8_pure -> cm_emit_var_expr_partial_solve_wit_8_aux.

Definition cm_emit_var_expr_partial_solve_wit_9_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (slot: Z) (scope: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (lvalue_pre = 0)) (PreH2 : ((cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)) <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (lvalue_pre = 0)) (PreH5 : (0 <= slot)) (PreH6 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH7 : (cm_binding_valid p f scope slot )) (PreH8 : (retval = (cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)))) (PreH9 : (program_pre <> 0)) (PreH10 : (fn_pre <> 0)) (PreH11 : (e = (CMVarE (scope) (slot) (ty)))) (PreH12 : (expr_pre <> 0)) (PreH13 : (0 <= lvalue_pre)) (PreH14 : (lvalue_pre <= 1)) (PreH15 : (e = (CMVarE (scope) (slot) (ty)))) (PreH16 : (cm_wf_program policy cg p )) (PreH17 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH18 : (0 <= slot)) (PreH19 : (slot <= INT_MAX)) (PreH20 : (cm_binding_valid p f scope slot )) (PreH21 : (cm_type_code_wf ty )) (PreH22 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH23 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH24 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH25 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH26 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_binding_address_code (policy) (p) (fid_pre) (scope) (slot))) (tail)) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  (cm_function_context_rep fn_pre f body next )
  **  ((( &( "array" ) )) # Int  |-> retval)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ ((cm_program_structs (p)) = (cm_program_structs (p))) ” 
  &&  “ ((cm_program_globals (p)) = (cm_program_globals (p))) ” 
  &&  “ (cm_binding_valid p f scope slot ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ”
.

Definition cm_emit_var_expr_partial_solve_wit_9_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (slot: Z) (scope: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (lvalue_pre = 0)) (PreH2 : ((cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)) <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (lvalue_pre = 0)) (PreH5 : (0 <= slot)) (PreH6 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH7 : (cm_binding_valid p f scope slot )) (PreH8 : (retval = (cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)))) (PreH9 : (program_pre <> 0)) (PreH10 : (fn_pre <> 0)) (PreH11 : (e = (CMVarE (scope) (slot) (ty)))) (PreH12 : (expr_pre <> 0)) (PreH13 : (0 <= lvalue_pre)) (PreH14 : (lvalue_pre <= 1)) (PreH15 : (e = (CMVarE (scope) (slot) (ty)))) (PreH16 : (cm_wf_program policy cg p )) (PreH17 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH18 : (0 <= slot)) (PreH19 : (slot <= INT_MAX)) (PreH20 : (cm_binding_valid p f scope slot )) (PreH21 : (cm_type_code_wf ty )) (PreH22 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH23 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH24 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH25 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH26 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_binding_address_code (policy) (p) (fid_pre) (scope) (slot))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ ((cm_program_structs (p)) = (cm_program_structs (p))) ” 
  &&  “ ((cm_program_globals (p)) = (cm_program_globals (p))) ” 
  &&  “ (cm_binding_valid p f scope slot ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (lvalue_pre = 0) ” 
  &&  “ ((cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)) <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (lvalue_pre = 0) ” 
  &&  “ (0 <= slot) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_binding_valid p f scope slot ) ” 
  &&  “ (retval = (cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot))) ” 
  &&  “ (program_pre <> 0) ” 
  &&  “ (fn_pre <> 0) ” 
  &&  “ (e = (CMVarE (scope) (slot) (ty))) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (e = (CMVarE (scope) (slot) (ty))) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (0 <= slot) ” 
  &&  “ (slot <= INT_MAX) ” 
  &&  “ (cm_binding_valid p f scope slot ) ” 
  &&  “ (cm_type_code_wf ty ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_binding_address_code (policy) (p) (fid_pre) (scope) (slot))) (tail)) )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
.

Definition cm_emit_var_expr_partial_solve_wit_9 := cm_emit_var_expr_partial_solve_wit_9_pure -> cm_emit_var_expr_partial_solve_wit_9_aux.

Definition cm_emit_var_expr_partial_solve_wit_10_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (slot: Z) (scope: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (lvalue_pre <> 0)) (PreH2 : (0 <= slot)) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (cm_binding_valid p f scope slot )) (PreH5 : (retval = (cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)))) (PreH6 : (program_pre <> 0)) (PreH7 : (fn_pre <> 0)) (PreH8 : (e = (CMVarE (scope) (slot) (ty)))) (PreH9 : (expr_pre <> 0)) (PreH10 : (0 <= lvalue_pre)) (PreH11 : (lvalue_pre <= 1)) (PreH12 : (e = (CMVarE (scope) (slot) (ty)))) (PreH13 : (cm_wf_program policy cg p )) (PreH14 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH15 : (0 <= slot)) (PreH16 : (slot <= INT_MAX)) (PreH17 : (cm_binding_valid p f scope slot )) (PreH18 : (cm_type_code_wf ty )) (PreH19 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH20 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH21 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH22 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH23 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  (cm_function_context_rep fn_pre f body next )
  **  ((( &( "array" ) )) # Int  |-> retval)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_var_code_for (policy) (p) (fid_pre) (scope) (slot) (ty) (lvalue_pre))) (tail)) )
|--
  “ (lvalue_pre <> 0) ”
.

Definition cm_emit_var_expr_partial_solve_wit_10_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (slot: Z) (scope: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (lvalue_pre <> 0)) (PreH2 : (0 <= slot)) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (cm_binding_valid p f scope slot )) (PreH5 : (retval = (cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)))) (PreH6 : (program_pre <> 0)) (PreH7 : (fn_pre <> 0)) (PreH8 : (e = (CMVarE (scope) (slot) (ty)))) (PreH9 : (expr_pre <> 0)) (PreH10 : (0 <= lvalue_pre)) (PreH11 : (lvalue_pre <= 1)) (PreH12 : (e = (CMVarE (scope) (slot) (ty)))) (PreH13 : (cm_wf_program policy cg p )) (PreH14 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH15 : (0 <= slot)) (PreH16 : (slot <= INT_MAX)) (PreH17 : (cm_binding_valid p f scope slot )) (PreH18 : (cm_type_code_wf ty )) (PreH19 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH20 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH21 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH22 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH23 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_var_code_for (policy) (p) (fid_pre) (scope) (slot) (ty) (lvalue_pre))) (tail)) )
|--
  “ (lvalue_pre <> 0) ” 
  &&  “ (lvalue_pre <> 0) ” 
  &&  “ (0 <= slot) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_binding_valid p f scope slot ) ” 
  &&  “ (retval = (cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot))) ” 
  &&  “ (program_pre <> 0) ” 
  &&  “ (fn_pre <> 0) ” 
  &&  “ (e = (CMVarE (scope) (slot) (ty))) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (e = (CMVarE (scope) (slot) (ty))) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (0 <= slot) ” 
  &&  “ (slot <= INT_MAX) ” 
  &&  “ (cm_binding_valid p f scope slot ) ” 
  &&  “ (cm_type_code_wf ty ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_var_code_for (policy) (p) (fid_pre) (scope) (slot) (ty) (lvalue_pre))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
.

Definition cm_emit_var_expr_partial_solve_wit_10 := cm_emit_var_expr_partial_solve_wit_10_pure -> cm_emit_var_expr_partial_solve_wit_10_aux.

Definition cm_emit_var_expr_partial_solve_wit_11_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (slot: Z) (scope: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (lvalue_pre <> 0)) (PreH2 : (lvalue_pre <> 0)) (PreH3 : (0 <= slot)) (PreH4 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH5 : (cm_binding_valid p f scope slot )) (PreH6 : (retval = (cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)))) (PreH7 : (program_pre <> 0)) (PreH8 : (fn_pre <> 0)) (PreH9 : (e = (CMVarE (scope) (slot) (ty)))) (PreH10 : (expr_pre <> 0)) (PreH11 : (0 <= lvalue_pre)) (PreH12 : (lvalue_pre <= 1)) (PreH13 : (e = (CMVarE (scope) (slot) (ty)))) (PreH14 : (cm_wf_program policy cg p )) (PreH15 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH16 : (0 <= slot)) (PreH17 : (slot <= INT_MAX)) (PreH18 : (cm_binding_valid p f scope slot )) (PreH19 : (cm_type_code_wf ty )) (PreH20 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH21 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH22 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH23 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH24 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_binding_address_code (policy) (p) (fid_pre) (scope) (slot))) (tail)) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  (cm_function_context_rep fn_pre f body next )
  **  ((( &( "array" ) )) # Int  |-> retval)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ ((cm_program_structs (p)) = (cm_program_structs (p))) ” 
  &&  “ ((cm_program_globals (p)) = (cm_program_globals (p))) ” 
  &&  “ (cm_binding_valid p f scope slot ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ”
.

Definition cm_emit_var_expr_partial_solve_wit_11_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (ty: cm_type) (slot: Z) (scope: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (lvalue_pre <> 0)) (PreH2 : (lvalue_pre <> 0)) (PreH3 : (0 <= slot)) (PreH4 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH5 : (cm_binding_valid p f scope slot )) (PreH6 : (retval = (cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot)))) (PreH7 : (program_pre <> 0)) (PreH8 : (fn_pre <> 0)) (PreH9 : (e = (CMVarE (scope) (slot) (ty)))) (PreH10 : (expr_pre <> 0)) (PreH11 : (0 <= lvalue_pre)) (PreH12 : (lvalue_pre <= 1)) (PreH13 : (e = (CMVarE (scope) (slot) (ty)))) (PreH14 : (cm_wf_program policy cg p )) (PreH15 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH16 : (0 <= slot)) (PreH17 : (slot <= INT_MAX)) (PreH18 : (cm_binding_valid p f scope slot )) (PreH19 : (cm_type_code_wf ty )) (PreH20 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH21 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH22 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH23 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH24 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_binding_address_code (policy) (p) (fid_pre) (scope) (slot))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ ((cm_program_structs (p)) = (cm_program_structs (p))) ” 
  &&  “ ((cm_program_globals (p)) = (cm_program_globals (p))) ” 
  &&  “ (cm_binding_valid p f scope slot ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (lvalue_pre <> 0) ” 
  &&  “ (lvalue_pre <> 0) ” 
  &&  “ (0 <= slot) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_binding_valid p f scope slot ) ” 
  &&  “ (retval = (cm_binding_array_code (policy) (p) (fid_pre) (scope) (slot))) ” 
  &&  “ (program_pre <> 0) ” 
  &&  “ (fn_pre <> 0) ” 
  &&  “ (e = (CMVarE (scope) (slot) (ty))) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (e = (CMVarE (scope) (slot) (ty))) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (0 <= slot) ” 
  &&  “ (slot <= INT_MAX) ” 
  &&  “ (cm_binding_valid p f scope slot ) ” 
  &&  “ (cm_type_code_wf ty ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_binding_address_code (policy) (p) (fid_pre) (scope) (slot))) (tail)) )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
.

Definition cm_emit_var_expr_partial_solve_wit_11 := cm_emit_var_expr_partial_solve_wit_11_pure -> cm_emit_var_expr_partial_solve_wit_11_aux.

Definition cm_emit_var_expr_which_implies_wit_1 := 
(
forall (ty: cm_type) (slot: Z) (scope: Z) (e: cm_expr) (expr: Z) (PreH1 : (e = (CMVarE (scope) (slot) (ty)))) ,
  (cm_expr_rep expr e )
|--
  “ (e = (CMVarE (scope) (slot) (ty))) ” 
  &&  “ (expr <> 0) ”
  &&  ((&((expr)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
) \/
(
forall (ty: cm_type) (slot: Z) (scope: Z) (e: cm_expr) (expr: Z) (PreH1 : (e = (CMVarE (scope) (slot) (ty)))) ,
  (cm_expr_rep expr e )
|--
  “ (expr <> 0) ”
  &&  ((&((expr)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
).

Definition cm_emit_var_expr_which_implies_wit_1_split_goal_1 := 
forall (ty: cm_type) (slot: Z) (scope: Z) (e: cm_expr) (expr: Z) (PreH1 : (e = (CMVarE (scope) (slot) (ty)))) ,
  (cm_expr_rep expr e )
|--
  “ (expr <> 0) ”
.

Definition cm_emit_var_expr_which_implies_wit_1_split_goal_spatial := 
forall (ty: cm_type) (slot: Z) (scope: Z) (e: cm_expr) (expr: Z) (PreH1 : (e = (CMVarE (scope) (slot) (ty)))) ,
  (cm_expr_rep expr e )
|--
  ((&((expr)  # "cm_expr" ->ₛ "kind")) # Int  |-> 2)
  **  ((&((expr)  # "cm_expr" ->ₛ "op")) # Int  |-> scope)
  **  ((&((expr)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode (ty)))
  **  ((&((expr)  # "cm_expr" ->ₛ "value")) # Int64  |-> slot)
  **  ((&((expr)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr)  # "cm_expr" ->ₛ "args")) # Ptr  |-> 0)
.

Definition cm_emit_var_expr_which_implies_wit_2 := 
(
forall (functions_ptr: Z) (next: Z) (body: Z) (f: cm_function_d) (p: cm_program) (program: Z) (fn: Z) ,
  (cm_program_context_rep program p functions_ptr )
  **  (cm_function_context_rep fn f body next )
|--
  EX (lp: Z)  (pp: Z)  (tp: Z)  (gp: Z)  (sp: Z) ,
  “ (program <> 0) ” 
  &&  “ (fn <> 0) ”
  &&  ((&((program)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  ((&((fn)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
) \/
(
forall (functions_ptr: Z) (next: Z) (body: Z) (f: cm_function_d) (p: cm_program) (program: Z) (fn: Z) ,
  (cm_program_context_rep program p functions_ptr )
  **  (cm_function_context_rep fn f body next )
|--
  EX (lp: Z)  (pp: Z)  (tp: Z)  (gp: Z)  (sp: Z) ,
  “ (program <> 0) ” 
  &&  “ (fn <> 0) ”
  &&  ((&((program)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  ((&((fn)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
).

Definition cm_emit_var_expr_which_implies_wit_3 := 
(
forall (functions_ptr: Z) (next: Z) (body: Z) (f: cm_function_d) (p: cm_program) (lp: Z) (pp: Z) (tp: Z) (gp: Z) (sp: Z) (program: Z) (fn: Z) (PreH1 : (program <> 0)) (PreH2 : (fn <> 0)) ,
  ((&((program)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  ((&((fn)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
|--
  (cm_program_context_rep program p functions_ptr )
  **  (cm_function_context_rep fn f body next )
) \/
(
forall (functions_ptr: Z) (next: Z) (body: Z) (f: cm_function_d) (p: cm_program) (lp: Z) (pp: Z) (tp: Z) (gp: Z) (sp: Z) (program: Z) (fn: Z) (PreH1 : ((cm_type_encode ((cm_function_ret (f)))) <= INT_MAX)) (PreH2 : ((cm_program_main (p)) <= INT_MAX)) (PreH3 : ((cm_type_encode ((cm_function_ret (f)))) >= INT_MIN)) (PreH4 : ((cm_program_main (p)) >= INT_MIN)) (PreH5 : (program <> 0)) (PreH6 : (fn <> 0)) ,
  ((&((program)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  ((&((fn)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
|--
  (cm_program_context_rep program p functions_ptr )
  **  (cm_function_context_rep fn f body next )
).

Definition cm_emit_var_expr_which_implies_wit_3_split_goal_spatial := 
forall (functions_ptr: Z) (next: Z) (body: Z) (f: cm_function_d) (p: cm_program) (lp: Z) (pp: Z) (tp: Z) (gp: Z) (sp: Z) (program: Z) (fn: Z) (PreH1 : ((cm_type_encode ((cm_function_ret (f)))) <= INT_MAX)) (PreH2 : ((cm_program_main (p)) <= INT_MAX)) (PreH3 : ((cm_type_encode ((cm_function_ret (f)))) >= INT_MIN)) (PreH4 : ((cm_program_main (p)) >= INT_MIN)) (PreH5 : (program <> 0)) (PreH6 : (fn <> 0)) ,
  ((&((program)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  ((&((fn)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
|--
  (cm_program_context_rep program p functions_ptr )
  **  (cm_function_context_rep fn f body next )
.

Definition cm_emit_var_expr_which_implies_wit_4 := 
(
forall (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (ty: cm_type) (slot: Z) (scope: Z) (p: cm_program) (policy: cm_lookup_policy) (lvalue: Z) (fid: Z) (emitter: Z) (PreH1 : (0 <= lvalue)) (PreH2 : (lvalue <= 0)) (PreH3 : ((cm_binding_array_code (policy) (p) (fid) (scope) (slot)) = 0)) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_var_code_for (policy) (p) (fid) (scope) (slot) (ty) (lvalue))) (tail)) )
|--
  “ (lvalue = 0) ” 
  &&  “ ((cm_binding_array_code (policy) (p) (fid) (scope) (slot)) = 0) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_binding_address_code (policy) (p) (fid) (scope) (slot))) ((app ((cm_load_code (ty))) (tail)))) )
) \/
(
forall (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (ty: cm_type) (slot: Z) (scope: Z) (p: cm_program) (policy: cm_lookup_policy) (lvalue: Z) (fid: Z) (emitter: Z) (PreH1 : (0 <= lvalue)) (PreH2 : (lvalue <= 0)) (PreH3 : ((cm_binding_array_code (policy) (p) (fid) (scope) (slot)) = 0)) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_var_code_for (policy) (p) (fid) (scope) (slot) (ty) (lvalue))) (tail)) )
|--
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_binding_address_code (policy) (p) (fid) (scope) (slot))) ((app ((cm_load_code (ty))) (tail)))) )
).

Definition cm_emit_var_expr_which_implies_wit_4_split_goal_spatial := 
forall (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (ty: cm_type) (slot: Z) (scope: Z) (p: cm_program) (policy: cm_lookup_policy) (lvalue: Z) (fid: Z) (emitter: Z) (PreH1 : (0 <= lvalue)) (PreH2 : (lvalue <= 0)) (PreH3 : ((cm_binding_array_code (policy) (p) (fid) (scope) (slot)) = 0)) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_var_code_for (policy) (p) (fid) (scope) (slot) (ty) (lvalue))) (tail)) )
|--
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_binding_address_code (policy) (p) (fid) (scope) (slot))) ((app ((cm_load_code (ty))) (tail)))) )
.

Definition cm_emit_var_expr_which_implies_wit_5 := 
(
forall (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (ty: cm_type) (slot: Z) (scope: Z) (p: cm_program) (policy: cm_lookup_policy) (lvalue: Z) (fid: Z) (emitter: Z) (PreH1 : (0 <= lvalue)) (PreH2 : (lvalue <= 0)) (PreH3 : ((cm_binding_array_code (policy) (p) (fid) (scope) (slot)) <> 0)) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_var_code_for (policy) (p) (fid) (scope) (slot) (ty) (lvalue))) (tail)) )
|--
  “ (lvalue = 0) ” 
  &&  “ ((cm_binding_array_code (policy) (p) (fid) (scope) (slot)) <> 0) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_binding_address_code (policy) (p) (fid) (scope) (slot))) (tail)) )
) \/
(
forall (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (ty: cm_type) (slot: Z) (scope: Z) (p: cm_program) (policy: cm_lookup_policy) (lvalue: Z) (fid: Z) (emitter: Z) (PreH1 : (0 <= lvalue)) (PreH2 : (lvalue <= 0)) (PreH3 : ((cm_binding_array_code (policy) (p) (fid) (scope) (slot)) <> 0)) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_var_code_for (policy) (p) (fid) (scope) (slot) (ty) (lvalue))) (tail)) )
|--
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_binding_address_code (policy) (p) (fid) (scope) (slot))) (tail)) )
).

Definition cm_emit_var_expr_which_implies_wit_5_split_goal_spatial := 
forall (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (ty: cm_type) (slot: Z) (scope: Z) (p: cm_program) (policy: cm_lookup_policy) (lvalue: Z) (fid: Z) (emitter: Z) (PreH1 : (0 <= lvalue)) (PreH2 : (lvalue <= 0)) (PreH3 : ((cm_binding_array_code (policy) (p) (fid) (scope) (slot)) <> 0)) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_var_code_for (policy) (p) (fid) (scope) (slot) (ty) (lvalue))) (tail)) )
|--
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_binding_address_code (policy) (p) (fid) (scope) (slot))) (tail)) )
.

Definition cm_emit_var_expr_which_implies_wit_6 := 
(
forall (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (ty: cm_type) (slot: Z) (scope: Z) (p: cm_program) (policy: cm_lookup_policy) (lvalue: Z) (fid: Z) (emitter: Z) (PreH1 : (lvalue <> 0)) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_var_code_for (policy) (p) (fid) (scope) (slot) (ty) (lvalue))) (tail)) )
|--
  “ (lvalue <> 0) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_binding_address_code (policy) (p) (fid) (scope) (slot))) (tail)) )
) \/
(
forall (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (ty: cm_type) (slot: Z) (scope: Z) (p: cm_program) (policy: cm_lookup_policy) (lvalue: Z) (fid: Z) (emitter: Z) (PreH1 : (lvalue <> 0)) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_var_code_for (policy) (p) (fid) (scope) (slot) (ty) (lvalue))) (tail)) )
|--
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_binding_address_code (policy) (p) (fid) (scope) (slot))) (tail)) )
).

Definition cm_emit_var_expr_which_implies_wit_6_split_goal_spatial := 
forall (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (ty: cm_type) (slot: Z) (scope: Z) (p: cm_program) (policy: cm_lookup_policy) (lvalue: Z) (fid: Z) (emitter: Z) (PreH1 : (lvalue <> 0)) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_var_code_for (policy) (p) (fid) (scope) (slot) (ty) (lvalue))) (tail)) )
|--
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_binding_address_code (policy) (p) (fid) (scope) (slot))) (tail)) )
.

Module Type VC_Correct.


Axiom proof_of_cm_emit_var_expr_safety_wit_1 : cm_emit_var_expr_safety_wit_1.
Axiom proof_of_cm_emit_var_expr_return_wit_1 : cm_emit_var_expr_return_wit_1.
Axiom proof_of_cm_emit_var_expr_return_wit_2 : cm_emit_var_expr_return_wit_2.
Axiom proof_of_cm_emit_var_expr_return_wit_3 : cm_emit_var_expr_return_wit_3.
Axiom proof_of_cm_emit_var_expr_partial_solve_wit_1_pure : cm_emit_var_expr_partial_solve_wit_1_pure.
Axiom proof_of_cm_emit_var_expr_partial_solve_wit_1 : cm_emit_var_expr_partial_solve_wit_1.
Axiom proof_of_cm_emit_var_expr_partial_solve_wit_2 : cm_emit_var_expr_partial_solve_wit_2.
Axiom proof_of_cm_emit_var_expr_partial_solve_wit_3_pure : cm_emit_var_expr_partial_solve_wit_3_pure.
Axiom proof_of_cm_emit_var_expr_partial_solve_wit_3 : cm_emit_var_expr_partial_solve_wit_3.
Axiom proof_of_cm_emit_var_expr_partial_solve_wit_4_pure : cm_emit_var_expr_partial_solve_wit_4_pure.
Axiom proof_of_cm_emit_var_expr_partial_solve_wit_4 : cm_emit_var_expr_partial_solve_wit_4.
Axiom proof_of_cm_emit_var_expr_partial_solve_wit_5_pure : cm_emit_var_expr_partial_solve_wit_5_pure.
Axiom proof_of_cm_emit_var_expr_partial_solve_wit_5 : cm_emit_var_expr_partial_solve_wit_5.
Axiom proof_of_cm_emit_var_expr_partial_solve_wit_6_pure : cm_emit_var_expr_partial_solve_wit_6_pure.
Axiom proof_of_cm_emit_var_expr_partial_solve_wit_6 : cm_emit_var_expr_partial_solve_wit_6.
Axiom proof_of_cm_emit_var_expr_partial_solve_wit_7_pure : cm_emit_var_expr_partial_solve_wit_7_pure.
Axiom proof_of_cm_emit_var_expr_partial_solve_wit_7 : cm_emit_var_expr_partial_solve_wit_7.
Axiom proof_of_cm_emit_var_expr_partial_solve_wit_8_pure : cm_emit_var_expr_partial_solve_wit_8_pure.
Axiom proof_of_cm_emit_var_expr_partial_solve_wit_8 : cm_emit_var_expr_partial_solve_wit_8.
Axiom proof_of_cm_emit_var_expr_partial_solve_wit_9_pure : cm_emit_var_expr_partial_solve_wit_9_pure.
Axiom proof_of_cm_emit_var_expr_partial_solve_wit_9 : cm_emit_var_expr_partial_solve_wit_9.
Axiom proof_of_cm_emit_var_expr_partial_solve_wit_10_pure : cm_emit_var_expr_partial_solve_wit_10_pure.
Axiom proof_of_cm_emit_var_expr_partial_solve_wit_10 : cm_emit_var_expr_partial_solve_wit_10.
Axiom proof_of_cm_emit_var_expr_partial_solve_wit_11_pure : cm_emit_var_expr_partial_solve_wit_11_pure.
Axiom proof_of_cm_emit_var_expr_partial_solve_wit_11 : cm_emit_var_expr_partial_solve_wit_11.
Axiom proof_of_cm_emit_var_expr_which_implies_wit_1 : cm_emit_var_expr_which_implies_wit_1.
Axiom proof_of_cm_emit_var_expr_which_implies_wit_2 : cm_emit_var_expr_which_implies_wit_2.
Axiom proof_of_cm_emit_var_expr_which_implies_wit_3 : cm_emit_var_expr_which_implies_wit_3.
Axiom proof_of_cm_emit_var_expr_which_implies_wit_4 : cm_emit_var_expr_which_implies_wit_4.
Axiom proof_of_cm_emit_var_expr_which_implies_wit_5 : cm_emit_var_expr_which_implies_wit_5.
Axiom proof_of_cm_emit_var_expr_which_implies_wit_6 : cm_emit_var_expr_which_implies_wit_6.

End VC_Correct.
