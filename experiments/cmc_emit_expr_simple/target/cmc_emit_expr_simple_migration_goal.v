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
Require Import SimpleC.EE.QCP_demos_human.cmc_emit_expr_simple_migration_lib.
Local Open Scope sac.

(*----- Function cm_emit_simple_expr -----*)

Definition cm_emit_simple_expr_safety_wit_1 := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (simple: cm_simple_view) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (xb: Z) (xa: Z) (PreH1 : (expr_pre <> 0)) (PreH2 : (0 <= lvalue_pre)) (PreH3 : (lvalue_pre <= 1)) (PreH4 : (e = (cm_simple_source_expr (simple)))) (PreH5 : (cm_simple_expr e )) (PreH6 : (cm_wf_program policy cg p )) (PreH7 : (cm_typed_program policy p )) (PreH8 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH9 : (cm_expr_wf policy p f e )) (PreH10 : (cm_expr_counts_representable policy p fid_pre e )) (PreH11 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH12 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH13 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH14 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH15 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH16 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH17 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH18 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> xa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> xb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_expr_payload e xa xb xargs )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_simple_code_for (policy) (p) (fid_pre) (simple) (lvalue_pre))) (tail)) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition cm_emit_simple_expr_return_wit_1 := 
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (simple: cm_simple_view) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (scope: Z) (slot: Z) (ty: cm_type) (PreH1 : (0 <= lvalue_pre)) (PreH2 : (lvalue_pre <= 1)) (PreH3 : (e = (CMVarE (scope) (slot) (ty)))) (PreH4 : (cm_wf_program policy cg p )) (PreH5 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH6 : (0 <= slot)) (PreH7 : (slot <= INT_MAX)) (PreH8 : (cm_binding_valid p f scope slot )) (PreH9 : (cm_type_code_wf ty )) (PreH10 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH11 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH12 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH13 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH14 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH15 : (e = (cm_simple_source_expr (simple)))) (PreH16 : (cm_simple_expr e )) (PreH17 : (e = (CMVarE (scope) (slot) (ty)))) (PreH18 : (simple = (CMSimpleVar (scope) (slot) (ty)))) (PreH19 : (0 <= slot)) (PreH20 : (slot <= INT_MAX)) (PreH21 : (cm_binding_valid p f scope slot )) (PreH22 : (cm_type_code_wf ty )) (PreH23 : (cm_expr_wf policy p f e )) (PreH24 : (cm_expr_counts_representable policy p fid_pre e )) (PreH25 : ((cm_rep_expr_kind (e)) = 2)) (PreH26 : (expr_pre <> 0)) (PreH27 : (0 <= lvalue_pre)) (PreH28 : (lvalue_pre <= 1)) (PreH29 : (e = (cm_simple_source_expr (simple)))) (PreH30 : (cm_simple_expr e )) (PreH31 : (cm_wf_program policy cg p )) (PreH32 : (cm_typed_program policy p )) (PreH33 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH34 : (cm_expr_wf policy p f e )) (PreH35 : (cm_expr_counts_representable policy p fid_pre e )) (PreH36 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH37 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH38 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH39 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH40 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH41 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH42 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH43 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_var_code_for (policy) (p) (fid_pre) (scope) (slot) (ty) (lvalue_pre)))) tail )
|--
  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (e = (cm_simple_source_expr (simple))) ” 
  &&  “ (cm_simple_expr e ) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_simple_code_for (policy) (p) (fid_pre) (simple) (lvalue_pre)))) tail )
) \/
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (simple: cm_simple_view) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (scope: Z) (slot: Z) (ty: cm_type) (PreH1 : (0 <= lvalue_pre)) (PreH2 : (lvalue_pre <= 1)) (PreH3 : (e = (CMVarE (scope) (slot) (ty)))) (PreH4 : (cm_wf_program policy cg p )) (PreH5 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH6 : (0 <= slot)) (PreH7 : (slot <= INT_MAX)) (PreH8 : (cm_binding_valid p f scope slot )) (PreH9 : (cm_type_code_wf ty )) (PreH10 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH11 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH12 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH13 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH14 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH15 : (e = (cm_simple_source_expr (simple)))) (PreH16 : (cm_simple_expr e )) (PreH17 : (e = (CMVarE (scope) (slot) (ty)))) (PreH18 : (simple = (CMSimpleVar (scope) (slot) (ty)))) (PreH19 : (0 <= slot)) (PreH20 : (slot <= INT_MAX)) (PreH21 : (cm_binding_valid p f scope slot )) (PreH22 : (cm_type_code_wf ty )) (PreH23 : (cm_expr_wf policy p f e )) (PreH24 : (cm_expr_counts_representable policy p fid_pre e )) (PreH25 : ((cm_rep_expr_kind (e)) = 2)) (PreH26 : (expr_pre <> 0)) (PreH27 : (0 <= lvalue_pre)) (PreH28 : (lvalue_pre <= 1)) (PreH29 : (e = (cm_simple_source_expr (simple)))) (PreH30 : (cm_simple_expr e )) (PreH31 : (cm_wf_program policy cg p )) (PreH32 : (cm_typed_program policy p )) (PreH33 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH34 : (cm_expr_wf policy p f e )) (PreH35 : (cm_expr_counts_representable policy p fid_pre e )) (PreH36 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH37 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH38 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH39 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH40 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH41 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH42 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH43 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_var_code_for (policy) (p) (fid_pre) (scope) (slot) (ty) (lvalue_pre)))) tail )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_simple_code_for (policy) (p) (fid_pre) (simple) (lvalue_pre)))) tail )
).

Definition cm_emit_simple_expr_return_wit_1_split_goal_spatial := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (simple: cm_simple_view) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (scope: Z) (slot: Z) (ty: cm_type) (PreH1 : (0 <= lvalue_pre)) (PreH2 : (lvalue_pre <= 1)) (PreH3 : (e = (CMVarE (scope) (slot) (ty)))) (PreH4 : (cm_wf_program policy cg p )) (PreH5 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH6 : (0 <= slot)) (PreH7 : (slot <= INT_MAX)) (PreH8 : (cm_binding_valid p f scope slot )) (PreH9 : (cm_type_code_wf ty )) (PreH10 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH11 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH12 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH13 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH14 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH15 : (e = (cm_simple_source_expr (simple)))) (PreH16 : (cm_simple_expr e )) (PreH17 : (e = (CMVarE (scope) (slot) (ty)))) (PreH18 : (simple = (CMSimpleVar (scope) (slot) (ty)))) (PreH19 : (0 <= slot)) (PreH20 : (slot <= INT_MAX)) (PreH21 : (cm_binding_valid p f scope slot )) (PreH22 : (cm_type_code_wf ty )) (PreH23 : (cm_expr_wf policy p f e )) (PreH24 : (cm_expr_counts_representable policy p fid_pre e )) (PreH25 : ((cm_rep_expr_kind (e)) = 2)) (PreH26 : (expr_pre <> 0)) (PreH27 : (0 <= lvalue_pre)) (PreH28 : (lvalue_pre <= 1)) (PreH29 : (e = (cm_simple_source_expr (simple)))) (PreH30 : (cm_simple_expr e )) (PreH31 : (cm_wf_program policy cg p )) (PreH32 : (cm_typed_program policy p )) (PreH33 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH34 : (cm_expr_wf policy p f e )) (PreH35 : (cm_expr_counts_representable policy p fid_pre e )) (PreH36 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH37 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH38 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH39 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH40 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH41 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH42 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH43 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_var_code_for (policy) (p) (fid_pre) (scope) (slot) (ty) (lvalue_pre)))) tail )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_simple_code_for (policy) (p) (fid_pre) (simple) (lvalue_pre)))) tail )
.

Definition cm_emit_simple_expr_return_wit_2 := 
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (simple: cm_simple_view) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (leaf: cm_leaf_expr) (PreH1 : (0 <= lvalue_pre)) (PreH2 : (lvalue_pre <= 1)) (PreH3 : (e = (cm_leaf_source_expr (leaf)))) (PreH4 : (cm_dispatch_leaf e )) (PreH5 : (cm_wf_program policy cg p )) (PreH6 : (cm_typed_program policy p )) (PreH7 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH8 : (cm_expr_wf policy p f e )) (PreH9 : (cm_expr_counts_representable policy p fid_pre e )) (PreH10 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH11 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH12 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH13 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH14 : (e = (cm_simple_source_expr (simple)))) (PreH15 : (cm_simple_expr e )) (PreH16 : (e = (cm_leaf_source_expr (leaf)))) (PreH17 : (simple = (CMSimpleLeaf (leaf)))) (PreH18 : (cm_dispatch_leaf e )) (PreH19 : (cm_expr_wf policy p f e )) (PreH20 : (cm_expr_counts_representable policy p fid_pre e )) (PreH21 : ((cm_rep_expr_kind (e)) <> 2)) (PreH22 : (expr_pre <> 0)) (PreH23 : (0 <= lvalue_pre)) (PreH24 : (lvalue_pre <= 1)) (PreH25 : (e = (cm_simple_source_expr (simple)))) (PreH26 : (cm_simple_expr e )) (PreH27 : (cm_wf_program policy cg p )) (PreH28 : (cm_typed_program policy p )) (PreH29 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH30 : (cm_expr_wf policy p f e )) (PreH31 : (cm_expr_counts_representable policy p fid_pre e )) (PreH32 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH33 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH34 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH35 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH36 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH37 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH38 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH39 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_leaf_code_for (p) (leaf) (lvalue_pre)))) tail )
|--
  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (e = (cm_simple_source_expr (simple))) ” 
  &&  “ (cm_simple_expr e ) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_simple_code_for (policy) (p) (fid_pre) (simple) (lvalue_pre)))) tail )
) \/
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (simple: cm_simple_view) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (leaf: cm_leaf_expr) (PreH1 : (0 <= lvalue_pre)) (PreH2 : (lvalue_pre <= 1)) (PreH3 : (e = (cm_leaf_source_expr (leaf)))) (PreH4 : (cm_dispatch_leaf e )) (PreH5 : (cm_wf_program policy cg p )) (PreH6 : (cm_typed_program policy p )) (PreH7 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH8 : (cm_expr_wf policy p f e )) (PreH9 : (cm_expr_counts_representable policy p fid_pre e )) (PreH10 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH11 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH12 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH13 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH14 : (e = (cm_simple_source_expr (simple)))) (PreH15 : (cm_simple_expr e )) (PreH16 : (e = (cm_leaf_source_expr (leaf)))) (PreH17 : (simple = (CMSimpleLeaf (leaf)))) (PreH18 : (cm_dispatch_leaf e )) (PreH19 : (cm_expr_wf policy p f e )) (PreH20 : (cm_expr_counts_representable policy p fid_pre e )) (PreH21 : ((cm_rep_expr_kind (e)) <> 2)) (PreH22 : (expr_pre <> 0)) (PreH23 : (0 <= lvalue_pre)) (PreH24 : (lvalue_pre <= 1)) (PreH25 : (e = (cm_simple_source_expr (simple)))) (PreH26 : (cm_simple_expr e )) (PreH27 : (cm_wf_program policy cg p )) (PreH28 : (cm_typed_program policy p )) (PreH29 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH30 : (cm_expr_wf policy p f e )) (PreH31 : (cm_expr_counts_representable policy p fid_pre e )) (PreH32 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH33 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH34 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH35 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH36 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH37 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH38 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH39 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_leaf_code_for (p) (leaf) (lvalue_pre)))) tail )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_simple_code_for (policy) (p) (fid_pre) (simple) (lvalue_pre)))) tail )
).

Definition cm_emit_simple_expr_return_wit_2_split_goal_spatial := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (simple: cm_simple_view) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (leaf: cm_leaf_expr) (PreH1 : (0 <= lvalue_pre)) (PreH2 : (lvalue_pre <= 1)) (PreH3 : (e = (cm_leaf_source_expr (leaf)))) (PreH4 : (cm_dispatch_leaf e )) (PreH5 : (cm_wf_program policy cg p )) (PreH6 : (cm_typed_program policy p )) (PreH7 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH8 : (cm_expr_wf policy p f e )) (PreH9 : (cm_expr_counts_representable policy p fid_pre e )) (PreH10 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH11 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH12 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH13 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH14 : (e = (cm_simple_source_expr (simple)))) (PreH15 : (cm_simple_expr e )) (PreH16 : (e = (cm_leaf_source_expr (leaf)))) (PreH17 : (simple = (CMSimpleLeaf (leaf)))) (PreH18 : (cm_dispatch_leaf e )) (PreH19 : (cm_expr_wf policy p f e )) (PreH20 : (cm_expr_counts_representable policy p fid_pre e )) (PreH21 : ((cm_rep_expr_kind (e)) <> 2)) (PreH22 : (expr_pre <> 0)) (PreH23 : (0 <= lvalue_pre)) (PreH24 : (lvalue_pre <= 1)) (PreH25 : (e = (cm_simple_source_expr (simple)))) (PreH26 : (cm_simple_expr e )) (PreH27 : (cm_wf_program policy cg p )) (PreH28 : (cm_typed_program policy p )) (PreH29 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH30 : (cm_expr_wf policy p f e )) (PreH31 : (cm_expr_counts_representable policy p fid_pre e )) (PreH32 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH33 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH34 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH35 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH36 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH37 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH38 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH39 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_leaf_code_for (p) (leaf) (lvalue_pre)))) tail )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_simple_code_for (policy) (p) (fid_pre) (simple) (lvalue_pre)))) tail )
.

Definition cm_emit_simple_expr_partial_solve_wit_1 := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (simple: cm_simple_view) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (0 <= lvalue_pre)) (PreH2 : (lvalue_pre <= 1)) (PreH3 : (e = (cm_simple_source_expr (simple)))) (PreH4 : (cm_simple_expr e )) (PreH5 : (cm_wf_program policy cg p )) (PreH6 : (cm_typed_program policy p )) (PreH7 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH8 : (cm_expr_wf policy p f e )) (PreH9 : (cm_expr_counts_representable policy p fid_pre e )) (PreH10 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH11 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH12 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH13 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH14 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH15 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH16 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH17 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_simple_code_for (policy) (p) (fid_pre) (simple) (lvalue_pre))) (tail)) )
|--
  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (e = (cm_simple_source_expr (simple))) ” 
  &&  “ (cm_simple_expr e ) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ”
  &&  (cm_expr_rep expr_pre e )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_simple_code_for (policy) (p) (fid_pre) (simple) (lvalue_pre))) (tail)) )
.

Definition cm_emit_simple_expr_partial_solve_wit_2_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (simple: cm_simple_view) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (xb: Z) (xa: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 2)) (PreH2 : (expr_pre <> 0)) (PreH3 : (0 <= lvalue_pre)) (PreH4 : (lvalue_pre <= 1)) (PreH5 : (e = (cm_simple_source_expr (simple)))) (PreH6 : (cm_simple_expr e )) (PreH7 : (cm_wf_program policy cg p )) (PreH8 : (cm_typed_program policy p )) (PreH9 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH10 : (cm_expr_wf policy p f e )) (PreH11 : (cm_expr_counts_representable policy p fid_pre e )) (PreH12 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH13 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH14 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH15 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH16 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH17 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH18 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH19 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> xa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> xb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_expr_payload e xa xb xargs )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_simple_code_for (policy) (p) (fid_pre) (simple) (lvalue_pre))) (tail)) )
|--
  “ (e = (cm_simple_source_expr (simple))) ” 
  &&  “ (cm_simple_expr e ) ” 
  &&  “ ((cm_rep_expr_kind (e)) = 2) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ”
.

Definition cm_emit_simple_expr_partial_solve_wit_2_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (simple: cm_simple_view) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (xb: Z) (xa: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 2)) (PreH2 : (expr_pre <> 0)) (PreH3 : (0 <= lvalue_pre)) (PreH4 : (lvalue_pre <= 1)) (PreH5 : (e = (cm_simple_source_expr (simple)))) (PreH6 : (cm_simple_expr e )) (PreH7 : (cm_wf_program policy cg p )) (PreH8 : (cm_typed_program policy p )) (PreH9 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH10 : (cm_expr_wf policy p f e )) (PreH11 : (cm_expr_counts_representable policy p fid_pre e )) (PreH12 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH13 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH14 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH15 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH16 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH17 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH18 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH19 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> xa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> xb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_expr_payload e xa xb xargs )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_simple_code_for (policy) (p) (fid_pre) (simple) (lvalue_pre))) (tail)) )
|--
  “ (e = (cm_simple_source_expr (simple))) ” 
  &&  “ (cm_simple_expr e ) ” 
  &&  “ ((cm_rep_expr_kind (e)) = 2) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ ((cm_rep_expr_kind (e)) = 2) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (e = (cm_simple_source_expr (simple))) ” 
  &&  “ (cm_simple_expr e ) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_simple_code_for (policy) (p) (fid_pre) (simple) (lvalue_pre))) (tail)) )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> xa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> xb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_expr_payload e xa xb xargs )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
.

Definition cm_emit_simple_expr_partial_solve_wit_2 := cm_emit_simple_expr_partial_solve_wit_2_pure -> cm_emit_simple_expr_partial_solve_wit_2_aux.

Definition cm_emit_simple_expr_partial_solve_wit_3_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (simple: cm_simple_view) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (xb: Z) (xa: Z) (scope: Z) (slot: Z) (ty: cm_type) (PreH1 : (e = (cm_simple_source_expr (simple)))) (PreH2 : (cm_simple_expr e )) (PreH3 : (e = (CMVarE (scope) (slot) (ty)))) (PreH4 : (simple = (CMSimpleVar (scope) (slot) (ty)))) (PreH5 : (0 <= slot)) (PreH6 : (slot <= INT_MAX)) (PreH7 : (cm_binding_valid p f scope slot )) (PreH8 : (cm_type_code_wf ty )) (PreH9 : (cm_expr_wf policy p f e )) (PreH10 : (cm_expr_counts_representable policy p fid_pre e )) (PreH11 : ((cm_rep_expr_kind (e)) = 2)) (PreH12 : (expr_pre <> 0)) (PreH13 : (0 <= lvalue_pre)) (PreH14 : (lvalue_pre <= 1)) (PreH15 : (e = (cm_simple_source_expr (simple)))) (PreH16 : (cm_simple_expr e )) (PreH17 : (cm_wf_program policy cg p )) (PreH18 : (cm_typed_program policy p )) (PreH19 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH20 : (cm_expr_wf policy p f e )) (PreH21 : (cm_expr_counts_representable policy p fid_pre e )) (PreH22 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH23 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH24 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH25 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH26 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH27 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH28 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH29 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_var_code_for (policy) (p) (fid_pre) (scope) (slot) (ty) (lvalue_pre))) (tail)) )
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> xa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> xb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_expr_payload e xa xb xargs )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
|--
  “ (expr_pre <> 0) ”
.

Definition cm_emit_simple_expr_partial_solve_wit_3_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (simple: cm_simple_view) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (xb: Z) (xa: Z) (scope: Z) (slot: Z) (ty: cm_type) (PreH1 : (e = (cm_simple_source_expr (simple)))) (PreH2 : (cm_simple_expr e )) (PreH3 : (e = (CMVarE (scope) (slot) (ty)))) (PreH4 : (simple = (CMSimpleVar (scope) (slot) (ty)))) (PreH5 : (0 <= slot)) (PreH6 : (slot <= INT_MAX)) (PreH7 : (cm_binding_valid p f scope slot )) (PreH8 : (cm_type_code_wf ty )) (PreH9 : (cm_expr_wf policy p f e )) (PreH10 : (cm_expr_counts_representable policy p fid_pre e )) (PreH11 : ((cm_rep_expr_kind (e)) = 2)) (PreH12 : (expr_pre <> 0)) (PreH13 : (0 <= lvalue_pre)) (PreH14 : (lvalue_pre <= 1)) (PreH15 : (e = (cm_simple_source_expr (simple)))) (PreH16 : (cm_simple_expr e )) (PreH17 : (cm_wf_program policy cg p )) (PreH18 : (cm_typed_program policy p )) (PreH19 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH20 : (cm_expr_wf policy p f e )) (PreH21 : (cm_expr_counts_representable policy p fid_pre e )) (PreH22 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH23 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH24 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH25 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH26 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH27 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH28 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH29 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_var_code_for (policy) (p) (fid_pre) (scope) (slot) (ty) (lvalue_pre))) (tail)) )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> xa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> xb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_expr_payload e xa xb xargs )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
|--
  “ (expr_pre <> 0) ” 
  &&  “ (e = (cm_simple_source_expr (simple))) ” 
  &&  “ (cm_simple_expr e ) ” 
  &&  “ (e = (CMVarE (scope) (slot) (ty))) ” 
  &&  “ (simple = (CMSimpleVar (scope) (slot) (ty))) ” 
  &&  “ (0 <= slot) ” 
  &&  “ (slot <= INT_MAX) ” 
  &&  “ (cm_binding_valid p f scope slot ) ” 
  &&  “ (cm_type_code_wf ty ) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ ((cm_rep_expr_kind (e)) = 2) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (e = (cm_simple_source_expr (simple))) ” 
  &&  “ (cm_simple_expr e ) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ”
  &&  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> xa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> xb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_expr_payload e xa xb xargs )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_var_code_for (policy) (p) (fid_pre) (scope) (slot) (ty) (lvalue_pre))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
.

Definition cm_emit_simple_expr_partial_solve_wit_3 := cm_emit_simple_expr_partial_solve_wit_3_pure -> cm_emit_simple_expr_partial_solve_wit_3_aux.

Definition cm_emit_simple_expr_partial_solve_wit_4_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (simple: cm_simple_view) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (scope: Z) (slot: Z) (ty: cm_type) (PreH1 : (e = (cm_simple_source_expr (simple)))) (PreH2 : (cm_simple_expr e )) (PreH3 : (e = (CMVarE (scope) (slot) (ty)))) (PreH4 : (simple = (CMSimpleVar (scope) (slot) (ty)))) (PreH5 : (0 <= slot)) (PreH6 : (slot <= INT_MAX)) (PreH7 : (cm_binding_valid p f scope slot )) (PreH8 : (cm_type_code_wf ty )) (PreH9 : (cm_expr_wf policy p f e )) (PreH10 : (cm_expr_counts_representable policy p fid_pre e )) (PreH11 : ((cm_rep_expr_kind (e)) = 2)) (PreH12 : (expr_pre <> 0)) (PreH13 : (0 <= lvalue_pre)) (PreH14 : (lvalue_pre <= 1)) (PreH15 : (e = (cm_simple_source_expr (simple)))) (PreH16 : (cm_simple_expr e )) (PreH17 : (cm_wf_program policy cg p )) (PreH18 : (cm_typed_program policy p )) (PreH19 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH20 : (cm_expr_wf policy p f e )) (PreH21 : (cm_expr_counts_representable policy p fid_pre e )) (PreH22 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH23 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH24 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH25 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH26 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH27 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH28 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH29 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  (cm_expr_rep expr_pre e )
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_var_code_for (policy) (p) (fid_pre) (scope) (slot) (ty) (lvalue_pre))) (tail)) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
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
.

Definition cm_emit_simple_expr_partial_solve_wit_4_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (simple: cm_simple_view) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (scope: Z) (slot: Z) (ty: cm_type) (PreH1 : (e = (cm_simple_source_expr (simple)))) (PreH2 : (cm_simple_expr e )) (PreH3 : (e = (CMVarE (scope) (slot) (ty)))) (PreH4 : (simple = (CMSimpleVar (scope) (slot) (ty)))) (PreH5 : (0 <= slot)) (PreH6 : (slot <= INT_MAX)) (PreH7 : (cm_binding_valid p f scope slot )) (PreH8 : (cm_type_code_wf ty )) (PreH9 : (cm_expr_wf policy p f e )) (PreH10 : (cm_expr_counts_representable policy p fid_pre e )) (PreH11 : ((cm_rep_expr_kind (e)) = 2)) (PreH12 : (expr_pre <> 0)) (PreH13 : (0 <= lvalue_pre)) (PreH14 : (lvalue_pre <= 1)) (PreH15 : (e = (cm_simple_source_expr (simple)))) (PreH16 : (cm_simple_expr e )) (PreH17 : (cm_wf_program policy cg p )) (PreH18 : (cm_typed_program policy p )) (PreH19 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH20 : (cm_expr_wf policy p f e )) (PreH21 : (cm_expr_counts_representable policy p fid_pre e )) (PreH22 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH23 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH24 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH25 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH26 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH27 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH28 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH29 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_var_code_for (policy) (p) (fid_pre) (scope) (slot) (ty) (lvalue_pre))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
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
  &&  “ (e = (cm_simple_source_expr (simple))) ” 
  &&  “ (cm_simple_expr e ) ” 
  &&  “ (e = (CMVarE (scope) (slot) (ty))) ” 
  &&  “ (simple = (CMSimpleVar (scope) (slot) (ty))) ” 
  &&  “ (0 <= slot) ” 
  &&  “ (slot <= INT_MAX) ” 
  &&  “ (cm_binding_valid p f scope slot ) ” 
  &&  “ (cm_type_code_wf ty ) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ ((cm_rep_expr_kind (e)) = 2) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (e = (cm_simple_source_expr (simple))) ” 
  &&  “ (cm_simple_expr e ) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_var_code_for (policy) (p) (fid_pre) (scope) (slot) (ty) (lvalue_pre))) (tail)) )
.

Definition cm_emit_simple_expr_partial_solve_wit_4 := cm_emit_simple_expr_partial_solve_wit_4_pure -> cm_emit_simple_expr_partial_solve_wit_4_aux.

Definition cm_emit_simple_expr_partial_solve_wit_5_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (simple: cm_simple_view) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (xb: Z) (xa: Z) (PreH1 : ((cm_rep_expr_kind (e)) <> 2)) (PreH2 : (expr_pre <> 0)) (PreH3 : (0 <= lvalue_pre)) (PreH4 : (lvalue_pre <= 1)) (PreH5 : (e = (cm_simple_source_expr (simple)))) (PreH6 : (cm_simple_expr e )) (PreH7 : (cm_wf_program policy cg p )) (PreH8 : (cm_typed_program policy p )) (PreH9 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH10 : (cm_expr_wf policy p f e )) (PreH11 : (cm_expr_counts_representable policy p fid_pre e )) (PreH12 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH13 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH14 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH15 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH16 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH17 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH18 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH19 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> xa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> xb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_expr_payload e xa xb xargs )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_simple_code_for (policy) (p) (fid_pre) (simple) (lvalue_pre))) (tail)) )
|--
  “ (e = (cm_simple_source_expr (simple))) ” 
  &&  “ (cm_simple_expr e ) ” 
  &&  “ ((cm_rep_expr_kind (e)) <> 2) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ”
.

Definition cm_emit_simple_expr_partial_solve_wit_5_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (simple: cm_simple_view) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (xb: Z) (xa: Z) (PreH1 : ((cm_rep_expr_kind (e)) <> 2)) (PreH2 : (expr_pre <> 0)) (PreH3 : (0 <= lvalue_pre)) (PreH4 : (lvalue_pre <= 1)) (PreH5 : (e = (cm_simple_source_expr (simple)))) (PreH6 : (cm_simple_expr e )) (PreH7 : (cm_wf_program policy cg p )) (PreH8 : (cm_typed_program policy p )) (PreH9 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH10 : (cm_expr_wf policy p f e )) (PreH11 : (cm_expr_counts_representable policy p fid_pre e )) (PreH12 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH13 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH14 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH15 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH16 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH17 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH18 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH19 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> xa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> xb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_expr_payload e xa xb xargs )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_simple_code_for (policy) (p) (fid_pre) (simple) (lvalue_pre))) (tail)) )
|--
  “ (e = (cm_simple_source_expr (simple))) ” 
  &&  “ (cm_simple_expr e ) ” 
  &&  “ ((cm_rep_expr_kind (e)) <> 2) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ ((cm_rep_expr_kind (e)) <> 2) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (e = (cm_simple_source_expr (simple))) ” 
  &&  “ (cm_simple_expr e ) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_simple_code_for (policy) (p) (fid_pre) (simple) (lvalue_pre))) (tail)) )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> xa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> xb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_expr_payload e xa xb xargs )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
.

Definition cm_emit_simple_expr_partial_solve_wit_5 := cm_emit_simple_expr_partial_solve_wit_5_pure -> cm_emit_simple_expr_partial_solve_wit_5_aux.

Definition cm_emit_simple_expr_partial_solve_wit_6_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (simple: cm_simple_view) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (xb: Z) (xa: Z) (leaf: cm_leaf_expr) (PreH1 : (e = (cm_simple_source_expr (simple)))) (PreH2 : (cm_simple_expr e )) (PreH3 : (e = (cm_leaf_source_expr (leaf)))) (PreH4 : (simple = (CMSimpleLeaf (leaf)))) (PreH5 : (cm_dispatch_leaf e )) (PreH6 : (cm_expr_wf policy p f e )) (PreH7 : (cm_expr_counts_representable policy p fid_pre e )) (PreH8 : ((cm_rep_expr_kind (e)) <> 2)) (PreH9 : (expr_pre <> 0)) (PreH10 : (0 <= lvalue_pre)) (PreH11 : (lvalue_pre <= 1)) (PreH12 : (e = (cm_simple_source_expr (simple)))) (PreH13 : (cm_simple_expr e )) (PreH14 : (cm_wf_program policy cg p )) (PreH15 : (cm_typed_program policy p )) (PreH16 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH17 : (cm_expr_wf policy p f e )) (PreH18 : (cm_expr_counts_representable policy p fid_pre e )) (PreH19 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH20 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH21 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH22 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH23 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH24 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH25 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH26 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) (leaf) (lvalue_pre))) (tail)) )
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> xa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> xb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_expr_payload e xa xb xargs )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
|--
  “ (expr_pre <> 0) ”
.

Definition cm_emit_simple_expr_partial_solve_wit_6_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (simple: cm_simple_view) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (xb: Z) (xa: Z) (leaf: cm_leaf_expr) (PreH1 : (e = (cm_simple_source_expr (simple)))) (PreH2 : (cm_simple_expr e )) (PreH3 : (e = (cm_leaf_source_expr (leaf)))) (PreH4 : (simple = (CMSimpleLeaf (leaf)))) (PreH5 : (cm_dispatch_leaf e )) (PreH6 : (cm_expr_wf policy p f e )) (PreH7 : (cm_expr_counts_representable policy p fid_pre e )) (PreH8 : ((cm_rep_expr_kind (e)) <> 2)) (PreH9 : (expr_pre <> 0)) (PreH10 : (0 <= lvalue_pre)) (PreH11 : (lvalue_pre <= 1)) (PreH12 : (e = (cm_simple_source_expr (simple)))) (PreH13 : (cm_simple_expr e )) (PreH14 : (cm_wf_program policy cg p )) (PreH15 : (cm_typed_program policy p )) (PreH16 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH17 : (cm_expr_wf policy p f e )) (PreH18 : (cm_expr_counts_representable policy p fid_pre e )) (PreH19 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH20 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH21 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH22 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH23 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH24 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH25 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH26 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) (leaf) (lvalue_pre))) (tail)) )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> xa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> xb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_expr_payload e xa xb xargs )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
|--
  “ (expr_pre <> 0) ” 
  &&  “ (e = (cm_simple_source_expr (simple))) ” 
  &&  “ (cm_simple_expr e ) ” 
  &&  “ (e = (cm_leaf_source_expr (leaf))) ” 
  &&  “ (simple = (CMSimpleLeaf (leaf))) ” 
  &&  “ (cm_dispatch_leaf e ) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ ((cm_rep_expr_kind (e)) <> 2) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (e = (cm_simple_source_expr (simple))) ” 
  &&  “ (cm_simple_expr e ) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ”
  &&  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> xa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> xb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_expr_payload e xa xb xargs )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) (leaf) (lvalue_pre))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
.

Definition cm_emit_simple_expr_partial_solve_wit_6 := cm_emit_simple_expr_partial_solve_wit_6_pure -> cm_emit_simple_expr_partial_solve_wit_6_aux.

Definition cm_emit_simple_expr_partial_solve_wit_7_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (simple: cm_simple_view) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (leaf: cm_leaf_expr) (PreH1 : (e = (cm_simple_source_expr (simple)))) (PreH2 : (cm_simple_expr e )) (PreH3 : (e = (cm_leaf_source_expr (leaf)))) (PreH4 : (simple = (CMSimpleLeaf (leaf)))) (PreH5 : (cm_dispatch_leaf e )) (PreH6 : (cm_expr_wf policy p f e )) (PreH7 : (cm_expr_counts_representable policy p fid_pre e )) (PreH8 : ((cm_rep_expr_kind (e)) <> 2)) (PreH9 : (expr_pre <> 0)) (PreH10 : (0 <= lvalue_pre)) (PreH11 : (lvalue_pre <= 1)) (PreH12 : (e = (cm_simple_source_expr (simple)))) (PreH13 : (cm_simple_expr e )) (PreH14 : (cm_wf_program policy cg p )) (PreH15 : (cm_typed_program policy p )) (PreH16 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH17 : (cm_expr_wf policy p f e )) (PreH18 : (cm_expr_counts_representable policy p fid_pre e )) (PreH19 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH20 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH21 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH22 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH23 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH24 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH25 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH26 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  (cm_expr_rep expr_pre e )
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) (leaf) (lvalue_pre))) (tail)) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
|--
  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (e = (cm_leaf_source_expr (leaf))) ” 
  &&  “ (cm_dispatch_leaf e ) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre (cm_simple_source_expr (simple)) ) ” 
  &&  “ (cm_expr_wf policy p f (cm_simple_source_expr (simple)) ) ”
.

Definition cm_emit_simple_expr_partial_solve_wit_7_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (simple: cm_simple_view) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (leaf: cm_leaf_expr) (PreH1 : (e = (cm_simple_source_expr (simple)))) (PreH2 : (cm_simple_expr e )) (PreH3 : (e = (cm_leaf_source_expr (leaf)))) (PreH4 : (simple = (CMSimpleLeaf (leaf)))) (PreH5 : (cm_dispatch_leaf e )) (PreH6 : (cm_expr_wf policy p f e )) (PreH7 : (cm_expr_counts_representable policy p fid_pre e )) (PreH8 : ((cm_rep_expr_kind (e)) <> 2)) (PreH9 : (expr_pre <> 0)) (PreH10 : (0 <= lvalue_pre)) (PreH11 : (lvalue_pre <= 1)) (PreH12 : (e = (cm_simple_source_expr (simple)))) (PreH13 : (cm_simple_expr e )) (PreH14 : (cm_wf_program policy cg p )) (PreH15 : (cm_typed_program policy p )) (PreH16 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH17 : (cm_expr_wf policy p f e )) (PreH18 : (cm_expr_counts_representable policy p fid_pre e )) (PreH19 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH20 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH21 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH22 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH23 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH24 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH25 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH26 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) (leaf) (lvalue_pre))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
|--
  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (e = (cm_leaf_source_expr (leaf))) ” 
  &&  “ (cm_dispatch_leaf e ) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre (cm_simple_source_expr (simple)) ) ” 
  &&  “ (cm_expr_wf policy p f (cm_simple_source_expr (simple)) ) ” 
  &&  “ (e = (cm_simple_source_expr (simple))) ” 
  &&  “ (cm_simple_expr e ) ” 
  &&  “ (e = (cm_leaf_source_expr (leaf))) ” 
  &&  “ (simple = (CMSimpleLeaf (leaf))) ” 
  &&  “ (cm_dispatch_leaf e ) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ ((cm_rep_expr_kind (e)) <> 2) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (e = (cm_simple_source_expr (simple))) ” 
  &&  “ (cm_simple_expr e ) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) (leaf) (lvalue_pre))) (tail)) )
.

Definition cm_emit_simple_expr_partial_solve_wit_7 := cm_emit_simple_expr_partial_solve_wit_7_pure -> cm_emit_simple_expr_partial_solve_wit_7_aux.

Definition cm_emit_simple_expr_which_implies_wit_1 := 
(
forall (e: cm_expr) (expr: Z) ,
  (cm_expr_rep expr e )
|--
  EX (xargs: Z)  (xb: Z)  (xa: Z) ,
  “ (expr <> 0) ”
  &&  ((&((expr)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr)  # "cm_expr" ->ₛ "a")) # Ptr  |-> xa)
  **  ((&((expr)  # "cm_expr" ->ₛ "b")) # Ptr  |-> xb)
  **  ((&((expr)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_expr_payload e xa xb xargs )
) \/
(
forall (e: cm_expr) (expr: Z) ,
  (cm_expr_rep expr e )
|--
  EX (xargs: Z)  (xb: Z)  (xa: Z) ,
  “ (expr <> 0) ”
  &&  ((&((expr)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr)  # "cm_expr" ->ₛ "a")) # Ptr  |-> xa)
  **  ((&((expr)  # "cm_expr" ->ₛ "b")) # Ptr  |-> xb)
  **  ((&((expr)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_expr_payload e xa xb xargs )
).

Definition cm_emit_simple_expr_which_implies_wit_2 := 
(
forall (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (simple: cm_simple_view) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (fid: Z) (lvalue: Z) (emitter: Z) (PreH1 : (e = (cm_simple_source_expr (simple)))) (PreH2 : (cm_simple_expr e )) (PreH3 : ((cm_rep_expr_kind (e)) = 2)) (PreH4 : (cm_expr_wf policy p f e )) (PreH5 : (cm_expr_counts_representable policy p fid e )) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_simple_code_for (policy) (p) (fid) (simple) (lvalue))) (tail)) )
|--
  EX (scope: Z)  (slot: Z)  (ty: cm_type) ,
  “ (e = (cm_simple_source_expr (simple))) ” 
  &&  “ (cm_simple_expr e ) ” 
  &&  “ (e = (CMVarE (scope) (slot) (ty))) ” 
  &&  “ (simple = (CMSimpleVar (scope) (slot) (ty))) ” 
  &&  “ (0 <= slot) ” 
  &&  “ (slot <= INT_MAX) ” 
  &&  “ (cm_binding_valid p f scope slot ) ” 
  &&  “ (cm_type_code_wf ty ) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid e ) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_var_code_for (policy) (p) (fid) (scope) (slot) (ty) (lvalue))) (tail)) )
) \/
(
forall (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (simple: cm_simple_view) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (fid: Z) (lvalue: Z) (emitter: Z) (PreH1 : (e = (cm_simple_source_expr (simple)))) (PreH2 : (cm_simple_expr e )) (PreH3 : ((cm_rep_expr_kind (e)) = 2)) (PreH4 : (cm_expr_wf policy p f e )) (PreH5 : (cm_expr_counts_representable policy p fid e )) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_simple_code_for (policy) (p) (fid) (simple) (lvalue))) (tail)) )
|--
  EX (scope: Z)  (slot: Z)  (ty: cm_type) ,
  “ (e = (cm_simple_source_expr (simple))) ” 
  &&  “ (cm_simple_expr e ) ” 
  &&  “ (e = (CMVarE (scope) (slot) (ty))) ” 
  &&  “ (simple = (CMSimpleVar (scope) (slot) (ty))) ” 
  &&  “ (0 <= slot) ” 
  &&  “ (slot <= INT_MAX) ” 
  &&  “ (cm_binding_valid p f scope slot ) ” 
  &&  “ (cm_type_code_wf ty ) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid e ) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_var_code_for (policy) (p) (fid) (scope) (slot) (ty) (lvalue))) (tail)) )
).

Definition cm_emit_simple_expr_which_implies_wit_3 := 
(
forall (e: cm_expr) (xargs: Z) (xb: Z) (xa: Z) (expr: Z) (PreH1 : (expr <> 0)) ,
  ((&((expr)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr)  # "cm_expr" ->ₛ "a")) # Ptr  |-> xa)
  **  ((&((expr)  # "cm_expr" ->ₛ "b")) # Ptr  |-> xb)
  **  ((&((expr)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_expr_payload e xa xb xargs )
|--
  (cm_expr_rep expr e )
) \/
(
forall (e: cm_expr) (xargs: Z) (xb: Z) (xa: Z) (expr: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (expr <> 0)) ,
  ((&((expr)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr)  # "cm_expr" ->ₛ "a")) # Ptr  |-> xa)
  **  ((&((expr)  # "cm_expr" ->ₛ "b")) # Ptr  |-> xb)
  **  ((&((expr)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_expr_payload e xa xb xargs )
|--
  (cm_expr_rep expr e )
).

Definition cm_emit_simple_expr_which_implies_wit_3_split_goal_spatial := 
forall (e: cm_expr) (xargs: Z) (xb: Z) (xa: Z) (expr: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (expr <> 0)) ,
  ((&((expr)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr)  # "cm_expr" ->ₛ "a")) # Ptr  |-> xa)
  **  ((&((expr)  # "cm_expr" ->ₛ "b")) # Ptr  |-> xb)
  **  ((&((expr)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_expr_payload e xa xb xargs )
|--
  (cm_expr_rep expr e )
.

Definition cm_emit_simple_expr_which_implies_wit_4 := 
(
forall (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (simple: cm_simple_view) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (fid: Z) (lvalue: Z) (emitter: Z) (PreH1 : (e = (cm_simple_source_expr (simple)))) (PreH2 : (cm_simple_expr e )) (PreH3 : ((cm_rep_expr_kind (e)) <> 2)) (PreH4 : (cm_expr_wf policy p f e )) (PreH5 : (cm_expr_counts_representable policy p fid e )) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_simple_code_for (policy) (p) (fid) (simple) (lvalue))) (tail)) )
|--
  EX (leaf: cm_leaf_expr) ,
  “ (e = (cm_simple_source_expr (simple))) ” 
  &&  “ (cm_simple_expr e ) ” 
  &&  “ (e = (cm_leaf_source_expr (leaf))) ” 
  &&  “ (simple = (CMSimpleLeaf (leaf))) ” 
  &&  “ (cm_dispatch_leaf e ) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid e ) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_leaf_code_for (p) (leaf) (lvalue))) (tail)) )
) \/
(
forall (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (simple: cm_simple_view) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (fid: Z) (lvalue: Z) (emitter: Z) (PreH1 : (e = (cm_simple_source_expr (simple)))) (PreH2 : (cm_simple_expr e )) (PreH3 : ((cm_rep_expr_kind (e)) <> 2)) (PreH4 : (cm_expr_wf policy p f e )) (PreH5 : (cm_expr_counts_representable policy p fid e )) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_simple_code_for (policy) (p) (fid) (simple) (lvalue))) (tail)) )
|--
  EX (leaf: cm_leaf_expr) ,
  “ (e = (cm_simple_source_expr (simple))) ” 
  &&  “ (cm_simple_expr e ) ” 
  &&  “ (e = (cm_leaf_source_expr (leaf))) ” 
  &&  “ (simple = (CMSimpleLeaf (leaf))) ” 
  &&  “ (cm_dispatch_leaf e ) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid e ) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_leaf_code_for (p) (leaf) (lvalue))) (tail)) )
).

Definition cm_emit_simple_expr_which_implies_wit_5 := 
(
forall (e: cm_expr) (xargs: Z) (xb: Z) (xa: Z) (expr: Z) (PreH1 : (expr <> 0)) ,
  ((&((expr)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr)  # "cm_expr" ->ₛ "a")) # Ptr  |-> xa)
  **  ((&((expr)  # "cm_expr" ->ₛ "b")) # Ptr  |-> xb)
  **  ((&((expr)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_expr_payload e xa xb xargs )
|--
  (cm_expr_rep expr e )
) \/
(
forall (e: cm_expr) (xargs: Z) (xb: Z) (xa: Z) (expr: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (expr <> 0)) ,
  ((&((expr)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr)  # "cm_expr" ->ₛ "a")) # Ptr  |-> xa)
  **  ((&((expr)  # "cm_expr" ->ₛ "b")) # Ptr  |-> xb)
  **  ((&((expr)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_expr_payload e xa xb xargs )
|--
  (cm_expr_rep expr e )
).

Definition cm_emit_simple_expr_which_implies_wit_5_split_goal_spatial := 
forall (e: cm_expr) (xargs: Z) (xb: Z) (xa: Z) (expr: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (expr <> 0)) ,
  ((&((expr)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr)  # "cm_expr" ->ₛ "a")) # Ptr  |-> xa)
  **  ((&((expr)  # "cm_expr" ->ₛ "b")) # Ptr  |-> xb)
  **  ((&((expr)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_expr_payload e xa xb xargs )
|--
  (cm_expr_rep expr e )
.

Module Type VC_Correct.


Axiom proof_of_cm_emit_simple_expr_safety_wit_1 : cm_emit_simple_expr_safety_wit_1.
Axiom proof_of_cm_emit_simple_expr_return_wit_1 : cm_emit_simple_expr_return_wit_1.
Axiom proof_of_cm_emit_simple_expr_return_wit_2 : cm_emit_simple_expr_return_wit_2.
Axiom proof_of_cm_emit_simple_expr_partial_solve_wit_1 : cm_emit_simple_expr_partial_solve_wit_1.
Axiom proof_of_cm_emit_simple_expr_partial_solve_wit_2_pure : cm_emit_simple_expr_partial_solve_wit_2_pure.
Axiom proof_of_cm_emit_simple_expr_partial_solve_wit_2 : cm_emit_simple_expr_partial_solve_wit_2.
Axiom proof_of_cm_emit_simple_expr_partial_solve_wit_3_pure : cm_emit_simple_expr_partial_solve_wit_3_pure.
Axiom proof_of_cm_emit_simple_expr_partial_solve_wit_3 : cm_emit_simple_expr_partial_solve_wit_3.
Axiom proof_of_cm_emit_simple_expr_partial_solve_wit_4_pure : cm_emit_simple_expr_partial_solve_wit_4_pure.
Axiom proof_of_cm_emit_simple_expr_partial_solve_wit_4 : cm_emit_simple_expr_partial_solve_wit_4.
Axiom proof_of_cm_emit_simple_expr_partial_solve_wit_5_pure : cm_emit_simple_expr_partial_solve_wit_5_pure.
Axiom proof_of_cm_emit_simple_expr_partial_solve_wit_5 : cm_emit_simple_expr_partial_solve_wit_5.
Axiom proof_of_cm_emit_simple_expr_partial_solve_wit_6_pure : cm_emit_simple_expr_partial_solve_wit_6_pure.
Axiom proof_of_cm_emit_simple_expr_partial_solve_wit_6 : cm_emit_simple_expr_partial_solve_wit_6.
Axiom proof_of_cm_emit_simple_expr_partial_solve_wit_7_pure : cm_emit_simple_expr_partial_solve_wit_7_pure.
Axiom proof_of_cm_emit_simple_expr_partial_solve_wit_7 : cm_emit_simple_expr_partial_solve_wit_7.
Axiom proof_of_cm_emit_simple_expr_which_implies_wit_1 : cm_emit_simple_expr_which_implies_wit_1.
Axiom proof_of_cm_emit_simple_expr_which_implies_wit_2 : cm_emit_simple_expr_which_implies_wit_2.
Axiom proof_of_cm_emit_simple_expr_which_implies_wit_3 : cm_emit_simple_expr_which_implies_wit_3.
Axiom proof_of_cm_emit_simple_expr_which_implies_wit_4 : cm_emit_simple_expr_which_implies_wit_4.
Axiom proof_of_cm_emit_simple_expr_which_implies_wit_5 : cm_emit_simple_expr_which_implies_wit_5.

End VC_Correct.
