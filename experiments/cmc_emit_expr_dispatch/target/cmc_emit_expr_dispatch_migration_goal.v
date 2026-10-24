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
Require Import SimpleC.EE.QCP_demos_human.cmc_emit_expr_dispatch_migration_lib.
Local Open Scope sac.

(*----- Function cm_emit_leaf_expr -----*)

Definition cm_emit_leaf_expr_safety_wit_1 := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (xb: Z) (xa: Z) (PreH1 : (expr_pre <> 0)) (PreH2 : (0 <= lvalue_pre)) (PreH3 : (lvalue_pre <= 1)) (PreH4 : (e = (cm_leaf_source_expr (leaf)))) (PreH5 : (cm_dispatch_leaf e )) (PreH6 : (cm_wf_program policy cg p )) (PreH7 : (cm_typed_program policy p )) (PreH8 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH9 : (cm_expr_wf policy p f e )) (PreH10 : (cm_expr_counts_representable policy p fid_pre e )) (PreH11 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH12 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH13 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH14 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
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
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) (leaf) (lvalue_pre))) (tail)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_emit_leaf_expr_safety_wit_2 := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (xb: Z) (xa: Z) (PreH1 : ((cm_rep_expr_kind (e)) <> 0)) (PreH2 : (expr_pre <> 0)) (PreH3 : (0 <= lvalue_pre)) (PreH4 : (lvalue_pre <= 1)) (PreH5 : (e = (cm_leaf_source_expr (leaf)))) (PreH6 : (cm_dispatch_leaf e )) (PreH7 : (cm_wf_program policy cg p )) (PreH8 : (cm_typed_program policy p )) (PreH9 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH10 : (cm_expr_wf policy p f e )) (PreH11 : (cm_expr_counts_representable policy p fid_pre e )) (PreH12 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH13 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH14 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH15 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
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
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) (leaf) (lvalue_pre))) (tail)) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cm_emit_leaf_expr_safety_wit_3 := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (xb: Z) (xa: Z) (PreH1 : ((cm_rep_expr_kind (e)) <> 1)) (PreH2 : ((cm_rep_expr_kind (e)) <> 0)) (PreH3 : (expr_pre <> 0)) (PreH4 : (0 <= lvalue_pre)) (PreH5 : (lvalue_pre <= 1)) (PreH6 : (e = (cm_leaf_source_expr (leaf)))) (PreH7 : (cm_dispatch_leaf e )) (PreH8 : (cm_wf_program policy cg p )) (PreH9 : (cm_typed_program policy p )) (PreH10 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH11 : (cm_expr_wf policy p f e )) (PreH12 : (cm_expr_counts_representable policy p fid_pre e )) (PreH13 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH14 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH15 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH16 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
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
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) (leaf) (lvalue_pre))) (tail)) )
|--
  “ (9 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 9) ”
.

Definition cm_emit_leaf_expr_return_wit_1 := 
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (n: Z) (ty: cm_type) (PreH1 : (0 <= lvalue_pre)) (PreH2 : (lvalue_pre <= 1)) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (e = (CMConstE (n) (ty)))) (PreH5 : (cm_type_code_wf ty )) (PreH6 : (e = (CMConstE (n) (ty)))) (PreH7 : (e = (cm_leaf_source_expr (leaf)))) (PreH8 : (cm_dispatch_leaf e )) (PreH9 : (leaf = (CMLeafConst (n) (ty)))) (PreH10 : (cm_type_code_wf ty )) (PreH11 : (cm_expr_wf policy p f e )) (PreH12 : (cm_expr_counts_representable policy p fid_pre e )) (PreH13 : ((cm_rep_expr_kind (e)) = 0)) (PreH14 : (expr_pre <> 0)) (PreH15 : (0 <= lvalue_pre)) (PreH16 : (lvalue_pre <= 1)) (PreH17 : (e = (cm_leaf_source_expr (leaf)))) (PreH18 : (cm_dispatch_leaf e )) (PreH19 : (cm_wf_program policy cg p )) (PreH20 : (cm_typed_program policy p )) (PreH21 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH22 : (cm_expr_wf policy p f e )) (PreH23 : (cm_expr_counts_representable policy p fid_pre e )) (PreH24 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH25 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH26 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH27 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_leaf_code_for (p) ((CMLeafConst (n) (ty))) (lvalue_pre)))) tail )
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
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_leaf_code_for (p) (leaf) (lvalue_pre)))) tail )
) \/
(
forall (lvalue_pre: Z) (expr_pre: Z) (fid_pre: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (n: Z) (ty: cm_type) (PreH1 : (0 <= lvalue_pre)) (PreH2 : (lvalue_pre <= 1)) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (e = (CMConstE (n) (ty)))) (PreH5 : (cm_type_code_wf ty )) (PreH6 : (e = (CMConstE (n) (ty)))) (PreH7 : (e = (cm_leaf_source_expr (leaf)))) (PreH8 : (cm_dispatch_leaf e )) (PreH9 : (leaf = (CMLeafConst (n) (ty)))) (PreH10 : (cm_type_code_wf ty )) (PreH11 : (cm_expr_wf policy p f e )) (PreH12 : (cm_expr_counts_representable policy p fid_pre e )) (PreH13 : ((cm_rep_expr_kind (e)) = 0)) (PreH14 : (expr_pre <> 0)) (PreH15 : (0 <= lvalue_pre)) (PreH16 : (lvalue_pre <= 1)) (PreH17 : (e = (cm_leaf_source_expr (leaf)))) (PreH18 : (cm_dispatch_leaf e )) (PreH19 : (cm_wf_program policy cg p )) (PreH20 : (cm_typed_program policy p )) (PreH21 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH22 : (cm_expr_wf policy p f e )) (PreH23 : (cm_expr_counts_representable policy p fid_pre e )) (PreH24 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH25 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH26 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH27 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  TT && emp 
|--
  “ (e = (cm_leaf_source_expr (leaf))) ”
  &&  emp
).

Definition cm_emit_leaf_expr_return_wit_1_split_goal_1 := 
forall (lvalue_pre: Z) (expr_pre: Z) (fid_pre: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (n: Z) (ty: cm_type) (PreH1 : (0 <= lvalue_pre)) (PreH2 : (lvalue_pre <= 1)) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (e = (CMConstE (n) (ty)))) (PreH5 : (cm_type_code_wf ty )) (PreH6 : (e = (CMConstE (n) (ty)))) (PreH7 : (e = (cm_leaf_source_expr (leaf)))) (PreH8 : (cm_dispatch_leaf e )) (PreH9 : (leaf = (CMLeafConst (n) (ty)))) (PreH10 : (cm_type_code_wf ty )) (PreH11 : (cm_expr_wf policy p f e )) (PreH12 : (cm_expr_counts_representable policy p fid_pre e )) (PreH13 : ((cm_rep_expr_kind (e)) = 0)) (PreH14 : (expr_pre <> 0)) (PreH15 : (0 <= lvalue_pre)) (PreH16 : (lvalue_pre <= 1)) (PreH17 : (e = (cm_leaf_source_expr (leaf)))) (PreH18 : (cm_dispatch_leaf e )) (PreH19 : (cm_wf_program policy cg p )) (PreH20 : (cm_typed_program policy p )) (PreH21 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH22 : (cm_expr_wf policy p f e )) (PreH23 : (cm_expr_counts_representable policy p fid_pre e )) (PreH24 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH25 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH26 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH27 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (e = (cm_leaf_source_expr (leaf)))
.

Definition cm_emit_leaf_expr_return_wit_2 := 
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sid: Z) (ty: cm_type) (PreH1 : (0 <= lvalue_pre)) (PreH2 : (lvalue_pre <= 1)) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (e = (CMStringE (sid) (ty)))) (PreH5 : (0 <= sid)) (PreH6 : (sid <= INT_MAX)) (PreH7 : (cm_typed_program policy p )) (PreH8 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH9 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH10 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH11 : (e = (CMStringE (sid) (ty)))) (PreH12 : (e = (cm_leaf_source_expr (leaf)))) (PreH13 : (cm_dispatch_leaf e )) (PreH14 : (leaf = (CMLeafString (sid) (ty)))) (PreH15 : (0 <= sid)) (PreH16 : (sid <= INT_MAX)) (PreH17 : (cm_expr_wf policy p f e )) (PreH18 : (cm_expr_counts_representable policy p fid_pre e )) (PreH19 : ((cm_rep_expr_kind (e)) = 1)) (PreH20 : ((cm_rep_expr_kind (e)) <> 0)) (PreH21 : (expr_pre <> 0)) (PreH22 : (0 <= lvalue_pre)) (PreH23 : (lvalue_pre <= 1)) (PreH24 : (e = (cm_leaf_source_expr (leaf)))) (PreH25 : (cm_dispatch_leaf e )) (PreH26 : (cm_wf_program policy cg p )) (PreH27 : (cm_typed_program policy p )) (PreH28 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH29 : (cm_expr_wf policy p f e )) (PreH30 : (cm_expr_counts_representable policy p fid_pre e )) (PreH31 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH32 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH33 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH34 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_leaf_code_for (p) ((CMLeafString (sid) (ty))) (lvalue_pre)))) tail )
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
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_leaf_code_for (p) (leaf) (lvalue_pre)))) tail )
) \/
(
forall (lvalue_pre: Z) (expr_pre: Z) (fid_pre: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sid: Z) (ty: cm_type) (PreH1 : (0 <= lvalue_pre)) (PreH2 : (lvalue_pre <= 1)) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (e = (CMStringE (sid) (ty)))) (PreH5 : (0 <= sid)) (PreH6 : (sid <= INT_MAX)) (PreH7 : (cm_typed_program policy p )) (PreH8 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH9 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH10 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH11 : (e = (CMStringE (sid) (ty)))) (PreH12 : (e = (cm_leaf_source_expr (leaf)))) (PreH13 : (cm_dispatch_leaf e )) (PreH14 : (leaf = (CMLeafString (sid) (ty)))) (PreH15 : (0 <= sid)) (PreH16 : (sid <= INT_MAX)) (PreH17 : (cm_expr_wf policy p f e )) (PreH18 : (cm_expr_counts_representable policy p fid_pre e )) (PreH19 : ((cm_rep_expr_kind (e)) = 1)) (PreH20 : ((cm_rep_expr_kind (e)) <> 0)) (PreH21 : (expr_pre <> 0)) (PreH22 : (0 <= lvalue_pre)) (PreH23 : (lvalue_pre <= 1)) (PreH24 : (e = (cm_leaf_source_expr (leaf)))) (PreH25 : (cm_dispatch_leaf e )) (PreH26 : (cm_wf_program policy cg p )) (PreH27 : (cm_typed_program policy p )) (PreH28 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH29 : (cm_expr_wf policy p f e )) (PreH30 : (cm_expr_counts_representable policy p fid_pre e )) (PreH31 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH32 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH33 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH34 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  TT && emp 
|--
  “ (e = (cm_leaf_source_expr (leaf))) ”
  &&  emp
).

Definition cm_emit_leaf_expr_return_wit_2_split_goal_1 := 
forall (lvalue_pre: Z) (expr_pre: Z) (fid_pre: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sid: Z) (ty: cm_type) (PreH1 : (0 <= lvalue_pre)) (PreH2 : (lvalue_pre <= 1)) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (e = (CMStringE (sid) (ty)))) (PreH5 : (0 <= sid)) (PreH6 : (sid <= INT_MAX)) (PreH7 : (cm_typed_program policy p )) (PreH8 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH9 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH10 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH11 : (e = (CMStringE (sid) (ty)))) (PreH12 : (e = (cm_leaf_source_expr (leaf)))) (PreH13 : (cm_dispatch_leaf e )) (PreH14 : (leaf = (CMLeafString (sid) (ty)))) (PreH15 : (0 <= sid)) (PreH16 : (sid <= INT_MAX)) (PreH17 : (cm_expr_wf policy p f e )) (PreH18 : (cm_expr_counts_representable policy p fid_pre e )) (PreH19 : ((cm_rep_expr_kind (e)) = 1)) (PreH20 : ((cm_rep_expr_kind (e)) <> 0)) (PreH21 : (expr_pre <> 0)) (PreH22 : (0 <= lvalue_pre)) (PreH23 : (lvalue_pre <= 1)) (PreH24 : (e = (cm_leaf_source_expr (leaf)))) (PreH25 : (cm_dispatch_leaf e )) (PreH26 : (cm_wf_program policy cg p )) (PreH27 : (cm_typed_program policy p )) (PreH28 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH29 : (cm_expr_wf policy p f e )) (PreH30 : (cm_expr_counts_representable policy p fid_pre e )) (PreH31 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH32 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH33 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH34 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (e = (cm_leaf_source_expr (leaf)))
.

Definition cm_emit_leaf_expr_return_wit_3 := 
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (asked: cm_type) (ty: cm_type) (PreH1 : (0 <= lvalue_pre)) (PreH2 : (lvalue_pre <= 1)) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (e = (CMSizeofE (asked) (ty)))) (PreH5 : (cm_typed_program policy p )) (PreH6 : (cm_type_code_wf asked )) (PreH7 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH8 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH9 : (e = (CMSizeofE (asked) (ty)))) (PreH10 : (e = (cm_leaf_source_expr (leaf)))) (PreH11 : (cm_dispatch_leaf e )) (PreH12 : (leaf = (CMLeafSizeof (asked) (ty)))) (PreH13 : (cm_type_code_wf asked )) (PreH14 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH15 : (cm_expr_wf policy p f e )) (PreH16 : (cm_expr_counts_representable policy p fid_pre e )) (PreH17 : ((cm_rep_expr_kind (e)) = 9)) (PreH18 : ((cm_rep_expr_kind (e)) <> 1)) (PreH19 : ((cm_rep_expr_kind (e)) <> 0)) (PreH20 : (expr_pre <> 0)) (PreH21 : (0 <= lvalue_pre)) (PreH22 : (lvalue_pre <= 1)) (PreH23 : (e = (cm_leaf_source_expr (leaf)))) (PreH24 : (cm_dispatch_leaf e )) (PreH25 : (cm_wf_program policy cg p )) (PreH26 : (cm_typed_program policy p )) (PreH27 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH28 : (cm_expr_wf policy p f e )) (PreH29 : (cm_expr_counts_representable policy p fid_pre e )) (PreH30 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH31 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH32 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH33 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_leaf_code_for (p) ((CMLeafSizeof (asked) (ty))) (lvalue_pre)))) tail )
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
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_leaf_code_for (p) (leaf) (lvalue_pre)))) tail )
) \/
(
forall (lvalue_pre: Z) (expr_pre: Z) (fid_pre: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (asked: cm_type) (ty: cm_type) (PreH1 : (0 <= lvalue_pre)) (PreH2 : (lvalue_pre <= 1)) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (e = (CMSizeofE (asked) (ty)))) (PreH5 : (cm_typed_program policy p )) (PreH6 : (cm_type_code_wf asked )) (PreH7 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH8 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH9 : (e = (CMSizeofE (asked) (ty)))) (PreH10 : (e = (cm_leaf_source_expr (leaf)))) (PreH11 : (cm_dispatch_leaf e )) (PreH12 : (leaf = (CMLeafSizeof (asked) (ty)))) (PreH13 : (cm_type_code_wf asked )) (PreH14 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH15 : (cm_expr_wf policy p f e )) (PreH16 : (cm_expr_counts_representable policy p fid_pre e )) (PreH17 : ((cm_rep_expr_kind (e)) = 9)) (PreH18 : ((cm_rep_expr_kind (e)) <> 1)) (PreH19 : ((cm_rep_expr_kind (e)) <> 0)) (PreH20 : (expr_pre <> 0)) (PreH21 : (0 <= lvalue_pre)) (PreH22 : (lvalue_pre <= 1)) (PreH23 : (e = (cm_leaf_source_expr (leaf)))) (PreH24 : (cm_dispatch_leaf e )) (PreH25 : (cm_wf_program policy cg p )) (PreH26 : (cm_typed_program policy p )) (PreH27 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH28 : (cm_expr_wf policy p f e )) (PreH29 : (cm_expr_counts_representable policy p fid_pre e )) (PreH30 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH31 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH32 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH33 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  TT && emp 
|--
  “ (e = (cm_leaf_source_expr (leaf))) ”
  &&  emp
).

Definition cm_emit_leaf_expr_return_wit_3_split_goal_1 := 
forall (lvalue_pre: Z) (expr_pre: Z) (fid_pre: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (asked: cm_type) (ty: cm_type) (PreH1 : (0 <= lvalue_pre)) (PreH2 : (lvalue_pre <= 1)) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (e = (CMSizeofE (asked) (ty)))) (PreH5 : (cm_typed_program policy p )) (PreH6 : (cm_type_code_wf asked )) (PreH7 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH8 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH9 : (e = (CMSizeofE (asked) (ty)))) (PreH10 : (e = (cm_leaf_source_expr (leaf)))) (PreH11 : (cm_dispatch_leaf e )) (PreH12 : (leaf = (CMLeafSizeof (asked) (ty)))) (PreH13 : (cm_type_code_wf asked )) (PreH14 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH15 : (cm_expr_wf policy p f e )) (PreH16 : (cm_expr_counts_representable policy p fid_pre e )) (PreH17 : ((cm_rep_expr_kind (e)) = 9)) (PreH18 : ((cm_rep_expr_kind (e)) <> 1)) (PreH19 : ((cm_rep_expr_kind (e)) <> 0)) (PreH20 : (expr_pre <> 0)) (PreH21 : (0 <= lvalue_pre)) (PreH22 : (lvalue_pre <= 1)) (PreH23 : (e = (cm_leaf_source_expr (leaf)))) (PreH24 : (cm_dispatch_leaf e )) (PreH25 : (cm_wf_program policy cg p )) (PreH26 : (cm_typed_program policy p )) (PreH27 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH28 : (cm_expr_wf policy p f e )) (PreH29 : (cm_expr_counts_representable policy p fid_pre e )) (PreH30 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH31 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH32 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH33 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (e = (cm_leaf_source_expr (leaf)))
.

Definition cm_emit_leaf_expr_return_wit_4 := 
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (ty: cm_type) (PreH1 : (0 <= lvalue_pre)) (PreH2 : (lvalue_pre <= 1)) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (e = (CMGetcE (ty)))) (PreH5 : (e = (CMGetcE (ty)))) (PreH6 : (e = (cm_leaf_source_expr (leaf)))) (PreH7 : (cm_dispatch_leaf e )) (PreH8 : (leaf = (CMLeafGetc (ty)))) (PreH9 : (cm_dispatch_leaf e )) (PreH10 : (cm_expr_wf policy p f e )) (PreH11 : (cm_expr_counts_representable policy p fid_pre e )) (PreH12 : ((cm_rep_expr_kind (e)) <> 9)) (PreH13 : ((cm_rep_expr_kind (e)) <> 1)) (PreH14 : ((cm_rep_expr_kind (e)) <> 0)) (PreH15 : (expr_pre <> 0)) (PreH16 : (0 <= lvalue_pre)) (PreH17 : (lvalue_pre <= 1)) (PreH18 : (e = (cm_leaf_source_expr (leaf)))) (PreH19 : (cm_dispatch_leaf e )) (PreH20 : (cm_wf_program policy cg p )) (PreH21 : (cm_typed_program policy p )) (PreH22 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH23 : (cm_expr_wf policy p f e )) (PreH24 : (cm_expr_counts_representable policy p fid_pre e )) (PreH25 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH26 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH27 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH28 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_leaf_code_for (p) ((CMLeafGetc (ty))) (lvalue_pre)))) tail )
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
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_leaf_code_for (p) (leaf) (lvalue_pre)))) tail )
) \/
(
forall (lvalue_pre: Z) (expr_pre: Z) (fid_pre: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (ty: cm_type) (PreH1 : (0 <= lvalue_pre)) (PreH2 : (lvalue_pre <= 1)) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (e = (CMGetcE (ty)))) (PreH5 : (e = (CMGetcE (ty)))) (PreH6 : (e = (cm_leaf_source_expr (leaf)))) (PreH7 : (cm_dispatch_leaf e )) (PreH8 : (leaf = (CMLeafGetc (ty)))) (PreH9 : (cm_dispatch_leaf e )) (PreH10 : (cm_expr_wf policy p f e )) (PreH11 : (cm_expr_counts_representable policy p fid_pre e )) (PreH12 : ((cm_rep_expr_kind (e)) <> 9)) (PreH13 : ((cm_rep_expr_kind (e)) <> 1)) (PreH14 : ((cm_rep_expr_kind (e)) <> 0)) (PreH15 : (expr_pre <> 0)) (PreH16 : (0 <= lvalue_pre)) (PreH17 : (lvalue_pre <= 1)) (PreH18 : (e = (cm_leaf_source_expr (leaf)))) (PreH19 : (cm_dispatch_leaf e )) (PreH20 : (cm_wf_program policy cg p )) (PreH21 : (cm_typed_program policy p )) (PreH22 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH23 : (cm_expr_wf policy p f e )) (PreH24 : (cm_expr_counts_representable policy p fid_pre e )) (PreH25 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH26 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH27 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH28 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  TT && emp 
|--
  “ (e = (cm_leaf_source_expr (leaf))) ”
  &&  emp
).

Definition cm_emit_leaf_expr_return_wit_4_split_goal_1 := 
forall (lvalue_pre: Z) (expr_pre: Z) (fid_pre: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (ty: cm_type) (PreH1 : (0 <= lvalue_pre)) (PreH2 : (lvalue_pre <= 1)) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (e = (CMGetcE (ty)))) (PreH5 : (e = (CMGetcE (ty)))) (PreH6 : (e = (cm_leaf_source_expr (leaf)))) (PreH7 : (cm_dispatch_leaf e )) (PreH8 : (leaf = (CMLeafGetc (ty)))) (PreH9 : (cm_dispatch_leaf e )) (PreH10 : (cm_expr_wf policy p f e )) (PreH11 : (cm_expr_counts_representable policy p fid_pre e )) (PreH12 : ((cm_rep_expr_kind (e)) <> 9)) (PreH13 : ((cm_rep_expr_kind (e)) <> 1)) (PreH14 : ((cm_rep_expr_kind (e)) <> 0)) (PreH15 : (expr_pre <> 0)) (PreH16 : (0 <= lvalue_pre)) (PreH17 : (lvalue_pre <= 1)) (PreH18 : (e = (cm_leaf_source_expr (leaf)))) (PreH19 : (cm_dispatch_leaf e )) (PreH20 : (cm_wf_program policy cg p )) (PreH21 : (cm_typed_program policy p )) (PreH22 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH23 : (cm_expr_wf policy p f e )) (PreH24 : (cm_expr_counts_representable policy p fid_pre e )) (PreH25 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH26 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH27 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH28 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (e = (cm_leaf_source_expr (leaf)))
.

Definition cm_emit_leaf_expr_partial_solve_wit_1 := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (0 <= lvalue_pre)) (PreH2 : (lvalue_pre <= 1)) (PreH3 : (e = (cm_leaf_source_expr (leaf)))) (PreH4 : (cm_dispatch_leaf e )) (PreH5 : (cm_wf_program policy cg p )) (PreH6 : (cm_typed_program policy p )) (PreH7 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH8 : (cm_expr_wf policy p f e )) (PreH9 : (cm_expr_counts_representable policy p fid_pre e )) (PreH10 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH11 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH12 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH13 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) (leaf) (lvalue_pre))) (tail)) )
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
  &&  (cm_expr_rep expr_pre e )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) (leaf) (lvalue_pre))) (tail)) )
.

Definition cm_emit_leaf_expr_partial_solve_wit_2_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (xb: Z) (xa: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 0)) (PreH2 : (expr_pre <> 0)) (PreH3 : (0 <= lvalue_pre)) (PreH4 : (lvalue_pre <= 1)) (PreH5 : (e = (cm_leaf_source_expr (leaf)))) (PreH6 : (cm_dispatch_leaf e )) (PreH7 : (cm_wf_program policy cg p )) (PreH8 : (cm_typed_program policy p )) (PreH9 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH10 : (cm_expr_wf policy p f e )) (PreH11 : (cm_expr_counts_representable policy p fid_pre e )) (PreH12 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH13 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH14 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH15 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
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
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) (leaf) (lvalue_pre))) (tail)) )
|--
  “ (e = (cm_leaf_source_expr (leaf))) ” 
  &&  “ (cm_dispatch_leaf e ) ” 
  &&  “ ((cm_rep_expr_kind (e)) = 0) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ”
.

Definition cm_emit_leaf_expr_partial_solve_wit_2_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (xb: Z) (xa: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 0)) (PreH2 : (expr_pre <> 0)) (PreH3 : (0 <= lvalue_pre)) (PreH4 : (lvalue_pre <= 1)) (PreH5 : (e = (cm_leaf_source_expr (leaf)))) (PreH6 : (cm_dispatch_leaf e )) (PreH7 : (cm_wf_program policy cg p )) (PreH8 : (cm_typed_program policy p )) (PreH9 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH10 : (cm_expr_wf policy p f e )) (PreH11 : (cm_expr_counts_representable policy p fid_pre e )) (PreH12 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH13 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH14 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH15 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
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
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) (leaf) (lvalue_pre))) (tail)) )
|--
  “ (e = (cm_leaf_source_expr (leaf))) ” 
  &&  “ (cm_dispatch_leaf e ) ” 
  &&  “ ((cm_rep_expr_kind (e)) = 0) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ ((cm_rep_expr_kind (e)) = 0) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
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
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) (leaf) (lvalue_pre))) (tail)) )
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

Definition cm_emit_leaf_expr_partial_solve_wit_2 := cm_emit_leaf_expr_partial_solve_wit_2_pure -> cm_emit_leaf_expr_partial_solve_wit_2_aux.

Definition cm_emit_leaf_expr_partial_solve_wit_3_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (xb: Z) (xa: Z) (n: Z) (ty: cm_type) (PreH1 : (e = (CMConstE (n) (ty)))) (PreH2 : (e = (cm_leaf_source_expr (leaf)))) (PreH3 : (cm_dispatch_leaf e )) (PreH4 : (leaf = (CMLeafConst (n) (ty)))) (PreH5 : (cm_type_code_wf ty )) (PreH6 : (cm_expr_wf policy p f e )) (PreH7 : (cm_expr_counts_representable policy p fid_pre e )) (PreH8 : ((cm_rep_expr_kind (e)) = 0)) (PreH9 : (expr_pre <> 0)) (PreH10 : (0 <= lvalue_pre)) (PreH11 : (lvalue_pre <= 1)) (PreH12 : (e = (cm_leaf_source_expr (leaf)))) (PreH13 : (cm_dispatch_leaf e )) (PreH14 : (cm_wf_program policy cg p )) (PreH15 : (cm_typed_program policy p )) (PreH16 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH17 : (cm_expr_wf policy p f e )) (PreH18 : (cm_expr_counts_representable policy p fid_pre e )) (PreH19 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH20 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH21 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH22 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafConst (n) (ty))) (lvalue_pre))) (tail)) )
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

Definition cm_emit_leaf_expr_partial_solve_wit_3_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (xb: Z) (xa: Z) (n: Z) (ty: cm_type) (PreH1 : (e = (CMConstE (n) (ty)))) (PreH2 : (e = (cm_leaf_source_expr (leaf)))) (PreH3 : (cm_dispatch_leaf e )) (PreH4 : (leaf = (CMLeafConst (n) (ty)))) (PreH5 : (cm_type_code_wf ty )) (PreH6 : (cm_expr_wf policy p f e )) (PreH7 : (cm_expr_counts_representable policy p fid_pre e )) (PreH8 : ((cm_rep_expr_kind (e)) = 0)) (PreH9 : (expr_pre <> 0)) (PreH10 : (0 <= lvalue_pre)) (PreH11 : (lvalue_pre <= 1)) (PreH12 : (e = (cm_leaf_source_expr (leaf)))) (PreH13 : (cm_dispatch_leaf e )) (PreH14 : (cm_wf_program policy cg p )) (PreH15 : (cm_typed_program policy p )) (PreH16 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH17 : (cm_expr_wf policy p f e )) (PreH18 : (cm_expr_counts_representable policy p fid_pre e )) (PreH19 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH20 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH21 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH22 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafConst (n) (ty))) (lvalue_pre))) (tail)) )
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
  &&  “ (e = (CMConstE (n) (ty))) ” 
  &&  “ (e = (cm_leaf_source_expr (leaf))) ” 
  &&  “ (cm_dispatch_leaf e ) ” 
  &&  “ (leaf = (CMLeafConst (n) (ty))) ” 
  &&  “ (cm_type_code_wf ty ) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ ((cm_rep_expr_kind (e)) = 0) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
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
  &&  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> xa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> xb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_expr_payload e xa xb xargs )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafConst (n) (ty))) (lvalue_pre))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
.

Definition cm_emit_leaf_expr_partial_solve_wit_3 := cm_emit_leaf_expr_partial_solve_wit_3_pure -> cm_emit_leaf_expr_partial_solve_wit_3_aux.

Definition cm_emit_leaf_expr_partial_solve_wit_4_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (n: Z) (ty: cm_type) (PreH1 : (e = (CMConstE (n) (ty)))) (PreH2 : (e = (cm_leaf_source_expr (leaf)))) (PreH3 : (cm_dispatch_leaf e )) (PreH4 : (leaf = (CMLeafConst (n) (ty)))) (PreH5 : (cm_type_code_wf ty )) (PreH6 : (cm_expr_wf policy p f e )) (PreH7 : (cm_expr_counts_representable policy p fid_pre e )) (PreH8 : ((cm_rep_expr_kind (e)) = 0)) (PreH9 : (expr_pre <> 0)) (PreH10 : (0 <= lvalue_pre)) (PreH11 : (lvalue_pre <= 1)) (PreH12 : (e = (cm_leaf_source_expr (leaf)))) (PreH13 : (cm_dispatch_leaf e )) (PreH14 : (cm_wf_program policy cg p )) (PreH15 : (cm_typed_program policy p )) (PreH16 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH17 : (cm_expr_wf policy p f e )) (PreH18 : (cm_expr_counts_representable policy p fid_pre e )) (PreH19 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH20 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH21 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH22 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  (cm_expr_rep expr_pre e )
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafConst (n) (ty))) (lvalue_pre))) (tail)) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
|--
  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (e = (CMConstE (n) (ty))) ” 
  &&  “ (cm_type_code_wf ty ) ”
.

Definition cm_emit_leaf_expr_partial_solve_wit_4_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (n: Z) (ty: cm_type) (PreH1 : (e = (CMConstE (n) (ty)))) (PreH2 : (e = (cm_leaf_source_expr (leaf)))) (PreH3 : (cm_dispatch_leaf e )) (PreH4 : (leaf = (CMLeafConst (n) (ty)))) (PreH5 : (cm_type_code_wf ty )) (PreH6 : (cm_expr_wf policy p f e )) (PreH7 : (cm_expr_counts_representable policy p fid_pre e )) (PreH8 : ((cm_rep_expr_kind (e)) = 0)) (PreH9 : (expr_pre <> 0)) (PreH10 : (0 <= lvalue_pre)) (PreH11 : (lvalue_pre <= 1)) (PreH12 : (e = (cm_leaf_source_expr (leaf)))) (PreH13 : (cm_dispatch_leaf e )) (PreH14 : (cm_wf_program policy cg p )) (PreH15 : (cm_typed_program policy p )) (PreH16 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH17 : (cm_expr_wf policy p f e )) (PreH18 : (cm_expr_counts_representable policy p fid_pre e )) (PreH19 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH20 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH21 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH22 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafConst (n) (ty))) (lvalue_pre))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
|--
  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (e = (CMConstE (n) (ty))) ” 
  &&  “ (cm_type_code_wf ty ) ” 
  &&  “ (e = (CMConstE (n) (ty))) ” 
  &&  “ (e = (cm_leaf_source_expr (leaf))) ” 
  &&  “ (cm_dispatch_leaf e ) ” 
  &&  “ (leaf = (CMLeafConst (n) (ty))) ” 
  &&  “ (cm_type_code_wf ty ) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ ((cm_rep_expr_kind (e)) = 0) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
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
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafConst (n) (ty))) (lvalue_pre))) (tail)) )
.

Definition cm_emit_leaf_expr_partial_solve_wit_4 := cm_emit_leaf_expr_partial_solve_wit_4_pure -> cm_emit_leaf_expr_partial_solve_wit_4_aux.

Definition cm_emit_leaf_expr_partial_solve_wit_5_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (xb: Z) (xa: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 1)) (PreH2 : ((cm_rep_expr_kind (e)) <> 0)) (PreH3 : (expr_pre <> 0)) (PreH4 : (0 <= lvalue_pre)) (PreH5 : (lvalue_pre <= 1)) (PreH6 : (e = (cm_leaf_source_expr (leaf)))) (PreH7 : (cm_dispatch_leaf e )) (PreH8 : (cm_wf_program policy cg p )) (PreH9 : (cm_typed_program policy p )) (PreH10 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH11 : (cm_expr_wf policy p f e )) (PreH12 : (cm_expr_counts_representable policy p fid_pre e )) (PreH13 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH14 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH15 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH16 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
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
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) (leaf) (lvalue_pre))) (tail)) )
|--
  “ (e = (cm_leaf_source_expr (leaf))) ” 
  &&  “ (cm_dispatch_leaf e ) ” 
  &&  “ ((cm_rep_expr_kind (e)) = 1) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ”
.

Definition cm_emit_leaf_expr_partial_solve_wit_5_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (xb: Z) (xa: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 1)) (PreH2 : ((cm_rep_expr_kind (e)) <> 0)) (PreH3 : (expr_pre <> 0)) (PreH4 : (0 <= lvalue_pre)) (PreH5 : (lvalue_pre <= 1)) (PreH6 : (e = (cm_leaf_source_expr (leaf)))) (PreH7 : (cm_dispatch_leaf e )) (PreH8 : (cm_wf_program policy cg p )) (PreH9 : (cm_typed_program policy p )) (PreH10 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH11 : (cm_expr_wf policy p f e )) (PreH12 : (cm_expr_counts_representable policy p fid_pre e )) (PreH13 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH14 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH15 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH16 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
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
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) (leaf) (lvalue_pre))) (tail)) )
|--
  “ (e = (cm_leaf_source_expr (leaf))) ” 
  &&  “ (cm_dispatch_leaf e ) ” 
  &&  “ ((cm_rep_expr_kind (e)) = 1) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ ((cm_rep_expr_kind (e)) = 1) ” 
  &&  “ ((cm_rep_expr_kind (e)) <> 0) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
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
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) (leaf) (lvalue_pre))) (tail)) )
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

Definition cm_emit_leaf_expr_partial_solve_wit_5 := cm_emit_leaf_expr_partial_solve_wit_5_pure -> cm_emit_leaf_expr_partial_solve_wit_5_aux.

Definition cm_emit_leaf_expr_partial_solve_wit_6_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (xb: Z) (xa: Z) (sid: Z) (ty: cm_type) (PreH1 : (e = (CMStringE (sid) (ty)))) (PreH2 : (e = (cm_leaf_source_expr (leaf)))) (PreH3 : (cm_dispatch_leaf e )) (PreH4 : (leaf = (CMLeafString (sid) (ty)))) (PreH5 : (0 <= sid)) (PreH6 : (sid <= INT_MAX)) (PreH7 : (cm_expr_wf policy p f e )) (PreH8 : (cm_expr_counts_representable policy p fid_pre e )) (PreH9 : ((cm_rep_expr_kind (e)) = 1)) (PreH10 : ((cm_rep_expr_kind (e)) <> 0)) (PreH11 : (expr_pre <> 0)) (PreH12 : (0 <= lvalue_pre)) (PreH13 : (lvalue_pre <= 1)) (PreH14 : (e = (cm_leaf_source_expr (leaf)))) (PreH15 : (cm_dispatch_leaf e )) (PreH16 : (cm_wf_program policy cg p )) (PreH17 : (cm_typed_program policy p )) (PreH18 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH19 : (cm_expr_wf policy p f e )) (PreH20 : (cm_expr_counts_representable policy p fid_pre e )) (PreH21 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH22 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH23 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH24 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafString (sid) (ty))) (lvalue_pre))) (tail)) )
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

Definition cm_emit_leaf_expr_partial_solve_wit_6_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (xb: Z) (xa: Z) (sid: Z) (ty: cm_type) (PreH1 : (e = (CMStringE (sid) (ty)))) (PreH2 : (e = (cm_leaf_source_expr (leaf)))) (PreH3 : (cm_dispatch_leaf e )) (PreH4 : (leaf = (CMLeafString (sid) (ty)))) (PreH5 : (0 <= sid)) (PreH6 : (sid <= INT_MAX)) (PreH7 : (cm_expr_wf policy p f e )) (PreH8 : (cm_expr_counts_representable policy p fid_pre e )) (PreH9 : ((cm_rep_expr_kind (e)) = 1)) (PreH10 : ((cm_rep_expr_kind (e)) <> 0)) (PreH11 : (expr_pre <> 0)) (PreH12 : (0 <= lvalue_pre)) (PreH13 : (lvalue_pre <= 1)) (PreH14 : (e = (cm_leaf_source_expr (leaf)))) (PreH15 : (cm_dispatch_leaf e )) (PreH16 : (cm_wf_program policy cg p )) (PreH17 : (cm_typed_program policy p )) (PreH18 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH19 : (cm_expr_wf policy p f e )) (PreH20 : (cm_expr_counts_representable policy p fid_pre e )) (PreH21 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH22 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH23 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH24 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafString (sid) (ty))) (lvalue_pre))) (tail)) )
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
  &&  “ (e = (CMStringE (sid) (ty))) ” 
  &&  “ (e = (cm_leaf_source_expr (leaf))) ” 
  &&  “ (cm_dispatch_leaf e ) ” 
  &&  “ (leaf = (CMLeafString (sid) (ty))) ” 
  &&  “ (0 <= sid) ” 
  &&  “ (sid <= INT_MAX) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ ((cm_rep_expr_kind (e)) = 1) ” 
  &&  “ ((cm_rep_expr_kind (e)) <> 0) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
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
  &&  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> xa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> xb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_expr_payload e xa xb xargs )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafString (sid) (ty))) (lvalue_pre))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
.

Definition cm_emit_leaf_expr_partial_solve_wit_6 := cm_emit_leaf_expr_partial_solve_wit_6_pure -> cm_emit_leaf_expr_partial_solve_wit_6_aux.

Definition cm_emit_leaf_expr_partial_solve_wit_7_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sid: Z) (ty: cm_type) (PreH1 : (e = (CMStringE (sid) (ty)))) (PreH2 : (e = (cm_leaf_source_expr (leaf)))) (PreH3 : (cm_dispatch_leaf e )) (PreH4 : (leaf = (CMLeafString (sid) (ty)))) (PreH5 : (0 <= sid)) (PreH6 : (sid <= INT_MAX)) (PreH7 : (cm_expr_wf policy p f e )) (PreH8 : (cm_expr_counts_representable policy p fid_pre e )) (PreH9 : ((cm_rep_expr_kind (e)) = 1)) (PreH10 : ((cm_rep_expr_kind (e)) <> 0)) (PreH11 : (expr_pre <> 0)) (PreH12 : (0 <= lvalue_pre)) (PreH13 : (lvalue_pre <= 1)) (PreH14 : (e = (cm_leaf_source_expr (leaf)))) (PreH15 : (cm_dispatch_leaf e )) (PreH16 : (cm_wf_program policy cg p )) (PreH17 : (cm_typed_program policy p )) (PreH18 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH19 : (cm_expr_wf policy p f e )) (PreH20 : (cm_expr_counts_representable policy p fid_pre e )) (PreH21 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH22 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH23 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH24 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  (cm_expr_rep expr_pre e )
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafString (sid) (ty))) (lvalue_pre))) (tail)) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
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
.

Definition cm_emit_leaf_expr_partial_solve_wit_7_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sid: Z) (ty: cm_type) (PreH1 : (e = (CMStringE (sid) (ty)))) (PreH2 : (e = (cm_leaf_source_expr (leaf)))) (PreH3 : (cm_dispatch_leaf e )) (PreH4 : (leaf = (CMLeafString (sid) (ty)))) (PreH5 : (0 <= sid)) (PreH6 : (sid <= INT_MAX)) (PreH7 : (cm_expr_wf policy p f e )) (PreH8 : (cm_expr_counts_representable policy p fid_pre e )) (PreH9 : ((cm_rep_expr_kind (e)) = 1)) (PreH10 : ((cm_rep_expr_kind (e)) <> 0)) (PreH11 : (expr_pre <> 0)) (PreH12 : (0 <= lvalue_pre)) (PreH13 : (lvalue_pre <= 1)) (PreH14 : (e = (cm_leaf_source_expr (leaf)))) (PreH15 : (cm_dispatch_leaf e )) (PreH16 : (cm_wf_program policy cg p )) (PreH17 : (cm_typed_program policy p )) (PreH18 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH19 : (cm_expr_wf policy p f e )) (PreH20 : (cm_expr_counts_representable policy p fid_pre e )) (PreH21 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH22 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH23 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH24 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafString (sid) (ty))) (lvalue_pre))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
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
  &&  “ (e = (CMStringE (sid) (ty))) ” 
  &&  “ (e = (cm_leaf_source_expr (leaf))) ” 
  &&  “ (cm_dispatch_leaf e ) ” 
  &&  “ (leaf = (CMLeafString (sid) (ty))) ” 
  &&  “ (0 <= sid) ” 
  &&  “ (sid <= INT_MAX) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ ((cm_rep_expr_kind (e)) = 1) ” 
  &&  “ ((cm_rep_expr_kind (e)) <> 0) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
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
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafString (sid) (ty))) (lvalue_pre))) (tail)) )
.

Definition cm_emit_leaf_expr_partial_solve_wit_7 := cm_emit_leaf_expr_partial_solve_wit_7_pure -> cm_emit_leaf_expr_partial_solve_wit_7_aux.

Definition cm_emit_leaf_expr_partial_solve_wit_8_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (xb: Z) (xa: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 9)) (PreH2 : ((cm_rep_expr_kind (e)) <> 1)) (PreH3 : ((cm_rep_expr_kind (e)) <> 0)) (PreH4 : (expr_pre <> 0)) (PreH5 : (0 <= lvalue_pre)) (PreH6 : (lvalue_pre <= 1)) (PreH7 : (e = (cm_leaf_source_expr (leaf)))) (PreH8 : (cm_dispatch_leaf e )) (PreH9 : (cm_wf_program policy cg p )) (PreH10 : (cm_typed_program policy p )) (PreH11 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH12 : (cm_expr_wf policy p f e )) (PreH13 : (cm_expr_counts_representable policy p fid_pre e )) (PreH14 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH15 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH16 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH17 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
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
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) (leaf) (lvalue_pre))) (tail)) )
|--
  “ (e = (cm_leaf_source_expr (leaf))) ” 
  &&  “ (cm_dispatch_leaf e ) ” 
  &&  “ ((cm_rep_expr_kind (e)) = 9) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ”
.

Definition cm_emit_leaf_expr_partial_solve_wit_8_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (xb: Z) (xa: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 9)) (PreH2 : ((cm_rep_expr_kind (e)) <> 1)) (PreH3 : ((cm_rep_expr_kind (e)) <> 0)) (PreH4 : (expr_pre <> 0)) (PreH5 : (0 <= lvalue_pre)) (PreH6 : (lvalue_pre <= 1)) (PreH7 : (e = (cm_leaf_source_expr (leaf)))) (PreH8 : (cm_dispatch_leaf e )) (PreH9 : (cm_wf_program policy cg p )) (PreH10 : (cm_typed_program policy p )) (PreH11 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH12 : (cm_expr_wf policy p f e )) (PreH13 : (cm_expr_counts_representable policy p fid_pre e )) (PreH14 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH15 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH16 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH17 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
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
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) (leaf) (lvalue_pre))) (tail)) )
|--
  “ (e = (cm_leaf_source_expr (leaf))) ” 
  &&  “ (cm_dispatch_leaf e ) ” 
  &&  “ ((cm_rep_expr_kind (e)) = 9) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ ((cm_rep_expr_kind (e)) = 9) ” 
  &&  “ ((cm_rep_expr_kind (e)) <> 1) ” 
  &&  “ ((cm_rep_expr_kind (e)) <> 0) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
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
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) (leaf) (lvalue_pre))) (tail)) )
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

Definition cm_emit_leaf_expr_partial_solve_wit_8 := cm_emit_leaf_expr_partial_solve_wit_8_pure -> cm_emit_leaf_expr_partial_solve_wit_8_aux.

Definition cm_emit_leaf_expr_partial_solve_wit_9_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (xb: Z) (xa: Z) (asked: cm_type) (ty: cm_type) (PreH1 : (e = (CMSizeofE (asked) (ty)))) (PreH2 : (e = (cm_leaf_source_expr (leaf)))) (PreH3 : (cm_dispatch_leaf e )) (PreH4 : (leaf = (CMLeafSizeof (asked) (ty)))) (PreH5 : (cm_type_code_wf asked )) (PreH6 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH7 : (cm_expr_wf policy p f e )) (PreH8 : (cm_expr_counts_representable policy p fid_pre e )) (PreH9 : ((cm_rep_expr_kind (e)) = 9)) (PreH10 : ((cm_rep_expr_kind (e)) <> 1)) (PreH11 : ((cm_rep_expr_kind (e)) <> 0)) (PreH12 : (expr_pre <> 0)) (PreH13 : (0 <= lvalue_pre)) (PreH14 : (lvalue_pre <= 1)) (PreH15 : (e = (cm_leaf_source_expr (leaf)))) (PreH16 : (cm_dispatch_leaf e )) (PreH17 : (cm_wf_program policy cg p )) (PreH18 : (cm_typed_program policy p )) (PreH19 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH20 : (cm_expr_wf policy p f e )) (PreH21 : (cm_expr_counts_representable policy p fid_pre e )) (PreH22 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH23 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH24 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH25 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafSizeof (asked) (ty))) (lvalue_pre))) (tail)) )
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

Definition cm_emit_leaf_expr_partial_solve_wit_9_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (xb: Z) (xa: Z) (asked: cm_type) (ty: cm_type) (PreH1 : (e = (CMSizeofE (asked) (ty)))) (PreH2 : (e = (cm_leaf_source_expr (leaf)))) (PreH3 : (cm_dispatch_leaf e )) (PreH4 : (leaf = (CMLeafSizeof (asked) (ty)))) (PreH5 : (cm_type_code_wf asked )) (PreH6 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH7 : (cm_expr_wf policy p f e )) (PreH8 : (cm_expr_counts_representable policy p fid_pre e )) (PreH9 : ((cm_rep_expr_kind (e)) = 9)) (PreH10 : ((cm_rep_expr_kind (e)) <> 1)) (PreH11 : ((cm_rep_expr_kind (e)) <> 0)) (PreH12 : (expr_pre <> 0)) (PreH13 : (0 <= lvalue_pre)) (PreH14 : (lvalue_pre <= 1)) (PreH15 : (e = (cm_leaf_source_expr (leaf)))) (PreH16 : (cm_dispatch_leaf e )) (PreH17 : (cm_wf_program policy cg p )) (PreH18 : (cm_typed_program policy p )) (PreH19 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH20 : (cm_expr_wf policy p f e )) (PreH21 : (cm_expr_counts_representable policy p fid_pre e )) (PreH22 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH23 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH24 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH25 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafSizeof (asked) (ty))) (lvalue_pre))) (tail)) )
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
  &&  “ (e = (CMSizeofE (asked) (ty))) ” 
  &&  “ (e = (cm_leaf_source_expr (leaf))) ” 
  &&  “ (cm_dispatch_leaf e ) ” 
  &&  “ (leaf = (CMLeafSizeof (asked) (ty))) ” 
  &&  “ (cm_type_code_wf asked ) ” 
  &&  “ (cm_type_refs (cm_program_structs (p)) asked ) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ ((cm_rep_expr_kind (e)) = 9) ” 
  &&  “ ((cm_rep_expr_kind (e)) <> 1) ” 
  &&  “ ((cm_rep_expr_kind (e)) <> 0) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
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
  &&  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> xa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> xb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_expr_payload e xa xb xargs )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafSizeof (asked) (ty))) (lvalue_pre))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
.

Definition cm_emit_leaf_expr_partial_solve_wit_9 := cm_emit_leaf_expr_partial_solve_wit_9_pure -> cm_emit_leaf_expr_partial_solve_wit_9_aux.

Definition cm_emit_leaf_expr_partial_solve_wit_10_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (asked: cm_type) (ty: cm_type) (PreH1 : (e = (CMSizeofE (asked) (ty)))) (PreH2 : (e = (cm_leaf_source_expr (leaf)))) (PreH3 : (cm_dispatch_leaf e )) (PreH4 : (leaf = (CMLeafSizeof (asked) (ty)))) (PreH5 : (cm_type_code_wf asked )) (PreH6 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH7 : (cm_expr_wf policy p f e )) (PreH8 : (cm_expr_counts_representable policy p fid_pre e )) (PreH9 : ((cm_rep_expr_kind (e)) = 9)) (PreH10 : ((cm_rep_expr_kind (e)) <> 1)) (PreH11 : ((cm_rep_expr_kind (e)) <> 0)) (PreH12 : (expr_pre <> 0)) (PreH13 : (0 <= lvalue_pre)) (PreH14 : (lvalue_pre <= 1)) (PreH15 : (e = (cm_leaf_source_expr (leaf)))) (PreH16 : (cm_dispatch_leaf e )) (PreH17 : (cm_wf_program policy cg p )) (PreH18 : (cm_typed_program policy p )) (PreH19 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH20 : (cm_expr_wf policy p f e )) (PreH21 : (cm_expr_counts_representable policy p fid_pre e )) (PreH22 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH23 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH24 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH25 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  (cm_expr_rep expr_pre e )
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafSizeof (asked) (ty))) (lvalue_pre))) (tail)) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
|--
  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (e = (CMSizeofE (asked) (ty))) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_type_code_wf asked ) ” 
  &&  “ (cm_type_refs (cm_program_structs (p)) asked ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ”
.

Definition cm_emit_leaf_expr_partial_solve_wit_10_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (asked: cm_type) (ty: cm_type) (PreH1 : (e = (CMSizeofE (asked) (ty)))) (PreH2 : (e = (cm_leaf_source_expr (leaf)))) (PreH3 : (cm_dispatch_leaf e )) (PreH4 : (leaf = (CMLeafSizeof (asked) (ty)))) (PreH5 : (cm_type_code_wf asked )) (PreH6 : (cm_type_refs (cm_program_structs (p)) asked )) (PreH7 : (cm_expr_wf policy p f e )) (PreH8 : (cm_expr_counts_representable policy p fid_pre e )) (PreH9 : ((cm_rep_expr_kind (e)) = 9)) (PreH10 : ((cm_rep_expr_kind (e)) <> 1)) (PreH11 : ((cm_rep_expr_kind (e)) <> 0)) (PreH12 : (expr_pre <> 0)) (PreH13 : (0 <= lvalue_pre)) (PreH14 : (lvalue_pre <= 1)) (PreH15 : (e = (cm_leaf_source_expr (leaf)))) (PreH16 : (cm_dispatch_leaf e )) (PreH17 : (cm_wf_program policy cg p )) (PreH18 : (cm_typed_program policy p )) (PreH19 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH20 : (cm_expr_wf policy p f e )) (PreH21 : (cm_expr_counts_representable policy p fid_pre e )) (PreH22 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH23 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH24 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH25 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafSizeof (asked) (ty))) (lvalue_pre))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
|--
  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (e = (CMSizeofE (asked) (ty))) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_type_code_wf asked ) ” 
  &&  “ (cm_type_refs (cm_program_structs (p)) asked ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (e = (CMSizeofE (asked) (ty))) ” 
  &&  “ (e = (cm_leaf_source_expr (leaf))) ” 
  &&  “ (cm_dispatch_leaf e ) ” 
  &&  “ (leaf = (CMLeafSizeof (asked) (ty))) ” 
  &&  “ (cm_type_code_wf asked ) ” 
  &&  “ (cm_type_refs (cm_program_structs (p)) asked ) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ ((cm_rep_expr_kind (e)) = 9) ” 
  &&  “ ((cm_rep_expr_kind (e)) <> 1) ” 
  &&  “ ((cm_rep_expr_kind (e)) <> 0) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
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
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafSizeof (asked) (ty))) (lvalue_pre))) (tail)) )
.

Definition cm_emit_leaf_expr_partial_solve_wit_10 := cm_emit_leaf_expr_partial_solve_wit_10_pure -> cm_emit_leaf_expr_partial_solve_wit_10_aux.

Definition cm_emit_leaf_expr_partial_solve_wit_11_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (xb: Z) (xa: Z) (PreH1 : ((cm_rep_expr_kind (e)) <> 9)) (PreH2 : ((cm_rep_expr_kind (e)) <> 1)) (PreH3 : ((cm_rep_expr_kind (e)) <> 0)) (PreH4 : (expr_pre <> 0)) (PreH5 : (0 <= lvalue_pre)) (PreH6 : (lvalue_pre <= 1)) (PreH7 : (e = (cm_leaf_source_expr (leaf)))) (PreH8 : (cm_dispatch_leaf e )) (PreH9 : (cm_wf_program policy cg p )) (PreH10 : (cm_typed_program policy p )) (PreH11 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH12 : (cm_expr_wf policy p f e )) (PreH13 : (cm_expr_counts_representable policy p fid_pre e )) (PreH14 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH15 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH16 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH17 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
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
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) (leaf) (lvalue_pre))) (tail)) )
|--
  “ (e = (cm_leaf_source_expr (leaf))) ” 
  &&  “ (cm_dispatch_leaf e ) ” 
  &&  “ ((cm_rep_expr_kind (e)) <> 0) ” 
  &&  “ ((cm_rep_expr_kind (e)) <> 1) ” 
  &&  “ ((cm_rep_expr_kind (e)) <> 9) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ”
.

Definition cm_emit_leaf_expr_partial_solve_wit_11_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (xb: Z) (xa: Z) (PreH1 : ((cm_rep_expr_kind (e)) <> 9)) (PreH2 : ((cm_rep_expr_kind (e)) <> 1)) (PreH3 : ((cm_rep_expr_kind (e)) <> 0)) (PreH4 : (expr_pre <> 0)) (PreH5 : (0 <= lvalue_pre)) (PreH6 : (lvalue_pre <= 1)) (PreH7 : (e = (cm_leaf_source_expr (leaf)))) (PreH8 : (cm_dispatch_leaf e )) (PreH9 : (cm_wf_program policy cg p )) (PreH10 : (cm_typed_program policy p )) (PreH11 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH12 : (cm_expr_wf policy p f e )) (PreH13 : (cm_expr_counts_representable policy p fid_pre e )) (PreH14 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH15 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH16 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH17 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
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
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) (leaf) (lvalue_pre))) (tail)) )
|--
  “ (e = (cm_leaf_source_expr (leaf))) ” 
  &&  “ (cm_dispatch_leaf e ) ” 
  &&  “ ((cm_rep_expr_kind (e)) <> 0) ” 
  &&  “ ((cm_rep_expr_kind (e)) <> 1) ” 
  &&  “ ((cm_rep_expr_kind (e)) <> 9) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ ((cm_rep_expr_kind (e)) <> 9) ” 
  &&  “ ((cm_rep_expr_kind (e)) <> 1) ” 
  &&  “ ((cm_rep_expr_kind (e)) <> 0) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
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
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) (leaf) (lvalue_pre))) (tail)) )
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

Definition cm_emit_leaf_expr_partial_solve_wit_11 := cm_emit_leaf_expr_partial_solve_wit_11_pure -> cm_emit_leaf_expr_partial_solve_wit_11_aux.

Definition cm_emit_leaf_expr_partial_solve_wit_12_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (xb: Z) (xa: Z) (ty: cm_type) (PreH1 : (e = (CMGetcE (ty)))) (PreH2 : (e = (cm_leaf_source_expr (leaf)))) (PreH3 : (cm_dispatch_leaf e )) (PreH4 : (leaf = (CMLeafGetc (ty)))) (PreH5 : (cm_dispatch_leaf e )) (PreH6 : (cm_expr_wf policy p f e )) (PreH7 : (cm_expr_counts_representable policy p fid_pre e )) (PreH8 : ((cm_rep_expr_kind (e)) <> 9)) (PreH9 : ((cm_rep_expr_kind (e)) <> 1)) (PreH10 : ((cm_rep_expr_kind (e)) <> 0)) (PreH11 : (expr_pre <> 0)) (PreH12 : (0 <= lvalue_pre)) (PreH13 : (lvalue_pre <= 1)) (PreH14 : (e = (cm_leaf_source_expr (leaf)))) (PreH15 : (cm_dispatch_leaf e )) (PreH16 : (cm_wf_program policy cg p )) (PreH17 : (cm_typed_program policy p )) (PreH18 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH19 : (cm_expr_wf policy p f e )) (PreH20 : (cm_expr_counts_representable policy p fid_pre e )) (PreH21 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH22 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH23 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH24 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafGetc (ty))) (lvalue_pre))) (tail)) )
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

Definition cm_emit_leaf_expr_partial_solve_wit_12_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (xb: Z) (xa: Z) (ty: cm_type) (PreH1 : (e = (CMGetcE (ty)))) (PreH2 : (e = (cm_leaf_source_expr (leaf)))) (PreH3 : (cm_dispatch_leaf e )) (PreH4 : (leaf = (CMLeafGetc (ty)))) (PreH5 : (cm_dispatch_leaf e )) (PreH6 : (cm_expr_wf policy p f e )) (PreH7 : (cm_expr_counts_representable policy p fid_pre e )) (PreH8 : ((cm_rep_expr_kind (e)) <> 9)) (PreH9 : ((cm_rep_expr_kind (e)) <> 1)) (PreH10 : ((cm_rep_expr_kind (e)) <> 0)) (PreH11 : (expr_pre <> 0)) (PreH12 : (0 <= lvalue_pre)) (PreH13 : (lvalue_pre <= 1)) (PreH14 : (e = (cm_leaf_source_expr (leaf)))) (PreH15 : (cm_dispatch_leaf e )) (PreH16 : (cm_wf_program policy cg p )) (PreH17 : (cm_typed_program policy p )) (PreH18 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH19 : (cm_expr_wf policy p f e )) (PreH20 : (cm_expr_counts_representable policy p fid_pre e )) (PreH21 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH22 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH23 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH24 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafGetc (ty))) (lvalue_pre))) (tail)) )
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
  &&  “ (e = (CMGetcE (ty))) ” 
  &&  “ (e = (cm_leaf_source_expr (leaf))) ” 
  &&  “ (cm_dispatch_leaf e ) ” 
  &&  “ (leaf = (CMLeafGetc (ty))) ” 
  &&  “ (cm_dispatch_leaf e ) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ ((cm_rep_expr_kind (e)) <> 9) ” 
  &&  “ ((cm_rep_expr_kind (e)) <> 1) ” 
  &&  “ ((cm_rep_expr_kind (e)) <> 0) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
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
  &&  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> xa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> xb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_expr_payload e xa xb xargs )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafGetc (ty))) (lvalue_pre))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
.

Definition cm_emit_leaf_expr_partial_solve_wit_12 := cm_emit_leaf_expr_partial_solve_wit_12_pure -> cm_emit_leaf_expr_partial_solve_wit_12_aux.

Definition cm_emit_leaf_expr_partial_solve_wit_13_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (ty: cm_type) (PreH1 : (e = (CMGetcE (ty)))) (PreH2 : (e = (cm_leaf_source_expr (leaf)))) (PreH3 : (cm_dispatch_leaf e )) (PreH4 : (leaf = (CMLeafGetc (ty)))) (PreH5 : (cm_dispatch_leaf e )) (PreH6 : (cm_expr_wf policy p f e )) (PreH7 : (cm_expr_counts_representable policy p fid_pre e )) (PreH8 : ((cm_rep_expr_kind (e)) <> 9)) (PreH9 : ((cm_rep_expr_kind (e)) <> 1)) (PreH10 : ((cm_rep_expr_kind (e)) <> 0)) (PreH11 : (expr_pre <> 0)) (PreH12 : (0 <= lvalue_pre)) (PreH13 : (lvalue_pre <= 1)) (PreH14 : (e = (cm_leaf_source_expr (leaf)))) (PreH15 : (cm_dispatch_leaf e )) (PreH16 : (cm_wf_program policy cg p )) (PreH17 : (cm_typed_program policy p )) (PreH18 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH19 : (cm_expr_wf policy p f e )) (PreH20 : (cm_expr_counts_representable policy p fid_pre e )) (PreH21 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH22 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH23 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH24 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  (cm_expr_rep expr_pre e )
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafGetc (ty))) (lvalue_pre))) (tail)) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
|--
  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (e = (CMGetcE (ty))) ”
.

Definition cm_emit_leaf_expr_partial_solve_wit_13_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (ty: cm_type) (PreH1 : (e = (CMGetcE (ty)))) (PreH2 : (e = (cm_leaf_source_expr (leaf)))) (PreH3 : (cm_dispatch_leaf e )) (PreH4 : (leaf = (CMLeafGetc (ty)))) (PreH5 : (cm_dispatch_leaf e )) (PreH6 : (cm_expr_wf policy p f e )) (PreH7 : (cm_expr_counts_representable policy p fid_pre e )) (PreH8 : ((cm_rep_expr_kind (e)) <> 9)) (PreH9 : ((cm_rep_expr_kind (e)) <> 1)) (PreH10 : ((cm_rep_expr_kind (e)) <> 0)) (PreH11 : (expr_pre <> 0)) (PreH12 : (0 <= lvalue_pre)) (PreH13 : (lvalue_pre <= 1)) (PreH14 : (e = (cm_leaf_source_expr (leaf)))) (PreH15 : (cm_dispatch_leaf e )) (PreH16 : (cm_wf_program policy cg p )) (PreH17 : (cm_typed_program policy p )) (PreH18 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH19 : (cm_expr_wf policy p f e )) (PreH20 : (cm_expr_counts_representable policy p fid_pre e )) (PreH21 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH22 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH23 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH24 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafGetc (ty))) (lvalue_pre))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
|--
  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (e = (CMGetcE (ty))) ” 
  &&  “ (e = (CMGetcE (ty))) ” 
  &&  “ (e = (cm_leaf_source_expr (leaf))) ” 
  &&  “ (cm_dispatch_leaf e ) ” 
  &&  “ (leaf = (CMLeafGetc (ty))) ” 
  &&  “ (cm_dispatch_leaf e ) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ ((cm_rep_expr_kind (e)) <> 9) ” 
  &&  “ ((cm_rep_expr_kind (e)) <> 1) ” 
  &&  “ ((cm_rep_expr_kind (e)) <> 0) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (0 <= lvalue_pre) ” 
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
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_leaf_code_for (p) ((CMLeafGetc (ty))) (lvalue_pre))) (tail)) )
.

Definition cm_emit_leaf_expr_partial_solve_wit_13 := cm_emit_leaf_expr_partial_solve_wit_13_pure -> cm_emit_leaf_expr_partial_solve_wit_13_aux.

Definition cm_emit_leaf_expr_which_implies_wit_1 := 
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

Definition cm_emit_leaf_expr_which_implies_wit_2 := 
(
forall (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (fid: Z) (lvalue: Z) (emitter: Z) (PreH1 : (e = (cm_leaf_source_expr (leaf)))) (PreH2 : (cm_dispatch_leaf e )) (PreH3 : ((cm_rep_expr_kind (e)) = 0)) (PreH4 : (cm_expr_wf policy p f e )) (PreH5 : (cm_expr_counts_representable policy p fid e )) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_leaf_code_for (p) (leaf) (lvalue))) (tail)) )
|--
  EX (n: Z)  (ty: cm_type) ,
  “ (e = (CMConstE (n) (ty))) ” 
  &&  “ (e = (cm_leaf_source_expr (leaf))) ” 
  &&  “ (cm_dispatch_leaf e ) ” 
  &&  “ (leaf = (CMLeafConst (n) (ty))) ” 
  &&  “ (cm_type_code_wf ty ) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid e ) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_leaf_code_for (p) ((CMLeafConst (n) (ty))) (lvalue))) (tail)) )
) \/
(
forall (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (fid: Z) (lvalue: Z) (emitter: Z) (PreH1 : (e = (cm_leaf_source_expr (leaf)))) (PreH2 : (cm_dispatch_leaf e )) (PreH3 : ((cm_rep_expr_kind (e)) = 0)) (PreH4 : (cm_expr_wf policy p f e )) (PreH5 : (cm_expr_counts_representable policy p fid e )) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_leaf_code_for (p) (leaf) (lvalue))) (tail)) )
|--
  EX (n: Z)  (ty: cm_type) ,
  “ (e = (CMConstE (n) (ty))) ” 
  &&  “ (e = (cm_leaf_source_expr (leaf))) ” 
  &&  “ (cm_dispatch_leaf e ) ” 
  &&  “ (leaf = (CMLeafConst (n) (ty))) ” 
  &&  “ (cm_type_code_wf ty ) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid e ) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_leaf_code_for (p) ((CMLeafConst (n) (ty))) (lvalue))) (tail)) )
).

Definition cm_emit_leaf_expr_which_implies_wit_3 := 
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

Definition cm_emit_leaf_expr_which_implies_wit_3_split_goal_spatial := 
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

Definition cm_emit_leaf_expr_which_implies_wit_4 := 
(
forall (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (fid: Z) (lvalue: Z) (emitter: Z) (PreH1 : (e = (cm_leaf_source_expr (leaf)))) (PreH2 : (cm_dispatch_leaf e )) (PreH3 : ((cm_rep_expr_kind (e)) = 1)) (PreH4 : (cm_expr_wf policy p f e )) (PreH5 : (cm_expr_counts_representable policy p fid e )) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_leaf_code_for (p) (leaf) (lvalue))) (tail)) )
|--
  EX (sid: Z)  (ty: cm_type) ,
  “ (e = (CMStringE (sid) (ty))) ” 
  &&  “ (e = (cm_leaf_source_expr (leaf))) ” 
  &&  “ (cm_dispatch_leaf e ) ” 
  &&  “ (leaf = (CMLeafString (sid) (ty))) ” 
  &&  “ (0 <= sid) ” 
  &&  “ (sid <= INT_MAX) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid e ) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_leaf_code_for (p) ((CMLeafString (sid) (ty))) (lvalue))) (tail)) )
) \/
(
forall (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (fid: Z) (lvalue: Z) (emitter: Z) (PreH1 : (e = (cm_leaf_source_expr (leaf)))) (PreH2 : (cm_dispatch_leaf e )) (PreH3 : ((cm_rep_expr_kind (e)) = 1)) (PreH4 : (cm_expr_wf policy p f e )) (PreH5 : (cm_expr_counts_representable policy p fid e )) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_leaf_code_for (p) (leaf) (lvalue))) (tail)) )
|--
  EX (sid: Z)  (ty: cm_type) ,
  “ (e = (CMStringE (sid) (ty))) ” 
  &&  “ (e = (cm_leaf_source_expr (leaf))) ” 
  &&  “ (cm_dispatch_leaf e ) ” 
  &&  “ (leaf = (CMLeafString (sid) (ty))) ” 
  &&  “ (0 <= sid) ” 
  &&  “ (sid <= INT_MAX) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid e ) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_leaf_code_for (p) ((CMLeafString (sid) (ty))) (lvalue))) (tail)) )
).

Definition cm_emit_leaf_expr_which_implies_wit_5 := 
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

Definition cm_emit_leaf_expr_which_implies_wit_5_split_goal_spatial := 
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

Definition cm_emit_leaf_expr_which_implies_wit_6 := 
(
forall (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (fid: Z) (lvalue: Z) (emitter: Z) (PreH1 : (e = (cm_leaf_source_expr (leaf)))) (PreH2 : (cm_dispatch_leaf e )) (PreH3 : ((cm_rep_expr_kind (e)) = 9)) (PreH4 : (cm_expr_wf policy p f e )) (PreH5 : (cm_expr_counts_representable policy p fid e )) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_leaf_code_for (p) (leaf) (lvalue))) (tail)) )
|--
  EX (asked: cm_type)  (ty: cm_type) ,
  “ (e = (CMSizeofE (asked) (ty))) ” 
  &&  “ (e = (cm_leaf_source_expr (leaf))) ” 
  &&  “ (cm_dispatch_leaf e ) ” 
  &&  “ (leaf = (CMLeafSizeof (asked) (ty))) ” 
  &&  “ (cm_type_code_wf asked ) ” 
  &&  “ (cm_type_refs (cm_program_structs (p)) asked ) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid e ) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_leaf_code_for (p) ((CMLeafSizeof (asked) (ty))) (lvalue))) (tail)) )
) \/
(
forall (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (fid: Z) (lvalue: Z) (emitter: Z) (PreH1 : (e = (cm_leaf_source_expr (leaf)))) (PreH2 : (cm_dispatch_leaf e )) (PreH3 : ((cm_rep_expr_kind (e)) = 9)) (PreH4 : (cm_expr_wf policy p f e )) (PreH5 : (cm_expr_counts_representable policy p fid e )) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_leaf_code_for (p) (leaf) (lvalue))) (tail)) )
|--
  EX (asked: cm_type)  (ty: cm_type) ,
  “ (e = (CMSizeofE (asked) (ty))) ” 
  &&  “ (e = (cm_leaf_source_expr (leaf))) ” 
  &&  “ (cm_dispatch_leaf e ) ” 
  &&  “ (leaf = (CMLeafSizeof (asked) (ty))) ” 
  &&  “ (cm_type_code_wf asked ) ” 
  &&  “ (cm_type_refs (cm_program_structs (p)) asked ) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid e ) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_leaf_code_for (p) ((CMLeafSizeof (asked) (ty))) (lvalue))) (tail)) )
).

Definition cm_emit_leaf_expr_which_implies_wit_7 := 
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

Definition cm_emit_leaf_expr_which_implies_wit_7_split_goal_spatial := 
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

Definition cm_emit_leaf_expr_which_implies_wit_8 := 
(
forall (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (fid: Z) (lvalue: Z) (emitter: Z) (PreH1 : (e = (cm_leaf_source_expr (leaf)))) (PreH2 : (cm_dispatch_leaf e )) (PreH3 : ((cm_rep_expr_kind (e)) <> 0)) (PreH4 : ((cm_rep_expr_kind (e)) <> 1)) (PreH5 : ((cm_rep_expr_kind (e)) <> 9)) (PreH6 : (cm_expr_wf policy p f e )) (PreH7 : (cm_expr_counts_representable policy p fid e )) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_leaf_code_for (p) (leaf) (lvalue))) (tail)) )
|--
  EX (ty: cm_type) ,
  “ (e = (CMGetcE (ty))) ” 
  &&  “ (e = (cm_leaf_source_expr (leaf))) ” 
  &&  “ (cm_dispatch_leaf e ) ” 
  &&  “ (leaf = (CMLeafGetc (ty))) ” 
  &&  “ (cm_dispatch_leaf e ) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid e ) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_leaf_code_for (p) ((CMLeafGetc (ty))) (lvalue))) (tail)) )
) \/
(
forall (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (leaf: cm_leaf_expr) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (fid: Z) (lvalue: Z) (emitter: Z) (PreH1 : (e = (cm_leaf_source_expr (leaf)))) (PreH2 : (cm_dispatch_leaf e )) (PreH3 : ((cm_rep_expr_kind (e)) <> 0)) (PreH4 : ((cm_rep_expr_kind (e)) <> 1)) (PreH5 : ((cm_rep_expr_kind (e)) <> 9)) (PreH6 : (cm_expr_wf policy p f e )) (PreH7 : (cm_expr_counts_representable policy p fid e )) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_leaf_code_for (p) (leaf) (lvalue))) (tail)) )
|--
  EX (ty: cm_type) ,
  “ (e = (CMGetcE (ty))) ” 
  &&  “ (e = (cm_leaf_source_expr (leaf))) ” 
  &&  “ (cm_dispatch_leaf e ) ” 
  &&  “ (leaf = (CMLeafGetc (ty))) ” 
  &&  “ (cm_dispatch_leaf e ) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid e ) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_leaf_code_for (p) ((CMLeafGetc (ty))) (lvalue))) (tail)) )
).

Definition cm_emit_leaf_expr_which_implies_wit_9 := 
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

Definition cm_emit_leaf_expr_which_implies_wit_9_split_goal_spatial := 
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


Axiom proof_of_cm_emit_leaf_expr_safety_wit_1 : cm_emit_leaf_expr_safety_wit_1.
Axiom proof_of_cm_emit_leaf_expr_safety_wit_2 : cm_emit_leaf_expr_safety_wit_2.
Axiom proof_of_cm_emit_leaf_expr_safety_wit_3 : cm_emit_leaf_expr_safety_wit_3.
Axiom proof_of_cm_emit_leaf_expr_return_wit_1 : cm_emit_leaf_expr_return_wit_1.
Axiom proof_of_cm_emit_leaf_expr_return_wit_2 : cm_emit_leaf_expr_return_wit_2.
Axiom proof_of_cm_emit_leaf_expr_return_wit_3 : cm_emit_leaf_expr_return_wit_3.
Axiom proof_of_cm_emit_leaf_expr_return_wit_4 : cm_emit_leaf_expr_return_wit_4.
Axiom proof_of_cm_emit_leaf_expr_partial_solve_wit_1 : cm_emit_leaf_expr_partial_solve_wit_1.
Axiom proof_of_cm_emit_leaf_expr_partial_solve_wit_2_pure : cm_emit_leaf_expr_partial_solve_wit_2_pure.
Axiom proof_of_cm_emit_leaf_expr_partial_solve_wit_2 : cm_emit_leaf_expr_partial_solve_wit_2.
Axiom proof_of_cm_emit_leaf_expr_partial_solve_wit_3_pure : cm_emit_leaf_expr_partial_solve_wit_3_pure.
Axiom proof_of_cm_emit_leaf_expr_partial_solve_wit_3 : cm_emit_leaf_expr_partial_solve_wit_3.
Axiom proof_of_cm_emit_leaf_expr_partial_solve_wit_4_pure : cm_emit_leaf_expr_partial_solve_wit_4_pure.
Axiom proof_of_cm_emit_leaf_expr_partial_solve_wit_4 : cm_emit_leaf_expr_partial_solve_wit_4.
Axiom proof_of_cm_emit_leaf_expr_partial_solve_wit_5_pure : cm_emit_leaf_expr_partial_solve_wit_5_pure.
Axiom proof_of_cm_emit_leaf_expr_partial_solve_wit_5 : cm_emit_leaf_expr_partial_solve_wit_5.
Axiom proof_of_cm_emit_leaf_expr_partial_solve_wit_6_pure : cm_emit_leaf_expr_partial_solve_wit_6_pure.
Axiom proof_of_cm_emit_leaf_expr_partial_solve_wit_6 : cm_emit_leaf_expr_partial_solve_wit_6.
Axiom proof_of_cm_emit_leaf_expr_partial_solve_wit_7_pure : cm_emit_leaf_expr_partial_solve_wit_7_pure.
Axiom proof_of_cm_emit_leaf_expr_partial_solve_wit_7 : cm_emit_leaf_expr_partial_solve_wit_7.
Axiom proof_of_cm_emit_leaf_expr_partial_solve_wit_8_pure : cm_emit_leaf_expr_partial_solve_wit_8_pure.
Axiom proof_of_cm_emit_leaf_expr_partial_solve_wit_8 : cm_emit_leaf_expr_partial_solve_wit_8.
Axiom proof_of_cm_emit_leaf_expr_partial_solve_wit_9_pure : cm_emit_leaf_expr_partial_solve_wit_9_pure.
Axiom proof_of_cm_emit_leaf_expr_partial_solve_wit_9 : cm_emit_leaf_expr_partial_solve_wit_9.
Axiom proof_of_cm_emit_leaf_expr_partial_solve_wit_10_pure : cm_emit_leaf_expr_partial_solve_wit_10_pure.
Axiom proof_of_cm_emit_leaf_expr_partial_solve_wit_10 : cm_emit_leaf_expr_partial_solve_wit_10.
Axiom proof_of_cm_emit_leaf_expr_partial_solve_wit_11_pure : cm_emit_leaf_expr_partial_solve_wit_11_pure.
Axiom proof_of_cm_emit_leaf_expr_partial_solve_wit_11 : cm_emit_leaf_expr_partial_solve_wit_11.
Axiom proof_of_cm_emit_leaf_expr_partial_solve_wit_12_pure : cm_emit_leaf_expr_partial_solve_wit_12_pure.
Axiom proof_of_cm_emit_leaf_expr_partial_solve_wit_12 : cm_emit_leaf_expr_partial_solve_wit_12.
Axiom proof_of_cm_emit_leaf_expr_partial_solve_wit_13_pure : cm_emit_leaf_expr_partial_solve_wit_13_pure.
Axiom proof_of_cm_emit_leaf_expr_partial_solve_wit_13 : cm_emit_leaf_expr_partial_solve_wit_13.
Axiom proof_of_cm_emit_leaf_expr_which_implies_wit_1 : cm_emit_leaf_expr_which_implies_wit_1.
Axiom proof_of_cm_emit_leaf_expr_which_implies_wit_2 : cm_emit_leaf_expr_which_implies_wit_2.
Axiom proof_of_cm_emit_leaf_expr_which_implies_wit_3 : cm_emit_leaf_expr_which_implies_wit_3.
Axiom proof_of_cm_emit_leaf_expr_which_implies_wit_4 : cm_emit_leaf_expr_which_implies_wit_4.
Axiom proof_of_cm_emit_leaf_expr_which_implies_wit_5 : cm_emit_leaf_expr_which_implies_wit_5.
Axiom proof_of_cm_emit_leaf_expr_which_implies_wit_6 : cm_emit_leaf_expr_which_implies_wit_6.
Axiom proof_of_cm_emit_leaf_expr_which_implies_wit_7 : cm_emit_leaf_expr_which_implies_wit_7.
Axiom proof_of_cm_emit_leaf_expr_which_implies_wit_8 : cm_emit_leaf_expr_which_implies_wit_8.
Axiom proof_of_cm_emit_leaf_expr_which_implies_wit_9 : cm_emit_leaf_expr_which_implies_wit_9.

End VC_Correct.
