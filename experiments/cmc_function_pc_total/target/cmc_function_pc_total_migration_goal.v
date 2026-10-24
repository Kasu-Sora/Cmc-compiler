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
Require Import SimpleC.EE.QCP_demos_human.cmc_function_pc_total_migration_lib.
Local Open Scope sac.

(*----- Function cmc_function_prefix_total -----*)

Definition cmc_function_prefix_total_safety_wit_1 := 
forall (target_pre: Z) (index_pre: Z) (fn_pre: Z) (program_pre: Z) (functions_ptr: Z) (functions: (@list cm_function_d)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH3 : (0 <= index_pre)) (PreH4 : (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) ))) (PreH5 : ((index_pre + (Zlength (functions)) ) <= INT_MAX)) (PreH6 : (cm_functions_counts_representable policy p functions index_pre )) (PreH7 : (cm_concrete_functions_ready policy p index_pre functions )) ,
  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((( &( "target" ) )) # Int64  |-> target_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep fn_pre functions )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_function_prefix_total_safety_wit_2 := 
forall (target_pre: Z) (index_pre: Z) (fn_pre: Z) (program_pre: Z) (functions_ptr: Z) (functions: (@list cm_function_d)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (fn_pre = 0)) (PreH2 : (cm_wf_program policy cg p )) (PreH3 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH4 : (0 <= index_pre)) (PreH5 : (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) ))) (PreH6 : ((index_pre + (Zlength (functions)) ) <= INT_MAX)) (PreH7 : (cm_functions_counts_representable policy p functions index_pre )) (PreH8 : (cm_concrete_functions_ready policy p index_pre functions )) ,
  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((( &( "target" ) )) # Int64  |-> target_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep fn_pre functions )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_function_prefix_total_safety_wit_3 := 
forall (target_pre: Z) (index_pre: Z) (fn_pre: Z) (program_pre: Z) (functions_ptr: Z) (functions: (@list cm_function_d)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (index_pre = target_pre)) (PreH2 : (fn_pre <> 0)) (PreH3 : (cm_wf_program policy cg p )) (PreH4 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH5 : (0 <= index_pre)) (PreH6 : (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) ))) (PreH7 : ((index_pre + (Zlength (functions)) ) <= INT_MAX)) (PreH8 : (cm_functions_counts_representable policy p functions index_pre )) (PreH9 : (cm_concrete_functions_ready policy p index_pre functions )) ,
  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((( &( "target" ) )) # Int64  |-> target_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep fn_pre functions )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_function_prefix_total_safety_wit_4 := 
(
forall (target_pre: Z) (index_pre: Z) (fn_pre: Z) (program_pre: Z) (functions_ptr: Z) (functions: (@list cm_function_d)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (f: cm_function_d) (rest: (@list cm_function_d)) (bp: Z) (np: Z) (pp: Z) (lp: Z) (head_count: Z) (PreH1 : (fn_pre <> 0)) (PreH2 : (index_pre <> target_pre)) (PreH3 : (functions = (cons (f) (rest)))) (PreH4 : (cm_function_counts_representable policy p index_pre f )) (PreH5 : (cm_stmt_wf policy p f false (cm_function_body (f)) )) (PreH6 : (cm_functions_counts_representable policy p rest (index_pre + 1 ) )) (PreH7 : (cm_concrete_functions_ready policy p (index_pre + 1 ) rest )) (PreH8 : (cm_i32_code_count (index_pre + 1 ) )) (PreH9 : (cm_wf_program policy cg p )) (PreH10 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH11 : (0 <= index_pre)) (PreH12 : (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) ))) (PreH13 : ((index_pre + (Zlength (functions)) ) <= INT_MAX)) (PreH14 : (cm_functions_counts_representable policy p functions index_pre )) (PreH15 : (cm_concrete_functions_ready policy p index_pre functions )) (PreH16 : (head_count = (cm_function_code_count (policy) (p) (index_pre)))) (PreH17 : (cm_i32_code_count head_count )) ,
  ((( &( "tail_count" ) )) # Int  |->_)
  **  ((( &( "next_fn" ) )) # Ptr  |-> np)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((( &( "target" ) )) # Int64  |-> target_pre)
  **  ((( &( "head_count" ) )) # Int  |-> head_count)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> bp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  (cm_stmt_rep bp (cm_function_body (f)) )
  **  (cm_function_list_rep np rest )
|--
  “ ((index_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (index_pre + 1 )) ”
) \/
(
forall (target_pre: Z) (index_pre: Z) (fn_pre: Z) (program_pre: Z) (functions_ptr: Z) (functions: (@list cm_function_d)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (f: cm_function_d) (rest: (@list cm_function_d)) (bp: Z) (np: Z) (pp: Z) (lp: Z) (head_count: Z) (PreH1 : (fn_pre <> 0)) (PreH2 : (index_pre <> target_pre)) (PreH3 : (functions = (cons (f) (rest)))) (PreH4 : (cm_function_counts_representable policy p index_pre f )) (PreH5 : (cm_stmt_wf policy p f false (cm_function_body (f)) )) (PreH6 : (cm_functions_counts_representable policy p rest (index_pre + 1 ) )) (PreH7 : (cm_concrete_functions_ready policy p (index_pre + 1 ) rest )) (PreH8 : (cm_i32_code_count (index_pre + 1 ) )) (PreH9 : (cm_wf_program policy cg p )) (PreH10 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH11 : (0 <= index_pre)) (PreH12 : (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) ))) (PreH13 : ((index_pre + (Zlength (functions)) ) <= INT_MAX)) (PreH14 : (cm_functions_counts_representable policy p functions index_pre )) (PreH15 : (cm_concrete_functions_ready policy p index_pre functions )) (PreH16 : (head_count = (cm_function_code_count (policy) (p) (index_pre)))) (PreH17 : (cm_i32_code_count head_count )) ,
  ((( &( "tail_count" ) )) # Int  |->_)
  **  ((( &( "next_fn" ) )) # Ptr  |-> np)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((( &( "target" ) )) # Int64  |-> target_pre)
  **  ((( &( "head_count" ) )) # Int  |-> head_count)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> bp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  (cm_stmt_rep bp (cm_function_body (f)) )
  **  (cm_function_list_rep np rest )
|--
  “ ((index_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (index_pre + 1 )) ”
).

Definition cmc_function_prefix_total_safety_wit_4_split_goal_1 := 
forall (target_pre: Z) (index_pre: Z) (fn_pre: Z) (program_pre: Z) (functions_ptr: Z) (functions: (@list cm_function_d)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (f: cm_function_d) (rest: (@list cm_function_d)) (bp: Z) (np: Z) (pp: Z) (lp: Z) (head_count: Z) (PreH1 : (fn_pre <> 0)) (PreH2 : (index_pre <> target_pre)) (PreH3 : (functions = (cons (f) (rest)))) (PreH4 : (cm_function_counts_representable policy p index_pre f )) (PreH5 : (cm_stmt_wf policy p f false (cm_function_body (f)) )) (PreH6 : (cm_functions_counts_representable policy p rest (index_pre + 1 ) )) (PreH7 : (cm_concrete_functions_ready policy p (index_pre + 1 ) rest )) (PreH8 : (cm_i32_code_count (index_pre + 1 ) )) (PreH9 : (cm_wf_program policy cg p )) (PreH10 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH11 : (0 <= index_pre)) (PreH12 : (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) ))) (PreH13 : ((index_pre + (Zlength (functions)) ) <= INT_MAX)) (PreH14 : (cm_functions_counts_representable policy p functions index_pre )) (PreH15 : (cm_concrete_functions_ready policy p index_pre functions )) (PreH16 : (head_count = (cm_function_code_count (policy) (p) (index_pre)))) (PreH17 : (cm_i32_code_count head_count )) ,
  ((( &( "tail_count" ) )) # Int  |->_)
  **  ((( &( "next_fn" ) )) # Ptr  |-> np)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((( &( "target" ) )) # Int64  |-> target_pre)
  **  ((( &( "head_count" ) )) # Int  |-> head_count)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> bp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  (cm_stmt_rep bp (cm_function_body (f)) )
  **  (cm_function_list_rep np rest )
|--
  “ ((index_pre + 1 ) <= INT_MAX) ”
.

Definition cmc_function_prefix_total_safety_wit_4_split_goal_2 := 
forall (target_pre: Z) (index_pre: Z) (fn_pre: Z) (program_pre: Z) (functions_ptr: Z) (functions: (@list cm_function_d)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (f: cm_function_d) (rest: (@list cm_function_d)) (bp: Z) (np: Z) (pp: Z) (lp: Z) (head_count: Z) (PreH1 : (fn_pre <> 0)) (PreH2 : (index_pre <> target_pre)) (PreH3 : (functions = (cons (f) (rest)))) (PreH4 : (cm_function_counts_representable policy p index_pre f )) (PreH5 : (cm_stmt_wf policy p f false (cm_function_body (f)) )) (PreH6 : (cm_functions_counts_representable policy p rest (index_pre + 1 ) )) (PreH7 : (cm_concrete_functions_ready policy p (index_pre + 1 ) rest )) (PreH8 : (cm_i32_code_count (index_pre + 1 ) )) (PreH9 : (cm_wf_program policy cg p )) (PreH10 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH11 : (0 <= index_pre)) (PreH12 : (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) ))) (PreH13 : ((index_pre + (Zlength (functions)) ) <= INT_MAX)) (PreH14 : (cm_functions_counts_representable policy p functions index_pre )) (PreH15 : (cm_concrete_functions_ready policy p index_pre functions )) (PreH16 : (head_count = (cm_function_code_count (policy) (p) (index_pre)))) (PreH17 : (cm_i32_code_count head_count )) ,
  ((( &( "tail_count" ) )) # Int  |->_)
  **  ((( &( "next_fn" ) )) # Ptr  |-> np)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((( &( "target" ) )) # Int64  |-> target_pre)
  **  ((( &( "head_count" ) )) # Int  |-> head_count)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> bp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  (cm_stmt_rep bp (cm_function_body (f)) )
  **  (cm_function_list_rep np rest )
|--
  “ ((INT_MIN) <= (index_pre + 1 )) ”
.

Definition cmc_function_prefix_total_safety_wit_5 := 
forall (target_pre: Z) (index_pre: Z) (fn_pre: Z) (program_pre: Z) (functions_ptr: Z) (functions: (@list cm_function_d)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (f: cm_function_d) (rest: (@list cm_function_d)) (bp: Z) (np: Z) (pp: Z) (lp: Z) (head_count: Z) (PreH1 : (fn_pre <> 0)) (PreH2 : (index_pre <> target_pre)) (PreH3 : (functions = (cons (f) (rest)))) (PreH4 : (cm_function_counts_representable policy p index_pre f )) (PreH5 : (cm_stmt_wf policy p f false (cm_function_body (f)) )) (PreH6 : (cm_functions_counts_representable policy p rest (index_pre + 1 ) )) (PreH7 : (cm_concrete_functions_ready policy p (index_pre + 1 ) rest )) (PreH8 : (cm_i32_code_count (index_pre + 1 ) )) (PreH9 : (cm_wf_program policy cg p )) (PreH10 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH11 : (0 <= index_pre)) (PreH12 : (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) ))) (PreH13 : ((index_pre + (Zlength (functions)) ) <= INT_MAX)) (PreH14 : (cm_functions_counts_representable policy p functions index_pre )) (PreH15 : (cm_concrete_functions_ready policy p index_pre functions )) (PreH16 : (head_count = (cm_function_code_count (policy) (p) (index_pre)))) (PreH17 : (cm_i32_code_count head_count )) ,
  ((( &( "tail_count" ) )) # Int  |->_)
  **  ((( &( "next_fn" ) )) # Ptr  |-> np)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((( &( "target" ) )) # Int64  |-> target_pre)
  **  ((( &( "head_count" ) )) # Int  |-> head_count)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> bp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  (cm_stmt_rep bp (cm_function_body (f)) )
  **  (cm_function_list_rep np rest )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmc_function_prefix_total_safety_wit_6 := 
(
forall (target_pre: Z) (index_pre: Z) (fn_pre: Z) (program_pre: Z) (functions_ptr: Z) (functions: (@list cm_function_d)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (f: cm_function_d) (rest: (@list cm_function_d)) (bp: Z) (np: Z) (pp: Z) (lp: Z) (head_count: Z) (retval: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH3 : (0 <= (index_pre + 1 ))) (PreH4 : ((index_pre + 1 ) = ((Zlength ((cm_program_functions (p)))) - (Zlength (rest)) ))) (PreH5 : (((index_pre + 1 ) + (Zlength (rest)) ) <= INT_MAX)) (PreH6 : (cm_functions_counts_representable policy p rest (index_pre + 1 ) )) (PreH7 : (cm_concrete_functions_ready policy p (index_pre + 1 ) rest )) (PreH8 : (retval = (cm_function_prefix (policy) (p) (rest) ((target_pre - (index_pre + 1 ) ))))) (PreH9 : (cm_i32_code_count retval )) (PreH10 : (fn_pre <> 0)) (PreH11 : (index_pre <> target_pre)) (PreH12 : (functions = (cons (f) (rest)))) (PreH13 : (cm_function_counts_representable policy p index_pre f )) (PreH14 : (cm_stmt_wf policy p f false (cm_function_body (f)) )) (PreH15 : (cm_functions_counts_representable policy p rest (index_pre + 1 ) )) (PreH16 : (cm_concrete_functions_ready policy p (index_pre + 1 ) rest )) (PreH17 : (cm_i32_code_count (index_pre + 1 ) )) (PreH18 : (cm_wf_program policy cg p )) (PreH19 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH20 : (0 <= index_pre)) (PreH21 : (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) ))) (PreH22 : ((index_pre + (Zlength (functions)) ) <= INT_MAX)) (PreH23 : (cm_functions_counts_representable policy p functions index_pre )) (PreH24 : (cm_concrete_functions_ready policy p index_pre functions )) (PreH25 : (head_count = (cm_function_code_count (policy) (p) (index_pre)))) (PreH26 : (cm_i32_code_count head_count )) ,
  ((( &( "result" ) )) # Int  |->_)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep np rest )
  **  ((( &( "tail_count" ) )) # Int  |-> retval)
  **  ((( &( "next_fn" ) )) # Ptr  |-> np)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((( &( "target" ) )) # Int64  |-> target_pre)
  **  ((( &( "head_count" ) )) # Int  |-> head_count)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> bp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  (cm_stmt_rep bp (cm_function_body (f)) )
|--
  “ ((head_count + retval ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (head_count + retval )) ”
) \/
(
forall (target_pre: Z) (index_pre: Z) (fn_pre: Z) (program_pre: Z) (functions_ptr: Z) (functions: (@list cm_function_d)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (f: cm_function_d) (rest: (@list cm_function_d)) (bp: Z) (np: Z) (pp: Z) (lp: Z) (head_count: Z) (retval: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH3 : (0 <= (index_pre + 1 ))) (PreH4 : ((index_pre + 1 ) = ((Zlength ((cm_program_functions (p)))) - (Zlength (rest)) ))) (PreH5 : (((index_pre + 1 ) + (Zlength (rest)) ) <= INT_MAX)) (PreH6 : (cm_functions_counts_representable policy p rest (index_pre + 1 ) )) (PreH7 : (cm_concrete_functions_ready policy p (index_pre + 1 ) rest )) (PreH8 : (retval = (cm_function_prefix (policy) (p) (rest) ((target_pre - (index_pre + 1 ) ))))) (PreH9 : (cm_i32_code_count retval )) (PreH10 : (fn_pre <> 0)) (PreH11 : (index_pre <> target_pre)) (PreH12 : (functions = (cons (f) (rest)))) (PreH13 : (cm_function_counts_representable policy p index_pre f )) (PreH14 : (cm_stmt_wf policy p f false (cm_function_body (f)) )) (PreH15 : (cm_functions_counts_representable policy p rest (index_pre + 1 ) )) (PreH16 : (cm_concrete_functions_ready policy p (index_pre + 1 ) rest )) (PreH17 : (cm_i32_code_count (index_pre + 1 ) )) (PreH18 : (cm_wf_program policy cg p )) (PreH19 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH20 : (0 <= index_pre)) (PreH21 : (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) ))) (PreH22 : ((index_pre + (Zlength (functions)) ) <= INT_MAX)) (PreH23 : (cm_functions_counts_representable policy p functions index_pre )) (PreH24 : (cm_concrete_functions_ready policy p index_pre functions )) (PreH25 : (head_count = (cm_function_code_count (policy) (p) (index_pre)))) (PreH26 : (cm_i32_code_count head_count )) ,
  ((( &( "result" ) )) # Int  |->_)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep np rest )
  **  ((( &( "tail_count" ) )) # Int  |-> retval)
  **  ((( &( "next_fn" ) )) # Ptr  |-> np)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((( &( "target" ) )) # Int64  |-> target_pre)
  **  ((( &( "head_count" ) )) # Int  |-> head_count)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> bp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  (cm_stmt_rep bp (cm_function_body (f)) )
|--
  “ ((head_count + retval ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (head_count + retval )) ”
).

Definition cmc_function_prefix_total_safety_wit_6_split_goal_1 := 
forall (target_pre: Z) (index_pre: Z) (fn_pre: Z) (program_pre: Z) (functions_ptr: Z) (functions: (@list cm_function_d)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (f: cm_function_d) (rest: (@list cm_function_d)) (bp: Z) (np: Z) (pp: Z) (lp: Z) (head_count: Z) (retval: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH3 : (0 <= (index_pre + 1 ))) (PreH4 : ((index_pre + 1 ) = ((Zlength ((cm_program_functions (p)))) - (Zlength (rest)) ))) (PreH5 : (((index_pre + 1 ) + (Zlength (rest)) ) <= INT_MAX)) (PreH6 : (cm_functions_counts_representable policy p rest (index_pre + 1 ) )) (PreH7 : (cm_concrete_functions_ready policy p (index_pre + 1 ) rest )) (PreH8 : (retval = (cm_function_prefix (policy) (p) (rest) ((target_pre - (index_pre + 1 ) ))))) (PreH9 : (cm_i32_code_count retval )) (PreH10 : (fn_pre <> 0)) (PreH11 : (index_pre <> target_pre)) (PreH12 : (functions = (cons (f) (rest)))) (PreH13 : (cm_function_counts_representable policy p index_pre f )) (PreH14 : (cm_stmt_wf policy p f false (cm_function_body (f)) )) (PreH15 : (cm_functions_counts_representable policy p rest (index_pre + 1 ) )) (PreH16 : (cm_concrete_functions_ready policy p (index_pre + 1 ) rest )) (PreH17 : (cm_i32_code_count (index_pre + 1 ) )) (PreH18 : (cm_wf_program policy cg p )) (PreH19 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH20 : (0 <= index_pre)) (PreH21 : (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) ))) (PreH22 : ((index_pre + (Zlength (functions)) ) <= INT_MAX)) (PreH23 : (cm_functions_counts_representable policy p functions index_pre )) (PreH24 : (cm_concrete_functions_ready policy p index_pre functions )) (PreH25 : (head_count = (cm_function_code_count (policy) (p) (index_pre)))) (PreH26 : (cm_i32_code_count head_count )) ,
  ((( &( "result" ) )) # Int  |->_)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep np rest )
  **  ((( &( "tail_count" ) )) # Int  |-> retval)
  **  ((( &( "next_fn" ) )) # Ptr  |-> np)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((( &( "target" ) )) # Int64  |-> target_pre)
  **  ((( &( "head_count" ) )) # Int  |-> head_count)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> bp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  (cm_stmt_rep bp (cm_function_body (f)) )
|--
  “ ((head_count + retval ) <= INT_MAX) ”
.

Definition cmc_function_prefix_total_safety_wit_6_split_goal_2 := 
forall (target_pre: Z) (index_pre: Z) (fn_pre: Z) (program_pre: Z) (functions_ptr: Z) (functions: (@list cm_function_d)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (f: cm_function_d) (rest: (@list cm_function_d)) (bp: Z) (np: Z) (pp: Z) (lp: Z) (head_count: Z) (retval: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH3 : (0 <= (index_pre + 1 ))) (PreH4 : ((index_pre + 1 ) = ((Zlength ((cm_program_functions (p)))) - (Zlength (rest)) ))) (PreH5 : (((index_pre + 1 ) + (Zlength (rest)) ) <= INT_MAX)) (PreH6 : (cm_functions_counts_representable policy p rest (index_pre + 1 ) )) (PreH7 : (cm_concrete_functions_ready policy p (index_pre + 1 ) rest )) (PreH8 : (retval = (cm_function_prefix (policy) (p) (rest) ((target_pre - (index_pre + 1 ) ))))) (PreH9 : (cm_i32_code_count retval )) (PreH10 : (fn_pre <> 0)) (PreH11 : (index_pre <> target_pre)) (PreH12 : (functions = (cons (f) (rest)))) (PreH13 : (cm_function_counts_representable policy p index_pre f )) (PreH14 : (cm_stmt_wf policy p f false (cm_function_body (f)) )) (PreH15 : (cm_functions_counts_representable policy p rest (index_pre + 1 ) )) (PreH16 : (cm_concrete_functions_ready policy p (index_pre + 1 ) rest )) (PreH17 : (cm_i32_code_count (index_pre + 1 ) )) (PreH18 : (cm_wf_program policy cg p )) (PreH19 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH20 : (0 <= index_pre)) (PreH21 : (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) ))) (PreH22 : ((index_pre + (Zlength (functions)) ) <= INT_MAX)) (PreH23 : (cm_functions_counts_representable policy p functions index_pre )) (PreH24 : (cm_concrete_functions_ready policy p index_pre functions )) (PreH25 : (head_count = (cm_function_code_count (policy) (p) (index_pre)))) (PreH26 : (cm_i32_code_count head_count )) ,
  ((( &( "result" ) )) # Int  |->_)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep np rest )
  **  ((( &( "tail_count" ) )) # Int  |-> retval)
  **  ((( &( "next_fn" ) )) # Ptr  |-> np)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((( &( "target" ) )) # Int64  |-> target_pre)
  **  ((( &( "head_count" ) )) # Int  |-> head_count)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> bp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  (cm_stmt_rep bp (cm_function_body (f)) )
|--
  “ ((INT_MIN) <= (head_count + retval )) ”
.

Definition cmc_function_prefix_total_entail_wit_1 := 
(
forall (target_pre: Z) (index_pre: Z) (fn_pre: Z) (program_pre: Z) (functions_ptr: Z) (functions: (@list cm_function_d)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (index_pre <> target_pre)) (PreH2 : (fn_pre <> 0)) (PreH3 : (cm_wf_program policy cg p )) (PreH4 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH5 : (0 <= index_pre)) (PreH6 : (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) ))) (PreH7 : ((index_pre + (Zlength (functions)) ) <= INT_MAX)) (PreH8 : (cm_functions_counts_representable policy p functions index_pre )) (PreH9 : (cm_concrete_functions_ready policy p index_pre functions )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep fn_pre functions )
|--
  EX (bp: Z)  (np: Z)  (f: cm_function_d)  (rest: (@list cm_function_d)) ,
  “ (fn_pre <> 0) ” 
  &&  “ (index_pre <> target_pre) ” 
  &&  “ (functions = (cons (f) (rest))) ” 
  &&  “ (cm_function_counts_representable policy p index_pre f ) ” 
  &&  “ (cm_stmt_wf policy p f false (cm_function_body (f)) ) ” 
  &&  “ (cm_functions_counts_representable policy p rest (index_pre + 1 ) ) ” 
  &&  “ (cm_concrete_functions_ready policy p (index_pre + 1 ) rest ) ” 
  &&  “ (cm_i32_code_count (index_pre + 1 ) ) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) )) ” 
  &&  “ ((index_pre + (Zlength (functions)) ) <= INT_MAX) ” 
  &&  “ (cm_functions_counts_representable policy p functions index_pre ) ” 
  &&  “ (cm_concrete_functions_ready policy p index_pre functions ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f bp np )
  **  (cm_stmt_rep bp (cm_function_body (f)) )
  **  (cm_function_list_rep np rest )
) \/
(
forall (target_pre: Z) (index_pre: Z) (fn_pre: Z) (program_pre: Z) (functions_ptr: Z) (functions: (@list cm_function_d)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (index_pre <> target_pre)) (PreH2 : (fn_pre <> 0)) (PreH3 : (cm_wf_program policy cg p )) (PreH4 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH5 : (0 <= index_pre)) (PreH6 : (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) ))) (PreH7 : ((index_pre + (Zlength (functions)) ) <= INT_MAX)) (PreH8 : (cm_functions_counts_representable policy p functions index_pre )) (PreH9 : (cm_concrete_functions_ready policy p index_pre functions )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep fn_pre functions )
|--
  EX (bp: Z)  (np: Z)  (f: cm_function_d)  (rest: (@list cm_function_d)) ,
  “ (fn_pre <> 0) ” 
  &&  “ (index_pre <> target_pre) ” 
  &&  “ (functions = (cons (f) (rest))) ” 
  &&  “ (cm_function_counts_representable policy p index_pre f ) ” 
  &&  “ (cm_stmt_wf policy p f false (cm_function_body (f)) ) ” 
  &&  “ (cm_functions_counts_representable policy p rest (index_pre + 1 ) ) ” 
  &&  “ (cm_concrete_functions_ready policy p (index_pre + 1 ) rest ) ” 
  &&  “ (cm_i32_code_count (index_pre + 1 ) ) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) )) ” 
  &&  “ ((index_pre + (Zlength (functions)) ) <= INT_MAX) ” 
  &&  “ (cm_functions_counts_representable policy p functions index_pre ) ” 
  &&  “ (cm_concrete_functions_ready policy p index_pre functions ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f bp np )
  **  (cm_stmt_rep bp (cm_function_body (f)) )
  **  (cm_function_list_rep np rest )
).

Definition cmc_function_prefix_total_entail_wit_2 := 
(
forall (target_pre: Z) (index_pre: Z) (fn_pre: Z) (program_pre: Z) (functions_ptr: Z) (functions: (@list cm_function_d)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (f_2: cm_function_d) (rest_2: (@list cm_function_d)) (bp_2: Z) (np_2: Z) (retval: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_function_counts_representable policy p index_pre f_2 )) (PreH3 : (cm_stmt_wf policy p f_2 false (cm_function_body (f_2)) )) (PreH4 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH5 : (retval = (cm_function_code_count (policy) (p) (index_pre)))) (PreH6 : (cm_i32_code_count retval )) (PreH7 : (fn_pre <> 0)) (PreH8 : (index_pre <> target_pre)) (PreH9 : (functions = (cons (f_2) (rest_2)))) (PreH10 : (cm_function_counts_representable policy p index_pre f_2 )) (PreH11 : (cm_stmt_wf policy p f_2 false (cm_function_body (f_2)) )) (PreH12 : (cm_functions_counts_representable policy p rest_2 (index_pre + 1 ) )) (PreH13 : (cm_concrete_functions_ready policy p (index_pre + 1 ) rest_2 )) (PreH14 : (cm_i32_code_count (index_pre + 1 ) )) (PreH15 : (cm_wf_program policy cg p )) (PreH16 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH17 : (0 <= index_pre)) (PreH18 : (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) ))) (PreH19 : ((index_pre + (Zlength (functions)) ) <= INT_MAX)) (PreH20 : (cm_functions_counts_representable policy p functions index_pre )) (PreH21 : (cm_concrete_functions_ready policy p index_pre functions )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f_2 bp_2 np_2 )
  **  (cm_stmt_rep bp_2 (cm_function_body (f_2)) )
  **  (cm_function_list_rep np_2 rest_2 )
|--
  EX (np: Z)  (bp: Z)  (lp: Z)  (pp: Z)  (f: cm_function_d)  (rest: (@list cm_function_d)) ,
  “ (fn_pre <> 0) ” 
  &&  “ (index_pre <> target_pre) ” 
  &&  “ (functions = (cons (f) (rest))) ” 
  &&  “ (cm_function_counts_representable policy p index_pre f ) ” 
  &&  “ (cm_stmt_wf policy p f false (cm_function_body (f)) ) ” 
  &&  “ (cm_functions_counts_representable policy p rest (index_pre + 1 ) ) ” 
  &&  “ (cm_concrete_functions_ready policy p (index_pre + 1 ) rest ) ” 
  &&  “ (cm_i32_code_count (index_pre + 1 ) ) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) )) ” 
  &&  “ ((index_pre + (Zlength (functions)) ) <= INT_MAX) ” 
  &&  “ (cm_functions_counts_representable policy p functions index_pre ) ” 
  &&  “ (cm_concrete_functions_ready policy p index_pre functions ) ” 
  &&  “ (retval = (cm_function_code_count (policy) (p) (index_pre))) ” 
  &&  “ (cm_i32_code_count retval ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> bp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  (cm_stmt_rep bp (cm_function_body (f)) )
  **  (cm_function_list_rep np rest )
) \/
(
forall (target_pre: Z) (index_pre: Z) (fn_pre: Z) (program_pre: Z) (functions_ptr: Z) (functions: (@list cm_function_d)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (f_2: cm_function_d) (rest_2: (@list cm_function_d)) (bp_2: Z) (np_2: Z) (retval: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_function_counts_representable policy p index_pre f_2 )) (PreH3 : (cm_stmt_wf policy p f_2 false (cm_function_body (f_2)) )) (PreH4 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH5 : (retval = (cm_function_code_count (policy) (p) (index_pre)))) (PreH6 : (cm_i32_code_count retval )) (PreH7 : (fn_pre <> 0)) (PreH8 : (index_pre <> target_pre)) (PreH9 : (functions = (cons (f_2) (rest_2)))) (PreH10 : (cm_function_counts_representable policy p index_pre f_2 )) (PreH11 : (cm_stmt_wf policy p f_2 false (cm_function_body (f_2)) )) (PreH12 : (cm_functions_counts_representable policy p rest_2 (index_pre + 1 ) )) (PreH13 : (cm_concrete_functions_ready policy p (index_pre + 1 ) rest_2 )) (PreH14 : (cm_i32_code_count (index_pre + 1 ) )) (PreH15 : (cm_wf_program policy cg p )) (PreH16 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH17 : (0 <= index_pre)) (PreH18 : (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) ))) (PreH19 : ((index_pre + (Zlength (functions)) ) <= INT_MAX)) (PreH20 : (cm_functions_counts_representable policy p functions index_pre )) (PreH21 : (cm_concrete_functions_ready policy p index_pre functions )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f_2 bp_2 np_2 )
  **  (cm_stmt_rep bp_2 (cm_function_body (f_2)) )
  **  (cm_function_list_rep np_2 rest_2 )
|--
  EX (np: Z)  (bp: Z)  (lp: Z)  (pp: Z)  (f: cm_function_d)  (rest: (@list cm_function_d)) ,
  “ (fn_pre <> 0) ” 
  &&  “ (index_pre <> target_pre) ” 
  &&  “ (functions = (cons (f) (rest))) ” 
  &&  “ (cm_function_counts_representable policy p index_pre f ) ” 
  &&  “ (cm_stmt_wf policy p f false (cm_function_body (f)) ) ” 
  &&  “ (cm_functions_counts_representable policy p rest (index_pre + 1 ) ) ” 
  &&  “ (cm_concrete_functions_ready policy p (index_pre + 1 ) rest ) ” 
  &&  “ (cm_i32_code_count (index_pre + 1 ) ) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) )) ” 
  &&  “ ((index_pre + (Zlength (functions)) ) <= INT_MAX) ” 
  &&  “ (cm_functions_counts_representable policy p functions index_pre ) ” 
  &&  “ (cm_concrete_functions_ready policy p index_pre functions ) ” 
  &&  “ (retval = (cm_function_code_count (policy) (p) (index_pre))) ” 
  &&  “ (cm_i32_code_count retval ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> bp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  (cm_stmt_rep bp (cm_function_body (f)) )
  **  (cm_function_list_rep np rest )
).

Definition cmc_function_prefix_total_return_wit_1 := 
(
forall (target_pre: Z) (index_pre: Z) (fn_pre: Z) (program_pre: Z) (functions_ptr: Z) (functions: (@list cm_function_d)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (f: cm_function_d) (rest: (@list cm_function_d)) (bp: Z) (np: Z) (pp: Z) (lp: Z) (head_count: Z) (retval: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH3 : (0 <= (index_pre + 1 ))) (PreH4 : ((index_pre + 1 ) = ((Zlength ((cm_program_functions (p)))) - (Zlength (rest)) ))) (PreH5 : (((index_pre + 1 ) + (Zlength (rest)) ) <= INT_MAX)) (PreH6 : (cm_functions_counts_representable policy p rest (index_pre + 1 ) )) (PreH7 : (cm_concrete_functions_ready policy p (index_pre + 1 ) rest )) (PreH8 : (retval = (cm_function_prefix (policy) (p) (rest) ((target_pre - (index_pre + 1 ) ))))) (PreH9 : (cm_i32_code_count retval )) (PreH10 : (fn_pre <> 0)) (PreH11 : (index_pre <> target_pre)) (PreH12 : (functions = (cons (f) (rest)))) (PreH13 : (cm_function_counts_representable policy p index_pre f )) (PreH14 : (cm_stmt_wf policy p f false (cm_function_body (f)) )) (PreH15 : (cm_functions_counts_representable policy p rest (index_pre + 1 ) )) (PreH16 : (cm_concrete_functions_ready policy p (index_pre + 1 ) rest )) (PreH17 : (cm_i32_code_count (index_pre + 1 ) )) (PreH18 : (cm_wf_program policy cg p )) (PreH19 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH20 : (0 <= index_pre)) (PreH21 : (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) ))) (PreH22 : ((index_pre + (Zlength (functions)) ) <= INT_MAX)) (PreH23 : (cm_functions_counts_representable policy p functions index_pre )) (PreH24 : (cm_concrete_functions_ready policy p index_pre functions )) (PreH25 : (head_count = (cm_function_code_count (policy) (p) (index_pre)))) (PreH26 : (cm_i32_code_count head_count )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep np rest )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> bp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  (cm_stmt_rep bp (cm_function_body (f)) )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) )) ” 
  &&  “ ((index_pre + (Zlength (functions)) ) <= INT_MAX) ” 
  &&  “ (cm_functions_counts_representable policy p functions index_pre ) ” 
  &&  “ (cm_concrete_functions_ready policy p index_pre functions ) ” 
  &&  “ ((head_count + retval ) = (cm_function_prefix (policy) (p) (functions) ((target_pre - index_pre )))) ” 
  &&  “ (cm_i32_code_count (head_count + retval ) ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep fn_pre functions )
) \/
(
forall (target_pre: Z) (index_pre: Z) (fn_pre: Z) (program_pre: Z) (functions_ptr: Z) (functions: (@list cm_function_d)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (f: cm_function_d) (rest: (@list cm_function_d)) (bp: Z) (np: Z) (pp: Z) (lp: Z) (head_count: Z) (retval: Z) (PreH1 : ((cm_type_encode ((cm_function_ret (f)))) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_function_ret (f)))) >= INT_MIN)) (PreH3 : (cm_wf_program policy cg p )) (PreH4 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH5 : (0 <= (index_pre + 1 ))) (PreH6 : ((index_pre + 1 ) = ((Zlength ((cm_program_functions (p)))) - (Zlength (rest)) ))) (PreH7 : (((index_pre + 1 ) + (Zlength (rest)) ) <= INT_MAX)) (PreH8 : (cm_functions_counts_representable policy p rest (index_pre + 1 ) )) (PreH9 : (cm_concrete_functions_ready policy p (index_pre + 1 ) rest )) (PreH10 : (retval = (cm_function_prefix (policy) (p) (rest) ((target_pre - (index_pre + 1 ) ))))) (PreH11 : (cm_i32_code_count retval )) (PreH12 : (fn_pre <> 0)) (PreH13 : (index_pre <> target_pre)) (PreH14 : (functions = (cons (f) (rest)))) (PreH15 : (cm_function_counts_representable policy p index_pre f )) (PreH16 : (cm_stmt_wf policy p f false (cm_function_body (f)) )) (PreH17 : (cm_functions_counts_representable policy p rest (index_pre + 1 ) )) (PreH18 : (cm_concrete_functions_ready policy p (index_pre + 1 ) rest )) (PreH19 : (cm_i32_code_count (index_pre + 1 ) )) (PreH20 : (cm_wf_program policy cg p )) (PreH21 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH22 : (0 <= index_pre)) (PreH23 : (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) ))) (PreH24 : ((index_pre + (Zlength (functions)) ) <= INT_MAX)) (PreH25 : (cm_functions_counts_representable policy p functions index_pre )) (PreH26 : (cm_concrete_functions_ready policy p index_pre functions )) (PreH27 : (head_count = (cm_function_code_count (policy) (p) (index_pre)))) (PreH28 : (cm_i32_code_count head_count )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep np rest )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> bp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  (cm_stmt_rep bp (cm_function_body (f)) )
|--
  “ (cm_i32_code_count (head_count + retval ) ) ” 
  &&  “ ((head_count + retval ) = (cm_function_prefix (policy) (p) (functions) ((target_pre - index_pre )))) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep fn_pre functions )
).

Definition cmc_function_prefix_total_return_wit_1_split_goal_1 := 
forall (target_pre: Z) (index_pre: Z) (fn_pre: Z) (program_pre: Z) (functions_ptr: Z) (functions: (@list cm_function_d)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (f: cm_function_d) (rest: (@list cm_function_d)) (bp: Z) (np: Z) (pp: Z) (lp: Z) (head_count: Z) (retval: Z) (PreH1 : ((cm_type_encode ((cm_function_ret (f)))) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_function_ret (f)))) >= INT_MIN)) (PreH3 : (cm_wf_program policy cg p )) (PreH4 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH5 : (0 <= (index_pre + 1 ))) (PreH6 : ((index_pre + 1 ) = ((Zlength ((cm_program_functions (p)))) - (Zlength (rest)) ))) (PreH7 : (((index_pre + 1 ) + (Zlength (rest)) ) <= INT_MAX)) (PreH8 : (cm_functions_counts_representable policy p rest (index_pre + 1 ) )) (PreH9 : (cm_concrete_functions_ready policy p (index_pre + 1 ) rest )) (PreH10 : (retval = (cm_function_prefix (policy) (p) (rest) ((target_pre - (index_pre + 1 ) ))))) (PreH11 : (cm_i32_code_count retval )) (PreH12 : (fn_pre <> 0)) (PreH13 : (index_pre <> target_pre)) (PreH14 : (functions = (cons (f) (rest)))) (PreH15 : (cm_function_counts_representable policy p index_pre f )) (PreH16 : (cm_stmt_wf policy p f false (cm_function_body (f)) )) (PreH17 : (cm_functions_counts_representable policy p rest (index_pre + 1 ) )) (PreH18 : (cm_concrete_functions_ready policy p (index_pre + 1 ) rest )) (PreH19 : (cm_i32_code_count (index_pre + 1 ) )) (PreH20 : (cm_wf_program policy cg p )) (PreH21 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH22 : (0 <= index_pre)) (PreH23 : (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) ))) (PreH24 : ((index_pre + (Zlength (functions)) ) <= INT_MAX)) (PreH25 : (cm_functions_counts_representable policy p functions index_pre )) (PreH26 : (cm_concrete_functions_ready policy p index_pre functions )) (PreH27 : (head_count = (cm_function_code_count (policy) (p) (index_pre)))) (PreH28 : (cm_i32_code_count head_count )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep np rest )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> bp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  (cm_stmt_rep bp (cm_function_body (f)) )
|--
  “ (cm_i32_code_count (head_count + retval ) ) ”
.

Definition cmc_function_prefix_total_return_wit_1_split_goal_2 := 
forall (target_pre: Z) (index_pre: Z) (fn_pre: Z) (program_pre: Z) (functions_ptr: Z) (functions: (@list cm_function_d)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (f: cm_function_d) (rest: (@list cm_function_d)) (bp: Z) (np: Z) (pp: Z) (lp: Z) (head_count: Z) (retval: Z) (PreH1 : ((cm_type_encode ((cm_function_ret (f)))) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_function_ret (f)))) >= INT_MIN)) (PreH3 : (cm_wf_program policy cg p )) (PreH4 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH5 : (0 <= (index_pre + 1 ))) (PreH6 : ((index_pre + 1 ) = ((Zlength ((cm_program_functions (p)))) - (Zlength (rest)) ))) (PreH7 : (((index_pre + 1 ) + (Zlength (rest)) ) <= INT_MAX)) (PreH8 : (cm_functions_counts_representable policy p rest (index_pre + 1 ) )) (PreH9 : (cm_concrete_functions_ready policy p (index_pre + 1 ) rest )) (PreH10 : (retval = (cm_function_prefix (policy) (p) (rest) ((target_pre - (index_pre + 1 ) ))))) (PreH11 : (cm_i32_code_count retval )) (PreH12 : (fn_pre <> 0)) (PreH13 : (index_pre <> target_pre)) (PreH14 : (functions = (cons (f) (rest)))) (PreH15 : (cm_function_counts_representable policy p index_pre f )) (PreH16 : (cm_stmt_wf policy p f false (cm_function_body (f)) )) (PreH17 : (cm_functions_counts_representable policy p rest (index_pre + 1 ) )) (PreH18 : (cm_concrete_functions_ready policy p (index_pre + 1 ) rest )) (PreH19 : (cm_i32_code_count (index_pre + 1 ) )) (PreH20 : (cm_wf_program policy cg p )) (PreH21 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH22 : (0 <= index_pre)) (PreH23 : (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) ))) (PreH24 : ((index_pre + (Zlength (functions)) ) <= INT_MAX)) (PreH25 : (cm_functions_counts_representable policy p functions index_pre )) (PreH26 : (cm_concrete_functions_ready policy p index_pre functions )) (PreH27 : (head_count = (cm_function_code_count (policy) (p) (index_pre)))) (PreH28 : (cm_i32_code_count head_count )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep np rest )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> bp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  (cm_stmt_rep bp (cm_function_body (f)) )
|--
  “ ((head_count + retval ) = (cm_function_prefix (policy) (p) (functions) ((target_pre - index_pre )))) ”
.

Definition cmc_function_prefix_total_return_wit_1_split_goal_spatial := 
forall (target_pre: Z) (index_pre: Z) (fn_pre: Z) (program_pre: Z) (functions_ptr: Z) (functions: (@list cm_function_d)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (f: cm_function_d) (rest: (@list cm_function_d)) (bp: Z) (np: Z) (pp: Z) (lp: Z) (head_count: Z) (retval: Z) (PreH1 : ((cm_type_encode ((cm_function_ret (f)))) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_function_ret (f)))) >= INT_MIN)) (PreH3 : (cm_wf_program policy cg p )) (PreH4 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH5 : (0 <= (index_pre + 1 ))) (PreH6 : ((index_pre + 1 ) = ((Zlength ((cm_program_functions (p)))) - (Zlength (rest)) ))) (PreH7 : (((index_pre + 1 ) + (Zlength (rest)) ) <= INT_MAX)) (PreH8 : (cm_functions_counts_representable policy p rest (index_pre + 1 ) )) (PreH9 : (cm_concrete_functions_ready policy p (index_pre + 1 ) rest )) (PreH10 : (retval = (cm_function_prefix (policy) (p) (rest) ((target_pre - (index_pre + 1 ) ))))) (PreH11 : (cm_i32_code_count retval )) (PreH12 : (fn_pre <> 0)) (PreH13 : (index_pre <> target_pre)) (PreH14 : (functions = (cons (f) (rest)))) (PreH15 : (cm_function_counts_representable policy p index_pre f )) (PreH16 : (cm_stmt_wf policy p f false (cm_function_body (f)) )) (PreH17 : (cm_functions_counts_representable policy p rest (index_pre + 1 ) )) (PreH18 : (cm_concrete_functions_ready policy p (index_pre + 1 ) rest )) (PreH19 : (cm_i32_code_count (index_pre + 1 ) )) (PreH20 : (cm_wf_program policy cg p )) (PreH21 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH22 : (0 <= index_pre)) (PreH23 : (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) ))) (PreH24 : ((index_pre + (Zlength (functions)) ) <= INT_MAX)) (PreH25 : (cm_functions_counts_representable policy p functions index_pre )) (PreH26 : (cm_concrete_functions_ready policy p index_pre functions )) (PreH27 : (head_count = (cm_function_code_count (policy) (p) (index_pre)))) (PreH28 : (cm_i32_code_count head_count )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep np rest )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> bp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  (cm_stmt_rep bp (cm_function_body (f)) )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep fn_pre functions )
.

Definition cmc_function_prefix_total_return_wit_2 := 
(
forall (target_pre: Z) (index_pre: Z) (fn_pre: Z) (program_pre: Z) (functions_ptr: Z) (functions: (@list cm_function_d)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (index_pre = target_pre)) (PreH2 : (fn_pre <> 0)) (PreH3 : (cm_wf_program policy cg p )) (PreH4 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH5 : (0 <= index_pre)) (PreH6 : (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) ))) (PreH7 : ((index_pre + (Zlength (functions)) ) <= INT_MAX)) (PreH8 : (cm_functions_counts_representable policy p functions index_pre )) (PreH9 : (cm_concrete_functions_ready policy p index_pre functions )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep fn_pre functions )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) )) ” 
  &&  “ ((index_pre + (Zlength (functions)) ) <= INT_MAX) ” 
  &&  “ (cm_functions_counts_representable policy p functions index_pre ) ” 
  &&  “ (cm_concrete_functions_ready policy p index_pre functions ) ” 
  &&  “ (0 = (cm_function_prefix (policy) (p) (functions) ((target_pre - index_pre )))) ” 
  &&  “ (cm_i32_code_count 0 ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep fn_pre functions )
) \/
(
forall (target_pre: Z) (index_pre: Z) (fn_pre: Z) (functions: (@list cm_function_d)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (index_pre = target_pre)) (PreH2 : (fn_pre <> 0)) (PreH3 : (cm_wf_program policy cg p )) (PreH4 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH5 : (0 <= index_pre)) (PreH6 : (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) ))) (PreH7 : ((index_pre + (Zlength (functions)) ) <= INT_MAX)) (PreH8 : (cm_functions_counts_representable policy p functions index_pre )) (PreH9 : (cm_concrete_functions_ready policy p index_pre functions )) ,
  TT && emp 
|--
  “ (cm_i32_code_count 0 ) ” 
  &&  “ (0 = (cm_function_prefix (policy) (p) (functions) ((target_pre - target_pre )))) ”
  &&  emp
).

Definition cmc_function_prefix_total_return_wit_2_split_goal_1 := 
forall (target_pre: Z) (index_pre: Z) (fn_pre: Z) (functions: (@list cm_function_d)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (index_pre = target_pre)) (PreH2 : (fn_pre <> 0)) (PreH3 : (cm_wf_program policy cg p )) (PreH4 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH5 : (0 <= index_pre)) (PreH6 : (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) ))) (PreH7 : ((index_pre + (Zlength (functions)) ) <= INT_MAX)) (PreH8 : (cm_functions_counts_representable policy p functions index_pre )) (PreH9 : (cm_concrete_functions_ready policy p index_pre functions )) ,
  (cm_i32_code_count 0 )
.

Definition cmc_function_prefix_total_return_wit_2_split_goal_2 := 
forall (target_pre: Z) (index_pre: Z) (fn_pre: Z) (functions: (@list cm_function_d)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (index_pre = target_pre)) (PreH2 : (fn_pre <> 0)) (PreH3 : (cm_wf_program policy cg p )) (PreH4 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH5 : (0 <= index_pre)) (PreH6 : (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) ))) (PreH7 : ((index_pre + (Zlength (functions)) ) <= INT_MAX)) (PreH8 : (cm_functions_counts_representable policy p functions index_pre )) (PreH9 : (cm_concrete_functions_ready policy p index_pre functions )) ,
  (0 = (cm_function_prefix (policy) (p) (functions) ((target_pre - target_pre ))))
.

Definition cmc_function_prefix_total_return_wit_3 := 
(
forall (target_pre: Z) (index_pre: Z) (fn_pre: Z) (program_pre: Z) (functions_ptr: Z) (functions: (@list cm_function_d)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (fn_pre = 0)) (PreH2 : (cm_wf_program policy cg p )) (PreH3 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH4 : (0 <= index_pre)) (PreH5 : (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) ))) (PreH6 : ((index_pre + (Zlength (functions)) ) <= INT_MAX)) (PreH7 : (cm_functions_counts_representable policy p functions index_pre )) (PreH8 : (cm_concrete_functions_ready policy p index_pre functions )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep fn_pre functions )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) )) ” 
  &&  “ ((index_pre + (Zlength (functions)) ) <= INT_MAX) ” 
  &&  “ (cm_functions_counts_representable policy p functions index_pre ) ” 
  &&  “ (cm_concrete_functions_ready policy p index_pre functions ) ” 
  &&  “ (0 = (cm_function_prefix (policy) (p) (functions) ((target_pre - index_pre )))) ” 
  &&  “ (cm_i32_code_count 0 ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep fn_pre functions )
) \/
(
forall (target_pre: Z) (index_pre: Z) (fn_pre: Z) (functions: (@list cm_function_d)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (fn_pre = 0)) (PreH2 : (cm_wf_program policy cg p )) (PreH3 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH4 : (0 <= index_pre)) (PreH5 : (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) ))) (PreH6 : ((index_pre + (Zlength (functions)) ) <= INT_MAX)) (PreH7 : (cm_functions_counts_representable policy p functions index_pre )) (PreH8 : (cm_concrete_functions_ready policy p index_pre functions )) ,
  TT && emp 
|--
  “ (cm_i32_code_count 0 ) ” 
  &&  “ (0 = (cm_function_prefix (policy) (p) (functions) ((target_pre - index_pre )))) ”
  &&  emp
).

Definition cmc_function_prefix_total_return_wit_3_split_goal_1 := 
forall (index_pre: Z) (fn_pre: Z) (functions: (@list cm_function_d)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (fn_pre = 0)) (PreH2 : (cm_wf_program policy cg p )) (PreH3 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH4 : (0 <= index_pre)) (PreH5 : (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) ))) (PreH6 : ((index_pre + (Zlength (functions)) ) <= INT_MAX)) (PreH7 : (cm_functions_counts_representable policy p functions index_pre )) (PreH8 : (cm_concrete_functions_ready policy p index_pre functions )) ,
  (cm_i32_code_count 0 )
.

Definition cmc_function_prefix_total_return_wit_3_split_goal_2 := 
forall (target_pre: Z) (index_pre: Z) (fn_pre: Z) (functions: (@list cm_function_d)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (fn_pre = 0)) (PreH2 : (cm_wf_program policy cg p )) (PreH3 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH4 : (0 <= index_pre)) (PreH5 : (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) ))) (PreH6 : ((index_pre + (Zlength (functions)) ) <= INT_MAX)) (PreH7 : (cm_functions_counts_representable policy p functions index_pre )) (PreH8 : (cm_concrete_functions_ready policy p index_pre functions )) ,
  (0 = (cm_function_prefix (policy) (p) (functions) ((target_pre - index_pre ))))
.

Definition cmc_function_prefix_total_partial_solve_wit_1_pure := 
forall (target_pre: Z) (index_pre: Z) (fn_pre: Z) (program_pre: Z) (functions_ptr: Z) (functions: (@list cm_function_d)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (f: cm_function_d) (rest: (@list cm_function_d)) (bp: Z) (np: Z) (PreH1 : (fn_pre <> 0)) (PreH2 : (index_pre <> target_pre)) (PreH3 : (functions = (cons (f) (rest)))) (PreH4 : (cm_function_counts_representable policy p index_pre f )) (PreH5 : (cm_stmt_wf policy p f false (cm_function_body (f)) )) (PreH6 : (cm_functions_counts_representable policy p rest (index_pre + 1 ) )) (PreH7 : (cm_concrete_functions_ready policy p (index_pre + 1 ) rest )) (PreH8 : (cm_i32_code_count (index_pre + 1 ) )) (PreH9 : (cm_wf_program policy cg p )) (PreH10 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH11 : (0 <= index_pre)) (PreH12 : (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) ))) (PreH13 : ((index_pre + (Zlength (functions)) ) <= INT_MAX)) (PreH14 : (cm_functions_counts_representable policy p functions index_pre )) (PreH15 : (cm_concrete_functions_ready policy p index_pre functions )) ,
  ((( &( "head_count" ) )) # Int  |->_)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((( &( "target" ) )) # Int64  |-> target_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f bp np )
  **  (cm_stmt_rep bp (cm_function_body (f)) )
  **  (cm_function_list_rep np rest )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_function_counts_representable policy p index_pre f ) ” 
  &&  “ (cm_stmt_wf policy p f false (cm_function_body (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ”
.

Definition cmc_function_prefix_total_partial_solve_wit_1_aux := 
forall (target_pre: Z) (index_pre: Z) (fn_pre: Z) (program_pre: Z) (functions_ptr: Z) (functions: (@list cm_function_d)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (f: cm_function_d) (rest: (@list cm_function_d)) (bp: Z) (np: Z) (PreH1 : (fn_pre <> 0)) (PreH2 : (index_pre <> target_pre)) (PreH3 : (functions = (cons (f) (rest)))) (PreH4 : (cm_function_counts_representable policy p index_pre f )) (PreH5 : (cm_stmt_wf policy p f false (cm_function_body (f)) )) (PreH6 : (cm_functions_counts_representable policy p rest (index_pre + 1 ) )) (PreH7 : (cm_concrete_functions_ready policy p (index_pre + 1 ) rest )) (PreH8 : (cm_i32_code_count (index_pre + 1 ) )) (PreH9 : (cm_wf_program policy cg p )) (PreH10 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH11 : (0 <= index_pre)) (PreH12 : (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) ))) (PreH13 : ((index_pre + (Zlength (functions)) ) <= INT_MAX)) (PreH14 : (cm_functions_counts_representable policy p functions index_pre )) (PreH15 : (cm_concrete_functions_ready policy p index_pre functions )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f bp np )
  **  (cm_stmt_rep bp (cm_function_body (f)) )
  **  (cm_function_list_rep np rest )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_function_counts_representable policy p index_pre f ) ” 
  &&  “ (cm_stmt_wf policy p f false (cm_function_body (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (fn_pre <> 0) ” 
  &&  “ (index_pre <> target_pre) ” 
  &&  “ (functions = (cons (f) (rest))) ” 
  &&  “ (cm_function_counts_representable policy p index_pre f ) ” 
  &&  “ (cm_stmt_wf policy p f false (cm_function_body (f)) ) ” 
  &&  “ (cm_functions_counts_representable policy p rest (index_pre + 1 ) ) ” 
  &&  “ (cm_concrete_functions_ready policy p (index_pre + 1 ) rest ) ” 
  &&  “ (cm_i32_code_count (index_pre + 1 ) ) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) )) ” 
  &&  “ ((index_pre + (Zlength (functions)) ) <= INT_MAX) ” 
  &&  “ (cm_functions_counts_representable policy p functions index_pre ) ” 
  &&  “ (cm_concrete_functions_ready policy p index_pre functions ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f bp np )
  **  (cm_stmt_rep bp (cm_function_body (f)) )
  **  (cm_function_list_rep np rest )
.

Definition cmc_function_prefix_total_partial_solve_wit_1 := cmc_function_prefix_total_partial_solve_wit_1_pure -> cmc_function_prefix_total_partial_solve_wit_1_aux.

Definition cmc_function_prefix_total_partial_solve_wit_2_pure := 
(
forall (target_pre: Z) (index_pre: Z) (fn_pre: Z) (program_pre: Z) (functions_ptr: Z) (functions: (@list cm_function_d)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (f: cm_function_d) (rest: (@list cm_function_d)) (bp: Z) (np: Z) (pp: Z) (lp: Z) (head_count: Z) (PreH1 : (fn_pre <> 0)) (PreH2 : (index_pre <> target_pre)) (PreH3 : (functions = (cons (f) (rest)))) (PreH4 : (cm_function_counts_representable policy p index_pre f )) (PreH5 : (cm_stmt_wf policy p f false (cm_function_body (f)) )) (PreH6 : (cm_functions_counts_representable policy p rest (index_pre + 1 ) )) (PreH7 : (cm_concrete_functions_ready policy p (index_pre + 1 ) rest )) (PreH8 : (cm_i32_code_count (index_pre + 1 ) )) (PreH9 : (cm_wf_program policy cg p )) (PreH10 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH11 : (0 <= index_pre)) (PreH12 : (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) ))) (PreH13 : ((index_pre + (Zlength (functions)) ) <= INT_MAX)) (PreH14 : (cm_functions_counts_representable policy p functions index_pre )) (PreH15 : (cm_concrete_functions_ready policy p index_pre functions )) (PreH16 : (head_count = (cm_function_code_count (policy) (p) (index_pre)))) (PreH17 : (cm_i32_code_count head_count )) ,
  ((( &( "tail_count" ) )) # Int  |->_)
  **  ((( &( "next_fn" ) )) # Ptr  |-> np)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((( &( "target" ) )) # Int64  |-> target_pre)
  **  ((( &( "head_count" ) )) # Int  |-> head_count)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> bp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  (cm_stmt_rep bp (cm_function_body (f)) )
  **  (cm_function_list_rep np rest )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (0 <= (index_pre + 1 )) ” 
  &&  “ (cm_functions_counts_representable policy p rest (index_pre + 1 ) ) ” 
  &&  “ (cm_concrete_functions_ready policy p (index_pre + 1 ) rest ) ” 
  &&  “ (((index_pre + 1 ) + (Zlength (rest)) ) <= INT_MAX) ” 
  &&  “ ((index_pre + 1 ) = ((Zlength ((cm_program_functions (p)))) - (Zlength (rest)) )) ”
) \/
(
forall (target_pre: Z) (index_pre: Z) (fn_pre: Z) (program_pre: Z) (functions_ptr: Z) (functions: (@list cm_function_d)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (f: cm_function_d) (rest: (@list cm_function_d)) (bp: Z) (np: Z) (pp: Z) (lp: Z) (head_count: Z) (PreH1 : (target_pre <= INT64_MAX)) (PreH2 : (target_pre >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_function_ret (f)))) <= INT_MAX)) (PreH4 : (head_count <= INT_MAX)) (PreH5 : (index_pre <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_function_ret (f)))) >= INT_MIN)) (PreH7 : (head_count >= INT_MIN)) (PreH8 : (index_pre >= INT_MIN)) (PreH9 : (fn_pre <> 0)) (PreH10 : (index_pre <> target_pre)) (PreH11 : (functions = (cons (f) (rest)))) (PreH12 : (cm_function_counts_representable policy p index_pre f )) (PreH13 : (cm_stmt_wf policy p f false (cm_function_body (f)) )) (PreH14 : (cm_functions_counts_representable policy p rest (index_pre + 1 ) )) (PreH15 : (cm_concrete_functions_ready policy p (index_pre + 1 ) rest )) (PreH16 : (cm_i32_code_count (index_pre + 1 ) )) (PreH17 : (cm_wf_program policy cg p )) (PreH18 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH19 : (0 <= index_pre)) (PreH20 : (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) ))) (PreH21 : ((index_pre + (Zlength (functions)) ) <= INT_MAX)) (PreH22 : (cm_functions_counts_representable policy p functions index_pre )) (PreH23 : (cm_concrete_functions_ready policy p index_pre functions )) (PreH24 : (head_count = (cm_function_code_count (policy) (p) (index_pre)))) (PreH25 : (cm_i32_code_count head_count )) ,
  ((( &( "tail_count" ) )) # Int  |->_)
  **  ((( &( "next_fn" ) )) # Ptr  |-> np)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((( &( "target" ) )) # Int64  |-> target_pre)
  **  ((( &( "head_count" ) )) # Int  |-> head_count)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> bp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  (cm_stmt_rep bp (cm_function_body (f)) )
  **  (cm_function_list_rep np rest )
|--
  “ ((index_pre + 1 ) = ((Zlength ((cm_program_functions (p)))) - (Zlength (rest)) )) ” 
  &&  “ (((index_pre + 1 ) + (Zlength (rest)) ) <= INT_MAX) ”
).

Definition cmc_function_prefix_total_partial_solve_wit_2_pure_split_goal_1 := 
forall (target_pre: Z) (index_pre: Z) (fn_pre: Z) (program_pre: Z) (functions_ptr: Z) (functions: (@list cm_function_d)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (f: cm_function_d) (rest: (@list cm_function_d)) (bp: Z) (np: Z) (pp: Z) (lp: Z) (head_count: Z) (PreH1 : (target_pre <= INT64_MAX)) (PreH2 : (target_pre >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_function_ret (f)))) <= INT_MAX)) (PreH4 : (head_count <= INT_MAX)) (PreH5 : (index_pre <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_function_ret (f)))) >= INT_MIN)) (PreH7 : (head_count >= INT_MIN)) (PreH8 : (index_pre >= INT_MIN)) (PreH9 : (fn_pre <> 0)) (PreH10 : (index_pre <> target_pre)) (PreH11 : (functions = (cons (f) (rest)))) (PreH12 : (cm_function_counts_representable policy p index_pre f )) (PreH13 : (cm_stmt_wf policy p f false (cm_function_body (f)) )) (PreH14 : (cm_functions_counts_representable policy p rest (index_pre + 1 ) )) (PreH15 : (cm_concrete_functions_ready policy p (index_pre + 1 ) rest )) (PreH16 : (cm_i32_code_count (index_pre + 1 ) )) (PreH17 : (cm_wf_program policy cg p )) (PreH18 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH19 : (0 <= index_pre)) (PreH20 : (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) ))) (PreH21 : ((index_pre + (Zlength (functions)) ) <= INT_MAX)) (PreH22 : (cm_functions_counts_representable policy p functions index_pre )) (PreH23 : (cm_concrete_functions_ready policy p index_pre functions )) (PreH24 : (head_count = (cm_function_code_count (policy) (p) (index_pre)))) (PreH25 : (cm_i32_code_count head_count )) ,
  ((( &( "tail_count" ) )) # Int  |->_)
  **  ((( &( "next_fn" ) )) # Ptr  |-> np)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((( &( "target" ) )) # Int64  |-> target_pre)
  **  ((( &( "head_count" ) )) # Int  |-> head_count)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> bp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  (cm_stmt_rep bp (cm_function_body (f)) )
  **  (cm_function_list_rep np rest )
|--
  “ ((index_pre + 1 ) = ((Zlength ((cm_program_functions (p)))) - (Zlength (rest)) )) ”
.

Definition cmc_function_prefix_total_partial_solve_wit_2_pure_split_goal_2 := 
forall (target_pre: Z) (index_pre: Z) (fn_pre: Z) (program_pre: Z) (functions_ptr: Z) (functions: (@list cm_function_d)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (f: cm_function_d) (rest: (@list cm_function_d)) (bp: Z) (np: Z) (pp: Z) (lp: Z) (head_count: Z) (PreH1 : (target_pre <= INT64_MAX)) (PreH2 : (target_pre >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_function_ret (f)))) <= INT_MAX)) (PreH4 : (head_count <= INT_MAX)) (PreH5 : (index_pre <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_function_ret (f)))) >= INT_MIN)) (PreH7 : (head_count >= INT_MIN)) (PreH8 : (index_pre >= INT_MIN)) (PreH9 : (fn_pre <> 0)) (PreH10 : (index_pre <> target_pre)) (PreH11 : (functions = (cons (f) (rest)))) (PreH12 : (cm_function_counts_representable policy p index_pre f )) (PreH13 : (cm_stmt_wf policy p f false (cm_function_body (f)) )) (PreH14 : (cm_functions_counts_representable policy p rest (index_pre + 1 ) )) (PreH15 : (cm_concrete_functions_ready policy p (index_pre + 1 ) rest )) (PreH16 : (cm_i32_code_count (index_pre + 1 ) )) (PreH17 : (cm_wf_program policy cg p )) (PreH18 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH19 : (0 <= index_pre)) (PreH20 : (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) ))) (PreH21 : ((index_pre + (Zlength (functions)) ) <= INT_MAX)) (PreH22 : (cm_functions_counts_representable policy p functions index_pre )) (PreH23 : (cm_concrete_functions_ready policy p index_pre functions )) (PreH24 : (head_count = (cm_function_code_count (policy) (p) (index_pre)))) (PreH25 : (cm_i32_code_count head_count )) ,
  ((( &( "tail_count" ) )) # Int  |->_)
  **  ((( &( "next_fn" ) )) # Ptr  |-> np)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((( &( "target" ) )) # Int64  |-> target_pre)
  **  ((( &( "head_count" ) )) # Int  |-> head_count)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> bp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  (cm_stmt_rep bp (cm_function_body (f)) )
  **  (cm_function_list_rep np rest )
|--
  “ (((index_pre + 1 ) + (Zlength (rest)) ) <= INT_MAX) ”
.

Definition cmc_function_prefix_total_partial_solve_wit_2_aux := 
forall (target_pre: Z) (index_pre: Z) (fn_pre: Z) (program_pre: Z) (functions_ptr: Z) (functions: (@list cm_function_d)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (f: cm_function_d) (rest: (@list cm_function_d)) (bp: Z) (np: Z) (pp: Z) (lp: Z) (head_count: Z) (PreH1 : (fn_pre <> 0)) (PreH2 : (index_pre <> target_pre)) (PreH3 : (functions = (cons (f) (rest)))) (PreH4 : (cm_function_counts_representable policy p index_pre f )) (PreH5 : (cm_stmt_wf policy p f false (cm_function_body (f)) )) (PreH6 : (cm_functions_counts_representable policy p rest (index_pre + 1 ) )) (PreH7 : (cm_concrete_functions_ready policy p (index_pre + 1 ) rest )) (PreH8 : (cm_i32_code_count (index_pre + 1 ) )) (PreH9 : (cm_wf_program policy cg p )) (PreH10 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH11 : (0 <= index_pre)) (PreH12 : (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) ))) (PreH13 : ((index_pre + (Zlength (functions)) ) <= INT_MAX)) (PreH14 : (cm_functions_counts_representable policy p functions index_pre )) (PreH15 : (cm_concrete_functions_ready policy p index_pre functions )) (PreH16 : (head_count = (cm_function_code_count (policy) (p) (index_pre)))) (PreH17 : (cm_i32_code_count head_count )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> bp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  (cm_stmt_rep bp (cm_function_body (f)) )
  **  (cm_function_list_rep np rest )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (0 <= (index_pre + 1 )) ” 
  &&  “ (cm_functions_counts_representable policy p rest (index_pre + 1 ) ) ” 
  &&  “ (cm_concrete_functions_ready policy p (index_pre + 1 ) rest ) ” 
  &&  “ (((index_pre + 1 ) + (Zlength (rest)) ) <= INT_MAX) ” 
  &&  “ ((index_pre + 1 ) = ((Zlength ((cm_program_functions (p)))) - (Zlength (rest)) )) ” 
  &&  “ (fn_pre <> 0) ” 
  &&  “ (index_pre <> target_pre) ” 
  &&  “ (functions = (cons (f) (rest))) ” 
  &&  “ (cm_function_counts_representable policy p index_pre f ) ” 
  &&  “ (cm_stmt_wf policy p f false (cm_function_body (f)) ) ” 
  &&  “ (cm_functions_counts_representable policy p rest (index_pre + 1 ) ) ” 
  &&  “ (cm_concrete_functions_ready policy p (index_pre + 1 ) rest ) ” 
  &&  “ (cm_i32_code_count (index_pre + 1 ) ) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (index_pre = ((Zlength ((cm_program_functions (p)))) - (Zlength (functions)) )) ” 
  &&  “ ((index_pre + (Zlength (functions)) ) <= INT_MAX) ” 
  &&  “ (cm_functions_counts_representable policy p functions index_pre ) ” 
  &&  “ (cm_concrete_functions_ready policy p index_pre functions ) ” 
  &&  “ (head_count = (cm_function_code_count (policy) (p) (index_pre))) ” 
  &&  “ (cm_i32_code_count head_count ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep np rest )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> pp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> lp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> bp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_slot_list_rep pp (cm_function_params (f)) )
  **  (cm_slot_list_rep lp (cm_function_locals (f)) )
  **  (cm_stmt_rep bp (cm_function_body (f)) )
.

Definition cmc_function_prefix_total_partial_solve_wit_2 := cmc_function_prefix_total_partial_solve_wit_2_pure -> cmc_function_prefix_total_partial_solve_wit_2_aux.

(*----- Function cmc_function_pc_total -----*)

Definition cmc_function_pc_total_safety_wit_1 := 
forall (target_pre: Z) (program_pre: Z) (functions_ptr: Z) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (program_pre <> 0)) (PreH2 : (cm_wf_program policy cg p )) (PreH3 : (cm_concrete_code_ready policy p )) (PreH4 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH5 : ((Zlength ((cm_program_functions (p)))) <= INT_MAX)) (PreH6 : (cm_functions_counts_representable policy p (cm_program_functions (p)) 0 )) (PreH7 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) ,
  ((( &( "prefix" ) )) # Int  |->_)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "target" ) )) # Int64  |-> target_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> functions_ptr)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_function_pc_total_safety_wit_2 := 
(
forall (target_pre: Z) (program_pre: Z) (functions_ptr: Z) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH3 : (0 <= 0)) (PreH4 : (0 = ((Zlength ((cm_program_functions (p)))) - (Zlength ((cm_program_functions (p)))) ))) (PreH5 : ((0 + (Zlength ((cm_program_functions (p)))) ) <= INT_MAX)) (PreH6 : (cm_functions_counts_representable policy p (cm_program_functions (p)) 0 )) (PreH7 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) (PreH8 : (retval = (cm_function_prefix (policy) (p) ((cm_program_functions (p))) ((target_pre - 0 ))))) (PreH9 : (cm_i32_code_count retval )) (PreH10 : (program_pre <> 0)) (PreH11 : (cm_wf_program policy cg p )) (PreH12 : (cm_concrete_code_ready policy p )) (PreH13 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH14 : ((Zlength ((cm_program_functions (p)))) <= INT_MAX)) (PreH15 : (cm_functions_counts_representable policy p (cm_program_functions (p)) 0 )) (PreH16 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) ,
  ((( &( "result" ) )) # Int  |->_)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((( &( "prefix" ) )) # Int  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "target" ) )) # Int64  |-> target_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> functions_ptr)
|--
  “ ((11 + retval ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (11 + retval )) ”
) \/
(
forall (target_pre: Z) (program_pre: Z) (functions_ptr: Z) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH3 : (0 <= 0)) (PreH4 : (0 = ((Zlength ((cm_program_functions (p)))) - (Zlength ((cm_program_functions (p)))) ))) (PreH5 : ((0 + (Zlength ((cm_program_functions (p)))) ) <= INT_MAX)) (PreH6 : (cm_functions_counts_representable policy p (cm_program_functions (p)) 0 )) (PreH7 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) (PreH8 : (retval = (cm_function_prefix (policy) (p) ((cm_program_functions (p))) ((target_pre - 0 ))))) (PreH9 : (cm_i32_code_count retval )) (PreH10 : (program_pre <> 0)) (PreH11 : (cm_wf_program policy cg p )) (PreH12 : (cm_concrete_code_ready policy p )) (PreH13 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH14 : ((Zlength ((cm_program_functions (p)))) <= INT_MAX)) (PreH15 : (cm_functions_counts_representable policy p (cm_program_functions (p)) 0 )) (PreH16 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) ,
  ((( &( "result" ) )) # Int  |->_)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((( &( "prefix" ) )) # Int  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "target" ) )) # Int64  |-> target_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> functions_ptr)
|--
  “ ((11 + retval ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (11 + retval )) ”
).

Definition cmc_function_pc_total_safety_wit_2_split_goal_1 := 
forall (target_pre: Z) (program_pre: Z) (functions_ptr: Z) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH3 : (0 <= 0)) (PreH4 : (0 = ((Zlength ((cm_program_functions (p)))) - (Zlength ((cm_program_functions (p)))) ))) (PreH5 : ((0 + (Zlength ((cm_program_functions (p)))) ) <= INT_MAX)) (PreH6 : (cm_functions_counts_representable policy p (cm_program_functions (p)) 0 )) (PreH7 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) (PreH8 : (retval = (cm_function_prefix (policy) (p) ((cm_program_functions (p))) ((target_pre - 0 ))))) (PreH9 : (cm_i32_code_count retval )) (PreH10 : (program_pre <> 0)) (PreH11 : (cm_wf_program policy cg p )) (PreH12 : (cm_concrete_code_ready policy p )) (PreH13 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH14 : ((Zlength ((cm_program_functions (p)))) <= INT_MAX)) (PreH15 : (cm_functions_counts_representable policy p (cm_program_functions (p)) 0 )) (PreH16 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) ,
  ((( &( "result" ) )) # Int  |->_)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((( &( "prefix" ) )) # Int  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "target" ) )) # Int64  |-> target_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> functions_ptr)
|--
  “ ((11 + retval ) <= INT_MAX) ”
.

Definition cmc_function_pc_total_safety_wit_2_split_goal_2 := 
forall (target_pre: Z) (program_pre: Z) (functions_ptr: Z) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH3 : (0 <= 0)) (PreH4 : (0 = ((Zlength ((cm_program_functions (p)))) - (Zlength ((cm_program_functions (p)))) ))) (PreH5 : ((0 + (Zlength ((cm_program_functions (p)))) ) <= INT_MAX)) (PreH6 : (cm_functions_counts_representable policy p (cm_program_functions (p)) 0 )) (PreH7 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) (PreH8 : (retval = (cm_function_prefix (policy) (p) ((cm_program_functions (p))) ((target_pre - 0 ))))) (PreH9 : (cm_i32_code_count retval )) (PreH10 : (program_pre <> 0)) (PreH11 : (cm_wf_program policy cg p )) (PreH12 : (cm_concrete_code_ready policy p )) (PreH13 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH14 : ((Zlength ((cm_program_functions (p)))) <= INT_MAX)) (PreH15 : (cm_functions_counts_representable policy p (cm_program_functions (p)) 0 )) (PreH16 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) ,
  ((( &( "result" ) )) # Int  |->_)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((( &( "prefix" ) )) # Int  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "target" ) )) # Int64  |-> target_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> functions_ptr)
|--
  “ ((INT_MIN) <= (11 + retval )) ”
.

Definition cmc_function_pc_total_safety_wit_3 := 
forall (target_pre: Z) (program_pre: Z) (functions_ptr: Z) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH3 : (0 <= 0)) (PreH4 : (0 = ((Zlength ((cm_program_functions (p)))) - (Zlength ((cm_program_functions (p)))) ))) (PreH5 : ((0 + (Zlength ((cm_program_functions (p)))) ) <= INT_MAX)) (PreH6 : (cm_functions_counts_representable policy p (cm_program_functions (p)) 0 )) (PreH7 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) (PreH8 : (retval = (cm_function_prefix (policy) (p) ((cm_program_functions (p))) ((target_pre - 0 ))))) (PreH9 : (cm_i32_code_count retval )) (PreH10 : (program_pre <> 0)) (PreH11 : (cm_wf_program policy cg p )) (PreH12 : (cm_concrete_code_ready policy p )) (PreH13 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH14 : ((Zlength ((cm_program_functions (p)))) <= INT_MAX)) (PreH15 : (cm_functions_counts_representable policy p (cm_program_functions (p)) 0 )) (PreH16 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) ,
  ((( &( "result" ) )) # Int  |->_)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((( &( "prefix" ) )) # Int  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "target" ) )) # Int64  |-> target_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> functions_ptr)
|--
  “ (11 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 11) ”
.

Definition cmc_function_pc_total_entail_wit_1 := 
(
forall (program_pre: Z) (functions_ptr: Z) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_concrete_code_ready policy p )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
|--
  EX (tp: Z)  (gp: Z)  (sp: Z) ,
  “ (program_pre <> 0) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_concrete_code_ready policy p ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ ((Zlength ((cm_program_functions (p)))) <= INT_MAX) ” 
  &&  “ (cm_functions_counts_representable policy p (cm_program_functions (p)) 0 ) ” 
  &&  “ (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) ) ”
  &&  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
) \/
(
forall (program_pre: Z) (functions_ptr: Z) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_concrete_code_ready policy p )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
|--
  EX (tp: Z)  (gp: Z)  (sp: Z) ,
  “ (program_pre <> 0) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_concrete_code_ready policy p ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ ((Zlength ((cm_program_functions (p)))) <= INT_MAX) ” 
  &&  “ (cm_functions_counts_representable policy p (cm_program_functions (p)) 0 ) ” 
  &&  “ (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) ) ”
  &&  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
).

Definition cmc_function_pc_total_entail_wit_2 := 
(
forall (program_pre: Z) (functions_ptr: Z) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (PreH1 : (program_pre <> 0)) (PreH2 : (cm_wf_program policy cg p )) (PreH3 : (cm_concrete_code_ready policy p )) (PreH4 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH5 : ((Zlength ((cm_program_functions (p)))) <= INT_MAX)) (PreH6 : (cm_functions_counts_representable policy p (cm_program_functions (p)) 0 )) (PreH7 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
|--
  “ (program_pre <> 0) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_concrete_code_ready policy p ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ ((Zlength ((cm_program_functions (p)))) <= INT_MAX) ” 
  &&  “ (cm_functions_counts_representable policy p (cm_program_functions (p)) 0 ) ” 
  &&  “ (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
) \/
(
forall (program_pre: Z) (functions_ptr: Z) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (PreH1 : ((cm_program_main (p)) <= INT_MAX)) (PreH2 : ((cm_program_main (p)) >= INT_MIN)) (PreH3 : (program_pre <> 0)) (PreH4 : (cm_wf_program policy cg p )) (PreH5 : (cm_concrete_code_ready policy p )) (PreH6 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH7 : ((Zlength ((cm_program_functions (p)))) <= INT_MAX)) (PreH8 : (cm_functions_counts_representable policy p (cm_program_functions (p)) 0 )) (PreH9 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
).

Definition cmc_function_pc_total_entail_wit_2_split_goal_spatial := 
forall (program_pre: Z) (functions_ptr: Z) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (PreH1 : ((cm_program_main (p)) <= INT_MAX)) (PreH2 : ((cm_program_main (p)) >= INT_MIN)) (PreH3 : (program_pre <> 0)) (PreH4 : (cm_wf_program policy cg p )) (PreH5 : (cm_concrete_code_ready policy p )) (PreH6 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH7 : ((Zlength ((cm_program_functions (p)))) <= INT_MAX)) (PreH8 : (cm_functions_counts_representable policy p (cm_program_functions (p)) 0 )) (PreH9 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
.

Definition cmc_function_pc_total_return_wit_1 := 
(
forall (target_pre: Z) (program_pre: Z) (functions_ptr: Z) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH3 : (0 <= 0)) (PreH4 : (0 = ((Zlength ((cm_program_functions (p)))) - (Zlength ((cm_program_functions (p)))) ))) (PreH5 : ((0 + (Zlength ((cm_program_functions (p)))) ) <= INT_MAX)) (PreH6 : (cm_functions_counts_representable policy p (cm_program_functions (p)) 0 )) (PreH7 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) (PreH8 : (retval = (cm_function_prefix (policy) (p) ((cm_program_functions (p))) ((target_pre - 0 ))))) (PreH9 : (cm_i32_code_count retval )) (PreH10 : (program_pre <> 0)) (PreH11 : (cm_wf_program policy cg p )) (PreH12 : (cm_concrete_code_ready policy p )) (PreH13 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH14 : ((Zlength ((cm_program_functions (p)))) <= INT_MAX)) (PreH15 : (cm_functions_counts_representable policy p (cm_program_functions (p)) 0 )) (PreH16 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_concrete_code_ready policy p ) ” 
  &&  “ ((11 + retval ) = (cm_function_pc (policy) (p) (target_pre))) ” 
  &&  “ (cm_i32_code_count (11 + retval ) ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
) \/
(
forall (target_pre: Z) (program_pre: Z) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH3 : (0 <= 0)) (PreH4 : (0 = ((Zlength ((cm_program_functions (p)))) - (Zlength ((cm_program_functions (p)))) ))) (PreH5 : ((0 + (Zlength ((cm_program_functions (p)))) ) <= INT_MAX)) (PreH6 : (cm_functions_counts_representable policy p (cm_program_functions (p)) 0 )) (PreH7 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) (PreH8 : (retval = (cm_function_prefix (policy) (p) ((cm_program_functions (p))) ((target_pre - 0 ))))) (PreH9 : (cm_i32_code_count retval )) (PreH10 : (program_pre <> 0)) (PreH11 : (cm_wf_program policy cg p )) (PreH12 : (cm_concrete_code_ready policy p )) (PreH13 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH14 : ((Zlength ((cm_program_functions (p)))) <= INT_MAX)) (PreH15 : (cm_functions_counts_representable policy p (cm_program_functions (p)) 0 )) (PreH16 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) ,
  TT && emp 
|--
  “ (cm_i32_code_count (11 + retval ) ) ” 
  &&  “ ((11 + retval ) = (cm_function_pc (policy) (p) (target_pre))) ”
  &&  emp
).

Definition cmc_function_pc_total_return_wit_1_split_goal_1 := 
forall (target_pre: Z) (program_pre: Z) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH3 : (0 <= 0)) (PreH4 : (0 = ((Zlength ((cm_program_functions (p)))) - (Zlength ((cm_program_functions (p)))) ))) (PreH5 : ((0 + (Zlength ((cm_program_functions (p)))) ) <= INT_MAX)) (PreH6 : (cm_functions_counts_representable policy p (cm_program_functions (p)) 0 )) (PreH7 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) (PreH8 : (retval = (cm_function_prefix (policy) (p) ((cm_program_functions (p))) ((target_pre - 0 ))))) (PreH9 : (cm_i32_code_count retval )) (PreH10 : (program_pre <> 0)) (PreH11 : (cm_wf_program policy cg p )) (PreH12 : (cm_concrete_code_ready policy p )) (PreH13 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH14 : ((Zlength ((cm_program_functions (p)))) <= INT_MAX)) (PreH15 : (cm_functions_counts_representable policy p (cm_program_functions (p)) 0 )) (PreH16 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) ,
  (cm_i32_code_count (11 + retval ) )
.

Definition cmc_function_pc_total_return_wit_1_split_goal_2 := 
forall (target_pre: Z) (program_pre: Z) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH3 : (0 <= 0)) (PreH4 : (0 = ((Zlength ((cm_program_functions (p)))) - (Zlength ((cm_program_functions (p)))) ))) (PreH5 : ((0 + (Zlength ((cm_program_functions (p)))) ) <= INT_MAX)) (PreH6 : (cm_functions_counts_representable policy p (cm_program_functions (p)) 0 )) (PreH7 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) (PreH8 : (retval = (cm_function_prefix (policy) (p) ((cm_program_functions (p))) ((target_pre - 0 ))))) (PreH9 : (cm_i32_code_count retval )) (PreH10 : (program_pre <> 0)) (PreH11 : (cm_wf_program policy cg p )) (PreH12 : (cm_concrete_code_ready policy p )) (PreH13 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH14 : ((Zlength ((cm_program_functions (p)))) <= INT_MAX)) (PreH15 : (cm_functions_counts_representable policy p (cm_program_functions (p)) 0 )) (PreH16 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) ,
  ((11 + retval ) = (cm_function_pc (policy) (p) (target_pre)))
.

Definition cmc_function_pc_total_partial_solve_wit_1_pure := 
forall (target_pre: Z) (program_pre: Z) (functions_ptr: Z) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (program_pre <> 0)) (PreH2 : (cm_wf_program policy cg p )) (PreH3 : (cm_concrete_code_ready policy p )) (PreH4 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH5 : ((Zlength ((cm_program_functions (p)))) <= INT_MAX)) (PreH6 : (cm_functions_counts_representable policy p (cm_program_functions (p)) 0 )) (PreH7 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) ,
  ((( &( "prefix" ) )) # Int  |->_)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "target" ) )) # Int64  |-> target_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> functions_ptr)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 = ((Zlength ((cm_program_functions (p)))) - (Zlength ((cm_program_functions (p)))) )) ” 
  &&  “ ((0 + (Zlength ((cm_program_functions (p)))) ) <= INT_MAX) ” 
  &&  “ (cm_functions_counts_representable policy p (cm_program_functions (p)) 0 ) ” 
  &&  “ (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) ) ”
.

Definition cmc_function_pc_total_partial_solve_wit_1_aux := 
forall (program_pre: Z) (functions_ptr: Z) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (program_pre <> 0)) (PreH2 : (cm_wf_program policy cg p )) (PreH3 : (cm_concrete_code_ready policy p )) (PreH4 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH5 : ((Zlength ((cm_program_functions (p)))) <= INT_MAX)) (PreH6 : (cm_functions_counts_representable policy p (cm_program_functions (p)) 0 )) (PreH7 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 = ((Zlength ((cm_program_functions (p)))) - (Zlength ((cm_program_functions (p)))) )) ” 
  &&  “ ((0 + (Zlength ((cm_program_functions (p)))) ) <= INT_MAX) ” 
  &&  “ (cm_functions_counts_representable policy p (cm_program_functions (p)) 0 ) ” 
  &&  “ (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) ) ” 
  &&  “ (program_pre <> 0) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_concrete_code_ready policy p ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ ((Zlength ((cm_program_functions (p)))) <= INT_MAX) ” 
  &&  “ (cm_functions_counts_representable policy p (cm_program_functions (p)) 0 ) ” 
  &&  “ (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
.

Definition cmc_function_pc_total_partial_solve_wit_1 := cmc_function_pc_total_partial_solve_wit_1_pure -> cmc_function_pc_total_partial_solve_wit_1_aux.

Module Type VC_Correct.


Axiom proof_of_cmc_function_prefix_total_safety_wit_1 : cmc_function_prefix_total_safety_wit_1.
Axiom proof_of_cmc_function_prefix_total_safety_wit_2 : cmc_function_prefix_total_safety_wit_2.
Axiom proof_of_cmc_function_prefix_total_safety_wit_3 : cmc_function_prefix_total_safety_wit_3.
Axiom proof_of_cmc_function_prefix_total_safety_wit_4 : cmc_function_prefix_total_safety_wit_4.
Axiom proof_of_cmc_function_prefix_total_safety_wit_5 : cmc_function_prefix_total_safety_wit_5.
Axiom proof_of_cmc_function_prefix_total_safety_wit_6 : cmc_function_prefix_total_safety_wit_6.
Axiom proof_of_cmc_function_prefix_total_entail_wit_1 : cmc_function_prefix_total_entail_wit_1.
Axiom proof_of_cmc_function_prefix_total_entail_wit_2 : cmc_function_prefix_total_entail_wit_2.
Axiom proof_of_cmc_function_prefix_total_return_wit_1 : cmc_function_prefix_total_return_wit_1.
Axiom proof_of_cmc_function_prefix_total_return_wit_2 : cmc_function_prefix_total_return_wit_2.
Axiom proof_of_cmc_function_prefix_total_return_wit_3 : cmc_function_prefix_total_return_wit_3.
Axiom proof_of_cmc_function_prefix_total_partial_solve_wit_1_pure : cmc_function_prefix_total_partial_solve_wit_1_pure.
Axiom proof_of_cmc_function_prefix_total_partial_solve_wit_1 : cmc_function_prefix_total_partial_solve_wit_1.
Axiom proof_of_cmc_function_prefix_total_partial_solve_wit_2_pure : cmc_function_prefix_total_partial_solve_wit_2_pure.
Axiom proof_of_cmc_function_prefix_total_partial_solve_wit_2 : cmc_function_prefix_total_partial_solve_wit_2.
Axiom proof_of_cmc_function_pc_total_safety_wit_1 : cmc_function_pc_total_safety_wit_1.
Axiom proof_of_cmc_function_pc_total_safety_wit_2 : cmc_function_pc_total_safety_wit_2.
Axiom proof_of_cmc_function_pc_total_safety_wit_3 : cmc_function_pc_total_safety_wit_3.
Axiom proof_of_cmc_function_pc_total_entail_wit_1 : cmc_function_pc_total_entail_wit_1.
Axiom proof_of_cmc_function_pc_total_entail_wit_2 : cmc_function_pc_total_entail_wit_2.
Axiom proof_of_cmc_function_pc_total_return_wit_1 : cmc_function_pc_total_return_wit_1.
Axiom proof_of_cmc_function_pc_total_partial_solve_wit_1_pure : cmc_function_pc_total_partial_solve_wit_1_pure.
Axiom proof_of_cmc_function_pc_total_partial_solve_wit_1 : cmc_function_pc_total_partial_solve_wit_1.

End VC_Correct.
