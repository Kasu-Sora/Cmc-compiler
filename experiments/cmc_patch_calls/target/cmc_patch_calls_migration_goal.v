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
Require Import SimpleC.EE.QCP_demos_human.cmc_patch_calls_migration_lib.
Local Open Scope sac.

(*----- Function cmc_patch_code_arrays -----*)

Definition cmc_patch_code_arrays_safety_wit_1 := 
forall (length_pre: Z) (imms_pre: Z) (ops_pre: Z) (program_pre: Z) (functions_ptr: Z) (raw: (@list tvm_inst)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_concrete_code_ready policy p )) (PreH3 : (0 <= length_pre)) (PreH4 : (length_pre <= INT_MAX)) (PreH5 : (length_pre = (Zlength (raw)))) ,
  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "imms" ) )) # Ptr  |-> imms_pre)
  **  ((( &( "length" ) )) # Int  |-> length_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_patch_arrays_rep ops_pre imms_pre length_pre raw )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_patch_code_arrays_safety_wit_2 := 
forall (length_pre: Z) (imms_pre: Z) (ops_pre: Z) (program_pre: Z) (functions_ptr: Z) (raw: (@list tvm_inst)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (opcode: tvm_opcode) (model_imm: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_concrete_code_ready policy p )) (PreH3 : (1 <= length_pre)) (PreH4 : (length_pre <= INT_MAX)) (PreH5 : (length_pre = (Zlength (raw)))) (PreH6 : (raw = (cons ((TVMInst (opcode) (model_imm))) ((cm_patch_tail (raw)))))) (PreH7 : ((length_pre - 1 ) = (Zlength ((cm_patch_tail (raw)))))) ,
  ((( &( "remaining_ops" ) )) # Ptr  |->_)
  **  ((( &( "immediate" ) )) # Int64  |-> model_imm)
  **  ((( &( "op" ) )) # Int  |-> (tvm_opcode_code (opcode)))
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "imms" ) )) # Ptr  |-> imms_pre)
  **  ((( &( "length" ) )) # Int  |-> length_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((ops_pre) # Int  |-> (tvm_opcode_code (opcode)))
  **  ((imms_pre) # Int64  |-> model_imm)
  **  (cm_patch_arrays_rep (ops_pre + (1 * sizeof(INT))) (imms_pre + (1 * sizeof(INT64))) (length_pre - 1 ) (cm_patch_tail (raw)) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmc_patch_code_arrays_safety_wit_3 := 
forall (length_pre: Z) (imms_pre: Z) (ops_pre: Z) (program_pre: Z) (functions_ptr: Z) (raw: (@list tvm_inst)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (opcode: tvm_opcode) (model_imm: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_concrete_code_ready policy p )) (PreH3 : (1 <= length_pre)) (PreH4 : (length_pre <= INT_MAX)) (PreH5 : (length_pre = (Zlength (raw)))) (PreH6 : (raw = (cons ((TVMInst (opcode) (model_imm))) ((cm_patch_tail (raw)))))) (PreH7 : ((length_pre - 1 ) = (Zlength ((cm_patch_tail (raw)))))) ,
  ((( &( "remaining_imms" ) )) # Ptr  |->_)
  **  ((( &( "remaining_ops" ) )) # Ptr  |-> (ops_pre + (1 * sizeof(INT))))
  **  ((( &( "immediate" ) )) # Int64  |-> model_imm)
  **  ((( &( "op" ) )) # Int  |-> (tvm_opcode_code (opcode)))
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "imms" ) )) # Ptr  |-> imms_pre)
  **  ((( &( "length" ) )) # Int  |-> length_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((ops_pre) # Int  |-> (tvm_opcode_code (opcode)))
  **  ((imms_pre) # Int64  |-> model_imm)
  **  (cm_patch_arrays_rep (ops_pre + (1 * sizeof(INT))) (imms_pre + (1 * sizeof(INT64))) (length_pre - 1 ) (cm_patch_tail (raw)) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmc_patch_code_arrays_safety_wit_4 := 
forall (length_pre: Z) (imms_pre: Z) (ops_pre: Z) (program_pre: Z) (functions_ptr: Z) (raw: (@list tvm_inst)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (opcode: tvm_opcode) (model_imm: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_concrete_code_ready policy p )) (PreH3 : (1 <= length_pre)) (PreH4 : (length_pre <= INT_MAX)) (PreH5 : (length_pre = (Zlength (raw)))) (PreH6 : (raw = (cons ((TVMInst (opcode) (model_imm))) ((cm_patch_tail (raw)))))) (PreH7 : ((length_pre - 1 ) = (Zlength ((cm_patch_tail (raw)))))) ,
  ((( &( "remaining_length" ) )) # Int  |->_)
  **  ((( &( "remaining_imms" ) )) # Ptr  |-> (imms_pre + (1 * sizeof(INT64))))
  **  ((( &( "remaining_ops" ) )) # Ptr  |-> (ops_pre + (1 * sizeof(INT))))
  **  ((( &( "immediate" ) )) # Int64  |-> model_imm)
  **  ((( &( "op" ) )) # Int  |-> (tvm_opcode_code (opcode)))
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "imms" ) )) # Ptr  |-> imms_pre)
  **  ((( &( "length" ) )) # Int  |-> length_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((ops_pre) # Int  |-> (tvm_opcode_code (opcode)))
  **  ((imms_pre) # Int64  |-> model_imm)
  **  (cm_patch_arrays_rep (ops_pre + (1 * sizeof(INT))) (imms_pre + (1 * sizeof(INT64))) (length_pre - 1 ) (cm_patch_tail (raw)) )
|--
  “ ((length_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (length_pre - 1 )) ”
.

Definition cmc_patch_code_arrays_safety_wit_5 := 
forall (length_pre: Z) (imms_pre: Z) (ops_pre: Z) (program_pre: Z) (functions_ptr: Z) (raw: (@list tvm_inst)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (opcode: tvm_opcode) (model_imm: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_concrete_code_ready policy p )) (PreH3 : (1 <= length_pre)) (PreH4 : (length_pre <= INT_MAX)) (PreH5 : (length_pre = (Zlength (raw)))) (PreH6 : (raw = (cons ((TVMInst (opcode) (model_imm))) ((cm_patch_tail (raw)))))) (PreH7 : ((length_pre - 1 ) = (Zlength ((cm_patch_tail (raw)))))) ,
  ((( &( "remaining_length" ) )) # Int  |->_)
  **  ((( &( "remaining_imms" ) )) # Ptr  |-> (imms_pre + (1 * sizeof(INT64))))
  **  ((( &( "remaining_ops" ) )) # Ptr  |-> (ops_pre + (1 * sizeof(INT))))
  **  ((( &( "immediate" ) )) # Int64  |-> model_imm)
  **  ((( &( "op" ) )) # Int  |-> (tvm_opcode_code (opcode)))
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "imms" ) )) # Ptr  |-> imms_pre)
  **  ((( &( "length" ) )) # Int  |-> length_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((ops_pre) # Int  |-> (tvm_opcode_code (opcode)))
  **  ((imms_pre) # Int64  |-> model_imm)
  **  (cm_patch_arrays_rep (ops_pre + (1 * sizeof(INT))) (imms_pre + (1 * sizeof(INT64))) (length_pre - 1 ) (cm_patch_tail (raw)) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmc_patch_code_arrays_safety_wit_6 := 
forall (length_pre: Z) (imms_pre: Z) (ops_pre: Z) (program_pre: Z) (functions_ptr: Z) (raw: (@list tvm_inst)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (opcode: tvm_opcode) (model_imm: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_concrete_code_ready policy p )) (PreH3 : (1 <= length_pre)) (PreH4 : (length_pre <= INT_MAX)) (PreH5 : (length_pre = (Zlength (raw)))) (PreH6 : (raw = (cons ((TVMInst (opcode) (model_imm))) ((cm_patch_tail (raw)))))) (PreH7 : ((length_pre - 1 ) = (Zlength ((cm_patch_tail (raw)))))) ,
  ((( &( "remaining_length" ) )) # Int  |-> (length_pre - 1 ))
  **  ((( &( "remaining_imms" ) )) # Ptr  |-> (imms_pre + (1 * sizeof(INT64))))
  **  ((( &( "remaining_ops" ) )) # Ptr  |-> (ops_pre + (1 * sizeof(INT))))
  **  ((( &( "immediate" ) )) # Int64  |-> model_imm)
  **  ((( &( "op" ) )) # Int  |-> (tvm_opcode_code (opcode)))
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "imms" ) )) # Ptr  |-> imms_pre)
  **  ((( &( "length" ) )) # Int  |-> length_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((ops_pre) # Int  |-> (tvm_opcode_code (opcode)))
  **  ((imms_pre) # Int64  |-> model_imm)
  **  (cm_patch_arrays_rep (ops_pre + (1 * sizeof(INT))) (imms_pre + (1 * sizeof(INT64))) (length_pre - 1 ) (cm_patch_tail (raw)) )
|--
  “ (22 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 22) ”
.

Definition cmc_patch_code_arrays_entail_wit_1 := 
(
forall (length_pre: Z) (imms_pre: Z) (ops_pre: Z) (program_pre: Z) (functions_ptr: Z) (raw: (@list tvm_inst)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (length_pre <> 0)) (PreH2 : (cm_wf_program policy cg p )) (PreH3 : (cm_concrete_code_ready policy p )) (PreH4 : (0 <= length_pre)) (PreH5 : (length_pre <= INT_MAX)) (PreH6 : (length_pre = (Zlength (raw)))) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_patch_arrays_rep ops_pre imms_pre length_pre raw )
|--
  EX (opcode: tvm_opcode)  (model_imm: Z) ,
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_concrete_code_ready policy p ) ” 
  &&  “ (1 <= length_pre) ” 
  &&  “ (length_pre <= INT_MAX) ” 
  &&  “ (length_pre = (Zlength (raw))) ” 
  &&  “ (raw = (cons ((TVMInst (opcode) (model_imm))) ((cm_patch_tail (raw))))) ” 
  &&  “ ((length_pre - 1 ) = (Zlength ((cm_patch_tail (raw))))) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((ops_pre) # Int  |-> (tvm_opcode_code (opcode)))
  **  ((imms_pre) # Int64  |-> model_imm)
  **  (cm_patch_arrays_rep (ops_pre + (1 * sizeof(INT))) (imms_pre + (1 * sizeof(INT64))) (length_pre - 1 ) (cm_patch_tail (raw)) )
) \/
(
forall (length_pre: Z) (imms_pre: Z) (ops_pre: Z) (program_pre: Z) (functions_ptr: Z) (raw: (@list tvm_inst)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (length_pre <> 0)) (PreH2 : (cm_wf_program policy cg p )) (PreH3 : (cm_concrete_code_ready policy p )) (PreH4 : (0 <= length_pre)) (PreH5 : (length_pre <= INT_MAX)) (PreH6 : (length_pre = (Zlength (raw)))) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_patch_arrays_rep ops_pre imms_pre length_pre raw )
|--
  EX (opcode: tvm_opcode)  (model_imm: Z) ,
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_concrete_code_ready policy p ) ” 
  &&  “ (1 <= length_pre) ” 
  &&  “ (length_pre <= INT_MAX) ” 
  &&  “ (length_pre = (Zlength (raw))) ” 
  &&  “ (raw = (cons ((TVMInst (opcode) (model_imm))) ((cm_patch_tail (raw))))) ” 
  &&  “ ((length_pre - 1 ) = (Zlength ((cm_patch_tail (raw))))) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((ops_pre) # Int  |-> (tvm_opcode_code (opcode)))
  **  ((imms_pre) # Int64  |-> model_imm)
  **  (cm_patch_arrays_rep (ops_pre + (1 * sizeof(INT))) (imms_pre + (1 * sizeof(INT64))) (length_pre - 1 ) (cm_patch_tail (raw)) )
).

Definition cmc_patch_code_arrays_return_wit_1 := 
(
forall (length_pre: Z) (imms_pre: Z) (ops_pre: Z) (program_pre: Z) (functions_ptr: Z) (raw: (@list tvm_inst)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (length_pre = 0)) (PreH2 : (cm_wf_program policy cg p )) (PreH3 : (cm_concrete_code_ready policy p )) (PreH4 : (0 <= length_pre)) (PreH5 : (length_pre <= INT_MAX)) (PreH6 : (length_pre = (Zlength (raw)))) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_patch_arrays_rep ops_pre imms_pre length_pre raw )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_concrete_code_ready policy p ) ” 
  &&  “ (0 <= length_pre) ” 
  &&  “ (length_pre <= INT_MAX) ” 
  &&  “ (length_pre = (Zlength (raw))) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_patch_arrays_rep ops_pre imms_pre length_pre (cm_patch_code (policy) (p) (raw)) )
) \/
(
forall (length_pre: Z) (imms_pre: Z) (ops_pre: Z) (program_pre: Z) (functions_ptr: Z) (raw: (@list tvm_inst)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (length_pre = 0)) (PreH2 : (cm_wf_program policy cg p )) (PreH3 : (cm_concrete_code_ready policy p )) (PreH4 : (0 <= length_pre)) (PreH5 : (length_pre <= INT_MAX)) (PreH6 : (length_pre = (Zlength (raw)))) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_patch_arrays_rep ops_pre imms_pre length_pre raw )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_patch_arrays_rep ops_pre imms_pre length_pre (cm_patch_code (policy) (p) (raw)) )
).

Definition cmc_patch_code_arrays_return_wit_1_split_goal_spatial := 
forall (length_pre: Z) (imms_pre: Z) (ops_pre: Z) (program_pre: Z) (functions_ptr: Z) (raw: (@list tvm_inst)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (length_pre = 0)) (PreH2 : (cm_wf_program policy cg p )) (PreH3 : (cm_concrete_code_ready policy p )) (PreH4 : (0 <= length_pre)) (PreH5 : (length_pre <= INT_MAX)) (PreH6 : (length_pre = (Zlength (raw)))) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_patch_arrays_rep ops_pre imms_pre length_pre raw )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_patch_arrays_rep ops_pre imms_pre length_pre (cm_patch_code (policy) (p) (raw)) )
.

Definition cmc_patch_code_arrays_return_wit_2 := 
(
forall (length_pre: Z) (imms_pre: Z) (ops_pre: Z) (program_pre: Z) (functions_ptr: Z) (raw: (@list tvm_inst)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (opcode: tvm_opcode) (model_imm: Z) (retval: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_concrete_code_ready policy p )) (PreH3 : (0 <= (length_pre - 1 ))) (PreH4 : ((length_pre - 1 ) <= INT_MAX)) (PreH5 : ((length_pre - 1 ) = (Zlength ((cm_patch_tail (raw)))))) (PreH6 : (cm_wf_program policy cg p )) (PreH7 : (cm_concrete_code_ready policy p )) (PreH8 : (retval = (cm_function_pc (policy) (p) (model_imm)))) (PreH9 : (cm_i32_code_count retval )) (PreH10 : ((tvm_opcode_code (opcode)) = 22)) (PreH11 : (cm_wf_program policy cg p )) (PreH12 : (cm_concrete_code_ready policy p )) (PreH13 : (1 <= length_pre)) (PreH14 : (length_pre <= INT_MAX)) (PreH15 : (length_pre = (Zlength (raw)))) (PreH16 : (raw = (cons ((TVMInst (opcode) (model_imm))) ((cm_patch_tail (raw)))))) (PreH17 : ((length_pre - 1 ) = (Zlength ((cm_patch_tail (raw)))))) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_patch_arrays_rep (ops_pre + (1 * sizeof(INT))) (imms_pre + (1 * sizeof(INT64))) (length_pre - 1 ) (cm_patch_code (policy) (p) ((cm_patch_tail (raw)))) )
  **  ((ops_pre) # Int  |-> (tvm_opcode_code (opcode)))
  **  ((imms_pre) # Int64  |-> retval)
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_concrete_code_ready policy p ) ” 
  &&  “ (0 <= length_pre) ” 
  &&  “ (length_pre <= INT_MAX) ” 
  &&  “ (length_pre = (Zlength (raw))) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_patch_arrays_rep ops_pre imms_pre length_pre (cm_patch_code (policy) (p) (raw)) )
) \/
(
forall (length_pre: Z) (imms_pre: Z) (ops_pre: Z) (program_pre: Z) (functions_ptr: Z) (raw: (@list tvm_inst)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (opcode: tvm_opcode) (model_imm: Z) (retval: Z) (PreH1 : (retval <= INT64_MAX)) (PreH2 : (retval >= INT64_MIN)) (PreH3 : ((tvm_opcode_code (opcode)) <= INT_MAX)) (PreH4 : ((tvm_opcode_code (opcode)) >= INT_MIN)) (PreH5 : (cm_wf_program policy cg p )) (PreH6 : (cm_concrete_code_ready policy p )) (PreH7 : (0 <= (length_pre - 1 ))) (PreH8 : ((length_pre - 1 ) <= INT_MAX)) (PreH9 : ((length_pre - 1 ) = (Zlength ((cm_patch_tail (raw)))))) (PreH10 : (cm_wf_program policy cg p )) (PreH11 : (cm_concrete_code_ready policy p )) (PreH12 : (retval = (cm_function_pc (policy) (p) (model_imm)))) (PreH13 : (cm_i32_code_count retval )) (PreH14 : ((tvm_opcode_code (opcode)) = 22)) (PreH15 : (cm_wf_program policy cg p )) (PreH16 : (cm_concrete_code_ready policy p )) (PreH17 : (1 <= length_pre)) (PreH18 : (length_pre <= INT_MAX)) (PreH19 : (length_pre = (Zlength (raw)))) (PreH20 : (raw = (cons ((TVMInst (opcode) (model_imm))) ((cm_patch_tail (raw)))))) (PreH21 : ((length_pre - 1 ) = (Zlength ((cm_patch_tail (raw)))))) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_patch_arrays_rep (ops_pre + (1 * sizeof(INT))) (imms_pre + (1 * sizeof(INT64))) (length_pre - 1 ) (cm_patch_code (policy) (p) ((cm_patch_tail (raw)))) )
  **  ((ops_pre) # Int  |-> (tvm_opcode_code (opcode)))
  **  ((imms_pre) # Int64  |-> retval)
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_patch_arrays_rep ops_pre imms_pre length_pre (cm_patch_code (policy) (p) (raw)) )
).

Definition cmc_patch_code_arrays_return_wit_2_split_goal_spatial := 
forall (length_pre: Z) (imms_pre: Z) (ops_pre: Z) (program_pre: Z) (functions_ptr: Z) (raw: (@list tvm_inst)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (opcode: tvm_opcode) (model_imm: Z) (retval: Z) (PreH1 : (retval <= INT64_MAX)) (PreH2 : (retval >= INT64_MIN)) (PreH3 : ((tvm_opcode_code (opcode)) <= INT_MAX)) (PreH4 : ((tvm_opcode_code (opcode)) >= INT_MIN)) (PreH5 : (cm_wf_program policy cg p )) (PreH6 : (cm_concrete_code_ready policy p )) (PreH7 : (0 <= (length_pre - 1 ))) (PreH8 : ((length_pre - 1 ) <= INT_MAX)) (PreH9 : ((length_pre - 1 ) = (Zlength ((cm_patch_tail (raw)))))) (PreH10 : (cm_wf_program policy cg p )) (PreH11 : (cm_concrete_code_ready policy p )) (PreH12 : (retval = (cm_function_pc (policy) (p) (model_imm)))) (PreH13 : (cm_i32_code_count retval )) (PreH14 : ((tvm_opcode_code (opcode)) = 22)) (PreH15 : (cm_wf_program policy cg p )) (PreH16 : (cm_concrete_code_ready policy p )) (PreH17 : (1 <= length_pre)) (PreH18 : (length_pre <= INT_MAX)) (PreH19 : (length_pre = (Zlength (raw)))) (PreH20 : (raw = (cons ((TVMInst (opcode) (model_imm))) ((cm_patch_tail (raw)))))) (PreH21 : ((length_pre - 1 ) = (Zlength ((cm_patch_tail (raw)))))) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_patch_arrays_rep (ops_pre + (1 * sizeof(INT))) (imms_pre + (1 * sizeof(INT64))) (length_pre - 1 ) (cm_patch_code (policy) (p) ((cm_patch_tail (raw)))) )
  **  ((ops_pre) # Int  |-> (tvm_opcode_code (opcode)))
  **  ((imms_pre) # Int64  |-> retval)
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_patch_arrays_rep ops_pre imms_pre length_pre (cm_patch_code (policy) (p) (raw)) )
.

Definition cmc_patch_code_arrays_return_wit_3 := 
(
forall (length_pre: Z) (imms_pre: Z) (ops_pre: Z) (program_pre: Z) (functions_ptr: Z) (raw: (@list tvm_inst)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (opcode: tvm_opcode) (model_imm: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_concrete_code_ready policy p )) (PreH3 : (0 <= (length_pre - 1 ))) (PreH4 : ((length_pre - 1 ) <= INT_MAX)) (PreH5 : ((length_pre - 1 ) = (Zlength ((cm_patch_tail (raw)))))) (PreH6 : ((tvm_opcode_code (opcode)) <> 22)) (PreH7 : (cm_wf_program policy cg p )) (PreH8 : (cm_concrete_code_ready policy p )) (PreH9 : (1 <= length_pre)) (PreH10 : (length_pre <= INT_MAX)) (PreH11 : (length_pre = (Zlength (raw)))) (PreH12 : (raw = (cons ((TVMInst (opcode) (model_imm))) ((cm_patch_tail (raw)))))) (PreH13 : ((length_pre - 1 ) = (Zlength ((cm_patch_tail (raw)))))) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_patch_arrays_rep (ops_pre + (1 * sizeof(INT))) (imms_pre + (1 * sizeof(INT64))) (length_pre - 1 ) (cm_patch_code (policy) (p) ((cm_patch_tail (raw)))) )
  **  ((ops_pre) # Int  |-> (tvm_opcode_code (opcode)))
  **  ((imms_pre) # Int64  |-> model_imm)
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_concrete_code_ready policy p ) ” 
  &&  “ (0 <= length_pre) ” 
  &&  “ (length_pre <= INT_MAX) ” 
  &&  “ (length_pre = (Zlength (raw))) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_patch_arrays_rep ops_pre imms_pre length_pre (cm_patch_code (policy) (p) (raw)) )
) \/
(
forall (length_pre: Z) (imms_pre: Z) (ops_pre: Z) (program_pre: Z) (functions_ptr: Z) (raw: (@list tvm_inst)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (opcode: tvm_opcode) (model_imm: Z) (PreH1 : (model_imm <= INT64_MAX)) (PreH2 : (model_imm >= INT64_MIN)) (PreH3 : ((tvm_opcode_code (opcode)) <= INT_MAX)) (PreH4 : ((tvm_opcode_code (opcode)) >= INT_MIN)) (PreH5 : (cm_wf_program policy cg p )) (PreH6 : (cm_concrete_code_ready policy p )) (PreH7 : (0 <= (length_pre - 1 ))) (PreH8 : ((length_pre - 1 ) <= INT_MAX)) (PreH9 : ((length_pre - 1 ) = (Zlength ((cm_patch_tail (raw)))))) (PreH10 : ((tvm_opcode_code (opcode)) <> 22)) (PreH11 : (cm_wf_program policy cg p )) (PreH12 : (cm_concrete_code_ready policy p )) (PreH13 : (1 <= length_pre)) (PreH14 : (length_pre <= INT_MAX)) (PreH15 : (length_pre = (Zlength (raw)))) (PreH16 : (raw = (cons ((TVMInst (opcode) (model_imm))) ((cm_patch_tail (raw)))))) (PreH17 : ((length_pre - 1 ) = (Zlength ((cm_patch_tail (raw)))))) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_patch_arrays_rep (ops_pre + (1 * sizeof(INT))) (imms_pre + (1 * sizeof(INT64))) (length_pre - 1 ) (cm_patch_code (policy) (p) ((cm_patch_tail (raw)))) )
  **  ((ops_pre) # Int  |-> (tvm_opcode_code (opcode)))
  **  ((imms_pre) # Int64  |-> model_imm)
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_patch_arrays_rep ops_pre imms_pre length_pre (cm_patch_code (policy) (p) (raw)) )
).

Definition cmc_patch_code_arrays_return_wit_3_split_goal_spatial := 
forall (length_pre: Z) (imms_pre: Z) (ops_pre: Z) (program_pre: Z) (functions_ptr: Z) (raw: (@list tvm_inst)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (opcode: tvm_opcode) (model_imm: Z) (PreH1 : (model_imm <= INT64_MAX)) (PreH2 : (model_imm >= INT64_MIN)) (PreH3 : ((tvm_opcode_code (opcode)) <= INT_MAX)) (PreH4 : ((tvm_opcode_code (opcode)) >= INT_MIN)) (PreH5 : (cm_wf_program policy cg p )) (PreH6 : (cm_concrete_code_ready policy p )) (PreH7 : (0 <= (length_pre - 1 ))) (PreH8 : ((length_pre - 1 ) <= INT_MAX)) (PreH9 : ((length_pre - 1 ) = (Zlength ((cm_patch_tail (raw)))))) (PreH10 : ((tvm_opcode_code (opcode)) <> 22)) (PreH11 : (cm_wf_program policy cg p )) (PreH12 : (cm_concrete_code_ready policy p )) (PreH13 : (1 <= length_pre)) (PreH14 : (length_pre <= INT_MAX)) (PreH15 : (length_pre = (Zlength (raw)))) (PreH16 : (raw = (cons ((TVMInst (opcode) (model_imm))) ((cm_patch_tail (raw)))))) (PreH17 : ((length_pre - 1 ) = (Zlength ((cm_patch_tail (raw)))))) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_patch_arrays_rep (ops_pre + (1 * sizeof(INT))) (imms_pre + (1 * sizeof(INT64))) (length_pre - 1 ) (cm_patch_code (policy) (p) ((cm_patch_tail (raw)))) )
  **  ((ops_pre) # Int  |-> (tvm_opcode_code (opcode)))
  **  ((imms_pre) # Int64  |-> model_imm)
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_patch_arrays_rep ops_pre imms_pre length_pre (cm_patch_code (policy) (p) (raw)) )
.

Definition cmc_patch_code_arrays_partial_solve_wit_1_pure := 
forall (length_pre: Z) (imms_pre: Z) (ops_pre: Z) (program_pre: Z) (functions_ptr: Z) (raw: (@list tvm_inst)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (opcode: tvm_opcode) (model_imm: Z) (PreH1 : ((tvm_opcode_code (opcode)) = 22)) (PreH2 : (cm_wf_program policy cg p )) (PreH3 : (cm_concrete_code_ready policy p )) (PreH4 : (1 <= length_pre)) (PreH5 : (length_pre <= INT_MAX)) (PreH6 : (length_pre = (Zlength (raw)))) (PreH7 : (raw = (cons ((TVMInst (opcode) (model_imm))) ((cm_patch_tail (raw)))))) (PreH8 : ((length_pre - 1 ) = (Zlength ((cm_patch_tail (raw)))))) ,
  ((( &( "pc" ) )) # Int  |->_)
  **  ((( &( "remaining_length" ) )) # Int  |-> (length_pre - 1 ))
  **  ((( &( "remaining_imms" ) )) # Ptr  |-> (imms_pre + (1 * sizeof(INT64))))
  **  ((( &( "remaining_ops" ) )) # Ptr  |-> (ops_pre + (1 * sizeof(INT))))
  **  ((( &( "immediate" ) )) # Int64  |-> model_imm)
  **  ((( &( "op" ) )) # Int  |-> (tvm_opcode_code (opcode)))
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "imms" ) )) # Ptr  |-> imms_pre)
  **  ((( &( "length" ) )) # Int  |-> length_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((ops_pre) # Int  |-> (tvm_opcode_code (opcode)))
  **  ((imms_pre) # Int64  |-> model_imm)
  **  (cm_patch_arrays_rep (ops_pre + (1 * sizeof(INT))) (imms_pre + (1 * sizeof(INT64))) (length_pre - 1 ) (cm_patch_tail (raw)) )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_concrete_code_ready policy p ) ”
.

Definition cmc_patch_code_arrays_partial_solve_wit_1_aux := 
forall (length_pre: Z) (imms_pre: Z) (ops_pre: Z) (program_pre: Z) (functions_ptr: Z) (raw: (@list tvm_inst)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (opcode: tvm_opcode) (model_imm: Z) (PreH1 : ((tvm_opcode_code (opcode)) = 22)) (PreH2 : (cm_wf_program policy cg p )) (PreH3 : (cm_concrete_code_ready policy p )) (PreH4 : (1 <= length_pre)) (PreH5 : (length_pre <= INT_MAX)) (PreH6 : (length_pre = (Zlength (raw)))) (PreH7 : (raw = (cons ((TVMInst (opcode) (model_imm))) ((cm_patch_tail (raw)))))) (PreH8 : ((length_pre - 1 ) = (Zlength ((cm_patch_tail (raw)))))) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((ops_pre) # Int  |-> (tvm_opcode_code (opcode)))
  **  ((imms_pre) # Int64  |-> model_imm)
  **  (cm_patch_arrays_rep (ops_pre + (1 * sizeof(INT))) (imms_pre + (1 * sizeof(INT64))) (length_pre - 1 ) (cm_patch_tail (raw)) )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_concrete_code_ready policy p ) ” 
  &&  “ ((tvm_opcode_code (opcode)) = 22) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_concrete_code_ready policy p ) ” 
  &&  “ (1 <= length_pre) ” 
  &&  “ (length_pre <= INT_MAX) ” 
  &&  “ (length_pre = (Zlength (raw))) ” 
  &&  “ (raw = (cons ((TVMInst (opcode) (model_imm))) ((cm_patch_tail (raw))))) ” 
  &&  “ ((length_pre - 1 ) = (Zlength ((cm_patch_tail (raw))))) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((ops_pre) # Int  |-> (tvm_opcode_code (opcode)))
  **  ((imms_pre) # Int64  |-> model_imm)
  **  (cm_patch_arrays_rep (ops_pre + (1 * sizeof(INT))) (imms_pre + (1 * sizeof(INT64))) (length_pre - 1 ) (cm_patch_tail (raw)) )
.

Definition cmc_patch_code_arrays_partial_solve_wit_1 := cmc_patch_code_arrays_partial_solve_wit_1_pure -> cmc_patch_code_arrays_partial_solve_wit_1_aux.

Definition cmc_patch_code_arrays_partial_solve_wit_2_pure := 
forall (length_pre: Z) (imms_pre: Z) (ops_pre: Z) (program_pre: Z) (functions_ptr: Z) (raw: (@list tvm_inst)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (opcode: tvm_opcode) (model_imm: Z) (retval: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_concrete_code_ready policy p )) (PreH3 : (retval = (cm_function_pc (policy) (p) (model_imm)))) (PreH4 : (cm_i32_code_count retval )) (PreH5 : ((tvm_opcode_code (opcode)) = 22)) (PreH6 : (cm_wf_program policy cg p )) (PreH7 : (cm_concrete_code_ready policy p )) (PreH8 : (1 <= length_pre)) (PreH9 : (length_pre <= INT_MAX)) (PreH10 : (length_pre = (Zlength (raw)))) (PreH11 : (raw = (cons ((TVMInst (opcode) (model_imm))) ((cm_patch_tail (raw)))))) (PreH12 : ((length_pre - 1 ) = (Zlength ((cm_patch_tail (raw)))))) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((( &( "pc" ) )) # Int  |-> retval)
  **  ((( &( "remaining_length" ) )) # Int  |-> (length_pre - 1 ))
  **  ((( &( "remaining_imms" ) )) # Ptr  |-> (imms_pre + (1 * sizeof(INT64))))
  **  ((( &( "remaining_ops" ) )) # Ptr  |-> (ops_pre + (1 * sizeof(INT))))
  **  ((( &( "immediate" ) )) # Int64  |-> model_imm)
  **  ((( &( "op" ) )) # Int  |-> (tvm_opcode_code (opcode)))
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "imms" ) )) # Ptr  |-> imms_pre)
  **  ((( &( "length" ) )) # Int  |-> length_pre)
  **  ((ops_pre) # Int  |-> (tvm_opcode_code (opcode)))
  **  ((imms_pre) # Int64  |-> retval)
  **  (cm_patch_arrays_rep (ops_pre + (1 * sizeof(INT))) (imms_pre + (1 * sizeof(INT64))) (length_pre - 1 ) (cm_patch_tail (raw)) )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_concrete_code_ready policy p ) ” 
  &&  “ (0 <= (length_pre - 1 )) ” 
  &&  “ ((length_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((length_pre - 1 ) = (Zlength ((cm_patch_tail (raw))))) ” 
  &&  “ (((Zlength (raw)) - 1 ) <= INT_MAX) ” 
  &&  “ (0 <= ((Zlength (raw)) - 1 )) ”
.

Definition cmc_patch_code_arrays_partial_solve_wit_2_aux := 
forall (length_pre: Z) (imms_pre: Z) (ops_pre: Z) (program_pre: Z) (functions_ptr: Z) (raw: (@list tvm_inst)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (opcode: tvm_opcode) (model_imm: Z) (retval: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_concrete_code_ready policy p )) (PreH3 : (retval = (cm_function_pc (policy) (p) (model_imm)))) (PreH4 : (cm_i32_code_count retval )) (PreH5 : ((tvm_opcode_code (opcode)) = 22)) (PreH6 : (cm_wf_program policy cg p )) (PreH7 : (cm_concrete_code_ready policy p )) (PreH8 : (1 <= length_pre)) (PreH9 : (length_pre <= INT_MAX)) (PreH10 : (length_pre = (Zlength (raw)))) (PreH11 : (raw = (cons ((TVMInst (opcode) (model_imm))) ((cm_patch_tail (raw)))))) (PreH12 : ((length_pre - 1 ) = (Zlength ((cm_patch_tail (raw)))))) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((ops_pre) # Int  |-> (tvm_opcode_code (opcode)))
  **  ((imms_pre) # Int64  |-> retval)
  **  (cm_patch_arrays_rep (ops_pre + (1 * sizeof(INT))) (imms_pre + (1 * sizeof(INT64))) (length_pre - 1 ) (cm_patch_tail (raw)) )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_concrete_code_ready policy p ) ” 
  &&  “ (0 <= (length_pre - 1 )) ” 
  &&  “ ((length_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((length_pre - 1 ) = (Zlength ((cm_patch_tail (raw))))) ” 
  &&  “ (((Zlength (raw)) - 1 ) <= INT_MAX) ” 
  &&  “ (0 <= ((Zlength (raw)) - 1 )) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_concrete_code_ready policy p ) ” 
  &&  “ (retval = (cm_function_pc (policy) (p) (model_imm))) ” 
  &&  “ (cm_i32_code_count retval ) ” 
  &&  “ ((tvm_opcode_code (opcode)) = 22) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_concrete_code_ready policy p ) ” 
  &&  “ (1 <= length_pre) ” 
  &&  “ (length_pre <= INT_MAX) ” 
  &&  “ (length_pre = (Zlength (raw))) ” 
  &&  “ (raw = (cons ((TVMInst (opcode) (model_imm))) ((cm_patch_tail (raw))))) ” 
  &&  “ ((length_pre - 1 ) = (Zlength ((cm_patch_tail (raw))))) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_patch_arrays_rep (ops_pre + (1 * sizeof(INT))) (imms_pre + (1 * sizeof(INT64))) (length_pre - 1 ) (cm_patch_tail (raw)) )
  **  ((ops_pre) # Int  |-> (tvm_opcode_code (opcode)))
  **  ((imms_pre) # Int64  |-> retval)
.

Definition cmc_patch_code_arrays_partial_solve_wit_2 := cmc_patch_code_arrays_partial_solve_wit_2_pure -> cmc_patch_code_arrays_partial_solve_wit_2_aux.

Definition cmc_patch_code_arrays_partial_solve_wit_3_pure := 
forall (length_pre: Z) (imms_pre: Z) (ops_pre: Z) (program_pre: Z) (functions_ptr: Z) (raw: (@list tvm_inst)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (opcode: tvm_opcode) (model_imm: Z) (PreH1 : ((tvm_opcode_code (opcode)) <> 22)) (PreH2 : (cm_wf_program policy cg p )) (PreH3 : (cm_concrete_code_ready policy p )) (PreH4 : (1 <= length_pre)) (PreH5 : (length_pre <= INT_MAX)) (PreH6 : (length_pre = (Zlength (raw)))) (PreH7 : (raw = (cons ((TVMInst (opcode) (model_imm))) ((cm_patch_tail (raw)))))) (PreH8 : ((length_pre - 1 ) = (Zlength ((cm_patch_tail (raw)))))) ,
  ((( &( "remaining_length" ) )) # Int  |-> (length_pre - 1 ))
  **  ((( &( "remaining_imms" ) )) # Ptr  |-> (imms_pre + (1 * sizeof(INT64))))
  **  ((( &( "remaining_ops" ) )) # Ptr  |-> (ops_pre + (1 * sizeof(INT))))
  **  ((( &( "immediate" ) )) # Int64  |-> model_imm)
  **  ((( &( "op" ) )) # Int  |-> (tvm_opcode_code (opcode)))
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "imms" ) )) # Ptr  |-> imms_pre)
  **  ((( &( "length" ) )) # Int  |-> length_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((ops_pre) # Int  |-> (tvm_opcode_code (opcode)))
  **  ((imms_pre) # Int64  |-> model_imm)
  **  (cm_patch_arrays_rep (ops_pre + (1 * sizeof(INT))) (imms_pre + (1 * sizeof(INT64))) (length_pre - 1 ) (cm_patch_tail (raw)) )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_concrete_code_ready policy p ) ” 
  &&  “ (0 <= (length_pre - 1 )) ” 
  &&  “ ((length_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((length_pre - 1 ) = (Zlength ((cm_patch_tail (raw))))) ” 
  &&  “ (((Zlength (raw)) - 1 ) <= INT_MAX) ” 
  &&  “ (0 <= ((Zlength (raw)) - 1 )) ”
.

Definition cmc_patch_code_arrays_partial_solve_wit_3_aux := 
forall (length_pre: Z) (imms_pre: Z) (ops_pre: Z) (program_pre: Z) (functions_ptr: Z) (raw: (@list tvm_inst)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (opcode: tvm_opcode) (model_imm: Z) (PreH1 : ((tvm_opcode_code (opcode)) <> 22)) (PreH2 : (cm_wf_program policy cg p )) (PreH3 : (cm_concrete_code_ready policy p )) (PreH4 : (1 <= length_pre)) (PreH5 : (length_pre <= INT_MAX)) (PreH6 : (length_pre = (Zlength (raw)))) (PreH7 : (raw = (cons ((TVMInst (opcode) (model_imm))) ((cm_patch_tail (raw)))))) (PreH8 : ((length_pre - 1 ) = (Zlength ((cm_patch_tail (raw)))))) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((ops_pre) # Int  |-> (tvm_opcode_code (opcode)))
  **  ((imms_pre) # Int64  |-> model_imm)
  **  (cm_patch_arrays_rep (ops_pre + (1 * sizeof(INT))) (imms_pre + (1 * sizeof(INT64))) (length_pre - 1 ) (cm_patch_tail (raw)) )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_concrete_code_ready policy p ) ” 
  &&  “ (0 <= (length_pre - 1 )) ” 
  &&  “ ((length_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((length_pre - 1 ) = (Zlength ((cm_patch_tail (raw))))) ” 
  &&  “ (((Zlength (raw)) - 1 ) <= INT_MAX) ” 
  &&  “ (0 <= ((Zlength (raw)) - 1 )) ” 
  &&  “ ((tvm_opcode_code (opcode)) <> 22) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_concrete_code_ready policy p ) ” 
  &&  “ (1 <= length_pre) ” 
  &&  “ (length_pre <= INT_MAX) ” 
  &&  “ (length_pre = (Zlength (raw))) ” 
  &&  “ (raw = (cons ((TVMInst (opcode) (model_imm))) ((cm_patch_tail (raw))))) ” 
  &&  “ ((length_pre - 1 ) = (Zlength ((cm_patch_tail (raw))))) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_patch_arrays_rep (ops_pre + (1 * sizeof(INT))) (imms_pre + (1 * sizeof(INT64))) (length_pre - 1 ) (cm_patch_tail (raw)) )
  **  ((ops_pre) # Int  |-> (tvm_opcode_code (opcode)))
  **  ((imms_pre) # Int64  |-> model_imm)
.

Definition cmc_patch_code_arrays_partial_solve_wit_3 := cmc_patch_code_arrays_partial_solve_wit_3_pure -> cmc_patch_code_arrays_partial_solve_wit_3_aux.

(*----- Function cmc_patch_resolved_calls -----*)

Definition cmc_patch_resolved_calls_entail_wit_1 := 
(
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (functions_ptr: Z) (resolved: (@list tvm_inst)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_concrete_code_ready policy p )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity resolved )
|--
  EX (imms_ptr: Z)  (ops_ptr: Z)  (raw_prefix: (@list tvm_inst)) ,
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_concrete_code_ready policy p ) ” 
  &&  “ ((cm_patch_code (policy) (p) (raw_prefix)) = resolved) ” 
  &&  “ (out <> 0) ” 
  &&  “ (ops_ptr <> 0) ” 
  &&  “ (imms_ptr <> 0) ” 
  &&  “ (0 <= (Zlength (raw_prefix))) ” 
  &&  “ ((Zlength (raw_prefix)) <= capacity) ” 
  &&  “ (capacity <= INT_MAX) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((&((emitter_pre)  # "cm_emitter" ->ₛ "output")) # Ptr  |-> out)
  **  ((&((emitter_pre)  # "cm_emitter" ->ₛ "pc")) # Int  |-> (Zlength (raw_prefix)))
  **  ((&((out)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops_ptr)
  **  ((&((out)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms_ptr)
  **  ((&((out)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> capacity)
  **  (cm_patch_arrays_rep ops_ptr imms_ptr (Zlength (raw_prefix)) raw_prefix )
  **  (IntArray.undef_seg ops_ptr (Zlength (raw_prefix)) capacity )
  **  (Int64Array.undef_seg imms_ptr (Zlength (raw_prefix)) capacity )
) \/
(
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (functions_ptr: Z) (resolved: (@list tvm_inst)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_concrete_code_ready policy p )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity resolved )
|--
  EX (imms_ptr: Z)  (ops_ptr: Z)  (raw_prefix: (@list tvm_inst)) ,
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_concrete_code_ready policy p ) ” 
  &&  “ ((cm_patch_code (policy) (p) (raw_prefix)) = resolved) ” 
  &&  “ (out <> 0) ” 
  &&  “ (ops_ptr <> 0) ” 
  &&  “ (imms_ptr <> 0) ” 
  &&  “ (0 <= (Zlength (raw_prefix))) ” 
  &&  “ ((Zlength (raw_prefix)) <= capacity) ” 
  &&  “ (capacity <= INT_MAX) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((&((emitter_pre)  # "cm_emitter" ->ₛ "output")) # Ptr  |-> out)
  **  ((&((emitter_pre)  # "cm_emitter" ->ₛ "pc")) # Int  |-> (Zlength (raw_prefix)))
  **  ((&((out)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops_ptr)
  **  ((&((out)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms_ptr)
  **  ((&((out)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> capacity)
  **  (cm_patch_arrays_rep ops_ptr imms_ptr (Zlength (raw_prefix)) raw_prefix )
  **  (IntArray.undef_seg ops_ptr (Zlength (raw_prefix)) capacity )
  **  (Int64Array.undef_seg imms_ptr (Zlength (raw_prefix)) capacity )
).

Definition cmc_patch_resolved_calls_return_wit_1 := 
(
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (functions_ptr: Z) (resolved: (@list tvm_inst)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (ops_ptr: Z) (imms_ptr: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_concrete_code_ready policy p )) (PreH3 : (0 <= (Zlength (raw_prefix)))) (PreH4 : ((Zlength (raw_prefix)) <= INT_MAX)) (PreH5 : ((Zlength (raw_prefix)) = (Zlength (raw_prefix)))) (PreH6 : (cm_wf_program policy cg p )) (PreH7 : (cm_concrete_code_ready policy p )) (PreH8 : ((cm_patch_code (policy) (p) (raw_prefix)) = resolved)) (PreH9 : (out <> 0)) (PreH10 : (ops_ptr <> 0)) (PreH11 : (imms_ptr <> 0)) (PreH12 : (0 <= (Zlength (raw_prefix)))) (PreH13 : ((Zlength (raw_prefix)) <= capacity)) (PreH14 : (capacity <= INT_MAX)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_patch_arrays_rep ops_ptr imms_ptr (Zlength (raw_prefix)) (cm_patch_code (policy) (p) (raw_prefix)) )
  **  ((&((emitter_pre)  # "cm_emitter" ->ₛ "output")) # Ptr  |-> out)
  **  ((&((emitter_pre)  # "cm_emitter" ->ₛ "pc")) # Int  |-> (Zlength (raw_prefix)))
  **  ((&((out)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops_ptr)
  **  ((&((out)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms_ptr)
  **  ((&((out)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> capacity)
  **  (IntArray.undef_seg ops_ptr (Zlength (raw_prefix)) capacity )
  **  (Int64Array.undef_seg imms_ptr (Zlength (raw_prefix)) capacity )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_concrete_code_ready policy p ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_emitter_rep emitter_pre out capacity (cm_rep_ops (resolved)) (cm_rep_imms (resolved)) )
) \/
(
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (functions_ptr: Z) (resolved: (@list tvm_inst)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (ops_ptr: Z) (imms_ptr: Z) (PreH1 : (capacity <= INT_MAX)) (PreH2 : ((Zlength (raw_prefix)) <= INT_MAX)) (PreH3 : (capacity >= INT_MIN)) (PreH4 : ((Zlength (raw_prefix)) >= INT_MIN)) (PreH5 : (cm_wf_program policy cg p )) (PreH6 : (cm_concrete_code_ready policy p )) (PreH7 : (0 <= (Zlength (raw_prefix)))) (PreH8 : ((Zlength (raw_prefix)) <= INT_MAX)) (PreH9 : (cm_wf_program policy cg p )) (PreH10 : (cm_concrete_code_ready policy p )) (PreH11 : ((cm_patch_code (policy) (p) (raw_prefix)) = resolved)) (PreH12 : (out <> 0)) (PreH13 : (ops_ptr <> 0)) (PreH14 : (imms_ptr <> 0)) (PreH15 : (0 <= (Zlength (raw_prefix)))) (PreH16 : ((Zlength (raw_prefix)) <= capacity)) (PreH17 : (capacity <= INT_MAX)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_patch_arrays_rep ops_ptr imms_ptr (Zlength (raw_prefix)) (cm_patch_code (policy) (p) (raw_prefix)) )
  **  ((&((emitter_pre)  # "cm_emitter" ->ₛ "output")) # Ptr  |-> out)
  **  ((&((emitter_pre)  # "cm_emitter" ->ₛ "pc")) # Int  |-> (Zlength (raw_prefix)))
  **  ((&((out)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops_ptr)
  **  ((&((out)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms_ptr)
  **  ((&((out)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> capacity)
  **  (IntArray.undef_seg ops_ptr (Zlength (raw_prefix)) capacity )
  **  (Int64Array.undef_seg imms_ptr (Zlength (raw_prefix)) capacity )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_emitter_rep emitter_pre out capacity (cm_rep_ops (resolved)) (cm_rep_imms (resolved)) )
).

Definition cmc_patch_resolved_calls_return_wit_1_split_goal_spatial := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (functions_ptr: Z) (resolved: (@list tvm_inst)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (ops_ptr: Z) (imms_ptr: Z) (PreH1 : (capacity <= INT_MAX)) (PreH2 : ((Zlength (raw_prefix)) <= INT_MAX)) (PreH3 : (capacity >= INT_MIN)) (PreH4 : ((Zlength (raw_prefix)) >= INT_MIN)) (PreH5 : (cm_wf_program policy cg p )) (PreH6 : (cm_concrete_code_ready policy p )) (PreH7 : (0 <= (Zlength (raw_prefix)))) (PreH8 : ((Zlength (raw_prefix)) <= INT_MAX)) (PreH9 : (cm_wf_program policy cg p )) (PreH10 : (cm_concrete_code_ready policy p )) (PreH11 : ((cm_patch_code (policy) (p) (raw_prefix)) = resolved)) (PreH12 : (out <> 0)) (PreH13 : (ops_ptr <> 0)) (PreH14 : (imms_ptr <> 0)) (PreH15 : (0 <= (Zlength (raw_prefix)))) (PreH16 : ((Zlength (raw_prefix)) <= capacity)) (PreH17 : (capacity <= INT_MAX)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_patch_arrays_rep ops_ptr imms_ptr (Zlength (raw_prefix)) (cm_patch_code (policy) (p) (raw_prefix)) )
  **  ((&((emitter_pre)  # "cm_emitter" ->ₛ "output")) # Ptr  |-> out)
  **  ((&((emitter_pre)  # "cm_emitter" ->ₛ "pc")) # Int  |-> (Zlength (raw_prefix)))
  **  ((&((out)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops_ptr)
  **  ((&((out)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms_ptr)
  **  ((&((out)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> capacity)
  **  (IntArray.undef_seg ops_ptr (Zlength (raw_prefix)) capacity )
  **  (Int64Array.undef_seg imms_ptr (Zlength (raw_prefix)) capacity )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_emitter_rep emitter_pre out capacity (cm_rep_ops (resolved)) (cm_rep_imms (resolved)) )
.

Definition cmc_patch_resolved_calls_partial_solve_wit_1_pure := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (functions_ptr: Z) (resolved: (@list tvm_inst)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (ops_ptr: Z) (imms_ptr: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_concrete_code_ready policy p )) (PreH3 : ((cm_patch_code (policy) (p) (raw_prefix)) = resolved)) (PreH4 : (out <> 0)) (PreH5 : (ops_ptr <> 0)) (PreH6 : (imms_ptr <> 0)) (PreH7 : (0 <= (Zlength (raw_prefix)))) (PreH8 : ((Zlength (raw_prefix)) <= capacity)) (PreH9 : (capacity <= INT_MAX)) ,
  ((( &( "imms" ) )) # Ptr  |-> imms_ptr)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_ptr)
  **  ((( &( "length" ) )) # Int  |-> (Zlength (raw_prefix)))
  **  ((( &( "output" ) )) # Ptr  |-> out)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((&((emitter_pre)  # "cm_emitter" ->ₛ "output")) # Ptr  |-> out)
  **  ((&((emitter_pre)  # "cm_emitter" ->ₛ "pc")) # Int  |-> (Zlength (raw_prefix)))
  **  ((&((out)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops_ptr)
  **  ((&((out)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms_ptr)
  **  ((&((out)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> capacity)
  **  (cm_patch_arrays_rep ops_ptr imms_ptr (Zlength (raw_prefix)) raw_prefix )
  **  (IntArray.undef_seg ops_ptr (Zlength (raw_prefix)) capacity )
  **  (Int64Array.undef_seg imms_ptr (Zlength (raw_prefix)) capacity )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_concrete_code_ready policy p ) ” 
  &&  “ (0 <= (Zlength (raw_prefix))) ” 
  &&  “ ((Zlength (raw_prefix)) <= INT_MAX) ” 
  &&  “ ((Zlength (raw_prefix)) = (Zlength (raw_prefix))) ”
.

Definition cmc_patch_resolved_calls_partial_solve_wit_1_aux := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (functions_ptr: Z) (resolved: (@list tvm_inst)) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (raw_prefix: (@list tvm_inst)) (ops_ptr: Z) (imms_ptr: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_concrete_code_ready policy p )) (PreH3 : ((cm_patch_code (policy) (p) (raw_prefix)) = resolved)) (PreH4 : (out <> 0)) (PreH5 : (ops_ptr <> 0)) (PreH6 : (imms_ptr <> 0)) (PreH7 : (0 <= (Zlength (raw_prefix)))) (PreH8 : ((Zlength (raw_prefix)) <= capacity)) (PreH9 : (capacity <= INT_MAX)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((&((emitter_pre)  # "cm_emitter" ->ₛ "output")) # Ptr  |-> out)
  **  ((&((emitter_pre)  # "cm_emitter" ->ₛ "pc")) # Int  |-> (Zlength (raw_prefix)))
  **  ((&((out)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops_ptr)
  **  ((&((out)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms_ptr)
  **  ((&((out)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> capacity)
  **  (cm_patch_arrays_rep ops_ptr imms_ptr (Zlength (raw_prefix)) raw_prefix )
  **  (IntArray.undef_seg ops_ptr (Zlength (raw_prefix)) capacity )
  **  (Int64Array.undef_seg imms_ptr (Zlength (raw_prefix)) capacity )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_concrete_code_ready policy p ) ” 
  &&  “ (0 <= (Zlength (raw_prefix))) ” 
  &&  “ ((Zlength (raw_prefix)) <= INT_MAX) ” 
  &&  “ ((Zlength (raw_prefix)) = (Zlength (raw_prefix))) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_concrete_code_ready policy p ) ” 
  &&  “ ((cm_patch_code (policy) (p) (raw_prefix)) = resolved) ” 
  &&  “ (out <> 0) ” 
  &&  “ (ops_ptr <> 0) ” 
  &&  “ (imms_ptr <> 0) ” 
  &&  “ (0 <= (Zlength (raw_prefix))) ” 
  &&  “ ((Zlength (raw_prefix)) <= capacity) ” 
  &&  “ (capacity <= INT_MAX) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_patch_arrays_rep ops_ptr imms_ptr (Zlength (raw_prefix)) raw_prefix )
  **  ((&((emitter_pre)  # "cm_emitter" ->ₛ "output")) # Ptr  |-> out)
  **  ((&((emitter_pre)  # "cm_emitter" ->ₛ "pc")) # Int  |-> (Zlength (raw_prefix)))
  **  ((&((out)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops_ptr)
  **  ((&((out)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms_ptr)
  **  ((&((out)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> capacity)
  **  (IntArray.undef_seg ops_ptr (Zlength (raw_prefix)) capacity )
  **  (Int64Array.undef_seg imms_ptr (Zlength (raw_prefix)) capacity )
.

Definition cmc_patch_resolved_calls_partial_solve_wit_1 := cmc_patch_resolved_calls_partial_solve_wit_1_pure -> cmc_patch_resolved_calls_partial_solve_wit_1_aux.

Module Type VC_Correct.


Axiom proof_of_cmc_patch_code_arrays_safety_wit_1 : cmc_patch_code_arrays_safety_wit_1.
Axiom proof_of_cmc_patch_code_arrays_safety_wit_2 : cmc_patch_code_arrays_safety_wit_2.
Axiom proof_of_cmc_patch_code_arrays_safety_wit_3 : cmc_patch_code_arrays_safety_wit_3.
Axiom proof_of_cmc_patch_code_arrays_safety_wit_4 : cmc_patch_code_arrays_safety_wit_4.
Axiom proof_of_cmc_patch_code_arrays_safety_wit_5 : cmc_patch_code_arrays_safety_wit_5.
Axiom proof_of_cmc_patch_code_arrays_safety_wit_6 : cmc_patch_code_arrays_safety_wit_6.
Axiom proof_of_cmc_patch_code_arrays_entail_wit_1 : cmc_patch_code_arrays_entail_wit_1.
Axiom proof_of_cmc_patch_code_arrays_return_wit_1 : cmc_patch_code_arrays_return_wit_1.
Axiom proof_of_cmc_patch_code_arrays_return_wit_2 : cmc_patch_code_arrays_return_wit_2.
Axiom proof_of_cmc_patch_code_arrays_return_wit_3 : cmc_patch_code_arrays_return_wit_3.
Axiom proof_of_cmc_patch_code_arrays_partial_solve_wit_1_pure : cmc_patch_code_arrays_partial_solve_wit_1_pure.
Axiom proof_of_cmc_patch_code_arrays_partial_solve_wit_1 : cmc_patch_code_arrays_partial_solve_wit_1.
Axiom proof_of_cmc_patch_code_arrays_partial_solve_wit_2_pure : cmc_patch_code_arrays_partial_solve_wit_2_pure.
Axiom proof_of_cmc_patch_code_arrays_partial_solve_wit_2 : cmc_patch_code_arrays_partial_solve_wit_2.
Axiom proof_of_cmc_patch_code_arrays_partial_solve_wit_3_pure : cmc_patch_code_arrays_partial_solve_wit_3_pure.
Axiom proof_of_cmc_patch_code_arrays_partial_solve_wit_3 : cmc_patch_code_arrays_partial_solve_wit_3.
Axiom proof_of_cmc_patch_resolved_calls_entail_wit_1 : cmc_patch_resolved_calls_entail_wit_1.
Axiom proof_of_cmc_patch_resolved_calls_return_wit_1 : cmc_patch_resolved_calls_return_wit_1.
Axiom proof_of_cmc_patch_resolved_calls_partial_solve_wit_1_pure : cmc_patch_resolved_calls_partial_solve_wit_1_pure.
Axiom proof_of_cmc_patch_resolved_calls_partial_solve_wit_1 : cmc_patch_resolved_calls_partial_solve_wit_1.

End VC_Correct.
