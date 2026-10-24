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
Require Import SimpleC.EE.QCP_demos_human.cmc_compile_migration_lib.
Local Open Scope sac.

(*----- Function cmc_compile -----*)

Definition cmc_compile_safety_wit_1 := 
forall (output_pre: Z) (program_pre: Z) (data_capacity: Z) (code_capacity: Z) (p: cm_program) (sp: cm_source_lookup_policy) (functions_ptr: Z) (ops_ptr: Z) (imms_ptr: Z) (data_ptr: Z) (old_entry: Z) (retval: Z) (retval_2: Z) (PreH1 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH2 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH3 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH4 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH5 : (retval_2 = (cm_model_data_length (p)))) (PreH6 : (cm_i32_code_count retval_2 )) (PreH7 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH8 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH9 : (retval = (cm_model_code_length ((cm_source_function_policy (sp))) (p)))) (PreH10 : (cm_i32_code_count retval )) (PreH11 : (program_pre <> 0)) (PreH12 : (output_pre <> 0)) (PreH13 : (cm_semantic_wf_program (cm_source_function_policy (sp)) p )) (PreH14 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH15 : (cm_typed_program (cm_source_function_policy (sp)) p )) (PreH16 : (cm_concrete_code_ready (cm_source_function_policy (sp)) p )) (PreH17 : (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) )) (PreH18 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH19 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH20 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH21 : (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) )) (PreH22 : (0 <= (cm_rep_globals_size ((cm_program_globals (p)))))) (PreH23 : (0 <= (cm_rep_strings_size ((cm_program_strings (p)))))) (PreH24 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH25 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH26 : (0 <= code_capacity)) (PreH27 : (code_capacity <= INT_MAX)) (PreH28 : (0 <= data_capacity)) (PreH29 : (data_capacity <= INT_MAX)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  ((( &( "data_length" ) )) # Int  |-> retval_2)
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((( &( "code_length" ) )) # Int  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((&((output_pre)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> code_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> retval)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> retval_2)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> old_entry)
  **  (cm_undef_int_buffer ops_ptr code_capacity )
  **  (cm_undef_int64_buffer imms_ptr code_capacity )
  **  (cm_undef_uint8_buffer data_ptr data_capacity )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmc_compile_safety_wit_2 := 
forall (output_pre: Z) (program_pre: Z) (data_capacity: Z) (code_capacity: Z) (p: cm_program) (sp: cm_source_lookup_policy) (functions_ptr: Z) (ops_ptr: Z) (imms_ptr: Z) (data_ptr: Z) (old_entry: Z) (retval: Z) (retval_2: Z) (PreH1 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH2 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH3 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH4 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH5 : (retval_2 = (cm_model_data_length (p)))) (PreH6 : (cm_i32_code_count retval_2 )) (PreH7 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH8 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH9 : (retval = (cm_model_code_length ((cm_source_function_policy (sp))) (p)))) (PreH10 : (cm_i32_code_count retval )) (PreH11 : (program_pre <> 0)) (PreH12 : (output_pre <> 0)) (PreH13 : (cm_semantic_wf_program (cm_source_function_policy (sp)) p )) (PreH14 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH15 : (cm_typed_program (cm_source_function_policy (sp)) p )) (PreH16 : (cm_concrete_code_ready (cm_source_function_policy (sp)) p )) (PreH17 : (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) )) (PreH18 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH19 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH20 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH21 : (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) )) (PreH22 : (0 <= (cm_rep_globals_size ((cm_program_globals (p)))))) (PreH23 : (0 <= (cm_rep_strings_size ((cm_program_strings (p)))))) (PreH24 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH25 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH26 : (0 <= code_capacity)) (PreH27 : (code_capacity <= INT_MAX)) (PreH28 : (0 <= data_capacity)) (PreH29 : (data_capacity <= INT_MAX)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  ((( &( "data_length" ) )) # Int  |-> retval_2)
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((( &( "code_length" ) )) # Int  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((&((output_pre)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> code_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> retval)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> retval_2)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> old_entry)
  **  (cm_undef_int_buffer ops_ptr code_capacity )
  **  (cm_undef_int64_buffer imms_ptr code_capacity )
  **  (cm_undef_uint8_buffer data_ptr data_capacity )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmc_compile_safety_wit_3 := 
forall (output_pre: Z) (program_pre: Z) (data_capacity: Z) (code_capacity: Z) (p: cm_program) (sp: cm_source_lookup_policy) (functions_ptr: Z) (ops_ptr: Z) (imms_ptr: Z) (data_ptr: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval > code_capacity)) (PreH2 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH3 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH4 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH5 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH6 : (retval_2 = (cm_model_data_length (p)))) (PreH7 : (cm_i32_code_count retval_2 )) (PreH8 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH9 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH10 : (retval = (cm_model_code_length ((cm_source_function_policy (sp))) (p)))) (PreH11 : (cm_i32_code_count retval )) (PreH12 : (program_pre <> 0)) (PreH13 : (output_pre <> 0)) (PreH14 : (cm_semantic_wf_program (cm_source_function_policy (sp)) p )) (PreH15 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH16 : (cm_typed_program (cm_source_function_policy (sp)) p )) (PreH17 : (cm_concrete_code_ready (cm_source_function_policy (sp)) p )) (PreH18 : (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) )) (PreH19 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH20 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH21 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH22 : (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) )) (PreH23 : (0 <= (cm_rep_globals_size ((cm_program_globals (p)))))) (PreH24 : (0 <= (cm_rep_strings_size ((cm_program_strings (p)))))) (PreH25 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH26 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH27 : (0 <= code_capacity)) (PreH28 : (code_capacity <= INT_MAX)) (PreH29 : (0 <= data_capacity)) (PreH30 : (data_capacity <= INT_MAX)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  ((( &( "data_length" ) )) # Int  |-> retval_2)
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((( &( "code_length" ) )) # Int  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((&((output_pre)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> code_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> retval)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> retval_2)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> (-1))
  **  (cm_undef_int_buffer ops_ptr code_capacity )
  **  (cm_undef_int64_buffer imms_ptr code_capacity )
  **  (cm_undef_uint8_buffer data_ptr data_capacity )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmc_compile_safety_wit_4 := 
forall (output_pre: Z) (program_pre: Z) (data_capacity: Z) (code_capacity: Z) (p: cm_program) (sp: cm_source_lookup_policy) (functions_ptr: Z) (ops_ptr: Z) (imms_ptr: Z) (data_ptr: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 > data_capacity)) (PreH2 : (retval <= code_capacity)) (PreH3 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH4 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH5 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH6 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH7 : (retval_2 = (cm_model_data_length (p)))) (PreH8 : (cm_i32_code_count retval_2 )) (PreH9 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH10 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH11 : (retval = (cm_model_code_length ((cm_source_function_policy (sp))) (p)))) (PreH12 : (cm_i32_code_count retval )) (PreH13 : (program_pre <> 0)) (PreH14 : (output_pre <> 0)) (PreH15 : (cm_semantic_wf_program (cm_source_function_policy (sp)) p )) (PreH16 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH17 : (cm_typed_program (cm_source_function_policy (sp)) p )) (PreH18 : (cm_concrete_code_ready (cm_source_function_policy (sp)) p )) (PreH19 : (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) )) (PreH20 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH21 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH22 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH23 : (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) )) (PreH24 : (0 <= (cm_rep_globals_size ((cm_program_globals (p)))))) (PreH25 : (0 <= (cm_rep_strings_size ((cm_program_strings (p)))))) (PreH26 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH27 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH28 : (0 <= code_capacity)) (PreH29 : (code_capacity <= INT_MAX)) (PreH30 : (0 <= data_capacity)) (PreH31 : (data_capacity <= INT_MAX)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  ((( &( "data_length" ) )) # Int  |-> retval_2)
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((( &( "code_length" ) )) # Int  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((&((output_pre)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> code_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> retval)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> retval_2)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> (-1))
  **  (cm_undef_int_buffer ops_ptr code_capacity )
  **  (cm_undef_int64_buffer imms_ptr code_capacity )
  **  (cm_undef_uint8_buffer data_ptr data_capacity )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmc_compile_safety_wit_5 := 
forall (output_pre: Z) (program_pre: Z) (data_capacity: Z) (code_capacity: Z) (p: cm_program) (sp: cm_source_lookup_policy) (functions_ptr: Z) (ops_ptr: Z) (imms_ptr: Z) (data_ptr: Z) (code_length: Z) (data_length: Z) (PreH1 : (program_pre <> 0)) (PreH2 : (output_pre <> 0)) (PreH3 : (ops_ptr <> 0)) (PreH4 : (imms_ptr <> 0)) (PreH5 : (data_ptr <> 0)) (PreH6 : (code_length = (cm_model_code_length ((cm_source_function_policy (sp))) (p)))) (PreH7 : (data_length = (cm_model_data_length (p)))) (PreH8 : (0 <= code_length)) (PreH9 : (code_length <= code_capacity)) (PreH10 : (0 <= data_length)) (PreH11 : (data_length <= data_capacity)) (PreH12 : (cm_semantic_wf_program (cm_source_function_policy (sp)) p )) (PreH13 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH14 : (cm_typed_program (cm_source_function_policy (sp)) p )) (PreH15 : (cm_concrete_code_ready (cm_source_function_policy (sp)) p )) (PreH16 : (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) )) (PreH17 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH18 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH19 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH20 : (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) )) (PreH21 : (0 <= (cm_rep_globals_size ((cm_program_globals (p)))))) (PreH22 : (0 <= (cm_rep_strings_size ((cm_program_strings (p)))))) (PreH23 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH24 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH25 : (0 <= code_capacity)) (PreH26 : (code_capacity <= INT_MAX)) (PreH27 : (0 <= data_capacity)) (PreH28 : (data_capacity <= INT_MAX)) ,
  ((&(( &( "emitter" ) )->ₛ "pc")) # Int  |->_)
  **  ((&(( &( "emitter" ) )->ₛ "output")) # Ptr  |-> output_pre)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "code_length" ) )) # Int  |-> code_length)
  **  ((( &( "data_length" ) )) # Int  |-> data_length)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> code_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> code_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> data_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> (-1))
  **  (IntArray.seg ops_ptr 0 0 (@nil Z) )
  **  (IntArray.undef_seg ops_ptr 0 code_capacity )
  **  (Int64Array.seg imms_ptr 0 0 (@nil Z) )
  **  (Int64Array.undef_seg imms_ptr 0 code_capacity )
  **  (UCharArray.seg data_ptr 0 0 (@nil Z) )
  **  (UCharArray.undef_seg data_ptr 0 data_capacity )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_compile_safety_wit_6 := 
forall (output_pre: Z) (program_pre: Z) (data_capacity: Z) (code_capacity: Z) (p: cm_program) (sp: cm_source_lookup_policy) (functions_ptr: Z) (ops_ptr: Z) (imms_ptr: Z) (data_ptr: Z) (globals_ptr: Z) (strings_ptr: Z) (code_length: Z) (data_length: Z) (emitted_data: Z) (PreH1 : (program_pre <> 0)) (PreH2 : (output_pre <> 0)) (PreH3 : (ops_ptr <> 0)) (PreH4 : (imms_ptr <> 0)) (PreH5 : (data_ptr <> 0)) (PreH6 : (code_length = (cm_model_code_length ((cm_source_function_policy (sp))) (p)))) (PreH7 : (data_length = (cm_model_data_length (p)))) (PreH8 : (0 <= code_length)) (PreH9 : (code_length <= code_capacity)) (PreH10 : (0 <= data_length)) (PreH11 : (data_length <= data_capacity)) (PreH12 : (cm_semantic_wf_program (cm_source_function_policy (sp)) p )) (PreH13 : (emitted_data = data_length)) ,
  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "code_length" ) )) # Int  |-> code_length)
  **  ((( &( "data_length" ) )) # Int  |-> data_length)
  **  ((( &( "globals" ) )) # Ptr  |-> globals_ptr)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_ptr)
  **  ((( &( "data" ) )) # Ptr  |-> data_ptr)
  **  ((( &( "output_data_capacity" ) )) # Int  |-> data_capacity)
  **  ((( &( "emitted_data" ) )) # Int  |-> emitted_data)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> code_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> code_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> data_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> (-1))
  **  ((&(( &( "emitter" ) )->ₛ "output")) # Ptr  |-> output_pre)
  **  ((&(( &( "emitter" ) )->ₛ "pc")) # Int  |-> code_length)
  **  (IntArray.seg ops_ptr 0 code_length (cm_rep_ops ((cm_model_code ((cm_source_function_policy (sp))) (p)))) )
  **  (IntArray.undef_seg ops_ptr code_length code_capacity )
  **  (Int64Array.seg imms_ptr 0 code_length (cm_rep_imms ((cm_model_code ((cm_source_function_policy (sp))) (p)))) )
  **  (Int64Array.undef_seg imms_ptr code_length code_capacity )
  **  (UCharArray.seg data_ptr 0 data_length (cm_model_data_bytes (p)) )
  **  (UCharArray.undef_seg data_ptr data_length data_capacity )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_compile_safety_wit_7 := 
forall (output_pre: Z) (program_pre: Z) (data_capacity: Z) (code_capacity: Z) (p: cm_program) (sp: cm_source_lookup_policy) (functions_ptr: Z) (ops_ptr: Z) (imms_ptr: Z) (data_ptr: Z) (globals_ptr: Z) (strings_ptr: Z) (code_length: Z) (data_length: Z) (emitted_data: Z) (PreH1 : (program_pre <> 0)) (PreH2 : (output_pre <> 0)) (PreH3 : (ops_ptr <> 0)) (PreH4 : (imms_ptr <> 0)) (PreH5 : (data_ptr <> 0)) (PreH6 : (code_length = (cm_model_code_length ((cm_source_function_policy (sp))) (p)))) (PreH7 : (data_length = (cm_model_data_length (p)))) (PreH8 : (0 <= code_length)) (PreH9 : (code_length <= code_capacity)) (PreH10 : (0 <= data_length)) (PreH11 : (data_length <= data_capacity)) (PreH12 : (cm_semantic_wf_program (cm_source_function_policy (sp)) p )) (PreH13 : (emitted_data = data_length)) ,
  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "code_length" ) )) # Int  |-> code_length)
  **  ((( &( "data_length" ) )) # Int  |-> data_length)
  **  ((( &( "globals" ) )) # Ptr  |-> globals_ptr)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_ptr)
  **  ((( &( "data" ) )) # Ptr  |-> data_ptr)
  **  ((( &( "output_data_capacity" ) )) # Int  |-> data_capacity)
  **  ((( &( "emitted_data" ) )) # Int  |-> emitted_data)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> code_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> code_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> data_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> 0)
  **  ((&(( &( "emitter" ) )->ₛ "output")) # Ptr  |-> output_pre)
  **  ((&(( &( "emitter" ) )->ₛ "pc")) # Int  |-> code_length)
  **  (IntArray.seg ops_ptr 0 code_length (cm_rep_ops ((cm_model_code ((cm_source_function_policy (sp))) (p)))) )
  **  (IntArray.undef_seg ops_ptr code_length code_capacity )
  **  (Int64Array.seg imms_ptr 0 code_length (cm_rep_imms ((cm_model_code ((cm_source_function_policy (sp))) (p)))) )
  **  (Int64Array.undef_seg imms_ptr code_length code_capacity )
  **  (UCharArray.seg data_ptr 0 data_length (cm_model_data_bytes (p)) )
  **  (UCharArray.undef_seg data_ptr data_length data_capacity )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_compile_entail_wit_1 := 
(
forall (output_pre: Z) (program_pre: Z) (data_capacity: Z) (code_capacity: Z) (p: cm_program) (sp: cm_source_lookup_policy) ,
  (cm_program_rep (cm_source_function_policy (sp)) program_pre p )
  **  (cm_output_pre output_pre code_capacity data_capacity )
|--
  EX (old_entry: Z)  (old_data: Z)  (old_code: Z)  (data_ptr: Z)  (imms_ptr: Z)  (ops_ptr: Z)  (functions_ptr: Z) ,
  “ (program_pre <> 0) ” 
  &&  “ (output_pre <> 0) ” 
  &&  “ (cm_semantic_wf_program (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p ) ” 
  &&  “ (cm_typed_program (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_concrete_code_ready (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) ) ” 
  &&  “ (0 <= (cm_rep_globals_size ((cm_program_globals (p))))) ” 
  &&  “ (0 <= (cm_rep_strings_size ((cm_program_strings (p))))) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) )) ” 
  &&  “ (0 <= code_capacity) ” 
  &&  “ (code_capacity <= INT_MAX) ” 
  &&  “ (0 <= data_capacity) ” 
  &&  “ (data_capacity <= INT_MAX) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> code_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> old_code)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> old_data)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> old_entry)
  **  (cm_undef_int_buffer ops_ptr code_capacity )
  **  (cm_undef_int64_buffer imms_ptr code_capacity )
  **  (cm_undef_uint8_buffer data_ptr data_capacity )
) \/
(
forall (output_pre: Z) (program_pre: Z) (data_capacity: Z) (code_capacity: Z) (p: cm_program) (sp: cm_source_lookup_policy) ,
  (cm_program_rep (cm_source_function_policy (sp)) program_pre p )
  **  (cm_output_pre output_pre code_capacity data_capacity )
|--
  EX (old_entry: Z)  (old_data: Z)  (old_code: Z)  (data_ptr: Z)  (imms_ptr: Z)  (ops_ptr: Z)  (functions_ptr: Z) ,
  “ (program_pre <> 0) ” 
  &&  “ (output_pre <> 0) ” 
  &&  “ (cm_semantic_wf_program (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p ) ” 
  &&  “ (cm_typed_program (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_concrete_code_ready (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) ) ” 
  &&  “ (0 <= (cm_rep_globals_size ((cm_program_globals (p))))) ” 
  &&  “ (0 <= (cm_rep_strings_size ((cm_program_strings (p))))) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) )) ” 
  &&  “ (0 <= code_capacity) ” 
  &&  “ (code_capacity <= INT_MAX) ” 
  &&  “ (0 <= data_capacity) ” 
  &&  “ (data_capacity <= INT_MAX) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> code_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> old_code)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> old_data)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> old_entry)
  **  (cm_undef_int_buffer ops_ptr code_capacity )
  **  (cm_undef_int64_buffer imms_ptr code_capacity )
  **  (cm_undef_uint8_buffer data_ptr data_capacity )
).

Definition cmc_compile_entail_wit_2 := 
(
forall (output_pre: Z) (program_pre: Z) (data_capacity: Z) (code_capacity: Z) (p: cm_program) (sp: cm_source_lookup_policy) (functions_ptr_2: Z) (ops_ptr_2: Z) (imms_ptr_2: Z) (data_ptr_2: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <= data_capacity)) (PreH2 : (retval <= code_capacity)) (PreH3 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH4 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH5 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH6 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH7 : (retval_2 = (cm_model_data_length (p)))) (PreH8 : (cm_i32_code_count retval_2 )) (PreH9 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH10 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH11 : (retval = (cm_model_code_length ((cm_source_function_policy (sp))) (p)))) (PreH12 : (cm_i32_code_count retval )) (PreH13 : (program_pre <> 0)) (PreH14 : (output_pre <> 0)) (PreH15 : (cm_semantic_wf_program (cm_source_function_policy (sp)) p )) (PreH16 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH17 : (cm_typed_program (cm_source_function_policy (sp)) p )) (PreH18 : (cm_concrete_code_ready (cm_source_function_policy (sp)) p )) (PreH19 : (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) )) (PreH20 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH21 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH22 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH23 : (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) )) (PreH24 : (0 <= (cm_rep_globals_size ((cm_program_globals (p)))))) (PreH25 : (0 <= (cm_rep_strings_size ((cm_program_strings (p)))))) (PreH26 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH27 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH28 : (0 <= code_capacity)) (PreH29 : (code_capacity <= INT_MAX)) (PreH30 : (0 <= data_capacity)) (PreH31 : (data_capacity <= INT_MAX)) ,
  (cm_program_context_rep program_pre p functions_ptr_2 )
  **  (cm_function_list_rep functions_ptr_2 (cm_program_functions (p)) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops_ptr_2)
  **  ((&((output_pre)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms_ptr_2)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr_2)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> code_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> retval)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> retval_2)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> (-1))
  **  (cm_undef_int_buffer ops_ptr_2 code_capacity )
  **  (cm_undef_int64_buffer imms_ptr_2 code_capacity )
  **  (cm_undef_uint8_buffer data_ptr_2 data_capacity )
|--
  EX (functions_ptr: Z)  (data_ptr: Z)  (imms_ptr: Z)  (ops_ptr: Z) ,
  “ (program_pre <> 0) ” 
  &&  “ (output_pre <> 0) ” 
  &&  “ (ops_ptr <> 0) ” 
  &&  “ (imms_ptr <> 0) ” 
  &&  “ (data_ptr <> 0) ” 
  &&  “ (retval = (cm_model_code_length ((cm_source_function_policy (sp))) (p))) ” 
  &&  “ (retval_2 = (cm_model_data_length (p))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= code_capacity) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= data_capacity) ” 
  &&  “ (cm_semantic_wf_program (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p ) ” 
  &&  “ (cm_typed_program (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_concrete_code_ready (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) ) ” 
  &&  “ (0 <= (cm_rep_globals_size ((cm_program_globals (p))))) ” 
  &&  “ (0 <= (cm_rep_strings_size ((cm_program_strings (p))))) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) )) ” 
  &&  “ (0 <= code_capacity) ” 
  &&  “ (code_capacity <= INT_MAX) ” 
  &&  “ (0 <= data_capacity) ” 
  &&  “ (data_capacity <= INT_MAX) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> code_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> retval)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> retval_2)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> (-1))
  **  (IntArray.seg ops_ptr 0 0 (@nil Z) )
  **  (IntArray.undef_seg ops_ptr 0 code_capacity )
  **  (Int64Array.seg imms_ptr 0 0 (@nil Z) )
  **  (Int64Array.undef_seg imms_ptr 0 code_capacity )
  **  (UCharArray.seg data_ptr 0 0 (@nil Z) )
  **  (UCharArray.undef_seg data_ptr 0 data_capacity )
) \/
(
forall (output_pre: Z) (program_pre: Z) (data_capacity: Z) (code_capacity: Z) (p: cm_program) (sp: cm_source_lookup_policy) (functions_ptr_2: Z) (ops_ptr_2: Z) (imms_ptr_2: Z) (data_ptr_2: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <= data_capacity)) (PreH2 : (retval <= code_capacity)) (PreH3 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH4 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH5 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH6 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH7 : (retval_2 = (cm_model_data_length (p)))) (PreH8 : (cm_i32_code_count retval_2 )) (PreH9 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH10 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH11 : (retval = (cm_model_code_length ((cm_source_function_policy (sp))) (p)))) (PreH12 : (cm_i32_code_count retval )) (PreH13 : (program_pre <> 0)) (PreH14 : (output_pre <> 0)) (PreH15 : (cm_semantic_wf_program (cm_source_function_policy (sp)) p )) (PreH16 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH17 : (cm_typed_program (cm_source_function_policy (sp)) p )) (PreH18 : (cm_concrete_code_ready (cm_source_function_policy (sp)) p )) (PreH19 : (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) )) (PreH20 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH21 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH22 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH23 : (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) )) (PreH24 : (0 <= (cm_rep_globals_size ((cm_program_globals (p)))))) (PreH25 : (0 <= (cm_rep_strings_size ((cm_program_strings (p)))))) (PreH26 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH27 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH28 : (0 <= code_capacity)) (PreH29 : (code_capacity <= INT_MAX)) (PreH30 : (0 <= data_capacity)) (PreH31 : (data_capacity <= INT_MAX)) ,
  (cm_program_context_rep program_pre p functions_ptr_2 )
  **  (cm_function_list_rep functions_ptr_2 (cm_program_functions (p)) )
  **  (cm_undef_int_buffer ops_ptr_2 code_capacity )
  **  (cm_undef_int64_buffer imms_ptr_2 code_capacity )
  **  (cm_undef_uint8_buffer data_ptr_2 data_capacity )
|--
  EX (functions_ptr: Z) ,
  “ (program_pre <> 0) ” 
  &&  “ (output_pre <> 0) ” 
  &&  “ (ops_ptr_2 <> 0) ” 
  &&  “ (imms_ptr_2 <> 0) ” 
  &&  “ (data_ptr_2 <> 0) ” 
  &&  “ (retval = (cm_model_code_length ((cm_source_function_policy (sp))) (p))) ” 
  &&  “ (retval_2 = (cm_model_data_length (p))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= code_capacity) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= data_capacity) ” 
  &&  “ (cm_semantic_wf_program (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p ) ” 
  &&  “ (cm_typed_program (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_concrete_code_ready (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) ) ” 
  &&  “ (0 <= (cm_rep_globals_size ((cm_program_globals (p))))) ” 
  &&  “ (0 <= (cm_rep_strings_size ((cm_program_strings (p))))) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) )) ” 
  &&  “ (0 <= code_capacity) ” 
  &&  “ (code_capacity <= INT_MAX) ” 
  &&  “ (0 <= data_capacity) ” 
  &&  “ (data_capacity <= INT_MAX) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (IntArray.undef_seg ops_ptr_2 0 code_capacity )
  **  (Int64Array.undef_seg imms_ptr_2 0 code_capacity )
  **  (UCharArray.undef_seg data_ptr_2 0 data_capacity )
).

Definition cmc_compile_entail_wit_3 := 
(
forall (output_pre: Z) (program_pre: Z) (data_capacity: Z) (code_capacity: Z) (p: cm_program) (sp: cm_source_lookup_policy) (functions_ptr_2: Z) (ops_ptr: Z) (imms_ptr: Z) (data_ptr_2: Z) (code_length: Z) (data_length: Z) (PreH1 : (program_pre <> 0)) (PreH2 : (output_pre <> 0)) (PreH3 : (ops_ptr <> 0)) (PreH4 : (imms_ptr <> 0)) (PreH5 : (data_ptr_2 <> 0)) (PreH6 : (code_length = (cm_model_code_length ((cm_source_function_policy (sp))) (p)))) (PreH7 : (data_length = (cm_model_data_length (p)))) (PreH8 : (0 <= code_length)) (PreH9 : (code_length <= code_capacity)) (PreH10 : (0 <= data_length)) (PreH11 : (data_length <= data_capacity)) (PreH12 : (cm_semantic_wf_program (cm_source_function_policy (sp)) p )) (PreH13 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH14 : (cm_typed_program (cm_source_function_policy (sp)) p )) (PreH15 : (cm_concrete_code_ready (cm_source_function_policy (sp)) p )) (PreH16 : (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) )) (PreH17 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH18 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH19 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH20 : (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) )) (PreH21 : (0 <= (cm_rep_globals_size ((cm_program_globals (p)))))) (PreH22 : (0 <= (cm_rep_strings_size ((cm_program_strings (p)))))) (PreH23 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH24 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH25 : (0 <= code_capacity)) (PreH26 : (code_capacity <= INT_MAX)) (PreH27 : (0 <= data_capacity)) (PreH28 : (data_capacity <= INT_MAX)) ,
  ((&(( &( "emitter" ) )->ₛ "pc")) # Int  |-> 0)
  **  ((&(( &( "emitter" ) )->ₛ "output")) # Ptr  |-> output_pre)
  **  (cm_program_context_rep program_pre p functions_ptr_2 )
  **  (cm_function_list_rep functions_ptr_2 (cm_program_functions (p)) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr_2)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> code_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> code_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> data_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> (-1))
  **  (IntArray.seg ops_ptr 0 0 (@nil Z) )
  **  (IntArray.undef_seg ops_ptr 0 code_capacity )
  **  (Int64Array.seg imms_ptr 0 0 (@nil Z) )
  **  (Int64Array.undef_seg imms_ptr 0 code_capacity )
  **  (UCharArray.seg data_ptr_2 0 0 (@nil Z) )
  **  (UCharArray.undef_seg data_ptr_2 0 data_capacity )
|--
  EX (functions_ptr: Z)  (data_ptr: Z) ,
  “ (program_pre <> 0) ” 
  &&  “ (output_pre <> 0) ” 
  &&  “ (data_ptr <> 0) ” 
  &&  “ (code_length = (cm_model_code_length ((cm_source_function_policy (sp))) (p))) ” 
  &&  “ (data_length = (cm_model_data_length (p))) ” 
  &&  “ (0 <= code_length) ” 
  &&  “ (code_length <= code_capacity) ” 
  &&  “ (0 <= data_length) ” 
  &&  “ (data_length <= data_capacity) ” 
  &&  “ (cm_semantic_wf_program (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p ) ” 
  &&  “ (cm_typed_program (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_concrete_code_ready (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) ) ” 
  &&  “ (0 <= (cm_rep_globals_size ((cm_program_globals (p))))) ” 
  &&  “ (0 <= (cm_rep_strings_size ((cm_program_strings (p))))) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) )) ” 
  &&  “ (0 <= code_capacity) ” 
  &&  “ (code_capacity <= INT_MAX) ” 
  &&  “ (0 <= data_capacity) ” 
  &&  “ (data_capacity <= INT_MAX) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> code_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> data_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> (-1))
  **  (UCharArray.seg data_ptr 0 0 (@nil Z) )
  **  (UCharArray.undef_seg data_ptr 0 data_capacity )
  **  (cm_resolved_emitter_plan_rep (cm_source_function_policy (sp)) p ( &( "emitter" ) ) output_pre code_capacity (@nil tvm_inst) (app ((cm_model_code ((cm_source_function_policy (sp))) (p))) ((@nil tvm_inst))) )
) \/
(
forall (output_pre: Z) (program_pre: Z) (data_capacity: Z) (code_capacity: Z) (p: cm_program) (sp: cm_source_lookup_policy) (functions_ptr_2: Z) (ops_ptr: Z) (imms_ptr: Z) (data_ptr_2: Z) (code_length: Z) (data_length: Z) (PreH1 : (code_capacity <= INT_MAX)) (PreH2 : (0 <= INT_MAX)) (PreH3 : (code_capacity >= INT_MIN)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (program_pre <> 0)) (PreH6 : (output_pre <> 0)) (PreH7 : (ops_ptr <> 0)) (PreH8 : (imms_ptr <> 0)) (PreH9 : (data_ptr_2 <> 0)) (PreH10 : (code_length = (cm_model_code_length ((cm_source_function_policy (sp))) (p)))) (PreH11 : (data_length = (cm_model_data_length (p)))) (PreH12 : (0 <= code_length)) (PreH13 : (code_length <= code_capacity)) (PreH14 : (0 <= data_length)) (PreH15 : (data_length <= data_capacity)) (PreH16 : (cm_semantic_wf_program (cm_source_function_policy (sp)) p )) (PreH17 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH18 : (cm_typed_program (cm_source_function_policy (sp)) p )) (PreH19 : (cm_concrete_code_ready (cm_source_function_policy (sp)) p )) (PreH20 : (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) )) (PreH21 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH22 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH23 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH24 : (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) )) (PreH25 : (0 <= (cm_rep_globals_size ((cm_program_globals (p)))))) (PreH26 : (0 <= (cm_rep_strings_size ((cm_program_strings (p)))))) (PreH27 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH28 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH29 : (0 <= code_capacity)) (PreH30 : (code_capacity <= INT_MAX)) (PreH31 : (0 <= data_capacity)) (PreH32 : (data_capacity <= INT_MAX)) ,
  ((&(( &( "emitter" ) )->ₛ "pc")) # Int  |-> 0)
  **  ((&(( &( "emitter" ) )->ₛ "output")) # Ptr  |-> output_pre)
  **  (cm_program_context_rep program_pre p functions_ptr_2 )
  **  (cm_function_list_rep functions_ptr_2 (cm_program_functions (p)) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> code_capacity)
  **  (IntArray.seg ops_ptr 0 0 (@nil Z) )
  **  (IntArray.undef_seg ops_ptr 0 code_capacity )
  **  (Int64Array.seg imms_ptr 0 0 (@nil Z) )
  **  (Int64Array.undef_seg imms_ptr 0 code_capacity )
|--
  EX (functions_ptr: Z) ,
  “ (program_pre <> 0) ” 
  &&  “ (output_pre <> 0) ” 
  &&  “ (data_ptr_2 <> 0) ” 
  &&  “ (code_length = (cm_model_code_length ((cm_source_function_policy (sp))) (p))) ” 
  &&  “ (data_length = (cm_model_data_length (p))) ” 
  &&  “ (0 <= code_length) ” 
  &&  “ (code_length <= code_capacity) ” 
  &&  “ (0 <= data_length) ” 
  &&  “ (data_length <= data_capacity) ” 
  &&  “ (cm_semantic_wf_program (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p ) ” 
  &&  “ (cm_typed_program (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_concrete_code_ready (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) ) ” 
  &&  “ (0 <= (cm_rep_globals_size ((cm_program_globals (p))))) ” 
  &&  “ (0 <= (cm_rep_strings_size ((cm_program_strings (p))))) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) )) ” 
  &&  “ (0 <= code_capacity) ” 
  &&  “ (code_capacity <= INT_MAX) ” 
  &&  “ (0 <= data_capacity) ” 
  &&  “ (data_capacity <= INT_MAX) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_resolved_emitter_plan_rep (cm_source_function_policy (sp)) p ( &( "emitter" ) ) output_pre code_capacity (@nil tvm_inst) (app ((cm_model_code ((cm_source_function_policy (sp))) (p))) ((@nil tvm_inst))) )
).

Definition cmc_compile_entail_wit_4 := 
(
forall (output_pre: Z) (program_pre: Z) (data_capacity: Z) (code_capacity: Z) (p: cm_program) (sp: cm_source_lookup_policy) (functions_ptr_2: Z) (data_ptr_2: Z) (code_length: Z) (data_length: Z) (PreH1 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH2 : (cm_typed_program (cm_source_function_policy (sp)) p )) (PreH3 : (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) )) (PreH4 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH5 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH6 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH7 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH8 : (program_pre <> 0)) (PreH9 : (output_pre <> 0)) (PreH10 : (data_ptr_2 <> 0)) (PreH11 : (code_length = (cm_model_code_length ((cm_source_function_policy (sp))) (p)))) (PreH12 : (data_length = (cm_model_data_length (p)))) (PreH13 : (0 <= code_length)) (PreH14 : (code_length <= code_capacity)) (PreH15 : (0 <= data_length)) (PreH16 : (data_length <= data_capacity)) (PreH17 : (cm_semantic_wf_program (cm_source_function_policy (sp)) p )) (PreH18 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH19 : (cm_typed_program (cm_source_function_policy (sp)) p )) (PreH20 : (cm_concrete_code_ready (cm_source_function_policy (sp)) p )) (PreH21 : (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) )) (PreH22 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH23 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH24 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH25 : (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) )) (PreH26 : (0 <= (cm_rep_globals_size ((cm_program_globals (p)))))) (PreH27 : (0 <= (cm_rep_strings_size ((cm_program_strings (p)))))) (PreH28 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH29 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH30 : (0 <= code_capacity)) (PreH31 : (code_capacity <= INT_MAX)) (PreH32 : (0 <= data_capacity)) (PreH33 : (data_capacity <= INT_MAX)) ,
  (cm_program_context_rep program_pre p functions_ptr_2 )
  **  (cm_function_list_rep functions_ptr_2 (cm_program_functions (p)) )
  **  (cm_resolved_emitter_plan_rep (cm_source_function_policy (sp)) p ( &( "emitter" ) ) output_pre code_capacity (app ((@nil tvm_inst)) ((cm_model_code ((cm_source_function_policy (sp))) (p)))) (@nil tvm_inst) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr_2)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> code_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> data_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> (-1))
  **  (UCharArray.seg data_ptr_2 0 0 (@nil Z) )
  **  (UCharArray.undef_seg data_ptr_2 0 data_capacity )
|--
  EX (functions_ptr: Z)  (data_ptr: Z) ,
  “ (program_pre <> 0) ” 
  &&  “ (output_pre <> 0) ” 
  &&  “ (data_ptr <> 0) ” 
  &&  “ (code_length = (cm_model_code_length ((cm_source_function_policy (sp))) (p))) ” 
  &&  “ (data_length = (cm_model_data_length (p))) ” 
  &&  “ (0 <= code_length) ” 
  &&  “ (code_length <= code_capacity) ” 
  &&  “ (0 <= data_length) ” 
  &&  “ (data_length <= data_capacity) ” 
  &&  “ (cm_semantic_wf_program (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p ) ” 
  &&  “ (cm_typed_program (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_concrete_code_ready (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) ) ” 
  &&  “ (0 <= (cm_rep_globals_size ((cm_program_globals (p))))) ” 
  &&  “ (0 <= (cm_rep_strings_size ((cm_program_strings (p))))) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) )) ” 
  &&  “ (0 <= code_capacity) ” 
  &&  “ (code_capacity <= INT_MAX) ” 
  &&  “ (0 <= data_capacity) ” 
  &&  “ (data_capacity <= INT_MAX) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> code_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> data_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> (-1))
  **  (UCharArray.seg data_ptr 0 0 (@nil Z) )
  **  (UCharArray.undef_seg data_ptr 0 data_capacity )
  **  (cm_resolved_emitter_rep (cm_source_function_policy (sp)) p ( &( "emitter" ) ) output_pre code_capacity (cm_model_code ((cm_source_function_policy (sp))) (p)) )
) \/
(
forall (output_pre: Z) (program_pre: Z) (data_capacity: Z) (code_capacity: Z) (p: cm_program) (sp: cm_source_lookup_policy) (functions_ptr_2: Z) (data_ptr_2: Z) (code_length: Z) (data_length: Z) (PreH1 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH2 : (cm_typed_program (cm_source_function_policy (sp)) p )) (PreH3 : (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) )) (PreH4 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH5 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH6 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH7 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH8 : (program_pre <> 0)) (PreH9 : (output_pre <> 0)) (PreH10 : (data_ptr_2 <> 0)) (PreH11 : (code_length = (cm_model_code_length ((cm_source_function_policy (sp))) (p)))) (PreH12 : (data_length = (cm_model_data_length (p)))) (PreH13 : (0 <= code_length)) (PreH14 : (code_length <= code_capacity)) (PreH15 : (0 <= data_length)) (PreH16 : (data_length <= data_capacity)) (PreH17 : (cm_semantic_wf_program (cm_source_function_policy (sp)) p )) (PreH18 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH19 : (cm_typed_program (cm_source_function_policy (sp)) p )) (PreH20 : (cm_concrete_code_ready (cm_source_function_policy (sp)) p )) (PreH21 : (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) )) (PreH22 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH23 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH24 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH25 : (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) )) (PreH26 : (0 <= (cm_rep_globals_size ((cm_program_globals (p)))))) (PreH27 : (0 <= (cm_rep_strings_size ((cm_program_strings (p)))))) (PreH28 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH29 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH30 : (0 <= code_capacity)) (PreH31 : (code_capacity <= INT_MAX)) (PreH32 : (0 <= data_capacity)) (PreH33 : (data_capacity <= INT_MAX)) ,
  (cm_program_context_rep program_pre p functions_ptr_2 )
  **  (cm_function_list_rep functions_ptr_2 (cm_program_functions (p)) )
  **  (cm_resolved_emitter_plan_rep (cm_source_function_policy (sp)) p ( &( "emitter" ) ) output_pre code_capacity (app ((@nil tvm_inst)) ((cm_model_code ((cm_source_function_policy (sp))) (p)))) (@nil tvm_inst) )
|--
  EX (functions_ptr: Z) ,
  “ (program_pre <> 0) ” 
  &&  “ (output_pre <> 0) ” 
  &&  “ (data_ptr_2 <> 0) ” 
  &&  “ (code_length = (cm_model_code_length ((cm_source_function_policy (sp))) (p))) ” 
  &&  “ (data_length = (cm_model_data_length (p))) ” 
  &&  “ (0 <= code_length) ” 
  &&  “ (code_length <= code_capacity) ” 
  &&  “ (0 <= data_length) ” 
  &&  “ (data_length <= data_capacity) ” 
  &&  “ (cm_semantic_wf_program (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p ) ” 
  &&  “ (cm_typed_program (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_concrete_code_ready (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) ) ” 
  &&  “ (0 <= (cm_rep_globals_size ((cm_program_globals (p))))) ” 
  &&  “ (0 <= (cm_rep_strings_size ((cm_program_strings (p))))) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) )) ” 
  &&  “ (0 <= code_capacity) ” 
  &&  “ (code_capacity <= INT_MAX) ” 
  &&  “ (0 <= data_capacity) ” 
  &&  “ (data_capacity <= INT_MAX) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_resolved_emitter_rep (cm_source_function_policy (sp)) p ( &( "emitter" ) ) output_pre code_capacity (cm_model_code ((cm_source_function_policy (sp))) (p)) )
).

Definition cmc_compile_entail_wit_5 := 
(
forall (output_pre: Z) (program_pre: Z) (data_capacity: Z) (code_capacity: Z) (p: cm_program) (sp: cm_source_lookup_policy) (functions_ptr_2: Z) (data_ptr_2: Z) (code_length: Z) (data_length: Z) (PreH1 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH2 : (cm_concrete_code_ready (cm_source_function_policy (sp)) p )) (PreH3 : (program_pre <> 0)) (PreH4 : (output_pre <> 0)) (PreH5 : (data_ptr_2 <> 0)) (PreH6 : (code_length = (cm_model_code_length ((cm_source_function_policy (sp))) (p)))) (PreH7 : (data_length = (cm_model_data_length (p)))) (PreH8 : (0 <= code_length)) (PreH9 : (code_length <= code_capacity)) (PreH10 : (0 <= data_length)) (PreH11 : (data_length <= data_capacity)) (PreH12 : (cm_semantic_wf_program (cm_source_function_policy (sp)) p )) (PreH13 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH14 : (cm_typed_program (cm_source_function_policy (sp)) p )) (PreH15 : (cm_concrete_code_ready (cm_source_function_policy (sp)) p )) (PreH16 : (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) )) (PreH17 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH18 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH19 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH20 : (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) )) (PreH21 : (0 <= (cm_rep_globals_size ((cm_program_globals (p)))))) (PreH22 : (0 <= (cm_rep_strings_size ((cm_program_strings (p)))))) (PreH23 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH24 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH25 : (0 <= code_capacity)) (PreH26 : (code_capacity <= INT_MAX)) (PreH27 : (0 <= data_capacity)) (PreH28 : (data_capacity <= INT_MAX)) ,
  (cm_program_context_rep program_pre p functions_ptr_2 )
  **  (cm_function_list_rep functions_ptr_2 (cm_program_functions (p)) )
  **  (cm_emitter_rep ( &( "emitter" ) ) output_pre code_capacity (cm_rep_ops ((cm_model_code ((cm_source_function_policy (sp))) (p)))) (cm_rep_imms ((cm_model_code ((cm_source_function_policy (sp))) (p)))) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr_2)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> code_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> data_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> (-1))
  **  (UCharArray.seg data_ptr_2 0 0 (@nil Z) )
  **  (UCharArray.undef_seg data_ptr_2 0 data_capacity )
|--
  EX (functions_ptr: Z)  (strings_ptr: Z)  (globals_ptr: Z)  (structs_ptr: Z)  (data_ptr: Z) ,
  “ (program_pre <> 0) ” 
  &&  “ (output_pre <> 0) ” 
  &&  “ (data_ptr <> 0) ” 
  &&  “ (code_length = (cm_model_code_length ((cm_source_function_policy (sp))) (p))) ” 
  &&  “ (data_length = (cm_model_data_length (p))) ” 
  &&  “ (0 <= code_length) ” 
  &&  “ (code_length <= code_capacity) ” 
  &&  “ (0 <= data_length) ” 
  &&  “ (data_length <= data_capacity) ” 
  &&  “ (cm_semantic_wf_program (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p ) ” 
  &&  “ (cm_typed_program (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_concrete_code_ready (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) ) ” 
  &&  “ (0 <= (cm_rep_globals_size ((cm_program_globals (p))))) ” 
  &&  “ (0 <= (cm_rep_strings_size ((cm_program_strings (p))))) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) )) ” 
  &&  “ (0 <= code_capacity) ” 
  &&  “ (code_capacity <= INT_MAX) ” 
  &&  “ (0 <= data_capacity) ” 
  &&  “ (data_capacity <= INT_MAX) ”
  &&  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> structs_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> globals_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> strings_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep structs_ptr (cm_program_structs (p)) )
  **  (cm_global_list_rep globals_ptr (cm_program_globals (p)) )
  **  (cm_string_list_rep strings_ptr (cm_program_strings (p)) )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> code_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> data_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> (-1))
  **  (UCharArray.seg data_ptr 0 0 (@nil Z) )
  **  (UCharArray.undef_seg data_ptr 0 data_capacity )
  **  (cm_emitter_rep ( &( "emitter" ) ) output_pre code_capacity (cm_rep_ops ((cm_model_code ((cm_source_function_policy (sp))) (p)))) (cm_rep_imms ((cm_model_code ((cm_source_function_policy (sp))) (p)))) )
) \/
(
forall (output_pre: Z) (program_pre: Z) (data_capacity: Z) (code_capacity: Z) (p: cm_program) (sp: cm_source_lookup_policy) (functions_ptr_2: Z) (data_ptr_2: Z) (code_length: Z) (data_length: Z) (PreH1 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH2 : (cm_concrete_code_ready (cm_source_function_policy (sp)) p )) (PreH3 : (program_pre <> 0)) (PreH4 : (output_pre <> 0)) (PreH5 : (data_ptr_2 <> 0)) (PreH6 : (code_length = (cm_model_code_length ((cm_source_function_policy (sp))) (p)))) (PreH7 : (data_length = (cm_model_data_length (p)))) (PreH8 : (0 <= code_length)) (PreH9 : (code_length <= code_capacity)) (PreH10 : (0 <= data_length)) (PreH11 : (data_length <= data_capacity)) (PreH12 : (cm_semantic_wf_program (cm_source_function_policy (sp)) p )) (PreH13 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH14 : (cm_typed_program (cm_source_function_policy (sp)) p )) (PreH15 : (cm_concrete_code_ready (cm_source_function_policy (sp)) p )) (PreH16 : (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) )) (PreH17 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH18 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH19 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH20 : (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) )) (PreH21 : (0 <= (cm_rep_globals_size ((cm_program_globals (p)))))) (PreH22 : (0 <= (cm_rep_strings_size ((cm_program_strings (p)))))) (PreH23 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH24 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH25 : (0 <= code_capacity)) (PreH26 : (code_capacity <= INT_MAX)) (PreH27 : (0 <= data_capacity)) (PreH28 : (data_capacity <= INT_MAX)) ,
  (cm_program_context_rep program_pre p functions_ptr_2 )
  **  (cm_function_list_rep functions_ptr_2 (cm_program_functions (p)) )
  **  (cm_emitter_rep ( &( "emitter" ) ) output_pre code_capacity (cm_rep_ops ((cm_model_code ((cm_source_function_policy (sp))) (p)))) (cm_rep_imms ((cm_model_code ((cm_source_function_policy (sp))) (p)))) )
|--
  EX (functions_ptr: Z)  (strings_ptr: Z)  (globals_ptr: Z)  (structs_ptr: Z) ,
  “ (program_pre <> 0) ” 
  &&  “ (output_pre <> 0) ” 
  &&  “ (data_ptr_2 <> 0) ” 
  &&  “ (code_length = (cm_model_code_length ((cm_source_function_policy (sp))) (p))) ” 
  &&  “ (data_length = (cm_model_data_length (p))) ” 
  &&  “ (0 <= code_length) ” 
  &&  “ (code_length <= code_capacity) ” 
  &&  “ (0 <= data_length) ” 
  &&  “ (data_length <= data_capacity) ” 
  &&  “ (cm_semantic_wf_program (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p ) ” 
  &&  “ (cm_typed_program (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_concrete_code_ready (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) ) ” 
  &&  “ (0 <= (cm_rep_globals_size ((cm_program_globals (p))))) ” 
  &&  “ (0 <= (cm_rep_strings_size ((cm_program_strings (p))))) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) )) ” 
  &&  “ (0 <= code_capacity) ” 
  &&  “ (code_capacity <= INT_MAX) ” 
  &&  “ (0 <= data_capacity) ” 
  &&  “ (data_capacity <= INT_MAX) ”
  &&  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> structs_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> globals_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> strings_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep structs_ptr (cm_program_structs (p)) )
  **  (cm_global_list_rep globals_ptr (cm_program_globals (p)) )
  **  (cm_string_list_rep strings_ptr (cm_program_strings (p)) )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_emitter_rep ( &( "emitter" ) ) output_pre code_capacity (cm_rep_ops ((cm_model_code ((cm_source_function_policy (sp))) (p)))) (cm_rep_imms ((cm_model_code ((cm_source_function_policy (sp))) (p)))) )
).

Definition cmc_compile_entail_wit_6 := 
(
forall (output_pre: Z) (program_pre: Z) (data_capacity: Z) (code_capacity: Z) (p: cm_program) (sp: cm_source_lookup_policy) (functions_ptr_2: Z) (structs_ptr: Z) (globals_ptr: Z) (strings_ptr: Z) (data_ptr: Z) (code_length: Z) (data_length: Z) (retval: Z) (PreH1 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH2 : (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) )) (PreH3 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH4 : (0 <= (cm_rep_globals_size ((cm_program_globals (p)))))) (PreH5 : (0 <= (cm_rep_strings_size ((cm_program_strings (p)))))) (PreH6 : (((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= data_capacity)) (PreH7 : (data_capacity <= INT_MAX)) (PreH8 : (retval = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH9 : (program_pre <> 0)) (PreH10 : (output_pre <> 0)) (PreH11 : (data_ptr <> 0)) (PreH12 : (code_length = (cm_model_code_length ((cm_source_function_policy (sp))) (p)))) (PreH13 : (data_length = (cm_model_data_length (p)))) (PreH14 : (0 <= code_length)) (PreH15 : (code_length <= code_capacity)) (PreH16 : (0 <= data_length)) (PreH17 : (data_length <= data_capacity)) (PreH18 : (cm_semantic_wf_program (cm_source_function_policy (sp)) p )) (PreH19 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH20 : (cm_typed_program (cm_source_function_policy (sp)) p )) (PreH21 : (cm_concrete_code_ready (cm_source_function_policy (sp)) p )) (PreH22 : (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) )) (PreH23 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH24 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH25 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH26 : (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) )) (PreH27 : (0 <= (cm_rep_globals_size ((cm_program_globals (p)))))) (PreH28 : (0 <= (cm_rep_strings_size ((cm_program_strings (p)))))) (PreH29 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH30 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH31 : (0 <= code_capacity)) (PreH32 : (code_capacity <= INT_MAX)) (PreH33 : (0 <= data_capacity)) (PreH34 : (data_capacity <= INT_MAX)) ,
  (cm_global_list_rep globals_ptr (cm_program_globals (p)) )
  **  (cm_string_list_rep strings_ptr (cm_program_strings (p)) )
  **  (UCharArray.seg data_ptr 0 ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ) (app ((app ((zeros (8))) ((cm_globals_bytes ((cm_program_structs (p))) ((cm_program_globals (p))))))) ((cm_strings_bytes ((cm_program_strings (p)))))) )
  **  (UCharArray.undef_seg data_ptr ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ) data_capacity )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> structs_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> globals_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> strings_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr_2)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep structs_ptr (cm_program_structs (p)) )
  **  (cm_function_list_rep functions_ptr_2 (cm_program_functions (p)) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> code_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> data_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> (-1))
  **  (cm_emitter_rep ( &( "emitter" ) ) output_pre code_capacity (cm_rep_ops ((cm_model_code ((cm_source_function_policy (sp))) (p)))) (cm_rep_imms ((cm_model_code ((cm_source_function_policy (sp))) (p)))) )
|--
  EX (functions_ptr: Z)  (imms_ptr: Z)  (ops_ptr: Z) ,
  “ (program_pre <> 0) ” 
  &&  “ (output_pre <> 0) ” 
  &&  “ (ops_ptr <> 0) ” 
  &&  “ (imms_ptr <> 0) ” 
  &&  “ (data_ptr <> 0) ” 
  &&  “ (code_length = (cm_model_code_length ((cm_source_function_policy (sp))) (p))) ” 
  &&  “ (data_length = (cm_model_data_length (p))) ” 
  &&  “ (0 <= code_length) ” 
  &&  “ (code_length <= code_capacity) ” 
  &&  “ (0 <= data_length) ” 
  &&  “ (data_length <= data_capacity) ” 
  &&  “ (cm_semantic_wf_program (cm_source_function_policy (sp)) p ) ” 
  &&  “ (retval = data_length) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> code_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> code_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> data_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> (-1))
  **  ((&(( &( "emitter" ) )->ₛ "output")) # Ptr  |-> output_pre)
  **  ((&(( &( "emitter" ) )->ₛ "pc")) # Int  |-> code_length)
  **  (IntArray.seg ops_ptr 0 code_length (cm_rep_ops ((cm_model_code ((cm_source_function_policy (sp))) (p)))) )
  **  (IntArray.undef_seg ops_ptr code_length code_capacity )
  **  (Int64Array.seg imms_ptr 0 code_length (cm_rep_imms ((cm_model_code ((cm_source_function_policy (sp))) (p)))) )
  **  (Int64Array.undef_seg imms_ptr code_length code_capacity )
  **  (UCharArray.seg data_ptr 0 data_length (cm_model_data_bytes (p)) )
  **  (UCharArray.undef_seg data_ptr data_length data_capacity )
) \/
(
forall (output_pre: Z) (program_pre: Z) (data_capacity: Z) (code_capacity: Z) (p: cm_program) (sp: cm_source_lookup_policy) (functions_ptr_2: Z) (structs_ptr: Z) (globals_ptr: Z) (strings_ptr: Z) (data_ptr: Z) (code_length: Z) (data_length: Z) (retval: Z) (PreH1 : ((cm_program_main (p)) <= INT_MAX)) (PreH2 : ((cm_program_main (p)) >= INT_MIN)) (PreH3 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH4 : (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) )) (PreH5 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH6 : (0 <= (cm_rep_globals_size ((cm_program_globals (p)))))) (PreH7 : (0 <= (cm_rep_strings_size ((cm_program_strings (p)))))) (PreH8 : (((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= data_capacity)) (PreH9 : (data_capacity <= INT_MAX)) (PreH10 : (retval = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH11 : (program_pre <> 0)) (PreH12 : (output_pre <> 0)) (PreH13 : (data_ptr <> 0)) (PreH14 : (code_length = (cm_model_code_length ((cm_source_function_policy (sp))) (p)))) (PreH15 : (data_length = (cm_model_data_length (p)))) (PreH16 : (0 <= code_length)) (PreH17 : (code_length <= code_capacity)) (PreH18 : (0 <= data_length)) (PreH19 : (data_length <= data_capacity)) (PreH20 : (cm_semantic_wf_program (cm_source_function_policy (sp)) p )) (PreH21 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH22 : (cm_typed_program (cm_source_function_policy (sp)) p )) (PreH23 : (cm_concrete_code_ready (cm_source_function_policy (sp)) p )) (PreH24 : (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) )) (PreH25 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH26 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH27 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH28 : (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) )) (PreH29 : (0 <= (cm_rep_globals_size ((cm_program_globals (p)))))) (PreH30 : (0 <= (cm_rep_strings_size ((cm_program_strings (p)))))) (PreH31 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH32 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH33 : (0 <= code_capacity)) (PreH34 : (code_capacity <= INT_MAX)) (PreH35 : (0 <= data_capacity)) (PreH36 : (data_capacity <= INT_MAX)) ,
  (cm_global_list_rep globals_ptr (cm_program_globals (p)) )
  **  (cm_string_list_rep strings_ptr (cm_program_strings (p)) )
  **  (UCharArray.seg data_ptr 0 ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ) (app ((app ((zeros (8))) ((cm_globals_bytes ((cm_program_structs (p))) ((cm_program_globals (p))))))) ((cm_strings_bytes ((cm_program_strings (p)))))) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> structs_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> globals_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> strings_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr_2)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep structs_ptr (cm_program_structs (p)) )
  **  (cm_function_list_rep functions_ptr_2 (cm_program_functions (p)) )
  **  (cm_emitter_rep ( &( "emitter" ) ) output_pre code_capacity (cm_rep_ops ((cm_model_code ((cm_source_function_policy (sp))) (p)))) (cm_rep_imms ((cm_model_code ((cm_source_function_policy (sp))) (p)))) )
|--
  EX (functions_ptr: Z)  (imms_ptr: Z)  (ops_ptr: Z) ,
  “ (program_pre <> 0) ” 
  &&  “ (output_pre <> 0) ” 
  &&  “ (ops_ptr <> 0) ” 
  &&  “ (imms_ptr <> 0) ” 
  &&  “ (data_ptr <> 0) ” 
  &&  “ (code_length = (cm_model_code_length ((cm_source_function_policy (sp))) (p))) ” 
  &&  “ (data_length = (cm_model_data_length (p))) ” 
  &&  “ (0 <= code_length) ” 
  &&  “ (code_length <= code_capacity) ” 
  &&  “ (0 <= data_length) ” 
  &&  “ (data_length <= data_capacity) ” 
  &&  “ (cm_semantic_wf_program (cm_source_function_policy (sp)) p ) ” 
  &&  “ (retval = data_length) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> code_capacity)
  **  ((&(( &( "emitter" ) )->ₛ "output")) # Ptr  |-> output_pre)
  **  ((&(( &( "emitter" ) )->ₛ "pc")) # Int  |-> code_length)
  **  (IntArray.seg ops_ptr 0 code_length (cm_rep_ops ((cm_model_code ((cm_source_function_policy (sp))) (p)))) )
  **  (IntArray.undef_seg ops_ptr code_length code_capacity )
  **  (Int64Array.seg imms_ptr 0 code_length (cm_rep_imms ((cm_model_code ((cm_source_function_policy (sp))) (p)))) )
  **  (Int64Array.undef_seg imms_ptr code_length code_capacity )
  **  (UCharArray.seg data_ptr 0 data_length (cm_model_data_bytes (p)) )
).

Definition cmc_compile_return_wit_1 := 
(
forall (output_pre: Z) (program_pre: Z) (data_capacity: Z) (code_capacity: Z) (p: cm_program) (sp: cm_source_lookup_policy) (functions_ptr: Z) (ops_ptr: Z) (imms_ptr: Z) (data_ptr: Z) (code_length: Z) (data_length: Z) (emitted_data: Z) (PreH1 : (program_pre <> 0)) (PreH2 : (output_pre <> 0)) (PreH3 : (ops_ptr <> 0)) (PreH4 : (imms_ptr <> 0)) (PreH5 : (data_ptr <> 0)) (PreH6 : (code_length = (cm_model_code_length ((cm_source_function_policy (sp))) (p)))) (PreH7 : (data_length = (cm_model_data_length (p)))) (PreH8 : (0 <= code_length)) (PreH9 : (code_length <= code_capacity)) (PreH10 : (0 <= data_length)) (PreH11 : (data_length <= data_capacity)) (PreH12 : (cm_semantic_wf_program (cm_source_function_policy (sp)) p )) (PreH13 : (emitted_data = data_length)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> code_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> code_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> data_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> 0)
  **  (IntArray.seg ops_ptr 0 code_length (cm_rep_ops ((cm_model_code ((cm_source_function_policy (sp))) (p)))) )
  **  (IntArray.undef_seg ops_ptr code_length code_capacity )
  **  (Int64Array.seg imms_ptr 0 code_length (cm_rep_imms ((cm_model_code ((cm_source_function_policy (sp))) (p)))) )
  **  (Int64Array.undef_seg imms_ptr code_length code_capacity )
  **  (UCharArray.seg data_ptr 0 data_length (cm_model_data_bytes (p)) )
  **  (UCharArray.undef_seg data_ptr data_length data_capacity )
|--
  “ (0 = 0) ”
  &&  (cm_program_rep (cm_source_function_policy (sp)) program_pre p )
  **  (cm_output_ok sp output_pre code_capacity data_capacity p )
) \/
(
forall (output_pre: Z) (program_pre: Z) (data_capacity: Z) (code_capacity: Z) (p: cm_program) (sp: cm_source_lookup_policy) (functions_ptr: Z) (ops_ptr: Z) (imms_ptr: Z) (data_ptr: Z) (code_length: Z) (data_length: Z) (emitted_data: Z) (PreH1 : (0 <= INT_MAX)) (PreH2 : (data_length <= INT_MAX)) (PreH3 : (code_length <= INT_MAX)) (PreH4 : (data_capacity <= INT_MAX)) (PreH5 : (code_capacity <= INT_MAX)) (PreH6 : (0 >= INT_MIN)) (PreH7 : (data_length >= INT_MIN)) (PreH8 : (code_length >= INT_MIN)) (PreH9 : (data_capacity >= INT_MIN)) (PreH10 : (code_capacity >= INT_MIN)) (PreH11 : (program_pre <> 0)) (PreH12 : (output_pre <> 0)) (PreH13 : (ops_ptr <> 0)) (PreH14 : (imms_ptr <> 0)) (PreH15 : (data_ptr <> 0)) (PreH16 : (code_length = (cm_model_code_length ((cm_source_function_policy (sp))) (p)))) (PreH17 : (data_length = (cm_model_data_length (p)))) (PreH18 : (0 <= code_length)) (PreH19 : (code_length <= code_capacity)) (PreH20 : (0 <= data_length)) (PreH21 : (data_length <= data_capacity)) (PreH22 : (cm_semantic_wf_program (cm_source_function_policy (sp)) p )) (PreH23 : (emitted_data = data_length)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> code_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> code_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> data_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> 0)
  **  (IntArray.seg ops_ptr 0 code_length (cm_rep_ops ((cm_model_code ((cm_source_function_policy (sp))) (p)))) )
  **  (IntArray.undef_seg ops_ptr code_length code_capacity )
  **  (Int64Array.seg imms_ptr 0 code_length (cm_rep_imms ((cm_model_code ((cm_source_function_policy (sp))) (p)))) )
  **  (Int64Array.undef_seg imms_ptr code_length code_capacity )
  **  (UCharArray.seg data_ptr 0 data_length (cm_model_data_bytes (p)) )
  **  (UCharArray.undef_seg data_ptr data_length data_capacity )
|--
  (cm_program_rep (cm_source_function_policy (sp)) program_pre p )
  **  (cm_output_ok sp output_pre code_capacity data_capacity p )
).

Definition cmc_compile_return_wit_1_split_goal_spatial := 
forall (output_pre: Z) (program_pre: Z) (data_capacity: Z) (code_capacity: Z) (p: cm_program) (sp: cm_source_lookup_policy) (functions_ptr: Z) (ops_ptr: Z) (imms_ptr: Z) (data_ptr: Z) (code_length: Z) (data_length: Z) (emitted_data: Z) (PreH1 : (0 <= INT_MAX)) (PreH2 : (data_length <= INT_MAX)) (PreH3 : (code_length <= INT_MAX)) (PreH4 : (data_capacity <= INT_MAX)) (PreH5 : (code_capacity <= INT_MAX)) (PreH6 : (0 >= INT_MIN)) (PreH7 : (data_length >= INT_MIN)) (PreH8 : (code_length >= INT_MIN)) (PreH9 : (data_capacity >= INT_MIN)) (PreH10 : (code_capacity >= INT_MIN)) (PreH11 : (program_pre <> 0)) (PreH12 : (output_pre <> 0)) (PreH13 : (ops_ptr <> 0)) (PreH14 : (imms_ptr <> 0)) (PreH15 : (data_ptr <> 0)) (PreH16 : (code_length = (cm_model_code_length ((cm_source_function_policy (sp))) (p)))) (PreH17 : (data_length = (cm_model_data_length (p)))) (PreH18 : (0 <= code_length)) (PreH19 : (code_length <= code_capacity)) (PreH20 : (0 <= data_length)) (PreH21 : (data_length <= data_capacity)) (PreH22 : (cm_semantic_wf_program (cm_source_function_policy (sp)) p )) (PreH23 : (emitted_data = data_length)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> code_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> code_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> data_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> 0)
  **  (IntArray.seg ops_ptr 0 code_length (cm_rep_ops ((cm_model_code ((cm_source_function_policy (sp))) (p)))) )
  **  (IntArray.undef_seg ops_ptr code_length code_capacity )
  **  (Int64Array.seg imms_ptr 0 code_length (cm_rep_imms ((cm_model_code ((cm_source_function_policy (sp))) (p)))) )
  **  (Int64Array.undef_seg imms_ptr code_length code_capacity )
  **  (UCharArray.seg data_ptr 0 data_length (cm_model_data_bytes (p)) )
  **  (UCharArray.undef_seg data_ptr data_length data_capacity )
|--
  (cm_program_rep (cm_source_function_policy (sp)) program_pre p )
  **  (cm_output_ok sp output_pre code_capacity data_capacity p )
.

Definition cmc_compile_return_wit_2 := 
(
forall (output_pre: Z) (program_pre: Z) (data_capacity: Z) (code_capacity: Z) (p: cm_program) (sp: cm_source_lookup_policy) (functions_ptr: Z) (ops_ptr: Z) (imms_ptr: Z) (data_ptr: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 > data_capacity)) (PreH2 : (retval <= code_capacity)) (PreH3 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH4 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH5 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH6 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH7 : (retval_2 = (cm_model_data_length (p)))) (PreH8 : (cm_i32_code_count retval_2 )) (PreH9 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH10 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH11 : (retval = (cm_model_code_length ((cm_source_function_policy (sp))) (p)))) (PreH12 : (cm_i32_code_count retval )) (PreH13 : (program_pre <> 0)) (PreH14 : (output_pre <> 0)) (PreH15 : (cm_semantic_wf_program (cm_source_function_policy (sp)) p )) (PreH16 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH17 : (cm_typed_program (cm_source_function_policy (sp)) p )) (PreH18 : (cm_concrete_code_ready (cm_source_function_policy (sp)) p )) (PreH19 : (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) )) (PreH20 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH21 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH22 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH23 : (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) )) (PreH24 : (0 <= (cm_rep_globals_size ((cm_program_globals (p)))))) (PreH25 : (0 <= (cm_rep_strings_size ((cm_program_strings (p)))))) (PreH26 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH27 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH28 : (0 <= code_capacity)) (PreH29 : (code_capacity <= INT_MAX)) (PreH30 : (0 <= data_capacity)) (PreH31 : (data_capacity <= INT_MAX)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> code_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> retval)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> retval_2)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> (-1))
  **  (cm_undef_int_buffer ops_ptr code_capacity )
  **  (cm_undef_int64_buffer imms_ptr code_capacity )
  **  (cm_undef_uint8_buffer data_ptr data_capacity )
|--
  “ (1 = 1) ”
  &&  (cm_program_rep (cm_source_function_policy (sp)) program_pre p )
  **  (cm_output_capacity (cm_source_function_policy (sp)) output_pre code_capacity data_capacity p )
) \/
(
forall (output_pre: Z) (program_pre: Z) (data_capacity: Z) (code_capacity: Z) (p: cm_program) (sp: cm_source_lookup_policy) (functions_ptr: Z) (ops_ptr: Z) (imms_ptr: Z) (data_ptr: Z) (retval: Z) (retval_2: Z) (PreH1 : ((-1) <= INT_MAX)) (PreH2 : (retval_2 <= INT_MAX)) (PreH3 : (retval <= INT_MAX)) (PreH4 : (data_capacity <= INT_MAX)) (PreH5 : (code_capacity <= INT_MAX)) (PreH6 : ((-1) >= INT_MIN)) (PreH7 : (retval_2 >= INT_MIN)) (PreH8 : (retval >= INT_MIN)) (PreH9 : (data_capacity >= INT_MIN)) (PreH10 : (code_capacity >= INT_MIN)) (PreH11 : (retval_2 > data_capacity)) (PreH12 : (retval <= code_capacity)) (PreH13 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH14 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH15 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH16 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH17 : (retval_2 = (cm_model_data_length (p)))) (PreH18 : (cm_i32_code_count retval_2 )) (PreH19 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH20 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH21 : (retval = (cm_model_code_length ((cm_source_function_policy (sp))) (p)))) (PreH22 : (cm_i32_code_count retval )) (PreH23 : (program_pre <> 0)) (PreH24 : (output_pre <> 0)) (PreH25 : (cm_semantic_wf_program (cm_source_function_policy (sp)) p )) (PreH26 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH27 : (cm_typed_program (cm_source_function_policy (sp)) p )) (PreH28 : (cm_concrete_code_ready (cm_source_function_policy (sp)) p )) (PreH29 : (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) )) (PreH30 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH31 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH32 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH33 : (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) )) (PreH34 : (0 <= (cm_rep_globals_size ((cm_program_globals (p)))))) (PreH35 : (0 <= (cm_rep_strings_size ((cm_program_strings (p)))))) (PreH36 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH37 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH38 : (0 <= code_capacity)) (PreH39 : (code_capacity <= INT_MAX)) (PreH40 : (0 <= data_capacity)) (PreH41 : (data_capacity <= INT_MAX)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> code_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> retval)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> retval_2)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> (-1))
  **  (cm_undef_int_buffer ops_ptr code_capacity )
  **  (cm_undef_int64_buffer imms_ptr code_capacity )
  **  (cm_undef_uint8_buffer data_ptr data_capacity )
|--
  (cm_program_rep (cm_source_function_policy (sp)) program_pre p )
  **  (cm_output_capacity (cm_source_function_policy (sp)) output_pre code_capacity data_capacity p )
).

Definition cmc_compile_return_wit_2_split_goal_spatial := 
forall (output_pre: Z) (program_pre: Z) (data_capacity: Z) (code_capacity: Z) (p: cm_program) (sp: cm_source_lookup_policy) (functions_ptr: Z) (ops_ptr: Z) (imms_ptr: Z) (data_ptr: Z) (retval: Z) (retval_2: Z) (PreH1 : ((-1) <= INT_MAX)) (PreH2 : (retval_2 <= INT_MAX)) (PreH3 : (retval <= INT_MAX)) (PreH4 : (data_capacity <= INT_MAX)) (PreH5 : (code_capacity <= INT_MAX)) (PreH6 : ((-1) >= INT_MIN)) (PreH7 : (retval_2 >= INT_MIN)) (PreH8 : (retval >= INT_MIN)) (PreH9 : (data_capacity >= INT_MIN)) (PreH10 : (code_capacity >= INT_MIN)) (PreH11 : (retval_2 > data_capacity)) (PreH12 : (retval <= code_capacity)) (PreH13 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH14 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH15 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH16 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH17 : (retval_2 = (cm_model_data_length (p)))) (PreH18 : (cm_i32_code_count retval_2 )) (PreH19 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH20 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH21 : (retval = (cm_model_code_length ((cm_source_function_policy (sp))) (p)))) (PreH22 : (cm_i32_code_count retval )) (PreH23 : (program_pre <> 0)) (PreH24 : (output_pre <> 0)) (PreH25 : (cm_semantic_wf_program (cm_source_function_policy (sp)) p )) (PreH26 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH27 : (cm_typed_program (cm_source_function_policy (sp)) p )) (PreH28 : (cm_concrete_code_ready (cm_source_function_policy (sp)) p )) (PreH29 : (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) )) (PreH30 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH31 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH32 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH33 : (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) )) (PreH34 : (0 <= (cm_rep_globals_size ((cm_program_globals (p)))))) (PreH35 : (0 <= (cm_rep_strings_size ((cm_program_strings (p)))))) (PreH36 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH37 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH38 : (0 <= code_capacity)) (PreH39 : (code_capacity <= INT_MAX)) (PreH40 : (0 <= data_capacity)) (PreH41 : (data_capacity <= INT_MAX)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> code_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> retval)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> retval_2)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> (-1))
  **  (cm_undef_int_buffer ops_ptr code_capacity )
  **  (cm_undef_int64_buffer imms_ptr code_capacity )
  **  (cm_undef_uint8_buffer data_ptr data_capacity )
|--
  (cm_program_rep (cm_source_function_policy (sp)) program_pre p )
  **  (cm_output_capacity (cm_source_function_policy (sp)) output_pre code_capacity data_capacity p )
.

Definition cmc_compile_return_wit_3 := 
(
forall (output_pre: Z) (program_pre: Z) (data_capacity: Z) (code_capacity: Z) (p: cm_program) (sp: cm_source_lookup_policy) (functions_ptr: Z) (ops_ptr: Z) (imms_ptr: Z) (data_ptr: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval > code_capacity)) (PreH2 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH3 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH4 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH5 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH6 : (retval_2 = (cm_model_data_length (p)))) (PreH7 : (cm_i32_code_count retval_2 )) (PreH8 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH9 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH10 : (retval = (cm_model_code_length ((cm_source_function_policy (sp))) (p)))) (PreH11 : (cm_i32_code_count retval )) (PreH12 : (program_pre <> 0)) (PreH13 : (output_pre <> 0)) (PreH14 : (cm_semantic_wf_program (cm_source_function_policy (sp)) p )) (PreH15 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH16 : (cm_typed_program (cm_source_function_policy (sp)) p )) (PreH17 : (cm_concrete_code_ready (cm_source_function_policy (sp)) p )) (PreH18 : (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) )) (PreH19 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH20 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH21 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH22 : (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) )) (PreH23 : (0 <= (cm_rep_globals_size ((cm_program_globals (p)))))) (PreH24 : (0 <= (cm_rep_strings_size ((cm_program_strings (p)))))) (PreH25 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH26 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH27 : (0 <= code_capacity)) (PreH28 : (code_capacity <= INT_MAX)) (PreH29 : (0 <= data_capacity)) (PreH30 : (data_capacity <= INT_MAX)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> code_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> retval)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> retval_2)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> (-1))
  **  (cm_undef_int_buffer ops_ptr code_capacity )
  **  (cm_undef_int64_buffer imms_ptr code_capacity )
  **  (cm_undef_uint8_buffer data_ptr data_capacity )
|--
  “ (1 = 1) ”
  &&  (cm_program_rep (cm_source_function_policy (sp)) program_pre p )
  **  (cm_output_capacity (cm_source_function_policy (sp)) output_pre code_capacity data_capacity p )
) \/
(
forall (output_pre: Z) (program_pre: Z) (data_capacity: Z) (code_capacity: Z) (p: cm_program) (sp: cm_source_lookup_policy) (functions_ptr: Z) (ops_ptr: Z) (imms_ptr: Z) (data_ptr: Z) (retval: Z) (retval_2: Z) (PreH1 : ((-1) <= INT_MAX)) (PreH2 : (retval_2 <= INT_MAX)) (PreH3 : (retval <= INT_MAX)) (PreH4 : (data_capacity <= INT_MAX)) (PreH5 : (code_capacity <= INT_MAX)) (PreH6 : ((-1) >= INT_MIN)) (PreH7 : (retval_2 >= INT_MIN)) (PreH8 : (retval >= INT_MIN)) (PreH9 : (data_capacity >= INT_MIN)) (PreH10 : (code_capacity >= INT_MIN)) (PreH11 : (retval > code_capacity)) (PreH12 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH13 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH14 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH15 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH16 : (retval_2 = (cm_model_data_length (p)))) (PreH17 : (cm_i32_code_count retval_2 )) (PreH18 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH19 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH20 : (retval = (cm_model_code_length ((cm_source_function_policy (sp))) (p)))) (PreH21 : (cm_i32_code_count retval )) (PreH22 : (program_pre <> 0)) (PreH23 : (output_pre <> 0)) (PreH24 : (cm_semantic_wf_program (cm_source_function_policy (sp)) p )) (PreH25 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH26 : (cm_typed_program (cm_source_function_policy (sp)) p )) (PreH27 : (cm_concrete_code_ready (cm_source_function_policy (sp)) p )) (PreH28 : (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) )) (PreH29 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH30 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH31 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH32 : (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) )) (PreH33 : (0 <= (cm_rep_globals_size ((cm_program_globals (p)))))) (PreH34 : (0 <= (cm_rep_strings_size ((cm_program_strings (p)))))) (PreH35 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH36 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH37 : (0 <= code_capacity)) (PreH38 : (code_capacity <= INT_MAX)) (PreH39 : (0 <= data_capacity)) (PreH40 : (data_capacity <= INT_MAX)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> code_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> retval)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> retval_2)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> (-1))
  **  (cm_undef_int_buffer ops_ptr code_capacity )
  **  (cm_undef_int64_buffer imms_ptr code_capacity )
  **  (cm_undef_uint8_buffer data_ptr data_capacity )
|--
  (cm_program_rep (cm_source_function_policy (sp)) program_pre p )
  **  (cm_output_capacity (cm_source_function_policy (sp)) output_pre code_capacity data_capacity p )
).

Definition cmc_compile_return_wit_3_split_goal_spatial := 
forall (output_pre: Z) (program_pre: Z) (data_capacity: Z) (code_capacity: Z) (p: cm_program) (sp: cm_source_lookup_policy) (functions_ptr: Z) (ops_ptr: Z) (imms_ptr: Z) (data_ptr: Z) (retval: Z) (retval_2: Z) (PreH1 : ((-1) <= INT_MAX)) (PreH2 : (retval_2 <= INT_MAX)) (PreH3 : (retval <= INT_MAX)) (PreH4 : (data_capacity <= INT_MAX)) (PreH5 : (code_capacity <= INT_MAX)) (PreH6 : ((-1) >= INT_MIN)) (PreH7 : (retval_2 >= INT_MIN)) (PreH8 : (retval >= INT_MIN)) (PreH9 : (data_capacity >= INT_MIN)) (PreH10 : (code_capacity >= INT_MIN)) (PreH11 : (retval > code_capacity)) (PreH12 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH13 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH14 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH15 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH16 : (retval_2 = (cm_model_data_length (p)))) (PreH17 : (cm_i32_code_count retval_2 )) (PreH18 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH19 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH20 : (retval = (cm_model_code_length ((cm_source_function_policy (sp))) (p)))) (PreH21 : (cm_i32_code_count retval )) (PreH22 : (program_pre <> 0)) (PreH23 : (output_pre <> 0)) (PreH24 : (cm_semantic_wf_program (cm_source_function_policy (sp)) p )) (PreH25 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH26 : (cm_typed_program (cm_source_function_policy (sp)) p )) (PreH27 : (cm_concrete_code_ready (cm_source_function_policy (sp)) p )) (PreH28 : (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) )) (PreH29 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH30 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH31 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH32 : (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) )) (PreH33 : (0 <= (cm_rep_globals_size ((cm_program_globals (p)))))) (PreH34 : (0 <= (cm_rep_strings_size ((cm_program_strings (p)))))) (PreH35 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH36 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH37 : (0 <= code_capacity)) (PreH38 : (code_capacity <= INT_MAX)) (PreH39 : (0 <= data_capacity)) (PreH40 : (data_capacity <= INT_MAX)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> code_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> retval)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> retval_2)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> (-1))
  **  (cm_undef_int_buffer ops_ptr code_capacity )
  **  (cm_undef_int64_buffer imms_ptr code_capacity )
  **  (cm_undef_uint8_buffer data_ptr data_capacity )
|--
  (cm_program_rep (cm_source_function_policy (sp)) program_pre p )
  **  (cm_output_capacity (cm_source_function_policy (sp)) output_pre code_capacity data_capacity p )
.

Definition cmc_compile_partial_solve_wit_1_pure := 
forall (output_pre: Z) (program_pre: Z) (data_capacity: Z) (code_capacity: Z) (p: cm_program) (sp: cm_source_lookup_policy) (functions_ptr: Z) (ops_ptr: Z) (imms_ptr: Z) (data_ptr: Z) (old_code: Z) (old_data: Z) (old_entry: Z) (PreH1 : (program_pre <> 0)) (PreH2 : (output_pre <> 0)) (PreH3 : (cm_semantic_wf_program (cm_source_function_policy (sp)) p )) (PreH4 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH5 : (cm_typed_program (cm_source_function_policy (sp)) p )) (PreH6 : (cm_concrete_code_ready (cm_source_function_policy (sp)) p )) (PreH7 : (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) )) (PreH8 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH9 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH10 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH11 : (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) )) (PreH12 : (0 <= (cm_rep_globals_size ((cm_program_globals (p)))))) (PreH13 : (0 <= (cm_rep_strings_size ((cm_program_strings (p)))))) (PreH14 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH15 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH16 : (0 <= code_capacity)) (PreH17 : (code_capacity <= INT_MAX)) (PreH18 : (0 <= data_capacity)) (PreH19 : (data_capacity <= INT_MAX)) ,
  ((( &( "code_length" ) )) # Int  |->_)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> code_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> old_code)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> old_data)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> old_entry)
  **  (cm_undef_int_buffer ops_ptr code_capacity )
  **  (cm_undef_int64_buffer imms_ptr code_capacity )
  **  (cm_undef_uint8_buffer data_ptr data_capacity )
|--
  “ (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ”
.

Definition cmc_compile_partial_solve_wit_1_aux := 
forall (output_pre: Z) (program_pre: Z) (data_capacity: Z) (code_capacity: Z) (p: cm_program) (sp: cm_source_lookup_policy) (functions_ptr: Z) (ops_ptr: Z) (imms_ptr: Z) (data_ptr: Z) (old_code: Z) (old_data: Z) (old_entry: Z) (PreH1 : (program_pre <> 0)) (PreH2 : (output_pre <> 0)) (PreH3 : (cm_semantic_wf_program (cm_source_function_policy (sp)) p )) (PreH4 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH5 : (cm_typed_program (cm_source_function_policy (sp)) p )) (PreH6 : (cm_concrete_code_ready (cm_source_function_policy (sp)) p )) (PreH7 : (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) )) (PreH8 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH9 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH10 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH11 : (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) )) (PreH12 : (0 <= (cm_rep_globals_size ((cm_program_globals (p)))))) (PreH13 : (0 <= (cm_rep_strings_size ((cm_program_strings (p)))))) (PreH14 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH15 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH16 : (0 <= code_capacity)) (PreH17 : (code_capacity <= INT_MAX)) (PreH18 : (0 <= data_capacity)) (PreH19 : (data_capacity <= INT_MAX)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> code_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> old_code)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> old_data)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> old_entry)
  **  (cm_undef_int_buffer ops_ptr code_capacity )
  **  (cm_undef_int64_buffer imms_ptr code_capacity )
  **  (cm_undef_uint8_buffer data_ptr data_capacity )
|--
  “ (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (program_pre <> 0) ” 
  &&  “ (output_pre <> 0) ” 
  &&  “ (cm_semantic_wf_program (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p ) ” 
  &&  “ (cm_typed_program (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_concrete_code_ready (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) ) ” 
  &&  “ (0 <= (cm_rep_globals_size ((cm_program_globals (p))))) ” 
  &&  “ (0 <= (cm_rep_strings_size ((cm_program_strings (p))))) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) )) ” 
  &&  “ (0 <= code_capacity) ” 
  &&  “ (code_capacity <= INT_MAX) ” 
  &&  “ (0 <= data_capacity) ” 
  &&  “ (data_capacity <= INT_MAX) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> code_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> old_code)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> old_data)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> old_entry)
  **  (cm_undef_int_buffer ops_ptr code_capacity )
  **  (cm_undef_int64_buffer imms_ptr code_capacity )
  **  (cm_undef_uint8_buffer data_ptr data_capacity )
.

Definition cmc_compile_partial_solve_wit_1 := cmc_compile_partial_solve_wit_1_pure -> cmc_compile_partial_solve_wit_1_aux.

Definition cmc_compile_partial_solve_wit_2_pure := 
forall (output_pre: Z) (program_pre: Z) (data_capacity: Z) (code_capacity: Z) (p: cm_program) (sp: cm_source_lookup_policy) (functions_ptr: Z) (ops_ptr: Z) (imms_ptr: Z) (data_ptr: Z) (old_code: Z) (old_data: Z) (old_entry: Z) (retval: Z) (PreH1 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH2 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH3 : (retval = (cm_model_code_length ((cm_source_function_policy (sp))) (p)))) (PreH4 : (cm_i32_code_count retval )) (PreH5 : (program_pre <> 0)) (PreH6 : (output_pre <> 0)) (PreH7 : (cm_semantic_wf_program (cm_source_function_policy (sp)) p )) (PreH8 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH9 : (cm_typed_program (cm_source_function_policy (sp)) p )) (PreH10 : (cm_concrete_code_ready (cm_source_function_policy (sp)) p )) (PreH11 : (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) )) (PreH12 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH13 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH14 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH15 : (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) )) (PreH16 : (0 <= (cm_rep_globals_size ((cm_program_globals (p)))))) (PreH17 : (0 <= (cm_rep_strings_size ((cm_program_strings (p)))))) (PreH18 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH19 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH20 : (0 <= code_capacity)) (PreH21 : (code_capacity <= INT_MAX)) (PreH22 : (0 <= data_capacity)) (PreH23 : (data_capacity <= INT_MAX)) ,
  ((( &( "data_length" ) )) # Int  |->_)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((( &( "code_length" ) )) # Int  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((&((output_pre)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> code_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> old_code)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> old_data)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> old_entry)
  **  (cm_undef_int_buffer ops_ptr code_capacity )
  **  (cm_undef_int64_buffer imms_ptr code_capacity )
  **  (cm_undef_uint8_buffer data_ptr data_capacity )
|--
  “ (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) )) ”
.

Definition cmc_compile_partial_solve_wit_2_aux := 
forall (output_pre: Z) (program_pre: Z) (data_capacity: Z) (code_capacity: Z) (p: cm_program) (sp: cm_source_lookup_policy) (functions_ptr: Z) (ops_ptr: Z) (imms_ptr: Z) (data_ptr: Z) (old_code: Z) (old_data: Z) (old_entry: Z) (retval: Z) (PreH1 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH2 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH3 : (retval = (cm_model_code_length ((cm_source_function_policy (sp))) (p)))) (PreH4 : (cm_i32_code_count retval )) (PreH5 : (program_pre <> 0)) (PreH6 : (output_pre <> 0)) (PreH7 : (cm_semantic_wf_program (cm_source_function_policy (sp)) p )) (PreH8 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH9 : (cm_typed_program (cm_source_function_policy (sp)) p )) (PreH10 : (cm_concrete_code_ready (cm_source_function_policy (sp)) p )) (PreH11 : (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) )) (PreH12 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH13 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH14 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH15 : (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) )) (PreH16 : (0 <= (cm_rep_globals_size ((cm_program_globals (p)))))) (PreH17 : (0 <= (cm_rep_strings_size ((cm_program_strings (p)))))) (PreH18 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH19 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH20 : (0 <= code_capacity)) (PreH21 : (code_capacity <= INT_MAX)) (PreH22 : (0 <= data_capacity)) (PreH23 : (data_capacity <= INT_MAX)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> code_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> old_code)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> old_data)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> old_entry)
  **  (cm_undef_int_buffer ops_ptr code_capacity )
  **  (cm_undef_int64_buffer imms_ptr code_capacity )
  **  (cm_undef_uint8_buffer data_ptr data_capacity )
|--
  “ (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) )) ” 
  &&  “ (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (retval = (cm_model_code_length ((cm_source_function_policy (sp))) (p))) ” 
  &&  “ (cm_i32_code_count retval ) ” 
  &&  “ (program_pre <> 0) ” 
  &&  “ (output_pre <> 0) ” 
  &&  “ (cm_semantic_wf_program (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p ) ” 
  &&  “ (cm_typed_program (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_concrete_code_ready (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) ) ” 
  &&  “ (0 <= (cm_rep_globals_size ((cm_program_globals (p))))) ” 
  &&  “ (0 <= (cm_rep_strings_size ((cm_program_strings (p))))) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) )) ” 
  &&  “ (0 <= code_capacity) ” 
  &&  “ (code_capacity <= INT_MAX) ” 
  &&  “ (0 <= data_capacity) ” 
  &&  “ (data_capacity <= INT_MAX) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "ops")) # Ptr  |-> ops_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "imms")) # Ptr  |-> imms_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_capacity")) # Int  |-> code_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> old_code)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> old_data)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> old_entry)
  **  (cm_undef_int_buffer ops_ptr code_capacity )
  **  (cm_undef_int64_buffer imms_ptr code_capacity )
  **  (cm_undef_uint8_buffer data_ptr data_capacity )
.

Definition cmc_compile_partial_solve_wit_2 := cmc_compile_partial_solve_wit_2_pure -> cmc_compile_partial_solve_wit_2_aux.

Definition cmc_compile_partial_solve_wit_3_pure := 
forall (output_pre: Z) (program_pre: Z) (data_capacity: Z) (code_capacity: Z) (p: cm_program) (sp: cm_source_lookup_policy) (functions_ptr: Z) (data_ptr: Z) (code_length: Z) (data_length: Z) (PreH1 : (program_pre <> 0)) (PreH2 : (output_pre <> 0)) (PreH3 : (data_ptr <> 0)) (PreH4 : (code_length = (cm_model_code_length ((cm_source_function_policy (sp))) (p)))) (PreH5 : (data_length = (cm_model_data_length (p)))) (PreH6 : (0 <= code_length)) (PreH7 : (code_length <= code_capacity)) (PreH8 : (0 <= data_length)) (PreH9 : (data_length <= data_capacity)) (PreH10 : (cm_semantic_wf_program (cm_source_function_policy (sp)) p )) (PreH11 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH12 : (cm_typed_program (cm_source_function_policy (sp)) p )) (PreH13 : (cm_concrete_code_ready (cm_source_function_policy (sp)) p )) (PreH14 : (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) )) (PreH15 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH16 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH17 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH18 : (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) )) (PreH19 : (0 <= (cm_rep_globals_size ((cm_program_globals (p)))))) (PreH20 : (0 <= (cm_rep_strings_size ((cm_program_strings (p)))))) (PreH21 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH22 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH23 : (0 <= code_capacity)) (PreH24 : (code_capacity <= INT_MAX)) (PreH25 : (0 <= data_capacity)) (PreH26 : (data_capacity <= INT_MAX)) ,
  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "code_length" ) )) # Int  |-> code_length)
  **  ((( &( "data_length" ) )) # Int  |-> data_length)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> code_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> data_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> (-1))
  **  (UCharArray.seg data_ptr 0 0 (@nil Z) )
  **  (UCharArray.undef_seg data_ptr 0 data_capacity )
  **  (cm_resolved_emitter_plan_rep (cm_source_function_policy (sp)) p ( &( "emitter" ) ) output_pre code_capacity (@nil tvm_inst) (app ((cm_model_code ((cm_source_function_policy (sp))) (p))) ((@nil tvm_inst))) )
|--
  “ (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p ) ” 
  &&  “ (cm_typed_program (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ”
.

Definition cmc_compile_partial_solve_wit_3_aux := 
forall (output_pre: Z) (program_pre: Z) (data_capacity: Z) (code_capacity: Z) (p: cm_program) (sp: cm_source_lookup_policy) (functions_ptr: Z) (data_ptr: Z) (code_length: Z) (data_length: Z) (PreH1 : (program_pre <> 0)) (PreH2 : (output_pre <> 0)) (PreH3 : (data_ptr <> 0)) (PreH4 : (code_length = (cm_model_code_length ((cm_source_function_policy (sp))) (p)))) (PreH5 : (data_length = (cm_model_data_length (p)))) (PreH6 : (0 <= code_length)) (PreH7 : (code_length <= code_capacity)) (PreH8 : (0 <= data_length)) (PreH9 : (data_length <= data_capacity)) (PreH10 : (cm_semantic_wf_program (cm_source_function_policy (sp)) p )) (PreH11 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH12 : (cm_typed_program (cm_source_function_policy (sp)) p )) (PreH13 : (cm_concrete_code_ready (cm_source_function_policy (sp)) p )) (PreH14 : (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) )) (PreH15 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH16 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH17 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH18 : (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) )) (PreH19 : (0 <= (cm_rep_globals_size ((cm_program_globals (p)))))) (PreH20 : (0 <= (cm_rep_strings_size ((cm_program_strings (p)))))) (PreH21 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH22 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH23 : (0 <= code_capacity)) (PreH24 : (code_capacity <= INT_MAX)) (PreH25 : (0 <= data_capacity)) (PreH26 : (data_capacity <= INT_MAX)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> code_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> data_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> (-1))
  **  (UCharArray.seg data_ptr 0 0 (@nil Z) )
  **  (UCharArray.undef_seg data_ptr 0 data_capacity )
  **  (cm_resolved_emitter_plan_rep (cm_source_function_policy (sp)) p ( &( "emitter" ) ) output_pre code_capacity (@nil tvm_inst) (app ((cm_model_code ((cm_source_function_policy (sp))) (p))) ((@nil tvm_inst))) )
|--
  “ (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p ) ” 
  &&  “ (cm_typed_program (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (program_pre <> 0) ” 
  &&  “ (output_pre <> 0) ” 
  &&  “ (data_ptr <> 0) ” 
  &&  “ (code_length = (cm_model_code_length ((cm_source_function_policy (sp))) (p))) ” 
  &&  “ (data_length = (cm_model_data_length (p))) ” 
  &&  “ (0 <= code_length) ” 
  &&  “ (code_length <= code_capacity) ” 
  &&  “ (0 <= data_length) ” 
  &&  “ (data_length <= data_capacity) ” 
  &&  “ (cm_semantic_wf_program (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p ) ” 
  &&  “ (cm_typed_program (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_concrete_code_ready (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) ) ” 
  &&  “ (0 <= (cm_rep_globals_size ((cm_program_globals (p))))) ” 
  &&  “ (0 <= (cm_rep_strings_size ((cm_program_strings (p))))) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) )) ” 
  &&  “ (0 <= code_capacity) ” 
  &&  “ (code_capacity <= INT_MAX) ” 
  &&  “ (0 <= data_capacity) ” 
  &&  “ (data_capacity <= INT_MAX) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_resolved_emitter_plan_rep (cm_source_function_policy (sp)) p ( &( "emitter" ) ) output_pre code_capacity (@nil tvm_inst) (app ((cm_model_code ((cm_source_function_policy (sp))) (p))) ((@nil tvm_inst))) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> code_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> data_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> (-1))
  **  (UCharArray.seg data_ptr 0 0 (@nil Z) )
  **  (UCharArray.undef_seg data_ptr 0 data_capacity )
.

Definition cmc_compile_partial_solve_wit_3 := cmc_compile_partial_solve_wit_3_pure -> cmc_compile_partial_solve_wit_3_aux.

Definition cmc_compile_partial_solve_wit_4_pure := 
forall (output_pre: Z) (program_pre: Z) (data_capacity: Z) (code_capacity: Z) (p: cm_program) (sp: cm_source_lookup_policy) (functions_ptr: Z) (data_ptr: Z) (code_length: Z) (data_length: Z) (PreH1 : (program_pre <> 0)) (PreH2 : (output_pre <> 0)) (PreH3 : (data_ptr <> 0)) (PreH4 : (code_length = (cm_model_code_length ((cm_source_function_policy (sp))) (p)))) (PreH5 : (data_length = (cm_model_data_length (p)))) (PreH6 : (0 <= code_length)) (PreH7 : (code_length <= code_capacity)) (PreH8 : (0 <= data_length)) (PreH9 : (data_length <= data_capacity)) (PreH10 : (cm_semantic_wf_program (cm_source_function_policy (sp)) p )) (PreH11 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH12 : (cm_typed_program (cm_source_function_policy (sp)) p )) (PreH13 : (cm_concrete_code_ready (cm_source_function_policy (sp)) p )) (PreH14 : (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) )) (PreH15 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH16 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH17 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH18 : (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) )) (PreH19 : (0 <= (cm_rep_globals_size ((cm_program_globals (p)))))) (PreH20 : (0 <= (cm_rep_strings_size ((cm_program_strings (p)))))) (PreH21 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH22 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH23 : (0 <= code_capacity)) (PreH24 : (code_capacity <= INT_MAX)) (PreH25 : (0 <= data_capacity)) (PreH26 : (data_capacity <= INT_MAX)) ,
  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "code_length" ) )) # Int  |-> code_length)
  **  ((( &( "data_length" ) )) # Int  |-> data_length)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> code_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> data_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> (-1))
  **  (UCharArray.seg data_ptr 0 0 (@nil Z) )
  **  (UCharArray.undef_seg data_ptr 0 data_capacity )
  **  (cm_resolved_emitter_rep (cm_source_function_policy (sp)) p ( &( "emitter" ) ) output_pre code_capacity (cm_model_code ((cm_source_function_policy (sp))) (p)) )
|--
  “ (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p ) ” 
  &&  “ (cm_concrete_code_ready (cm_source_function_policy (sp)) p ) ”
.

Definition cmc_compile_partial_solve_wit_4_aux := 
forall (output_pre: Z) (program_pre: Z) (data_capacity: Z) (code_capacity: Z) (p: cm_program) (sp: cm_source_lookup_policy) (functions_ptr: Z) (data_ptr: Z) (code_length: Z) (data_length: Z) (PreH1 : (program_pre <> 0)) (PreH2 : (output_pre <> 0)) (PreH3 : (data_ptr <> 0)) (PreH4 : (code_length = (cm_model_code_length ((cm_source_function_policy (sp))) (p)))) (PreH5 : (data_length = (cm_model_data_length (p)))) (PreH6 : (0 <= code_length)) (PreH7 : (code_length <= code_capacity)) (PreH8 : (0 <= data_length)) (PreH9 : (data_length <= data_capacity)) (PreH10 : (cm_semantic_wf_program (cm_source_function_policy (sp)) p )) (PreH11 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH12 : (cm_typed_program (cm_source_function_policy (sp)) p )) (PreH13 : (cm_concrete_code_ready (cm_source_function_policy (sp)) p )) (PreH14 : (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) )) (PreH15 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH16 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH17 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH18 : (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) )) (PreH19 : (0 <= (cm_rep_globals_size ((cm_program_globals (p)))))) (PreH20 : (0 <= (cm_rep_strings_size ((cm_program_strings (p)))))) (PreH21 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH22 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH23 : (0 <= code_capacity)) (PreH24 : (code_capacity <= INT_MAX)) (PreH25 : (0 <= data_capacity)) (PreH26 : (data_capacity <= INT_MAX)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> code_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> data_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> (-1))
  **  (UCharArray.seg data_ptr 0 0 (@nil Z) )
  **  (UCharArray.undef_seg data_ptr 0 data_capacity )
  **  (cm_resolved_emitter_rep (cm_source_function_policy (sp)) p ( &( "emitter" ) ) output_pre code_capacity (cm_model_code ((cm_source_function_policy (sp))) (p)) )
|--
  “ (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p ) ” 
  &&  “ (cm_concrete_code_ready (cm_source_function_policy (sp)) p ) ” 
  &&  “ (program_pre <> 0) ” 
  &&  “ (output_pre <> 0) ” 
  &&  “ (data_ptr <> 0) ” 
  &&  “ (code_length = (cm_model_code_length ((cm_source_function_policy (sp))) (p))) ” 
  &&  “ (data_length = (cm_model_data_length (p))) ” 
  &&  “ (0 <= code_length) ” 
  &&  “ (code_length <= code_capacity) ” 
  &&  “ (0 <= data_length) ” 
  &&  “ (data_length <= data_capacity) ” 
  &&  “ (cm_semantic_wf_program (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p ) ” 
  &&  “ (cm_typed_program (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_concrete_code_ready (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) ) ” 
  &&  “ (0 <= (cm_rep_globals_size ((cm_program_globals (p))))) ” 
  &&  “ (0 <= (cm_rep_strings_size ((cm_program_strings (p))))) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) )) ” 
  &&  “ (0 <= code_capacity) ” 
  &&  “ (code_capacity <= INT_MAX) ” 
  &&  “ (0 <= data_capacity) ” 
  &&  “ (data_capacity <= INT_MAX) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_resolved_emitter_rep (cm_source_function_policy (sp)) p ( &( "emitter" ) ) output_pre code_capacity (cm_model_code ((cm_source_function_policy (sp))) (p)) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> code_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> data_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> (-1))
  **  (UCharArray.seg data_ptr 0 0 (@nil Z) )
  **  (UCharArray.undef_seg data_ptr 0 data_capacity )
.

Definition cmc_compile_partial_solve_wit_4 := cmc_compile_partial_solve_wit_4_pure -> cmc_compile_partial_solve_wit_4_aux.

Definition cmc_compile_partial_solve_wit_5_pure := 
forall (output_pre: Z) (program_pre: Z) (data_capacity: Z) (code_capacity: Z) (p: cm_program) (sp: cm_source_lookup_policy) (functions_ptr: Z) (structs_ptr: Z) (globals_ptr: Z) (strings_ptr: Z) (data_ptr: Z) (code_length: Z) (data_length: Z) (PreH1 : (program_pre <> 0)) (PreH2 : (output_pre <> 0)) (PreH3 : (data_ptr <> 0)) (PreH4 : (code_length = (cm_model_code_length ((cm_source_function_policy (sp))) (p)))) (PreH5 : (data_length = (cm_model_data_length (p)))) (PreH6 : (0 <= code_length)) (PreH7 : (code_length <= code_capacity)) (PreH8 : (0 <= data_length)) (PreH9 : (data_length <= data_capacity)) (PreH10 : (cm_semantic_wf_program (cm_source_function_policy (sp)) p )) (PreH11 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH12 : (cm_typed_program (cm_source_function_policy (sp)) p )) (PreH13 : (cm_concrete_code_ready (cm_source_function_policy (sp)) p )) (PreH14 : (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) )) (PreH15 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH16 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH17 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH18 : (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) )) (PreH19 : (0 <= (cm_rep_globals_size ((cm_program_globals (p)))))) (PreH20 : (0 <= (cm_rep_strings_size ((cm_program_strings (p)))))) (PreH21 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH22 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH23 : (0 <= code_capacity)) (PreH24 : (code_capacity <= INT_MAX)) (PreH25 : (0 <= data_capacity)) (PreH26 : (data_capacity <= INT_MAX)) ,
  ((( &( "emitted_data" ) )) # Int  |->_)
  **  ((( &( "output_data_capacity" ) )) # Int  |-> data_capacity)
  **  ((( &( "data" ) )) # Ptr  |-> data_ptr)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_ptr)
  **  ((( &( "globals" ) )) # Ptr  |-> globals_ptr)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "output" ) )) # Ptr  |-> output_pre)
  **  ((( &( "code_length" ) )) # Int  |-> code_length)
  **  ((( &( "data_length" ) )) # Int  |-> data_length)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> structs_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> globals_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> strings_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep structs_ptr (cm_program_structs (p)) )
  **  (cm_global_list_rep globals_ptr (cm_program_globals (p)) )
  **  (cm_string_list_rep strings_ptr (cm_program_strings (p)) )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> code_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> data_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> (-1))
  **  (UCharArray.seg data_ptr 0 0 (@nil Z) )
  **  (UCharArray.undef_seg data_ptr 0 data_capacity )
  **  (cm_emitter_rep ( &( "emitter" ) ) output_pre code_capacity (cm_rep_ops ((cm_model_code ((cm_source_function_policy (sp))) (p)))) (cm_rep_imms ((cm_model_code ((cm_source_function_policy (sp))) (p)))) )
|--
  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (0 <= (cm_rep_globals_size ((cm_program_globals (p))))) ” 
  &&  “ (0 <= (cm_rep_strings_size ((cm_program_strings (p))))) ” 
  &&  “ (((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= data_capacity) ” 
  &&  “ (data_capacity <= INT_MAX) ”
.

Definition cmc_compile_partial_solve_wit_5_aux := 
forall (output_pre: Z) (program_pre: Z) (data_capacity: Z) (code_capacity: Z) (p: cm_program) (sp: cm_source_lookup_policy) (functions_ptr: Z) (structs_ptr: Z) (globals_ptr: Z) (strings_ptr: Z) (data_ptr: Z) (code_length: Z) (data_length: Z) (PreH1 : (program_pre <> 0)) (PreH2 : (output_pre <> 0)) (PreH3 : (data_ptr <> 0)) (PreH4 : (code_length = (cm_model_code_length ((cm_source_function_policy (sp))) (p)))) (PreH5 : (data_length = (cm_model_data_length (p)))) (PreH6 : (0 <= code_length)) (PreH7 : (code_length <= code_capacity)) (PreH8 : (0 <= data_length)) (PreH9 : (data_length <= data_capacity)) (PreH10 : (cm_semantic_wf_program (cm_source_function_policy (sp)) p )) (PreH11 : (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p )) (PreH12 : (cm_typed_program (cm_source_function_policy (sp)) p )) (PreH13 : (cm_concrete_code_ready (cm_source_function_policy (sp)) p )) (PreH14 : (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) )) (PreH15 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH16 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH17 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH18 : (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) )) (PreH19 : (0 <= (cm_rep_globals_size ((cm_program_globals (p)))))) (PreH20 : (0 <= (cm_rep_strings_size ((cm_program_strings (p)))))) (PreH21 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH22 : ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ))) (PreH23 : (0 <= code_capacity)) (PreH24 : (code_capacity <= INT_MAX)) (PreH25 : (0 <= data_capacity)) (PreH26 : (data_capacity <= INT_MAX)) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> structs_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> globals_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> strings_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep structs_ptr (cm_program_structs (p)) )
  **  (cm_global_list_rep globals_ptr (cm_program_globals (p)) )
  **  (cm_string_list_rep strings_ptr (cm_program_strings (p)) )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> code_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> data_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> (-1))
  **  (UCharArray.seg data_ptr 0 0 (@nil Z) )
  **  (UCharArray.undef_seg data_ptr 0 data_capacity )
  **  (cm_emitter_rep ( &( "emitter" ) ) output_pre code_capacity (cm_rep_ops ((cm_model_code ((cm_source_function_policy (sp))) (p)))) (cm_rep_imms ((cm_model_code ((cm_source_function_policy (sp))) (p)))) )
|--
  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (0 <= (cm_rep_globals_size ((cm_program_globals (p))))) ” 
  &&  “ (0 <= (cm_rep_strings_size ((cm_program_strings (p))))) ” 
  &&  “ (((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= data_capacity) ” 
  &&  “ (data_capacity <= INT_MAX) ” 
  &&  “ (program_pre <> 0) ” 
  &&  “ (output_pre <> 0) ” 
  &&  “ (data_ptr <> 0) ” 
  &&  “ (code_length = (cm_model_code_length ((cm_source_function_policy (sp))) (p))) ” 
  &&  “ (data_length = (cm_model_data_length (p))) ” 
  &&  “ (0 <= code_length) ” 
  &&  “ (code_length <= code_capacity) ” 
  &&  “ (0 <= data_length) ” 
  &&  “ (data_length <= data_capacity) ” 
  &&  “ (cm_semantic_wf_program (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_wf_program (cm_source_function_policy (sp)) (cm_source_codegen_obligations ((cm_source_function_policy (sp)))) p ) ” 
  &&  “ (cm_typed_program (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_concrete_code_ready (cm_source_function_policy (sp)) p ) ” 
  &&  “ (cm_concrete_functions_ready (cm_source_function_policy (sp)) p 0 (cm_program_functions (p)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_data_globals_wf (cm_program_structs (p)) (cm_program_globals (p)) ) ” 
  &&  “ (0 <= (cm_rep_globals_size ((cm_program_globals (p))))) ” 
  &&  “ (0 <= (cm_rep_strings_size ((cm_program_strings (p))))) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ ((cm_model_data_length (p)) = ((8 + (cm_rep_globals_size ((cm_program_globals (p)))) ) + (cm_rep_strings_size ((cm_program_strings (p)))) )) ” 
  &&  “ (0 <= code_capacity) ” 
  &&  “ (code_capacity <= INT_MAX) ” 
  &&  “ (0 <= data_capacity) ” 
  &&  “ (data_capacity <= INT_MAX) ”
  &&  (cm_global_list_rep globals_ptr (cm_program_globals (p)) )
  **  (cm_string_list_rep strings_ptr (cm_program_strings (p)) )
  **  (UCharArray.seg data_ptr 0 0 (@nil Z) )
  **  (UCharArray.undef_seg data_ptr 0 data_capacity )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> structs_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> globals_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> strings_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep structs_ptr (cm_program_structs (p)) )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  ((&((output_pre)  # "cm_output" ->ₛ "data")) # Ptr  |-> data_ptr)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_capacity")) # Int  |-> data_capacity)
  **  ((&((output_pre)  # "cm_output" ->ₛ "code_length")) # Int  |-> code_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "data_length")) # Int  |-> data_length)
  **  ((&((output_pre)  # "cm_output" ->ₛ "entry")) # Int  |-> (-1))
  **  (cm_emitter_rep ( &( "emitter" ) ) output_pre code_capacity (cm_rep_ops ((cm_model_code ((cm_source_function_policy (sp))) (p)))) (cm_rep_imms ((cm_model_code ((cm_source_function_policy (sp))) (p)))) )
.

Definition cmc_compile_partial_solve_wit_5 := cmc_compile_partial_solve_wit_5_pure -> cmc_compile_partial_solve_wit_5_aux.

Module Type VC_Correct.


Axiom proof_of_cmc_compile_safety_wit_1 : cmc_compile_safety_wit_1.
Axiom proof_of_cmc_compile_safety_wit_2 : cmc_compile_safety_wit_2.
Axiom proof_of_cmc_compile_safety_wit_3 : cmc_compile_safety_wit_3.
Axiom proof_of_cmc_compile_safety_wit_4 : cmc_compile_safety_wit_4.
Axiom proof_of_cmc_compile_safety_wit_5 : cmc_compile_safety_wit_5.
Axiom proof_of_cmc_compile_safety_wit_6 : cmc_compile_safety_wit_6.
Axiom proof_of_cmc_compile_safety_wit_7 : cmc_compile_safety_wit_7.
Axiom proof_of_cmc_compile_entail_wit_1 : cmc_compile_entail_wit_1.
Axiom proof_of_cmc_compile_entail_wit_2 : cmc_compile_entail_wit_2.
Axiom proof_of_cmc_compile_entail_wit_3 : cmc_compile_entail_wit_3.
Axiom proof_of_cmc_compile_entail_wit_4 : cmc_compile_entail_wit_4.
Axiom proof_of_cmc_compile_entail_wit_5 : cmc_compile_entail_wit_5.
Axiom proof_of_cmc_compile_entail_wit_6 : cmc_compile_entail_wit_6.
Axiom proof_of_cmc_compile_return_wit_1 : cmc_compile_return_wit_1.
Axiom proof_of_cmc_compile_return_wit_2 : cmc_compile_return_wit_2.
Axiom proof_of_cmc_compile_return_wit_3 : cmc_compile_return_wit_3.
Axiom proof_of_cmc_compile_partial_solve_wit_1_pure : cmc_compile_partial_solve_wit_1_pure.
Axiom proof_of_cmc_compile_partial_solve_wit_1 : cmc_compile_partial_solve_wit_1.
Axiom proof_of_cmc_compile_partial_solve_wit_2_pure : cmc_compile_partial_solve_wit_2_pure.
Axiom proof_of_cmc_compile_partial_solve_wit_2 : cmc_compile_partial_solve_wit_2.
Axiom proof_of_cmc_compile_partial_solve_wit_3_pure : cmc_compile_partial_solve_wit_3_pure.
Axiom proof_of_cmc_compile_partial_solve_wit_3 : cmc_compile_partial_solve_wit_3.
Axiom proof_of_cmc_compile_partial_solve_wit_4_pure : cmc_compile_partial_solve_wit_4_pure.
Axiom proof_of_cmc_compile_partial_solve_wit_4 : cmc_compile_partial_solve_wit_4.
Axiom proof_of_cmc_compile_partial_solve_wit_5_pure : cmc_compile_partial_solve_wit_5_pure.
Axiom proof_of_cmc_compile_partial_solve_wit_5 : cmc_compile_partial_solve_wit_5.

End VC_Correct.
