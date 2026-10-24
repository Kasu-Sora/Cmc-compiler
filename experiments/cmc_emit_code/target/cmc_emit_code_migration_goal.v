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
Require Import SimpleC.EE.QCP_demos_human.cmc_emit_code_migration_lib.
Local Open Scope sac.

(*----- Function cmc_emit_code -----*)

Definition cmc_emit_code_safety_wit_1 := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : ((cm_function_pc (policy) (p) (0)) = 11)) (PreH2 : (cm_wf_program policy cg p )) (PreH3 : (cm_typed_program policy p )) (PreH4 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) (PreH5 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH6 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH7 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH8 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_emit_prelude (policy) (p)))) (app ((cm_emit_functions (policy) (p) (0) ((cm_program_functions (p))))) (tail)) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "functions" ) )) # Ptr  |-> functions_ptr)
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_emit_code_safety_wit_2 := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : ((cm_function_pc (policy) (p) (0)) = 11)) (PreH2 : (cm_wf_program policy cg p )) (PreH3 : (cm_typed_program policy p )) (PreH4 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) (PreH5 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH6 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH7 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH8 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_emit_prelude (policy) (p)))) (app ((cm_emit_functions (policy) (p) (0) ((cm_program_functions (p))))) (tail)) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "functions" ) )) # Ptr  |-> functions_ptr)
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
|--
  “ (11 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 11) ”
.

Definition cmc_emit_code_entail_wit_1 := 
(
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_typed_program policy p )) (PreH3 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) (PreH4 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH5 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH6 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH7 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_model_code (policy) (p))) (tail)) )
|--
  EX (tp: Z)  (gp: Z)  (sp: Z) ,
  “ (program_pre <> 0) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ”
  &&  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_model_code (policy) (p))) (tail)) )
) \/
(
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_typed_program policy p )) (PreH3 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) (PreH4 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH5 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH6 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH7 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_model_code (policy) (p))) (tail)) )
|--
  EX (tp: Z)  (gp: Z)  (sp: Z) ,
  “ (program_pre <> 0) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ”
  &&  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_model_code (policy) (p))) (tail)) )
).

Definition cmc_emit_code_entail_wit_2 := 
(
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (PreH1 : (program_pre <> 0)) (PreH2 : (cm_wf_program policy cg p )) (PreH3 : (cm_typed_program policy p )) (PreH4 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) (PreH5 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH6 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH7 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH8 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_model_code (policy) (p))) (tail)) )
|--
  “ ((cm_function_pc (policy) (p) (0)) = 11) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_prelude (policy) (p))) ((app ((cm_emit_functions (policy) (p) (0) ((cm_program_functions (p))))) (tail)))) )
) \/
(
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (PreH1 : ((cm_program_main (p)) <= INT_MAX)) (PreH2 : ((cm_program_main (p)) >= INT_MIN)) (PreH3 : (program_pre <> 0)) (PreH4 : (cm_wf_program policy cg p )) (PreH5 : (cm_typed_program policy p )) (PreH6 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) (PreH7 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH8 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH9 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH10 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_model_code (policy) (p))) (tail)) )
|--
  “ ((cm_function_pc (policy) (p) (0)) = 11) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_prelude (policy) (p))) ((app ((cm_emit_functions (policy) (p) (0) ((cm_program_functions (p))))) (tail)))) )
).

Definition cmc_emit_code_entail_wit_2_split_goal_1 := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (PreH1 : ((cm_program_main (p)) <= INT_MAX)) (PreH2 : ((cm_program_main (p)) >= INT_MIN)) (PreH3 : (program_pre <> 0)) (PreH4 : (cm_wf_program policy cg p )) (PreH5 : (cm_typed_program policy p )) (PreH6 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) (PreH7 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH8 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH9 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH10 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_model_code (policy) (p))) (tail)) )
|--
  “ ((cm_function_pc (policy) (p) (0)) = 11) ”
.

Definition cmc_emit_code_entail_wit_2_split_goal_spatial := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (PreH1 : ((cm_program_main (p)) <= INT_MAX)) (PreH2 : ((cm_program_main (p)) >= INT_MIN)) (PreH3 : (program_pre <> 0)) (PreH4 : (cm_wf_program policy cg p )) (PreH5 : (cm_typed_program policy p )) (PreH6 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) (PreH7 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH8 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH9 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH10 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_model_code (policy) (p))) (tail)) )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_prelude (policy) (p))) ((app ((cm_emit_functions (policy) (p) (0) ((cm_program_functions (p))))) (tail)))) )
.

Definition cmc_emit_code_return_wit_1 := 
(
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_typed_program policy p )) (PreH3 : (11 = (cm_function_pc (policy) (p) (0)))) (PreH4 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) (PreH5 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH6 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH7 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH8 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH9 : ((cm_function_pc (policy) (p) (0)) = 11)) (PreH10 : (cm_wf_program policy cg p )) (PreH11 : (cm_typed_program policy p )) (PreH12 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) (PreH13 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH14 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH15 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH16 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app (done) ((cm_emit_prelude (policy) (p))))) ((cm_emit_functions (policy) (p) (0) ((cm_program_functions (p)))))) tail )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_model_code (policy) (p)))) tail )
) \/
(
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_typed_program policy p )) (PreH3 : (11 = (cm_function_pc (policy) (p) (0)))) (PreH4 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) (PreH5 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH6 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH7 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH8 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH9 : ((cm_function_pc (policy) (p) (0)) = 11)) (PreH10 : (cm_wf_program policy cg p )) (PreH11 : (cm_typed_program policy p )) (PreH12 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) (PreH13 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH14 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH15 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH16 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app (done) ((cm_emit_prelude (policy) (p))))) ((cm_emit_functions (policy) (p) (0) ((cm_program_functions (p)))))) tail )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_model_code (policy) (p)))) tail )
).

Definition cmc_emit_code_return_wit_1_split_goal_spatial := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_typed_program policy p )) (PreH3 : (11 = (cm_function_pc (policy) (p) (0)))) (PreH4 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) (PreH5 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH6 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH7 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH8 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH9 : ((cm_function_pc (policy) (p) (0)) = 11)) (PreH10 : (cm_wf_program policy cg p )) (PreH11 : (cm_typed_program policy p )) (PreH12 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) (PreH13 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH14 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH15 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH16 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app (done) ((cm_emit_prelude (policy) (p))))) ((cm_emit_functions (policy) (p) (0) ((cm_program_functions (p)))))) tail )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_model_code (policy) (p)))) tail )
.

Definition cmc_emit_code_partial_solve_wit_1 := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : ((cm_function_pc (policy) (p) (0)) = 11)) (PreH2 : (cm_wf_program policy cg p )) (PreH3 : (cm_typed_program policy p )) (PreH4 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) (PreH5 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH6 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH7 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH8 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_prelude (policy) (p))) ((app ((cm_emit_functions (policy) (p) (0) ((cm_program_functions (p))))) (tail)))) )
|--
  “ ((cm_function_pc (policy) (p) (0)) = 11) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_prelude (policy) (p))) ((app ((cm_emit_functions (policy) (p) (0) ((cm_program_functions (p))))) (tail)))) )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
.

Definition cmc_emit_code_partial_solve_wit_2_pure := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : ((cm_function_pc (policy) (p) (0)) = 11)) (PreH2 : (cm_wf_program policy cg p )) (PreH3 : (cm_typed_program policy p )) (PreH4 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) (PreH5 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH6 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH7 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH8 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_emit_prelude (policy) (p)))) (app ((cm_emit_functions (policy) (p) (0) ((cm_program_functions (p))))) (tail)) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "functions" ) )) # Ptr  |-> functions_ptr)
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (11 = (cm_function_pc (policy) (p) (0))) ” 
  &&  “ (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ”
.

Definition cmc_emit_code_partial_solve_wit_2_aux := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : ((cm_function_pc (policy) (p) (0)) = 11)) (PreH2 : (cm_wf_program policy cg p )) (PreH3 : (cm_typed_program policy p )) (PreH4 : (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) )) (PreH5 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH6 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH7 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH8 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_emit_prelude (policy) (p)))) (app ((cm_emit_functions (policy) (p) (0) ((cm_program_functions (p))))) (tail)) )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (11 = (cm_function_pc (policy) (p) (0))) ” 
  &&  “ (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ ((cm_function_pc (policy) (p) (0)) = 11) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (cm_concrete_functions_ready policy p 0 (cm_program_functions (p)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_list_rep functions_ptr (cm_program_functions (p)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_emit_prelude (policy) (p)))) (app ((cm_emit_functions (policy) (p) (0) ((cm_program_functions (p))))) (tail)) )
.

Definition cmc_emit_code_partial_solve_wit_2 := cmc_emit_code_partial_solve_wit_2_pure -> cmc_emit_code_partial_solve_wit_2_aux.

Module Type VC_Correct.


Axiom proof_of_cmc_emit_code_safety_wit_1 : cmc_emit_code_safety_wit_1.
Axiom proof_of_cmc_emit_code_safety_wit_2 : cmc_emit_code_safety_wit_2.
Axiom proof_of_cmc_emit_code_entail_wit_1 : cmc_emit_code_entail_wit_1.
Axiom proof_of_cmc_emit_code_entail_wit_2 : cmc_emit_code_entail_wit_2.
Axiom proof_of_cmc_emit_code_return_wit_1 : cmc_emit_code_return_wit_1.
Axiom proof_of_cmc_emit_code_partial_solve_wit_1 : cmc_emit_code_partial_solve_wit_1.
Axiom proof_of_cmc_emit_code_partial_solve_wit_2_pure : cmc_emit_code_partial_solve_wit_2_pure.
Axiom proof_of_cmc_emit_code_partial_solve_wit_2 : cmc_emit_code_partial_solve_wit_2.

End VC_Correct.
