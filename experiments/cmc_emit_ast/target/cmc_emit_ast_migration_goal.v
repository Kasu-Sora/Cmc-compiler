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
Require Import SimpleC.EE.QCP_demos_human.cmc_emit_ast_migration_lib.
Local Open Scope sac.

(*----- Function cm_emit_binding_address -----*)

Definition cm_emit_binding_address_safety_wit_1 := 
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (zp: Z) (zl: Z) (PreH1 : (program_pre <> 0)) (PreH2 : (fn_pre <> 0)) (PreH3 : (0 <= slot_pre)) (PreH4 : (cm_wf_program policy cg p )) (PreH5 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH6 : (structs = (cm_program_structs (p)))) (PreH7 : (globals = (cm_program_globals (p)))) (PreH8 : (cm_binding_valid p f scope_pre slot_pre )) (PreH9 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH10 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH11 : (cm_rep_globals_safe globals )) (PreH12 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH13 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH14 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "scope" ) )) # Int  |-> scope_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_emit_binding_address_safety_wit_2 := 
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (zp: Z) (zl: Z) (retval: Z) (PreH1 : (0 <= slot_pre)) (PreH2 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH3 : (retval = (cm_rep_global_address ((cm_program_globals (p))) (slot_pre)))) (PreH4 : (16 <= retval)) (PreH5 : (retval <= 1048576)) (PreH6 : (scope_pre = 0)) (PreH7 : (program_pre <> 0)) (PreH8 : (fn_pre <> 0)) (PreH9 : (0 <= slot_pre)) (PreH10 : (cm_wf_program policy cg p )) (PreH11 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH12 : (structs = (cm_program_structs (p)))) (PreH13 : (globals = (cm_program_globals (p)))) (PreH14 : (cm_binding_valid p f scope_pre slot_pre )) (PreH15 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH16 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH17 : (cm_rep_globals_safe globals )) (PreH18 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH19 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH20 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  ((( &( "address" ) )) # Int64  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "scope" ) )) # Int  |-> scope_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_emit_binding_address_safety_wit_3 := 
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (zp: Z) (zl: Z) (PreH1 : (scope_pre <> 0)) (PreH2 : (program_pre <> 0)) (PreH3 : (fn_pre <> 0)) (PreH4 : (0 <= slot_pre)) (PreH5 : (cm_wf_program policy cg p )) (PreH6 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH7 : (structs = (cm_program_structs (p)))) (PreH8 : (globals = (cm_program_globals (p)))) (PreH9 : (cm_binding_valid p f scope_pre slot_pre )) (PreH10 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH11 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH12 : (cm_rep_globals_safe globals )) (PreH13 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH14 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH15 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "scope" ) )) # Int  |-> scope_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cm_emit_binding_address_entail_wit_1 := 
(
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH3 : (structs = (cm_program_structs (p)))) (PreH4 : (globals = (cm_program_globals (p)))) (PreH5 : (cm_binding_valid p f scope_pre slot_pre )) (PreH6 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH7 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH8 : (cm_rep_globals_safe globals )) (PreH9 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH10 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH11 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  EX (zl: Z)  (zp: Z)  (tp: Z)  (gp: Z)  (sp: Z) ,
  “ (program_pre <> 0) ” 
  &&  “ (fn_pre <> 0) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (globals = (cm_program_globals (p))) ” 
  &&  “ (cm_binding_valid p f scope_pre slot_pre ) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity) ”
  &&  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
) \/
(
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH3 : (structs = (cm_program_structs (p)))) (PreH4 : (globals = (cm_program_globals (p)))) (PreH5 : (cm_binding_valid p f scope_pre slot_pre )) (PreH6 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH7 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH8 : (cm_rep_globals_safe globals )) (PreH9 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH10 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH11 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  EX (zl: Z)  (zp: Z)  (tp: Z)  (gp: Z)  (sp: Z) ,
  “ (program_pre <> 0) ” 
  &&  “ (fn_pre <> 0) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (globals = (cm_program_globals (p))) ” 
  &&  “ (cm_binding_valid p f scope_pre slot_pre ) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity) ”
  &&  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
).

Definition cm_emit_binding_address_return_wit_1 := 
(
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (zp: Z) (zl: Z) (retval: Z) (PreH1 : (0 <= slot_pre)) (PreH2 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH3 : (retval = (cm_rep_global_address ((cm_program_globals (p))) (slot_pre)))) (PreH4 : (16 <= retval)) (PreH5 : (retval <= 1048576)) (PreH6 : (scope_pre = 0)) (PreH7 : (program_pre <> 0)) (PreH8 : (fn_pre <> 0)) (PreH9 : (0 <= slot_pre)) (PreH10 : (cm_wf_program policy cg p )) (PreH11 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH12 : (structs = (cm_program_structs (p)))) (PreH13 : (globals = (cm_program_globals (p)))) (PreH14 : (cm_binding_valid p f scope_pre slot_pre )) (PreH15 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH16 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH17 : (cm_rep_globals_safe globals )) (PreH18 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH19 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH20 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMPushOp) (retval))) ((@nil tvm_inst))))) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (globals = (cm_program_globals (p))) ” 
  &&  “ (cm_binding_valid p f scope_pre slot_pre ) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) )
) \/
(
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (zp: Z) (zl: Z) (retval: Z) (PreH1 : ((cm_type_encode ((cm_function_ret (f)))) <= INT_MAX)) (PreH2 : ((cm_program_main (p)) <= INT_MAX)) (PreH3 : ((cm_type_encode ((cm_function_ret (f)))) >= INT_MIN)) (PreH4 : ((cm_program_main (p)) >= INT_MIN)) (PreH5 : (0 <= slot_pre)) (PreH6 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH7 : (retval = (cm_rep_global_address ((cm_program_globals (p))) (slot_pre)))) (PreH8 : (16 <= retval)) (PreH9 : (retval <= 1048576)) (PreH10 : (scope_pre = 0)) (PreH11 : (program_pre <> 0)) (PreH12 : (fn_pre <> 0)) (PreH13 : (0 <= slot_pre)) (PreH14 : (cm_wf_program policy cg p )) (PreH15 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH16 : (structs = (cm_program_structs (p)))) (PreH17 : (globals = (cm_program_globals (p)))) (PreH18 : (cm_binding_valid p f scope_pre slot_pre )) (PreH19 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH20 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH21 : (cm_rep_globals_safe globals )) (PreH22 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH23 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH24 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMPushOp) (retval))) ((@nil tvm_inst))))) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) )
).

Definition cm_emit_binding_address_return_wit_1_split_goal_spatial := 
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (zp: Z) (zl: Z) (retval: Z) (PreH1 : ((cm_type_encode ((cm_function_ret (f)))) <= INT_MAX)) (PreH2 : ((cm_program_main (p)) <= INT_MAX)) (PreH3 : ((cm_type_encode ((cm_function_ret (f)))) >= INT_MIN)) (PreH4 : ((cm_program_main (p)) >= INT_MIN)) (PreH5 : (0 <= slot_pre)) (PreH6 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH7 : (retval = (cm_rep_global_address ((cm_program_globals (p))) (slot_pre)))) (PreH8 : (16 <= retval)) (PreH9 : (retval <= 1048576)) (PreH10 : (scope_pre = 0)) (PreH11 : (program_pre <> 0)) (PreH12 : (fn_pre <> 0)) (PreH13 : (0 <= slot_pre)) (PreH14 : (cm_wf_program policy cg p )) (PreH15 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH16 : (structs = (cm_program_structs (p)))) (PreH17 : (globals = (cm_program_globals (p)))) (PreH18 : (cm_binding_valid p f scope_pre slot_pre )) (PreH19 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH20 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH21 : (cm_rep_globals_safe globals )) (PreH22 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH23 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH24 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMPushOp) (retval))) ((@nil tvm_inst))))) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) )
.

Definition cm_emit_binding_address_return_wit_2 := 
(
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (zp: Z) (zl: Z) (retval: Z) (PreH1 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH2 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH3 : (0 <= slot_pre)) (PreH4 : (retval = ((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_member_prefix ((cm_function_locals (f))) (slot_pre)) ))) (PreH5 : (scope_pre = 1)) (PreH6 : (scope_pre <> 0)) (PreH7 : (program_pre <> 0)) (PreH8 : (fn_pre <> 0)) (PreH9 : (0 <= slot_pre)) (PreH10 : (cm_wf_program policy cg p )) (PreH11 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH12 : (structs = (cm_program_structs (p)))) (PreH13 : (globals = (cm_program_globals (p)))) (PreH14 : (cm_binding_valid p f scope_pre slot_pre )) (PreH15 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH16 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH17 : (cm_rep_globals_safe globals )) (PreH18 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH19 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH20 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_fp_relative_address_code (retval)))) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (globals = (cm_program_globals (p))) ” 
  &&  “ (cm_binding_valid p f scope_pre slot_pre ) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) )
) \/
(
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (zp: Z) (zl: Z) (retval: Z) (PreH1 : ((cm_type_encode ((cm_function_ret (f)))) <= INT_MAX)) (PreH2 : ((cm_program_main (p)) <= INT_MAX)) (PreH3 : ((cm_type_encode ((cm_function_ret (f)))) >= INT_MIN)) (PreH4 : ((cm_program_main (p)) >= INT_MIN)) (PreH5 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH7 : (0 <= slot_pre)) (PreH8 : (retval = ((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_member_prefix ((cm_function_locals (f))) (slot_pre)) ))) (PreH9 : (scope_pre = 1)) (PreH10 : (scope_pre <> 0)) (PreH11 : (program_pre <> 0)) (PreH12 : (fn_pre <> 0)) (PreH13 : (0 <= slot_pre)) (PreH14 : (cm_wf_program policy cg p )) (PreH15 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH16 : (structs = (cm_program_structs (p)))) (PreH17 : (globals = (cm_program_globals (p)))) (PreH18 : (cm_binding_valid p f scope_pre slot_pre )) (PreH19 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH20 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH21 : (cm_rep_globals_safe globals )) (PreH22 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH23 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH24 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_fp_relative_address_code (retval)))) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) )
).

Definition cm_emit_binding_address_return_wit_2_split_goal_spatial := 
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (zp: Z) (zl: Z) (retval: Z) (PreH1 : ((cm_type_encode ((cm_function_ret (f)))) <= INT_MAX)) (PreH2 : ((cm_program_main (p)) <= INT_MAX)) (PreH3 : ((cm_type_encode ((cm_function_ret (f)))) >= INT_MIN)) (PreH4 : ((cm_program_main (p)) >= INT_MIN)) (PreH5 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH7 : (0 <= slot_pre)) (PreH8 : (retval = ((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_member_prefix ((cm_function_locals (f))) (slot_pre)) ))) (PreH9 : (scope_pre = 1)) (PreH10 : (scope_pre <> 0)) (PreH11 : (program_pre <> 0)) (PreH12 : (fn_pre <> 0)) (PreH13 : (0 <= slot_pre)) (PreH14 : (cm_wf_program policy cg p )) (PreH15 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH16 : (structs = (cm_program_structs (p)))) (PreH17 : (globals = (cm_program_globals (p)))) (PreH18 : (cm_binding_valid p f scope_pre slot_pre )) (PreH19 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH20 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH21 : (cm_rep_globals_safe globals )) (PreH22 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH23 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH24 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_fp_relative_address_code (retval)))) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) )
.

Definition cm_emit_binding_address_return_wit_3 := 
(
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (zp: Z) (zl: Z) (retval: Z) (PreH1 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH2 : (0 <= slot_pre)) (PreH3 : (retval = (8 + (cm_rep_member_prefix ((cm_function_params (f))) (slot_pre)) ))) (PreH4 : (scope_pre <> 1)) (PreH5 : (scope_pre <> 0)) (PreH6 : (program_pre <> 0)) (PreH7 : (fn_pre <> 0)) (PreH8 : (0 <= slot_pre)) (PreH9 : (cm_wf_program policy cg p )) (PreH10 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH11 : (structs = (cm_program_structs (p)))) (PreH12 : (globals = (cm_program_globals (p)))) (PreH13 : (cm_binding_valid p f scope_pre slot_pre )) (PreH14 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH15 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH16 : (cm_rep_globals_safe globals )) (PreH17 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH18 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH19 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_fp_relative_address_code (retval)))) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (globals = (cm_program_globals (p))) ” 
  &&  “ (cm_binding_valid p f scope_pre slot_pre ) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) )
) \/
(
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (zp: Z) (zl: Z) (retval: Z) (PreH1 : ((cm_type_encode ((cm_function_ret (f)))) <= INT_MAX)) (PreH2 : ((cm_program_main (p)) <= INT_MAX)) (PreH3 : ((cm_type_encode ((cm_function_ret (f)))) >= INT_MIN)) (PreH4 : ((cm_program_main (p)) >= INT_MIN)) (PreH5 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH6 : (0 <= slot_pre)) (PreH7 : (retval = (8 + (cm_rep_member_prefix ((cm_function_params (f))) (slot_pre)) ))) (PreH8 : (scope_pre <> 1)) (PreH9 : (scope_pre <> 0)) (PreH10 : (program_pre <> 0)) (PreH11 : (fn_pre <> 0)) (PreH12 : (0 <= slot_pre)) (PreH13 : (cm_wf_program policy cg p )) (PreH14 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH15 : (structs = (cm_program_structs (p)))) (PreH16 : (globals = (cm_program_globals (p)))) (PreH17 : (cm_binding_valid p f scope_pre slot_pre )) (PreH18 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH19 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH20 : (cm_rep_globals_safe globals )) (PreH21 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH22 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH23 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_fp_relative_address_code (retval)))) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) )
).

Definition cm_emit_binding_address_return_wit_3_split_goal_spatial := 
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (zp: Z) (zl: Z) (retval: Z) (PreH1 : ((cm_type_encode ((cm_function_ret (f)))) <= INT_MAX)) (PreH2 : ((cm_program_main (p)) <= INT_MAX)) (PreH3 : ((cm_type_encode ((cm_function_ret (f)))) >= INT_MIN)) (PreH4 : ((cm_program_main (p)) >= INT_MIN)) (PreH5 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH6 : (0 <= slot_pre)) (PreH7 : (retval = (8 + (cm_rep_member_prefix ((cm_function_params (f))) (slot_pre)) ))) (PreH8 : (scope_pre <> 1)) (PreH9 : (scope_pre <> 0)) (PreH10 : (program_pre <> 0)) (PreH11 : (fn_pre <> 0)) (PreH12 : (0 <= slot_pre)) (PreH13 : (cm_wf_program policy cg p )) (PreH14 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH15 : (structs = (cm_program_structs (p)))) (PreH16 : (globals = (cm_program_globals (p)))) (PreH17 : (cm_binding_valid p f scope_pre slot_pre )) (PreH18 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH19 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH20 : (cm_rep_globals_safe globals )) (PreH21 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH22 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH23 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_fp_relative_address_code (retval)))) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) )
.

Definition cm_emit_binding_address_partial_solve_wit_1_pure := 
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (zp: Z) (zl: Z) (PreH1 : (scope_pre = 0)) (PreH2 : (program_pre <> 0)) (PreH3 : (fn_pre <> 0)) (PreH4 : (0 <= slot_pre)) (PreH5 : (cm_wf_program policy cg p )) (PreH6 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH7 : (structs = (cm_program_structs (p)))) (PreH8 : (globals = (cm_program_globals (p)))) (PreH9 : (cm_binding_valid p f scope_pre slot_pre )) (PreH10 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH11 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH12 : (cm_rep_globals_safe globals )) (PreH13 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH14 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH15 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  ((( &( "address" ) )) # Int64  |->_)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "scope" ) )) # Int  |-> scope_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (0 <= slot_pre) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ”
.

Definition cm_emit_binding_address_partial_solve_wit_1_aux := 
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (zp: Z) (zl: Z) (PreH1 : (scope_pre = 0)) (PreH2 : (program_pre <> 0)) (PreH3 : (fn_pre <> 0)) (PreH4 : (0 <= slot_pre)) (PreH5 : (cm_wf_program policy cg p )) (PreH6 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH7 : (structs = (cm_program_structs (p)))) (PreH8 : (globals = (cm_program_globals (p)))) (PreH9 : (cm_binding_valid p f scope_pre slot_pre )) (PreH10 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH11 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH12 : (cm_rep_globals_safe globals )) (PreH13 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH14 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH15 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (0 <= slot_pre) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (scope_pre = 0) ” 
  &&  “ (program_pre <> 0) ” 
  &&  “ (fn_pre <> 0) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (globals = (cm_program_globals (p))) ” 
  &&  “ (cm_binding_valid p f scope_pre slot_pre ) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity) ”
  &&  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
.

Definition cm_emit_binding_address_partial_solve_wit_1 := cm_emit_binding_address_partial_solve_wit_1_pure -> cm_emit_binding_address_partial_solve_wit_1_aux.

Definition cm_emit_binding_address_partial_solve_wit_2_pure := 
(
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (zp: Z) (zl: Z) (retval: Z) (PreH1 : (0 <= slot_pre)) (PreH2 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH3 : (retval = (cm_rep_global_address ((cm_program_globals (p))) (slot_pre)))) (PreH4 : (16 <= retval)) (PreH5 : (retval <= 1048576)) (PreH6 : (scope_pre = 0)) (PreH7 : (program_pre <> 0)) (PreH8 : (fn_pre <> 0)) (PreH9 : (0 <= slot_pre)) (PreH10 : (cm_wf_program policy cg p )) (PreH11 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH12 : (structs = (cm_program_structs (p)))) (PreH13 : (globals = (cm_program_globals (p)))) (PreH14 : (cm_binding_valid p f scope_pre slot_pre )) (PreH15 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH16 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH17 : (cm_rep_globals_safe globals )) (PreH18 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH19 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH20 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  ((( &( "address" ) )) # Int64  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "scope" ) )) # Int  |-> scope_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (((Zlength (done)) + 1 ) <= capacity) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ” 
  &&  “ (0 = (tvm_opcode_code (TVMPushOp))) ”
) \/
(
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (zp: Z) (zl: Z) (retval: Z) (PreH1 : (retval <= INT64_MAX)) (PreH2 : (retval >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_function_ret (f)))) <= INT_MAX)) (PreH4 : ((cm_program_main (p)) <= INT_MAX)) (PreH5 : (slot_pre <= INT_MAX)) (PreH6 : (scope_pre <= INT_MAX)) (PreH7 : ((cm_type_encode ((cm_function_ret (f)))) >= INT_MIN)) (PreH8 : ((cm_program_main (p)) >= INT_MIN)) (PreH9 : (slot_pre >= INT_MIN)) (PreH10 : (scope_pre >= INT_MIN)) (PreH11 : (0 <= slot_pre)) (PreH12 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH13 : (retval = (cm_rep_global_address ((cm_program_globals (p))) (slot_pre)))) (PreH14 : (16 <= retval)) (PreH15 : (retval <= 1048576)) (PreH16 : (scope_pre = 0)) (PreH17 : (program_pre <> 0)) (PreH18 : (fn_pre <> 0)) (PreH19 : (0 <= slot_pre)) (PreH20 : (cm_wf_program policy cg p )) (PreH21 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH22 : (structs = (cm_program_structs (p)))) (PreH23 : (globals = (cm_program_globals (p)))) (PreH24 : (cm_binding_valid p f scope_pre slot_pre )) (PreH25 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH26 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH27 : (cm_rep_globals_safe globals )) (PreH28 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH29 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH30 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  ((( &( "address" ) )) # Int64  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "scope" ) )) # Int  |-> scope_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ” 
  &&  “ (((Zlength (done)) + 1 ) <= capacity) ”
).

Definition cm_emit_binding_address_partial_solve_wit_2_pure_split_goal_1 := 
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (zp: Z) (zl: Z) (retval: Z) (PreH1 : (retval <= INT64_MAX)) (PreH2 : (retval >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_function_ret (f)))) <= INT_MAX)) (PreH4 : ((cm_program_main (p)) <= INT_MAX)) (PreH5 : (slot_pre <= INT_MAX)) (PreH6 : (scope_pre <= INT_MAX)) (PreH7 : ((cm_type_encode ((cm_function_ret (f)))) >= INT_MIN)) (PreH8 : ((cm_program_main (p)) >= INT_MIN)) (PreH9 : (slot_pre >= INT_MIN)) (PreH10 : (scope_pre >= INT_MIN)) (PreH11 : (0 <= slot_pre)) (PreH12 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH13 : (retval = (cm_rep_global_address ((cm_program_globals (p))) (slot_pre)))) (PreH14 : (16 <= retval)) (PreH15 : (retval <= 1048576)) (PreH16 : (scope_pre = 0)) (PreH17 : (program_pre <> 0)) (PreH18 : (fn_pre <> 0)) (PreH19 : (0 <= slot_pre)) (PreH20 : (cm_wf_program policy cg p )) (PreH21 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH22 : (structs = (cm_program_structs (p)))) (PreH23 : (globals = (cm_program_globals (p)))) (PreH24 : (cm_binding_valid p f scope_pre slot_pre )) (PreH25 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH26 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH27 : (cm_rep_globals_safe globals )) (PreH28 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH29 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH30 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  ((( &( "address" ) )) # Int64  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "scope" ) )) # Int  |-> scope_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ”
.

Definition cm_emit_binding_address_partial_solve_wit_2_pure_split_goal_2 := 
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (zp: Z) (zl: Z) (retval: Z) (PreH1 : (retval <= INT64_MAX)) (PreH2 : (retval >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_function_ret (f)))) <= INT_MAX)) (PreH4 : ((cm_program_main (p)) <= INT_MAX)) (PreH5 : (slot_pre <= INT_MAX)) (PreH6 : (scope_pre <= INT_MAX)) (PreH7 : ((cm_type_encode ((cm_function_ret (f)))) >= INT_MIN)) (PreH8 : ((cm_program_main (p)) >= INT_MIN)) (PreH9 : (slot_pre >= INT_MIN)) (PreH10 : (scope_pre >= INT_MIN)) (PreH11 : (0 <= slot_pre)) (PreH12 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH13 : (retval = (cm_rep_global_address ((cm_program_globals (p))) (slot_pre)))) (PreH14 : (16 <= retval)) (PreH15 : (retval <= 1048576)) (PreH16 : (scope_pre = 0)) (PreH17 : (program_pre <> 0)) (PreH18 : (fn_pre <> 0)) (PreH19 : (0 <= slot_pre)) (PreH20 : (cm_wf_program policy cg p )) (PreH21 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH22 : (structs = (cm_program_structs (p)))) (PreH23 : (globals = (cm_program_globals (p)))) (PreH24 : (cm_binding_valid p f scope_pre slot_pre )) (PreH25 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH26 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH27 : (cm_rep_globals_safe globals )) (PreH28 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH29 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH30 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  ((( &( "address" ) )) # Int64  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "scope" ) )) # Int  |-> scope_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ”
.

Definition cm_emit_binding_address_partial_solve_wit_2_pure_split_goal_3 := 
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (zp: Z) (zl: Z) (retval: Z) (PreH1 : (retval <= INT64_MAX)) (PreH2 : (retval >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_function_ret (f)))) <= INT_MAX)) (PreH4 : ((cm_program_main (p)) <= INT_MAX)) (PreH5 : (slot_pre <= INT_MAX)) (PreH6 : (scope_pre <= INT_MAX)) (PreH7 : ((cm_type_encode ((cm_function_ret (f)))) >= INT_MIN)) (PreH8 : ((cm_program_main (p)) >= INT_MIN)) (PreH9 : (slot_pre >= INT_MIN)) (PreH10 : (scope_pre >= INT_MIN)) (PreH11 : (0 <= slot_pre)) (PreH12 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH13 : (retval = (cm_rep_global_address ((cm_program_globals (p))) (slot_pre)))) (PreH14 : (16 <= retval)) (PreH15 : (retval <= 1048576)) (PreH16 : (scope_pre = 0)) (PreH17 : (program_pre <> 0)) (PreH18 : (fn_pre <> 0)) (PreH19 : (0 <= slot_pre)) (PreH20 : (cm_wf_program policy cg p )) (PreH21 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH22 : (structs = (cm_program_structs (p)))) (PreH23 : (globals = (cm_program_globals (p)))) (PreH24 : (cm_binding_valid p f scope_pre slot_pre )) (PreH25 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH26 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH27 : (cm_rep_globals_safe globals )) (PreH28 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH29 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH30 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  ((( &( "address" ) )) # Int64  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "scope" ) )) # Int  |-> scope_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (((Zlength (done)) + 1 ) <= capacity) ”
.

Definition cm_emit_binding_address_partial_solve_wit_2_aux := 
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (zp: Z) (zl: Z) (retval: Z) (PreH1 : (0 <= slot_pre)) (PreH2 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH3 : (retval = (cm_rep_global_address ((cm_program_globals (p))) (slot_pre)))) (PreH4 : (16 <= retval)) (PreH5 : (retval <= 1048576)) (PreH6 : (scope_pre = 0)) (PreH7 : (program_pre <> 0)) (PreH8 : (fn_pre <> 0)) (PreH9 : (0 <= slot_pre)) (PreH10 : (cm_wf_program policy cg p )) (PreH11 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH12 : (structs = (cm_program_structs (p)))) (PreH13 : (globals = (cm_program_globals (p)))) (PreH14 : (cm_binding_valid p f scope_pre slot_pre )) (PreH15 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH16 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH17 : (cm_rep_globals_safe globals )) (PreH18 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH19 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH20 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (((Zlength (done)) + 1 ) <= capacity) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ” 
  &&  “ (0 = (tvm_opcode_code (TVMPushOp))) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (retval = (cm_rep_global_address ((cm_program_globals (p))) (slot_pre))) ” 
  &&  “ (16 <= retval) ” 
  &&  “ (retval <= 1048576) ” 
  &&  “ (scope_pre = 0) ” 
  &&  “ (program_pre <> 0) ” 
  &&  “ (fn_pre <> 0) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (globals = (cm_program_globals (p))) ” 
  &&  “ (cm_binding_valid p f scope_pre slot_pre ) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity) ”
  &&  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
.

Definition cm_emit_binding_address_partial_solve_wit_2 := cm_emit_binding_address_partial_solve_wit_2_pure -> cm_emit_binding_address_partial_solve_wit_2_aux.

Definition cm_emit_binding_address_partial_solve_wit_3_pure := 
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (zp: Z) (zl: Z) (PreH1 : (scope_pre = 1)) (PreH2 : (scope_pre <> 0)) (PreH3 : (program_pre <> 0)) (PreH4 : (fn_pre <> 0)) (PreH5 : (0 <= slot_pre)) (PreH6 : (cm_wf_program policy cg p )) (PreH7 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH8 : (structs = (cm_program_structs (p)))) (PreH9 : (globals = (cm_program_globals (p)))) (PreH10 : (cm_binding_valid p f scope_pre slot_pre )) (PreH11 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH12 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH13 : (cm_rep_globals_safe globals )) (PreH14 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH15 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH16 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  ((( &( "offset" ) )) # Int64  |->_)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "scope" ) )) # Int  |-> scope_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (0 <= slot_pre) ”
.

Definition cm_emit_binding_address_partial_solve_wit_3_aux := 
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (zp: Z) (zl: Z) (PreH1 : (scope_pre = 1)) (PreH2 : (scope_pre <> 0)) (PreH3 : (program_pre <> 0)) (PreH4 : (fn_pre <> 0)) (PreH5 : (0 <= slot_pre)) (PreH6 : (cm_wf_program policy cg p )) (PreH7 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH8 : (structs = (cm_program_structs (p)))) (PreH9 : (globals = (cm_program_globals (p)))) (PreH10 : (cm_binding_valid p f scope_pre slot_pre )) (PreH11 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH12 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH13 : (cm_rep_globals_safe globals )) (PreH14 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH15 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH16 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ (scope_pre = 1) ” 
  &&  “ (scope_pre <> 0) ” 
  &&  “ (program_pre <> 0) ” 
  &&  “ (fn_pre <> 0) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (globals = (cm_program_globals (p))) ” 
  &&  “ (cm_binding_valid p f scope_pre slot_pre ) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity) ”
  &&  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
.

Definition cm_emit_binding_address_partial_solve_wit_3 := cm_emit_binding_address_partial_solve_wit_3_pure -> cm_emit_binding_address_partial_solve_wit_3_aux.

Definition cm_emit_binding_address_partial_solve_wit_4_pure := 
(
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (zp: Z) (zl: Z) (retval: Z) (PreH1 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH2 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH3 : (0 <= slot_pre)) (PreH4 : (retval = ((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_member_prefix ((cm_function_locals (f))) (slot_pre)) ))) (PreH5 : (scope_pre = 1)) (PreH6 : (scope_pre <> 0)) (PreH7 : (program_pre <> 0)) (PreH8 : (fn_pre <> 0)) (PreH9 : (0 <= slot_pre)) (PreH10 : (cm_wf_program policy cg p )) (PreH11 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH12 : (structs = (cm_program_structs (p)))) (PreH13 : (globals = (cm_program_globals (p)))) (PreH14 : (cm_binding_valid p f scope_pre slot_pre )) (PreH15 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH16 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH17 : (cm_rep_globals_safe globals )) (PreH18 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH19 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH20 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  ((( &( "offset" ) )) # Int64  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "scope" ) )) # Int  |-> scope_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (((Zlength (done)) + (Zlength ((cm_fp_relative_address_code (retval)))) ) <= capacity) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_fp_relative_address_code (((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_member_prefix ((cm_function_locals (f))) (slot_pre)) ))))) ) <= capacity) ”
) \/
(
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (zp: Z) (zl: Z) (retval: Z) (PreH1 : (retval <= INT64_MAX)) (PreH2 : (retval >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_function_ret (f)))) <= INT_MAX)) (PreH4 : ((cm_program_main (p)) <= INT_MAX)) (PreH5 : (slot_pre <= INT_MAX)) (PreH6 : (scope_pre <= INT_MAX)) (PreH7 : ((cm_type_encode ((cm_function_ret (f)))) >= INT_MIN)) (PreH8 : ((cm_program_main (p)) >= INT_MIN)) (PreH9 : (slot_pre >= INT_MIN)) (PreH10 : (scope_pre >= INT_MIN)) (PreH11 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH12 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH13 : (0 <= slot_pre)) (PreH14 : (retval = ((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_member_prefix ((cm_function_locals (f))) (slot_pre)) ))) (PreH15 : (scope_pre = 1)) (PreH16 : (scope_pre <> 0)) (PreH17 : (program_pre <> 0)) (PreH18 : (fn_pre <> 0)) (PreH19 : (0 <= slot_pre)) (PreH20 : (cm_wf_program policy cg p )) (PreH21 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH22 : (structs = (cm_program_structs (p)))) (PreH23 : (globals = (cm_program_globals (p)))) (PreH24 : (cm_binding_valid p f scope_pre slot_pre )) (PreH25 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH26 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH27 : (cm_rep_globals_safe globals )) (PreH28 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH29 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH30 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  ((( &( "offset" ) )) # Int64  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "scope" ) )) # Int  |-> scope_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (((Zlength (done)) + (Zlength ((cm_fp_relative_address_code (retval)))) ) <= capacity) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_fp_relative_address_code (retval)))) ) <= capacity) ”
).

Definition cm_emit_binding_address_partial_solve_wit_4_pure_split_goal_1 := 
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (zp: Z) (zl: Z) (retval: Z) (PreH1 : (retval <= INT64_MAX)) (PreH2 : (retval >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_function_ret (f)))) <= INT_MAX)) (PreH4 : ((cm_program_main (p)) <= INT_MAX)) (PreH5 : (slot_pre <= INT_MAX)) (PreH6 : (scope_pre <= INT_MAX)) (PreH7 : ((cm_type_encode ((cm_function_ret (f)))) >= INT_MIN)) (PreH8 : ((cm_program_main (p)) >= INT_MIN)) (PreH9 : (slot_pre >= INT_MIN)) (PreH10 : (scope_pre >= INT_MIN)) (PreH11 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH12 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH13 : (0 <= slot_pre)) (PreH14 : (retval = ((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_member_prefix ((cm_function_locals (f))) (slot_pre)) ))) (PreH15 : (scope_pre = 1)) (PreH16 : (scope_pre <> 0)) (PreH17 : (program_pre <> 0)) (PreH18 : (fn_pre <> 0)) (PreH19 : (0 <= slot_pre)) (PreH20 : (cm_wf_program policy cg p )) (PreH21 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH22 : (structs = (cm_program_structs (p)))) (PreH23 : (globals = (cm_program_globals (p)))) (PreH24 : (cm_binding_valid p f scope_pre slot_pre )) (PreH25 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH26 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH27 : (cm_rep_globals_safe globals )) (PreH28 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH29 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH30 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  ((( &( "offset" ) )) # Int64  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "scope" ) )) # Int  |-> scope_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (((Zlength (done)) + (Zlength ((cm_fp_relative_address_code (retval)))) ) <= capacity) ”
.

Definition cm_emit_binding_address_partial_solve_wit_4_pure_split_goal_2 := 
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (zp: Z) (zl: Z) (retval: Z) (PreH1 : (retval <= INT64_MAX)) (PreH2 : (retval >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_function_ret (f)))) <= INT_MAX)) (PreH4 : ((cm_program_main (p)) <= INT_MAX)) (PreH5 : (slot_pre <= INT_MAX)) (PreH6 : (scope_pre <= INT_MAX)) (PreH7 : ((cm_type_encode ((cm_function_ret (f)))) >= INT_MIN)) (PreH8 : ((cm_program_main (p)) >= INT_MIN)) (PreH9 : (slot_pre >= INT_MIN)) (PreH10 : (scope_pre >= INT_MIN)) (PreH11 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH12 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH13 : (0 <= slot_pre)) (PreH14 : (retval = ((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_member_prefix ((cm_function_locals (f))) (slot_pre)) ))) (PreH15 : (scope_pre = 1)) (PreH16 : (scope_pre <> 0)) (PreH17 : (program_pre <> 0)) (PreH18 : (fn_pre <> 0)) (PreH19 : (0 <= slot_pre)) (PreH20 : (cm_wf_program policy cg p )) (PreH21 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH22 : (structs = (cm_program_structs (p)))) (PreH23 : (globals = (cm_program_globals (p)))) (PreH24 : (cm_binding_valid p f scope_pre slot_pre )) (PreH25 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH26 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH27 : (cm_rep_globals_safe globals )) (PreH28 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH29 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH30 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  ((( &( "offset" ) )) # Int64  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "scope" ) )) # Int  |-> scope_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (((Zlength (done)) + (Zlength ((cm_fp_relative_address_code (retval)))) ) <= capacity) ”
.

Definition cm_emit_binding_address_partial_solve_wit_4_aux := 
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (zp: Z) (zl: Z) (retval: Z) (PreH1 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH2 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH3 : (0 <= slot_pre)) (PreH4 : (retval = ((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_member_prefix ((cm_function_locals (f))) (slot_pre)) ))) (PreH5 : (scope_pre = 1)) (PreH6 : (scope_pre <> 0)) (PreH7 : (program_pre <> 0)) (PreH8 : (fn_pre <> 0)) (PreH9 : (0 <= slot_pre)) (PreH10 : (cm_wf_program policy cg p )) (PreH11 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH12 : (structs = (cm_program_structs (p)))) (PreH13 : (globals = (cm_program_globals (p)))) (PreH14 : (cm_binding_valid p f scope_pre slot_pre )) (PreH15 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH16 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH17 : (cm_rep_globals_safe globals )) (PreH18 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH19 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH20 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (((Zlength (done)) + (Zlength ((cm_fp_relative_address_code (retval)))) ) <= capacity) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_fp_relative_address_code (((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_member_prefix ((cm_function_locals (f))) (slot_pre)) ))))) ) <= capacity) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ (retval = ((8 + (cm_rep_members_size ((cm_function_params (f)))) ) + (cm_rep_member_prefix ((cm_function_locals (f))) (slot_pre)) )) ” 
  &&  “ (scope_pre = 1) ” 
  &&  “ (scope_pre <> 0) ” 
  &&  “ (program_pre <> 0) ” 
  &&  “ (fn_pre <> 0) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (globals = (cm_program_globals (p))) ” 
  &&  “ (cm_binding_valid p f scope_pre slot_pre ) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity) ”
  &&  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
.

Definition cm_emit_binding_address_partial_solve_wit_4 := cm_emit_binding_address_partial_solve_wit_4_pure -> cm_emit_binding_address_partial_solve_wit_4_aux.

Definition cm_emit_binding_address_partial_solve_wit_5_pure := 
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (zp: Z) (zl: Z) (PreH1 : (scope_pre <> 1)) (PreH2 : (scope_pre <> 0)) (PreH3 : (program_pre <> 0)) (PreH4 : (fn_pre <> 0)) (PreH5 : (0 <= slot_pre)) (PreH6 : (cm_wf_program policy cg p )) (PreH7 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH8 : (structs = (cm_program_structs (p)))) (PreH9 : (globals = (cm_program_globals (p)))) (PreH10 : (cm_binding_valid p f scope_pre slot_pre )) (PreH11 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH12 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH13 : (cm_rep_globals_safe globals )) (PreH14 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH15 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH16 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  ((( &( "offset" ) )) # Int64  |->_)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "scope" ) )) # Int  |-> scope_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (0 <= slot_pre) ”
.

Definition cm_emit_binding_address_partial_solve_wit_5_aux := 
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (zp: Z) (zl: Z) (PreH1 : (scope_pre <> 1)) (PreH2 : (scope_pre <> 0)) (PreH3 : (program_pre <> 0)) (PreH4 : (fn_pre <> 0)) (PreH5 : (0 <= slot_pre)) (PreH6 : (cm_wf_program policy cg p )) (PreH7 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH8 : (structs = (cm_program_structs (p)))) (PreH9 : (globals = (cm_program_globals (p)))) (PreH10 : (cm_binding_valid p f scope_pre slot_pre )) (PreH11 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH12 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH13 : (cm_rep_globals_safe globals )) (PreH14 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH15 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH16 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ (scope_pre <> 1) ” 
  &&  “ (scope_pre <> 0) ” 
  &&  “ (program_pre <> 0) ” 
  &&  “ (fn_pre <> 0) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (globals = (cm_program_globals (p))) ” 
  &&  “ (cm_binding_valid p f scope_pre slot_pre ) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity) ”
  &&  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
.

Definition cm_emit_binding_address_partial_solve_wit_5 := cm_emit_binding_address_partial_solve_wit_5_pure -> cm_emit_binding_address_partial_solve_wit_5_aux.

Definition cm_emit_binding_address_partial_solve_wit_6_pure := 
(
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (zp: Z) (zl: Z) (retval: Z) (PreH1 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH2 : (0 <= slot_pre)) (PreH3 : (retval = (8 + (cm_rep_member_prefix ((cm_function_params (f))) (slot_pre)) ))) (PreH4 : (scope_pre <> 1)) (PreH5 : (scope_pre <> 0)) (PreH6 : (program_pre <> 0)) (PreH7 : (fn_pre <> 0)) (PreH8 : (0 <= slot_pre)) (PreH9 : (cm_wf_program policy cg p )) (PreH10 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH11 : (structs = (cm_program_structs (p)))) (PreH12 : (globals = (cm_program_globals (p)))) (PreH13 : (cm_binding_valid p f scope_pre slot_pre )) (PreH14 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH15 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH16 : (cm_rep_globals_safe globals )) (PreH17 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH18 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH19 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  ((( &( "offset" ) )) # Int64  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "scope" ) )) # Int  |-> scope_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (((Zlength (done)) + (Zlength ((cm_fp_relative_address_code (retval)))) ) <= capacity) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_fp_relative_address_code ((8 + (cm_rep_member_prefix ((cm_function_params (f))) (slot_pre)) ))))) ) <= capacity) ”
) \/
(
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (zp: Z) (zl: Z) (retval: Z) (PreH1 : (retval <= INT64_MAX)) (PreH2 : (retval >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_function_ret (f)))) <= INT_MAX)) (PreH4 : ((cm_program_main (p)) <= INT_MAX)) (PreH5 : (slot_pre <= INT_MAX)) (PreH6 : (scope_pre <= INT_MAX)) (PreH7 : ((cm_type_encode ((cm_function_ret (f)))) >= INT_MIN)) (PreH8 : ((cm_program_main (p)) >= INT_MIN)) (PreH9 : (slot_pre >= INT_MIN)) (PreH10 : (scope_pre >= INT_MIN)) (PreH11 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH12 : (0 <= slot_pre)) (PreH13 : (retval = (8 + (cm_rep_member_prefix ((cm_function_params (f))) (slot_pre)) ))) (PreH14 : (scope_pre <> 1)) (PreH15 : (scope_pre <> 0)) (PreH16 : (program_pre <> 0)) (PreH17 : (fn_pre <> 0)) (PreH18 : (0 <= slot_pre)) (PreH19 : (cm_wf_program policy cg p )) (PreH20 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH21 : (structs = (cm_program_structs (p)))) (PreH22 : (globals = (cm_program_globals (p)))) (PreH23 : (cm_binding_valid p f scope_pre slot_pre )) (PreH24 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH25 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH26 : (cm_rep_globals_safe globals )) (PreH27 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH28 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH29 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  ((( &( "offset" ) )) # Int64  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "scope" ) )) # Int  |-> scope_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (((Zlength (done)) + (Zlength ((cm_fp_relative_address_code (retval)))) ) <= capacity) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_fp_relative_address_code (retval)))) ) <= capacity) ”
).

Definition cm_emit_binding_address_partial_solve_wit_6_pure_split_goal_1 := 
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (zp: Z) (zl: Z) (retval: Z) (PreH1 : (retval <= INT64_MAX)) (PreH2 : (retval >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_function_ret (f)))) <= INT_MAX)) (PreH4 : ((cm_program_main (p)) <= INT_MAX)) (PreH5 : (slot_pre <= INT_MAX)) (PreH6 : (scope_pre <= INT_MAX)) (PreH7 : ((cm_type_encode ((cm_function_ret (f)))) >= INT_MIN)) (PreH8 : ((cm_program_main (p)) >= INT_MIN)) (PreH9 : (slot_pre >= INT_MIN)) (PreH10 : (scope_pre >= INT_MIN)) (PreH11 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH12 : (0 <= slot_pre)) (PreH13 : (retval = (8 + (cm_rep_member_prefix ((cm_function_params (f))) (slot_pre)) ))) (PreH14 : (scope_pre <> 1)) (PreH15 : (scope_pre <> 0)) (PreH16 : (program_pre <> 0)) (PreH17 : (fn_pre <> 0)) (PreH18 : (0 <= slot_pre)) (PreH19 : (cm_wf_program policy cg p )) (PreH20 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH21 : (structs = (cm_program_structs (p)))) (PreH22 : (globals = (cm_program_globals (p)))) (PreH23 : (cm_binding_valid p f scope_pre slot_pre )) (PreH24 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH25 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH26 : (cm_rep_globals_safe globals )) (PreH27 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH28 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH29 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  ((( &( "offset" ) )) # Int64  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "scope" ) )) # Int  |-> scope_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (((Zlength (done)) + (Zlength ((cm_fp_relative_address_code (retval)))) ) <= capacity) ”
.

Definition cm_emit_binding_address_partial_solve_wit_6_pure_split_goal_2 := 
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (zp: Z) (zl: Z) (retval: Z) (PreH1 : (retval <= INT64_MAX)) (PreH2 : (retval >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_function_ret (f)))) <= INT_MAX)) (PreH4 : ((cm_program_main (p)) <= INT_MAX)) (PreH5 : (slot_pre <= INT_MAX)) (PreH6 : (scope_pre <= INT_MAX)) (PreH7 : ((cm_type_encode ((cm_function_ret (f)))) >= INT_MIN)) (PreH8 : ((cm_program_main (p)) >= INT_MIN)) (PreH9 : (slot_pre >= INT_MIN)) (PreH10 : (scope_pre >= INT_MIN)) (PreH11 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH12 : (0 <= slot_pre)) (PreH13 : (retval = (8 + (cm_rep_member_prefix ((cm_function_params (f))) (slot_pre)) ))) (PreH14 : (scope_pre <> 1)) (PreH15 : (scope_pre <> 0)) (PreH16 : (program_pre <> 0)) (PreH17 : (fn_pre <> 0)) (PreH18 : (0 <= slot_pre)) (PreH19 : (cm_wf_program policy cg p )) (PreH20 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH21 : (structs = (cm_program_structs (p)))) (PreH22 : (globals = (cm_program_globals (p)))) (PreH23 : (cm_binding_valid p f scope_pre slot_pre )) (PreH24 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH25 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH26 : (cm_rep_globals_safe globals )) (PreH27 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH28 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH29 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  ((( &( "offset" ) )) # Int64  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "scope" ) )) # Int  |-> scope_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (((Zlength (done)) + (Zlength ((cm_fp_relative_address_code (retval)))) ) <= capacity) ”
.

Definition cm_emit_binding_address_partial_solve_wit_6_aux := 
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (zp: Z) (zl: Z) (retval: Z) (PreH1 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH2 : (0 <= slot_pre)) (PreH3 : (retval = (8 + (cm_rep_member_prefix ((cm_function_params (f))) (slot_pre)) ))) (PreH4 : (scope_pre <> 1)) (PreH5 : (scope_pre <> 0)) (PreH6 : (program_pre <> 0)) (PreH7 : (fn_pre <> 0)) (PreH8 : (0 <= slot_pre)) (PreH9 : (cm_wf_program policy cg p )) (PreH10 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH11 : (structs = (cm_program_structs (p)))) (PreH12 : (globals = (cm_program_globals (p)))) (PreH13 : (cm_binding_valid p f scope_pre slot_pre )) (PreH14 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH15 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH16 : (cm_rep_globals_safe globals )) (PreH17 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH18 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH19 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (((Zlength (done)) + (Zlength ((cm_fp_relative_address_code (retval)))) ) <= capacity) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_fp_relative_address_code ((8 + (cm_rep_member_prefix ((cm_function_params (f))) (slot_pre)) ))))) ) <= capacity) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ (retval = (8 + (cm_rep_member_prefix ((cm_function_params (f))) (slot_pre)) )) ” 
  &&  “ (scope_pre <> 1) ” 
  &&  “ (scope_pre <> 0) ” 
  &&  “ (program_pre <> 0) ” 
  &&  “ (fn_pre <> 0) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (globals = (cm_program_globals (p))) ” 
  &&  “ (cm_binding_valid p f scope_pre slot_pre ) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity) ”
  &&  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
.

Definition cm_emit_binding_address_partial_solve_wit_6 := cm_emit_binding_address_partial_solve_wit_6_pure -> cm_emit_binding_address_partial_solve_wit_6_aux.

(*----- Function cm_emit_binding_address_plan -----*)

Definition cm_emit_binding_address_plan_entail_wit_1 := 
(
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (tail: (@list tvm_inst)) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH3 : (structs = (cm_program_structs (p)))) (PreH4 : (globals = (cm_program_globals (p)))) (PreH5 : (cm_binding_valid p f scope_pre slot_pre )) (PreH6 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH7 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH8 : (cm_rep_globals_safe globals )) (PreH9 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH10 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre))) (tail)) )
|--
  “ (((Zlength ((app (done) ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))))) + (Zlength (tail)) ) <= capacity) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (globals = (cm_program_globals (p))) ” 
  &&  “ (cm_binding_valid p f scope_pre slot_pre ) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
) \/
(
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (tail: (@list tvm_inst)) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH3 : (structs = (cm_program_structs (p)))) (PreH4 : (globals = (cm_program_globals (p)))) (PreH5 : (cm_binding_valid p f scope_pre slot_pre )) (PreH6 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH7 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH8 : (cm_rep_globals_safe globals )) (PreH9 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH10 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre))) (tail)) )
|--
  “ (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity) ” 
  &&  “ (((Zlength ((app (done) ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))))) + (Zlength (tail)) ) <= capacity) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
).

Definition cm_emit_binding_address_plan_entail_wit_1_split_goal_1 := 
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (tail: (@list tvm_inst)) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH3 : (structs = (cm_program_structs (p)))) (PreH4 : (globals = (cm_program_globals (p)))) (PreH5 : (cm_binding_valid p f scope_pre slot_pre )) (PreH6 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH7 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH8 : (cm_rep_globals_safe globals )) (PreH9 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH10 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre))) (tail)) )
|--
  “ (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity) ”
.

Definition cm_emit_binding_address_plan_entail_wit_1_split_goal_2 := 
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (tail: (@list tvm_inst)) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH3 : (structs = (cm_program_structs (p)))) (PreH4 : (globals = (cm_program_globals (p)))) (PreH5 : (cm_binding_valid p f scope_pre slot_pre )) (PreH6 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH7 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH8 : (cm_rep_globals_safe globals )) (PreH9 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH10 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre))) (tail)) )
|--
  “ (((Zlength ((app (done) ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))))) + (Zlength (tail)) ) <= capacity) ”
.

Definition cm_emit_binding_address_plan_entail_wit_1_split_goal_spatial := 
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (tail: (@list tvm_inst)) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH3 : (structs = (cm_program_structs (p)))) (PreH4 : (globals = (cm_program_globals (p)))) (PreH5 : (cm_binding_valid p f scope_pre slot_pre )) (PreH6 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH7 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH8 : (cm_rep_globals_safe globals )) (PreH9 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH10 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre))) (tail)) )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
.

Definition cm_emit_binding_address_plan_return_wit_1 := 
(
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (tail: (@list tvm_inst)) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH3 : (structs = (cm_program_structs (p)))) (PreH4 : (globals = (cm_program_globals (p)))) (PreH5 : (cm_binding_valid p f scope_pre slot_pre )) (PreH6 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH7 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH8 : (cm_rep_globals_safe globals )) (PreH9 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH10 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH11 : (((Zlength ((app (done) ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))))) + (Zlength (tail)) ) <= capacity)) (PreH12 : (cm_wf_program policy cg p )) (PreH13 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH14 : (structs = (cm_program_structs (p)))) (PreH15 : (globals = (cm_program_globals (p)))) (PreH16 : (cm_binding_valid p f scope_pre slot_pre )) (PreH17 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH18 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH19 : (cm_rep_globals_safe globals )) (PreH20 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH21 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH22 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (globals = (cm_program_globals (p))) ” 
  &&  “ (cm_binding_valid p f scope_pre slot_pre ) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) tail )
) \/
(
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (tail: (@list tvm_inst)) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH3 : (structs = (cm_program_structs (p)))) (PreH4 : (globals = (cm_program_globals (p)))) (PreH5 : (cm_binding_valid p f scope_pre slot_pre )) (PreH6 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH7 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH8 : (cm_rep_globals_safe globals )) (PreH9 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH10 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH11 : (((Zlength ((app (done) ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))))) + (Zlength (tail)) ) <= capacity)) (PreH12 : (cm_wf_program policy cg p )) (PreH13 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH14 : (structs = (cm_program_structs (p)))) (PreH15 : (globals = (cm_program_globals (p)))) (PreH16 : (cm_binding_valid p f scope_pre slot_pre )) (PreH17 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH18 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH19 : (cm_rep_globals_safe globals )) (PreH20 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH21 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH22 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) tail )
).

Definition cm_emit_binding_address_plan_return_wit_1_split_goal_spatial := 
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (tail: (@list tvm_inst)) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH3 : (structs = (cm_program_structs (p)))) (PreH4 : (globals = (cm_program_globals (p)))) (PreH5 : (cm_binding_valid p f scope_pre slot_pre )) (PreH6 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH7 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH8 : (cm_rep_globals_safe globals )) (PreH9 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH10 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH11 : (((Zlength ((app (done) ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))))) + (Zlength (tail)) ) <= capacity)) (PreH12 : (cm_wf_program policy cg p )) (PreH13 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH14 : (structs = (cm_program_structs (p)))) (PreH15 : (globals = (cm_program_globals (p)))) (PreH16 : (cm_binding_valid p f scope_pre slot_pre )) (PreH17 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH18 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH19 : (cm_rep_globals_safe globals )) (PreH20 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH21 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH22 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity (app (done) ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) tail )
.

Definition cm_emit_binding_address_plan_partial_solve_wit_1_pure := 
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (tail: (@list tvm_inst)) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (((Zlength ((app (done) ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))))) + (Zlength (tail)) ) <= capacity)) (PreH2 : (cm_wf_program policy cg p )) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (structs = (cm_program_structs (p)))) (PreH5 : (globals = (cm_program_globals (p)))) (PreH6 : (cm_binding_valid p f scope_pre slot_pre )) (PreH7 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH8 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH9 : (cm_rep_globals_safe globals )) (PreH10 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH11 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH12 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "scope" ) )) # Int  |-> scope_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (globals = (cm_program_globals (p))) ” 
  &&  “ (cm_binding_valid p f scope_pre slot_pre ) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity) ”
.

Definition cm_emit_binding_address_plan_partial_solve_wit_1_aux := 
forall (emitter_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (program_pre: Z) (tail: (@list tvm_inst)) (capacity: Z) (out: Z) (done: (@list tvm_inst)) (next: Z) (body: Z) (functions_ptr: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (fid: Z) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (((Zlength ((app (done) ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))))) + (Zlength (tail)) ) <= capacity)) (PreH2 : (cm_wf_program policy cg p )) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (structs = (cm_program_structs (p)))) (PreH5 : (globals = (cm_program_globals (p)))) (PreH6 : (cm_binding_valid p f scope_pre slot_pre )) (PreH7 : (cm_slots_wf structs (cm_function_params (f)) )) (PreH8 : (cm_slots_wf structs (cm_function_locals (f)) )) (PreH9 : (cm_rep_globals_safe globals )) (PreH10 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH11 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH12 : (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (globals = (cm_program_globals (p))) ” 
  &&  “ (cm_binding_valid p f scope_pre slot_pre ) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity) ” 
  &&  “ (((Zlength ((app (done) ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))))) + (Zlength (tail)) ) <= capacity) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (globals = (cm_program_globals (p))) ” 
  &&  “ (cm_binding_valid p f scope_pre slot_pre ) ” 
  &&  “ (cm_slots_wf structs (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf structs (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((Zlength (done)) + (Zlength ((cm_binding_address_code (policy) (p) (fid) (scope_pre) (slot_pre)))) ) <= capacity) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_rep policy p emitter_pre out capacity done )
.

Definition cm_emit_binding_address_plan_partial_solve_wit_1 := cm_emit_binding_address_plan_partial_solve_wit_1_pure -> cm_emit_binding_address_plan_partial_solve_wit_1_aux.

Module Type VC_Correct.


Axiom proof_of_cm_emit_binding_address_safety_wit_1 : cm_emit_binding_address_safety_wit_1.
Axiom proof_of_cm_emit_binding_address_safety_wit_2 : cm_emit_binding_address_safety_wit_2.
Axiom proof_of_cm_emit_binding_address_safety_wit_3 : cm_emit_binding_address_safety_wit_3.
Axiom proof_of_cm_emit_binding_address_entail_wit_1 : cm_emit_binding_address_entail_wit_1.
Axiom proof_of_cm_emit_binding_address_return_wit_1 : cm_emit_binding_address_return_wit_1.
Axiom proof_of_cm_emit_binding_address_return_wit_2 : cm_emit_binding_address_return_wit_2.
Axiom proof_of_cm_emit_binding_address_return_wit_3 : cm_emit_binding_address_return_wit_3.
Axiom proof_of_cm_emit_binding_address_partial_solve_wit_1_pure : cm_emit_binding_address_partial_solve_wit_1_pure.
Axiom proof_of_cm_emit_binding_address_partial_solve_wit_1 : cm_emit_binding_address_partial_solve_wit_1.
Axiom proof_of_cm_emit_binding_address_partial_solve_wit_2_pure : cm_emit_binding_address_partial_solve_wit_2_pure.
Axiom proof_of_cm_emit_binding_address_partial_solve_wit_2 : cm_emit_binding_address_partial_solve_wit_2.
Axiom proof_of_cm_emit_binding_address_partial_solve_wit_3_pure : cm_emit_binding_address_partial_solve_wit_3_pure.
Axiom proof_of_cm_emit_binding_address_partial_solve_wit_3 : cm_emit_binding_address_partial_solve_wit_3.
Axiom proof_of_cm_emit_binding_address_partial_solve_wit_4_pure : cm_emit_binding_address_partial_solve_wit_4_pure.
Axiom proof_of_cm_emit_binding_address_partial_solve_wit_4 : cm_emit_binding_address_partial_solve_wit_4.
Axiom proof_of_cm_emit_binding_address_partial_solve_wit_5_pure : cm_emit_binding_address_partial_solve_wit_5_pure.
Axiom proof_of_cm_emit_binding_address_partial_solve_wit_5 : cm_emit_binding_address_partial_solve_wit_5.
Axiom proof_of_cm_emit_binding_address_partial_solve_wit_6_pure : cm_emit_binding_address_partial_solve_wit_6_pure.
Axiom proof_of_cm_emit_binding_address_partial_solve_wit_6 : cm_emit_binding_address_partial_solve_wit_6.
Axiom proof_of_cm_emit_binding_address_plan_entail_wit_1 : cm_emit_binding_address_plan_entail_wit_1.
Axiom proof_of_cm_emit_binding_address_plan_return_wit_1 : cm_emit_binding_address_plan_return_wit_1.
Axiom proof_of_cm_emit_binding_address_plan_partial_solve_wit_1_pure : cm_emit_binding_address_plan_partial_solve_wit_1_pure.
Axiom proof_of_cm_emit_binding_address_plan_partial_solve_wit_1 : cm_emit_binding_address_plan_partial_solve_wit_1.

End VC_Correct.
