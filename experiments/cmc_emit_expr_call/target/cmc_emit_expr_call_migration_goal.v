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
Require Import SimpleC.EE.QCP_demos_human.cmc_emit_expr_call_migration_lib.
Local Open Scope sac.

(*----- Function cm_emit_args_reload_plan -----*)

Definition cm_emit_args_reload_plan_safety_wit_1 := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (slot_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (args: (@list cm_expr)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= slot_pre)) (PreH2 : ((slot_pre + (Zlength (args)) ) <= temp_limit_pre)) (PreH3 : (0 <= temp_limit_pre)) (PreH4 : (temp_limit_pre <= INT_MAX)) (PreH5 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH6 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH7 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH8 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH9 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH10 : ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX)) ,
  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "temp_limit" ) )) # Int  |-> temp_limit_pre)
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_arg_list_rep arg_pre args )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_args_reload (policy) (p) (fid) (slot_pre) (args))) (tail)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_emit_args_reload_plan_safety_wit_2 := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (slot_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (args: (@list cm_expr)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (np: Z) (ep: Z) (PreH1 : (0 <= slot_pre)) (PreH2 : ((cm_program_structs (p)) = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH5 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (slot_pre)) <= INT_MAX)) (PreH9 : (0 <= (slot_pre + 1 ))) (PreH10 : ((slot_pre + 1 ) <= INT_MAX)) (PreH11 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) <= temp_limit_pre)) (PreH12 : ((cm_temp_offset (policy) (p) (fid) (slot_pre)) <= INT_MAX)) (PreH13 : (arg_pre <> 0)) (PreH14 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH15 : (arg_pre <> 0)) (PreH16 : (0 <= slot_pre)) (PreH17 : ((slot_pre + (Zlength (args)) ) <= temp_limit_pre)) (PreH18 : (0 <= temp_limit_pre)) (PreH19 : (temp_limit_pre <= INT_MAX)) (PreH20 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH21 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH22 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH23 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH24 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH25 : ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_temp_load_code (policy) (p) (fid) (slot_pre)))) (app ((cm_emit_args_reload (policy) (p) (fid) ((slot_pre + 1 )) ((cm_args_tail (args))))) (tail)) )
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "temp_limit" ) )) # Int  |-> temp_limit_pre)
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
|--
  “ ((slot_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (slot_pre + 1 )) ”
.

Definition cm_emit_args_reload_plan_safety_wit_3 := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (slot_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (args: (@list cm_expr)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (np: Z) (ep: Z) (PreH1 : (0 <= slot_pre)) (PreH2 : ((cm_program_structs (p)) = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH5 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (slot_pre)) <= INT_MAX)) (PreH9 : (0 <= (slot_pre + 1 ))) (PreH10 : ((slot_pre + 1 ) <= INT_MAX)) (PreH11 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) <= temp_limit_pre)) (PreH12 : ((cm_temp_offset (policy) (p) (fid) (slot_pre)) <= INT_MAX)) (PreH13 : (arg_pre <> 0)) (PreH14 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH15 : (arg_pre <> 0)) (PreH16 : (0 <= slot_pre)) (PreH17 : ((slot_pre + (Zlength (args)) ) <= temp_limit_pre)) (PreH18 : (0 <= temp_limit_pre)) (PreH19 : (temp_limit_pre <= INT_MAX)) (PreH20 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH21 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH22 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH23 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH24 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH25 : ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_temp_load_code (policy) (p) (fid) (slot_pre)))) (app ((cm_emit_args_reload (policy) (p) (fid) ((slot_pre + 1 )) ((cm_args_tail (args))))) (tail)) )
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "temp_limit" ) )) # Int  |-> temp_limit_pre)
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cm_emit_args_reload_plan_return_wit_1 := 
(
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (slot_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (args: (@list cm_expr)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (args = (@nil cm_expr))) (PreH2 : (arg_pre = 0)) (PreH3 : (0 <= slot_pre)) (PreH4 : ((slot_pre + (Zlength (args)) ) <= temp_limit_pre)) (PreH5 : (0 <= temp_limit_pre)) (PreH6 : (temp_limit_pre <= INT_MAX)) (PreH7 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH8 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH9 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH10 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH11 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH12 : ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX)) ,
  (cm_arg_list_rep arg_pre args )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_args_reload (policy) (p) (fid) (slot_pre) (args))) (tail)) )
|--
  “ (0 <= slot_pre) ” 
  &&  “ ((slot_pre + (Zlength (args)) ) <= temp_limit_pre) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX) ”
  &&  (cm_function_context_rep fn_pre f body next )
  **  (cm_arg_list_rep arg_pre args )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_emit_args_reload (policy) (p) (fid) (slot_pre) (args)))) tail )
) \/
(
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (slot_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (args: (@list cm_expr)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (args = (@nil cm_expr))) (PreH2 : (arg_pre = 0)) (PreH3 : (0 <= slot_pre)) (PreH4 : ((slot_pre + (Zlength (args)) ) <= temp_limit_pre)) (PreH5 : (0 <= temp_limit_pre)) (PreH6 : (temp_limit_pre <= INT_MAX)) (PreH7 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH8 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH9 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH10 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH11 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH12 : ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX)) ,
  (cm_arg_list_rep arg_pre args )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_args_reload (policy) (p) (fid) (slot_pre) (args))) (tail)) )
|--
  (cm_function_context_rep fn_pre f body next )
  **  (cm_arg_list_rep arg_pre args )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_emit_args_reload (policy) (p) (fid) (slot_pre) (args)))) tail )
).

Definition cm_emit_args_reload_plan_return_wit_1_split_goal_spatial := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (slot_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (args: (@list cm_expr)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (args = (@nil cm_expr))) (PreH2 : (arg_pre = 0)) (PreH3 : (0 <= slot_pre)) (PreH4 : ((slot_pre + (Zlength (args)) ) <= temp_limit_pre)) (PreH5 : (0 <= temp_limit_pre)) (PreH6 : (temp_limit_pre <= INT_MAX)) (PreH7 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH8 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH9 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH10 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH11 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH12 : ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX)) ,
  (cm_arg_list_rep arg_pre args )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_args_reload (policy) (p) (fid) (slot_pre) (args))) (tail)) )
|--
  (cm_function_context_rep fn_pre f body next )
  **  (cm_arg_list_rep arg_pre args )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_emit_args_reload (policy) (p) (fid) (slot_pre) (args)))) tail )
.

Definition cm_emit_args_reload_plan_return_wit_2 := 
(
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (slot_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (args: (@list cm_expr)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= (slot_pre + 1 ))) (PreH2 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) <= temp_limit_pre)) (PreH3 : (0 <= temp_limit_pre)) (PreH4 : (temp_limit_pre <= INT_MAX)) (PreH5 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH6 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH7 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH8 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH9 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH10 : ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX)) (PreH11 : (0 <= slot_pre)) (PreH12 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH13 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH14 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH15 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH16 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH17 : ((cm_temp_offset (policy) (p) (fid) (slot_pre)) <= INT_MAX)) (PreH18 : (0 <= (slot_pre + 1 ))) (PreH19 : ((slot_pre + 1 ) <= INT_MAX)) (PreH20 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) <= temp_limit_pre)) (PreH21 : ((cm_temp_offset (policy) (p) (fid) (slot_pre)) <= INT_MAX)) (PreH22 : (arg_pre <> 0)) (PreH23 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH24 : (arg_pre <> 0)) (PreH25 : (0 <= slot_pre)) (PreH26 : ((slot_pre + (Zlength (args)) ) <= temp_limit_pre)) (PreH27 : (0 <= temp_limit_pre)) (PreH28 : (temp_limit_pre <= INT_MAX)) (PreH29 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH30 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH31 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH32 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH33 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH34 : ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX)) ,
  (cm_arg_list_rep arg_pre args )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app (done) ((cm_temp_load_code (policy) (p) (fid) (slot_pre))))) ((cm_emit_args_reload (policy) (p) (fid) ((slot_pre + 1 )) ((cm_args_tail (args)))))) tail )
|--
  “ (0 <= slot_pre) ” 
  &&  “ ((slot_pre + (Zlength (args)) ) <= temp_limit_pre) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX) ”
  &&  (cm_function_context_rep fn_pre f body next )
  **  (cm_arg_list_rep arg_pre args )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_emit_args_reload (policy) (p) (fid) (slot_pre) (args)))) tail )
) \/
(
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (slot_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (args: (@list cm_expr)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= (slot_pre + 1 ))) (PreH2 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) <= temp_limit_pre)) (PreH3 : (0 <= temp_limit_pre)) (PreH4 : (temp_limit_pre <= INT_MAX)) (PreH5 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH6 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH7 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH8 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH9 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH10 : ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX)) (PreH11 : (0 <= slot_pre)) (PreH12 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH13 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH14 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH15 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH16 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH17 : ((cm_temp_offset (policy) (p) (fid) (slot_pre)) <= INT_MAX)) (PreH18 : (0 <= (slot_pre + 1 ))) (PreH19 : ((slot_pre + 1 ) <= INT_MAX)) (PreH20 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) <= temp_limit_pre)) (PreH21 : ((cm_temp_offset (policy) (p) (fid) (slot_pre)) <= INT_MAX)) (PreH22 : (arg_pre <> 0)) (PreH23 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH24 : (arg_pre <> 0)) (PreH25 : (0 <= slot_pre)) (PreH26 : ((slot_pre + (Zlength (args)) ) <= temp_limit_pre)) (PreH27 : (0 <= temp_limit_pre)) (PreH28 : (temp_limit_pre <= INT_MAX)) (PreH29 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH30 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH31 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH32 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH33 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH34 : ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX)) ,
  (cm_arg_list_rep arg_pre args )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app (done) ((cm_temp_load_code (policy) (p) (fid) (slot_pre))))) ((cm_emit_args_reload (policy) (p) (fid) ((slot_pre + 1 )) ((cm_args_tail (args)))))) tail )
|--
  (cm_function_context_rep fn_pre f body next )
  **  (cm_arg_list_rep arg_pre args )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_emit_args_reload (policy) (p) (fid) (slot_pre) (args)))) tail )
).

Definition cm_emit_args_reload_plan_return_wit_2_split_goal_spatial := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (slot_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (args: (@list cm_expr)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= (slot_pre + 1 ))) (PreH2 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) <= temp_limit_pre)) (PreH3 : (0 <= temp_limit_pre)) (PreH4 : (temp_limit_pre <= INT_MAX)) (PreH5 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH6 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH7 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH8 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH9 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH10 : ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX)) (PreH11 : (0 <= slot_pre)) (PreH12 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH13 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH14 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH15 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH16 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH17 : ((cm_temp_offset (policy) (p) (fid) (slot_pre)) <= INT_MAX)) (PreH18 : (0 <= (slot_pre + 1 ))) (PreH19 : ((slot_pre + 1 ) <= INT_MAX)) (PreH20 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) <= temp_limit_pre)) (PreH21 : ((cm_temp_offset (policy) (p) (fid) (slot_pre)) <= INT_MAX)) (PreH22 : (arg_pre <> 0)) (PreH23 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH24 : (arg_pre <> 0)) (PreH25 : (0 <= slot_pre)) (PreH26 : ((slot_pre + (Zlength (args)) ) <= temp_limit_pre)) (PreH27 : (0 <= temp_limit_pre)) (PreH28 : (temp_limit_pre <= INT_MAX)) (PreH29 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH30 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH31 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH32 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH33 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH34 : ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX)) ,
  (cm_arg_list_rep arg_pre args )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app (done) ((cm_temp_load_code (policy) (p) (fid) (slot_pre))))) ((cm_emit_args_reload (policy) (p) (fid) ((slot_pre + 1 )) ((cm_args_tail (args)))))) tail )
|--
  (cm_function_context_rep fn_pre f body next )
  **  (cm_arg_list_rep arg_pre args )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_emit_args_reload (policy) (p) (fid) (slot_pre) (args)))) tail )
.

Definition cm_emit_args_reload_plan_partial_solve_wit_1_pure := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (slot_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (args: (@list cm_expr)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (arg_pre = 0)) (PreH2 : (0 <= slot_pre)) (PreH3 : ((slot_pre + (Zlength (args)) ) <= temp_limit_pre)) (PreH4 : (0 <= temp_limit_pre)) (PreH5 : (temp_limit_pre <= INT_MAX)) (PreH6 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH7 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH8 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH9 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH10 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH11 : ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX)) ,
  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "temp_limit" ) )) # Int  |-> temp_limit_pre)
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_arg_list_rep arg_pre args )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_args_reload (policy) (p) (fid) (slot_pre) (args))) (tail)) )
|--
  “ (arg_pre = 0) ”
.

Definition cm_emit_args_reload_plan_partial_solve_wit_1_aux := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (slot_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (args: (@list cm_expr)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (arg_pre = 0)) (PreH2 : (0 <= slot_pre)) (PreH3 : ((slot_pre + (Zlength (args)) ) <= temp_limit_pre)) (PreH4 : (0 <= temp_limit_pre)) (PreH5 : (temp_limit_pre <= INT_MAX)) (PreH6 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH7 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH8 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH9 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH10 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH11 : ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_arg_list_rep arg_pre args )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_args_reload (policy) (p) (fid) (slot_pre) (args))) (tail)) )
|--
  “ (arg_pre = 0) ” 
  &&  “ (arg_pre = 0) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ ((slot_pre + (Zlength (args)) ) <= temp_limit_pre) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX) ”
  &&  (cm_arg_list_rep arg_pre args )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_args_reload (policy) (p) (fid) (slot_pre) (args))) (tail)) )
.

Definition cm_emit_args_reload_plan_partial_solve_wit_1 := cm_emit_args_reload_plan_partial_solve_wit_1_pure -> cm_emit_args_reload_plan_partial_solve_wit_1_aux.

Definition cm_emit_args_reload_plan_partial_solve_wit_2_pure := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (slot_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (args: (@list cm_expr)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (arg_pre <> 0)) (PreH2 : (0 <= slot_pre)) (PreH3 : ((slot_pre + (Zlength (args)) ) <= temp_limit_pre)) (PreH4 : (0 <= temp_limit_pre)) (PreH5 : (temp_limit_pre <= INT_MAX)) (PreH6 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH7 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH8 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH9 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH10 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH11 : ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX)) ,
  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "temp_limit" ) )) # Int  |-> temp_limit_pre)
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_arg_list_rep arg_pre args )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_args_reload (policy) (p) (fid) (slot_pre) (args))) (tail)) )
|--
  “ (arg_pre <> 0) ”
.

Definition cm_emit_args_reload_plan_partial_solve_wit_2_aux := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (slot_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (args: (@list cm_expr)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (arg_pre <> 0)) (PreH2 : (0 <= slot_pre)) (PreH3 : ((slot_pre + (Zlength (args)) ) <= temp_limit_pre)) (PreH4 : (0 <= temp_limit_pre)) (PreH5 : (temp_limit_pre <= INT_MAX)) (PreH6 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH7 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH8 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH9 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH10 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH11 : ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_arg_list_rep arg_pre args )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_args_reload (policy) (p) (fid) (slot_pre) (args))) (tail)) )
|--
  “ (arg_pre <> 0) ” 
  &&  “ (arg_pre <> 0) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ ((slot_pre + (Zlength (args)) ) <= temp_limit_pre) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX) ”
  &&  (cm_arg_list_rep arg_pre args )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_args_reload (policy) (p) (fid) (slot_pre) (args))) (tail)) )
.

Definition cm_emit_args_reload_plan_partial_solve_wit_2 := cm_emit_args_reload_plan_partial_solve_wit_2_pure -> cm_emit_args_reload_plan_partial_solve_wit_2_aux.

Definition cm_emit_args_reload_plan_partial_solve_wit_3_pure := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (slot_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (args: (@list cm_expr)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (np: Z) (ep: Z) (PreH1 : (arg_pre <> 0)) (PreH2 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH3 : (arg_pre <> 0)) (PreH4 : (0 <= slot_pre)) (PreH5 : ((slot_pre + (Zlength (args)) ) <= temp_limit_pre)) (PreH6 : (0 <= temp_limit_pre)) (PreH7 : (temp_limit_pre <= INT_MAX)) (PreH8 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH9 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH10 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH11 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH12 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH13 : ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX)) ,
  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "temp_limit" ) )) # Int  |-> temp_limit_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_args_reload (policy) (p) (fid) (slot_pre) (args))) (tail)) )
|--
  “ (0 <= slot_pre) ” 
  &&  “ ((slot_pre + (Zlength (args)) ) <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (args = (cons ((cm_args_head (args))) ((cm_args_tail (args))))) ”
.

Definition cm_emit_args_reload_plan_partial_solve_wit_3_aux := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (slot_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (args: (@list cm_expr)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (np: Z) (ep: Z) (PreH1 : (arg_pre <> 0)) (PreH2 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH3 : (arg_pre <> 0)) (PreH4 : (0 <= slot_pre)) (PreH5 : ((slot_pre + (Zlength (args)) ) <= temp_limit_pre)) (PreH6 : (0 <= temp_limit_pre)) (PreH7 : (temp_limit_pre <= INT_MAX)) (PreH8 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH9 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH10 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH11 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH12 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH13 : ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX)) ,
  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_args_reload (policy) (p) (fid) (slot_pre) (args))) (tail)) )
|--
  “ (0 <= slot_pre) ” 
  &&  “ ((slot_pre + (Zlength (args)) ) <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (args = (cons ((cm_args_head (args))) ((cm_args_tail (args))))) ” 
  &&  “ (arg_pre <> 0) ” 
  &&  “ (args = (cons ((cm_args_head (args))) ((cm_args_tail (args))))) ” 
  &&  “ (arg_pre <> 0) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ ((slot_pre + (Zlength (args)) ) <= temp_limit_pre) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX) ”
  &&  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_args_reload (policy) (p) (fid) (slot_pre) (args))) (tail)) )
.

Definition cm_emit_args_reload_plan_partial_solve_wit_3 := cm_emit_args_reload_plan_partial_solve_wit_3_pure -> cm_emit_args_reload_plan_partial_solve_wit_3_aux.

Definition cm_emit_args_reload_plan_partial_solve_wit_4_pure := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (slot_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (args: (@list cm_expr)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (np: Z) (ep: Z) (PreH1 : (0 <= (slot_pre + 1 ))) (PreH2 : ((slot_pre + 1 ) <= INT_MAX)) (PreH3 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) <= temp_limit_pre)) (PreH4 : ((cm_temp_offset (policy) (p) (fid) (slot_pre)) <= INT_MAX)) (PreH5 : (arg_pre <> 0)) (PreH6 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH7 : (arg_pre <> 0)) (PreH8 : (0 <= slot_pre)) (PreH9 : ((slot_pre + (Zlength (args)) ) <= temp_limit_pre)) (PreH10 : (0 <= temp_limit_pre)) (PreH11 : (temp_limit_pre <= INT_MAX)) (PreH12 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH13 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH14 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH15 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH16 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH17 : ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX)) ,
  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "temp_limit" ) )) # Int  |-> temp_limit_pre)
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_args_reload (policy) (p) (fid) (slot_pre) (args))) (tail)) )
|--
  “ (args = (cons ((cm_args_head (args))) ((cm_args_tail (args))))) ”
.

Definition cm_emit_args_reload_plan_partial_solve_wit_4_aux := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (slot_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (args: (@list cm_expr)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (np: Z) (ep: Z) (PreH1 : (0 <= (slot_pre + 1 ))) (PreH2 : ((slot_pre + 1 ) <= INT_MAX)) (PreH3 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) <= temp_limit_pre)) (PreH4 : ((cm_temp_offset (policy) (p) (fid) (slot_pre)) <= INT_MAX)) (PreH5 : (arg_pre <> 0)) (PreH6 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH7 : (arg_pre <> 0)) (PreH8 : (0 <= slot_pre)) (PreH9 : ((slot_pre + (Zlength (args)) ) <= temp_limit_pre)) (PreH10 : (0 <= temp_limit_pre)) (PreH11 : (temp_limit_pre <= INT_MAX)) (PreH12 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH13 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH14 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH15 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH16 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH17 : ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX)) ,
  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_args_reload (policy) (p) (fid) (slot_pre) (args))) (tail)) )
|--
  “ (args = (cons ((cm_args_head (args))) ((cm_args_tail (args))))) ” 
  &&  “ (0 <= (slot_pre + 1 )) ” 
  &&  “ ((slot_pre + 1 ) <= INT_MAX) ” 
  &&  “ (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) <= temp_limit_pre) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (slot_pre)) <= INT_MAX) ” 
  &&  “ (arg_pre <> 0) ” 
  &&  “ (args = (cons ((cm_args_head (args))) ((cm_args_tail (args))))) ” 
  &&  “ (arg_pre <> 0) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ ((slot_pre + (Zlength (args)) ) <= temp_limit_pre) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_args_reload (policy) (p) (fid) (slot_pre) (args))) (tail)) )
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
  **  (cm_function_context_rep fn_pre f body next )
.

Definition cm_emit_args_reload_plan_partial_solve_wit_4 := cm_emit_args_reload_plan_partial_solve_wit_4_pure -> cm_emit_args_reload_plan_partial_solve_wit_4_aux.

Definition cm_emit_args_reload_plan_partial_solve_wit_5_pure := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (slot_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (args: (@list cm_expr)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (np: Z) (ep: Z) (PreH1 : (0 <= (slot_pre + 1 ))) (PreH2 : ((slot_pre + 1 ) <= INT_MAX)) (PreH3 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) <= temp_limit_pre)) (PreH4 : ((cm_temp_offset (policy) (p) (fid) (slot_pre)) <= INT_MAX)) (PreH5 : (arg_pre <> 0)) (PreH6 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH7 : (arg_pre <> 0)) (PreH8 : (0 <= slot_pre)) (PreH9 : ((slot_pre + (Zlength (args)) ) <= temp_limit_pre)) (PreH10 : (0 <= temp_limit_pre)) (PreH11 : (temp_limit_pre <= INT_MAX)) (PreH12 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH13 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH14 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH15 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH16 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH17 : ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX)) ,
  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_temp_load_code (policy) (p) (fid) (slot_pre))) ((app ((cm_emit_args_reload (policy) (p) (fid) ((slot_pre + 1 )) ((cm_args_tail (args))))) (tail)))) )
  **  ((( &( "temp_limit" ) )) # Int  |-> temp_limit_pre)
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  (cm_function_context_rep fn_pre f body next )
|--
  “ (0 <= slot_pre) ” 
  &&  “ ((cm_program_structs (p)) = (cm_program_structs (p))) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (slot_pre)) <= INT_MAX) ”
.

Definition cm_emit_args_reload_plan_partial_solve_wit_5_aux := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (slot_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (args: (@list cm_expr)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (np: Z) (ep: Z) (PreH1 : (0 <= (slot_pre + 1 ))) (PreH2 : ((slot_pre + 1 ) <= INT_MAX)) (PreH3 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) <= temp_limit_pre)) (PreH4 : ((cm_temp_offset (policy) (p) (fid) (slot_pre)) <= INT_MAX)) (PreH5 : (arg_pre <> 0)) (PreH6 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH7 : (arg_pre <> 0)) (PreH8 : (0 <= slot_pre)) (PreH9 : ((slot_pre + (Zlength (args)) ) <= temp_limit_pre)) (PreH10 : (0 <= temp_limit_pre)) (PreH11 : (temp_limit_pre <= INT_MAX)) (PreH12 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH13 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH14 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH15 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH16 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH17 : ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_temp_load_code (policy) (p) (fid) (slot_pre))) ((app ((cm_emit_args_reload (policy) (p) (fid) ((slot_pre + 1 )) ((cm_args_tail (args))))) (tail)))) )
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
  **  (cm_function_context_rep fn_pre f body next )
|--
  “ (0 <= slot_pre) ” 
  &&  “ ((cm_program_structs (p)) = (cm_program_structs (p))) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (slot_pre)) <= INT_MAX) ” 
  &&  “ (0 <= (slot_pre + 1 )) ” 
  &&  “ ((slot_pre + 1 ) <= INT_MAX) ” 
  &&  “ (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) <= temp_limit_pre) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (slot_pre)) <= INT_MAX) ” 
  &&  “ (arg_pre <> 0) ” 
  &&  “ (args = (cons ((cm_args_head (args))) ((cm_args_tail (args))))) ” 
  &&  “ (arg_pre <> 0) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ ((slot_pre + (Zlength (args)) ) <= temp_limit_pre) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX) ”
  &&  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_temp_load_code (policy) (p) (fid) (slot_pre))) ((app ((cm_emit_args_reload (policy) (p) (fid) ((slot_pre + 1 )) ((cm_args_tail (args))))) (tail)))) )
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
.

Definition cm_emit_args_reload_plan_partial_solve_wit_5 := cm_emit_args_reload_plan_partial_solve_wit_5_pure -> cm_emit_args_reload_plan_partial_solve_wit_5_aux.

Definition cm_emit_args_reload_plan_partial_solve_wit_6_pure := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (slot_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (args: (@list cm_expr)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (np: Z) (ep: Z) (PreH1 : (0 <= slot_pre)) (PreH2 : ((cm_program_structs (p)) = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH5 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (slot_pre)) <= INT_MAX)) (PreH9 : (0 <= (slot_pre + 1 ))) (PreH10 : ((slot_pre + 1 ) <= INT_MAX)) (PreH11 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) <= temp_limit_pre)) (PreH12 : ((cm_temp_offset (policy) (p) (fid) (slot_pre)) <= INT_MAX)) (PreH13 : (arg_pre <> 0)) (PreH14 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH15 : (arg_pre <> 0)) (PreH16 : (0 <= slot_pre)) (PreH17 : ((slot_pre + (Zlength (args)) ) <= temp_limit_pre)) (PreH18 : (0 <= temp_limit_pre)) (PreH19 : (temp_limit_pre <= INT_MAX)) (PreH20 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH21 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH22 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH23 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH24 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH25 : ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_temp_load_code (policy) (p) (fid) (slot_pre)))) (app ((cm_emit_args_reload (policy) (p) (fid) ((slot_pre + 1 )) ((cm_args_tail (args))))) (tail)) )
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "temp_limit" ) )) # Int  |-> temp_limit_pre)
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
|--
  “ (0 <= (slot_pre + 1 )) ” 
  &&  “ (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) <= temp_limit_pre) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX) ”
.

Definition cm_emit_args_reload_plan_partial_solve_wit_6_aux := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (slot_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (args: (@list cm_expr)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (np: Z) (ep: Z) (PreH1 : (0 <= slot_pre)) (PreH2 : ((cm_program_structs (p)) = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH5 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (slot_pre)) <= INT_MAX)) (PreH9 : (0 <= (slot_pre + 1 ))) (PreH10 : ((slot_pre + 1 ) <= INT_MAX)) (PreH11 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) <= temp_limit_pre)) (PreH12 : ((cm_temp_offset (policy) (p) (fid) (slot_pre)) <= INT_MAX)) (PreH13 : (arg_pre <> 0)) (PreH14 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH15 : (arg_pre <> 0)) (PreH16 : (0 <= slot_pre)) (PreH17 : ((slot_pre + (Zlength (args)) ) <= temp_limit_pre)) (PreH18 : (0 <= temp_limit_pre)) (PreH19 : (temp_limit_pre <= INT_MAX)) (PreH20 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH21 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH22 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH23 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH24 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH25 : ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_temp_load_code (policy) (p) (fid) (slot_pre)))) (app ((cm_emit_args_reload (policy) (p) (fid) ((slot_pre + 1 )) ((cm_args_tail (args))))) (tail)) )
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
|--
  “ (0 <= (slot_pre + 1 )) ” 
  &&  “ (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) <= temp_limit_pre) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (slot_pre)) <= INT_MAX) ” 
  &&  “ (0 <= (slot_pre + 1 )) ” 
  &&  “ ((slot_pre + 1 ) <= INT_MAX) ” 
  &&  “ (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) <= temp_limit_pre) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (slot_pre)) <= INT_MAX) ” 
  &&  “ (arg_pre <> 0) ” 
  &&  “ (args = (cons ((cm_args_head (args))) ((cm_args_tail (args))))) ” 
  &&  “ (arg_pre <> 0) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ ((slot_pre + (Zlength (args)) ) <= temp_limit_pre) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX) ”
  &&  (cm_function_context_rep fn_pre f body next )
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_temp_load_code (policy) (p) (fid) (slot_pre)))) (app ((cm_emit_args_reload (policy) (p) (fid) ((slot_pre + 1 )) ((cm_args_tail (args))))) (tail)) )
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep (cm_args_head (args)) )
.

Definition cm_emit_args_reload_plan_partial_solve_wit_6 := cm_emit_args_reload_plan_partial_solve_wit_6_pure -> cm_emit_args_reload_plan_partial_solve_wit_6_aux.

Definition cm_emit_args_reload_plan_partial_solve_wit_7_pure := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (slot_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (args: (@list cm_expr)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (np: Z) (ep: Z) (PreH1 : (0 <= (slot_pre + 1 ))) (PreH2 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) <= temp_limit_pre)) (PreH3 : (0 <= temp_limit_pre)) (PreH4 : (temp_limit_pre <= INT_MAX)) (PreH5 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH6 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH7 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH8 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH9 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH10 : ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX)) (PreH11 : (0 <= slot_pre)) (PreH12 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH13 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH14 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH15 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH16 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH17 : ((cm_temp_offset (policy) (p) (fid) (slot_pre)) <= INT_MAX)) (PreH18 : (0 <= (slot_pre + 1 ))) (PreH19 : ((slot_pre + 1 ) <= INT_MAX)) (PreH20 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) <= temp_limit_pre)) (PreH21 : ((cm_temp_offset (policy) (p) (fid) (slot_pre)) <= INT_MAX)) (PreH22 : (arg_pre <> 0)) (PreH23 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH24 : (arg_pre <> 0)) (PreH25 : (0 <= slot_pre)) (PreH26 : ((slot_pre + (Zlength (args)) ) <= temp_limit_pre)) (PreH27 : (0 <= temp_limit_pre)) (PreH28 : (temp_limit_pre <= INT_MAX)) (PreH29 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH30 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH31 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH32 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH33 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH34 : ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app (done) ((cm_temp_load_code (policy) (p) (fid) (slot_pre))))) ((cm_emit_args_reload (policy) (p) (fid) ((slot_pre + 1 )) ((cm_args_tail (args)))))) tail )
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "temp_limit" ) )) # Int  |-> temp_limit_pre)
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
|--
  “ (arg_pre <> 0) ” 
  &&  “ (args = (cons ((cm_args_head (args))) ((cm_args_tail (args))))) ”
.

Definition cm_emit_args_reload_plan_partial_solve_wit_7_aux := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (slot_pre: Z) (fn_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (next: Z) (body: Z) (args: (@list cm_expr)) (fid: Z) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (np: Z) (ep: Z) (PreH1 : (0 <= (slot_pre + 1 ))) (PreH2 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) <= temp_limit_pre)) (PreH3 : (0 <= temp_limit_pre)) (PreH4 : (temp_limit_pre <= INT_MAX)) (PreH5 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH6 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH7 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH8 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH9 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH10 : ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX)) (PreH11 : (0 <= slot_pre)) (PreH12 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH13 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH14 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH15 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH16 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH17 : ((cm_temp_offset (policy) (p) (fid) (slot_pre)) <= INT_MAX)) (PreH18 : (0 <= (slot_pre + 1 ))) (PreH19 : ((slot_pre + 1 ) <= INT_MAX)) (PreH20 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) <= temp_limit_pre)) (PreH21 : ((cm_temp_offset (policy) (p) (fid) (slot_pre)) <= INT_MAX)) (PreH22 : (arg_pre <> 0)) (PreH23 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH24 : (arg_pre <> 0)) (PreH25 : (0 <= slot_pre)) (PreH26 : ((slot_pre + (Zlength (args)) ) <= temp_limit_pre)) (PreH27 : (0 <= temp_limit_pre)) (PreH28 : (temp_limit_pre <= INT_MAX)) (PreH29 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH30 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH31 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH32 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH33 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH34 : ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX)) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app (done) ((cm_temp_load_code (policy) (p) (fid) (slot_pre))))) ((cm_emit_args_reload (policy) (p) (fid) ((slot_pre + 1 )) ((cm_args_tail (args)))))) tail )
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep (cm_args_head (args)) )
|--
  “ (arg_pre <> 0) ” 
  &&  “ (args = (cons ((cm_args_head (args))) ((cm_args_tail (args))))) ” 
  &&  “ (0 <= (slot_pre + 1 )) ” 
  &&  “ (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) <= temp_limit_pre) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (slot_pre)) <= INT_MAX) ” 
  &&  “ (0 <= (slot_pre + 1 )) ” 
  &&  “ ((slot_pre + 1 ) <= INT_MAX) ” 
  &&  “ (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) <= temp_limit_pre) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (slot_pre)) <= INT_MAX) ” 
  &&  “ (arg_pre <> 0) ” 
  &&  “ (args = (cons ((cm_args_head (args))) ((cm_args_tail (args))))) ” 
  &&  “ (arg_pre <> 0) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ ((slot_pre + (Zlength (args)) ) <= temp_limit_pre) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ (f = (cm_function_at (policy) (fid) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (temp_limit_pre)) <= INT_MAX) ”
  &&  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app (done) ((cm_temp_load_code (policy) (p) (fid) (slot_pre))))) ((cm_emit_args_reload (policy) (p) (fid) ((slot_pre + 1 )) ((cm_args_tail (args)))))) tail )
.

Definition cm_emit_args_reload_plan_partial_solve_wit_7 := cm_emit_args_reload_plan_partial_solve_wit_7_pure -> cm_emit_args_reload_plan_partial_solve_wit_7_aux.

Definition cm_emit_args_reload_plan_which_implies_wit_1 := 
(
forall (arg_pre: Z) (args: (@list cm_expr)) (PreH1 : (arg_pre = 0)) ,
  (cm_arg_list_rep arg_pre args )
|--
  “ (args = (@nil cm_expr)) ”
  &&  (cm_arg_list_rep arg_pre args )
) \/
(
forall (arg_pre: Z) (args: (@list cm_expr)) (PreH1 : (arg_pre = 0)) ,
  TT && emp 
|--
  “ (args = (@nil cm_expr)) ”
  &&  emp
).

Definition cm_emit_args_reload_plan_which_implies_wit_1_split_goal_1 := 
forall (arg_pre: Z) (args: (@list cm_expr)) (PreH1 : (arg_pre = 0)) ,
  (args = (@nil cm_expr))
.

Definition cm_emit_args_reload_plan_which_implies_wit_2 := 
(
forall (args: (@list cm_expr)) (arg: Z) (PreH1 : (arg <> 0)) ,
  (cm_arg_list_rep arg args )
|--
  EX (np: Z)  (ep: Z) ,
  “ (arg <> 0) ” 
  &&  “ (args = (cons ((cm_args_head (args))) ((cm_args_tail (args))))) ”
  &&  ((&((arg)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
) \/
(
forall (args: (@list cm_expr)) (arg: Z) (PreH1 : (arg <> 0)) ,
  (cm_arg_list_rep arg args )
|--
  EX (np: Z)  (ep: Z) ,
  “ (arg <> 0) ” 
  &&  “ (args = (cons ((cm_args_head (args))) ((cm_args_tail (args))))) ”
  &&  ((&((arg)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
).

Definition cm_emit_args_reload_plan_which_implies_wit_3 := 
(
forall (args: (@list cm_expr)) (fid: Z) (p: cm_program) (policy: cm_lookup_policy) (slot: Z) (temp_limit: Z) (PreH1 : (0 <= slot)) (PreH2 : ((slot + (Zlength (args)) ) <= temp_limit)) (PreH3 : (temp_limit <= INT_MAX)) (PreH4 : ((cm_temp_offset (policy) (p) (fid) (temp_limit)) <= INT_MAX)) (PreH5 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) ,
  TT && emp 
|--
  “ (0 <= (slot + 1 )) ” 
  &&  “ ((slot + 1 ) <= INT_MAX) ” 
  &&  “ (((slot + 1 ) + (Zlength ((cm_args_tail (args)))) ) <= temp_limit) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (slot)) <= INT_MAX) ”
  &&  emp
) \/
(
forall (args: (@list cm_expr)) (fid: Z) (p: cm_program) (policy: cm_lookup_policy) (slot: Z) (temp_limit: Z) (PreH1 : (0 <= slot)) (PreH2 : ((slot + (Zlength (args)) ) <= temp_limit)) (PreH3 : (temp_limit <= INT_MAX)) (PreH4 : ((cm_temp_offset (policy) (p) (fid) (temp_limit)) <= INT_MAX)) (PreH5 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) ,
  TT && emp 
|--
  “ ((cm_temp_offset (policy) (p) (fid) (slot)) <= INT_MAX) ” 
  &&  “ (((slot + 1 ) + (Zlength ((cm_args_tail (args)))) ) <= temp_limit) ” 
  &&  “ ((slot + 1 ) <= INT_MAX) ”
  &&  emp
).

Definition cm_emit_args_reload_plan_which_implies_wit_3_split_goal_1 := 
forall (args: (@list cm_expr)) (fid: Z) (p: cm_program) (policy: cm_lookup_policy) (slot: Z) (temp_limit: Z) (PreH1 : (0 <= slot)) (PreH2 : ((slot + (Zlength (args)) ) <= temp_limit)) (PreH3 : (temp_limit <= INT_MAX)) (PreH4 : ((cm_temp_offset (policy) (p) (fid) (temp_limit)) <= INT_MAX)) (PreH5 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) ,
  ((cm_temp_offset (policy) (p) (fid) (slot)) <= INT_MAX)
.

Definition cm_emit_args_reload_plan_which_implies_wit_3_split_goal_2 := 
forall (args: (@list cm_expr)) (fid: Z) (p: cm_program) (policy: cm_lookup_policy) (slot: Z) (temp_limit: Z) (PreH1 : (0 <= slot)) (PreH2 : ((slot + (Zlength (args)) ) <= temp_limit)) (PreH3 : (temp_limit <= INT_MAX)) (PreH4 : ((cm_temp_offset (policy) (p) (fid) (temp_limit)) <= INT_MAX)) (PreH5 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) ,
  (((slot + 1 ) + (Zlength ((cm_args_tail (args)))) ) <= temp_limit)
.

Definition cm_emit_args_reload_plan_which_implies_wit_3_split_goal_3 := 
forall (args: (@list cm_expr)) (fid: Z) (p: cm_program) (policy: cm_lookup_policy) (slot: Z) (temp_limit: Z) (PreH1 : (0 <= slot)) (PreH2 : ((slot + (Zlength (args)) ) <= temp_limit)) (PreH3 : (temp_limit <= INT_MAX)) (PreH4 : ((cm_temp_offset (policy) (p) (fid) (temp_limit)) <= INT_MAX)) (PreH5 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) ,
  ((slot + 1 ) <= INT_MAX)
.

Definition cm_emit_args_reload_plan_which_implies_wit_4 := 
(
forall (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (args: (@list cm_expr)) (fid: Z) (p: cm_program) (policy: cm_lookup_policy) (slot: Z) (emitter: Z) (PreH1 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_emit_args_reload (policy) (p) (fid) (slot) (args))) (tail)) )
|--
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_temp_load_code (policy) (p) (fid) (slot))) ((app ((cm_emit_args_reload (policy) (p) (fid) ((slot + 1 )) ((cm_args_tail (args))))) (tail)))) )
) \/
(
forall (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (args: (@list cm_expr)) (fid: Z) (p: cm_program) (policy: cm_lookup_policy) (slot: Z) (emitter: Z) (PreH1 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_emit_args_reload (policy) (p) (fid) (slot) (args))) (tail)) )
|--
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_temp_load_code (policy) (p) (fid) (slot))) ((app ((cm_emit_args_reload (policy) (p) (fid) ((slot + 1 )) ((cm_args_tail (args))))) (tail)))) )
).

Definition cm_emit_args_reload_plan_which_implies_wit_4_split_goal_spatial := 
forall (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (args: (@list cm_expr)) (fid: Z) (p: cm_program) (policy: cm_lookup_policy) (slot: Z) (emitter: Z) (PreH1 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_emit_args_reload (policy) (p) (fid) (slot) (args))) (tail)) )
|--
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_temp_load_code (policy) (p) (fid) (slot))) ((app ((cm_emit_args_reload (policy) (p) (fid) ((slot + 1 )) ((cm_args_tail (args))))) (tail)))) )
.

Definition cm_emit_args_reload_plan_which_implies_wit_5 := 
(
forall (args: (@list cm_expr)) (np: Z) (ep: Z) (arg: Z) (PreH1 : (arg <> 0)) (PreH2 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) ,
  ((&((arg)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
|--
  (cm_arg_list_rep arg args )
) \/
(
forall (args: (@list cm_expr)) (np: Z) (ep: Z) (arg: Z) (PreH1 : (arg <> 0)) (PreH2 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) ,
  ((&((arg)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
|--
  (cm_arg_list_rep arg args )
).

Definition cm_emit_args_reload_plan_which_implies_wit_5_split_goal_spatial := 
forall (args: (@list cm_expr)) (np: Z) (ep: Z) (arg: Z) (PreH1 : (arg <> 0)) (PreH2 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) ,
  ((&((arg)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
|--
  (cm_arg_list_rep arg args )
.

(*----- Function cm_emit_args_store_plan -----*)

Definition cm_emit_args_store_plan_safety_wit_1 := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (scratch_pre: Z) (slot_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (slots: (@list cm_slot_d)) (args: (@list cm_expr)) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_typed_program policy p )) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH5 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH6 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH7 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH8 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH9 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH10 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH11 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH12 : (cm_args_wf policy p f args slots )) (PreH13 : (cm_args_counts_representable policy p fid_pre args )) (PreH14 : (0 <= slot_pre)) (PreH15 : ((slot_pre + (Zlength (args)) ) = scratch_pre)) (PreH16 : (0 <= scratch_pre)) (PreH17 : (scratch_pre <= temp_limit_pre)) (PreH18 : ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre)) (PreH19 : (0 <= temp_limit_pre)) (PreH20 : (temp_limit_pre <= INT_MAX)) (PreH21 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH22 : (cm_i32_code_count pc_pre )) (PreH23 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) )) ,
  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "scratch" ) )) # Int  |-> scratch_pre)
  **  ((( &( "temp_limit" ) )) # Int  |-> temp_limit_pre)
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_arg_list_rep arg_pre args )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args))) (tail)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_emit_args_store_plan_safety_wit_2 := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (scratch_pre: Z) (slot_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (slots: (@list cm_slot_d)) (args: (@list cm_expr)) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (np: Z) (ep: Z) (retval: Z) (PreH1 : (0 <= (slot_pre + 1 ))) (PreH2 : ((slot_pre + 1 ) <= INT_MAX)) (PreH3 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) = scratch_pre)) (PreH4 : ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre)) (PreH5 : ((scratch_pre + (cm_adepth ((cm_args_apair ((cm_args_tail (args)))))) ) <= temp_limit_pre)) (PreH6 : ((cm_temp_offset (policy) (p) (fid_pre) (slot_pre)) <= INT_MAX)) (PreH7 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) )) (PreH8 : (0 <= (pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ))) (PreH9 : ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) <= INT_MAX)) (PreH10 : (0 <= ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ))) (PreH11 : (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) <= INT_MAX)) (PreH12 : (cm_i32_code_count ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) )) (PreH13 : (cm_i32_code_count (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args)))))) ) )) (PreH14 : (cm_wf_program policy cg p )) (PreH15 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH16 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH17 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH18 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH19 : (retval = (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))))) (PreH20 : (cm_i32_code_count retval )) (PreH21 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH22 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH23 : (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) )) (PreH24 : (cm_args_counts_representable policy p fid_pre (cm_args_tail (args)) )) (PreH25 : (arg_pre <> 0)) (PreH26 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH27 : (arg_pre <> 0)) (PreH28 : (cm_wf_program policy cg p )) (PreH29 : (cm_typed_program policy p )) (PreH30 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH31 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH32 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH33 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH34 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH35 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH36 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH37 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH38 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH39 : (cm_args_wf policy p f args slots )) (PreH40 : (cm_args_counts_representable policy p fid_pre args )) (PreH41 : (0 <= slot_pre)) (PreH42 : ((slot_pre + (Zlength (args)) ) = scratch_pre)) (PreH43 : (0 <= scratch_pre)) (PreH44 : (scratch_pre <= temp_limit_pre)) (PreH45 : ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre)) (PreH46 : (0 <= temp_limit_pre)) (PreH47 : (temp_limit_pre <= INT_MAX)) (PreH48 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH49 : (cm_i32_code_count pc_pre )) (PreH50 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) )) ,
  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "scratch" ) )) # Int  |-> scratch_pre)
  **  ((( &( "temp_limit" ) )) # Int  |-> temp_limit_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "head_count" ) )) # Int  |-> (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))))
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0))) ((app ((cm_temp_store_code (policy) (p) (fid_pre) (slot_pre))) ((app ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args))))) (tail)))))) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_emit_args_store_plan_safety_wit_3 := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (scratch_pre: Z) (slot_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (slots: (@list cm_slot_d)) (args: (@list cm_expr)) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (np: Z) (ep: Z) (retval: Z) (PreH1 : (0 <= slot_pre)) (PreH2 : ((cm_program_structs (p)) = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH5 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid_pre) (slot_pre)) <= INT_MAX)) (PreH9 : (0 <= 0)) (PreH10 : (0 <= 1)) (PreH11 : (cm_wf_program policy cg p )) (PreH12 : (cm_typed_program policy p )) (PreH13 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH14 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH15 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH16 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH17 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH18 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH19 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH20 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH21 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH22 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH23 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH24 : (0 <= scratch_pre)) (PreH25 : (scratch_pre <= temp_limit_pre)) (PreH26 : ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre)) (PreH27 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH28 : (cm_i32_code_count pc_pre )) (PreH29 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) )) (PreH30 : (0 <= (slot_pre + 1 ))) (PreH31 : ((slot_pre + 1 ) <= INT_MAX)) (PreH32 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) = scratch_pre)) (PreH33 : ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre)) (PreH34 : ((scratch_pre + (cm_adepth ((cm_args_apair ((cm_args_tail (args)))))) ) <= temp_limit_pre)) (PreH35 : ((cm_temp_offset (policy) (p) (fid_pre) (slot_pre)) <= INT_MAX)) (PreH36 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) )) (PreH37 : (0 <= (pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ))) (PreH38 : ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) <= INT_MAX)) (PreH39 : (0 <= ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ))) (PreH40 : (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) <= INT_MAX)) (PreH41 : (cm_i32_code_count ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) )) (PreH42 : (cm_i32_code_count (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args)))))) ) )) (PreH43 : (cm_wf_program policy cg p )) (PreH44 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH45 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH46 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH47 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH48 : (retval = (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))))) (PreH49 : (cm_i32_code_count retval )) (PreH50 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH51 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH52 : (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) )) (PreH53 : (cm_args_counts_representable policy p fid_pre (cm_args_tail (args)) )) (PreH54 : (arg_pre <> 0)) (PreH55 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH56 : (arg_pre <> 0)) (PreH57 : (cm_wf_program policy cg p )) (PreH58 : (cm_typed_program policy p )) (PreH59 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH60 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH61 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH62 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH63 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH64 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH65 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH66 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH67 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH68 : (cm_args_wf policy p f args slots )) (PreH69 : (cm_args_counts_representable policy p fid_pre args )) (PreH70 : (0 <= slot_pre)) (PreH71 : ((slot_pre + (Zlength (args)) ) = scratch_pre)) (PreH72 : (0 <= scratch_pre)) (PreH73 : (scratch_pre <= temp_limit_pre)) (PreH74 : ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre)) (PreH75 : (0 <= temp_limit_pre)) (PreH76 : (temp_limit_pre <= INT_MAX)) (PreH77 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH78 : (cm_i32_code_count pc_pre )) (PreH79 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) )) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app (done) ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0))))) ((cm_temp_store_code (policy) (p) (fid_pre) (slot_pre)))) (app ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args))))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "scratch" ) )) # Int  |-> scratch_pre)
  **  ((( &( "temp_limit" ) )) # Int  |-> temp_limit_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "head_count" ) )) # Int  |-> (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))))
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
|--
  “ ((slot_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (slot_pre + 1 )) ”
.

Definition cm_emit_args_store_plan_safety_wit_4 := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (scratch_pre: Z) (slot_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (slots: (@list cm_slot_d)) (args: (@list cm_expr)) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (np: Z) (ep: Z) (retval: Z) (PreH1 : (0 <= slot_pre)) (PreH2 : ((cm_program_structs (p)) = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH5 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid_pre) (slot_pre)) <= INT_MAX)) (PreH9 : (0 <= 0)) (PreH10 : (0 <= 1)) (PreH11 : (cm_wf_program policy cg p )) (PreH12 : (cm_typed_program policy p )) (PreH13 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH14 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH15 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH16 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH17 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH18 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH19 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH20 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH21 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH22 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH23 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH24 : (0 <= scratch_pre)) (PreH25 : (scratch_pre <= temp_limit_pre)) (PreH26 : ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre)) (PreH27 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH28 : (cm_i32_code_count pc_pre )) (PreH29 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) )) (PreH30 : (0 <= (slot_pre + 1 ))) (PreH31 : ((slot_pre + 1 ) <= INT_MAX)) (PreH32 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) = scratch_pre)) (PreH33 : ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre)) (PreH34 : ((scratch_pre + (cm_adepth ((cm_args_apair ((cm_args_tail (args)))))) ) <= temp_limit_pre)) (PreH35 : ((cm_temp_offset (policy) (p) (fid_pre) (slot_pre)) <= INT_MAX)) (PreH36 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) )) (PreH37 : (0 <= (pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ))) (PreH38 : ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) <= INT_MAX)) (PreH39 : (0 <= ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ))) (PreH40 : (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) <= INT_MAX)) (PreH41 : (cm_i32_code_count ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) )) (PreH42 : (cm_i32_code_count (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args)))))) ) )) (PreH43 : (cm_wf_program policy cg p )) (PreH44 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH45 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH46 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH47 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH48 : (retval = (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))))) (PreH49 : (cm_i32_code_count retval )) (PreH50 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH51 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH52 : (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) )) (PreH53 : (cm_args_counts_representable policy p fid_pre (cm_args_tail (args)) )) (PreH54 : (arg_pre <> 0)) (PreH55 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH56 : (arg_pre <> 0)) (PreH57 : (cm_wf_program policy cg p )) (PreH58 : (cm_typed_program policy p )) (PreH59 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH60 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH61 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH62 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH63 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH64 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH65 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH66 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH67 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH68 : (cm_args_wf policy p f args slots )) (PreH69 : (cm_args_counts_representable policy p fid_pre args )) (PreH70 : (0 <= slot_pre)) (PreH71 : ((slot_pre + (Zlength (args)) ) = scratch_pre)) (PreH72 : (0 <= scratch_pre)) (PreH73 : (scratch_pre <= temp_limit_pre)) (PreH74 : ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre)) (PreH75 : (0 <= temp_limit_pre)) (PreH76 : (temp_limit_pre <= INT_MAX)) (PreH77 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH78 : (cm_i32_code_count pc_pre )) (PreH79 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) )) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app (done) ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0))))) ((cm_temp_store_code (policy) (p) (fid_pre) (slot_pre)))) (app ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args))))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "scratch" ) )) # Int  |-> scratch_pre)
  **  ((( &( "temp_limit" ) )) # Int  |-> temp_limit_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "head_count" ) )) # Int  |-> (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))))
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
|--
  “ (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ”
.

Definition cm_emit_args_store_plan_safety_wit_5 := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (scratch_pre: Z) (slot_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (slots: (@list cm_slot_d)) (args: (@list cm_expr)) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (np: Z) (ep: Z) (retval: Z) (PreH1 : (0 <= slot_pre)) (PreH2 : ((cm_program_structs (p)) = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH5 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid_pre) (slot_pre)) <= INT_MAX)) (PreH9 : (0 <= 0)) (PreH10 : (0 <= 1)) (PreH11 : (cm_wf_program policy cg p )) (PreH12 : (cm_typed_program policy p )) (PreH13 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH14 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH15 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH16 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH17 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH18 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH19 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH20 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH21 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH22 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH23 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH24 : (0 <= scratch_pre)) (PreH25 : (scratch_pre <= temp_limit_pre)) (PreH26 : ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre)) (PreH27 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH28 : (cm_i32_code_count pc_pre )) (PreH29 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) )) (PreH30 : (0 <= (slot_pre + 1 ))) (PreH31 : ((slot_pre + 1 ) <= INT_MAX)) (PreH32 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) = scratch_pre)) (PreH33 : ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre)) (PreH34 : ((scratch_pre + (cm_adepth ((cm_args_apair ((cm_args_tail (args)))))) ) <= temp_limit_pre)) (PreH35 : ((cm_temp_offset (policy) (p) (fid_pre) (slot_pre)) <= INT_MAX)) (PreH36 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) )) (PreH37 : (0 <= (pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ))) (PreH38 : ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) <= INT_MAX)) (PreH39 : (0 <= ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ))) (PreH40 : (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) <= INT_MAX)) (PreH41 : (cm_i32_code_count ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) )) (PreH42 : (cm_i32_code_count (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args)))))) ) )) (PreH43 : (cm_wf_program policy cg p )) (PreH44 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH45 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH46 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH47 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH48 : (retval = (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))))) (PreH49 : (cm_i32_code_count retval )) (PreH50 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH51 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH52 : (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) )) (PreH53 : (cm_args_counts_representable policy p fid_pre (cm_args_tail (args)) )) (PreH54 : (arg_pre <> 0)) (PreH55 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH56 : (arg_pre <> 0)) (PreH57 : (cm_wf_program policy cg p )) (PreH58 : (cm_typed_program policy p )) (PreH59 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH60 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH61 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH62 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH63 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH64 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH65 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH66 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH67 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH68 : (cm_args_wf policy p f args slots )) (PreH69 : (cm_args_counts_representable policy p fid_pre args )) (PreH70 : (0 <= slot_pre)) (PreH71 : ((slot_pre + (Zlength (args)) ) = scratch_pre)) (PreH72 : (0 <= scratch_pre)) (PreH73 : (scratch_pre <= temp_limit_pre)) (PreH74 : ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre)) (PreH75 : (0 <= temp_limit_pre)) (PreH76 : (temp_limit_pre <= INT_MAX)) (PreH77 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH78 : (cm_i32_code_count pc_pre )) (PreH79 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) )) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app (done) ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0))))) ((cm_temp_store_code (policy) (p) (fid_pre) (slot_pre)))) (app ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args))))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "scratch" ) )) # Int  |-> scratch_pre)
  **  ((( &( "temp_limit" ) )) # Int  |-> temp_limit_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "head_count" ) )) # Int  |-> (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))))
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
|--
  “ ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) )) ”
.

Definition cm_emit_args_store_plan_safety_wit_6 := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (scratch_pre: Z) (slot_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (slots: (@list cm_slot_d)) (args: (@list cm_expr)) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (np: Z) (ep: Z) (retval: Z) (PreH1 : (0 <= slot_pre)) (PreH2 : ((cm_program_structs (p)) = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH5 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid_pre) (slot_pre)) <= INT_MAX)) (PreH9 : (0 <= 0)) (PreH10 : (0 <= 1)) (PreH11 : (cm_wf_program policy cg p )) (PreH12 : (cm_typed_program policy p )) (PreH13 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH14 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH15 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH16 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH17 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH18 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH19 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH20 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH21 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH22 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH23 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH24 : (0 <= scratch_pre)) (PreH25 : (scratch_pre <= temp_limit_pre)) (PreH26 : ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre)) (PreH27 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH28 : (cm_i32_code_count pc_pre )) (PreH29 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) )) (PreH30 : (0 <= (slot_pre + 1 ))) (PreH31 : ((slot_pre + 1 ) <= INT_MAX)) (PreH32 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) = scratch_pre)) (PreH33 : ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre)) (PreH34 : ((scratch_pre + (cm_adepth ((cm_args_apair ((cm_args_tail (args)))))) ) <= temp_limit_pre)) (PreH35 : ((cm_temp_offset (policy) (p) (fid_pre) (slot_pre)) <= INT_MAX)) (PreH36 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) )) (PreH37 : (0 <= (pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ))) (PreH38 : ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) <= INT_MAX)) (PreH39 : (0 <= ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ))) (PreH40 : (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) <= INT_MAX)) (PreH41 : (cm_i32_code_count ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) )) (PreH42 : (cm_i32_code_count (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args)))))) ) )) (PreH43 : (cm_wf_program policy cg p )) (PreH44 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH45 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH46 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH47 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH48 : (retval = (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))))) (PreH49 : (cm_i32_code_count retval )) (PreH50 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH51 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH52 : (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) )) (PreH53 : (cm_args_counts_representable policy p fid_pre (cm_args_tail (args)) )) (PreH54 : (arg_pre <> 0)) (PreH55 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH56 : (arg_pre <> 0)) (PreH57 : (cm_wf_program policy cg p )) (PreH58 : (cm_typed_program policy p )) (PreH59 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH60 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH61 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH62 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH63 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH64 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH65 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH66 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH67 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH68 : (cm_args_wf policy p f args slots )) (PreH69 : (cm_args_counts_representable policy p fid_pre args )) (PreH70 : (0 <= slot_pre)) (PreH71 : ((slot_pre + (Zlength (args)) ) = scratch_pre)) (PreH72 : (0 <= scratch_pre)) (PreH73 : (scratch_pre <= temp_limit_pre)) (PreH74 : ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre)) (PreH75 : (0 <= temp_limit_pre)) (PreH76 : (temp_limit_pre <= INT_MAX)) (PreH77 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH78 : (cm_i32_code_count pc_pre )) (PreH79 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) )) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app (done) ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0))))) ((cm_temp_store_code (policy) (p) (fid_pre) (slot_pre)))) (app ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args))))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "scratch" ) )) # Int  |-> scratch_pre)
  **  ((( &( "temp_limit" ) )) # Int  |-> temp_limit_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "head_count" ) )) # Int  |-> (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))))
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
|--
  “ (5 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 5) ”
.

Definition cm_emit_args_store_plan_safety_wit_7 := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (scratch_pre: Z) (slot_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (slots: (@list cm_slot_d)) (args: (@list cm_expr)) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (np: Z) (ep: Z) (retval: Z) (PreH1 : (0 <= slot_pre)) (PreH2 : ((cm_program_structs (p)) = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH5 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid_pre) (slot_pre)) <= INT_MAX)) (PreH9 : (0 <= 0)) (PreH10 : (0 <= 1)) (PreH11 : (cm_wf_program policy cg p )) (PreH12 : (cm_typed_program policy p )) (PreH13 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH14 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH15 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH16 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH17 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH18 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH19 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH20 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH21 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH22 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH23 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH24 : (0 <= scratch_pre)) (PreH25 : (scratch_pre <= temp_limit_pre)) (PreH26 : ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre)) (PreH27 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH28 : (cm_i32_code_count pc_pre )) (PreH29 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) )) (PreH30 : (0 <= (slot_pre + 1 ))) (PreH31 : ((slot_pre + 1 ) <= INT_MAX)) (PreH32 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) = scratch_pre)) (PreH33 : ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre)) (PreH34 : ((scratch_pre + (cm_adepth ((cm_args_apair ((cm_args_tail (args)))))) ) <= temp_limit_pre)) (PreH35 : ((cm_temp_offset (policy) (p) (fid_pre) (slot_pre)) <= INT_MAX)) (PreH36 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) )) (PreH37 : (0 <= (pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ))) (PreH38 : ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) <= INT_MAX)) (PreH39 : (0 <= ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ))) (PreH40 : (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) <= INT_MAX)) (PreH41 : (cm_i32_code_count ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) )) (PreH42 : (cm_i32_code_count (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args)))))) ) )) (PreH43 : (cm_wf_program policy cg p )) (PreH44 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH45 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH46 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH47 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH48 : (retval = (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))))) (PreH49 : (cm_i32_code_count retval )) (PreH50 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH51 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH52 : (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) )) (PreH53 : (cm_args_counts_representable policy p fid_pre (cm_args_tail (args)) )) (PreH54 : (arg_pre <> 0)) (PreH55 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH56 : (arg_pre <> 0)) (PreH57 : (cm_wf_program policy cg p )) (PreH58 : (cm_typed_program policy p )) (PreH59 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH60 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH61 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH62 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH63 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH64 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH65 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH66 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH67 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH68 : (cm_args_wf policy p f args slots )) (PreH69 : (cm_args_counts_representable policy p fid_pre args )) (PreH70 : (0 <= slot_pre)) (PreH71 : ((slot_pre + (Zlength (args)) ) = scratch_pre)) (PreH72 : (0 <= scratch_pre)) (PreH73 : (scratch_pre <= temp_limit_pre)) (PreH74 : ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre)) (PreH75 : (0 <= temp_limit_pre)) (PreH76 : (temp_limit_pre <= INT_MAX)) (PreH77 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH78 : (cm_i32_code_count pc_pre )) (PreH79 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) )) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app (done) ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0))))) ((cm_temp_store_code (policy) (p) (fid_pre) (slot_pre)))) (app ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args))))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "scratch" ) )) # Int  |-> scratch_pre)
  **  ((( &( "temp_limit" ) )) # Int  |-> temp_limit_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "head_count" ) )) # Int  |-> (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))))
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cm_emit_args_store_plan_return_wit_1 := 
(
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (scratch_pre: Z) (slot_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (slots: (@list cm_slot_d)) (args: (@list cm_expr)) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (args = (@nil cm_expr))) (PreH2 : (arg_pre = 0)) (PreH3 : (cm_wf_program policy cg p )) (PreH4 : (cm_typed_program policy p )) (PreH5 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH6 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH7 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH8 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH9 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH10 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH11 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH12 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH13 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH14 : (cm_args_wf policy p f args slots )) (PreH15 : (cm_args_counts_representable policy p fid_pre args )) (PreH16 : (0 <= slot_pre)) (PreH17 : ((slot_pre + (Zlength (args)) ) = scratch_pre)) (PreH18 : (0 <= scratch_pre)) (PreH19 : (scratch_pre <= temp_limit_pre)) (PreH20 : ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre)) (PreH21 : (0 <= temp_limit_pre)) (PreH22 : (temp_limit_pre <= INT_MAX)) (PreH23 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH24 : (cm_i32_code_count pc_pre )) (PreH25 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) )) ,
  (cm_arg_list_rep arg_pre args )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args))) (tail)) )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (cm_args_wf policy p f args slots ) ” 
  &&  “ (cm_args_counts_representable policy p fid_pre args ) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ ((slot_pre + (Zlength (args)) ) = scratch_pre) ” 
  &&  “ (0 <= scratch_pre) ” 
  &&  “ (scratch_pre <= temp_limit_pre) ” 
  &&  “ ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count pc_pre ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_arg_list_rep arg_pre args )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) tail )
) \/
(
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (scratch_pre: Z) (slot_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (slots: (@list cm_slot_d)) (args: (@list cm_expr)) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (args = (@nil cm_expr))) (PreH2 : (arg_pre = 0)) (PreH3 : (cm_wf_program policy cg p )) (PreH4 : (cm_typed_program policy p )) (PreH5 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH6 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH7 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH8 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH9 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH10 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH11 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH12 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH13 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH14 : (cm_args_wf policy p f args slots )) (PreH15 : (cm_args_counts_representable policy p fid_pre args )) (PreH16 : (0 <= slot_pre)) (PreH17 : ((slot_pre + (Zlength (args)) ) = scratch_pre)) (PreH18 : (0 <= scratch_pre)) (PreH19 : (scratch_pre <= temp_limit_pre)) (PreH20 : ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre)) (PreH21 : (0 <= temp_limit_pre)) (PreH22 : (temp_limit_pre <= INT_MAX)) (PreH23 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH24 : (cm_i32_code_count pc_pre )) (PreH25 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) )) ,
  (cm_arg_list_rep arg_pre args )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args))) (tail)) )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_arg_list_rep arg_pre args )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) tail )
).

Definition cm_emit_args_store_plan_return_wit_1_split_goal_spatial := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (scratch_pre: Z) (slot_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (slots: (@list cm_slot_d)) (args: (@list cm_expr)) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (args = (@nil cm_expr))) (PreH2 : (arg_pre = 0)) (PreH3 : (cm_wf_program policy cg p )) (PreH4 : (cm_typed_program policy p )) (PreH5 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH6 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH7 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH8 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH9 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH10 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH11 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH12 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH13 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH14 : (cm_args_wf policy p f args slots )) (PreH15 : (cm_args_counts_representable policy p fid_pre args )) (PreH16 : (0 <= slot_pre)) (PreH17 : ((slot_pre + (Zlength (args)) ) = scratch_pre)) (PreH18 : (0 <= scratch_pre)) (PreH19 : (scratch_pre <= temp_limit_pre)) (PreH20 : ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre)) (PreH21 : (0 <= temp_limit_pre)) (PreH22 : (temp_limit_pre <= INT_MAX)) (PreH23 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH24 : (cm_i32_code_count pc_pre )) (PreH25 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) )) ,
  (cm_arg_list_rep arg_pre args )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args))) (tail)) )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_arg_list_rep arg_pre args )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) tail )
.

Definition cm_emit_args_store_plan_return_wit_2 := 
(
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (scratch_pre: Z) (slot_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (slots: (@list cm_slot_d)) (args: (@list cm_expr)) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_typed_program policy p )) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH5 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH6 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH7 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH8 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH9 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH10 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH11 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH12 : (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) )) (PreH13 : (cm_args_counts_representable policy p fid_pre (cm_args_tail (args)) )) (PreH14 : (0 <= (slot_pre + 1 ))) (PreH15 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) = scratch_pre)) (PreH16 : (0 <= scratch_pre)) (PreH17 : (scratch_pre <= temp_limit_pre)) (PreH18 : ((scratch_pre + (cm_adepth ((cm_args_apair ((cm_args_tail (args)))))) ) <= temp_limit_pre)) (PreH19 : (0 <= temp_limit_pre)) (PreH20 : (temp_limit_pre <= INT_MAX)) (PreH21 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH22 : (cm_i32_code_count ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) )) (PreH23 : (cm_i32_code_count (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args)))))) ) )) (PreH24 : (0 <= slot_pre)) (PreH25 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH26 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH27 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH28 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH29 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH30 : ((cm_temp_offset (policy) (p) (fid_pre) (slot_pre)) <= INT_MAX)) (PreH31 : (0 <= 0)) (PreH32 : (0 <= 1)) (PreH33 : (cm_wf_program policy cg p )) (PreH34 : (cm_typed_program policy p )) (PreH35 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH36 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH37 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH38 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH39 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH40 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH41 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH42 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH43 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH44 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH45 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH46 : (0 <= scratch_pre)) (PreH47 : (scratch_pre <= temp_limit_pre)) (PreH48 : ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre)) (PreH49 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH50 : (cm_i32_code_count pc_pre )) (PreH51 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) )) (PreH52 : (0 <= (slot_pre + 1 ))) (PreH53 : ((slot_pre + 1 ) <= INT_MAX)) (PreH54 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) = scratch_pre)) (PreH55 : ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre)) (PreH56 : ((scratch_pre + (cm_adepth ((cm_args_apair ((cm_args_tail (args)))))) ) <= temp_limit_pre)) (PreH57 : ((cm_temp_offset (policy) (p) (fid_pre) (slot_pre)) <= INT_MAX)) (PreH58 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) )) (PreH59 : (0 <= (pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ))) (PreH60 : ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) <= INT_MAX)) (PreH61 : (0 <= ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ))) (PreH62 : (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) <= INT_MAX)) (PreH63 : (cm_i32_code_count ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) )) (PreH64 : (cm_i32_code_count (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args)))))) ) )) (PreH65 : (cm_wf_program policy cg p )) (PreH66 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH67 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH68 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH69 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH70 : (retval = (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))))) (PreH71 : (cm_i32_code_count retval )) (PreH72 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH73 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH74 : (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) )) (PreH75 : (cm_args_counts_representable policy p fid_pre (cm_args_tail (args)) )) (PreH76 : (arg_pre <> 0)) (PreH77 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH78 : (arg_pre <> 0)) (PreH79 : (cm_wf_program policy cg p )) (PreH80 : (cm_typed_program policy p )) (PreH81 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH82 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH83 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH84 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH85 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH86 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH87 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH88 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH89 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH90 : (cm_args_wf policy p f args slots )) (PreH91 : (cm_args_counts_representable policy p fid_pre args )) (PreH92 : (0 <= slot_pre)) (PreH93 : ((slot_pre + (Zlength (args)) ) = scratch_pre)) (PreH94 : (0 <= scratch_pre)) (PreH95 : (scratch_pre <= temp_limit_pre)) (PreH96 : ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre)) (PreH97 : (0 <= temp_limit_pre)) (PreH98 : (temp_limit_pre <= INT_MAX)) (PreH99 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH100 : (cm_i32_code_count pc_pre )) (PreH101 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) )) ,
  (cm_arg_list_rep arg_pre args )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app (done) ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0))))) ((cm_temp_store_code (policy) (p) (fid_pre) (slot_pre))))) ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args)))))) tail )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (cm_args_wf policy p f args slots ) ” 
  &&  “ (cm_args_counts_representable policy p fid_pre args ) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ ((slot_pre + (Zlength (args)) ) = scratch_pre) ” 
  &&  “ (0 <= scratch_pre) ” 
  &&  “ (scratch_pre <= temp_limit_pre) ” 
  &&  “ ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count pc_pre ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_arg_list_rep arg_pre args )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) tail )
) \/
(
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (scratch_pre: Z) (slot_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (slots: (@list cm_slot_d)) (args: (@list cm_expr)) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_typed_program policy p )) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH5 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH6 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH7 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH8 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH9 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH10 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH11 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH12 : (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) )) (PreH13 : (cm_args_counts_representable policy p fid_pre (cm_args_tail (args)) )) (PreH14 : (0 <= (slot_pre + 1 ))) (PreH15 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) = scratch_pre)) (PreH16 : (0 <= scratch_pre)) (PreH17 : (scratch_pre <= temp_limit_pre)) (PreH18 : ((scratch_pre + (cm_adepth ((cm_args_apair ((cm_args_tail (args)))))) ) <= temp_limit_pre)) (PreH19 : (0 <= temp_limit_pre)) (PreH20 : (temp_limit_pre <= INT_MAX)) (PreH21 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH22 : (cm_i32_code_count ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) )) (PreH23 : (cm_i32_code_count (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args)))))) ) )) (PreH24 : (0 <= slot_pre)) (PreH25 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH26 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH27 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH28 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH29 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH30 : ((cm_temp_offset (policy) (p) (fid_pre) (slot_pre)) <= INT_MAX)) (PreH31 : (0 <= 0)) (PreH32 : (0 <= 1)) (PreH33 : (cm_wf_program policy cg p )) (PreH34 : (cm_typed_program policy p )) (PreH35 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH36 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH37 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH38 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH39 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH40 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH41 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH42 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH43 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH44 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH45 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH46 : (0 <= scratch_pre)) (PreH47 : (scratch_pre <= temp_limit_pre)) (PreH48 : ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre)) (PreH49 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH50 : (cm_i32_code_count pc_pre )) (PreH51 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) )) (PreH52 : (0 <= (slot_pre + 1 ))) (PreH53 : ((slot_pre + 1 ) <= INT_MAX)) (PreH54 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) = scratch_pre)) (PreH55 : ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre)) (PreH56 : ((scratch_pre + (cm_adepth ((cm_args_apair ((cm_args_tail (args)))))) ) <= temp_limit_pre)) (PreH57 : ((cm_temp_offset (policy) (p) (fid_pre) (slot_pre)) <= INT_MAX)) (PreH58 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) )) (PreH59 : (0 <= (pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ))) (PreH60 : ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) <= INT_MAX)) (PreH61 : (0 <= ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ))) (PreH62 : (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) <= INT_MAX)) (PreH63 : (cm_i32_code_count ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) )) (PreH64 : (cm_i32_code_count (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args)))))) ) )) (PreH65 : (cm_wf_program policy cg p )) (PreH66 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH67 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH68 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH69 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH70 : (retval = (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))))) (PreH71 : (cm_i32_code_count retval )) (PreH72 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH73 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH74 : (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) )) (PreH75 : (cm_args_counts_representable policy p fid_pre (cm_args_tail (args)) )) (PreH76 : (arg_pre <> 0)) (PreH77 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH78 : (arg_pre <> 0)) (PreH79 : (cm_wf_program policy cg p )) (PreH80 : (cm_typed_program policy p )) (PreH81 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH82 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH83 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH84 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH85 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH86 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH87 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH88 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH89 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH90 : (cm_args_wf policy p f args slots )) (PreH91 : (cm_args_counts_representable policy p fid_pre args )) (PreH92 : (0 <= slot_pre)) (PreH93 : ((slot_pre + (Zlength (args)) ) = scratch_pre)) (PreH94 : (0 <= scratch_pre)) (PreH95 : (scratch_pre <= temp_limit_pre)) (PreH96 : ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre)) (PreH97 : (0 <= temp_limit_pre)) (PreH98 : (temp_limit_pre <= INT_MAX)) (PreH99 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH100 : (cm_i32_code_count pc_pre )) (PreH101 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) )) ,
  (cm_arg_list_rep arg_pre args )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app (done) ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0))))) ((cm_temp_store_code (policy) (p) (fid_pre) (slot_pre))))) ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args)))))) tail )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_arg_list_rep arg_pre args )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) tail )
).

Definition cm_emit_args_store_plan_return_wit_2_split_goal_spatial := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (scratch_pre: Z) (slot_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (slots: (@list cm_slot_d)) (args: (@list cm_expr)) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_typed_program policy p )) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH5 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH6 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH7 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH8 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH9 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH10 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH11 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH12 : (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) )) (PreH13 : (cm_args_counts_representable policy p fid_pre (cm_args_tail (args)) )) (PreH14 : (0 <= (slot_pre + 1 ))) (PreH15 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) = scratch_pre)) (PreH16 : (0 <= scratch_pre)) (PreH17 : (scratch_pre <= temp_limit_pre)) (PreH18 : ((scratch_pre + (cm_adepth ((cm_args_apair ((cm_args_tail (args)))))) ) <= temp_limit_pre)) (PreH19 : (0 <= temp_limit_pre)) (PreH20 : (temp_limit_pre <= INT_MAX)) (PreH21 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH22 : (cm_i32_code_count ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) )) (PreH23 : (cm_i32_code_count (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args)))))) ) )) (PreH24 : (0 <= slot_pre)) (PreH25 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH26 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH27 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH28 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH29 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH30 : ((cm_temp_offset (policy) (p) (fid_pre) (slot_pre)) <= INT_MAX)) (PreH31 : (0 <= 0)) (PreH32 : (0 <= 1)) (PreH33 : (cm_wf_program policy cg p )) (PreH34 : (cm_typed_program policy p )) (PreH35 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH36 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH37 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH38 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH39 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH40 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH41 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH42 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH43 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH44 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH45 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH46 : (0 <= scratch_pre)) (PreH47 : (scratch_pre <= temp_limit_pre)) (PreH48 : ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre)) (PreH49 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH50 : (cm_i32_code_count pc_pre )) (PreH51 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) )) (PreH52 : (0 <= (slot_pre + 1 ))) (PreH53 : ((slot_pre + 1 ) <= INT_MAX)) (PreH54 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) = scratch_pre)) (PreH55 : ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre)) (PreH56 : ((scratch_pre + (cm_adepth ((cm_args_apair ((cm_args_tail (args)))))) ) <= temp_limit_pre)) (PreH57 : ((cm_temp_offset (policy) (p) (fid_pre) (slot_pre)) <= INT_MAX)) (PreH58 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) )) (PreH59 : (0 <= (pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ))) (PreH60 : ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) <= INT_MAX)) (PreH61 : (0 <= ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ))) (PreH62 : (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) <= INT_MAX)) (PreH63 : (cm_i32_code_count ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) )) (PreH64 : (cm_i32_code_count (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args)))))) ) )) (PreH65 : (cm_wf_program policy cg p )) (PreH66 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH67 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH68 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH69 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH70 : (retval = (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))))) (PreH71 : (cm_i32_code_count retval )) (PreH72 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH73 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH74 : (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) )) (PreH75 : (cm_args_counts_representable policy p fid_pre (cm_args_tail (args)) )) (PreH76 : (arg_pre <> 0)) (PreH77 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH78 : (arg_pre <> 0)) (PreH79 : (cm_wf_program policy cg p )) (PreH80 : (cm_typed_program policy p )) (PreH81 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH82 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH83 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH84 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH85 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH86 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH87 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH88 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH89 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH90 : (cm_args_wf policy p f args slots )) (PreH91 : (cm_args_counts_representable policy p fid_pre args )) (PreH92 : (0 <= slot_pre)) (PreH93 : ((slot_pre + (Zlength (args)) ) = scratch_pre)) (PreH94 : (0 <= scratch_pre)) (PreH95 : (scratch_pre <= temp_limit_pre)) (PreH96 : ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre)) (PreH97 : (0 <= temp_limit_pre)) (PreH98 : (temp_limit_pre <= INT_MAX)) (PreH99 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH100 : (cm_i32_code_count pc_pre )) (PreH101 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) )) ,
  (cm_arg_list_rep arg_pre args )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app (done) ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0))))) ((cm_temp_store_code (policy) (p) (fid_pre) (slot_pre))))) ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args)))))) tail )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_arg_list_rep arg_pre args )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) tail )
.

Definition cm_emit_args_store_plan_partial_solve_wit_1_pure := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (scratch_pre: Z) (slot_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (slots: (@list cm_slot_d)) (args: (@list cm_expr)) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (arg_pre = 0)) (PreH2 : (cm_wf_program policy cg p )) (PreH3 : (cm_typed_program policy p )) (PreH4 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH5 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH6 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH7 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH8 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH9 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH10 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH11 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH12 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH13 : (cm_args_wf policy p f args slots )) (PreH14 : (cm_args_counts_representable policy p fid_pre args )) (PreH15 : (0 <= slot_pre)) (PreH16 : ((slot_pre + (Zlength (args)) ) = scratch_pre)) (PreH17 : (0 <= scratch_pre)) (PreH18 : (scratch_pre <= temp_limit_pre)) (PreH19 : ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre)) (PreH20 : (0 <= temp_limit_pre)) (PreH21 : (temp_limit_pre <= INT_MAX)) (PreH22 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH23 : (cm_i32_code_count pc_pre )) (PreH24 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) )) ,
  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "scratch" ) )) # Int  |-> scratch_pre)
  **  ((( &( "temp_limit" ) )) # Int  |-> temp_limit_pre)
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_arg_list_rep arg_pre args )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args))) (tail)) )
|--
  “ (arg_pre = 0) ”
.

Definition cm_emit_args_store_plan_partial_solve_wit_1_aux := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (scratch_pre: Z) (slot_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (slots: (@list cm_slot_d)) (args: (@list cm_expr)) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (arg_pre = 0)) (PreH2 : (cm_wf_program policy cg p )) (PreH3 : (cm_typed_program policy p )) (PreH4 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH5 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH6 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH7 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH8 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH9 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH10 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH11 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH12 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH13 : (cm_args_wf policy p f args slots )) (PreH14 : (cm_args_counts_representable policy p fid_pre args )) (PreH15 : (0 <= slot_pre)) (PreH16 : ((slot_pre + (Zlength (args)) ) = scratch_pre)) (PreH17 : (0 <= scratch_pre)) (PreH18 : (scratch_pre <= temp_limit_pre)) (PreH19 : ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre)) (PreH20 : (0 <= temp_limit_pre)) (PreH21 : (temp_limit_pre <= INT_MAX)) (PreH22 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH23 : (cm_i32_code_count pc_pre )) (PreH24 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_arg_list_rep arg_pre args )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args))) (tail)) )
|--
  “ (arg_pre = 0) ” 
  &&  “ (arg_pre = 0) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (cm_args_wf policy p f args slots ) ” 
  &&  “ (cm_args_counts_representable policy p fid_pre args ) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ ((slot_pre + (Zlength (args)) ) = scratch_pre) ” 
  &&  “ (0 <= scratch_pre) ” 
  &&  “ (scratch_pre <= temp_limit_pre) ” 
  &&  “ ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count pc_pre ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) ) ”
  &&  (cm_arg_list_rep arg_pre args )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args))) (tail)) )
.

Definition cm_emit_args_store_plan_partial_solve_wit_1 := cm_emit_args_store_plan_partial_solve_wit_1_pure -> cm_emit_args_store_plan_partial_solve_wit_1_aux.

Definition cm_emit_args_store_plan_partial_solve_wit_2_pure := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (scratch_pre: Z) (slot_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (slots: (@list cm_slot_d)) (args: (@list cm_expr)) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (arg_pre <> 0)) (PreH2 : (cm_wf_program policy cg p )) (PreH3 : (cm_typed_program policy p )) (PreH4 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH5 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH6 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH7 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH8 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH9 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH10 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH11 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH12 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH13 : (cm_args_wf policy p f args slots )) (PreH14 : (cm_args_counts_representable policy p fid_pre args )) (PreH15 : (0 <= slot_pre)) (PreH16 : ((slot_pre + (Zlength (args)) ) = scratch_pre)) (PreH17 : (0 <= scratch_pre)) (PreH18 : (scratch_pre <= temp_limit_pre)) (PreH19 : ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre)) (PreH20 : (0 <= temp_limit_pre)) (PreH21 : (temp_limit_pre <= INT_MAX)) (PreH22 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH23 : (cm_i32_code_count pc_pre )) (PreH24 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) )) ,
  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "scratch" ) )) # Int  |-> scratch_pre)
  **  ((( &( "temp_limit" ) )) # Int  |-> temp_limit_pre)
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_arg_list_rep arg_pre args )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args))) (tail)) )
|--
  “ (arg_pre <> 0) ”
.

Definition cm_emit_args_store_plan_partial_solve_wit_2_aux := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (scratch_pre: Z) (slot_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (slots: (@list cm_slot_d)) (args: (@list cm_expr)) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (arg_pre <> 0)) (PreH2 : (cm_wf_program policy cg p )) (PreH3 : (cm_typed_program policy p )) (PreH4 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH5 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH6 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH7 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH8 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH9 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH10 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH11 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH12 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH13 : (cm_args_wf policy p f args slots )) (PreH14 : (cm_args_counts_representable policy p fid_pre args )) (PreH15 : (0 <= slot_pre)) (PreH16 : ((slot_pre + (Zlength (args)) ) = scratch_pre)) (PreH17 : (0 <= scratch_pre)) (PreH18 : (scratch_pre <= temp_limit_pre)) (PreH19 : ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre)) (PreH20 : (0 <= temp_limit_pre)) (PreH21 : (temp_limit_pre <= INT_MAX)) (PreH22 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH23 : (cm_i32_code_count pc_pre )) (PreH24 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_arg_list_rep arg_pre args )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args))) (tail)) )
|--
  “ (arg_pre <> 0) ” 
  &&  “ (arg_pre <> 0) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (cm_args_wf policy p f args slots ) ” 
  &&  “ (cm_args_counts_representable policy p fid_pre args ) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ ((slot_pre + (Zlength (args)) ) = scratch_pre) ” 
  &&  “ (0 <= scratch_pre) ” 
  &&  “ (scratch_pre <= temp_limit_pre) ” 
  &&  “ ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count pc_pre ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) ) ”
  &&  (cm_arg_list_rep arg_pre args )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args))) (tail)) )
.

Definition cm_emit_args_store_plan_partial_solve_wit_2 := cm_emit_args_store_plan_partial_solve_wit_2_pure -> cm_emit_args_store_plan_partial_solve_wit_2_aux.

Definition cm_emit_args_store_plan_partial_solve_wit_3_pure := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (scratch_pre: Z) (slot_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (slots: (@list cm_slot_d)) (args: (@list cm_expr)) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (np: Z) (ep: Z) (PreH1 : (arg_pre <> 0)) (PreH2 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH3 : (arg_pre <> 0)) (PreH4 : (cm_wf_program policy cg p )) (PreH5 : (cm_typed_program policy p )) (PreH6 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH7 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH8 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH9 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH10 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH11 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH12 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH13 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH14 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH15 : (cm_args_wf policy p f args slots )) (PreH16 : (cm_args_counts_representable policy p fid_pre args )) (PreH17 : (0 <= slot_pre)) (PreH18 : ((slot_pre + (Zlength (args)) ) = scratch_pre)) (PreH19 : (0 <= scratch_pre)) (PreH20 : (scratch_pre <= temp_limit_pre)) (PreH21 : ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre)) (PreH22 : (0 <= temp_limit_pre)) (PreH23 : (temp_limit_pre <= INT_MAX)) (PreH24 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH25 : (cm_i32_code_count pc_pre )) (PreH26 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) )) ,
  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "scratch" ) )) # Int  |-> scratch_pre)
  **  ((( &( "temp_limit" ) )) # Int  |-> temp_limit_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args))) (tail)) )
|--
  “ (args = (cons ((cm_args_head (args))) ((cm_args_tail (args))))) ” 
  &&  “ (cm_args_wf policy p f args slots ) ” 
  &&  “ (cm_args_counts_representable policy p fid_pre args ) ”
.

Definition cm_emit_args_store_plan_partial_solve_wit_3_aux := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (scratch_pre: Z) (slot_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (slots: (@list cm_slot_d)) (args: (@list cm_expr)) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (np: Z) (ep: Z) (PreH1 : (arg_pre <> 0)) (PreH2 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH3 : (arg_pre <> 0)) (PreH4 : (cm_wf_program policy cg p )) (PreH5 : (cm_typed_program policy p )) (PreH6 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH7 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH8 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH9 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH10 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH11 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH12 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH13 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH14 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH15 : (cm_args_wf policy p f args slots )) (PreH16 : (cm_args_counts_representable policy p fid_pre args )) (PreH17 : (0 <= slot_pre)) (PreH18 : ((slot_pre + (Zlength (args)) ) = scratch_pre)) (PreH19 : (0 <= scratch_pre)) (PreH20 : (scratch_pre <= temp_limit_pre)) (PreH21 : ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre)) (PreH22 : (0 <= temp_limit_pre)) (PreH23 : (temp_limit_pre <= INT_MAX)) (PreH24 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH25 : (cm_i32_code_count pc_pre )) (PreH26 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) )) ,
  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args))) (tail)) )
|--
  “ (args = (cons ((cm_args_head (args))) ((cm_args_tail (args))))) ” 
  &&  “ (cm_args_wf policy p f args slots ) ” 
  &&  “ (cm_args_counts_representable policy p fid_pre args ) ” 
  &&  “ (arg_pre <> 0) ” 
  &&  “ (args = (cons ((cm_args_head (args))) ((cm_args_tail (args))))) ” 
  &&  “ (arg_pre <> 0) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (cm_args_wf policy p f args slots ) ” 
  &&  “ (cm_args_counts_representable policy p fid_pre args ) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ ((slot_pre + (Zlength (args)) ) = scratch_pre) ” 
  &&  “ (0 <= scratch_pre) ” 
  &&  “ (scratch_pre <= temp_limit_pre) ” 
  &&  “ ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count pc_pre ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) ) ”
  &&  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args))) (tail)) )
.

Definition cm_emit_args_store_plan_partial_solve_wit_3 := cm_emit_args_store_plan_partial_solve_wit_3_pure -> cm_emit_args_store_plan_partial_solve_wit_3_aux.

Definition cm_emit_args_store_plan_partial_solve_wit_4_pure := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (scratch_pre: Z) (slot_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (slots: (@list cm_slot_d)) (args: (@list cm_expr)) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (np: Z) (ep: Z) (PreH1 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH2 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH3 : (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) )) (PreH4 : (cm_args_counts_representable policy p fid_pre (cm_args_tail (args)) )) (PreH5 : (arg_pre <> 0)) (PreH6 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH7 : (arg_pre <> 0)) (PreH8 : (cm_wf_program policy cg p )) (PreH9 : (cm_typed_program policy p )) (PreH10 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH11 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH12 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH13 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH14 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH15 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH16 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH17 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH18 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH19 : (cm_args_wf policy p f args slots )) (PreH20 : (cm_args_counts_representable policy p fid_pre args )) (PreH21 : (0 <= slot_pre)) (PreH22 : ((slot_pre + (Zlength (args)) ) = scratch_pre)) (PreH23 : (0 <= scratch_pre)) (PreH24 : (scratch_pre <= temp_limit_pre)) (PreH25 : ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre)) (PreH26 : (0 <= temp_limit_pre)) (PreH27 : (temp_limit_pre <= INT_MAX)) (PreH28 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH29 : (cm_i32_code_count pc_pre )) (PreH30 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) )) ,
  ((( &( "head_count" ) )) # Int  |->_)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "scratch" ) )) # Int  |-> scratch_pre)
  **  ((( &( "temp_limit" ) )) # Int  |-> temp_limit_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args))) (tail)) )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_expr_wf policy p f (cm_args_head (args)) ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ”
.

Definition cm_emit_args_store_plan_partial_solve_wit_4_aux := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (scratch_pre: Z) (slot_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (slots: (@list cm_slot_d)) (args: (@list cm_expr)) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (np: Z) (ep: Z) (PreH1 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH2 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH3 : (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) )) (PreH4 : (cm_args_counts_representable policy p fid_pre (cm_args_tail (args)) )) (PreH5 : (arg_pre <> 0)) (PreH6 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH7 : (arg_pre <> 0)) (PreH8 : (cm_wf_program policy cg p )) (PreH9 : (cm_typed_program policy p )) (PreH10 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH11 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH12 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH13 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH14 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH15 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH16 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH17 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH18 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH19 : (cm_args_wf policy p f args slots )) (PreH20 : (cm_args_counts_representable policy p fid_pre args )) (PreH21 : (0 <= slot_pre)) (PreH22 : ((slot_pre + (Zlength (args)) ) = scratch_pre)) (PreH23 : (0 <= scratch_pre)) (PreH24 : (scratch_pre <= temp_limit_pre)) (PreH25 : ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre)) (PreH26 : (0 <= temp_limit_pre)) (PreH27 : (temp_limit_pre <= INT_MAX)) (PreH28 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH29 : (cm_i32_code_count pc_pre )) (PreH30 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) )) ,
  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args))) (tail)) )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_expr_wf policy p f (cm_args_head (args)) ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_expr_wf policy p f (cm_args_head (args)) ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) ) ” 
  &&  “ (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) ) ” 
  &&  “ (cm_args_counts_representable policy p fid_pre (cm_args_tail (args)) ) ” 
  &&  “ (arg_pre <> 0) ” 
  &&  “ (args = (cons ((cm_args_head (args))) ((cm_args_tail (args))))) ” 
  &&  “ (arg_pre <> 0) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (cm_args_wf policy p f args slots ) ” 
  &&  “ (cm_args_counts_representable policy p fid_pre args ) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ ((slot_pre + (Zlength (args)) ) = scratch_pre) ” 
  &&  “ (0 <= scratch_pre) ” 
  &&  “ (scratch_pre <= temp_limit_pre) ” 
  &&  “ ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count pc_pre ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args))) (tail)) )
.

Definition cm_emit_args_store_plan_partial_solve_wit_4 := cm_emit_args_store_plan_partial_solve_wit_4_pure -> cm_emit_args_store_plan_partial_solve_wit_4_aux.

Definition cm_emit_args_store_plan_partial_solve_wit_5_pure := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (scratch_pre: Z) (slot_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (slots: (@list cm_slot_d)) (args: (@list cm_expr)) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (np: Z) (ep: Z) (retval: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH3 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH4 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH5 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH6 : (retval = (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))))) (PreH7 : (cm_i32_code_count retval )) (PreH8 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH9 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH10 : (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) )) (PreH11 : (cm_args_counts_representable policy p fid_pre (cm_args_tail (args)) )) (PreH12 : (arg_pre <> 0)) (PreH13 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH14 : (arg_pre <> 0)) (PreH15 : (cm_wf_program policy cg p )) (PreH16 : (cm_typed_program policy p )) (PreH17 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH18 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH19 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH20 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH21 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH22 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH23 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH24 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH25 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH26 : (cm_args_wf policy p f args slots )) (PreH27 : (cm_args_counts_representable policy p fid_pre args )) (PreH28 : (0 <= slot_pre)) (PreH29 : ((slot_pre + (Zlength (args)) ) = scratch_pre)) (PreH30 : (0 <= scratch_pre)) (PreH31 : (scratch_pre <= temp_limit_pre)) (PreH32 : ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre)) (PreH33 : (0 <= temp_limit_pre)) (PreH34 : (temp_limit_pre <= INT_MAX)) (PreH35 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH36 : (cm_i32_code_count pc_pre )) (PreH37 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  ((( &( "head_count" ) )) # Int  |-> retval)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "scratch" ) )) # Int  |-> scratch_pre)
  **  ((( &( "temp_limit" ) )) # Int  |-> temp_limit_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args))) (tail)) )
|--
  “ (args = (cons ((cm_args_head (args))) ((cm_args_tail (args))))) ” 
  &&  “ ((cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) = (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args))))) ”
.

Definition cm_emit_args_store_plan_partial_solve_wit_5_aux := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (scratch_pre: Z) (slot_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (slots: (@list cm_slot_d)) (args: (@list cm_expr)) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (np: Z) (ep: Z) (retval: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH3 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH4 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH5 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH6 : (retval = (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))))) (PreH7 : (cm_i32_code_count retval )) (PreH8 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH9 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH10 : (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) )) (PreH11 : (cm_args_counts_representable policy p fid_pre (cm_args_tail (args)) )) (PreH12 : (arg_pre <> 0)) (PreH13 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH14 : (arg_pre <> 0)) (PreH15 : (cm_wf_program policy cg p )) (PreH16 : (cm_typed_program policy p )) (PreH17 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH18 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH19 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH20 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH21 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH22 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH23 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH24 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH25 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH26 : (cm_args_wf policy p f args slots )) (PreH27 : (cm_args_counts_representable policy p fid_pre args )) (PreH28 : (0 <= slot_pre)) (PreH29 : ((slot_pre + (Zlength (args)) ) = scratch_pre)) (PreH30 : (0 <= scratch_pre)) (PreH31 : (scratch_pre <= temp_limit_pre)) (PreH32 : ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre)) (PreH33 : (0 <= temp_limit_pre)) (PreH34 : (temp_limit_pre <= INT_MAX)) (PreH35 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH36 : (cm_i32_code_count pc_pre )) (PreH37 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  ((( &( "head_count" ) )) # Int  |-> retval)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args))) (tail)) )
|--
  “ (args = (cons ((cm_args_head (args))) ((cm_args_tail (args))))) ” 
  &&  “ ((cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) = (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args))))) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_expr_wf policy p f (cm_args_head (args)) ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (retval = (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args))))) ” 
  &&  “ (cm_i32_code_count retval ) ” 
  &&  “ (cm_expr_wf policy p f (cm_args_head (args)) ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) ) ” 
  &&  “ (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) ) ” 
  &&  “ (cm_args_counts_representable policy p fid_pre (cm_args_tail (args)) ) ” 
  &&  “ (arg_pre <> 0) ” 
  &&  “ (args = (cons ((cm_args_head (args))) ((cm_args_tail (args))))) ” 
  &&  “ (arg_pre <> 0) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (cm_args_wf policy p f args slots ) ” 
  &&  “ (cm_args_counts_representable policy p fid_pre args ) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ ((slot_pre + (Zlength (args)) ) = scratch_pre) ” 
  &&  “ (0 <= scratch_pre) ” 
  &&  “ (scratch_pre <= temp_limit_pre) ” 
  &&  “ ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count pc_pre ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) ) ”
  &&  ((( &( "head_count" ) )) # Int  |-> (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))))
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
.

Definition cm_emit_args_store_plan_partial_solve_wit_5 := cm_emit_args_store_plan_partial_solve_wit_5_pure -> cm_emit_args_store_plan_partial_solve_wit_5_aux.

Definition cm_emit_args_store_plan_partial_solve_wit_6_pure := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (scratch_pre: Z) (slot_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (slots: (@list cm_slot_d)) (args: (@list cm_expr)) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (np: Z) (ep: Z) (retval: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH3 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH4 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH5 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH6 : (retval = (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))))) (PreH7 : (cm_i32_code_count retval )) (PreH8 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH9 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH10 : (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) )) (PreH11 : (cm_args_counts_representable policy p fid_pre (cm_args_tail (args)) )) (PreH12 : (arg_pre <> 0)) (PreH13 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH14 : (arg_pre <> 0)) (PreH15 : (cm_wf_program policy cg p )) (PreH16 : (cm_typed_program policy p )) (PreH17 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH18 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH19 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH20 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH21 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH22 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH23 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH24 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH25 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH26 : (cm_args_wf policy p f args slots )) (PreH27 : (cm_args_counts_representable policy p fid_pre args )) (PreH28 : (0 <= slot_pre)) (PreH29 : ((slot_pre + (Zlength (args)) ) = scratch_pre)) (PreH30 : (0 <= scratch_pre)) (PreH31 : (scratch_pre <= temp_limit_pre)) (PreH32 : ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre)) (PreH33 : (0 <= temp_limit_pre)) (PreH34 : (temp_limit_pre <= INT_MAX)) (PreH35 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH36 : (cm_i32_code_count pc_pre )) (PreH37 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) )) ,
  ((( &( "scratch" ) )) # Int  |-> scratch_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "head_count" ) )) # Int  |-> (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))))
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0))) ((app ((cm_temp_store_code (policy) (p) (fid_pre) (slot_pre))) ((app ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args))))) (tail)))))) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "temp_limit" ) )) # Int  |-> temp_limit_pre)
|--
  “ (args = (cons ((cm_args_head (args))) ((cm_args_tail (args))))) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ ((slot_pre + (Zlength (args)) ) = scratch_pre) ” 
  &&  “ (scratch_pre <= temp_limit_pre) ” 
  &&  “ ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count pc_pre ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) ) ” 
  &&  “ ((cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) = (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args))))) ”
.

Definition cm_emit_args_store_plan_partial_solve_wit_6_aux := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (scratch_pre: Z) (slot_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (slots: (@list cm_slot_d)) (args: (@list cm_expr)) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (np: Z) (ep: Z) (retval: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH3 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH4 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH5 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH6 : (retval = (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))))) (PreH7 : (cm_i32_code_count retval )) (PreH8 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH9 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH10 : (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) )) (PreH11 : (cm_args_counts_representable policy p fid_pre (cm_args_tail (args)) )) (PreH12 : (arg_pre <> 0)) (PreH13 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH14 : (arg_pre <> 0)) (PreH15 : (cm_wf_program policy cg p )) (PreH16 : (cm_typed_program policy p )) (PreH17 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH18 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH19 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH20 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH21 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH22 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH23 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH24 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH25 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH26 : (cm_args_wf policy p f args slots )) (PreH27 : (cm_args_counts_representable policy p fid_pre args )) (PreH28 : (0 <= slot_pre)) (PreH29 : ((slot_pre + (Zlength (args)) ) = scratch_pre)) (PreH30 : (0 <= scratch_pre)) (PreH31 : (scratch_pre <= temp_limit_pre)) (PreH32 : ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre)) (PreH33 : (0 <= temp_limit_pre)) (PreH34 : (temp_limit_pre <= INT_MAX)) (PreH35 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH36 : (cm_i32_code_count pc_pre )) (PreH37 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) )) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0))) ((app ((cm_temp_store_code (policy) (p) (fid_pre) (slot_pre))) ((app ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args))))) (tail)))))) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
|--
  “ (args = (cons ((cm_args_head (args))) ((cm_args_tail (args))))) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ ((slot_pre + (Zlength (args)) ) = scratch_pre) ” 
  &&  “ (scratch_pre <= temp_limit_pre) ” 
  &&  “ ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count pc_pre ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) ) ” 
  &&  “ ((cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) = (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args))))) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_expr_wf policy p f (cm_args_head (args)) ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (retval = (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args))))) ” 
  &&  “ (cm_i32_code_count retval ) ” 
  &&  “ (cm_expr_wf policy p f (cm_args_head (args)) ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) ) ” 
  &&  “ (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) ) ” 
  &&  “ (cm_args_counts_representable policy p fid_pre (cm_args_tail (args)) ) ” 
  &&  “ (arg_pre <> 0) ” 
  &&  “ (args = (cons ((cm_args_head (args))) ((cm_args_tail (args))))) ” 
  &&  “ (arg_pre <> 0) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (cm_args_wf policy p f args slots ) ” 
  &&  “ (cm_args_counts_representable policy p fid_pre args ) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ ((slot_pre + (Zlength (args)) ) = scratch_pre) ” 
  &&  “ (0 <= scratch_pre) ” 
  &&  “ (scratch_pre <= temp_limit_pre) ” 
  &&  “ ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count pc_pre ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) ) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0))) ((app ((cm_temp_store_code (policy) (p) (fid_pre) (slot_pre))) ((app ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args))))) (tail)))))) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
.

Definition cm_emit_args_store_plan_partial_solve_wit_6 := cm_emit_args_store_plan_partial_solve_wit_6_pure -> cm_emit_args_store_plan_partial_solve_wit_6_aux.

Definition cm_emit_args_store_plan_partial_solve_wit_7_pure := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (scratch_pre: Z) (slot_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (slots: (@list cm_slot_d)) (args: (@list cm_expr)) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (np: Z) (ep: Z) (retval: Z) (PreH1 : (0 <= (slot_pre + 1 ))) (PreH2 : ((slot_pre + 1 ) <= INT_MAX)) (PreH3 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) = scratch_pre)) (PreH4 : ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre)) (PreH5 : ((scratch_pre + (cm_adepth ((cm_args_apair ((cm_args_tail (args)))))) ) <= temp_limit_pre)) (PreH6 : ((cm_temp_offset (policy) (p) (fid_pre) (slot_pre)) <= INT_MAX)) (PreH7 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) )) (PreH8 : (0 <= (pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ))) (PreH9 : ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) <= INT_MAX)) (PreH10 : (0 <= ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ))) (PreH11 : (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) <= INT_MAX)) (PreH12 : (cm_i32_code_count ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) )) (PreH13 : (cm_i32_code_count (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args)))))) ) )) (PreH14 : (cm_wf_program policy cg p )) (PreH15 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH16 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH17 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH18 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH19 : (retval = (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))))) (PreH20 : (cm_i32_code_count retval )) (PreH21 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH22 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH23 : (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) )) (PreH24 : (cm_args_counts_representable policy p fid_pre (cm_args_tail (args)) )) (PreH25 : (arg_pre <> 0)) (PreH26 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH27 : (arg_pre <> 0)) (PreH28 : (cm_wf_program policy cg p )) (PreH29 : (cm_typed_program policy p )) (PreH30 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH31 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH32 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH33 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH34 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH35 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH36 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH37 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH38 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH39 : (cm_args_wf policy p f args slots )) (PreH40 : (cm_args_counts_representable policy p fid_pre args )) (PreH41 : (0 <= slot_pre)) (PreH42 : ((slot_pre + (Zlength (args)) ) = scratch_pre)) (PreH43 : (0 <= scratch_pre)) (PreH44 : (scratch_pre <= temp_limit_pre)) (PreH45 : ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre)) (PreH46 : (0 <= temp_limit_pre)) (PreH47 : (temp_limit_pre <= INT_MAX)) (PreH48 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH49 : (cm_i32_code_count pc_pre )) (PreH50 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) )) ,
  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "scratch" ) )) # Int  |-> scratch_pre)
  **  ((( &( "temp_limit" ) )) # Int  |-> temp_limit_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "head_count" ) )) # Int  |-> (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))))
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0))) ((app ((cm_temp_store_code (policy) (p) (fid_pre) (slot_pre))) ((app ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args))))) (tail)))))) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (cm_expr_wf policy p f (cm_args_head (args)) ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) ) ” 
  &&  “ (0 <= scratch_pre) ” 
  &&  “ (scratch_pre <= temp_limit_pre) ” 
  &&  “ ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count pc_pre ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) ) ”
.

Definition cm_emit_args_store_plan_partial_solve_wit_7_aux := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (scratch_pre: Z) (slot_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (slots: (@list cm_slot_d)) (args: (@list cm_expr)) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (np: Z) (ep: Z) (retval: Z) (PreH1 : (0 <= (slot_pre + 1 ))) (PreH2 : ((slot_pre + 1 ) <= INT_MAX)) (PreH3 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) = scratch_pre)) (PreH4 : ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre)) (PreH5 : ((scratch_pre + (cm_adepth ((cm_args_apair ((cm_args_tail (args)))))) ) <= temp_limit_pre)) (PreH6 : ((cm_temp_offset (policy) (p) (fid_pre) (slot_pre)) <= INT_MAX)) (PreH7 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) )) (PreH8 : (0 <= (pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ))) (PreH9 : ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) <= INT_MAX)) (PreH10 : (0 <= ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ))) (PreH11 : (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) <= INT_MAX)) (PreH12 : (cm_i32_code_count ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) )) (PreH13 : (cm_i32_code_count (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args)))))) ) )) (PreH14 : (cm_wf_program policy cg p )) (PreH15 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH16 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH17 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH18 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH19 : (retval = (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))))) (PreH20 : (cm_i32_code_count retval )) (PreH21 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH22 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH23 : (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) )) (PreH24 : (cm_args_counts_representable policy p fid_pre (cm_args_tail (args)) )) (PreH25 : (arg_pre <> 0)) (PreH26 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH27 : (arg_pre <> 0)) (PreH28 : (cm_wf_program policy cg p )) (PreH29 : (cm_typed_program policy p )) (PreH30 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH31 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH32 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH33 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH34 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH35 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH36 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH37 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH38 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH39 : (cm_args_wf policy p f args slots )) (PreH40 : (cm_args_counts_representable policy p fid_pre args )) (PreH41 : (0 <= slot_pre)) (PreH42 : ((slot_pre + (Zlength (args)) ) = scratch_pre)) (PreH43 : (0 <= scratch_pre)) (PreH44 : (scratch_pre <= temp_limit_pre)) (PreH45 : ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre)) (PreH46 : (0 <= temp_limit_pre)) (PreH47 : (temp_limit_pre <= INT_MAX)) (PreH48 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH49 : (cm_i32_code_count pc_pre )) (PreH50 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) )) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0))) ((app ((cm_temp_store_code (policy) (p) (fid_pre) (slot_pre))) ((app ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args))))) (tail)))))) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (cm_expr_wf policy p f (cm_args_head (args)) ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) ) ” 
  &&  “ (0 <= scratch_pre) ” 
  &&  “ (scratch_pre <= temp_limit_pre) ” 
  &&  “ ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count pc_pre ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) ) ” 
  &&  “ (0 <= (slot_pre + 1 )) ” 
  &&  “ ((slot_pre + 1 ) <= INT_MAX) ” 
  &&  “ (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) = scratch_pre) ” 
  &&  “ ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre) ” 
  &&  “ ((scratch_pre + (cm_adepth ((cm_args_apair ((cm_args_tail (args)))))) ) <= temp_limit_pre) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (slot_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) ) ” 
  &&  “ (0 <= (pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) )) ” 
  &&  “ ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) <= INT_MAX) ” 
  &&  “ (0 <= ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ” 
  &&  “ (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) ) ” 
  &&  “ (cm_i32_code_count (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args)))))) ) ) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_expr_wf policy p f (cm_args_head (args)) ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (retval = (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args))))) ” 
  &&  “ (cm_i32_code_count retval ) ” 
  &&  “ (cm_expr_wf policy p f (cm_args_head (args)) ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) ) ” 
  &&  “ (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) ) ” 
  &&  “ (cm_args_counts_representable policy p fid_pre (cm_args_tail (args)) ) ” 
  &&  “ (arg_pre <> 0) ” 
  &&  “ (args = (cons ((cm_args_head (args))) ((cm_args_tail (args))))) ” 
  &&  “ (arg_pre <> 0) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (cm_args_wf policy p f args slots ) ” 
  &&  “ (cm_args_counts_representable policy p fid_pre args ) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ ((slot_pre + (Zlength (args)) ) = scratch_pre) ” 
  &&  “ (0 <= scratch_pre) ” 
  &&  “ (scratch_pre <= temp_limit_pre) ” 
  &&  “ ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count pc_pre ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0))) ((app ((cm_temp_store_code (policy) (p) (fid_pre) (slot_pre))) ((app ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args))))) (tail)))))) )
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
.

Definition cm_emit_args_store_plan_partial_solve_wit_7 := cm_emit_args_store_plan_partial_solve_wit_7_pure -> cm_emit_args_store_plan_partial_solve_wit_7_aux.

Definition cm_emit_args_store_plan_partial_solve_wit_8_pure := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (scratch_pre: Z) (slot_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (slots: (@list cm_slot_d)) (args: (@list cm_expr)) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (np: Z) (ep: Z) (retval: Z) (PreH1 : (0 <= 0)) (PreH2 : (0 <= 1)) (PreH3 : (cm_wf_program policy cg p )) (PreH4 : (cm_typed_program policy p )) (PreH5 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH6 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH7 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH8 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH9 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH10 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH11 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH12 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH13 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH14 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH15 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH16 : (0 <= scratch_pre)) (PreH17 : (scratch_pre <= temp_limit_pre)) (PreH18 : ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre)) (PreH19 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH20 : (cm_i32_code_count pc_pre )) (PreH21 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) )) (PreH22 : (0 <= (slot_pre + 1 ))) (PreH23 : ((slot_pre + 1 ) <= INT_MAX)) (PreH24 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) = scratch_pre)) (PreH25 : ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre)) (PreH26 : ((scratch_pre + (cm_adepth ((cm_args_apair ((cm_args_tail (args)))))) ) <= temp_limit_pre)) (PreH27 : ((cm_temp_offset (policy) (p) (fid_pre) (slot_pre)) <= INT_MAX)) (PreH28 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) )) (PreH29 : (0 <= (pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ))) (PreH30 : ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) <= INT_MAX)) (PreH31 : (0 <= ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ))) (PreH32 : (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) <= INT_MAX)) (PreH33 : (cm_i32_code_count ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) )) (PreH34 : (cm_i32_code_count (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args)))))) ) )) (PreH35 : (cm_wf_program policy cg p )) (PreH36 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH37 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH38 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH39 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH40 : (retval = (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))))) (PreH41 : (cm_i32_code_count retval )) (PreH42 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH43 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH44 : (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) )) (PreH45 : (cm_args_counts_representable policy p fid_pre (cm_args_tail (args)) )) (PreH46 : (arg_pre <> 0)) (PreH47 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH48 : (arg_pre <> 0)) (PreH49 : (cm_wf_program policy cg p )) (PreH50 : (cm_typed_program policy p )) (PreH51 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH52 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH53 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH54 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH55 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH56 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH57 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH58 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH59 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH60 : (cm_args_wf policy p f args slots )) (PreH61 : (cm_args_counts_representable policy p fid_pre args )) (PreH62 : (0 <= slot_pre)) (PreH63 : ((slot_pre + (Zlength (args)) ) = scratch_pre)) (PreH64 : (0 <= scratch_pre)) (PreH65 : (scratch_pre <= temp_limit_pre)) (PreH66 : ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre)) (PreH67 : (0 <= temp_limit_pre)) (PreH68 : (temp_limit_pre <= INT_MAX)) (PreH69 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH70 : (cm_i32_code_count pc_pre )) (PreH71 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) (app ((cm_temp_store_code (policy) (p) (fid_pre) (slot_pre))) ((app ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args))))) (tail)))) )
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "scratch" ) )) # Int  |-> scratch_pre)
  **  ((( &( "temp_limit" ) )) # Int  |-> temp_limit_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "head_count" ) )) # Int  |-> (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))))
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
|--
  “ (0 <= slot_pre) ” 
  &&  “ ((cm_program_structs (p)) = (cm_program_structs (p))) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (slot_pre)) <= INT_MAX) ”
.

Definition cm_emit_args_store_plan_partial_solve_wit_8_aux := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (scratch_pre: Z) (slot_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (slots: (@list cm_slot_d)) (args: (@list cm_expr)) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (np: Z) (ep: Z) (retval: Z) (PreH1 : (0 <= 0)) (PreH2 : (0 <= 1)) (PreH3 : (cm_wf_program policy cg p )) (PreH4 : (cm_typed_program policy p )) (PreH5 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH6 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH7 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH8 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH9 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH10 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH11 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH12 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH13 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH14 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH15 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH16 : (0 <= scratch_pre)) (PreH17 : (scratch_pre <= temp_limit_pre)) (PreH18 : ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre)) (PreH19 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH20 : (cm_i32_code_count pc_pre )) (PreH21 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) )) (PreH22 : (0 <= (slot_pre + 1 ))) (PreH23 : ((slot_pre + 1 ) <= INT_MAX)) (PreH24 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) = scratch_pre)) (PreH25 : ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre)) (PreH26 : ((scratch_pre + (cm_adepth ((cm_args_apair ((cm_args_tail (args)))))) ) <= temp_limit_pre)) (PreH27 : ((cm_temp_offset (policy) (p) (fid_pre) (slot_pre)) <= INT_MAX)) (PreH28 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) )) (PreH29 : (0 <= (pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ))) (PreH30 : ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) <= INT_MAX)) (PreH31 : (0 <= ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ))) (PreH32 : (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) <= INT_MAX)) (PreH33 : (cm_i32_code_count ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) )) (PreH34 : (cm_i32_code_count (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args)))))) ) )) (PreH35 : (cm_wf_program policy cg p )) (PreH36 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH37 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH38 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH39 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH40 : (retval = (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))))) (PreH41 : (cm_i32_code_count retval )) (PreH42 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH43 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH44 : (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) )) (PreH45 : (cm_args_counts_representable policy p fid_pre (cm_args_tail (args)) )) (PreH46 : (arg_pre <> 0)) (PreH47 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH48 : (arg_pre <> 0)) (PreH49 : (cm_wf_program policy cg p )) (PreH50 : (cm_typed_program policy p )) (PreH51 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH52 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH53 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH54 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH55 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH56 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH57 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH58 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH59 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH60 : (cm_args_wf policy p f args slots )) (PreH61 : (cm_args_counts_representable policy p fid_pre args )) (PreH62 : (0 <= slot_pre)) (PreH63 : ((slot_pre + (Zlength (args)) ) = scratch_pre)) (PreH64 : (0 <= scratch_pre)) (PreH65 : (scratch_pre <= temp_limit_pre)) (PreH66 : ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre)) (PreH67 : (0 <= temp_limit_pre)) (PreH68 : (temp_limit_pre <= INT_MAX)) (PreH69 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH70 : (cm_i32_code_count pc_pre )) (PreH71 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) (app ((cm_temp_store_code (policy) (p) (fid_pre) (slot_pre))) ((app ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args))))) (tail)))) )
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
|--
  “ (0 <= slot_pre) ” 
  &&  “ ((cm_program_structs (p)) = (cm_program_structs (p))) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (slot_pre)) <= INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (cm_expr_wf policy p f (cm_args_head (args)) ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) ) ” 
  &&  “ (0 <= scratch_pre) ” 
  &&  “ (scratch_pre <= temp_limit_pre) ” 
  &&  “ ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count pc_pre ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) ) ” 
  &&  “ (0 <= (slot_pre + 1 )) ” 
  &&  “ ((slot_pre + 1 ) <= INT_MAX) ” 
  &&  “ (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) = scratch_pre) ” 
  &&  “ ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre) ” 
  &&  “ ((scratch_pre + (cm_adepth ((cm_args_apair ((cm_args_tail (args)))))) ) <= temp_limit_pre) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (slot_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) ) ” 
  &&  “ (0 <= (pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) )) ” 
  &&  “ ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) <= INT_MAX) ” 
  &&  “ (0 <= ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ” 
  &&  “ (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) ) ” 
  &&  “ (cm_i32_code_count (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args)))))) ) ) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_expr_wf policy p f (cm_args_head (args)) ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (retval = (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args))))) ” 
  &&  “ (cm_i32_code_count retval ) ” 
  &&  “ (cm_expr_wf policy p f (cm_args_head (args)) ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) ) ” 
  &&  “ (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) ) ” 
  &&  “ (cm_args_counts_representable policy p fid_pre (cm_args_tail (args)) ) ” 
  &&  “ (arg_pre <> 0) ” 
  &&  “ (args = (cons ((cm_args_head (args))) ((cm_args_tail (args))))) ” 
  &&  “ (arg_pre <> 0) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (cm_args_wf policy p f args slots ) ” 
  &&  “ (cm_args_counts_representable policy p fid_pre args ) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ ((slot_pre + (Zlength (args)) ) = scratch_pre) ” 
  &&  “ (0 <= scratch_pre) ” 
  &&  “ (scratch_pre <= temp_limit_pre) ” 
  &&  “ ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count pc_pre ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) ) ”
  &&  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) (app ((cm_temp_store_code (policy) (p) (fid_pre) (slot_pre))) ((app ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args))))) (tail)))) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
.

Definition cm_emit_args_store_plan_partial_solve_wit_8 := cm_emit_args_store_plan_partial_solve_wit_8_pure -> cm_emit_args_store_plan_partial_solve_wit_8_aux.

Definition cm_emit_args_store_plan_partial_solve_wit_9_pure := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (scratch_pre: Z) (slot_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (slots: (@list cm_slot_d)) (args: (@list cm_expr)) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (np: Z) (ep: Z) (retval: Z) (PreH1 : (0 <= slot_pre)) (PreH2 : ((cm_program_structs (p)) = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH5 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid_pre) (slot_pre)) <= INT_MAX)) (PreH9 : (0 <= 0)) (PreH10 : (0 <= 1)) (PreH11 : (cm_wf_program policy cg p )) (PreH12 : (cm_typed_program policy p )) (PreH13 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH14 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH15 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH16 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH17 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH18 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH19 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH20 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH21 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH22 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH23 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH24 : (0 <= scratch_pre)) (PreH25 : (scratch_pre <= temp_limit_pre)) (PreH26 : ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre)) (PreH27 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH28 : (cm_i32_code_count pc_pre )) (PreH29 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) )) (PreH30 : (0 <= (slot_pre + 1 ))) (PreH31 : ((slot_pre + 1 ) <= INT_MAX)) (PreH32 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) = scratch_pre)) (PreH33 : ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre)) (PreH34 : ((scratch_pre + (cm_adepth ((cm_args_apair ((cm_args_tail (args)))))) ) <= temp_limit_pre)) (PreH35 : ((cm_temp_offset (policy) (p) (fid_pre) (slot_pre)) <= INT_MAX)) (PreH36 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) )) (PreH37 : (0 <= (pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ))) (PreH38 : ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) <= INT_MAX)) (PreH39 : (0 <= ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ))) (PreH40 : (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) <= INT_MAX)) (PreH41 : (cm_i32_code_count ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) )) (PreH42 : (cm_i32_code_count (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args)))))) ) )) (PreH43 : (cm_wf_program policy cg p )) (PreH44 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH45 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH46 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH47 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH48 : (retval = (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))))) (PreH49 : (cm_i32_code_count retval )) (PreH50 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH51 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH52 : (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) )) (PreH53 : (cm_args_counts_representable policy p fid_pre (cm_args_tail (args)) )) (PreH54 : (arg_pre <> 0)) (PreH55 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH56 : (arg_pre <> 0)) (PreH57 : (cm_wf_program policy cg p )) (PreH58 : (cm_typed_program policy p )) (PreH59 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH60 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH61 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH62 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH63 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH64 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH65 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH66 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH67 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH68 : (cm_args_wf policy p f args slots )) (PreH69 : (cm_args_counts_representable policy p fid_pre args )) (PreH70 : (0 <= slot_pre)) (PreH71 : ((slot_pre + (Zlength (args)) ) = scratch_pre)) (PreH72 : (0 <= scratch_pre)) (PreH73 : (scratch_pre <= temp_limit_pre)) (PreH74 : ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre)) (PreH75 : (0 <= temp_limit_pre)) (PreH76 : (temp_limit_pre <= INT_MAX)) (PreH77 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH78 : (cm_i32_code_count pc_pre )) (PreH79 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) )) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app (done) ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0))))) ((cm_temp_store_code (policy) (p) (fid_pre) (slot_pre)))) (app ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args))))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "scratch" ) )) # Int  |-> scratch_pre)
  **  ((( &( "temp_limit" ) )) # Int  |-> temp_limit_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "head_count" ) )) # Int  |-> (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))))
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) ) ” 
  &&  “ (cm_args_counts_representable policy p fid_pre (cm_args_tail (args)) ) ” 
  &&  “ (0 <= (slot_pre + 1 )) ” 
  &&  “ (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) = scratch_pre) ” 
  &&  “ (0 <= scratch_pre) ” 
  &&  “ (scratch_pre <= temp_limit_pre) ” 
  &&  “ ((scratch_pre + (cm_adepth ((cm_args_apair ((cm_args_tail (args)))))) ) <= temp_limit_pre) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) ) ” 
  &&  “ (cm_i32_code_count (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args)))))) ) ) ” 
  &&  “ (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) <= temp_limit_pre) ” 
  &&  “ (0 <= ((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) )) ”
.

Definition cm_emit_args_store_plan_partial_solve_wit_9_aux := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (scratch_pre: Z) (slot_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (slots: (@list cm_slot_d)) (args: (@list cm_expr)) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (np: Z) (ep: Z) (retval: Z) (PreH1 : (0 <= slot_pre)) (PreH2 : ((cm_program_structs (p)) = (cm_program_structs (p)))) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH5 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH6 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH7 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH8 : ((cm_temp_offset (policy) (p) (fid_pre) (slot_pre)) <= INT_MAX)) (PreH9 : (0 <= 0)) (PreH10 : (0 <= 1)) (PreH11 : (cm_wf_program policy cg p )) (PreH12 : (cm_typed_program policy p )) (PreH13 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH14 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH15 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH16 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH17 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH18 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH19 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH20 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH21 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH22 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH23 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH24 : (0 <= scratch_pre)) (PreH25 : (scratch_pre <= temp_limit_pre)) (PreH26 : ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre)) (PreH27 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH28 : (cm_i32_code_count pc_pre )) (PreH29 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) )) (PreH30 : (0 <= (slot_pre + 1 ))) (PreH31 : ((slot_pre + 1 ) <= INT_MAX)) (PreH32 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) = scratch_pre)) (PreH33 : ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre)) (PreH34 : ((scratch_pre + (cm_adepth ((cm_args_apair ((cm_args_tail (args)))))) ) <= temp_limit_pre)) (PreH35 : ((cm_temp_offset (policy) (p) (fid_pre) (slot_pre)) <= INT_MAX)) (PreH36 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) )) (PreH37 : (0 <= (pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ))) (PreH38 : ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) <= INT_MAX)) (PreH39 : (0 <= ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ))) (PreH40 : (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) <= INT_MAX)) (PreH41 : (cm_i32_code_count ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) )) (PreH42 : (cm_i32_code_count (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args)))))) ) )) (PreH43 : (cm_wf_program policy cg p )) (PreH44 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH45 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH46 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH47 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH48 : (retval = (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))))) (PreH49 : (cm_i32_code_count retval )) (PreH50 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH51 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH52 : (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) )) (PreH53 : (cm_args_counts_representable policy p fid_pre (cm_args_tail (args)) )) (PreH54 : (arg_pre <> 0)) (PreH55 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH56 : (arg_pre <> 0)) (PreH57 : (cm_wf_program policy cg p )) (PreH58 : (cm_typed_program policy p )) (PreH59 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH60 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH61 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH62 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH63 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH64 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH65 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH66 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH67 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH68 : (cm_args_wf policy p f args slots )) (PreH69 : (cm_args_counts_representable policy p fid_pre args )) (PreH70 : (0 <= slot_pre)) (PreH71 : ((slot_pre + (Zlength (args)) ) = scratch_pre)) (PreH72 : (0 <= scratch_pre)) (PreH73 : (scratch_pre <= temp_limit_pre)) (PreH74 : ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre)) (PreH75 : (0 <= temp_limit_pre)) (PreH76 : (temp_limit_pre <= INT_MAX)) (PreH77 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH78 : (cm_i32_code_count pc_pre )) (PreH79 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) )) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app (done) ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0))))) ((cm_temp_store_code (policy) (p) (fid_pre) (slot_pre)))) (app ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args))))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) ) ” 
  &&  “ (cm_args_counts_representable policy p fid_pre (cm_args_tail (args)) ) ” 
  &&  “ (0 <= (slot_pre + 1 )) ” 
  &&  “ (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) = scratch_pre) ” 
  &&  “ (0 <= scratch_pre) ” 
  &&  “ (scratch_pre <= temp_limit_pre) ” 
  &&  “ ((scratch_pre + (cm_adepth ((cm_args_apair ((cm_args_tail (args)))))) ) <= temp_limit_pre) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) ) ” 
  &&  “ (cm_i32_code_count (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args)))))) ) ) ” 
  &&  “ (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) <= temp_limit_pre) ” 
  &&  “ (0 <= ((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) )) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (slot_pre)) <= INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (cm_expr_wf policy p f (cm_args_head (args)) ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) ) ” 
  &&  “ (0 <= scratch_pre) ” 
  &&  “ (scratch_pre <= temp_limit_pre) ” 
  &&  “ ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count pc_pre ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) ) ” 
  &&  “ (0 <= (slot_pre + 1 )) ” 
  &&  “ ((slot_pre + 1 ) <= INT_MAX) ” 
  &&  “ (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) = scratch_pre) ” 
  &&  “ ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre) ” 
  &&  “ ((scratch_pre + (cm_adepth ((cm_args_apair ((cm_args_tail (args)))))) ) <= temp_limit_pre) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (slot_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) ) ” 
  &&  “ (0 <= (pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) )) ” 
  &&  “ ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) <= INT_MAX) ” 
  &&  “ (0 <= ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ” 
  &&  “ (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) ) ” 
  &&  “ (cm_i32_code_count (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args)))))) ) ) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_expr_wf policy p f (cm_args_head (args)) ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (retval = (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args))))) ” 
  &&  “ (cm_i32_code_count retval ) ” 
  &&  “ (cm_expr_wf policy p f (cm_args_head (args)) ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) ) ” 
  &&  “ (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) ) ” 
  &&  “ (cm_args_counts_representable policy p fid_pre (cm_args_tail (args)) ) ” 
  &&  “ (arg_pre <> 0) ” 
  &&  “ (args = (cons ((cm_args_head (args))) ((cm_args_tail (args))))) ” 
  &&  “ (arg_pre <> 0) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (cm_args_wf policy p f args slots ) ” 
  &&  “ (cm_args_counts_representable policy p fid_pre args ) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ ((slot_pre + (Zlength (args)) ) = scratch_pre) ” 
  &&  “ (0 <= scratch_pre) ” 
  &&  “ (scratch_pre <= temp_limit_pre) ” 
  &&  “ ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count pc_pre ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app (done) ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0))))) ((cm_temp_store_code (policy) (p) (fid_pre) (slot_pre)))) (app ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args))))) (tail)) )
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
.

Definition cm_emit_args_store_plan_partial_solve_wit_9 := cm_emit_args_store_plan_partial_solve_wit_9_pure -> cm_emit_args_store_plan_partial_solve_wit_9_aux.

Definition cm_emit_args_store_plan_partial_solve_wit_10_pure := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (scratch_pre: Z) (slot_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (slots: (@list cm_slot_d)) (args: (@list cm_expr)) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (np: Z) (ep: Z) (retval: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_typed_program policy p )) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH5 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH6 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH7 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH8 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH9 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH10 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH11 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH12 : (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) )) (PreH13 : (cm_args_counts_representable policy p fid_pre (cm_args_tail (args)) )) (PreH14 : (0 <= (slot_pre + 1 ))) (PreH15 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) = scratch_pre)) (PreH16 : (0 <= scratch_pre)) (PreH17 : (scratch_pre <= temp_limit_pre)) (PreH18 : ((scratch_pre + (cm_adepth ((cm_args_apair ((cm_args_tail (args)))))) ) <= temp_limit_pre)) (PreH19 : (0 <= temp_limit_pre)) (PreH20 : (temp_limit_pre <= INT_MAX)) (PreH21 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH22 : (cm_i32_code_count ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) )) (PreH23 : (cm_i32_code_count (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args)))))) ) )) (PreH24 : (0 <= slot_pre)) (PreH25 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH26 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH27 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH28 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH29 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH30 : ((cm_temp_offset (policy) (p) (fid_pre) (slot_pre)) <= INT_MAX)) (PreH31 : (0 <= 0)) (PreH32 : (0 <= 1)) (PreH33 : (cm_wf_program policy cg p )) (PreH34 : (cm_typed_program policy p )) (PreH35 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH36 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH37 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH38 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH39 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH40 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH41 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH42 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH43 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH44 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH45 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH46 : (0 <= scratch_pre)) (PreH47 : (scratch_pre <= temp_limit_pre)) (PreH48 : ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre)) (PreH49 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH50 : (cm_i32_code_count pc_pre )) (PreH51 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) )) (PreH52 : (0 <= (slot_pre + 1 ))) (PreH53 : ((slot_pre + 1 ) <= INT_MAX)) (PreH54 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) = scratch_pre)) (PreH55 : ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre)) (PreH56 : ((scratch_pre + (cm_adepth ((cm_args_apair ((cm_args_tail (args)))))) ) <= temp_limit_pre)) (PreH57 : ((cm_temp_offset (policy) (p) (fid_pre) (slot_pre)) <= INT_MAX)) (PreH58 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) )) (PreH59 : (0 <= (pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ))) (PreH60 : ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) <= INT_MAX)) (PreH61 : (0 <= ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ))) (PreH62 : (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) <= INT_MAX)) (PreH63 : (cm_i32_code_count ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) )) (PreH64 : (cm_i32_code_count (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args)))))) ) )) (PreH65 : (cm_wf_program policy cg p )) (PreH66 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH67 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH68 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH69 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH70 : (retval = (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))))) (PreH71 : (cm_i32_code_count retval )) (PreH72 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH73 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH74 : (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) )) (PreH75 : (cm_args_counts_representable policy p fid_pre (cm_args_tail (args)) )) (PreH76 : (arg_pre <> 0)) (PreH77 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH78 : (arg_pre <> 0)) (PreH79 : (cm_wf_program policy cg p )) (PreH80 : (cm_typed_program policy p )) (PreH81 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH82 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH83 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH84 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH85 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH86 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH87 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH88 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH89 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH90 : (cm_args_wf policy p f args slots )) (PreH91 : (cm_args_counts_representable policy p fid_pre args )) (PreH92 : (0 <= slot_pre)) (PreH93 : ((slot_pre + (Zlength (args)) ) = scratch_pre)) (PreH94 : (0 <= scratch_pre)) (PreH95 : (scratch_pre <= temp_limit_pre)) (PreH96 : ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre)) (PreH97 : (0 <= temp_limit_pre)) (PreH98 : (temp_limit_pre <= INT_MAX)) (PreH99 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH100 : (cm_i32_code_count pc_pre )) (PreH101 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app (done) ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0))))) ((cm_temp_store_code (policy) (p) (fid_pre) (slot_pre))))) ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args)))))) tail )
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "scratch" ) )) # Int  |-> scratch_pre)
  **  ((( &( "temp_limit" ) )) # Int  |-> temp_limit_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "head_count" ) )) # Int  |-> (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))))
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
|--
  “ (arg_pre <> 0) ” 
  &&  “ (args = (cons ((cm_args_head (args))) ((cm_args_tail (args))))) ”
.

Definition cm_emit_args_store_plan_partial_solve_wit_10_aux := 
forall (emitter_pre: Z) (arg_pre: Z) (temp_limit_pre: Z) (scratch_pre: Z) (slot_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (slots: (@list cm_slot_d)) (args: (@list cm_expr)) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (np: Z) (ep: Z) (retval: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_typed_program policy p )) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH5 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH6 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH7 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH8 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH9 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH10 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH11 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH12 : (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) )) (PreH13 : (cm_args_counts_representable policy p fid_pre (cm_args_tail (args)) )) (PreH14 : (0 <= (slot_pre + 1 ))) (PreH15 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) = scratch_pre)) (PreH16 : (0 <= scratch_pre)) (PreH17 : (scratch_pre <= temp_limit_pre)) (PreH18 : ((scratch_pre + (cm_adepth ((cm_args_apair ((cm_args_tail (args)))))) ) <= temp_limit_pre)) (PreH19 : (0 <= temp_limit_pre)) (PreH20 : (temp_limit_pre <= INT_MAX)) (PreH21 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH22 : (cm_i32_code_count ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) )) (PreH23 : (cm_i32_code_count (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args)))))) ) )) (PreH24 : (0 <= slot_pre)) (PreH25 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH26 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH27 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH28 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH29 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH30 : ((cm_temp_offset (policy) (p) (fid_pre) (slot_pre)) <= INT_MAX)) (PreH31 : (0 <= 0)) (PreH32 : (0 <= 1)) (PreH33 : (cm_wf_program policy cg p )) (PreH34 : (cm_typed_program policy p )) (PreH35 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH36 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH37 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH38 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH39 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH40 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH41 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH42 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH43 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH44 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH45 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH46 : (0 <= scratch_pre)) (PreH47 : (scratch_pre <= temp_limit_pre)) (PreH48 : ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre)) (PreH49 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH50 : (cm_i32_code_count pc_pre )) (PreH51 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) )) (PreH52 : (0 <= (slot_pre + 1 ))) (PreH53 : ((slot_pre + 1 ) <= INT_MAX)) (PreH54 : (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) = scratch_pre)) (PreH55 : ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre)) (PreH56 : ((scratch_pre + (cm_adepth ((cm_args_apair ((cm_args_tail (args)))))) ) <= temp_limit_pre)) (PreH57 : ((cm_temp_offset (policy) (p) (fid_pre) (slot_pre)) <= INT_MAX)) (PreH58 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) )) (PreH59 : (0 <= (pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ))) (PreH60 : ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) <= INT_MAX)) (PreH61 : (0 <= ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ))) (PreH62 : (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) <= INT_MAX)) (PreH63 : (cm_i32_code_count ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) )) (PreH64 : (cm_i32_code_count (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args)))))) ) )) (PreH65 : (cm_wf_program policy cg p )) (PreH66 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH67 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH68 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH69 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH70 : (retval = (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))))) (PreH71 : (cm_i32_code_count retval )) (PreH72 : (cm_expr_wf policy p f (cm_args_head (args)) )) (PreH73 : (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) )) (PreH74 : (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) )) (PreH75 : (cm_args_counts_representable policy p fid_pre (cm_args_tail (args)) )) (PreH76 : (arg_pre <> 0)) (PreH77 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH78 : (arg_pre <> 0)) (PreH79 : (cm_wf_program policy cg p )) (PreH80 : (cm_typed_program policy p )) (PreH81 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH82 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH83 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH84 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH85 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH86 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH87 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH88 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH89 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH90 : (cm_args_wf policy p f args slots )) (PreH91 : (cm_args_counts_representable policy p fid_pre args )) (PreH92 : (0 <= slot_pre)) (PreH93 : ((slot_pre + (Zlength (args)) ) = scratch_pre)) (PreH94 : (0 <= scratch_pre)) (PreH95 : (scratch_pre <= temp_limit_pre)) (PreH96 : ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre)) (PreH97 : (0 <= temp_limit_pre)) (PreH98 : (temp_limit_pre <= INT_MAX)) (PreH99 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH100 : (cm_i32_code_count pc_pre )) (PreH101 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app (done) ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0))))) ((cm_temp_store_code (policy) (p) (fid_pre) (slot_pre))))) ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args)))))) tail )
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
|--
  “ (arg_pre <> 0) ” 
  &&  “ (args = (cons ((cm_args_head (args))) ((cm_args_tail (args))))) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) ) ” 
  &&  “ (cm_args_counts_representable policy p fid_pre (cm_args_tail (args)) ) ” 
  &&  “ (0 <= (slot_pre + 1 )) ” 
  &&  “ (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) = scratch_pre) ” 
  &&  “ (0 <= scratch_pre) ” 
  &&  “ (scratch_pre <= temp_limit_pre) ” 
  &&  “ ((scratch_pre + (cm_adepth ((cm_args_apair ((cm_args_tail (args)))))) ) <= temp_limit_pre) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) ) ” 
  &&  “ (cm_i32_code_count (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args)))))) ) ) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (slot_pre)) <= INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (cm_expr_wf policy p f (cm_args_head (args)) ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) ) ” 
  &&  “ (0 <= scratch_pre) ” 
  &&  “ (scratch_pre <= temp_limit_pre) ” 
  &&  “ ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count pc_pre ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) ) ” 
  &&  “ (0 <= (slot_pre + 1 )) ” 
  &&  “ ((slot_pre + 1 ) <= INT_MAX) ” 
  &&  “ (((slot_pre + 1 ) + (Zlength ((cm_args_tail (args)))) ) = scratch_pre) ” 
  &&  “ ((scratch_pre + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit_pre) ” 
  &&  “ ((scratch_pre + (cm_adepth ((cm_args_apair ((cm_args_tail (args)))))) ) <= temp_limit_pre) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (slot_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0)))) ) ) ” 
  &&  “ (0 <= (pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) )) ” 
  &&  “ ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) <= INT_MAX) ” 
  &&  “ (0 <= ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ” 
  &&  “ (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count ((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) ) ” 
  &&  “ (cm_i32_code_count (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 ) + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args)))))) ) ) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_expr_wf policy p f (cm_args_head (args)) ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (retval = (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args))))) ” 
  &&  “ (cm_i32_code_count retval ) ” 
  &&  “ (cm_expr_wf policy p f (cm_args_head (args)) ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre (cm_args_head (args)) ) ” 
  &&  “ (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) ) ” 
  &&  “ (cm_args_counts_representable policy p fid_pre (cm_args_tail (args)) ) ” 
  &&  “ (arg_pre <> 0) ” 
  &&  “ (args = (cons ((cm_args_head (args))) ((cm_args_tail (args))))) ” 
  &&  “ (arg_pre <> 0) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (cm_args_wf policy p f args slots ) ” 
  &&  “ (cm_args_counts_representable policy p fid_pre args ) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ ((slot_pre + (Zlength (args)) ) = scratch_pre) ” 
  &&  “ (0 <= scratch_pre) ” 
  &&  “ (scratch_pre <= temp_limit_pre) ” 
  &&  “ ((scratch_pre + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit_pre) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count pc_pre ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (slot_pre) (scratch_pre) (args)))) ) ) ”
  &&  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app (done) ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (scratch_pre) ((cm_args_head (args))) (0))))) ((cm_temp_store_code (policy) (p) (fid_pre) (slot_pre))))) ((cm_emit_args_store (policy) (p) (fid_pre) (((pc_pre + (cm_rvalue_code_count (policy) (p) (fid_pre) ((cm_args_head (args)))) ) + 5 )) ((slot_pre + 1 )) (scratch_pre) ((cm_args_tail (args)))))) tail )
.

Definition cm_emit_args_store_plan_partial_solve_wit_10 := cm_emit_args_store_plan_partial_solve_wit_10_pure -> cm_emit_args_store_plan_partial_solve_wit_10_aux.

Definition cm_emit_args_store_plan_which_implies_wit_1 := 
(
forall (arg_pre: Z) (args: (@list cm_expr)) (PreH1 : (arg_pre = 0)) ,
  (cm_arg_list_rep arg_pre args )
|--
  “ (args = (@nil cm_expr)) ”
  &&  (cm_arg_list_rep arg_pre args )
) \/
(
forall (arg_pre: Z) (args: (@list cm_expr)) (PreH1 : (arg_pre = 0)) ,
  TT && emp 
|--
  “ (args = (@nil cm_expr)) ”
  &&  emp
).

Definition cm_emit_args_store_plan_which_implies_wit_1_split_goal_1 := 
forall (arg_pre: Z) (args: (@list cm_expr)) (PreH1 : (arg_pre = 0)) ,
  (args = (@nil cm_expr))
.

Definition cm_emit_args_store_plan_which_implies_wit_2 := 
(
forall (args: (@list cm_expr)) (arg: Z) (PreH1 : (arg <> 0)) ,
  (cm_arg_list_rep arg args )
|--
  EX (np: Z)  (ep: Z) ,
  “ (arg <> 0) ” 
  &&  “ (args = (cons ((cm_args_head (args))) ((cm_args_tail (args))))) ”
  &&  ((&((arg)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
) \/
(
forall (args: (@list cm_expr)) (arg: Z) (PreH1 : (arg <> 0)) ,
  (cm_arg_list_rep arg args )
|--
  EX (np: Z)  (ep: Z) ,
  “ (arg <> 0) ” 
  &&  “ (args = (cons ((cm_args_head (args))) ((cm_args_tail (args))))) ”
  &&  ((&((arg)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
).

Definition cm_emit_args_store_plan_which_implies_wit_3 := 
(
forall (slots: (@list cm_slot_d)) (args: (@list cm_expr)) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (fid: Z) (PreH1 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH2 : (cm_args_wf policy p f args slots )) (PreH3 : (cm_args_counts_representable policy p fid args )) ,
  TT && emp 
|--
  “ (cm_expr_wf policy p f (cm_args_head (args)) ) ” 
  &&  “ (cm_expr_counts_representable policy p fid (cm_args_head (args)) ) ” 
  &&  “ (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) ) ” 
  &&  “ (cm_args_counts_representable policy p fid (cm_args_tail (args)) ) ”
  &&  emp
) \/
(
forall (slots: (@list cm_slot_d)) (args: (@list cm_expr)) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (fid: Z) (PreH1 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH2 : (cm_args_wf policy p f args slots )) (PreH3 : (cm_args_counts_representable policy p fid args )) ,
  TT && emp 
|--
  “ (cm_args_counts_representable policy p fid (cm_args_tail (args)) ) ” 
  &&  “ (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) ) ” 
  &&  “ (cm_expr_counts_representable policy p fid (cm_args_head (args)) ) ” 
  &&  “ (cm_expr_wf policy p f (cm_args_head (args)) ) ”
  &&  emp
).

Definition cm_emit_args_store_plan_which_implies_wit_3_split_goal_1 := 
forall (slots: (@list cm_slot_d)) (args: (@list cm_expr)) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (fid: Z) (PreH1 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH2 : (cm_args_wf policy p f args slots )) (PreH3 : (cm_args_counts_representable policy p fid args )) ,
  (cm_args_counts_representable policy p fid (cm_args_tail (args)) )
.

Definition cm_emit_args_store_plan_which_implies_wit_3_split_goal_2 := 
forall (slots: (@list cm_slot_d)) (args: (@list cm_expr)) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (fid: Z) (PreH1 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH2 : (cm_args_wf policy p f args slots )) (PreH3 : (cm_args_counts_representable policy p fid args )) ,
  (cm_args_wf policy p f (cm_args_tail (args)) (cm_call_slots_tail (slots)) )
.

Definition cm_emit_args_store_plan_which_implies_wit_3_split_goal_3 := 
forall (slots: (@list cm_slot_d)) (args: (@list cm_expr)) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (fid: Z) (PreH1 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH2 : (cm_args_wf policy p f args slots )) (PreH3 : (cm_args_counts_representable policy p fid args )) ,
  (cm_expr_counts_representable policy p fid (cm_args_head (args)) )
.

Definition cm_emit_args_store_plan_which_implies_wit_3_split_goal_4 := 
forall (slots: (@list cm_slot_d)) (args: (@list cm_expr)) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (fid: Z) (PreH1 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH2 : (cm_args_wf policy p f args slots )) (PreH3 : (cm_args_counts_representable policy p fid args )) ,
  (cm_expr_wf policy p f (cm_args_head (args)) )
.

Definition cm_emit_args_store_plan_which_implies_wit_4 := 
(
forall (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (args: (@list cm_expr)) (p: cm_program) (policy: cm_lookup_policy) (head_count: Z) (fid: Z) (scratch: Z) (slot: Z) (pc: Z) (emitter: Z) (PreH1 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH2 : (head_count = (cm_rvalue_code_count (policy) (p) (fid) ((cm_args_head (args)))))) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_emit_args_store (policy) (p) (fid) (pc) (slot) (scratch) (args))) (tail)) )
|--
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_expr_code_for (policy) (p) (fid) (pc) (scratch) ((cm_args_head (args))) (0))) ((app ((cm_temp_store_code (policy) (p) (fid) (slot))) ((app ((cm_emit_args_store (policy) (p) (fid) (((pc + head_count ) + 5 )) ((slot + 1 )) (scratch) ((cm_args_tail (args))))) (tail)))))) )
) \/
(
forall (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (args: (@list cm_expr)) (p: cm_program) (policy: cm_lookup_policy) (head_count: Z) (fid: Z) (scratch: Z) (slot: Z) (pc: Z) (emitter: Z) (PreH1 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH2 : (head_count = (cm_rvalue_code_count (policy) (p) (fid) ((cm_args_head (args)))))) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_emit_args_store (policy) (p) (fid) (pc) (slot) (scratch) (args))) (tail)) )
|--
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_expr_code_for (policy) (p) (fid) (pc) (scratch) ((cm_args_head (args))) (0))) ((app ((cm_temp_store_code (policy) (p) (fid) (slot))) ((app ((cm_emit_args_store (policy) (p) (fid) (((pc + head_count ) + 5 )) ((slot + 1 )) (scratch) ((cm_args_tail (args))))) (tail)))))) )
).

Definition cm_emit_args_store_plan_which_implies_wit_4_split_goal_spatial := 
forall (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (args: (@list cm_expr)) (p: cm_program) (policy: cm_lookup_policy) (head_count: Z) (fid: Z) (scratch: Z) (slot: Z) (pc: Z) (emitter: Z) (PreH1 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH2 : (head_count = (cm_rvalue_code_count (policy) (p) (fid) ((cm_args_head (args)))))) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_emit_args_store (policy) (p) (fid) (pc) (slot) (scratch) (args))) (tail)) )
|--
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_expr_code_for (policy) (p) (fid) (pc) (scratch) ((cm_args_head (args))) (0))) ((app ((cm_temp_store_code (policy) (p) (fid) (slot))) ((app ((cm_emit_args_store (policy) (p) (fid) (((pc + head_count ) + 5 )) ((slot + 1 )) (scratch) ((cm_args_tail (args))))) (tail)))))) )
.

Definition cm_emit_args_store_plan_which_implies_wit_5 := 
(
forall (args: (@list cm_expr)) (p: cm_program) (policy: cm_lookup_policy) (slot: Z) (scratch: Z) (temp_limit: Z) (fid: Z) (pc: Z) (head_count: Z) (PreH1 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH2 : (0 <= slot)) (PreH3 : ((slot + (Zlength (args)) ) = scratch)) (PreH4 : (scratch <= temp_limit)) (PreH5 : ((scratch + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit)) (PreH6 : (temp_limit <= INT_MAX)) (PreH7 : ((cm_temp_offset (policy) (p) (fid) (temp_limit)) <= INT_MAX)) (PreH8 : (cm_i32_code_count pc )) (PreH9 : (cm_i32_code_count (pc + (Zlength ((cm_emit_args_store (policy) (p) (fid) (pc) (slot) (scratch) (args)))) ) )) (PreH10 : (head_count = (cm_rvalue_code_count (policy) (p) (fid) ((cm_args_head (args)))))) ,
  TT && emp 
|--
  “ (0 <= (slot + 1 )) ” 
  &&  “ ((slot + 1 ) <= INT_MAX) ” 
  &&  “ (((slot + 1 ) + (Zlength ((cm_args_tail (args)))) ) = scratch) ” 
  &&  “ ((scratch + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit) ” 
  &&  “ ((scratch + (cm_adepth ((cm_args_apair ((cm_args_tail (args)))))) ) <= temp_limit) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (slot)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count (pc + (Zlength ((cm_expr_code_for (policy) (p) (fid) (pc) (scratch) ((cm_args_head (args))) (0)))) ) ) ” 
  &&  “ (0 <= (pc + head_count )) ” 
  &&  “ ((pc + head_count ) <= INT_MAX) ” 
  &&  “ (0 <= ((pc + head_count ) + 5 )) ” 
  &&  “ (((pc + head_count ) + 5 ) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count ((pc + head_count ) + 5 ) ) ” 
  &&  “ (cm_i32_code_count (((pc + head_count ) + 5 ) + (Zlength ((cm_emit_args_store (policy) (p) (fid) (((pc + head_count ) + 5 )) ((slot + 1 )) (scratch) ((cm_args_tail (args)))))) ) ) ”
  &&  emp
) \/
(
forall (args: (@list cm_expr)) (p: cm_program) (policy: cm_lookup_policy) (slot: Z) (scratch: Z) (temp_limit: Z) (fid: Z) (pc: Z) (head_count: Z) (PreH1 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH2 : (0 <= slot)) (PreH3 : ((slot + (Zlength (args)) ) = scratch)) (PreH4 : (scratch <= temp_limit)) (PreH5 : ((scratch + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit)) (PreH6 : (temp_limit <= INT_MAX)) (PreH7 : ((cm_temp_offset (policy) (p) (fid) (temp_limit)) <= INT_MAX)) (PreH8 : (cm_i32_code_count pc )) (PreH9 : (cm_i32_code_count (pc + (Zlength ((cm_emit_args_store (policy) (p) (fid) (pc) (slot) (scratch) (args)))) ) )) (PreH10 : (head_count = (cm_rvalue_code_count (policy) (p) (fid) ((cm_args_head (args)))))) ,
  TT && emp 
|--
  “ (cm_i32_code_count (((pc + head_count ) + 5 ) + (Zlength ((cm_emit_args_store (policy) (p) (fid) (((pc + head_count ) + 5 )) ((slot + 1 )) (scratch) ((cm_args_tail (args)))))) ) ) ” 
  &&  “ (cm_i32_code_count ((pc + head_count ) + 5 ) ) ” 
  &&  “ (((pc + head_count ) + 5 ) <= INT_MAX) ” 
  &&  “ (0 <= ((pc + head_count ) + 5 )) ” 
  &&  “ ((pc + head_count ) <= INT_MAX) ” 
  &&  “ (0 <= (pc + head_count )) ” 
  &&  “ (cm_i32_code_count (pc + (Zlength ((cm_expr_code_for (policy) (p) (fid) (pc) (scratch) ((cm_args_head (args))) (0)))) ) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid) (slot)) <= INT_MAX) ” 
  &&  “ ((scratch + (cm_adepth ((cm_args_apair ((cm_args_tail (args)))))) ) <= temp_limit) ” 
  &&  “ ((scratch + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit) ” 
  &&  “ (((slot + 1 ) + (Zlength ((cm_args_tail (args)))) ) = scratch) ” 
  &&  “ ((slot + 1 ) <= INT_MAX) ”
  &&  emp
).

Definition cm_emit_args_store_plan_which_implies_wit_5_split_goal_1 := 
forall (args: (@list cm_expr)) (p: cm_program) (policy: cm_lookup_policy) (slot: Z) (scratch: Z) (temp_limit: Z) (fid: Z) (pc: Z) (head_count: Z) (PreH1 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH2 : (0 <= slot)) (PreH3 : ((slot + (Zlength (args)) ) = scratch)) (PreH4 : (scratch <= temp_limit)) (PreH5 : ((scratch + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit)) (PreH6 : (temp_limit <= INT_MAX)) (PreH7 : ((cm_temp_offset (policy) (p) (fid) (temp_limit)) <= INT_MAX)) (PreH8 : (cm_i32_code_count pc )) (PreH9 : (cm_i32_code_count (pc + (Zlength ((cm_emit_args_store (policy) (p) (fid) (pc) (slot) (scratch) (args)))) ) )) (PreH10 : (head_count = (cm_rvalue_code_count (policy) (p) (fid) ((cm_args_head (args)))))) ,
  (cm_i32_code_count (((pc + head_count ) + 5 ) + (Zlength ((cm_emit_args_store (policy) (p) (fid) (((pc + head_count ) + 5 )) ((slot + 1 )) (scratch) ((cm_args_tail (args)))))) ) )
.

Definition cm_emit_args_store_plan_which_implies_wit_5_split_goal_2 := 
forall (args: (@list cm_expr)) (p: cm_program) (policy: cm_lookup_policy) (slot: Z) (scratch: Z) (temp_limit: Z) (fid: Z) (pc: Z) (head_count: Z) (PreH1 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH2 : (0 <= slot)) (PreH3 : ((slot + (Zlength (args)) ) = scratch)) (PreH4 : (scratch <= temp_limit)) (PreH5 : ((scratch + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit)) (PreH6 : (temp_limit <= INT_MAX)) (PreH7 : ((cm_temp_offset (policy) (p) (fid) (temp_limit)) <= INT_MAX)) (PreH8 : (cm_i32_code_count pc )) (PreH9 : (cm_i32_code_count (pc + (Zlength ((cm_emit_args_store (policy) (p) (fid) (pc) (slot) (scratch) (args)))) ) )) (PreH10 : (head_count = (cm_rvalue_code_count (policy) (p) (fid) ((cm_args_head (args)))))) ,
  (cm_i32_code_count ((pc + head_count ) + 5 ) )
.

Definition cm_emit_args_store_plan_which_implies_wit_5_split_goal_3 := 
forall (args: (@list cm_expr)) (p: cm_program) (policy: cm_lookup_policy) (slot: Z) (scratch: Z) (temp_limit: Z) (fid: Z) (pc: Z) (head_count: Z) (PreH1 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH2 : (0 <= slot)) (PreH3 : ((slot + (Zlength (args)) ) = scratch)) (PreH4 : (scratch <= temp_limit)) (PreH5 : ((scratch + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit)) (PreH6 : (temp_limit <= INT_MAX)) (PreH7 : ((cm_temp_offset (policy) (p) (fid) (temp_limit)) <= INT_MAX)) (PreH8 : (cm_i32_code_count pc )) (PreH9 : (cm_i32_code_count (pc + (Zlength ((cm_emit_args_store (policy) (p) (fid) (pc) (slot) (scratch) (args)))) ) )) (PreH10 : (head_count = (cm_rvalue_code_count (policy) (p) (fid) ((cm_args_head (args)))))) ,
  (((pc + head_count ) + 5 ) <= INT_MAX)
.

Definition cm_emit_args_store_plan_which_implies_wit_5_split_goal_4 := 
forall (args: (@list cm_expr)) (p: cm_program) (policy: cm_lookup_policy) (slot: Z) (scratch: Z) (temp_limit: Z) (fid: Z) (pc: Z) (head_count: Z) (PreH1 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH2 : (0 <= slot)) (PreH3 : ((slot + (Zlength (args)) ) = scratch)) (PreH4 : (scratch <= temp_limit)) (PreH5 : ((scratch + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit)) (PreH6 : (temp_limit <= INT_MAX)) (PreH7 : ((cm_temp_offset (policy) (p) (fid) (temp_limit)) <= INT_MAX)) (PreH8 : (cm_i32_code_count pc )) (PreH9 : (cm_i32_code_count (pc + (Zlength ((cm_emit_args_store (policy) (p) (fid) (pc) (slot) (scratch) (args)))) ) )) (PreH10 : (head_count = (cm_rvalue_code_count (policy) (p) (fid) ((cm_args_head (args)))))) ,
  (0 <= ((pc + head_count ) + 5 ))
.

Definition cm_emit_args_store_plan_which_implies_wit_5_split_goal_5 := 
forall (args: (@list cm_expr)) (p: cm_program) (policy: cm_lookup_policy) (slot: Z) (scratch: Z) (temp_limit: Z) (fid: Z) (pc: Z) (head_count: Z) (PreH1 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH2 : (0 <= slot)) (PreH3 : ((slot + (Zlength (args)) ) = scratch)) (PreH4 : (scratch <= temp_limit)) (PreH5 : ((scratch + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit)) (PreH6 : (temp_limit <= INT_MAX)) (PreH7 : ((cm_temp_offset (policy) (p) (fid) (temp_limit)) <= INT_MAX)) (PreH8 : (cm_i32_code_count pc )) (PreH9 : (cm_i32_code_count (pc + (Zlength ((cm_emit_args_store (policy) (p) (fid) (pc) (slot) (scratch) (args)))) ) )) (PreH10 : (head_count = (cm_rvalue_code_count (policy) (p) (fid) ((cm_args_head (args)))))) ,
  ((pc + head_count ) <= INT_MAX)
.

Definition cm_emit_args_store_plan_which_implies_wit_5_split_goal_6 := 
forall (args: (@list cm_expr)) (p: cm_program) (policy: cm_lookup_policy) (slot: Z) (scratch: Z) (temp_limit: Z) (fid: Z) (pc: Z) (head_count: Z) (PreH1 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH2 : (0 <= slot)) (PreH3 : ((slot + (Zlength (args)) ) = scratch)) (PreH4 : (scratch <= temp_limit)) (PreH5 : ((scratch + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit)) (PreH6 : (temp_limit <= INT_MAX)) (PreH7 : ((cm_temp_offset (policy) (p) (fid) (temp_limit)) <= INT_MAX)) (PreH8 : (cm_i32_code_count pc )) (PreH9 : (cm_i32_code_count (pc + (Zlength ((cm_emit_args_store (policy) (p) (fid) (pc) (slot) (scratch) (args)))) ) )) (PreH10 : (head_count = (cm_rvalue_code_count (policy) (p) (fid) ((cm_args_head (args)))))) ,
  (0 <= (pc + head_count ))
.

Definition cm_emit_args_store_plan_which_implies_wit_5_split_goal_7 := 
forall (args: (@list cm_expr)) (p: cm_program) (policy: cm_lookup_policy) (slot: Z) (scratch: Z) (temp_limit: Z) (fid: Z) (pc: Z) (head_count: Z) (PreH1 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH2 : (0 <= slot)) (PreH3 : ((slot + (Zlength (args)) ) = scratch)) (PreH4 : (scratch <= temp_limit)) (PreH5 : ((scratch + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit)) (PreH6 : (temp_limit <= INT_MAX)) (PreH7 : ((cm_temp_offset (policy) (p) (fid) (temp_limit)) <= INT_MAX)) (PreH8 : (cm_i32_code_count pc )) (PreH9 : (cm_i32_code_count (pc + (Zlength ((cm_emit_args_store (policy) (p) (fid) (pc) (slot) (scratch) (args)))) ) )) (PreH10 : (head_count = (cm_rvalue_code_count (policy) (p) (fid) ((cm_args_head (args)))))) ,
  (cm_i32_code_count (pc + (Zlength ((cm_expr_code_for (policy) (p) (fid) (pc) (scratch) ((cm_args_head (args))) (0)))) ) )
.

Definition cm_emit_args_store_plan_which_implies_wit_5_split_goal_8 := 
forall (args: (@list cm_expr)) (p: cm_program) (policy: cm_lookup_policy) (slot: Z) (scratch: Z) (temp_limit: Z) (fid: Z) (pc: Z) (head_count: Z) (PreH1 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH2 : (0 <= slot)) (PreH3 : ((slot + (Zlength (args)) ) = scratch)) (PreH4 : (scratch <= temp_limit)) (PreH5 : ((scratch + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit)) (PreH6 : (temp_limit <= INT_MAX)) (PreH7 : ((cm_temp_offset (policy) (p) (fid) (temp_limit)) <= INT_MAX)) (PreH8 : (cm_i32_code_count pc )) (PreH9 : (cm_i32_code_count (pc + (Zlength ((cm_emit_args_store (policy) (p) (fid) (pc) (slot) (scratch) (args)))) ) )) (PreH10 : (head_count = (cm_rvalue_code_count (policy) (p) (fid) ((cm_args_head (args)))))) ,
  ((cm_temp_offset (policy) (p) (fid) (slot)) <= INT_MAX)
.

Definition cm_emit_args_store_plan_which_implies_wit_5_split_goal_9 := 
forall (args: (@list cm_expr)) (p: cm_program) (policy: cm_lookup_policy) (slot: Z) (scratch: Z) (temp_limit: Z) (fid: Z) (pc: Z) (head_count: Z) (PreH1 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH2 : (0 <= slot)) (PreH3 : ((slot + (Zlength (args)) ) = scratch)) (PreH4 : (scratch <= temp_limit)) (PreH5 : ((scratch + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit)) (PreH6 : (temp_limit <= INT_MAX)) (PreH7 : ((cm_temp_offset (policy) (p) (fid) (temp_limit)) <= INT_MAX)) (PreH8 : (cm_i32_code_count pc )) (PreH9 : (cm_i32_code_count (pc + (Zlength ((cm_emit_args_store (policy) (p) (fid) (pc) (slot) (scratch) (args)))) ) )) (PreH10 : (head_count = (cm_rvalue_code_count (policy) (p) (fid) ((cm_args_head (args)))))) ,
  ((scratch + (cm_adepth ((cm_args_apair ((cm_args_tail (args)))))) ) <= temp_limit)
.

Definition cm_emit_args_store_plan_which_implies_wit_5_split_goal_10 := 
forall (args: (@list cm_expr)) (p: cm_program) (policy: cm_lookup_policy) (slot: Z) (scratch: Z) (temp_limit: Z) (fid: Z) (pc: Z) (head_count: Z) (PreH1 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH2 : (0 <= slot)) (PreH3 : ((slot + (Zlength (args)) ) = scratch)) (PreH4 : (scratch <= temp_limit)) (PreH5 : ((scratch + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit)) (PreH6 : (temp_limit <= INT_MAX)) (PreH7 : ((cm_temp_offset (policy) (p) (fid) (temp_limit)) <= INT_MAX)) (PreH8 : (cm_i32_code_count pc )) (PreH9 : (cm_i32_code_count (pc + (Zlength ((cm_emit_args_store (policy) (p) (fid) (pc) (slot) (scratch) (args)))) ) )) (PreH10 : (head_count = (cm_rvalue_code_count (policy) (p) (fid) ((cm_args_head (args)))))) ,
  ((scratch + (cm_expr_temps_for ((cm_args_head (args))) (0)) ) <= temp_limit)
.

Definition cm_emit_args_store_plan_which_implies_wit_5_split_goal_11 := 
forall (args: (@list cm_expr)) (p: cm_program) (policy: cm_lookup_policy) (slot: Z) (scratch: Z) (temp_limit: Z) (fid: Z) (pc: Z) (head_count: Z) (PreH1 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH2 : (0 <= slot)) (PreH3 : ((slot + (Zlength (args)) ) = scratch)) (PreH4 : (scratch <= temp_limit)) (PreH5 : ((scratch + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit)) (PreH6 : (temp_limit <= INT_MAX)) (PreH7 : ((cm_temp_offset (policy) (p) (fid) (temp_limit)) <= INT_MAX)) (PreH8 : (cm_i32_code_count pc )) (PreH9 : (cm_i32_code_count (pc + (Zlength ((cm_emit_args_store (policy) (p) (fid) (pc) (slot) (scratch) (args)))) ) )) (PreH10 : (head_count = (cm_rvalue_code_count (policy) (p) (fid) ((cm_args_head (args)))))) ,
  (((slot + 1 ) + (Zlength ((cm_args_tail (args)))) ) = scratch)
.

Definition cm_emit_args_store_plan_which_implies_wit_5_split_goal_12 := 
forall (args: (@list cm_expr)) (p: cm_program) (policy: cm_lookup_policy) (slot: Z) (scratch: Z) (temp_limit: Z) (fid: Z) (pc: Z) (head_count: Z) (PreH1 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) (PreH2 : (0 <= slot)) (PreH3 : ((slot + (Zlength (args)) ) = scratch)) (PreH4 : (scratch <= temp_limit)) (PreH5 : ((scratch + (cm_adepth ((cm_args_apair (args)))) ) <= temp_limit)) (PreH6 : (temp_limit <= INT_MAX)) (PreH7 : ((cm_temp_offset (policy) (p) (fid) (temp_limit)) <= INT_MAX)) (PreH8 : (cm_i32_code_count pc )) (PreH9 : (cm_i32_code_count (pc + (Zlength ((cm_emit_args_store (policy) (p) (fid) (pc) (slot) (scratch) (args)))) ) )) (PreH10 : (head_count = (cm_rvalue_code_count (policy) (p) (fid) ((cm_args_head (args)))))) ,
  ((slot + 1 ) <= INT_MAX)
.

Definition cm_emit_args_store_plan_which_implies_wit_6 := 
(
forall (args: (@list cm_expr)) (np: Z) (ep: Z) (arg: Z) (PreH1 : (arg <> 0)) (PreH2 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) ,
  ((&((arg)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
|--
  (cm_arg_list_rep arg args )
) \/
(
forall (args: (@list cm_expr)) (np: Z) (ep: Z) (arg: Z) (PreH1 : (arg <> 0)) (PreH2 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) ,
  ((&((arg)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
|--
  (cm_arg_list_rep arg args )
).

Definition cm_emit_args_store_plan_which_implies_wit_6_split_goal_spatial := 
forall (args: (@list cm_expr)) (np: Z) (ep: Z) (arg: Z) (PreH1 : (arg <> 0)) (PreH2 : (args = (cons ((cm_args_head (args))) ((cm_args_tail (args)))))) ,
  ((&((arg)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep (cm_args_head (args)) )
  **  (cm_arg_list_rep np (cm_args_tail (args)) )
|--
  (cm_arg_list_rep arg args )
.

(*----- Function cm_emit_call_expr -----*)

Definition cm_emit_call_expr_safety_wit_1 := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_limit_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (retval: Z) (PreH1 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e)))))) ) )) (PreH2 : (cm_rep_args_safe (cm_call_args (e)) )) (PreH3 : (retval = (cm_rep_args_length ((cm_call_args (e)))))) (PreH4 : (0 <= (cm_rep_expr_value (e)))) (PreH5 : ((cm_rep_expr_value (e)) <= INT_MAX)) (PreH6 : (cm_args_wf policy p f (cm_call_args (e)) (cm_function_params ((cm_function_at (policy) ((cm_rep_expr_value (e))) ((cm_program_functions (p)))))) )) (PreH7 : (cm_args_counts_representable policy p fid_pre (cm_call_args (e)) )) (PreH8 : (cm_rep_args_safe (cm_call_args (e)) )) (PreH9 : ((cm_rep_args_length ((cm_call_args (e)))) = (Zlength ((cm_call_args (e)))))) (PreH10 : (0 <= temp_limit_pre)) (PreH11 : (temp_limit_pre <= INT_MAX)) (PreH12 : (0 <= (temp_pre + (Zlength ((cm_call_args (e)))) ))) (PreH13 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre)) (PreH14 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= INT_MAX)) (PreH15 : (((temp_pre + (Zlength ((cm_call_args (e)))) ) + (cm_adepth ((cm_args_apair ((cm_call_args (e)))))) ) <= temp_limit_pre)) (PreH16 : (expr_pre <> 0)) (PreH17 : (lvalue_pre = 0)) (PreH18 : ((cm_rep_expr_kind (e)) = 8)) (PreH19 : (0 <= lvalue_pre)) (PreH20 : (lvalue_pre <= 1)) (PreH21 : (cm_wf_program policy cg p )) (PreH22 : (cm_typed_program policy p )) (PreH23 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH24 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH25 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH26 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH27 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH28 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH29 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH30 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH31 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH32 : (cm_expr_wf policy p f e )) (PreH33 : (cm_expr_counts_representable policy p fid_pre e )) (PreH34 : (0 <= temp_pre)) (PreH35 : (temp_pre <= temp_limit_pre)) (PreH36 : ((temp_pre + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit_pre)) (PreH37 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH38 : (cm_i32_code_count pc_pre )) (PreH39 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) ) )) ,
  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "count" ) )) # Int  |-> (Zlength ((cm_call_args (e)))))
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e))))) ((app ((cm_emit_args_reload (policy) (p) (fid_pre) (temp_pre) ((cm_call_args (e))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) ((cm_rep_expr_value (e))))))) (tail)))))) )
  **  (cm_arg_list_rep xargs (cm_call_args (e)) )
  **  ((( &( "temp_limit" ) )) # Int  |-> temp_limit_pre)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
|--
  “ ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (temp_pre + (Zlength ((cm_call_args (e)))) )) ”
.

Definition cm_emit_call_expr_return_wit_1 := 
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_limit_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (0 <= temp_pre)) (PreH2 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre)) (PreH3 : (0 <= temp_limit_pre)) (PreH4 : (temp_limit_pre <= INT_MAX)) (PreH5 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH6 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH7 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH8 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH9 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH10 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH11 : (cm_wf_program policy cg p )) (PreH12 : (cm_typed_program policy p )) (PreH13 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH14 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH15 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH16 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH17 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH18 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH19 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH20 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH21 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH22 : (cm_args_wf policy p f (cm_call_args (e)) (cm_function_params ((cm_function_at (policy) ((cm_rep_expr_value (e))) ((cm_program_functions (p)))))) )) (PreH23 : (cm_args_counts_representable policy p fid_pre (cm_call_args (e)) )) (PreH24 : (0 <= temp_pre)) (PreH25 : (0 <= (temp_pre + (Zlength ((cm_call_args (e)))) ))) (PreH26 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre)) (PreH27 : (((temp_pre + (Zlength ((cm_call_args (e)))) ) + (cm_adepth ((cm_args_apair ((cm_call_args (e)))))) ) <= temp_limit_pre)) (PreH28 : (0 <= temp_limit_pre)) (PreH29 : (temp_limit_pre <= INT_MAX)) (PreH30 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH31 : (cm_i32_code_count pc_pre )) (PreH32 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e)))))) ) )) (PreH33 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e)))))) ) )) (PreH34 : (cm_rep_args_safe (cm_call_args (e)) )) (PreH35 : (retval = (cm_rep_args_length ((cm_call_args (e)))))) (PreH36 : (0 <= (cm_rep_expr_value (e)))) (PreH37 : ((cm_rep_expr_value (e)) <= INT_MAX)) (PreH38 : (cm_args_wf policy p f (cm_call_args (e)) (cm_function_params ((cm_function_at (policy) ((cm_rep_expr_value (e))) ((cm_program_functions (p)))))) )) (PreH39 : (cm_args_counts_representable policy p fid_pre (cm_call_args (e)) )) (PreH40 : (cm_rep_args_safe (cm_call_args (e)) )) (PreH41 : ((cm_rep_args_length ((cm_call_args (e)))) = (Zlength ((cm_call_args (e)))))) (PreH42 : (0 <= temp_limit_pre)) (PreH43 : (temp_limit_pre <= INT_MAX)) (PreH44 : (0 <= (temp_pre + (Zlength ((cm_call_args (e)))) ))) (PreH45 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre)) (PreH46 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= INT_MAX)) (PreH47 : (((temp_pre + (Zlength ((cm_call_args (e)))) ) + (cm_adepth ((cm_args_apair ((cm_call_args (e)))))) ) <= temp_limit_pre)) (PreH48 : (expr_pre <> 0)) (PreH49 : (lvalue_pre = 0)) (PreH50 : ((cm_rep_expr_kind (e)) = 8)) (PreH51 : (0 <= lvalue_pre)) (PreH52 : (lvalue_pre <= 1)) (PreH53 : (cm_wf_program policy cg p )) (PreH54 : (cm_typed_program policy p )) (PreH55 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH56 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH57 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH58 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH59 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH60 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH61 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH62 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH63 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH64 : (cm_expr_wf policy p f e )) (PreH65 : (cm_expr_counts_representable policy p fid_pre e )) (PreH66 : (0 <= temp_pre)) (PreH67 : (temp_pre <= temp_limit_pre)) (PreH68 : ((temp_pre + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit_pre)) (PreH69 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH70 : (cm_i32_code_count pc_pre )) (PreH71 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) ) )) ,
  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app (done) ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e))))))) ((cm_emit_args_reload (policy) (p) (fid_pre) (temp_pre) ((cm_call_args (e))))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) ((cm_rep_expr_value (e))))))) ((@nil tvm_inst))))) tail )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ ((cm_rep_expr_kind (e)) = 8) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ (0 <= temp_pre) ” 
  &&  “ (temp_pre <= temp_limit_pre) ” 
  &&  “ ((temp_pre + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit_pre) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count pc_pre ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) ) ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) tail )
) \/
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_limit_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (0 <= temp_pre)) (PreH2 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre)) (PreH3 : (0 <= temp_limit_pre)) (PreH4 : (temp_limit_pre <= INT_MAX)) (PreH5 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH6 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH7 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH8 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH9 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH10 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH11 : (cm_wf_program policy cg p )) (PreH12 : (cm_typed_program policy p )) (PreH13 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH14 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH15 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH16 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH17 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH18 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH19 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH20 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH21 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH22 : (cm_args_wf policy p f (cm_call_args (e)) (cm_function_params ((cm_function_at (policy) ((cm_rep_expr_value (e))) ((cm_program_functions (p)))))) )) (PreH23 : (cm_args_counts_representable policy p fid_pre (cm_call_args (e)) )) (PreH24 : (0 <= temp_pre)) (PreH25 : (0 <= (temp_pre + (Zlength ((cm_call_args (e)))) ))) (PreH26 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre)) (PreH27 : (((temp_pre + (Zlength ((cm_call_args (e)))) ) + (cm_adepth ((cm_args_apair ((cm_call_args (e)))))) ) <= temp_limit_pre)) (PreH28 : (0 <= temp_limit_pre)) (PreH29 : (temp_limit_pre <= INT_MAX)) (PreH30 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH31 : (cm_i32_code_count pc_pre )) (PreH32 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e)))))) ) )) (PreH33 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e)))))) ) )) (PreH34 : (cm_rep_args_safe (cm_call_args (e)) )) (PreH35 : (retval = (cm_rep_args_length ((cm_call_args (e)))))) (PreH36 : (0 <= (cm_rep_expr_value (e)))) (PreH37 : ((cm_rep_expr_value (e)) <= INT_MAX)) (PreH38 : (cm_args_wf policy p f (cm_call_args (e)) (cm_function_params ((cm_function_at (policy) ((cm_rep_expr_value (e))) ((cm_program_functions (p)))))) )) (PreH39 : (cm_args_counts_representable policy p fid_pre (cm_call_args (e)) )) (PreH40 : (cm_rep_args_safe (cm_call_args (e)) )) (PreH41 : ((cm_rep_args_length ((cm_call_args (e)))) = (Zlength ((cm_call_args (e)))))) (PreH42 : (0 <= temp_limit_pre)) (PreH43 : (temp_limit_pre <= INT_MAX)) (PreH44 : (0 <= (temp_pre + (Zlength ((cm_call_args (e)))) ))) (PreH45 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre)) (PreH46 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= INT_MAX)) (PreH47 : (((temp_pre + (Zlength ((cm_call_args (e)))) ) + (cm_adepth ((cm_args_apair ((cm_call_args (e)))))) ) <= temp_limit_pre)) (PreH48 : (expr_pre <> 0)) (PreH49 : (lvalue_pre = 0)) (PreH50 : ((cm_rep_expr_kind (e)) = 8)) (PreH51 : (0 <= lvalue_pre)) (PreH52 : (lvalue_pre <= 1)) (PreH53 : (cm_wf_program policy cg p )) (PreH54 : (cm_typed_program policy p )) (PreH55 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH56 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH57 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH58 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH59 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH60 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH61 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH62 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH63 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH64 : (cm_expr_wf policy p f e )) (PreH65 : (cm_expr_counts_representable policy p fid_pre e )) (PreH66 : (0 <= temp_pre)) (PreH67 : (temp_pre <= temp_limit_pre)) (PreH68 : ((temp_pre + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit_pre)) (PreH69 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH70 : (cm_i32_code_count pc_pre )) (PreH71 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) ) )) ,
  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app (done) ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e))))))) ((cm_emit_args_reload (policy) (p) (fid_pre) (temp_pre) ((cm_call_args (e))))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) ((cm_rep_expr_value (e))))))) ((@nil tvm_inst))))) tail )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) tail )
).

Definition cm_emit_call_expr_return_wit_1_split_goal_spatial := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_limit_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (0 <= temp_pre)) (PreH2 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre)) (PreH3 : (0 <= temp_limit_pre)) (PreH4 : (temp_limit_pre <= INT_MAX)) (PreH5 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH6 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH7 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH8 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH9 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH10 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH11 : (cm_wf_program policy cg p )) (PreH12 : (cm_typed_program policy p )) (PreH13 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH14 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH15 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH16 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH17 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH18 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH19 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH20 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH21 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH22 : (cm_args_wf policy p f (cm_call_args (e)) (cm_function_params ((cm_function_at (policy) ((cm_rep_expr_value (e))) ((cm_program_functions (p)))))) )) (PreH23 : (cm_args_counts_representable policy p fid_pre (cm_call_args (e)) )) (PreH24 : (0 <= temp_pre)) (PreH25 : (0 <= (temp_pre + (Zlength ((cm_call_args (e)))) ))) (PreH26 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre)) (PreH27 : (((temp_pre + (Zlength ((cm_call_args (e)))) ) + (cm_adepth ((cm_args_apair ((cm_call_args (e)))))) ) <= temp_limit_pre)) (PreH28 : (0 <= temp_limit_pre)) (PreH29 : (temp_limit_pre <= INT_MAX)) (PreH30 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH31 : (cm_i32_code_count pc_pre )) (PreH32 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e)))))) ) )) (PreH33 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e)))))) ) )) (PreH34 : (cm_rep_args_safe (cm_call_args (e)) )) (PreH35 : (retval = (cm_rep_args_length ((cm_call_args (e)))))) (PreH36 : (0 <= (cm_rep_expr_value (e)))) (PreH37 : ((cm_rep_expr_value (e)) <= INT_MAX)) (PreH38 : (cm_args_wf policy p f (cm_call_args (e)) (cm_function_params ((cm_function_at (policy) ((cm_rep_expr_value (e))) ((cm_program_functions (p)))))) )) (PreH39 : (cm_args_counts_representable policy p fid_pre (cm_call_args (e)) )) (PreH40 : (cm_rep_args_safe (cm_call_args (e)) )) (PreH41 : ((cm_rep_args_length ((cm_call_args (e)))) = (Zlength ((cm_call_args (e)))))) (PreH42 : (0 <= temp_limit_pre)) (PreH43 : (temp_limit_pre <= INT_MAX)) (PreH44 : (0 <= (temp_pre + (Zlength ((cm_call_args (e)))) ))) (PreH45 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre)) (PreH46 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= INT_MAX)) (PreH47 : (((temp_pre + (Zlength ((cm_call_args (e)))) ) + (cm_adepth ((cm_args_apair ((cm_call_args (e)))))) ) <= temp_limit_pre)) (PreH48 : (expr_pre <> 0)) (PreH49 : (lvalue_pre = 0)) (PreH50 : ((cm_rep_expr_kind (e)) = 8)) (PreH51 : (0 <= lvalue_pre)) (PreH52 : (lvalue_pre <= 1)) (PreH53 : (cm_wf_program policy cg p )) (PreH54 : (cm_typed_program policy p )) (PreH55 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH56 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH57 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH58 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH59 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH60 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH61 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH62 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH63 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH64 : (cm_expr_wf policy p f e )) (PreH65 : (cm_expr_counts_representable policy p fid_pre e )) (PreH66 : (0 <= temp_pre)) (PreH67 : (temp_pre <= temp_limit_pre)) (PreH68 : ((temp_pre + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit_pre)) (PreH69 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH70 : (cm_i32_code_count pc_pre )) (PreH71 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) ) )) ,
  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app (done) ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e))))))) ((cm_emit_args_reload (policy) (p) (fid_pre) (temp_pre) ((cm_call_args (e))))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) ((cm_rep_expr_value (e))))))) ((@nil tvm_inst))))) tail )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) tail )
.

Definition cm_emit_call_expr_return_wit_2 := 
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_limit_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (lvalue_pre <> 0)) (PreH2 : ((cm_rep_expr_kind (e)) = 8)) (PreH3 : (0 <= lvalue_pre)) (PreH4 : (lvalue_pre <= 1)) (PreH5 : (cm_wf_program policy cg p )) (PreH6 : (cm_typed_program policy p )) (PreH7 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH8 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH9 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH10 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH11 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH12 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH13 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH14 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH15 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH16 : (cm_expr_wf policy p f e )) (PreH17 : (cm_expr_counts_representable policy p fid_pre e )) (PreH18 : (0 <= temp_pre)) (PreH19 : (temp_pre <= temp_limit_pre)) (PreH20 : ((temp_pre + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit_pre)) (PreH21 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH22 : (cm_i32_code_count pc_pre )) (PreH23 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) ) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre))) (tail)) )
|--
  “ ((cm_rep_expr_kind (e)) = 8) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ (0 <= temp_pre) ” 
  &&  “ (temp_pre <= temp_limit_pre) ” 
  &&  “ ((temp_pre + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit_pre) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count pc_pre ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) ) ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) tail )
) \/
(
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_limit_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (lvalue_pre <> 0)) (PreH2 : ((cm_rep_expr_kind (e)) = 8)) (PreH3 : (0 <= lvalue_pre)) (PreH4 : (lvalue_pre <= 1)) (PreH5 : (cm_wf_program policy cg p )) (PreH6 : (cm_typed_program policy p )) (PreH7 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH8 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH9 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH10 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH11 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH12 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH13 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH14 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH15 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH16 : (cm_expr_wf policy p f e )) (PreH17 : (cm_expr_counts_representable policy p fid_pre e )) (PreH18 : (0 <= temp_pre)) (PreH19 : (temp_pre <= temp_limit_pre)) (PreH20 : ((temp_pre + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit_pre)) (PreH21 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH22 : (cm_i32_code_count pc_pre )) (PreH23 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) ) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre))) (tail)) )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) tail )
).

Definition cm_emit_call_expr_return_wit_2_split_goal_spatial := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_limit_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (lvalue_pre <> 0)) (PreH2 : ((cm_rep_expr_kind (e)) = 8)) (PreH3 : (0 <= lvalue_pre)) (PreH4 : (lvalue_pre <= 1)) (PreH5 : (cm_wf_program policy cg p )) (PreH6 : (cm_typed_program policy p )) (PreH7 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH8 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH9 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH10 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH11 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH12 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH13 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH14 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH15 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH16 : (cm_expr_wf policy p f e )) (PreH17 : (cm_expr_counts_representable policy p fid_pre e )) (PreH18 : (0 <= temp_pre)) (PreH19 : (temp_pre <= temp_limit_pre)) (PreH20 : ((temp_pre + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit_pre)) (PreH21 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH22 : (cm_i32_code_count pc_pre )) (PreH23 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) ) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre))) (tail)) )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) tail )
.

Definition cm_emit_call_expr_partial_solve_wit_1_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_limit_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (lvalue_pre = 0)) (PreH2 : ((cm_rep_expr_kind (e)) = 8)) (PreH3 : (0 <= lvalue_pre)) (PreH4 : (lvalue_pre <= 1)) (PreH5 : (cm_wf_program policy cg p )) (PreH6 : (cm_typed_program policy p )) (PreH7 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH8 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH9 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH10 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH11 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH12 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH13 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH14 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH15 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH16 : (cm_expr_wf policy p f e )) (PreH17 : (cm_expr_counts_representable policy p fid_pre e )) (PreH18 : (0 <= temp_pre)) (PreH19 : (temp_pre <= temp_limit_pre)) (PreH20 : ((temp_pre + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit_pre)) (PreH21 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH22 : (cm_i32_code_count pc_pre )) (PreH23 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) ) )) ,
  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "temp_limit" ) )) # Int  |-> temp_limit_pre)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre))) (tail)) )
|--
  “ ((cm_rep_expr_kind (e)) = 8) ”
.

Definition cm_emit_call_expr_partial_solve_wit_1_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_limit_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (lvalue_pre = 0)) (PreH2 : ((cm_rep_expr_kind (e)) = 8)) (PreH3 : (0 <= lvalue_pre)) (PreH4 : (lvalue_pre <= 1)) (PreH5 : (cm_wf_program policy cg p )) (PreH6 : (cm_typed_program policy p )) (PreH7 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH8 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH9 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH10 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH11 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH12 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH13 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH14 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH15 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH16 : (cm_expr_wf policy p f e )) (PreH17 : (cm_expr_counts_representable policy p fid_pre e )) (PreH18 : (0 <= temp_pre)) (PreH19 : (temp_pre <= temp_limit_pre)) (PreH20 : ((temp_pre + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit_pre)) (PreH21 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH22 : (cm_i32_code_count pc_pre )) (PreH23 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) ) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre))) (tail)) )
|--
  “ ((cm_rep_expr_kind (e)) = 8) ” 
  &&  “ (lvalue_pre = 0) ” 
  &&  “ ((cm_rep_expr_kind (e)) = 8) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ (0 <= temp_pre) ” 
  &&  “ (temp_pre <= temp_limit_pre) ” 
  &&  “ ((temp_pre + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit_pre) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count pc_pre ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) ) ) ”
  &&  (cm_expr_rep expr_pre e )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre))) (tail)) )
.

Definition cm_emit_call_expr_partial_solve_wit_1 := cm_emit_call_expr_partial_solve_wit_1_pure -> cm_emit_call_expr_partial_solve_wit_1_aux.

Definition cm_emit_call_expr_partial_solve_wit_2_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_limit_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (PreH1 : (expr_pre <> 0)) (PreH2 : (lvalue_pre = 0)) (PreH3 : ((cm_rep_expr_kind (e)) = 8)) (PreH4 : (0 <= lvalue_pre)) (PreH5 : (lvalue_pre <= 1)) (PreH6 : (cm_wf_program policy cg p )) (PreH7 : (cm_typed_program policy p )) (PreH8 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH9 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH10 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH11 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH12 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH13 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH14 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH15 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH16 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH17 : (cm_expr_wf policy p f e )) (PreH18 : (cm_expr_counts_representable policy p fid_pre e )) (PreH19 : (0 <= temp_pre)) (PreH20 : (temp_pre <= temp_limit_pre)) (PreH21 : ((temp_pre + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit_pre)) (PreH22 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH23 : (cm_i32_code_count pc_pre )) (PreH24 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) ) )) ,
  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_arg_list_rep xargs (cm_call_args (e)) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "temp_limit" ) )) # Int  |-> temp_limit_pre)
  **  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre))) (tail)) )
|--
  “ ((cm_rep_expr_kind (e)) = 8) ” 
  &&  “ (lvalue_pre = 0) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ (0 <= temp_pre) ” 
  &&  “ (temp_pre <= temp_limit_pre) ” 
  &&  “ ((temp_pre + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit_pre) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ”
.

Definition cm_emit_call_expr_partial_solve_wit_2_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_limit_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (PreH1 : (expr_pre <> 0)) (PreH2 : (lvalue_pre = 0)) (PreH3 : ((cm_rep_expr_kind (e)) = 8)) (PreH4 : (0 <= lvalue_pre)) (PreH5 : (lvalue_pre <= 1)) (PreH6 : (cm_wf_program policy cg p )) (PreH7 : (cm_typed_program policy p )) (PreH8 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH9 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH10 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH11 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH12 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH13 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH14 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH15 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH16 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH17 : (cm_expr_wf policy p f e )) (PreH18 : (cm_expr_counts_representable policy p fid_pre e )) (PreH19 : (0 <= temp_pre)) (PreH20 : (temp_pre <= temp_limit_pre)) (PreH21 : ((temp_pre + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit_pre)) (PreH22 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH23 : (cm_i32_code_count pc_pre )) (PreH24 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) ) )) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_arg_list_rep xargs (cm_call_args (e)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre))) (tail)) )
|--
  “ ((cm_rep_expr_kind (e)) = 8) ” 
  &&  “ (lvalue_pre = 0) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ (0 <= temp_pre) ” 
  &&  “ (temp_pre <= temp_limit_pre) ” 
  &&  “ ((temp_pre + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit_pre) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (lvalue_pre = 0) ” 
  &&  “ ((cm_rep_expr_kind (e)) = 8) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ (0 <= temp_pre) ” 
  &&  “ (temp_pre <= temp_limit_pre) ” 
  &&  “ ((temp_pre + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit_pre) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count pc_pre ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) ) ) ”
  &&  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_arg_list_rep xargs (cm_call_args (e)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre))) (tail)) )
.

Definition cm_emit_call_expr_partial_solve_wit_2 := cm_emit_call_expr_partial_solve_wit_2_pure -> cm_emit_call_expr_partial_solve_wit_2_aux.

Definition cm_emit_call_expr_partial_solve_wit_3_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_limit_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (PreH1 : (0 <= (cm_rep_expr_value (e)))) (PreH2 : ((cm_rep_expr_value (e)) <= INT_MAX)) (PreH3 : (cm_args_wf policy p f (cm_call_args (e)) (cm_function_params ((cm_function_at (policy) ((cm_rep_expr_value (e))) ((cm_program_functions (p)))))) )) (PreH4 : (cm_args_counts_representable policy p fid_pre (cm_call_args (e)) )) (PreH5 : (cm_rep_args_safe (cm_call_args (e)) )) (PreH6 : ((cm_rep_args_length ((cm_call_args (e)))) = (Zlength ((cm_call_args (e)))))) (PreH7 : (0 <= temp_limit_pre)) (PreH8 : (temp_limit_pre <= INT_MAX)) (PreH9 : (0 <= (temp_pre + (Zlength ((cm_call_args (e)))) ))) (PreH10 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre)) (PreH11 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= INT_MAX)) (PreH12 : (((temp_pre + (Zlength ((cm_call_args (e)))) ) + (cm_adepth ((cm_args_apair ((cm_call_args (e)))))) ) <= temp_limit_pre)) (PreH13 : (expr_pre <> 0)) (PreH14 : (lvalue_pre = 0)) (PreH15 : ((cm_rep_expr_kind (e)) = 8)) (PreH16 : (0 <= lvalue_pre)) (PreH17 : (lvalue_pre <= 1)) (PreH18 : (cm_wf_program policy cg p )) (PreH19 : (cm_typed_program policy p )) (PreH20 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH21 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH22 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH23 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH24 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH25 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH26 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH27 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH28 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH29 : (cm_expr_wf policy p f e )) (PreH30 : (cm_expr_counts_representable policy p fid_pre e )) (PreH31 : (0 <= temp_pre)) (PreH32 : (temp_pre <= temp_limit_pre)) (PreH33 : ((temp_pre + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit_pre)) (PreH34 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH35 : (cm_i32_code_count pc_pre )) (PreH36 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) ) )) ,
  ((( &( "count" ) )) # Int  |->_)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "temp_limit" ) )) # Int  |-> temp_limit_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_arg_list_rep xargs (cm_call_args (e)) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre))) (tail)) )
|--
  “ (cm_rep_args_safe (cm_call_args (e)) ) ”
.

Definition cm_emit_call_expr_partial_solve_wit_3_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_limit_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (PreH1 : (0 <= (cm_rep_expr_value (e)))) (PreH2 : ((cm_rep_expr_value (e)) <= INT_MAX)) (PreH3 : (cm_args_wf policy p f (cm_call_args (e)) (cm_function_params ((cm_function_at (policy) ((cm_rep_expr_value (e))) ((cm_program_functions (p)))))) )) (PreH4 : (cm_args_counts_representable policy p fid_pre (cm_call_args (e)) )) (PreH5 : (cm_rep_args_safe (cm_call_args (e)) )) (PreH6 : ((cm_rep_args_length ((cm_call_args (e)))) = (Zlength ((cm_call_args (e)))))) (PreH7 : (0 <= temp_limit_pre)) (PreH8 : (temp_limit_pre <= INT_MAX)) (PreH9 : (0 <= (temp_pre + (Zlength ((cm_call_args (e)))) ))) (PreH10 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre)) (PreH11 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= INT_MAX)) (PreH12 : (((temp_pre + (Zlength ((cm_call_args (e)))) ) + (cm_adepth ((cm_args_apair ((cm_call_args (e)))))) ) <= temp_limit_pre)) (PreH13 : (expr_pre <> 0)) (PreH14 : (lvalue_pre = 0)) (PreH15 : ((cm_rep_expr_kind (e)) = 8)) (PreH16 : (0 <= lvalue_pre)) (PreH17 : (lvalue_pre <= 1)) (PreH18 : (cm_wf_program policy cg p )) (PreH19 : (cm_typed_program policy p )) (PreH20 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH21 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH22 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH23 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH24 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH25 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH26 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH27 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH28 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH29 : (cm_expr_wf policy p f e )) (PreH30 : (cm_expr_counts_representable policy p fid_pre e )) (PreH31 : (0 <= temp_pre)) (PreH32 : (temp_pre <= temp_limit_pre)) (PreH33 : ((temp_pre + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit_pre)) (PreH34 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH35 : (cm_i32_code_count pc_pre )) (PreH36 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) ) )) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_arg_list_rep xargs (cm_call_args (e)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre))) (tail)) )
|--
  “ (cm_rep_args_safe (cm_call_args (e)) ) ” 
  &&  “ (0 <= (cm_rep_expr_value (e))) ” 
  &&  “ ((cm_rep_expr_value (e)) <= INT_MAX) ” 
  &&  “ (cm_args_wf policy p f (cm_call_args (e)) (cm_function_params ((cm_function_at (policy) ((cm_rep_expr_value (e))) ((cm_program_functions (p)))))) ) ” 
  &&  “ (cm_args_counts_representable policy p fid_pre (cm_call_args (e)) ) ” 
  &&  “ (cm_rep_args_safe (cm_call_args (e)) ) ” 
  &&  “ ((cm_rep_args_length ((cm_call_args (e)))) = (Zlength ((cm_call_args (e))))) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ (0 <= (temp_pre + (Zlength ((cm_call_args (e)))) )) ” 
  &&  “ ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre) ” 
  &&  “ ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= INT_MAX) ” 
  &&  “ (((temp_pre + (Zlength ((cm_call_args (e)))) ) + (cm_adepth ((cm_args_apair ((cm_call_args (e)))))) ) <= temp_limit_pre) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (lvalue_pre = 0) ” 
  &&  “ ((cm_rep_expr_kind (e)) = 8) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ (0 <= temp_pre) ” 
  &&  “ (temp_pre <= temp_limit_pre) ” 
  &&  “ ((temp_pre + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit_pre) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count pc_pre ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) ) ) ”
  &&  (cm_arg_list_rep xargs (cm_call_args (e)) )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre))) (tail)) )
.

Definition cm_emit_call_expr_partial_solve_wit_3 := cm_emit_call_expr_partial_solve_wit_3_pure -> cm_emit_call_expr_partial_solve_wit_3_aux.

Definition cm_emit_call_expr_partial_solve_wit_4_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_limit_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (retval: Z) (PreH1 : (cm_rep_args_safe (cm_call_args (e)) )) (PreH2 : (retval = (cm_rep_args_length ((cm_call_args (e)))))) (PreH3 : (0 <= (cm_rep_expr_value (e)))) (PreH4 : ((cm_rep_expr_value (e)) <= INT_MAX)) (PreH5 : (cm_args_wf policy p f (cm_call_args (e)) (cm_function_params ((cm_function_at (policy) ((cm_rep_expr_value (e))) ((cm_program_functions (p)))))) )) (PreH6 : (cm_args_counts_representable policy p fid_pre (cm_call_args (e)) )) (PreH7 : (cm_rep_args_safe (cm_call_args (e)) )) (PreH8 : ((cm_rep_args_length ((cm_call_args (e)))) = (Zlength ((cm_call_args (e)))))) (PreH9 : (0 <= temp_limit_pre)) (PreH10 : (temp_limit_pre <= INT_MAX)) (PreH11 : (0 <= (temp_pre + (Zlength ((cm_call_args (e)))) ))) (PreH12 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre)) (PreH13 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= INT_MAX)) (PreH14 : (((temp_pre + (Zlength ((cm_call_args (e)))) ) + (cm_adepth ((cm_args_apair ((cm_call_args (e)))))) ) <= temp_limit_pre)) (PreH15 : (expr_pre <> 0)) (PreH16 : (lvalue_pre = 0)) (PreH17 : ((cm_rep_expr_kind (e)) = 8)) (PreH18 : (0 <= lvalue_pre)) (PreH19 : (lvalue_pre <= 1)) (PreH20 : (cm_wf_program policy cg p )) (PreH21 : (cm_typed_program policy p )) (PreH22 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH23 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH24 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH25 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH26 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH27 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH28 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH29 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH30 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH31 : (cm_expr_wf policy p f e )) (PreH32 : (cm_expr_counts_representable policy p fid_pre e )) (PreH33 : (0 <= temp_pre)) (PreH34 : (temp_pre <= temp_limit_pre)) (PreH35 : ((temp_pre + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit_pre)) (PreH36 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH37 : (cm_i32_code_count pc_pre )) (PreH38 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) ) )) ,
  (cm_arg_list_rep xargs (cm_call_args (e)) )
  **  ((( &( "count" ) )) # Int  |-> retval)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "temp_limit" ) )) # Int  |-> temp_limit_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre))) (tail)) )
|--
  “ ((cm_rep_expr_kind (e)) = 8) ” 
  &&  “ (lvalue_pre = 0) ” 
  &&  “ ((Zlength ((cm_call_args (e)))) = (Zlength ((cm_call_args (e))))) ” 
  &&  “ (cm_i32_code_count pc_pre ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) ) ) ”
.

Definition cm_emit_call_expr_partial_solve_wit_4_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_limit_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (retval: Z) (PreH1 : (cm_rep_args_safe (cm_call_args (e)) )) (PreH2 : (retval = (cm_rep_args_length ((cm_call_args (e)))))) (PreH3 : (0 <= (cm_rep_expr_value (e)))) (PreH4 : ((cm_rep_expr_value (e)) <= INT_MAX)) (PreH5 : (cm_args_wf policy p f (cm_call_args (e)) (cm_function_params ((cm_function_at (policy) ((cm_rep_expr_value (e))) ((cm_program_functions (p)))))) )) (PreH6 : (cm_args_counts_representable policy p fid_pre (cm_call_args (e)) )) (PreH7 : (cm_rep_args_safe (cm_call_args (e)) )) (PreH8 : ((cm_rep_args_length ((cm_call_args (e)))) = (Zlength ((cm_call_args (e)))))) (PreH9 : (0 <= temp_limit_pre)) (PreH10 : (temp_limit_pre <= INT_MAX)) (PreH11 : (0 <= (temp_pre + (Zlength ((cm_call_args (e)))) ))) (PreH12 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre)) (PreH13 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= INT_MAX)) (PreH14 : (((temp_pre + (Zlength ((cm_call_args (e)))) ) + (cm_adepth ((cm_args_apair ((cm_call_args (e)))))) ) <= temp_limit_pre)) (PreH15 : (expr_pre <> 0)) (PreH16 : (lvalue_pre = 0)) (PreH17 : ((cm_rep_expr_kind (e)) = 8)) (PreH18 : (0 <= lvalue_pre)) (PreH19 : (lvalue_pre <= 1)) (PreH20 : (cm_wf_program policy cg p )) (PreH21 : (cm_typed_program policy p )) (PreH22 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH23 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH24 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH25 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH26 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH27 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH28 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH29 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH30 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH31 : (cm_expr_wf policy p f e )) (PreH32 : (cm_expr_counts_representable policy p fid_pre e )) (PreH33 : (0 <= temp_pre)) (PreH34 : (temp_pre <= temp_limit_pre)) (PreH35 : ((temp_pre + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit_pre)) (PreH36 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH37 : (cm_i32_code_count pc_pre )) (PreH38 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) ) )) ,
  (cm_arg_list_rep xargs (cm_call_args (e)) )
  **  ((( &( "count" ) )) # Int  |-> retval)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre))) (tail)) )
|--
  “ ((cm_rep_expr_kind (e)) = 8) ” 
  &&  “ (lvalue_pre = 0) ” 
  &&  “ ((Zlength ((cm_call_args (e)))) = (Zlength ((cm_call_args (e))))) ” 
  &&  “ (cm_i32_code_count pc_pre ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) ) ) ” 
  &&  “ (cm_rep_args_safe (cm_call_args (e)) ) ” 
  &&  “ (retval = (cm_rep_args_length ((cm_call_args (e))))) ” 
  &&  “ (0 <= (cm_rep_expr_value (e))) ” 
  &&  “ ((cm_rep_expr_value (e)) <= INT_MAX) ” 
  &&  “ (cm_args_wf policy p f (cm_call_args (e)) (cm_function_params ((cm_function_at (policy) ((cm_rep_expr_value (e))) ((cm_program_functions (p)))))) ) ” 
  &&  “ (cm_args_counts_representable policy p fid_pre (cm_call_args (e)) ) ” 
  &&  “ (cm_rep_args_safe (cm_call_args (e)) ) ” 
  &&  “ ((cm_rep_args_length ((cm_call_args (e)))) = (Zlength ((cm_call_args (e))))) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ (0 <= (temp_pre + (Zlength ((cm_call_args (e)))) )) ” 
  &&  “ ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre) ” 
  &&  “ ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= INT_MAX) ” 
  &&  “ (((temp_pre + (Zlength ((cm_call_args (e)))) ) + (cm_adepth ((cm_args_apair ((cm_call_args (e)))))) ) <= temp_limit_pre) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (lvalue_pre = 0) ” 
  &&  “ ((cm_rep_expr_kind (e)) = 8) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ (0 <= temp_pre) ” 
  &&  “ (temp_pre <= temp_limit_pre) ” 
  &&  “ ((temp_pre + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit_pre) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count pc_pre ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) ) ) ”
  &&  ((( &( "count" ) )) # Int  |-> (Zlength ((cm_call_args (e)))))
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre))) (tail)) )
  **  (cm_arg_list_rep xargs (cm_call_args (e)) )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
.

Definition cm_emit_call_expr_partial_solve_wit_4 := cm_emit_call_expr_partial_solve_wit_4_pure -> cm_emit_call_expr_partial_solve_wit_4_aux.

Definition cm_emit_call_expr_partial_solve_wit_5_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_limit_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (retval: Z) (PreH1 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e)))))) ) )) (PreH2 : (cm_rep_args_safe (cm_call_args (e)) )) (PreH3 : (retval = (cm_rep_args_length ((cm_call_args (e)))))) (PreH4 : (0 <= (cm_rep_expr_value (e)))) (PreH5 : ((cm_rep_expr_value (e)) <= INT_MAX)) (PreH6 : (cm_args_wf policy p f (cm_call_args (e)) (cm_function_params ((cm_function_at (policy) ((cm_rep_expr_value (e))) ((cm_program_functions (p)))))) )) (PreH7 : (cm_args_counts_representable policy p fid_pre (cm_call_args (e)) )) (PreH8 : (cm_rep_args_safe (cm_call_args (e)) )) (PreH9 : ((cm_rep_args_length ((cm_call_args (e)))) = (Zlength ((cm_call_args (e)))))) (PreH10 : (0 <= temp_limit_pre)) (PreH11 : (temp_limit_pre <= INT_MAX)) (PreH12 : (0 <= (temp_pre + (Zlength ((cm_call_args (e)))) ))) (PreH13 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre)) (PreH14 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= INT_MAX)) (PreH15 : (((temp_pre + (Zlength ((cm_call_args (e)))) ) + (cm_adepth ((cm_args_apair ((cm_call_args (e)))))) ) <= temp_limit_pre)) (PreH16 : (expr_pre <> 0)) (PreH17 : (lvalue_pre = 0)) (PreH18 : ((cm_rep_expr_kind (e)) = 8)) (PreH19 : (0 <= lvalue_pre)) (PreH20 : (lvalue_pre <= 1)) (PreH21 : (cm_wf_program policy cg p )) (PreH22 : (cm_typed_program policy p )) (PreH23 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH24 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH25 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH26 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH27 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH28 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH29 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH30 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH31 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH32 : (cm_expr_wf policy p f e )) (PreH33 : (cm_expr_counts_representable policy p fid_pre e )) (PreH34 : (0 <= temp_pre)) (PreH35 : (temp_pre <= temp_limit_pre)) (PreH36 : ((temp_pre + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit_pre)) (PreH37 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH38 : (cm_i32_code_count pc_pre )) (PreH39 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) ) )) ,
  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "count" ) )) # Int  |-> (Zlength ((cm_call_args (e)))))
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e))))) ((app ((cm_emit_args_reload (policy) (p) (fid_pre) (temp_pre) ((cm_call_args (e))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) ((cm_rep_expr_value (e))))))) (tail)))))) )
  **  (cm_arg_list_rep xargs (cm_call_args (e)) )
  **  ((( &( "temp_limit" ) )) # Int  |-> temp_limit_pre)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (cm_args_wf policy p f (cm_call_args (e)) (cm_function_params ((cm_function_at (policy) ((cm_rep_expr_value (e))) ((cm_program_functions (p)))))) ) ” 
  &&  “ (cm_args_counts_representable policy p fid_pre (cm_call_args (e)) ) ” 
  &&  “ (0 <= temp_pre) ” 
  &&  “ ((temp_pre + (Zlength ((cm_call_args (e)))) ) = (temp_pre + (Zlength ((cm_call_args (e)))) )) ” 
  &&  “ (0 <= (temp_pre + (Zlength ((cm_call_args (e)))) )) ” 
  &&  “ ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre) ” 
  &&  “ (((temp_pre + (Zlength ((cm_call_args (e)))) ) + (cm_adepth ((cm_args_apair ((cm_call_args (e)))))) ) <= temp_limit_pre) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count pc_pre ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e)))))) ) ) ”
.

Definition cm_emit_call_expr_partial_solve_wit_5_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_limit_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (retval: Z) (PreH1 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e)))))) ) )) (PreH2 : (cm_rep_args_safe (cm_call_args (e)) )) (PreH3 : (retval = (cm_rep_args_length ((cm_call_args (e)))))) (PreH4 : (0 <= (cm_rep_expr_value (e)))) (PreH5 : ((cm_rep_expr_value (e)) <= INT_MAX)) (PreH6 : (cm_args_wf policy p f (cm_call_args (e)) (cm_function_params ((cm_function_at (policy) ((cm_rep_expr_value (e))) ((cm_program_functions (p)))))) )) (PreH7 : (cm_args_counts_representable policy p fid_pre (cm_call_args (e)) )) (PreH8 : (cm_rep_args_safe (cm_call_args (e)) )) (PreH9 : ((cm_rep_args_length ((cm_call_args (e)))) = (Zlength ((cm_call_args (e)))))) (PreH10 : (0 <= temp_limit_pre)) (PreH11 : (temp_limit_pre <= INT_MAX)) (PreH12 : (0 <= (temp_pre + (Zlength ((cm_call_args (e)))) ))) (PreH13 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre)) (PreH14 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= INT_MAX)) (PreH15 : (((temp_pre + (Zlength ((cm_call_args (e)))) ) + (cm_adepth ((cm_args_apair ((cm_call_args (e)))))) ) <= temp_limit_pre)) (PreH16 : (expr_pre <> 0)) (PreH17 : (lvalue_pre = 0)) (PreH18 : ((cm_rep_expr_kind (e)) = 8)) (PreH19 : (0 <= lvalue_pre)) (PreH20 : (lvalue_pre <= 1)) (PreH21 : (cm_wf_program policy cg p )) (PreH22 : (cm_typed_program policy p )) (PreH23 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH24 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH25 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH26 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH27 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH28 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH29 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH30 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH31 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH32 : (cm_expr_wf policy p f e )) (PreH33 : (cm_expr_counts_representable policy p fid_pre e )) (PreH34 : (0 <= temp_pre)) (PreH35 : (temp_pre <= temp_limit_pre)) (PreH36 : ((temp_pre + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit_pre)) (PreH37 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH38 : (cm_i32_code_count pc_pre )) (PreH39 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) ) )) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e))))) ((app ((cm_emit_args_reload (policy) (p) (fid_pre) (temp_pre) ((cm_call_args (e))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) ((cm_rep_expr_value (e))))))) (tail)))))) )
  **  (cm_arg_list_rep xargs (cm_call_args (e)) )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (cm_args_wf policy p f (cm_call_args (e)) (cm_function_params ((cm_function_at (policy) ((cm_rep_expr_value (e))) ((cm_program_functions (p)))))) ) ” 
  &&  “ (cm_args_counts_representable policy p fid_pre (cm_call_args (e)) ) ” 
  &&  “ (0 <= temp_pre) ” 
  &&  “ ((temp_pre + (Zlength ((cm_call_args (e)))) ) = (temp_pre + (Zlength ((cm_call_args (e)))) )) ” 
  &&  “ (0 <= (temp_pre + (Zlength ((cm_call_args (e)))) )) ” 
  &&  “ ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre) ” 
  &&  “ (((temp_pre + (Zlength ((cm_call_args (e)))) ) + (cm_adepth ((cm_args_apair ((cm_call_args (e)))))) ) <= temp_limit_pre) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count pc_pre ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e)))))) ) ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e)))))) ) ) ” 
  &&  “ (cm_rep_args_safe (cm_call_args (e)) ) ” 
  &&  “ (retval = (cm_rep_args_length ((cm_call_args (e))))) ” 
  &&  “ (0 <= (cm_rep_expr_value (e))) ” 
  &&  “ ((cm_rep_expr_value (e)) <= INT_MAX) ” 
  &&  “ (cm_args_wf policy p f (cm_call_args (e)) (cm_function_params ((cm_function_at (policy) ((cm_rep_expr_value (e))) ((cm_program_functions (p)))))) ) ” 
  &&  “ (cm_args_counts_representable policy p fid_pre (cm_call_args (e)) ) ” 
  &&  “ (cm_rep_args_safe (cm_call_args (e)) ) ” 
  &&  “ ((cm_rep_args_length ((cm_call_args (e)))) = (Zlength ((cm_call_args (e))))) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ (0 <= (temp_pre + (Zlength ((cm_call_args (e)))) )) ” 
  &&  “ ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre) ” 
  &&  “ ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= INT_MAX) ” 
  &&  “ (((temp_pre + (Zlength ((cm_call_args (e)))) ) + (cm_adepth ((cm_args_apair ((cm_call_args (e)))))) ) <= temp_limit_pre) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (lvalue_pre = 0) ” 
  &&  “ ((cm_rep_expr_kind (e)) = 8) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ (0 <= temp_pre) ” 
  &&  “ (temp_pre <= temp_limit_pre) ” 
  &&  “ ((temp_pre + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit_pre) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count pc_pre ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) ) ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_arg_list_rep xargs (cm_call_args (e)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e))))) ((app ((cm_emit_args_reload (policy) (p) (fid_pre) (temp_pre) ((cm_call_args (e))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) ((cm_rep_expr_value (e))))))) (tail)))))) )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
.

Definition cm_emit_call_expr_partial_solve_wit_5 := cm_emit_call_expr_partial_solve_wit_5_pure -> cm_emit_call_expr_partial_solve_wit_5_aux.

Definition cm_emit_call_expr_partial_solve_wit_6_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_limit_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (retval: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_typed_program policy p )) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH5 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH6 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH7 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH8 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH9 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH10 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH11 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH12 : (cm_args_wf policy p f (cm_call_args (e)) (cm_function_params ((cm_function_at (policy) ((cm_rep_expr_value (e))) ((cm_program_functions (p)))))) )) (PreH13 : (cm_args_counts_representable policy p fid_pre (cm_call_args (e)) )) (PreH14 : (0 <= temp_pre)) (PreH15 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) = (temp_pre + (Zlength ((cm_call_args (e)))) ))) (PreH16 : (0 <= (temp_pre + (Zlength ((cm_call_args (e)))) ))) (PreH17 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre)) (PreH18 : (((temp_pre + (Zlength ((cm_call_args (e)))) ) + (cm_adepth ((cm_args_apair ((cm_call_args (e)))))) ) <= temp_limit_pre)) (PreH19 : (0 <= temp_limit_pre)) (PreH20 : (temp_limit_pre <= INT_MAX)) (PreH21 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH22 : (cm_i32_code_count pc_pre )) (PreH23 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e)))))) ) )) (PreH24 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e)))))) ) )) (PreH25 : (cm_rep_args_safe (cm_call_args (e)) )) (PreH26 : (retval = (cm_rep_args_length ((cm_call_args (e)))))) (PreH27 : (0 <= (cm_rep_expr_value (e)))) (PreH28 : ((cm_rep_expr_value (e)) <= INT_MAX)) (PreH29 : (cm_args_wf policy p f (cm_call_args (e)) (cm_function_params ((cm_function_at (policy) ((cm_rep_expr_value (e))) ((cm_program_functions (p)))))) )) (PreH30 : (cm_args_counts_representable policy p fid_pre (cm_call_args (e)) )) (PreH31 : (cm_rep_args_safe (cm_call_args (e)) )) (PreH32 : ((cm_rep_args_length ((cm_call_args (e)))) = (Zlength ((cm_call_args (e)))))) (PreH33 : (0 <= temp_limit_pre)) (PreH34 : (temp_limit_pre <= INT_MAX)) (PreH35 : (0 <= (temp_pre + (Zlength ((cm_call_args (e)))) ))) (PreH36 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre)) (PreH37 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= INT_MAX)) (PreH38 : (((temp_pre + (Zlength ((cm_call_args (e)))) ) + (cm_adepth ((cm_args_apair ((cm_call_args (e)))))) ) <= temp_limit_pre)) (PreH39 : (expr_pre <> 0)) (PreH40 : (lvalue_pre = 0)) (PreH41 : ((cm_rep_expr_kind (e)) = 8)) (PreH42 : (0 <= lvalue_pre)) (PreH43 : (lvalue_pre <= 1)) (PreH44 : (cm_wf_program policy cg p )) (PreH45 : (cm_typed_program policy p )) (PreH46 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH47 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH48 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH49 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH50 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH51 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH52 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH53 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH54 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH55 : (cm_expr_wf policy p f e )) (PreH56 : (cm_expr_counts_representable policy p fid_pre e )) (PreH57 : (0 <= temp_pre)) (PreH58 : (temp_pre <= temp_limit_pre)) (PreH59 : ((temp_pre + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit_pre)) (PreH60 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH61 : (cm_i32_code_count pc_pre )) (PreH62 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) ) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_arg_list_rep xargs (cm_call_args (e)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e)))))) (app ((cm_emit_args_reload (policy) (p) (fid_pre) (temp_pre) ((cm_call_args (e))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) ((cm_rep_expr_value (e))))))) (tail)))) )
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "count" ) )) # Int  |-> (Zlength ((cm_call_args (e)))))
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "temp_limit" ) )) # Int  |-> temp_limit_pre)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
|--
  “ (0 <= temp_pre) ” 
  &&  “ ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ”
.

Definition cm_emit_call_expr_partial_solve_wit_6_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_limit_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (retval: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (cm_typed_program policy p )) (PreH3 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH4 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH5 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH6 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH7 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH8 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH9 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH10 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH11 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH12 : (cm_args_wf policy p f (cm_call_args (e)) (cm_function_params ((cm_function_at (policy) ((cm_rep_expr_value (e))) ((cm_program_functions (p)))))) )) (PreH13 : (cm_args_counts_representable policy p fid_pre (cm_call_args (e)) )) (PreH14 : (0 <= temp_pre)) (PreH15 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) = (temp_pre + (Zlength ((cm_call_args (e)))) ))) (PreH16 : (0 <= (temp_pre + (Zlength ((cm_call_args (e)))) ))) (PreH17 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre)) (PreH18 : (((temp_pre + (Zlength ((cm_call_args (e)))) ) + (cm_adepth ((cm_args_apair ((cm_call_args (e)))))) ) <= temp_limit_pre)) (PreH19 : (0 <= temp_limit_pre)) (PreH20 : (temp_limit_pre <= INT_MAX)) (PreH21 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH22 : (cm_i32_code_count pc_pre )) (PreH23 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e)))))) ) )) (PreH24 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e)))))) ) )) (PreH25 : (cm_rep_args_safe (cm_call_args (e)) )) (PreH26 : (retval = (cm_rep_args_length ((cm_call_args (e)))))) (PreH27 : (0 <= (cm_rep_expr_value (e)))) (PreH28 : ((cm_rep_expr_value (e)) <= INT_MAX)) (PreH29 : (cm_args_wf policy p f (cm_call_args (e)) (cm_function_params ((cm_function_at (policy) ((cm_rep_expr_value (e))) ((cm_program_functions (p)))))) )) (PreH30 : (cm_args_counts_representable policy p fid_pre (cm_call_args (e)) )) (PreH31 : (cm_rep_args_safe (cm_call_args (e)) )) (PreH32 : ((cm_rep_args_length ((cm_call_args (e)))) = (Zlength ((cm_call_args (e)))))) (PreH33 : (0 <= temp_limit_pre)) (PreH34 : (temp_limit_pre <= INT_MAX)) (PreH35 : (0 <= (temp_pre + (Zlength ((cm_call_args (e)))) ))) (PreH36 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre)) (PreH37 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= INT_MAX)) (PreH38 : (((temp_pre + (Zlength ((cm_call_args (e)))) ) + (cm_adepth ((cm_args_apair ((cm_call_args (e)))))) ) <= temp_limit_pre)) (PreH39 : (expr_pre <> 0)) (PreH40 : (lvalue_pre = 0)) (PreH41 : ((cm_rep_expr_kind (e)) = 8)) (PreH42 : (0 <= lvalue_pre)) (PreH43 : (lvalue_pre <= 1)) (PreH44 : (cm_wf_program policy cg p )) (PreH45 : (cm_typed_program policy p )) (PreH46 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH47 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH48 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH49 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH50 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH51 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH52 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH53 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH54 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH55 : (cm_expr_wf policy p f e )) (PreH56 : (cm_expr_counts_representable policy p fid_pre e )) (PreH57 : (0 <= temp_pre)) (PreH58 : (temp_pre <= temp_limit_pre)) (PreH59 : ((temp_pre + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit_pre)) (PreH60 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH61 : (cm_i32_code_count pc_pre )) (PreH62 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) ) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_arg_list_rep xargs (cm_call_args (e)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e)))))) (app ((cm_emit_args_reload (policy) (p) (fid_pre) (temp_pre) ((cm_call_args (e))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) ((cm_rep_expr_value (e))))))) (tail)))) )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
|--
  “ (0 <= temp_pre) ” 
  &&  “ ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (cm_args_wf policy p f (cm_call_args (e)) (cm_function_params ((cm_function_at (policy) ((cm_rep_expr_value (e))) ((cm_program_functions (p)))))) ) ” 
  &&  “ (cm_args_counts_representable policy p fid_pre (cm_call_args (e)) ) ” 
  &&  “ (0 <= temp_pre) ” 
  &&  “ (0 <= (temp_pre + (Zlength ((cm_call_args (e)))) )) ” 
  &&  “ ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre) ” 
  &&  “ (((temp_pre + (Zlength ((cm_call_args (e)))) ) + (cm_adepth ((cm_args_apair ((cm_call_args (e)))))) ) <= temp_limit_pre) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count pc_pre ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e)))))) ) ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e)))))) ) ) ” 
  &&  “ (cm_rep_args_safe (cm_call_args (e)) ) ” 
  &&  “ (retval = (cm_rep_args_length ((cm_call_args (e))))) ” 
  &&  “ (0 <= (cm_rep_expr_value (e))) ” 
  &&  “ ((cm_rep_expr_value (e)) <= INT_MAX) ” 
  &&  “ (cm_args_wf policy p f (cm_call_args (e)) (cm_function_params ((cm_function_at (policy) ((cm_rep_expr_value (e))) ((cm_program_functions (p)))))) ) ” 
  &&  “ (cm_args_counts_representable policy p fid_pre (cm_call_args (e)) ) ” 
  &&  “ (cm_rep_args_safe (cm_call_args (e)) ) ” 
  &&  “ ((cm_rep_args_length ((cm_call_args (e)))) = (Zlength ((cm_call_args (e))))) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ (0 <= (temp_pre + (Zlength ((cm_call_args (e)))) )) ” 
  &&  “ ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre) ” 
  &&  “ ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= INT_MAX) ” 
  &&  “ (((temp_pre + (Zlength ((cm_call_args (e)))) ) + (cm_adepth ((cm_args_apair ((cm_call_args (e)))))) ) <= temp_limit_pre) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (lvalue_pre = 0) ” 
  &&  “ ((cm_rep_expr_kind (e)) = 8) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ (0 <= temp_pre) ” 
  &&  “ (temp_pre <= temp_limit_pre) ” 
  &&  “ ((temp_pre + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit_pre) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count pc_pre ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) ) ) ”
  &&  (cm_function_context_rep fn_pre f body next )
  **  (cm_arg_list_rep xargs (cm_call_args (e)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e)))))) (app ((cm_emit_args_reload (policy) (p) (fid_pre) (temp_pre) ((cm_call_args (e))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) ((cm_rep_expr_value (e))))))) (tail)))) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
.

Definition cm_emit_call_expr_partial_solve_wit_6 := cm_emit_call_expr_partial_solve_wit_6_pure -> cm_emit_call_expr_partial_solve_wit_6_aux.

Definition cm_emit_call_expr_partial_solve_wit_7 := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_limit_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (retval: Z) (PreH1 : (0 <= temp_pre)) (PreH2 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre)) (PreH3 : (0 <= temp_limit_pre)) (PreH4 : (temp_limit_pre <= INT_MAX)) (PreH5 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH6 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH7 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH8 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH9 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH10 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH11 : (cm_wf_program policy cg p )) (PreH12 : (cm_typed_program policy p )) (PreH13 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH14 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH15 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH16 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH17 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH18 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH19 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH20 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH21 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH22 : (cm_args_wf policy p f (cm_call_args (e)) (cm_function_params ((cm_function_at (policy) ((cm_rep_expr_value (e))) ((cm_program_functions (p)))))) )) (PreH23 : (cm_args_counts_representable policy p fid_pre (cm_call_args (e)) )) (PreH24 : (0 <= temp_pre)) (PreH25 : (0 <= (temp_pre + (Zlength ((cm_call_args (e)))) ))) (PreH26 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre)) (PreH27 : (((temp_pre + (Zlength ((cm_call_args (e)))) ) + (cm_adepth ((cm_args_apair ((cm_call_args (e)))))) ) <= temp_limit_pre)) (PreH28 : (0 <= temp_limit_pre)) (PreH29 : (temp_limit_pre <= INT_MAX)) (PreH30 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH31 : (cm_i32_code_count pc_pre )) (PreH32 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e)))))) ) )) (PreH33 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e)))))) ) )) (PreH34 : (cm_rep_args_safe (cm_call_args (e)) )) (PreH35 : (retval = (cm_rep_args_length ((cm_call_args (e)))))) (PreH36 : (0 <= (cm_rep_expr_value (e)))) (PreH37 : ((cm_rep_expr_value (e)) <= INT_MAX)) (PreH38 : (cm_args_wf policy p f (cm_call_args (e)) (cm_function_params ((cm_function_at (policy) ((cm_rep_expr_value (e))) ((cm_program_functions (p)))))) )) (PreH39 : (cm_args_counts_representable policy p fid_pre (cm_call_args (e)) )) (PreH40 : (cm_rep_args_safe (cm_call_args (e)) )) (PreH41 : ((cm_rep_args_length ((cm_call_args (e)))) = (Zlength ((cm_call_args (e)))))) (PreH42 : (0 <= temp_limit_pre)) (PreH43 : (temp_limit_pre <= INT_MAX)) (PreH44 : (0 <= (temp_pre + (Zlength ((cm_call_args (e)))) ))) (PreH45 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre)) (PreH46 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= INT_MAX)) (PreH47 : (((temp_pre + (Zlength ((cm_call_args (e)))) ) + (cm_adepth ((cm_args_apair ((cm_call_args (e)))))) ) <= temp_limit_pre)) (PreH48 : (expr_pre <> 0)) (PreH49 : (lvalue_pre = 0)) (PreH50 : ((cm_rep_expr_kind (e)) = 8)) (PreH51 : (0 <= lvalue_pre)) (PreH52 : (lvalue_pre <= 1)) (PreH53 : (cm_wf_program policy cg p )) (PreH54 : (cm_typed_program policy p )) (PreH55 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH56 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH57 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH58 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH59 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH60 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH61 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH62 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH63 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH64 : (cm_expr_wf policy p f e )) (PreH65 : (cm_expr_counts_representable policy p fid_pre e )) (PreH66 : (0 <= temp_pre)) (PreH67 : (temp_pre <= temp_limit_pre)) (PreH68 : ((temp_pre + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit_pre)) (PreH69 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH70 : (cm_i32_code_count pc_pre )) (PreH71 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) ) )) ,
  (cm_function_context_rep fn_pre f body next )
  **  (cm_arg_list_rep xargs (cm_call_args (e)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app (done) ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e))))))) ((cm_emit_args_reload (policy) (p) (fid_pre) (temp_pre) ((cm_call_args (e)))))) (cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) ((cm_rep_expr_value (e))))))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
|--
  “ (0 <= temp_pre) ” 
  &&  “ ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (cm_args_wf policy p f (cm_call_args (e)) (cm_function_params ((cm_function_at (policy) ((cm_rep_expr_value (e))) ((cm_program_functions (p)))))) ) ” 
  &&  “ (cm_args_counts_representable policy p fid_pre (cm_call_args (e)) ) ” 
  &&  “ (0 <= temp_pre) ” 
  &&  “ (0 <= (temp_pre + (Zlength ((cm_call_args (e)))) )) ” 
  &&  “ ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre) ” 
  &&  “ (((temp_pre + (Zlength ((cm_call_args (e)))) ) + (cm_adepth ((cm_args_apair ((cm_call_args (e)))))) ) <= temp_limit_pre) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count pc_pre ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e)))))) ) ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e)))))) ) ) ” 
  &&  “ (cm_rep_args_safe (cm_call_args (e)) ) ” 
  &&  “ (retval = (cm_rep_args_length ((cm_call_args (e))))) ” 
  &&  “ (0 <= (cm_rep_expr_value (e))) ” 
  &&  “ ((cm_rep_expr_value (e)) <= INT_MAX) ” 
  &&  “ (cm_args_wf policy p f (cm_call_args (e)) (cm_function_params ((cm_function_at (policy) ((cm_rep_expr_value (e))) ((cm_program_functions (p)))))) ) ” 
  &&  “ (cm_args_counts_representable policy p fid_pre (cm_call_args (e)) ) ” 
  &&  “ (cm_rep_args_safe (cm_call_args (e)) ) ” 
  &&  “ ((cm_rep_args_length ((cm_call_args (e)))) = (Zlength ((cm_call_args (e))))) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ (0 <= (temp_pre + (Zlength ((cm_call_args (e)))) )) ” 
  &&  “ ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre) ” 
  &&  “ ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= INT_MAX) ” 
  &&  “ (((temp_pre + (Zlength ((cm_call_args (e)))) ) + (cm_adepth ((cm_args_apair ((cm_call_args (e)))))) ) <= temp_limit_pre) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (lvalue_pre = 0) ” 
  &&  “ ((cm_rep_expr_kind (e)) = 8) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ (0 <= temp_pre) ” 
  &&  “ (temp_pre <= temp_limit_pre) ” 
  &&  “ ((temp_pre + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit_pre) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count pc_pre ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) ) ) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app (done) ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e))))))) ((cm_emit_args_reload (policy) (p) (fid_pre) (temp_pre) ((cm_call_args (e)))))) (cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) ((cm_rep_expr_value (e))))))) (tail)) )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_arg_list_rep xargs (cm_call_args (e)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
.

Definition cm_emit_call_expr_partial_solve_wit_8_pure := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_limit_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (retval: Z) (PreH1 : (0 <= temp_pre)) (PreH2 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre)) (PreH3 : (0 <= temp_limit_pre)) (PreH4 : (temp_limit_pre <= INT_MAX)) (PreH5 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH6 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH7 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH8 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH9 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH10 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH11 : (cm_wf_program policy cg p )) (PreH12 : (cm_typed_program policy p )) (PreH13 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH14 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH15 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH16 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH17 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH18 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH19 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH20 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH21 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH22 : (cm_args_wf policy p f (cm_call_args (e)) (cm_function_params ((cm_function_at (policy) ((cm_rep_expr_value (e))) ((cm_program_functions (p)))))) )) (PreH23 : (cm_args_counts_representable policy p fid_pre (cm_call_args (e)) )) (PreH24 : (0 <= temp_pre)) (PreH25 : (0 <= (temp_pre + (Zlength ((cm_call_args (e)))) ))) (PreH26 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre)) (PreH27 : (((temp_pre + (Zlength ((cm_call_args (e)))) ) + (cm_adepth ((cm_args_apair ((cm_call_args (e)))))) ) <= temp_limit_pre)) (PreH28 : (0 <= temp_limit_pre)) (PreH29 : (temp_limit_pre <= INT_MAX)) (PreH30 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH31 : (cm_i32_code_count pc_pre )) (PreH32 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e)))))) ) )) (PreH33 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e)))))) ) )) (PreH34 : (cm_rep_args_safe (cm_call_args (e)) )) (PreH35 : (retval = (cm_rep_args_length ((cm_call_args (e)))))) (PreH36 : (0 <= (cm_rep_expr_value (e)))) (PreH37 : ((cm_rep_expr_value (e)) <= INT_MAX)) (PreH38 : (cm_args_wf policy p f (cm_call_args (e)) (cm_function_params ((cm_function_at (policy) ((cm_rep_expr_value (e))) ((cm_program_functions (p)))))) )) (PreH39 : (cm_args_counts_representable policy p fid_pre (cm_call_args (e)) )) (PreH40 : (cm_rep_args_safe (cm_call_args (e)) )) (PreH41 : ((cm_rep_args_length ((cm_call_args (e)))) = (Zlength ((cm_call_args (e)))))) (PreH42 : (0 <= temp_limit_pre)) (PreH43 : (temp_limit_pre <= INT_MAX)) (PreH44 : (0 <= (temp_pre + (Zlength ((cm_call_args (e)))) ))) (PreH45 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre)) (PreH46 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= INT_MAX)) (PreH47 : (((temp_pre + (Zlength ((cm_call_args (e)))) ) + (cm_adepth ((cm_args_apair ((cm_call_args (e)))))) ) <= temp_limit_pre)) (PreH48 : (expr_pre <> 0)) (PreH49 : (lvalue_pre = 0)) (PreH50 : ((cm_rep_expr_kind (e)) = 8)) (PreH51 : (0 <= lvalue_pre)) (PreH52 : (lvalue_pre <= 1)) (PreH53 : (cm_wf_program policy cg p )) (PreH54 : (cm_typed_program policy p )) (PreH55 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH56 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH57 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH58 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH59 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH60 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH61 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH62 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH63 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH64 : (cm_expr_wf policy p f e )) (PreH65 : (cm_expr_counts_representable policy p fid_pre e )) (PreH66 : (0 <= temp_pre)) (PreH67 : (temp_pre <= temp_limit_pre)) (PreH68 : ((temp_pre + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit_pre)) (PreH69 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH70 : (cm_i32_code_count pc_pre )) (PreH71 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) ) )) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app (done) ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e))))))) ((cm_emit_args_reload (policy) (p) (fid_pre) (temp_pre) ((cm_call_args (e))))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) ((cm_rep_expr_value (e))))))) ((@nil tvm_inst))))) tail )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_arg_list_rep xargs (cm_call_args (e)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  ((( &( "pc" ) )) # Int  |-> pc_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((( &( "count" ) )) # Int  |-> (Zlength ((cm_call_args (e)))))
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "temp_limit" ) )) # Int  |-> temp_limit_pre)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "lvalue" ) )) # Int  |-> lvalue_pre)
|--
  “ ((cm_rep_expr_kind (e)) = 8) ” 
  &&  “ (expr_pre <> 0) ”
.

Definition cm_emit_call_expr_partial_solve_wit_8_aux := 
forall (emitter_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (temp_limit_pre: Z) (temp_pre: Z) (pc_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (next: Z) (body: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (xargs: Z) (retval: Z) (PreH1 : (0 <= temp_pre)) (PreH2 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre)) (PreH3 : (0 <= temp_limit_pre)) (PreH4 : (temp_limit_pre <= INT_MAX)) (PreH5 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH6 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH7 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH8 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH9 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH10 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH11 : (cm_wf_program policy cg p )) (PreH12 : (cm_typed_program policy p )) (PreH13 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH14 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH15 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH16 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH17 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH18 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH19 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH20 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH21 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH22 : (cm_args_wf policy p f (cm_call_args (e)) (cm_function_params ((cm_function_at (policy) ((cm_rep_expr_value (e))) ((cm_program_functions (p)))))) )) (PreH23 : (cm_args_counts_representable policy p fid_pre (cm_call_args (e)) )) (PreH24 : (0 <= temp_pre)) (PreH25 : (0 <= (temp_pre + (Zlength ((cm_call_args (e)))) ))) (PreH26 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre)) (PreH27 : (((temp_pre + (Zlength ((cm_call_args (e)))) ) + (cm_adepth ((cm_args_apair ((cm_call_args (e)))))) ) <= temp_limit_pre)) (PreH28 : (0 <= temp_limit_pre)) (PreH29 : (temp_limit_pre <= INT_MAX)) (PreH30 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH31 : (cm_i32_code_count pc_pre )) (PreH32 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e)))))) ) )) (PreH33 : (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e)))))) ) )) (PreH34 : (cm_rep_args_safe (cm_call_args (e)) )) (PreH35 : (retval = (cm_rep_args_length ((cm_call_args (e)))))) (PreH36 : (0 <= (cm_rep_expr_value (e)))) (PreH37 : ((cm_rep_expr_value (e)) <= INT_MAX)) (PreH38 : (cm_args_wf policy p f (cm_call_args (e)) (cm_function_params ((cm_function_at (policy) ((cm_rep_expr_value (e))) ((cm_program_functions (p)))))) )) (PreH39 : (cm_args_counts_representable policy p fid_pre (cm_call_args (e)) )) (PreH40 : (cm_rep_args_safe (cm_call_args (e)) )) (PreH41 : ((cm_rep_args_length ((cm_call_args (e)))) = (Zlength ((cm_call_args (e)))))) (PreH42 : (0 <= temp_limit_pre)) (PreH43 : (temp_limit_pre <= INT_MAX)) (PreH44 : (0 <= (temp_pre + (Zlength ((cm_call_args (e)))) ))) (PreH45 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre)) (PreH46 : ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= INT_MAX)) (PreH47 : (((temp_pre + (Zlength ((cm_call_args (e)))) ) + (cm_adepth ((cm_args_apair ((cm_call_args (e)))))) ) <= temp_limit_pre)) (PreH48 : (expr_pre <> 0)) (PreH49 : (lvalue_pre = 0)) (PreH50 : ((cm_rep_expr_kind (e)) = 8)) (PreH51 : (0 <= lvalue_pre)) (PreH52 : (lvalue_pre <= 1)) (PreH53 : (cm_wf_program policy cg p )) (PreH54 : (cm_typed_program policy p )) (PreH55 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH56 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH57 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH58 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH59 : (cm_rep_globals_safe (cm_program_globals (p)) )) (PreH60 : (cm_rep_strings_safe (cm_program_strings (p)) )) (PreH61 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH62 : (cm_rep_members_safe (cm_function_locals (f)) )) (PreH63 : (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560)) (PreH64 : (cm_expr_wf policy p f e )) (PreH65 : (cm_expr_counts_representable policy p fid_pre e )) (PreH66 : (0 <= temp_pre)) (PreH67 : (temp_pre <= temp_limit_pre)) (PreH68 : ((temp_pre + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit_pre)) (PreH69 : ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX)) (PreH70 : (cm_i32_code_count pc_pre )) (PreH71 : (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) ) )) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app (done) ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e))))))) ((cm_emit_args_reload (policy) (p) (fid_pre) (temp_pre) ((cm_call_args (e))))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) ((cm_rep_expr_value (e))))))) ((@nil tvm_inst))))) tail )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_arg_list_rep xargs (cm_call_args (e)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
|--
  “ ((cm_rep_expr_kind (e)) = 8) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (0 <= temp_pre) ” 
  &&  “ ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (cm_args_wf policy p f (cm_call_args (e)) (cm_function_params ((cm_function_at (policy) ((cm_rep_expr_value (e))) ((cm_program_functions (p)))))) ) ” 
  &&  “ (cm_args_counts_representable policy p fid_pre (cm_call_args (e)) ) ” 
  &&  “ (0 <= temp_pre) ” 
  &&  “ (0 <= (temp_pre + (Zlength ((cm_call_args (e)))) )) ” 
  &&  “ ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre) ” 
  &&  “ (((temp_pre + (Zlength ((cm_call_args (e)))) ) + (cm_adepth ((cm_args_apair ((cm_call_args (e)))))) ) <= temp_limit_pre) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count pc_pre ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e)))))) ) ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e)))))) ) ) ” 
  &&  “ (cm_rep_args_safe (cm_call_args (e)) ) ” 
  &&  “ (retval = (cm_rep_args_length ((cm_call_args (e))))) ” 
  &&  “ (0 <= (cm_rep_expr_value (e))) ” 
  &&  “ ((cm_rep_expr_value (e)) <= INT_MAX) ” 
  &&  “ (cm_args_wf policy p f (cm_call_args (e)) (cm_function_params ((cm_function_at (policy) ((cm_rep_expr_value (e))) ((cm_program_functions (p)))))) ) ” 
  &&  “ (cm_args_counts_representable policy p fid_pre (cm_call_args (e)) ) ” 
  &&  “ (cm_rep_args_safe (cm_call_args (e)) ) ” 
  &&  “ ((cm_rep_args_length ((cm_call_args (e)))) = (Zlength ((cm_call_args (e))))) ” 
  &&  “ (0 <= temp_limit_pre) ” 
  &&  “ (temp_limit_pre <= INT_MAX) ” 
  &&  “ (0 <= (temp_pre + (Zlength ((cm_call_args (e)))) )) ” 
  &&  “ ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= temp_limit_pre) ” 
  &&  “ ((temp_pre + (Zlength ((cm_call_args (e)))) ) <= INT_MAX) ” 
  &&  “ (((temp_pre + (Zlength ((cm_call_args (e)))) ) + (cm_adepth ((cm_args_apair ((cm_call_args (e)))))) ) <= temp_limit_pre) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (lvalue_pre = 0) ” 
  &&  “ ((cm_rep_expr_kind (e)) = 8) ” 
  &&  “ (0 <= lvalue_pre) ” 
  &&  “ (lvalue_pre <= 1) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (cm_typed_program policy p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) ) ” 
  &&  “ (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_rep_globals_safe (cm_program_globals (p)) ) ” 
  &&  “ (cm_rep_strings_safe (cm_program_strings (p)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_params (f)) ) ” 
  &&  “ (cm_rep_members_safe (cm_function_locals (f)) ) ” 
  &&  “ (((cm_rep_globals_size ((cm_program_globals (p)))) + (cm_rep_strings_size ((cm_program_strings (p)))) ) <= 1048560) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ (0 <= temp_pre) ” 
  &&  “ (temp_pre <= temp_limit_pre) ” 
  &&  “ ((temp_pre + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit_pre) ” 
  &&  “ ((cm_temp_offset (policy) (p) (fid_pre) (temp_limit_pre)) <= INT_MAX) ” 
  &&  “ (cm_i32_code_count pc_pre ) ” 
  &&  “ (cm_i32_code_count (pc_pre + (Zlength ((cm_expr_code_for (policy) (p) (fid_pre) (pc_pre) (temp_pre) (e) (lvalue_pre)))) ) ) ”
  &&  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_arg_list_rep xargs (cm_call_args (e)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app (done) ((cm_emit_args_store (policy) (p) (fid_pre) (pc_pre) (temp_pre) ((temp_pre + (Zlength ((cm_call_args (e)))) )) ((cm_call_args (e))))))) ((cm_emit_args_reload (policy) (p) (fid_pre) (temp_pre) ((cm_call_args (e))))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) ((cm_rep_expr_value (e))))))) ((@nil tvm_inst))))) tail )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_program_context_rep program_pre p functions_ptr )
.

Definition cm_emit_call_expr_partial_solve_wit_8 := cm_emit_call_expr_partial_solve_wit_8_pure -> cm_emit_call_expr_partial_solve_wit_8_aux.

Definition cm_emit_call_expr_which_implies_wit_1 := 
(
forall (e: cm_expr) (expr: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 8)) ,
  (cm_expr_rep expr e )
|--
  EX (xargs: Z) ,
  “ (expr <> 0) ”
  &&  ((&((expr)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_arg_list_rep xargs (cm_call_args (e)) )
) \/
(
forall (e: cm_expr) (expr: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 8)) ,
  (cm_expr_rep expr e )
|--
  EX (xargs: Z) ,
  “ (expr <> 0) ”
  &&  ((&((expr)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_arg_list_rep xargs (cm_call_args (e)) )
).

Definition cm_emit_call_expr_which_implies_wit_2 := 
(
forall (lvalue_pre: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (fid: Z) (temp: Z) (temp_limit: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 8)) (PreH2 : (lvalue_pre = 0)) (PreH3 : (cm_expr_wf policy p f e )) (PreH4 : (cm_expr_counts_representable policy p fid e )) (PreH5 : (0 <= temp)) (PreH6 : (temp <= temp_limit)) (PreH7 : ((temp + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit)) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_limit)) <= INT_MAX)) (PreH9 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH10 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH11 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH12 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH13 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  TT && emp 
|--
  “ (0 <= (cm_rep_expr_value (e))) ” 
  &&  “ ((cm_rep_expr_value (e)) <= INT_MAX) ” 
  &&  “ (cm_args_wf policy p f (cm_call_args (e)) (cm_function_params ((cm_function_at (policy) ((cm_rep_expr_value (e))) ((cm_program_functions (p)))))) ) ” 
  &&  “ (cm_args_counts_representable policy p fid (cm_call_args (e)) ) ” 
  &&  “ (cm_rep_args_safe (cm_call_args (e)) ) ” 
  &&  “ ((cm_rep_args_length ((cm_call_args (e)))) = (Zlength ((cm_call_args (e))))) ” 
  &&  “ (0 <= temp_limit) ” 
  &&  “ (temp_limit <= INT_MAX) ” 
  &&  “ (0 <= (temp + (Zlength ((cm_call_args (e)))) )) ” 
  &&  “ ((temp + (Zlength ((cm_call_args (e)))) ) <= temp_limit) ” 
  &&  “ ((temp + (Zlength ((cm_call_args (e)))) ) <= INT_MAX) ” 
  &&  “ (((temp + (Zlength ((cm_call_args (e)))) ) + (cm_adepth ((cm_args_apair ((cm_call_args (e)))))) ) <= temp_limit) ”
  &&  emp
) \/
(
forall (lvalue_pre: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (fid: Z) (temp: Z) (temp_limit: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 8)) (PreH2 : (lvalue_pre = 0)) (PreH3 : (cm_expr_wf policy p f e )) (PreH4 : (cm_expr_counts_representable policy p fid e )) (PreH5 : (0 <= temp)) (PreH6 : (temp <= temp_limit)) (PreH7 : ((temp + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit)) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_limit)) <= INT_MAX)) (PreH9 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH10 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH11 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH12 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH13 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  TT && emp 
|--
  “ (((temp + (Zlength ((cm_call_args (e)))) ) + (cm_adepth ((cm_args_apair ((cm_call_args (e)))))) ) <= temp_limit) ” 
  &&  “ ((temp + (Zlength ((cm_call_args (e)))) ) <= INT_MAX) ” 
  &&  “ ((temp + (Zlength ((cm_call_args (e)))) ) <= temp_limit) ” 
  &&  “ (0 <= (temp + (Zlength ((cm_call_args (e)))) )) ” 
  &&  “ (temp_limit <= INT_MAX) ” 
  &&  “ ((cm_rep_args_length ((cm_call_args (e)))) = (Zlength ((cm_call_args (e))))) ” 
  &&  “ (cm_rep_args_safe (cm_call_args (e)) ) ” 
  &&  “ (cm_args_counts_representable policy p fid (cm_call_args (e)) ) ” 
  &&  “ (cm_args_wf policy p f (cm_call_args (e)) (cm_function_params ((cm_function_at (policy) ((cm_rep_expr_value (e))) ((cm_program_functions (p)))))) ) ” 
  &&  “ ((cm_rep_expr_value (e)) <= INT_MAX) ” 
  &&  “ (0 <= (cm_rep_expr_value (e))) ”
  &&  emp
).

Definition cm_emit_call_expr_which_implies_wit_2_split_goal_1 := 
forall (lvalue_pre: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (fid: Z) (temp: Z) (temp_limit: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 8)) (PreH2 : (lvalue_pre = 0)) (PreH3 : (cm_expr_wf policy p f e )) (PreH4 : (cm_expr_counts_representable policy p fid e )) (PreH5 : (0 <= temp)) (PreH6 : (temp <= temp_limit)) (PreH7 : ((temp + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit)) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_limit)) <= INT_MAX)) (PreH9 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH10 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH11 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH12 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH13 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  (((temp + (Zlength ((cm_call_args (e)))) ) + (cm_adepth ((cm_args_apair ((cm_call_args (e)))))) ) <= temp_limit)
.

Definition cm_emit_call_expr_which_implies_wit_2_split_goal_2 := 
forall (lvalue_pre: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (fid: Z) (temp: Z) (temp_limit: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 8)) (PreH2 : (lvalue_pre = 0)) (PreH3 : (cm_expr_wf policy p f e )) (PreH4 : (cm_expr_counts_representable policy p fid e )) (PreH5 : (0 <= temp)) (PreH6 : (temp <= temp_limit)) (PreH7 : ((temp + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit)) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_limit)) <= INT_MAX)) (PreH9 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH10 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH11 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH12 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH13 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  ((temp + (Zlength ((cm_call_args (e)))) ) <= INT_MAX)
.

Definition cm_emit_call_expr_which_implies_wit_2_split_goal_3 := 
forall (lvalue_pre: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (fid: Z) (temp: Z) (temp_limit: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 8)) (PreH2 : (lvalue_pre = 0)) (PreH3 : (cm_expr_wf policy p f e )) (PreH4 : (cm_expr_counts_representable policy p fid e )) (PreH5 : (0 <= temp)) (PreH6 : (temp <= temp_limit)) (PreH7 : ((temp + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit)) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_limit)) <= INT_MAX)) (PreH9 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH10 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH11 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH12 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH13 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  ((temp + (Zlength ((cm_call_args (e)))) ) <= temp_limit)
.

Definition cm_emit_call_expr_which_implies_wit_2_split_goal_4 := 
forall (lvalue_pre: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (fid: Z) (temp: Z) (temp_limit: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 8)) (PreH2 : (lvalue_pre = 0)) (PreH3 : (cm_expr_wf policy p f e )) (PreH4 : (cm_expr_counts_representable policy p fid e )) (PreH5 : (0 <= temp)) (PreH6 : (temp <= temp_limit)) (PreH7 : ((temp + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit)) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_limit)) <= INT_MAX)) (PreH9 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH10 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH11 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH12 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH13 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  (0 <= (temp + (Zlength ((cm_call_args (e)))) ))
.

Definition cm_emit_call_expr_which_implies_wit_2_split_goal_5 := 
forall (lvalue_pre: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (fid: Z) (temp: Z) (temp_limit: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 8)) (PreH2 : (lvalue_pre = 0)) (PreH3 : (cm_expr_wf policy p f e )) (PreH4 : (cm_expr_counts_representable policy p fid e )) (PreH5 : (0 <= temp)) (PreH6 : (temp <= temp_limit)) (PreH7 : ((temp + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit)) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_limit)) <= INT_MAX)) (PreH9 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH10 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH11 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH12 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH13 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  (temp_limit <= INT_MAX)
.

Definition cm_emit_call_expr_which_implies_wit_2_split_goal_6 := 
forall (lvalue_pre: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (fid: Z) (temp: Z) (temp_limit: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 8)) (PreH2 : (lvalue_pre = 0)) (PreH3 : (cm_expr_wf policy p f e )) (PreH4 : (cm_expr_counts_representable policy p fid e )) (PreH5 : (0 <= temp)) (PreH6 : (temp <= temp_limit)) (PreH7 : ((temp + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit)) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_limit)) <= INT_MAX)) (PreH9 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH10 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH11 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH12 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH13 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  ((cm_rep_args_length ((cm_call_args (e)))) = (Zlength ((cm_call_args (e)))))
.

Definition cm_emit_call_expr_which_implies_wit_2_split_goal_7 := 
forall (lvalue_pre: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (fid: Z) (temp: Z) (temp_limit: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 8)) (PreH2 : (lvalue_pre = 0)) (PreH3 : (cm_expr_wf policy p f e )) (PreH4 : (cm_expr_counts_representable policy p fid e )) (PreH5 : (0 <= temp)) (PreH6 : (temp <= temp_limit)) (PreH7 : ((temp + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit)) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_limit)) <= INT_MAX)) (PreH9 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH10 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH11 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH12 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH13 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  (cm_rep_args_safe (cm_call_args (e)) )
.

Definition cm_emit_call_expr_which_implies_wit_2_split_goal_8 := 
forall (lvalue_pre: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (fid: Z) (temp: Z) (temp_limit: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 8)) (PreH2 : (lvalue_pre = 0)) (PreH3 : (cm_expr_wf policy p f e )) (PreH4 : (cm_expr_counts_representable policy p fid e )) (PreH5 : (0 <= temp)) (PreH6 : (temp <= temp_limit)) (PreH7 : ((temp + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit)) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_limit)) <= INT_MAX)) (PreH9 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH10 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH11 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH12 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH13 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  (cm_args_counts_representable policy p fid (cm_call_args (e)) )
.

Definition cm_emit_call_expr_which_implies_wit_2_split_goal_9 := 
forall (lvalue_pre: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (fid: Z) (temp: Z) (temp_limit: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 8)) (PreH2 : (lvalue_pre = 0)) (PreH3 : (cm_expr_wf policy p f e )) (PreH4 : (cm_expr_counts_representable policy p fid e )) (PreH5 : (0 <= temp)) (PreH6 : (temp <= temp_limit)) (PreH7 : ((temp + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit)) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_limit)) <= INT_MAX)) (PreH9 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH10 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH11 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH12 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH13 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  (cm_args_wf policy p f (cm_call_args (e)) (cm_function_params ((cm_function_at (policy) ((cm_rep_expr_value (e))) ((cm_program_functions (p)))))) )
.

Definition cm_emit_call_expr_which_implies_wit_2_split_goal_10 := 
forall (lvalue_pre: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (fid: Z) (temp: Z) (temp_limit: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 8)) (PreH2 : (lvalue_pre = 0)) (PreH3 : (cm_expr_wf policy p f e )) (PreH4 : (cm_expr_counts_representable policy p fid e )) (PreH5 : (0 <= temp)) (PreH6 : (temp <= temp_limit)) (PreH7 : ((temp + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit)) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_limit)) <= INT_MAX)) (PreH9 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH10 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH11 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH12 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH13 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  ((cm_rep_expr_value (e)) <= INT_MAX)
.

Definition cm_emit_call_expr_which_implies_wit_2_split_goal_11 := 
forall (lvalue_pre: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (fid: Z) (temp: Z) (temp_limit: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 8)) (PreH2 : (lvalue_pre = 0)) (PreH3 : (cm_expr_wf policy p f e )) (PreH4 : (cm_expr_counts_representable policy p fid e )) (PreH5 : (0 <= temp)) (PreH6 : (temp <= temp_limit)) (PreH7 : ((temp + (cm_expr_temps_for (e) (lvalue_pre)) ) <= temp_limit)) (PreH8 : ((cm_temp_offset (policy) (p) (fid) (temp_limit)) <= INT_MAX)) (PreH9 : (f = (cm_function_at (policy) (fid) ((cm_program_functions (p)))))) (PreH10 : (cm_slots_wf (cm_program_structs (p)) (cm_function_params (f)) )) (PreH11 : (cm_slots_wf (cm_program_structs (p)) (cm_function_locals (f)) )) (PreH12 : (cm_rep_members_safe (cm_function_params (f)) )) (PreH13 : (cm_rep_members_safe (cm_function_locals (f)) )) ,
  (0 <= (cm_rep_expr_value (e)))
.

Definition cm_emit_call_expr_which_implies_wit_3 := 
(
forall (lvalue_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (e: cm_expr) (p: cm_program) (policy: cm_lookup_policy) (count: Z) (pc: Z) (temp: Z) (fid: Z) (emitter: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 8)) (PreH2 : (lvalue_pre = 0)) (PreH3 : (count = (Zlength ((cm_call_args (e)))))) (PreH4 : (cm_i32_code_count pc )) (PreH5 : (cm_i32_code_count (pc + (Zlength ((cm_expr_code_for (policy) (p) (fid) (pc) (temp) (e) (lvalue_pre)))) ) )) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_expr_code_for (policy) (p) (fid) (pc) (temp) (e) (lvalue_pre))) (tail)) )
|--
  “ (cm_i32_code_count (pc + (Zlength ((cm_emit_args_store (policy) (p) (fid) (pc) (temp) ((temp + count )) ((cm_call_args (e)))))) ) ) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_emit_args_store (policy) (p) (fid) (pc) (temp) ((temp + count )) ((cm_call_args (e))))) ((app ((cm_emit_args_reload (policy) (p) (fid) (temp) ((cm_call_args (e))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) ((cm_rep_expr_value (e))))))) (tail)))))) )
) \/
(
forall (lvalue_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (e: cm_expr) (p: cm_program) (policy: cm_lookup_policy) (count: Z) (pc: Z) (temp: Z) (fid: Z) (emitter: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 8)) (PreH2 : (lvalue_pre = 0)) (PreH3 : (count = (Zlength ((cm_call_args (e)))))) (PreH4 : (cm_i32_code_count pc )) (PreH5 : (cm_i32_code_count (pc + (Zlength ((cm_expr_code_for (policy) (p) (fid) (pc) (temp) (e) (lvalue_pre)))) ) )) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_expr_code_for (policy) (p) (fid) (pc) (temp) (e) (lvalue_pre))) (tail)) )
|--
  “ (cm_i32_code_count (pc + (Zlength ((cm_emit_args_store (policy) (p) (fid) (pc) (temp) ((temp + count )) ((cm_call_args (e)))))) ) ) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_emit_args_store (policy) (p) (fid) (pc) (temp) ((temp + count )) ((cm_call_args (e))))) ((app ((cm_emit_args_reload (policy) (p) (fid) (temp) ((cm_call_args (e))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) ((cm_rep_expr_value (e))))))) (tail)))))) )
).

Definition cm_emit_call_expr_which_implies_wit_3_split_goal_1 := 
forall (lvalue_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (e: cm_expr) (p: cm_program) (policy: cm_lookup_policy) (count: Z) (pc: Z) (temp: Z) (fid: Z) (emitter: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 8)) (PreH2 : (lvalue_pre = 0)) (PreH3 : (count = (Zlength ((cm_call_args (e)))))) (PreH4 : (cm_i32_code_count pc )) (PreH5 : (cm_i32_code_count (pc + (Zlength ((cm_expr_code_for (policy) (p) (fid) (pc) (temp) (e) (lvalue_pre)))) ) )) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_expr_code_for (policy) (p) (fid) (pc) (temp) (e) (lvalue_pre))) (tail)) )
|--
  “ (cm_i32_code_count (pc + (Zlength ((cm_emit_args_store (policy) (p) (fid) (pc) (temp) ((temp + count )) ((cm_call_args (e)))))) ) ) ”
.

Definition cm_emit_call_expr_which_implies_wit_3_split_goal_spatial := 
forall (lvalue_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (e: cm_expr) (p: cm_program) (policy: cm_lookup_policy) (count: Z) (pc: Z) (temp: Z) (fid: Z) (emitter: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 8)) (PreH2 : (lvalue_pre = 0)) (PreH3 : (count = (Zlength ((cm_call_args (e)))))) (PreH4 : (cm_i32_code_count pc )) (PreH5 : (cm_i32_code_count (pc + (Zlength ((cm_expr_code_for (policy) (p) (fid) (pc) (temp) (e) (lvalue_pre)))) ) )) ,
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_expr_code_for (policy) (p) (fid) (pc) (temp) (e) (lvalue_pre))) (tail)) )
|--
  (cm_resolved_emitter_plan_rep policy p emitter out capacity done (app ((cm_emit_args_store (policy) (p) (fid) (pc) (temp) ((temp + count )) ((cm_call_args (e))))) ((app ((cm_emit_args_reload (policy) (p) (fid) (temp) ((cm_call_args (e))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) ((cm_rep_expr_value (e))))))) (tail)))))) )
.

Definition cm_emit_call_expr_which_implies_wit_4 := 
(
forall (e: cm_expr) (xargs: Z) (expr: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 8)) (PreH2 : (expr <> 0)) ,
  ((&((expr)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_arg_list_rep xargs (cm_call_args (e)) )
|--
  (cm_expr_rep expr e )
) \/
(
forall (e: cm_expr) (xargs: Z) (expr: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_kind (e)) = 8)) (PreH10 : (expr <> 0)) ,
  ((&((expr)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_arg_list_rep xargs (cm_call_args (e)) )
|--
  (cm_expr_rep expr e )
).

Definition cm_emit_call_expr_which_implies_wit_4_split_goal_spatial := 
forall (e: cm_expr) (xargs: Z) (expr: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_kind (e)) = 8)) (PreH10 : (expr <> 0)) ,
  ((&((expr)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr)  # "cm_expr" ->ₛ "a")) # Ptr  |-> 0)
  **  ((&((expr)  # "cm_expr" ->ₛ "b")) # Ptr  |-> 0)
  **  ((&((expr)  # "cm_expr" ->ₛ "args")) # Ptr  |-> xargs)
  **  (cm_arg_list_rep xargs (cm_call_args (e)) )
|--
  (cm_expr_rep expr e )
.

Module Type VC_Correct.


Axiom proof_of_cm_emit_args_reload_plan_safety_wit_1 : cm_emit_args_reload_plan_safety_wit_1.
Axiom proof_of_cm_emit_args_reload_plan_safety_wit_2 : cm_emit_args_reload_plan_safety_wit_2.
Axiom proof_of_cm_emit_args_reload_plan_safety_wit_3 : cm_emit_args_reload_plan_safety_wit_3.
Axiom proof_of_cm_emit_args_reload_plan_return_wit_1 : cm_emit_args_reload_plan_return_wit_1.
Axiom proof_of_cm_emit_args_reload_plan_return_wit_2 : cm_emit_args_reload_plan_return_wit_2.
Axiom proof_of_cm_emit_args_reload_plan_partial_solve_wit_1_pure : cm_emit_args_reload_plan_partial_solve_wit_1_pure.
Axiom proof_of_cm_emit_args_reload_plan_partial_solve_wit_1 : cm_emit_args_reload_plan_partial_solve_wit_1.
Axiom proof_of_cm_emit_args_reload_plan_partial_solve_wit_2_pure : cm_emit_args_reload_plan_partial_solve_wit_2_pure.
Axiom proof_of_cm_emit_args_reload_plan_partial_solve_wit_2 : cm_emit_args_reload_plan_partial_solve_wit_2.
Axiom proof_of_cm_emit_args_reload_plan_partial_solve_wit_3_pure : cm_emit_args_reload_plan_partial_solve_wit_3_pure.
Axiom proof_of_cm_emit_args_reload_plan_partial_solve_wit_3 : cm_emit_args_reload_plan_partial_solve_wit_3.
Axiom proof_of_cm_emit_args_reload_plan_partial_solve_wit_4_pure : cm_emit_args_reload_plan_partial_solve_wit_4_pure.
Axiom proof_of_cm_emit_args_reload_plan_partial_solve_wit_4 : cm_emit_args_reload_plan_partial_solve_wit_4.
Axiom proof_of_cm_emit_args_reload_plan_partial_solve_wit_5_pure : cm_emit_args_reload_plan_partial_solve_wit_5_pure.
Axiom proof_of_cm_emit_args_reload_plan_partial_solve_wit_5 : cm_emit_args_reload_plan_partial_solve_wit_5.
Axiom proof_of_cm_emit_args_reload_plan_partial_solve_wit_6_pure : cm_emit_args_reload_plan_partial_solve_wit_6_pure.
Axiom proof_of_cm_emit_args_reload_plan_partial_solve_wit_6 : cm_emit_args_reload_plan_partial_solve_wit_6.
Axiom proof_of_cm_emit_args_reload_plan_partial_solve_wit_7_pure : cm_emit_args_reload_plan_partial_solve_wit_7_pure.
Axiom proof_of_cm_emit_args_reload_plan_partial_solve_wit_7 : cm_emit_args_reload_plan_partial_solve_wit_7.
Axiom proof_of_cm_emit_args_reload_plan_which_implies_wit_1 : cm_emit_args_reload_plan_which_implies_wit_1.
Axiom proof_of_cm_emit_args_reload_plan_which_implies_wit_2 : cm_emit_args_reload_plan_which_implies_wit_2.
Axiom proof_of_cm_emit_args_reload_plan_which_implies_wit_3 : cm_emit_args_reload_plan_which_implies_wit_3.
Axiom proof_of_cm_emit_args_reload_plan_which_implies_wit_4 : cm_emit_args_reload_plan_which_implies_wit_4.
Axiom proof_of_cm_emit_args_reload_plan_which_implies_wit_5 : cm_emit_args_reload_plan_which_implies_wit_5.
Axiom proof_of_cm_emit_args_store_plan_safety_wit_1 : cm_emit_args_store_plan_safety_wit_1.
Axiom proof_of_cm_emit_args_store_plan_safety_wit_2 : cm_emit_args_store_plan_safety_wit_2.
Axiom proof_of_cm_emit_args_store_plan_safety_wit_3 : cm_emit_args_store_plan_safety_wit_3.
Axiom proof_of_cm_emit_args_store_plan_safety_wit_4 : cm_emit_args_store_plan_safety_wit_4.
Axiom proof_of_cm_emit_args_store_plan_safety_wit_5 : cm_emit_args_store_plan_safety_wit_5.
Axiom proof_of_cm_emit_args_store_plan_safety_wit_6 : cm_emit_args_store_plan_safety_wit_6.
Axiom proof_of_cm_emit_args_store_plan_safety_wit_7 : cm_emit_args_store_plan_safety_wit_7.
Axiom proof_of_cm_emit_args_store_plan_return_wit_1 : cm_emit_args_store_plan_return_wit_1.
Axiom proof_of_cm_emit_args_store_plan_return_wit_2 : cm_emit_args_store_plan_return_wit_2.
Axiom proof_of_cm_emit_args_store_plan_partial_solve_wit_1_pure : cm_emit_args_store_plan_partial_solve_wit_1_pure.
Axiom proof_of_cm_emit_args_store_plan_partial_solve_wit_1 : cm_emit_args_store_plan_partial_solve_wit_1.
Axiom proof_of_cm_emit_args_store_plan_partial_solve_wit_2_pure : cm_emit_args_store_plan_partial_solve_wit_2_pure.
Axiom proof_of_cm_emit_args_store_plan_partial_solve_wit_2 : cm_emit_args_store_plan_partial_solve_wit_2.
Axiom proof_of_cm_emit_args_store_plan_partial_solve_wit_3_pure : cm_emit_args_store_plan_partial_solve_wit_3_pure.
Axiom proof_of_cm_emit_args_store_plan_partial_solve_wit_3 : cm_emit_args_store_plan_partial_solve_wit_3.
Axiom proof_of_cm_emit_args_store_plan_partial_solve_wit_4_pure : cm_emit_args_store_plan_partial_solve_wit_4_pure.
Axiom proof_of_cm_emit_args_store_plan_partial_solve_wit_4 : cm_emit_args_store_plan_partial_solve_wit_4.
Axiom proof_of_cm_emit_args_store_plan_partial_solve_wit_5_pure : cm_emit_args_store_plan_partial_solve_wit_5_pure.
Axiom proof_of_cm_emit_args_store_plan_partial_solve_wit_5 : cm_emit_args_store_plan_partial_solve_wit_5.
Axiom proof_of_cm_emit_args_store_plan_partial_solve_wit_6_pure : cm_emit_args_store_plan_partial_solve_wit_6_pure.
Axiom proof_of_cm_emit_args_store_plan_partial_solve_wit_6 : cm_emit_args_store_plan_partial_solve_wit_6.
Axiom proof_of_cm_emit_args_store_plan_partial_solve_wit_7_pure : cm_emit_args_store_plan_partial_solve_wit_7_pure.
Axiom proof_of_cm_emit_args_store_plan_partial_solve_wit_7 : cm_emit_args_store_plan_partial_solve_wit_7.
Axiom proof_of_cm_emit_args_store_plan_partial_solve_wit_8_pure : cm_emit_args_store_plan_partial_solve_wit_8_pure.
Axiom proof_of_cm_emit_args_store_plan_partial_solve_wit_8 : cm_emit_args_store_plan_partial_solve_wit_8.
Axiom proof_of_cm_emit_args_store_plan_partial_solve_wit_9_pure : cm_emit_args_store_plan_partial_solve_wit_9_pure.
Axiom proof_of_cm_emit_args_store_plan_partial_solve_wit_9 : cm_emit_args_store_plan_partial_solve_wit_9.
Axiom proof_of_cm_emit_args_store_plan_partial_solve_wit_10_pure : cm_emit_args_store_plan_partial_solve_wit_10_pure.
Axiom proof_of_cm_emit_args_store_plan_partial_solve_wit_10 : cm_emit_args_store_plan_partial_solve_wit_10.
Axiom proof_of_cm_emit_args_store_plan_which_implies_wit_1 : cm_emit_args_store_plan_which_implies_wit_1.
Axiom proof_of_cm_emit_args_store_plan_which_implies_wit_2 : cm_emit_args_store_plan_which_implies_wit_2.
Axiom proof_of_cm_emit_args_store_plan_which_implies_wit_3 : cm_emit_args_store_plan_which_implies_wit_3.
Axiom proof_of_cm_emit_args_store_plan_which_implies_wit_4 : cm_emit_args_store_plan_which_implies_wit_4.
Axiom proof_of_cm_emit_args_store_plan_which_implies_wit_5 : cm_emit_args_store_plan_which_implies_wit_5.
Axiom proof_of_cm_emit_args_store_plan_which_implies_wit_6 : cm_emit_args_store_plan_which_implies_wit_6.
Axiom proof_of_cm_emit_call_expr_safety_wit_1 : cm_emit_call_expr_safety_wit_1.
Axiom proof_of_cm_emit_call_expr_return_wit_1 : cm_emit_call_expr_return_wit_1.
Axiom proof_of_cm_emit_call_expr_return_wit_2 : cm_emit_call_expr_return_wit_2.
Axiom proof_of_cm_emit_call_expr_partial_solve_wit_1_pure : cm_emit_call_expr_partial_solve_wit_1_pure.
Axiom proof_of_cm_emit_call_expr_partial_solve_wit_1 : cm_emit_call_expr_partial_solve_wit_1.
Axiom proof_of_cm_emit_call_expr_partial_solve_wit_2_pure : cm_emit_call_expr_partial_solve_wit_2_pure.
Axiom proof_of_cm_emit_call_expr_partial_solve_wit_2 : cm_emit_call_expr_partial_solve_wit_2.
Axiom proof_of_cm_emit_call_expr_partial_solve_wit_3_pure : cm_emit_call_expr_partial_solve_wit_3_pure.
Axiom proof_of_cm_emit_call_expr_partial_solve_wit_3 : cm_emit_call_expr_partial_solve_wit_3.
Axiom proof_of_cm_emit_call_expr_partial_solve_wit_4_pure : cm_emit_call_expr_partial_solve_wit_4_pure.
Axiom proof_of_cm_emit_call_expr_partial_solve_wit_4 : cm_emit_call_expr_partial_solve_wit_4.
Axiom proof_of_cm_emit_call_expr_partial_solve_wit_5_pure : cm_emit_call_expr_partial_solve_wit_5_pure.
Axiom proof_of_cm_emit_call_expr_partial_solve_wit_5 : cm_emit_call_expr_partial_solve_wit_5.
Axiom proof_of_cm_emit_call_expr_partial_solve_wit_6_pure : cm_emit_call_expr_partial_solve_wit_6_pure.
Axiom proof_of_cm_emit_call_expr_partial_solve_wit_6 : cm_emit_call_expr_partial_solve_wit_6.
Axiom proof_of_cm_emit_call_expr_partial_solve_wit_7 : cm_emit_call_expr_partial_solve_wit_7.
Axiom proof_of_cm_emit_call_expr_partial_solve_wit_8_pure : cm_emit_call_expr_partial_solve_wit_8_pure.
Axiom proof_of_cm_emit_call_expr_partial_solve_wit_8 : cm_emit_call_expr_partial_solve_wit_8.
Axiom proof_of_cm_emit_call_expr_which_implies_wit_1 : cm_emit_call_expr_which_implies_wit_1.
Axiom proof_of_cm_emit_call_expr_which_implies_wit_2 : cm_emit_call_expr_which_implies_wit_2.
Axiom proof_of_cm_emit_call_expr_which_implies_wit_3 : cm_emit_call_expr_which_implies_wit_3.
Axiom proof_of_cm_emit_call_expr_which_implies_wit_4 : cm_emit_call_expr_which_implies_wit_4.

End VC_Correct.
