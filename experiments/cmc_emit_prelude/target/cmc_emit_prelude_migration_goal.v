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
Require Import SimpleC.EE.QCP_demos_human.cmc_emit_prelude_migration_lib.
Local Open Scope sac.

(*----- Function cmc_emit_prelude -----*)

Definition cmc_emit_prelude_safety_wit_1 := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "main_id" ) )) # Int  |-> main_id)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) (1048576))) ((cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))))))))))))))))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_emit_prelude_safety_wit_2 := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "main_id" ) )) # Int  |-> main_id)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) (1048576))) ((cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))))))))))))))))) )
|--
  “ (1048576 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1048576) ”
.

Definition cmc_emit_prelude_safety_wit_3 := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))))))))))))))) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "main_id" ) )) # Int  |-> main_id)
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_emit_prelude_safety_wit_4 := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))))))))))))))) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "main_id" ) )) # Int  |-> main_id)
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition cmc_emit_prelude_safety_wit_5 := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))))))))))))) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "main_id" ) )) # Int  |-> main_id)
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (5 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 5) ”
.

Definition cmc_emit_prelude_safety_wit_6 := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))))))))))))) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "main_id" ) )) # Int  |-> main_id)
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_emit_prelude_safety_wit_7 := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))))))))) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "main_id" ) )) # Int  |-> main_id)
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_emit_prelude_safety_wit_8 := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))))))))) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "main_id" ) )) # Int  |-> main_id)
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (256 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 256) ”
.

Definition cmc_emit_prelude_safety_wit_9 := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))))))) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "main_id" ) )) # Int  |-> main_id)
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (12 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 12) ”
.

Definition cmc_emit_prelude_safety_wit_10 := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))))))) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "main_id" ) )) # Int  |-> main_id)
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_emit_prelude_safety_wit_11 := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))))) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "main_id" ) )) # Int  |-> main_id)
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_emit_prelude_safety_wit_12 := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))))) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "main_id" ) )) # Int  |-> main_id)
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (256 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 256) ”
.

Definition cmc_emit_prelude_safety_wit_13 := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "main_id" ) )) # Int  |-> main_id)
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition cmc_emit_prelude_safety_wit_14 := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "main_id" ) )) # Int  |-> main_id)
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_emit_prelude_safety_wit_15 := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMAddOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "main_id" ) )) # Int  |-> main_id)
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_emit_prelude_safety_wit_16 := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMAddOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "main_id" ) )) # Int  |-> main_id)
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (256 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 256) ”
.

Definition cmc_emit_prelude_safety_wit_17 := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMAddOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "main_id" ) )) # Int  |-> main_id)
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (12 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 12) ”
.

Definition cmc_emit_prelude_safety_wit_18 := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMAddOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "main_id" ) )) # Int  |-> main_id)
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_emit_prelude_safety_wit_19 := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app ((app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMAddOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMHaltOp) (0))) (tail)) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "main_id" ) )) # Int  |-> main_id)
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (27 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 27) ”
.

Definition cmc_emit_prelude_safety_wit_20 := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app ((app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMAddOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMHaltOp) (0))) (tail)) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "main_id" ) )) # Int  |-> main_id)
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_emit_prelude_entail_wit_1 := 
(
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_prelude (policy) (p))) (tail)) )
|--
  EX (tp: Z)  (gp: Z)  (sp: Z) ,
  “ (program_pre <> 0) ”
  &&  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_prelude (policy) (p))) (tail)) )
) \/
(
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_prelude (policy) (p))) (tail)) )
|--
  EX (tp: Z)  (gp: Z)  (sp: Z) ,
  “ (program_pre <> 0) ”
  &&  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_prelude (policy) (p))) (tail)) )
).

Definition cmc_emit_prelude_entail_wit_2 := 
(
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (PreH1 : (program_pre <> 0)) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_prelude (policy) (p))) (tail)) )
|--
  “ ((cm_program_main (p)) = (cm_program_main (p))) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) = 0) ” 
  &&  “ ((tvm_opcode_code (TVMStoreOp)) = 5) ” 
  &&  “ ((tvm_opcode_code (TVMModOp)) = 12) ” 
  &&  “ ((tvm_opcode_code (TVMAddOp)) = 8) ” 
  &&  “ ((tvm_opcode_code (TVMHaltOp)) = 27) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) (1048576))) ((cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) ((cm_program_main (p))))))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))))))))))))))))) )
) \/
(
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (PreH1 : ((cm_program_main (p)) <= INT_MAX)) (PreH2 : ((cm_program_main (p)) >= INT_MIN)) (PreH3 : (program_pre <> 0)) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_prelude (policy) (p))) (tail)) )
|--
  “ ((tvm_opcode_code (TVMHaltOp)) = 27) ” 
  &&  “ ((tvm_opcode_code (TVMAddOp)) = 8) ” 
  &&  “ ((tvm_opcode_code (TVMModOp)) = 12) ” 
  &&  “ ((tvm_opcode_code (TVMStoreOp)) = 5) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) = 0) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) (1048576))) ((cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) ((cm_program_main (p))))))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))))))))))))))))) )
).

Definition cmc_emit_prelude_entail_wit_2_split_goal_1 := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (PreH1 : ((cm_program_main (p)) <= INT_MAX)) (PreH2 : ((cm_program_main (p)) >= INT_MIN)) (PreH3 : (program_pre <> 0)) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_prelude (policy) (p))) (tail)) )
|--
  “ ((tvm_opcode_code (TVMHaltOp)) = 27) ”
.

Definition cmc_emit_prelude_entail_wit_2_split_goal_2 := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (PreH1 : ((cm_program_main (p)) <= INT_MAX)) (PreH2 : ((cm_program_main (p)) >= INT_MIN)) (PreH3 : (program_pre <> 0)) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_prelude (policy) (p))) (tail)) )
|--
  “ ((tvm_opcode_code (TVMAddOp)) = 8) ”
.

Definition cmc_emit_prelude_entail_wit_2_split_goal_3 := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (PreH1 : ((cm_program_main (p)) <= INT_MAX)) (PreH2 : ((cm_program_main (p)) >= INT_MIN)) (PreH3 : (program_pre <> 0)) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_prelude (policy) (p))) (tail)) )
|--
  “ ((tvm_opcode_code (TVMModOp)) = 12) ”
.

Definition cmc_emit_prelude_entail_wit_2_split_goal_4 := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (PreH1 : ((cm_program_main (p)) <= INT_MAX)) (PreH2 : ((cm_program_main (p)) >= INT_MIN)) (PreH3 : (program_pre <> 0)) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_prelude (policy) (p))) (tail)) )
|--
  “ ((tvm_opcode_code (TVMStoreOp)) = 5) ”
.

Definition cmc_emit_prelude_entail_wit_2_split_goal_5 := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (PreH1 : ((cm_program_main (p)) <= INT_MAX)) (PreH2 : ((cm_program_main (p)) >= INT_MIN)) (PreH3 : (program_pre <> 0)) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_prelude (policy) (p))) (tail)) )
|--
  “ ((tvm_opcode_code (TVMPushOp)) = 0) ”
.

Definition cmc_emit_prelude_entail_wit_2_split_goal_spatial := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (sp: Z) (gp: Z) (tp: Z) (PreH1 : ((cm_program_main (p)) <= INT_MAX)) (PreH2 : ((cm_program_main (p)) >= INT_MIN)) (PreH3 : (program_pre <> 0)) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> sp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> gp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> tp)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep sp (cm_program_structs (p)) )
  **  (cm_global_list_rep gp (cm_program_globals (p)) )
  **  (cm_string_list_rep tp (cm_program_strings (p)) )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app ((cm_emit_prelude (policy) (p))) (tail)) )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) (1048576))) ((cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) ((cm_program_main (p))))))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))))))))))))))))) )
.

Definition cmc_emit_prelude_return_wit_1 := 
(
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app ((app ((app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMAddOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMHaltOp) (0))) ((@nil tvm_inst))))) tail )
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_emit_prelude (policy) (p)))) tail )
) \/
(
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app ((app ((app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMAddOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMHaltOp) (0))) ((@nil tvm_inst))))) tail )
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_emit_prelude (policy) (p)))) tail )
).

Definition cmc_emit_prelude_return_wit_1_split_goal_spatial := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app ((app ((app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMAddOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMHaltOp) (0))) ((@nil tvm_inst))))) tail )
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cm_emit_prelude (policy) (p)))) tail )
.

Definition cmc_emit_prelude_partial_solve_wit_1_pure := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "main_id" ) )) # Int  |-> main_id)
  **  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) (1048576))) ((cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))))))))))))))))) )
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ”
.

Definition cmc_emit_prelude_partial_solve_wit_1_aux := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) (1048576))) ((cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))))))))))))))))) )
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ” 
  &&  “ (main_id = (cm_program_main (p))) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) = 0) ” 
  &&  “ ((tvm_opcode_code (TVMStoreOp)) = 5) ” 
  &&  “ ((tvm_opcode_code (TVMModOp)) = 12) ” 
  &&  “ ((tvm_opcode_code (TVMAddOp)) = 8) ” 
  &&  “ ((tvm_opcode_code (TVMHaltOp)) = 27) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) (1048576))) ((cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))))))))))))))))) )
  **  (cm_program_context_rep program_pre p functions_ptr )
.

Definition cmc_emit_prelude_partial_solve_wit_1 := cmc_emit_prelude_partial_solve_wit_1_pure -> cmc_emit_prelude_partial_solve_wit_1_aux.

Definition cmc_emit_prelude_partial_solve_wit_2_pure := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))))))))))))))) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "main_id" ) )) # Int  |-> main_id)
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ”
.

Definition cmc_emit_prelude_partial_solve_wit_2_aux := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))))))))))))))) )
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ” 
  &&  “ (main_id = (cm_program_main (p))) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) = 0) ” 
  &&  “ ((tvm_opcode_code (TVMStoreOp)) = 5) ” 
  &&  “ ((tvm_opcode_code (TVMModOp)) = 12) ” 
  &&  “ ((tvm_opcode_code (TVMAddOp)) = 8) ” 
  &&  “ ((tvm_opcode_code (TVMHaltOp)) = 27) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))))))))))))))) )
  **  (cm_program_context_rep program_pre p functions_ptr )
.

Definition cmc_emit_prelude_partial_solve_wit_2 := cmc_emit_prelude_partial_solve_wit_2_pure -> cmc_emit_prelude_partial_solve_wit_2_aux.

Definition cmc_emit_prelude_partial_solve_wit_3_pure := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))))))))))))) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "main_id" ) )) # Int  |-> main_id)
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (5 = (tvm_opcode_code (TVMStoreOp))) ” 
  &&  “ ((tvm_opcode_code (TVMStoreOp)) <> 22) ”
.

Definition cmc_emit_prelude_partial_solve_wit_3_aux := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))))))))))))) )
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (5 = (tvm_opcode_code (TVMStoreOp))) ” 
  &&  “ ((tvm_opcode_code (TVMStoreOp)) <> 22) ” 
  &&  “ (main_id = (cm_program_main (p))) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) = 0) ” 
  &&  “ ((tvm_opcode_code (TVMStoreOp)) = 5) ” 
  &&  “ ((tvm_opcode_code (TVMModOp)) = 12) ” 
  &&  “ ((tvm_opcode_code (TVMAddOp)) = 8) ” 
  &&  “ ((tvm_opcode_code (TVMHaltOp)) = 27) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))))))))))))) )
  **  (cm_program_context_rep program_pre p functions_ptr )
.

Definition cmc_emit_prelude_partial_solve_wit_3 := cmc_emit_prelude_partial_solve_wit_3_pure -> cmc_emit_prelude_partial_solve_wit_3_aux.

Definition cmc_emit_prelude_partial_solve_wit_4 := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))))))))))) )
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (main_id = (cm_program_main (p))) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) = 0) ” 
  &&  “ ((tvm_opcode_code (TVMStoreOp)) = 5) ” 
  &&  “ ((tvm_opcode_code (TVMModOp)) = 12) ” 
  &&  “ ((tvm_opcode_code (TVMAddOp)) = 8) ” 
  &&  “ ((tvm_opcode_code (TVMHaltOp)) = 27) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))))))))))) )
  **  (cm_program_context_rep program_pre p functions_ptr )
.

Definition cmc_emit_prelude_partial_solve_wit_5_pure := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))))))))) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "main_id" ) )) # Int  |-> main_id)
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ”
.

Definition cmc_emit_prelude_partial_solve_wit_5_aux := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))))))))) )
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ” 
  &&  “ (main_id = (cm_program_main (p))) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) = 0) ” 
  &&  “ ((tvm_opcode_code (TVMStoreOp)) = 5) ” 
  &&  “ ((tvm_opcode_code (TVMModOp)) = 12) ” 
  &&  “ ((tvm_opcode_code (TVMAddOp)) = 8) ” 
  &&  “ ((tvm_opcode_code (TVMHaltOp)) = 27) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))))))))) )
  **  (cm_program_context_rep program_pre p functions_ptr )
.

Definition cmc_emit_prelude_partial_solve_wit_5 := cmc_emit_prelude_partial_solve_wit_5_pure -> cmc_emit_prelude_partial_solve_wit_5_aux.

Definition cmc_emit_prelude_partial_solve_wit_6_pure := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))))))) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "main_id" ) )) # Int  |-> main_id)
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (12 = (tvm_opcode_code (TVMModOp))) ” 
  &&  “ ((tvm_opcode_code (TVMModOp)) <> 22) ”
.

Definition cmc_emit_prelude_partial_solve_wit_6_aux := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))))))) )
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (12 = (tvm_opcode_code (TVMModOp))) ” 
  &&  “ ((tvm_opcode_code (TVMModOp)) <> 22) ” 
  &&  “ (main_id = (cm_program_main (p))) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) = 0) ” 
  &&  “ ((tvm_opcode_code (TVMStoreOp)) = 5) ” 
  &&  “ ((tvm_opcode_code (TVMModOp)) = 12) ” 
  &&  “ ((tvm_opcode_code (TVMAddOp)) = 8) ” 
  &&  “ ((tvm_opcode_code (TVMHaltOp)) = 27) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))))))) )
  **  (cm_program_context_rep program_pre p functions_ptr )
.

Definition cmc_emit_prelude_partial_solve_wit_6 := cmc_emit_prelude_partial_solve_wit_6_pure -> cmc_emit_prelude_partial_solve_wit_6_aux.

Definition cmc_emit_prelude_partial_solve_wit_7_pure := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))))) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "main_id" ) )) # Int  |-> main_id)
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ”
.

Definition cmc_emit_prelude_partial_solve_wit_7_aux := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))))) )
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ” 
  &&  “ (main_id = (cm_program_main (p))) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) = 0) ” 
  &&  “ ((tvm_opcode_code (TVMStoreOp)) = 5) ” 
  &&  “ ((tvm_opcode_code (TVMModOp)) = 12) ” 
  &&  “ ((tvm_opcode_code (TVMAddOp)) = 8) ” 
  &&  “ ((tvm_opcode_code (TVMHaltOp)) = 27) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))))) )
  **  (cm_program_context_rep program_pre p functions_ptr )
.

Definition cmc_emit_prelude_partial_solve_wit_7 := cmc_emit_prelude_partial_solve_wit_7_pure -> cmc_emit_prelude_partial_solve_wit_7_aux.

Definition cmc_emit_prelude_partial_solve_wit_8_pure := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "main_id" ) )) # Int  |-> main_id)
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (8 = (tvm_opcode_code (TVMAddOp))) ” 
  &&  “ ((tvm_opcode_code (TVMAddOp)) <> 22) ”
.

Definition cmc_emit_prelude_partial_solve_wit_8_aux := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))) )
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (8 = (tvm_opcode_code (TVMAddOp))) ” 
  &&  “ ((tvm_opcode_code (TVMAddOp)) <> 22) ” 
  &&  “ (main_id = (cm_program_main (p))) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) = 0) ” 
  &&  “ ((tvm_opcode_code (TVMStoreOp)) = 5) ” 
  &&  “ ((tvm_opcode_code (TVMModOp)) = 12) ” 
  &&  “ ((tvm_opcode_code (TVMAddOp)) = 8) ” 
  &&  “ ((tvm_opcode_code (TVMHaltOp)) = 27) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMAddOp) (0))) ((cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))))) )
  **  (cm_program_context_rep program_pre p functions_ptr )
.

Definition cmc_emit_prelude_partial_solve_wit_8 := cmc_emit_prelude_partial_solve_wit_8_pure -> cmc_emit_prelude_partial_solve_wit_8_aux.

Definition cmc_emit_prelude_partial_solve_wit_9_pure := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMAddOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "main_id" ) )) # Int  |-> main_id)
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ”
.

Definition cmc_emit_prelude_partial_solve_wit_9_aux := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMAddOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))) )
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ” 
  &&  “ (main_id = (cm_program_main (p))) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) = 0) ” 
  &&  “ ((tvm_opcode_code (TVMStoreOp)) = 5) ” 
  &&  “ ((tvm_opcode_code (TVMModOp)) = 12) ” 
  &&  “ ((tvm_opcode_code (TVMAddOp)) = 8) ” 
  &&  “ ((tvm_opcode_code (TVMHaltOp)) = 27) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMAddOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (256))) ((cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))))) )
  **  (cm_program_context_rep program_pre p functions_ptr )
.

Definition cmc_emit_prelude_partial_solve_wit_9 := cmc_emit_prelude_partial_solve_wit_9_pure -> cmc_emit_prelude_partial_solve_wit_9_aux.

Definition cmc_emit_prelude_partial_solve_wit_10_pure := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMAddOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "main_id" ) )) # Int  |-> main_id)
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (12 = (tvm_opcode_code (TVMModOp))) ” 
  &&  “ ((tvm_opcode_code (TVMModOp)) <> 22) ”
.

Definition cmc_emit_prelude_partial_solve_wit_10_aux := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMAddOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))) )
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (12 = (tvm_opcode_code (TVMModOp))) ” 
  &&  “ ((tvm_opcode_code (TVMModOp)) <> 22) ” 
  &&  “ (main_id = (cm_program_main (p))) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) = 0) ” 
  &&  “ ((tvm_opcode_code (TVMStoreOp)) = 5) ” 
  &&  “ ((tvm_opcode_code (TVMModOp)) = 12) ” 
  &&  “ ((tvm_opcode_code (TVMAddOp)) = 8) ” 
  &&  “ ((tvm_opcode_code (TVMHaltOp)) = 27) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMAddOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMModOp) (0))) ((cons ((TVMInst (TVMHaltOp) (0))) (tail)))) )
  **  (cm_program_context_rep program_pre p functions_ptr )
.

Definition cmc_emit_prelude_partial_solve_wit_10 := cmc_emit_prelude_partial_solve_wit_10_pure -> cmc_emit_prelude_partial_solve_wit_10_aux.

Definition cmc_emit_prelude_partial_solve_wit_11_pure := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app ((app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMAddOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMHaltOp) (0))) (tail)) )
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  ((( &( "main_id" ) )) # Int  |-> main_id)
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (27 = (tvm_opcode_code (TVMHaltOp))) ” 
  &&  “ ((tvm_opcode_code (TVMHaltOp)) <> 22) ”
.

Definition cmc_emit_prelude_partial_solve_wit_11_aux := 
forall (emitter_pre: Z) (program_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (functions_ptr: Z) (p: cm_program) (policy: cm_lookup_policy) (main_id: Z) (PreH1 : (main_id = (cm_program_main (p)))) (PreH2 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH3 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH4 : ((tvm_opcode_code (TVMModOp)) = 12)) (PreH5 : ((tvm_opcode_code (TVMAddOp)) = 8)) (PreH6 : ((tvm_opcode_code (TVMHaltOp)) = 27)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app ((app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMAddOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMHaltOp) (0))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
|--
  “ (27 = (tvm_opcode_code (TVMHaltOp))) ” 
  &&  “ ((tvm_opcode_code (TVMHaltOp)) <> 22) ” 
  &&  “ (main_id = (cm_program_main (p))) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) = 0) ” 
  &&  “ ((tvm_opcode_code (TVMStoreOp)) = 5) ” 
  &&  “ ((tvm_opcode_code (TVMModOp)) = 12) ” 
  &&  “ ((tvm_opcode_code (TVMAddOp)) = 8) ” 
  &&  “ ((tvm_opcode_code (TVMHaltOp)) = 27) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app ((app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (1048576))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMCallOp) ((cm_function_pc (policy) (p) (main_id))))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMAddOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (256))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMModOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMHaltOp) (0))) (tail)) )
  **  (cm_program_context_rep program_pre p functions_ptr )
.

Definition cmc_emit_prelude_partial_solve_wit_11 := cmc_emit_prelude_partial_solve_wit_11_pure -> cmc_emit_prelude_partial_solve_wit_11_aux.

Module Type VC_Correct.


Axiom proof_of_cmc_emit_prelude_safety_wit_1 : cmc_emit_prelude_safety_wit_1.
Axiom proof_of_cmc_emit_prelude_safety_wit_2 : cmc_emit_prelude_safety_wit_2.
Axiom proof_of_cmc_emit_prelude_safety_wit_3 : cmc_emit_prelude_safety_wit_3.
Axiom proof_of_cmc_emit_prelude_safety_wit_4 : cmc_emit_prelude_safety_wit_4.
Axiom proof_of_cmc_emit_prelude_safety_wit_5 : cmc_emit_prelude_safety_wit_5.
Axiom proof_of_cmc_emit_prelude_safety_wit_6 : cmc_emit_prelude_safety_wit_6.
Axiom proof_of_cmc_emit_prelude_safety_wit_7 : cmc_emit_prelude_safety_wit_7.
Axiom proof_of_cmc_emit_prelude_safety_wit_8 : cmc_emit_prelude_safety_wit_8.
Axiom proof_of_cmc_emit_prelude_safety_wit_9 : cmc_emit_prelude_safety_wit_9.
Axiom proof_of_cmc_emit_prelude_safety_wit_10 : cmc_emit_prelude_safety_wit_10.
Axiom proof_of_cmc_emit_prelude_safety_wit_11 : cmc_emit_prelude_safety_wit_11.
Axiom proof_of_cmc_emit_prelude_safety_wit_12 : cmc_emit_prelude_safety_wit_12.
Axiom proof_of_cmc_emit_prelude_safety_wit_13 : cmc_emit_prelude_safety_wit_13.
Axiom proof_of_cmc_emit_prelude_safety_wit_14 : cmc_emit_prelude_safety_wit_14.
Axiom proof_of_cmc_emit_prelude_safety_wit_15 : cmc_emit_prelude_safety_wit_15.
Axiom proof_of_cmc_emit_prelude_safety_wit_16 : cmc_emit_prelude_safety_wit_16.
Axiom proof_of_cmc_emit_prelude_safety_wit_17 : cmc_emit_prelude_safety_wit_17.
Axiom proof_of_cmc_emit_prelude_safety_wit_18 : cmc_emit_prelude_safety_wit_18.
Axiom proof_of_cmc_emit_prelude_safety_wit_19 : cmc_emit_prelude_safety_wit_19.
Axiom proof_of_cmc_emit_prelude_safety_wit_20 : cmc_emit_prelude_safety_wit_20.
Axiom proof_of_cmc_emit_prelude_entail_wit_1 : cmc_emit_prelude_entail_wit_1.
Axiom proof_of_cmc_emit_prelude_entail_wit_2 : cmc_emit_prelude_entail_wit_2.
Axiom proof_of_cmc_emit_prelude_return_wit_1 : cmc_emit_prelude_return_wit_1.
Axiom proof_of_cmc_emit_prelude_partial_solve_wit_1_pure : cmc_emit_prelude_partial_solve_wit_1_pure.
Axiom proof_of_cmc_emit_prelude_partial_solve_wit_1 : cmc_emit_prelude_partial_solve_wit_1.
Axiom proof_of_cmc_emit_prelude_partial_solve_wit_2_pure : cmc_emit_prelude_partial_solve_wit_2_pure.
Axiom proof_of_cmc_emit_prelude_partial_solve_wit_2 : cmc_emit_prelude_partial_solve_wit_2.
Axiom proof_of_cmc_emit_prelude_partial_solve_wit_3_pure : cmc_emit_prelude_partial_solve_wit_3_pure.
Axiom proof_of_cmc_emit_prelude_partial_solve_wit_3 : cmc_emit_prelude_partial_solve_wit_3.
Axiom proof_of_cmc_emit_prelude_partial_solve_wit_4 : cmc_emit_prelude_partial_solve_wit_4.
Axiom proof_of_cmc_emit_prelude_partial_solve_wit_5_pure : cmc_emit_prelude_partial_solve_wit_5_pure.
Axiom proof_of_cmc_emit_prelude_partial_solve_wit_5 : cmc_emit_prelude_partial_solve_wit_5.
Axiom proof_of_cmc_emit_prelude_partial_solve_wit_6_pure : cmc_emit_prelude_partial_solve_wit_6_pure.
Axiom proof_of_cmc_emit_prelude_partial_solve_wit_6 : cmc_emit_prelude_partial_solve_wit_6.
Axiom proof_of_cmc_emit_prelude_partial_solve_wit_7_pure : cmc_emit_prelude_partial_solve_wit_7_pure.
Axiom proof_of_cmc_emit_prelude_partial_solve_wit_7 : cmc_emit_prelude_partial_solve_wit_7.
Axiom proof_of_cmc_emit_prelude_partial_solve_wit_8_pure : cmc_emit_prelude_partial_solve_wit_8_pure.
Axiom proof_of_cmc_emit_prelude_partial_solve_wit_8 : cmc_emit_prelude_partial_solve_wit_8.
Axiom proof_of_cmc_emit_prelude_partial_solve_wit_9_pure : cmc_emit_prelude_partial_solve_wit_9_pure.
Axiom proof_of_cmc_emit_prelude_partial_solve_wit_9 : cmc_emit_prelude_partial_solve_wit_9.
Axiom proof_of_cmc_emit_prelude_partial_solve_wit_10_pure : cmc_emit_prelude_partial_solve_wit_10_pure.
Axiom proof_of_cmc_emit_prelude_partial_solve_wit_10 : cmc_emit_prelude_partial_solve_wit_10.
Axiom proof_of_cmc_emit_prelude_partial_solve_wit_11_pure : cmc_emit_prelude_partial_solve_wit_11_pure.
Axiom proof_of_cmc_emit_prelude_partial_solve_wit_11 : cmc_emit_prelude_partial_solve_wit_11.

End VC_Correct.
