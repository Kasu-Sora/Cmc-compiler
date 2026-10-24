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
Require Import SimpleC.EE.QCP_demos_human.cmc_emit_return_migration_lib.
Local Open Scope sac.

(*----- Function cm_emit_return_epilogue_plan -----*)

Definition cm_emit_return_epilogue_plan_safety_wit_1 := 
forall (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH2 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH3 : ((tvm_opcode_code (TVMLoadOp)) = 4)) (PreH4 : ((tvm_opcode_code (TVMLoadOp)) <> 22)) (PreH5 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH6 : ((tvm_opcode_code (TVMStoreOp)) <> 22)) (PreH7 : ((tvm_opcode_code (TVMRetOp)) = 23)) (PreH8 : ((tvm_opcode_code (TVMRetOp)) <> 22)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMRetOp) (0))) (tail)))))))))))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_emit_return_epilogue_plan_safety_wit_2 := 
forall (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH2 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH3 : ((tvm_opcode_code (TVMLoadOp)) = 4)) (PreH4 : ((tvm_opcode_code (TVMLoadOp)) <> 22)) (PreH5 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH6 : ((tvm_opcode_code (TVMStoreOp)) <> 22)) (PreH7 : ((tvm_opcode_code (TVMRetOp)) = 23)) (PreH8 : ((tvm_opcode_code (TVMRetOp)) <> 22)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMRetOp) (0))) (tail)))))))))))) )
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition cm_emit_return_epilogue_plan_safety_wit_3 := 
forall (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH2 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH3 : ((tvm_opcode_code (TVMLoadOp)) = 4)) (PreH4 : ((tvm_opcode_code (TVMLoadOp)) <> 22)) (PreH5 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH6 : ((tvm_opcode_code (TVMStoreOp)) <> 22)) (PreH7 : ((tvm_opcode_code (TVMRetOp)) = 23)) (PreH8 : ((tvm_opcode_code (TVMRetOp)) <> 22)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMRetOp) (0))) (tail)))))))))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition cm_emit_return_epilogue_plan_safety_wit_4 := 
forall (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH2 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH3 : ((tvm_opcode_code (TVMLoadOp)) = 4)) (PreH4 : ((tvm_opcode_code (TVMLoadOp)) <> 22)) (PreH5 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH6 : ((tvm_opcode_code (TVMStoreOp)) <> 22)) (PreH7 : ((tvm_opcode_code (TVMRetOp)) = 23)) (PreH8 : ((tvm_opcode_code (TVMRetOp)) <> 22)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMRetOp) (0))) (tail)))))))))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_emit_return_epilogue_plan_safety_wit_5 := 
forall (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH2 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH3 : ((tvm_opcode_code (TVMLoadOp)) = 4)) (PreH4 : ((tvm_opcode_code (TVMLoadOp)) <> 22)) (PreH5 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH6 : ((tvm_opcode_code (TVMStoreOp)) <> 22)) (PreH7 : ((tvm_opcode_code (TVMRetOp)) = 23)) (PreH8 : ((tvm_opcode_code (TVMRetOp)) <> 22)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMRetOp) (0))) (tail)))))))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition cm_emit_return_epilogue_plan_safety_wit_6 := 
forall (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH2 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH3 : ((tvm_opcode_code (TVMLoadOp)) = 4)) (PreH4 : ((tvm_opcode_code (TVMLoadOp)) <> 22)) (PreH5 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH6 : ((tvm_opcode_code (TVMStoreOp)) <> 22)) (PreH7 : ((tvm_opcode_code (TVMRetOp)) = 23)) (PreH8 : ((tvm_opcode_code (TVMRetOp)) <> 22)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMRetOp) (0))) (tail)))))))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_emit_return_epilogue_plan_safety_wit_7 := 
forall (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH2 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH3 : ((tvm_opcode_code (TVMLoadOp)) = 4)) (PreH4 : ((tvm_opcode_code (TVMLoadOp)) <> 22)) (PreH5 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH6 : ((tvm_opcode_code (TVMStoreOp)) <> 22)) (PreH7 : ((tvm_opcode_code (TVMRetOp)) = 23)) (PreH8 : ((tvm_opcode_code (TVMRetOp)) <> 22)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMRetOp) (0))) (tail)))))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_emit_return_epilogue_plan_safety_wit_8 := 
forall (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH2 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH3 : ((tvm_opcode_code (TVMLoadOp)) = 4)) (PreH4 : ((tvm_opcode_code (TVMLoadOp)) <> 22)) (PreH5 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH6 : ((tvm_opcode_code (TVMStoreOp)) <> 22)) (PreH7 : ((tvm_opcode_code (TVMRetOp)) = 23)) (PreH8 : ((tvm_opcode_code (TVMRetOp)) <> 22)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMRetOp) (0))) (tail)))))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition cm_emit_return_epilogue_plan_safety_wit_9 := 
forall (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH2 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH3 : ((tvm_opcode_code (TVMLoadOp)) = 4)) (PreH4 : ((tvm_opcode_code (TVMLoadOp)) <> 22)) (PreH5 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH6 : ((tvm_opcode_code (TVMStoreOp)) <> 22)) (PreH7 : ((tvm_opcode_code (TVMRetOp)) = 23)) (PreH8 : ((tvm_opcode_code (TVMRetOp)) <> 22)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMRetOp) (0))) (tail)))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
|--
  “ (5 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 5) ”
.

Definition cm_emit_return_epilogue_plan_safety_wit_10 := 
forall (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH2 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH3 : ((tvm_opcode_code (TVMLoadOp)) = 4)) (PreH4 : ((tvm_opcode_code (TVMLoadOp)) <> 22)) (PreH5 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH6 : ((tvm_opcode_code (TVMStoreOp)) <> 22)) (PreH7 : ((tvm_opcode_code (TVMRetOp)) = 23)) (PreH8 : ((tvm_opcode_code (TVMRetOp)) <> 22)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMRetOp) (0))) (tail)))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_emit_return_epilogue_plan_safety_wit_11 := 
forall (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH2 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH3 : ((tvm_opcode_code (TVMLoadOp)) = 4)) (PreH4 : ((tvm_opcode_code (TVMLoadOp)) <> 22)) (PreH5 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH6 : ((tvm_opcode_code (TVMStoreOp)) <> 22)) (PreH7 : ((tvm_opcode_code (TVMRetOp)) = 23)) (PreH8 : ((tvm_opcode_code (TVMRetOp)) <> 22)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMRetOp) (0))) (tail)) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
|--
  “ (23 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 23) ”
.

Definition cm_emit_return_epilogue_plan_safety_wit_12 := 
forall (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH2 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH3 : ((tvm_opcode_code (TVMLoadOp)) = 4)) (PreH4 : ((tvm_opcode_code (TVMLoadOp)) <> 22)) (PreH5 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH6 : ((tvm_opcode_code (TVMStoreOp)) <> 22)) (PreH7 : ((tvm_opcode_code (TVMRetOp)) = 23)) (PreH8 : ((tvm_opcode_code (TVMRetOp)) <> 22)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMRetOp) (0))) (tail)) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_emit_return_epilogue_plan_entail_wit_1 := 
(
forall (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app (cm_return_epilogue) (tail)) )
|--
  “ ((tvm_opcode_code (TVMPushOp)) = 0) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ” 
  &&  “ ((tvm_opcode_code (TVMLoadOp)) = 4) ” 
  &&  “ ((tvm_opcode_code (TVMLoadOp)) <> 22) ” 
  &&  “ ((tvm_opcode_code (TVMStoreOp)) = 5) ” 
  &&  “ ((tvm_opcode_code (TVMStoreOp)) <> 22) ” 
  &&  “ ((tvm_opcode_code (TVMRetOp)) = 23) ” 
  &&  “ ((tvm_opcode_code (TVMRetOp)) <> 22) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMRetOp) (0))) (tail)))))))))))) )
) \/
(
forall (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app (cm_return_epilogue) (tail)) )
|--
  “ ((tvm_opcode_code (TVMRetOp)) <> 22) ” 
  &&  “ ((tvm_opcode_code (TVMRetOp)) = 23) ” 
  &&  “ ((tvm_opcode_code (TVMStoreOp)) <> 22) ” 
  &&  “ ((tvm_opcode_code (TVMStoreOp)) = 5) ” 
  &&  “ ((tvm_opcode_code (TVMLoadOp)) <> 22) ” 
  &&  “ ((tvm_opcode_code (TVMLoadOp)) = 4) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) = 0) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMRetOp) (0))) (tail)))))))))))) )
).

Definition cm_emit_return_epilogue_plan_entail_wit_1_split_goal_1 := 
forall (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app (cm_return_epilogue) (tail)) )
|--
  “ ((tvm_opcode_code (TVMRetOp)) <> 22) ”
.

Definition cm_emit_return_epilogue_plan_entail_wit_1_split_goal_2 := 
forall (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app (cm_return_epilogue) (tail)) )
|--
  “ ((tvm_opcode_code (TVMRetOp)) = 23) ”
.

Definition cm_emit_return_epilogue_plan_entail_wit_1_split_goal_3 := 
forall (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app (cm_return_epilogue) (tail)) )
|--
  “ ((tvm_opcode_code (TVMStoreOp)) <> 22) ”
.

Definition cm_emit_return_epilogue_plan_entail_wit_1_split_goal_4 := 
forall (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app (cm_return_epilogue) (tail)) )
|--
  “ ((tvm_opcode_code (TVMStoreOp)) = 5) ”
.

Definition cm_emit_return_epilogue_plan_entail_wit_1_split_goal_5 := 
forall (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app (cm_return_epilogue) (tail)) )
|--
  “ ((tvm_opcode_code (TVMLoadOp)) <> 22) ”
.

Definition cm_emit_return_epilogue_plan_entail_wit_1_split_goal_6 := 
forall (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app (cm_return_epilogue) (tail)) )
|--
  “ ((tvm_opcode_code (TVMLoadOp)) = 4) ”
.

Definition cm_emit_return_epilogue_plan_entail_wit_1_split_goal_7 := 
forall (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app (cm_return_epilogue) (tail)) )
|--
  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ”
.

Definition cm_emit_return_epilogue_plan_entail_wit_1_split_goal_8 := 
forall (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app (cm_return_epilogue) (tail)) )
|--
  “ ((tvm_opcode_code (TVMPushOp)) = 0) ”
.

Definition cm_emit_return_epilogue_plan_entail_wit_1_split_goal_spatial := 
forall (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (app (cm_return_epilogue) (tail)) )
|--
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMRetOp) (0))) (tail)))))))))))) )
.

Definition cm_emit_return_epilogue_plan_return_wit_1 := 
(
forall (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH2 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH3 : ((tvm_opcode_code (TVMLoadOp)) = 4)) (PreH4 : ((tvm_opcode_code (TVMLoadOp)) <> 22)) (PreH5 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH6 : ((tvm_opcode_code (TVMStoreOp)) <> 22)) (PreH7 : ((tvm_opcode_code (TVMRetOp)) = 23)) (PreH8 : ((tvm_opcode_code (TVMRetOp)) <> 22)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMRetOp) (0))) ((@nil tvm_inst))))) tail )
|--
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) (cm_return_epilogue)) tail )
) \/
(
forall (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH2 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH3 : ((tvm_opcode_code (TVMLoadOp)) = 4)) (PreH4 : ((tvm_opcode_code (TVMLoadOp)) <> 22)) (PreH5 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH6 : ((tvm_opcode_code (TVMStoreOp)) <> 22)) (PreH7 : ((tvm_opcode_code (TVMRetOp)) = 23)) (PreH8 : ((tvm_opcode_code (TVMRetOp)) <> 22)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMRetOp) (0))) ((@nil tvm_inst))))) tail )
|--
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) (cm_return_epilogue)) tail )
).

Definition cm_emit_return_epilogue_plan_return_wit_1_split_goal_spatial := 
forall (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH2 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH3 : ((tvm_opcode_code (TVMLoadOp)) = 4)) (PreH4 : ((tvm_opcode_code (TVMLoadOp)) <> 22)) (PreH5 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH6 : ((tvm_opcode_code (TVMStoreOp)) <> 22)) (PreH7 : ((tvm_opcode_code (TVMRetOp)) = 23)) (PreH8 : ((tvm_opcode_code (TVMRetOp)) <> 22)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMRetOp) (0))) ((@nil tvm_inst))))) tail )
|--
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) (cm_return_epilogue)) tail )
.

Definition cm_emit_return_epilogue_plan_partial_solve_wit_1_pure := 
forall (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH2 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH3 : ((tvm_opcode_code (TVMLoadOp)) = 4)) (PreH4 : ((tvm_opcode_code (TVMLoadOp)) <> 22)) (PreH5 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH6 : ((tvm_opcode_code (TVMStoreOp)) <> 22)) (PreH7 : ((tvm_opcode_code (TVMRetOp)) = 23)) (PreH8 : ((tvm_opcode_code (TVMRetOp)) <> 22)) ,
  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
  **  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMRetOp) (0))) (tail)))))))))))) )
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ”
.

Definition cm_emit_return_epilogue_plan_partial_solve_wit_1_aux := 
forall (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH2 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH3 : ((tvm_opcode_code (TVMLoadOp)) = 4)) (PreH4 : ((tvm_opcode_code (TVMLoadOp)) <> 22)) (PreH5 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH6 : ((tvm_opcode_code (TVMStoreOp)) <> 22)) (PreH7 : ((tvm_opcode_code (TVMRetOp)) = 23)) (PreH8 : ((tvm_opcode_code (TVMRetOp)) <> 22)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMRetOp) (0))) (tail)))))))))))) )
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) = 0) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ” 
  &&  “ ((tvm_opcode_code (TVMLoadOp)) = 4) ” 
  &&  “ ((tvm_opcode_code (TVMLoadOp)) <> 22) ” 
  &&  “ ((tvm_opcode_code (TVMStoreOp)) = 5) ” 
  &&  “ ((tvm_opcode_code (TVMStoreOp)) <> 22) ” 
  &&  “ ((tvm_opcode_code (TVMRetOp)) = 23) ” 
  &&  “ ((tvm_opcode_code (TVMRetOp)) <> 22) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity done (cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMRetOp) (0))) (tail)))))))))))) )
.

Definition cm_emit_return_epilogue_plan_partial_solve_wit_1 := cm_emit_return_epilogue_plan_partial_solve_wit_1_pure -> cm_emit_return_epilogue_plan_partial_solve_wit_1_aux.

Definition cm_emit_return_epilogue_plan_partial_solve_wit_2_pure := 
forall (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH2 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH3 : ((tvm_opcode_code (TVMLoadOp)) = 4)) (PreH4 : ((tvm_opcode_code (TVMLoadOp)) <> 22)) (PreH5 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH6 : ((tvm_opcode_code (TVMStoreOp)) <> 22)) (PreH7 : ((tvm_opcode_code (TVMRetOp)) = 23)) (PreH8 : ((tvm_opcode_code (TVMRetOp)) <> 22)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMRetOp) (0))) (tail)))))))))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
|--
  “ (4 = (tvm_opcode_code (TVMLoadOp))) ” 
  &&  “ ((tvm_opcode_code (TVMLoadOp)) <> 22) ”
.

Definition cm_emit_return_epilogue_plan_partial_solve_wit_2_aux := 
forall (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH2 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH3 : ((tvm_opcode_code (TVMLoadOp)) = 4)) (PreH4 : ((tvm_opcode_code (TVMLoadOp)) <> 22)) (PreH5 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH6 : ((tvm_opcode_code (TVMStoreOp)) <> 22)) (PreH7 : ((tvm_opcode_code (TVMRetOp)) = 23)) (PreH8 : ((tvm_opcode_code (TVMRetOp)) <> 22)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMRetOp) (0))) (tail)))))))))) )
|--
  “ (4 = (tvm_opcode_code (TVMLoadOp))) ” 
  &&  “ ((tvm_opcode_code (TVMLoadOp)) <> 22) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) = 0) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ” 
  &&  “ ((tvm_opcode_code (TVMLoadOp)) = 4) ” 
  &&  “ ((tvm_opcode_code (TVMLoadOp)) <> 22) ” 
  &&  “ ((tvm_opcode_code (TVMStoreOp)) = 5) ” 
  &&  “ ((tvm_opcode_code (TVMStoreOp)) <> 22) ” 
  &&  “ ((tvm_opcode_code (TVMRetOp)) = 23) ” 
  &&  “ ((tvm_opcode_code (TVMRetOp)) <> 22) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMRetOp) (0))) (tail)))))))))) )
.

Definition cm_emit_return_epilogue_plan_partial_solve_wit_2 := cm_emit_return_epilogue_plan_partial_solve_wit_2_pure -> cm_emit_return_epilogue_plan_partial_solve_wit_2_aux.

Definition cm_emit_return_epilogue_plan_partial_solve_wit_3_pure := 
forall (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH2 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH3 : ((tvm_opcode_code (TVMLoadOp)) = 4)) (PreH4 : ((tvm_opcode_code (TVMLoadOp)) <> 22)) (PreH5 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH6 : ((tvm_opcode_code (TVMStoreOp)) <> 22)) (PreH7 : ((tvm_opcode_code (TVMRetOp)) = 23)) (PreH8 : ((tvm_opcode_code (TVMRetOp)) <> 22)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMRetOp) (0))) (tail)))))))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
|--
  “ (4 = (tvm_opcode_code (TVMLoadOp))) ” 
  &&  “ ((tvm_opcode_code (TVMLoadOp)) <> 22) ”
.

Definition cm_emit_return_epilogue_plan_partial_solve_wit_3_aux := 
forall (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH2 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH3 : ((tvm_opcode_code (TVMLoadOp)) = 4)) (PreH4 : ((tvm_opcode_code (TVMLoadOp)) <> 22)) (PreH5 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH6 : ((tvm_opcode_code (TVMStoreOp)) <> 22)) (PreH7 : ((tvm_opcode_code (TVMRetOp)) = 23)) (PreH8 : ((tvm_opcode_code (TVMRetOp)) <> 22)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMRetOp) (0))) (tail)))))))) )
|--
  “ (4 = (tvm_opcode_code (TVMLoadOp))) ” 
  &&  “ ((tvm_opcode_code (TVMLoadOp)) <> 22) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) = 0) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ” 
  &&  “ ((tvm_opcode_code (TVMLoadOp)) = 4) ” 
  &&  “ ((tvm_opcode_code (TVMLoadOp)) <> 22) ” 
  &&  “ ((tvm_opcode_code (TVMStoreOp)) = 5) ” 
  &&  “ ((tvm_opcode_code (TVMStoreOp)) <> 22) ” 
  &&  “ ((tvm_opcode_code (TVMRetOp)) = 23) ” 
  &&  “ ((tvm_opcode_code (TVMRetOp)) <> 22) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMLoadOp) (0))) ((cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMRetOp) (0))) (tail)))))))) )
.

Definition cm_emit_return_epilogue_plan_partial_solve_wit_3 := cm_emit_return_epilogue_plan_partial_solve_wit_3_pure -> cm_emit_return_epilogue_plan_partial_solve_wit_3_aux.

Definition cm_emit_return_epilogue_plan_partial_solve_wit_4_pure := 
forall (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH2 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH3 : ((tvm_opcode_code (TVMLoadOp)) = 4)) (PreH4 : ((tvm_opcode_code (TVMLoadOp)) <> 22)) (PreH5 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH6 : ((tvm_opcode_code (TVMStoreOp)) <> 22)) (PreH7 : ((tvm_opcode_code (TVMRetOp)) = 23)) (PreH8 : ((tvm_opcode_code (TVMRetOp)) <> 22)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMRetOp) (0))) (tail)))))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ”
.

Definition cm_emit_return_epilogue_plan_partial_solve_wit_4_aux := 
forall (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH2 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH3 : ((tvm_opcode_code (TVMLoadOp)) = 4)) (PreH4 : ((tvm_opcode_code (TVMLoadOp)) <> 22)) (PreH5 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH6 : ((tvm_opcode_code (TVMStoreOp)) <> 22)) (PreH7 : ((tvm_opcode_code (TVMRetOp)) = 23)) (PreH8 : ((tvm_opcode_code (TVMRetOp)) <> 22)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMRetOp) (0))) (tail)))))) )
|--
  “ (0 = (tvm_opcode_code (TVMPushOp))) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) = 0) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ” 
  &&  “ ((tvm_opcode_code (TVMLoadOp)) = 4) ” 
  &&  “ ((tvm_opcode_code (TVMLoadOp)) <> 22) ” 
  &&  “ ((tvm_opcode_code (TVMStoreOp)) = 5) ” 
  &&  “ ((tvm_opcode_code (TVMStoreOp)) <> 22) ” 
  &&  “ ((tvm_opcode_code (TVMRetOp)) = 23) ” 
  &&  “ ((tvm_opcode_code (TVMRetOp)) <> 22) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMPushOp) (8))) ((cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMRetOp) (0))) (tail)))))) )
.

Definition cm_emit_return_epilogue_plan_partial_solve_wit_4 := cm_emit_return_epilogue_plan_partial_solve_wit_4_pure -> cm_emit_return_epilogue_plan_partial_solve_wit_4_aux.

Definition cm_emit_return_epilogue_plan_partial_solve_wit_5_pure := 
forall (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH2 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH3 : ((tvm_opcode_code (TVMLoadOp)) = 4)) (PreH4 : ((tvm_opcode_code (TVMLoadOp)) <> 22)) (PreH5 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH6 : ((tvm_opcode_code (TVMStoreOp)) <> 22)) (PreH7 : ((tvm_opcode_code (TVMRetOp)) = 23)) (PreH8 : ((tvm_opcode_code (TVMRetOp)) <> 22)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMRetOp) (0))) (tail)))) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
|--
  “ (5 = (tvm_opcode_code (TVMStoreOp))) ” 
  &&  “ ((tvm_opcode_code (TVMStoreOp)) <> 22) ”
.

Definition cm_emit_return_epilogue_plan_partial_solve_wit_5_aux := 
forall (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH2 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH3 : ((tvm_opcode_code (TVMLoadOp)) = 4)) (PreH4 : ((tvm_opcode_code (TVMLoadOp)) <> 22)) (PreH5 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH6 : ((tvm_opcode_code (TVMStoreOp)) <> 22)) (PreH7 : ((tvm_opcode_code (TVMRetOp)) = 23)) (PreH8 : ((tvm_opcode_code (TVMRetOp)) <> 22)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMRetOp) (0))) (tail)))) )
|--
  “ (5 = (tvm_opcode_code (TVMStoreOp))) ” 
  &&  “ ((tvm_opcode_code (TVMStoreOp)) <> 22) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) = 0) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ” 
  &&  “ ((tvm_opcode_code (TVMLoadOp)) = 4) ” 
  &&  “ ((tvm_opcode_code (TVMLoadOp)) <> 22) ” 
  &&  “ ((tvm_opcode_code (TVMStoreOp)) = 5) ” 
  &&  “ ((tvm_opcode_code (TVMStoreOp)) <> 22) ” 
  &&  “ ((tvm_opcode_code (TVMRetOp)) = 23) ” 
  &&  “ ((tvm_opcode_code (TVMRetOp)) <> 22) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMStoreOp) (0))) ((cons ((TVMInst (TVMRetOp) (0))) (tail)))) )
.

Definition cm_emit_return_epilogue_plan_partial_solve_wit_5 := cm_emit_return_epilogue_plan_partial_solve_wit_5_pure -> cm_emit_return_epilogue_plan_partial_solve_wit_5_aux.

Definition cm_emit_return_epilogue_plan_partial_solve_wit_6_pure := 
forall (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH2 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH3 : ((tvm_opcode_code (TVMLoadOp)) = 4)) (PreH4 : ((tvm_opcode_code (TVMLoadOp)) <> 22)) (PreH5 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH6 : ((tvm_opcode_code (TVMStoreOp)) <> 22)) (PreH7 : ((tvm_opcode_code (TVMRetOp)) = 23)) (PreH8 : ((tvm_opcode_code (TVMRetOp)) <> 22)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMRetOp) (0))) (tail)) )
  **  ((( &( "emitter" ) )) # Ptr  |-> emitter_pre)
|--
  “ (23 = (tvm_opcode_code (TVMRetOp))) ” 
  &&  “ ((tvm_opcode_code (TVMRetOp)) <> 22) ”
.

Definition cm_emit_return_epilogue_plan_partial_solve_wit_6_aux := 
forall (emitter_pre: Z) (capacity: Z) (out: Z) (tail: (@list tvm_inst)) (done: (@list tvm_inst)) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : ((tvm_opcode_code (TVMPushOp)) = 0)) (PreH2 : ((tvm_opcode_code (TVMPushOp)) <> 22)) (PreH3 : ((tvm_opcode_code (TVMLoadOp)) = 4)) (PreH4 : ((tvm_opcode_code (TVMLoadOp)) <> 22)) (PreH5 : ((tvm_opcode_code (TVMStoreOp)) = 5)) (PreH6 : ((tvm_opcode_code (TVMStoreOp)) <> 22)) (PreH7 : ((tvm_opcode_code (TVMRetOp)) = 23)) (PreH8 : ((tvm_opcode_code (TVMRetOp)) <> 22)) ,
  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMRetOp) (0))) (tail)) )
|--
  “ (23 = (tvm_opcode_code (TVMRetOp))) ” 
  &&  “ ((tvm_opcode_code (TVMRetOp)) <> 22) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) = 0) ” 
  &&  “ ((tvm_opcode_code (TVMPushOp)) <> 22) ” 
  &&  “ ((tvm_opcode_code (TVMLoadOp)) = 4) ” 
  &&  “ ((tvm_opcode_code (TVMLoadOp)) <> 22) ” 
  &&  “ ((tvm_opcode_code (TVMStoreOp)) = 5) ” 
  &&  “ ((tvm_opcode_code (TVMStoreOp)) <> 22) ” 
  &&  “ ((tvm_opcode_code (TVMRetOp)) = 23) ” 
  &&  “ ((tvm_opcode_code (TVMRetOp)) <> 22) ”
  &&  (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity (app ((app ((app ((app ((app (done) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMLoadOp) (0))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMPushOp) (8))) ((@nil tvm_inst)))))) ((cons ((TVMInst (TVMStoreOp) (0))) ((@nil tvm_inst))))) (cons ((TVMInst (TVMRetOp) (0))) (tail)) )
.

Definition cm_emit_return_epilogue_plan_partial_solve_wit_6 := cm_emit_return_epilogue_plan_partial_solve_wit_6_pure -> cm_emit_return_epilogue_plan_partial_solve_wit_6_aux.

Module Type VC_Correct.


Axiom proof_of_cm_emit_return_epilogue_plan_safety_wit_1 : cm_emit_return_epilogue_plan_safety_wit_1.
Axiom proof_of_cm_emit_return_epilogue_plan_safety_wit_2 : cm_emit_return_epilogue_plan_safety_wit_2.
Axiom proof_of_cm_emit_return_epilogue_plan_safety_wit_3 : cm_emit_return_epilogue_plan_safety_wit_3.
Axiom proof_of_cm_emit_return_epilogue_plan_safety_wit_4 : cm_emit_return_epilogue_plan_safety_wit_4.
Axiom proof_of_cm_emit_return_epilogue_plan_safety_wit_5 : cm_emit_return_epilogue_plan_safety_wit_5.
Axiom proof_of_cm_emit_return_epilogue_plan_safety_wit_6 : cm_emit_return_epilogue_plan_safety_wit_6.
Axiom proof_of_cm_emit_return_epilogue_plan_safety_wit_7 : cm_emit_return_epilogue_plan_safety_wit_7.
Axiom proof_of_cm_emit_return_epilogue_plan_safety_wit_8 : cm_emit_return_epilogue_plan_safety_wit_8.
Axiom proof_of_cm_emit_return_epilogue_plan_safety_wit_9 : cm_emit_return_epilogue_plan_safety_wit_9.
Axiom proof_of_cm_emit_return_epilogue_plan_safety_wit_10 : cm_emit_return_epilogue_plan_safety_wit_10.
Axiom proof_of_cm_emit_return_epilogue_plan_safety_wit_11 : cm_emit_return_epilogue_plan_safety_wit_11.
Axiom proof_of_cm_emit_return_epilogue_plan_safety_wit_12 : cm_emit_return_epilogue_plan_safety_wit_12.
Axiom proof_of_cm_emit_return_epilogue_plan_entail_wit_1 : cm_emit_return_epilogue_plan_entail_wit_1.
Axiom proof_of_cm_emit_return_epilogue_plan_return_wit_1 : cm_emit_return_epilogue_plan_return_wit_1.
Axiom proof_of_cm_emit_return_epilogue_plan_partial_solve_wit_1_pure : cm_emit_return_epilogue_plan_partial_solve_wit_1_pure.
Axiom proof_of_cm_emit_return_epilogue_plan_partial_solve_wit_1 : cm_emit_return_epilogue_plan_partial_solve_wit_1.
Axiom proof_of_cm_emit_return_epilogue_plan_partial_solve_wit_2_pure : cm_emit_return_epilogue_plan_partial_solve_wit_2_pure.
Axiom proof_of_cm_emit_return_epilogue_plan_partial_solve_wit_2 : cm_emit_return_epilogue_plan_partial_solve_wit_2.
Axiom proof_of_cm_emit_return_epilogue_plan_partial_solve_wit_3_pure : cm_emit_return_epilogue_plan_partial_solve_wit_3_pure.
Axiom proof_of_cm_emit_return_epilogue_plan_partial_solve_wit_3 : cm_emit_return_epilogue_plan_partial_solve_wit_3.
Axiom proof_of_cm_emit_return_epilogue_plan_partial_solve_wit_4_pure : cm_emit_return_epilogue_plan_partial_solve_wit_4_pure.
Axiom proof_of_cm_emit_return_epilogue_plan_partial_solve_wit_4 : cm_emit_return_epilogue_plan_partial_solve_wit_4.
Axiom proof_of_cm_emit_return_epilogue_plan_partial_solve_wit_5_pure : cm_emit_return_epilogue_plan_partial_solve_wit_5_pure.
Axiom proof_of_cm_emit_return_epilogue_plan_partial_solve_wit_5 : cm_emit_return_epilogue_plan_partial_solve_wit_5.
Axiom proof_of_cm_emit_return_epilogue_plan_partial_solve_wit_6_pure : cm_emit_return_epilogue_plan_partial_solve_wit_6_pure.
Axiom proof_of_cm_emit_return_epilogue_plan_partial_solve_wit_6 : cm_emit_return_epilogue_plan_partial_solve_wit_6.

End VC_Correct.
