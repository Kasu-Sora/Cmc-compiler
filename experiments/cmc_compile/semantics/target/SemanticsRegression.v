(* Executable regression observations; these examples do not prove preservation. *)
Require Import SimpleC.EE.QCP_demos_human.cmc_preservation_observation_migration_lib.
From Coq Require Import ZArith List Bool.
Import ListNotations.
Local Open Scope Z_scope.
Definition regression_function := CMFunctionD CMIntTy [] [] CMSkipS.
Definition regression_policy := CMLookupPolicy O (fun _=>regression_function).
Definition regression_source_policy := CMSourceLookupPolicy regression_policy
 (fun _=>cm_default_global) (fun _=>CMStringD []) (fun _=>cm_default_slot) (fun _=>cm_default_struct).
Definition regression_source fuel p input := match cm_iter regression_source_policy fuel (CMStartTask p input) with
 | CMDoneTask st ctl status=>Some (cm_control_kind ctl,status,cm_state_output st) | _=>None end.
Definition regression_target fuel p input := match tvm_iter fuel (TVMBoot (cm_compile_model regression_policy p) input) with
 | TVMDoneTask st status kind=>Some (kind,status,tvm_output st) | _=>None end.
Definition regression_main body := CMProgram [] [] [] [CMFunctionD CMIntTy [] [] body] 0.
Definition regression_const := regression_main (CMReturnS (CMConstE 42 CMIntTy)).
Example return_constant_source : regression_source 32 regression_const []=Some (3,42,[]).
Proof. vm_compute; reflexivity. Qed.
Example return_constant_target : regression_target 128 regression_const []=Some (0,42,[]).
Proof. vm_compute; reflexivity. Qed.
Definition regression_short := regression_main (CMReturnS (CMBinaryE 0 (CMConstE 1 CMIntTy)
 (CMBinaryE 11 (CMConstE 1 CMIntTy) (CMConstE 0 CMIntTy) CMIntTy) CMIntTy)).
Example short_circuit_source : regression_source 64 regression_short []=Some (3,1,[]).
Proof. vm_compute; reflexivity. Qed.
Example short_circuit_target : regression_target 128 regression_short []=Some (0,1,[]).
Proof. vm_compute; reflexivity. Qed.
Definition regression_call := CMProgram [] [] []
 [CMFunctionD CMIntTy [] [] (CMSeqS (CMExprS (CMPutcE (CMGetcE CMIntTy) CMIntTy))
   (CMReturnS (CMCallE 1 [CMConstE 40 CMIntTy;CMConstE 2 CMIntTy] CMIntTy)));
  CMFunctionD CMIntTy [CMSlotD CMIntTy 0;CMSlotD CMIntTy 0] []
   (CMReturnS (CMBinaryE 8 (CMVarE 2 0 CMIntTy) (CMVarE 2 1 CMIntTy) CMIntTy))] 0.
Example call_io_source : regression_source 128 regression_call [65]=Some (3,42,[65]).
Proof. vm_compute; reflexivity. Qed.
Example call_io_target : regression_target 256 regression_call [65]=Some (0,42,[65]).
Proof. vm_compute; reflexivity. Qed.
Definition regression_loop := CMProgram [] [] [] [CMFunctionD CMIntTy [] [CMSlotD CMIntTy 0]
 (CMSeqS (CMInitS 0 (CMConstE 0 CMIntTy))
 (CMSeqS (CMWhileS (CMBinaryE 4 (CMVarE 1 0 CMIntTy) (CMConstE 3 CMIntTy) CMIntTy)
  (CMExprS (CMAssignE (CMVarE 1 0 CMIntTy) (CMBinaryE 8 (CMVarE 1 0 CMIntTy) (CMConstE 1 CMIntTy) CMIntTy) CMIntTy)))
  (CMReturnS (CMVarE 1 0 CMIntTy))))] 0.
Example loop_source : regression_source 256 regression_loop []=Some (3,3,[]).
Proof. vm_compute; reflexivity. Qed.
Example loop_target : regression_target 512 regression_loop []=Some (0,3,[]).
Proof. vm_compute; reflexivity. Qed.
Definition regression_global := CMProgram [] [CMGlobalD CMCharTy 0 true 65] []
 [CMFunctionD CMIntTy [] [] (CMSeqS (CMExprS (CMPutcE (CMVarE 0 0 CMCharTy) CMIntTy)) (CMReturnS (CMConstE 0 CMIntTy)))] 0.
Example global_source : regression_source 64 regression_global []=Some (3,0,[65]).
Proof. vm_compute; reflexivity. Qed.
Example global_target : regression_target 128 regression_global []=Some (0,0,[65]).
Proof. vm_compute; reflexivity. Qed.
Definition regression_uninit := CMProgram [] [] [] [CMFunctionD CMIntTy [] [CMSlotD CMIntTy 0]
 (CMSeqS (CMDeclS 0) (CMReturnS (CMVarE 1 0 CMIntTy)))] 0.
Example uninitialized_is_source_error : regression_source 64 regression_uninit []=Some (5,2,[]).
Proof. vm_compute; reflexivity. Qed.
Example invalid_pc_is_target_error :
 match tvm_step (TVMRunTask (TVMObject 0 [] []) (TVMState 0 [] [] tower_zero_mem [] [])) with
 | TVMDoneTask _ status kind => (status,kind) | _=>(-1,-1) end = (2,1).
Proof. reflexivity. Qed.
