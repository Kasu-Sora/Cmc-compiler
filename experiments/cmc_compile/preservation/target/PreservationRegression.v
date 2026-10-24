(* Finite executable checks of annotation step counts and PC alignment.
   These observations are not a universal compiler-correctness proof. *)
Require Import SimpleC.EE.QCP_demos_human.cmc_simulation_composition_migration_lib.
Require Import SimpleC.EE.QCP_demos_human.SemanticsRegression.
From Coq Require Import ZArith List Bool.
Import ListNotations.
Local Open Scope Z_scope.
Definition regression_annotation_policy := CMAnnotationPolicy (CMACursor CAHaltP 0 0 0)
 (CMSpillFrame (-1) 0 []) (CMCallSimFrame 0 0 0).
Definition regression_annotated fuel p input :=
 let ast:=cm_annotated_iter regression_source_policy regression_annotation_policy fuel (cm_annotated_start regression_policy p input) in
 match cm_astate_task ast,cm_astate_target ast with
 | CMDoneTask st ctl status,TVMDoneTask vm targetstatus kind=>
 Some (status,targetstatus,kind,cm_state_output st,tvm_output vm,
       tvm_pc vm =? cm_ann_pc (cm_astate_annotation ast),cm_list_empty (cm_ann_cursors (cm_astate_annotation ast)))
 | _,_=>None end.
Example annotated_return_constant : regression_annotated 32 regression_const []=Some (42,42,0,[],[],true,true).
Proof. vm_compute; reflexivity. Qed.
Example annotated_short_circuit : regression_annotated 64 regression_short []=Some (1,1,0,[],[],true,true).
Proof. vm_compute; reflexivity. Qed.
Example annotated_call_io : regression_annotated 128 regression_call [65]=Some (42,42,0,[65],[65],true,true).
Proof. vm_compute; reflexivity. Qed.
Example annotated_while_assignment : regression_annotated 256 regression_loop []=Some (3,3,0,[],[],true,true).
Proof. vm_compute; reflexivity. Qed.
Example annotated_global_char : regression_annotated 64 regression_global []=Some (0,0,0,[65],[65],true,true).
Proof. vm_compute; reflexivity. Qed.
Example word_negative_roundtrip : tower_getw (tower_setw tower_zero_mem 32 (-1)) 32=(-1).
Proof. rewrite tower_getw_setw; reflexivity. Qed.
Example word_overflow_roundtrip : tower_getw (tower_setw tower_zero_mem 32 18446744073709551617) 32=1.
Proof. rewrite tower_getw_setw; reflexivity. Qed.
Example partial_word_write_clears_tag : cm_clear_tagged (fun _=>true) 39 1 32=false.
Proof. reflexivity. Qed.
Example adjacent_word_write_keeps_tag : cm_clear_tagged (fun _=>true) 40 8 32=true.
Proof. reflexivity. Qed.
