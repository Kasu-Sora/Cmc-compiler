Require Export SimpleC.EE.QCP_demos_human.cmc_simulation_state_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
(* Annotation data and terminal-observation fragment of cmc_annotate_model.c
   and cmc_preservation_state.c. The preservation-step theorem is not assumed. *)
Inductive cm_aphase := CAHaltP | CALoadP (ty:cm_type)
 | CAAssignLP (expr:cm_expr) (ty:cm_type) | CAAssignRP (v:cm_value) (ty:cm_type)
 | CABinLP (op:Z) (lhs rhs:cm_expr) (ty:cm_type) | CABinRP (op:Z) (lhs rhs:cm_expr) (v:cm_value) (ty:cm_type)
 | CAUnaryP (op:Z) | CAIndexLP (expr:cm_expr) (ty:cm_type) | CAIndexRP (v:cm_value) (ty:cm_type)
 | CAMemberP (mid:Z) (ty:cm_type) | CAPutcP | CAPutiP | CAExitP | CAExprStmtP | CAInitP (slot:Z)
 | CABlockP (env:Z->Z->cm_value) (regions:list cm_region) (flag:bool) (pc:Z)
 | CASeqP (stmt:cm_stmt) | CAIfP (yes no:cm_stmt)
 | CAWhileGuardP (guard:cm_expr) (body:cm_stmt) (start finish:Z)
 | CAWhileBodyP (guard:cm_expr) (body:cm_stmt) (env:Z->Z->cm_value) (regions:list cm_region) (start finish:Z)
 | CAReturnP | CAArgP (callee:Z) (rest:list cm_expr) (values:list cm_value) (ret:cm_type) (args:list cm_expr) (pc index temp:Z)
 | CACallP (caller:Z) (env:Z->Z->cm_value) (fp:Z) (regions:list cm_region) (ret:cm_type).
Inductive cm_acursor := CMACursor (phase:cm_aphase) (temp breakpc continuepc:Z).
Inductive cm_annotation := CMAnnotation (pc temp breakpc continuepc:Z) (cursors:list cm_acursor)
 (spills:list cm_spill) (saved:list cm_spill_frame) (calls:list cm_call_sim_frame).
Inductive cm_aupdate := CMAUpdate (steps:nat) (ann:cm_annotation).
Inductive cm_astate := CMAState (task:cm_task) (target:tvm_task) (ann:cm_annotation).
Definition cm_ann_pc ann := match ann with CMAnnotation pc _ _ _ _ _ _ _=>pc end.
Definition cm_ann_temp ann := match ann with CMAnnotation _ temp _ _ _ _ _ _=>temp end.
Definition cm_ann_break ann := match ann with CMAnnotation _ _ b _ _ _ _ _=>b end.
Definition cm_ann_continue ann := match ann with CMAnnotation _ _ _ c _ _ _ _=>c end.
Definition cm_ann_cursors ann := match ann with CMAnnotation _ _ _ _ cs _ _ _=>cs end.
Definition cm_ann_spills ann := match ann with CMAnnotation _ _ _ _ _ ss _ _=>ss end.
Definition cm_ann_saved ann := match ann with CMAnnotation _ _ _ _ _ _ ss _=>ss end.
Definition cm_ann_calls ann := match ann with CMAnnotation _ _ _ _ _ _ _ cs=>cs end.
Definition cm_update_steps update := match update with CMAUpdate n _=>n end.
Definition cm_update_annotation update := match update with CMAUpdate _ ann=>ann end.
Definition cm_astate_task ast := match ast with CMAState task _ _=>task end.
Definition cm_astate_target ast := match ast with CMAState _ target _=>target end.
Definition cm_astate_annotation ast := match ast with CMAState _ _ ann=>ann end.
Definition cm_initial_annotation := CMAnnotation 0 0 0 0 [] [] [] [].
Definition cm_annotated_start policy p input := CMAState (CMStartTask p input) (TVMBoot (cm_compile_model policy p) input) cm_initial_annotation.
Definition cm_active_spill_frames fid st ann := CMSpillFrame fid (cm_state_fp st) (cm_ann_spills ann) :: cm_ann_saved ann.
Definition cm_running_target_sim policy p fid st values ann target := exists vm,
 target=TVMRunTask (cm_compile_model policy p) vm /\ tvm_pc vm=cm_ann_pc ann /\
 cm_machine_state_sim policy p st vm (cm_ann_calls ann) (cm_active_spill_frames fid st ann) values [].
Definition cm_halted_target_sim policy p fid st status (active:bool) ann target := exists vm,
 target=TVMDoneTask vm status 0 /\ tvm_pc vm=cm_ann_pc ann /\
 cm_machine_state_sim policy p st vm (cm_ann_calls ann)
 (if active then cm_active_spill_frames fid st ann else cm_ann_saved ann) [] [].
Definition cm_task_target_sim policy rootp task target ann := match task with
 | CMStartTask p input => p=rootp /\ target=TVMBoot (cm_compile_model policy rootp) input /\ ann=cm_initial_annotation
 | CMRTask p fid expr st ks | CMLTask p fid expr st ks => p=rootp /\ cm_running_target_sim policy rootp fid st [] ann target
 | CMSTask p fid stmt st ks => p=rootp /\ cm_running_target_sim policy rootp fid st [] ann target
 | CMVTask p fid v st ks => p=rootp /\ cm_running_target_sim policy rootp fid st [v] ann target
 | CMCTask p fid ctl st ks => p=rootp /\
   (if cm_control_kind ctl =? 4 then cm_halted_target_sim policy rootp fid st (cm_control_status ctl) true ann target
   else cm_running_target_sim policy rootp fid st (if cm_control_kind ctl =? 3 then [cm_control_value ctl] else []) ann target)
 | CMDoneTask st ctl status => cm_halted_target_sim policy rootp (-1) st status false ann target end.
Definition cm_astate_sim policy p ast := cm_task_target_sim policy p (cm_astate_task ast) (cm_astate_target ast) (cm_astate_annotation ast).
Definition cm_task_succeeds sp task := exists st ctl status, cm_exec sp task (CMOutcome st ctl status) /\ cm_success_control ctl.
Lemma cm_done_target_observation policy p st ctl status target ann :
 cm_task_target_sim policy p (CMDoneTask st ctl status) target ann ->
 exists vm, target=TVMDoneTask vm status 0 /\ tvm_output vm=cm_state_output st.
Proof. intros [vm [Heq [Hpc Hsim]]]. exists vm; split; [exact Heq|exact (proj2 (cm_machine_sim_io _ _ _ _ _ _ _ _ Hsim))]. Qed.
Lemma cm_succeeds_step_total sp task : cm_task_succeeds sp task -> cm_task_succeeds sp (cm_step sp task).
Proof. intros [st [ctl [status [Hrun Hctl]]]]; exists st,ctl,status; split; [now apply cm_exec_step_inv|exact Hctl]. Qed.
Lemma cm_succeeds_step_inv sp task : cm_task_succeeds sp (cm_step sp task) -> cm_task_succeeds sp task.
Proof. intros [st [ctl [status [Hrun Hctl]]]]; exists st,ctl,status; split; [now apply cm_exec_rule|exact Hctl]. Qed.
Lemma cm_done_target_exec policy p st ctl status target ann :
 cm_task_target_sim policy p (CMDoneTask st ctl status) target ann ->
 exists vm, tvm_exec target (TVMOutcome vm status 0) /\ tvm_output vm=cm_state_output st.
Proof. intro H; destruct (cm_done_target_observation _ _ _ _ _ _ _ H) as [vm [-> Ho]]. exists vm; split; [apply tvm_exec_done|exact Ho]. Qed.
Lemma cm_initial_target_sim policy p input : cm_astate_sim policy p (cm_annotated_start policy p input).
Proof. repeat split; reflexivity. Qed.
