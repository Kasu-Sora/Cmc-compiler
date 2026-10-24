Require Export SimpleC.EE.QCP_demos_human.cmc_annotation_updates_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Definition cm_entry_steps sp p := S (4+cm_code_steps (cm_emit_prologue (cm_source_function_policy sp) p (cm_program_main p)))%nat.
Definition cm_annotation_step sp ap task ann := match task with
 | CMStartTask p input =>
   if cm_call_ok sp p (cm_program_main p) [] (cm_initial_state sp p input) && (cm_call_depth [CMHaltK] <? 65536)
   then CMAUpdate (cm_entry_steps sp p) (cm_ann_enter_call sp p (-1) (cm_program_main p) (cm_initial_state sp p input) CMIntTy 4 0 0 0 [CMACursor CAHaltP 0 0 0] [] [] [])
   else CMAUpdate 0 (CMAnnotation 0 0 0 0 [CMACursor CAHaltP 0 0 0] [] [] [])
 | CMRTask p fid expr st ks=>cm_update_r sp ap p fid st ann expr
 | CMLTask p fid expr st ks=>cm_update_l sp ap p fid st ann expr
 | CMSTask p fid stmt st ks=>cm_update_s sp ap p fid st ann stmt
 | CMVTask p fid v st ks=>match cm_ann_cursors ann with []=>CMAUpdate 0 ann | cursor::_=>cm_update_v sp ap p fid v st ann (cm_cursor_phase cursor) end
 | CMCTask p fid ctl st ks=>if cm_control_kind ctl =? 4 then CMAUpdate 0 (cm_ann_done ann) else
   match cm_ann_cursors ann with []=>CMAUpdate 0 ann | cursor::_=>cm_update_c sp ap p fid ctl st ann (cm_cursor_phase cursor) end
 | CMDoneTask st ctl status=>CMAUpdate 0 ann end.
Definition cm_annotated_step sp ap ast :=
 let update:=cm_annotation_step sp ap (cm_astate_task ast) (cm_astate_annotation ast) in
 CMAState (cm_step sp (cm_astate_task ast)) (tvm_iter (cm_update_steps update) (cm_astate_target ast)) (cm_update_annotation update).
Fixpoint cm_annotated_iter sp ap n ast := match n with O=>ast | S k=>cm_annotated_iter sp ap k (cm_annotated_step sp ap ast) end.
Definition cm_annotation_erases task ann := match task with
 | CMStartTask _ _ | CMDoneTask _ _ _=>cm_ann_cursors ann=[]
 | CMRTask _ _ _ _ ks | CMLTask _ _ _ _ ks | CMSTask _ _ _ _ ks | CMVTask _ _ _ _ ks | CMCTask _ _ _ _ ks=>cm_cursor_frames (cm_ann_cursors ann)=ks end.
Fixpoint cm_cursors_rooted cursors : Prop := match cursors with []=>True | cursor::rest=>(cm_cursor_phase cursor=CAHaltP -> rest=[]) /\ cm_cursors_rooted rest end.
Definition cm_annotation_rooted ann := cm_cursors_rooted (cm_ann_cursors ann).
Lemma cm_annotated_step_task sp ap ast : cm_astate_task (cm_annotated_step sp ap ast)=cm_step sp (cm_astate_task ast).
Proof. reflexivity. Qed.
Lemma cm_annotated_step_target sp ap ast : cm_astate_target (cm_annotated_step sp ap ast)=tvm_iter (cm_update_steps (cm_annotation_step sp ap (cm_astate_task ast) (cm_astate_annotation ast))) (cm_astate_target ast).
Proof. reflexivity. Qed.
Lemma cm_annotated_iter_task sp ap n ast : cm_astate_task (cm_annotated_iter sp ap n ast)=cm_iter sp n (cm_astate_task ast).
Proof. revert ast; induction n; intro ast; cbn [cm_annotated_iter cm_iter]; [reflexivity|rewrite IHn; reflexivity]. Qed.
Lemma cm_annotated_iter_add sp ap m n ast : cm_annotated_iter sp ap (m+n) ast=cm_annotated_iter sp ap n (cm_annotated_iter sp ap m ast).
Proof. revert ast; induction m; intro ast; cbn; [reflexivity|apply IHm]. Qed.
Lemma cm_annotated_iter_exec_prefix sp ap n ast out : tvm_exec (cm_astate_target (cm_annotated_iter sp ap n ast)) out -> tvm_exec (cm_astate_target ast) out.
Proof. revert ast; induction n; intros ast H; cbn [cm_annotated_iter] in H; [exact H|]. apply IHn in H; rewrite cm_annotated_step_target in H; now apply tvm_exec_prefix in H. Qed.
Lemma cm_annotated_start_rooted policy p input : cm_annotation_rooted (cm_astate_annotation (cm_annotated_start policy p input)).
Proof. exact I. Qed.
Lemma cm_annotated_start_erases policy p input : cm_annotation_erases (cm_astate_task (cm_annotated_start policy p input)) (cm_astate_annotation (cm_annotated_start policy p input)).
Proof. reflexivity. Qed.
