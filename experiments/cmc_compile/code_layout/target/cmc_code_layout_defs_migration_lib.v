Require Export SimpleC.EE.QCP_demos_human.cmc_code_phase_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Fixpoint cm_cursor_code sp p fid pc temp (normal:bool) (cursors:list cm_acursor) : list tvm_inst := match cursors with
 | []=>[]
 | cursor::rest=>let phase:=cm_cursor_phase cursor in
   let fragment:=if normal then cm_normal_phase_code sp p fid pc temp (cm_cursor_temp cursor) (cm_cursor_break cursor) (cm_cursor_continue cursor) phase else cm_value_phase_code sp p fid pc temp (cm_cursor_temp cursor) (cm_cursor_break cursor) (cm_cursor_continue cursor) phase in
   fragment++(if (if normal then cm_normal_phase_stops phase else cm_phase_stops phase) then [] else cm_cursor_code sp p fid (pc+Zlength fragment) (cm_cursor_temp cursor) (normal || cm_phase_yields_normal phase) rest) end.
Definition cm_cont_code sp p fid pc temp cursors := cm_cursor_code sp p fid pc temp false cursors.
Definition cm_normal_cont_code sp p fid pc temp cursors := cm_cursor_code sp p fid pc temp true cursors.
Definition cm_control_phase_code sp p fid pc temp breakpc continuepc ctl cursors :=
 if cm_control_kind ctl=?3 then cm_return_tail_code sp p fid
 else if cm_control_kind ctl=?1 then [TVMInst TVMJmpOp breakpc]
 else if cm_control_kind ctl=?2 then [TVMInst TVMJmpOp continuepc]
 else if (cm_control_kind ctl=?4) || cm_list_empty cursors then []
 else cm_normal_cont_code sp p fid pc temp cursors.
Definition cm_task_code sp p task ann := let policy:=cm_source_function_policy sp in match task with
 | CMStartTask _ _=>[TVMInst TVMPushOp 1048576; TVMInst TVMPushOp 8; TVMInst TVMStoreOp 0; TVMInst TVMCallOp (cm_function_pc policy p (cm_program_main p))]
 | CMRTask _ fid expr _ _=>cm_emit_rvalue policy p fid (cm_ann_pc ann) (cm_ann_temp ann) expr ++ cm_cont_code sp p fid (cm_ann_pc ann+cm_rvalue_code_count policy p fid expr) (cm_ann_temp ann) (cm_ann_cursors ann)
 | CMLTask _ fid expr _ _=>cm_emit_lvalue policy p fid (cm_ann_pc ann) (cm_ann_temp ann) expr ++ cm_cont_code sp p fid (cm_ann_pc ann+cm_lvalue_code_count policy p fid expr) (cm_ann_temp ann) (cm_ann_cursors ann)
 | CMSTask _ fid stmt _ _=>cm_emit_stmt policy p fid (cm_ann_pc ann) (cm_ann_temp ann) (cm_ann_break ann) (cm_ann_continue ann) stmt ++ cm_normal_cont_code sp p fid (cm_ann_pc ann+cm_stmt_code_count policy p fid stmt) (cm_ann_temp ann) (cm_ann_cursors ann)
 | CMVTask _ fid _ _ _=>cm_cont_code sp p fid (cm_ann_pc ann) (cm_ann_temp ann) (cm_ann_cursors ann)
 | CMCTask _ fid ctl _ _=>cm_control_phase_code sp p fid (cm_ann_pc ann) (cm_ann_temp ann) (cm_ann_break ann) (cm_ann_continue ann) ctl (cm_ann_cursors ann)
 | CMDoneTask _ _ _=>[] end.
Definition cm_phase_site sp ap p code fid cursor rest calls phase : Prop := let policy:=cm_source_function_policy sp in match phase with
 | CABlockP _ _ jump target=>jump=false \/ cm_code_at code target (cm_normal_cont_code sp p fid target (cm_cursor_temp cursor) rest)
 | CAWhileGuardP guard body loop_start loop_end | CAWhileBodyP guard body _ _ loop_start loop_end=>
   cm_code_at code loop_start (cm_emit_rvalue policy p fid loop_start (cm_cursor_temp cursor) guard ++ [TVMInst TVMJzOp loop_end] ++ cm_emit_stmt policy p fid (loop_start+cm_rvalue_code_count policy p fid guard+1) (cm_cursor_temp cursor) loop_end loop_start body ++ [TVMInst TVMJmpOp loop_start] ++ cm_normal_cont_code sp p fid loop_end (cm_cursor_temp cursor) rest) /\ cm_code_at code loop_end (cm_normal_cont_code sp p fid loop_end (cm_cursor_temp cursor) rest)
 | CACallP caller _ _ _ _=>calls<>[] /\ cm_code_at code (cm_call_sim_return (hd (cm_call_nil ap) calls)) (cm_cont_code sp p caller (cm_call_sim_return (hd (cm_call_nil ap) calls)) (cm_cursor_temp cursor) rest)
 | _=>True end.
Fixpoint cm_saved_layout sp ap p code fid (cursors:list cm_acursor) calls : Prop := match cursors with
 | []=>calls=[]
 | cursor::rest=>cm_phase_site sp ap p code fid cursor rest calls (cm_cursor_phase cursor) /\ cm_saved_layout sp ap p code (if cm_phase_is_call (cm_cursor_phase cursor) then cm_phase_caller (cm_cursor_phase cursor) else fid) rest (if cm_phase_is_call (cm_cursor_phase cursor) then tl calls else calls) end.
Definition cm_task_fid task := match task with
 | CMStartTask _ _ | CMDoneTask _ _ _=> -1
 | CMRTask _ fid _ _ _ | CMLTask _ fid _ _ _ | CMSTask _ fid _ _ _ | CMVTask _ fid _ _ _ | CMCTask _ fid _ _ _=>fid end.
Definition cm_task_layout sp ap p task ann : Prop := match task with
 | CMDoneTask _ _ _=>True
 | _=>cm_code_at (cm_model_code (cm_source_function_policy sp) p) (cm_ann_pc ann) (cm_task_code sp p task ann) /\ cm_saved_layout sp ap p (cm_model_code (cm_source_function_policy sp) p) (cm_task_fid task) (cm_ann_cursors ann) (cm_ann_calls ann) end.
