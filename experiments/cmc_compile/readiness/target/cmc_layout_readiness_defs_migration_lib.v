Require Export SimpleC.EE.QCP_demos_human.cmc_runtime_invariant_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
(* Original layout readiness predicates; Boolean source guards are asserted true.
   Total HOL head selection remains explicit in ap. *)
Definition cm_r_layout_ready sp p fid expr st ks ann : Prop :=
 (forall callee ty, expr=CMCallE callee [] ty -> cm_call_ok sp p callee [] st=true /\ cm_call_depth ks<65536 /\ cm_call_depth (cm_cursor_frames (cm_ann_cursors ann))<65536) /\
 (forall ty, expr=CMGetcE ty -> cm_state_input st=[] \/ tower_byte_value (hd 0 (cm_state_input st))) /\
 (forall scope slot ty, expr=CMVarE scope slot ty -> cm_binding_array sp p fid scope slot=true -> cm_binding_address_ok sp p fid scope slot st=true).
Definition cm_l_layout_ready sp p fid expr st : Prop := cm_lvalue expr /\
 (forall scope slot ty, expr=CMVarE scope slot ty -> cm_binding_address_ok sp p fid scope slot st=true).
Definition cm_v_temp_ready ap ann phase : Prop := cm_ann_temp ann=cm_phase_child_temp phase (cm_cursor_temp (hd (cm_cursor_nil ap) (cm_ann_cursors ann))).
Definition cm_v_phase_ready sp p v st ann phase : Prop := match phase with
 | CAHaltP=>tl (cm_ann_cursors ann)=[]
 | CALoadP ty=>cm_load_ok ty v st=true
 | CAAssignRP ptr ty=>cm_store_ok ty ptr st=true
 | CABinRP op _ _ lhs _=>cm_binary_ok p op lhs v st=true
 | CAIndexRP base _=>cm_ptr_shift_ok (cm_program_structs p) base (cm_value_number st v) st=true
 | CAMemberP mid _=>cm_ptr_member_ok sp p v mid st=true
 | CABlockP _ _ _ _ | CASeqP _ | CAWhileBodyP _ _ _ _ _ _ | CACallP _ _ _ _ _=>False
 | CAArgP callee rest values ret args base current scratch=>rest<>[] \/ (cm_call_ok sp p callee (rev (v::values)) st=true /\ cm_call_depth (cm_cursor_frames (tl (cm_ann_cursors ann)))<65536)
 | _=>True end.
Definition cm_v_layout_ready sp ap p v st ann : Prop := cm_ann_cursors ann=[] \/
 (cm_ann_cursors ann<>[] /\ cm_v_temp_ready ap ann (cm_cursor_phase (hd (cm_cursor_nil ap) (cm_ann_cursors ann))) /\ cm_v_phase_ready sp p v st ann (cm_cursor_phase (hd (cm_cursor_nil ap) (cm_ann_cursors ann)))).
Definition cm_c_regular_ready ap ctl ann : Prop := cm_control_kind ctl<>5 /\
 (cm_control_kind ctl=1 -> cm_ann_break ann=cm_cursor_break (hd (cm_cursor_nil ap) (cm_ann_cursors ann))) /\
 (cm_control_kind ctl=2 -> cm_ann_continue ann=cm_cursor_continue (hd (cm_cursor_nil ap) (cm_ann_cursors ann))).
Definition cm_c_phase_ready ap ctl ann phase : Prop := match phase with
 | CAHaltP=>cm_control_kind ctl=4 /\ tl (cm_ann_cursors ann)=[]
 | CABlockP _ _ _ _ | CASeqP _=>cm_c_regular_ready ap ctl ann
 | CAWhileBodyP _ _ _ _ _ _=>cm_control_kind ctl<>5
 | CACallP _ _ _ _ _=>cm_control_kind ctl=0 \/ cm_control_kind ctl=3 \/ cm_control_kind ctl=4
 | _=>cm_control_kind ctl=4 /\ cm_c_regular_ready ap ctl ann end.
Definition cm_c_code_ready policy p fid ann phase : Prop := forall guard body env regions loop_start loop_end,
 phase=CAWhileBodyP guard body env regions loop_start loop_end ->
 cm_ann_break ann=loop_end /\ cm_ann_continue ann=loop_start /\
 loop_end=loop_start+cm_rvalue_code_count policy p fid guard+1+cm_stmt_code_count policy p fid body+1.
Definition cm_c_layout_ready policy ap p fid ctl ann : Prop :=
 (cm_ann_cursors ann=[] /\ cm_control_kind ctl<>1 /\ cm_control_kind ctl<>2 /\ cm_control_kind ctl<>3) \/
 (cm_ann_cursors ann<>[] /\ cm_c_phase_ready ap ctl ann (cm_cursor_phase (hd (cm_cursor_nil ap) (cm_ann_cursors ann))) /\ cm_c_code_ready policy p fid ann (cm_cursor_phase (hd (cm_cursor_nil ap) (cm_ann_cursors ann)))).
Definition cm_task_layout_ready sp ap p task ann : Prop := match task with
 | CMStartTask q input=>q=p /\ ann=cm_initial_annotation /\ cm_call_ok sp p (cm_program_main p) [] (cm_initial_state sp p input)=true
 | CMRTask q fid e st ks=>q=p /\ cm_r_layout_ready sp p fid e st ks ann
 | CMLTask q fid e st _=>q=p /\ cm_l_layout_ready sp p fid e st
 | CMSTask q fid s _ _=>q=p /\ cm_stmt_start_safe sp p fid s=true
 | CMVTask q _ v st _=>q=p /\ cm_v_layout_ready sp ap p v st ann
 | CMCTask q fid ctl _ _=>q=p /\ cm_c_layout_ready (cm_source_function_policy sp) ap p fid ctl ann
 | CMDoneTask _ _ _=>True end.
(* Local refinement: controls other than exit/error occur at statement parents.
   This is proved from the concrete steps and never imposed as a C Require. *)
Definition cm_task_statement_control task ann : Prop := match task with
 | CMCTask _ _ ctl _ _=>cm_control_kind ctl=4 \/ cm_control_kind ctl=5 \/ cm_statement_cursors_ready (cm_ann_cursors ann)=true
 | _=>True end.
