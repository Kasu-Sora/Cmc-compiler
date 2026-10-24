(* The continuation machine of cmc_lang.c, parameterized over total HOL lookups. *)
Require Export SimpleC.EE.QCP_demos_human.cmc_source_call_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Definition cm_binding_array sp p fid scope slot :=
 if scope =? 0 then negb (cm_global_count (cm_source_global_at sp slot (cm_program_globals p)) =? 0)
 else if scope =? 1 then negb (cm_slot_count (cm_source_slot_at sp slot (cm_function_locals (cm_source_function_at sp fid p))) =? 0) else false.
Definition cm_member_slot sp p ptr mid := cm_source_slot_at sp mid (cm_struct_members (cm_source_struct_at sp (cm_struct_id (cm_ptr_view ptr)) (cm_program_structs p))).
Definition cm_member_array sp p base mid := negb (cm_slot_count (cm_source_slot_at sp mid
 (cm_struct_members (cm_source_struct_at sp (cm_struct_id (cm_pointee base)) (cm_program_structs p)))) =? 0).
Definition cm_ptr_member sp p ptr mid :=
 let off:=cm_ptr_offset ptr+cm_member_offset (cm_program_structs p) (cm_struct_id (cm_ptr_view ptr)) mid in
 CMPtrV (cm_ptr_gen ptr) off (off+cm_slot_size (cm_program_structs p) (cm_member_slot sp p ptr mid)) off (cm_slot_ty (cm_member_slot sp p ptr mid)).
Definition cm_ptr_member_ok sp p ptr mid st := cm_pointer_live st ptr &&
 (cm_ptr_lo ptr <=? cm_ptr_lo (cm_ptr_member sp p ptr mid)) &&
 (cm_ptr_hi (cm_ptr_member sp p ptr mid) <=? cm_ptr_hi ptr) && cm_pointer_live st (cm_ptr_member sp p ptr mid).
Definition cm_binding_address_ok sp p fid scope slot st :=
 let addr:=if scope =? 0 then cm_global_address p slot else if scope =? 1 then cm_local_base sp p fid slot (cm_state_fp st) else cm_param_base sp p fid slot (cm_state_fp st) in
 let ptr:=if scope =? 0 then cm_global_pointer sp p slot else cm_state_env st scope slot in
 let ty:=if scope =? 0 then cm_global_ty (cm_source_global_at sp slot (cm_program_globals p))
 else if scope =? 1 then cm_slot_ty (cm_source_slot_at sp slot (cm_function_locals (cm_source_function_at sp fid p)))
 else cm_slot_ty (cm_source_slot_at sp slot (cm_function_params (cm_source_function_at sp fid p))) in
 tower_signed64b addr && (tower_wrap64 addr =? cm_value_number st ptr) && cm_type_eqb (cm_value_type ptr) (CMPtrTy ty).
Definition cm_args_start sp p caller args st ks callee ret := match args with
 | [] => cm_begin_call sp p caller callee [] st ret ks
 | arg::args=>CMRTask p caller arg st (CMArgK callee args [] ret :: ks) end.
Definition cm_rstart sp p fid expr st ks := match expr with
 | CMConstE n ty => CMVTask p fid (cm_convert_value st ty (CMIntV n)) st ks
 | CMStringE sid ty => CMVTask p fid (cm_string_pointer sp p sid) st ks
 | CMVarE scope slot ty => if cm_binding_array sp p fid scope slot then
   if cm_binding_address_ok sp p fid scope slot st then CMVTask p fid
    (if scope =? 0 then cm_global_pointer sp p slot else cm_state_env st scope slot) st ks
   else CMCTask p fid (CMError 1) st ks
   else CMLTask p fid (CMVarE scope slot ty) st (CMLoadK ty :: ks)
 | CMAssignE dst src ty => CMLTask p fid dst st (CMAssignLK src ty :: ks)
 | CMBinaryE op lhs rhs ty => CMRTask p fid lhs st (CMBinLK op rhs ty :: ks)
 | CMUnaryE op arg ty => if op =? 2 then CMRTask p fid arg st (CMLoadK ty :: ks)
   else if op =? 3 then CMLTask p fid arg st ks else CMRTask p fid arg st (CMUnaryK op :: ks)
 | CMIndexE base index ty => CMLTask p fid (CMIndexE base index ty) st (CMLoadK ty :: ks)
 | CMMemberE base mid ty => CMLTask p fid (CMMemberE base mid ty) st (if cm_member_array sp p (cm_expr_type base) mid then ks else CMLoadK ty :: ks)
 | CMCallE callee args ty => cm_args_start sp p fid args st ks callee ty
 | CMSizeofE asked ty => CMVTask p fid (CMIntV (cm_type_size (cm_program_structs p) asked)) st ks
 | CMGetcE ty => match cm_state_input st with []=>CMVTask p fid (CMIntV (-1)) st ks
   | byte::rest=>if tower_byte_valueb byte then CMVTask p fid (CMIntV byte) (cm_state_io st rest (cm_state_output st)) ks
    else CMCTask p fid (CMError 1) st ks end
 | CMPutcE arg ty => CMRTask p fid arg st (CMPutcK :: ks)
 | CMPutiE arg ty => CMRTask p fid arg st (CMPutiK :: ks)
 | CMExitE arg ty => CMRTask p fid arg st (CMExitK :: ks) end.
Definition cm_lstart sp p fid expr st ks := match expr with
 | CMVarE scope slot ty => if cm_binding_address_ok sp p fid scope slot st then
 CMVTask p fid (if scope =? 0 then cm_global_pointer sp p slot else cm_state_env st scope slot) st ks
 else CMCTask p fid (CMError 1) st ks
 | CMUnaryE op arg ty => if op =? 2 then CMRTask p fid arg st ks else CMCTask p fid (CMError 1) st ks
 | CMIndexE base index ty => CMRTask p fid base st (CMIndexLK index ty :: ks)
 | CMMemberE base mid ty => CMRTask p fid base st (CMMemberK mid :: ks)
 | _=> CMCTask p fid (CMError 1) st ks end.
Definition cm_lstart_list (sp:cm_source_lookup_policy) p fid (args:list cm_expr) st ks := CMCTask p fid (CMError 1) st ks.
Definition cm_control_kind ctl : Z := match ctl with CMNormal=>0 | CMBreak=>1 | CMContinue=>2 | CMReturn _=>3 | CMExit _=>4 | CMError _=>5 end.
Definition cm_control_value ctl := match ctl with CMReturn v=>v | CMExit status | CMError status=>CMIntV status | _=>CMIntV 0 end.
Definition cm_control_status ctl := match ctl with CMNormal | CMReturn _=>0 | CMExit status=>status | _=>2 end.
Definition cm_local_slot_ok sp p fid slot := (0 <=? fid) && (fid <? Zlength (cm_program_functions p)) &&
 (0 <=? slot) && (slot <? Zlength (cm_function_locals (cm_source_function_at sp fid p))).
Definition cm_stmt_start_safe sp p fid stmt := match stmt with CMDeclS slot | CMInitS slot _=>cm_local_slot_ok sp p fid slot | _=>true end.
Definition cm_sstart sp p fid stmt st ks := match stmt with
 | CMSkipS => CMCTask p fid CMNormal st ks
 | CMExprS expr => CMRTask p fid expr st (CMExprStmtK :: ks)
 | CMDeclS slot => if cm_local_slot_ok sp p fid slot then CMCTask p fid CMNormal (cm_activate_local sp p fid slot st) ks else CMCTask p fid (CMError 1) st ks
 | CMInitS slot expr => if cm_local_slot_ok sp p fid slot then CMRTask p fid expr (cm_activate_local sp p fid slot st) (CMInitK slot :: ks) else CMCTask p fid (CMError 1) st ks
 | CMSeqS first second => CMSTask p fid first st (CMSeqK second :: ks)
 | CMBlockS body => CMSTask p fid body st (CMBlockK (cm_state_env st) (cm_state_regions st) :: ks)
 | CMIfS guard yes no => CMRTask p fid guard st (CMIfK yes no :: ks)
 | CMWhileS guard body => CMRTask p fid guard st (CMWhileGuardK guard body :: ks)
 | CMBreakS => CMCTask p fid CMBreak st ks
 | CMContinueS => CMCTask p fid CMContinue st ks
 | CMReturnS expr => CMRTask p fid expr st (CMReturnK :: ks) end.
Definition cm_vapply sp p fid frame v st ks := match frame with
 | CMHaltK => CMDoneTask st (CMReturn v) (tower_status (cm_value_number st v))
 | CMLoadK ty => if cm_load_ok ty v st then CMVTask p fid (cm_load_value ty v st) st ks else CMCTask p fid (CMError 1) st ks
 | CMAssignLK src ty => CMRTask p fid src st (CMAssignRK v ty :: ks)
 | CMAssignRK ptr ty => if cm_store_ok ty ptr st then CMVTask p fid (cm_convert_value st ty v) (cm_state_store ty ptr v st) ks else CMCTask p fid (CMError 1) st ks
 | CMBinLK op rhs ty => if (op =? 0) && cm_truth st v then CMVTask p fid (CMIntV 1) st ks
   else if (op =? 1) && negb (cm_truth st v) then CMVTask p fid (CMIntV 0) st ks
   else CMRTask p fid rhs st (CMBinRK op v ty :: ks)
 | CMBinRK op lhs ty => if cm_binary_ok p op lhs v st then CMVTask p fid (cm_binary_value p op lhs v ty st) st ks else CMCTask p fid (CMError 1) st ks
 | CMUnaryK op => CMVTask p fid (cm_unary_value op v st) st ks
 | CMIndexLK index ty => CMRTask p fid index st (CMIndexRK v ty :: ks)
 | CMIndexRK base ty => if cm_ptr_shift_ok (cm_program_structs p) base (cm_value_number st v) st then CMVTask p fid (cm_ptr_add (cm_program_structs p) base (cm_value_number st v)) st ks else CMCTask p fid (CMError 1) st ks
 | CMMemberK mid => if cm_ptr_member_ok sp p v mid st then CMVTask p fid (cm_ptr_member sp p v mid) st ks else CMCTask p fid (CMError 1) st ks
 | CMPutcK => CMVTask p fid (CMIntV (cm_value_number st v)) (cm_state_io st (cm_state_input st) (cm_state_output st ++ [tower_u8 (cm_value_number st v)])) ks
 | CMPutiK => CMVTask p fid (CMIntV (cm_value_number st v)) (cm_state_io st (cm_state_input st) (cm_state_output st ++ tower_decimal (cm_value_number st v))) ks
 | CMExitK => CMCTask p fid (CMExit (tower_status (cm_value_number st v))) st ks
 | CMExprStmtK => CMCTask p fid CMNormal st ks
 | CMInitK slot => let ty:=cm_slot_ty (cm_source_slot_at sp slot (cm_function_locals (cm_source_function_at sp fid p))) in
   if cm_binding_address_ok sp p fid 1 slot st && cm_store_ok ty (cm_state_env st 1 slot) st then CMCTask p fid CMNormal (cm_state_store ty (cm_state_env st 1 slot) v st) ks else CMCTask p fid (CMError 1) st ks
 | CMBlockK oldenv oldregions => CMCTask p fid (CMError 1) (cm_restore_scope st oldenv oldregions) ks
 | CMSeqK second => CMCTask p fid (CMError 1) st ks
 | CMIfK yes no => CMSTask p fid (if cm_truth st v then yes else no) st (CMBlockK (cm_state_env st) (cm_state_regions st) :: ks)
 | CMWhileGuardK guard body => if cm_truth st v then CMSTask p fid body st (CMWhileBodyK guard body (cm_state_env st) (cm_state_regions st) :: ks) else CMCTask p fid CMNormal st ks
 | CMWhileBodyK guard body oldenv oldregions => CMCTask p fid (CMError 1) (cm_restore_scope st oldenv oldregions) ks
 | CMReturnK => CMCTask p fid (CMReturn v) st ks
 | CMArgK callee rest values ret => match rest with []=>cm_begin_call sp p fid callee (rev (v::values)) st ret ks
    | arg::args=>CMRTask p fid arg st (CMArgK callee args (v::values) ret :: ks) end
 | CMCallK caller oldenv oldfp oldregions ret => CMCTask p fid (CMError 1) st ks end.
Definition cm_capply (sp:cm_source_lookup_policy) p fid frame ctl st ks := match frame with
 | CMHaltK => CMDoneTask st ctl (if cm_control_kind ctl =? 4 then cm_control_status ctl
   else if cm_control_kind ctl =? 3 then tower_status (cm_value_number st (cm_control_value ctl)) else if cm_control_kind ctl =? 0 then 0 else 2)
 | CMBlockK oldenv oldregions => CMCTask p fid ctl (cm_restore_scope st oldenv oldregions) ks
 | CMSeqK second => if cm_control_kind ctl =? 0 then CMSTask p fid second st ks else CMCTask p fid ctl st ks
 | CMWhileBodyK guard body oldenv oldregions =>
   if (cm_control_kind ctl =? 0) || (cm_control_kind ctl =? 2) then CMRTask p fid guard (cm_restore_scope st oldenv oldregions) (CMWhileGuardK guard body :: ks)
   else if cm_control_kind ctl =? 1 then CMCTask p fid CMNormal (cm_restore_scope st oldenv oldregions) ks
   else CMCTask p fid ctl (cm_restore_scope st oldenv oldregions) ks
 | CMCallK caller oldenv oldfp oldregions ret =>
   if cm_control_kind ctl =? 3 then CMVTask p caller (cm_convert_value (cm_restore_call st oldenv oldfp oldregions) ret (cm_control_value ctl)) (cm_restore_call st oldenv oldfp oldregions) ks
   else if cm_control_kind ctl =? 0 then CMVTask p caller (cm_convert_value (cm_restore_call st oldenv oldfp oldregions) ret (CMIntV 0)) (cm_restore_call st oldenv oldfp oldregions) ks
   else CMCTask p caller ctl (cm_restore_call st oldenv oldfp oldregions) ks
 | _=>CMCTask p fid ctl st ks end.
Definition cm_step sp task := match task with
 | CMStartTask p input => cm_begin_call sp p (-1) (cm_program_main p) [] (cm_initial_state sp p input) CMIntTy [CMHaltK]
 | CMRTask p fid expr st ks => cm_rstart sp p fid expr st ks
 | CMLTask p fid expr st ks => cm_lstart sp p fid expr st ks
 | CMSTask p fid stmt st ks => cm_sstart sp p fid stmt st ks
 | CMVTask p fid v st ks => match ks with []=>CMDoneTask st (CMError 2) 2 | k::rest=>cm_vapply sp p fid k v st rest end
 | CMCTask p fid ctl st ks => if cm_control_kind ctl =? 4 then CMDoneTask st ctl (cm_control_status ctl)
   else match ks with []=>if cm_control_kind ctl =? 5 then CMDoneTask st ctl (cm_control_status ctl) else CMDoneTask st (CMError 2) 2
   | k::rest=>cm_capply sp p fid k ctl st rest end
 | CMDoneTask st ctl status => CMDoneTask st ctl status end.
Definition cm_task_done task := match task with CMDoneTask _ _ _=>true | _=>false end.
Definition cm_task_outcome sp task := match task with
 | CMStartTask p input => CMOutcome (cm_initial_state sp p input) (CMError 2) 2
 | CMDoneTask st ctl status => CMOutcome st ctl status
 | CMRTask _ _ _ st _ | CMLTask _ _ _ st _ | CMSTask _ _ _ st _ | CMVTask _ _ _ st _ | CMCTask _ _ _ st _ => CMOutcome st (CMError 2) 2 end.
Fixpoint cm_iter sp n task := match n with O=>task | S k=>cm_iter sp k (cm_step sp task) end.
Definition cm_exec_closed sp (P:cm_task->cm_outcome->Prop) :=
 (forall st ctl status, P (CMDoneTask st ctl status) (CMOutcome st ctl status)) /\
 (forall task out, P (cm_step sp task) out -> P task out).
Definition cm_exec sp task out := forall P, cm_exec_closed sp P -> P task out.
Definition cm_outcome_state out := match out with CMOutcome st _ _=>st end.
Definition cm_outcome_control out := match out with CMOutcome _ ctl _=>ctl end.
Definition cm_outcome_status out := match out with CMOutcome _ _ status=>status end.
Definition cm_valid_input input := Forall tower_byte_value input.
Definition cm_success_control ctl := cm_control_kind ctl=3 \/ cm_control_kind ctl=4.
Definition cm_source_terminates sp p input output status := cm_valid_input input /\ tower_byte_value status /\
 exists st ctl, cm_exec sp (CMStartTask p input) (CMOutcome st ctl status) /\ cm_success_control ctl /\ cm_state_output st=output.
Lemma cm_exec_done sp st ctl status : cm_exec sp (CMDoneTask st ctl status) (CMOutcome st ctl status).
Proof. intros P [Hdone Hstep]; apply Hdone. Qed.
Lemma cm_exec_rule sp task out : cm_exec sp (cm_step sp task) out -> cm_exec sp task out.
Proof. intros H P [Hdone Hstep]; apply Hstep; apply H; split; assumption. Qed.
Lemma cm_iter_done sp n st ctl status : cm_iter sp n (CMDoneTask st ctl status)=CMDoneTask st ctl status.
Proof. induction n; cbn; auto. Qed.
Lemma cm_iter_add sp m n task : cm_iter sp (m+n) task=cm_iter sp n (cm_iter sp m task).
Proof. revert task; induction m; intros; cbn; auto. Qed.
Lemma cm_exec_prefix sp n task out : cm_exec sp (cm_iter sp n task) out -> cm_exec sp task out.
Proof. revert task; induction n; intros task H; cbn in H; [exact H|apply cm_exec_rule; now apply IHn]. Qed.
Lemma cm_exec_witness sp task out : cm_exec sp task out <->
 exists n st ctl status, cm_iter sp n task=CMDoneTask st ctl status /\ out=CMOutcome st ctl status.
Proof.
 split.
 - intros H. apply (H (fun task out=>exists n st ctl status, cm_iter sp n task=CMDoneTask st ctl status /\ out=CMOutcome st ctl status)).
   split.
   + intros; exists O,st,ctl,status; split; reflexivity.
   + intros task0 out0 [n [st [ctl [status [Hn Ho]]]]]; exists (S n),st,ctl,status; auto.
 - intros [n [st [ctl [status [Hn ->]]]]]. apply (cm_exec_prefix sp n). rewrite Hn; apply cm_exec_done.
Qed.
Lemma cm_exec_deterministic sp task out1 out2 : cm_exec sp task out1 -> cm_exec sp task out2 -> out1=out2.
Proof.
 intros H1 H2. apply cm_exec_witness in H1; apply cm_exec_witness in H2.
 destruct H1 as [m [st1 [ctl1 [s1 [H1 E1]]]]]; destruct H2 as [n [st2 [ctl2 [s2 [H2 E2]]]]].
 destruct (le_dec m n).
 - replace n with (m+(n-m))%nat in H2 by lia; rewrite cm_iter_add,H1,cm_iter_done in H2; inversion H2; subst; reflexivity.
 - replace m with (n+(m-n))%nat in H1 by lia; rewrite cm_iter_add,H2,cm_iter_done in H1; inversion H1; subst; reflexivity.
Qed.
Lemma cm_exec_step_inv sp task out : cm_exec sp task out -> cm_exec sp (cm_step sp task) out.
Proof.
 intro H; apply cm_exec_witness in H; destruct H as [[|n] [st [ctl [status [H ->]]]]].
 - cbn in H; subst; apply cm_exec_done.
 - apply cm_exec_witness; exists n,st,ctl,status; auto.
Qed.
Lemma cm_valid_input_bridge input : cm_valid_input input -> tvm_valid_input input.
Proof. exact (fun H=>H). Qed.
