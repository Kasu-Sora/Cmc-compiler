Require Export SimpleC.EE.QCP_demos_human.cmc_preservation_observation_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
(* HOL's total HD [] remains an arbitrary interpretation parameter. *)
Record cm_annotation_policy := CMAnnotationPolicy {
 cm_cursor_nil : cm_acursor;
 cm_saved_nil : cm_spill_frame;
 cm_call_nil : cm_call_sim_frame
}.
Definition cm_list_empty {A:Type} (xs:list A) := match xs with []=>true | _=>false end.
Definition cm_phase_frame phase := match phase with
 | CAHaltP=>CMHaltK | CALoadP ty=>CMLoadK ty
 | CAAssignLP e ty=>CMAssignLK e ty | CAAssignRP v ty=>CMAssignRK v ty
 | CABinLP op lhs rhs ty=>CMBinLK op rhs ty | CABinRP op lhs rhs v ty=>CMBinRK op v ty
 | CAUnaryP op=>CMUnaryK op | CAIndexLP e ty=>CMIndexLK e ty | CAIndexRP v ty=>CMIndexRK v ty
 | CAMemberP mid ty=>CMMemberK mid | CAPutcP=>CMPutcK | CAPutiP=>CMPutiK
 | CAExitP=>CMExitK | CAExprStmtP=>CMExprStmtK | CAInitP slot=>CMInitK slot
 | CABlockP env regions jump target=>CMBlockK env regions | CASeqP s=>CMSeqK s
 | CAIfP yes no=>CMIfK yes no | CAWhileGuardP guard body start finish=>CMWhileGuardK guard body
 | CAWhileBodyP guard body env regions start finish=>CMWhileBodyK guard body env regions
 | CAReturnP=>CMReturnK | CAArgP callee rest values ret args base current scratch=>CMArgK callee rest values ret
 | CACallP caller env fp regions ret=>CMCallK caller env fp regions ret end.
Definition cm_cursor_phase cursor := match cursor with CMACursor phase _ _ _=>phase end.
Definition cm_cursor_temp cursor := match cursor with CMACursor _ temp _ _=>temp end.
Definition cm_cursor_break cursor := match cursor with CMACursor _ _ b _=>b end.
Definition cm_cursor_continue cursor := match cursor with CMACursor _ _ _ c=>c end.
Definition cm_cursor_frames cursors := map (fun c=>cm_phase_frame (cm_cursor_phase c)) cursors.
Definition cm_code_steps (code:list tvm_inst) := Z.to_nat (Zlength code).
Definition cm_ann_plain pc temp breakpc continuepc ann := CMAnnotation pc temp breakpc continuepc
 (cm_ann_cursors ann) (cm_ann_spills ann) (cm_ann_saved ann) (cm_ann_calls ann).
Definition cm_ann_done ann := CMAnnotation (cm_ann_pc ann) (cm_ann_temp ann) (cm_ann_break ann) (cm_ann_continue ann)
 [] (cm_ann_spills ann) (cm_ann_saved ann) (cm_ann_calls ann).
Definition cm_ann_linear (code:list tvm_inst) ann := cm_ann_plain (cm_ann_pc ann+Zlength code) (cm_ann_temp ann) (cm_ann_break ann) (cm_ann_continue ann) ann.
Definition cm_ann_push phase pc temp breakpc continuepc ann := CMAnnotation pc temp breakpc continuepc
 (CMACursor phase (cm_ann_temp ann) (cm_ann_break ann) (cm_ann_continue ann)::cm_ann_cursors ann)
 (cm_ann_spills ann) (cm_ann_saved ann) (cm_ann_calls ann).
Definition cm_ann_replace ap phase pc temp breakpc continuepc ann :=
 let cursor:=hd (cm_cursor_nil ap) (cm_ann_cursors ann) in
 CMAnnotation pc temp breakpc continuepc
 (CMACursor phase (cm_cursor_temp cursor) (cm_cursor_break cursor) (cm_cursor_continue cursor)::tl (cm_ann_cursors ann))
 (cm_ann_spills ann) (cm_ann_saved ann) (cm_ann_calls ann).
Definition cm_ann_pop ap pc ann := let cursor:=hd (cm_cursor_nil ap) (cm_ann_cursors ann) in
 CMAnnotation pc (cm_cursor_temp cursor) (cm_cursor_break cursor) (cm_cursor_continue cursor)
 (tl (cm_ann_cursors ann)) (cm_ann_spills ann) (cm_ann_saved ann) (cm_ann_calls ann).
Definition cm_ann_spills_set spills ann := CMAnnotation (cm_ann_pc ann) (cm_ann_temp ann) (cm_ann_break ann) (cm_ann_continue ann)
 (cm_ann_cursors ann) spills (cm_ann_saved ann) (cm_ann_calls ann).
Fixpoint cm_spill_remove slot spills := match spills with []=>[] | spill::rest=>
 if cm_spill_slot spill =? slot then cm_spill_remove slot rest else spill::cm_spill_remove slot rest end.
Definition cm_spill_put slot value spills := CMSpill slot value::cm_spill_remove slot spills.
Definition cm_call_body_pc sp p fid := cm_function_pc (cm_source_function_policy sp) p fid + cm_function_prologue_count (cm_source_function_at sp fid p).
Definition cm_ann_enter_call sp p caller callee st ret returnpc parent_temp parent_break parent_continue tail caller_spills saved calls :=
 CMAnnotation (cm_call_body_pc sp p callee) 0 0 0
 (CMACursor (CACallP caller (cm_state_env st) (cm_state_fp st) (cm_state_regions st) ret) parent_temp parent_break parent_continue::tail)
 [] (CMSpillFrame caller (cm_state_fp st) caller_spills::saved)
 (CMCallSimFrame (cm_state_fp st-cm_frame_size (cm_program_structs p) (cm_source_function_at sp callee p)) (cm_state_fp st) returnpc::calls).
Definition cm_assign_tail_code policy p fid ty temp := cm_char_normalize_code ty ++ cm_temp_load_code policy p fid temp ++ cm_store_code ty ++ cm_temp_load_code policy p fid temp ++ cm_load_code ty.
Definition cm_index_tail_code policy p fid ty temp := [TVMInst TVMPushOp (cm_type_size (cm_program_structs p) ty);TVMInst TVMMulOp 0] ++ cm_temp_load_code policy p fid temp ++ [TVMInst TVMAddOp 0].
Definition cm_member_tail_code p base_ty mid := [TVMInst TVMPushOp (cm_member_offset (cm_program_structs p) (cm_struct_id (cm_pointee base_ty)) mid); TVMInst TVMAddOp 0].
Definition cm_init_tail_code sp p fid slot :=
 let ty:=cm_slot_ty (cm_source_slot_at sp slot (cm_function_locals (cm_source_function_at sp fid p))) in
 cm_char_normalize_code ty ++ cm_fp_relative_address_code (cm_local_offset (cm_source_function_policy sp) p fid slot) ++ cm_store_code ty.
Definition cm_status_tail_code := cm_char_normalize_code CMCharTy ++ [TVMInst TVMHaltOp 0].
Definition cm_return_tail_code sp p fid := cm_char_normalize_code (cm_function_ret (cm_source_function_at sp fid p)) ++ cm_return_epilogue.
Definition cm_fallthrough_tail_code := [TVMInst TVMPushOp 0] ++ cm_return_epilogue.
Definition cm_arg_final_code policy p caller callee all_args base_slot current_slot := cm_temp_store_code policy p caller current_slot ++ cm_emit_args_reload policy p caller base_slot all_args ++ [TVMInst TVMCallOp (cm_function_pc policy p callee)] ++ cm_emit_prologue policy p callee.
Definition cm_ann_put_spill slot value ann := cm_ann_spills_set (cm_spill_put slot value (cm_ann_spills ann)) ann.
Definition cm_ann_leave_call ap returnpc ann :=
 let cursor:=hd (cm_cursor_nil ap) (cm_ann_cursors ann) in
 CMAnnotation returnpc (cm_cursor_temp cursor) (cm_cursor_break cursor) (cm_cursor_continue cursor)
 (tl (cm_ann_cursors ann)) (cm_spill_frame_spills (hd (cm_saved_nil ap) (cm_ann_saved ann)))
 (tl (cm_ann_saved ann)) (tl (cm_ann_calls ann)).
Lemma cm_cursor_frames_app xs ys : cm_cursor_frames (xs++ys)=cm_cursor_frames xs++cm_cursor_frames ys.
Proof. apply map_app. Qed.
Lemma cm_cursor_frames_nil xs : cm_cursor_frames xs=[] <-> xs=[].
Proof. destruct xs; cbn; split; intros; auto; discriminate. Qed.
Lemma cm_phase_frame_halt phase : cm_phase_frame phase=CMHaltK <-> phase=CAHaltP.
Proof. destruct phase; cbn; split; intros; auto; discriminate. Qed.
Lemma cm_spill_remove_other slot s spills : cm_spill_slot s<>slot -> (In s (cm_spill_remove slot spills) <-> In s spills).
Proof. intro H; induction spills as [|a xs IH]; cbn; [tauto|]. destruct (cm_spill_slot a =? slot) eqn:E; [apply Z.eqb_eq in E; rewrite IH; split; [auto|intros [->|H0]; [contradiction|exact H0]]|cbn; tauto]. Qed.
Lemma cm_spill_remove_absent slot spills : forall s, In s (cm_spill_remove slot spills) -> cm_spill_slot s<>slot.
Proof. induction spills as [|a xs IH]; cbn; intros s H; [contradiction|]. destruct (cm_spill_slot a =? slot) eqn:E; [eauto|]. destruct H as [<-|H]; [now apply Z.eqb_neq|eauto]. Qed.
Lemma cm_spill_put_holds slot v spills : cm_spill_holds slot v (cm_spill_put slot v spills).
Proof. cbn; rewrite Z.eqb_refl; reflexivity. Qed.
Lemma cm_spill_put_unique slot v spills s : In s (cm_spill_put slot v spills) -> cm_spill_slot s=slot -> s=CMSpill slot v.
Proof. intros [<-|H] E; [reflexivity|exfalso; exact (cm_spill_remove_absent slot spills s H E)]. Qed.
