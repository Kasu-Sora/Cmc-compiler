Require Export SimpleC.EE.QCP_demos_human.cmc_code_value_helpers_migration_lib.
From Coq Require Import ZArith List Bool Lia.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_v_load_layout_step sp ap p fid v st ty pc temp b c owner ob oc tail spills saved calls :
 let ann:=CMAnnotation pc temp b c (CMACursor (CALoadP ty) owner ob oc::tail) spills saved calls in
 cm_load_ok ty v st=true ->
 cm_task_layout sp ap p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) ann ->
 cm_task_layout sp ap p (cm_vapply sp p fid (cm_phase_frame (CALoadP ty)) v st (cm_cursor_frames tail)) (cm_update_annotation(cm_update_v sp ap p fid v st ann (CALoadP ty))).
Proof.
 cbn zeta; intros OK [CODE [_ SAVED]]; cm_code_value_reduce; rewrite OK; cm_code_value_reduce; split; [|exact SAVED].
 apply cm_code_at_append_right in CODE; repeat rewrite Zlength_cons in CODE; rewrite ?Zlength_nil in CODE; exact CODE.
Qed.
Lemma cm_v_assign_r_layout_step sp ap p fid v st ptr ty pc temp b c owner ob oc tail spills saved calls :
 let ann:=CMAnnotation pc temp b c (CMACursor (CAAssignRP ptr ty) owner ob oc::tail) spills saved calls in
 cm_store_ok ty ptr st=true ->
 cm_task_layout sp ap p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) ann ->
 cm_task_layout sp ap p (cm_vapply sp p fid (cm_phase_frame (CAAssignRP ptr ty)) v st (cm_cursor_frames tail)) (cm_update_annotation(cm_update_v sp ap p fid v st ann (CAAssignRP ptr ty))).
Proof.
 cbn zeta; intros OK [CODE [_ SAVED]]; cm_code_value_reduce; rewrite OK; cm_code_value_reduce; split; [|exact SAVED].
 apply cm_code_at_append_right in CODE; repeat rewrite Zlength_cons in CODE; rewrite ?Zlength_nil in CODE; exact CODE.
Qed.
Lemma cm_v_unary_layout_step sp ap p fid v st op pc temp b c owner ob oc tail spills saved calls :
 let ann:=CMAnnotation pc temp b c (CMACursor (CAUnaryP op) owner ob oc::tail) spills saved calls in
 
 cm_task_layout sp ap p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) ann ->
 cm_task_layout sp ap p (cm_vapply sp p fid (cm_phase_frame (CAUnaryP op)) v st (cm_cursor_frames tail)) (cm_update_annotation(cm_update_v sp ap p fid v st ann (CAUnaryP op))).
Proof.
 cbn zeta; intros [CODE [_ SAVED]]; cm_code_value_reduce;  split; [|exact SAVED].
 apply cm_code_at_append_right in CODE; repeat rewrite Zlength_cons in CODE; rewrite ?Zlength_nil in CODE; exact CODE.
Qed.
Lemma cm_v_index_r_layout_step sp ap p fid v st base ty pc temp b c owner ob oc tail spills saved calls :
 let ann:=CMAnnotation pc temp b c (CMACursor (CAIndexRP base ty) owner ob oc::tail) spills saved calls in
 cm_ptr_shift_ok (cm_program_structs p) base (cm_value_number st v) st=true ->
 cm_task_layout sp ap p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) ann ->
 cm_task_layout sp ap p (cm_vapply sp p fid (cm_phase_frame (CAIndexRP base ty)) v st (cm_cursor_frames tail)) (cm_update_annotation(cm_update_v sp ap p fid v st ann (CAIndexRP base ty))).
Proof.
 cbn zeta; intros OK [CODE [_ SAVED]]; cm_code_value_reduce; rewrite OK; cm_code_value_reduce; split; [|exact SAVED].
 apply cm_code_at_append_right in CODE; repeat rewrite Zlength_cons in CODE; rewrite ?Zlength_nil in CODE; exact CODE.
Qed.
Lemma cm_v_member_layout_step sp ap p fid v st mid base_ty pc temp b c owner ob oc tail spills saved calls :
 let ann:=CMAnnotation pc temp b c (CMACursor (CAMemberP mid base_ty) owner ob oc::tail) spills saved calls in
 cm_ptr_member_ok sp p v mid st=true ->
 cm_task_layout sp ap p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) ann ->
 cm_task_layout sp ap p (cm_vapply sp p fid (cm_phase_frame (CAMemberP mid base_ty)) v st (cm_cursor_frames tail)) (cm_update_annotation(cm_update_v sp ap p fid v st ann (CAMemberP mid base_ty))).
Proof.
 cbn zeta; intros OK [CODE [_ SAVED]]; cm_code_value_reduce; rewrite OK; cm_code_value_reduce; split; [|exact SAVED].
 apply cm_code_at_append_right in CODE; repeat rewrite Zlength_cons in CODE; rewrite ?Zlength_nil in CODE; exact CODE.
Qed.
Lemma cm_v_putc_layout_step sp ap p fid v st  pc temp b c owner ob oc tail spills saved calls :
 let ann:=CMAnnotation pc temp b c (CMACursor (CAPutcP) owner ob oc::tail) spills saved calls in
 
 cm_task_layout sp ap p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) ann ->
 cm_task_layout sp ap p (cm_vapply sp p fid (cm_phase_frame (CAPutcP)) v st (cm_cursor_frames tail)) (cm_update_annotation(cm_update_v sp ap p fid v st ann (CAPutcP))).
Proof.
 cbn zeta; intros [CODE [_ SAVED]]; cm_code_value_reduce;  split; [|exact SAVED].
 apply cm_code_at_append_right in CODE; repeat rewrite Zlength_cons in CODE; rewrite ?Zlength_nil in CODE; exact CODE.
Qed.
Lemma cm_v_puti_layout_step sp ap p fid v st  pc temp b c owner ob oc tail spills saved calls :
 let ann:=CMAnnotation pc temp b c (CMACursor (CAPutiP) owner ob oc::tail) spills saved calls in
 
 cm_task_layout sp ap p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) ann ->
 cm_task_layout sp ap p (cm_vapply sp p fid (cm_phase_frame (CAPutiP)) v st (cm_cursor_frames tail)) (cm_update_annotation(cm_update_v sp ap p fid v st ann (CAPutiP))).
Proof.
 cbn zeta; intros [CODE [_ SAVED]]; cm_code_value_reduce;  split; [|exact SAVED].
 apply cm_code_at_append_right in CODE; repeat rewrite Zlength_cons in CODE; rewrite ?Zlength_nil in CODE; exact CODE.
Qed.
Lemma cm_v_expr_stmt_layout_step sp ap p fid v st  pc temp b c owner ob oc tail spills saved calls :
 let ann:=CMAnnotation pc temp b c (CMACursor (CAExprStmtP) owner ob oc::tail) spills saved calls in
 
 cm_task_layout sp ap p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) ann ->
 cm_task_layout sp ap p (cm_vapply sp p fid (cm_phase_frame (CAExprStmtP)) v st (cm_cursor_frames tail)) (cm_update_annotation(cm_update_v sp ap p fid v st ann (CAExprStmtP))).
Proof.
 cbn zeta; intros [CODE [_ SAVED]]; cm_code_value_reduce;  split; [|exact SAVED].
 apply cm_code_at_append_right in CODE; repeat rewrite Zlength_cons in CODE; rewrite ?Zlength_nil in CODE; exact CODE.
Qed.
