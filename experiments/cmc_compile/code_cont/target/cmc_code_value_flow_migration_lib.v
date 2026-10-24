Require Export SimpleC.EE.QCP_demos_human.cmc_code_value_linear_migration_lib.
From Coq Require Import ZArith List Bool Lia.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_v_assign_l_layout_step sp ap p fid v st src ty pc temp b c owner ob oc tail spills saved calls :
 let ann:=CMAnnotation pc temp b c (CMACursor (CAAssignLP src ty) owner ob oc::tail) spills saved calls in
 temp=owner -> cm_task_layout sp ap p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) ann ->
 cm_task_layout sp ap p (cm_vapply sp p fid (CMAssignLK src ty) v st (cm_cursor_frames tail)) (cm_update_annotation(cm_update_v sp ap p fid v st ann (CAAssignLP src ty))).
Proof.
 cbn zeta; intros -> [CODE [_ SAVED]]; cm_code_value_reduce; split; [|split; [exact I|exact SAVED]].
 repeat rewrite <-app_assoc in CODE; apply cm_code_at_append_right in CODE.
 match type of CODE with cm_code_at ?c ?pc ?old=>match goal with |-cm_code_at _ _ ?new=>replace new with old; [exact CODE|] end end.
 repeat rewrite Zlength_app; rewrite cm_layout_rvalue_code_length; repeat rewrite <-app_assoc; repeat rewrite Z.add_assoc; reflexivity.
Qed.
Lemma cm_v_index_l_layout_step sp ap p fid v st index ty pc temp b c owner ob oc tail spills saved calls :
 let ann:=CMAnnotation pc temp b c (CMACursor (CAIndexLP index ty) owner ob oc::tail) spills saved calls in
 temp=owner -> cm_task_layout sp ap p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) ann ->
 cm_task_layout sp ap p (cm_vapply sp p fid (CMIndexLK index ty) v st (cm_cursor_frames tail)) (cm_update_annotation(cm_update_v sp ap p fid v st ann (CAIndexLP index ty))).
Proof.
 cbn zeta; intros -> [CODE [_ SAVED]]; cm_code_value_reduce; split; [|split; [exact I|exact SAVED]].
 repeat rewrite <-app_assoc in CODE; apply cm_code_at_append_right in CODE.
 match type of CODE with cm_code_at ?c ?pc ?old=>match goal with |-cm_code_at _ _ ?new=>replace new with old; [exact CODE|] end end.
 repeat rewrite Zlength_app; rewrite cm_layout_rvalue_code_length; repeat rewrite <-app_assoc; repeat rewrite Z.add_assoc; reflexivity.
Qed.
Lemma cm_v_init_layout_step sp ap p fid v st slot pc temp b c owner ob oc tail spills saved calls :
 let ann:=CMAnnotation pc temp b c (CMACursor (CAInitP slot) owner ob oc::tail) spills saved calls in
 cm_task_layout sp ap p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) ann ->
 cm_task_layout sp ap p (cm_vapply sp p fid (CMInitK slot) v st (cm_cursor_frames tail)) (cm_update_annotation(cm_update_v sp ap p fid v st ann (CAInitP slot))).
Proof.
 cbn zeta; intros [CODE [_ SAVED]]; cm_code_value_reduce.
 destruct (cm_binding_address_ok sp p fid 1 slot st && cm_store_ok (cm_slot_ty (cm_source_slot_at sp slot (cm_function_locals (cm_source_function_at sp fid p)))) (cm_state_env st 1 slot) st); cm_code_value_reduce; rewrite ?cm_error_control_code; split; [apply cm_code_at_append_right in CODE; exact CODE|exact SAVED|apply cm_code_at_append_right in CODE; exact CODE|exact SAVED].
Qed.
Lemma cm_v_return_layout_step sp ap p fid v st pc temp b c owner ob oc tail spills saved calls :
 let ann:=CMAnnotation pc temp b c (CMACursor CAReturnP owner ob oc::tail) spills saved calls in
 cm_task_layout sp ap p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) ann ->
 cm_task_layout sp ap p (cm_vapply sp p fid CMReturnK v st (cm_cursor_frames tail)) (cm_update_annotation(cm_update_v sp ap p fid v st ann CAReturnP)).
Proof. cbn zeta; intros [CODE [_ SAVED]]; cm_code_value_reduce; split; [|exact SAVED]. rewrite app_nil_r in CODE; exact CODE. Qed.
Lemma cm_v_halt_layout_step sp ap p fid v st pc temp b c owner ob oc tail spills saved calls :
 let ann:=CMAnnotation pc temp b c (CMACursor CAHaltP owner ob oc::tail) spills saved calls in
 cm_task_layout sp ap p (cm_vapply sp p fid CMHaltK v st (cm_cursor_frames tail)) (cm_update_annotation(cm_update_v sp ap p fid v st ann CAHaltP)).
Proof. exact I. Qed.
Lemma cm_v_exit_layout_step sp ap p fid v st pc temp b c owner ob oc tail spills saved calls :
 let ann:=CMAnnotation pc temp b c (CMACursor CAExitP owner ob oc::tail) spills saved calls in
 cm_task_layout sp ap p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) ann ->
 cm_task_layout sp ap p (cm_vapply sp p fid CMExitK v st (cm_cursor_frames tail)) (cm_update_annotation(cm_update_v sp ap p fid v st ann CAExitP)).
Proof.
 cbn zeta; intros [CODE [_ SAVED]]; cm_code_value_reduce; split; [|exact SAVED].
 apply cm_code_at_empty; pose proof(cm_code_at_bounds _ _ _ CODE) as B.
 unfold cm_status_tail_code in B; repeat rewrite Zlength_app in B; rewrite cm_layout_char_normalize_length in *; cbn [cm_char_normalize_count] in *; change(Zlength[TVMInst TVMHaltOp 0])with 1 in B; rewrite Zlength_nil in B; lia.
Qed.
