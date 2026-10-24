Require Export SimpleC.EE.QCP_demos_human.cmc_code_layout_facts_migration_lib.
From Coq Require Import ZArith List Bool Lia.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_layout_rvalue_linear sp ap p fid expr st ks ann out st' :
 cm_task_layout sp ap p (CMRTask p fid expr st ks) ann ->
 cm_task_layout sp ap p (CMVTask p fid out st' ks) (cm_ann_linear (cm_emit_rvalue (cm_source_function_policy sp) p fid (cm_ann_pc ann) (cm_ann_temp ann) expr) ann).
Proof.
 intros [CODE SAVED]; split; [|exact SAVED].
 cbn [cm_task_code] in CODE; cbn [cm_task_code cm_ann_linear cm_ann_plain cm_ann_pc cm_ann_temp cm_ann_cursors].
 rewrite <-(cm_layout_rvalue_code_length (cm_source_function_policy sp) p fid expr (cm_ann_pc ann) (cm_ann_temp ann)) in CODE; now apply cm_code_at_append_right in CODE.
Qed.
Lemma cm_r_const_layout_step sp ap p fid n ty st ks ann : cm_task_layout sp ap p (CMRTask p fid (CMConstE n ty) st ks) ann ->
 cm_task_layout sp ap p (cm_rstart sp p fid (CMConstE n ty) st ks) (cm_update_annotation (cm_update_r sp ap p fid st ann (CMConstE n ty))).
Proof. intro H; exact (cm_layout_rvalue_linear sp ap p fid (CMConstE n ty) st ks ann _ _ H). Qed.
Lemma cm_r_string_layout_step sp ap p fid sid ty st ks ann : cm_task_layout sp ap p (CMRTask p fid (CMStringE sid ty) st ks) ann ->
 cm_task_layout sp ap p (cm_rstart sp p fid (CMStringE sid ty) st ks) (cm_update_annotation (cm_update_r sp ap p fid st ann (CMStringE sid ty))).
Proof. intro H; exact (cm_layout_rvalue_linear sp ap p fid (CMStringE sid ty) st ks ann _ _ H). Qed.
Lemma cm_r_sizeof_layout_step sp ap p fid asked ty st ks ann : cm_task_layout sp ap p (CMRTask p fid (CMSizeofE asked ty) st ks) ann ->
 cm_task_layout sp ap p (cm_rstart sp p fid (CMSizeofE asked ty) st ks) (cm_update_annotation (cm_update_r sp ap p fid st ann (CMSizeofE asked ty))).
Proof. intro H; exact (cm_layout_rvalue_linear sp ap p fid (CMSizeofE asked ty) st ks ann _ _ H). Qed.
Lemma cm_r_getc_layout_step sp ap p fid ty st ks ann : cm_task_succeeds sp (cm_rstart sp p fid (CMGetcE ty) st ks) -> cm_task_layout sp ap p (CMRTask p fid (CMGetcE ty) st ks) ann ->
 cm_task_layout sp ap p (cm_rstart sp p fid (CMGetcE ty) st ks) (cm_update_annotation (cm_update_r sp ap p fid st ann (CMGetcE ty))).
Proof.
 cbn [cm_rstart cm_update_r cm_update_annotation]; destruct (cm_state_input st) as [|b input]; [intros _ H; exact (cm_layout_rvalue_linear sp ap p fid (CMGetcE ty) st ks ann _ _ H)|].
 destruct (tower_byte_valueb b); [intros _ H; exact (cm_layout_rvalue_linear sp ap p fid (CMGetcE ty) st ks ann _ _ H)|].
 intros S _; exfalso; eapply cm_error_not_succeeds; eauto.
Qed.
