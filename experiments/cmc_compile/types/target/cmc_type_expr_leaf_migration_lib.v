Require Export SimpleC.EE.QCP_demos_human.cmc_type_control_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_type_args_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_r_type_yield policy nilslot p fid expr st ks ann v out outks outann :
 cm_task_type_ready policy nilslot p (CMRTask p fid expr st ks) ann -> cm_expr_value_type_ready expr v -> cm_ann_cursors outann=cm_ann_cursors ann ->
 cm_task_type_ready policy nilslot p (CMVTask p fid v out outks) outann.
Proof. intros [_ [_ [_ [_ [_ [CT [_ VALUES]]]]]]] V C; split; [reflexivity|]; rewrite C; split; [exact CT|now apply VALUES]. Qed.
Lemma cm_type_error policy nilslot p fid st ks ann : cm_cursors_type_ready policy nilslot p fid (cm_ann_cursors ann) -> cm_task_type_ready policy nilslot p (CMCTask p fid (CMError 1) st ks) ann.
Proof. intro CT; split; [reflexivity|split; [exact I|exact CT]]. Qed.
Lemma cm_r_const_type_ready_step sp ap nilslot p fid n ty st ks ann :
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (CMRTask p fid (CMConstE n ty) st ks) ann ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (cm_rstart sp p fid (CMConstE n ty) st ks) (cm_update_annotation (cm_update_r sp ap p fid st ann (CMConstE n ty))).
Proof. intro H; eapply cm_r_type_yield; [exact H|apply cm_const_expr_value_ready; exact (proj1 (proj2 (proj2 (proj2 H))))|reflexivity]. Qed.
Lemma cm_r_string_type_ready_step sp ap nilslot p fid sid ty st ks ann :
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (CMRTask p fid (CMStringE sid ty) st ks) ann ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (cm_rstart sp p fid (CMStringE sid ty) st ks) (cm_update_annotation (cm_update_r sp ap p fid st ann (CMStringE sid ty))).
Proof.
 intro H; eapply cm_r_type_yield; [exact H| |reflexivity]. apply cm_expr_not_zero_ready; [discriminate|].
 pose proof (proj1 (proj2 (proj2 (proj2 H)))) as [_ ->]; left; reflexivity.
Qed.
Lemma cm_r_sizeof_type_ready_step sp ap nilslot p fid asked ty st ks ann :
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (CMRTask p fid (CMSizeofE asked ty) st ks) ann ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (cm_rstart sp p fid (CMSizeofE asked ty) st ks) (cm_update_annotation (cm_update_r sp ap p fid st ann (CMSizeofE asked ty))).
Proof.
 intro H; eapply cm_r_type_yield; [exact H| |reflexivity]. apply cm_expr_not_zero_ready; [discriminate|].
 pose proof (proj1 (proj2 (proj2 (proj2 H)))) as [_ [_ ->]]; left; reflexivity.
Qed.
Lemma cm_r_getc_type_ready_step sp ap nilslot p fid ty st ks ann :
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (CMRTask p fid (CMGetcE ty) st ks) ann ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (cm_rstart sp p fid (CMGetcE ty) st ks) (cm_update_annotation (cm_update_r sp ap p fid st ann (CMGetcE ty))).
Proof.
 intro H; pose proof (proj1 (proj2 (proj2 (proj2 H)))) as TY; change (ty=CMIntTy) in TY.
 cbn [cm_rstart]; destruct (cm_state_input st); [|destruct (tower_byte_valueb z)].
 all: try solve [eapply cm_r_type_yield; [exact H|apply cm_expr_not_zero_ready; [discriminate|rewrite TY; left; reflexivity]|reflexivity]].
 apply cm_type_error; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))).
Qed.
