Require Export SimpleC.EE.QCP_demos_human.cmc_code_control_basic_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_code_value_branch_migration_lib.
From Coq Require Import ZArith List Bool Lia.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_c_while_layout_step sp ap p fid ctl st guard body env regions loop_start loop_end pc temp b c owner ob oc tail spills saved calls :
 let phase:=CAWhileBodyP guard body env regions loop_start loop_end in
 let ann:=CMAnnotation pc temp b c (CMACursor phase owner ob oc::tail) spills saved calls in
 cm_control_kind ctl<>4 -> cm_control_kind ctl<>5 ->
 loop_end=loop_start+cm_rvalue_code_count(cm_source_function_policy sp)p fid guard+1+cm_stmt_code_count(cm_source_function_policy sp)p fid body+1 ->
 cm_task_layout sp ap p (CMCTask p fid ctl st (cm_cursor_frames(cm_ann_cursors ann))) ann ->
 cm_task_layout sp ap p (cm_capply sp p fid (cm_phase_frame phase) ctl st (cm_cursor_frames tail)) (cm_update_annotation(cm_update_c sp ap p fid ctl st ann phase)).
Proof.
 cbn zeta; intros NE ERR END [CODE [SITES SAVED]]; destruct ctl; cbn[cm_control_kind]in *; try contradiction; cm_code_control_reduce; split; try(split; [exact SITES|exact SAVED]); try exact SAVED.
 - destruct SITES as [SITE _]; cm_code_layout_lengths; rewrite END in *; cm_code_layout_equal SITE.
 - pose proof(proj2 SITES)as SITE; destruct tail; exact SITE.
 - destruct SITES as [SITE _]; cm_code_layout_lengths; rewrite END in *; cm_code_layout_equal SITE.
 - exact CODE.
Qed.
Lemma cm_c_call_layout_step sp ap p fid ctl st caller env fp regions ret pc temp b c owner ob oc tail spills saved calls :
 let phase:=CACallP caller env fp regions ret in
 let ann:=CMAnnotation pc temp b c (CMACursor phase owner ob oc::tail) spills saved calls in
 (cm_control_kind ctl=0 \/ cm_control_kind ctl=3) ->
 cm_task_layout sp ap p (CMCTask p fid ctl st (cm_cursor_frames(cm_ann_cursors ann))) ann ->
 cm_task_layout sp ap p (cm_capply sp p fid (cm_phase_frame phase) ctl st (cm_cursor_frames tail)) (cm_update_annotation(cm_update_c sp ap p fid ctl st ann phase)).
Proof.
 cbn zeta; intros KIND [CODE [[NONEMPTY RETURN] SAVED]]; destruct ctl; cbn[cm_control_kind]in KIND; try lia; cm_code_control_reduce; split; assumption.
Qed.
