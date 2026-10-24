Require Export SimpleC.EE.QCP_demos_human.cmc_code_value_helpers_migration_lib.
From Coq Require Import ZArith List Bool Lia.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Ltac cm_code_layout_lengths := repeat rewrite Zlength_app in *; repeat rewrite cm_emit_stmt_length__stmt_capacity in *; repeat rewrite cm_layout_rvalue_code_length in *; repeat rewrite Zlength_cons in *; rewrite ?Zlength_nil in *.
Ltac cm_code_layout_equal CODE := match type of CODE with cm_code_at ?code ?oldpc ?old=>match goal with |-cm_code_at _ ?newpc _=>replace newpc with oldpc by lia end; match goal with |-cm_code_at _ _ ?new=>replace new with old; [exact CODE|]end end; unfold cm_normal_cont_code; repeat rewrite <-app_assoc; cbn [app]; repeat first[reflexivity|solve[lia]|progress f_equal].
Lemma cm_v_while_guard_layout_step sp ap p fid v st guard body loop_start loop_end pc temp b c owner ob oc tail spills saved calls :
 let ann:=CMAnnotation pc temp b c (CMACursor (CAWhileGuardP guard body loop_start loop_end) owner ob oc::tail) spills saved calls in
 cm_task_layout sp ap p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) ann ->
 cm_task_layout sp ap p (cm_vapply sp p fid (CMWhileGuardK guard body) v st (cm_cursor_frames tail)) (cm_update_annotation(cm_update_v sp ap p fid v st ann (CAWhileGuardP guard body loop_start loop_end))).
Proof.
 cbn zeta; intros [CODE [SITES SAVED]]; destruct(cm_truth st v)eqn:TRUTH; cm_code_value_reduce; rewrite TRUTH; cm_code_value_reduce; split; try(split; [exact SITES|exact SAVED]); try exact SAVED.
 - repeat rewrite <-app_assoc in CODE; apply cm_code_at_tail in CODE; cm_code_layout_lengths; cm_code_layout_equal CODE.
 - exact(proj2 SITES).
Qed.
Lemma cm_v_if_layout_step sp ap p fid v st yes no pc temp b c owner ob oc tail spills saved calls :
 let ann:=CMAnnotation pc temp b c (CMACursor (CAIfP yes no) owner ob oc::tail) spills saved calls in
 cm_task_layout sp ap p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) ann ->
 cm_task_layout sp ap p (cm_vapply sp p fid (CMIfK yes no) v st (cm_cursor_frames tail)) (cm_update_annotation(cm_update_v sp ap p fid v st ann (CAIfP yes no))).
Proof.
 cbn zeta; intros [CODE [_ SAVED]]; destruct(cm_truth st v)eqn:TRUTH; cm_code_value_reduce; rewrite TRUTH; cm_code_value_reduce.
 - pose proof CODE as END; apply cm_code_at_append_right in END; cm_code_layout_lengths.
   split; [|split; [right; cm_code_layout_equal END|exact SAVED]].
   repeat rewrite <-app_assoc in CODE; apply cm_code_at_tail in CODE.
   fold app in CODE; cbn [app] in CODE; fold app in CODE.
   match type of CODE with cm_code_at _ _ (?yescode++?jump::?rest)=>replace (yescode++jump::rest) with ((yescode++[jump])++rest) in CODE by (rewrite <-app_assoc; reflexivity) end.
   apply cm_code_at_append_left in CODE; rewrite app_nil_r; cm_code_layout_equal CODE.
 - repeat rewrite <-app_assoc in CODE; apply cm_code_at_tail in CODE; apply cm_code_at_append_right in CODE; apply cm_code_at_tail in CODE; cm_code_layout_lengths.
   split; [|split; [now left|exact SAVED]]. rewrite Z.add_0_r; cm_code_layout_equal CODE.
Qed.
