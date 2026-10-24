Require Export SimpleC.EE.QCP_demos_human.cmc_code_value_flow_migration_lib.
From Coq Require Import ZArith List Bool Lia.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_v_binary_r_layout_step sp ap p fid v st op lhs rhs left ty pc temp b c owner ob oc tail spills saved calls :
 let ann:=CMAnnotation pc temp b c (CMACursor (CABinRP op lhs rhs left ty) owner ob oc::tail) spills saved calls in
 cm_binary_ok p op left v st=true -> cm_task_layout sp ap p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) ann ->
 cm_task_layout sp ap p (cm_vapply sp p fid (CMBinRK op left ty) v st (cm_cursor_frames tail)) (cm_update_annotation(cm_update_v sp ap p fid v st ann (CABinRP op lhs rhs left ty))).
Proof.
 cbn zeta; intros OK [CODE [_ SAVED]]; cm_code_value_reduce; rewrite OK; destruct((op=?0)||(op=?1)); cm_code_value_reduce; split; try exact SAVED;
 apply cm_code_at_append_right in CODE; repeat rewrite Zlength_cons in CODE; rewrite ?Zlength_nil in CODE; exact CODE.
Qed.
Lemma cm_v_binary_l_layout_step sp ap p fid v st op lhs rhs ty pc temp b c owner ob oc tail spills saved calls :
 let ann:=CMAnnotation pc temp b c (CMACursor (CABinLP op lhs rhs ty) owner ob oc::tail) spills saved calls in
 temp=owner -> cm_task_layout sp ap p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) ann ->
 cm_task_layout sp ap p (cm_vapply sp p fid (CMBinLK op rhs ty) v st (cm_cursor_frames tail)) (cm_update_annotation(cm_update_v sp ap p fid v st ann (CABinLP op lhs rhs ty))).
Proof.
 cbn zeta; intros -> [CODE [_ SAVED]]; cm_code_value_reduce; destruct(op=?0)eqn:ZERO; destruct(op=?1)eqn:ONE; try (apply Z.eqb_eq in ZERO; apply Z.eqb_eq in ONE; lia).
 all: destruct(cm_truth st v); cm_code_value_reduce; rewrite ?ZERO,?ONE in *; cbn [andb orb negb] in *; cm_code_value_reduce; split; try exact SAVED; try(split; [exact I|exact SAVED]).
 all: unfold cm_cont_code in *; rewrite ?ZERO,?ONE in *; cbn[orb]in *; fold app in CODE; match goal with |-cm_code_at _ _ (cm_cursor_code _ _ _ _ _ _ _) => apply cm_code_at_append_right in CODE | _=>repeat rewrite <-app_assoc in CODE; lazymatch type of ZERO with _=false=>lazymatch type of ONE with _=false=>apply cm_code_at_append_right in CODE | _=>apply cm_code_at_tail in CODE end | _=>apply cm_code_at_tail in CODE end end.
 all: repeat rewrite Zlength_app in *; repeat rewrite cm_layout_rvalue_code_length in *; repeat rewrite Zlength_cons in *; rewrite ?Zlength_nil in *.
 all: match type of CODE with cm_code_at ?c ?oldpc ?old=>match goal with |-cm_code_at _ ?newpc ?new=>replace newpc with oldpc by lia; replace new with old; [exact CODE|]end end.
 all: rewrite ?ZERO,?ONE; cbn [orb]; repeat rewrite Zlength_app; repeat rewrite cm_layout_rvalue_code_length; repeat rewrite Zlength_cons; rewrite ?Zlength_nil; repeat rewrite <-app_assoc; repeat first [reflexivity|solve[lia]|progress f_equal].
Qed.
