Require Export SimpleC.EE.QCP_demos_human.cmc_code_call_layout_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_code_expr_struct_migration_lib.
From Coq Require Import ZArith List Bool Lia.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_layout_call_cons_length policy p fid pc temp callee arg args ty :
 cm_rvalue_code_count policy p fid (CMCallE callee (arg::args) ty)=
 cm_rvalue_code_count policy p fid arg+Zlength(cm_temp_store_code policy p fid temp++cm_emit_args_store policy p fid (pc+cm_rvalue_code_count policy p fid arg+5) (temp+1) (temp+Zlength(arg::args)) args++cm_emit_args_reload policy p fid temp (arg::args)++[TVMInst TVMCallOp(cm_function_pc policy p callee)]).
Proof.
 rewrite <-(cm_layout_rvalue_code_length policy p fid (CMCallE callee (arg::args) ty) pc temp).
 unfold cm_emit_rvalue; rewrite cm_call_code_equation; cbn [cm_emit_args_store].
 pose proof (cm_layout_rvalue_code_length policy p fid arg pc (temp+Zlength(arg::args))) as LEN; unfold cm_emit_rvalue in LEN.
 repeat rewrite Zlength_app; rewrite LEN; lia.
Qed.
Lemma cm_r_call_cons_layout_step sp ap p fid callee arg args ty st ks ann : cm_task_layout sp ap p (CMRTask p fid (CMCallE callee (arg::args) ty) st ks) ann -> cm_task_layout sp ap p (cm_rstart sp p fid (CMCallE callee (arg::args) ty) st ks) (cm_update_annotation (cm_update_r sp ap p fid st ann (CMCallE callee (arg::args) ty))).
Proof.
 intros [CODE SAVED]; cbn [cm_rstart cm_args_start cm_update_r cm_list_empty cm_update_annotation tl].
 cm_code_expr_reduce; split; [|split; [exact I|exact SAVED]].
 match type of CODE with cm_code_at ?c ?pc ?old=>match goal with |- cm_code_at _ _ ?new=>replace new with old; [exact CODE|] end end.
 unfold cm_emit_rvalue; rewrite cm_call_code_equation; cbn [cm_emit_args_store].
 rewrite (cm_layout_call_cons_length (cm_source_function_policy sp) p fid (cm_ann_pc ann) (cm_ann_temp ann) callee arg args ty),cm_layout_temp_store_length.
 repeat rewrite <-app_assoc; repeat rewrite Z.add_assoc; reflexivity.
Qed.
