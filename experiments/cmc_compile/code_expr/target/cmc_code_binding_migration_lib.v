Require Export SimpleC.EE.QCP_demos_human.cmc_code_unary_migration_lib.
From Coq Require Import ZArith List Bool Lia.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_binding_array_code_agrees sp p fid scope slot :
 cm_binding_valid p (cm_source_function_at sp fid p) scope slot ->
 (cm_binding_array_code (cm_source_function_policy sp) p fid scope slot=?0)=negb(cm_binding_array sp p fid scope slot).
Proof.
 intros [[-> B]|[[-> B]|[-> B]]]; unfold cm_binding_array_code,cm_binding_array; cbn [Z.eqb Pos.eqb]; rewrite ?(cm_source_global_at_valid sp _ _ B),?(cm_source_slot_at_valid sp _ _ B); unfold cm_source_function_at,cm_rep_nonzero; repeat match goal with |-context[if ?b then _ else _]=>destruct b end; reflexivity.
Qed.
Lemma cm_member_array_code_agrees sp p base mid : cm_member_valid p base mid -> (cm_member_array_code p base mid=?0)=negb(cm_member_array sp p base mid).
Proof.
 intros [_ [_ [STRUCT MEMBER]]]; unfold cm_member_array,cm_member_array_code.
 rewrite (cm_source_struct_at_valid sp _ _ STRUCT),(cm_source_slot_at_valid sp _ _ MEMBER).
 unfold cm_source_function_at,cm_rep_nonzero; repeat match goal with |-context[if ?b then _ else _]=>destruct b end; reflexivity.
Qed.
Lemma cm_l_var_layout_step sp ap p fid scope slot ty st ks ann : cm_binding_address_ok sp p fid scope slot st=true -> cm_task_layout sp ap p (CMLTask p fid (CMVarE scope slot ty) st ks) ann -> cm_task_layout sp ap p (cm_lstart sp p fid (CMVarE scope slot ty) st ks) (cm_update_annotation (cm_update_l sp ap p fid st ann (CMVarE scope slot ty))).
Proof.
 intros OK H; cbn [cm_lstart cm_update_l cm_update_annotation]; rewrite OK.
 exact (cm_layout_lvalue_linear sp ap p fid (CMVarE scope slot ty) st ks ann _ _ H).
Qed.
Lemma cm_r_var_layout_step sp ap p fid scope slot ty st ks ann :
 cm_binding_valid p (cm_source_function_at sp fid p) scope slot ->
 (cm_binding_array sp p fid scope slot=true -> cm_binding_address_ok sp p fid scope slot st=true) ->
 cm_task_layout sp ap p (CMRTask p fid (CMVarE scope slot ty) st ks) ann -> cm_task_layout sp ap p (cm_rstart sp p fid (CMVarE scope slot ty) st ks) (cm_update_annotation (cm_update_r sp ap p fid st ann (CMVarE scope slot ty))).
Proof.
 intros B OK H; pose proof (cm_binding_array_code_agrees sp p fid scope slot B) as ARRAY.
 destruct (cm_binding_array sp p fid scope slot) eqn:AR.
 - specialize (OK eq_refl); cbn [cm_rstart cm_update_r]; rewrite AR,OK; cbn [cm_update_annotation].
   pose proof (cm_layout_rvalue_linear sp ap p fid (CMVarE scope slot ty) st ks ann (if scope=?0 then cm_global_pointer sp p slot else cm_state_env st scope slot) st H) as RESULT.
   unfold cm_emit_rvalue,cm_expr_code_for in RESULT; cbn [Z.eqb cm_emit_expr_pair cm_rcode_of] in RESULT; unfold cm_var_rcode in RESULT; rewrite ARRAY in RESULT; cbn [negb] in RESULT; rewrite app_nil_r in RESULT; exact RESULT.
 - destruct H as [CODE SAVED]; cm_code_expr_reduce; rewrite AR; cbn [cm_task_code cm_task_fid cm_update_annotation cm_ann_push cm_ann_pc cm_ann_temp cm_ann_break cm_ann_continue cm_ann_cursors cm_ann_calls cm_cursor_code cm_cursor_phase cm_cursor_temp cm_cursor_break cm_cursor_continue cm_value_phase_code cm_phase_stops cm_phase_yields_normal cm_saved_layout cm_phase_site cm_phase_is_call orb]; split; [|split; [exact I|exact SAVED]].
   match type of CODE with cm_code_at ?c ?pc ?old=>match goal with |- cm_code_at _ _ ?new=>replace new with old; [exact CODE|] end end.
   unfold cm_emit_rvalue,cm_emit_lvalue,cm_expr_code_for; cbn [Z.eqb cm_emit_expr_pair cm_rcode_of cm_lcode_of]; unfold cm_var_rcode,cm_var_lcode,cm_rvalue_code_count,cm_lvalue_code_count; cbn [cm_expr_code_counts cm_rcount_of cm_lcount_of]; rewrite ARRAY; cbn [negb]; rewrite cm_layout_load_length; repeat rewrite <-app_assoc; repeat rewrite Z.add_assoc; reflexivity.
Qed.
