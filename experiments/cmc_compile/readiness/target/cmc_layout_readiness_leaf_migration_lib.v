Require Export SimpleC.EE.QCP_demos_human.cmc_layout_readiness_defs_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Ltac cm_ready_error := match goal with H:cm_task_succeeds ?sp (CMCTask ?p ?fid (CMError ?error) ?st ?ks)|-_=>exfalso; exact (cm_error_not_succeeds sp p fid st error ks H) end.
Lemma cm_begin_call_succeeds_ready sp p caller fid values st ret ks :
 cm_task_succeeds sp (cm_begin_call sp p caller fid values st ret ks) ->
 cm_call_ok sp p fid values st=true /\ cm_call_depth ks<65536.
Proof.
 unfold cm_begin_call; destruct (cm_call_ok sp p fid values st && (cm_call_depth ks <? 65536)) eqn:OK; intro S.
 - apply andb_true_iff in OK; destruct OK as [OK D]; split; [exact OK|now apply Z.ltb_lt].
 - cm_ready_error.
Qed.
Lemma cm_start_succeeds_ready sp p input : cm_task_succeeds sp (CMStartTask p input) -> cm_call_ok sp p (cm_program_main p) [] (cm_initial_state sp p input)=true.
Proof. intro S; apply cm_succeeds_step_total in S; exact (proj1 (cm_begin_call_succeeds_ready _ _ _ _ _ _ _ _ S)). Qed.
Lemma cm_r_succeeds_ready sp p fid expr st ks ann : cm_cursor_frames (cm_ann_cursors ann)=ks ->
 cm_task_succeeds sp (cm_rstart sp p fid expr st ks) -> cm_r_layout_ready sp p fid expr st ks ann.
Proof.
 intros E S; unfold cm_r_layout_ready; split.
 - intros callee ty ->; cbn [cm_rstart cm_args_start] in S; apply cm_begin_call_succeeds_ready in S; rewrite E; tauto.
 - split.
   + intros ty ->; cbn [cm_rstart] in S; destruct (cm_state_input st) as [|byte rest] eqn:IN; [now left|].
     destruct (tower_byte_valueb byte) eqn:B; [right; now apply tower_byte_valueb_spec|cm_ready_error].
   + intros scope slot ty -> ARRAY; cbn [cm_rstart] in S; rewrite ARRAY in S.
     destruct (cm_binding_address_ok sp p fid scope slot st) eqn:ADDR; [reflexivity|cm_ready_error].
Qed.
Lemma cm_l_succeeds_ready sp p fid expr st ks : cm_task_succeeds sp (cm_lstart sp p fid expr st ks) -> cm_l_layout_ready sp p fid expr st.
Proof.
 destruct expr; cbn [cm_lstart]; intro S; try solve [cm_ready_error]; unfold cm_l_layout_ready; cbn [cm_lvalue].
 all: try solve [split; [exact I|intros; discriminate]].
 - split; [exact I|]; intros scope0 slot0 ty0 EQ; inversion EQ; subst.
   destruct (cm_binding_address_ok sp p fid scope0 slot0 st) eqn:B; [reflexivity|cm_ready_error].
 - destruct (op=?2) eqn:OP; [apply Z.eqb_eq in OP|cm_ready_error]. split; [exact OP|intros; discriminate].
Qed.
Lemma cm_s_succeeds_ready sp p fid stmt st ks : cm_task_succeeds sp (cm_sstart sp p fid stmt st ks) -> cm_stmt_start_safe sp p fid stmt=true.
Proof. destruct stmt; cbn [cm_sstart cm_stmt_start_safe]; intro S; try reflexivity; destruct (cm_local_slot_ok sp p fid slot) eqn:B; [reflexivity|cm_ready_error|reflexivity|cm_ready_error]. Qed.
Lemma cm_v_succeeds_phase_ready sp p fid phase owner ob oc rest v st ann :
 cm_ann_cursors ann=CMACursor phase owner ob oc::rest -> cm_annotation_rooted ann ->
 cm_task_succeeds sp (cm_vapply sp p fid (cm_phase_frame phase) v st (cm_cursor_frames rest)) ->
 cm_v_phase_ready sp p v st ann phase.
Proof.
 intros CUR ROOT S; unfold cm_annotation_rooted in ROOT; rewrite CUR in ROOT.
 destruct phase; cbn [cm_v_phase_ready cm_phase_frame cm_vapply] in *; try exact I; try solve [cm_ready_error].
 all: try solve [match goal with |- ?b=true=>destruct b eqn:B; [reflexivity|cm_ready_error] end].
 - rewrite CUR; cbn [tl]; apply (proj1 ROOT); reflexivity.
 - destruct rest0 as [|arg args0]; [right|left; discriminate]. rewrite CUR; cbn [tl]; now apply cm_begin_call_succeeds_ready in S.
Qed.
