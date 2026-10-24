Require Export SimpleC.EE.QCP_demos_human.cmc_runtime_call_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_local_slot_ok_bounds sp p fid slot : cm_local_slot_ok sp p fid slot=true -> 0<=slot<Zlength (cm_function_locals (cm_source_function_at sp fid p)).
Proof. unfold cm_local_slot_ok; repeat rewrite Bool.andb_true_iff; intros [[[_ _] L] U]; split; [now apply Z.leb_le|now apply Z.ltb_lt]. Qed.
Ltac cm_rt_reduce := cbv beta iota zeta delta [cm_update_r cm_update_l cm_update_s cm_update_v cm_update_c
 cm_rstart cm_lstart cm_sstart cm_vapply cm_capply cm_args_start cm_begin_call cm_update_annotation
 cm_list_empty cm_phase_frame cm_control_kind andb orb negb hd tl] in *.
Ltac cm_rt_bool b := lazymatch b with | if ?x then _ else _=>cm_rt_bool x | _=>cm_ann_bool b end.
Ltac cm_rt_cases := cm_rt_reduce; repeat match goal with |- context[if ?b then _ else _]=>cm_rt_bool b; cm_rt_reduce end.
Ltac cm_rt_task := lazymatch goal with
 | |- cm_task_runtime_invariant ?pol ?ap ?p (CMRTask ?p ?fid _ ?st _) ?ann=>change (p=p /\ cm_runtime_core pol ap p fid st ann); split; [reflexivity|]
 | |- cm_task_runtime_invariant ?pol ?ap ?p (CMLTask ?p ?fid _ ?st _) ?ann=>change (p=p /\ cm_runtime_core pol ap p fid st ann); split; [reflexivity|]
 | |- cm_task_runtime_invariant ?pol ?ap ?p (CMSTask ?p ?fid _ ?st _) ?ann=>change (p=p /\ cm_runtime_core pol ap p fid st ann); split; [reflexivity|]
 | |- cm_task_runtime_invariant ?pol ?ap ?p (CMVTask ?p ?fid _ ?st _) ?ann=>change (p=p /\ cm_runtime_core pol ap p fid st ann); split; [reflexivity|]
 | |- cm_task_runtime_invariant ?pol ?ap ?p (CMCTask ?p ?fid _ ?st _) ?ann=>change (p=p /\ cm_runtime_core pol ap p fid st ann); split; [reflexivity|]
 end.
Ltac cm_rt_atom := lazymatch goal with
 | |- cm_runtime_core _ _ _ _ _ (cm_ann_plain _ _ _ _ _)=>apply cm_runtime_core_plain
 | |- cm_runtime_core _ _ _ _ _ (cm_ann_linear _ _)=>apply cm_runtime_core_linear
 | |- cm_runtime_core _ _ _ _ _ (cm_ann_push ?phase _ _ _ _ _)=>first [apply cm_runtime_core_push_plain; [reflexivity|reflexivity|reflexivity|] | apply cm_runtime_core_enter_scope; [lia|reflexivity|reflexivity|reflexivity|]]
 | |- cm_runtime_core _ _ _ _ (cm_state_io _ _ _) _=>apply cm_runtime_core_io
 | |- cm_runtime_core _ _ _ _ (cm_state_store _ _ _ _) _=>apply cm_runtime_core_store
 | |- cm_runtime_core _ _ _ _ (cm_activate_local _ _ _ _ _) _=>apply cm_runtime_core_activate_local; [assumption|lia|first [assumption|lia]|]
 | |- cm_runtime_core _ _ _ _ (cm_enter_call _ _ _ _ _) (cm_ann_enter_call _ _ _ _ _ _ _ _ _ _ _ _ _ _)=>apply cm_runtime_core_enter_call; [assumption|assumption|]
 end.
Ltac cm_rt_finish := repeat first [assumption|reflexivity|exact I|cm_rt_task|cm_rt_atom].
Lemma cm_r_runtime_step sp ap p fid expr st ann : cm_typed_program (cm_source_function_policy sp) p -> cm_runtime_core (cm_source_function_policy sp) ap p fid st ann ->
 cm_task_runtime_invariant (cm_source_function_policy sp) ap p (cm_rstart sp p fid expr st (cm_cursor_frames (cm_ann_cursors ann))) (cm_update_annotation (cm_update_r sp ap p fid st ann expr)).
Proof.
 destruct expr; intros WF R; cm_rt_cases; try cm_rt_finish.
 all: match goal with |- context[match ?xs with []=>_ | _::_=>_ end]=>destruct xs; cm_rt_cases; cm_rt_finish end.
Qed.
Lemma cm_l_runtime_step sp ap p fid expr st ann : cm_runtime_core (cm_source_function_policy sp) ap p fid st ann ->
 cm_task_runtime_invariant (cm_source_function_policy sp) ap p (cm_lstart sp p fid expr st (cm_cursor_frames (cm_ann_cursors ann))) (cm_update_annotation (cm_update_l sp ap p fid st ann expr)).
Proof. destruct expr; intro R; cm_rt_cases; cm_rt_finish. Qed.
Lemma cm_s_runtime_step sp ap p fid stmt st ann : cm_typed_program (cm_source_function_policy sp) p -> 0<=fid<Zlength (cm_program_functions p) -> cm_runtime_core (cm_source_function_policy sp) ap p fid st ann ->
 cm_task_runtime_invariant (cm_source_function_policy sp) ap p (cm_sstart sp p fid stmt st (cm_cursor_frames (cm_ann_cursors ann))) (cm_update_annotation (cm_update_s sp ap p fid st ann stmt)).
Proof.
 intros WF F R; assert (FW:cm_function_wf (cm_source_function_policy sp) p (cm_source_function_at sp fid p)) by (destruct WF as [_ [_ [_ [FN _]]]]; now apply FN).
 destruct F as [FL FU]; destruct stmt; cm_rt_cases; try cm_rt_finish.
 all: match goal with H:cm_local_slot_ok _ _ _ _=true|-_=>pose proof (cm_local_slot_ok_bounds _ _ _ _ H) as SLOT end; cm_rt_finish.
Qed.
Lemma cm_runtime_start_step sp ap p input : cm_typed_program (cm_source_function_policy sp) p ->
 cm_task_runtime_invariant (cm_source_function_policy sp) ap p (cm_step sp (CMStartTask p input)) (cm_update_annotation (cm_annotation_step sp ap (CMStartTask p input) cm_initial_annotation)).
Proof.
 intro WF; pose proof (cm_runtime_core_halt_initial sp ap p input WF) as R.
 cbv beta iota zeta delta [cm_step cm_annotation_step]; cm_rt_cases; cm_rt_finish.
 all: apply cm_runtime_core_enter_call with (ann:=CMAnnotation 0 0 0 0 [CMACursor CAHaltP 0 0 0] [] [] []); assumption.
Qed.
