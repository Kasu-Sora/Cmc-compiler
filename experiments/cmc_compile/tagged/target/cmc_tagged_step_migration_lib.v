Require Export SimpleC.EE.QCP_demos_human.cmc_tagged_call_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_runtime_core_scope_incl policy ap p fid st ann phase owner ob oc rest :
 cm_ann_cursors ann=CMACursor phase owner ob oc::rest -> cm_phase_is_call phase=false -> cm_phase_is_scope phase=true -> cm_runtime_core policy ap p fid st ann ->
 incl (cm_phase_oldregions phase) (cm_state_regions st).
Proof.
 intros CUR CALL SCOPE [_ R]; rewrite CUR in R; cbn [cm_runtime_stack cm_cursor_phase] in R; rewrite CALL,SCOPE in R.
 destruct R as [_ [PRE _]]; eapply cm_region_prefix_suffix_incl; exact PRE.
Qed.
Lemma cm_runtime_core_call_incl policy ap p fid st ann phase owner ob oc rest :
 cm_ann_cursors ann=CMACursor phase owner ob oc::rest -> cm_phase_is_call phase=true -> cm_runtime_core policy ap p fid st ann ->
 incl (cm_phase_oldregions phase) (cm_state_regions st).
Proof.
 intros CUR CALL [_ R]; rewrite CUR in R; cbn [cm_runtime_stack cm_cursor_phase] in R; rewrite CALL in R.
 destruct R as [PRE _]; eapply cm_region_prefix_suffix_incl; exact PRE.
Qed.
Ltac cm_tag_reduce := cbv beta iota zeta delta [cm_task_tagged_valid cm_rstart cm_lstart cm_sstart cm_vapply cm_capply cm_args_start cm_begin_call cm_phase_frame cm_control_kind andb orb negb] in *.
Ltac cm_tag_cases := cm_tag_reduce; repeat match goal with |- context[if ?b then _ else _]=>cm_rt_bool b; cm_tag_reduce end.
Ltac cm_tag_finish := repeat first [assumption|exact I|apply cm_tagged_span_io|apply cm_tagged_span_enter_call; [assumption|assumption|assumption|]|apply cm_tagged_span_activate_local; [assumption|]].
Lemma cm_r_tagged_step sp p fid expr st ks : cm_typed_program (cm_source_function_policy sp) p -> cm_regions_before (cm_state_regions st) (cm_state_nextgen st) -> cm_tagged_span_valid st -> cm_task_tagged_valid (cm_rstart sp p fid expr st ks).
Proof.
 destruct expr; intros WF BEFORE TAG; cm_tag_cases; try cm_tag_finish.
 all: match goal with |- context[match ?xs with []=>_ | _::_=>_ end]=>destruct xs; cm_tag_cases; cm_tag_finish end.
Qed.
Lemma cm_l_tagged_step sp p fid expr st ks : cm_tagged_span_valid st -> cm_task_tagged_valid (cm_lstart sp p fid expr st ks).
Proof. destruct expr; intro TAG; cm_tag_cases; cm_tag_finish. Qed.
Lemma cm_s_tagged_step sp p fid stmt st ks : cm_regions_before (cm_state_regions st) (cm_state_nextgen st) -> cm_tagged_span_valid st -> cm_task_tagged_valid (cm_sstart sp p fid stmt st ks).
Proof. destruct stmt; intros BEFORE TAG; cm_tag_cases; cm_tag_finish. Qed.
Lemma cm_v_tagged_step sp ap p fid phase owner ob oc rest v st ann :
 cm_typed_program (cm_source_function_policy sp) p -> cm_ann_cursors ann=CMACursor phase owner ob oc::rest ->
 cm_runtime_core (cm_source_function_policy sp) ap p fid st ann -> cm_tagged_span_valid st ->
 cm_task_tagged_valid (cm_vapply sp p fid (cm_phase_frame phase) v st (cm_cursor_frames rest)).
Proof.
 intros WF CUR CORE TAG; pose proof (proj1 CORE) as BEFORE.
 pose proof (cm_runtime_stack_memory_layout _ _ _ _ _ _ _ _ _ (proj2 CORE)) as MEM.
 destruct phase; cm_tag_cases; try cm_tag_finish.
 all: try solve [eapply cm_tagged_span_store; [exact MEM|eassumption|exact TAG]].
 all: try solve [apply cm_tagged_span_restore_scope; [exact (cm_runtime_core_scope_incl _ _ _ _ _ _ _ _ _ _ _ CUR eq_refl eq_refl CORE)|exact TAG]].
 all: try match goal with H:(_ && _)=true|-_=>apply andb_true_iff in H; destruct H end.
 all: try solve [eapply cm_tagged_span_store; [exact MEM|eassumption|exact TAG]].
 all: try match goal with |- context[match ?xs with []=>_ | _::_=>_ end]=>destruct xs; cm_tag_cases; cm_tag_finish end.
Qed.
Lemma cm_c_tagged_step sp ap p fid phase owner ob oc rest ctl st ann :
 cm_ann_cursors ann=CMACursor phase owner ob oc::rest ->
 cm_runtime_core (cm_source_function_policy sp) ap p fid st ann -> cm_tagged_span_valid st ->
 cm_task_tagged_valid (cm_capply sp p fid (cm_phase_frame phase) ctl st (cm_cursor_frames rest)).
Proof.
 intros CUR CORE TAG; destruct phase; cm_tag_cases; try cm_tag_finish.
 all: try solve [apply cm_tagged_span_restore_scope; [exact (cm_runtime_core_scope_incl _ _ _ _ _ _ _ _ _ _ _ CUR eq_refl eq_refl CORE)|exact TAG]].
 all: apply cm_tagged_span_restore_call; [exact (cm_runtime_core_call_incl _ _ _ _ _ _ _ _ _ _ _ CUR eq_refl CORE)|exact TAG].
Qed.
