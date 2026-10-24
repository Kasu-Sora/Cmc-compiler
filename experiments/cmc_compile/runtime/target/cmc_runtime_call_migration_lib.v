Require Export SimpleC.EE.QCP_demos_human.cmc_runtime_frame_geometry_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_store_params_fp sp p fid values index st : cm_state_fp (cm_store_params sp p fid values index st)=cm_state_fp st.
Proof. revert index st; induction values; intros; [reflexivity|cbn [cm_store_params]; rewrite IHvalues; reflexivity]. Qed.
Lemma cm_call_ok_function_wf sp p fid values st : cm_typed_program (cm_source_function_policy sp) p -> cm_call_ok sp p fid values st=true -> cm_function_wf (cm_source_function_policy sp) p (cm_source_function_at sp fid p).
Proof.
 intros [_ [_ [_ [F _]]]] OK; unfold cm_call_ok in OK; repeat rewrite Bool.andb_true_iff in OK.
 repeat match goal with H:_ /\ _|-_=>destruct H end; apply F; split; [apply Z.leb_le|apply Z.ltb_lt]; assumption.
Qed.
Lemma cm_call_frame_segment sp p fid values st : cm_typed_program (cm_source_function_policy sp) p -> cm_call_ok sp p fid values st=true ->
 cm_frame_segment (cm_source_function_policy sp) p fid (cm_state_fp st-cm_frame_size (cm_program_structs p) (cm_source_function_at sp fid p)) (cm_state_fp st).
Proof.
 intros WF OK; pose proof (cm_call_ok_function_wf _ _ _ _ _ WF OK) as FW.
 destruct FW as [_ [[PW _] [LW [_ [_ [_ [TEMP FS]]]]]]].
 pose proof (cm_slots_size_nonnegative__call_bounds _ _ PW) as PN; pose proof (cm_slots_size_nonnegative__call_bounds _ _ LW) as LN.
 assert (ST:16<=cm_static_size p) by (unfold cm_typed_program in WF; tauto).
 unfold cm_call_ok in OK; repeat rewrite Bool.andb_true_iff in OK; repeat match goal with H:_ /\ _|-_=>destruct H end.
 repeat match goal with H:(_<=?_) = true|-_=>apply Z.leb_le in H | H:(_<?_) = true|-_=>apply Z.ltb_lt in H end.
 unfold cm_frame_segment,cm_temp_offset,cm_frame_size,cm_source_function_at in *; repeat split; lia.
Qed.
Lemma cm_runtime_core_enter_call sp ap p caller callee values st ret returnpc parent_temp parent_break parent_continue ann :
 cm_typed_program (cm_source_function_policy sp) p -> cm_call_ok sp p callee values st=true -> cm_runtime_core (cm_source_function_policy sp) ap p caller st ann ->
 cm_runtime_core (cm_source_function_policy sp) ap p callee (cm_enter_call sp p callee values st)
 (cm_ann_enter_call sp p caller callee st ret returnpc parent_temp parent_break parent_continue (cm_ann_cursors ann) (cm_ann_spills ann) (cm_ann_saved ann) (cm_ann_calls ann)).
Proof.
 intros WF OK [BEFORE RUN]; split; [now apply cm_enter_call_regions_before|].
 pose proof (cm_call_ok_function_wf _ _ _ _ _ WF OK) as FW; pose proof (cm_call_frame_segment _ _ _ _ _ WF OK) as SEG.
 unfold cm_enter_call; rewrite cm_store_params_regions,cm_store_params_fp.
 cbv beta iota zeta delta [cm_call_base_state cm_state_fp cm_state_regions cm_ann_enter_call cm_ann_cursors cm_ann_spills cm_ann_saved cm_ann_calls] in *.
 cbn [cm_runtime_stack cm_cursor_phase cm_phase_is_call cm_phase_oldregions cm_phase_oldfp cm_phase_caller hd tl cm_spill_frame_fid cm_spill_frame_fp cm_spill_frame_spills cm_call_sim_base cm_call_sim_saved].
 split; [now apply cm_parameter_region_prefix_safe|].
 split; [exact SEG|]. repeat first [exact I|discriminate|reflexivity|match goal with |- _ /\ _=>split end].
 apply cm_runtime_stack_regions_for_slots; assumption.
Qed.
Lemma cm_runtime_stack_halt_initial sp ap p (input:list Z) owner ob oc : cm_typed_program (cm_source_function_policy sp) p ->
 cm_runtime_stack (cm_source_function_policy sp) ap p (cm_static_regions p) (-1) 1048576 (cm_static_regions p) [CMACursor CAHaltP owner ob oc] [] [] [].
Proof.
 intro WF; cbn [cm_runtime_stack cm_cursor_phase cm_phase_is_call cm_phase_is_scope cm_phase_is_halt].
 assert (BOUND:16<=cm_static_size p<=1048576) by (unfold cm_typed_program in WF; tauto).
 split; [reflexivity|]; split; [reflexivity|]; split; [apply cm_region_dead_prefix_refl|].
 destruct BOUND as [LOW UP]; repeat first [assumption|reflexivity|match goal with |- _ /\ _=>split end].
 now apply cm_typed_static_regions_layout with (policy:=cm_source_function_policy sp).
Qed.
Lemma cm_runtime_core_halt_initial sp ap p input : cm_typed_program (cm_source_function_policy sp) p -> cm_runtime_core (cm_source_function_policy sp) ap p (-1) (cm_initial_state sp p input) (CMAnnotation 0 0 0 0 [CMACursor CAHaltP 0 0 0] [] [] []).
Proof. intro WF; split; [apply cm_initial_regions_before|exact (cm_runtime_stack_halt_initial sp ap p input 0 0 0 WF)]. Qed.
