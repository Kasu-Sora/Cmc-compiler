Require Export SimpleC.EE.QCP_demos_human.cmc_simulation_budget_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Definition cm_value_generation_below limit v : Prop := match v with CMPtrV g _ _ _ _=>g<limit | _=>True end.
Fixpoint cm_values_generation_below limit values : Prop := match values with []=>True | v::rest=>cm_value_generation_below limit v /\ cm_values_generation_below limit rest end.
Fixpoint cm_spills_generation_below limit spills : Prop := match spills with []=>True | s::rest=>cm_value_generation_below limit (cm_spill_value s) /\ cm_spills_generation_below limit rest end.
Fixpoint cm_spill_frames_generation_below limit frames : Prop := match frames with []=>True | f::rest=>cm_spills_generation_below limit (cm_spill_frame_spills f) /\ cm_spill_frames_generation_below limit rest end.
Definition cm_env_generation_below policy p fid limit (env:Z->Z->cm_value) : Prop :=
 (forall slot,0<=slot<Zlength (cm_program_globals p)->cm_value_generation_below limit (env 0 slot)) /\
 (forall slot,0<=slot<Zlength (cm_function_locals (cm_function_at policy fid (cm_program_functions p)))->cm_value_generation_below limit (env 1 slot)) /\
 (forall slot,0<=slot<Zlength (cm_function_params (cm_function_at policy fid (cm_program_functions p)))->cm_value_generation_below limit (env 2 slot)).
Definition cm_tags_generation_below limit (tags:Z->cm_value) : Prop := forall addr,cm_value_generation_below limit (tags addr).
Definition cm_control_generation_below limit ctl : Prop := match ctl with CMReturn v=>cm_value_generation_below limit v | _=>True end.
Definition cm_frame_generation_below policy p fid limit frame : Prop := match frame with
 | CMHaltK=>fid = -1 | CMAssignRK v _ | CMBinRK _ v _ | CMIndexRK v _=>cm_value_generation_below limit v
 | CMBlockK env _ | CMWhileBodyK _ _ env _=>cm_env_generation_below policy p fid limit env
 | CMArgK _ _ values _=>cm_values_generation_below limit values
 | CMCallK caller env _ _ _=>cm_env_generation_below policy p caller limit env | _=>True end.
Fixpoint cm_frames_generation_below policy p fid limit frames : Prop := match frames with []=>fid = -1 | f::rest=>cm_frame_generation_below policy p fid limit f /\ cm_frames_generation_below policy p (cm_frame_parent_fid f fid) limit rest end.
Definition cm_state_generation_below policy p fid st := cm_first_dynamic_generation p<=cm_state_nextgen st /\ cm_env_generation_below policy p fid (cm_state_nextgen st) (cm_state_env st) /\ cm_tags_generation_below (cm_state_nextgen st) (cm_state_tags st).
Definition cm_task_generation_below policy p task : Prop := match task with
 | CMStartTask q _=>q=p
 | CMRTask q fid _ st ks | CMLTask q fid _ st ks | CMSTask q fid _ st ks=>q=p /\ cm_state_generation_below policy p fid st /\ cm_frames_generation_below policy p fid (cm_state_nextgen st) ks
 | CMVTask q fid v st ks=>q=p /\ cm_state_generation_below policy p fid st /\ cm_value_generation_below (cm_state_nextgen st) v /\ cm_frames_generation_below policy p fid (cm_state_nextgen st) ks
 | CMCTask q fid ctl st ks=>q=p /\ cm_state_generation_below policy p fid st /\ cm_control_generation_below (cm_state_nextgen st) ctl /\ cm_frames_generation_below policy p fid (cm_state_nextgen st) ks
 | CMDoneTask st ctl _=>cm_first_dynamic_generation p<=cm_state_nextgen st /\ cm_tags_generation_below (cm_state_nextgen st) (cm_state_tags st) /\ cm_control_generation_below (cm_state_nextgen st) ctl end.
Definition cm_task_generation_limit task := match task with CMStartTask p _=>cm_first_dynamic_generation p |
 CMRTask _ _ _ st _ | CMLTask _ _ _ st _ | CMSTask _ _ _ st _ | CMVTask _ _ _ st _ | CMCTask _ _ _ st _ | CMDoneTask st _ _=>cm_state_nextgen st end.
Definition cm_annotation_generation_below task ann : Prop := match task with
 | CMStartTask p _=>cm_spill_frames_generation_below (cm_first_dynamic_generation p) (cm_ann_saved ann)
 | CMRTask _ fid _ st _ | CMLTask _ fid _ st _ | CMSTask _ fid _ st _ | CMVTask _ fid _ st _ | CMCTask _ fid _ st _=>cm_spill_frames_generation_below (cm_state_nextgen st) (cm_active_spill_frames fid st ann)
 | CMDoneTask st _ _=>cm_spill_frames_generation_below (cm_state_nextgen st) (cm_ann_saved ann) end.
Definition cm_annotation_payload_generation_below limit ann := cm_spills_generation_below limit (cm_ann_spills ann) /\ cm_spill_frames_generation_below limit (cm_ann_saved ann).
Definition cm_task_generation_safe policy p task ann := cm_task_generation_below policy p task /\ cm_annotation_generation_below task ann.
Lemma cm_value_generation_below_mono v old new : old<=new -> cm_value_generation_below old v -> cm_value_generation_below new v.
Proof. destruct v; cbn; auto; lia. Qed.
Lemma cm_values_generation_below_mono values old new : old<=new -> cm_values_generation_below old values -> cm_values_generation_below new values.
Proof. induction values; cbn; intuition eauto using cm_value_generation_below_mono. Qed.
Lemma cm_spills_generation_below_mono spills old new : old<=new -> cm_spills_generation_below old spills -> cm_spills_generation_below new spills.
Proof. induction spills; cbn; intuition eauto using cm_value_generation_below_mono. Qed.
Lemma cm_spill_frames_generation_below_mono frames old new : old<=new -> cm_spill_frames_generation_below old frames -> cm_spill_frames_generation_below new frames.
Proof. induction frames; cbn; intuition eauto using cm_spills_generation_below_mono. Qed.
Lemma cm_env_generation_below_mono policy p fid env old new : old<=new -> cm_env_generation_below policy p fid old env -> cm_env_generation_below policy p fid new env.
Proof. unfold cm_env_generation_below; intuition eauto using cm_value_generation_below_mono. Qed.
Lemma cm_tags_generation_below_mono tags old new : old<=new -> cm_tags_generation_below old tags -> cm_tags_generation_below new tags.
Proof. unfold cm_tags_generation_below; eauto using cm_value_generation_below_mono. Qed.
Lemma cm_frames_generation_below_mono policy p fid frames old new : old<=new -> cm_frames_generation_below policy p fid old frames -> cm_frames_generation_below policy p fid new frames.
Proof. revert fid; induction frames; intros; cbn in *; auto; destruct a; cbn in *; intuition eauto using cm_env_generation_below_mono,cm_values_generation_below_mono,cm_value_generation_below_mono. Qed.
Lemma cm_values_generation_below_app limit a b : cm_values_generation_below limit a -> cm_values_generation_below limit b -> cm_values_generation_below limit (a++b).
Proof. induction a; cbn; tauto. Qed.
Lemma cm_values_generation_below_reverse limit values : cm_values_generation_below limit values -> cm_values_generation_below limit (rev values).
Proof. induction values; cbn; auto; intros [H T]; apply cm_values_generation_below_app; cbn; auto. Qed.
Lemma cm_annotation_payload_implies_task_generation task ann : cm_annotation_payload_generation_below (cm_task_generation_limit task) ann -> cm_annotation_generation_below task ann.
Proof. destruct task; unfold cm_annotation_payload_generation_below; cbn; tauto. Qed.
Lemma cm_annotation_payload_generation_below_mono ann old new : old<=new -> cm_annotation_payload_generation_below old ann -> cm_annotation_payload_generation_below new ann.
Proof. unfold cm_annotation_payload_generation_below; intuition eauto using cm_spills_generation_below_mono,cm_spill_frames_generation_below_mono. Qed.
Lemma cm_first_dynamic_generation_positive p : 0<cm_first_dynamic_generation p.
Proof. unfold cm_first_dynamic_generation; pose proof (ListLib.General.Length.Zlength_nonneg (cm_program_globals p)); pose proof (ListLib.General.Length.Zlength_nonneg (cm_program_strings p)); lia. Qed.
Lemma cm_global_pointer_generation_below sp p slot : 0<=slot<Zlength (cm_program_globals p) -> cm_value_generation_below (cm_first_dynamic_generation p) (cm_global_pointer sp p slot).
Proof. change (0<=slot<Zlength (cm_program_globals p) -> cm_global_generation slot<cm_first_dynamic_generation p); unfold cm_first_dynamic_generation,cm_global_generation; pose proof (ListLib.General.Length.Zlength_nonneg (cm_program_strings p)); lia. Qed.
Lemma cm_string_pointer_generation_below sp p slot : 0<=slot<Zlength (cm_program_strings p) -> cm_value_generation_below (cm_first_dynamic_generation p) (cm_string_pointer sp p slot).
Proof. change (0<=slot<Zlength (cm_program_strings p) -> cm_string_generation p slot<cm_first_dynamic_generation p); unfold cm_first_dynamic_generation,cm_string_generation; lia. Qed.
Lemma cm_state_generation_initial sp p input : cm_state_generation_below (cm_source_function_policy sp) p (-1) (cm_initial_state sp p input).
Proof. unfold cm_state_generation_below; cbn; split; [lia|]. split; [|intro; exact I]. unfold cm_env_generation_below; repeat split; intros; try exact I; now apply cm_global_pointer_generation_below. Qed.
Lemma cm_pointer_retype_generation limit ty v : cm_value_generation_below limit v -> cm_value_generation_below limit (cm_pointer_retype ty v).
Proof. destruct v; cbn; auto; destruct (_ =? 0); auto. Qed.
Lemma cm_convert_value_generation limit st ty v : cm_value_generation_below limit v -> cm_value_generation_below limit (cm_convert_value st ty v).
Proof. destruct ty; cbn; auto using cm_pointer_retype_generation. Qed.
Lemma cm_load_value_generation limit st ty ptr : cm_tags_generation_below limit (cm_state_tags st) -> cm_value_generation_below limit (cm_load_value ty ptr st).
Proof. destruct ty; cbn; auto; intro H; destruct (_ =? 0); try exact I; apply cm_pointer_retype_generation; apply H. Qed.
Lemma cm_ptr_add_generation limit structs v index : 0<=limit -> cm_value_generation_below limit v -> cm_value_generation_below limit (cm_ptr_add structs v index).
Proof. destruct v; cbn; lia. Qed.
Lemma cm_ptr_member_generation sp limit p v mid : 0<=limit -> cm_value_generation_below limit v -> cm_value_generation_below limit (cm_ptr_member sp p v mid).
Proof. destruct v; cbn; lia. Qed.
Lemma cm_binary_value_generation limit p op left right ty st : 0<=limit -> cm_value_generation_below limit left -> cm_value_generation_below limit right -> cm_value_generation_below limit (cm_binary_value p op left right ty st).
Proof. intros L A B; unfold cm_binary_value; repeat match goal with |- context[if ?b then _ else _]=>destruct b end; try exact I; eauto using cm_ptr_add_generation. Qed.
Lemma cm_unary_value_generation limit op v st : cm_value_generation_below limit (cm_unary_value op v st).
Proof. unfold cm_unary_value; destruct (op=?0); exact I. Qed.
