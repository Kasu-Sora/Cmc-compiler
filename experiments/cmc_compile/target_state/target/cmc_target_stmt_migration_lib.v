Require Export SimpleC.EE.QCP_demos_human.cmc_target_activate_memory_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_target_activate_local_empty sp p fid slot st ann target :
 cm_regions_before(cm_state_regions st)(cm_state_nextgen st) -> cm_tags_generation_below(cm_state_nextgen st)(cm_state_tags st) ->
 cm_spill_frames_generation_below(cm_state_nextgen st)(cm_active_spill_frames fid st ann) ->
 cm_running_target_sim(cm_source_function_policy sp)p fid st []ann target ->
 cm_running_target_sim(cm_source_function_policy sp)p fid(cm_activate_local sp p fid slot st)[]ann target.
Proof.
 intros BEFORE GEN SG[vm[EQ[PC SIM]]];exists vm;split;[exact EQ|split;[exact PC|]].
 now apply cm_machine_activate_local_empty.
Qed.
Lemma cm_target_s_step sp ap p fid stmt st ks ann target :
 cm_regions_before(cm_state_regions st)(cm_state_nextgen st) -> cm_tags_generation_below(cm_state_nextgen st)(cm_state_tags st) ->
 cm_spill_frames_generation_below(cm_state_nextgen st)(cm_active_spill_frames fid st ann) ->
 cm_task_target_sim(cm_source_function_policy sp)p(CMSTask p fid stmt st ks)target ann ->
 cm_target_step_result sp ap p(CMSTask p fid stmt st ks)target ann.
Proof.
 intros BEFORE GEN SG SIM;destruct stmt;try solve[apply cm_target_s_structural_step;[exact I|exact SIM]].
 all: destruct SIM as[_ SIM];unfold cm_target_step_result;cbv beta iota zeta delta [cm_step cm_sstart cm_annotation_step cm_update_s cm_update_steps cm_update_annotation];destruct(cm_local_slot_ok sp p fid slot).
 all: split;[reflexivity|];first[exact SIM|exact(cm_target_activate_local_empty _ _ _ slot _ _ _ BEFORE GEN SG SIM)].
Qed.
