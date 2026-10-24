Require Export SimpleC.EE.QCP_demos_human.cmc_target_push_migration_lib.
From Coq Require Import ZArith List Bool Lia.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_value_number_io st input output v : cm_value_number (cm_state_io st input output) v=cm_value_number st v.
Proof. destruct v; reflexivity. Qed.
Lemma cm_spill_list_sim_io policy p st input output mem fid fp spills : cm_spill_list_sim policy p st mem fid fp spills -> cm_spill_list_sim policy p (cm_state_io st input output) mem fid fp spills.
Proof. induction spills as [|s rest IH]; cbn [cm_spill_list_sim]; [auto|rewrite cm_value_number_io; tauto]. Qed.
Lemma cm_spill_frames_sim_io policy p st input output mem frames : cm_spill_frames_sim policy p st mem frames -> cm_spill_frames_sim policy p (cm_state_io st input output) mem frames.
Proof. induction frames as [|f rest IH]; cbn [cm_spill_frames_sim]; [auto|intros [H REST]; split; [now apply cm_spill_list_sim_io|now apply IH]]. Qed.
Lemma cm_machine_sim_io_stack policy p st vm frames spills oldvals oldsuffix vals suffix pc input output :
 cm_machine_state_sim policy p st vm frames spills oldvals oldsuffix ->
 cm_machine_state_sim policy p (cm_state_io st input output)
 (TVMState pc (cm_encode_values st vals++suffix) (tvm_calls vm) (tvm_mem vm) input output) frames spills vals suffix.
Proof.
 intros [MEM [PROV [FP [CALL [SPILLS REST]]]]]; unfold cm_machine_state_sim.
 split; [exact MEM|split].
 - intros addr TAG LIVE; change(cm_state_init st addr=true /\ tower_getw(tvm_mem vm)addr=cm_value_number(cm_state_io st input output)(cm_state_tags st addr)); rewrite cm_value_number_io; apply PROV; assumption.
 - split; [exact FP|split; [exact CALL|split]].
   + now apply cm_spill_frames_sim_io.
   + split; [reflexivity|split; [reflexivity|]]. unfold cm_operand_suffix_sim,cm_encode_values; cbn [tvm_stack]; f_equal; apply map_ext; intro v; symmetry; apply cm_value_number_io.
Qed.
Lemma cm_target_getc_step sp ap p fid ty st ks target ann :
 (cm_state_input st=[] \/ tower_byte_value(hd 0(cm_state_input st))) ->
 cm_task_layout sp ap p (CMRTask p fid (CMGetcE ty) st ks) ann ->
 cm_task_target_sim (cm_source_function_policy sp) p (CMRTask p fid (CMGetcE ty) st ks) target ann ->
 cm_target_step_result sp ap p (CMRTask p fid (CMGetcE ty) st ks) target ann.
Proof.
 intros INPUT [CODE SAVED] [_ [vm [-> [PC SIM]]]].
 pose proof SIM as OLD; destruct SIM as [MEM [PROV [FP [CALL [SPILLS [IN [OUT STACK]]]]]]].
 change(tvm_stack vm=[])in STACK.
 assert(CODE':cm_code_at (tvm_object_code(cm_compile_model(cm_source_function_policy sp)p)) (tvm_pc vm) (TVMInst TVMGetcOp 0::cm_cont_code sp p fid (cm_ann_pc ann+1) (cm_ann_temp ann) (cm_ann_cursors ann)))by(rewrite PC; exact CODE).
 pose proof(cm_tvm_code_step _ _ _ _ _ CODE')as STEP.
 unfold cm_target_step_result; cbn [cm_step cm_rstart cm_annotation_step cm_update_r cm_update_steps cm_update_annotation tvm_iter].
 rewrite STEP; cbn [tvm_inst_step]; rewrite STACK,IN; cbn [Zlength Z.ltb].
 destruct(cm_state_input st)as[|byte input]eqn:READ.
 - cbn [list_empty tvm_action_task cm_task_target_sim]; split; [reflexivity|].
   exists(tvm_next_state vm [-1] (tvm_calls vm) (tvm_mem vm) [] (tvm_output vm)); split; [reflexivity|split; [cbn [tvm_next_state tvm_pc cm_ann_plain cm_ann_pc]; now rewrite PC|]].
   unfold cm_machine_state_sim; cbn [tvm_next_state tvm_mem tvm_calls tvm_input tvm_output tvm_stack cm_ann_plain cm_ann_calls cm_active_spill_frames].
   do 5 (split; [assumption|]); split; [symmetry; exact READ|split; [exact OUT|reflexivity]].
 - destruct INPUT as [NO|BYTE]; [discriminate|]; cbn [hd]in BYTE; pose proof BYTE as B; apply tower_byte_valueb_spec in B; rewrite B.
   cbn [list_empty hd tl tvm_action_task cm_task_target_sim]; rewrite(tower_u8_fixed _ BYTE); split; [reflexivity|].
   exists(tvm_next_state vm [byte] (tvm_calls vm) (tvm_mem vm) input (tvm_output vm)); split; [reflexivity|split; [cbn [tvm_next_state tvm_pc cm_ann_plain cm_ann_pc]; now rewrite PC|]].
   assert(WRAP:tower_wrap64 byte=byte)by(apply tower_wrap64_fixed; unfold tower_byte_value,tower_signed64 in *; lia).
   pose proof(cm_machine_sim_io_stack (cm_source_function_policy sp) p st vm (cm_ann_calls ann) (cm_active_spill_frames fid st ann) [] [] [CMIntV byte] [] (tvm_pc vm+1) input (cm_state_output st) OLD)as NEW.
   cbn [cm_encode_values map app cm_value_number]in NEW; rewrite WRAP in NEW; rewrite OUT; exact NEW.
Qed.
