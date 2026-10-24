Require Export SimpleC.EE.QCP_demos_human.cmc_target_structural_migration_lib.
From Coq Require Import ZArith List Bool Lia.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_target_push_sim sp p fid st ann target imm v rest :
 cm_running_target_sim (cm_source_function_policy sp) p fid st [] ann target ->
 cm_code_at (cm_model_code (cm_source_function_policy sp) p) (cm_ann_pc ann) (TVMInst TVMPushOp imm::rest) ->
 cm_value_number st v=tower_wrap64 imm ->
 cm_running_target_sim (cm_source_function_policy sp) p fid st [v] (cm_ann_linear (cm_push_code imm) ann) (tvm_iter 1 target).
Proof.
 intros [vm [-> [PC SIM]]] CODE VALUE.
 destruct SIM as [MEM [PROV [FP [CALL [SPILLS [INPUT [OUTPUT STACK]]]]]]].
 change (tvm_stack vm=[]) in STACK.
 pose proof(cm_tvm_push_step (cm_compile_model(cm_source_function_policy sp)p) vm imm rest)as STEP.
 assert(CAP:Zlength(tvm_stack vm)<65536)by(rewrite STACK; cbn; lia).
 specialize(STEP ltac:(rewrite PC; exact CODE) CAP); cbn [tvm_iter]; rewrite STEP.
 exists(tvm_next_state vm (tower_wrap64 imm::tvm_stack vm) (tvm_calls vm) (tvm_mem vm) (tvm_input vm) (tvm_output vm)).
 split; [reflexivity|split; [cbn [tvm_next_state tvm_pc cm_ann_linear cm_push_code cm_ann_plain cm_ann_pc]; rewrite PC; reflexivity|]].
 unfold cm_machine_state_sim,cm_operand_suffix_sim,cm_encode_values;
 cbn [tvm_next_state tvm_mem tvm_calls tvm_input tvm_output tvm_stack cm_active_spill_frames cm_ann_linear cm_push_code cm_ann_plain cm_ann_spills cm_ann_saved cm_ann_calls map app].
 do 4 (split; [assumption|]); split; [exact SPILLS|].
 split; [exact INPUT|split; [exact OUTPUT|]]. rewrite STACK,VALUE; reflexivity.
Qed.
Lemma tower_u8_wrap64 z : tower_u8(tower_wrap64 z)=tower_u8 z.
Proof.
 replace (tower_wrap64 z) with (z+(-((z+9223372036854775808)/18446744073709551616)*72057594037927936)*256).
 - unfold tower_u8; rewrite Z.mod_add by lia; reflexivity.
 - unfold tower_wrap64; pose proof(Z.div_mod (z+9223372036854775808) 18446744073709551616 ltac:(lia)); lia.
Qed.
Lemma cm_const_number st ty n : cm_value_number st (cm_convert_value st ty (CMIntV n))=tower_wrap64(cm_const_immediate ty n).
Proof.
 rewrite cm_convert_number; destruct ty; cbn [cm_type_eqb cm_type_dec cm_const_immediate cm_value_number]; try reflexivity.
 rewrite tower_u8_wrap64; symmetry; apply tower_wrap64_fixed; rewrite (proj2 (cm_type_eqb_spec CMCharTy CMCharTy) eq_refl); pose proof(tower_u8_range n); unfold tower_signed64,tower_byte_value in *; lia.
Qed.
Lemma cm_target_const_step sp ap p fid n ty st ks target ann :
 cm_task_layout sp ap p (CMRTask p fid (CMConstE n ty) st ks) ann ->
 cm_task_target_sim (cm_source_function_policy sp) p (CMRTask p fid (CMConstE n ty) st ks) target ann ->
 cm_target_step_result sp ap p (CMRTask p fid (CMConstE n ty) st ks) target ann.
Proof.
 intros [CODE SAVED] [_ SIM]; unfold cm_target_step_result; cbn [cm_step cm_rstart cm_annotation_step cm_update_r cm_update_annotation cm_update_steps cm_task_target_sim].
 split; [reflexivity|]. eapply cm_target_push_sim; [exact SIM| |apply cm_const_number].
 exact CODE.
Qed.
Lemma cm_target_sizeof_step sp ap p fid asked ty st ks target ann :
 cm_task_layout sp ap p (CMRTask p fid (CMSizeofE asked ty) st ks) ann ->
 cm_task_target_sim (cm_source_function_policy sp) p (CMRTask p fid (CMSizeofE asked ty) st ks) target ann ->
 cm_target_step_result sp ap p (CMRTask p fid (CMSizeofE asked ty) st ks) target ann.
Proof.
 intros [CODE SAVED] [_ SIM]; unfold cm_target_step_result; cbn [cm_step cm_rstart cm_annotation_step cm_update_r cm_update_annotation cm_update_steps cm_task_target_sim].
 split; [reflexivity|]. eapply cm_target_push_sim; [exact SIM|exact CODE|reflexivity].
Qed.
