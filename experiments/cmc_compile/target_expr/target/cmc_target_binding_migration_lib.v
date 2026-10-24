Require Export SimpleC.EE.QCP_demos_human.cmc_target_address_migration_lib.
From Coq Require Import ZArith List Bool Lia.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_target_fp_address_sim sp p fid st ann target offset v rest :
 cm_running_target_sim (cm_source_function_policy sp) p fid st [] ann target ->
 cm_code_at (cm_model_code (cm_source_function_policy sp) p) (cm_ann_pc ann) (cm_fp_relative_address_code offset++rest) ->
 cm_value_number st v=tower_wrap64(cm_state_fp st+offset) ->
 cm_running_target_sim (cm_source_function_policy sp) p fid st [v] (cm_ann_linear (cm_fp_relative_address_code offset) ann) (tvm_iter 4 target).
Proof.
 intros [[pc stack calls mem input output] [-> [PC SIM]]] CODE VALUE.
 destruct SIM as [MEM [PROV [FP [CALL [SPILLS [INPUT [OUTPUT STACK]]]]]]].
 change(stack=[])in STACK; subst stack; cbn [tvm_pc]in PC; subst pc.
 rewrite(cm_tvm_fp_address (cm_compile_model(cm_source_function_policy sp)p) _ _ _ _ _ _ _ CODE).
 exists(TVMState (cm_ann_pc ann+4) [tower_wrap64(tower_getw mem 8+offset)] calls mem input output); split; [reflexivity|split;[reflexivity|]].
 unfold cm_machine_state_sim; do 5(split;[assumption|]); split;[exact INPUT|split;[exact OUTPUT|]].
 unfold cm_operand_suffix_sim,cm_encode_values; cbn [map app tvm_stack]; rewrite VALUE; change(tower_getw mem 8=cm_state_fp st)in FP; now rewrite FP.
Qed.
Lemma cm_target_binding_sim sp p fid scope slot st ann target rest :
 cm_binding_address_ok sp p fid scope slot st=true ->
 cm_running_target_sim (cm_source_function_policy sp) p fid st [] ann target ->
 cm_code_at (cm_model_code (cm_source_function_policy sp) p) (cm_ann_pc ann) (cm_binding_address_code(cm_source_function_policy sp)p fid scope slot++rest) ->
 cm_running_target_sim (cm_source_function_policy sp) p fid st [if scope=?0 then cm_global_pointer sp p slot else cm_state_env st scope slot]
 (cm_ann_linear (cm_binding_address_code(cm_source_function_policy sp)p fid scope slot) ann)
 (tvm_iter (cm_code_steps(cm_binding_address_code(cm_source_function_policy sp)p fid scope slot)) target).
Proof.
 intros OK SIM CODE; unfold cm_binding_address_ok in OK; repeat rewrite andb_true_iff in OK; destruct OK as [[SIGNED NUM] TYPE]; apply Z.eqb_eq in NUM.
 unfold cm_binding_address_code in *; destruct(scope=?0)eqn:GLOBAL.
 - eapply cm_target_push_sim; [exact SIM|exact CODE|symmetry; exact NUM].
 - eapply cm_target_fp_address_sim; [exact SIM|exact CODE|].
   rewrite <-NUM; destruct(scope=?1); unfold cm_local_base,cm_local_offset,cm_param_base,cm_param_offset,cm_source_function_at; f_equal; lia.
Qed.
Lemma cm_target_l_var_step sp ap p fid scope slot ty st ks target ann :
 cm_binding_address_ok sp p fid scope slot st=true ->
 cm_task_layout sp ap p (CMLTask p fid (CMVarE scope slot ty) st ks) ann ->
 cm_task_target_sim (cm_source_function_policy sp) p (CMLTask p fid (CMVarE scope slot ty) st ks) target ann ->
 cm_target_step_result sp ap p (CMLTask p fid (CMVarE scope slot ty) st ks) target ann.
Proof.
 intros OK [CODE SAVED] [_ SIM]; unfold cm_target_step_result; cbn [cm_step cm_lstart cm_annotation_step cm_update_l cm_update_annotation cm_update_steps]; rewrite OK; split;[reflexivity|].
 eapply cm_target_binding_sim; [exact OK|exact SIM|exact CODE].
Qed.
Lemma cm_target_r_var_step sp ap p fid scope slot ty st ks target ann :
 cm_binding_valid p (cm_source_function_at sp fid p) scope slot ->
 (cm_binding_array sp p fid scope slot=true ->cm_binding_address_ok sp p fid scope slot st=true) ->
 cm_task_layout sp ap p (CMRTask p fid (CMVarE scope slot ty) st ks) ann ->
 cm_task_target_sim (cm_source_function_policy sp) p (CMRTask p fid (CMVarE scope slot ty) st ks) target ann ->
 cm_target_step_result sp ap p (CMRTask p fid (CMVarE scope slot ty) st ks) target ann.
Proof.
 intros VALID OK LAYOUT SIM; destruct(cm_binding_array sp p fid scope slot)eqn:ARRAY.
 - specialize(OK eq_refl); destruct LAYOUT as [CODE SAVED]; destruct SIM as [_ SIM].
   unfold cm_target_step_result; cbn [cm_step cm_rstart cm_annotation_step cm_update_r]; rewrite ARRAY,OK; cbn [cm_update_annotation cm_update_steps cm_task_target_sim]; split;[reflexivity|].
   eapply cm_target_binding_sim; [exact OK|exact SIM|].
   pose proof(cm_binding_array_code_agrees sp p fid scope slot VALID)as AGREE; rewrite ARRAY in AGREE; cbn [negb]in AGREE.
   cbn [cm_task_code]in CODE; unfold cm_emit_rvalue,cm_expr_code_for in CODE; cbn [Z.eqb cm_emit_expr_pair cm_rcode_of]in CODE; unfold cm_var_rcode in CODE; rewrite AGREE in CODE; cbn [negb]in CODE; rewrite app_nil_r in CODE; exact CODE.
 - apply cm_target_r_structural_step; [exact ARRAY|exact SIM].
Qed.
