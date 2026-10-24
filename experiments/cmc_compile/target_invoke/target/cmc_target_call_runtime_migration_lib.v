Require Export SimpleC.EE.QCP_demos_human.cmc_target_call_frame_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_runtime_new_frame_range policy ap p st caller ann base :
 cm_runtime_core policy ap p caller st ann ->cm_static_size p<=base ->base+8<=cm_state_fp st ->
 (forall a,cm_live_address st a ->a<base \/ base+8<=a) /\
 cm_machine_range_safe policy p base 8(cm_ann_calls ann)(CMSpillFrame caller(cm_state_fp st)(cm_ann_spills ann)::cm_ann_saved ann).
Proof.
 intros[_ RT]LOW HIGH;pose proof(cm_runtime_stack_fp_bounds _ _ _ _ _ _ _ _ _ _ _ RT)as[SL[FL FU]].
 pose proof(cm_runtime_stack_lower _ _ _ _ _ _ _ _ _ _ _ RT)as[C[S F]].
 split.
 - intros a[r[IN[LIVE[A B]]]];pose proof(cm_runtime_stack_region_bounds _ _ _ _ _ _ _ _ _ _ _ _ RT IN LIVE)as[_[_[_[_ PLACE]]]];lia.
 - split;[unfold cm_range_disjoint;lia|];split;[eapply cm_call_frames_lower_range;[exact C|exact HIGH]|].
   split;[eapply cm_spill_list_lower_range;[exact S|exact HIGH]|eapply cm_spill_frames_lower_range;[exact F|exact HIGH]].
Qed.
Lemma cm_call_pending_runtime sp ap p caller callee st values ann returnpc :
 cm_typed_program(cm_source_function_policy sp)p ->cm_call_ok sp p callee values st=true ->
 cm_runtime_core(cm_source_function_policy sp)ap p caller st ann ->
 cm_runtime_memory_layout(cm_source_function_policy sp)p(cm_call_pending_base sp p callee st)
 (CMCallSimFrame(cm_state_fp(cm_call_base_state sp p callee st))(cm_state_fp st)returnpc::cm_ann_calls ann)
 (CMSpillFrame callee(cm_state_fp(cm_call_base_state sp p callee st))[]::CMSpillFrame caller(cm_state_fp st)(cm_ann_spills ann)::cm_ann_saved ann).
Proof.
 intros WF OK RT.
 pose proof(cm_runtime_core_enter_call sp ap p caller callee values st CMIntTy returnpc 0 0 0 ann WF OK RT)as[_ ENTER].
 pose proof(cm_runtime_stack_memory_layout(cm_source_function_policy sp)ap p(cm_enter_call sp p callee values st)callee _ _ _ _ ENTER)as MEM.
 unfold cm_runtime_memory_layout,cm_enter_call in MEM;rewrite cm_store_params_regions,cm_store_params_fp in MEM;exact MEM.
Qed.
