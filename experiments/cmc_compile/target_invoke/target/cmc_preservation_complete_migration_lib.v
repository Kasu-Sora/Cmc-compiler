Require Export SimpleC.EE.QCP_demos_human.cmc_target_total_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
(* The eighteen conjuncts of cmc_preservation_total.c, in their original order.
   The stronger full-support invariant is internal to the induction proof. *)
Definition cm_preservation_invariant sp ap nilslot p ast :Prop :=
 cm_task_succeeds sp(cm_astate_task ast) /\
 cm_annotation_erases(cm_astate_task ast)(cm_astate_annotation ast) /\
 cm_annotation_rooted(cm_astate_annotation ast) /\
 cm_task_coordinate_ready(cm_source_function_policy sp)p(cm_astate_task ast)(cm_astate_annotation ast) /\
 cm_task_layout_ready sp ap p(cm_astate_task ast)(cm_astate_annotation ast) /\
 cm_task_context_ready(cm_astate_task ast)(cm_astate_annotation ast) /\
 cm_task_runtime_invariant(cm_source_function_policy sp)ap p(cm_astate_task ast)(cm_astate_annotation ast) /\
 cm_task_type_ready(cm_source_function_policy sp)nilslot p(cm_astate_task ast)(cm_astate_annotation ast) /\
 cm_task_fid_ready p(cm_astate_task ast) /\
 cm_annotation_spill_consistent ap(cm_astate_annotation ast) /\
 cm_task_generation_safe(cm_source_function_policy sp)p(cm_astate_task ast)(cm_astate_annotation ast) /\
 cm_task_static_valid(cm_source_function_policy sp)(cm_astate_task ast) /\
 cm_task_static_bases p(cm_astate_task ast) /\
 cm_task_tagged_valid(cm_astate_task ast) /\
 cm_task_budget(cm_source_function_policy sp)p(cm_astate_task ast)(cm_astate_annotation ast) /\
 cm_task_short_ready(cm_astate_task ast) /\
 cm_task_layout sp ap p(cm_astate_task ast)(cm_astate_annotation ast) /\
 cm_task_target_sim(cm_source_function_policy sp)p(cm_astate_task ast)(cm_astate_target ast)(cm_astate_annotation ast).
Lemma cm_full_support_original_invariant sp ap nilslot p ast :
 cm_full_support_invariants sp ap nilslot p ast ->cm_preservation_invariant sp ap nilslot p ast.
Proof.
 intros[[[[READY TAG]TYPE]LAYOUT]SIM];pose proof(cm_readiness_support_layout_ready sp ap p ast READY)as LR.
 destruct READY as[[[BASE[SG SHORT]]RT]STMT];destruct BASE as[STRUCT[STATICBASE SAVEDBASE]].
 destruct STRUCT as[CTRL[STATIC[BUD[GEN PAYLOAD]]]];destruct CTRL as[S[ER[ROOT[COORD[CONTEXT[FID[SP ACTIVE]]]]]]].
 pose proof(cm_annotation_payload_implies_task_generation _ _ PAYLOAD)as AG.
 unfold cm_preservation_invariant,cm_task_generation_safe,cm_astate_sim in *;tauto.
Qed.
Theorem cm_preservation_initial sp ap nilslot p input :
 cm_task_succeeds sp(CMStartTask p input) ->cm_preservation_invariant sp ap nilslot p(cm_annotated_start(cm_source_function_policy sp)p input).
Proof. intro S;apply cm_full_support_original_invariant;now apply cm_full_support_initial. Qed.
Theorem cm_preservation_reachable sp ap nilslot p input n :
 cm_semantic_wf_program(cm_source_function_policy sp)p ->cm_task_succeeds sp(CMStartTask p input) ->
 cm_preservation_invariant sp ap nilslot p(cm_annotated_iter sp ap n(cm_annotated_start(cm_source_function_policy sp)p input)).
Proof. intros WF S;apply cm_full_support_original_invariant;apply cm_full_support_iter;[exact WF|now apply cm_full_support_initial]. Qed.
Theorem cmc_preservation sp p input output status :
 cm_semantic_wf_program(cm_source_function_policy sp)p ->cm_source_terminates sp p input output status ->
 tvm_terminates(cm_compile_model(cm_source_function_policy sp)p)input output status.
Proof.
 intros WF SOURCE.
 set(ap:=CMAnnotationPolicy(CMACursor CAHaltP 0 0 0)(CMSpillFrame(-1)1048576[])(CMCallSimFrame 0 0 0)).
 set(nilslot:=CMSlotD CMIntTy 0).
 eapply cm_source_termination_from_invariant with(sp:=sp)(ap:=ap)(Inv:=cm_full_support_invariants sp ap nilslot p).
 - apply cm_full_support_initial;destruct SOURCE as[_[_[st[ctl[RUN[SUCCESS _]]]]]];exists st,ctl,status;auto.
 - intros ast H;now apply cm_full_support_step.
 - intros ast H;exact(proj2 H).
 - exact SOURCE.
Qed.
Theorem cmc_compile_success_bridge sp p obj input output status :
 cm_semantic_wf_program(cm_source_function_policy sp)p ->cm_source_terminates sp p input output status ->
 cm_output_decodes 0(cm_rep_ops(cm_model_code(cm_source_function_policy sp)p))(cm_rep_imms(cm_model_code(cm_source_function_policy sp)p))(cm_model_data_bytes p)obj ->
 tvm_terminates obj input output status.
Proof. intros WF SOURCE DECODE;rewrite(cm_decoded_model_unique _ _ _ WF DECODE);now apply cmc_preservation. Qed.
