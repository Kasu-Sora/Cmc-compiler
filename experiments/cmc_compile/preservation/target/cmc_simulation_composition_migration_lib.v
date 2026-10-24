Require Export SimpleC.EE.QCP_demos_human.cmc_simulation_code_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
(* Composition lemmas, not the missing cmc_preservation theorem.
   The invariant's initialization, transition and simulation projection are
   explicit arguments. No caller contract may assume these arguments. *)
Lemma cm_annotated_source_outcome sp ap ast st ctl status :
 cm_exec sp (cm_astate_task ast) (CMOutcome st ctl status) ->
 exists n, cm_astate_task (cm_annotated_iter sp ap n ast)=CMDoneTask st ctl status.
Proof.
 intro H; apply cm_exec_witness in H; destruct H as [n [st' [ctl' [status' [Hn E]]]]].
 inversion E; subst; exists n; rewrite cm_annotated_iter_task; exact Hn.
Qed.
Lemma cm_annotated_invariant_induction sp ap (Inv:cm_astate->Prop) :
 (forall ast, Inv ast -> Inv (cm_annotated_step sp ap ast)) ->
 forall n ast, Inv ast -> Inv (cm_annotated_iter sp ap n ast).
Proof. intros Hstep n; induction n; intros ast H; [exact H|apply IHn; now apply Hstep]. Qed.
Lemma cm_simulated_annotated_outcome sp ap policy p n ast st ctl status :
 cm_astate_task (cm_annotated_iter sp ap n ast)=CMDoneTask st ctl status ->
 cm_astate_sim policy p (cm_annotated_iter sp ap n ast) ->
 exists vm, tvm_exec (cm_astate_target ast) (TVMOutcome vm status 0) /\ tvm_output vm=cm_state_output st.
Proof.
 intros Hdone Hsim; unfold cm_astate_sim in Hsim; rewrite Hdone in Hsim.
 destruct (cm_done_target_exec _ _ _ _ _ _ _ Hsim) as [vm [Hrun Hout]].
 exists vm; split; [eapply cm_annotated_iter_exec_prefix; exact Hrun|exact Hout].
Qed.
Lemma cm_successful_exec_from_invariant sp ap p input st ctl status (Inv:cm_astate->Prop) :
 Inv (cm_annotated_start (cm_source_function_policy sp) p input) ->
 (forall ast, Inv ast -> Inv (cm_annotated_step sp ap ast)) ->
 (forall ast, Inv ast -> cm_astate_sim (cm_source_function_policy sp) p ast) ->
 cm_exec sp (CMStartTask p input) (CMOutcome st ctl status) ->
 exists vm, tvm_exec (TVMBoot (cm_compile_model (cm_source_function_policy sp) p) input) (TVMOutcome vm status 0) /\ tvm_output vm=cm_state_output st.
Proof.
 intros Hinit Hstep Hsim Hexec.
 destruct (cm_annotated_source_outcome sp ap (cm_annotated_start (cm_source_function_policy sp) p input) st ctl status Hexec) as [n Hdone].
 eapply (cm_simulated_annotated_outcome sp ap (cm_source_function_policy sp) p n (cm_annotated_start (cm_source_function_policy sp) p input) st ctl status); [exact Hdone|]. apply Hsim.
 eapply cm_annotated_invariant_induction; eauto.
Qed.
Lemma cm_source_termination_from_invariant sp ap p input output status (Inv:cm_astate->Prop) :
 Inv (cm_annotated_start (cm_source_function_policy sp) p input) ->
 (forall ast, Inv ast -> Inv (cm_annotated_step sp ap ast)) ->
 (forall ast, Inv ast -> cm_astate_sim (cm_source_function_policy sp) p ast) ->
 cm_source_terminates sp p input output status ->
 tvm_terminates (cm_compile_model (cm_source_function_policy sp) p) input output status.
Proof.
 intros Hinit Hstep Hsim [Hin [Hstatus [st [ctl [Hrun [Hctl Hout]]]]]].
 split; [now apply cm_valid_input_bridge|split; [exact Hstatus|]].
 destruct (cm_successful_exec_from_invariant sp ap p input st ctl status Inv Hinit Hstep Hsim Hrun) as [vm [Hv Ho]].
 exists vm; split; [exact Hv|congruence].
Qed.
Lemma cm_compile_success_from_model_termination policy p obj input output status :
 cm_semantic_wf_program policy p ->
 cm_output_decodes 0 (cm_rep_ops (cm_model_code policy p)) (cm_rep_imms (cm_model_code policy p)) (cm_model_data_bytes p) obj ->
 tvm_terminates (cm_compile_model policy p) input output status ->
 tvm_terminates obj input output status.
Proof. intros Hwf Hdecode Hterm; rewrite (cm_decoded_model_unique _ _ _ Hwf Hdecode); exact Hterm. Qed.
