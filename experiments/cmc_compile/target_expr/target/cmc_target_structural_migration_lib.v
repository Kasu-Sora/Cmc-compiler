Require Export SimpleC.EE.QCP_demos_human.cmc_code_layout_invariant_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Definition cm_target_step_result sp ap p task target ann :=
 cm_task_target_sim (cm_source_function_policy sp) p (cm_step sp task)
 (tvm_iter (cm_update_steps(cm_annotation_step sp ap task ann)) target)
 (cm_update_annotation(cm_annotation_step sp ap task ann)).
Lemma cm_target_r_structural_step sp ap p fid expr st ks target ann :
 (match expr with
 | CMVarE scope slot _ =>cm_binding_array sp p fid scope slot=false
 | CMConstE _ _ | CMStringE _ _ | CMSizeofE _ _ | CMGetcE _=>False
 | CMCallE _ args _=>args<>[]
 | _=>True end) ->
 cm_task_target_sim (cm_source_function_policy sp) p (CMRTask p fid expr st ks) target ann ->
 cm_target_step_result sp ap p (CMRTask p fid expr st ks) target ann.
Proof.
 intros GUARD [_ SIM]; destruct expr; try contradiction;
 unfold cm_target_step_result; cbn [cm_step cm_rstart cm_args_start cm_annotation_step cm_update_r];
 try rewrite GUARD; try (destruct (op=?2); [|destruct(op=?3)]);
 try match goal with |-context[cm_member_array ?sp ?p ?ty ?mid]=>destruct(cm_member_array sp p ty mid) end;
 try (destruct args; [contradiction|]);
 cbn [cm_list_empty cm_update_steps cm_update_annotation tvm_iter cm_task_target_sim].
 all: split; [reflexivity|exact SIM].
Qed.
Lemma cm_target_l_structural_step sp ap p fid expr st ks target ann :
 (match expr with CMUnaryE op _ _=>op=2 | CMIndexE _ _ _ | CMMemberE _ _ _=>True | _=>False end) ->
 cm_task_target_sim (cm_source_function_policy sp) p (CMLTask p fid expr st ks) target ann ->
 cm_target_step_result sp ap p (CMLTask p fid expr st ks) target ann.
Proof.
 intros GUARD [_ SIM]; destruct expr; try contradiction;
 unfold cm_target_step_result; cbn [cm_step cm_lstart cm_annotation_step cm_update_l]; try subst op;
 cbn [Z.eqb cm_update_steps cm_update_annotation tvm_iter cm_task_target_sim].
 all: split; [reflexivity|exact SIM].
Qed.
Lemma cm_target_done_step sp ap p st ctl status target ann :
 cm_task_target_sim (cm_source_function_policy sp) p (CMDoneTask st ctl status) target ann ->
 cm_target_step_result sp ap p (CMDoneTask st ctl status) target ann.
Proof. exact (fun x=>x). Qed.
