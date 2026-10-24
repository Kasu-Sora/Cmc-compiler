Require Export SimpleC.EE.QCP_demos_human.cmc_target_parameter_step_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Definition cm_parameter_ready sp p fid st index ty :=
 ty=cm_slot_ty(cm_source_slot_at sp index(cm_function_params(cm_source_function_at sp fid p))) /\
 cm_store_ok ty(cm_state_env st 2 index)st=true /\
 cm_value_number st(cm_state_env st 2 index)=tower_wrap64(cm_state_fp st+cm_param_offset(cm_source_function_policy sp)p fid index).
Fixpoint cm_parameters_ready sp p fid st index params :=match params with
 |[]=>True|s::rest=>cm_parameter_ready sp p fid st index(cm_slot_ty s)/\cm_parameters_ready sp p fid st(index+1)rest end.
Lemma cm_store_ok_regions a b ty ptr :cm_state_regions a=cm_state_regions b ->cm_store_ok ty ptr a=cm_store_ok ty ptr b.
Proof. intro R;unfold cm_store_ok,cm_pointer_writable,cm_pointer_live,cm_value_number;now rewrite R. Qed.
Lemma cm_parameter_ready_reverse sp p fid st values start index ty :cm_parameter_ready sp p fid st index ty ->
 cm_parameter_ready sp p fid(cm_store_params_reverse sp p fid values start st)index ty.
Proof.
 intros[T[OK NUM]];destruct(cm_store_params_reverse_structure sp p fid values start st)as[E[R[F _]]].
 unfold cm_parameter_ready;rewrite E,F,cm_store_params_reverse_value_number,(cm_store_ok_regions _ st ty _ R);auto.
Qed.
Lemma cm_parameters_ready_reverse sp p fid st values start index params :cm_parameters_ready sp p fid st index params ->
 cm_parameters_ready sp p fid(cm_store_params_reverse sp p fid values start st)index params.
Proof. revert index;induction params;intros index;[auto|];cbn[cm_parameters_ready];intros[H T];split;[now apply cm_parameter_ready_reverse|now apply IHparams]. Qed.
Lemma cm_runtime_reverse_params sp p fid st values index calls frames :cm_runtime_memory_layout(cm_source_function_policy sp)p st calls frames ->
 cm_runtime_memory_layout(cm_source_function_policy sp)p(cm_store_params_reverse sp p fid values index st)calls frames.
Proof. unfold cm_runtime_memory_layout;rewrite(proj1(proj2(cm_store_params_reverse_structure sp p fid values index st)));auto. Qed.
