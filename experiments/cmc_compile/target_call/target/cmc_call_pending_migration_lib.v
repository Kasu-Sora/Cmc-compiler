Require Export SimpleC.EE.QCP_demos_human.cmc_target_control_invariant_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
(* Exact pending-parameter state from cmc_preservation_call_pending.c.
   Clearing initialization here is an intermediate proof construction only;
   cm_call_base_state and the source execution semantics are unchanged. *)
Definition cm_call_param_span sp p fid :=cm_slots_size(cm_program_structs p)(cm_function_params(cm_source_function_at sp fid p)).
Definition cm_call_pending_base sp p fid st :=
 let base:=cm_call_base_state sp p fid st in let start:=cm_state_fp base+8 in
 CMState(cm_state_mem base)(cm_clear_init(cm_state_init st)start(cm_call_param_span sp p fid))
 (cm_state_tags st)(cm_clear_tagged(cm_state_tagged st)start(cm_call_param_span sp p fid))
 (cm_state_env base)(cm_state_input st)(cm_state_output st)(cm_state_fp base)(cm_state_nextgen base)(cm_state_regions base).
Fixpoint cm_store_params_reverse sp p fid values index st :=match values with
 | []=>st
 | v::rest=>let after:=cm_store_params_reverse sp p fid rest(index+1)st in
 cm_state_store(cm_slot_ty(cm_source_slot_at sp index(cm_function_params(cm_source_function_at sp fid p))))(cm_state_env after 2 index)v after end.
Lemma cm_call_pending_structure sp p fid st :
 cm_state_regions(cm_call_pending_base sp p fid st)=cm_state_regions(cm_call_base_state sp p fid st) /\
 cm_state_fp(cm_call_pending_base sp p fid st)=cm_state_fp(cm_call_base_state sp p fid st) /\
 cm_state_nextgen(cm_call_pending_base sp p fid st)=cm_state_nextgen(cm_call_base_state sp p fid st) /\
 cm_state_env(cm_call_pending_base sp p fid st)=cm_state_env(cm_call_base_state sp p fid st) /\
 cm_state_mem(cm_call_pending_base sp p fid st)=cm_state_mem(cm_call_base_state sp p fid st) /\
 cm_state_input(cm_call_pending_base sp p fid st)=cm_state_input st /\cm_state_output(cm_call_pending_base sp p fid st)=cm_state_output st.
Proof. repeat split;reflexivity. Qed.
Lemma cm_call_pending_bases sp p fid st :cm_region_bases_below_equal(cm_state_regions(cm_call_pending_base sp p fid st))(cm_state_regions st)(cm_state_nextgen st).
Proof. apply cm_regions_for_slots_bases;lia. Qed.
Lemma cm_call_pending_live_old_or_param sp p fid st a :
 cm_function_wf(cm_source_function_policy sp)p(cm_source_function_at sp fid p) ->cm_regions_before(cm_state_regions st)(cm_state_nextgen st) ->
 cm_live_address(cm_call_pending_base sp p fid st)a ->cm_live_address st a \/
 (cm_state_fp(cm_call_pending_base sp p fid st)+8<=a /\ a<cm_state_fp(cm_call_pending_base sp p fid st)+8+cm_call_param_span sp p fid).
Proof. exact(cm_call_base_live_old_or_param sp p fid st a). Qed.
Lemma cm_call_pending_value_number sp p fid st v :cm_value_generation_below(cm_state_nextgen st)v ->cm_value_number(cm_call_pending_base sp p fid st)v=cm_value_number st v.
Proof. intro GEN;eapply cm_value_number_bases;[apply cm_call_pending_bases|exact GEN]. Qed.
Lemma cm_store_params_reverse_structure sp p fid values index st :
 cm_state_env(cm_store_params_reverse sp p fid values index st)=cm_state_env st /\
 cm_state_regions(cm_store_params_reverse sp p fid values index st)=cm_state_regions st /\
 cm_state_fp(cm_store_params_reverse sp p fid values index st)=cm_state_fp st /\
 cm_state_nextgen(cm_store_params_reverse sp p fid values index st)=cm_state_nextgen st /\
 cm_state_input(cm_store_params_reverse sp p fid values index st)=cm_state_input st /\
 cm_state_output(cm_store_params_reverse sp p fid values index st)=cm_state_output st.
Proof. revert index;induction values as[|v rest IH];intro index;[repeat split;reflexivity|exact(IH(index+1))]. Qed.
Lemma cm_store_params_reverse_value_number sp p fid values index st v :cm_value_number(cm_store_params_reverse sp p fid values index st)v=cm_value_number st v.
Proof. revert index;induction values as[|w rest IH];intro index;[reflexivity|cbn[cm_store_params_reverse];rewrite cm_store_value_number;apply IH]. Qed.
