Require Export SimpleC.EE.QCP_demos_human.cmc_param_store_order_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_address_monotone_nat (address:Z->Z) lo n :
 (forall k,lo<=k<lo+Z.of_nat n ->address k<=address(k+1)) ->address lo<=address(lo+Z.of_nat n).
Proof.
 induction n as[|n IH];intro STEP;[rewrite Z.add_0_r;lia|].
 assert(A:address lo<=address(lo+Z.of_nat n)) by(apply IH;intros;apply STEP;lia).
 pose proof(STEP(lo+Z.of_nat n)ltac:(lia));replace(lo+Z.of_nat n+1)with(lo+Z.of_nat(S n))in H by lia;lia.
Qed.
Lemma cm_address_monotone (address:Z->Z) lo hi :lo<=hi ->
 (forall k,lo<=k<hi ->address k<=address(k+1)) ->address lo<=address hi.
Proof.
 intros LE STEP;pose proof(cm_address_monotone_nat address lo(Z.to_nat(hi-lo)))as H.
 rewrite Z2Nat.id in H by lia;replace(lo+(hi-lo))with hi in H by lia;auto.
Qed.
Lemma cm_call_parameter_disjoint sp p fid st i j :
 cm_function_wf(cm_source_function_policy sp)p(cm_source_function_at sp fid p) ->
 cm_frame_segment(cm_source_function_policy sp)p fid(cm_state_fp st-cm_frame_size(cm_program_structs p)(cm_source_function_at sp fid p))(cm_state_fp st) ->
 0<=i<j ->j<Zlength(cm_function_params(cm_source_function_at sp fid p)) ->
 cm_range_disjoint(cm_value_number(cm_call_base_state sp p fid st)(cm_state_env(cm_call_base_state sp p fid st)2 i))(cm_store_width(cm_slot_ty(cm_source_slot_at sp i(cm_function_params(cm_source_function_at sp fid p)))))
 (cm_value_number(cm_call_base_state sp p fid st)(cm_state_env(cm_call_base_state sp p fid st)2 j))(cm_store_width(cm_slot_ty(cm_source_slot_at sp j(cm_function_params(cm_source_function_at sp fid p))))).
Proof.
 intros FW SEG IJ J;pose proof(cm_call_param_geometry sp p fid st i FW SEG ltac:(lia))as[A[N _]].
 pose proof(cm_call_param_geometry sp p fid st j FW SEG ltac:(lia))as[B _].
 unfold cm_range_disjoint;left;rewrite A,B,N;apply(cm_address_monotone(fun k=>cm_param_base sp p fid k(cm_state_fp st-cm_frame_size(cm_program_structs p)(cm_source_function_at sp fid p))));[lia|].
 intros k K;pose proof(cm_call_param_geometry sp p fid st k FW SEG ltac:(lia))as[_[NEXT _]].
 pose proof(cm_store_width_positive(cm_slot_ty(cm_source_slot_at sp k(cm_function_params(cm_source_function_at sp fid p)))));lia.
Qed.
Lemma cm_call_pending_numeric sp p fid st v :cm_value_number(cm_call_pending_base sp p fid st)v=cm_value_number(cm_call_base_state sp p fid st)v.
Proof. reflexivity. Qed.
Lemma cm_call_params_reverse_forward sp p fid st values index :
 cm_function_wf(cm_source_function_policy sp)p(cm_source_function_at sp fid p) ->
 cm_frame_segment(cm_source_function_policy sp)p fid(cm_state_fp st-cm_frame_size(cm_program_structs p)(cm_source_function_at sp fid p))(cm_state_fp st) ->
 0<=index ->index+Zlength values<=Zlength(cm_function_params(cm_source_function_at sp fid p)) ->
 cm_state_pointwise_eq(cm_store_params_reverse sp p fid values index(cm_call_pending_base sp p fid st))
 (cm_store_params sp p fid values index(cm_call_pending_base sp p fid st)).
Proof.
 intros FW SEG LOW BOUND;apply cm_store_params_reverse_forward_disjoint;intros i j IJ J.
 exact(cm_call_parameter_disjoint sp p fid st i j FW SEG ltac:(lia)ltac:(lia)).
Qed.
