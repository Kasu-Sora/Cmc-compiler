Require Export SimpleC.EE.QCP_demos_human.cmc_param_store_fields_migration_lib.
From AUXLib Require Import ListLib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Definition cm_parameter_state_store sp p fid index value st :=
 cm_state_store(cm_slot_ty(cm_source_slot_at sp index(cm_function_params(cm_source_function_at sp fid p))))(cm_state_env st 2 index)value st.
Lemma cm_store_params_env sp p fid values index st : cm_state_env(cm_store_params sp p fid values index st)=cm_state_env st.
Proof. revert index st;induction values;intros;[reflexivity|cbn[cm_store_params];rewrite IHvalues;reflexivity]. Qed.
Lemma cm_store_params_value_number sp p fid values index st v :cm_value_number(cm_store_params sp p fid values index st)v=cm_value_number st v.
Proof. unfold cm_value_number;rewrite cm_store_params_regions;reflexivity. Qed.
Lemma cm_parameter_store_pointwise sp p fid index value a b :cm_state_pointwise_eq a b ->
 cm_state_pointwise_eq(cm_parameter_state_store sp p fid index value a)(cm_parameter_state_store sp p fid index value b).
Proof.
 intro EQ;pose proof EQ as[_[_[_[_[ENV _]]]]];unfold cm_parameter_state_store;rewrite(ENV 2 index);now apply cm_pointwise_store.
Qed.
Lemma cm_params_pointwise sp p fid values index a b :cm_state_pointwise_eq a b ->
 cm_state_pointwise_eq(cm_store_params sp p fid values index a)(cm_store_params sp p fid values index b).
Proof.
 revert index a b;induction values as[|v vs IH];intros index a b EQ;[exact EQ|].
 cbn[cm_store_params];apply IH;change(cm_state_pointwise_eq(cm_parameter_state_store sp p fid index v a)(cm_parameter_state_store sp p fid index v b));now apply cm_parameter_store_pointwise.
Qed.
Lemma cm_store_params_push_disjoint sp p fid values index st ty ptr value :
 (forall j,index<=j<index+Zlength values ->cm_range_disjoint(cm_value_number st ptr)(cm_store_width ty)
  (cm_value_number st(cm_state_env st 2 j))(cm_store_width(cm_slot_ty(cm_source_slot_at sp j(cm_function_params(cm_source_function_at sp fid p)))))) ->
 cm_state_pointwise_eq
 (cm_state_store ty ptr value(cm_store_params sp p fid values index st))
 (cm_store_params sp p fid values index(cm_state_store ty ptr value st)).
Proof.
 revert index st;induction values as[|v vs IH];intros index st DIS;[apply cm_state_pointwise_refl|].
 cbn[cm_store_params]. eapply cm_state_pointwise_trans.
 - apply IH;intros j J;rewrite !cm_store_value_number;apply DIS;rewrite Zlength_cons;lia.
 - apply cm_params_pointwise;cbn[cm_state_env];apply cm_state_store_commutes.
   apply DIS;pose proof(Zlength_nonneg vs);rewrite Zlength_cons;lia.
Qed.
Lemma cm_store_params_reverse_forward_disjoint sp p fid values index st :
 (forall i j,index<=i<j ->j<index+Zlength values ->
 cm_range_disjoint(cm_value_number st(cm_state_env st 2 i))(cm_store_width(cm_slot_ty(cm_source_slot_at sp i(cm_function_params(cm_source_function_at sp fid p)))))
 (cm_value_number st(cm_state_env st 2 j))(cm_store_width(cm_slot_ty(cm_source_slot_at sp j(cm_function_params(cm_source_function_at sp fid p)))))) ->
 cm_state_pointwise_eq(cm_store_params_reverse sp p fid values index st)(cm_store_params sp p fid values index st).
Proof.
 revert index st;induction values as[|v vs IH];intros index st DIS;[apply cm_state_pointwise_refl|].
 change(cm_state_pointwise_eq
 (cm_parameter_state_store sp p fid index v(cm_store_params_reverse sp p fid vs(index+1)st))
 (cm_store_params sp p fid vs(index+1)(cm_parameter_state_store sp p fid index v st))).
 eapply cm_state_pointwise_trans.
 - apply cm_parameter_store_pointwise;apply IH;intros i j I J;apply DIS;[lia|rewrite Zlength_cons;lia].
 - unfold cm_parameter_state_store;rewrite cm_store_params_env;apply cm_store_params_push_disjoint.
   intros j J;apply DIS;[lia|rewrite Zlength_cons;lia].
Qed.
