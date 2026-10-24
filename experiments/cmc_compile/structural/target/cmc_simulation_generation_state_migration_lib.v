Require Export SimpleC.EE.QCP_demos_human.cmc_simulation_generation_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_state_store_generation policy p fid ty ptr v st : cm_state_generation_below policy p fid st ->
 cm_value_generation_below (cm_state_nextgen st) v -> cm_state_generation_below policy p fid (cm_state_store ty ptr v st).
Proof.
 intros [B [E T]] V; unfold cm_state_generation_below,cm_state_store; cbv beta iota zeta delta [cm_state_nextgen cm_state_env cm_state_tags] in *. split; [exact B|]; split; [exact E|].
 unfold cm_tags_generation_below; intro a; destruct (cm_is_pointerb ty); [destruct (a=?cm_value_number st ptr); [now apply cm_convert_value_generation|apply T]|apply T].
Qed.
Lemma cm_state_io_generation policy p fid st input output : cm_state_generation_below policy p fid st -> cm_state_generation_below policy p fid (cm_state_io st input output).
Proof. exact (fun H=>H). Qed.
Lemma cm_activate_local_generation sp p fid slot st : cm_state_generation_below (cm_source_function_policy sp) p fid st ->
 cm_state_generation_below (cm_source_function_policy sp) p fid (cm_activate_local sp p fid slot st).
Proof.
 intros [B [E T]]; unfold cm_state_generation_below,cm_activate_local; cbv beta iota zeta delta [cm_state_nextgen cm_state_env cm_state_tags] in *. split; [lia|]; split.
 - destruct E as [G [L A]]; unfold cm_env_generation_below; repeat split; intros index H; cbn [andb].
   + eapply cm_value_generation_below_mono; [|now apply G]; lia.
   + destruct (index=?slot); cbn; [lia|].
     eapply cm_value_generation_below_mono; [|now apply L]; lia.
   + eapply cm_value_generation_below_mono; [|now apply A]; lia.
 - eapply cm_tags_generation_below_mono; [|exact T]; lia.
Qed.
Lemma cm_restore_call_generation policy p fid oldfid st env fp regions : cm_state_generation_below policy p oldfid st ->
 cm_env_generation_below policy p fid (cm_state_nextgen st) env -> cm_state_generation_below policy p fid (cm_restore_call st env fp regions).
Proof. unfold cm_state_generation_below; cbv beta iota zeta delta [cm_restore_call cm_state_nextgen cm_state_env cm_state_tags]; tauto. Qed.
Lemma cm_call_base_generation sp p caller fid st : cm_state_generation_below (cm_source_function_policy sp) p caller st ->
 cm_state_generation_below (cm_source_function_policy sp) p fid (cm_call_base_state sp p fid st).
Proof.
 intros [B [[G [L A]] T]]; pose proof (ListLib.General.Length.Zlength_nonneg (cm_function_params (cm_source_function_at sp fid p))) as LEN.
 unfold cm_state_generation_below,cm_call_base_state; cbv beta iota zeta delta [cm_state_nextgen cm_state_env cm_state_tags] in *; split; [lia|]; split.
 - unfold cm_env_generation_below,cm_call_env; repeat split; intros index H; cbn; try exact I.
   + eapply cm_value_generation_below_mono; [|now apply G]; lia.
   + cbv beta iota zeta delta [cm_value_generation_below]; unfold cm_source_function_at in *; lia.
 - eapply cm_tags_generation_below_mono; [|exact T]; lia.
Qed.
Lemma cm_store_params_nextgen sp p fid values index st : cm_state_nextgen (cm_store_params sp p fid values index st)=cm_state_nextgen st.
Proof. revert index st; induction values; intros; cbv beta iota zeta delta [cm_store_params]; [reflexivity|rewrite IHvalues; reflexivity]. Qed.
Lemma cm_store_params_generation sp p fid values index st : cm_state_generation_below (cm_source_function_policy sp) p fid st ->
 cm_values_generation_below (cm_state_nextgen st) values -> cm_state_generation_below (cm_source_function_policy sp) p fid (cm_store_params sp p fid values index st).
Proof. revert index st; induction values; intros index st H V; [exact H|]. destruct V as [V VS]; cbv beta iota zeta delta [cm_store_params]. apply IHvalues; [now apply cm_state_store_generation|exact VS]. Qed.
Lemma cm_enter_call_nextgen sp p fid values st : cm_state_nextgen (cm_enter_call sp p fid values st)=cm_state_nextgen st+Zlength (cm_function_params (cm_source_function_at sp fid p)).
Proof. unfold cm_enter_call; rewrite cm_store_params_nextgen; reflexivity. Qed.
Lemma cm_enter_call_generation sp p caller fid values st : cm_state_generation_below (cm_source_function_policy sp) p caller st ->
 cm_values_generation_below (cm_state_nextgen st) values -> cm_state_generation_below (cm_source_function_policy sp) p fid (cm_enter_call sp p fid values st).
Proof.
 intros H V; unfold cm_enter_call; apply cm_store_params_generation; [eapply cm_call_base_generation; exact H|].
 eapply cm_values_generation_below_mono; [|exact V]. cbv beta iota zeta delta [cm_call_base_state cm_state_nextgen] in *; pose proof (ListLib.General.Length.Zlength_nonneg (cm_function_params (cm_source_function_at sp fid p))); lia.
Qed.
Lemma cm_env_binding_generation policy p fid limit env scope slot : cm_env_generation_below policy p fid limit env ->
 cm_binding_valid p (cm_function_at policy fid (cm_program_functions p)) scope slot -> cm_value_generation_below limit (env scope slot).
Proof.
 intros [G [L A]]; unfold cm_binding_valid; intros [[-> B]|[[-> B]|[-> B]]]; auto.
Qed.
Lemma cm_state_generation_limit_positive policy p fid st : cm_state_generation_below policy p fid st -> 0<=cm_state_nextgen st.
Proof. intros [B _]; pose proof (cm_first_dynamic_generation_positive p); lia. Qed.
