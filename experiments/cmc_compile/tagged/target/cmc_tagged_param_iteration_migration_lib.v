Require Export SimpleC.EE.QCP_demos_human.cmc_tagged_partial_params_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_store_params_tagged_except sp p fid values index st address finish :
 (forall j, index<=j<index+Zlength values ->
 cm_value_number st (cm_state_env st 2 j)=address j /\
 address j+cm_store_width (cm_slot_ty (cm_source_slot_at sp j (cm_function_params (cm_source_function_at sp fid p))))=address (j+1) /\
 (cm_is_pointerb (cm_slot_ty (cm_source_slot_at sp j (cm_function_params (cm_source_function_at sp fid p))))=true -> cm_live_span st (address j) 8)) ->
 cm_tagged_span_except st (address index) finish ->
 cm_tagged_span_except (cm_store_params sp p fid values index st) (address (index+Zlength values)) finish.
Proof.
 revert index st; induction values as [|v rest IH]; intros index st FACT VALID.
 - rewrite Zlength_nil,Z.add_0_r; exact VALID.
 - replace (index+Zlength (v::rest)) with ((index+1)+Zlength rest) by (rewrite Zlength_cons; lia).
   cbn [cm_store_params]; apply IH.
   + intros j J; destruct (FACT j ltac:(rewrite Zlength_cons; lia)) as [ADDR [NEXT SPAN]].
     split; [rewrite cm_store_value_number; exact ADDR|]; split; [exact NEXT|exact SPAN].
   + pose proof (ListLib.General.Length.Zlength_nonneg rest) as N.
     destruct (FACT index ltac:(rewrite Zlength_cons; lia)) as [ADDR [NEXT SPAN]].
     rewrite <-NEXT,<-ADDR; apply cm_tagged_span_except_store; [now rewrite ADDR|now rewrite ADDR].
Qed.
Lemma cm_slots_prefix_successor_nat structs slots i : (i<length slots)%nat ->
 cm_slots_prefix structs slots (Z.of_nat (S i))=cm_slots_prefix structs slots (Z.of_nat i)+cm_slot_size structs (nth i slots cm_default_slot).
Proof.
 revert i; induction slots as [|s slots IH]; intros i B; [cbn in B; lia|]. destruct i as [|i].
 - change (cm_slot_size structs s+cm_slots_prefix structs slots 0=0+cm_slot_size structs s); destruct slots; change (cm_slot_size structs s+0=0+cm_slot_size structs s); lia.
 - assert (A:(Z.of_nat (S (S i))=?0)=false) by (apply Z.eqb_neq; lia).
   assert (B0:(Z.of_nat (S i)=?0)=false) by (apply Z.eqb_neq; lia).
   cbn [cm_slots_prefix nth]; rewrite A,B0.
   replace (Z.of_nat (S (S i))-1) with (Z.of_nat (S i)) by lia.
   replace (Z.of_nat (S i)-1) with (Z.of_nat i) by lia.
   rewrite IH by (cbn in B; lia); lia.
Qed.
Lemma cm_slots_prefix_successor structs slots i : 0<=i<Zlength slots ->
 cm_slots_prefix structs slots (i+1)=cm_slots_prefix structs slots i+cm_slot_size structs (cm_slot_at i slots).
Proof.
 intro B; pose proof (cm_slots_prefix_successor_nat structs slots (Z.to_nat i) ltac:(rewrite Zlength_correct in B; lia)) as H.
 rewrite Nat2Z.inj_succ,Z2Nat.id in H by lia; replace (Z.succ i) with (i+1) in H by lia; exact H.
Qed.
Lemma cm_slots_prefix_length structs slots : cm_slots_prefix structs slots (Zlength slots)=cm_slots_size structs slots.
Proof.
 induction slots as [|s slots IH]; [reflexivity|]. replace (Zlength (s::slots)) with (Zlength slots+1) by (rewrite Zlength_cons; lia); cbn [cm_slots_prefix cm_slots_size].
 assert (B:(Zlength slots+1=?0)=false) by (apply Z.eqb_neq; pose proof (ListLib.General.Length.Zlength_nonneg slots); lia).
 rewrite B; replace (Zlength slots+1-1) with (Zlength slots) by lia; now rewrite IH.
Qed.
