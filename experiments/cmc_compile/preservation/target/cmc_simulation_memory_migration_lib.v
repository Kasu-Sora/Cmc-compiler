Require Export SimpleC.EE.QCP_demos_human.cmc_annotation_invariant_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma tower_wrap64_periodic z k : tower_wrap64 (z+k*18446744073709551616)=tower_wrap64 z.
Proof. unfold tower_wrap64. replace (z+k*18446744073709551616+9223372036854775808) with (z+9223372036854775808+k*18446744073709551616) by ring. rewrite Z.mod_add by lia; reflexivity. Qed.
Lemma tower_decode_encode z :
 tower_decode8 (tower_encode_byte z 0) (tower_encode_byte z 1) (tower_encode_byte z 2) (tower_encode_byte z 3)
 (tower_encode_byte z 4) (tower_encode_byte z 5) (tower_encode_byte z 6) (tower_encode_byte z 7)=tower_wrap64 z.
Proof.
 unfold tower_decode8,tower_encode_byte; cbn [Z.eqb Pos.eqb]; repeat rewrite tower_u8_idempotent; unfold tower_u8.
 set (q1:=z/256). set (q2:=q1/256). set (q3:=q2/256). set (q4:=q3/256).
 set (q5:=q4/256). set (q6:=q5/256). set (q7:=q6/256). set (q8:=q7/256).
 assert (E0:z=256*q1+z mod 256) by (apply Z.div_mod; lia).
 assert (E1:q1=256*q2+q1 mod 256) by (apply Z.div_mod; lia).
 assert (E2:q2=256*q3+q2 mod 256) by (apply Z.div_mod; lia).
 assert (E3:q3=256*q4+q3 mod 256) by (apply Z.div_mod; lia).
 assert (E4:q4=256*q5+q4 mod 256) by (apply Z.div_mod; lia).
 assert (E5:q5=256*q6+q5 mod 256) by (apply Z.div_mod; lia).
 assert (E6:q6=256*q7+q6 mod 256) by (apply Z.div_mod; lia).
 assert (E7:q7=256*q8+q7 mod 256) by (apply Z.div_mod; lia).
 replace (z mod 256 + 256*(q1 mod 256) + 65536*(q2 mod 256) + 16777216*(q3 mod 256) + 4294967296*(q4 mod 256) + 1099511627776*(q5 mod 256) + 281474976710656*(q6 mod 256) + 72057594037927936*(q7 mod 256)) with (z+(-q8)*18446744073709551616) by lia.
 apply tower_wrap64_periodic.
Qed.
Ltac tower_offset_eqb := repeat match goal with |- context[?x =? ?y] =>
 first [let E:=fresh in assert (E:(x =? y)=true) by (apply Z.eqb_eq; lia); rewrite E; clear E |
 let E:=fresh in assert (E:(x =? y)=false) by (apply Z.eqb_neq; lia); rewrite E; clear E] end.
Lemma tower_getw_setw m a z : tower_getw (tower_setw m a z) a=tower_wrap64 z.
Proof. unfold tower_getw,tower_getb,tower_setw. tower_offset_eqb. unfold tower_decode8 at 1. repeat rewrite tower_u8_idempotent. change (tower_decode8 (tower_encode_byte z 0) (tower_encode_byte z 1) (tower_encode_byte z 2) (tower_encode_byte z 3) (tower_encode_byte z 4) (tower_encode_byte z 5) (tower_encode_byte z 6) (tower_encode_byte z 7)=tower_wrap64 z). apply tower_decode_encode. Qed.
Lemma cm_store_width_positive ty : 0<cm_store_width ty.
Proof. destruct ty; cbn; lia. Qed.
Lemma cm_store_mem_word_outside ty base n mem a : a+8<=base \/ base+cm_store_width ty<=a ->
 tower_getw (cm_store_mem ty base n mem) a=tower_getw mem a.
Proof. intro H; apply tower_getw_ext; intros i Hi; apply cm_store_mem_outside; lia. Qed.
Lemma cm_clear_tagged_survives old base width a : 0<width -> cm_clear_tagged old base width a=true ->
 old a=true /\ (a+8<=base \/ base+width<=a).
Proof.
 unfold cm_clear_tagged; intros Hw H; apply Bool.andb_true_iff in H; destruct H as [H Hn]; split; [exact H|].
 apply Bool.negb_true_iff in Hn. repeat rewrite Bool.andb_false_iff in Hn.
 destruct Hn as [[Hn|Hn]|Hn]; [apply Z.ltb_ge in Hn|apply Z.ltb_ge in Hn|apply Z.ltb_ge in Hn]; lia.
Qed.
Lemma cm_store_preserved_tag ty ptr v st a :
 cm_clear_tagged (cm_state_tagged st) (cm_value_number st ptr) (cm_store_width ty) a=true ->
 cm_state_tagged st a=true /\
 (a+8<=cm_value_number st ptr \/ cm_value_number st ptr+cm_store_width ty<=a) /\
 cm_state_tags (cm_state_store ty ptr v st) a=cm_state_tags st a.
Proof.
 intro H; destruct (cm_clear_tagged_survives _ _ _ _ (cm_store_width_positive ty) H) as [Ht Hd].
 split; [exact Ht|split; [exact Hd|]].
 cbn [cm_state_store cm_state_tags]. destruct (cm_is_pointerb ty); [|reflexivity].
 destruct (a =? cm_value_number st ptr) eqn:E; [apply Z.eqb_eq in E; pose proof (cm_store_width_positive ty); exfalso; lia|reflexivity].
Qed.
Lemma cm_store_old_provenance_sim ty ptr v st vmem a : cm_stored_provenance_sim st vmem ->
 cm_clear_tagged (cm_state_tagged st) (cm_value_number st ptr) (cm_store_width ty) a=true -> cm_live_address st a ->
 cm_state_init (cm_state_store ty ptr v st) a=true /\
 tower_getw (cm_store_mem ty (cm_value_number st ptr) (cm_value_number st (cm_convert_value st ty v)) vmem) a=
 cm_value_number (cm_state_store ty ptr v st) (cm_state_tags (cm_state_store ty ptr v st) a).
Proof.
 intros Hsim Htag Hlive; destruct (cm_store_preserved_tag ty ptr v st a Htag) as [Ht [Hd Htags]].
 destruct (Hsim a Ht Hlive) as [Hi Hv]; split.
 - change (cm_mark_init (cm_state_init st) (cm_value_number st ptr) (cm_store_width ty) a=true); unfold cm_mark_init; rewrite Hi; reflexivity.
 - rewrite Htags,cm_store_value_number,cm_store_mem_word_outside by exact Hd; exact Hv.
Qed.
Lemma cm_store_provenance_sim ty ptr v st vmem : cm_stored_provenance_sim st vmem ->
 cm_stored_provenance_sim (cm_state_store ty ptr v st)
 (cm_store_mem ty (cm_value_number st ptr) (cm_value_number st (cm_convert_value st ty v)) vmem).
Proof.
 intros Hsim a Htag Hlive.
 change (cm_live_address st a) in Hlive.
 destruct (cm_is_pointerb ty) eqn:Hp.
 - cbn [cm_state_store cm_state_tagged] in Htag; rewrite Hp in Htag.
   apply Bool.orb_true_iff in Htag; destruct Htag as [Hnew|Hold].
   + apply Bool.andb_true_iff in Hnew; destruct Hnew as [Ha Hv]; apply Z.eqb_eq in Ha; subst a.
     split; [apply cm_store_initializes; pose proof (cm_store_width_positive ty); lia|].
     rewrite cm_store_tags_pointer by exact Hp; rewrite cm_store_value_number.
     destruct ty; cbn [cm_is_pointerb] in Hp; try discriminate;
      cbn [cm_store_mem]; rewrite tower_getw_setw,tower_wrap64_idempotent; apply cm_value_number_wrap.
   + apply cm_store_old_provenance_sim; try assumption.
     destruct ty; cbn [cm_is_pointerb] in Hp; try discriminate; exact Hold.
 - cbn [cm_state_store cm_state_tagged] in Htag; rewrite Hp in Htag.
   apply cm_store_old_provenance_sim; assumption.
Qed.
