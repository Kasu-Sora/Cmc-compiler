Require Export SimpleC.EE.QCP_demos_human.cmc_call_store_commutation_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Definition cm_tags_write (flag:bool) base value (tags:Z->cm_value) x :=if flag then if x=?base then value else tags x else tags x.
Definition cm_tagged_write (flag:bool) base width (nonzero:bool) (tags:Z->bool) x :=((flag&&(x=?base))&&nonzero)||cm_clear_tagged tags base width x.
Lemma cm_tags_write_commutes fa fb a b va vb tags x :a<>b ->
 cm_tags_write fa a va(cm_tags_write fb b vb tags)x=cm_tags_write fb b vb(cm_tags_write fa a va tags)x.
Proof.
 intro NE;unfold cm_tags_write;destruct fa,fb,(x=?a)eqn:A,(x=?b)eqn:B;try reflexivity;apply Z.eqb_eq in A,B;congruence.
Qed.
Lemma cm_boolean_writes_commute old ca cb ka kb : (ca=true ->kb=true) ->(cb=true ->ka=true) ->
 ca||((cb||(old&&kb))&&ka)=cb||((ca||(old&&ka))&&kb).
Proof. destruct old,ca,cb,ka,kb;cbn;intuition discriminate. Qed.
Lemma cm_tagged_write_commutes fa fb a aw b bw na nb tags x :
 (fa=true ->aw=8) ->(fb=true ->bw=8) ->cm_range_disjoint a aw b bw ->
 cm_tagged_write fa a aw na(cm_tagged_write fb b bw nb tags)x=cm_tagged_write fb b bw nb(cm_tagged_write fa a aw na tags)x.
Proof.
 intros WA WB DIS;unfold cm_tagged_write,cm_clear_tagged;apply cm_boolean_writes_commute.
 - intro CREATE;apply andb_true_iff in CREATE;destruct CREATE as[C _];apply andb_true_iff in C;destruct C as[FA A];apply Z.eqb_eq in A;subst x;specialize(WA FA);subst aw.
   apply negb_true_iff;apply not_true_is_false;intro OVER;repeat rewrite andb_true_iff in OVER;destruct OVER as[[P L]H];apply Z.ltb_lt in P,L,H;unfold cm_range_disjoint in DIS;lia.
 - intro CREATE;apply andb_true_iff in CREATE;destruct CREATE as[C _];apply andb_true_iff in C;destruct C as[FB B];apply Z.eqb_eq in B;subst x;specialize(WB FB);subst bw.
   apply negb_true_iff;apply not_true_is_false;intro OVER;repeat rewrite andb_true_iff in OVER;destruct OVER as[[P L]H];apply Z.ltb_lt in P,L,H;unfold cm_range_disjoint in DIS;lia.
Qed.
Lemma cm_convert_store ty ptr v st other w :cm_convert_value(cm_state_store ty ptr v st)other w=cm_convert_value st other w.
Proof. destruct other;cbn[cm_convert_value];try reflexivity;now rewrite cm_store_value_number. Qed.
Lemma cm_state_store_mem ty ptr v st :cm_state_mem(cm_state_store ty ptr v st)=cm_store_mem ty(cm_value_number st ptr)(cm_value_number st(cm_convert_value st ty v))(cm_state_mem st).
Proof. reflexivity. Qed.
Lemma cm_state_store_init ty ptr v st :cm_state_init(cm_state_store ty ptr v st)=cm_mark_init(cm_state_init st)(cm_value_number st ptr)(cm_store_width ty).
Proof. reflexivity. Qed.
Lemma cm_state_store_tags ty ptr v st :cm_state_tags(cm_state_store ty ptr v st)=cm_tags_write(cm_is_pointerb ty)(cm_value_number st ptr)(cm_convert_value st ty v)(cm_state_tags st).
Proof. destruct ty;reflexivity. Qed.
Lemma cm_state_store_tagged ty ptr v st :cm_state_tagged(cm_state_store ty ptr v st)=cm_tagged_write(cm_is_pointerb ty)(cm_value_number st ptr)(cm_store_width ty)(negb(cm_value_number st(cm_convert_value st ty v)=?0))(cm_state_tagged st).
Proof. destruct ty;reflexivity. Qed.
Lemma cm_state_store_commutes ta tb pa pb va vb st :
 cm_range_disjoint(cm_value_number st pa)(cm_store_width ta)(cm_value_number st pb)(cm_store_width tb) ->
 cm_state_pointwise_eq(cm_state_store ta pa va(cm_state_store tb pb vb st))(cm_state_store tb pb vb(cm_state_store ta pa va st)).
Proof.
 intro DIS;unfold cm_state_pointwise_eq;repeat split;intros;try reflexivity.
 - rewrite !cm_state_store_mem,!cm_store_value_number,!cm_convert_store;apply cm_store_mem_commutes_at;exact DIS.
 - rewrite !cm_state_store_init,!cm_store_value_number;symmetry;apply cm_mark_init_commutes.
 - rewrite !cm_state_store_tags,!cm_store_value_number,!cm_convert_store;apply cm_tags_write_commutes;pose proof(cm_store_width_positive ta);pose proof(cm_store_width_positive tb);unfold cm_range_disjoint in DIS;lia.
 - rewrite !cm_state_store_tagged,!cm_store_value_number,!cm_convert_store;apply cm_tagged_write_commutes;[now apply cm_pointer_store_width|now apply cm_pointer_store_width|exact DIS].
Qed.
