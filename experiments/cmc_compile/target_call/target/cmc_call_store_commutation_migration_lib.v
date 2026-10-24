Require Export SimpleC.EE.QCP_demos_human.cmc_call_observation_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_store_mem_raw_inside ty base n m1 m2 a :base<=a<base+cm_store_width ty ->cm_store_mem ty base n m1 a=cm_store_mem ty base n m2 a.
Proof.
 intro H;destruct ty;cbn[cm_store_mem cm_store_width]in *;unfold tower_setb,tower_setw;
 repeat match goal with |-context[if ?b then _ else _]=>destruct b eqn:? end;try reflexivity;
 repeat match goal with H:(_=?_)=false |- _=>apply Z.eqb_neq in H end;exfalso;lia.
Qed.
Lemma cm_store_mem_raw_outside ty base n mem a :a<base \/ base+cm_store_width ty<=a ->cm_store_mem ty base n mem a=mem a.
Proof.
 intro H;destruct ty;cbn[cm_store_mem cm_store_width]in *;unfold tower_setb,tower_setw;
 repeat match goal with |-context[if ?b then _ else _]=>destruct b eqn:? end;try reflexivity;
 repeat match goal with H:(_=?_)=true |- _=>apply Z.eqb_eq in H end;exfalso;lia.
Qed.
Lemma cm_store_mem_commutes_at ta tb a b va vb mem x :cm_range_disjoint a(cm_store_width ta)b(cm_store_width tb) ->
 cm_store_mem ta a va(cm_store_mem tb b vb mem)x=cm_store_mem tb b vb(cm_store_mem ta a va mem)x.
Proof.
 unfold cm_range_disjoint;intro DIS;pose proof(cm_store_width_positive ta)as WIDTH;destruct(Z_lt_ge_dec x a)as[L|L];destruct(Z_lt_ge_dec x(a+cm_store_width ta))as[H|H].
 - rewrite cm_store_mem_raw_outside by lia;destruct(Z_lt_ge_dec x b)as[B|B];destruct(Z_lt_ge_dec x(b+cm_store_width tb))as[T|T];
   try(rewrite !cm_store_mem_raw_outside by lia;reflexivity);apply cm_store_mem_raw_inside;lia.
 - exfalso;lia.
 - rewrite cm_store_mem_raw_outside with(ty:=tb)by lia;apply cm_store_mem_raw_inside;lia.
 - rewrite cm_store_mem_raw_outside with(ty:=ta)by lia;destruct(Z_lt_ge_dec x b)as[B|B];destruct(Z_lt_ge_dec x(b+cm_store_width tb))as[T|T];
   try(rewrite !cm_store_mem_raw_outside by lia;reflexivity);apply cm_store_mem_raw_inside;lia.
Qed.
Lemma cm_pointwise_convert_value a b ty v :cm_state_pointwise_eq a b ->cm_convert_value a ty v=cm_convert_value b ty v.
Proof. intro EQ;destruct ty;cbn[cm_convert_value];try reflexivity;now rewrite(cm_pointwise_value_number a b v EQ). Qed.
Lemma cm_store_mem_pointwise ty base value left right : (forall x,left x=right x) ->forall x,cm_store_mem ty base value left x=cm_store_mem ty base value right x.
Proof.
 intros EQ x;destruct ty;cbn[cm_store_mem];unfold tower_setb,tower_setw;
 repeat match goal with |-context[if ?b then _ else _]=>destruct b end;auto.
Qed.
Lemma cm_pointwise_store ty ptr v a b :cm_state_pointwise_eq a b ->cm_state_pointwise_eq(cm_state_store ty ptr v a)(cm_state_store ty ptr v b).
Proof.
 intro EQ;pose proof EQ as[M[I[T[G[E[IN[OUT[F[N R]]]]]]]]].
 pose proof(cm_pointwise_value_number a b ptr EQ)as PTR;pose proof(cm_pointwise_convert_value a b ty v EQ)as VAL.
 pose proof(cm_pointwise_value_number a b(cm_convert_value b ty v)EQ)as NUMBER.
 unfold cm_state_pointwise_eq;cbv beta iota zeta delta [cm_state_store cm_state_mem cm_state_init cm_state_tags cm_state_tagged cm_state_env cm_state_input cm_state_output cm_state_fp cm_state_nextgen cm_state_regions];rewrite PTR,VAL,NUMBER.
 split;[now apply cm_store_mem_pointwise|];split;[intro x;unfold cm_mark_init;now rewrite I|].
 split;[intro x;destruct(cm_is_pointerb ty);[destruct(x=?cm_value_number b ptr);auto|auto]|].
 split;[intro x;destruct(cm_is_pointerb ty);unfold cm_clear_tagged;now rewrite G|].
 split;[exact E|];split;[exact IN|];split;[exact OUT|];split;[exact F|];split;[exact N|exact R].
Qed.
Lemma cm_mark_init_commutes init a aw b bw x :cm_mark_init(cm_mark_init init a aw)b bw x=cm_mark_init(cm_mark_init init b bw)a aw x.
Proof. unfold cm_mark_init;destruct(init x),((a<=?x)&&(x<?a+aw)),((b<=?x)&&(x<?b+bw));reflexivity. Qed.
Lemma cm_clear_tagged_commutes tags a aw b bw x :cm_clear_tagged(cm_clear_tagged tags a aw)b bw x=cm_clear_tagged(cm_clear_tagged tags b bw)a aw x.
Proof. unfold cm_clear_tagged;destruct(tags x),((0<?aw)&&(x<?a+aw)&&(a<?x+8)),((0<?bw)&&(x<?b+bw)&&(b<?x+8));reflexivity. Qed.
