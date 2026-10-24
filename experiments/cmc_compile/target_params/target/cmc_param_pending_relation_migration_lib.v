Require Export SimpleC.EE.QCP_demos_human.cmc_param_store_geometry_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Definition cm_state_pending_eq a b base finish :=
 (forall x,cm_state_mem a x=cm_state_mem b x) /\
 (forall x,x<base \/ finish<=x ->cm_state_init a x=cm_state_init b x) /\
 (forall x,cm_state_tags a x=cm_state_tags b x) /\
 (forall x,finish<=base \/ x+8<=base \/ finish<=x ->cm_state_tagged a x=cm_state_tagged b x) /\
 (forall scope slot,cm_state_env a scope slot=cm_state_env b scope slot) /\
 cm_state_input a=cm_state_input b /\ cm_state_output a=cm_state_output b /\
 cm_state_fp a=cm_state_fp b /\cm_state_nextgen a=cm_state_nextgen b /\cm_state_regions a=cm_state_regions b.
Lemma cm_pending_eq_number a b base finish v :cm_state_pending_eq a b base finish ->cm_value_number a v=cm_value_number b v.
Proof. intros[_[_[_[_[_[_[_[_[_ R]]]]]]]]];unfold cm_value_number;now rewrite R. Qed.
Lemma cm_pending_eq_convert a b base finish ty v :cm_state_pending_eq a b base finish ->cm_convert_value a ty v=cm_convert_value b ty v.
Proof. intro EQ;destruct ty;cbn[cm_convert_value];try reflexivity;now rewrite(cm_pending_eq_number a b base finish v EQ). Qed.
Lemma cm_pending_eq_complete a b base :cm_state_pending_eq a b base base ->cm_state_pointwise_eq a b.
Proof. intros[M[I[T[G[E[IN[OUT[F[N R]]]]]]]]];unfold cm_state_pointwise_eq;repeat split;auto;intros;[apply I;lia|apply G;lia]. Qed.
Lemma cm_pending_eq_store a b base finish ty ptr value :
 cm_state_pending_eq a b base finish ->cm_value_number a ptr=base ->base+cm_store_width ty<=finish ->
 cm_state_pending_eq(cm_state_store ty ptr value a)(cm_state_store ty ptr value b)(base+cm_store_width ty)finish.
Proof.
 intros EQ ADDR BOUND;pose proof EQ as[M[I[T[G[E[IN[OUT[F[N R]]]]]]]]].
 pose proof(cm_pending_eq_number a b base finish ptr EQ)as P.
 pose proof(cm_pending_eq_convert a b base finish ty value EQ)as C.
 pose proof(cm_pending_eq_number a b base finish(cm_convert_value b ty value)EQ)as V.
 unfold cm_state_pending_eq;repeat split;intros;try assumption.
 - rewrite !cm_state_store_mem,P,C,V;now apply cm_store_mem_pointwise.
 - rewrite !cm_state_store_init,<-P,ADDR;unfold cm_mark_init.
   destruct((base<=?x)&&(x<?base+cm_store_width ty))eqn:K;[now rewrite !orb_true_r|].
   rewrite !orb_false_r;apply I;apply andb_false_iff in K;destruct K;[apply Z.leb_gt in H0|apply Z.ltb_ge in H0];lia.
 - rewrite !cm_state_store_tags,P,C;unfold cm_tags_write;destruct(cm_is_pointerb ty),(x=?cm_value_number b ptr);auto.
 - rewrite !cm_state_store_tagged,<-P,ADDR,C,V;unfold cm_tagged_write,cm_clear_tagged.
   destruct(((0<?cm_store_width ty)&&(x<?base+cm_store_width ty))&&(base<?x+8))eqn:K.
   + cbn;now rewrite !andb_false_r.
   + cbn;rewrite !andb_true_r;rewrite G;[reflexivity|].
     apply andb_false_iff in K;destruct K as[K|K];[apply andb_false_iff in K;destruct K as[K|K];[apply Z.ltb_ge in K;pose proof(cm_store_width_positive ty)|apply Z.ltb_ge in K]|apply Z.ltb_ge in K];lia.
 - exact(E _ _).
Qed.
