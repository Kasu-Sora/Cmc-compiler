Require Export SimpleC.EE.QCP_demos_human.cmc_call_pending_machine_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
(* Pointwise equality avoids introducing functional-extensionality axioms when
   comparing forward source parameter stores with reverse target stores. *)
Definition cm_state_pointwise_eq a b :Prop:=
 (forall x,cm_state_mem a x=cm_state_mem b x) /\(forall x,cm_state_init a x=cm_state_init b x) /\
 (forall x,cm_state_tags a x=cm_state_tags b x) /\(forall x,cm_state_tagged a x=cm_state_tagged b x) /\
 (forall scope slot,cm_state_env a scope slot=cm_state_env b scope slot) /\
 cm_state_input a=cm_state_input b /\cm_state_output a=cm_state_output b /\cm_state_fp a=cm_state_fp b /\
 cm_state_nextgen a=cm_state_nextgen b /\cm_state_regions a=cm_state_regions b.
Lemma cm_state_pointwise_refl a :cm_state_pointwise_eq a a.
Proof. repeat split;reflexivity. Qed.
Lemma cm_state_pointwise_sym a b :cm_state_pointwise_eq a b ->cm_state_pointwise_eq b a.
Proof. intros[M[I[T[G[E[IN[OUT[F[N R]]]]]]]]];repeat split;intros;symmetry;auto. Qed.
Lemma cm_state_pointwise_trans a b c :cm_state_pointwise_eq a b ->cm_state_pointwise_eq b c ->cm_state_pointwise_eq a c.
Proof.
 intros[M[I[T[G[E[IN[OUT[F[N R]]]]]]]]][M2[I2[T2[G2[E2[IN2[OUT2[F2[N2 R2]]]]]]]]];repeat split;intros;etransitivity;eauto.
Qed.
Lemma cm_pointwise_value_number a b v :cm_state_pointwise_eq a b ->cm_value_number a v=cm_value_number b v.
Proof. intros[_[_[_[_[_[_[_[_[_ R]]]]]]]]];destruct v;cbn[cm_value_number];now rewrite ?R. Qed.
Lemma cm_pointwise_live a b x :cm_state_pointwise_eq a b ->cm_live_address a x <->cm_live_address b x.
Proof. intros[_[_[_[_[_[_[_[_[_ R]]]]]]]]];unfold cm_live_address;now rewrite R. Qed.
Lemma cm_pointwise_initialized a b mem :cm_state_pointwise_eq a b ->cm_initialized_bytes_sim a mem ->cm_initialized_bytes_sim b mem.
Proof.
 intros EQ SIM x INIT LIVE;pose proof EQ as[M[I REST]];rewrite <-I in INIT;apply(cm_pointwise_live a b x EQ)in LIVE.
 rewrite(SIM x INIT LIVE);unfold tower_getb;now rewrite M.
Qed.
Lemma cm_pointwise_provenance a b mem :cm_state_pointwise_eq a b ->cm_stored_provenance_sim a mem ->cm_stored_provenance_sim b mem.
Proof.
 intros EQ SIM x TAG LIVE;pose proof EQ as[M[I[T[G REST]]]];rewrite <-G in TAG;apply(cm_pointwise_live a b x EQ)in LIVE.
 destruct(SIM x TAG LIVE)as[INIT WORD];split;[now rewrite <-I|rewrite <-T,<-(cm_pointwise_value_number a b _ EQ);exact WORD].
Qed.
Lemma cm_pointwise_spill_list policy p a b mem fid fp spills :cm_state_pointwise_eq a b ->cm_spill_list_sim policy p a mem fid fp spills ->cm_spill_list_sim policy p b mem fid fp spills.
Proof.
 intro EQ;induction spills as[|s rest IH];cbn[cm_spill_list_sim];[auto|intros[H T];split;[rewrite <-(cm_pointwise_value_number a b _ EQ);exact H|now apply IH]].
Qed.
Lemma cm_pointwise_spill_frames policy p a b mem frames :cm_state_pointwise_eq a b ->cm_spill_frames_sim policy p a mem frames ->cm_spill_frames_sim policy p b mem frames.
Proof. intro EQ;induction frames;cbn[cm_spill_frames_sim];[auto|intros[H T];split;[now apply cm_pointwise_spill_list with a|now apply IHframes]]. Qed.
Lemma cm_pointwise_machine_sim policy p a b vm calls frames values suffix :cm_state_pointwise_eq a b ->
 cm_machine_state_sim policy p a vm calls frames values suffix ->cm_machine_state_sim policy p b vm calls frames values suffix.
Proof.
 intros EQ[M[P[F[C[S[I[O STACK]]]]]]];pose proof EQ as[_[_[_[_[_[IN[OUT[FP _]]]]]]]].
 unfold cm_machine_state_sim;split;[now apply cm_pointwise_initialized with a|];split;[now apply cm_pointwise_provenance with a|].
 split;[now rewrite <-FP|];split;[exact C|];split;[now apply cm_pointwise_spill_frames with a|];split;[now rewrite <-IN|];split;[now rewrite <-OUT|].
 unfold cm_operand_suffix_sim in *;rewrite STACK;f_equal;unfold cm_encode_values;apply map_ext;intro v;now apply cm_pointwise_value_number.
Qed.
