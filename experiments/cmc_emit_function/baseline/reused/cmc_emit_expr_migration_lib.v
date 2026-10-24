From Coq Require Import ZArith List Bool Lia.
Require Export SimpleC.EE.QCP_demos_human.cmc_emit_binary_finish_migration_lib.
Import ListNotations.
Local Open Scope Z_scope.

(* Constructor observations and exact optional suffixes; the complete code,
   count, lookup and temporary models are imported unchanged. *)
Definition cm_intrinsic_expr (e:cm_expr) : Prop :=
 match e with CMPutcE _ _ | CMPutiE _ _ | CMExitE _ _ => True | _ => False end.
Definition cm_expr_child (e:cm_expr) : cm_expr :=
 match e with
 | CMAssignE a _ _ | CMBinaryE _ a _ _ | CMIndexE a _ _
 | CMUnaryE _ a _ | CMMemberE a _ _ | CMPutcE a _ | CMPutiE a _ | CMExitE a _ => a
 | _ => CMConstE 0 CMIntTy end.
Definition cm_expr_second (e:cm_expr) : cm_expr :=
 match e with CMAssignE _ b _ | CMBinaryE _ _ b _ | CMIndexE _ b _ => b
 | _ => CMConstE 0 CMIntTy end.
Definition cm_optional_load ty (lvalue:Z) :=
 if Z.eqb lvalue 0 then cm_load_code ty else [].
Definition cm_member_load_suffix p arg mid ty (lvalue:Z) :=
 if Z.eqb lvalue 0 then
   if Z.eqb (cm_member_array_code p (cm_expr_type arg) mid) 0 then cm_load_code ty else []
 else [].
Definition cm_short_opcode (op:Z) := if Z.eqb op 0 then TVMJnzOp else TVMJzOp.
Definition cm_short_value (op:Z) := if Z.eqb op 0 then 1 else 0.

Definition cm_expr_shape (e shape:cm_expr) : Prop := e = shape.

Lemma cm_slot_expr_refs__constructor_facts_a structs s :
 cm_slot_wf structs s -> cm_type_refs structs (cm_slot_expr_type s).
Proof.
 unfold cm_slot_wf, cm_scalar_type, cm_slot_expr_type.
 destruct (Z.eqb (cm_slot_count s) 0); cbn; tauto.
Qed.
Lemma cm_binary_refs__constructor_facts_a structs op a b ty :
 cm_type_refs structs a -> cm_type_refs structs b ->
 cm_binary_types op a b ty -> cm_type_refs structs ty.
Proof.
 intros Ha Hb H. unfold cm_binary_types in H.
 repeat match type of H with context [if ?c then _ else _] => destruct c eqn:? end;
 repeat match goal with H : _ /\ _ |- _ => destruct H | H : _ \/ _ |- _ => destruct H end;
 subst; cbn; auto.
Qed.
Lemma cm_unary_refs__constructor_facts_a structs op a ty :
 cm_type_refs structs a -> cm_unary_types op a ty -> cm_type_refs structs ty.
Proof.
 intros Ha H. unfold cm_unary_types in H.
 repeat match type of H with context [if ?c then _ else _] => destruct c eqn:? end;
 repeat match goal with H : _ /\ _ |- _ => destruct H end;
 subst; cbn; auto.
 destruct a; cbn in *; auto.
Qed.
Lemma cm_expr_type_refs__constructor_facts_a policy p f e :
 cm_typed_program policy p ->
 cm_slots_wf (cm_program_structs p) (cm_function_params f) ->
 cm_slots_wf (cm_program_structs p) (cm_function_locals f) ->
 cm_expr_wf policy p f e -> cm_type_refs (cm_program_structs p) (cm_expr_type e).
Proof.
 intros Hp Hparams Hlocals. induction e; intro Hw; cbn [cm_expr_wf cm_expr_type] in *.
 - destruct Hw as [Heq | Heq]; subst ty; exact I.
 - destruct Hw as [_ ->]; exact I.
 - destruct Hw as [Hv ->]. unfold cm_binding_valid in Hv.
   destruct Hv as [[-> Hb]|[[-> Hb]|[-> Hb]]]; unfold cm_binding_type; simpl Z.eqb.
   + destruct Hp as [_ [Hg _]]. specialize (Hg slot Hb).
     unfold cm_global_wf, cm_scalar_type, cm_global_expr_type in *.
     destruct (Z.eqb (cm_global_count (cm_global_at slot (cm_program_globals p))) 0); cbn; tauto.
   + apply cm_slot_expr_refs__constructor_facts_a. apply Hlocals. exact Hb.
   + apply cm_slot_expr_refs__constructor_facts_a. apply Hparams. exact Hb.
 - destruct Hw as [Ha [Hb [Hl [Harr [Heq Hc]]]]]. rewrite Heq. exact (IHe1 Ha).
 - destruct Hw as [Ha [Hb Hty]]. exact (cm_binary_refs__constructor_facts_a _ _ _ _ _ (IHe1 Ha) (IHe2 Hb) Hty).
 - destruct Hw as [Ha [Hty Hl]]. exact (cm_unary_refs__constructor_facts_a _ _ _ _ (IHe Ha) Hty).
 - destruct Hw as [Ha [Hb [Hptr [Hint ->]]]].
   specialize (IHe1 Ha). destruct (cm_expr_type e1); cbn in *; auto.
 - destruct Hw as [Ha [Hv ->]]. unfold cm_member_valid in Hv.
   destruct Hv as [Hptr [Hstruct [Hsid Hmid]]].
   unfold cm_member_type. apply cm_slot_expr_refs__constructor_facts_a.
   destruct Hp as [Hs _]. specialize (Hs _ Hsid).
   destruct Hs as [_ [Hslots _]]. apply Hslots. exact Hmid.
 - destruct Hw as [Hfid [Hargs ->]].
   destruct Hp as [_ [_ [_ [Hf _]]]]. specialize (Hf fid Hfid).
   unfold cm_function_wf, cm_scalar_type in Hf. tauto.
 - destruct Hw as [_ [_ ->]]. exact I.
 - subst ty. exact I.
 - destruct Hw as [_ [_ ->]]. exact I.
 - destruct Hw as [_ [_ ->]]. exact I.
 - destruct Hw as [_ [_ ->]]. exact I.
Qed.
Lemma cm_expr_node_facts__constructor_facts_a policy p fid e :
 cm_expr_counts_representable policy p fid e ->
 cm_type_code_wf (cm_expr_type e) /\ cm_i32_code_count (cm_type_encode (cm_expr_type e)).
Proof.
 destruct e; cbn [cm_expr_counts_representable];
 unfold cm_expr_count_node_representable; tauto.
Qed.
Lemma cm_expr_type_refs__constructor_facts_b : forall policy p f e,
 cm_typed_program policy p ->
 cm_slots_wf (cm_program_structs p) (cm_function_params f) ->
 cm_slots_wf (cm_program_structs p) (cm_function_locals f) ->
 cm_expr_wf policy p f e -> cm_type_refs (cm_program_structs p) (cm_expr_type e).
Proof.
 intros policy p f e Hprog Hparams Hlocals.
 assert (Hslot : forall slots i, cm_slots_wf (cm_program_structs p) slots ->
   0 <= i < Zlength slots -> cm_type_refs (cm_program_structs p) (cm_slot_expr_type (cm_slot_at i slots))).
 { intros slots i Hslots Hi. specialize (Hslots i Hi).
   unfold cm_slot_wf, cm_scalar_type in Hslots.
   unfold cm_slot_expr_type. destruct (Z.eqb (cm_slot_count (cm_slot_at i slots)) 0); cbn; tauto. }
 destruct Hprog as [Hstruct [Hglobal [Hstring [Hfun Hrest]]]].
 induction e as [v ty|sid ty|scope slot ty|a IHa b IHb ty|op a IHa b IHb ty|op a IHa ty|a IHa b IHb ty|a IHa mid ty|callee args ty|asked ty|ty|a IHa ty|a IHa ty|a IHa ty];
 cbn [cm_expr_wf cm_expr_type]; intro Hwf.
 - unfold cm_integer_type in Hwf. destruct Hwf; subst; exact I.
 - destruct Hwf as [_ ->]. exact I.
 - destruct Hwf as [Hv ->]. unfold cm_binding_valid in Hv.
   destruct Hv as [[-> Hi]|[[-> Hi]|[-> Hi]]]; unfold cm_binding_type; cbn.
   + specialize (Hglobal slot Hi). unfold cm_global_wf, cm_scalar_type in Hglobal.
     unfold cm_global_expr_type. destruct (Z.eqb (cm_global_count (cm_global_at slot (cm_program_globals p))) 0); cbn; tauto.
   + apply Hslot; assumption.
   + apply Hslot; assumption.
 - destruct Hwf as [Ha [Hb [_ [_ [-> _]]]]]. exact (IHa Ha).
 - destruct Hwf as [Ha [Hb Htypes]]. specialize (IHa Ha). specialize (IHb Hb).
   unfold cm_binary_types in Htypes.
   repeat match type of Htypes with context [if ?b then _ else _] => destruct b end;
   intuition subst; cbn; auto.
 - destruct Hwf as [Ha [Htypes Hlv]]. specialize (IHa Ha).
   unfold cm_unary_types in Htypes.
   repeat match type of Htypes with context [if ?b then _ else _] => destruct b end.
   + destruct Htypes as [_ [_ ->]]. exact I.
   + destruct Htypes as [_ [Hp ->]]. destruct (cm_expr_type a); cbn in *; tauto.
   + destruct Htypes as [_ ->]. exact IHa.
 - destruct Hwf as [Ha [Hb [Hp [Hint ->]]]]. specialize (IHa Ha).
   destruct (cm_expr_type a); cbn in *; tauto.
 - destruct Hwf as [Ha [Hv ->]].
   unfold cm_member_valid in Hv. destruct Hv as [_ [_ [Hs Hm]]].
   specialize (Hstruct _ Hs). destruct Hstruct as [_ [Hslots _]].
   unfold cm_member_type. apply Hslot; assumption.
 - destruct Hwf as [Hi [_ ->]]. specialize (Hfun callee Hi).
   unfold cm_function_wf, cm_scalar_type in Hfun. tauto.
 - destruct Hwf as [_ [_ ->]]. exact I.
 - subst. exact I.
 - destruct Hwf as [_ [_ ->]]. exact I.
 - destruct Hwf as [_ [_ ->]]. exact I.
 - destruct Hwf as [_ [_ ->]]. exact I.
Qed.
Lemma cm_slot_refs__constructor_facts_c structs s :
 cm_slot_wf structs s -> cm_type_refs structs (cm_slot_expr_type s).
Proof.
 intros [_ [[_ [H _]] _]]. unfold cm_slot_expr_type.
 destruct (Z.eqb (cm_slot_count s) 0); exact H.
Qed.
Lemma cm_binding_refs__constructor_facts_c policy p f scope slot :
 cm_typed_program policy p ->
 cm_slots_wf (cm_program_structs p) (cm_function_params f) ->
 cm_slots_wf (cm_program_structs p) (cm_function_locals f) ->
 cm_binding_valid p f scope slot ->
 cm_type_refs (cm_program_structs p) (cm_binding_type p f scope slot).
Proof.
 intros [_ [Hg _]] Hp Hl Hv.
 destruct Hv as [[-> H]|[[-> H]|[-> H]]]; unfold cm_binding_type; cbn.
 - specialize (Hg slot H). destruct Hg as [_ [[_ [Hr _]] _]].
   unfold cm_global_expr_type. destruct (Z.eqb (cm_global_count _) 0); exact Hr.
 - apply cm_slot_refs__constructor_facts_c. apply Hl. exact H.
 - apply cm_slot_refs__constructor_facts_c. apply Hp. exact H.
Qed.
Lemma cm_member_refs__constructor_facts_c policy p base mid :
 cm_typed_program policy p -> cm_member_valid p base mid ->
 cm_type_refs (cm_program_structs p) (cm_member_type p base mid).
Proof.
 intros [Hs _] [_ [_ [Hi Hm]]].
 specialize (Hs _ Hi). destruct Hs as [_ [Hs _]].
 unfold cm_member_type. apply cm_slot_refs__constructor_facts_c.
 apply Hs. exact Hm.
Qed.
Lemma cm_pointee_refs__constructor_facts_c structs ty :
 cm_type_refs structs ty -> cm_type_refs structs (cm_pointee ty).
Proof. destruct ty; cbn; auto. Qed.
Lemma cm_binary_refs__constructor_facts_c structs op a b ty :
 cm_type_refs structs a -> cm_type_refs structs b ->
 cm_binary_types op a b ty -> cm_type_refs structs ty.
Proof.
 intros Ha Hb [_ H].
 repeat match type of H with context [if ?c then _ else _] => destruct c end;
 repeat match goal with
 | Hx : _ /\ _ |- _ => destruct Hx
 | Hx : _ \/ _ |- _ => destruct Hx
 end;
 subst; cbn; auto.
Qed.
Lemma cm_unary_refs__constructor_facts_c structs op a ty :
 cm_type_refs structs a -> cm_unary_types op a ty -> cm_type_refs structs ty.
Proof.
 intros Ha [_ H].
 repeat match type of H with context [if ?c then _ else _] => destruct c end;
 repeat match goal with Hx : _ /\ _ |- _ => destruct Hx end;
 subst; cbn; auto using cm_pointee_refs__constructor_facts_c.
Qed.
Lemma cm_expr_type_refs__constructor_facts_c : forall policy p f e,
 cm_typed_program policy p ->
 cm_slots_wf (cm_program_structs p) (cm_function_params f) ->
 cm_slots_wf (cm_program_structs p) (cm_function_locals f) ->
 cm_expr_wf policy p f e -> cm_type_refs (cm_program_structs p) (cm_expr_type e).
Proof.
 intros policy p f e Htyped Hp Hl. induction e; intro Hw;
 cbn [cm_expr_wf] in Hw; cbn [cm_expr_type].
 - destruct Hw as [H | H]; subst; exact I.
 - destruct Hw as [_ ->]. exact I.
 - destruct Hw as [Hv ->]. eapply cm_binding_refs__constructor_facts_c; eauto.
 - destruct Hw as [Ha [Hb [_ [_ [-> _]]]]]. auto.
 - destruct Hw as [Ha [Hb Htypes]]. eapply cm_binary_refs__constructor_facts_c; [| |exact Htypes]; auto.
 - destruct Hw as [Ha [Htypes _]]. eapply cm_unary_refs__constructor_facts_c; [|exact Htypes]; auto.
 - destruct Hw as [Ha [_ [_ [_ ->]]]]. apply cm_pointee_refs__constructor_facts_c. auto.
 - destruct Hw as [_ [Hv ->]]. eapply cm_member_refs__constructor_facts_c; eauto.
 - destruct Hw as [Hc [_ ->]]. destruct Htyped as [_ [_ [_ [Hf _]]]].
   specialize (Hf _ Hc). exact (proj1 (proj2 (proj1 Hf))).
 - destruct Hw as [_ [_ ->]]. exact I.
 - subst. exact I.
 - destruct Hw as [_ [_ ->]]. exact I.
 - destruct Hw as [_ [_ ->]]. exact I.
 - destruct Hw as [_ [_ ->]]. exact I.
Qed.
Lemma cm_count_node__constructor_facts_c policy p fid e :
 cm_expr_counts_representable policy p fid e ->
 cm_type_code_wf (cm_expr_type e) /\ cm_i32_code_count (cm_type_encode (cm_expr_type e)).
Proof. destruct e; intros [H _]; exact (proj2 H). Qed.
Lemma cm_temp_bounds__constructor_facts_c policy p fid f temp temp_limit max :
 f = cm_function_at policy fid (cm_program_functions p) ->
 cm_slots_wf (cm_program_structs p) (cm_function_params f) ->
 cm_slots_wf (cm_program_structs p) (cm_function_locals f) ->
 0 <= temp -> temp <= temp_limit -> cm_temp_offset policy p fid temp_limit <= max ->
 cm_temp_offset policy p fid temp <= max /\ temp_limit <= max.
Proof.
 intros Hf Hp Hl Ht Htl Hb.
 pose proof (cm_slots_size_nonnegative__call_bounds _ _ Hp).
 pose proof (cm_slots_size_nonnegative__call_bounds _ _ Hl).
 unfold cm_temp_offset in *. rewrite <- Hf in *. split; lia.
Qed.
Lemma cm_expr_temps_nonnegative__index_bounds : forall e,
  0 <= cm_ltemps e /\ 0 <= cm_rtemps e.
Proof.
  fix IH 1. intro e.
  destruct e as [n ty|sid ty|scope slot ty|a b ty|op a b ty|op a ty|
    a b ty|a mid ty|callee args ty|asked ty|ty|a ty|a ty|a ty].
  all: try pose proof (IH a) as Ha.
  all: try pose proof (IH b) as Hb.
  all: unfold cm_ltemps, cm_rtemps in *.
  all: cbn [cm_expr_tpair cm_tleft cm_tright].
  all: unfold cm_imax.
  all: try solve [split; lia].
  - destruct (Z.eqb op 2); cbn [cm_tleft cm_tright]; [split; lia|].
    destruct (Z.eqb op 3); cbn [cm_tleft cm_tright]; split; lia.
  - change (0 <= 0 /\ 0 <= cm_acount (cm_args_apair args) + cm_adepth (cm_args_apair args)).
    pose proof (cm_args_apair_count_depth__call_bounds args).
    pose proof (ListLib.General.Length.Zlength_nonneg args). split; lia.
Qed.
Lemma cm_index_code_bounds__index_bounds policy p fid pc temp a b ty lv :
  cm_i32_code_count pc ->
  cm_i32_code_count (pc + Zlength (cm_expr_code_for policy p fid pc temp (CMIndexE a b ty) lv)) ->
  cm_i32_code_count (pc + Zlength (cm_expr_code_for policy p fid pc temp a 0)) /\
  cm_i32_code_count (pc + (cm_rvalue_code_count policy p fid a + 5)) /\
  cm_i32_code_count (pc + (cm_rvalue_code_count policy p fid a + 5) +
    Zlength (cm_expr_code_for policy p fid (pc + (cm_rvalue_code_count policy p fid a + 5)) (temp+1) b 0)) /\
  cm_i32_code_count (cm_rvalue_code_count policy p fid a + 5).
Proof.
  intros Hpc Hend.
  unfold cm_expr_code_for in *.
  cbn [Z.eqb] in *.
  rewrite (proj2 (cm_emit_pair_lengths__store_bounds policy p fid a pc temp)).
  rewrite (proj2 (cm_emit_pair_lengths__store_bounds policy p fid b (pc+(cm_rvalue_code_count policy p fid a+5)) (temp+1))).
  destruct (Z.eqb lv 0) eqn:Hlv;
  [rewrite (proj2 (cm_emit_pair_lengths__store_bounds policy p fid (CMIndexE a b ty) pc temp)) in Hend|
   rewrite (proj1 (cm_emit_pair_lengths__store_bounds policy p fid (CMIndexE a b ty) pc temp)) in Hend];
  unfold cm_lvalue_code_count, cm_rvalue_code_count in *;
  cbn [cm_expr_code_counts cm_lcount_of cm_rcount_of] in Hend;
  pose proof (cm_expr_code_counts_nonnegative policy p fid a);
  pose proof (cm_expr_code_counts_nonnegative policy p fid b);
  unfold cm_i32_code_count in *; repeat split; lia.
Qed.
Lemma cm_index_temp_bounds__index_bounds a b ty lv temp lim :
  temp + cm_expr_temps_for (CMIndexE a b ty) lv <= lim ->
  temp + cm_expr_temps_for a 0 <= lim /\
  temp + 1 + cm_expr_temps_for b 0 <= lim /\ temp + 1 <= lim.
Proof.
  intro H.
  unfold cm_expr_temps_for, cm_ltemps, cm_rtemps in *.
  destruct (Z.eqb lv 0);
  cbn [cm_expr_tpair cm_tleft cm_tright Z.eqb] in *;
  unfold cm_imax in *;
  pose proof (cm_expr_temps_nonnegative__index_bounds b) as Hb;
  unfold cm_ltemps, cm_rtemps in Hb; repeat split; lia.
Qed.
Lemma cm_expr_temps_nonnegative__assignment_bounds : forall e,
 0 <= cm_ltemps e /\ 0 <= cm_rtemps e.
Proof.
 fix IH 1. intro e. destruct e;
 unfold cm_ltemps, cm_rtemps;
 cbn [cm_expr_tpair cm_tleft cm_tright];
 try solve [split; lia].
 all: try solve [
 repeat match goal with
 | |- context [cm_expr_tpair ?a] =>
   let H := fresh "Hchild" in
   pose proof (IH a) as H; unfold cm_ltemps, cm_rtemps in H;
   destruct H; generalize dependent (cm_tleft (cm_expr_tpair a));
   generalize dependent (cm_tright (cm_expr_tpair a)); intros
 end;
 unfold cm_imax;
 repeat match goal with |- context [if ?b then _ else _] => destruct b end;
 cbn [cm_tleft cm_tright]; split; lia].
 split; [lia|].
 change (0 <= cm_acount (cm_args_apair args) + cm_adepth (cm_args_apair args)).
 pose proof (cm_args_apair_count_depth__call_bounds args).
 pose proof (ListLib.General.Length.Zlength_nonneg args). lia.
Qed.
Lemma cm_assignment_prefix_bounds__assignment_bounds policy p fid pc temp a b ty :
 cm_i32_code_count pc ->
 cm_i32_code_count (pc + Zlength (cm_expr_code_for policy p fid pc temp (CMAssignE a b ty) 0)) ->
 cm_i32_code_count (pc + cm_lvalue_code_count policy p fid a) /\
 cm_i32_code_count (pc + (cm_lvalue_code_count policy p fid a + 5)) /\
 cm_i32_code_count (pc + (cm_lvalue_code_count policy p fid a + 5) +
 Zlength (cm_expr_code_for policy p fid (pc + (cm_lvalue_code_count policy p fid a + 5)) (temp+1) b 0)).
Proof.
 unfold cm_expr_code_for. cbn [Z.eqb].
 rewrite (proj2 (cm_emit_pair_lengths__store_bounds policy p fid (CMAssignE a b ty) pc temp)).
 rewrite (proj2 (cm_emit_pair_lengths__store_bounds policy p fid b (pc+(cm_lvalue_code_count policy p fid a+5)) (temp+1))).
 pose proof (ListLib.General.Length.Zlength_nonneg (cm_lcode_of (cm_emit_expr_pair policy p fid pc temp a))) as Ha.
 pose proof (ListLib.General.Length.Zlength_nonneg (cm_rcode_of (cm_emit_expr_pair policy p fid pc temp b))) as Hb.
 rewrite (proj1 (cm_emit_pair_lengths__store_bounds policy p fid a pc temp)) in Ha.
 rewrite (proj2 (cm_emit_pair_lengths__store_bounds policy p fid b pc temp)) in Hb.
 unfold cm_i32_code_count, cm_lvalue_code_count, cm_rvalue_code_count in *.
 cbn [cm_expr_code_counts cm_rcount_of].
 unfold cm_char_normalize_count. destruct ty; intros; repeat split; lia.
Qed.
Lemma cm_expr_temps_nonnegative__binary_regular_bounds : forall e,
  0 <= cm_ltemps e /\ 0 <= cm_rtemps e.
Proof.
 fix IH 1. intro e.
 destruct e as [n ty|sid ty|scope slot ty|a b ty|op a b ty|op a ty|
   a b ty|a mid ty|callee args ty|asked ty|ty|a ty|a ty|a ty].
 all: try pose proof (IH a) as Ha.
 all: try pose proof (IH b) as Hb.
 all: unfold cm_ltemps, cm_rtemps in *.
 all: cbn [cm_expr_tpair cm_tleft cm_tright].
 all: try solve [split; lia].
 all: try solve [unfold cm_imax; repeat match goal with |- context [if ?c then _ else _] => destruct c end;
   cbn [cm_tleft cm_tright]; split; lia].
 change (0 <= 0 /\ 0 <= cm_acount (cm_args_apair args) + cm_adepth (cm_args_apair args)).
 pose proof (cm_args_apair_count_depth__call_bounds args).
 pose proof (ListLib.General.Length.Zlength_nonneg args). split; lia.
Qed.
Lemma cm_binary_regular_code_bounds__binary_regular_bounds policy p fid pc temp op a b ty :
 op <> 0 -> op <> 1 -> cm_i32_code_count pc ->
 cm_i32_code_count (pc + Zlength (cm_expr_code_for policy p fid pc temp (CMBinaryE op a b ty) 0)) ->
 cm_i32_code_count (pc + cm_rvalue_code_count policy p fid a + 5) /\
 cm_i32_code_count (pc + cm_rvalue_code_count policy p fid a + 5 + cm_rvalue_code_count policy p fid b) /\
 cm_i32_code_count (pc + cm_rvalue_code_count policy p fid a).
Proof.
 intros H0 H1 Hpc Hend.
 unfold cm_expr_code_for in Hend. cbn [Z.eqb] in Hend.
 rewrite (proj2 (cm_emit_pair_lengths__store_bounds policy p fid (CMBinaryE op a b ty) pc temp)) in Hend.
 unfold cm_rvalue_code_count in *.
 cbn [cm_expr_code_counts cm_rcount_of] in Hend.
 assert (E0 : (op =? 0) = false) by (apply Z.eqb_neq; exact H0).
 assert (E1 : (op =? 1) = false) by (apply Z.eqb_neq; exact H1).
 rewrite E0, E1 in Hend. cbn [orb] in Hend.
 pose proof (cm_expr_code_counts_nonnegative policy p fid a).
 pose proof (cm_expr_code_counts_nonnegative policy p fid b).
 assert (Ht : 5 <= cm_binary_tail_count p op a b).
 { unfold cm_binary_tail_count.
   repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia. }
 unfold cm_i32_code_count in *. repeat split; lia.
Qed.
Lemma cm_binary_regular_temp_bounds__binary_regular_bounds op a b ty temp limit :
 op <> 0 -> op <> 1 -> temp + cm_expr_temps_for (CMBinaryE op a b ty) 0 <= limit ->
 temp + cm_expr_temps_for a 0 <= limit /\
 temp + 1 + cm_expr_temps_for b 0 <= limit /\ temp + 1 <= limit.
Proof.
 intros H0 H1 Hbudget.
 assert (E0 : (op =? 0) = false) by (apply Z.eqb_neq; exact H0).
 assert (E1 : (op =? 1) = false) by (apply Z.eqb_neq; exact H1).
 unfold cm_expr_temps_for, cm_rtemps in *.
 cbn [Z.eqb cm_expr_tpair cm_tright] in Hbudget.
 rewrite E0, E1 in Hbudget. cbn [orb] in Hbudget.
 unfold cm_imax in Hbudget.
 pose proof (cm_expr_temps_nonnegative__binary_regular_bounds b) as Hb.
 unfold cm_rtemps in Hb. cbn [Z.eqb]. repeat split; lia.
Qed.
