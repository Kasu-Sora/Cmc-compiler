From Coq Require Import ZArith List Bool Lia.
Require Export SimpleC.EE.QCP_demos_human.cmc_emit_expr_migration_lib.
Import ListNotations.
Local Open Scope Z_scope.

(* The existing count and temporary models are reused without modification.
   The lookup policy remains arbitrary, including on malformed programs. *)
Lemma cm_temp_imax_upper x y z : cm_imax x y <= z <-> x <= z /\ y <= z.
Proof. unfold cm_imax; apply Z.max_lub_iff. Qed.
Lemma cm_temp_imax_add_upper base x y z :
 base + cm_imax x y <= z <-> base + x <= z /\ base + y <= z.
Proof. unfold cm_imax; lia. Qed.
Lemma cm_binary_tail_positive p op left right :
 1 <= cm_binary_tail_count p op left right.
Proof.
 unfold cm_binary_tail_count.
 repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia.
Qed.
Lemma cm_expr_count_node_from_tree policy e p fid :
 cm_expr_counts_representable policy p fid e -> cm_expr_count_node_representable policy p fid e.
Proof. destruct e; cbn [cm_expr_counts_representable]; tauto. Qed.
Lemma cm_args_count_node_from_tree policy args p fid :
 cm_args_counts_representable policy p fid args ->
 cm_i32_code_count (cm_args_code_count_of (cm_args_code_counts policy p fid args)).
Proof. destruct args; cbn [cm_args_counts_representable]; tauto. Qed.
Lemma cm_args_temps_safe_pair args :
 cm_rep_args_temps_safe args -> cm_rep_apair_safe (cm_args_apair args).
Proof. apply cm_args_pair_safe__expr_safety. Qed.

(* The cons arithmetic is shared by nested expression recursion and the
   exported argument-list theorem; its cost belongs to this module. *)
Lemma cm_args_temps_ready_cons policy p fid a args :
 cm_rep_expr_temps_safe a /\ cm_ltemps a <= cm_lvalue_code_count policy p fid a /\
   cm_rtemps a <= cm_rvalue_code_count policy p fid a ->
 cm_rep_args_temps_safe args /\
   cm_args_temps args <= cm_args_code_count_of (cm_args_code_counts policy p fid args) ->
 cm_i32_code_count (cm_args_code_count_of (cm_args_code_counts policy p fid (a::args))) ->
 cm_rep_args_temps_safe (a::args) /\
 cm_args_temps (a::args) <= cm_args_code_count_of (cm_args_code_counts policy p fid (a::args)).
Proof.
 intros [Hsafe [Hl Hr]] [HsafeTail Hbound] Hnode.
 pose proof (cm_args_temps_safe_pair args HsafeTail) as Hpair.
 pose proof (cm_expr_temps_nonnegative__index_bounds a) as Hnonneg.
 unfold cm_i32_code_count in Hnode.
 cbn [cm_rep_args_temps_safe cm_args_apair cm_rep_apair_safe cm_acount cm_adepth].
 unfold cm_args_temps in *.
 cbn [cm_args_apair cm_acount cm_adepth cm_args_code_counts cm_args_code_count_of] in *.
 unfold cm_rep_apair_safe, cm_rtemps, cm_rvalue_code_count, cm_imax in *.
 cbn [cm_acount cm_adepth] in *. intuition lia.
Qed.

Theorem cm_expr_temps_ready_from_counts : forall policy e p fid,
 cm_expr_counts_representable policy p fid e ->
 cm_rep_expr_temps_safe e /\ cm_ltemps e <= cm_lvalue_code_count policy p fid e /\
 cm_rtemps e <= cm_rvalue_code_count policy p fid e.
Proof.
 fix IH 2. intros policy e p fid Hrep.
 destruct e as [n ty|sid ty|scope slot ty|a b ty|op a b ty|op a ty|
   a b ty|a mid ty|callee args ty|asked ty|ty|a ty|a ty|a ty].
 all: try (rewrite cm_expr_counts_repr_call in Hrep).
 all: try (cbn [cm_expr_counts_representable] in Hrep).
 all: destruct Hrep as [Hnode Hchildren].
 all: unfold cm_expr_count_node_representable, cm_code_counts_representable in Hnode.
 all: destruct Hnode as [Hcounts _].
 all: repeat match type of Hchildren with _ /\ _ => destruct Hchildren as [? Hchildren] end.
 all: repeat match goal with
   | H : cm_expr_counts_representable ?pol ?pr ?f ?a |- _ =>
     let Hsafe := fresh "Hsafe" in let Hl := fresh "Hl" in let Hr := fresh "Hr" in
     destruct (IH pol a pr f H) as [Hsafe [Hl Hr]]; clear H
   end.
 all: try pose proof (cm_char_normalize_count_nonnegative ty).
 all: try pose proof (cm_binary_tail_positive p op a b).
 all: try pose proof (cm_expr_code_counts_nonnegative policy p fid a).
 all: try pose proof (cm_expr_code_counts_nonnegative policy p fid b).
 all: try pose proof (cm_expr_temps_nonnegative__index_bounds a).
 all: try pose proof (cm_expr_temps_nonnegative__index_bounds b).
 9: {
   assert (Hargs : cm_rep_args_temps_safe args /\
     cm_args_temps args <= cm_args_code_count_of (cm_args_code_counts policy p fid args)) by
   (clear Hcounts; revert Hchildren; induction args as [|a args IHargs]; intro Hchildren;
    [unfold cm_args_temps; cbn [cm_rep_args_temps_safe cm_args_apair cm_acount cm_adepth
       cm_args_code_counts cm_args_code_count_of]; unfold cm_rep_apair_safe; cbn; intuition lia|
     destruct Hchildren as [Hnode [Ha Htail]];
     apply (cm_args_temps_ready_cons policy p fid a args);
     [exact (IH policy a p fid Ha)|exact (IHargs Htail)|exact Hnode]]).
   destruct Hargs as [Hsafe Hbound].
   pose proof (cm_args_temps_safe_pair args Hsafe) as Hpair.
   rewrite cm_expr_safe_call.
   unfold cm_ltemps, cm_rtemps, cm_lvalue_code_count, cm_rvalue_code_count.
   rewrite cm_expr_tpair_call, cm_expr_counts_call.
   unfold cm_rep_tpair_safe, cm_rep_apair_safe, cm_args_temps in *.
   cbn [cm_tleft cm_tright cm_lcount_of cm_rcount_of]. intuition lia.
 }
 all: cbn [cm_rep_expr_temps_safe].
 all: unfold cm_rep_tpair_safe, cm_ltemps, cm_rtemps,
   cm_lvalue_code_count, cm_rvalue_code_count, cm_i32_code_count in *.
 all: cbn [cm_expr_tpair cm_expr_code_counts cm_tleft cm_tright cm_lcount_of cm_rcount_of] in *.
 all: unfold cm_binding_address_count in *.
 all: repeat match goal with
   | |- context [if ?b then _ else _] => destruct b eqn:?
   | H : context [if ?b then _ else _] |- _ => destruct b eqn:?
   end.
 all: cbn [cm_tleft cm_tright cm_lcount_of cm_rcount_of] in *.
 all: unfold cm_imax in *; intuition lia.
Qed.

Theorem cm_args_temps_ready_from_counts policy args p fid :
 cm_args_counts_representable policy p fid args ->
 cm_rep_args_temps_safe args /\
 cm_args_temps args <= cm_args_code_count_of (cm_args_code_counts policy p fid args).
Proof.
 induction args as [|a args IH]; intro Hrep.
 - unfold cm_args_temps; cbn [cm_rep_args_temps_safe cm_args_apair cm_acount cm_adepth
     cm_args_code_counts cm_args_code_count_of]; unfold cm_rep_apair_safe; cbn; intuition lia.
 - destruct Hrep as [Hnode [Ha Htail]]. apply (cm_args_temps_ready_cons policy p fid a args).
   + exact (cm_expr_temps_ready_from_counts policy a p fid Ha).
   + exact (IH Htail).
   + exact Hnode.
Qed.
Lemma cm_expr_and_args_temps_ready policy :
 (forall e p fid, cm_expr_counts_representable policy p fid e ->
   cm_rep_expr_temps_safe e /\ cm_ltemps e <= cm_lvalue_code_count policy p fid e /\
   cm_rtemps e <= cm_rvalue_code_count policy p fid e) /\
 (forall args p fid, cm_args_counts_representable policy p fid args ->
   cm_rep_args_temps_safe args /\
   cm_args_temps args <= cm_args_code_count_of (cm_args_code_counts policy p fid args)).
Proof. split; [apply cm_expr_temps_ready_from_counts|apply cm_args_temps_ready_from_counts]. Qed.
Lemma cm_stmt_count_node_from_tree policy s p fid :
 cm_stmt_counts_representable policy p fid s -> cm_i32_code_count (cm_stmt_code_count policy p fid s).
Proof. destruct s; cbn [cm_stmt_counts_representable]; tauto. Qed.

Theorem cm_stmt_temps_ready_with_bound policy stmt p fid :
 cm_stmt_counts_representable policy p fid stmt ->
 cm_rep_stmt_temps_safe stmt /\ cm_stemps stmt <= cm_stmt_code_count policy p fid stmt.
Proof.
 induction stmt; intro Hrep; cbn [cm_stmt_counts_representable] in Hrep;
 destruct Hrep as [Hnode Hchildren].
 all: repeat match type of Hchildren with _ /\ _ => destruct Hchildren as [? Hchildren] end.
 all: repeat match goal with
 | H : cm_expr_counts_representable ?pol ?pr ?f ?e |- _ =>
   let Hready := fresh "Hready" in
   pose proof (cm_expr_temps_ready_from_counts pol e pr f H) as Hready;
   pose proof (cm_expr_temps_nonnegative__index_bounds e);
   clear H
 end.
 all: try specialize (IHstmt Hchildren).
 all: try match goal with H : cm_stmt_counts_representable _ _ _ _ |- _ =>
   specialize (IHstmt1 H); specialize (IHstmt2 Hchildren) end.
 all: try pose proof (cm_char_normalize_count_nonnegative
   (cm_slot_ty (cm_slot_at slot (cm_function_locals (cm_function_at policy fid (cm_program_functions p)))))).
 all: pose proof (cm_char_normalize_count_nonnegative
   (cm_function_ret (cm_function_at policy fid (cm_program_functions p)))).
 all: unfold cm_rep_stmt_temps_safe, cm_i32_code_count in *.
 all: cbn [cm_stemps cm_rep_stmt_children_safe cm_stmt_code_count] in *.
 all: unfold cm_imax in *; intuition lia.
Qed.
Theorem cm_stmt_temps_ready_from_counts policy stmt p fid :
 cm_stmt_counts_representable policy p fid stmt -> cm_rep_stmt_temps_safe stmt.
Proof. intro H; exact (proj1 (cm_stmt_temps_ready_with_bound policy stmt p fid H)). Qed.
