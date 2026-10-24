From Coq Require Import ZArith List Bool Lia.
Require Export SimpleC.EE.QCP_demos_human.cmc_emit_expr_leaf_migration_lib.
Import ListNotations.
Local Open Scope Z_scope.

(* Source cm_leaf_expr boolean predicate, renamed to avoid collision with
   the already verified explicit leaf-view datatype. *)
Definition cm_dispatch_leaf (e : cm_expr) : Prop :=
 cm_rep_expr_kind e = 0 \/ cm_rep_expr_kind e = 1 \/
 cm_rep_expr_kind e = 9 \/ cm_rep_expr_kind e = 10.

(* Introducing the leaf-view witness preserves exactly the source domain. *)
Lemma cm_dispatch_leaf_coverage e :
 cm_dispatch_leaf e <-> exists leaf, e = cm_leaf_source_expr leaf.
Proof.
 split.
 - destruct e; cbn [cm_dispatch_leaf cm_rep_expr_kind]; intros H;
   try (destruct H as [H|[H|[H|H]]]; discriminate).
   + exists (CMLeafConst n ty). reflexivity.
   + exists (CMLeafString sid ty). reflexivity.
   + exists (CMLeafSizeof asked ty). reflexivity.
   + exists (CMLeafGetc ty). reflexivity.
 - intros [leaf ->]. unfold cm_dispatch_leaf; destruct leaf; cbn [cm_leaf_source_expr cm_rep_expr_kind]; tauto.
Qed.
Lemma cm_dispatch_leaf_unique a b :
 cm_leaf_source_expr a = cm_leaf_source_expr b -> a = b.
Proof. intro H. apply (f_equal cm_leaf_of_expr) in H.
 rewrite !cm_leaf_source_roundtrip in H. congruence. Qed.
