From Coq Require Import ZArith List Bool Lia.
Require Export SimpleC.EE.QCP_demos_human.cmc_emit_expr_dispatch_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_emit_expr_var_migration_lib.
Import ListNotations.
Local Open Scope Z_scope.

(* Exact source leaf-or-variable domain; code is defined only on this view. *)
Definition cm_simple_expr (e : cm_expr) : Prop :=
 cm_dispatch_leaf e \/ cm_rep_expr_kind e = 2.
Inductive cm_simple_view :=
| CMSimpleLeaf (leaf : cm_leaf_expr)
| CMSimpleVar (scope slot : Z) (ty : cm_type).
Definition cm_simple_source_expr simple := match simple with
| CMSimpleLeaf leaf => cm_leaf_source_expr leaf
| CMSimpleVar scope slot ty => CMVarE scope slot ty end.
Definition cm_simple_code_for policy p fid simple lvalue := match simple with
| CMSimpleLeaf leaf => cm_leaf_code_for p leaf lvalue
| CMSimpleVar scope slot ty => cm_var_code_for policy p fid scope slot ty lvalue end.

Lemma cm_simple_source_coverage e :
 cm_simple_expr e <-> exists simple, e = cm_simple_source_expr simple.
Proof.
 split.
 - intros [Hleaf|Hvar].
   + apply cm_dispatch_leaf_coverage in Hleaf. destruct Hleaf as [leaf ->].
     exists (CMSimpleLeaf leaf). reflexivity.
   + destruct e; cbn [cm_rep_expr_kind] in Hvar; try discriminate.
     exists (CMSimpleVar scope slot ty). reflexivity.
 - intros [simple ->]. destruct simple as [leaf|scope slot ty].
   + left. apply cm_dispatch_leaf_coverage. exists leaf. reflexivity.
   + right. reflexivity.
Qed.
Lemma cm_simple_source_unique a b :
 cm_simple_source_expr a = cm_simple_source_expr b -> a = b.
Proof.
 destruct a as [la|sa ia ta], b as [lb|sb ib tb]; cbn [cm_simple_source_expr]; intro H.
 - apply cm_dispatch_leaf_unique in H. subst. reflexivity.
 - destruct la; discriminate.
 - destruct lb; discriminate.
 - inversion H. reflexivity.
Qed.
