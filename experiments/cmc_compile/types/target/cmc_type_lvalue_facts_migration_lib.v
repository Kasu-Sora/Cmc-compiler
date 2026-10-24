Require Export SimpleC.EE.QCP_demos_human.cmc_type_expr_leaf_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_nonarray_lvalue_output policy p f expr : cm_function_wf policy p f -> cm_expr_wf policy p f expr -> ~cm_expr_array p f expr -> cm_lvalue_output_type p f expr=CMPtrTy (cm_expr_type expr).
Proof.
 intros FW EW NA; destruct expr; try reflexivity.
 - cbn [cm_expr_wf] in EW; destruct EW as [BV ->]. unfold cm_lvalue_output_type,cm_expr_type,cm_binding_type,cm_expr_array in *.
   destruct (scope=?0) eqn:S0; [|destruct (scope=?1) eqn:S1]; unfold cm_global_expr_type,cm_slot_expr_type.
   + assert (Z:cm_global_count (cm_global_at slot (cm_program_globals p))=0) by lia; now rewrite Z.
   + assert (Z:cm_slot_count (cm_slot_at slot (cm_function_locals f))=0) by lia; now rewrite Z.
   + destruct FW as [_ [[_ PARAMS] _]]; destruct BV as [[B _]|[[B _]|[B BOUND]]]; try (subst scope; discriminate).
     rewrite (PARAMS slot BOUND); reflexivity.
 - cbn [cm_expr_wf] in EW; destruct EW as [_ [_ ->]]. unfold cm_lvalue_output_type,cm_expr_type,cm_member_type,cm_member_lvalue_type,cm_slot_expr_type.
   assert (ZERO:cm_slot_count (cm_slot_at mid (cm_struct_members (cm_struct_at (cm_struct_id (cm_pointee (cm_expr_type expr))) (cm_program_structs p))))=0) by (unfold cm_expr_array in NA; lia).
   unfold cm_expr_type in ZERO; rewrite ZERO; reflexivity.
Qed.
Lemma cm_binary_operand_scalars op a b ty : cm_binary_types op a b ty -> cm_scalar_expr_type a /\ cm_scalar_expr_type b.
Proof.
 unfold cm_binary_types; intros [_ H]; repeat match type of H with context[if ?b then _ else _]=>destruct b end;
 unfold cm_scalar_expr_type; intuition congruence.
Qed.
Lemma cm_nonzero_cursor_values policy nilslot p fid expr cursors : expr<>CMConstE 0 CMIntTy -> cm_cursor_expr_values_type_ready policy nilslot p fid expr cursors -> forall v,cm_value_type_compatible v (cm_expr_type expr) -> cm_cursor_head_value_type_ready policy nilslot p fid v cursors.
Proof. intros N H v V; apply H; now apply cm_expr_not_zero_ready. Qed.
