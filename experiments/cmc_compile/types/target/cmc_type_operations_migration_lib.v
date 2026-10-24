Require Export SimpleC.EE.QCP_demos_human.cmc_type_lvalue_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_pointer_retype_type_ready v ty : cm_is_pointer (cm_value_type v) -> cm_is_pointer ty -> cm_value_type_compatible (cm_pointer_retype ty v) ty.
Proof. destruct v,ty; cbv beta iota delta [cm_value_type cm_is_pointer cm_pointer_retype cm_pointee cm_value_type_compatible]; intuition congruence. Qed.
Lemma cm_load_value_type_ready st ptr ty : cm_scalar_expr_type ty -> cm_load_ok ty ptr st=true -> cm_value_type_compatible (cm_load_value ty ptr st) ty.
Proof.
 destruct ty; intros SC OK; try solve [left; reflexivity].
 - destruct SC as [[E|E]|E]; discriminate || contradiction.
 - cbn [cm_load_value]; destruct (tower_getw (cm_state_mem st) (cm_value_number st ptr)=?0) eqn:ZERO; [right; split; [reflexivity|exact I]|].
   apply cm_pointer_retype_type_ready; [|exact I].
   unfold cm_load_ok in OK; cbn [cm_is_pointerb negb] in OK; rewrite ZERO in OK; cbn [orb] in OK.
   repeat rewrite andb_true_iff in OK; apply cm_is_pointerb_spec; tauto.
Qed.
Lemma cm_pointer_live_nonnull st v : cm_pointer_live st v=true -> v<>CMNullV.
Proof. intros L ->; unfold cm_pointer_live,cm_ptr_gen in L; discriminate. Qed.
Lemma cm_ptr_add_type_ready structs st ptr index ty : cm_value_type_compatible ptr (CMPtrTy ty) -> cm_pointer_live st ptr=true -> cm_value_type_compatible (cm_ptr_add structs ptr index) (CMPtrTy ty).
Proof. intros T LIVE; left; cbn [cm_ptr_add cm_value_type]; f_equal; apply cm_pointer_value_view; [exact T|eapply cm_pointer_live_nonnull; exact LIVE]. Qed.
Lemma cm_ptr_shift_type_ready structs st ptr index ty : cm_value_type_compatible ptr (CMPtrTy ty) -> cm_ptr_shift_ok structs ptr index st=true -> cm_value_type_compatible (cm_ptr_add structs ptr index) (CMPtrTy ty).
Proof. intros T OK; apply cm_ptr_add_type_ready with (st:=st); [exact T|unfold cm_ptr_shift_ok in OK; repeat rewrite andb_true_iff in OK; tauto]. Qed.
Lemma cm_member_value_type_ready sp p st v base mid : cm_member_valid p base mid -> cm_value_type_compatible v base -> cm_ptr_member_ok sp p v mid st=true -> cm_value_type_compatible (cm_ptr_member sp p v mid) (cm_member_lvalue_type p base mid).
Proof.
 intros [PTR [STR [BOUND MID]]] COMP OK.
 pose proof (cm_pointer_pointee_type _ PTR) as PT.
 rewrite PT in COMP; pose proof (cm_pointer_value_view _ _ COMP) as VIEW.
 assert (LIVE:cm_pointer_live st v=true) by (unfold cm_ptr_member_ok in OK; repeat rewrite andb_true_iff in OK; tauto).
 specialize (VIEW (cm_pointer_live_nonnull _ _ LIVE)).
 left; cbn [cm_ptr_member cm_value_type]; unfold cm_member_slot,cm_member_lvalue_type; rewrite VIEW.
 rewrite (cm_source_struct_at_valid sp _ _ BOUND).
 rewrite (cm_source_slot_at_valid sp _ _ MID); reflexivity.
Qed.
Lemma cm_unary_value_type_ready op v st : cm_value_type_compatible (cm_unary_value op v st) CMIntTy.
Proof. unfold cm_unary_value; destruct (op=?0); left; reflexivity. Qed.
Lemma cm_integer_pointerb_false v ty : cm_value_type_compatible v ty -> cm_integer_type ty -> cm_is_pointerb (cm_value_type v)=false.
Proof. intros C I; pose proof (cm_compatible_integer _ _ C I) as [-> | ->]; reflexivity. Qed.
Lemma cm_pointer_pointerb_true v ty : cm_value_type_compatible v ty -> cm_is_pointer ty -> cm_is_pointerb (cm_value_type v)=true.
Proof. intros C P; apply cm_is_pointerb_spec; eapply cm_compatible_pointer; eauto. Qed.
