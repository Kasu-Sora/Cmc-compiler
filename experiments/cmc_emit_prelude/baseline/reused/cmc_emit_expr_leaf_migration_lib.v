(* Leaf-only expression closure of cmc_codegen.c:710 and concrete_defs.c:581.
   No definition of general cm_emit_expr_pair or cm_expr_code_for is claimed. *)
From Coq Require Import ZArith List Bool Lia.
From AUXLib Require Import ListLib.
Require Export SimpleC.EE.QCP_demos_human.cmc_emit_ast_migration_lib.
Import ListNotations.
Local Open Scope Z_scope.

Definition cm_const_immediate (ty:cm_type) (n:Z) :=
  match ty with CMCharTy => tower_u8 n | _ => n end.
Definition cm_strings_prefix := cm_rep_strings_prefix.
Definition cm_string_address p sid :=
  16 + cm_globals_size (cm_program_structs p) (cm_program_globals p) +
  cm_strings_prefix (cm_program_strings p) sid.
Fixpoint cm_member_offset_slots (slots:list cm_slot_d) (mid:Z) : Z :=
  match slots with [] => 0 | s::rest =>
    if Z.eqb mid 0 then 0 else cm_struct_member_size s + cm_member_offset_slots rest (mid-1)
  end.
Definition cm_member_offset structs sid mid :=
  if (Z.leb 0 sid && Z.ltb sid (Zlength structs))%bool
  then cm_member_offset_slots (cm_struct_members (cm_struct_at sid structs)) mid else 0.

(* The datatype makes the unsupported nonleaf boundary explicit. *)
Inductive cm_leaf_expr :=
| CMLeafConst (n:Z) (ty:cm_type)
| CMLeafString (sid:Z) (ty:cm_type)
| CMLeafGetc (ty:cm_type)
| CMLeafSizeof (asked ty:cm_type).
Definition cm_leaf_source_expr leaf := match leaf with
| CMLeafConst n ty => CMConstE n ty | CMLeafString sid ty => CMStringE sid ty
| CMLeafGetc ty => CMGetcE ty | CMLeafSizeof asked ty => CMSizeofE asked ty end.
Definition cm_leaf_of_expr e : option cm_leaf_expr := match e with
| CMConstE n ty => Some (CMLeafConst n ty)
| CMStringE sid ty => Some (CMLeafString sid ty)
| CMGetcE ty => Some (CMLeafGetc ty)
| CMSizeofE asked ty => Some (CMLeafSizeof asked ty)
| _ => None end.
Definition cm_leaf_rvalue p leaf : list tvm_inst := match leaf with
| CMLeafConst n ty => cm_push_code (cm_const_immediate ty n)
| CMLeafString sid _ => cm_push_code (cm_string_address p sid)
| CMLeafGetc _ => [TVMInst TVMGetcOp 0]
| CMLeafSizeof asked _ => cm_push_code (cm_type_size (cm_program_structs p) asked) end.
Definition cm_leaf_code_for p leaf (lvalue:Z) :=
  if Z.eqb lvalue 0 then cm_leaf_rvalue p leaf else [].
Lemma cm_leaf_source_roundtrip leaf : cm_leaf_of_expr (cm_leaf_source_expr leaf) = Some leaf.
Proof. destruct leaf; reflexivity. Qed.
Lemma cm_leaf_const_source_equation p n ty lv :
 cm_leaf_code_for p (CMLeafConst n ty) lv =
 if Z.eqb lv 0 then [TVMInst TVMPushOp (cm_const_immediate ty n)] else [].
Proof. reflexivity. Qed.
Lemma cm_leaf_string_source_equation p sid ty lv :
 cm_leaf_code_for p (CMLeafString sid ty) lv =
 if Z.eqb lv 0 then [TVMInst TVMPushOp (cm_string_address p sid)] else [].
Proof. reflexivity. Qed.
Lemma cm_leaf_getc_source_equation p ty lv :
 cm_leaf_code_for p (CMLeafGetc ty) lv =
 if Z.eqb lv 0 then [TVMInst TVMGetcOp 0] else [].
Proof. reflexivity. Qed.
Lemma cm_leaf_sizeof_source_equation p asked ty lv :
 cm_leaf_code_for p (CMLeafSizeof asked ty) lv =
 if Z.eqb lv 0 then [TVMInst TVMPushOp (cm_type_size (cm_program_structs p) asked)] else [].
Proof. reflexivity. Qed.

Lemma cm_rep_globals_size_matches structs globals :
 (forall i, 0 <= i < Zlength globals -> cm_global_wf structs (cm_global_at i globals)) ->
 cm_rep_globals_size globals = cm_globals_size structs globals.
Proof.
 induction globals as [|h t IH]; intros H; [reflexivity|].
 assert (Hh : cm_global_wf structs h).
 { apply (H 0). rewrite Zlength_cons. pose proof (Zlength_nonneg t). lia. }
 assert (Ht : forall i, 0 <= i < Zlength t -> cm_global_wf structs (cm_global_at i t)).
 { intros i Hi. specialize (H (i+1)). unfold cm_global_at in *.
   replace (i+1) with (Z.succ i) in H by lia.
   rewrite Z2Nat.inj_succ in H by lia. simpl nth in H.
   apply H. rewrite Zlength_cons. lia. }
 cbn [cm_rep_globals_size cm_globals_size]. rewrite (cm_rep_global_size_matches _ _ Hh), (IH Ht). reflexivity.
Qed.
Lemma cm_rep_string_address_matches policy p sid : cm_typed_program policy p ->
 cm_rep_string_address (cm_program_globals p) (cm_program_strings p) sid = cm_string_address p sid.
Proof. intros [_ [H _]]. unfold cm_rep_string_address, cm_string_address, cm_strings_prefix.
 rewrite (cm_rep_globals_size_matches _ _ H). reflexivity. Qed.

Lemma cm_scalar_struct_leaf_size structs ty : cm_scalar_type structs ty -> cm_type_size structs ty = cm_leaf_size ty.
Proof. intros [_ [_ H]]. destruct ty; try reflexivity. exfalso; apply H; exact I. Qed.
Lemma cm_slots_struct_size_matches structs slots : cm_slots_wf structs slots ->
 cm_slots_size structs slots = cm_struct_slots_size slots.
Proof.
 induction slots as [|h t IH]; intros H; [reflexivity|].
 assert (Hh : cm_slot_wf structs h).
 { apply (H 0). rewrite Zlength_cons. pose proof (Zlength_nonneg t). lia. }
 assert (Ht : cm_slots_wf structs t).
 { intros i Hi. specialize (H (i+1)). unfold cm_slot_at in *.
   replace (i+1) with (Z.succ i) in H by lia.
   rewrite Z2Nat.inj_succ in H by lia. simpl nth in H.
   apply H. rewrite Zlength_cons. lia. }
 cbn [cm_slots_size cm_struct_slots_size]. rewrite IH by exact Ht.
 destruct Hh as [_ [Hs _]]. unfold cm_slot_size, cm_struct_member_size.
 rewrite (cm_scalar_struct_leaf_size _ _ Hs). reflexivity.
Qed.
Lemma cm_slots_struct_prefix_matches structs slots mid : cm_slots_wf structs slots ->
 cm_slots_prefix structs slots mid = cm_member_offset_slots slots mid.
Proof.
 revert mid; induction slots as [|h t IH]; intros mid H; [reflexivity|].
 assert (Hh : cm_slot_wf structs h).
 { apply (H 0). rewrite Zlength_cons. pose proof (Zlength_nonneg t). lia. }
 assert (Ht : cm_slots_wf structs t).
 { intros i Hi. specialize (H (i+1)). unfold cm_slot_at in *.
   replace (i+1) with (Z.succ i) in H by lia.
   rewrite Z2Nat.inj_succ in H by lia. simpl nth in H.
   apply H. rewrite Zlength_cons. lia. }
 cbn [cm_slots_prefix cm_member_offset_slots]. destruct (Z.eqb mid 0); [reflexivity|].
 rewrite IH by exact Ht. destruct Hh as [_ [Hs _]]. unfold cm_slot_size, cm_struct_member_size.
 rewrite (cm_scalar_struct_leaf_size _ _ Hs). reflexivity.
Qed.
Lemma cm_rep_struct_size_nth structs sid : 0 <= sid < Zlength structs ->
 cm_rep_struct_size structs sid = cm_rep_members_size (cm_struct_members (cm_struct_at sid structs)).
Proof.
 revert sid; induction structs as [|h t IH]; intros sid H; [rewrite Zlength_nil in H; lia|].
 cbn [cm_rep_struct_size]. destruct (Z.eqb sid 0) eqn:E.
 - apply Z.eqb_eq in E. subst sid. reflexivity.
 - apply Z.eqb_neq in E. assert (Hs : 0 <= sid-1 < Zlength t) by (rewrite Zlength_cons in H; lia).
   rewrite IH by exact Hs. unfold cm_struct_at.
   replace sid with (Z.succ (sid-1)) at 2 by lia.
   rewrite Z2Nat.inj_succ by lia. reflexivity.
Qed.
Lemma cm_rep_type_size_matches structs asked : cm_type_code_wf asked -> cm_type_refs structs asked ->
 (forall i, 0 <= i < Zlength structs -> cm_struct_wf structs (cm_struct_at i structs)) ->
 cm_rep_type_size structs (cm_type_encode asked) = cm_type_size structs asked.
Proof.
 intros Hwf Hr Hs. destruct asked as [| |sid|ty]; try reflexivity.
 - cbn [cm_type_code_wf] in Hwf. cbn [cm_type_refs] in Hr.
   unfold cm_type_encode. cbn [cm_type_depth cm_type_base_code].
   unfold cm_rep_type_size. assert (E1 : (1024 <=? 1024*0+(sid+2)) = false) by (apply Z.leb_gt; lia).
   assert (E2 : (1024*0+(sid+2) =? 0) = false) by (apply Z.eqb_neq; lia).
   assert (E3 : (1024*0+(sid+2) =? 1) = false) by (apply Z.eqb_neq; lia).
   rewrite E1,E2,E3. replace (1024*0+(sid+2)-2) with sid by lia.
   rewrite cm_rep_struct_size_nth by exact Hr.
   destruct (Hs sid Hr) as [_ [Hslots _]].
   rewrite (cm_slots_size_matches__temp_context _ _ Hslots), (cm_slots_struct_size_matches _ _ Hslots).
   cbn [cm_type_size]. unfold cm_struct_size.
   assert (E4 : (0 <=? sid) = true) by (apply Z.leb_le; lia).
   assert (E5 : (sid <? Zlength structs) = true) by (apply Z.ltb_lt; lia).
   rewrite E4,E5. reflexivity.
 - pose proof (cm_type_depth_nonnegative__expression_assignment_safety ty) as Hd.
   pose proof (cm_type_base_bounds__expression_assignment_safety ty Hwf) as Hb.
   unfold cm_rep_type_size,cm_type_encode. cbn [cm_type_depth cm_type_base_code cm_type_size].
   assert (E : (1024 <=? 1024*(1+cm_type_depth ty)+cm_type_base_code ty) = true) by (apply Z.leb_le; lia).
   rewrite E. reflexivity.
Qed.
Lemma cm_rep_struct_member_prefix_nth structs sid mid : 0 <= sid < Zlength structs ->
 cm_rep_struct_member_prefix structs sid mid = cm_rep_member_prefix (cm_struct_members (cm_struct_at sid structs)) mid.
Proof.
 revert sid; induction structs as [|h t IH]; intros sid H; [rewrite Zlength_nil in H; lia|].
 cbn [cm_rep_struct_member_prefix]. destruct (Z.eqb sid 0) eqn:E.
 - apply Z.eqb_eq in E. subst sid. reflexivity.
 - apply Z.eqb_neq in E. assert (Hs : 0 <= sid-1 < Zlength t) by (rewrite Zlength_cons in H; lia).
   rewrite IH by exact Hs. unfold cm_struct_at.
   replace sid with (Z.succ (sid-1)) at 2 by lia.
   rewrite Z2Nat.inj_succ by lia. reflexivity.
Qed.
Lemma cm_rep_struct_member_prefix_matches structs sid mid :
 0 <= sid < Zlength structs -> cm_slots_wf structs (cm_struct_members (cm_struct_at sid structs)) ->
 cm_rep_struct_member_prefix structs sid mid = cm_member_offset structs sid mid.
Proof.
 intros H Hslots. rewrite cm_rep_struct_member_prefix_nth by exact H.
 rewrite (cm_rep_member_prefix_matches _ _ _ Hslots), (cm_slots_struct_prefix_matches _ _ _ Hslots).
 unfold cm_member_offset.
 assert (E1 : (0 <=? sid) = true) by (apply Z.leb_le; lia).
 assert (E2 : (sid <? Zlength structs) = true) by (apply Z.ltb_lt; lia).
 rewrite E1,E2. reflexivity.
Qed.
