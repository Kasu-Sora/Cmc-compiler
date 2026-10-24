From Coq Require Import ZArith List Bool Lia.
Require Export SimpleC.EE.QCP_demos_human.cmc_counts_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_layout_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_copy_bytes_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_write_word_migration_lib.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.

(* Exact structural conjunction from cmc_concrete_data_ready.c. All six
   components of the existing cm_global_wf, including pointer-init = 0,
   remain present through this shared predicate. *)
Fixpoint cm_data_globals_wf (structs : list cm_struct_d)
    (globals : list cm_global_d) : Prop :=
  match globals with
  | [] => True
  | g :: rest => cm_global_wf structs g /\ cm_data_globals_wf structs rest
  end.

Lemma cm_scalar_rep_leaf_size structs t :
  cm_scalar_type structs t ->
  cm_rep_leaf_size (cm_type_encode t) = cm_type_size structs t.
Proof.
  intros [Hcode [Href Hscalar]]. destruct t as [| |sid|t]; try reflexivity.
  - exfalso. apply Hscalar. exact I.
  - pose proof (cm_type_depth_nonnegative__expression_assignment_safety t) as Hd.
    pose proof (cm_type_base_bounds__expression_assignment_safety t Hcode) as Hb.
    unfold cm_rep_leaf_size, cm_type_encode.
    cbn [cm_type_depth cm_type_base_code cm_type_size].
    assert (Hle : (1024 <=? 1024 * (1 + cm_type_depth t) + cm_type_base_code t) = true)
      by (apply Z.leb_le; lia).
    rewrite Hle. reflexivity.
Qed.

Lemma cm_rep_global_size_matches structs g :
  cm_global_wf structs g -> cm_rep_global_size g = cm_global_size structs g.
Proof.
  intros [_ [Hscalar _]]. unfold cm_rep_global_size, cm_rep_code_slot_size, cm_global_size.
  rewrite (cm_scalar_rep_leaf_size structs (cm_global_ty g) Hscalar). reflexivity.
Qed.

(* This equality uses floor division for every integer z, including negatives;
   the immutable counts map/seq model is not replaced by a new definition. *)
Lemma cm_counts_word_bytes_eq_tower z :
  map (fun k : nat => (z / (256 ^ Z.of_nat k)) mod 256) (seq 0 8) =
  tower_word_bytes z.
Proof.
  unfold tower_word_bytes, tower_encode_byte, tower_u8.
  cbn [seq map Z.of_nat Z.eqb].
  repeat rewrite Z.div_div by lia.
  rewrite Z.div_1_r. reflexivity.
Qed.

Lemma cm_global_init_bytes_char g :
  cm_global_ty g = CMCharTy ->
  cm_global_init_bytes g = [tower_u8 (cm_global_init g)].
Proof. intros H. unfold cm_global_init_bytes. rewrite H. reflexivity. Qed.

Lemma cm_global_init_bytes_word g :
  cm_global_ty g <> CMCharTy ->
  cm_global_init_bytes g = tower_word_bytes (cm_global_init g).
Proof.
  intros H. unfold cm_global_init_bytes.
  destruct (cm_global_ty g); try contradiction; apply cm_counts_word_bytes_eq_tower.
Qed.

Lemma cm_global_bytes_initialized structs g :
  0 <= cm_global_size structs g -> cm_global_has_init g = true ->
  cm_global_size structs g = Zlength (cm_global_init_bytes g) ->
  cm_global_bytes structs g = cm_global_init_bytes g.
Proof.
  intros Hnonneg Hinit Hsize. unfold cm_global_bytes.
  rewrite Hinit, <- Hsize, Z.leb_refl.
  assert (Hle : (0 <=? cm_global_size structs g) = true) by (apply Z.leb_le; lia).
  rewrite Hle, Z.sub_diag. cbn. apply app_nil_r.
Qed.

Lemma cm_global_bytes_zero structs g :
  0 <= cm_global_size structs g -> cm_global_has_init g = false ->
  cm_global_bytes structs g = zeros (cm_global_size structs g).
Proof.
  intros Hnonneg Hinit. unfold cm_global_bytes.
  rewrite Hinit.
  assert (Hle : (0 <=? cm_global_size structs g) = true) by (apply Z.leb_le; lia).
  rewrite Hle. reflexivity.
Qed.

Lemma cm_initialized_char_facts__initialized_emission structs g :
  cm_global_wf structs g ->
  cm_rep_bool (cm_global_has_init g) <> 0 ->
  cm_type_encode (cm_global_ty g) = 1 ->
  cm_rep_global_size g = 1 /\
  cm_global_bytes structs g = [tower_u8 (cm_global_init g)].
Proof.
  intros Hwf Hflag Hcode.
  assert (Hinit : cm_global_has_init g = true).
  { unfold cm_rep_bool in Hflag. destruct (cm_global_has_init g); congruence. }
  destruct Hwf as [Hcount [[Htype [Href Hscalar]] [Hbounds [Hcount0 Hrest]]]].
  specialize (Hcount0 Hinit).
  assert (Hchar : cm_global_ty g = CMCharTy).
  { destruct (cm_global_ty g) as [| |sid|t] eqn:Hty; try reflexivity.
    - cbv [cm_type_encode cm_type_depth cm_type_base_code] in Hcode. lia.
    - exfalso. apply Hscalar. exact I.
    - pose proof (cm_type_depth_nonnegative__expression_assignment_safety t) as Hd.
      pose proof (cm_type_base_bounds__expression_assignment_safety t Htype) as Hb.
      unfold cm_type_encode in Hcode.
      cbn [cm_type_depth cm_type_base_code] in Hcode. lia. }
  assert (Hsize : cm_global_size structs g = 1).
  { unfold cm_global_size. rewrite Hcount0, Hchar. reflexivity. }
  assert (Hrep : cm_rep_global_size g = 1).
  { unfold cm_rep_global_size, cm_rep_code_slot_size.
    rewrite Hcount0, Hchar. reflexivity. }
  split; [exact Hrep|].
  rewrite <- (cm_global_init_bytes_char g Hchar).
  apply cm_global_bytes_initialized; try lia; auto.
  rewrite (cm_global_init_bytes_char g Hchar), Hsize. reflexivity.
Qed.
Lemma cm_initialized_word_facts__initialized_emission structs g :
  cm_global_wf structs g ->
  cm_rep_bool (cm_global_has_init g) <> 0 ->
  cm_type_encode (cm_global_ty g) <> 1 ->
  cm_rep_global_size g = 8 /\
  cm_global_bytes structs g = tower_word_bytes (cm_global_init g).
Proof.
  intros Hwf Hflag Hcode.
  pose proof (cm_rep_global_size_matches structs g Hwf) as Hmatch.
  assert (Hinit : cm_global_has_init g = true).
  { unfold cm_rep_bool in Hflag. destruct (cm_global_has_init g); congruence. }
  destruct Hwf as [Hcount [[Htype [Href Hscalar]] [Hbounds [Hcount0 Hrest]]]].
  specialize (Hcount0 Hinit).
  assert (Hnotchar : cm_global_ty g <> CMCharTy).
  { intro H. apply Hcode. rewrite H. reflexivity. }
  assert (Hsize : cm_global_size structs g = 8).
  { unfold cm_global_size. rewrite Hcount0.
    destruct (cm_global_ty g); try reflexivity; contradiction || (exfalso; apply Hscalar; exact I). }
  split; [lia|].
  rewrite <- (cm_global_init_bytes_word g Hnotchar).
  apply cm_global_bytes_initialized; try lia; auto.
  rewrite (cm_global_init_bytes_word g Hnotchar), Hsize.
  unfold tower_word_bytes. reflexivity.
Qed.
