From Coq Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.

(* Direct translation of tower_base.c: positive-divisor HOL integer division
   is Euclidean floor division, represented by Z.div rather than Z.quot. *)
Definition tower_u8 (z : Z) : Z := Z.modulo z 256.

Definition tower_encode_byte (z k : Z) : Z :=
  if Z.eqb k 0 then tower_u8 (z)
  else if Z.eqb k 1 then tower_u8 (z / 256)
  else if Z.eqb k 2 then tower_u8 (z / 256 / 256)
  else if Z.eqb k 3 then tower_u8 (z / 256 / 256 / 256)
  else if Z.eqb k 4 then tower_u8 (z / 256 / 256 / 256 / 256)
  else if Z.eqb k 5 then tower_u8 (z / 256 / 256 / 256 / 256 / 256)
  else if Z.eqb k 6 then tower_u8 (z / 256 / 256 / 256 / 256 / 256 / 256)
  else if Z.eqb k 7 then tower_u8 (z / 256 / 256 / 256 / 256 / 256 / 256 / 256)
  else 0.

Definition tower_word_bytes (z : Z) : list Z :=
  [tower_encode_byte z 0; tower_encode_byte z 1;
   tower_encode_byte z 2; tower_encode_byte z 3;
   tower_encode_byte z 4; tower_encode_byte z 5;
   tower_encode_byte z 6; tower_encode_byte z 7].

From Coq Require Import Lia.
Lemma tower_mod_div_byte__byte_encoding : forall z d q : Z,
  0 < d -> 0 < q ->
  ((z mod (d * 256 * q)) / d) mod 256 = (z / d) mod 256.
Proof.
  intros z d q Hd Hq.
  pose proof (Z.div_mod z (d * 256 * q) ltac:(nia)) as H.
  assert (E : z = z mod (d * 256 * q) +
                   (256 * q * (z / (d * 256 * q))) * d) by nia.
  assert (D : z / d = (z mod (d * 256 * q)) / d +
                     (q * (z / (d * 256 * q))) * 256).
  { rewrite E at 1. rewrite Z.div_add by lia. ring. }
  rewrite D, Z.mod_add by lia. reflexivity.
Qed.
Lemma tower_machine_byte__byte_encoding : forall z k : Z,
  0 <= k <= 7 ->
  ((Z.quot (z mod 2 ^ 64) (256 ^ k)) mod 256) mod 2 ^ 8 =
  tower_encode_byte z k.
Proof.
  intros z k Hk.
  assert (Hd : 0 < 256 ^ k) by (apply Z.pow_pos_nonneg; lia).
  assert (Hq : 0 < 256 ^ (7 - k)) by (apply Z.pow_pos_nonneg; lia).
  assert (K : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/
              k = 4 \/ k = 5 \/ k = 6 \/ k = 7) by lia.
  assert (HN : 2 ^ 64 = 256 ^ k * 256 * 256 ^ (7 - k)).
  { destruct K as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; reflexivity. }
  replace (2 ^ 8) with 256 by reflexivity.
  rewrite Z.mod_mod by lia.
  rewrite Z.quot_div_nonneg by
    (try assumption; pose proof (Z.mod_pos_bound z (2 ^ 64) ltac:(lia)); lia).
  rewrite HN, tower_mod_div_byte__byte_encoding by assumption.
  destruct K as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
    unfold tower_encode_byte, tower_u8;
    cbn [Z.eqb];
    repeat rewrite Z.div_div by lia;
    try rewrite Z.div_1_r;
    reflexivity.
Qed.
Lemma tower_machine_rem_byte__byte_encoding : forall z k : Z,
  0 <= k <= 7 ->
  (Z.rem (Z.quot (z mod 2 ^ 64) (256 ^ k)) 256) mod 2 ^ 8 =
  tower_encode_byte z k.
Proof.
  intros z k Hk.
  assert (Hd : 0 < 256 ^ k) by (apply Z.pow_pos_nonneg; lia).
  assert (Hz : 0 <= z mod 2 ^ 64).
  { apply Z.mod_pos_bound. lia. }
  rewrite Z.rem_mod_nonneg.
  - apply tower_machine_byte__byte_encoding. exact Hk.
  - rewrite Z.quot_div_nonneg by assumption. apply Z.div_pos; assumption.
  - lia.
Qed.
