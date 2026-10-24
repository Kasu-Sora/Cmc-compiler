(* Arithmetic, byte memory and decimal output from tower_base.c.
   Reuse the verified u8/encode/word-byte definitions. *)
Require Export SimpleC.EE.QCP_demos_human.cmc_tvm_object_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Definition tower_wrap64 z := (z+9223372036854775808) mod 18446744073709551616 - 9223372036854775808.
Definition tower_status := tower_u8.
Definition tower_bool (b:bool) : Z := if b then 1 else 0.
Definition tower_add a b := tower_wrap64 (a+b).
Definition tower_sub a b := tower_wrap64 (a-b).
Definition tower_mul a b := tower_wrap64 (a*b).
Definition tower_neg a := tower_wrap64 (-a).
Definition tower_tquot a b :=
 if b =? 0 then 0 else if a =? 0 then 0 else
 if Bool.eqb (a <? 0) (b <? 0) then Z.abs a / Z.abs b else -(Z.abs a / Z.abs b).
Definition tower_trem a b := a - tower_tquot a b * b.
Definition tower_div a b := tower_wrap64 (tower_tquot a b).
Definition tower_mod a b := tower_wrap64 (tower_trem a b).
Definition tower_decode8 b0 b1 b2 b3 b4 b5 b6 b7 :=
 tower_wrap64 (tower_u8 b0 + 256*tower_u8 b1 + 65536*tower_u8 b2 +
 16777216*tower_u8 b3 + 4294967296*tower_u8 b4 + 1099511627776*tower_u8 b5 +
 281474976710656*tower_u8 b6 + 72057594037927936*tower_u8 b7).
Definition tower_zero_mem (_:Z) : Z := 0.
Definition tower_getb (m:Z->Z) a := tower_u8 (m a).
Definition tower_setb (m:Z->Z) a v x := if x =? a then tower_u8 v else m x.
Definition tower_getw (m:Z->Z) a :=
 tower_decode8 (tower_getb m (a+0)) (tower_getb m (a+1)) (tower_getb m (a+2))
 (tower_getb m (a+3)) (tower_getb m (a+4)) (tower_getb m (a+5))
 (tower_getb m (a+6)) (tower_getb m (a+7)).
Definition tower_setw (m:Z->Z) a z x :=
 if x =? a+0 then tower_encode_byte z 0 else
 if x =? a+1 then tower_encode_byte z 1 else
 if x =? a+2 then tower_encode_byte z 2 else
 if x =? a+3 then tower_encode_byte z 3 else
 if x =? a+4 then tower_encode_byte z 4 else
 if x =? a+5 then tower_encode_byte z 5 else
 if x =? a+6 then tower_encode_byte z 6 else
 if x =? a+7 then tower_encode_byte z 7 else m x.
Definition tower_digit m place := 48 + (m/place) mod 10.
Definition tower_digits (m:Z) : list Z :=
if (1000000000000000000 <=? m) then
         [tower_digit m 1000000000000000000;
          tower_digit m 100000000000000000;
          tower_digit m 10000000000000000;
          tower_digit m 1000000000000000;
          tower_digit m 100000000000000;
          tower_digit m 10000000000000;
          tower_digit m 1000000000000;
          tower_digit m 100000000000;
          tower_digit m 10000000000;
          tower_digit m 1000000000;
          tower_digit m 100000000;
          tower_digit m 10000000;
          tower_digit m 1000000;
          tower_digit m 100000;
          tower_digit m 10000;
          tower_digit m 1000;
          tower_digit m 100;
          tower_digit m 10;
          tower_digit m 1]
       else if (100000000000000000 <=? m) then
         [tower_digit m 100000000000000000;
          tower_digit m 10000000000000000;
          tower_digit m 1000000000000000;
          tower_digit m 100000000000000;
          tower_digit m 10000000000000;
          tower_digit m 1000000000000;
          tower_digit m 100000000000;
          tower_digit m 10000000000;
          tower_digit m 1000000000;
          tower_digit m 100000000;
          tower_digit m 10000000;
          tower_digit m 1000000;
          tower_digit m 100000;
          tower_digit m 10000;
          tower_digit m 1000;
          tower_digit m 100;
          tower_digit m 10;
          tower_digit m 1]
       else if (10000000000000000 <=? m) then
         [tower_digit m 10000000000000000;
          tower_digit m 1000000000000000;
          tower_digit m 100000000000000;
          tower_digit m 10000000000000;
          tower_digit m 1000000000000;
          tower_digit m 100000000000;
          tower_digit m 10000000000;
          tower_digit m 1000000000;
          tower_digit m 100000000;
          tower_digit m 10000000;
          tower_digit m 1000000;
          tower_digit m 100000;
          tower_digit m 10000;
          tower_digit m 1000;
          tower_digit m 100;
          tower_digit m 10;
          tower_digit m 1]
       else if (1000000000000000 <=? m) then
         [tower_digit m 1000000000000000;
          tower_digit m 100000000000000;
          tower_digit m 10000000000000;
          tower_digit m 1000000000000;
          tower_digit m 100000000000;
          tower_digit m 10000000000;
          tower_digit m 1000000000;
          tower_digit m 100000000;
          tower_digit m 10000000;
          tower_digit m 1000000;
          tower_digit m 100000;
          tower_digit m 10000;
          tower_digit m 1000;
          tower_digit m 100;
          tower_digit m 10;
          tower_digit m 1]
       else if (100000000000000 <=? m) then
         [tower_digit m 100000000000000;
          tower_digit m 10000000000000;
          tower_digit m 1000000000000;
          tower_digit m 100000000000;
          tower_digit m 10000000000;
          tower_digit m 1000000000;
          tower_digit m 100000000;
          tower_digit m 10000000;
          tower_digit m 1000000;
          tower_digit m 100000;
          tower_digit m 10000;
          tower_digit m 1000;
          tower_digit m 100;
          tower_digit m 10;
          tower_digit m 1]
       else if (10000000000000 <=? m) then
         [tower_digit m 10000000000000;
          tower_digit m 1000000000000;
          tower_digit m 100000000000;
          tower_digit m 10000000000;
          tower_digit m 1000000000;
          tower_digit m 100000000;
          tower_digit m 10000000;
          tower_digit m 1000000;
          tower_digit m 100000;
          tower_digit m 10000;
          tower_digit m 1000;
          tower_digit m 100;
          tower_digit m 10;
          tower_digit m 1]
       else if (1000000000000 <=? m) then
         [tower_digit m 1000000000000;
          tower_digit m 100000000000;
          tower_digit m 10000000000;
          tower_digit m 1000000000;
          tower_digit m 100000000;
          tower_digit m 10000000;
          tower_digit m 1000000;
          tower_digit m 100000;
          tower_digit m 10000;
          tower_digit m 1000;
          tower_digit m 100;
          tower_digit m 10;
          tower_digit m 1]
       else if (100000000000 <=? m) then
         [tower_digit m 100000000000;
          tower_digit m 10000000000;
          tower_digit m 1000000000;
          tower_digit m 100000000;
          tower_digit m 10000000;
          tower_digit m 1000000;
          tower_digit m 100000;
          tower_digit m 10000;
          tower_digit m 1000;
          tower_digit m 100;
          tower_digit m 10;
          tower_digit m 1]
       else if (10000000000 <=? m) then
         [tower_digit m 10000000000;
          tower_digit m 1000000000;
          tower_digit m 100000000;
          tower_digit m 10000000;
          tower_digit m 1000000;
          tower_digit m 100000;
          tower_digit m 10000;
          tower_digit m 1000;
          tower_digit m 100;
          tower_digit m 10;
          tower_digit m 1]
       else if (1000000000 <=? m) then
         [tower_digit m 1000000000;
          tower_digit m 100000000;
          tower_digit m 10000000;
          tower_digit m 1000000;
          tower_digit m 100000;
          tower_digit m 10000;
          tower_digit m 1000;
          tower_digit m 100;
          tower_digit m 10;
          tower_digit m 1]
       else if (100000000 <=? m) then
         [tower_digit m 100000000;
          tower_digit m 10000000;
          tower_digit m 1000000;
          tower_digit m 100000;
          tower_digit m 10000;
          tower_digit m 1000;
          tower_digit m 100;
          tower_digit m 10;
          tower_digit m 1]
       else if (10000000 <=? m) then
         [tower_digit m 10000000;
          tower_digit m 1000000;
          tower_digit m 100000;
          tower_digit m 10000;
          tower_digit m 1000;
          tower_digit m 100;
          tower_digit m 10;
          tower_digit m 1]
       else if (1000000 <=? m) then
         [tower_digit m 1000000;
          tower_digit m 100000;
          tower_digit m 10000;
          tower_digit m 1000;
          tower_digit m 100;
          tower_digit m 10;
          tower_digit m 1]
       else if (100000 <=? m) then
         [tower_digit m 100000;
          tower_digit m 10000;
          tower_digit m 1000;
          tower_digit m 100;
          tower_digit m 10;
          tower_digit m 1]
       else if (10000 <=? m) then
         [tower_digit m 10000;
          tower_digit m 1000;
          tower_digit m 100;
          tower_digit m 10;
          tower_digit m 1]
       else if (1000 <=? m) then
         [tower_digit m 1000;
          tower_digit m 100;
          tower_digit m 10;
          tower_digit m 1]
       else if (100 <=? m) then
         [tower_digit m 100;
          tower_digit m 10;
          tower_digit m 1]
       else if (10 <=? m) then
         [tower_digit m 10; tower_digit m 1]
       else [tower_digit m 1].
Definition tower_decimal z := if z <? 0 then 45 :: tower_digits (-z) else tower_digits z.

Lemma tower_u8_range z : tower_byte_value (tower_u8 z).
Proof. unfold tower_byte_value, tower_u8. apply Z.mod_pos_bound. lia. Qed.
Lemma tower_wrap64_range z : tower_signed64 (tower_wrap64 z).
Proof. unfold tower_signed64, tower_wrap64. pose proof (Z.mod_pos_bound (z+9223372036854775808) 18446744073709551616 ltac:(lia)). lia. Qed.
Lemma tower_u8_idempotent z : tower_u8 (tower_u8 z) = tower_u8 z.
Proof. unfold tower_u8. apply Z.mod_mod. lia. Qed.
Lemma tower_u8_fixed z : tower_byte_value z -> tower_u8 z = z.
Proof. unfold tower_byte_value, tower_u8. intro H. apply Z.mod_small. exact H. Qed.
Lemma tower_wrap64_fixed z : tower_signed64 z -> tower_wrap64 z = z.
Proof. unfold tower_signed64, tower_wrap64. intros H. rewrite Z.mod_small by lia. lia. Qed.
Lemma tower_wrap64_idempotent z : tower_wrap64 (tower_wrap64 z) = tower_wrap64 z.
Proof. apply tower_wrap64_fixed, tower_wrap64_range. Qed.
Lemma tower_status_range z : tower_byte_value (tower_status z).
Proof. apply tower_u8_range. Qed.
Lemma tower_bool_cases b : tower_bool b = 0 \/ tower_bool b = 1.
Proof. destruct b; cbn; auto. Qed.
Lemma tower_getb_setb_same m a v : tower_getb (tower_setb m a v) a = tower_u8 v.
Proof. unfold tower_getb, tower_setb. rewrite Z.eqb_refl. apply tower_u8_idempotent. Qed.
Lemma tower_getb_setb_other m a b v : b<>a -> tower_getb (tower_setb m a v) b = tower_getb m b.
Proof. intro H. unfold tower_getb, tower_setb. apply Z.eqb_neq in H. rewrite H. reflexivity. Qed.
Lemma tower_div_min_neg1 : tower_div (-9223372036854775808) (-1) = -9223372036854775808.
Proof. reflexivity. Qed.
Lemma tower_mod_min_neg1 : tower_mod (-9223372036854775808) (-1) = 0.
Proof. reflexivity. Qed.
Lemma tower_decimal_zero : tower_decimal 0 = [48].
Proof. reflexivity. Qed.
Lemma tower_decimal_neg1 : tower_decimal (-1) = [45;49].
Proof. reflexivity. Qed.
Lemma tower_decimal_255 : tower_decimal 255 = [50;53;53].
Proof. reflexivity. Qed.
