Require Export SimpleC.EE.QCP_demos_human.cmc_target_load_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma tower_trem_256_nonnegative z : 0<=z -> tower_trem z 256=z mod 256.
Proof.
 intro POS;unfold tower_trem,tower_tquot;change(256=?0)with false;change(256<?0)with false.
 destruct(z=?0)eqn:ZERO;[apply Z.eqb_eq in ZERO;subst;reflexivity|].
 assert(SIGN:(z<?0)=false)by(apply Z.ltb_ge;lia);rewrite SIGN;cbn [Bool.eqb];rewrite Z.abs_eq by lia;change(Z.abs 256)with 256.
 pose proof(Z.div_mod z 256 ltac:(lia));lia.
Qed.
Lemma tower_trem_256_bound z : -256<tower_trem z 256<256.
Proof.
 destruct(Z_le_gt_dec 0 z).
 - rewrite tower_trem_256_nonnegative by lia;pose proof(Z.mod_pos_bound z 256 ltac:(lia));lia.
 - unfold tower_trem,tower_tquot;change(256=?0)with false;change(256<?0)with false.
   assert(ZERO:(z=?0)=false)by(apply Z.eqb_neq;lia);assert(SIGN:(z<?0)=true)by(apply Z.ltb_lt;lia).
   rewrite ZERO,SIGN;cbn [Bool.eqb];rewrite Z.abs_neq by lia;change(Z.abs 256)with 256.
   pose proof(Z.div_mod (-z) 256 ltac:(lia));pose proof(Z.mod_pos_bound (-z) 256 ltac:(lia));lia.
Qed.
Lemma tower_trem_256_mod z : (tower_trem z 256) mod 256=z mod 256.
Proof.
 unfold tower_trem;replace(z-tower_tquot z 256*256)with(z+(-tower_tquot z 256)*256)by ring;apply Z.mod_add;lia.
Qed.
Lemma tower_char_normalize_number z : tower_mod(tower_add(tower_mod z 256)256)256=tower_u8 z.
Proof.
 pose proof(tower_trem_256_bound z)as B;unfold tower_mod,tower_add.
 rewrite(tower_wrap64_fixed(tower_trem z 256))by(unfold tower_signed64;lia).
 rewrite(tower_wrap64_fixed(tower_trem z 256+256))by(unfold tower_signed64;lia).
 rewrite tower_trem_256_nonnegative by lia.
 replace((tower_trem z 256+256)mod 256)with((tower_trem z 256)mod 256)by(rewrite Z.add_mod by lia;cbn;rewrite Z.add_0_r,Z.mod_mod by lia;reflexivity).
 rewrite tower_trem_256_mod;unfold tower_u8;apply tower_wrap64_fixed;unfold tower_signed64;pose proof(Z.mod_pos_bound z 256 ltac:(lia));lia.
Qed.
