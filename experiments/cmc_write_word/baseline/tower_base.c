#include "proof/proof.h"
#include "userlib/renderers.h"
#include "tower_base.h"
#include "userlib/proof.h"
#require "userlib/proof.c"

PROOF static size_t _tower_base_axioms_before = vector_size(get_all_axioms());

/* Signed scalar domains and deterministic wrapping operations. */
PROOF thm tower_signed64_def = new_fun_definition(
    `tower_signed64 (z:int) <=>
       --9223372036854775808i <= z && z <= 9223372036854775807i`);
PROOF static int _e_tower_signed64 =
    cst_add_const_to_header(`tower_signed64:int->bool`);

PROOF thm tower_byte_value_def = new_fun_definition(
    `tower_byte_value (z:int) <=> 0i <= z && z < 256i`);
PROOF static int _e_tower_byte_value =
    cst_add_const_to_header(`tower_byte_value:int->bool`);

PROOF thm tower_wrap64_def = new_fun_definition(
    `tower_wrap64 (z:int) =
       (z + 9223372036854775808i) % 18446744073709551616i -
       9223372036854775808i`);
PROOF static int _e_tower_wrap64 =
    cst_add_const_to_header(`tower_wrap64:int->int`);

PROOF thm tower_u8_def = new_fun_definition(
    `tower_u8 (z:int) = z % 256i`);
PROOF static int _e_tower_u8 = cst_add_const_to_header(`tower_u8:int->int`);

PROOF thm tower_status_def = new_fun_definition(
    `tower_status (z:int) = tower_u8 z`);
PROOF static int _e_tower_status =
    cst_add_const_to_header(`tower_status:int->int`);

PROOF thm tower_bool_def = new_fun_definition(
    `tower_bool (b:bool) = if b then 1i else 0i`);
PROOF static int _e_tower_bool = cst_add_const_to_header(`tower_bool:bool->int`);

PROOF thm tower_add_def = new_fun_definition(
    `tower_add (a:int) (b:int) = tower_wrap64 (a + b)`);
PROOF static int _e_tower_add = cst_add_const_to_header(`tower_add:int->int->int`);
PROOF thm tower_sub_def = new_fun_definition(
    `tower_sub (a:int) (b:int) = tower_wrap64 (a - b)`);
PROOF static int _e_tower_sub = cst_add_const_to_header(`tower_sub:int->int->int`);
PROOF thm tower_mul_def = new_fun_definition(
    `tower_mul (a:int) (b:int) = tower_wrap64 (a * b)`);
PROOF static int _e_tower_mul = cst_add_const_to_header(`tower_mul:int->int->int`);
PROOF thm tower_neg_def = new_fun_definition(
    `tower_neg (a:int) = tower_wrap64 (--a)`);
PROOF static int _e_tower_neg = cst_add_const_to_header(`tower_neg:int->int`);

/* Truncation toward zero is defined independently of HOL's Euclidean
 * integer division.  Division by zero is represented here by zero; both
 * semantic clients guard it before applying this total helper. */
PROOF thm tower_tquot_def = new_fun_definition(
    `tower_tquot (a:int) (b:int) =
       if b == 0i then 0i
       else if a == 0i then 0i
       else if ((a < 0i) <=> (b < 0i))
            then abs a / abs b
            else --(abs a / abs b)`);
PROOF static int _e_tower_tquot =
    cst_add_const_to_header(`tower_tquot:int->int->int`);

PROOF thm tower_trem_def = new_fun_definition(
    `tower_trem (a:int) (b:int) = a - tower_tquot a b * b`);
PROOF static int _e_tower_trem =
    cst_add_const_to_header(`tower_trem:int->int->int`);

PROOF thm tower_div_def = new_fun_definition(
    `tower_div (a:int) (b:int) = tower_wrap64 (tower_tquot a b)`);
PROOF static int _e_tower_div = cst_add_const_to_header(`tower_div:int->int->int`);
PROOF thm tower_mod_def = new_fun_definition(
    `tower_mod (a:int) (b:int) = tower_wrap64 (tower_trem a b)`);
PROOF static int _e_tower_mod = cst_add_const_to_header(`tower_mod:int->int->int`);

PROOF thm get_tower_signed64_def(void) { return tower_signed64_def; }
PROOF thm get_tower_byte_value_def(void) { return tower_byte_value_def; }
PROOF thm get_tower_wrap64_def(void) { return tower_wrap64_def; }
PROOF thm get_tower_u8_def(void) { return tower_u8_def; }
PROOF thm get_tower_status_def(void) { return tower_status_def; }
PROOF thm get_tower_bool_def(void) { return tower_bool_def; }
PROOF thm get_tower_add_def(void) { return tower_add_def; }
PROOF thm get_tower_sub_def(void) { return tower_sub_def; }
PROOF thm get_tower_mul_def(void) { return tower_mul_def; }
PROOF thm get_tower_neg_def(void) { return tower_neg_def; }
PROOF thm get_tower_tquot_def(void) { return tower_tquot_def; }
PROOF thm get_tower_trem_def(void) { return tower_trem_def; }
PROOF thm get_tower_div_def(void) { return tower_div_def; }
PROOF thm get_tower_mod_def(void) { return tower_mod_def; }

PROOF static thm tower_positive_abs(const term n) {
  return spec_rule(n, get_theorem_by_name("INT_ABS_NUM"));
}

PROOF thm mk_tower_u8_range(void) {
  gnode root = gnode_new_with_ccl(
      `!z. tower_byte_value (tower_u8 (z:int))`);
  gnode g = AUTO_INTROS_TAC(root);
  thm d = mp_rule(
      specl_rule(TERM_LIST(`z:int`, `256i`),
                 get_theorem_by_name("INT_DIVISION")),
      int_arith_rule(`~(256i == 0i)`));
  d = conv_rule(rewrite_conv(THM_LIST(tower_positive_abs(`256:num`))), d);
  thm lo = conjunct1_rule(conjunct2_rule(d));
  thm hi = conjunct2_rule(conjunct2_rule(d));
  thm body = mp_rule(mp_rule(int_arith_rule(
      `0i <= (z:int) % 256i ==> z % 256i < 256i ==>
       0i <= z % 256i && z % 256i < 256i`), lo), hi);
  ACCEPT_TAC(CONV_TAC(g, rewrite_conv(
      THM_LIST(tower_byte_value_def, tower_u8_def))), body);
  return gnode_prove(root);
}
PROOF thm tower_u8_range = mk_tower_u8_range();

PROOF thm mk_tower_wrap64_range(void) {
  gnode root = gnode_new_with_ccl(
      `!z. tower_signed64 (tower_wrap64 (z:int))`);
  gnode g = AUTO_INTROS_TAC(root);
  thm d = mp_rule(
      specl_rule(TERM_LIST(`(z:int) + 9223372036854775808i`,
                           `18446744073709551616i`),
                 get_theorem_by_name("INT_DIVISION")),
      int_arith_rule(`~(18446744073709551616i == 0i)`));
  d = conv_rule(rewrite_conv(THM_LIST(
      tower_positive_abs(`18446744073709551616:num`))), d);
  thm lo = conjunct1_rule(conjunct2_rule(d));
  thm hi = conjunct2_rule(conjunct2_rule(d));
  thm body = mp_rule(mp_rule(int_arith_rule(
      `0i <= ((z:int) + 9223372036854775808i) %
             18446744073709551616i ==>
       ((z + 9223372036854775808i) % 18446744073709551616i) <
             18446744073709551616i ==>
       --9223372036854775808i <=
         ((z + 9223372036854775808i) % 18446744073709551616i -
          9223372036854775808i) &&
         ((z + 9223372036854775808i) % 18446744073709551616i -
          9223372036854775808i) <= 9223372036854775807i`), lo), hi);
  ACCEPT_TAC(CONV_TAC(g, rewrite_conv(
      THM_LIST(tower_signed64_def, tower_wrap64_def))), body);
  return gnode_prove(root);
}
PROOF thm tower_wrap64_range = mk_tower_wrap64_range();

PROOF thm mk_tower_u8_idempotent(void) {
  gnode root = gnode_new_with_ccl(
      `!z. tower_u8 (tower_u8 (z:int)) == tower_u8 z`);
  gnode g = AUTO_INTROS_TAC(root);
  thm rr = specl_rule(TERM_LIST(`z:int`, `256i`),
      get_theorem_by_name("INT_REM_REM"));
  ACCEPT_TAC(CONV_TAC(g, rewrite_conv(THM_LIST(tower_u8_def))), rr);
  return gnode_prove(root);
}
PROOF thm tower_u8_idempotent = mk_tower_u8_idempotent();

PROOF thm mk_tower_u8_fixed(void) {
  gnode root = gnode_new_with_ccl(
      `!z. tower_byte_value (z:int) ==> tower_u8 z == z`);
  gnode g = AUTO_INTROS_TAC(root);
  thm byte_bounds = conv_rule(rewrite_conv(
      THM_LIST(tower_byte_value_def)),
      assume_rule(`tower_byte_value (z:int)`));
  thm premise = conj_rule(
      int_arith_rule(`(z:int) == 0i * 256i + z`),
      byte_bounds);
  thm uniq_rule = conv_rule(rewrite_conv(THM_LIST(
      tower_positive_abs(`256:num`))),
      specl_rule(TERM_LIST(`z:int`, `256i`, `0i`, `z:int`),
          get_theorem_by_name("INT_DIVMOD_UNIQ")));
  thm remainder = conjunct2_rule(mp_rule(uniq_rule, premise));
  ACCEPT_TAC(CONV_TAC(g, rewrite_conv(THM_LIST(tower_u8_def))),
      remainder);
  return gnode_prove(root);
}
PROOF thm tower_u8_fixed = mk_tower_u8_fixed();

PROOF thm get_tower_wrap64_range(void) { return tower_wrap64_range; }
PROOF thm get_tower_u8_range(void) { return tower_u8_range; }
PROOF thm get_tower_u8_idempotent(void) { return tower_u8_idempotent; }
PROOF thm get_tower_u8_fixed(void) { return tower_u8_fixed; }

PROOF thm mk_tower_wrap64_idempotent(void) {
  gnode root = gnode_new_with_ccl(
      `!z. tower_wrap64 (tower_wrap64 (z:int)) == tower_wrap64 z`);
  gnode g = AUTO_INTROS_TAC(root);
  thm wr = conv_rule(rewrite_conv(THM_LIST(tower_signed64_def)),
      spec_rule(`z:int`, tower_wrap64_range));
  thm wlo = conjunct1_rule(wr);
  thm whi = conjunct2_rule(wr);
  thm xlo = mp_rule(int_arith_rule(
      `--9223372036854775808i <= tower_wrap64 (z:int) ==>
       0i <= tower_wrap64 z + 9223372036854775808i`), wlo);
  thm xhi = mp_rule(int_arith_rule(
      `tower_wrap64 (z:int) <= 9223372036854775807i ==>
       tower_wrap64 z + 9223372036854775808i <
         18446744073709551616i`), whi);
  thm premise = conj_rule(
      int_arith_rule(
          `tower_wrap64 (z:int) + 9223372036854775808i ==
           0i * 18446744073709551616i +
           (tower_wrap64 z + 9223372036854775808i)`),
      conj_rule(xlo, xhi));
  thm uniq_rule = conv_rule(rewrite_conv(THM_LIST(
      tower_positive_abs(`18446744073709551616:num`))),
      specl_rule(TERM_LIST(
          `tower_wrap64 (z:int) + 9223372036854775808i`,
          `18446744073709551616i`, `0i`,
          `tower_wrap64 (z:int) + 9223372036854775808i`),
          get_theorem_by_name("INT_DIVMOD_UNIQ")));
  thm uniq = mp_rule(uniq_rule, premise);
  thm remself = conjunct2_rule(uniq);
  thm reduced = mp_rule(int_arith_rule(
      `(tower_wrap64 (z:int) + 9223372036854775808i) %
          18446744073709551616i ==
          tower_wrap64 z + 9223372036854775808i ==>
       (tower_wrap64 z + 9223372036854775808i) %
          18446744073709551616i -
          9223372036854775808i == tower_wrap64 z`), remself);
  thm outer = inst_rule(TERM_PAIR_LIST(
      (term_pair){`tower_wrap64 (z:int)`, `z:int`}), tower_wrap64_def);
  ACCEPT_TAC(g, trans_rule(outer, reduced));
  return gnode_prove(root);
}
PROOF thm tower_wrap64_idempotent = mk_tower_wrap64_idempotent();

PROOF thm mk_tower_wrap64_fixed(void) {
  gnode root = gnode_new_with_ccl(
      `!z. tower_signed64 (z:int) ==> tower_wrap64 z == z`);
  gnode g = AUTO_INTROS_TAC(root);
  thm signed_parts = conv_rule(rewrite_conv(THM_LIST(tower_signed64_def)),
      assume_rule(`tower_signed64 (z:int)`));
  thm xlo = mp_rule(int_arith_rule(
      `--9223372036854775808i <= (z:int) ==>
       0i <= z + 9223372036854775808i`),
      conjunct1_rule(signed_parts));
  thm xhi = mp_rule(int_arith_rule(
      `(z:int) <= 9223372036854775807i ==>
       z + 9223372036854775808i < 18446744073709551616i`),
      conjunct2_rule(signed_parts));
  thm premise = conj_rule(
      int_arith_rule(
          `(z:int) + 9223372036854775808i ==
           0i * 18446744073709551616i +
           (z + 9223372036854775808i)`),
      conj_rule(xlo, xhi));
  thm uniq_rule = conv_rule(rewrite_conv(THM_LIST(
      tower_positive_abs(`18446744073709551616:num`))),
      specl_rule(TERM_LIST(
          `(z:int) + 9223372036854775808i`,
          `18446744073709551616i`, `0i`,
          `(z:int) + 9223372036854775808i`),
          get_theorem_by_name("INT_DIVMOD_UNIQ")));
  thm remself = conjunct2_rule(mp_rule(uniq_rule, premise));
  thm reduced = mp_rule(int_arith_rule(
      `((z:int) + 9223372036854775808i) %
          18446744073709551616i ==
          z + 9223372036854775808i ==>
       (z + 9223372036854775808i) %
          18446744073709551616i -
          9223372036854775808i == z`), remself);
  thm outer = tower_wrap64_def;
  ACCEPT_TAC(g, trans_rule(outer, reduced));
  return gnode_prove(root);
}
PROOF thm tower_wrap64_fixed = mk_tower_wrap64_fixed();

PROOF thm mk_tower_wrap64_u8(void) {
  gnode root = gnode_new_with_ccl(
      `!z. tower_wrap64 (tower_u8 (z:int)) == tower_u8 z`);
  gnode g = AUTO_INTROS_TAC(root);
  thm byte_range = conv_rule(rewrite_conv(THM_LIST(
      tower_byte_value_def)), spec_rule(`z:int`, tower_u8_range));
  thm signed_range = mp_rule(int_arith_rule(
      `0i <= tower_u8 (z:int) && tower_u8 z < 256i ==>
       --9223372036854775808i <= tower_u8 z &&
       tower_u8 z <= 9223372036854775807i`), byte_range);
  thm folded_range = eq_mp_rule(sym_rule(inst_rule(TERM_PAIR_LIST(
      (term_pair){`tower_u8 (z:int)`, `z:int`}), tower_signed64_def)),
      signed_range);
  thm fixed = mp_rule(spec_rule(
      `tower_u8 (z:int)`, tower_wrap64_fixed), folded_range);
  ACCEPT_TAC(g, fixed);
  return gnode_prove(root);
}
PROOF thm tower_wrap64_u8 = mk_tower_wrap64_u8();
PROOF thm mk_tower_u8_wrap64(void) {
  gnode root = gnode_new_with_ccl(
      `!z. tower_u8 (tower_wrap64 (z:int)) == tower_u8 z`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm down = int_ring_rule(
      `((((z:int) + 9223372036854775808i) %
           18446744073709551616i) -
          9223372036854775808i) ==
       (((z + 9223372036854775808i) %
           18446744073709551616i) +
        256i * --36028797018963968i)`);
  thm down_mod = beta_norm(ap_term_rule(
      `\x:int. x % 256i`, down));
  thm add_clause = get_theorem_by_name("INT_REM_MUL_ADD");
  for (size_t i = 0; i < 3; ++i) {
    add_clause = conjunct2_rule(add_clause);
  }
  thm down_strip = specl_rule(TERM_LIST(
      `--36028797018963968i:int`, `256i:int`,
      `((z:int) + 9223372036854775808i) %
         18446744073709551616i`), add_clause);
  thm nested = specl_rule(TERM_LIST(
      `(z:int) + 9223372036854775808i`,
      `256i:int`, `72057594037927936i:int`),
      conjunct1_rule(get_theorem_by_name("INT_REM_REM_MUL")));
  nested = conv_rule(
      get_conversion_by_name("INT_REDUCE_CONV"), nested);
  thm up = int_ring_rule(
      `(z:int) + 9223372036854775808i ==
       z + 256i * 36028797018963968i`);
  thm up_mod = beta_norm(ap_term_rule(
      `\x:int. x % 256i`, up));
  thm up_strip = specl_rule(TERM_LIST(
      `36028797018963968i:int`, `256i:int`, `z:int`),
      add_clause);
  thm result = trans_rule(down_mod,
      trans_rule(down_strip,
      trans_rule(nested,
      trans_rule(up_mod, up_strip))));
  gnode opened = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      tower_u8_def, tower_wrap64_def)));
  ACCEPT_TAC(opened, result);
  return gnode_prove(root);
}
PROOF thm tower_u8_wrap64 = mk_tower_u8_wrap64();


PROOF thm mk_tower_status_range(void) {
  gnode root = gnode_new_with_ccl(
      `!z. 0i <= tower_status (z:int) && tower_status z < 256i`);
  gnode g = AUTO_INTROS_TAC(root);
  thm ur = conv_rule(rewrite_conv(THM_LIST(
      tower_byte_value_def, tower_u8_def)),
      spec_rule(`z:int`, tower_u8_range));
  ACCEPT_TAC(CONV_TAC(g, rewrite_conv(THM_LIST(
      tower_status_def, tower_u8_def))), ur);
  return gnode_prove(root);
}
PROOF thm tower_status_range = mk_tower_status_range();

PROOF thm mk_tower_div_min_neg1(void) {
  gnode root = gnode_new_with_ccl(
      `tower_div (--9223372036854775808i) (--1i) ==
       --9223372036854775808i`);
  CONV_TAC(root, reduce_rewrite_conv(THM_LIST(
      tower_div_def, tower_tquot_def, tower_wrap64_def,
      get_theorem_by_name("INT_REM_REFL"))));
  return gnode_prove(root);
}
PROOF thm tower_div_min_neg1 = mk_tower_div_min_neg1();

PROOF thm mk_tower_mod_min_neg1(void) {
  gnode root = gnode_new_with_ccl(
      `tower_mod (--9223372036854775808i) (--1i) == 0i`);
  CONV_TAC(root, reduce_rewrite_conv(THM_LIST(
      tower_mod_def, tower_trem_def, tower_tquot_def,
      tower_wrap64_def, get_theorem_by_name("INT_REM_REFL"))));
  return gnode_prove(root);
}
PROOF thm tower_mod_min_neg1 = mk_tower_mod_min_neg1();

PROOF thm tower_bool_cases = prove_by_cases(
    `!b. tower_bool (b:bool) == 0i || tower_bool b == 1i`,
    "b", `b:bool`, THM_LIST(tower_bool_def));

PROOF thm get_tower_wrap64_idempotent(void) {
  return tower_wrap64_idempotent;
}
PROOF thm get_tower_wrap64_fixed(void) {
  return tower_wrap64_fixed;
}
PROOF thm get_tower_wrap64_u8(void) {
  return tower_wrap64_u8;
}
PROOF thm get_tower_u8_wrap64(void) {
  return tower_u8_wrap64;
}
PROOF thm get_tower_status_range(void) { return tower_status_range; }
PROOF thm get_tower_div_min_neg1(void) { return tower_div_min_neg1; }
PROOF thm get_tower_mod_min_neg1(void) { return tower_mod_min_neg1; }
PROOF thm get_tower_bool_cases(void) { return tower_bool_cases; }

/* Eight-byte little-endian encoding.  Repeated Euclidean quotients make
 * this definition valid for every mathematical integer; the eight low
 * residues are exactly its two's-complement low 64 bits. */
PROOF thm tower_encode_byte_def = new_fun_definition(
    `tower_encode_byte (z:int) (k:int) =
       if k == 0i then tower_u8 z
       else if k == 1i then tower_u8 (z / 256i)
       else if k == 2i then tower_u8 (z / 256i / 256i)
       else if k == 3i then tower_u8 (z / 256i / 256i / 256i)
       else if k == 4i then tower_u8 (z / 256i / 256i / 256i / 256i)
       else if k == 5i then
         tower_u8 (z / 256i / 256i / 256i / 256i / 256i)
       else if k == 6i then
         tower_u8 (z / 256i / 256i / 256i / 256i / 256i / 256i)
       else if k == 7i then
         tower_u8
           (z / 256i / 256i / 256i / 256i / 256i / 256i / 256i)
       else 0i`);
PROOF static int _e_tower_encode_byte =
    cst_add_const_to_header(`tower_encode_byte:int->int->int`);

PROOF thm tower_decode8_def = new_fun_definition(
    `tower_decode8 (b0:int) (b1:int) (b2:int) (b3:int)
                   (b4:int) (b5:int) (b6:int) (b7:int) =
       tower_wrap64
         (tower_u8 b0 +
          256i * tower_u8 b1 +
          65536i * tower_u8 b2 +
          16777216i * tower_u8 b3 +
          4294967296i * tower_u8 b4 +
          1099511627776i * tower_u8 b5 +
          281474976710656i * tower_u8 b6 +
          72057594037927936i * tower_u8 b7)`);
PROOF static int _e_tower_decode8 =
    cst_add_const_to_header(
        `tower_decode8:int->int->int->int->int->int->int->int->int`);

PROOF thm tower_word_bytes_def = new_fun_definition(
    `tower_word_bytes (z:int) =
       [tower_encode_byte z 0i; tower_encode_byte z 1i;
        tower_encode_byte z 2i; tower_encode_byte z 3i;
        tower_encode_byte z 4i; tower_encode_byte z 5i;
        tower_encode_byte z 6i; tower_encode_byte z 7i]`);
PROOF static int _e_tower_word_bytes =
    cst_add_const_to_header(`tower_word_bytes:int->(int)list`);

PROOF thm get_tower_encode_byte_def(void) {
  return tower_encode_byte_def;
}
PROOF thm get_tower_decode8_def(void) { return tower_decode8_def; }
PROOF thm get_tower_word_bytes_def(void) { return tower_word_bytes_def; }

PROOF thm mk_tower_wrap64_periodic(void) {
  gnode root = gnode_new_with_ccl(
      `!z k. tower_wrap64
          ((z:int) + k * 18446744073709551616i) == tower_wrap64 z`);
  gnode g = AUTO_INTROS_TAC(root);
  thm rearrange = int_ring_rule(
      `((z:int) + k * 18446744073709551616i) +
          9223372036854775808i ==
       (z + 9223372036854775808i) +
          k * 18446744073709551616i`);
  thm rem_rearrange = beta_norm(ap_term_rule(
      `\x:int. x % 18446744073709551616i`, rearrange));
  thm four = get_theorem_by_name("INT_REM_MUL_ADD");
  thm third = conjunct1_rule(conjunct2_rule(conjunct2_rule(four)));
  thm periodic_rem = specl_rule(TERM_LIST(
      `k:int`, `18446744073709551616i`,
      `(z:int) + 9223372036854775808i`), third);
  thm rem_eq = trans_rule(rem_rearrange, periodic_rem);
  thm body = beta_norm(ap_term_rule(
      `\x:int. x - 9223372036854775808i`, rem_eq));
  ACCEPT_TAC(CONV_TAC(g, rewrite_conv(THM_LIST(tower_wrap64_def))), body);
  return gnode_prove(root);
}
PROOF static thm tower_wrap64_periodic = mk_tower_wrap64_periodic();

PROOF thm mk_tower_decode_encode(void) {
  term q0 = `z:int`;
  term q1 = `${q0:int} / 256i`;
  term q2 = `${q1:int} / 256i`;
  term q3 = `${q2:int} / 256i`;
  term q4 = `${q3:int} / 256i`;
  term q5 = `${q4:int} / 256i`;
  term q6 = `${q5:int} / 256i`;
  term q7 = `${q6:int} / 256i`;
  term q8 = `${q7:int} / 256i`;
  term r0 = `${q0:int} % 256i`;
  term r1 = `${q1:int} % 256i`;
  term r2 = `${q2:int} % 256i`;
  term r3 = `${q3:int} % 256i`;
  term r4 = `${q4:int} % 256i`;
  term r5 = `${q5:int} % 256i`;
  term r6 = `${q6:int} % 256i`;
  term r7 = `${q7:int} % 256i`;
  term sum =
      `${r0:int} +
       256i * ${r1:int} +
       65536i * ${r2:int} +
       16777216i * ${r3:int} +
       4294967296i * ${r4:int} +
       1099511627776i * ${r5:int} +
       281474976710656i * ${r6:int} +
       72057594037927936i * ${r7:int}`;

  thm divsimp = get_theorem_by_name("INT_DIVISION_SIMP");
  thm d0 = sym_rule(specl_rule(TERM_LIST(q0, `256i`), divsimp));
  thm d1 = sym_rule(specl_rule(TERM_LIST(q1, `256i`), divsimp));
  thm d2 = sym_rule(specl_rule(TERM_LIST(q2, `256i`), divsimp));
  thm d3 = sym_rule(specl_rule(TERM_LIST(q3, `256i`), divsimp));
  thm d4 = sym_rule(specl_rule(TERM_LIST(q4, `256i`), divsimp));
  thm d5 = sym_rule(specl_rule(TERM_LIST(q5, `256i`), divsimp));
  thm d6 = sym_rule(specl_rule(TERM_LIST(q6, `256i`), divsimp));
  thm d7 = sym_rule(specl_rule(TERM_LIST(q7, `256i`), divsimp));
  thm chain = int_ring_rule(
      `${q0:int} == ${q1:int} * 256i + ${r0:int} ==>
       ${q1:int} == ${q2:int} * 256i + ${r1:int} ==>
       ${q2:int} == ${q3:int} * 256i + ${r2:int} ==>
       ${q3:int} == ${q4:int} * 256i + ${r3:int} ==>
       ${q4:int} == ${q5:int} * 256i + ${r4:int} ==>
       ${q5:int} == ${q6:int} * 256i + ${r5:int} ==>
       ${q6:int} == ${q7:int} * 256i + ${r6:int} ==>
       ${q7:int} == ${q8:int} * 256i + ${r7:int} ==>
       ${q0:int} == ${sum:int} +
         18446744073709551616i * ${q8:int}`);
  thm expansion = mp_rule(mp_rule(mp_rule(mp_rule(mp_rule(mp_rule(
      mp_rule(mp_rule(chain, d0), d1), d2), d3), d4), d5), d6), d7);
  thm sumform = mp_rule(int_ring_rule(
      `${q0:int} == ${sum:int} +
          18446744073709551616i * ${q8:int} ==>
       ${sum:int} == ${q0:int} +
          (--(${q8:int})) * 18446744073709551616i`), expansion);
  thm at_sum = beta_norm(ap_term_rule(`tower_wrap64:int->int`, sumform));
  thm periodic = specl_rule(TERM_LIST(
      q0, `--(${q8:int})`), tower_wrap64_periodic);
  thm wrapped = trans_rule(at_sum, periodic);

  gnode root = gnode_new_with_ccl(
      `!z. tower_decode8
          (tower_encode_byte (z:int) 0i)
          (tower_encode_byte z 1i)
          (tower_encode_byte z 2i)
          (tower_encode_byte z 3i)
          (tower_encode_byte z 4i)
          (tower_encode_byte z 5i)
          (tower_encode_byte z 6i)
          (tower_encode_byte z 7i) ==
        tower_wrap64 z`);
  gnode g = AUTO_INTROS_TAC(root);
  gnode reduced1 = CONV_TAC(g, reduce_rewrite_conv(THM_LIST(
      tower_decode8_def, tower_encode_byte_def, tower_u8_def)));
  gnode reduced = CONV_TAC(reduced1, rewrite_conv(THM_LIST(
      get_theorem_by_name("INT_REM_REM"))));
  ACCEPT_TAC(reduced, wrapped);
  return gnode_prove(root);
}
PROOF thm tower_decode_encode = mk_tower_decode_encode();
PROOF thm get_tower_decode_encode(void) { return tower_decode_encode; }

/* Total numerical byte memory. */
PROOF thm tower_addr_valid_def = new_fun_definition(
    `tower_addr_valid (a:int) <=> 0i <= a && a < 1048576i`);
PROOF static int _e_tower_addr_valid =
    cst_add_const_to_header(`tower_addr_valid:int->bool`);

PROOF thm tower_word_valid_def = new_fun_definition(
    `tower_word_valid (a:int) <=> 0i <= a && a + 7i < 1048576i`);
PROOF static int _e_tower_word_valid =
    cst_add_const_to_header(`tower_word_valid:int->bool`);

PROOF thm tower_zero_mem_def = new_fun_definition(
    `tower_zero_mem (a:int) = 0i`);
PROOF static int _e_tower_zero_mem =
    cst_add_const_to_header(`tower_zero_mem:int->int`);

PROOF thm tower_getb_def = new_fun_definition(
    `tower_getb (m:int->int) (a:int) = tower_u8 (m a)`);
PROOF static int _e_tower_getb =
    cst_add_const_to_header(`tower_getb:(int->int)->int->int`);

PROOF thm tower_setb_def = new_fun_definition(
    `tower_setb (m:int->int) (a:int) (v:int) =
       \x. if x == a then tower_u8 v else m x`);
PROOF static int _e_tower_setb =
    cst_add_const_to_header(`tower_setb:(int->int)->int->int->int->int`);

PROOF thm tower_getw_def = new_fun_definition(
    `tower_getw (m:int->int) (a:int) =
       tower_decode8
         (tower_getb m (a + 0i)) (tower_getb m (a + 1i))
         (tower_getb m (a + 2i)) (tower_getb m (a + 3i))
         (tower_getb m (a + 4i)) (tower_getb m (a + 5i))
         (tower_getb m (a + 6i)) (tower_getb m (a + 7i))`);
PROOF static int _e_tower_getw =
    cst_add_const_to_header(`tower_getw:(int->int)->int->int`);

PROOF thm tower_setw_def = new_fun_definition(
    `tower_setw (m:int->int) (a:int) (z:int) =
       \x. if x == a + 0i then tower_encode_byte z 0i
           else if x == a + 1i then tower_encode_byte z 1i
           else if x == a + 2i then tower_encode_byte z 2i
           else if x == a + 3i then tower_encode_byte z 3i
           else if x == a + 4i then tower_encode_byte z 4i
           else if x == a + 5i then tower_encode_byte z 5i
           else if x == a + 6i then tower_encode_byte z 6i
           else if x == a + 7i then tower_encode_byte z 7i
           else m x`);
PROOF static int _e_tower_setw =
    cst_add_const_to_header(`tower_setw:(int->int)->int->int->int->int`);

PROOF thm get_tower_addr_valid_def(void) { return tower_addr_valid_def; }
PROOF thm get_tower_word_valid_def(void) { return tower_word_valid_def; }
PROOF thm get_tower_zero_mem_def(void) { return tower_zero_mem_def; }
PROOF thm get_tower_getb_def(void) { return tower_getb_def; }
PROOF thm get_tower_setb_def(void) { return tower_setb_def; }
PROOF thm get_tower_getw_def(void) { return tower_getw_def; }
PROOF thm get_tower_setw_def(void) { return tower_setw_def; }

PROOF thm mk_tower_getb_setb_same(void) {
  gnode root = gnode_new_with_ccl(
      `!m a v. tower_getb
          (tower_setb (m:int->int) (a:int) (v:int)) a == tower_u8 v`);
  gnode g = AUTO_INTROS_TAC(root);
  CONV_TAC(g, reduce_rewrite_conv(THM_LIST(
      tower_getb_def, tower_setb_def, tower_u8_idempotent)));
  return gnode_prove(root);
}
PROOF thm tower_getb_setb_same = mk_tower_getb_setb_same();

PROOF thm mk_tower_getb_setb_other(void) {
  gnode root = gnode_new_with_ccl(
      `!m a b v. ~(b == a) ==>
       tower_getb (tower_setb (m:int->int) (a:int) (v:int)) b ==
       tower_getb m b`);
  gnode g = AUTO_INTROS_TAC(root);
  CONV_WITH_ASMP_TAC(g, reduce_rewrite_conv,
      THM_LIST(tower_getb_def, tower_setb_def));
  return gnode_prove(root);
}
PROOF thm tower_getb_setb_other = mk_tower_getb_setb_other();

PROOF thm mk_tower_offset_eq(void) {
  gnode root = gnode_new_with_ccl(
      `!a i j. (((a:int) + i == a + j) <=> i == j)`);
  gnode g = AUTO_INTROS_TAC(root);
  ACCEPT_TAC(g, int_arith_rule(
      `(((a:int) + i == a + j) <=> i == j)`));
  return gnode_prove(root);
}
PROOF static thm tower_offset_eq = mk_tower_offset_eq();

PROOF thm mk_tower_getw_setw(void) {
  gnode root = gnode_new_with_ccl(
      `!m a z. tower_getw
          (tower_setw (m:int->int) (a:int) (z:int)) a ==
        tower_wrap64 z`);
  gnode g = AUTO_INTROS_TAC(root);
  gnode expanded = CONV_TAC(g, rewrite_conv(THM_LIST(
      tower_getw_def, tower_getb_def, tower_setw_def)));
  gnode selected = CONV_TAC(expanded, reduce_rewrite_conv(
      THM_LIST(tower_offset_eq)));
  gnode normalized1 = CONV_TAC(selected, reduce_rewrite_conv(THM_LIST(
      tower_encode_byte_def, tower_u8_def)));
  gnode normalized = CONV_TAC(normalized1, rewrite_conv(THM_LIST(
      get_theorem_by_name("INT_REM_REM"))));
  thm expected1 = conv_rule(reduce_rewrite_conv(THM_LIST(
      tower_encode_byte_def, tower_u8_def)),
      spec_rule(`z:int`, tower_decode_encode));
  thm expected = conv_rule(rewrite_conv(THM_LIST(
      get_theorem_by_name("INT_REM_REM"))), expected1);
  ACCEPT_TAC(normalized, expected);
  return gnode_prove(root);
}
PROOF thm tower_getw_setw = mk_tower_getw_setw();

PROOF thm get_tower_getb_setb_same(void) {
  return tower_getb_setb_same;
}
PROOF thm get_tower_getb_setb_other(void) {
  return tower_getb_setb_other;
}
PROOF thm get_tower_getw_setw(void) { return tower_getw_setw; }

/* Canonical signed-decimal byte rendering for signed-64 inputs. */
PROOF thm tower_digit_def = new_fun_definition(
    `tower_digit (m:int) (place:int) = 48i + (m / place) % 10i`);
PROOF static int _e_tower_digit =
    cst_add_const_to_header(`tower_digit:int->int->int`);

PROOF thm tower_digits_def = new_fun_definition(
    `tower_digits (m:int) =
       if 1000000000000000000i <= m then
         [tower_digit m 1000000000000000000i;
          tower_digit m 100000000000000000i;
          tower_digit m 10000000000000000i;
          tower_digit m 1000000000000000i;
          tower_digit m 100000000000000i;
          tower_digit m 10000000000000i;
          tower_digit m 1000000000000i;
          tower_digit m 100000000000i;
          tower_digit m 10000000000i;
          tower_digit m 1000000000i;
          tower_digit m 100000000i;
          tower_digit m 10000000i;
          tower_digit m 1000000i;
          tower_digit m 100000i;
          tower_digit m 10000i;
          tower_digit m 1000i;
          tower_digit m 100i;
          tower_digit m 10i;
          tower_digit m 1i]
       else if 100000000000000000i <= m then
         [tower_digit m 100000000000000000i;
          tower_digit m 10000000000000000i;
          tower_digit m 1000000000000000i;
          tower_digit m 100000000000000i;
          tower_digit m 10000000000000i;
          tower_digit m 1000000000000i;
          tower_digit m 100000000000i;
          tower_digit m 10000000000i;
          tower_digit m 1000000000i;
          tower_digit m 100000000i;
          tower_digit m 10000000i;
          tower_digit m 1000000i;
          tower_digit m 100000i;
          tower_digit m 10000i;
          tower_digit m 1000i;
          tower_digit m 100i;
          tower_digit m 10i;
          tower_digit m 1i]
       else if 10000000000000000i <= m then
         [tower_digit m 10000000000000000i;
          tower_digit m 1000000000000000i;
          tower_digit m 100000000000000i;
          tower_digit m 10000000000000i;
          tower_digit m 1000000000000i;
          tower_digit m 100000000000i;
          tower_digit m 10000000000i;
          tower_digit m 1000000000i;
          tower_digit m 100000000i;
          tower_digit m 10000000i;
          tower_digit m 1000000i;
          tower_digit m 100000i;
          tower_digit m 10000i;
          tower_digit m 1000i;
          tower_digit m 100i;
          tower_digit m 10i;
          tower_digit m 1i]
       else if 1000000000000000i <= m then
         [tower_digit m 1000000000000000i;
          tower_digit m 100000000000000i;
          tower_digit m 10000000000000i;
          tower_digit m 1000000000000i;
          tower_digit m 100000000000i;
          tower_digit m 10000000000i;
          tower_digit m 1000000000i;
          tower_digit m 100000000i;
          tower_digit m 10000000i;
          tower_digit m 1000000i;
          tower_digit m 100000i;
          tower_digit m 10000i;
          tower_digit m 1000i;
          tower_digit m 100i;
          tower_digit m 10i;
          tower_digit m 1i]
       else if 100000000000000i <= m then
         [tower_digit m 100000000000000i;
          tower_digit m 10000000000000i;
          tower_digit m 1000000000000i;
          tower_digit m 100000000000i;
          tower_digit m 10000000000i;
          tower_digit m 1000000000i;
          tower_digit m 100000000i;
          tower_digit m 10000000i;
          tower_digit m 1000000i;
          tower_digit m 100000i;
          tower_digit m 10000i;
          tower_digit m 1000i;
          tower_digit m 100i;
          tower_digit m 10i;
          tower_digit m 1i]
       else if 10000000000000i <= m then
         [tower_digit m 10000000000000i;
          tower_digit m 1000000000000i;
          tower_digit m 100000000000i;
          tower_digit m 10000000000i;
          tower_digit m 1000000000i;
          tower_digit m 100000000i;
          tower_digit m 10000000i;
          tower_digit m 1000000i;
          tower_digit m 100000i;
          tower_digit m 10000i;
          tower_digit m 1000i;
          tower_digit m 100i;
          tower_digit m 10i;
          tower_digit m 1i]
       else if 1000000000000i <= m then
         [tower_digit m 1000000000000i;
          tower_digit m 100000000000i;
          tower_digit m 10000000000i;
          tower_digit m 1000000000i;
          tower_digit m 100000000i;
          tower_digit m 10000000i;
          tower_digit m 1000000i;
          tower_digit m 100000i;
          tower_digit m 10000i;
          tower_digit m 1000i;
          tower_digit m 100i;
          tower_digit m 10i;
          tower_digit m 1i]
       else if 100000000000i <= m then
         [tower_digit m 100000000000i;
          tower_digit m 10000000000i;
          tower_digit m 1000000000i;
          tower_digit m 100000000i;
          tower_digit m 10000000i;
          tower_digit m 1000000i;
          tower_digit m 100000i;
          tower_digit m 10000i;
          tower_digit m 1000i;
          tower_digit m 100i;
          tower_digit m 10i;
          tower_digit m 1i]
       else if 10000000000i <= m then
         [tower_digit m 10000000000i;
          tower_digit m 1000000000i;
          tower_digit m 100000000i;
          tower_digit m 10000000i;
          tower_digit m 1000000i;
          tower_digit m 100000i;
          tower_digit m 10000i;
          tower_digit m 1000i;
          tower_digit m 100i;
          tower_digit m 10i;
          tower_digit m 1i]
       else if 1000000000i <= m then
         [tower_digit m 1000000000i;
          tower_digit m 100000000i;
          tower_digit m 10000000i;
          tower_digit m 1000000i;
          tower_digit m 100000i;
          tower_digit m 10000i;
          tower_digit m 1000i;
          tower_digit m 100i;
          tower_digit m 10i;
          tower_digit m 1i]
       else if 100000000i <= m then
         [tower_digit m 100000000i;
          tower_digit m 10000000i;
          tower_digit m 1000000i;
          tower_digit m 100000i;
          tower_digit m 10000i;
          tower_digit m 1000i;
          tower_digit m 100i;
          tower_digit m 10i;
          tower_digit m 1i]
       else if 10000000i <= m then
         [tower_digit m 10000000i;
          tower_digit m 1000000i;
          tower_digit m 100000i;
          tower_digit m 10000i;
          tower_digit m 1000i;
          tower_digit m 100i;
          tower_digit m 10i;
          tower_digit m 1i]
       else if 1000000i <= m then
         [tower_digit m 1000000i;
          tower_digit m 100000i;
          tower_digit m 10000i;
          tower_digit m 1000i;
          tower_digit m 100i;
          tower_digit m 10i;
          tower_digit m 1i]
       else if 100000i <= m then
         [tower_digit m 100000i;
          tower_digit m 10000i;
          tower_digit m 1000i;
          tower_digit m 100i;
          tower_digit m 10i;
          tower_digit m 1i]
       else if 10000i <= m then
         [tower_digit m 10000i;
          tower_digit m 1000i;
          tower_digit m 100i;
          tower_digit m 10i;
          tower_digit m 1i]
       else if 1000i <= m then
         [tower_digit m 1000i;
          tower_digit m 100i;
          tower_digit m 10i;
          tower_digit m 1i]
       else if 100i <= m then
         [tower_digit m 100i;
          tower_digit m 10i;
          tower_digit m 1i]
       else if 10i <= m then
         [tower_digit m 10i; tower_digit m 1i]
       else [tower_digit m 1i]`);
PROOF static int _e_tower_digits =
    cst_add_const_to_header(`tower_digits:int->(int)list`);

PROOF thm tower_decimal_def = new_fun_definition(
    `tower_decimal (z:int) =
       if z < 0i then 45i :: tower_digits (--z) else tower_digits z`);
PROOF static int _e_tower_decimal =
    cst_add_const_to_header(`tower_decimal:int->(int)list`);

PROOF thm get_tower_digit_def(void) { return tower_digit_def; }
PROOF thm get_tower_digits_def(void) { return tower_digits_def; }
PROOF thm get_tower_decimal_def(void) { return tower_decimal_def; }

PROOF static thm tower_decimal_closed(const term ccl) {
  gnode root = gnode_new_with_ccl(ccl);
  CONV_TAC(root, reduce_rewrite_conv(THM_LIST(
      tower_decimal_def, tower_digits_def, tower_digit_def,
      get_theorem_by_name("INT_REM_DIV"))));
  return gnode_prove(root);
}

PROOF thm tower_decimal_zero =
    tower_decimal_closed(`tower_decimal 0i == [48i]`);
PROOF thm tower_decimal_neg1 =
    tower_decimal_closed(`tower_decimal (--1i) == [45i; 49i]`);
PROOF thm tower_decimal_255 =
    tower_decimal_closed(`tower_decimal 255i == [50i; 53i; 53i]`);

PROOF thm get_tower_decimal_zero(void) { return tower_decimal_zero; }
PROOF thm get_tower_decimal_neg1(void) { return tower_decimal_neg1; }
PROOF thm get_tower_decimal_255(void) { return tower_decimal_255; }

PROOF static int _tower_base_audit(void) {
  thm_list pubs = THM_LIST(
      tower_signed64_def, tower_byte_value_def,
      tower_wrap64_def, tower_u8_def, tower_status_def, tower_bool_def,
      tower_add_def, tower_sub_def, tower_mul_def, tower_neg_def,
      tower_tquot_def, tower_trem_def, tower_div_def, tower_mod_def,
      tower_u8_range, tower_wrap64_range, tower_u8_idempotent,
      tower_u8_fixed,
      tower_wrap64_idempotent, tower_wrap64_fixed, tower_wrap64_u8,
      tower_u8_wrap64, tower_status_range,
      tower_div_min_neg1, tower_mod_min_neg1, tower_bool_cases,
      tower_encode_byte_def, tower_decode8_def, tower_word_bytes_def,
      tower_wrap64_periodic, tower_decode_encode,
      tower_addr_valid_def, tower_word_valid_def, tower_zero_mem_def,
      tower_getb_def, tower_setb_def, tower_getw_def, tower_setw_def,
      tower_getb_setb_same, tower_getb_setb_other,
      tower_offset_eq, tower_getw_setw,
      tower_digit_def, tower_digits_def, tower_decimal_def,
      tower_decimal_zero, tower_decimal_neg1, tower_decimal_255);
  for (size_t i = 0; i < vector_size(pubs); ++i) {
    ENSURE_COND(!IS_NULL(pubs[i]),
                "tower_base theorem %zu is empty", i);
    ENSURE_COND(vector_size(hyp(pubs[i])) == 0,
                "tower_base theorem %zu has hypotheses", i);
  }
  ENSURE_COND(vector_size(get_all_axioms()) == _tower_base_axioms_before,
              "tower_base introduced an axiom");
  return 0;
err:
  ERR_FUN_PUTS("_tower_base_audit");
  return -1;
}
PROOF int _tower_base_audit_run = _tower_base_audit();
