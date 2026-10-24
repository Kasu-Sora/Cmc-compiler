#include "cmc_concrete_emit_word.h"
#include "userlib/proof.h"
#include "userlib/operational.h"
#require "cmc_concrete_emit_bytes.c"

PROOF static thm cmc_div256_collapse(const term base,
                                     const size_t steps) {
  term denominators[8] = {
    `1i:int`, `256i:int`, `65536i:int`, `16777216i:int`,
    `4294967296i:int`, `1099511627776i:int`,
    `281474976710656i:int`, `72057594037927936i:int`
  };
  if (steps == 0)
    return refl_rule(base);
  if (steps == 1)
    return refl_rule(`(${base:int}) / 256i`);

  thm result = mp_rule(specl_rule(TERM_LIST(
      base, denominators[1], `256i:int`),
      get_theorem_by_name("INT_DIV_DIV")),
      int_arith_rule(`0i <= 256i`));
  result = conv_rule(
      get_conversion_by_name("INT_REDUCE_CONV"), result);
  for (size_t step = 2; step < steps; ++step) {
    thm lifted = beta_norm(ap_term_rule(`\x:int. x / 256i`, result));
    thm collapse = mp_rule(specl_rule(TERM_LIST(
        base, denominators[step], `256i:int`),
        get_theorem_by_name("INT_DIV_DIV")),
        int_arith_rule(`0i <= ${denominators[step]:int}`));
    collapse = conv_rule(
        get_conversion_by_name("INT_REDUCE_CONV"), collapse);
    result = trans_rule(lifted, collapse);
  }
  return result;
}

PROOF static thm cmc_unsigned_byte(
    const term denominator, const term small_modulus,
    const term outer_factor, const term index,
    const size_t quotient_steps) {
  thm concrete = apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("unsigned_last_nbits_def"),
        get_theorem_by_name("cast_unsigned_def"),
        get_theorem_by_name("INT_EXP_2_DEF"),
        get_theorem_by_name("NUM_OF_INT_OF_NUM"),
        get_theorem_by_name("INT_REM_REM"))),
      `unsigned_last_nbits
        (unsigned_last_nbits (z:int) 64i /
          ${denominator:int} % 256i) 8i`);
  concrete = rewrite_rule(THM_LIST(
      apply_conversion(get_conversion_by_name("NUM_REDUCE_CONV"),
        `2 EXP 64`),
      apply_conversion(get_conversion_by_name("NUM_REDUCE_CONV"),
        `2 EXP 8`)), concrete);
  concrete = conv_rule(rewrite_conv(THM_LIST(
      get_theorem_by_name("INT_DIV_1"),
      get_theorem_by_name("INT_REM_REM"))), concrete);

  thm left_divrem = mp_rule(specl_rule(TERM_LIST(
      `(z:int) % 18446744073709551616i`,
      denominator, `256i:int`),
      get_theorem_by_name("INT_DIV_REM")),
      int_arith_rule(`0i <= ${denominator:int}`));
  left_divrem = conv_rule(
      get_conversion_by_name("INT_REDUCE_CONV"), left_divrem);
  left_divrem = conv_rule(rewrite_conv(THM_LIST(
      get_theorem_by_name("INT_DIV_1"))), left_divrem);

  thm nested = specl_rule(TERM_LIST(
      `z:int`, outer_factor, small_modulus),
      conjunct2_rule(get_theorem_by_name("INT_REM_REM_MUL")));
  nested = conv_rule(get_conversion_by_name("INT_REDUCE_CONV"), nested);
  thm lifted = beta_norm(ap_term_rule(
      `\x:int. x / ${denominator:int}`, nested));
  lifted = conv_rule(rewrite_conv(THM_LIST(
      get_theorem_by_name("INT_DIV_1"))), lifted);

  thm right_divrem = mp_rule(specl_rule(TERM_LIST(
      `z:int`, denominator, `256i:int`),
      get_theorem_by_name("INT_DIV_REM")),
      int_arith_rule(`0i <= ${denominator:int}`));
  right_divrem = conv_rule(
      get_conversion_by_name("INT_REDUCE_CONV"), right_divrem);
  right_divrem = conv_rule(rewrite_conv(THM_LIST(
      get_theorem_by_name("INT_DIV_1"))), right_divrem);

  thm model_def = apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_tower_encode_byte_def(), get_tower_u8_def())),
      `tower_encode_byte (z:int) ${index:int}`);
  thm model = model_def;
  if (quotient_steps > 1) {
    thm model_collapse = beta_norm(ap_term_rule(
        `\x:int. x % 256i`,
        cmc_div256_collapse(`z:int`, quotient_steps)));
    model = trans_rule(model_def, model_collapse);
  }
  if (quotient_steps == 0) {
    return gen_rule(`z:int`, trans_rule(concrete,
        trans_rule(nested, sym_rule(model))));
  }
  return gen_rule(`z:int`, trans_rule(concrete,
      trans_rule(left_divrem, trans_rule(lifted,
        trans_rule(sym_rule(right_divrem), sym_rule(model))))));
}

PROOF thm cmc_unsigned_byte0_bridge =
    cmc_unsigned_byte(`1i:int`, `256i:int`,
      `72057594037927936i:int`, `0i:int`, 0);
PROOF static thm cmc_unsigned_byte1_bridge =
    cmc_unsigned_byte(`256i:int`, `65536i:int`,
      `281474976710656i:int`, `1i:int`, 1);
PROOF static thm cmc_unsigned_byte2_bridge =
    cmc_unsigned_byte(`65536i:int`, `16777216i:int`,
      `1099511627776i:int`, `2i:int`, 2);
PROOF static thm cmc_unsigned_byte3_bridge =
    cmc_unsigned_byte(`16777216i:int`, `4294967296i:int`,
      `4294967296i:int`, `3i:int`, 3);
PROOF static thm cmc_unsigned_byte4_bridge =
    cmc_unsigned_byte(`4294967296i:int`, `1099511627776i:int`,
      `16777216i:int`, `4i:int`, 4);
PROOF static thm cmc_unsigned_byte5_bridge =
    cmc_unsigned_byte(`1099511627776i:int`, `281474976710656i:int`,
      `65536i:int`, `5i:int`, 5);
PROOF static thm cmc_unsigned_byte6_bridge =
    cmc_unsigned_byte(`281474976710656i:int`, `72057594037927936i:int`,
      `256i:int`, `6i:int`, 6);
PROOF static thm cmc_unsigned_byte7_bridge =
    cmc_unsigned_byte(`72057594037927936i:int`,
      `18446744073709551616i:int`, `1i:int`, `7i:int`, 7);

PROOF static thm cmc_encoded_byte_range(const term index) {
  thm model = apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_tower_encode_byte_def())),
      `tower_encode_byte (z:int) ${index:int}`);
  struct dest_comb_results encoded = dest_comb(rhs_of(model));
  thm byte_value = spec_rule(encoded.tm2, get_tower_u8_range());
  thm lifted = ap_term_rule(`tower_byte_value:int->bool`, model);
  return gen_rule(`z:int`, eqt_intro_rule(
      eq_mp_rule(sym_rule(lifted), byte_value)));
}

PROOF static void cmc_normalize_word_prefix(const term old_prefix,
                                            const term new_prefix) {
  struct dest_comb_results old_outer = dest_comb(old_prefix);
  struct dest_comb_results old_head = dest_comb(old_outer.tm1);
  struct dest_comb_results old_first_outer = dest_comb(old_head.tm2);
  struct dest_comb_results old_first_head =
      dest_comb(old_first_outer.tm1);
  struct dest_comb_results new_outer = dest_comb(new_prefix);
  struct dest_comb_results new_head = dest_comb(new_outer.tm1);

  thm assoc = ispecl_rule(TERM_LIST(
      old_first_head.tm2, old_first_outer.tm2, old_outer.tm2),
      get_theorem_by_name("APPEND_ASSOC"));
  thm prior_view = apply_conversion(
      rewrite_conv(THM_LIST(get_theorem_by_name("APPEND"))),
      mk_comb(mk_comb(
        `APPEND:(int)list->(int)list->(int)list`,
        old_first_outer.tm2), old_outer.tm2));
  thm expanded_view = apply_conversion(
      rewrite_conv(THM_LIST(get_theorem_by_name("APPEND"))),
      new_outer.tm2);
  thm inner_shape = trans_rule(prior_view, sym_rule(expanded_view));
  thm lifted = mk_comb_rule(mk_comb_rule(refl_rule(
      `APPEND:(int)list->(int)list->(int)list`),
      refl_rule(new_head.tm2)), inner_shape);
  substitute_st(trans_rule(sym_rule(assoc), lifted));
}

void cmc_write_word(unsigned char *data, int capacity,
                    int cursor, long long word_value)
    [[cst::param(`prefix:(int)list`)]]
    [[cst::require(
      `fact(0i <= cursor) ** fact(cursor + 8i <= capacity) **
       fact(capacity <= 2147483647i) **
       store_uint8_array data cursor prefix **
       store_undef_uint8_array
         (data + cursor * sizeof Tuchar) (capacity - cursor)`)]]
    [[cst::ensure(
      `store_uint8_array data (cursor + 8i)
         (prefix ++ tower_word_bytes word_value) **
       store_undef_uint8_array
         (data + (cursor + 8i) * sizeof Tuchar)
         (capacity - (cursor + 8i))`)]]
{
  unsigned long long bits = (unsigned long long)word_value;
  unsigned char b0 = (unsigned char)(bits % 256ULL);
  unsigned char b1 = (unsigned char)((bits / 256ULL) % 256ULL);
  unsigned char b2 = (unsigned char)((bits / 65536ULL) % 256ULL);
  unsigned char b3 = (unsigned char)((bits / 16777216ULL) % 256ULL);
  unsigned char b4 = (unsigned char)((bits / 4294967296ULL) % 256ULL);
  unsigned char b5 = (unsigned char)((bits / 1099511627776ULL) % 256ULL);
  unsigned char b6 = (unsigned char)((bits / 281474976710656ULL) % 256ULL);
  unsigned char b7 = (unsigned char)((bits / 72057594037927936ULL) % 256ULL);

  [[cst::proof]] {
    add_fact_st(spec_rule(`word_value__pre:int`,
        cmc_unsigned_byte0_bridge));
    add_fact_st(spec_rule(`word_value__pre:int`,
        cmc_encoded_byte_range(`0i:int`)));
  }
  [[cst::where(`prefix`, `prefix:(int)list`)]]
  [[cst::where(`model_byte`,
      `tower_encode_byte (word_value__pre:int) 0i`)]]
  cmc_write_byte(data, capacity, cursor, b0);

  [[cst::proof]] {
    add_fact_st(spec_rule(`word_value__pre:int`,
        cmc_unsigned_byte1_bridge));
    add_fact_st(spec_rule(`word_value__pre:int`,
        cmc_encoded_byte_range(`1i:int`)));
  }
  [[cst::where(`prefix`,
      `(prefix:(int)list) ++
       [tower_encode_byte (word_value__pre:int) 0i]`)]]
  [[cst::where(`model_byte`,
      `tower_encode_byte (word_value__pre:int) 1i`)]]
  cmc_write_byte(data, capacity, cursor + 1, b1);
  [[cst::proof]] {
    substitute_st(int_arith_rule(
        `((cursor__pre:int) + 1i) + 1i == cursor__pre + 2i`));
    cmc_normalize_word_prefix(
        `((prefix:(int)list) ++
           [tower_encode_byte (word_value__pre:int) 0i]) ++
         [tower_encode_byte word_value__pre 1i]`,
        `(prefix:(int)list) ++
         [tower_encode_byte (word_value__pre:int) 0i;
          tower_encode_byte word_value__pre 1i]`);
    add_fact_st(spec_rule(`word_value__pre:int`,
        cmc_unsigned_byte2_bridge));
    add_fact_st(spec_rule(`word_value__pre:int`,
        cmc_encoded_byte_range(`2i:int`)));
  }
  [[cst::where(`prefix`,
      `(prefix:(int)list) ++
       [tower_encode_byte (word_value__pre:int) 0i;
        tower_encode_byte word_value__pre 1i]`)]]
  [[cst::where(`model_byte`,
      `tower_encode_byte (word_value__pre:int) 2i`)]]
  cmc_write_byte(data, capacity, cursor + 2, b2);
  [[cst::proof]] {
    substitute_st(int_arith_rule(
        `((cursor__pre:int) + 2i) + 1i == cursor__pre + 3i`));
    cmc_normalize_word_prefix(
        `((prefix:(int)list) ++
          [tower_encode_byte (word_value__pre:int) 0i;
           tower_encode_byte word_value__pre 1i]) ++
         [tower_encode_byte word_value__pre 2i]`,
        `(prefix:(int)list) ++
         [tower_encode_byte (word_value__pre:int) 0i;
          tower_encode_byte word_value__pre 1i;
          tower_encode_byte word_value__pre 2i]`);
    add_fact_st(spec_rule(`word_value__pre:int`,
        cmc_unsigned_byte3_bridge));
    add_fact_st(spec_rule(`word_value__pre:int`,
        cmc_encoded_byte_range(`3i:int`)));
  }
  [[cst::where(`prefix`,
      `(prefix:(int)list) ++
       [tower_encode_byte (word_value__pre:int) 0i;
        tower_encode_byte word_value__pre 1i;
        tower_encode_byte word_value__pre 2i]`)]]
  [[cst::where(`model_byte`,
      `tower_encode_byte (word_value__pre:int) 3i`)]]
  cmc_write_byte(data, capacity, cursor + 3, b3);
  [[cst::proof]] {
    substitute_st(int_arith_rule(
        `((cursor__pre:int) + 3i) + 1i == cursor__pre + 4i`));
    cmc_normalize_word_prefix(
        `((prefix:(int)list) ++
          [tower_encode_byte (word_value__pre:int) 0i;
           tower_encode_byte word_value__pre 1i;
           tower_encode_byte word_value__pre 2i]) ++
         [tower_encode_byte word_value__pre 3i]`,
        `(prefix:(int)list) ++
         [tower_encode_byte (word_value__pre:int) 0i;
          tower_encode_byte word_value__pre 1i;
          tower_encode_byte word_value__pre 2i;
          tower_encode_byte word_value__pre 3i]`);
    add_fact_st(spec_rule(`word_value__pre:int`,
        cmc_unsigned_byte4_bridge));
    add_fact_st(spec_rule(`word_value__pre:int`,
        cmc_encoded_byte_range(`4i:int`)));
  }
  [[cst::where(`prefix`,
      `(prefix:(int)list) ++
       [tower_encode_byte (word_value__pre:int) 0i;
        tower_encode_byte word_value__pre 1i;
        tower_encode_byte word_value__pre 2i;
        tower_encode_byte word_value__pre 3i]`)]]
  [[cst::where(`model_byte`,
      `tower_encode_byte (word_value__pre:int) 4i`)]]
  cmc_write_byte(data, capacity, cursor + 4, b4);
  [[cst::proof]] {
    substitute_st(int_arith_rule(
        `((cursor__pre:int) + 4i) + 1i == cursor__pre + 5i`));
    cmc_normalize_word_prefix(
        `((prefix:(int)list) ++
          [tower_encode_byte (word_value__pre:int) 0i;
           tower_encode_byte word_value__pre 1i;
           tower_encode_byte word_value__pre 2i;
           tower_encode_byte word_value__pre 3i]) ++
         [tower_encode_byte word_value__pre 4i]`,
        `(prefix:(int)list) ++
         [tower_encode_byte (word_value__pre:int) 0i;
          tower_encode_byte word_value__pre 1i;
          tower_encode_byte word_value__pre 2i;
          tower_encode_byte word_value__pre 3i;
          tower_encode_byte word_value__pre 4i]`);
    add_fact_st(spec_rule(`word_value__pre:int`,
        cmc_unsigned_byte5_bridge));
    add_fact_st(spec_rule(`word_value__pre:int`,
        cmc_encoded_byte_range(`5i:int`)));
  }
  [[cst::where(`prefix`,
      `(prefix:(int)list) ++
       [tower_encode_byte (word_value__pre:int) 0i;
        tower_encode_byte word_value__pre 1i;
        tower_encode_byte word_value__pre 2i;
        tower_encode_byte word_value__pre 3i;
        tower_encode_byte word_value__pre 4i]`)]]
  [[cst::where(`model_byte`,
      `tower_encode_byte (word_value__pre:int) 5i`)]]
  cmc_write_byte(data, capacity, cursor + 5, b5);
  [[cst::proof]] {
    substitute_st(int_arith_rule(
        `((cursor__pre:int) + 5i) + 1i == cursor__pre + 6i`));
    cmc_normalize_word_prefix(
        `((prefix:(int)list) ++
          [tower_encode_byte (word_value__pre:int) 0i;
           tower_encode_byte word_value__pre 1i;
           tower_encode_byte word_value__pre 2i;
           tower_encode_byte word_value__pre 3i;
           tower_encode_byte word_value__pre 4i]) ++
         [tower_encode_byte word_value__pre 5i]`,
        `(prefix:(int)list) ++
         [tower_encode_byte (word_value__pre:int) 0i;
          tower_encode_byte word_value__pre 1i;
          tower_encode_byte word_value__pre 2i;
          tower_encode_byte word_value__pre 3i;
          tower_encode_byte word_value__pre 4i;
          tower_encode_byte word_value__pre 5i]`);
    add_fact_st(spec_rule(`word_value__pre:int`,
        cmc_unsigned_byte6_bridge));
    add_fact_st(spec_rule(`word_value__pre:int`,
        cmc_encoded_byte_range(`6i:int`)));
  }
  [[cst::where(`prefix`,
      `(prefix:(int)list) ++
       [tower_encode_byte (word_value__pre:int) 0i;
        tower_encode_byte word_value__pre 1i;
        tower_encode_byte word_value__pre 2i;
        tower_encode_byte word_value__pre 3i;
        tower_encode_byte word_value__pre 4i;
        tower_encode_byte word_value__pre 5i]`)]]
  [[cst::where(`model_byte`,
      `tower_encode_byte (word_value__pre:int) 6i`)]]
  cmc_write_byte(data, capacity, cursor + 6, b6);
  [[cst::proof]] {
    substitute_st(int_arith_rule(
        `((cursor__pre:int) + 6i) + 1i == cursor__pre + 7i`));
    cmc_normalize_word_prefix(
        `((prefix:(int)list) ++
          [tower_encode_byte (word_value__pre:int) 0i;
           tower_encode_byte word_value__pre 1i;
           tower_encode_byte word_value__pre 2i;
           tower_encode_byte word_value__pre 3i;
           tower_encode_byte word_value__pre 4i;
           tower_encode_byte word_value__pre 5i]) ++
         [tower_encode_byte word_value__pre 6i]`,
        `(prefix:(int)list) ++
         [tower_encode_byte (word_value__pre:int) 0i;
          tower_encode_byte word_value__pre 1i;
          tower_encode_byte word_value__pre 2i;
          tower_encode_byte word_value__pre 3i;
          tower_encode_byte word_value__pre 4i;
          tower_encode_byte word_value__pre 5i;
          tower_encode_byte word_value__pre 6i]`);
    add_fact_st(spec_rule(`word_value__pre:int`,
        cmc_unsigned_byte7_bridge));
    add_fact_st(spec_rule(`word_value__pre:int`,
        cmc_encoded_byte_range(`7i:int`)));
  }
  [[cst::where(`prefix`,
      `(prefix:(int)list) ++
       [tower_encode_byte (word_value__pre:int) 0i;
        tower_encode_byte word_value__pre 1i;
        tower_encode_byte word_value__pre 2i;
        tower_encode_byte word_value__pre 3i;
        tower_encode_byte word_value__pre 4i;
        tower_encode_byte word_value__pre 5i;
        tower_encode_byte word_value__pre 6i]`)]]
  [[cst::where(`model_byte`,
      `tower_encode_byte (word_value__pre:int) 7i`)]]
  cmc_write_byte(data, capacity, cursor + 7, b7);
  [[cst::proof]] {
    substitute_st(int_arith_rule(
        `((cursor__pre:int) + 7i) + 1i == cursor__pre + 8i`));
    cmc_normalize_word_prefix(
        `((prefix:(int)list) ++
          [tower_encode_byte (word_value__pre:int) 0i;
           tower_encode_byte word_value__pre 1i;
           tower_encode_byte word_value__pre 2i;
           tower_encode_byte word_value__pre 3i;
           tower_encode_byte word_value__pre 4i;
           tower_encode_byte word_value__pre 5i;
           tower_encode_byte word_value__pre 6i]) ++
         [tower_encode_byte word_value__pre 7i]`,
        `(prefix:(int)list) ++
         [tower_encode_byte (word_value__pre:int) 0i;
          tower_encode_byte word_value__pre 1i;
          tower_encode_byte word_value__pre 2i;
          tower_encode_byte word_value__pre 3i;
          tower_encode_byte word_value__pre 4i;
          tower_encode_byte word_value__pre 5i;
          tower_encode_byte word_value__pre 6i;
          tower_encode_byte word_value__pre 7i]`);
    thm bytes_model = inst_rule(TERM_PAIR_LIST(
        (term_pair){`word_value__pre:int`, `z:int`}),
        get_tower_word_bytes_def());
    thm prefix_model = beta_norm(ap_term_rule(
        `\xs:(int)list. (prefix:(int)list) ++ xs`,
        sym_rule(bytes_model)));
    substitute_st(prefix_model);
  }
}
