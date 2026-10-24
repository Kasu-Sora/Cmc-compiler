#include "cmc_concrete_emit_globals.h"
#include "cmc_list_selectors.h"
#include "cmc_concrete_data_ready.h"
#require "cmc_concrete_data_ready.c"
#include "userlib/proof.h"
#include "userlib/operational.h"
#require "cmc_concrete_emit_char.c"
#require "cmc_concrete_emit_zeroes.c"
#require "cmc_concrete_layout.c"
#require "cmc_codegen.c"
#require "cmc_list_selectors.c"

PROOF static thm cmc_rep_bool_zero_iff(void) {
  gnode root = gnode_new_with_ccl(
      `!(b:bool). (cm_rep_bool b == 0i <=> ~b)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(leaf, `b:bool`, "Hb");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode reduced = CONV_WITH_ASMP_TAC(
        cases[i], reduce_rewrite_conv,
        THM_LIST(get_cm_rep_bool_def()));
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, refl_rule(get_true_term()));
    }
  }
  return gnode_prove(root);
}
PROOF static thm cmc_rep_bool_zero_iff_rule =
    cmc_rep_bool_zero_iff();

PROOF static thm cmc_make_rep_bool_nonzero_rule(void) {
  thm iff = spec_rule(`b:bool`, cmc_rep_bool_zero_iff_rule);
  thm body = mp_rule(mp_rule(taut_rule(
      `(cm_rep_bool (b:bool) == 0i <=> ~b) ==>
       ~(cm_rep_bool b == 0i) ==> b`), iff),
      assume_rule(`~(cm_rep_bool (b:bool) == 0i)`));
  return gen_rule(`b:bool`, disch_rule(
      `~(cm_rep_bool (b:bool) == 0i)`, body));
}
PROOF static thm cmc_rep_bool_nonzero_rule =
    cmc_make_rep_bool_nonzero_rule();

PROOF static thm cmc_make_rep_bool_zero_rule(void) {
  thm iff = spec_rule(`b:bool`, cmc_rep_bool_zero_iff_rule);
  thm body = eq_mp_rule(iff,
      assume_rule(`cm_rep_bool (b:bool) == 0i`));
  return gen_rule(`b:bool`, disch_rule(
      `cm_rep_bool (b:bool) == 0i`, body));
}
PROOF static thm cmc_rep_bool_zero_rule =
    cmc_make_rep_bool_zero_rule();

PROOF static thm cmc_positive_nonchar_leaf(void) {
  gnode root = gnode_new_with_ccl(
      `!(code:int). ~(code == 1i) ==>
         0i < cm_rep_leaf_size code ==>
         cm_rep_leaf_size code == 8i`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list pointer_cases = BOOL_CASES_TAC(
      leaf, `1024i <= (code:int)`, "Hpointer");
  CONV_WITH_ASMP_TAC(pointer_cases[0], reduce_rewrite_conv,
      THM_LIST(get_cm_rep_leaf_size_def()));
  gnode_list zero_cases = BOOL_CASES_TAC(
      pointer_cases[1], `(code:int) == 0i`, "Hzero");
  CONV_WITH_ASMP_TAC(zero_cases[0], reduce_rewrite_conv,
      THM_LIST(get_cm_rep_leaf_size_def()));
  gnode impossible = CONV_WITH_ASMP_TAC(
      zero_cases[1], reduce_rewrite_conv,
      THM_LIST(get_cm_rep_leaf_size_def()));
  if (IS_NULL(impossible->solved)) {
    thm contradiction = mp_rule(int_arith_rule(
        `0i < cm_rep_leaf_size (code:int) ==>
         cm_rep_leaf_size code == 0i ==> F`),
        assume_rule(`0i < cm_rep_leaf_size (code:int)`));
    contradiction = mp_rule(contradiction, by_rewrite(
        `cm_rep_leaf_size (code:int) == 0i`, THM_LIST(
          get_cm_rep_leaf_size_def(),
          eqf_intro_rule(assume_rule(`~(1024i <= (code:int))`)),
          eqf_intro_rule(assume_rule(`~((code:int) == 0i)`)),
          eqf_intro_rule(assume_rule(`~((code:int) == 1i)`)))));
    ACCEPT_TAC(impossible, false_elim_rule(
        contradiction, goal_ccl(impossible->g)));
  }
  return gnode_prove(root);
}
PROOF static thm cmc_positive_nonchar_leaf_rule =
    cmc_positive_nonchar_leaf();

PROOF static thm cmc_global_initialized_bytes(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (global:cm_global_d).
         0i <= cm_global_size structs global ==>
         cm_global_has_init global ==>
         cm_global_size structs global ==
           ilength (cm_global_init_bytes global) ==>
         cm_global_bytes structs global ==
           cm_global_init_bytes global`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm size_equal = assume_rule(
      `cm_global_size (structs:(cm_struct_d)list)
         (global:cm_global_d) ==
       ilength (cm_global_init_bytes global)`);
  thm length_bound = mp_rule(int_arith_rule(
      `cm_global_size structs global ==
         ilength (cm_global_init_bytes global) ==>
       ilength (cm_global_init_bytes global) <=
         cm_global_size structs global`), size_equal);
  thm padding_zero = mp_rule(int_arith_rule(
      `cm_global_size structs global ==
         ilength (cm_global_init_bytes global) ==>
       cm_global_size structs global -
         ilength (cm_global_init_bytes global) == 0i`), size_equal);
  thm result = by_rewrite(goal_ccl(leaf->g), THM_LIST(
      get_cm_global_bytes_def(),
      eqt_intro_rule(assume_rule(
        `0i <= cm_global_size
          (structs:(cm_struct_d)list) (global:cm_global_d)`)),
      eqt_intro_rule(assume_rule(
        `cm_global_has_init (global:cm_global_d)`)),
      eqt_intro_rule(length_bound), padding_zero,
      get_theorem_by_name("IREPLICATE_DEF"),
      get_theorem_by_name("NUM_OF_INT_OF_NUM"),
      get_theorem_by_name("REPLICATE"),
      get_theorem_by_name("APPEND_NIL")));
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF static thm cmc_global_initialized_bytes_rule =
    cmc_global_initialized_bytes();

PROOF static thm cmc_global_zero_bytes(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (global:cm_global_d).
         0i <= cm_global_size structs global ==>
         ~(cm_global_has_init global) ==>
         cm_global_bytes structs global ==
           ireplicate (cm_global_size structs global) 0i`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, THM_LIST(
      get_cm_global_bytes_def()));
  return gnode_prove(root);
}
PROOF static thm cmc_global_zero_bytes_rule =
    cmc_global_zero_bytes();

int cmc_emit_globals(struct cm_global *node,
                      unsigned char *data, int capacity, int cursor)
    [[cst::param(`structs:(cm_struct_d)list`,
                 `globals:(cm_global_d)list`, `prefix:(int)list`)]]
    [[cst::require(
      `fact(cm_rep_globals_safe globals <=> true) **
       fact(cm_data_globals_wf structs globals <=> true) **
       fact(0i <= cursor) **
       fact(cursor + cm_rep_globals_size globals <= capacity) **
       fact(capacity <= 2147483647i) **
       cm_global_list_rep node globals **
       store_uint8_array data cursor prefix **
       store_undef_uint8_array
         (data + cursor * sizeof Tuchar) (capacity - cursor)`)]]
    [[cst::ensure(
      `fact(cm_rep_globals_safe globals <=> true) **
       fact(cm_data_globals_wf structs globals <=> true) **
       cm_global_list_rep node globals **
       store_uint8_array data
         (cursor + cm_rep_globals_size globals)
         (prefix ++ cm_globals_bytes structs globals) **
       store_undef_uint8_array
         (data + (cursor + cm_rep_globals_size globals) * sizeof Tuchar)
         (capacity - (cursor + cm_rep_globals_size globals)) **
       fact((__return:int) ==
         cursor + cm_rep_globals_size globals)`)]]
{
  if (node == 0) {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(TERM_LIST(
              `node__pre:int`, `globals:(cm_global_d)list`),
              get_cm_global_null()),
            assume_rule(`node__pre == 0i`))));
      thm nil_model = assume_rule(
          `globals == ([]:(cm_global_d)list)`);
      thm list_view = apply_conversion(rewrite_conv(THM_LIST(
          nil_model, get_cm_global_list_rep_def())),
          `cm_global_list_rep (node__pre:int) globals`);
      apply_hconv_st(eq2ent(sym_rule(list_view)));
      thm destination_view = apply_conversion(rewrite_conv(THM_LIST(
          nil_model, get_cm_rep_globals_size_def(),
          get_cm_globals_bytes_def(), get_theorem_by_name("APPEND_NIL"),
          get_theorem_by_name("INT_ADD_RID"))),
          `store_uint8_array (data__pre:int)
            ((cursor__pre:int) + cm_rep_globals_size globals)
            ((prefix:(int)list) ++
              cm_globals_bytes (structs:(cm_struct_d)list) globals)`);
      apply_hconv_st(eq2ent(sym_rule(destination_view)));
      thm undefined_view = apply_conversion(rewrite_conv(THM_LIST(
          nil_model, get_cm_rep_globals_size_def(),
          get_theorem_by_name("INT_ADD_RID"))),
          `store_undef_uint8_array
            ((data__pre:int) +
              ((cursor__pre:int) + cm_rep_globals_size globals) *
                sizeof Tuchar)
            ((capacity__pre:int) -
              (cursor__pre + cm_rep_globals_size globals))`);
      apply_hconv_st(eq2ent(sym_rule(undefined_view)));
      thm cursor_view = by_rewrite(
          `(cursor__pre:int) ==
           cursor__pre + cm_rep_globals_size globals`,
          THM_LIST(nil_model, get_cm_rep_globals_size_def(),
            get_theorem_by_name("INT_ADD_RID")));
      add_fact_st(cursor_view);
    }
    return cursor;
  };

  [[cst::proof]] {
    thm opened = mp_rule(specl_rule(TERM_LIST(
        `node__pre:int`, `globals:(cm_global_d)list`),
        get_cm_global_unfold()),
        assume_rule(`~(node__pre == 0i)`));
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        rename_exists_hconv(opened, TERM_LIST(
          `global_:cm_global_d`, `rest_:(cm_global_d)list`,
          `next_:int`))));
    thm shape = assume_rule(
        `globals == (global_:cm_global_d) ::
          (rest_:(cm_global_d)list)`);

    thm safe = from_state_bool(
        `cm_rep_globals_safe (globals:(cm_global_d)list)`);
    thm opened_safe = conv_rule(rewrite_conv(THM_LIST(
        shape, get_cm_rep_globals_safe_def())), safe);
    add_fact_st(conjunct1_rule(opened_safe));
    thm safe_tail = conjunct2_rule(opened_safe);
    add_fact_st(conjunct1_rule(safe_tail));
    safe_tail = conjunct2_rule(safe_tail);
    thm sum_upper = conjunct1_rule(safe_tail);
    add_fact_st(sum_upper);
    add_fact_st(conv_rule(rewrite_conv(THM_LIST(
        get_cm_rep_globals_size_def())), sum_upper));
    add_fact_st(eqt_intro_rule(conjunct2_rule(safe_tail)));

    thm data_wf = from_state_bool(
        `cm_data_globals_wf (structs:(cm_struct_d)list)
          (globals:(cm_global_d)list)`);
    thm opened_data_wf = conv_rule(rewrite_conv(THM_LIST(
        shape, get_cm_data_globals_wf_def())), data_wf);
    thm head_wf = conjunct1_rule(opened_data_wf);
    thm tail_wf = conjunct2_rule(opened_data_wf);
    add_fact_st(eqt_intro_rule(head_wf));
    add_fact_st(eqt_intro_rule(tail_wf));

    thm opened_wf = conv_rule(rewrite_conv(THM_LIST(
        get_cm_global_wf_def(), get_cm_scalar_type_def())), head_wf);
    thm code_wf = mp_rule(taut_rule(mk_imp(concl(opened_wf),
        `cm_type_code_wf (cm_global_ty (global_:cm_global_d))`)),
        opened_wf);
    add_fact_st(eqt_intro_rule(code_wf));
    thm positive_size = mp_rule(taut_rule(mk_imp(concl(opened_wf),
        `0i < cm_global_size (structs:(cm_struct_d)list)
          (global_:cm_global_d)`)), opened_wf);
    add_fact_st(positive_size);
    thm size_bridge = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`, `global_:cm_global_d`),
        cm_rep_global_size_matches), head_wf);
    add_fact_st(size_bridge);
    add_fact_st(sym_rule(size_bridge));
    thm positive_rep_size = conv_rule(rewrite_conv(THM_LIST(
        sym_rule(size_bridge))), positive_size);
    add_fact_st(positive_rep_size);

    thm total_model = trans_rule(beta_norm(ap_term_rule(
        `cm_rep_globals_size:(cm_global_d)list->int`, shape)),
        apply_conversion(rewrite_conv(THM_LIST(
          get_cm_rep_globals_size_def())),
          `cm_rep_globals_size
            ((global_:cm_global_d) ::
             (rest_:(cm_global_d)list))`));
    add_fact_st(total_model);
    thm bytes_model = trans_rule(beta_norm(ap_term_rule(
        `cm_globals_bytes (structs:(cm_struct_d)list)`, shape)),
        apply_conversion(rewrite_conv(THM_LIST(
          get_cm_globals_bytes_def())),
          `cm_globals_bytes structs
            ((global_:cm_global_d) ::
             (rest_:(cm_global_d)list))`));
    add_fact_st(bytes_model);

    cst_set_symbolic_state(add_arith_fact_st(
        cst_get_symbolic_state(),
        "0i <= cursor__pre ==> "
        "cursor__pre + cm_rep_globals_size globals <= capacity__pre ==> "
        "cm_rep_globals_size globals == "
        "  cm_rep_global_size (global_:cm_global_d) + "
        "  cm_rep_globals_size (rest_:(cm_global_d)list) ==> "
        "0i <= cm_rep_global_size global_ ==> "
        "0i <= cm_rep_globals_size rest_ ==> "
        "cm_rep_global_size global_ + cm_rep_globals_size rest_ <= "
        "  1048560i ==> "
        "capacity__pre <= 2147483647i ==> "
        "(0i <= cm_rep_global_size global_ && "
        " cm_rep_global_size global_ <= 1048560i && "
        " cursor__pre + cm_rep_global_size global_ <= capacity__pre && "
        " 0i <= cursor__pre + cm_rep_global_size global_ && "
        " cursor__pre + cm_rep_global_size global_ + "
        "   cm_rep_globals_size rest_ <= capacity__pre && "
        " cursor__pre + cm_rep_global_size global_ <= 2147483647i)"));

    thm head_model = apply_conversion(rewrite_conv(THM_LIST(
        shape, get_theorem_by_name("HD"))),
        `HD (globals:(cm_global_d)list)`);
    thm tail_model = apply_conversion(rewrite_conv(THM_LIST(
        shape, get_theorem_by_name("TL"))),
        `TL (globals:(cm_global_d)list)`);
    thm stable_shape = conv_rule(rewrite_conv(THM_LIST(
        sym_rule(head_model), sym_rule(tail_model))), shape);
    add_fact_st(stable_shape);
    substitute_st(sym_rule(head_model));
    substitute_st(sym_rule(tail_model));
  }

  int type_code = node->ty;
  int count = node->count;
  int has_init = node->has_init;
  long long init_value = node->init;
  struct cm_global *next = node->next;

  long long size64 = cmc_code_slot_size(type_code, count);
  [[cst::proof]] {
    thm size_def = inst_rule(TERM_PAIR_LIST(
        (term_pair){`HD (globals:(cm_global_d)list)`,
                    `global:cm_global_d`}),
        get_cm_rep_global_size_def());
    thm value_model = trans_rule(assume_rule(
        `retval == cm_rep_code_slot_size
          (cm_type_encode
            (cm_global_ty (HD (globals:(cm_global_d)list))))
          (cm_global_count (HD globals))`),
        sym_rule(size_def));
    add_fact_st(value_model);
    cst_set_symbolic_state(retarget_cell64_st(
        cst_get_symbolic_state(), `size64__addr:addr`, `retval:int`,
        `cm_rep_global_size (HD (globals:(cm_global_d)list))`));
    term size_model =
        `cm_rep_global_size (HD (globals:(cm_global_d)list))`;
    thm cast = mp_rule(mp_rule(spec_rule(size_model,
        cm_nonnegative_i32_cast),
        assume_rule(`0i <= cm_rep_global_size
          (HD (globals:(cm_global_d)list))`)),
        mp_rule(int_arith_rule(
          `cm_rep_global_size (HD (globals:(cm_global_d)list)) <=
             1048560i ==>
           cm_rep_global_size (HD globals) <= 2147483647i`),
          assume_rule(`cm_rep_global_size
            (HD (globals:(cm_global_d)list)) <= 1048560i`)));
    add_fact_st(cast);
  }
  int size = (int)size64;

  if (has_init) {
    [[cst::proof]] {
      thm has = mp_rule(spec_rule(
          `cm_global_has_init (HD (globals:(cm_global_d)list))`,
          cmc_rep_bool_nonzero_rule),
          assume_rule(`~(cm_rep_bool
            (cm_global_has_init
              (HD (globals:(cm_global_d)list))) == 0i)`));
      add_fact_st(eqt_intro_rule(has));
      thm wf = from_state_bool(
          `cm_global_wf (structs:(cm_struct_d)list)
            (HD (globals:(cm_global_d)list))`);
      thm opened_wf = conv_rule(rewrite_conv(THM_LIST(
          get_cm_global_wf_def())), wf);
      thm count_zero = mp_rule(
          conjunct1_rule(conjunct2_rule(conjunct2_rule(
            conjunct2_rule(conjunct2_rule(opened_wf))))), has);
      add_fact_st(count_zero);
      thm signed_value = mp_rule(
          conjunct1_rule(conjunct2_rule(conjunct2_rule(conjunct2_rule(
            conjunct2_rule(conjunct2_rule(opened_wf)))))), has);
      add_fact_st(eqt_intro_rule(signed_value));
    }

    if (type_code == CMC_TYPE_CHAR) {
      [[cst::proof]] {
        thm code_wf = from_state_bool(
            `cm_type_code_wf
              (cm_global_ty (HD (globals:(cm_global_d)list)))`);
        thm char_iff = mp_rule(spec_rule(
            `cm_global_ty (HD (globals:(cm_global_d)list))`,
            cm_char_encode), code_wf);
        thm char_type = eq_mp_rule(char_iff, assume_rule(
            `cm_type_encode
              (cm_global_ty (HD (globals:(cm_global_d)list))) == 1i`));
        add_fact_st(char_type);
        thm size_one = eqt_elim_rule(apply_conversion(
            reduce_rewrite_conv(THM_LIST(
              get_cm_rep_global_size_def(),
              get_cm_rep_code_slot_size_def(),
              get_cm_rep_leaf_size_def(),
              assume_rule(`cm_global_count
                (HD (globals:(cm_global_d)list)) == 0i`),
              assume_rule(`cm_type_encode
                (cm_global_ty
                  (HD (globals:(cm_global_d)list))) == 1i`))),
            `cm_rep_global_size
              (HD (globals:(cm_global_d)list)) == 1i`));
        add_fact_st(size_one);
        cst_set_symbolic_state(add_arith_fact_st(
            cst_get_symbolic_state(),
            "cursor__pre + cm_rep_global_size "
            "  (HD (globals:(cm_global_d)list)) <= capacity__pre ==> "
            "cm_rep_global_size (HD globals) == 1i ==> "
            "cursor__pre + 1i <= capacity__pre"));
      }
      [[cst::where(`prefix`, `prefix:(int)list`)]]
      cmc_write_char(data, capacity, cursor, init_value);
      [[cst::proof]] {
        thm char_type = assume_rule(
            `cm_global_ty (HD (globals:(cm_global_d)list)) == CMCharTy`);
        thm size_bridge = assume_rule(
            `cm_rep_global_size (HD (globals:(cm_global_d)list)) ==
             cm_global_size (structs:(cm_struct_d)list) (HD globals)`);
        thm size_one = assume_rule(
            `cm_rep_global_size (HD (globals:(cm_global_d)list)) == 1i`);
        thm semantic_size = trans_rule(sym_rule(size_bridge), size_one);
        thm init_bytes = apply_conversion(rewrite_conv(THM_LIST(
            char_type, get_cm_global_init_bytes_def())),
            `cm_global_init_bytes (HD (globals:(cm_global_d)list))`);
        thm init_length = apply_conversion(reduce_rewrite_conv(THM_LIST(
            init_bytes, get_theorem_by_name("ILENGTH_DEF"))),
            `ilength (cm_global_init_bytes
              (HD (globals:(cm_global_d)list)))`);
        thm head_bytes = mp_rule(mp_rule(mp_rule(specl_rule(TERM_LIST(
            `structs:(cm_struct_d)list`,
            `HD (globals:(cm_global_d)list)`),
            cmc_global_initialized_bytes_rule),
            mp_rule(int_arith_rule(
              `cm_global_size structs (HD globals) == 1i ==>
               0i <= cm_global_size structs (HD globals)`), semantic_size)),
            from_state_bool(
              `cm_global_has_init (HD (globals:(cm_global_d)list))`)),
            trans_rule(semantic_size, sym_rule(init_length)));
        thm char_bytes = trans_rule(head_bytes, init_bytes);
        thm cursor_step = beta_norm(ap_term_rule(
            `\n:int. (cursor__pre:int) + n`, sym_rule(size_one)));
        substitute_st(cursor_step);
        thm prefix_step = beta_norm(ap_term_rule(
            `\xs:(int)list. (prefix:(int)list) ++ xs`,
            sym_rule(char_bytes)));
        substitute_st(prefix_step);
      }
    } else {
      [[cst::proof]] {
        thm code_wf = from_state_bool(
            `cm_type_code_wf
              (cm_global_ty (HD (globals:(cm_global_d)list)))`);
        thm char_iff = mp_rule(spec_rule(
            `cm_global_ty (HD (globals:(cm_global_d)list))`,
            cm_char_encode), code_wf);
        thm not_char = eq_mp_rule(beta_norm(ap_term_rule(
            `\b:bool. ~b`, char_iff)), assume_rule(
            `~(cm_type_encode
              (cm_global_ty (HD (globals:(cm_global_d)list))) == 1i)`));
        add_fact_st(not_char);
        thm leaf_positive = conv_rule(rewrite_conv(THM_LIST(
            get_cm_rep_global_size_def(),
            get_cm_rep_code_slot_size_def(),
            assume_rule(`cm_global_count
              (HD (globals:(cm_global_d)list)) == 0i`))),
            assume_rule(`0i < cm_rep_global_size
              (HD (globals:(cm_global_d)list))`));
        thm leaf_eight = mp_rule(mp_rule(spec_rule(
            `cm_type_encode
              (cm_global_ty (HD (globals:(cm_global_d)list)))`,
            cmc_positive_nonchar_leaf_rule),
            assume_rule(`~(cm_type_encode
              (cm_global_ty (HD (globals:(cm_global_d)list))) == 1i)`)),
            leaf_positive);
        thm size_eight = by_rewrite(
            `cm_rep_global_size (HD (globals:(cm_global_d)list)) == 8i`,
            THM_LIST(get_cm_rep_global_size_def(),
              get_cm_rep_code_slot_size_def(),
              assume_rule(`cm_global_count
                (HD (globals:(cm_global_d)list)) == 0i`), leaf_eight));
        add_fact_st(size_eight);
        cst_set_symbolic_state(add_arith_fact_st(
            cst_get_symbolic_state(),
            "cursor__pre + cm_rep_global_size "
            "  (HD (globals:(cm_global_d)list)) <= capacity__pre ==> "
            "cm_rep_global_size (HD globals) == 8i ==> "
            "cursor__pre + 8i <= capacity__pre"));
      }
      [[cst::where(`prefix`, `prefix:(int)list`)]]
      cmc_write_word(data, capacity, cursor, init_value);
      [[cst::proof]] {
        thm not_char = assume_rule(
            `~(cm_global_ty
              (HD (globals:(cm_global_d)list)) == CMCharTy)`);
        thm size_bridge = assume_rule(
            `cm_rep_global_size (HD (globals:(cm_global_d)list)) ==
             cm_global_size (structs:(cm_struct_d)list) (HD globals)`);
        thm size_eight = assume_rule(
            `cm_rep_global_size (HD (globals:(cm_global_d)list)) == 8i`);
        thm semantic_size = trans_rule(sym_rule(size_bridge), size_eight);
        thm init_bytes = apply_conversion(rewrite_conv(THM_LIST(
            eqf_intro_rule(not_char), get_cm_global_init_bytes_def())),
            `cm_global_init_bytes (HD (globals:(cm_global_d)list))`);
        thm init_length = apply_conversion(reduce_rewrite_conv(THM_LIST(
            init_bytes, get_tower_word_bytes_def(),
            get_theorem_by_name("ILENGTH_DEF"))),
            `ilength (cm_global_init_bytes
              (HD (globals:(cm_global_d)list)))`);
        thm head_bytes = mp_rule(mp_rule(mp_rule(specl_rule(TERM_LIST(
            `structs:(cm_struct_d)list`,
            `HD (globals:(cm_global_d)list)`),
            cmc_global_initialized_bytes_rule),
            mp_rule(int_arith_rule(
              `cm_global_size structs (HD globals) == 8i ==>
               0i <= cm_global_size structs (HD globals)`), semantic_size)),
            from_state_bool(
              `cm_global_has_init (HD (globals:(cm_global_d)list))`)),
            trans_rule(semantic_size, sym_rule(init_length)));
        thm word_bytes = trans_rule(head_bytes, init_bytes);
        thm cursor_step = beta_norm(ap_term_rule(
            `\n:int. (cursor__pre:int) + n`, sym_rule(size_eight)));
        substitute_st(cursor_step);
        thm prefix_step = beta_norm(ap_term_rule(
            `\xs:(int)list. (prefix:(int)list) ++ xs`,
            sym_rule(word_bytes)));
        substitute_st(prefix_step);
      }
    }
  } else {
    [[cst::proof]] {
      thm no_init = mp_rule(spec_rule(
          `cm_global_has_init (HD (globals:(cm_global_d)list))`,
          cmc_rep_bool_zero_rule),
          assume_rule(`cm_rep_bool
            (cm_global_has_init
              (HD (globals:(cm_global_d)list))) == 0i`));
      add_fact_st(eqf_intro_rule(no_init));
    }
    [[cst::where(`prefix`, `prefix:(int)list`)]]
    cmc_write_zeroes(data, capacity, cursor, size);
    [[cst::proof]] {
      thm size_bridge = assume_rule(
          `cm_rep_global_size (HD (globals:(cm_global_d)list)) ==
           cm_global_size (structs:(cm_struct_d)list) (HD globals)`);
      thm zero_bytes = mp_rule(mp_rule(specl_rule(TERM_LIST(
          `structs:(cm_struct_d)list`,
          `HD (globals:(cm_global_d)list)`),
          cmc_global_zero_bytes_rule),
          mp_rule(int_arith_rule(
            `0i < cm_global_size structs (HD globals) ==>
             0i <= cm_global_size structs (HD globals)`),
            assume_rule(`0i < cm_global_size
              (structs:(cm_struct_d)list) (HD globals)`))),
          eqf_elim_rule(assume_rule(
            `cm_global_has_init
              (HD (globals:(cm_global_d)list)) <=> false`)));
      thm zero_model = trans_rule(zero_bytes,
          beta_norm(ap_term_rule(
            `\n:int. ireplicate n 0i`, sym_rule(size_bridge))));
      thm prefix_step = beta_norm(ap_term_rule(
          `\xs:(int)list. (prefix:(int)list) ++ xs`,
          sym_rule(zero_model)));
      substitute_st(prefix_step);
    }
  }

  [[cst::where(`structs`, `structs:(cm_struct_d)list`)]]
  [[cst::where(`globals`, `TL (globals:(cm_global_d)list)`)]]
  [[cst::where(`prefix`,
      `(prefix:(int)list) ++
       cm_global_bytes (structs:(cm_struct_d)list)
         (HD (globals:(cm_global_d)list))`)]]
  int final_cursor =
      cmc_emit_globals(next, data, capacity, cursor + size);

  [[cst::proof]] {
    thm shape = assume_rule(
        `globals ==
          HD (globals:(cm_global_d)list) :: TL globals`);
    thm total_model = trans_rule(beta_norm(ap_term_rule(
        `cm_rep_globals_size:(cm_global_d)list->int`, shape)),
        apply_conversion(rewrite_conv(THM_LIST(
          get_cm_rep_globals_size_def())),
          `cm_rep_globals_size
            (HD (globals:(cm_global_d)list) :: TL globals)`));
    thm total_step = mp_rule(int_arith_rule(
        `cm_rep_globals_size globals ==
           cm_rep_global_size (HD (globals:(cm_global_d)list)) +
             cm_rep_globals_size (TL globals) ==>
         ((cursor__pre:int) + cm_rep_global_size (HD globals)) +
           cm_rep_globals_size (TL globals) ==
         cursor__pre + cm_rep_globals_size globals`), total_model);
    substitute_st(total_step);

    thm assoc = ispecl_rule(TERM_LIST(
        `prefix:(int)list`,
        `cm_global_bytes (structs:(cm_struct_d)list)
          (HD (globals:(cm_global_d)list))`,
        `cm_globals_bytes structs (TL (globals:(cm_global_d)list))`),
        get_theorem_by_name("APPEND_ASSOC"));
    thm bytes_model = trans_rule(beta_norm(ap_term_rule(
        `cm_globals_bytes (structs:(cm_struct_d)list)`, shape)),
        apply_conversion(rewrite_conv(THM_LIST(
          get_cm_globals_bytes_def())),
          `cm_globals_bytes structs
            (HD (globals:(cm_global_d)list) :: TL globals)`));
    thm prefix_model = beta_norm(ap_term_rule(
        `\xs:(int)list. (prefix:(int)list) ++ xs`,
        sym_rule(bytes_model)));
    thm list_step = trans_rule(sym_rule(assoc), prefix_model);
    substitute_st(list_step);

    thm folded = mp_rule(specl_rule(TERM_LIST(
        `node__pre:int`, `HD (globals:(cm_global_d)list)`,
        `TL (globals:(cm_global_d)list)`, `next_:int`),
        get_cm_global_fold()),
        assume_rule(`~(node__pre == 0i)`));
    apply_hconv_st(folded);
    thm list_view = beta_norm(ap_term_rule(
        `\xs:(cm_global_d)list.
           cm_global_list_rep (node__pre:int) xs`, shape));
    apply_hconv_st(eq2ent(sym_rule(list_view)));
  }
  return final_cursor;
}
