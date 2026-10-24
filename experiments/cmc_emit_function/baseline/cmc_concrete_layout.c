/* Concrete size, address, layout, and temporary-space calculations. */

#include "cmc_concrete_layout.h"


static int cm_max(int a, int b)
    [[cst::require(`emp`)]]
    [[cst::ensure(`emp ** fact((__return:int) == cm_imax a b)`)]]
{
  int result;
  if (a <= b) {
    result = b;
    [[cst::proof]] {
      thm model = mp_rule(specl_rule(
          TERM_LIST(`(a__pre:int)`, `(b__pre:int)`),
          cmc_imax_le_case()), assume_rule(`a__pre <= b__pre`));
      cst_set_symbolic_state(add_fact_st_sym(
          cst_get_symbolic_state(), sym_rule(model)));
    }
  } else {
    result = a;
    [[cst::proof]] {
      thm model = mp_rule(specl_rule(
          TERM_LIST(`(a__pre:int)`, `(b__pre:int)`),
          cmc_imax_gt_case()), assume_rule(`a__pre > b__pre`));
      cst_set_symbolic_state(add_fact_st_sym(
          cst_get_symbolic_state(), sym_rule(model)));
    }
  }
  return result;
}

int cmc_is_pointer(int ty)
    [[cst::require(`emp`)]]
    [[cst::ensure(`emp **
      fact((__return:int) == cm_rep_is_pointer_code ty)`)]]
{
  int result;
  if (ty >= 1024) {
    result = 1;
    [[cst::proof]] {
      thm model = mp_rule(spec_rule(`(ty__pre:int)`,
          cmc_pointer_code_true()),
          assume_rule(`ty__pre >= 1024i`));
      cst_set_symbolic_state(add_fact_st_sym(
          cst_get_symbolic_state(), sym_rule(model)));
    }
  } else {
    result = 0;
    [[cst::proof]] {
      thm model = mp_rule(spec_rule(`(ty__pre:int)`,
          cmc_pointer_code_false()),
          assume_rule(`ty__pre < 1024i`));
      cst_set_symbolic_state(add_fact_st_sym(
          cst_get_symbolic_state(), sym_rule(model)));
    }
  }
  return result;
}

void cmc_is_pointer_value(int ty, int *pointer)
    [[cst::require(`undef_data_at pointer Tint`)]]
    [[cst::ensure(
      `data_at pointer Tint (cm_rep_is_pointer_code (ty:int))`)]]
{
  int result = cmc_is_pointer(ty);
  [[cst::proof]] {
    substitute_fact_st(
        `retval == cm_rep_is_pointer_code (ty__pre:int)`);
  }
  *pointer = result;
}

int cmc_pointee(int ty)
    [[cst::require(
      `fact(1024i <= ty) ** fact(ty <= 2147483647i)`)]]
    [[cst::ensure(`fact((__return:int) == ty - 1024i)`)]]
{
  return ty - 1024;
}

static int cmc_leaf_size(int ty)
    [[cst::require(`emp`)]]
    [[cst::ensure(`emp ** fact((__return:int) == cm_rep_leaf_size ty)`)]]
{
  int result;
  if (ty >= 1024) {
    result = 8;
    [[cst::proof]] {
      thm model = mp_rule(spec_rule(`ty__pre:int`,
          cmc_leaf_pointer_case()),
          assume_rule(`ty__pre >= 1024i`));
      cst_set_symbolic_state(add_fact_st_sym(
          cst_get_symbolic_state(), sym_rule(model)));
    }
  } else if (ty == CMC_TYPE_INT) {
    result = 8;
    [[cst::proof]] {
      thm model = mp_rule(mp_rule(spec_rule(`ty__pre:int`,
          cmc_leaf_int_case()),
          assume_rule(`ty__pre < 1024i`)),
          assume_rule(`ty__pre == 0i`));
      cst_set_symbolic_state(add_fact_st_sym(
          cst_get_symbolic_state(), sym_rule(model)));
    }
  } else if (ty == CMC_TYPE_CHAR) {
    result = 1;
    [[cst::proof]] {
      thm model = mp_rule(mp_rule(mp_rule(spec_rule(`ty__pre:int`,
          cmc_leaf_char_case()),
          assume_rule(`ty__pre < 1024i`)),
          assume_rule(`~(ty__pre == 0i)`)),
          assume_rule(`ty__pre == 1i`));
      cst_set_symbolic_state(add_fact_st_sym(
          cst_get_symbolic_state(), sym_rule(model)));
    }
  } else {
    result = 0;
    [[cst::proof]] {
      thm model = mp_rule(mp_rule(mp_rule(spec_rule(`ty__pre:int`,
          cmc_leaf_other_case()),
          assume_rule(`ty__pre < 1024i`)),
          assume_rule(`~(ty__pre == 0i)`)),
          assume_rule(`~(ty__pre == 1i)`));
      cst_set_symbolic_state(add_fact_st_sym(
          cst_get_symbolic_state(), sym_rule(model)));
    }
  }
  return result;
}

long long cmc_code_slot_size(int code, int count)
    [[cst::require(`emp`)]]
    [[cst::ensure(`emp **
      fact((__return:int) == cm_rep_code_slot_size code count)`)]]
{
  [[cst::proof]] {
    add_data_at_range_st(`count__addr:addr`, `Tint`,
        `count__pre:int`);
  }
  int leaf = cmc_leaf_size(code);
  long long result;
  if (count == 0) {
    result = leaf;
    [[cst::proof]] {
      thm branch_model = mp_rule(specl_rule(
          TERM_LIST(`code__pre:int`, `count__pre:int`),
          cmc_code_slot_zero_case()),
          assume_rule(`count__pre == 0i`));
      thm result_model = trans_rule(
          assume_rule(
            `retval == cm_rep_leaf_size (code__pre:int)`),
          sym_rule(branch_model));
      cst_set_symbolic_state(add_fact_st_sym(
          cst_get_symbolic_state(), result_model));
    }
  } else {
    [[cst::proof]] {
      thm leaf_cases = conv_rule(rewrite_conv(THM_LIST(
          sym_rule(assume_rule(
            `retval == cm_rep_leaf_size (code__pre:int)`)))),
          spec_rule(`code__pre:int`, cmc_leaf_cases()));
      thm count_lo = assume_rule(
          `--2147483648i <= (count__pre:int)`);
      thm count_hi = assume_rule(
          `(count__pre:int) <= 2147483647i`);
      thm zero_core = int_arith_rule(
          `--9223372036854775808i <=
             (count__pre:int) * 0i &&
           count__pre * 0i <= 9223372036854775807i`);
      thm zero_bound = conv_rule(rewrite_conv(THM_LIST(
          sym_rule(assume_rule(`(retval:int) == 0i`)))), zero_core);
      thm one_core = mp_rule(mp_rule(int_arith_rule(
          `--2147483648i <= (count__pre:int) ==>
           count__pre <= 2147483647i ==>
           --9223372036854775808i <= count__pre * 1i &&
           count__pre * 1i <= 9223372036854775807i`),
          count_lo), count_hi);
      thm one_bound = conv_rule(rewrite_conv(THM_LIST(
          sym_rule(assume_rule(`(retval:int) == 1i`)))), one_core);
      thm eight_core = mp_rule(mp_rule(int_arith_rule(
          `--2147483648i <= (count__pre:int) ==>
           count__pre <= 2147483647i ==>
           --9223372036854775808i <= count__pre * 8i &&
           count__pre * 8i <= 9223372036854775807i`),
          count_lo), count_hi);
      thm eight_bound = conv_rule(rewrite_conv(THM_LIST(
          sym_rule(assume_rule(`(retval:int) == 8i`)))), eight_core);
      thm product_bound = disj_cases_rule(leaf_cases, zero_bound,
          disj_cases_rule(assume_rule(
              `(retval:int) == 1i || retval == 8i`),
            one_bound, eight_bound));
      cst_set_symbolic_state(add_fact_st_sym(
          cst_get_symbolic_state(), conjunct1_rule(product_bound)));
      cst_set_symbolic_state(add_fact_st_sym(
          cst_get_symbolic_state(), conjunct2_rule(product_bound)));
    }
    result = (long long)count * leaf;
    [[cst::proof]] {
      thm branch_model = mp_rule(specl_rule(
          TERM_LIST(`code__pre:int`, `count__pre:int`),
          cmc_code_slot_nonzero_case()),
          assume_rule(`~(count__pre == 0i)`));
      thm result_model = by_rewrite(
          `count__pre * (retval:int) ==
             cm_rep_code_slot_size code__pre count__pre`,
          THM_LIST(assume_rule(
              `retval == cm_rep_leaf_size (code__pre:int)`),
            branch_model));
      cst_set_symbolic_state(add_fact_st_sym(
          cst_get_symbolic_state(), result_model));
    }
  }
  return result;
}

static long long cmc_members_size(struct cm_member *member)
    [[cst::param(`members:(cm_slot_d)list`)]]
    [[cst::require(`fact(cm_rep_members_safe members <=> true) **
      cm_member_list_rep member members`)]]
    [[cst::ensure(`fact(cm_rep_members_safe members <=> true) **
      cm_member_list_rep member members **
      fact((__return:int) == cm_rep_members_size members)`)]]
{
  long long total;
  if (member == 0) {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`member__pre:addr`, `members:(cm_slot_d)list`),
              get_cm_member_null()),
            assume_rule(`member__pre == 0i`))));
      thm model = by_rewrite(
          `cm_rep_members_size (members:(cm_slot_d)list) == 0i`,
          THM_LIST(assume_rule(
              `members == ([]:(cm_slot_d)list)`),
            get_cm_rep_members_size_def()));
      cst_set_symbolic_state(add_fact_st_sym(
          cst_get_symbolic_state(), sym_rule(model)));
      thm nil_view = spec_rule(`member__pre:addr`,
          conjunct1_rule(get_cm_member_list_rep_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(nil_view))));
    }
    total = 0;
  } else {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`member__pre:addr`, `members:(cm_slot_d)list`),
              get_cm_member_unfold()),
            assume_rule(`~(member__pre == 0i)`))));
    }
    [[cst::proof]] {
      thm safe = from_state_bool(
          `cm_rep_members_safe (members:(cm_slot_d)list)`);
      thm opened_safe = conv_rule(rewrite_conv(THM_LIST(
          assume_rule(
            `members == (member_:cm_slot_d) ::
              (rest_:(cm_slot_d)list)`),
          get_cm_rep_members_safe_def(),
          get_cm_rep_members_size_def())), safe);
      thm head_nonnegative = conjunct1_rule(opened_safe);
      thm tail_nonnegative =
          conjunct1_rule(conjunct2_rule(opened_safe));
      thm sum_upper = conjunct1_rule(
          conjunct2_rule(conjunct2_rule(opened_safe)));
      thm tail_safe = conjunct2_rule(
          conjunct2_rule(conjunct2_rule(opened_safe)));
      add_fact_st(head_nonnegative);
      add_fact_st(tail_nonnegative);
      add_fact_st(sum_upper);
      add_fact_st(eqt_intro_rule(tail_safe));
      add_fact_st(mp_rule(mp_rule(int_arith_rule(
          `0i <= cm_rep_member_size (member_:cm_slot_d) ==>
           0i <= cm_rep_members_size (rest_:(cm_slot_d)list) ==>
           0i <= cm_rep_member_size member_ +
             cm_rep_members_size rest_`),
          head_nonnegative), tail_nonnegative));
    }
    long long size = cmc_code_slot_size(member->ty, member->count);
    [[cst::proof]] {
      thm member_model = inst_rule(TERM_PAIR_LIST(
          (term_pair){`member_:cm_slot_d`, `member:cm_slot_d`}),
          get_cm_rep_member_size_def());
      thm value_model = trans_rule(
          assume_rule(
            `retval == cm_rep_code_slot_size
              (cm_type_encode (cm_slot_ty (member_:cm_slot_d)))
              (cm_slot_count member_)`),
          sym_rule(member_model));
      cst_set_symbolic_state(add_fact_st_sym(
          cst_get_symbolic_state(), value_model));
      cst_set_symbolic_state(retarget_cell64_st(
          cst_get_symbolic_state(), `size__addr:addr`, `retval:int`,
          `cm_rep_member_size (member_:cm_slot_d)`));
    }
    struct cm_member *next = member->next;
    long long rest_size = cmc_members_size(next);
    [[cst::proof]] {
      cst_set_symbolic_state(retarget_cell64_st(
          cst_get_symbolic_state(), `rest_size__addr:addr`,
          `retval_1:int`, `cm_rep_members_size rest_`));
    }
    total = size + rest_size;
    [[cst::proof]] {
      thm total_model = by_rewrite(
          `cm_rep_member_size (member_:cm_slot_d) +
             cm_rep_members_size (rest_:(cm_slot_d)list) ==
           cm_rep_members_size (members:(cm_slot_d)list)`,
          THM_LIST(assume_rule(
              `members == (member_:cm_slot_d) ::
                (rest_:(cm_slot_d)list)`),
            get_cm_rep_members_size_def()));
      cst_set_symbolic_state(add_fact_st_sym(
          cst_get_symbolic_state(), total_model));
      cst_set_symbolic_state(retarget_cell64_st(
          cst_get_symbolic_state(), `total__addr:addr`,
          `cm_rep_member_size (member_:cm_slot_d) +
            cm_rep_members_size (rest_:(cm_slot_d)list)`,
          `cm_rep_members_size (members:(cm_slot_d)list)`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(TERM_LIST(`member__pre:addr`,
              `member_:cm_slot_d`, `rest_:(cm_slot_d)list`,
              `zn_:int`), get_cm_member_fold()),
            assume_rule(`~(member__pre == 0i)`))));
    }
  }
  return total;
}

static long long cmc_struct_size_at(struct cm_struct *item, int sid)
    [[cst::param(`structs:(cm_struct_d)list`)]]
    [[cst::require(`fact(0i <= sid) **
      fact(cm_rep_structs_safe structs <=> true) **
      cm_struct_list_rep item structs`)]]
    [[cst::ensure(`fact(0i <= sid) **
      fact(cm_rep_structs_safe structs <=> true) **
      cm_struct_list_rep item structs **
      fact((__return:int) == cm_rep_struct_size structs sid)`)]]
{
  long long total;
  if (item == 0) {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`item__pre:addr`, `structs:(cm_struct_d)list`),
              get_cm_struct_null()),
            assume_rule(`item__pre == 0i`))));
      thm model = by_rewrite(
          `cm_rep_struct_size (structs:(cm_struct_d)list)
             (sid__pre:int) == 0i`,
          THM_LIST(assume_rule(
              `structs == ([]:(cm_struct_d)list)`),
            get_cm_rep_struct_size_def()));
      cst_set_symbolic_state(add_fact_st_sym(
          cst_get_symbolic_state(), sym_rule(model)));
      thm nil_view = spec_rule(`item__pre:addr`,
          conjunct1_rule(get_cm_struct_list_rep_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(nil_view))));
    }
    total = 0;
  } else {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`item__pre:addr`, `structs:(cm_struct_d)list`),
              get_cm_struct_unfold()),
            assume_rule(`~(item__pre == 0i)`))));
      thm safe = from_state_bool(
          `cm_rep_structs_safe (structs:(cm_struct_d)list)`);
      thm opened_safe = conv_rule(rewrite_conv(THM_LIST(
          assume_rule(
            `structs == (strct_:cm_struct_d) ::
              (rest_:(cm_struct_d)list)`),
          get_cm_rep_structs_safe_def())), safe);
      add_fact_st(eqt_intro_rule(conjunct1_rule(opened_safe)));
      add_fact_st(eqt_intro_rule(conjunct2_rule(opened_safe)));
    }
    if (sid == 0) {
      total = cmc_members_size(item->members);
      [[cst::proof]] {
        thm model = by_rewrite(
            `cm_rep_members_size
                (cm_struct_members (strct_:cm_struct_d)) ==
             cm_rep_struct_size
               (structs:(cm_struct_d)list) (sid__pre:int)`,
            THM_LIST(assume_rule(`sid__pre == 0i`),
              assume_rule(
                `structs == (strct_:cm_struct_d) ::
                  (rest_:(cm_struct_d)list)`),
              get_cm_rep_struct_size_def()));
        add_fact_st(trans_rule(assume_rule(
            `retval ==
              cm_rep_members_size
                (cm_struct_members (strct_:cm_struct_d))`), model));
        cst_set_symbolic_state(retarget_cell64_st(
            cst_get_symbolic_state(), `total__addr:addr`, `retval:int`,
            `cm_rep_struct_size
              (structs:(cm_struct_d)list) (sid__pre:int)`));
        cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
            mp_rule(specl_rule(TERM_LIST(`item__pre:addr`,
                `strct_:cm_struct_d`, `rest_:(cm_struct_d)list`,
                `zm_:int`, `zn_:int`), get_cm_struct_fold()),
              assume_rule(`~(item__pre == 0i)`))));
      }
    } else {
      struct cm_struct *next = item->next;
      [[cst::proof]] {
        add_data_at_range_st(`sid__addr:addr`, `Tint`,
            `sid__pre:int`);
      }
      total = cmc_struct_size_at(next, sid - 1);
      [[cst::proof]] {
        thm model = by_rewrite(
            `cm_rep_struct_size (rest_:(cm_struct_d)list)
                ((sid__pre:int) - 1i) ==
             cm_rep_struct_size
               (structs:(cm_struct_d)list) sid__pre`,
            THM_LIST(assume_rule(`~(sid__pre == 0i)`),
              assume_rule(
                `structs == (strct_:cm_struct_d) ::
                  (rest_:(cm_struct_d)list)`),
              get_cm_rep_struct_size_def()));
        add_fact_st(trans_rule(assume_rule(
            `retval == cm_rep_struct_size
              (rest_:(cm_struct_d)list) ((sid__pre:int) - 1i)`),
            model));
        cst_set_symbolic_state(retarget_cell64_st(
            cst_get_symbolic_state(), `total__addr:addr`, `retval:int`,
            `cm_rep_struct_size
              (structs:(cm_struct_d)list) (sid__pre:int)`));
        cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
            mp_rule(specl_rule(TERM_LIST(`item__pre:addr`,
                `strct_:cm_struct_d`, `rest_:(cm_struct_d)list`,
                `zm_:int`, `zn_:int`), get_cm_struct_fold()),
              assume_rule(`~(item__pre == 0i)`))));
      }
    }
  }
  return total;
}

static int cmc_nonzero(int n)
    [[cst::require(`emp`)]]
    [[cst::ensure(`fact((__return:int) == cm_rep_nonzero n)`)]]
{
  int result;
  if (n == 0) {
    result = 0;
    [[cst::proof]] {
      add_fact_st(sym_rule(by_rewrite(
          `cm_rep_nonzero (n__pre:int) == 0i`,
          THM_LIST(assume_rule(`n__pre == 0i`),
            get_cm_rep_nonzero_def()))));
    }
  } else {
    result = 1;
    [[cst::proof]] {
      add_fact_st(sym_rule(by_rewrite(
          `cm_rep_nonzero (n__pre:int) == 1i`,
          THM_LIST(assume_rule(`~(n__pre == 0i)`),
            get_cm_rep_nonzero_def()))));
    }
  }
  return result;
}
static int cmc_global_array_at(struct cm_global *item, int index)
    [[cst::param(`globals:(cm_global_d)list`)]]
    [[cst::require(`fact(0i <= index) **
      cm_global_list_rep item globals`)]]
    [[cst::ensure(`fact(0i <= index) **
      cm_global_list_rep item globals **
      fact((__return:int) == cm_rep_global_array globals index)`)]]
{
  int result;
  if (item == 0) {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`item__pre:addr`, `globals:(cm_global_d)list`),
              get_cm_global_null()),
            assume_rule(`item__pre == 0i`))));
      thm model = by_rewrite(
          `cm_rep_global_array (globals:(cm_global_d)list)
             (index__pre:int) == 0i`,
          THM_LIST(assume_rule(
              `globals == ([]:(cm_global_d)list)`),
            get_cm_rep_global_array_def()));
      add_fact_st(sym_rule(model));
      thm nil_view = spec_rule(`item__pre:addr`,
          conjunct1_rule(get_cm_global_list_rep_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(nil_view))));
    }
    result = 0;
  } else {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`item__pre:addr`, `globals:(cm_global_d)list`),
              get_cm_global_unfold()),
            assume_rule(`~(item__pre == 0i)`))));
    }
    if (index == 0) {
      result = cmc_nonzero(item->count);
      [[cst::proof]] {
        thm model = by_rewrite(
            `cm_rep_nonzero
                (cm_global_count (global_:cm_global_d)) ==
             cm_rep_global_array
               (globals:(cm_global_d)list) (index__pre:int)`,
            THM_LIST(assume_rule(`index__pre == 0i`),
              assume_rule(
                `globals == (global_:cm_global_d) ::
                  (rest_:(cm_global_d)list)`),
              get_cm_rep_nonzero_def(),
              get_cm_rep_global_array_def()));
        add_fact_st(trans_rule(assume_rule(
            `retval ==
              cm_rep_nonzero
                (cm_global_count (global_:cm_global_d))`), model));
        cst_set_symbolic_state(retarget_cell_st(
            cst_get_symbolic_state(), `result__addr:addr`, `retval:int`,
            `cm_rep_global_array
              (globals:(cm_global_d)list) (index__pre:int)`));
        cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
            mp_rule(specl_rule(TERM_LIST(`item__pre:addr`,
                `global_:cm_global_d`, `rest_:(cm_global_d)list`,
                `zn_:int`), get_cm_global_fold()),
              assume_rule(`~(item__pre == 0i)`))));
      }
    } else {
      struct cm_global *next = item->next;
      [[cst::proof]] {
        add_data_at_range_st(`index__addr:addr`, `Tint`,
            `index__pre:int`);
      }
      result = cmc_global_array_at(next, index - 1);
      [[cst::proof]] {
        thm model = by_rewrite(
            `cm_rep_global_array (rest_:(cm_global_d)list)
                ((index__pre:int) - 1i) ==
             cm_rep_global_array
               (globals:(cm_global_d)list) index__pre`,
            THM_LIST(assume_rule(`~(index__pre == 0i)`),
              assume_rule(
                `globals == (global_:cm_global_d) ::
                  (rest_:(cm_global_d)list)`),
              get_cm_rep_global_array_def()));
        add_fact_st(trans_rule(assume_rule(
            `retval == cm_rep_global_array
              (rest_:(cm_global_d)list) ((index__pre:int) - 1i)`),
            model));
        cst_set_symbolic_state(retarget_cell_st(
            cst_get_symbolic_state(), `result__addr:addr`, `retval:int`,
            `cm_rep_global_array
              (globals:(cm_global_d)list) (index__pre:int)`));
        cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
            mp_rule(specl_rule(TERM_LIST(`item__pre:addr`,
                `global_:cm_global_d`, `rest_:(cm_global_d)list`,
                `zn_:int`), get_cm_global_fold()),
              assume_rule(`~(item__pre == 0i)`))));
      }
    }
  }
  return result;
}


static int cmc_slot_array_at(struct cm_slot *item, int index)
    [[cst::param(`slots:(cm_slot_d)list`)]]
    [[cst::require(`fact(0i <= index) **
      cm_slot_list_rep item slots`)]]
    [[cst::ensure(`fact(0i <= index) **
      cm_slot_list_rep item slots **
      fact((__return:int) == cm_rep_member_array slots index)`)]]
{
  int result;
  if (item == 0) {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`item__pre:addr`, `slots:(cm_slot_d)list`),
              get_cm_slot_null()),
            assume_rule(`item__pre == 0i`))));
      thm model = by_rewrite(
          `cm_rep_member_array (slots:(cm_slot_d)list)
             (index__pre:int) == 0i`,
          THM_LIST(assume_rule(
              `slots == ([]:(cm_slot_d)list)`),
            get_cm_rep_member_array_def()));
      add_fact_st(sym_rule(model));
      thm nil_view = spec_rule(`item__pre:addr`,
          conjunct1_rule(get_cm_slot_list_rep_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(nil_view))));
    }
    result = 0;
  } else {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`item__pre:addr`, `slots:(cm_slot_d)list`),
              get_cm_slot_unfold()),
            assume_rule(`~(item__pre == 0i)`))));
    }
    if (index == 0) {
      result = cmc_nonzero(item->count);
      [[cst::proof]] {
        thm model = by_rewrite(
            `cm_rep_nonzero (cm_slot_count (slot_:cm_slot_d)) ==
             cm_rep_member_array
               (slots:(cm_slot_d)list) (index__pre:int)`,
            THM_LIST(assume_rule(`index__pre == 0i`),
              assume_rule(
                `slots == (slot_:cm_slot_d) ::
                  (rest_:(cm_slot_d)list)`),
              get_cm_rep_nonzero_def(),
              get_cm_rep_member_array_def()));
        add_fact_st(trans_rule(assume_rule(
            `retval == cm_rep_nonzero
              (cm_slot_count (slot_:cm_slot_d))`), model));
        cst_set_symbolic_state(retarget_cell_st(
            cst_get_symbolic_state(), `result__addr:addr`, `retval:int`,
            `cm_rep_member_array
              (slots:(cm_slot_d)list) (index__pre:int)`));
        cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
            mp_rule(specl_rule(TERM_LIST(`item__pre:addr`,
                `slot_:cm_slot_d`, `rest_:(cm_slot_d)list`,
                `zn_:int`), get_cm_slot_fold()),
              assume_rule(`~(item__pre == 0i)`))));
      }
    } else {
      struct cm_slot *next = item->next;
      [[cst::proof]] {
        add_data_at_range_st(`index__addr:addr`, `Tint`,
            `index__pre:int`);
      }
      result = cmc_slot_array_at(next, index - 1);
      [[cst::proof]] {
        thm model = by_rewrite(
            `cm_rep_member_array (rest_:(cm_slot_d)list)
                ((index__pre:int) - 1i) ==
             cm_rep_member_array
               (slots:(cm_slot_d)list) index__pre`,
            THM_LIST(assume_rule(`~(index__pre == 0i)`),
              assume_rule(
                `slots == (slot_:cm_slot_d) ::
                  (rest_:(cm_slot_d)list)`),
              get_cm_rep_member_array_def()));
        add_fact_st(trans_rule(assume_rule(
            `retval == cm_rep_member_array
              (rest_:(cm_slot_d)list) ((index__pre:int) - 1i)`),
            model));
        cst_set_symbolic_state(retarget_cell_st(
            cst_get_symbolic_state(), `result__addr:addr`, `retval:int`,
            `cm_rep_member_array
              (slots:(cm_slot_d)list) (index__pre:int)`));
        cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
            mp_rule(specl_rule(TERM_LIST(`item__pre:addr`,
                `slot_:cm_slot_d`, `rest_:(cm_slot_d)list`,
                `zn_:int`), get_cm_slot_fold()),
              assume_rule(`~(item__pre == 0i)`))));
      }
    }
  }
  return result;
}

int cmc_slot_type_at(struct cm_slot *item, int index)
    [[cst::param(`slots:(cm_slot_d)list`)]]
    [[cst::require(`fact(0i <= index) **
      cm_slot_list_rep item slots`)]]
    [[cst::ensure(`fact(0i <= index) **
      cm_slot_list_rep item slots **
      fact((__return:int) == cm_rep_slot_type slots index)`)]]
{
  int result;
  if (item == 0) {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`item__pre:addr`, `slots:(cm_slot_d)list`),
              get_cm_slot_null()),
            assume_rule(`item__pre == 0i`))));
      thm model = by_rewrite(
          `cm_rep_slot_type (slots:(cm_slot_d)list)
             (index__pre:int) == 0i`,
          THM_LIST(assume_rule(
              `slots == ([]:(cm_slot_d)list)`),
            get_cm_rep_slot_type_def()));
      add_fact_st(sym_rule(model));
      thm nil_view = spec_rule(`item__pre:addr`,
          conjunct1_rule(get_cm_slot_list_rep_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(nil_view))));
    }
    result = 0;
  } else {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`item__pre:addr`, `slots:(cm_slot_d)list`),
              get_cm_slot_unfold()),
            assume_rule(`~(item__pre == 0i)`))));
    }
    if (index == 0) {
      result = item->ty;
      [[cst::proof]] {
        thm model = by_rewrite(
            `cm_type_encode (cm_slot_ty (slot_:cm_slot_d)) ==
             cm_rep_slot_type
               (slots:(cm_slot_d)list) (index__pre:int)`,
            THM_LIST(assume_rule(`index__pre == 0i`),
              assume_rule(
                `slots == (slot_:cm_slot_d) ::
                  (rest_:(cm_slot_d)list)`),
              get_cm_rep_slot_type_def()));
        add_fact_st(model);
        cst_set_symbolic_state(retarget_cell_st(
            cst_get_symbolic_state(), `result__addr:addr`,
            `cm_type_encode (cm_slot_ty (slot_:cm_slot_d))`,
            `cm_rep_slot_type
              (slots:(cm_slot_d)list) (index__pre:int)`));
        cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
            mp_rule(specl_rule(TERM_LIST(`item__pre:addr`,
                `slot_:cm_slot_d`, `rest_:(cm_slot_d)list`,
                `zn_:int`), get_cm_slot_fold()),
              assume_rule(`~(item__pre == 0i)`))));
      }
    } else {
      struct cm_slot *next = item->next;
      [[cst::proof]] {
        add_data_at_range_st(`index__addr:addr`, `Tint`,
            `index__pre:int`);
      }
      result = cmc_slot_type_at(next, index - 1);
      [[cst::proof]] {
        thm model = by_rewrite(
            `cm_rep_slot_type (rest_:(cm_slot_d)list)
                ((index__pre:int) - 1i) ==
             cm_rep_slot_type
               (slots:(cm_slot_d)list) index__pre`,
            THM_LIST(assume_rule(`~(index__pre == 0i)`),
              assume_rule(
                `slots == (slot_:cm_slot_d) ::
                  (rest_:(cm_slot_d)list)`),
              get_cm_rep_slot_type_def()));
        add_fact_st(trans_rule(assume_rule(
            `retval == cm_rep_slot_type
              (rest_:(cm_slot_d)list) ((index__pre:int) - 1i)`),
            model));
        cst_set_symbolic_state(retarget_cell_st(
            cst_get_symbolic_state(), `result__addr:addr`, `retval:int`,
            `cm_rep_slot_type
              (slots:(cm_slot_d)list) (index__pre:int)`));
        cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
            mp_rule(specl_rule(TERM_LIST(`item__pre:addr`,
                `slot_:cm_slot_d`, `rest_:(cm_slot_d)list`,
                `zn_:int`), get_cm_slot_fold()),
              assume_rule(`~(item__pre == 0i)`))));
      }
    }
  }
  return result;
}

static int cmc_member_array_at(struct cm_member *item, int index)
    [[cst::param(`members:(cm_slot_d)list`)]]
    [[cst::require(`fact(0i <= index) **
      cm_member_list_rep item members`)]]
    [[cst::ensure(`fact(0i <= index) **
      cm_member_list_rep item members **
      fact((__return:int) == cm_rep_member_array members index)`)]]
{
  int result;
  if (item == 0) {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`item__pre:addr`, `members:(cm_slot_d)list`),
              get_cm_member_null()),
            assume_rule(`item__pre == 0i`))));
      thm model = by_rewrite(
          `cm_rep_member_array (members:(cm_slot_d)list)
             (index__pre:int) == 0i`,
          THM_LIST(assume_rule(
              `members == ([]:(cm_slot_d)list)`),
            get_cm_rep_member_array_def()));
      add_fact_st(sym_rule(model));
      thm nil_view = spec_rule(`item__pre:addr`,
          conjunct1_rule(get_cm_member_list_rep_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(nil_view))));
    }
    result = 0;
  } else {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`item__pre:addr`, `members:(cm_slot_d)list`),
              get_cm_member_unfold()),
            assume_rule(`~(item__pre == 0i)`))));
    }
    if (index == 0) {
      result = cmc_nonzero(item->count);
      [[cst::proof]] {
        thm model = by_rewrite(
            `cm_rep_nonzero (cm_slot_count (member_:cm_slot_d)) ==
             cm_rep_member_array
               (members:(cm_slot_d)list) (index__pre:int)`,
            THM_LIST(assume_rule(`index__pre == 0i`),
              assume_rule(
                `members == (member_:cm_slot_d) ::
                  (rest_:(cm_slot_d)list)`),
              get_cm_rep_nonzero_def(),
              get_cm_rep_member_array_def()));
        add_fact_st(trans_rule(assume_rule(
            `retval == cm_rep_nonzero
              (cm_slot_count (member_:cm_slot_d))`), model));
        cst_set_symbolic_state(retarget_cell_st(
            cst_get_symbolic_state(), `result__addr:addr`, `retval:int`,
            `cm_rep_member_array
              (members:(cm_slot_d)list) (index__pre:int)`));
        cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
            mp_rule(specl_rule(TERM_LIST(`item__pre:addr`,
                `member_:cm_slot_d`, `rest_:(cm_slot_d)list`,
                `zn_:int`), get_cm_member_fold()),
              assume_rule(`~(item__pre == 0i)`))));
      }
    } else {
      struct cm_member *next = item->next;
      [[cst::proof]] {
        add_data_at_range_st(`index__addr:addr`, `Tint`,
            `index__pre:int`);
      }
      result = cmc_member_array_at(next, index - 1);
      [[cst::proof]] {
        thm model = by_rewrite(
            `cm_rep_member_array (rest_:(cm_slot_d)list)
                ((index__pre:int) - 1i) ==
             cm_rep_member_array
               (members:(cm_slot_d)list) index__pre`,
            THM_LIST(assume_rule(`~(index__pre == 0i)`),
              assume_rule(
                `members == (member_:cm_slot_d) ::
                  (rest_:(cm_slot_d)list)`),
              get_cm_rep_member_array_def()));
        add_fact_st(trans_rule(assume_rule(
            `retval == cm_rep_member_array
              (rest_:(cm_slot_d)list) ((index__pre:int) - 1i)`),
            model));
        cst_set_symbolic_state(retarget_cell_st(
            cst_get_symbolic_state(), `result__addr:addr`, `retval:int`,
            `cm_rep_member_array
              (members:(cm_slot_d)list) (index__pre:int)`));
        cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
            mp_rule(specl_rule(TERM_LIST(`item__pre:addr`,
                `member_:cm_slot_d`, `rest_:(cm_slot_d)list`,
                `zn_:int`), get_cm_member_fold()),
              assume_rule(`~(item__pre == 0i)`))));
      }
    }
  }
  return result;
}




long long cmc_type_size_at(struct cm_struct *items, int ty)
    [[cst::param(`structs:(cm_struct_d)list`)]]
    [[cst::require(`fact(0i <= ty) **
      fact(cm_rep_structs_safe structs <=> true) **
      cm_struct_list_rep items structs`)]]
    [[cst::ensure(`fact(0i <= ty) **
      fact(cm_rep_structs_safe structs <=> true) **
      cm_struct_list_rep items structs **
      fact((__return:int) == cm_rep_type_size structs ty)`)]]
{
  long long result;
  if (ty >= 1024) {
    result = 8;
    [[cst::proof]] {
      thm ge = mp_rule(int_arith_rule(
          `(ty__pre:int) >= 1024i ==> 1024i <= ty__pre`),
          assume_rule(`ty__pre >= 1024i`));
      add_fact_st(sym_rule(by_rewrite(
          `cm_rep_type_size (structs:(cm_struct_d)list)
             (ty__pre:int) == 8i`,
          THM_LIST(ge, get_cm_rep_type_size_def()))));
    }
  } else if (ty == CMC_TYPE_INT) {
    result = 8;
    [[cst::proof]] {
      thm not_ge = mp_rule(int_arith_rule(
          `(ty__pre:int) < 1024i ==> ~(1024i <= ty__pre)`),
          assume_rule(`ty__pre < 1024i`));
      add_fact_st(sym_rule(by_rewrite(
          `cm_rep_type_size (structs:(cm_struct_d)list)
             (ty__pre:int) == 8i`,
          THM_LIST(not_ge, assume_rule(`ty__pre == 0i`),
            get_cm_rep_type_size_def()))));
    }
  } else if (ty == CMC_TYPE_CHAR) {
    result = 1;
    [[cst::proof]] {
      thm not_ge = mp_rule(int_arith_rule(
          `(ty__pre:int) < 1024i ==> ~(1024i <= ty__pre)`),
          assume_rule(`ty__pre < 1024i`));
      add_fact_st(sym_rule(by_rewrite(
          `cm_rep_type_size (structs:(cm_struct_d)list)
             (ty__pre:int) == 1i`,
          THM_LIST(not_ge, assume_rule(`~(ty__pre == 0i)`),
            assume_rule(`ty__pre == 1i`),
            get_cm_rep_type_size_def()))));
    }
  } else {
    [[cst::proof]] {
      add_data_at_range_st(`ty__addr:addr`, `Tint`, `ty__pre:int`);
    }
    result = cmc_struct_size_at(items, ty - 2);
    [[cst::proof]] {
      thm not_ge = mp_rule(int_arith_rule(
          `(ty__pre:int) < 1024i ==> ~(1024i <= ty__pre)`),
          assume_rule(`ty__pre < 1024i`));
      thm model = by_rewrite(
          `cm_rep_struct_size (structs:(cm_struct_d)list)
              ((ty__pre:int) - 2i) ==
           cm_rep_type_size structs ty__pre`,
          THM_LIST(not_ge, assume_rule(`~(ty__pre == 0i)`),
            assume_rule(`~(ty__pre == 1i)`),
            get_cm_rep_type_size_def()));
      add_fact_st(trans_rule(assume_rule(
          `retval == cm_rep_struct_size
            (structs:(cm_struct_d)list) ((ty__pre:int) - 2i)`),
          model));
      cst_set_symbolic_state(retarget_cell64_st(
          cst_get_symbolic_state(), `result__addr:addr`, `retval:int`,
          `cm_rep_type_size
            (structs:(cm_struct_d)list) (ty__pre:int)`));
    }
  }
  return result;
}

static long long cmc_slots_size(struct cm_slot *slot)
    [[cst::param(`slots:(cm_slot_d)list`)]]
    [[cst::require(`fact(cm_rep_members_safe slots <=> true) **
      cm_slot_list_rep slot slots`)]]
    [[cst::ensure(`fact(cm_rep_members_safe slots <=> true) **
      cm_slot_list_rep slot slots **
      fact((__return:int) == cm_rep_members_size slots) **
      fact(0i <= cm_rep_members_size slots) **
      fact(cm_rep_members_size slots <= 1048576i)`)]]
{
  long long total;
  if (slot == 0) {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`slot__pre:addr`, `slots:(cm_slot_d)list`),
              get_cm_slot_null()),
            assume_rule(`slot__pre == 0i`))));
      thm model = by_rewrite(
          `cm_rep_members_size (slots:(cm_slot_d)list) == 0i`,
          THM_LIST(assume_rule(
              `slots == ([]:(cm_slot_d)list)`),
            get_cm_rep_members_size_def()));
      add_fact_st(sym_rule(model));
      thm nil_view = spec_rule(`slot__pre:addr`,
          conjunct1_rule(get_cm_slot_list_rep_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(nil_view))));
    }
    total = 0;
  } else {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`slot__pre:addr`, `slots:(cm_slot_d)list`),
              get_cm_slot_unfold()),
            assume_rule(`~(slot__pre == 0i)`))));
      thm safe = from_state_bool(
          `cm_rep_members_safe (slots:(cm_slot_d)list)`);
      thm opened_safe = conv_rule(rewrite_conv(THM_LIST(
          assume_rule(
            `slots == (slot_:cm_slot_d) ::
              (rest_:(cm_slot_d)list)`),
          get_cm_rep_members_safe_def(),
          get_cm_rep_members_size_def())), safe);
      thm head_nonnegative = conjunct1_rule(opened_safe);
      thm tail_nonnegative =
          conjunct1_rule(conjunct2_rule(opened_safe));
      thm sum_upper = conjunct1_rule(
          conjunct2_rule(conjunct2_rule(opened_safe)));
      thm tail_safe = conjunct2_rule(
          conjunct2_rule(conjunct2_rule(opened_safe)));
      add_fact_st(head_nonnegative);
      add_fact_st(tail_nonnegative);
      add_fact_st(sum_upper);
      add_fact_st(eqt_intro_rule(tail_safe));
      add_fact_st(mp_rule(mp_rule(int_arith_rule(
          `0i <= cm_rep_member_size (slot_:cm_slot_d) ==>
           0i <= cm_rep_members_size (rest_:(cm_slot_d)list) ==>
           0i <= cm_rep_member_size slot_ +
             cm_rep_members_size rest_`),
          head_nonnegative), tail_nonnegative));
    }
    long long size = cmc_code_slot_size(slot->ty, slot->count);
    [[cst::proof]] {
      thm slot_model = inst_rule(TERM_PAIR_LIST(
          (term_pair){`slot_:cm_slot_d`, `member:cm_slot_d`}),
          get_cm_rep_member_size_def());
      thm value_model = trans_rule(
          assume_rule(
            `retval == cm_rep_code_slot_size
              (cm_type_encode (cm_slot_ty (slot_:cm_slot_d)))
              (cm_slot_count slot_)`),
          sym_rule(slot_model));
      add_fact_st(value_model);
      cst_set_symbolic_state(retarget_cell64_st(
          cst_get_symbolic_state(), `size__addr:addr`, `retval:int`,
          `cm_rep_member_size (slot_:cm_slot_d)`));
    }
    struct cm_slot *next = slot->next;
    long long rest_size = cmc_slots_size(next);
    [[cst::proof]] {
      cst_set_symbolic_state(retarget_cell64_st(
          cst_get_symbolic_state(), `rest_size__addr:addr`,
          `retval_1:int`, `cm_rep_members_size rest_`));
    }
    total = size + rest_size;
    [[cst::proof]] {
      thm total_model = by_rewrite(
          `cm_rep_member_size (slot_:cm_slot_d) +
             cm_rep_members_size (rest_:(cm_slot_d)list) ==
           cm_rep_members_size (slots:(cm_slot_d)list)`,
          THM_LIST(assume_rule(
              `slots == (slot_:cm_slot_d) ::
                (rest_:(cm_slot_d)list)`),
            get_cm_rep_members_size_def()));
      add_fact_st(total_model);
      cst_set_symbolic_state(retarget_cell64_st(
          cst_get_symbolic_state(), `total__addr:addr`,
          `cm_rep_member_size (slot_:cm_slot_d) +
            cm_rep_members_size (rest_:(cm_slot_d)list)`,
          `cm_rep_members_size (slots:(cm_slot_d)list)`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(TERM_LIST(`slot__pre:addr`,
              `slot_:cm_slot_d`, `rest_:(cm_slot_d)list`,
              `zn_:int`), get_cm_slot_fold()),
            assume_rule(`~(slot__pre == 0i)`))));
    }
  }
  return total;
}

static long long cmc_slots_prefix(struct cm_slot *slot, int index)
    [[cst::param(`slots:(cm_slot_d)list`)]]
    [[cst::require(`fact(0i <= index) **
      fact(cm_rep_members_safe slots <=> true) **
      cm_slot_list_rep slot slots`)]]
    [[cst::ensure(`fact(0i <= index) **
      fact(cm_rep_members_safe slots <=> true) **
      cm_slot_list_rep slot slots **
      fact((__return:int) == cm_rep_member_prefix slots index) **
      fact(0i <= cm_rep_member_prefix slots index) **
      fact(cm_rep_member_prefix slots index <=
        cm_rep_members_size slots) **
      fact(cm_rep_member_prefix slots index <= 1048576i)`)]]
{
  long long total;
  if (slot == 0) {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`slot__pre:addr`, `slots:(cm_slot_d)list`),
              get_cm_slot_null()),
            assume_rule(`slot__pre == 0i`))));
      thm model = by_rewrite(
          `cm_rep_member_prefix (slots:(cm_slot_d)list)
             (index__pre:int) == 0i`,
          THM_LIST(assume_rule(
              `slots == ([]:(cm_slot_d)list)`),
            get_cm_rep_member_prefix_def()));
      add_fact_st(sym_rule(model));
      thm size_model = by_rewrite(
          `cm_rep_members_size (slots:(cm_slot_d)list) == 0i`,
          THM_LIST(assume_rule(
              `slots == ([]:(cm_slot_d)list)`),
            get_cm_rep_members_size_def()));
      thm zero_nonnegative = int_arith_rule(`0i <= 0i`);
      thm prefix_nonnegative_eq = mk_binop_rule(
          `(<=):int->int->bool`, refl_rule(`0i:int`), model);
      add_fact_st(eq_mp_rule(sym_rule(prefix_nonnegative_eq),
          zero_nonnegative));
      thm prefix_upper_eq = mk_binop_rule(
          `(<=):int->int->bool`, model, size_model);
      add_fact_st(eq_mp_rule(sym_rule(prefix_upper_eq),
          zero_nonnegative));
      thm nil_view = spec_rule(`slot__pre:addr`,
          conjunct1_rule(get_cm_slot_list_rep_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(nil_view))));
    }
    total = 0;
  } else {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`slot__pre:addr`, `slots:(cm_slot_d)list`),
              get_cm_slot_unfold()),
            assume_rule(`~(slot__pre == 0i)`))));
      thm safe = from_state_bool(
          `cm_rep_members_safe (slots:(cm_slot_d)list)`);
      thm opened_safe = conv_rule(rewrite_conv(THM_LIST(
          assume_rule(
            `slots == (slot_:cm_slot_d) ::
              (rest_:(cm_slot_d)list)`),
          get_cm_rep_members_safe_def(),
          get_cm_rep_members_size_def())), safe);
      thm head_nonnegative = conjunct1_rule(opened_safe);
      thm tail_nonnegative =
          conjunct1_rule(conjunct2_rule(opened_safe));
      thm sum_upper = conjunct1_rule(
          conjunct2_rule(conjunct2_rule(opened_safe)));
      thm tail_safe = conjunct2_rule(
          conjunct2_rule(conjunct2_rule(opened_safe)));
      add_fact_st(head_nonnegative);
      add_fact_st(tail_nonnegative);
      add_fact_st(sum_upper);
      add_fact_st(eqt_intro_rule(tail_safe));
      add_fact_st(mp_rule(mp_rule(int_arith_rule(
          `0i <= cm_rep_member_size (slot_:cm_slot_d) ==>
           0i <= cm_rep_members_size (rest_:(cm_slot_d)list) ==>
           0i <= cm_rep_member_size slot_ +
             cm_rep_members_size rest_`),
          head_nonnegative), tail_nonnegative));
    }
    if (index == 0) {
      total = 0;
      [[cst::proof]] {
        thm model = by_rewrite(
            `cm_rep_member_prefix (slots:(cm_slot_d)list)
               (index__pre:int) == 0i`,
            THM_LIST(assume_rule(`index__pre == 0i`),
              assume_rule(
                `slots == (slot_:cm_slot_d) ::
                  (rest_:(cm_slot_d)list)`),
              get_cm_rep_member_prefix_def()));
        add_fact_st(sym_rule(model));
        thm zero_nonnegative = int_arith_rule(`0i <= 0i`);
        thm prefix_nonnegative_eq = mk_binop_rule(
            `(<=):int->int->bool`, refl_rule(`0i:int`), model);
        add_fact_st(eq_mp_rule(sym_rule(prefix_nonnegative_eq),
            zero_nonnegative));
        add_fact_st(mp_rule(int_arith_rule(
            `cm_rep_member_prefix (slots:(cm_slot_d)list)
               (index__pre:int) == 0i ==>
             cm_rep_member_prefix slots index__pre <= 1048576i`),
            model));
        thm size_model = by_rewrite(
            `cm_rep_members_size (slots:(cm_slot_d)list) ==
             cm_rep_member_size (slot_:cm_slot_d) +
               cm_rep_members_size (rest_:(cm_slot_d)list)`,
            THM_LIST(assume_rule(
                `slots == (slot_:cm_slot_d) ::
                  (rest_:(cm_slot_d)list)`),
              get_cm_rep_members_size_def()));
        thm size_nonnegative_eq = mk_binop_rule(
            `(<=):int->int->bool`, refl_rule(`0i:int`), size_model);
        thm size_nonnegative = eq_mp_rule(
            sym_rule(size_nonnegative_eq), assume_rule(
              `0i <= cm_rep_member_size (slot_:cm_slot_d) +
                cm_rep_members_size (rest_:(cm_slot_d)list)`));
        thm prefix_upper_eq = mk_binop_rule(
            `(<=):int->int->bool`, model,
            refl_rule(`cm_rep_members_size
              (slots:(cm_slot_d)list)`));
        add_fact_st(eq_mp_rule(sym_rule(prefix_upper_eq),
            size_nonnegative));
        cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
            mp_rule(specl_rule(TERM_LIST(`slot__pre:addr`,
                `slot_:cm_slot_d`, `rest_:(cm_slot_d)list`,
                `zn_:int`), get_cm_slot_fold()),
              assume_rule(`~(slot__pre == 0i)`))));
      }
    } else {
      long long size = cmc_code_slot_size(slot->ty, slot->count);
      [[cst::proof]] {
        thm slot_model = inst_rule(TERM_PAIR_LIST(
            (term_pair){`slot_:cm_slot_d`, `member:cm_slot_d`}),
            get_cm_rep_member_size_def());
        add_fact_st(trans_rule(assume_rule(
            `retval == cm_rep_code_slot_size
              (cm_type_encode (cm_slot_ty (slot_:cm_slot_d)))
              (cm_slot_count slot_)`), sym_rule(slot_model)));
        cst_set_symbolic_state(retarget_cell64_st(
            cst_get_symbolic_state(), `size__addr:addr`, `retval:int`,
            `cm_rep_member_size (slot_:cm_slot_d)`));
      }
      struct cm_slot *next = slot->next;
      [[cst::proof]] {
        add_data_at_range_st(`index__addr:addr`, `Tint`,
            `index__pre:int`);
      }
      long long rest_size = cmc_slots_prefix(next, index - 1);
      [[cst::proof]] {
        thm result_model = assume_rule(
            `retval_1 == cm_rep_member_prefix
              (rest_:(cm_slot_d)list) ((index__pre:int) - 1i)`);
        thm prefix_nonnegative = assume_rule(
            `0i <= cm_rep_member_prefix
              (rest_:(cm_slot_d)list) ((index__pre:int) - 1i)`);
        thm prefix_upper = assume_rule(
            `cm_rep_member_prefix
               (rest_:(cm_slot_d)list) ((index__pre:int) - 1i) <=
             cm_rep_members_size rest_`);
        thm combined_nonnegative = mp_rule(mp_rule(int_arith_rule(
            `0i <= cm_rep_member_size (slot_:cm_slot_d) ==>
             0i <= cm_rep_member_prefix
               (rest_:(cm_slot_d)list) ((index__pre:int) - 1i) ==>
             0i <= cm_rep_member_size slot_ +
               cm_rep_member_prefix rest_ (index__pre - 1i)`),
            assume_rule(`0i <= cm_rep_member_size
              (slot_:cm_slot_d)`)), prefix_nonnegative);
        thm combined_upper = mp_rule(mp_rule(int_arith_rule(
            `cm_rep_member_prefix
               (rest_:(cm_slot_d)list) ((index__pre:int) - 1i) <=
                 cm_rep_members_size rest_ ==>
             cm_rep_member_size (slot_:cm_slot_d) +
               cm_rep_members_size rest_ <= 1048576i ==>
             cm_rep_member_size slot_ +
               cm_rep_member_prefix rest_ (index__pre - 1i) <=
                 1048576i`),
            prefix_upper), assume_rule(
              `cm_rep_member_size (slot_:cm_slot_d) +
                 cm_rep_members_size (rest_:(cm_slot_d)list) <=
               1048576i`));
        add_fact_st(prefix_nonnegative);
        add_fact_st(prefix_upper);
        add_fact_st(combined_nonnegative);
        add_fact_st(combined_upper);
        cst_set_symbolic_state(retarget_cell64_st(
            cst_get_symbolic_state(), `rest_size__addr:addr`,
            `retval_1:int`,
            `cm_rep_member_prefix
              (rest_:(cm_slot_d)list) ((index__pre:int) - 1i)`));
      }
      total = size + rest_size;
      [[cst::proof]] {
        thm model = by_rewrite(
            `cm_rep_member_size (slot_:cm_slot_d) +
               cm_rep_member_prefix
                 (rest_:(cm_slot_d)list) ((index__pre:int) - 1i) ==
             cm_rep_member_prefix
               (slots:(cm_slot_d)list) index__pre`,
            THM_LIST(assume_rule(`~(index__pre == 0i)`),
              assume_rule(
                `slots == (slot_:cm_slot_d) ::
                  (rest_:(cm_slot_d)list)`),
              get_cm_rep_member_prefix_def()));
        add_fact_st(model);
        thm combined_nonnegative = assume_rule(
            `0i <= cm_rep_member_size (slot_:cm_slot_d) +
              cm_rep_member_prefix
                (rest_:(cm_slot_d)list) ((index__pre:int) - 1i)`);
        thm combined_relative = mp_rule(int_arith_rule(
            `cm_rep_member_prefix
               (rest_:(cm_slot_d)list) ((index__pre:int) - 1i) <=
                 cm_rep_members_size rest_ ==>
             cm_rep_member_size (slot_:cm_slot_d) +
               cm_rep_member_prefix rest_ (index__pre - 1i) <=
             cm_rep_member_size slot_ + cm_rep_members_size rest_`),
            assume_rule(
              `cm_rep_member_prefix
                 (rest_:(cm_slot_d)list) ((index__pre:int) - 1i) <=
               cm_rep_members_size rest_`));
        thm size_model = by_rewrite(
            `cm_rep_members_size (slots:(cm_slot_d)list) ==
             cm_rep_member_size (slot_:cm_slot_d) +
               cm_rep_members_size (rest_:(cm_slot_d)list)`,
            THM_LIST(assume_rule(
                `slots == (slot_:cm_slot_d) ::
                  (rest_:(cm_slot_d)list)`),
              get_cm_rep_members_size_def()));
        add_fact_st(conv_rule(rewrite_conv(THM_LIST(model)),
            combined_nonnegative));
        add_fact_st(conv_rule(rewrite_conv(
            THM_LIST(model, sym_rule(size_model))),
            combined_relative));
        cst_set_symbolic_state(retarget_cell64_st(
            cst_get_symbolic_state(), `total__addr:addr`,
            `cm_rep_member_size (slot_:cm_slot_d) +
              cm_rep_member_prefix
                (rest_:(cm_slot_d)list) ((index__pre:int) - 1i)`,
            `cm_rep_member_prefix
              (slots:(cm_slot_d)list) (index__pre:int)`));
        cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
            mp_rule(specl_rule(TERM_LIST(`slot__pre:addr`,
                `slot_:cm_slot_d`, `rest_:(cm_slot_d)list`,
                `zn_:int`), get_cm_slot_fold()),
              assume_rule(`~(slot__pre == 0i)`))));
      }
    }
  }
  return total;
}

static long long cmc_members_prefix(struct cm_member *node, int index)
    [[cst::param(`members:(cm_slot_d)list`)]]
    [[cst::require(`fact(0i <= index) **
      fact(cm_rep_members_safe members <=> true) **
      cm_member_list_rep node members`)]]
    [[cst::ensure(`fact(0i <= index) **
      fact(cm_rep_members_safe members <=> true) **
      cm_member_list_rep node members **
      fact((__return:int) == cm_rep_member_prefix members index) **
      fact(0i <= (__return:int)) **
      fact((__return:int) <= cm_rep_members_size members) **
      fact((__return:int) <= 1048576i)`)]]
{
  long long total;
  if (node == 0) {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`node__pre:addr`, `members:(cm_slot_d)list`),
              get_cm_member_null()),
            assume_rule(`node__pre == 0i`))));
      thm model = by_rewrite(
          `cm_rep_member_prefix (members:(cm_slot_d)list)
             (index__pre:int) == 0i`,
          THM_LIST(assume_rule(
              `members == ([]:(cm_slot_d)list)`),
            get_cm_rep_member_prefix_def()));
      add_fact_st(sym_rule(model));
      thm size_model = by_rewrite(
          `cm_rep_members_size (members:(cm_slot_d)list) == 0i`,
          THM_LIST(assume_rule(
              `members == ([]:(cm_slot_d)list)`),
            get_cm_rep_members_size_def()));
      thm zero_nonnegative = int_arith_rule(`0i <= 0i`);
      thm prefix_nonnegative_eq = mk_binop_rule(
          `(<=):int->int->bool`, refl_rule(`0i:int`), model);
      add_fact_st(eq_mp_rule(sym_rule(prefix_nonnegative_eq),
          zero_nonnegative));
      thm prefix_upper_eq = mk_binop_rule(
          `(<=):int->int->bool`, model, size_model);
      add_fact_st(eq_mp_rule(sym_rule(prefix_upper_eq),
          zero_nonnegative));
      thm nil_view = spec_rule(`node__pre:addr`,
          conjunct1_rule(get_cm_member_list_rep_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(nil_view))));
    }
    total = 0;
  } else {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`node__pre:addr`, `members:(cm_slot_d)list`),
              get_cm_member_unfold()),
            assume_rule(`~(node__pre == 0i)`))));
      thm safe = from_state_bool(
          `cm_rep_members_safe (members:(cm_slot_d)list)`);
      thm opened_safe = conv_rule(rewrite_conv(THM_LIST(
          assume_rule(
            `members == (member_:cm_slot_d) ::
              (rest_:(cm_slot_d)list)`),
          get_cm_rep_members_safe_def(),
          get_cm_rep_members_size_def())), safe);
      thm head_nonnegative = conjunct1_rule(opened_safe);
      thm tail_nonnegative =
          conjunct1_rule(conjunct2_rule(opened_safe));
      thm sum_upper = conjunct1_rule(
          conjunct2_rule(conjunct2_rule(opened_safe)));
      thm tail_safe = conjunct2_rule(
          conjunct2_rule(conjunct2_rule(opened_safe)));
      add_fact_st(head_nonnegative);
      add_fact_st(tail_nonnegative);
      add_fact_st(sum_upper);
      add_fact_st(eqt_intro_rule(tail_safe));
      add_fact_st(mp_rule(mp_rule(int_arith_rule(
          `0i <= cm_rep_member_size (member_:cm_slot_d) ==>
           0i <= cm_rep_members_size (rest_:(cm_slot_d)list) ==>
           0i <= cm_rep_member_size member_ +
             cm_rep_members_size rest_`),
          head_nonnegative), tail_nonnegative));
    }
    if (index == 0) {
      total = 0;
      [[cst::proof]] {
        thm model = by_rewrite(
            `cm_rep_member_prefix (members:(cm_slot_d)list)
               (index__pre:int) == 0i`,
            THM_LIST(assume_rule(`index__pre == 0i`),
              assume_rule(
                `members == (member_:cm_slot_d) ::
                  (rest_:(cm_slot_d)list)`),
              get_cm_rep_member_prefix_def()));
        add_fact_st(sym_rule(model));
        thm zero_nonnegative = int_arith_rule(`0i <= 0i`);
        thm prefix_nonnegative_eq = mk_binop_rule(
            `(<=):int->int->bool`, refl_rule(`0i:int`), model);
        add_fact_st(eq_mp_rule(sym_rule(prefix_nonnegative_eq),
            zero_nonnegative));
        thm size_model = by_rewrite(
            `cm_rep_members_size (members:(cm_slot_d)list) ==
             cm_rep_member_size (member_:cm_slot_d) +
               cm_rep_members_size (rest_:(cm_slot_d)list)`,
            THM_LIST(assume_rule(
                `members == (member_:cm_slot_d) ::
                  (rest_:(cm_slot_d)list)`),
              get_cm_rep_members_size_def()));
        thm size_nonnegative_eq = mk_binop_rule(
            `(<=):int->int->bool`, refl_rule(`0i:int`), size_model);
        thm size_nonnegative = eq_mp_rule(
            sym_rule(size_nonnegative_eq), assume_rule(
              `0i <= cm_rep_member_size (member_:cm_slot_d) +
                cm_rep_members_size (rest_:(cm_slot_d)list)`));
        thm prefix_upper_eq = mk_binop_rule(
            `(<=):int->int->bool`, model,
            refl_rule(`cm_rep_members_size
              (members:(cm_slot_d)list)`));
        add_fact_st(eq_mp_rule(sym_rule(prefix_upper_eq),
            size_nonnegative));
        cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
            mp_rule(specl_rule(TERM_LIST(`node__pre:addr`,
                `member_:cm_slot_d`, `rest_:(cm_slot_d)list`,
                `zn_:int`), get_cm_member_fold()),
              assume_rule(`~(node__pre == 0i)`))));
      }
    } else {
      long long size = cmc_code_slot_size(node->ty, node->count);
      [[cst::proof]] {
        thm member_model = inst_rule(TERM_PAIR_LIST(
            (term_pair){`member_:cm_slot_d`, `member:cm_slot_d`}),
            get_cm_rep_member_size_def());
        add_fact_st(trans_rule(assume_rule(
            `retval == cm_rep_code_slot_size
              (cm_type_encode (cm_slot_ty (member_:cm_slot_d)))
              (cm_slot_count member_)`), sym_rule(member_model)));
        cst_set_symbolic_state(retarget_cell64_st(
            cst_get_symbolic_state(), `size__addr:addr`, `retval:int`,
            `cm_rep_member_size (member_:cm_slot_d)`));
      }
      struct cm_member *next = node->next;
      [[cst::proof]] {
        add_data_at_range_st(`index__addr:addr`, `Tint`,
            `index__pre:int`);
      }
      long long rest_size = cmc_members_prefix(next, index - 1);
      [[cst::proof]] {
        thm result_model = assume_rule(
            `retval_1 == cm_rep_member_prefix
              (rest_:(cm_slot_d)list) ((index__pre:int) - 1i)`);
        thm prefix_nonnegative = conv_rule(
            rewrite_conv(THM_LIST(result_model)),
            assume_rule(`0i <= retval_1`));
        thm prefix_upper = conv_rule(
            rewrite_conv(THM_LIST(result_model)),
            assume_rule(
              `retval_1 <= cm_rep_members_size
                (rest_:(cm_slot_d)list)`));
        thm combined_nonnegative = mp_rule(mp_rule(int_arith_rule(
            `0i <= cm_rep_member_size (member_:cm_slot_d) ==>
             0i <= cm_rep_member_prefix
               (rest_:(cm_slot_d)list) ((index__pre:int) - 1i) ==>
             0i <= cm_rep_member_size member_ +
               cm_rep_member_prefix rest_ (index__pre - 1i)`),
            assume_rule(`0i <= cm_rep_member_size
              (member_:cm_slot_d)`)), prefix_nonnegative);
        thm combined_upper = mp_rule(mp_rule(int_arith_rule(
            `cm_rep_member_prefix
               (rest_:(cm_slot_d)list) ((index__pre:int) - 1i) <=
                 cm_rep_members_size rest_ ==>
             cm_rep_member_size (member_:cm_slot_d) +
               cm_rep_members_size rest_ <= 1048576i ==>
             cm_rep_member_size member_ +
               cm_rep_member_prefix rest_ (index__pre - 1i) <=
                 1048576i`),
            prefix_upper), assume_rule(
              `cm_rep_member_size (member_:cm_slot_d) +
                 cm_rep_members_size (rest_:(cm_slot_d)list) <=
               1048576i`));
        add_fact_st(prefix_nonnegative);
        add_fact_st(prefix_upper);
        add_fact_st(combined_nonnegative);
        add_fact_st(combined_upper);
        cst_set_symbolic_state(retarget_cell64_st(
            cst_get_symbolic_state(), `rest_size__addr:addr`,
            `retval_1:int`,
            `cm_rep_member_prefix
              (rest_:(cm_slot_d)list) ((index__pre:int) - 1i)`));
      }
      total = size + rest_size;
      [[cst::proof]] {
        thm model = by_rewrite(
            `cm_rep_member_size (member_:cm_slot_d) +
               cm_rep_member_prefix
                 (rest_:(cm_slot_d)list) ((index__pre:int) - 1i) ==
             cm_rep_member_prefix
               (members:(cm_slot_d)list) index__pre`,
            THM_LIST(assume_rule(`~(index__pre == 0i)`),
              assume_rule(
                `members == (member_:cm_slot_d) ::
                  (rest_:(cm_slot_d)list)`),
              get_cm_rep_member_prefix_def()));
        add_fact_st(model);
        thm combined_nonnegative = assume_rule(
            `0i <= cm_rep_member_size (member_:cm_slot_d) +
              cm_rep_member_prefix
                (rest_:(cm_slot_d)list) ((index__pre:int) - 1i)`);
        thm combined_relative = mp_rule(int_arith_rule(
            `cm_rep_member_prefix
               (rest_:(cm_slot_d)list) ((index__pre:int) - 1i) <=
                 cm_rep_members_size rest_ ==>
             cm_rep_member_size (member_:cm_slot_d) +
               cm_rep_member_prefix rest_ (index__pre - 1i) <=
             cm_rep_member_size member_ + cm_rep_members_size rest_`),
            assume_rule(
              `cm_rep_member_prefix
                 (rest_:(cm_slot_d)list) ((index__pre:int) - 1i) <=
               cm_rep_members_size rest_`));
        thm size_model = by_rewrite(
            `cm_rep_members_size (members:(cm_slot_d)list) ==
             cm_rep_member_size (member_:cm_slot_d) +
               cm_rep_members_size (rest_:(cm_slot_d)list)`,
            THM_LIST(assume_rule(
                `members == (member_:cm_slot_d) ::
                  (rest_:(cm_slot_d)list)`),
              get_cm_rep_members_size_def()));
        add_fact_st(conv_rule(rewrite_conv(THM_LIST(model)),
            combined_nonnegative));
        add_fact_st(conv_rule(rewrite_conv(
            THM_LIST(model, sym_rule(size_model))),
            combined_relative));
        cst_set_symbolic_state(retarget_cell64_st(
            cst_get_symbolic_state(), `total__addr:addr`,
            `cm_rep_member_size (member_:cm_slot_d) +
              cm_rep_member_prefix
                (rest_:(cm_slot_d)list) ((index__pre:int) - 1i)`,
            `cm_rep_member_prefix
              (members:(cm_slot_d)list) (index__pre:int)`));
        cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
            mp_rule(specl_rule(TERM_LIST(`node__pre:addr`,
                `member_:cm_slot_d`, `rest_:(cm_slot_d)list`,
                `zn_:int`), get_cm_member_fold()),
              assume_rule(`~(node__pre == 0i)`))));
      }
    }
  }
  return total;
}
long long cmc_member_offset_at(struct cm_struct *item,
                                      int sid, int index)
    [[cst::param(`structs:(cm_struct_d)list`)]]
    [[cst::require(`fact(0i <= sid) ** fact(0i <= index) **
      fact(cm_rep_structs_safe structs <=> true) **
      cm_struct_list_rep item structs`)]]
    [[cst::ensure(`fact(0i <= sid) ** fact(0i <= index) **
      fact(cm_rep_structs_safe structs <=> true) **
      cm_struct_list_rep item structs **
      fact((__return:int) ==
        cm_rep_struct_member_prefix structs sid index) **
      fact(0i <= (__return:int)) ** fact((__return:int) <= 1048576i)`)]]
{
  long long total;
  if (item == 0) {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`item__pre:addr`, `structs:(cm_struct_d)list`),
              get_cm_struct_null()),
            assume_rule(`item__pre == 0i`))));
      thm model = by_rewrite(
          `cm_rep_struct_member_prefix
             (structs:(cm_struct_d)list)
             (sid__pre:int) (index__pre:int) == 0i`,
          THM_LIST(assume_rule(
              `structs == ([]:(cm_struct_d)list)`),
            get_cm_rep_struct_member_prefix_def()));
      add_fact_st(sym_rule(model));
      thm nil_view = spec_rule(`item__pre:addr`,
          conjunct1_rule(get_cm_struct_list_rep_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(nil_view))));
    }
    total = 0;
  } else {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`item__pre:addr`, `structs:(cm_struct_d)list`),
              get_cm_struct_unfold()),
            assume_rule(`~(item__pre == 0i)`))));
      thm safe = from_state_bool(
          `cm_rep_structs_safe (structs:(cm_struct_d)list)`);
      thm opened_safe = conv_rule(rewrite_conv(THM_LIST(
          assume_rule(
            `structs == (strct_:cm_struct_d) ::
              (rest_:(cm_struct_d)list)`),
          get_cm_rep_structs_safe_def())), safe);
      add_fact_st(eqt_intro_rule(conjunct1_rule(opened_safe)));
      add_fact_st(eqt_intro_rule(conjunct2_rule(opened_safe)));
    }
    if (sid == 0) {
      total = cmc_members_prefix(item->members, index);
      [[cst::proof]] {
        thm model = by_rewrite(
            `cm_rep_member_prefix
                (cm_struct_members (strct_:cm_struct_d))
                (index__pre:int) ==
             cm_rep_struct_member_prefix
               (structs:(cm_struct_d)list)
               (sid__pre:int) index__pre`,
            THM_LIST(assume_rule(`sid__pre == 0i`),
              assume_rule(
                `structs == (strct_:cm_struct_d) ::
                  (rest_:(cm_struct_d)list)`),
              get_cm_rep_struct_member_prefix_def()));
        thm result_model = trans_rule(assume_rule(
            `retval == cm_rep_member_prefix
              (cm_struct_members (strct_:cm_struct_d))
              (index__pre:int)`), model);
        add_fact_st(result_model);
        add_fact_st(conv_rule(rewrite_conv(THM_LIST(result_model)),
            assume_rule(`0i <= retval`)));
        add_fact_st(conv_rule(rewrite_conv(THM_LIST(result_model)),
            assume_rule(`retval <= 1048576i`)));
        cst_set_symbolic_state(retarget_cell64_st(
            cst_get_symbolic_state(), `total__addr:addr`, `retval:int`,
            `cm_rep_struct_member_prefix
              (structs:(cm_struct_d)list)
              (sid__pre:int) (index__pre:int)`));
        cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
            mp_rule(specl_rule(TERM_LIST(`item__pre:addr`,
                `strct_:cm_struct_d`, `rest_:(cm_struct_d)list`,
                `zm_:int`, `zn_:int`), get_cm_struct_fold()),
              assume_rule(`~(item__pre == 0i)`))));
      }
    } else {
      struct cm_struct *next = item->next;
      [[cst::proof]] {
        add_data_at_range_st(`sid__addr:addr`, `Tint`,
            `sid__pre:int`);
      }
      total = cmc_member_offset_at(next, sid - 1, index);
      [[cst::proof]] {
        thm model = by_rewrite(
            `cm_rep_struct_member_prefix
                (rest_:(cm_struct_d)list)
                ((sid__pre:int) - 1i) (index__pre:int) ==
             cm_rep_struct_member_prefix
               (structs:(cm_struct_d)list)
               sid__pre index__pre`,
            THM_LIST(assume_rule(`~(sid__pre == 0i)`),
              assume_rule(
                `structs == (strct_:cm_struct_d) ::
                  (rest_:(cm_struct_d)list)`),
              get_cm_rep_struct_member_prefix_def()));
        thm result_model = trans_rule(assume_rule(
            `retval == cm_rep_struct_member_prefix
              (rest_:(cm_struct_d)list)
              ((sid__pre:int) - 1i) (index__pre:int)`), model);
        add_fact_st(result_model);
        add_fact_st(conv_rule(rewrite_conv(THM_LIST(result_model)),
            assume_rule(`0i <= retval`)));
        add_fact_st(conv_rule(rewrite_conv(THM_LIST(result_model)),
            assume_rule(`retval <= 1048576i`)));
        cst_set_symbolic_state(retarget_cell64_st(
            cst_get_symbolic_state(), `total__addr:addr`, `retval:int`,
            `cm_rep_struct_member_prefix
              (structs:(cm_struct_d)list)
              (sid__pre:int) (index__pre:int)`));
        cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
            mp_rule(specl_rule(TERM_LIST(`item__pre:addr`,
                `strct_:cm_struct_d`, `rest_:(cm_struct_d)list`,
                `zm_:int`, `zn_:int`), get_cm_struct_fold()),
              assume_rule(`~(item__pre == 0i)`))));
      }
    }
  }
  return total;
}

static int cmc_struct_member_array_at(struct cm_struct *item,
                                      int sid, int index)
    [[cst::param(`structs:(cm_struct_d)list`)]]
    [[cst::require(`fact(0i <= sid) ** fact(0i <= index) **
      fact(cm_rep_structs_safe structs <=> true) **
      cm_struct_list_rep item structs`)]]
    [[cst::ensure(`fact(0i <= sid) ** fact(0i <= index) **
      fact(cm_rep_structs_safe structs <=> true) **
      cm_struct_list_rep item structs **
      fact((__return:int) ==
        cm_rep_struct_member_array structs sid index)`)]]
{
  int result;
  if (item == 0) {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`item__pre:addr`, `structs:(cm_struct_d)list`),
              get_cm_struct_null()),
            assume_rule(`item__pre == 0i`))));
      thm model = by_rewrite(
          `cm_rep_struct_member_array
             (structs:(cm_struct_d)list)
             (sid__pre:int) (index__pre:int) == 0i`,
          THM_LIST(assume_rule(
              `structs == ([]:(cm_struct_d)list)`),
            get_cm_rep_struct_member_array_def()));
      add_fact_st(sym_rule(model));
      thm nil_view = spec_rule(`item__pre:addr`,
          conjunct1_rule(get_cm_struct_list_rep_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(nil_view))));
    }
    result = 0;
  } else {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`item__pre:addr`, `structs:(cm_struct_d)list`),
              get_cm_struct_unfold()),
            assume_rule(`~(item__pre == 0i)`))));
      thm safe = from_state_bool(
          `cm_rep_structs_safe (structs:(cm_struct_d)list)`);
      thm opened_safe = conv_rule(rewrite_conv(THM_LIST(
          assume_rule(
            `structs == (strct_:cm_struct_d) ::
              (rest_:(cm_struct_d)list)`),
          get_cm_rep_structs_safe_def())), safe);
      add_fact_st(eqt_intro_rule(conjunct1_rule(opened_safe)));
      add_fact_st(eqt_intro_rule(conjunct2_rule(opened_safe)));
    }
    if (sid == 0) {
      result = cmc_member_array_at(item->members, index);
      [[cst::proof]] {
        thm model = by_rewrite(
            `cm_rep_member_array
                (cm_struct_members (strct_:cm_struct_d))
                (index__pre:int) ==
             cm_rep_struct_member_array
               (structs:(cm_struct_d)list)
               (sid__pre:int) index__pre`,
            THM_LIST(assume_rule(`sid__pre == 0i`),
              assume_rule(
                `structs == (strct_:cm_struct_d) ::
                  (rest_:(cm_struct_d)list)`),
              get_cm_rep_struct_member_array_def()));
        thm result_model = trans_rule(assume_rule(
            `retval == cm_rep_member_array
              (cm_struct_members (strct_:cm_struct_d))
              (index__pre:int)`), model);
        add_fact_st(result_model);
        cst_set_symbolic_state(retarget_cell_st(
            cst_get_symbolic_state(), `result__addr:addr`, `retval:int`,
            `cm_rep_struct_member_array
              (structs:(cm_struct_d)list)
              (sid__pre:int) (index__pre:int)`));
        cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
            mp_rule(specl_rule(TERM_LIST(`item__pre:addr`,
                `strct_:cm_struct_d`, `rest_:(cm_struct_d)list`,
                `zm_:int`, `zn_:int`), get_cm_struct_fold()),
              assume_rule(`~(item__pre == 0i)`))));
      }
    } else {
      struct cm_struct *next = item->next;
      [[cst::proof]] {
        add_data_at_range_st(`sid__addr:addr`, `Tint`,
            `sid__pre:int`);
      }
      result = cmc_struct_member_array_at(next, sid - 1, index);
      [[cst::proof]] {
        thm model = by_rewrite(
            `cm_rep_struct_member_array
                (rest_:(cm_struct_d)list)
                ((sid__pre:int) - 1i) (index__pre:int) ==
             cm_rep_struct_member_array
               (structs:(cm_struct_d)list)
               sid__pre index__pre`,
            THM_LIST(assume_rule(`~(sid__pre == 0i)`),
              assume_rule(
                `structs == (strct_:cm_struct_d) ::
                  (rest_:(cm_struct_d)list)`),
              get_cm_rep_struct_member_array_def()));
        thm result_model = trans_rule(assume_rule(
            `retval == cm_rep_struct_member_array
              (rest_:(cm_struct_d)list)
              ((sid__pre:int) - 1i) (index__pre:int)`), model);
        add_fact_st(result_model);
        cst_set_symbolic_state(retarget_cell_st(
            cst_get_symbolic_state(), `result__addr:addr`, `retval:int`,
            `cm_rep_struct_member_array
              (structs:(cm_struct_d)list)
              (sid__pre:int) (index__pre:int)`));
        cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
            mp_rule(specl_rule(TERM_LIST(`item__pre:addr`,
                `strct_:cm_struct_d`, `rest_:(cm_struct_d)list`,
                `zm_:int`, `zn_:int`), get_cm_struct_fold()),
              assume_rule(`~(item__pre == 0i)`))));
      }
    }
  }
  return result;
}

long long cmc_globals_size(struct cm_global *node)
    [[cst::param(`globals:(cm_global_d)list`)]]
    [[cst::require(`fact(cm_rep_globals_safe globals <=> true) **
      cm_global_list_rep node globals`)]]
    [[cst::ensure(`fact(cm_rep_globals_safe globals <=> true) **
      cm_global_list_rep node globals **
      fact((__return:int) == cm_rep_globals_size globals) **
      fact(0i <= (__return:int)) ** fact((__return:int) <= 1048560i)`)]]
{
  long long total;
  if (node == 0) {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`node__pre:addr`, `globals:(cm_global_d)list`),
              get_cm_global_null()),
            assume_rule(`node__pre == 0i`))));
      thm model = by_rewrite(
          `cm_rep_globals_size (globals:(cm_global_d)list) == 0i`,
          THM_LIST(assume_rule(
              `globals == ([]:(cm_global_d)list)`),
            get_cm_rep_globals_size_def()));
      cst_set_symbolic_state(add_fact_st_sym(
          cst_get_symbolic_state(), sym_rule(model)));
      thm nil_view = spec_rule(`node__pre:addr`,
          conjunct1_rule(get_cm_global_list_rep_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(nil_view))));
    }
    total = 0;
  } else {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`node__pre:addr`, `globals:(cm_global_d)list`),
              get_cm_global_unfold()),
            assume_rule(`~(node__pre == 0i)`))));
    }
    [[cst::proof]] {
      thm safe = from_state_bool(
          `cm_rep_globals_safe (globals:(cm_global_d)list)`);
      thm opened_safe = conv_rule(rewrite_conv(THM_LIST(
          assume_rule(
            `globals == (global_:cm_global_d) ::
              (rest_:(cm_global_d)list)`),
          get_cm_rep_globals_safe_def(),
          get_cm_rep_globals_size_def())), safe);
      thm head_nonnegative = conjunct1_rule(opened_safe);
      thm tail_nonnegative =
          conjunct1_rule(conjunct2_rule(opened_safe));
      thm sum_upper = conjunct1_rule(
          conjunct2_rule(conjunct2_rule(opened_safe)));
      thm tail_safe = conjunct2_rule(
          conjunct2_rule(conjunct2_rule(opened_safe)));
      add_fact_st(head_nonnegative);
      add_fact_st(tail_nonnegative);
      add_fact_st(sum_upper);
      add_fact_st(eqt_intro_rule(tail_safe));
      add_fact_st(mp_rule(mp_rule(int_arith_rule(
          `0i <= cm_rep_global_size (global_:cm_global_d) ==>
           0i <= cm_rep_globals_size (rest_:(cm_global_d)list) ==>
           0i <= cm_rep_global_size global_ +
             cm_rep_globals_size rest_`),
          head_nonnegative), tail_nonnegative));
    }
    long long size = cmc_code_slot_size(node->ty, node->count);
    [[cst::proof]] {
      thm member_model = inst_rule(TERM_PAIR_LIST(
          (term_pair){`global_:cm_global_d`, `global:cm_global_d`}),
          get_cm_rep_global_size_def());
      thm value_model = trans_rule(
          assume_rule(
            `retval == cm_rep_code_slot_size
              (cm_type_encode (cm_global_ty (global_:cm_global_d)))
              (cm_global_count global_)`),
          sym_rule(member_model));
      cst_set_symbolic_state(add_fact_st_sym(
          cst_get_symbolic_state(), value_model));
      cst_set_symbolic_state(retarget_cell64_st(
          cst_get_symbolic_state(), `size__addr:addr`, `retval:int`,
          `cm_rep_global_size (global_:cm_global_d)`));
    }
    struct cm_global *next = node->next;
    long long rest_size = cmc_globals_size(next);
    [[cst::proof]] {
      cst_set_symbolic_state(retarget_cell64_st(
          cst_get_symbolic_state(), `rest_size__addr:addr`,
          `retval_1:int`, `cm_rep_globals_size rest_`));
    }
    total = size + rest_size;
    [[cst::proof]] {
      thm total_model = by_rewrite(
          `cm_rep_global_size (global_:cm_global_d) +
             cm_rep_globals_size (rest_:(cm_global_d)list) ==
           cm_rep_globals_size (globals:(cm_global_d)list)`,
          THM_LIST(assume_rule(
              `globals == (global_:cm_global_d) ::
                (rest_:(cm_global_d)list)`),
            get_cm_rep_globals_size_def()));
      cst_set_symbolic_state(add_fact_st_sym(
          cst_get_symbolic_state(), total_model));
      cst_set_symbolic_state(retarget_cell64_st(
          cst_get_symbolic_state(), `total__addr:addr`,
          `cm_rep_global_size (global_:cm_global_d) +
            cm_rep_globals_size (rest_:(cm_global_d)list)`,
          `cm_rep_globals_size (globals:(cm_global_d)list)`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(TERM_LIST(`node__pre:addr`,
              `global_:cm_global_d`, `rest_:(cm_global_d)list`,
              `zn_:int`), get_cm_global_fold()),
            assume_rule(`~(node__pre == 0i)`))));
    }
  }
  return total;
}

static long long cmc_globals_prefix(struct cm_global *node, int index)
    [[cst::param(`globals:(cm_global_d)list`)]]
    [[cst::require(`fact(0i <= index) **
      fact(cm_rep_globals_safe globals <=> true) **
      cm_global_list_rep node globals`)]]
    [[cst::ensure(`fact(0i <= index) **
      fact(cm_rep_globals_safe globals <=> true) **
      cm_global_list_rep node globals **
      fact((__return:int) == cm_rep_globals_prefix globals index) **
      fact(0i <= (__return:int)) **
      fact((__return:int) <= cm_rep_globals_size globals) **
      fact((__return:int) <= 1048560i)`)]]
{
  long long total;
  if (node == 0) {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`node__pre:addr`, `globals:(cm_global_d)list`),
              get_cm_global_null()),
            assume_rule(`node__pre == 0i`))));
      thm model = by_rewrite(
          `cm_rep_globals_prefix (globals:(cm_global_d)list)
             (index__pre:int) == 0i`,
          THM_LIST(assume_rule(
              `globals == ([]:(cm_global_d)list)`),
            get_cm_rep_globals_prefix_def()));
      add_fact_st(sym_rule(model));
      thm size_model = by_rewrite(
          `cm_rep_globals_size (globals:(cm_global_d)list) == 0i`,
          THM_LIST(assume_rule(
              `globals == ([]:(cm_global_d)list)`),
            get_cm_rep_globals_size_def()));
      thm zero_nonnegative = int_arith_rule(`0i <= 0i`);
      thm prefix_nonnegative_eq = mk_binop_rule(
          `(<=):int->int->bool`, refl_rule(`0i:int`), model);
      add_fact_st(eq_mp_rule(sym_rule(prefix_nonnegative_eq),
          zero_nonnegative));
      thm prefix_upper_eq = mk_binop_rule(
          `(<=):int->int->bool`, model, size_model);
      add_fact_st(eq_mp_rule(sym_rule(prefix_upper_eq),
          zero_nonnegative));
      thm nil_view = spec_rule(`node__pre:addr`,
          conjunct1_rule(get_cm_global_list_rep_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(nil_view))));
    }
    total = 0;
  } else {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`node__pre:addr`, `globals:(cm_global_d)list`),
              get_cm_global_unfold()),
            assume_rule(`~(node__pre == 0i)`))));
      thm safe = from_state_bool(
          `cm_rep_globals_safe (globals:(cm_global_d)list)`);
      thm opened_safe = conv_rule(rewrite_conv(THM_LIST(
          assume_rule(
            `globals == (global_:cm_global_d) ::
              (rest_:(cm_global_d)list)`),
          get_cm_rep_globals_safe_def(),
          get_cm_rep_globals_size_def())), safe);
      thm head_nonnegative = conjunct1_rule(opened_safe);
      thm tail_nonnegative =
          conjunct1_rule(conjunct2_rule(opened_safe));
      thm sum_upper = conjunct1_rule(
          conjunct2_rule(conjunct2_rule(opened_safe)));
      thm tail_safe = conjunct2_rule(
          conjunct2_rule(conjunct2_rule(opened_safe)));
      add_fact_st(head_nonnegative);
      add_fact_st(tail_nonnegative);
      add_fact_st(sum_upper);
      add_fact_st(eqt_intro_rule(tail_safe));
      add_fact_st(mp_rule(mp_rule(int_arith_rule(
          `0i <= cm_rep_global_size (global_:cm_global_d) ==>
           0i <= cm_rep_globals_size (rest_:(cm_global_d)list) ==>
           0i <= cm_rep_global_size global_ +
             cm_rep_globals_size rest_`),
          head_nonnegative), tail_nonnegative));
    }
    if (index == 0) {
      total = 0;
      [[cst::proof]] {
        thm model = by_rewrite(
            `cm_rep_globals_prefix (globals:(cm_global_d)list)
               (index__pre:int) == 0i`,
            THM_LIST(assume_rule(`index__pre == 0i`),
              assume_rule(
                `globals == (global_:cm_global_d) ::
                  (rest_:(cm_global_d)list)`),
              get_cm_rep_globals_prefix_def()));
        add_fact_st(sym_rule(model));
        thm zero_nonnegative = int_arith_rule(`0i <= 0i`);
        thm prefix_nonnegative_eq = mk_binop_rule(
            `(<=):int->int->bool`, refl_rule(`0i:int`), model);
        add_fact_st(eq_mp_rule(sym_rule(prefix_nonnegative_eq),
            zero_nonnegative));
        thm size_model = by_rewrite(
            `cm_rep_globals_size (globals:(cm_global_d)list) ==
             cm_rep_global_size (global_:cm_global_d) +
               cm_rep_globals_size (rest_:(cm_global_d)list)`,
            THM_LIST(assume_rule(
                `globals == (global_:cm_global_d) ::
                  (rest_:(cm_global_d)list)`),
              get_cm_rep_globals_size_def()));
        thm size_nonnegative_eq = mk_binop_rule(
            `(<=):int->int->bool`, refl_rule(`0i:int`), size_model);
        thm size_nonnegative = eq_mp_rule(
            sym_rule(size_nonnegative_eq), assume_rule(
              `0i <= cm_rep_global_size (global_:cm_global_d) +
                cm_rep_globals_size (rest_:(cm_global_d)list)`));
        thm prefix_upper_eq = mk_binop_rule(
            `(<=):int->int->bool`, model,
            refl_rule(`cm_rep_globals_size
              (globals:(cm_global_d)list)`));
        add_fact_st(eq_mp_rule(sym_rule(prefix_upper_eq),
            size_nonnegative));
        cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
            mp_rule(specl_rule(TERM_LIST(`node__pre:addr`,
                `global_:cm_global_d`, `rest_:(cm_global_d)list`,
                `zn_:int`), get_cm_global_fold()),
              assume_rule(`~(node__pre == 0i)`))));
      }
    } else {
      long long size = cmc_code_slot_size(node->ty, node->count);
      [[cst::proof]] {
        thm member_model = inst_rule(TERM_PAIR_LIST(
            (term_pair){`global_:cm_global_d`, `global:cm_global_d`}),
            get_cm_rep_global_size_def());
        add_fact_st(trans_rule(assume_rule(
            `retval == cm_rep_code_slot_size
              (cm_type_encode (cm_global_ty (global_:cm_global_d)))
              (cm_global_count global_)`), sym_rule(member_model)));
        cst_set_symbolic_state(retarget_cell64_st(
            cst_get_symbolic_state(), `size__addr:addr`, `retval:int`,
            `cm_rep_global_size (global_:cm_global_d)`));
      }
      struct cm_global *next = node->next;
      [[cst::proof]] {
        add_data_at_range_st(`index__addr:addr`, `Tint`,
            `index__pre:int`);
      }
      long long rest_size = cmc_globals_prefix(next, index - 1);
      [[cst::proof]] {
        thm result_model = assume_rule(
            `retval_1 == cm_rep_globals_prefix
              (rest_:(cm_global_d)list) ((index__pre:int) - 1i)`);
        thm prefix_nonnegative = conv_rule(
            rewrite_conv(THM_LIST(result_model)),
            assume_rule(`0i <= retval_1`));
        thm prefix_upper = conv_rule(
            rewrite_conv(THM_LIST(result_model)),
            assume_rule(
              `retval_1 <= cm_rep_globals_size
                (rest_:(cm_global_d)list)`));
        thm combined_nonnegative = mp_rule(mp_rule(int_arith_rule(
            `0i <= cm_rep_global_size (global_:cm_global_d) ==>
             0i <= cm_rep_globals_prefix
               (rest_:(cm_global_d)list) ((index__pre:int) - 1i) ==>
             0i <= cm_rep_global_size global_ +
               cm_rep_globals_prefix rest_ (index__pre - 1i)`),
            assume_rule(`0i <= cm_rep_global_size
              (global_:cm_global_d)`)), prefix_nonnegative);
        thm combined_upper = mp_rule(mp_rule(int_arith_rule(
            `cm_rep_globals_prefix
               (rest_:(cm_global_d)list) ((index__pre:int) - 1i) <=
                 cm_rep_globals_size rest_ ==>
             cm_rep_global_size (global_:cm_global_d) +
               cm_rep_globals_size rest_ <= 1048560i ==>
             cm_rep_global_size global_ +
               cm_rep_globals_prefix rest_ (index__pre - 1i) <=
                 1048560i`),
            prefix_upper), assume_rule(
              `cm_rep_global_size (global_:cm_global_d) +
                 cm_rep_globals_size (rest_:(cm_global_d)list) <=
               1048560i`));
        add_fact_st(prefix_nonnegative);
        add_fact_st(prefix_upper);
        add_fact_st(combined_nonnegative);
        add_fact_st(combined_upper);
        cst_set_symbolic_state(retarget_cell64_st(
            cst_get_symbolic_state(), `rest_size__addr:addr`,
            `retval_1:int`,
            `cm_rep_globals_prefix
              (rest_:(cm_global_d)list) ((index__pre:int) - 1i)`));
      }
      total = size + rest_size;
      [[cst::proof]] {
        thm model = by_rewrite(
            `cm_rep_global_size (global_:cm_global_d) +
               cm_rep_globals_prefix
                 (rest_:(cm_global_d)list) ((index__pre:int) - 1i) ==
             cm_rep_globals_prefix
               (globals:(cm_global_d)list) index__pre`,
            THM_LIST(assume_rule(`~(index__pre == 0i)`),
              assume_rule(
                `globals == (global_:cm_global_d) ::
                  (rest_:(cm_global_d)list)`),
              get_cm_rep_globals_prefix_def()));
        add_fact_st(model);
        thm combined_nonnegative = assume_rule(
            `0i <= cm_rep_global_size (global_:cm_global_d) +
              cm_rep_globals_prefix
                (rest_:(cm_global_d)list) ((index__pre:int) - 1i)`);
        thm combined_relative = mp_rule(int_arith_rule(
            `cm_rep_globals_prefix
               (rest_:(cm_global_d)list) ((index__pre:int) - 1i) <=
                 cm_rep_globals_size rest_ ==>
             cm_rep_global_size (global_:cm_global_d) +
               cm_rep_globals_prefix rest_ (index__pre - 1i) <=
             cm_rep_global_size global_ + cm_rep_globals_size rest_`),
            assume_rule(
              `cm_rep_globals_prefix
                 (rest_:(cm_global_d)list) ((index__pre:int) - 1i) <=
               cm_rep_globals_size rest_`));
        thm size_model = by_rewrite(
            `cm_rep_globals_size (globals:(cm_global_d)list) ==
             cm_rep_global_size (global_:cm_global_d) +
               cm_rep_globals_size (rest_:(cm_global_d)list)`,
            THM_LIST(assume_rule(
                `globals == (global_:cm_global_d) ::
                  (rest_:(cm_global_d)list)`),
              get_cm_rep_globals_size_def()));
        add_fact_st(conv_rule(rewrite_conv(THM_LIST(model)),
            combined_nonnegative));
        add_fact_st(conv_rule(rewrite_conv(
            THM_LIST(model, sym_rule(size_model))),
            combined_relative));
        cst_set_symbolic_state(retarget_cell64_st(
            cst_get_symbolic_state(), `total__addr:addr`,
            `cm_rep_global_size (global_:cm_global_d) +
              cm_rep_globals_prefix
                (rest_:(cm_global_d)list) ((index__pre:int) - 1i)`,
            `cm_rep_globals_prefix
              (globals:(cm_global_d)list) (index__pre:int)`));
        cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
            mp_rule(specl_rule(TERM_LIST(`node__pre:addr`,
                `global_:cm_global_d`, `rest_:(cm_global_d)list`,
                `zn_:int`), get_cm_global_fold()),
              assume_rule(`~(node__pre == 0i)`))));
      }
    }
  }
  return total;
}


long long cmc_strings_size(struct cm_string *node)
    [[cst::param(`strings:(cm_string_d)list`)]]
    [[cst::require(`fact(cm_rep_strings_safe strings <=> true) **
      cm_string_list_rep node strings`)]]
    [[cst::ensure(`fact(cm_rep_strings_safe strings <=> true) **
      cm_string_list_rep node strings **
      fact((__return:int) == cm_rep_strings_size strings) **
      fact(0i <= (__return:int)) ** fact((__return:int) <= 1048560i)`)]]
{
  long long total;
  if (node == 0) {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`node__pre:addr`,
                `strings:(cm_string_d)list`),
              get_cm_string_null()),
            assume_rule(`node__pre == 0i`))));
      thm model = by_rewrite(
          `cm_rep_strings_size (strings:(cm_string_d)list) == 0i`,
          THM_LIST(assume_rule(
              `strings == ([]:(cm_string_d)list)`),
            get_cm_rep_strings_size_def()));
      add_fact_st(sym_rule(model));
      thm nil_view = spec_rule(`node__pre:addr`,
          conjunct1_rule(get_cm_string_list_rep_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(nil_view))));
    }
    total = 0;
  } else {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`node__pre:addr`,
                `strings:(cm_string_d)list`),
              get_cm_string_unfold()),
            assume_rule(`~(node__pre == 0i)`))));
      thm safe = from_state_bool(
          `cm_rep_strings_safe (strings:(cm_string_d)list)`);
      thm opened_safe = conv_rule(rewrite_conv(THM_LIST(
          assume_rule(
            `strings == (string_:cm_string_d) ::
              (rest_:(cm_string_d)list)`),
          get_cm_rep_strings_safe_def(),
          get_cm_rep_strings_size_def())), safe);
      thm head_nonnegative = conjunct1_rule(opened_safe);
      thm tail_nonnegative =
          conjunct1_rule(conjunct2_rule(opened_safe));
      thm sum_upper = conjunct1_rule(
          conjunct2_rule(conjunct2_rule(opened_safe)));
      thm tail_safe = conjunct2_rule(
          conjunct2_rule(conjunct2_rule(opened_safe)));
      add_fact_st(head_nonnegative);
      add_fact_st(tail_nonnegative);
      add_fact_st(sum_upper);
      add_fact_st(eqt_intro_rule(tail_safe));
      thm head_upper = mp_rule(mp_rule(int_arith_rule(
          `0i <= cm_rep_strings_size
              (rest_:(cm_string_d)list) ==>
           cm_rep_string_size (string_:cm_string_d) +
             cm_rep_strings_size rest_ <= 1048560i ==>
           cm_rep_string_size string_ <= 1048560i`),
          tail_nonnegative), sum_upper);
      thm size_model = inst_rule(TERM_PAIR_LIST(
          (term_pair){`string_:cm_string_d`, `string:cm_string_d`}),
          get_cm_rep_string_size_def());
      add_fact_st(conv_rule(rewrite_conv(THM_LIST(size_model)),
          head_nonnegative));
      add_fact_st(conv_rule(rewrite_conv(THM_LIST(size_model)),
          head_upper));
    }
    long long size = node->length;
    size = size + 1;
    [[cst::proof]] {
      add_fact_st(sym_rule(inst_rule(TERM_PAIR_LIST(
          (term_pair){`string_:cm_string_d`, `string:cm_string_d`}),
          get_cm_rep_string_size_def())));
      cst_set_symbolic_state(retarget_cell64_st(
          cst_get_symbolic_state(), `size__addr:addr`,
          `cm_rep_string_length (string_:cm_string_d) + 1i`,
          `cm_rep_string_size (string_:cm_string_d)`));
    }
    struct cm_string *next = node->next;
    long long rest_size = cmc_strings_size(next);
    [[cst::proof]] {
      cst_set_symbolic_state(retarget_cell64_st(
          cst_get_symbolic_state(), `rest_size__addr:addr`,
          `retval:int`, `cm_rep_strings_size rest_`));
    }
    total = size + rest_size;
    [[cst::proof]] {
      thm model = by_rewrite(
          `cm_rep_string_size (string_:cm_string_d) +
             cm_rep_strings_size (rest_:(cm_string_d)list) ==
           cm_rep_strings_size (strings:(cm_string_d)list)`,
          THM_LIST(assume_rule(
              `strings == (string_:cm_string_d) ::
                (rest_:(cm_string_d)list)`),
            get_cm_rep_strings_size_def()));
      add_fact_st(model);
      cst_set_symbolic_state(retarget_cell64_st(
          cst_get_symbolic_state(), `total__addr:addr`,
          `cm_rep_string_size (string_:cm_string_d) +
            cm_rep_strings_size (rest_:(cm_string_d)list)`,
          `cm_rep_strings_size (strings:(cm_string_d)list)`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(TERM_LIST(`node__pre:addr`,
              `string_:cm_string_d`, `rest_:(cm_string_d)list`,
              `zb_:int`, `zn_:int`), get_cm_string_fold()),
            assume_rule(`~(node__pre == 0i)`))));
    }
  }
  return total;
}

static long long cmc_strings_prefix(struct cm_string *node, int index)
    [[cst::param(`strings:(cm_string_d)list`)]]
    [[cst::require(`fact(0i <= index) **
      fact(cm_rep_strings_safe strings <=> true) **
      cm_string_list_rep node strings`)]]
    [[cst::ensure(`fact(0i <= index) **
      fact(cm_rep_strings_safe strings <=> true) **
      cm_string_list_rep node strings **
      fact((__return:int) == cm_rep_strings_prefix strings index) **
      fact(0i <= (__return:int)) **
      fact((__return:int) <= cm_rep_strings_size strings) **
      fact((__return:int) <= 1048560i)`)]]
{
  long long total;
  if (node == 0) {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`node__pre:addr`, `strings:(cm_string_d)list`),
              get_cm_string_null()),
            assume_rule(`node__pre == 0i`))));
      thm model = by_rewrite(
          `cm_rep_strings_prefix (strings:(cm_string_d)list)
             (index__pre:int) == 0i`,
          THM_LIST(assume_rule(
              `strings == ([]:(cm_string_d)list)`),
            get_cm_rep_strings_prefix_def()));
      add_fact_st(sym_rule(model));
      thm size_model = by_rewrite(
          `cm_rep_strings_size (strings:(cm_string_d)list) == 0i`,
          THM_LIST(assume_rule(
              `strings == ([]:(cm_string_d)list)`),
            get_cm_rep_strings_size_def()));
      thm zero_nonnegative = int_arith_rule(`0i <= 0i`);
      thm prefix_nonnegative_eq = mk_binop_rule(
          `(<=):int->int->bool`, refl_rule(`0i:int`), model);
      add_fact_st(eq_mp_rule(sym_rule(prefix_nonnegative_eq),
          zero_nonnegative));
      thm prefix_upper_eq = mk_binop_rule(
          `(<=):int->int->bool`, model, size_model);
      add_fact_st(eq_mp_rule(sym_rule(prefix_upper_eq),
          zero_nonnegative));
      thm nil_view = spec_rule(`node__pre:addr`,
          conjunct1_rule(get_cm_string_list_rep_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(nil_view))));
    }
    total = 0;
  } else {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`node__pre:addr`, `strings:(cm_string_d)list`),
              get_cm_string_unfold()),
            assume_rule(`~(node__pre == 0i)`))));
      thm safe = from_state_bool(
          `cm_rep_strings_safe (strings:(cm_string_d)list)`);
      thm opened_safe = conv_rule(rewrite_conv(THM_LIST(
          assume_rule(
            `strings == (string_:cm_string_d) ::
              (rest_:(cm_string_d)list)`),
          get_cm_rep_strings_safe_def(),
          get_cm_rep_strings_size_def())), safe);
      thm head_nonnegative = conjunct1_rule(opened_safe);
      thm tail_nonnegative =
          conjunct1_rule(conjunct2_rule(opened_safe));
      thm sum_upper = conjunct1_rule(
          conjunct2_rule(conjunct2_rule(opened_safe)));
      thm tail_safe = conjunct2_rule(
          conjunct2_rule(conjunct2_rule(opened_safe)));
      add_fact_st(head_nonnegative);
      add_fact_st(tail_nonnegative);
      add_fact_st(sum_upper);
      add_fact_st(eqt_intro_rule(tail_safe));
      add_fact_st(mp_rule(mp_rule(int_arith_rule(
          `0i <= cm_rep_string_size (string_:cm_string_d) ==>
           0i <= cm_rep_strings_size (rest_:(cm_string_d)list) ==>
           0i <= cm_rep_string_size string_ +
             cm_rep_strings_size rest_`),
          head_nonnegative), tail_nonnegative));
      thm head_upper = mp_rule(mp_rule(int_arith_rule(
          `0i <= cm_rep_strings_size
              (rest_:(cm_string_d)list) ==>
           cm_rep_string_size (string_:cm_string_d) +
             cm_rep_strings_size rest_ <= 1048560i ==>
           cm_rep_string_size string_ <= 1048560i`),
          tail_nonnegative), sum_upper);
      thm size_model = inst_rule(TERM_PAIR_LIST(
          (term_pair){`string_:cm_string_d`, `string:cm_string_d`}),
          get_cm_rep_string_size_def());
      add_fact_st(conv_rule(rewrite_conv(THM_LIST(size_model)),
          head_nonnegative));
      add_fact_st(conv_rule(rewrite_conv(THM_LIST(size_model)),
          head_upper));
    }
    if (index == 0) {
      total = 0;
      [[cst::proof]] {
        thm model = by_rewrite(
            `cm_rep_strings_prefix (strings:(cm_string_d)list)
               (index__pre:int) == 0i`,
            THM_LIST(assume_rule(`index__pre == 0i`),
              assume_rule(
                `strings == (string_:cm_string_d) ::
                  (rest_:(cm_string_d)list)`),
              get_cm_rep_strings_prefix_def()));
        add_fact_st(sym_rule(model));
        thm zero_nonnegative = int_arith_rule(`0i <= 0i`);
        thm prefix_nonnegative_eq = mk_binop_rule(
            `(<=):int->int->bool`, refl_rule(`0i:int`), model);
        add_fact_st(eq_mp_rule(sym_rule(prefix_nonnegative_eq),
            zero_nonnegative));
        thm size_model = by_rewrite(
            `cm_rep_strings_size (strings:(cm_string_d)list) ==
             cm_rep_string_size (string_:cm_string_d) +
               cm_rep_strings_size (rest_:(cm_string_d)list)`,
            THM_LIST(assume_rule(
                `strings == (string_:cm_string_d) ::
                  (rest_:(cm_string_d)list)`),
              get_cm_rep_strings_size_def()));
        thm size_nonnegative_eq = mk_binop_rule(
            `(<=):int->int->bool`, refl_rule(`0i:int`), size_model);
        thm size_nonnegative = eq_mp_rule(
            sym_rule(size_nonnegative_eq), assume_rule(
              `0i <= cm_rep_string_size (string_:cm_string_d) +
                cm_rep_strings_size (rest_:(cm_string_d)list)`));
        thm prefix_upper_eq = mk_binop_rule(
            `(<=):int->int->bool`, model,
            refl_rule(`cm_rep_strings_size
              (strings:(cm_string_d)list)`));
        add_fact_st(eq_mp_rule(sym_rule(prefix_upper_eq),
            size_nonnegative));
        cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
            mp_rule(specl_rule(TERM_LIST(`node__pre:addr`,
                `string_:cm_string_d`, `rest_:(cm_string_d)list`,
                `zb_:int`, `zn_:int`), get_cm_string_fold()),
              assume_rule(`~(node__pre == 0i)`))));
      }
    } else {
      long long size = node->length;
      size = size + 1;
      [[cst::proof]] {
        add_fact_st(sym_rule(inst_rule(TERM_PAIR_LIST(
            (term_pair){`string_:cm_string_d`, `string:cm_string_d`}),
            get_cm_rep_string_size_def())));
        cst_set_symbolic_state(retarget_cell64_st(
            cst_get_symbolic_state(), `size__addr:addr`,
            `cm_rep_string_length (string_:cm_string_d) + 1i`,
            `cm_rep_string_size (string_:cm_string_d)`));
      }
      struct cm_string *next = node->next;
      [[cst::proof]] {
        add_data_at_range_st(`index__addr:addr`, `Tint`,
            `index__pre:int`);
      }
      long long rest_size = cmc_strings_prefix(next, index - 1);
      [[cst::proof]] {
        thm result_model = assume_rule(
            `retval == cm_rep_strings_prefix
              (rest_:(cm_string_d)list) ((index__pre:int) - 1i)`);
        thm prefix_nonnegative = conv_rule(
            rewrite_conv(THM_LIST(result_model)),
            assume_rule(`0i <= retval`));
        thm prefix_upper = conv_rule(
            rewrite_conv(THM_LIST(result_model)),
            assume_rule(
              `retval <= cm_rep_strings_size
                (rest_:(cm_string_d)list)`));
        thm combined_nonnegative = mp_rule(mp_rule(int_arith_rule(
            `0i <= cm_rep_string_size (string_:cm_string_d) ==>
             0i <= cm_rep_strings_prefix
               (rest_:(cm_string_d)list) ((index__pre:int) - 1i) ==>
             0i <= cm_rep_string_size string_ +
               cm_rep_strings_prefix rest_ (index__pre - 1i)`),
            assume_rule(`0i <= cm_rep_string_size
              (string_:cm_string_d)`)), prefix_nonnegative);
        thm combined_upper = mp_rule(mp_rule(int_arith_rule(
            `cm_rep_strings_prefix
               (rest_:(cm_string_d)list) ((index__pre:int) - 1i) <=
                 cm_rep_strings_size rest_ ==>
             cm_rep_string_size (string_:cm_string_d) +
               cm_rep_strings_size rest_ <= 1048560i ==>
             cm_rep_string_size string_ +
               cm_rep_strings_prefix rest_ (index__pre - 1i) <=
                 1048560i`),
            prefix_upper), assume_rule(
              `cm_rep_string_size (string_:cm_string_d) +
                 cm_rep_strings_size (rest_:(cm_string_d)list) <=
               1048560i`));
        add_fact_st(prefix_nonnegative);
        add_fact_st(prefix_upper);
        add_fact_st(combined_nonnegative);
        add_fact_st(combined_upper);
        cst_set_symbolic_state(retarget_cell64_st(
            cst_get_symbolic_state(), `rest_size__addr:addr`,
            `retval:int`,
            `cm_rep_strings_prefix
              (rest_:(cm_string_d)list) ((index__pre:int) - 1i)`));
      }
      total = size + rest_size;
      [[cst::proof]] {
        thm model = by_rewrite(
            `cm_rep_string_size (string_:cm_string_d) +
               cm_rep_strings_prefix
                 (rest_:(cm_string_d)list) ((index__pre:int) - 1i) ==
             cm_rep_strings_prefix
               (strings:(cm_string_d)list) index__pre`,
            THM_LIST(assume_rule(`~(index__pre == 0i)`),
              assume_rule(
                `strings == (string_:cm_string_d) ::
                  (rest_:(cm_string_d)list)`),
              get_cm_rep_strings_prefix_def()));
        add_fact_st(model);
        thm combined_nonnegative = assume_rule(
            `0i <= cm_rep_string_size (string_:cm_string_d) +
              cm_rep_strings_prefix
                (rest_:(cm_string_d)list) ((index__pre:int) - 1i)`);
        thm combined_relative = mp_rule(int_arith_rule(
            `cm_rep_strings_prefix
               (rest_:(cm_string_d)list) ((index__pre:int) - 1i) <=
                 cm_rep_strings_size rest_ ==>
             cm_rep_string_size (string_:cm_string_d) +
               cm_rep_strings_prefix rest_ (index__pre - 1i) <=
             cm_rep_string_size string_ + cm_rep_strings_size rest_`),
            assume_rule(
              `cm_rep_strings_prefix
                 (rest_:(cm_string_d)list) ((index__pre:int) - 1i) <=
               cm_rep_strings_size rest_`));
        thm size_model = by_rewrite(
            `cm_rep_strings_size (strings:(cm_string_d)list) ==
             cm_rep_string_size (string_:cm_string_d) +
               cm_rep_strings_size (rest_:(cm_string_d)list)`,
            THM_LIST(assume_rule(
                `strings == (string_:cm_string_d) ::
                  (rest_:(cm_string_d)list)`),
              get_cm_rep_strings_size_def()));
        add_fact_st(conv_rule(rewrite_conv(THM_LIST(model)),
            combined_nonnegative));
        add_fact_st(conv_rule(rewrite_conv(
            THM_LIST(model, sym_rule(size_model))),
            combined_relative));
        cst_set_symbolic_state(retarget_cell64_st(
            cst_get_symbolic_state(), `total__addr:addr`,
            `cm_rep_string_size (string_:cm_string_d) +
              cm_rep_strings_prefix
                (rest_:(cm_string_d)list) ((index__pre:int) - 1i)`,
            `cm_rep_strings_prefix
              (strings:(cm_string_d)list) (index__pre:int)`));
        cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
            mp_rule(specl_rule(TERM_LIST(`node__pre:addr`,
                `string_:cm_string_d`, `rest_:(cm_string_d)list`,
                `zb_:int`, `zn_:int`), get_cm_string_fold()),
              assume_rule(`~(node__pre == 0i)`))));
      }
    }
  }
  return total;
}

long long cmc_global_address(struct cm_global *globals, int index)
    [[cst::param(`items:(cm_global_d)list`)]]
    [[cst::require(`fact(0i <= index) **
      fact(cm_rep_globals_safe items <=> true) **
      cm_global_list_rep globals items`)]]
    [[cst::ensure(`fact(0i <= index) **
      fact(cm_rep_globals_safe items <=> true) **
      cm_global_list_rep globals items **
      fact((__return:int) == cm_rep_global_address items index) **
      fact(16i <= (__return:int)) ** fact((__return:int) <= 1048576i)`)]]
{
  long long prefix = cmc_globals_prefix(globals, index);
  [[cst::proof]] {
    cst_set_symbolic_state(retarget_cell64_st(
        cst_get_symbolic_state(), `prefix__addr:addr`, `retval:int`,
        `cm_rep_globals_prefix
          (items:(cm_global_d)list) (index__pre:int)`));
  }
  long long address = 16LL + prefix;
  [[cst::proof]] {
    thm model = by_rewrite(
        `16i + cm_rep_globals_prefix
            (items:(cm_global_d)list) (index__pre:int) ==
         cm_rep_global_address items index__pre`,
        THM_LIST(get_cm_rep_global_address_def()));
    add_fact_st(model);
    cst_set_symbolic_state(retarget_cell64_st(
        cst_get_symbolic_state(), `address__addr:addr`,
        `16i + cm_rep_globals_prefix
          (items:(cm_global_d)list) (index__pre:int)`,
        `cm_rep_global_address items index__pre`));
  }
  return address;
}

long long cmc_string_address(struct cm_global *globals,
                                    struct cm_string *strings, int index)
    [[cst::param(`global_items:(cm_global_d)list`,
                 `string_items:(cm_string_d)list`)]]
    [[cst::require(`fact(0i <= index) **
      fact(cm_rep_globals_safe global_items <=> true) **
      fact(cm_rep_strings_safe string_items <=> true) **
      fact(cm_rep_globals_size global_items +
        cm_rep_strings_size string_items <= 1048560i) **
      cm_global_list_rep globals global_items **
      cm_string_list_rep strings string_items`)]]
    [[cst::ensure(`fact(0i <= index) **
      fact(cm_rep_globals_safe global_items <=> true) **
      fact(cm_rep_strings_safe string_items <=> true) **
      fact(cm_rep_globals_size global_items +
        cm_rep_strings_size string_items <= 1048560i) **
      cm_global_list_rep globals global_items **
      cm_string_list_rep strings string_items **
      fact((__return:int) ==
        cm_rep_string_address global_items string_items index) **
      fact(16i <= (__return:int)) ** fact((__return:int) <= 1048576i)`)]]
{
  long long global_size = cmc_globals_size(globals);
  [[cst::proof]] {
    cst_set_symbolic_state(retarget_cell64_st(
        cst_get_symbolic_state(), `global_size__addr:addr`,
        `retval:int`,
        `cm_rep_globals_size (global_items:(cm_global_d)list)`));
  }
  long long prefix = cmc_strings_prefix(strings, index);
  [[cst::proof]] {
    thm prefix_model = assume_rule(
        `retval_1 == cm_rep_strings_prefix
          (string_items:(cm_string_d)list) (index__pre:int)`);
    add_fact_st(conv_rule(rewrite_conv(THM_LIST(prefix_model)),
        assume_rule(`retval_1 <=
          cm_rep_strings_size (string_items:(cm_string_d)list)`)));
    thm combined_upper = mp_rule(mp_rule(int_arith_rule(
        `cm_rep_strings_prefix
            (string_items:(cm_string_d)list) (index__pre:int) <=
              cm_rep_strings_size string_items ==>
         cm_rep_globals_size
            (global_items:(cm_global_d)list) +
           cm_rep_strings_size string_items <= 1048560i ==>
         cm_rep_globals_size global_items +
           cm_rep_strings_prefix string_items index__pre <= 1048560i`),
        assume_rule(
          `cm_rep_strings_prefix
             (string_items:(cm_string_d)list) (index__pre:int) <=
           cm_rep_strings_size string_items`)),
        assume_rule(
          `cm_rep_globals_size (global_items:(cm_global_d)list) +
           cm_rep_strings_size (string_items:(cm_string_d)list) <=
             1048560i`));
    add_fact_st(combined_upper);
    cst_set_symbolic_state(retarget_cell64_st(
        cst_get_symbolic_state(), `prefix__addr:addr`,
        `retval_1:int`,
        `cm_rep_strings_prefix string_items index__pre`));
  }
  long long address = 16LL + global_size;
  address = address + prefix;
  [[cst::proof]] {
    thm model = by_defs_arith(
        `(16i + cm_rep_globals_size
            (global_items:(cm_global_d)list)) +
          cm_rep_strings_prefix
            (string_items:(cm_string_d)list) (index__pre:int) ==
         cm_rep_string_address global_items string_items index__pre`,
        THM_LIST(get_cm_rep_string_address_def()), THM_LIST());
    add_fact_st(model);
    cst_set_symbolic_state(retarget_cell64_st(
        cst_get_symbolic_state(), `address__addr:addr`,
        `(16i + cm_rep_globals_size global_items) +
          cm_rep_strings_prefix string_items index__pre`,
        `cm_rep_string_address global_items string_items index__pre`));
  }
  return address;
}

PROOF static thm cm_prove_rep_nonzero_bool(void) {
  gnode root = gnode_new_with_ccl(
      `!(n:int).
         (cm_rep_nonzero n == 1i <=> ~(n == 0i)) &&
         (cm_rep_nonzero n == 0i <=> n == 0i)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      leaf, `(n:int) == 0i`, "Hzero");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_WITH_ASMP_TAC(cases[i], reduce_rewrite_conv, THM_LIST(
        get_cm_rep_nonzero_def()));
  }
  return gnode_prove(root);
}
PROOF thm cm_rep_nonzero_bool =
    cm_prove_rep_nonzero_bool();
PROOF static thm cm_prove_rep_nonzero_value(void) {
  gnode root = gnode_new_with_ccl(
      `!(n:int).
         cm_rep_nonzero n == (if ~(n == 0i) then 1i else 0i)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      leaf, `(n:int) == 0i`, "Hzero");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_WITH_ASMP_TAC(cases[i], reduce_rewrite_conv, THM_LIST(
        get_cm_rep_nonzero_def()));
  }
  return gnode_prove(root);
}
PROOF thm cm_rep_nonzero_value =
    cm_prove_rep_nonzero_value();

PROOF static thm cm_prove_binding_valid_slot_nonnegative(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (f:cm_function_d) scope slot.
         cm_binding_valid p f scope slot ==> 0i <= slot`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list global_cases =
      BOOL_CASES_TAC(leaf, `(scope:int) == 0i`, "Hglobal");
  {
    thm valid = conv_rule(reduce_rewrite_conv(THM_LIST(
        assume_rule(`(scope:int) == 0i`),
        get_cm_binding_valid_def())),
        assume_rule(
          `cm_binding_valid (p:cm_program) (f:cm_function_d)
             (scope:int) (slot:int)`));
    ACCEPT_TAC(global_cases[0], mp_rule(int_arith_rule(
        mk_imp(concl(valid), `0i <= (slot:int)`)), valid));
  }
  {
    gnode_list local_cases = BOOL_CASES_TAC(
        global_cases[1], `(scope:int) == 1i`, "Hlocal");
    thm local_valid = conv_rule(reduce_rewrite_conv(THM_LIST(
        assume_rule(`~((scope:int) == 0i)`),
        assume_rule(`(scope:int) == 1i`),
        get_cm_binding_valid_def())),
        assume_rule(
          `cm_binding_valid (p:cm_program) (f:cm_function_d)
             (scope:int) (slot:int)`));
    ACCEPT_TAC(local_cases[0], mp_rule(int_arith_rule(
        mk_imp(concl(local_valid), `0i <= (slot:int)`)),
        local_valid));
    thm param_valid = conv_rule(reduce_rewrite_conv(THM_LIST(
        assume_rule(`~((scope:int) == 0i)`),
        assume_rule(`~((scope:int) == 1i)`),
        get_cm_binding_valid_def())),
        assume_rule(
          `cm_binding_valid (p:cm_program) (f:cm_function_d)
             (scope:int) (slot:int)`));
    ACCEPT_TAC(local_cases[1], mp_rule(int_arith_rule(
        mk_imp(concl(param_valid), `0i <= (slot:int)`)),
        param_valid));
  }
  return gnode_prove(root);
}
PROOF thm cm_binding_valid_slot_nonnegative =
    cm_prove_binding_valid_slot_nonnegative();

PROOF static thm cm_prove_nonnegative_i32_cast(void) {
  gnode root = gnode_new_with_ccl(
      `!(x:int).
         0i <= x ==> x <= 2147483647i ==>
         signed_last_nbits x 32i == x`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm low = assume_rule(`0i <= (x:int)`);
  thm high = assume_rule(`(x:int) <= 2147483647i`);
  thm exp32 = spec_rule(
      `32i:int`, get_theorem_by_name("INT_EXP_2_DEF"));
  exp32 = rewrite_rule(THM_LIST(spec_rule(
      `32:num`, get_theorem_by_name("NUM_OF_INT_OF_NUM"))), exp32);
  exp32 = rewrite_rule(THM_LIST(apply_conversion(
      get_conversion_by_name("NUM_REDUCE_CONV"), `2 EXP 32`)), exp32);
  thm exp31 = spec_rule(
      `31i:int`, get_theorem_by_name("INT_EXP_2_DEF"));
  exp31 = rewrite_rule(THM_LIST(spec_rule(
      `31:num`, get_theorem_by_name("NUM_OF_INT_OF_NUM"))), exp31);
  exp31 = rewrite_rule(THM_LIST(apply_conversion(
      get_conversion_by_name("NUM_REDUCE_CONV"), `2 EXP 31`)), exp31);
  thm unsigned_id = specl_rule(TERM_LIST(
      `x:int`, `32i:int`),
      get_theorem_by_name("unsigned_last_nbits_id"));
  unsigned_id = conv_rule(
      rewrite_conv(THM_LIST(exp32)), unsigned_id);
  unsigned_id = mp_rule(unsigned_id, mp_rule(mp_rule(int_arith_rule(
      `0i <= (x:int) ==> x <= 2147483647i ==>
       0i <= x && x < 4294967296i`), low), high));
  thm x_below_sign = mp_rule(mp_rule(int_arith_rule(
      `0i <= (x:int) ==> x <= 2147483647i ==>
       x < 2147483648i`), low), high);
  thm x_below_exp = eq_mp_rule(sym_rule(beta_norm(ap_term_rule(
      `\bound:int. (x:int) < bound`, exp31))), x_below_sign);
  thm signed_open = apply_conversion(rewrite_conv(THM_LIST(
      get_theorem_by_name("signed_last_nbits_def"))),
      `signed_last_nbits (x:int) 32i`);
  thm cast_open = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_theorem_by_name("cast_signed_def"),
      gsym_rule(get_theorem_by_name("unsigned_last_nbits_def")),
      unsigned_id, exp32, exp31)),
      `cast_signed 32i (x:int)`);
  thm choose_true = conv_rule(reduce_rewrite_conv(THM_LIST()),
      beta_norm(ap_term_rule(
        `\b:bool. if b then (x:int) else x - 4294967296i`,
        eqt_intro_rule(x_below_exp))));
  ACCEPT_TAC(leaf, trans_rule(
      trans_rule(signed_open, cast_open), choose_true));
  return gnode_prove(root);
}
PROOF thm cm_nonnegative_i32_cast =
    cm_prove_nonnegative_i32_cast();


PROOF static thm cm_prove_binding_array_code_cases(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) fid scope slot.
         (cm_binding_array_code p fid scope slot == 0i <=>
          ~cm_binding_array p fid scope slot) &&
         (~(cm_binding_array_code p fid scope slot == 0i) <=>
          cm_binding_array p fid scope slot)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(leaf,
      `cm_binding_array (p:cm_program) (fid:int)
         (scope:int) (slot:int)`, "Harray");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_WITH_ASMP_TAC(cases[i], reduce_rewrite_conv,
        THM_LIST(cm_binding_array_code_def));
  }
  return gnode_prove(root);
}
PROOF thm cm_binding_array_code_cases =
    cm_prove_binding_array_code_cases();


PROOF static thm cm_prove_binding_array_bridge(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (f:cm_function_d) fid
         (globals:(cm_global_d)list) (locals:(cm_slot_d)list)
         scope slot.
         globals == cm_program_globals p ==>
         locals == cm_function_locals f ==>
         f == inth fid (cm_program_functions p) ==>
         cm_binding_valid p f scope slot ==>
         cm_rep_binding_array globals locals scope slot ==
           cm_binding_array_code p fid scope slot`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list global_cases =
      BOOL_CASES_TAC(leaf, `(scope:int) == 0i`, "Hglobal");
  {
    thm valid = conv_rule(reduce_rewrite_conv(THM_LIST(
        assume_rule(`(scope:int) == 0i`),
        sym_rule(assume_rule(
          `globals == cm_program_globals (p:cm_program)`)),
        get_cm_binding_valid_def())),
        assume_rule(
          `cm_binding_valid (p:cm_program) (f:cm_function_d)
             (scope:int) (slot:int)`));
    thm lookup = mp_rule(mp_rule(specl_rule(TERM_LIST(
        `globals:(cm_global_d)list`, `slot:int`),
        get_cm_rep_global_array_at()),
        conjunct1_rule(valid)), conjunct2_rule(valid));
    gnode global_done = CONV_WITH_ASMP_TAC(
        global_cases[0], reduce_rewrite_conv, THM_LIST(
          lookup, get_cm_rep_binding_array_def(),
          cm_rep_nonzero_value, cm_binding_array_code_def,
          get_cm_binding_array_def()));
    ENSURE_COND(!IS_NULL(global_done->solved),
        "global binding bridge remains open: %s",
        cstr_gnode(global_done));
  }
  {
    gnode_list local_cases = BOOL_CASES_TAC(
        global_cases[1], `(scope:int) == 1i`, "Hlocal");
    {
      thm valid = conv_rule(reduce_rewrite_conv(THM_LIST(
          assume_rule(`~((scope:int) == 0i)`),
          assume_rule(`(scope:int) == 1i`),
          sym_rule(assume_rule(
            `locals == cm_function_locals (f:cm_function_d)`)),
          get_cm_binding_valid_def())),
          assume_rule(
            `cm_binding_valid (p:cm_program) (f:cm_function_d)
               (scope:int) (slot:int)`));
      thm lookup = mp_rule(mp_rule(specl_rule(TERM_LIST(
          `locals:(cm_slot_d)list`, `slot:int`),
          get_cm_rep_member_array_at()),
          conjunct1_rule(valid)), conjunct2_rule(valid));
      gnode local_done = CONV_WITH_ASMP_TAC(
          local_cases[0], reduce_rewrite_conv, THM_LIST(
            lookup, get_cm_rep_binding_array_def(),
            cm_rep_nonzero_value, cm_binding_array_code_def,
            get_cm_binding_array_def()));
      ENSURE_COND(!IS_NULL(local_done->solved),
          "local binding bridge remains open: %s",
          cstr_gnode(local_done));
    }
    gnode param_done = CONV_WITH_ASMP_TAC(
        local_cases[1], reduce_rewrite_conv, THM_LIST(
          get_cm_rep_binding_array_def(), cm_binding_array_code_def,
          get_cm_binding_array_def()));
    ENSURE_COND(!IS_NULL(param_done->solved),
        "parameter binding bridge remains open: %s",
        cstr_gnode(param_done));
  }
  return gnode_prove(root);
err:
  return empty_theorem;
}
PROOF thm cm_binding_array_bridge =
    cm_prove_binding_array_bridge();

void cmc_binding_array_value(struct cm_program *program, int fid,
                                    struct cm_function *fn,
                                    int scope, int slot, int *array)
    [[cst::param(`p:cm_program`, `f:cm_function_d`,
                 `globals:(cm_global_d)list`,
                 `locals:(cm_slot_d)list`, `zg:int`, `zl:int`)]]
    [[cst::require(
      `fact(0i <= slot) **
       fact(globals == cm_program_globals p) **
       fact(locals == cm_function_locals f) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_binding_valid p f scope slot <=> true) **
       data_at (field_addr program Tcm_program Fglobals) Tptr zg **
       cm_global_list_rep zg globals **
       data_at (field_addr fn Tcm_function Flocals) Tptr zl **
       cm_slot_list_rep zl locals **
       undef_data_at array Tint`)]]
    [[cst::ensure(
      `fact(0i <= slot) **
       fact(globals == cm_program_globals p) **
       fact(locals == cm_function_locals f) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_binding_valid p f scope slot <=> true) **
       data_at (field_addr program Tcm_program Fglobals) Tptr zg **
       cm_global_list_rep zg globals **
       data_at (field_addr fn Tcm_function Flocals) Tptr zl **
       cm_slot_list_rep zl locals **
       data_at array Tint
         (cm_binding_array_code p fid scope slot)`)]]
{
  int result;
  if (scope == CMC_BIND_GLOBAL) {
    result = cmc_global_array_at(program->globals, slot);
    [[cst::proof]] {
      thm model = by_rewrite(
          `cm_rep_global_array (globals:(cm_global_d)list)
              (slot__pre:int) ==
           cm_rep_binding_array globals
             (locals:(cm_slot_d)list) (scope__pre:int) slot__pre`,
          THM_LIST(assume_rule(`scope__pre == 0i`),
            get_cm_rep_binding_array_def()));
      add_fact_st(trans_rule(assume_rule(
          `retval == cm_rep_global_array
            (globals:(cm_global_d)list) (slot__pre:int)`), model));
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `result__addr:addr`, `retval:int`,
          `cm_rep_binding_array globals locals scope__pre slot__pre`));
    }
  } else if (scope == CMC_BIND_LOCAL) {
    result = cmc_slot_array_at(fn->locals, slot);
    [[cst::proof]] {
      thm model = by_rewrite(
          `cm_rep_member_array (locals:(cm_slot_d)list)
              (slot__pre:int) ==
           cm_rep_binding_array
             (globals:(cm_global_d)list) locals
             (scope__pre:int) slot__pre`,
          THM_LIST(assume_rule(`~(scope__pre == 0i)`),
            assume_rule(`scope__pre == 1i`),
            get_cm_rep_binding_array_def()));
      add_fact_st(trans_rule(assume_rule(
          `retval == cm_rep_member_array
            (locals:(cm_slot_d)list) (slot__pre:int)`), model));
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `result__addr:addr`, `retval:int`,
          `cm_rep_binding_array globals locals scope__pre slot__pre`));
    }
  } else {
    result = 0;
    [[cst::proof]] {
      thm zero_model = sym_rule(by_rewrite(
          `cm_rep_binding_array
             (globals:(cm_global_d)list) (locals:(cm_slot_d)list)
             (scope__pre:int) (slot__pre:int) == 0i`,
          THM_LIST(assume_rule(`~(scope__pre == 0i)`),
            assume_rule(`~(scope__pre == 1i)`),
            get_cm_rep_binding_array_def())));
      add_fact_st(zero_model);
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `result__addr:addr`, `0i`,
          `cm_rep_binding_array globals locals scope__pre slot__pre`));
    }
  }
  [[cst::proof]] {
    thm bridge = specl_rule(TERM_LIST(
        `p:cm_program`, `f:cm_function_d`, `fid__pre:int`,
        `globals:(cm_global_d)list`, `locals:(cm_slot_d)list`,
        `scope__pre:int`, `slot__pre:int`),
        cm_binding_array_bridge);
    bridge = mp_rule(bridge, assume_rule(
        `globals == cm_program_globals (p:cm_program)`));
    bridge = mp_rule(bridge, assume_rule(
        `locals == cm_function_locals (f:cm_function_d)`));
    bridge = mp_rule(bridge, assume_rule(
        `(f:cm_function_d) ==
          inth (fid__pre:int) (cm_program_functions p)`));
    bridge = mp_rule(bridge, from_state_bool(
        `cm_binding_valid (p:cm_program) (f:cm_function_d)
          (scope__pre:int) (slot__pre:int)`));
    add_fact_st(bridge);
    substitute_fact_st(
        `cm_rep_binding_array
           (globals:(cm_global_d)list) (locals:(cm_slot_d)list)
           (scope__pre:int) (slot__pre:int) ==
         cm_binding_array_code (p:cm_program) (fid__pre:int)
           scope__pre slot__pre`);
  }
  *array = result;
}

int cmc_binding_array(struct cm_program *program, int fid,
                             struct cm_function *fn,
                             int scope, int slot)
    [[cst::param(`p:cm_program`, `f:cm_function_d`,
                 `globals:(cm_global_d)list`,
                 `locals:(cm_slot_d)list`, `zg:int`, `zl:int`)]]
    [[cst::require(
      `fact(0i <= slot) **
       fact(globals == cm_program_globals p) **
       fact(locals == cm_function_locals f) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_binding_valid p f scope slot <=> true) **
       data_at (field_addr program Tcm_program Fglobals) Tptr zg **
       cm_global_list_rep zg globals **
       data_at (field_addr fn Tcm_function Flocals) Tptr zl **
       cm_slot_list_rep zl locals`)]]
    [[cst::ensure(
      `fact(0i <= slot) **
       fact(globals == cm_program_globals p) **
       fact(locals == cm_function_locals f) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_binding_valid p f scope slot <=> true) **
       data_at (field_addr program Tcm_program Fglobals) Tptr zg **
       cm_global_list_rep zg globals **
       data_at (field_addr fn Tcm_function Flocals) Tptr zl **
       cm_slot_list_rep zl locals **
       fact((__return:int) ==
         cm_binding_array_code p fid scope slot)`)]]
{
  int result;
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`f`, `(f:cm_function_d)`)]]
  [[cst::where(`globals`, `globals:(cm_global_d)list`)]]
  [[cst::where(`locals`, `locals:(cm_slot_d)list`)]]
  [[cst::where(`zg`, `(zg:int)`)]]
  [[cst::where(`zl`, `(zl:int)`)]]
  cmc_binding_array_value(program, fid, fn, scope, slot, &result);
  return result;
}

PROOF static thm cm_prove_struct_base_code(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type).
         cm_is_struct ty ==>
         cm_type_base_code ty == cm_struct_id ty + 2i`);
  gnode_list cases = INDUCT_TAC(root, `ty:cm_type`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_TAC(cases[i], reduce_rewrite_conv(THM_LIST(
        get_cm_is_struct_def(), get_cm_type_base_code_def(),
        get_cm_struct_id_def())));
  }
  return gnode_prove(root);
}
PROOF thm cm_struct_base_code =
    cm_prove_struct_base_code();

PROOF static thm cm_prove_pointer_base_code(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type).
         cm_is_pointer ty ==>
         cm_type_base_code ty == cm_type_base_code (cm_pointee ty)`);
  gnode_list cases = INDUCT_TAC(root, `ty:cm_type`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_TAC(cases[i], reduce_rewrite_conv(THM_LIST(
        get_cm_is_pointer_def(), get_cm_type_base_code_def(),
        get_cm_pointee_def())));
  }
  return gnode_prove(root);
}
PROOF thm cm_pointer_base_code =
    cm_prove_pointer_base_code();

PROOF static thm cm_prove_encoded_member_sid(void) {
  gnode root = gnode_new_with_ccl(
      `!(base:cm_type).
         cm_type_code_wf base ==>
         cm_is_pointer base ==>
         cm_is_struct (cm_pointee base) ==>
         ((cm_type_encode base - 1024i) rem 1024i) - 2i ==
           cm_struct_id (cm_pointee base)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm type_wf = assume_rule(`cm_type_code_wf (base:cm_type)`);
  thm pointer = assume_rule(`cm_is_pointer (base:cm_type)`);
  thm structure =
      assume_rule(`cm_is_struct (cm_pointee (base:cm_type))`);
  thm divmod = mp_rule(spec_rule(
      `base:cm_type`, get_cm_type_encode_divmod()), type_wf);
  thm pointer_base = mp_rule(spec_rule(
      `base:cm_type`, cm_pointer_base_code), pointer);
  thm struct_base = mp_rule(spec_rule(
      `cm_pointee (base:cm_type)`, cm_struct_base_code), structure);
  thm shift_arg = int_ring_rule(
      `cm_type_encode (base:cm_type) - 1024i ==
       (--1i) * 1024i + cm_type_encode base`);
  thm shift_lift = beta_norm(ap_term_rule(
      `\z:int. z % 1024i`, shift_arg));
  thm rem_mul = specl_rule(TERM_LIST(
      `--1i`, `1024i`, `cm_type_encode (base:cm_type)`),
      conjunct1_rule(get_theorem_by_name("INT_REM_MUL_ADD")));
  thm shifted = trans_rule(shift_lift, rem_mul);
  thm result = mp_rule(mp_rule(mp_rule(mp_rule(int_arith_rule(
      `((cm_type_encode (base:cm_type) - 1024i) % 1024i ==
          cm_type_encode base % 1024i) ==>
       (cm_type_encode base % 1024i == cm_type_base_code base) ==>
       (cm_type_base_code base ==
          cm_type_base_code (cm_pointee base)) ==>
       (cm_type_base_code (cm_pointee base) ==
          cm_struct_id (cm_pointee base) + 2i) ==>
       ((cm_type_encode base - 1024i) % 1024i) - 2i ==
          cm_struct_id (cm_pointee base)`),
      shifted), conjunct2_rule(divmod)), pointer_base), struct_base);
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_encoded_member_sid =
    cm_prove_encoded_member_sid();


PROOF static thm cm_prove_member_array_code_cases(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (base:cm_type) (mid:int).
         ((cm_member_array_code p base mid == 0i <=>
            ~cm_member_array p base mid) &&
          (~(cm_member_array_code p base mid == 0i) <=>
            cm_member_array p base mid))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      leaf, `cm_member_array (p:cm_program)
        (base:cm_type) (mid:int)`, "Harray");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_WITH_ASMP_TAC(cases[i], reduce_rewrite_conv,
        THM_LIST(cm_member_array_code_def));
  }
  return gnode_prove(root);
}
PROOF thm cm_member_array_code_cases =
    cm_prove_member_array_code_cases();

PROOF static thm cm_prove_member_array_bridge(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (base:cm_type)
         (structs:(cm_struct_d)list) base_ty mid.
         structs == cm_program_structs p ==>
         base_ty == cm_type_encode base ==>
         cm_type_code_wf base ==>
         cm_member_valid p base mid ==>
         cm_rep_member_array_code structs base_ty mid ==
           cm_member_array_code p base mid`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm structs_eq = assume_rule(
      `structs == cm_program_structs (p:cm_program)`);
  thm code_eq = assume_rule(
      `(base_ty:int) == cm_type_encode (base:cm_type)`);
  thm type_wf = assume_rule(`cm_type_code_wf (base:cm_type)`);
  thm valid = conv_rule(rewrite_conv(THM_LIST(
      get_cm_member_valid_def())), assume_rule(
        `cm_member_valid (p:cm_program) (base:cm_type) (mid:int)`));
  thm pointer = conjunct1_rule(valid);
  thm rest = conjunct2_rule(valid);
  thm structure = conjunct1_rule(rest);
  rest = conjunct2_rule(rest);
  thm sid_nonnegative = conjunct1_rule(rest);
  rest = conjunct2_rule(rest);
  thm sid_upper = conjunct1_rule(rest);
  rest = conjunct2_rule(rest);
  thm mid_nonnegative = conjunct1_rule(rest);
  thm mid_upper = conjunct2_rule(rest);
  thm sid_eq = match_mp_rule(match_mp_rule(match_mp_rule(
      spec_rule(`base:cm_type`, cm_encoded_member_sid),
      type_wf), pointer), structure);
  thm sid_nonnegative_rep = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(structs_eq))), sid_nonnegative);
  thm sid_upper_rep = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(structs_eq))), sid_upper);
  thm mid_upper_rep = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(structs_eq))), mid_upper);
  thm member = specl_rule(TERM_LIST(
      `structs:(cm_struct_d)list`,
      `cm_struct_id (cm_pointee (base:cm_type))`, `mid:int`),
      get_cm_rep_struct_member_array_at());
  member = mp_rule(member, sid_nonnegative_rep);
  member = mp_rule(member, sid_upper_rep);
  member = mp_rule(member, mid_nonnegative);
  member = mp_rule(member, mid_upper_rep);
  thm opened_rep = by_rewrite(
      `cm_rep_member_array_code (structs:(cm_struct_d)list)
          (base_ty:int) (mid:int) ==
       cm_rep_struct_member_array structs
         (cm_struct_id (cm_pointee (base:cm_type))) mid`,
      THM_LIST(code_eq, sid_eq, get_cm_rep_member_array_code_def()));
  thm model = by_rewrite(
      `cm_rep_nonzero
          (cm_slot_count
            (inth (mid:int)
              (cm_struct_members
                (inth (cm_struct_id (cm_pointee (base:cm_type)))
                  (structs:(cm_struct_d)list))))) ==
       cm_member_array_code (p:cm_program) base mid`,
      THM_LIST(structs_eq, cm_rep_nonzero_value,
        cm_member_array_code_def, get_cm_member_array_def()));
  ACCEPT_TAC(leaf, trans_rule(opened_rep, trans_rule(member, model)));
  return gnode_prove(root);
}
PROOF thm cm_member_array_bridge =
    cm_prove_member_array_bridge();

int cmc_member_array(struct cm_program *program, int base_ty, int mid)
    [[cst::param(`p:cm_program`, `base:cm_type`,
                 `structs:(cm_struct_d)list`, `zs:int`)]]
    [[cst::require(
      `fact(1024i <= base_ty) **
       fact(base_ty <= 2147483647i) **
       fact(0i <= ((base_ty - 1024i) rem 1024i) - 2i) **
       fact(0i <= mid) **
       fact(structs == cm_program_structs p) **
       fact(base_ty == cm_type_encode base) **
       fact(cm_type_code_wf base <=> true) **
       fact(cm_member_valid p base mid <=> true) **
       fact(cm_rep_structs_safe structs <=> true) **
       data_at (field_addr program Tcm_program Fstructs) Tptr zs **
       cm_struct_list_rep zs structs`)]]
    [[cst::ensure(
      `fact(1024i <= base_ty) **
       fact(base_ty <= 2147483647i) **
       fact(0i <= ((base_ty - 1024i) rem 1024i) - 2i) **
       fact(0i <= mid) **
       fact(structs == cm_program_structs p) **
       fact(base_ty == cm_type_encode base) **
       fact(cm_type_code_wf base <=> true) **
       fact(cm_member_valid p base mid <=> true) **
       fact(cm_rep_structs_safe structs <=> true) **
       data_at (field_addr program Tcm_program Fstructs) Tptr zs **
       cm_struct_list_rep zs structs **
       fact((__return:int) == cm_member_array_code p base mid)`)]]
{
  int pointee = cmc_pointee(base_ty);
  [[cst::proof]] {
    thm nz = int_arith_rule(`~((1024i:int) == 0i)`);
    thm pos = mp_rule(specl_rule(
        TERM_LIST(`retval:int`, `1024i`),
        get_theorem_by_name("INT_REM_POS")), nz);
    thm lt = mp_rule(specl_rule(
        TERM_LIST(`retval:int`, `1024i`),
        get_theorem_by_name("INT_LT_REM")),
        int_arith_rule(`(0i:int) < 1024i`));
    add_fact_st(pos);
    add_fact_st(lt);
    add_fact_st(beta_norm(ap_term_rule(`\z:int. z % 1024i`,
        assume_rule(`retval == (base_ty__pre:int) - 1024i`))));
    cst_set_symbolic_state(retarget_cell_st(
        cst_get_symbolic_state(), `pointee__addr:addr`, `retval:int`,
        `(base_ty__pre:int) - 1024i`));
  }
  int sid = (pointee % 1024) - 2;
  int result = cmc_struct_member_array_at(program->structs, sid, mid);
  [[cst::proof]] {
    thm model = by_rewrite(
        `cm_rep_struct_member_array
            (structs:(cm_struct_d)list)
            (((base_ty__pre:int) - 1024i) % 1024i - 2i)
            (mid__pre:int) ==
         cm_rep_member_array_code structs base_ty__pre mid__pre`,
        THM_LIST(get_cm_rep_member_array_code_def()));
    add_fact_st(trans_rule(assume_rule(
        `retval_1 == cm_rep_struct_member_array
          (structs:(cm_struct_d)list)
          (((base_ty__pre:int) - 1024i) % 1024i - 2i)
          (mid__pre:int)`), model));
    cst_set_symbolic_state(retarget_cell_st(
        cst_get_symbolic_state(), `result__addr:addr`, `retval_1:int`,
        `cm_rep_member_array_code structs base_ty__pre mid__pre`));
  }
  [[cst::proof]] {
    thm bridge = specl_rule(TERM_LIST(
        `p:cm_program`, `base:cm_type`,
        `structs:(cm_struct_d)list`, `base_ty__pre:int`,
        `mid__pre:int`), cm_member_array_bridge);
    bridge = mp_rule(bridge, assume_rule(
        `structs == cm_program_structs (p:cm_program)`));
    bridge = mp_rule(bridge, assume_rule(
        `base_ty__pre == cm_type_encode (base:cm_type)`));
    bridge = mp_rule(bridge, from_state_bool(
        `cm_type_code_wf (base:cm_type)`));
    bridge = mp_rule(bridge, from_state_bool(
        `cm_member_valid (p:cm_program) (base:cm_type)
          (mid__pre:int)`));
    add_fact_st(bridge);
  }
  return result;
}

void cmc_member_array_value(struct cm_program *program,
                                   int base_ty, int mid, int *array)
    [[cst::param(`p:cm_program`, `base:cm_type`,
                 `structs:(cm_struct_d)list`, `zs:int`)]]
    [[cst::require(
      `fact(1024i <= base_ty) **
       fact(base_ty <= 2147483647i) **
       fact(0i <= ((base_ty - 1024i) rem 1024i) - 2i) **
       fact(0i <= mid) **
       fact(structs == cm_program_structs p) **
       fact(base_ty == cm_type_encode base) **
       fact(cm_type_code_wf base <=> true) **
       fact(cm_member_valid p base mid <=> true) **
       fact(cm_rep_structs_safe structs <=> true) **
       data_at (field_addr program Tcm_program Fstructs) Tptr zs **
       cm_struct_list_rep zs structs **
       undef_data_at array Tint`)]]
    [[cst::ensure(
      `fact(1024i <= base_ty) **
       fact(base_ty <= 2147483647i) **
       fact(0i <= ((base_ty - 1024i) rem 1024i) - 2i) **
       fact(0i <= mid) **
       fact(structs == cm_program_structs p) **
       fact(base_ty == cm_type_encode base) **
       fact(cm_type_code_wf base <=> true) **
       fact(cm_member_valid p base mid <=> true) **
       fact(cm_rep_structs_safe structs <=> true) **
       data_at (field_addr program Tcm_program Fstructs) Tptr zs **
       cm_struct_list_rep zs structs **
       data_at array Tint
         (cm_member_array_code p base mid)`)]]
{
  int result;
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`base`, `(base:cm_type)`)]]
  [[cst::where(`structs`, `structs:(cm_struct_d)list`)]]
  [[cst::where(`zs`, `(zs:int)`)]]
  result = cmc_member_array(program, base_ty, mid);
  [[cst::proof]] {
    substitute_fact_st(
        `retval ==
         cm_member_array_code (p:cm_program)
           (base:cm_type) (mid__pre:int)`);
  }
  *array = result;
}

static void cm_expr_temps(struct cm_expr *expr,
                          int *lvalue, int *rvalue)
    [[cst::param(`e:cm_expr`)]]
    [[cst::require(
      `fact(cm_rep_expr_temps_safe e <=> true) **
       cm_expr_rep expr e **
       undef_data_at lvalue Tint **
       undef_data_at rvalue Tint`)]]
    [[cst::ensure(
      `fact(cm_rep_expr_temps_safe e <=> true) **
       cm_expr_rep expr e **
       data_at lvalue Tint (cm_tleft (cm_expr_tpair e)) **
       data_at rvalue Tint (cm_tright (cm_expr_tpair e))`)]];
int cm_args_length(struct cm_arg *arg)
    [[cst::param(`args:(cm_expr)list`)]]
    [[cst::require(`fact(cm_rep_args_safe args <=> true) **
      cm_arg_list_rep arg args`)]]
    [[cst::ensure(`fact(cm_rep_args_safe args <=> true) **
      cm_arg_list_rep arg args **
      fact((__return:int) == cm_rep_args_length args)`)]]
{
  int count;
  if (arg == 0) {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`arg__pre:addr`, `args:(cm_expr)list`),
              get_cm_arg_null()),
            assume_rule(`arg__pre == 0i`))));
      add_fact_st(sym_rule(by_rewrite(
          `cm_rep_args_length (args:(cm_expr)list) == 0i`,
          THM_LIST(assume_rule(
              `args == ([]:(cm_expr)list)`),
            get_cm_rep_args_length_def()))));
      thm nil_view = by_rewrite(
          `cm_arg_list_rep (arg__pre:int)
              ([]:(cm_expr)list) -|-
           fact(arg__pre == 0i)`,
          THM_LIST(get_cm_arg_list_rep_def(),
            get_cm_expr_payload_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(nil_view))));
    }
    count = 0;
  } else {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`arg__pre:addr`, `args:(cm_expr)list`),
              get_cm_arg_unfold()),
            assume_rule(`~(arg__pre == 0i)`))));
      thm safe = from_state_bool(
          `cm_rep_args_safe (args:(cm_expr)list)`);
      thm opened_safe = conv_rule(rewrite_conv(THM_LIST(
          assume_rule(
            `args == (arg_:cm_expr) ::
              (rest_:(cm_expr)list)`),
          get_cm_rep_args_safe_def())), safe);
      add_fact_st(conjunct1_rule(opened_safe));
      add_fact_st(
          conjunct1_rule(conjunct2_rule(opened_safe)));
      add_fact_st(eqt_intro_rule(
          conjunct2_rule(conjunct2_rule(opened_safe))));
    }
    count = cm_args_length(arg->next);
    count = count + 1;
    [[cst::proof]] {
      thm model = by_rewrite(
          `cm_rep_args_length
              ((arg_:cm_expr) :: (rest_:(cm_expr)list)) ==
           1i + cm_rep_args_length rest_`,
          THM_LIST(get_cm_rep_args_length_def()));
      thm original = sym_rule(trans_rule(
          beta_norm(ap_term_rule(
            `\xs:(cm_expr)list. cm_rep_args_length xs`,
            assume_rule(
              `args == (arg_:cm_expr) ::
                (rest_:(cm_expr)list)`))),
          model));
      thm result_model = trans_rule(
          mp_rule(int_arith_rule(
              `retval == cm_rep_args_length
                 (rest_:(cm_expr)list) ==>
               retval + 1i ==
                 1i + cm_rep_args_length rest_`),
            assume_rule(
              `retval == cm_rep_args_length
                (rest_:(cm_expr)list)`)),
          original);
      add_fact_st(result_model);
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `count__addr:addr`,
          `retval + 1i`, `cm_rep_args_length args`));
      thm expr_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`ze_:int`, `p:int`},
          (term_pair){`arg_:cm_expr`, `e:cm_expr`}),
          get_cm_expr_rep_def());
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(expr_view)));
      thm tail_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`zn_:int`, `p:int`},
          (term_pair){`rest_:(cm_expr)list`,
                      `args:(cm_expr)list`}),
          get_cm_arg_list_rep_def());
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(tail_view)));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(TERM_LIST(`arg__pre:addr`,
              `arg_:cm_expr`, `rest_:(cm_expr)list`,
              `ze_:int`, `zn_:int`), get_cm_arg_fold()),
            assume_rule(`~(arg__pre == 0i)`))));
    }
  }
  return count;
}


static void cmc_args_tpair(struct cm_arg *arg, int *count, int *depth)
    [[cst::param(`args:(cm_expr)list`)]]
    [[cst::require(
      `fact(cm_rep_args_temps_safe args <=> true) **
       cm_arg_list_rep arg args **
       undef_data_at count Tint **
       undef_data_at depth Tint`)]]
    [[cst::ensure(
      `fact(cm_rep_args_temps_safe args <=> true) **
       cm_arg_list_rep arg args **
       data_at count Tint (cm_acount (cm_args_apair args)) **
       data_at depth Tint (cm_adepth (cm_args_apair args))`)]]
{
  if (arg == 0) {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`arg__pre:addr`, `args:(cm_expr)list`),
              get_cm_arg_null()),
            assume_rule(`arg__pre == 0i`))));
      add_fact_st(sym_rule(by_rewrite(
          `cm_acount (cm_args_apair (args:(cm_expr)list)) == 0i`,
          THM_LIST(assume_rule(
              `args == ([]:(cm_expr)list)`),
            get_cm_expr_tpair_def(), get_cm_acount_def()))));
      add_fact_st(sym_rule(by_rewrite(
          `cm_adepth (cm_args_apair (args:(cm_expr)list)) == 0i`,
          THM_LIST(assume_rule(
              `args == ([]:(cm_expr)list)`),
            get_cm_expr_tpair_def(), get_cm_adepth_def()))));
      thm nil_view = by_rewrite(
          `cm_arg_list_rep (arg__pre:int)
              ([]:(cm_expr)list) -|-
           fact(arg__pre == 0i)`,
          THM_LIST(get_cm_arg_list_rep_def(),
            get_cm_expr_payload_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(nil_view))));
    }
    *count = 0;
    *depth = 0;
  } else {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`arg__pre:addr`, `args:(cm_expr)list`),
              get_cm_arg_unfold()),
            assume_rule(`~(arg__pre == 0i)`))));
      thm safe = from_state_bool(
          `cm_rep_args_temps_safe (args:(cm_expr)list)`);
      thm opened_safe = conv_rule(rewrite_conv(THM_LIST(
          assume_rule(
            `args == (arg_:cm_expr) ::
              (rest_:(cm_expr)list)`),
          get_cm_rep_expr_temps_safe_def())), safe);
      thm pair_safe = conjunct1_rule(opened_safe);
      add_fact_st(eqt_intro_rule(pair_safe));
      thm pair_bounds = conv_rule(rewrite_conv(THM_LIST(
          get_cm_rep_apair_safe_def(), get_cm_expr_tpair_def(),
          get_cm_acount_def())), pair_safe);
      add_fact_st(conjunct1_rule(pair_bounds));
      thm safe_tail = conjunct2_rule(opened_safe);
      add_fact_st(conjunct1_rule(safe_tail));
      safe_tail = conjunct2_rule(safe_tail);
      add_fact_st(eqt_intro_rule(conjunct1_rule(safe_tail)));
      add_fact_st(eqt_intro_rule(conjunct2_rule(safe_tail)));
    }
    struct cm_expr *child = arg->expr;
    int child_lvalue;
    int child_rvalue;
    cm_expr_temps(child, &child_lvalue, &child_rvalue);
    int rest_count;
    int rest_depth;
    cmc_args_tpair(arg->next, &rest_count, &rest_depth);
    int new_count = rest_count + 1;
    int new_depth = cm_max(child_rvalue, rest_depth);
    [[cst::proof]] {
      thm count_model = by_rewrite(
          `cm_acount (cm_args_apair (args:(cm_expr)list)) ==
           1i + cm_acount (cm_args_apair
             (rest_:(cm_expr)list))`,
          THM_LIST(assume_rule(
              `args == (arg_:cm_expr) :: rest_`),
            get_cm_expr_tpair_def(), get_cm_acount_def()));
      thm count_value = trans_rule(
          int_arith_rule(
            `cm_acount (cm_args_apair
               (rest_:(cm_expr)list)) + 1i ==
             1i + cm_acount (cm_args_apair rest_)`),
          sym_rule(count_model));
      add_fact_st(count_value);
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `new_count__addr:addr`,
          `cm_acount (cm_args_apair
             (rest_:(cm_expr)list)) + 1i`,
          `cm_acount (cm_args_apair args)`));
      thm depth_model = by_rewrite(
          `cm_adepth (cm_args_apair (args:(cm_expr)list)) ==
           cm_imax
             (cm_tright (cm_expr_tpair (arg_:cm_expr)))
             (cm_adepth (cm_args_apair
               (rest_:(cm_expr)list)))`,
          THM_LIST(assume_rule(
              `args == (arg_:cm_expr) :: rest_`),
            get_cm_expr_tpair_def(), get_cm_adepth_def()));
      thm depth_value = trans_rule(
          assume_rule(
            `retval ==
             cm_imax
               (cm_tright (cm_expr_tpair (arg_:cm_expr)))
               (cm_adepth (cm_args_apair
                 (rest_:(cm_expr)list)))`),
          sym_rule(depth_model));
      add_fact_st(depth_value);
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `new_depth__addr:addr`,
          `retval:int`, `cm_adepth (cm_args_apair args)`));
    }
    *count = new_count;
    *depth = new_depth;
    [[cst::proof]] {
      thm expr_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`ze_:int`, `p:int`},
          (term_pair){`arg_:cm_expr`, `e:cm_expr`}),
          get_cm_expr_rep_def());
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(expr_view)));
      thm tail_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`zn_:int`, `p:int`},
          (term_pair){`rest_:(cm_expr)list`,
                      `args:(cm_expr)list`}),
          get_cm_arg_list_rep_def());
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(tail_view)));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(TERM_LIST(`arg__pre:addr`,
              `arg_:cm_expr`, `rest_:(cm_expr)list`,
              `ze_:int`, `zn_:int`), get_cm_arg_fold()),
            assume_rule(`~(arg__pre == 0i)`))));
    }
  }
}

static void cm_expr_temps(struct cm_expr *expr,
                          int *lvalue, int *rvalue)
    [[cst::param(`e:cm_expr`)]]
    [[cst::require(
      `fact(cm_rep_expr_temps_safe e <=> true) **
       cm_expr_rep expr e **
       undef_data_at lvalue Tint **
       undef_data_at rvalue Tint`)]]
    [[cst::ensure(
      `fact(cm_rep_expr_temps_safe e <=> true) **
       cm_expr_rep expr e **
       data_at lvalue Tint (cm_tleft (cm_expr_tpair e)) **
       data_at rvalue Tint (cm_tright (cm_expr_tpair e))`)]]
{
  [[cst::proof]] {
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        specl_rule(TERM_LIST(`expr__pre:int`, `e:cm_expr`),
          get_cm_expr_open())));
  }
  int out_lvalue = 0;
  int out_rvalue = 0;
  if (expr->kind == CMC_EXPR_ASSIGN) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`e:cm_expr`,
          get_cm_expr_assign_shape_ent()),
          assume_rule(`cm_rep_expr_kind (e:cm_expr) == 3i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`dst_:cm_expr`, `src_:cm_expr`,
                      `ty_:cm_type`))));
      thm shape = assume_rule(
          `e == CMAssignE (dst_:cm_expr)
             (src_:cm_expr) (ty_:cm_type)`);
      thm safe = from_state_bool(
          `cm_rep_expr_temps_safe (e:cm_expr)`);
      thm opened_safe = conv_rule(rewrite_conv(THM_LIST(
          shape, get_cm_rep_expr_temps_safe_def())), safe);
      add_fact_st(eqt_intro_rule(conjunct1_rule(opened_safe)));
      thm safe_tail = conjunct2_rule(opened_safe);
      add_fact_st(conjunct1_rule(safe_tail));
      safe_tail = conjunct2_rule(safe_tail);
      add_fact_st(eqt_intro_rule(conjunct1_rule(safe_tail)));
      add_fact_st(eqt_intro_rule(conjunct2_rule(safe_tail)));
      thm payload_view = by_rewrite(
          `cm_expr_payload (e:cm_expr)
             (za:int) (zb:int) (zargs:int) -|-
           fact(zargs == 0i) **
           cm_expr_node za (dst_:cm_expr)
             (cm_expr_payload dst_) **
           cm_expr_node zb (src_:cm_expr)
             (cm_expr_payload src_)`,
          THM_LIST(shape, get_cm_expr_payload_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(payload_view)));
      thm dst_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`za:int`, `p:int`},
          (term_pair){`dst_:cm_expr`, `e:cm_expr`}),
          get_cm_expr_rep_def());
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(dst_view))));
      thm src_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`zb:int`, `p:int`},
          (term_pair){`src_:cm_expr`, `e:cm_expr`}),
          get_cm_expr_rep_def());
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(src_view))));
    }
    int left_lvalue;
    int left_rvalue;
    int right_lvalue;
    int right_rvalue;
    cm_expr_temps(expr->a, &left_lvalue, &left_rvalue);
    cm_expr_temps(expr->b, &right_lvalue, &right_rvalue);
    [[cst::proof]] {
      thm src_pair_safe = mp_rule(
          spec_rule(`src_:cm_expr`,
            get_cm_rep_expr_temps_safe_pair()),
          from_state_bool(
            `cm_rep_expr_temps_safe (src_:cm_expr)`));
      thm src_bounds = conv_rule(rewrite_conv(THM_LIST(
          get_cm_rep_tpair_safe_def())), src_pair_safe);
      thm src_right_nonnegative =
          conjunct1_rule(conjunct2_rule(conjunct2_rule(src_bounds)));
      thm sum_bounds = mp_rule(mp_rule(int_arith_rule(
          `0i <= cm_tright (cm_expr_tpair (src_:cm_expr)) ==>
           cm_tright (cm_expr_tpair src_) < 2147483647i ==>
           -- 2147483648i <=
             1i + cm_tright (cm_expr_tpair src_) &&
           1i + cm_tright (cm_expr_tpair src_) <= 2147483647i`),
          src_right_nonnegative),
          assume_rule(
            `cm_tright (cm_expr_tpair (src_:cm_expr)) <
             2147483647i`));
      add_fact_st(conjunct1_rule(sum_bounds));
      add_fact_st(conjunct2_rule(sum_bounds));
    }
    out_rvalue = cm_max(left_lvalue, 1 + right_rvalue);
    [[cst::proof]] {
      thm shape = assume_rule(
          `e == CMAssignE (dst_:cm_expr)
             (src_:cm_expr) (ty_:cm_type)`);
      thm left_model = by_rewrite(
          `cm_tleft (cm_expr_tpair (e:cm_expr)) == 0i`,
          THM_LIST(shape, get_cm_expr_tpair_def(),
            get_cm_tleft_def()));
      add_fact_st(sym_rule(left_model));
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `out_lvalue__addr:addr`,
          `0i`, `cm_tleft (cm_expr_tpair e)`));
      thm right_model = by_rewrite(
          `cm_tright (cm_expr_tpair (e:cm_expr)) ==
           cm_imax
             (cm_tleft (cm_expr_tpair (dst_:cm_expr)))
             (1i + cm_tright
               (cm_expr_tpair (src_:cm_expr)))`,
          THM_LIST(shape, get_cm_expr_tpair_def(),
            get_cm_tright_def()));
      thm right_value = trans_rule(
          assume_rule(
            `retval ==
             cm_imax
               (cm_tleft (cm_expr_tpair (dst_:cm_expr)))
               (1i + cm_tright
                 (cm_expr_tpair (src_:cm_expr)))`),
          sym_rule(right_model));
      add_fact_st(right_value);
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `out_rvalue__addr:addr`,
          `retval:int`, `cm_tright (cm_expr_tpair e)`));
      thm dst_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`za:int`, `p:int`},
          (term_pair){`dst_:cm_expr`, `e:cm_expr`}),
          get_cm_expr_rep_def());
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(dst_view)));
      thm src_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`zb:int`, `p:int`},
          (term_pair){`src_:cm_expr`, `e:cm_expr`}),
          get_cm_expr_rep_def());
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(src_view)));
      thm payload_view = by_rewrite(
          `cm_expr_payload (e:cm_expr)
             (za:int) (zb:int) (zargs:int) -|-
           fact(zargs == 0i) **
           cm_expr_node za (dst_:cm_expr)
             (cm_expr_payload dst_) **
           cm_expr_node zb (src_:cm_expr)
             (cm_expr_payload src_)`,
          THM_LIST(assume_rule(
              `e == CMAssignE (dst_:cm_expr)
                 (src_:cm_expr) (ty_:cm_type)`),
            get_cm_expr_payload_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(payload_view))));
    }
  } else if (expr->kind == CMC_EXPR_BINARY) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`e:cm_expr`,
          get_cm_expr_binary_shape_ent()),
          assume_rule(`cm_rep_expr_kind (e:cm_expr) == 4i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`op_:int`, `left_:cm_expr`,
                      `right_:cm_expr`, `ty_:cm_type`))));
      thm shape = assume_rule(
          `e == CMBinaryE (op_:int) (left_:cm_expr)
             (right_:cm_expr) (ty_:cm_type)`);
      thm safe = from_state_bool(
          `cm_rep_expr_temps_safe (e:cm_expr)`);
      thm opened_safe = conv_rule(rewrite_conv(THM_LIST(
          shape, get_cm_rep_expr_temps_safe_def())), safe);
      add_fact_st(eqt_intro_rule(conjunct1_rule(opened_safe)));
      thm safe_tail = conjunct2_rule(opened_safe);
      add_fact_st(conjunct1_rule(safe_tail));
      safe_tail = conjunct2_rule(safe_tail);
      add_fact_st(eqt_intro_rule(conjunct1_rule(safe_tail)));
      add_fact_st(eqt_intro_rule(conjunct2_rule(safe_tail)));
      thm payload_view = by_rewrite(
          `cm_expr_payload (e:cm_expr)
             (za:int) (zb:int) (zargs:int) -|-
           fact(zargs == 0i) **
           cm_expr_node za (left_:cm_expr)
             (cm_expr_payload left_) **
           cm_expr_node zb (right_:cm_expr)
             (cm_expr_payload right_)`,
          THM_LIST(shape, get_cm_expr_payload_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(payload_view)));
      thm left_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`za:int`, `p:int`},
          (term_pair){`left_:cm_expr`, `e:cm_expr`}),
          get_cm_expr_rep_def());
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(left_view))));
      thm right_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`zb:int`, `p:int`},
          (term_pair){`right_:cm_expr`, `e:cm_expr`}),
          get_cm_expr_rep_def());
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(right_view))));
    }
    int left_lvalue;
    int left_rvalue;
    int right_lvalue;
    int right_rvalue;
    cm_expr_temps(expr->a, &left_lvalue, &left_rvalue);
    cm_expr_temps(expr->b, &right_lvalue, &right_rvalue);
    [[cst::proof]] {
      thm left_model = by_rewrite(
          `cm_tleft (cm_expr_tpair (e:cm_expr)) == 0i`,
          THM_LIST(assume_rule(
              `e == CMBinaryE (op_:int) (left_:cm_expr)
                 (right_:cm_expr) (ty_:cm_type)`),
            get_cm_expr_tpair_def(), get_cm_tleft_def()));
      add_fact_st(sym_rule(left_model));
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `out_lvalue__addr:addr`,
          `0i`, `cm_tleft (cm_expr_tpair e)`));
    }
    if (expr->op == CMC_BIN_OR) {
      out_rvalue = cm_max(left_rvalue, right_rvalue);
      [[cst::proof]] {
        thm op_model = conv_rule(rewrite_conv(THM_LIST(
            assume_rule(
              `e == CMBinaryE (op_:int) (left_:cm_expr)
                 (right_:cm_expr) (ty_:cm_type)`),
            get_cm_rep_expr_op_def())),
            assume_rule(`cm_rep_expr_op (e:cm_expr) == 0i`));
        thm right_model = by_rewrite(
            `cm_tright (cm_expr_tpair (e:cm_expr)) ==
             cm_imax
               (cm_tright (cm_expr_tpair (left_:cm_expr)))
               (cm_tright (cm_expr_tpair (right_:cm_expr)))`,
            THM_LIST(assume_rule(
                `e == CMBinaryE (op_:int) (left_:cm_expr)
                   (right_:cm_expr) (ty_:cm_type)`),
              op_model, get_cm_expr_tpair_def(),
              get_cm_tright_def()));
        thm right_value = trans_rule(
            assume_rule(
              `retval ==
               cm_imax
                 (cm_tright (cm_expr_tpair (left_:cm_expr)))
                 (cm_tright (cm_expr_tpair (right_:cm_expr)))`),
            sym_rule(right_model));
        add_fact_st(right_value);
        cst_set_symbolic_state(retarget_cell_st(
            cst_get_symbolic_state(), `out_rvalue__addr:addr`,
            `retval:int`, `cm_tright (cm_expr_tpair e)`));
      }
    } else if (expr->op == CMC_BIN_AND) {
      out_rvalue = cm_max(left_rvalue, right_rvalue);
      [[cst::proof]] {
        thm op_model = conv_rule(rewrite_conv(THM_LIST(
            assume_rule(
              `e == CMBinaryE (op_:int) (left_:cm_expr)
                 (right_:cm_expr) (ty_:cm_type)`),
            get_cm_rep_expr_op_def())),
            assume_rule(`cm_rep_expr_op (e:cm_expr) == 1i`));
        thm right_model = by_rewrite(
            `cm_tright (cm_expr_tpair (e:cm_expr)) ==
             cm_imax
               (cm_tright (cm_expr_tpair (left_:cm_expr)))
               (cm_tright (cm_expr_tpair (right_:cm_expr)))`,
            THM_LIST(assume_rule(
                `e == CMBinaryE (op_:int) (left_:cm_expr)
                   (right_:cm_expr) (ty_:cm_type)`),
              op_model, get_cm_expr_tpair_def(),
              get_cm_tright_def()));
        thm right_value = trans_rule(
            assume_rule(
              `retval ==
               cm_imax
                 (cm_tright (cm_expr_tpair (left_:cm_expr)))
                 (cm_tright (cm_expr_tpair (right_:cm_expr)))`),
            sym_rule(right_model));
        add_fact_st(right_value);
        cst_set_symbolic_state(retarget_cell_st(
            cst_get_symbolic_state(), `out_rvalue__addr:addr`,
            `retval:int`, `cm_tright (cm_expr_tpair e)`));
      }
    } else {
      [[cst::proof]] {
        thm right_pair_safe = mp_rule(
            spec_rule(`right_:cm_expr`,
              get_cm_rep_expr_temps_safe_pair()),
            from_state_bool(
              `cm_rep_expr_temps_safe (right_:cm_expr)`));
        thm right_bounds = conv_rule(rewrite_conv(THM_LIST(
            get_cm_rep_tpair_safe_def())), right_pair_safe);
        thm right_nonnegative =
            conjunct1_rule(conjunct2_rule(
              conjunct2_rule(right_bounds)));
        thm sum_bounds = mp_rule(mp_rule(int_arith_rule(
            `0i <= cm_tright (cm_expr_tpair (right_:cm_expr)) ==>
             cm_tright (cm_expr_tpair right_) < 2147483647i ==>
             -- 2147483648i <=
               1i + cm_tright (cm_expr_tpair right_) &&
             1i + cm_tright (cm_expr_tpair right_) <= 2147483647i`),
            right_nonnegative),
            assume_rule(
              `cm_tright (cm_expr_tpair (right_:cm_expr)) <
               2147483647i`));
        add_fact_st(conjunct1_rule(sum_bounds));
        add_fact_st(conjunct2_rule(sum_bounds));
      }
      out_rvalue = cm_max(left_rvalue, 1 + right_rvalue);
      [[cst::proof]] {
        thm shape = assume_rule(
            `e == CMBinaryE (op_:int) (left_:cm_expr)
               (right_:cm_expr) (ty_:cm_type)`);
        thm not_zero = conv_rule(rewrite_conv(THM_LIST(
            shape, get_cm_rep_expr_op_def())),
            assume_rule(`~(cm_rep_expr_op (e:cm_expr) == 0i)`));
        thm not_one = conv_rule(rewrite_conv(THM_LIST(
            shape, get_cm_rep_expr_op_def())),
            assume_rule(`~(cm_rep_expr_op (e:cm_expr) == 1i)`));
        thm long_model = mp_rule(mp_rule(int_arith_rule(
            `~((op_:int) == 0i) ==> ~(op_ == 1i) ==>
             ~(op_ == 0i || op_ == 1i)`), not_zero), not_one);
        thm right_model = by_rewrite(
            `cm_tright (cm_expr_tpair (e:cm_expr)) ==
             cm_imax
               (cm_tright (cm_expr_tpair (left_:cm_expr)))
               (1i + cm_tright
                 (cm_expr_tpair (right_:cm_expr)))`,
            THM_LIST(shape, long_model, get_cm_expr_tpair_def(),
              get_cm_tright_def()));
        thm right_value = trans_rule(
            assume_rule(
              `retval ==
               cm_imax
                 (cm_tright (cm_expr_tpair (left_:cm_expr)))
                 (1i + cm_tright
                   (cm_expr_tpair (right_:cm_expr)))`),
            sym_rule(right_model));
        add_fact_st(right_value);
        cst_set_symbolic_state(retarget_cell_st(
            cst_get_symbolic_state(), `out_rvalue__addr:addr`,
            `retval:int`, `cm_tright (cm_expr_tpair e)`));
      }
    }
    [[cst::proof]] {
      thm left_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`za:int`, `p:int`},
          (term_pair){`left_:cm_expr`, `e:cm_expr`}),
          get_cm_expr_rep_def());
      apply_hconv_st(eq2ent(left_view));
      thm right_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`zb:int`, `p:int`},
          (term_pair){`right_:cm_expr`, `e:cm_expr`}),
          get_cm_expr_rep_def());
      apply_hconv_st(eq2ent(right_view));
      thm payload_view = by_rewrite(
          `cm_expr_payload (e:cm_expr)
             (za:int) (zb:int) (zargs:int) -|-
           fact(zargs == 0i) **
           cm_expr_node za (left_:cm_expr)
             (cm_expr_payload left_) **
           cm_expr_node zb (right_:cm_expr)
             (cm_expr_payload right_)`,
          THM_LIST(assume_rule(
              `e == CMBinaryE (op_:int) (left_:cm_expr)
                 (right_:cm_expr) (ty_:cm_type)`),
            get_cm_expr_payload_def()));
      apply_hconv_st(eq2ent(sym_rule(payload_view)));
    }
  } else if (expr->kind == CMC_EXPR_UNARY) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`e:cm_expr`,
          get_cm_expr_unary_shape_ent()),
          assume_rule(`cm_rep_expr_kind (e:cm_expr) == 5i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`op_:int`, `arg_:cm_expr`,
                      `ty_:cm_type`))));
      thm shape = assume_rule(
          `e == CMUnaryE (op_:int)
             (arg_:cm_expr) (ty_:cm_type)`);
      thm safe = from_state_bool(
          `cm_rep_expr_temps_safe (e:cm_expr)`);
      thm opened_safe = conv_rule(rewrite_conv(THM_LIST(
          shape, get_cm_rep_expr_temps_safe_def())), safe);
      add_fact_st(eqt_intro_rule(conjunct1_rule(opened_safe)));
      add_fact_st(eqt_intro_rule(conjunct2_rule(opened_safe)));
      thm payload_view = by_rewrite(
          `cm_expr_payload (e:cm_expr)
             (za:int) (zb:int) (zargs:int) -|-
           fact(~(za == 0i) && zb == 0i && zargs == 0i) **
           cm_expr_node za (arg_:cm_expr)
             (cm_expr_payload arg_)`,
          THM_LIST(shape, get_cm_expr_payload_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(payload_view)));
      thm arg_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`za:int`, `p:int`},
          (term_pair){`arg_:cm_expr`, `e:cm_expr`}),
          get_cm_expr_rep_def());
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(arg_view))));
    }
    int child_lvalue;
    int child_rvalue;
    cm_expr_temps(expr->a, &child_lvalue, &child_rvalue);
    if (expr->op == CMC_UN_DEREF) {
      out_lvalue = child_rvalue;
      out_rvalue = child_rvalue;
      [[cst::proof]] {
        thm shape = assume_rule(
            `e == CMUnaryE (op_:int)
               (arg_:cm_expr) (ty_:cm_type)`);
        thm op_model = conv_rule(rewrite_conv(THM_LIST(
            shape, get_cm_rep_expr_op_def())),
            assume_rule(`cm_rep_expr_op (e:cm_expr) == 2i`));
        thm left_model = by_rewrite(
            `cm_tleft (cm_expr_tpair (e:cm_expr)) ==
             cm_tright (cm_expr_tpair (arg_:cm_expr))`,
            THM_LIST(shape, op_model, get_cm_expr_tpair_def(),
              get_cm_tleft_def()));
        add_fact_st(sym_rule(left_model));
        cst_set_symbolic_state(retarget_cell_st(
            cst_get_symbolic_state(), `out_lvalue__addr:addr`,
            `cm_tright (cm_expr_tpair (arg_:cm_expr))`,
            `cm_tleft (cm_expr_tpair e)`));
        thm right_model = by_rewrite(
            `cm_tright (cm_expr_tpair (e:cm_expr)) ==
             cm_tright (cm_expr_tpair (arg_:cm_expr))`,
            THM_LIST(shape, op_model, get_cm_expr_tpair_def(),
              get_cm_tright_def()));
        add_fact_st(sym_rule(right_model));
        cst_set_symbolic_state(retarget_cell_st(
            cst_get_symbolic_state(), `out_rvalue__addr:addr`,
            `cm_tright (cm_expr_tpair (arg_:cm_expr))`,
            `cm_tright (cm_expr_tpair e)`));
      }
    } else if (expr->op == CMC_UN_ADDR) {
      out_rvalue = child_lvalue;
      [[cst::proof]] {
        thm shape = assume_rule(
            `e == CMUnaryE (op_:int)
               (arg_:cm_expr) (ty_:cm_type)`);
        thm op_model = conv_rule(rewrite_conv(THM_LIST(
            shape, get_cm_rep_expr_op_def())),
            assume_rule(`cm_rep_expr_op (e:cm_expr) == 3i`));
        thm left_model = by_rewrite(
            `cm_tleft (cm_expr_tpair (e:cm_expr)) == 0i`,
            THM_LIST(shape, op_model,
              int_arith_rule(`~(3i == 2i)`),
              get_cm_expr_tpair_def(), get_cm_tleft_def()));
        add_fact_st(sym_rule(left_model));
        cst_set_symbolic_state(retarget_cell_st(
            cst_get_symbolic_state(), `out_lvalue__addr:addr`,
            `0i`, `cm_tleft (cm_expr_tpair e)`));
        thm right_model = by_rewrite(
            `cm_tright (cm_expr_tpair (e:cm_expr)) ==
             cm_tleft (cm_expr_tpair (arg_:cm_expr))`,
            THM_LIST(shape, op_model,
              int_arith_rule(`~(3i == 2i)`),
              get_cm_expr_tpair_def(), get_cm_tright_def()));
        add_fact_st(sym_rule(right_model));
        cst_set_symbolic_state(retarget_cell_st(
            cst_get_symbolic_state(), `out_rvalue__addr:addr`,
            `cm_tleft (cm_expr_tpair (arg_:cm_expr))`,
            `cm_tright (cm_expr_tpair e)`));
      }
    } else {
      out_rvalue = child_rvalue;
      [[cst::proof]] {
        thm shape = assume_rule(
            `e == CMUnaryE (op_:int)
               (arg_:cm_expr) (ty_:cm_type)`);
        thm not_deref = conv_rule(rewrite_conv(THM_LIST(
            shape, get_cm_rep_expr_op_def())),
            assume_rule(`~(cm_rep_expr_op (e:cm_expr) == 2i)`));
        thm not_addr = conv_rule(rewrite_conv(THM_LIST(
            shape, get_cm_rep_expr_op_def())),
            assume_rule(`~(cm_rep_expr_op (e:cm_expr) == 3i)`));
        thm left_model = by_rewrite(
            `cm_tleft (cm_expr_tpair (e:cm_expr)) == 0i`,
            THM_LIST(shape, not_deref, not_addr,
              get_cm_expr_tpair_def(), get_cm_tleft_def()));
        add_fact_st(sym_rule(left_model));
        cst_set_symbolic_state(retarget_cell_st(
            cst_get_symbolic_state(), `out_lvalue__addr:addr`,
            `0i`, `cm_tleft (cm_expr_tpair e)`));
        thm right_model = by_rewrite(
            `cm_tright (cm_expr_tpair (e:cm_expr)) ==
             cm_tright (cm_expr_tpair (arg_:cm_expr))`,
            THM_LIST(shape, not_deref, not_addr,
              get_cm_expr_tpair_def(), get_cm_tright_def()));
        add_fact_st(sym_rule(right_model));
        cst_set_symbolic_state(retarget_cell_st(
            cst_get_symbolic_state(), `out_rvalue__addr:addr`,
            `cm_tright (cm_expr_tpair (arg_:cm_expr))`,
            `cm_tright (cm_expr_tpair e)`));
      }
    }
    [[cst::proof]] {
      thm arg_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`za:int`, `p:int`},
          (term_pair){`arg_:cm_expr`, `e:cm_expr`}),
          get_cm_expr_rep_def());
      apply_hconv_st(eq2ent(arg_view));
      thm payload_view = by_rewrite(
          `cm_expr_payload (e:cm_expr)
             (za:int) (zb:int) (zargs:int) -|-
           fact(~(za == 0i) && zb == 0i && zargs == 0i) **
           cm_expr_node za (arg_:cm_expr)
             (cm_expr_payload arg_)`,
          THM_LIST(assume_rule(
              `e == CMUnaryE (op_:int)
                 (arg_:cm_expr) (ty_:cm_type)`),
            get_cm_expr_payload_def()));
      thm payload_facts = conj_rule(
          assume_rule(`~((za:int) == 0i)`),
          conj_rule(assume_rule(`(zb:int) == 0i`),
            assume_rule(`(zargs:int) == 0i`)));
      thm payload_intro = frame_right_slrule(
          add_fact_hconv(payload_facts),
          `cm_expr_node (za:int) (arg_:cm_expr)
             (cm_expr_payload arg_)`);
      thm payload_fold = trans_slrule(payload_intro,
          eq2ent(sym_rule(payload_view)));
      apply_hconv_st(payload_fold);
    }
  } else if (expr->kind == CMC_EXPR_INDEX) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`e:cm_expr`,
          get_cm_expr_index_shape_ent()),
          assume_rule(`cm_rep_expr_kind (e:cm_expr) == 6i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`base_:cm_expr`, `index_:cm_expr`,
                      `ty_:cm_type`))));
      thm shape = assume_rule(
          `e == CMIndexE (base_:cm_expr)
             (index_:cm_expr) (ty_:cm_type)`);
      thm safe = from_state_bool(
          `cm_rep_expr_temps_safe (e:cm_expr)`);
      thm opened_safe = conv_rule(rewrite_conv(THM_LIST(
          shape, get_cm_rep_expr_temps_safe_def())), safe);
      add_fact_st(eqt_intro_rule(conjunct1_rule(opened_safe)));
      thm safe_tail = conjunct2_rule(opened_safe);
      add_fact_st(conjunct1_rule(safe_tail));
      safe_tail = conjunct2_rule(safe_tail);
      add_fact_st(eqt_intro_rule(conjunct1_rule(safe_tail)));
      add_fact_st(eqt_intro_rule(conjunct2_rule(safe_tail)));
      thm payload_view = by_rewrite(
          `cm_expr_payload (e:cm_expr)
             (za:int) (zb:int) (zargs:int) -|-
           fact(zargs == 0i) **
           cm_expr_node za (base_:cm_expr)
             (cm_expr_payload base_) **
           cm_expr_node zb (index_:cm_expr)
             (cm_expr_payload index_)`,
          THM_LIST(shape, get_cm_expr_payload_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(payload_view)));
      thm base_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`za:int`, `p:int`},
          (term_pair){`base_:cm_expr`, `e:cm_expr`}),
          get_cm_expr_rep_def());
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(base_view))));
      thm index_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`zb:int`, `p:int`},
          (term_pair){`index_:cm_expr`, `e:cm_expr`}),
          get_cm_expr_rep_def());
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(index_view))));
    }
    int base_lvalue;
    int base_rvalue;
    int index_lvalue;
    int index_rvalue;
    cm_expr_temps(expr->a, &base_lvalue, &base_rvalue);
    cm_expr_temps(expr->b, &index_lvalue, &index_rvalue);
    [[cst::proof]] {
      thm index_pair_safe = mp_rule(
          spec_rule(`index_:cm_expr`,
            get_cm_rep_expr_temps_safe_pair()),
          from_state_bool(
            `cm_rep_expr_temps_safe (index_:cm_expr)`));
      thm index_bounds = conv_rule(rewrite_conv(THM_LIST(
          get_cm_rep_tpair_safe_def())), index_pair_safe);
      thm index_right_nonnegative =
          conjunct1_rule(conjunct2_rule(
            conjunct2_rule(index_bounds)));
      thm sum_bounds = mp_rule(mp_rule(int_arith_rule(
          `0i <= cm_tright (cm_expr_tpair (index_:cm_expr)) ==>
           cm_tright (cm_expr_tpair index_) < 2147483647i ==>
           -- 2147483648i <=
             1i + cm_tright (cm_expr_tpair index_) &&
           1i + cm_tright (cm_expr_tpair index_) <= 2147483647i`),
          index_right_nonnegative),
          assume_rule(
            `cm_tright (cm_expr_tpair (index_:cm_expr)) <
             2147483647i`));
      add_fact_st(conjunct1_rule(sum_bounds));
      add_fact_st(conjunct2_rule(sum_bounds));
    }
    out_lvalue = cm_max(base_rvalue, 1 + index_rvalue);
    out_rvalue = out_lvalue;
    [[cst::proof]] {
      thm shape = assume_rule(
          `e == CMIndexE (base_:cm_expr)
             (index_:cm_expr) (ty_:cm_type)`);
      thm left_model = by_rewrite(
          `cm_tleft (cm_expr_tpair (e:cm_expr)) ==
           cm_imax
             (cm_tright (cm_expr_tpair (base_:cm_expr)))
             (1i + cm_tright
               (cm_expr_tpair (index_:cm_expr)))`,
          THM_LIST(shape, get_cm_expr_tpair_def(),
            get_cm_tleft_def()));
      thm left_value = trans_rule(
          assume_rule(
            `retval ==
             cm_imax
               (cm_tright (cm_expr_tpair (base_:cm_expr)))
               (1i + cm_tright
                 (cm_expr_tpair (index_:cm_expr)))`),
          sym_rule(left_model));
      add_fact_st(left_value);
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `out_lvalue__addr:addr`,
          `retval:int`, `cm_tleft (cm_expr_tpair e)`));
      thm right_model = by_rewrite(
          `cm_tright (cm_expr_tpair (e:cm_expr)) ==
           cm_imax
             (cm_tright (cm_expr_tpair (base_:cm_expr)))
             (1i + cm_tright
               (cm_expr_tpair (index_:cm_expr)))`,
          THM_LIST(shape, get_cm_expr_tpair_def(),
            get_cm_tright_def()));
      thm right_value = trans_rule(
          assume_rule(
            `retval ==
             cm_imax
               (cm_tright (cm_expr_tpair (base_:cm_expr)))
               (1i + cm_tright
                 (cm_expr_tpair (index_:cm_expr)))`),
          sym_rule(right_model));
      add_fact_st(right_value);
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `out_rvalue__addr:addr`,
          `retval:int`, `cm_tright (cm_expr_tpair e)`));
      thm base_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`za:int`, `p:int`},
          (term_pair){`base_:cm_expr`, `e:cm_expr`}),
          get_cm_expr_rep_def());
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(base_view)));
      thm index_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`zb:int`, `p:int`},
          (term_pair){`index_:cm_expr`, `e:cm_expr`}),
          get_cm_expr_rep_def());
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(index_view)));
      thm payload_view = by_rewrite(
          `cm_expr_payload (e:cm_expr)
             (za:int) (zb:int) (zargs:int) -|-
           fact(zargs == 0i) **
           cm_expr_node za (base_:cm_expr)
             (cm_expr_payload base_) **
           cm_expr_node zb (index_:cm_expr)
             (cm_expr_payload index_)`,
          THM_LIST(shape, get_cm_expr_payload_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(payload_view))));
    }
  } else if (expr->kind == CMC_EXPR_MEMBER) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`e:cm_expr`,
          get_cm_expr_member_shape_ent()),
          assume_rule(`cm_rep_expr_kind (e:cm_expr) == 7i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`base_:cm_expr`, `mid_:int`,
                      `ty_:cm_type`))));
      thm shape = assume_rule(
          `e == CMMemberE (base_:cm_expr)
             (mid_:int) (ty_:cm_type)`);
      thm safe = from_state_bool(
          `cm_rep_expr_temps_safe (e:cm_expr)`);
      thm opened_safe = conv_rule(rewrite_conv(THM_LIST(
          shape, get_cm_rep_expr_temps_safe_def())), safe);
      add_fact_st(eqt_intro_rule(conjunct1_rule(opened_safe)));
      add_fact_st(eqt_intro_rule(conjunct2_rule(opened_safe)));
      thm payload_view = by_rewrite(
          `cm_expr_payload (e:cm_expr)
             (za:int) (zb:int) (zargs:int) -|-
           fact(~(za == 0i) && zb == 0i && zargs == 0i) **
           cm_expr_node za (base_:cm_expr)
             (cm_expr_payload base_)`,
          THM_LIST(shape, get_cm_expr_payload_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(payload_view)));
      thm base_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`za:int`, `p:int`},
          (term_pair){`base_:cm_expr`, `e:cm_expr`}),
          get_cm_expr_rep_def());
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(base_view))));
    }
    int base_lvalue;
    int base_rvalue;
    cm_expr_temps(expr->a, &base_lvalue, &base_rvalue);
    out_lvalue = base_rvalue;
    out_rvalue = base_rvalue;
    [[cst::proof]] {
      thm shape = assume_rule(
          `e == CMMemberE (base_:cm_expr)
             (mid_:int) (ty_:cm_type)`);
      thm left_model = by_rewrite(
          `cm_tleft (cm_expr_tpair (e:cm_expr)) ==
           cm_tright (cm_expr_tpair (base_:cm_expr))`,
          THM_LIST(shape, get_cm_expr_tpair_def(),
            get_cm_tleft_def()));
      add_fact_st(sym_rule(left_model));
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `out_lvalue__addr:addr`,
          `cm_tright (cm_expr_tpair (base_:cm_expr))`,
          `cm_tleft (cm_expr_tpair e)`));
      thm right_model = by_rewrite(
          `cm_tright (cm_expr_tpair (e:cm_expr)) ==
           cm_tright (cm_expr_tpair (base_:cm_expr))`,
          THM_LIST(shape, get_cm_expr_tpair_def(),
            get_cm_tright_def()));
      add_fact_st(sym_rule(right_model));
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `out_rvalue__addr:addr`,
          `cm_tright (cm_expr_tpair (base_:cm_expr))`,
          `cm_tright (cm_expr_tpair e)`));
      thm base_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`za:int`, `p:int`},
          (term_pair){`base_:cm_expr`, `e:cm_expr`}),
          get_cm_expr_rep_def());
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(base_view)));
      thm payload_view = by_rewrite(
          `cm_expr_payload (e:cm_expr)
             (za:int) (zb:int) (zargs:int) -|-
           fact(~(za == 0i) && zb == 0i && zargs == 0i) **
           cm_expr_node za (base_:cm_expr)
             (cm_expr_payload base_)`,
          THM_LIST(shape, get_cm_expr_payload_def()));
      thm payload_facts = conj_rule(
          assume_rule(`~((za:int) == 0i)`),
          conj_rule(assume_rule(`(zb:int) == 0i`),
            assume_rule(`(zargs:int) == 0i`)));
      thm payload_intro = frame_right_slrule(
          add_fact_hconv(payload_facts),
          `cm_expr_node (za:int) (base_:cm_expr)
             (cm_expr_payload base_)`);
      thm payload_fold = trans_slrule(payload_intro,
          eq2ent(sym_rule(payload_view)));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          payload_fold));
    }
  } else if (expr->kind == CMC_EXPR_CALL) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`e:cm_expr`,
          get_cm_expr_call_shape_ent()),
          assume_rule(`cm_rep_expr_kind (e:cm_expr) == 8i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`fid_:int`, `args_:(cm_expr)list`,
                      `ty_:cm_type`))));
      thm shape = assume_rule(
          `e == CMCallE (fid_:int)
             (args_:(cm_expr)list) (ty_:cm_type)`);
      thm safe = from_state_bool(
          `cm_rep_expr_temps_safe (e:cm_expr)`);
      thm opened_safe = conv_rule(rewrite_conv(THM_LIST(
          shape, get_cm_rep_expr_temps_safe_def())), safe);
      add_fact_st(eqt_intro_rule(conjunct1_rule(opened_safe)));
      add_fact_st(eqt_intro_rule(conjunct2_rule(opened_safe)));
      thm payload_view = by_rewrite(
          `cm_expr_payload (e:cm_expr)
             (za:int) (zb:int) (zargs:int) -|-
           fact(za == 0i && zb == 0i) **
           cm_arg_tree (args_:(cm_expr)list) zargs`,
          THM_LIST(shape, get_cm_expr_payload_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(payload_view)));
      thm args_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`zargs:int`, `p:int`},
          (term_pair){`args_:(cm_expr)list`,
                      `args:(cm_expr)list`}),
          get_cm_arg_list_rep_def());
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(args_view))));
    }
    int count;
    int depth;
    cmc_args_tpair(expr->args, &count, &depth);
    [[cst::proof]] {
      thm shape = assume_rule(
          `e == CMCallE (fid_:int) (args_:(cm_expr)list)
             (ty_:cm_type)`);
      thm safe = from_state_bool(
          `cm_rep_expr_temps_safe (e:cm_expr)`);
      thm opened_safe = conv_rule(rewrite_conv(THM_LIST(
          shape, get_cm_rep_expr_temps_safe_def())), safe);
      thm pair_safe = conjunct1_rule(opened_safe);
      thm pair_bounds = conv_rule(rewrite_conv(THM_LIST(
          get_cm_rep_tpair_safe_def(), get_cm_expr_tpair_def(),
          get_cm_tleft_def(), get_cm_tright_def())), pair_safe);
      add_fact_st(
          conjunct1_rule(conjunct2_rule(conjunct2_rule(pair_bounds))));
      add_fact_st(
          conjunct2_rule(conjunct2_rule(conjunct2_rule(pair_bounds))));
    }
    out_rvalue = count + depth;
    [[cst::proof]] {
      thm shape = assume_rule(
          `e == CMCallE (fid_:int)
             (args_:(cm_expr)list) (ty_:cm_type)`);
      thm left_model = by_rewrite(
          `cm_tleft (cm_expr_tpair (e:cm_expr)) == 0i`,
          THM_LIST(shape, get_cm_expr_tpair_def(),
            get_cm_tleft_def()));
      add_fact_st(sym_rule(left_model));
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `out_lvalue__addr:addr`,
          `0i`, `cm_tleft (cm_expr_tpair e)`));
      thm right_model = by_rewrite(
          `cm_tright (cm_expr_tpair (e:cm_expr)) ==
           cm_acount (cm_args_apair
             (args_:(cm_expr)list)) +
           cm_adepth (cm_args_apair args_)`,
          THM_LIST(shape, get_cm_expr_tpair_def(),
            get_cm_tright_def()));
      add_fact_st(sym_rule(right_model));
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `out_rvalue__addr:addr`,
          `cm_acount (cm_args_apair (args_:(cm_expr)list)) +
           cm_adepth (cm_args_apair args_)`,
          `cm_tright (cm_expr_tpair e)`));
      thm args_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`zargs:int`, `p:int`},
          (term_pair){`args_:(cm_expr)list`,
                      `args:(cm_expr)list`}),
          get_cm_arg_list_rep_def());
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(args_view)));
      thm payload_view = by_rewrite(
          `cm_expr_payload (e:cm_expr)
             (za:int) (zb:int) (zargs:int) -|-
           fact(za == 0i && zb == 0i) **
           cm_arg_tree (args_:(cm_expr)list) zargs`,
          THM_LIST(shape, get_cm_expr_payload_def()));
      thm payload_facts = conj_rule(
          assume_rule(`(za:int) == 0i`),
          assume_rule(`(zb:int) == 0i`));
      thm payload_intro = frame_right_slrule(
          add_fact_hconv(payload_facts),
          `cm_arg_tree (args_:(cm_expr)list) (zargs:int)`);
      thm payload_fold = trans_slrule(payload_intro,
          eq2ent(sym_rule(payload_view)));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          payload_fold));
    }
  } else if (expr->kind == CMC_EXPR_PUTC) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`e:cm_expr`,
          get_cm_expr_putc_shape_ent()),
          assume_rule(`cm_rep_expr_kind (e:cm_expr) == 11i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`arg_:cm_expr`, `ty_:cm_type`))));
      thm shape = assume_rule(
          `e == CMPutcE (arg_:cm_expr) (ty_:cm_type)`);
      thm safe = from_state_bool(
          `cm_rep_expr_temps_safe (e:cm_expr)`);
      thm opened_safe = conv_rule(rewrite_conv(THM_LIST(
          shape, get_cm_rep_expr_temps_safe_def())), safe);
      add_fact_st(eqt_intro_rule(conjunct1_rule(opened_safe)));
      add_fact_st(eqt_intro_rule(conjunct2_rule(opened_safe)));
      thm payload_view = by_rewrite(
          `cm_expr_payload (e:cm_expr)
             (za:int) (zb:int) (zargs:int) -|-
           fact(~(za == 0i) && zb == 0i && zargs == 0i) **
           cm_expr_node za (arg_:cm_expr)
             (cm_expr_payload arg_)`,
          THM_LIST(shape, get_cm_expr_payload_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(payload_view)));
      thm arg_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`za:int`, `p:int`},
          (term_pair){`arg_:cm_expr`, `e:cm_expr`}),
          get_cm_expr_rep_def());
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(arg_view))));
    }
    int child_lvalue;
    int child_rvalue;
    cm_expr_temps(expr->a, &child_lvalue, &child_rvalue);
    out_rvalue = child_rvalue;
    [[cst::proof]] {
      thm shape = assume_rule(
          `e == CMPutcE (arg_:cm_expr) (ty_:cm_type)`);
      thm left_model = by_rewrite(
          `cm_tleft (cm_expr_tpair (e:cm_expr)) == 0i`,
          THM_LIST(shape, get_cm_expr_tpair_def(),
            get_cm_tleft_def()));
      add_fact_st(sym_rule(left_model));
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `out_lvalue__addr:addr`,
          `0i`, `cm_tleft (cm_expr_tpair e)`));
      thm right_model = by_rewrite(
          `cm_tright (cm_expr_tpair (e:cm_expr)) ==
           cm_tright (cm_expr_tpair (arg_:cm_expr))`,
          THM_LIST(shape, get_cm_expr_tpair_def(),
            get_cm_tright_def()));
      add_fact_st(sym_rule(right_model));
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `out_rvalue__addr:addr`,
          `cm_tright (cm_expr_tpair (arg_:cm_expr))`,
          `cm_tright (cm_expr_tpair e)`));
      thm arg_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`za:int`, `p:int`},
          (term_pair){`arg_:cm_expr`, `e:cm_expr`}),
          get_cm_expr_rep_def());
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(arg_view)));
      thm payload_view = by_rewrite(
          `cm_expr_payload (e:cm_expr)
             (za:int) (zb:int) (zargs:int) -|-
           fact(~(za == 0i) && zb == 0i && zargs == 0i) **
           cm_expr_node za (arg_:cm_expr)
             (cm_expr_payload arg_)`,
          THM_LIST(shape, get_cm_expr_payload_def()));
      thm payload_facts = conj_rule(
          assume_rule(`~((za:int) == 0i)`),
          conj_rule(assume_rule(`(zb:int) == 0i`),
            assume_rule(`(zargs:int) == 0i`)));
      thm payload_intro = frame_right_slrule(
          add_fact_hconv(payload_facts),
          `cm_expr_node (za:int) (arg_:cm_expr)
             (cm_expr_payload arg_)`);
      thm payload_fold = trans_slrule(payload_intro,
          eq2ent(sym_rule(payload_view)));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          payload_fold));
    }
  } else if (expr->kind == CMC_EXPR_PUTI) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`e:cm_expr`,
          get_cm_expr_puti_shape_ent()),
          assume_rule(`cm_rep_expr_kind (e:cm_expr) == 12i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`arg_:cm_expr`, `ty_:cm_type`))));
      thm shape = assume_rule(
          `e == CMPutiE (arg_:cm_expr) (ty_:cm_type)`);
      thm safe = from_state_bool(
          `cm_rep_expr_temps_safe (e:cm_expr)`);
      thm opened_safe = conv_rule(rewrite_conv(THM_LIST(
          shape, get_cm_rep_expr_temps_safe_def())), safe);
      add_fact_st(eqt_intro_rule(conjunct1_rule(opened_safe)));
      add_fact_st(eqt_intro_rule(conjunct2_rule(opened_safe)));
      thm payload_view = by_rewrite(
          `cm_expr_payload (e:cm_expr)
             (za:int) (zb:int) (zargs:int) -|-
           fact(~(za == 0i) && zb == 0i && zargs == 0i) **
           cm_expr_node za (arg_:cm_expr)
             (cm_expr_payload arg_)`,
          THM_LIST(shape, get_cm_expr_payload_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(payload_view)));
      thm arg_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`za:int`, `p:int`},
          (term_pair){`arg_:cm_expr`, `e:cm_expr`}),
          get_cm_expr_rep_def());
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(arg_view))));
    }
    int child_lvalue;
    int child_rvalue;
    cm_expr_temps(expr->a, &child_lvalue, &child_rvalue);
    out_rvalue = child_rvalue;
    [[cst::proof]] {
      thm shape = assume_rule(
          `e == CMPutiE (arg_:cm_expr) (ty_:cm_type)`);
      thm left_model = by_rewrite(
          `cm_tleft (cm_expr_tpair (e:cm_expr)) == 0i`,
          THM_LIST(shape, get_cm_expr_tpair_def(),
            get_cm_tleft_def()));
      add_fact_st(sym_rule(left_model));
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `out_lvalue__addr:addr`,
          `0i`, `cm_tleft (cm_expr_tpair e)`));
      thm right_model = by_rewrite(
          `cm_tright (cm_expr_tpair (e:cm_expr)) ==
           cm_tright (cm_expr_tpair (arg_:cm_expr))`,
          THM_LIST(shape, get_cm_expr_tpair_def(),
            get_cm_tright_def()));
      add_fact_st(sym_rule(right_model));
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `out_rvalue__addr:addr`,
          `cm_tright (cm_expr_tpair (arg_:cm_expr))`,
          `cm_tright (cm_expr_tpair e)`));
      thm arg_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`za:int`, `p:int`},
          (term_pair){`arg_:cm_expr`, `e:cm_expr`}),
          get_cm_expr_rep_def());
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(arg_view)));
      thm payload_view = by_rewrite(
          `cm_expr_payload (e:cm_expr)
             (za:int) (zb:int) (zargs:int) -|-
           fact(~(za == 0i) && zb == 0i && zargs == 0i) **
           cm_expr_node za (arg_:cm_expr)
             (cm_expr_payload arg_)`,
          THM_LIST(shape, get_cm_expr_payload_def()));
      thm payload_facts = conj_rule(
          assume_rule(`~((za:int) == 0i)`),
          conj_rule(assume_rule(`(zb:int) == 0i`),
            assume_rule(`(zargs:int) == 0i`)));
      thm payload_intro = frame_right_slrule(
          add_fact_hconv(payload_facts),
          `cm_expr_node (za:int) (arg_:cm_expr)
             (cm_expr_payload arg_)`);
      thm payload_fold = trans_slrule(payload_intro,
          eq2ent(sym_rule(payload_view)));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          payload_fold));
    }
  } else if (expr->kind == CMC_EXPR_EXIT) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`e:cm_expr`,
          get_cm_expr_exit_shape_ent()),
          assume_rule(`cm_rep_expr_kind (e:cm_expr) == 13i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`arg_:cm_expr`, `ty_:cm_type`))));
      thm shape = assume_rule(
          `e == CMExitE (arg_:cm_expr) (ty_:cm_type)`);
      thm safe = from_state_bool(
          `cm_rep_expr_temps_safe (e:cm_expr)`);
      thm opened_safe = conv_rule(rewrite_conv(THM_LIST(
          shape, get_cm_rep_expr_temps_safe_def())), safe);
      add_fact_st(eqt_intro_rule(conjunct1_rule(opened_safe)));
      add_fact_st(eqt_intro_rule(conjunct2_rule(opened_safe)));
      thm payload_view = by_rewrite(
          `cm_expr_payload (e:cm_expr)
             (za:int) (zb:int) (zargs:int) -|-
           fact(~(za == 0i) && zb == 0i && zargs == 0i) **
           cm_expr_node za (arg_:cm_expr)
             (cm_expr_payload arg_)`,
          THM_LIST(shape, get_cm_expr_payload_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(payload_view)));
      thm arg_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`za:int`, `p:int`},
          (term_pair){`arg_:cm_expr`, `e:cm_expr`}),
          get_cm_expr_rep_def());
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(arg_view))));
    }
    int child_lvalue;
    int child_rvalue;
    cm_expr_temps(expr->a, &child_lvalue, &child_rvalue);
    out_rvalue = child_rvalue;
    [[cst::proof]] {
      thm shape = assume_rule(
          `e == CMExitE (arg_:cm_expr) (ty_:cm_type)`);
      thm left_model = by_rewrite(
          `cm_tleft (cm_expr_tpair (e:cm_expr)) == 0i`,
          THM_LIST(shape, get_cm_expr_tpair_def(),
            get_cm_tleft_def()));
      add_fact_st(sym_rule(left_model));
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `out_lvalue__addr:addr`,
          `0i`, `cm_tleft (cm_expr_tpair e)`));
      thm right_model = by_rewrite(
          `cm_tright (cm_expr_tpair (e:cm_expr)) ==
           cm_tright (cm_expr_tpair (arg_:cm_expr))`,
          THM_LIST(shape, get_cm_expr_tpair_def(),
            get_cm_tright_def()));
      add_fact_st(sym_rule(right_model));
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `out_rvalue__addr:addr`,
          `cm_tright (cm_expr_tpair (arg_:cm_expr))`,
          `cm_tright (cm_expr_tpair e)`));
      thm arg_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`za:int`, `p:int`},
          (term_pair){`arg_:cm_expr`, `e:cm_expr`}),
          get_cm_expr_rep_def());
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(arg_view)));
      thm payload_view = by_rewrite(
          `cm_expr_payload (e:cm_expr)
             (za:int) (zb:int) (zargs:int) -|-
           fact(~(za == 0i) && zb == 0i && zargs == 0i) **
           cm_expr_node za (arg_:cm_expr)
             (cm_expr_payload arg_)`,
          THM_LIST(shape, get_cm_expr_payload_def()));
      thm payload_facts = conj_rule(
          assume_rule(`~((za:int) == 0i)`),
          conj_rule(assume_rule(`(zb:int) == 0i`),
            assume_rule(`(zargs:int) == 0i`)));
      thm payload_intro = frame_right_slrule(
          add_fact_hconv(payload_facts),
          `cm_expr_node (za:int) (arg_:cm_expr)
             (cm_expr_payload arg_)`);
      thm payload_fold = trans_slrule(payload_intro,
          eq2ent(sym_rule(payload_view)));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          payload_fold));
    }
  } else if (expr->kind == CMC_EXPR_CONST) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`e:cm_expr`,
          get_cm_expr_const_shape_ent()),
          assume_rule(`cm_rep_expr_kind (e:cm_expr) == 0i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`n_:int`, `ty_:cm_type`))));
      thm shape = assume_rule(
          `e == CMConstE (n_:int) (ty_:cm_type)`);
      thm left_model = by_rewrite(
          `cm_tleft (cm_expr_tpair (e:cm_expr)) == 0i`,
          THM_LIST(shape, get_cm_expr_tpair_def(),
            get_cm_tleft_def()));
      thm right_model = by_rewrite(
          `cm_tright (cm_expr_tpair (e:cm_expr)) == 0i`,
          THM_LIST(shape, get_cm_expr_tpair_def(),
            get_cm_tright_def()));
      add_fact_st(sym_rule(left_model));
      add_fact_st(sym_rule(right_model));
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `out_lvalue__addr:addr`,
          `0i`, `cm_tleft (cm_expr_tpair e)`));
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `out_rvalue__addr:addr`,
          `0i`, `cm_tright (cm_expr_tpair e)`));
    }
  } else if (expr->kind == CMC_EXPR_STRING) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`e:cm_expr`,
          get_cm_expr_string_shape_ent()),
          assume_rule(`cm_rep_expr_kind (e:cm_expr) == 1i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`sid_:int`, `ty_:cm_type`))));
      thm shape = assume_rule(
          `e == CMStringE (sid_:int) (ty_:cm_type)`);
      thm left_model = by_rewrite(
          `cm_tleft (cm_expr_tpair (e:cm_expr)) == 0i`,
          THM_LIST(shape, get_cm_expr_tpair_def(),
            get_cm_tleft_def()));
      thm right_model = by_rewrite(
          `cm_tright (cm_expr_tpair (e:cm_expr)) == 0i`,
          THM_LIST(shape, get_cm_expr_tpair_def(),
            get_cm_tright_def()));
      add_fact_st(sym_rule(left_model));
      add_fact_st(sym_rule(right_model));
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `out_lvalue__addr:addr`,
          `0i`, `cm_tleft (cm_expr_tpair e)`));
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `out_rvalue__addr:addr`,
          `0i`, `cm_tright (cm_expr_tpair e)`));
    }
  } else if (expr->kind == CMC_EXPR_VAR) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`e:cm_expr`,
          get_cm_expr_var_shape_ent()),
          assume_rule(`cm_rep_expr_kind (e:cm_expr) == 2i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`scope_:int`, `slot_:int`, `ty_:cm_type`))));
      thm shape = assume_rule(
          `e == CMVarE (scope_:int) (slot_:int) (ty_:cm_type)`);
      thm left_model = by_rewrite(
          `cm_tleft (cm_expr_tpair (e:cm_expr)) == 0i`,
          THM_LIST(shape, get_cm_expr_tpair_def(),
            get_cm_tleft_def()));
      thm right_model = by_rewrite(
          `cm_tright (cm_expr_tpair (e:cm_expr)) == 0i`,
          THM_LIST(shape, get_cm_expr_tpair_def(),
            get_cm_tright_def()));
      add_fact_st(sym_rule(left_model));
      add_fact_st(sym_rule(right_model));
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `out_lvalue__addr:addr`,
          `0i`, `cm_tleft (cm_expr_tpair e)`));
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `out_rvalue__addr:addr`,
          `0i`, `cm_tright (cm_expr_tpair e)`));
    }
  } else if (expr->kind == CMC_EXPR_SIZEOF) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`e:cm_expr`,
          get_cm_expr_sizeof_shape_ent()),
          assume_rule(`cm_rep_expr_kind (e:cm_expr) == 9i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`asked_:cm_type`, `ty_:cm_type`))));
      thm shape = assume_rule(
          `e == CMSizeofE (asked_:cm_type) (ty_:cm_type)`);
      thm left_model = by_rewrite(
          `cm_tleft (cm_expr_tpair (e:cm_expr)) == 0i`,
          THM_LIST(shape, get_cm_expr_tpair_def(),
            get_cm_tleft_def()));
      thm right_model = by_rewrite(
          `cm_tright (cm_expr_tpair (e:cm_expr)) == 0i`,
          THM_LIST(shape, get_cm_expr_tpair_def(),
            get_cm_tright_def()));
      add_fact_st(sym_rule(left_model));
      add_fact_st(sym_rule(right_model));
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `out_lvalue__addr:addr`,
          `0i`, `cm_tleft (cm_expr_tpair e)`));
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `out_rvalue__addr:addr`,
          `0i`, `cm_tright (cm_expr_tpair e)`));
    }
  } else if (expr->kind == CMC_EXPR_GETC) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`e:cm_expr`,
          get_cm_expr_getc_shape_ent()),
          assume_rule(`cm_rep_expr_kind (e:cm_expr) == 10i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`ty_:cm_type`))));
      thm shape = assume_rule(
          `e == CMGetcE (ty_:cm_type)`);
      thm left_model = by_rewrite(
          `cm_tleft (cm_expr_tpair (e:cm_expr)) == 0i`,
          THM_LIST(shape, get_cm_expr_tpair_def(),
            get_cm_tleft_def()));
      thm right_model = by_rewrite(
          `cm_tright (cm_expr_tpair (e:cm_expr)) == 0i`,
          THM_LIST(shape, get_cm_expr_tpair_def(),
            get_cm_tright_def()));
      add_fact_st(sym_rule(left_model));
      add_fact_st(sym_rule(right_model));
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `out_lvalue__addr:addr`,
          `0i`, `cm_tleft (cm_expr_tpair e)`));
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `out_rvalue__addr:addr`,
          `0i`, `cm_tright (cm_expr_tpair e)`));
    }
  } else {
    [[cst::proof]] {
      thm impossible = spec_rule(`e:cm_expr`,
          get_cm_rep_expr_kind_exhaustive());
      impossible = mp_rule(impossible,
          assume_rule(`~(cm_rep_expr_kind (e:cm_expr) == 0i)`));
      impossible = mp_rule(impossible,
          assume_rule(`~(cm_rep_expr_kind (e:cm_expr) == 1i)`));
      impossible = mp_rule(impossible,
          assume_rule(`~(cm_rep_expr_kind (e:cm_expr) == 2i)`));
      impossible = mp_rule(impossible,
          assume_rule(`~(cm_rep_expr_kind (e:cm_expr) == 3i)`));
      impossible = mp_rule(impossible,
          assume_rule(`~(cm_rep_expr_kind (e:cm_expr) == 4i)`));
      impossible = mp_rule(impossible,
          assume_rule(`~(cm_rep_expr_kind (e:cm_expr) == 5i)`));
      impossible = mp_rule(impossible,
          assume_rule(`~(cm_rep_expr_kind (e:cm_expr) == 6i)`));
      impossible = mp_rule(impossible,
          assume_rule(`~(cm_rep_expr_kind (e:cm_expr) == 7i)`));
      impossible = mp_rule(impossible,
          assume_rule(`~(cm_rep_expr_kind (e:cm_expr) == 8i)`));
      impossible = mp_rule(impossible,
          assume_rule(`~(cm_rep_expr_kind (e:cm_expr) == 9i)`));
      impossible = mp_rule(impossible,
          assume_rule(`~(cm_rep_expr_kind (e:cm_expr) == 10i)`));
      impossible = mp_rule(impossible,
          assume_rule(`~(cm_rep_expr_kind (e:cm_expr) == 11i)`));
      impossible = mp_rule(impossible,
          assume_rule(`~(cm_rep_expr_kind (e:cm_expr) == 12i)`));
      impossible = mp_rule(impossible,
          assume_rule(`~(cm_rep_expr_kind (e:cm_expr) == 13i)`));
      thm left_model = false_elim_rule(impossible,
          `0i == cm_tleft (cm_expr_tpair (e:cm_expr))`);
      thm right_model = false_elim_rule(impossible,
          `0i == cm_tright (cm_expr_tpair (e:cm_expr))`);
      add_fact_st(left_model);
      add_fact_st(right_model);
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `out_lvalue__addr:addr`,
          `0i`, `cm_tleft (cm_expr_tpair e)`));
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `out_rvalue__addr:addr`,
          `0i`, `cm_tright (cm_expr_tpair e)`));
      add_fact_st(eqt_intro_rule(impossible));
    }
  }
  *lvalue = out_lvalue;
  *rvalue = out_rvalue;
  [[cst::proof]] {
    apply_hconv_st(specl_rule(TERM_LIST(
        `expr__pre:int`, `e:cm_expr`, `za:int`, `zb:int`,
        `zargs:int`), get_cm_expr_close_witness()));
  }
}


static int cm_expr_rtemps(struct cm_expr *expr)
    [[cst::param(`e:cm_expr`)]]
    [[cst::require(
      `fact(cm_rep_expr_temps_safe e <=> true) **
       cm_expr_rep expr e`)]]
    [[cst::ensure(
      `fact(cm_rep_expr_temps_safe e <=> true) **
       cm_expr_rep expr e **
       fact((__return:int) == cm_tright (cm_expr_tpair e))`)]]
{
  int lvalue;
  int rvalue;
  cm_expr_temps(expr, &lvalue, &rvalue);
  return rvalue;
}

int cmc_stmt_temps(struct cm_stmt *stmt)
    [[cst::param(`s:cm_stmt`)]]
    [[cst::require(
      `fact(cm_rep_stmt_temps_safe s <=> true) **
       cm_stmt_rep stmt s`)]]
    [[cst::ensure(
      `fact(cm_rep_stmt_temps_safe s <=> true) **
       cm_stmt_rep stmt s **
       fact((__return:int) == cm_stemps s) **
       fact(0i <= cm_stemps s) **
       fact(cm_stemps s <= 2147483647i)`)]]
{
  [[cst::proof]] {
    apply_hconv_st(specl_rule(
        TERM_LIST(`stmt__pre:int`, `s:cm_stmt`),
        get_cm_stmt_open()));
  }
  int result = 0;
  if (stmt->kind == CMC_STMT_EXPR) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`s:cm_stmt`,
          get_cm_stmt_expr_shape_ent()),
          assume_rule(`cm_rep_stmt_kind (s:cm_stmt) == 1i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`expr_:cm_expr`))));
      thm shape = assume_rule(`s == CMExprS (expr_:cm_expr)`);
      thm parent_safe = conv_rule(rewrite_conv(THM_LIST(shape)),
          from_state_bool(`cm_rep_stmt_temps_safe (s:cm_stmt)`));
      thm safe = mp_rule(spec_rule(`expr_:cm_expr`,
          get_cm_rep_stmt_expr_child_safe()), parent_safe);
      add_fact_st(eqt_intro_rule(safe));
      thm payload_view = by_rewrite(
          `cm_stmt_payload (s:cm_stmt)
             (ze:int) (za:int) (zb:int) -|-
           fact(~(ze == 0i) && za == 0i && zb == 0i) **
           cm_expr_rep ze (expr_:cm_expr)`,
          THM_LIST(shape, get_cm_stmt_payload_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(payload_view)));
    }
    result = cm_expr_rtemps(stmt->expr);
    [[cst::proof]] {
      thm shape = assume_rule(`s == CMExprS (expr_:cm_expr)`);
      thm model = by_rewrite(
          `cm_stemps (s:cm_stmt) ==
           cm_tright (cm_expr_tpair (expr_:cm_expr))`,
          THM_LIST(shape, get_cm_stemps_def(),
            get_cm_rtemps_def()));
      thm result_model = trans_rule(
          assume_rule(
            `(retval:int) ==
             cm_tright (cm_expr_tpair (expr_:cm_expr))`),
          sym_rule(model));
      add_fact_st(result_model);
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `result__addr:addr`,
          `retval:int`, `cm_stemps (s:cm_stmt)`));
      thm payload_view = by_rewrite(
          `cm_stmt_payload (s:cm_stmt)
             (ze:int) (za:int) (zb:int) -|-
           fact(~(ze == 0i) && za == 0i && zb == 0i) **
           cm_expr_rep ze (expr_:cm_expr)`,
          THM_LIST(shape, get_cm_stmt_payload_def()));
      thm payload_facts = conj_rule(
          assume_rule(`~((ze:int) == 0i)`),
          conj_rule(assume_rule(`(za:int) == 0i`),
            assume_rule(`(zb:int) == 0i`)));
      thm payload_intro = frame_right_slrule(
          add_fact_hconv(payload_facts),
          `cm_expr_rep (ze:int) (expr_:cm_expr)`);
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          trans_slrule(payload_intro,
            eq2ent(sym_rule(payload_view)))));
    }
  } else if (stmt->kind == CMC_STMT_INIT) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`s:cm_stmt`,
          get_cm_stmt_init_shape_ent()),
          assume_rule(`cm_rep_stmt_kind (s:cm_stmt) == 3i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`init_slot_:int`, `init_expr_:cm_expr`))));
      thm shape = assume_rule(
          `s == CMInitS (init_slot_:int) (init_expr_:cm_expr)`);
      thm parent_safe = conv_rule(rewrite_conv(THM_LIST(shape)),
          from_state_bool(`cm_rep_stmt_temps_safe (s:cm_stmt)`));
      thm safe = mp_rule(specl_rule(
          TERM_LIST(`init_slot_:int`, `init_expr_:cm_expr`),
          get_cm_rep_stmt_init_child_safe()), parent_safe);
      add_fact_st(eqt_intro_rule(safe));
      thm payload_view = by_rewrite(
          `cm_stmt_payload (s:cm_stmt)
             (ze:int) (za:int) (zb:int) -|-
           fact(~(ze == 0i) && za == 0i && zb == 0i) **
           cm_expr_rep ze (init_expr_:cm_expr)`,
          THM_LIST(shape, get_cm_stmt_payload_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(payload_view)));
    }
    result = cm_expr_rtemps(stmt->expr);
    [[cst::proof]] {
      thm shape = assume_rule(
          `s == CMInitS (init_slot_:int) (init_expr_:cm_expr)`);
      thm model = by_rewrite(
          `cm_stemps (s:cm_stmt) ==
           cm_tright (cm_expr_tpair (init_expr_:cm_expr))`,
          THM_LIST(shape, get_cm_stemps_def(),
            get_cm_rtemps_def()));
      thm result_model = trans_rule(
          assume_rule(
            `(retval:int) ==
             cm_tright (cm_expr_tpair (init_expr_:cm_expr))`),
          sym_rule(model));
      add_fact_st(result_model);
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `result__addr:addr`,
          `retval:int`, `cm_stemps (s:cm_stmt)`));
      thm payload_view = by_rewrite(
          `cm_stmt_payload (s:cm_stmt)
             (ze:int) (za:int) (zb:int) -|-
           fact(~(ze == 0i) && za == 0i && zb == 0i) **
           cm_expr_rep ze (init_expr_:cm_expr)`,
          THM_LIST(shape, get_cm_stmt_payload_def()));
      thm payload_facts = conj_rule(
          assume_rule(`~((ze:int) == 0i)`),
          conj_rule(assume_rule(`(za:int) == 0i`),
            assume_rule(`(zb:int) == 0i`)));
      thm payload_intro = frame_right_slrule(
          add_fact_hconv(payload_facts),
          `cm_expr_rep (ze:int) (init_expr_:cm_expr)`);
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          trans_slrule(payload_intro,
            eq2ent(sym_rule(payload_view)))));
    }
  } else if (stmt->kind == CMC_STMT_RETURN) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`s:cm_stmt`,
          get_cm_stmt_return_shape_ent()),
          assume_rule(`cm_rep_stmt_kind (s:cm_stmt) == 10i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`return_expr_:cm_expr`))));
      thm shape = assume_rule(
          `s == CMReturnS (return_expr_:cm_expr)`);
      thm parent_safe = conv_rule(rewrite_conv(THM_LIST(shape)),
          from_state_bool(`cm_rep_stmt_temps_safe (s:cm_stmt)`));
      thm safe = mp_rule(spec_rule(`return_expr_:cm_expr`,
          get_cm_rep_stmt_return_child_safe()), parent_safe);
      add_fact_st(eqt_intro_rule(safe));
      thm payload_view = by_rewrite(
          `cm_stmt_payload (s:cm_stmt)
             (ze:int) (za:int) (zb:int) -|-
           fact(~(ze == 0i) && za == 0i && zb == 0i) **
           cm_expr_rep ze (return_expr_:cm_expr)`,
          THM_LIST(shape, get_cm_stmt_payload_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(payload_view)));
    }
    result = cm_expr_rtemps(stmt->expr);
    [[cst::proof]] {
      thm shape = assume_rule(
          `s == CMReturnS (return_expr_:cm_expr)`);
      thm model = by_rewrite(
          `cm_stemps (s:cm_stmt) ==
           cm_tright (cm_expr_tpair (return_expr_:cm_expr))`,
          THM_LIST(shape, get_cm_stemps_def(),
            get_cm_rtemps_def()));
      thm result_model = trans_rule(
          assume_rule(
            `(retval:int) ==
             cm_tright (cm_expr_tpair (return_expr_:cm_expr))`),
          sym_rule(model));
      add_fact_st(result_model);
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `result__addr:addr`,
          `retval:int`, `cm_stemps (s:cm_stmt)`));
      thm payload_view = by_rewrite(
          `cm_stmt_payload (s:cm_stmt)
             (ze:int) (za:int) (zb:int) -|-
           fact(~(ze == 0i) && za == 0i && zb == 0i) **
           cm_expr_rep ze (return_expr_:cm_expr)`,
          THM_LIST(shape, get_cm_stmt_payload_def()));
      thm payload_facts = conj_rule(
          assume_rule(`~((ze:int) == 0i)`),
          conj_rule(assume_rule(`(za:int) == 0i`),
            assume_rule(`(zb:int) == 0i`)));
      thm payload_intro = frame_right_slrule(
          add_fact_hconv(payload_facts),
          `cm_expr_rep (ze:int) (return_expr_:cm_expr)`);
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          trans_slrule(payload_intro,
            eq2ent(sym_rule(payload_view)))));
    }
  } else if (stmt->kind == CMC_STMT_SEQ) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`s:cm_stmt`,
          get_cm_stmt_seq_shape_ent()),
          assume_rule(`cm_rep_stmt_kind (s:cm_stmt) == 4i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`first_:cm_stmt`, `second_:cm_stmt`))));
      thm shape = assume_rule(
          `s == CMSeqS (first_:cm_stmt) (second_:cm_stmt)`);
      thm parent_safe = conv_rule(rewrite_conv(THM_LIST(shape)),
          from_state_bool(`cm_rep_stmt_temps_safe (s:cm_stmt)`));
      thm safe = mp_rule(specl_rule(
          TERM_LIST(`first_:cm_stmt`, `second_:cm_stmt`),
          get_cm_rep_stmt_seq_children_safe()), parent_safe);
      add_fact_st(eqt_intro_rule(conjunct1_rule(safe)));
      add_fact_st(eqt_intro_rule(conjunct2_rule(safe)));
      thm payload_view = by_rewrite(
          `cm_stmt_payload (s:cm_stmt)
             (ze:int) (za:int) (zb:int) -|-
           fact(ze == 0i) **
           cm_stmt_node za (first_:cm_stmt)
             (cm_stmt_payload first_) **
           cm_stmt_node zb (second_:cm_stmt)
             (cm_stmt_payload second_)`,
          THM_LIST(shape, get_cm_stmt_payload_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(payload_view)));
      thm first_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`za:int`, `p:int`},
          (term_pair){`first_:cm_stmt`, `s:cm_stmt`}),
          get_cm_stmt_rep_def());
      thm second_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`zb:int`, `p:int`},
          (term_pair){`second_:cm_stmt`, `s:cm_stmt`}),
          get_cm_stmt_rep_def());
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(first_view))));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(second_view))));
    }
    int first_temps = cmc_stmt_temps(stmt->a);
    int second_temps = cmc_stmt_temps(stmt->b);
    result = cm_max(first_temps, second_temps);
    [[cst::proof]] {
      thm shape = assume_rule(
          `s == CMSeqS (first_:cm_stmt) (second_:cm_stmt)`);
      thm model = by_rewrite(
          `cm_stemps (s:cm_stmt) ==
           cm_imax (cm_stemps (first_:cm_stmt))
             (cm_stemps (second_:cm_stmt))`,
          THM_LIST(shape, get_cm_stemps_def()));
      thm concrete = conv_rule(rewrite_conv(THM_LIST(
          assume_rule(`(retval:int) == cm_stemps (first_:cm_stmt)`),
          assume_rule(
            `(retval_1:int) == cm_stemps (second_:cm_stmt)`))),
          assume_rule(
            `(retval_2:int) == cm_imax (retval:int) (retval_1:int)`));
      thm result_model = trans_rule(concrete, sym_rule(model));
      add_fact_st(result_model);
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `result__addr:addr`,
          `retval_2:int`, `cm_stemps (s:cm_stmt)`));
      thm first_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`za:int`, `p:int`},
          (term_pair){`first_:cm_stmt`, `s:cm_stmt`}),
          get_cm_stmt_rep_def());
      thm second_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`zb:int`, `p:int`},
          (term_pair){`second_:cm_stmt`, `s:cm_stmt`}),
          get_cm_stmt_rep_def());
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(first_view)));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(second_view)));
      thm payload_view = by_rewrite(
          `cm_stmt_payload (s:cm_stmt)
             (ze:int) (za:int) (zb:int) -|-
           fact(ze == 0i) **
           cm_stmt_node za (first_:cm_stmt)
             (cm_stmt_payload first_) **
           cm_stmt_node zb (second_:cm_stmt)
             (cm_stmt_payload second_)`,
          THM_LIST(shape, get_cm_stmt_payload_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(payload_view))));
    }
  } else if (stmt->kind == CMC_STMT_BLOCK) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`s:cm_stmt`,
          get_cm_stmt_block_shape_ent()),
          assume_rule(`cm_rep_stmt_kind (s:cm_stmt) == 5i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`body_:cm_stmt`))));
      thm shape = assume_rule(`s == CMBlockS (body_:cm_stmt)`);
      thm parent_safe = conv_rule(rewrite_conv(THM_LIST(shape)),
          from_state_bool(`cm_rep_stmt_temps_safe (s:cm_stmt)`));
      thm safe = mp_rule(spec_rule(`body_:cm_stmt`,
          get_cm_rep_stmt_block_child_safe()), parent_safe);
      add_fact_st(eqt_intro_rule(safe));
      thm payload_view = by_rewrite(
          `cm_stmt_payload (s:cm_stmt)
             (ze:int) (za:int) (zb:int) -|-
           fact(ze == 0i && ~(za == 0i) && zb == 0i) **
           cm_stmt_node za (body_:cm_stmt)
             (cm_stmt_payload body_)`,
          THM_LIST(shape, get_cm_stmt_payload_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(payload_view)));
      thm body_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`za:int`, `p:int`},
          (term_pair){`body_:cm_stmt`, `s:cm_stmt`}),
          get_cm_stmt_rep_def());
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(body_view))));
    }
    result = cmc_stmt_temps(stmt->a);
    [[cst::proof]] {
      thm shape = assume_rule(`s == CMBlockS (body_:cm_stmt)`);
      thm model = by_rewrite(
          `cm_stemps (s:cm_stmt) == cm_stemps (body_:cm_stmt)`,
          THM_LIST(shape, get_cm_stemps_def()));
      thm result_model = trans_rule(
          assume_rule(`(retval:int) == cm_stemps (body_:cm_stmt)`),
          sym_rule(model));
      add_fact_st(result_model);
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `result__addr:addr`,
          `retval:int`, `cm_stemps (s:cm_stmt)`));
      thm body_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`za:int`, `p:int`},
          (term_pair){`body_:cm_stmt`, `s:cm_stmt`}),
          get_cm_stmt_rep_def());
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(body_view)));
      thm payload_view = by_rewrite(
          `cm_stmt_payload (s:cm_stmt)
             (ze:int) (za:int) (zb:int) -|-
           fact(ze == 0i && ~(za == 0i) && zb == 0i) **
           cm_stmt_node za (body_:cm_stmt)
             (cm_stmt_payload body_)`,
          THM_LIST(shape, get_cm_stmt_payload_def()));
      thm payload_facts = conj_rule(
          assume_rule(`(ze:int) == 0i`),
          conj_rule(assume_rule(`~((za:int) == 0i)`),
            assume_rule(`(zb:int) == 0i`)));
      thm payload_intro = frame_right_slrule(
          add_fact_hconv(payload_facts),
          `cm_stmt_node (za:int) (body_:cm_stmt)
             (cm_stmt_payload body_)`);
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          trans_slrule(payload_intro,
            eq2ent(sym_rule(payload_view)))));
    }
  } else if (stmt->kind == CMC_STMT_IF) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`s:cm_stmt`,
          get_cm_stmt_if_shape_ent()),
          assume_rule(`cm_rep_stmt_kind (s:cm_stmt) == 6i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`guard_:cm_expr`, `yes_:cm_stmt`,
              `no_:cm_stmt`))));
      thm shape = assume_rule(
          `s == CMIfS (guard_:cm_expr) (yes_:cm_stmt)
             (no_:cm_stmt)`);
      thm parent_safe = conv_rule(rewrite_conv(THM_LIST(shape)),
          from_state_bool(`cm_rep_stmt_temps_safe (s:cm_stmt)`));
      thm safe = mp_rule(specl_rule(
          TERM_LIST(`guard_:cm_expr`, `yes_:cm_stmt`,
            `no_:cm_stmt`),
          get_cm_rep_stmt_if_children_safe()), parent_safe);
      add_fact_st(eqt_intro_rule(conjunct1_rule(safe)));
      add_fact_st(eqt_intro_rule(
          conjunct1_rule(conjunct2_rule(safe))));
      add_fact_st(eqt_intro_rule(
          conjunct2_rule(conjunct2_rule(safe))));
      thm payload_view = by_rewrite(
          `cm_stmt_payload (s:cm_stmt)
             (ze:int) (za:int) (zb:int) -|-
           cm_expr_rep ze (guard_:cm_expr) **
           cm_stmt_node za (yes_:cm_stmt)
             (cm_stmt_payload yes_) **
           cm_stmt_node zb (no_:cm_stmt)
             (cm_stmt_payload no_)`,
          THM_LIST(shape, get_cm_stmt_payload_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(payload_view)));
      thm yes_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`za:int`, `p:int`},
          (term_pair){`yes_:cm_stmt`, `s:cm_stmt`}),
          get_cm_stmt_rep_def());
      thm no_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`zb:int`, `p:int`},
          (term_pair){`no_:cm_stmt`, `s:cm_stmt`}),
          get_cm_stmt_rep_def());
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(yes_view))));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(no_view))));
    }
    int guard_temps = cm_expr_rtemps(stmt->expr);
    int yes_temps = cmc_stmt_temps(stmt->a);
    int no_temps = cmc_stmt_temps(stmt->b);
    int branch_temps = cm_max(yes_temps, no_temps);
    result = cm_max(guard_temps, branch_temps);
    [[cst::proof]] {
      thm shape = assume_rule(
          `s == CMIfS (guard_:cm_expr) (yes_:cm_stmt)
             (no_:cm_stmt)`);
      thm model = by_rewrite(
          `cm_stemps (s:cm_stmt) ==
           cm_imax
             (cm_tright (cm_expr_tpair (guard_:cm_expr)))
             (cm_imax (cm_stemps (yes_:cm_stmt))
               (cm_stemps (no_:cm_stmt)))`,
          THM_LIST(shape, get_cm_stemps_def(),
            get_cm_rtemps_def()));
      thm concrete = conv_rule(rewrite_conv(THM_LIST(
          assume_rule(
            `(retval:int) ==
             cm_tright (cm_expr_tpair (guard_:cm_expr))`),
          assume_rule(
            `(retval_1:int) == cm_stemps (yes_:cm_stmt)`),
          assume_rule(
            `(retval_2:int) == cm_stemps (no_:cm_stmt)`),
          assume_rule(
            `(retval_3:int) ==
             cm_imax (retval_1:int) (retval_2:int)`))),
          assume_rule(
            `(retval_4:int) ==
             cm_imax (retval:int) (retval_3:int)`));
      thm result_model = trans_rule(concrete, sym_rule(model));
      add_fact_st(result_model);
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `result__addr:addr`,
          `retval_4:int`, `cm_stemps (s:cm_stmt)`));
      thm yes_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`za:int`, `p:int`},
          (term_pair){`yes_:cm_stmt`, `s:cm_stmt`}),
          get_cm_stmt_rep_def());
      thm no_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`zb:int`, `p:int`},
          (term_pair){`no_:cm_stmt`, `s:cm_stmt`}),
          get_cm_stmt_rep_def());
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(yes_view)));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(no_view)));
      thm payload_view = by_rewrite(
          `cm_stmt_payload (s:cm_stmt)
             (ze:int) (za:int) (zb:int) -|-
           cm_expr_rep ze (guard_:cm_expr) **
           cm_stmt_node za (yes_:cm_stmt)
             (cm_stmt_payload yes_) **
           cm_stmt_node zb (no_:cm_stmt)
             (cm_stmt_payload no_)`,
          THM_LIST(shape, get_cm_stmt_payload_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(payload_view))));
    }
  } else if (stmt->kind == CMC_STMT_WHILE) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`s:cm_stmt`,
          get_cm_stmt_while_shape_ent()),
          assume_rule(`cm_rep_stmt_kind (s:cm_stmt) == 7i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`while_guard_:cm_expr`,
              `while_body_:cm_stmt`))));
      thm shape = assume_rule(
          `s == CMWhileS (while_guard_:cm_expr)
             (while_body_:cm_stmt)`);
      thm parent_safe = conv_rule(rewrite_conv(THM_LIST(shape)),
          from_state_bool(`cm_rep_stmt_temps_safe (s:cm_stmt)`));
      thm safe = mp_rule(specl_rule(
          TERM_LIST(`while_guard_:cm_expr`,
            `while_body_:cm_stmt`),
          get_cm_rep_stmt_while_children_safe()), parent_safe);
      add_fact_st(eqt_intro_rule(conjunct1_rule(safe)));
      add_fact_st(eqt_intro_rule(conjunct2_rule(safe)));
      thm payload_view = by_rewrite(
          `cm_stmt_payload (s:cm_stmt)
             (ze:int) (za:int) (zb:int) -|-
           fact(~(ze == 0i) && ~(za == 0i) && zb == 0i) **
           cm_expr_rep ze (while_guard_:cm_expr) **
           cm_stmt_node za (while_body_:cm_stmt)
             (cm_stmt_payload while_body_)`,
          THM_LIST(shape, get_cm_stmt_payload_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(payload_view)));
      thm body_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`za:int`, `p:int`},
          (term_pair){`while_body_:cm_stmt`, `s:cm_stmt`}),
          get_cm_stmt_rep_def());
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(body_view))));
    }
    int guard_temps = cm_expr_rtemps(stmt->expr);
    int body_temps = cmc_stmt_temps(stmt->a);
    result = cm_max(guard_temps, body_temps);
    [[cst::proof]] {
      thm shape = assume_rule(
          `s == CMWhileS (while_guard_:cm_expr)
             (while_body_:cm_stmt)`);
      thm model = by_rewrite(
          `cm_stemps (s:cm_stmt) ==
           cm_imax
             (cm_tright (cm_expr_tpair (while_guard_:cm_expr)))
             (cm_stemps (while_body_:cm_stmt))`,
          THM_LIST(shape, get_cm_stemps_def(),
            get_cm_rtemps_def()));
      thm concrete = conv_rule(rewrite_conv(THM_LIST(
          assume_rule(
            `(retval:int) ==
             cm_tright (cm_expr_tpair (while_guard_:cm_expr))`),
          assume_rule(
            `(retval_1:int) == cm_stemps (while_body_:cm_stmt)`))),
          assume_rule(
            `(retval_2:int) ==
             cm_imax (retval:int) (retval_1:int)`));
      thm result_model = trans_rule(concrete, sym_rule(model));
      add_fact_st(result_model);
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `result__addr:addr`,
          `retval_2:int`, `cm_stemps (s:cm_stmt)`));
      thm body_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`za:int`, `p:int`},
          (term_pair){`while_body_:cm_stmt`, `s:cm_stmt`}),
          get_cm_stmt_rep_def());
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(body_view)));
      thm payload_view = by_rewrite(
          `cm_stmt_payload (s:cm_stmt)
             (ze:int) (za:int) (zb:int) -|-
           fact(~(ze == 0i) && ~(za == 0i) && zb == 0i) **
           cm_expr_rep ze (while_guard_:cm_expr) **
           cm_stmt_node za (while_body_:cm_stmt)
             (cm_stmt_payload while_body_)`,
          THM_LIST(shape, get_cm_stmt_payload_def()));
      thm payload_facts = conj_rule(
          assume_rule(`~((ze:int) == 0i)`),
          conj_rule(assume_rule(`~((za:int) == 0i)`),
            assume_rule(`(zb:int) == 0i`)));
      thm payload_intro = frame_right_slrule(
          add_fact_hconv(payload_facts),
          `cm_expr_rep (ze:int) (while_guard_:cm_expr) **
           cm_stmt_node (za:int) (while_body_:cm_stmt)
             (cm_stmt_payload while_body_)`);
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          trans_slrule(payload_intro,
            eq2ent(sym_rule(payload_view)))));
    }
  } else if (stmt->kind == CMC_STMT_SKIP) {
    result = 0;
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`s:cm_stmt`,
          get_cm_stmt_skip_shape_ent()),
          assume_rule(`cm_rep_stmt_kind (s:cm_stmt) == 0i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          shape_ent));
      thm shape = assume_rule(`s == CMSkipS`);
      thm model = by_rewrite(`cm_stemps (s:cm_stmt) == 0i`,
          THM_LIST(shape, get_cm_stemps_def()));
      add_fact_st(sym_rule(model));
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `result__addr:addr`,
          `0i`, `cm_stemps (s:cm_stmt)`));
    }
  } else if (stmt->kind == CMC_STMT_DECL) {
    result = 0;
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`s:cm_stmt`,
          get_cm_stmt_decl_shape_ent()),
          assume_rule(`cm_rep_stmt_kind (s:cm_stmt) == 2i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`decl_slot_:int`))));
      thm shape = assume_rule(`s == CMDeclS (decl_slot_:int)`);
      thm model = by_rewrite(`cm_stemps (s:cm_stmt) == 0i`,
          THM_LIST(shape, get_cm_stemps_def()));
      add_fact_st(sym_rule(model));
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `result__addr:addr`,
          `0i`, `cm_stemps (s:cm_stmt)`));
    }
  } else if (stmt->kind == CMC_STMT_BREAK) {
    result = 0;
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`s:cm_stmt`,
          get_cm_stmt_break_shape_ent()),
          assume_rule(`cm_rep_stmt_kind (s:cm_stmt) == 8i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          shape_ent));
      thm shape = assume_rule(`s == CMBreakS`);
      thm model = by_rewrite(`cm_stemps (s:cm_stmt) == 0i`,
          THM_LIST(shape, get_cm_stemps_def()));
      add_fact_st(sym_rule(model));
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `result__addr:addr`,
          `0i`, `cm_stemps (s:cm_stmt)`));
    }
  } else if (stmt->kind == CMC_STMT_CONTINUE) {
    result = 0;
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`s:cm_stmt`,
          get_cm_stmt_continue_shape_ent()),
          assume_rule(`cm_rep_stmt_kind (s:cm_stmt) == 9i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          shape_ent));
      thm shape = assume_rule(`s == CMContinueS`);
      thm model = by_rewrite(`cm_stemps (s:cm_stmt) == 0i`,
          THM_LIST(shape, get_cm_stemps_def()));
      add_fact_st(sym_rule(model));
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `result__addr:addr`,
          `0i`, `cm_stemps (s:cm_stmt)`));
    }
  } else {
    result = 0;
    [[cst::proof]] {
      thm impossible = spec_rule(`s:cm_stmt`,
          get_cm_rep_stmt_kind_exhaustive());
      impossible = mp_rule(impossible,
          assume_rule(`~(cm_rep_stmt_kind (s:cm_stmt) == 0i)`));
      impossible = mp_rule(impossible,
          assume_rule(`~(cm_rep_stmt_kind (s:cm_stmt) == 1i)`));
      impossible = mp_rule(impossible,
          assume_rule(`~(cm_rep_stmt_kind (s:cm_stmt) == 2i)`));
      impossible = mp_rule(impossible,
          assume_rule(`~(cm_rep_stmt_kind (s:cm_stmt) == 3i)`));
      impossible = mp_rule(impossible,
          assume_rule(`~(cm_rep_stmt_kind (s:cm_stmt) == 4i)`));
      impossible = mp_rule(impossible,
          assume_rule(`~(cm_rep_stmt_kind (s:cm_stmt) == 5i)`));
      impossible = mp_rule(impossible,
          assume_rule(`~(cm_rep_stmt_kind (s:cm_stmt) == 6i)`));
      impossible = mp_rule(impossible,
          assume_rule(`~(cm_rep_stmt_kind (s:cm_stmt) == 7i)`));
      impossible = mp_rule(impossible,
          assume_rule(`~(cm_rep_stmt_kind (s:cm_stmt) == 8i)`));
      impossible = mp_rule(impossible,
          assume_rule(`~(cm_rep_stmt_kind (s:cm_stmt) == 9i)`));
      impossible = mp_rule(impossible,
          assume_rule(`~(cm_rep_stmt_kind (s:cm_stmt) == 10i)`));
      thm model = false_elim_rule(impossible,
          `0i == cm_stemps (s:cm_stmt)`);
      add_fact_st(model);
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `result__addr:addr`,
          `0i`, `cm_stemps (s:cm_stmt)`));
      add_fact_st(eqt_intro_rule(impossible));
    }
  }
  [[cst::proof]] {
    apply_hconv_st(specl_rule(TERM_LIST(
        `stmt__pre:int`, `s:cm_stmt`, `ze:int`, `za:int`,
        `zb:int`), get_cm_stmt_close_witness()));
    thm bounds = mp_rule(spec_rule(`s:cm_stmt`,
        get_cm_rep_stmt_temps_safe_bounds()),
        from_state_bool(`cm_rep_stmt_temps_safe (s:cm_stmt)`));
    add_fact_st(conjunct1_rule(bounds));
    add_fact_st(conjunct2_rule(bounds));
  }
  return result;
}

long long cmc_frame_size(struct cm_function *fn)
    [[cst::param(`params:(cm_slot_d)list`,
                 `locals:(cm_slot_d)list`, `body:cm_stmt`,
                 `zp:int`, `zl:int`, `zb:int`)]]
    [[cst::require(
      `fact(cm_rep_members_safe params <=> true) **
       fact(cm_rep_members_safe locals <=> true) **
       fact(cm_rep_stmt_temps_safe body <=> true) **
       fact(8i + cm_rep_members_size params +
         cm_rep_members_size locals + 8i * cm_stemps body <=
         2147483647i) **
       data_at (field_addr fn Tcm_function Fparams) Tptr zp **
       data_at (field_addr fn Tcm_function Flocals) Tptr zl **
       data_at (field_addr fn Tcm_function Fbody) Tptr zb **
       cm_slot_list_rep zp params **
       cm_slot_list_rep zl locals **
       cm_stmt_rep zb body`)]]
    [[cst::ensure(
      `fact(cm_rep_members_safe params <=> true) **
       fact(cm_rep_members_safe locals <=> true) **
       fact(cm_rep_stmt_temps_safe body <=> true) **
       fact(8i + cm_rep_members_size params +
         cm_rep_members_size locals + 8i * cm_stemps body <=
         2147483647i) **
       data_at (field_addr fn Tcm_function Fparams) Tptr zp **
       data_at (field_addr fn Tcm_function Flocals) Tptr zl **
       data_at (field_addr fn Tcm_function Fbody) Tptr zb **
       cm_slot_list_rep zp params **
       cm_slot_list_rep zl locals **
       cm_stmt_rep zb body **
       fact((__return:int) == 8i + cm_rep_members_size params +
         cm_rep_members_size locals + 8i * cm_stemps body)`)]]
{
  long long params_size = cmc_slots_size(fn->params);
  [[cst::proof]] {
    cst_set_symbolic_state(retarget_cell64_st(
        cst_get_symbolic_state(), `params_size__addr:addr`,
        `retval:int`, `cm_rep_members_size params`));
  }
  long long locals_size = cmc_slots_size(fn->locals);
  [[cst::proof]] {
    cst_set_symbolic_state(retarget_cell64_st(
        cst_get_symbolic_state(), `locals_size__addr:addr`,
        `retval_1:int`, `cm_rep_members_size locals`));
  }
  int temps = cmc_stmt_temps(fn->body);
  [[cst::proof]] {
    cst_set_symbolic_state(retarget_cell_st(
        cst_get_symbolic_state(), `temps__addr:addr`,
        `retval_1:int`, `cm_stemps body`));
    add_arith_fact_st(cst_get_symbolic_state(),
        "0i <= cm_rep_members_size (params:(cm_slot_d)list) ==>"
        "0i <= cm_rep_members_size (locals:(cm_slot_d)list) ==>"
        "0i <= cm_stemps (body:cm_stmt) ==>"
        "8i + cm_rep_members_size params + cm_rep_members_size locals +"
        " 8i * cm_stemps body <= 2147483647i ==>"
        "(--9223372036854775808i <= 8i + cm_rep_members_size params &&"
        " 8i + cm_rep_members_size params <= 9223372036854775807i &&"
        " --9223372036854775808i <="
        "   (8i + cm_rep_members_size params) +"
        "     cm_rep_members_size locals &&"
        " (8i + cm_rep_members_size params) +"
        "   cm_rep_members_size locals <= 9223372036854775807i &&"
        " --9223372036854775808i <= 8i * cm_stemps body &&"
        " 8i * cm_stemps body <= 9223372036854775807i &&"
        " --9223372036854775808i <="
        "   ((8i + cm_rep_members_size params) +"
        "     cm_rep_members_size locals) + 8i * cm_stemps body &&"
        " ((8i + cm_rep_members_size params) +"
        "   cm_rep_members_size locals) + 8i * cm_stemps body <="
        "   9223372036854775807i)");
  }
  return 8 + params_size + locals_size + 8LL * temps;
}

long long cmc_param_offset(struct cm_function *fn, int slot)
    [[cst::param(`params:(cm_slot_d)list`, `zp:int`)]]
    [[cst::require(
      `fact(0i <= slot) **
       fact(cm_rep_members_safe params <=> true) **
       data_at (field_addr fn Tcm_function Fparams) Tptr zp **
       cm_slot_list_rep zp params`)]]
    [[cst::ensure(
      `fact(0i <= slot) **
       fact(cm_rep_members_safe params <=> true) **
       data_at (field_addr fn Tcm_function Fparams) Tptr zp **
       cm_slot_list_rep zp params **
       fact((__return:int) == 8i + cm_rep_member_prefix params slot)`)]]
{
  long long prefix = cmc_slots_prefix(fn->params, slot);
  [[cst::proof]] {
    cst_set_symbolic_state(retarget_cell64_st(
        cst_get_symbolic_state(), `prefix__addr:addr`,
        `retval:int`, `cm_rep_member_prefix params slot__pre`));
    add_arith_fact_st(cst_get_symbolic_state(),
        "0i <= cm_rep_member_prefix (params:(cm_slot_d)list)"
        " (slot__pre:int) ==>"
        "cm_rep_member_prefix params slot__pre <= 1048576i ==>"
        "(--9223372036854775808i <="
        "   8i + cm_rep_member_prefix params slot__pre &&"
        " 8i + cm_rep_member_prefix params slot__pre <="
        "   9223372036854775807i)");
  }
  return 8 + prefix;
}

long long cmc_local_offset(struct cm_function *fn, int slot)
    [[cst::param(`params:(cm_slot_d)list`,
                 `locals:(cm_slot_d)list`, `zp:int`, `zl:int`)]]
    [[cst::require(
      `fact(0i <= slot) **
       fact(cm_rep_members_safe params <=> true) **
       fact(cm_rep_members_safe locals <=> true) **
       data_at (field_addr fn Tcm_function Fparams) Tptr zp **
       data_at (field_addr fn Tcm_function Flocals) Tptr zl **
       cm_slot_list_rep zp params **
       cm_slot_list_rep zl locals`)]]
    [[cst::ensure(
      `fact(0i <= slot) **
       fact(cm_rep_members_safe params <=> true) **
       fact(cm_rep_members_safe locals <=> true) **
       data_at (field_addr fn Tcm_function Fparams) Tptr zp **
       data_at (field_addr fn Tcm_function Flocals) Tptr zl **
       cm_slot_list_rep zp params **
       cm_slot_list_rep zl locals **
       fact((__return:int) == 8i + cm_rep_members_size params +
         cm_rep_member_prefix locals slot)`)]]
{
  long long params_size = cmc_slots_size(fn->params);
  [[cst::proof]] {
    cst_set_symbolic_state(retarget_cell64_st(
        cst_get_symbolic_state(), `params_size__addr:addr`,
        `retval:int`, `cm_rep_members_size params`));
  }
  long long prefix = cmc_slots_prefix(fn->locals, slot);
  [[cst::proof]] {
    cst_set_symbolic_state(retarget_cell64_st(
        cst_get_symbolic_state(), `prefix__addr:addr`,
        `retval_1:int`, `cm_rep_member_prefix locals slot__pre`));
    add_arith_fact_st(cst_get_symbolic_state(),
        "0i <= cm_rep_members_size (params:(cm_slot_d)list) ==>"
        "cm_rep_members_size params <= 1048576i ==>"
        "0i <= cm_rep_member_prefix (locals:(cm_slot_d)list)"
        " (slot__pre:int) ==>"
        "cm_rep_member_prefix locals slot__pre <= 1048576i ==>"
        "(--9223372036854775808i <= 8i + cm_rep_members_size params &&"
        " 8i + cm_rep_members_size params <= 9223372036854775807i &&"
        " --9223372036854775808i <="
        "   (8i + cm_rep_members_size params) +"
        "     cm_rep_member_prefix locals slot__pre &&"
        " (8i + cm_rep_members_size params) +"
        "   cm_rep_member_prefix locals slot__pre <="
        "     9223372036854775807i)");
  }
  return 8 + params_size + prefix;
}

long long cmc_temp_offset(struct cm_function *fn, int temp)
    [[cst::param(`params:(cm_slot_d)list`,
                 `locals:(cm_slot_d)list`, `zp:int`, `zl:int`)]]
    [[cst::require(
      `fact(0i <= temp) **
       fact(8i + cm_rep_members_size params +
         cm_rep_members_size locals + 8i * temp <= 2147483647i) **
       fact(cm_rep_members_safe params <=> true) **
       fact(cm_rep_members_safe locals <=> true) **
       data_at (field_addr fn Tcm_function Fparams) Tptr zp **
       data_at (field_addr fn Tcm_function Flocals) Tptr zl **
       cm_slot_list_rep zp params **
       cm_slot_list_rep zl locals`)]]
    [[cst::ensure(
      `fact(0i <= temp) **
       fact(8i + cm_rep_members_size params +
         cm_rep_members_size locals + 8i * temp <= 2147483647i) **
       fact(cm_rep_members_safe params <=> true) **
       fact(cm_rep_members_safe locals <=> true) **
       data_at (field_addr fn Tcm_function Fparams) Tptr zp **
       data_at (field_addr fn Tcm_function Flocals) Tptr zl **
       cm_slot_list_rep zp params **
       cm_slot_list_rep zl locals **
       fact((__return:int) == 8i + cm_rep_members_size params +
         cm_rep_members_size locals + 8i * temp)`)]]
{
  long long params_size = cmc_slots_size(fn->params);
  [[cst::proof]] {
    cst_set_symbolic_state(retarget_cell64_st(
        cst_get_symbolic_state(), `params_size__addr:addr`,
        `retval:int`, `cm_rep_members_size params`));
  }
  long long locals_size = cmc_slots_size(fn->locals);
  [[cst::proof]] {
    cst_set_symbolic_state(retarget_cell64_st(
        cst_get_symbolic_state(), `locals_size__addr:addr`,
        `retval_1:int`, `cm_rep_members_size locals`));
    add_arith_fact_st(cst_get_symbolic_state(),
        "0i <= cm_rep_members_size (params:(cm_slot_d)list) ==>"
        "0i <= cm_rep_members_size (locals:(cm_slot_d)list) ==>"
        "0i <= (temp__pre:int) ==>"
        "8i + cm_rep_members_size params + cm_rep_members_size locals +"
        " 8i * temp__pre <= 2147483647i ==>"
        "(--9223372036854775808i <= 8i + cm_rep_members_size params &&"
        " 8i + cm_rep_members_size params <= 9223372036854775807i &&"
        " --9223372036854775808i <="
        "   (8i + cm_rep_members_size params) +"
        "     cm_rep_members_size locals &&"
        " (8i + cm_rep_members_size params) +"
        "   cm_rep_members_size locals <= 9223372036854775807i &&"
        " --9223372036854775808i <= 8i * temp__pre &&"
        " 8i * temp__pre <= 9223372036854775807i &&"
        " --9223372036854775808i <="
        "   ((8i + cm_rep_members_size params) +"
        "     cm_rep_members_size locals) + 8i * temp__pre &&"
        " ((8i + cm_rep_members_size params) +"
        "   cm_rep_members_size locals) + 8i * temp__pre <="
        "   9223372036854775807i)");
  }
  return 8 + params_size + locals_size + 8LL * temp;
}

int cm_normalize_count(int ty)
    [[cst::require(`emp`)]]
    [[cst::ensure(
      `fact((__return:int) == cm_normalize_code_value ty)`)]]
{
  int result;
  if (ty == CMC_TYPE_CHAR) {
    result = 6;
    [[cst::proof]] {
      add_fact_st(sym_rule(by_rewrite(
          `cm_normalize_code_value (ty__pre:int) == 6i`,
          THM_LIST(assume_rule(`ty__pre == 1i`),
            cm_normalize_code_value_def))));
    }
  } else {
    result = 0;
    [[cst::proof]] {
      add_fact_st(sym_rule(by_rewrite(
          `cm_normalize_code_value (ty__pre:int) == 0i`,
          THM_LIST(assume_rule(`~(ty__pre == 1i)`),
            cm_normalize_code_value_def))));
    }
  }
  return result;
}
