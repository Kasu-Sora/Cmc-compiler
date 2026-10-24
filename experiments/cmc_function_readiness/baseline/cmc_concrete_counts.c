#include "cmc_concrete_counts.h"
#include "cmc_stack_local_syntax.h"
#require "cmc_stack_local_syntax.c"


PROOF thm cm_args_tail_slots_def = new_fun_definition(
    `cm_args_tail_slots (slots:(cm_slot_d)list) : (cm_slot_d)list =
       TL slots`);
PROOF int _e_cm_args_tail_slots =
    cst_add_const_to_header(`cm_args_tail_slots`);


static void cmc_expr_type_code_value(struct cm_expr *expr, int *code)
    [[cst::param(`e:cm_expr`)]]
    [[cst::require(
      `cm_expr_rep expr e ** undef_data_at code Tint`)]]
    [[cst::ensure(
      `cm_expr_rep expr e **
       data_at code Tint (cm_type_encode (cm_expr_type e))`)]]
{
  [[cst::proof]] {
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        specl_rule(TERM_LIST(`expr__pre:int`, `e:cm_expr`),
          get_cm_expr_open())));
  }
  *code = expr->ty;
  [[cst::proof]] {
    apply_hconv_st(specl_rule(TERM_LIST(
        `expr__pre:int`, `e:cm_expr`, `za:int`, `zb:int`,
        `zargs:int`), get_cm_expr_close_witness()));
  }
}

static void cm_expr_counts(struct cm_program *program, int fid,
                           struct cm_function *fn,
                           struct cm_expr *expr, int *lvalue, int *rvalue)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `e:cm_expr`,
                 `structs:(cm_struct_d)list`,
                 `globals:(cm_global_d)list`,
                 `locals:(cm_slot_d)list`,
                 `zs:int`, `zg:int`, `zl:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(structs == cm_program_structs p) **
       fact(globals == cm_program_globals p) **
       fact(locals == cm_function_locals f) **
       fact(cm_expr_wf p f e <=> true) **
       fact(cm_expr_counts_representable p fid e <=> true) **
       fact(cm_rep_structs_safe structs <=> true) **
       data_at (field_addr program Tcm_program Fstructs) Tptr zs **
       cm_struct_list_rep zs structs **
       data_at (field_addr program Tcm_program Fglobals) Tptr zg **
       cm_global_list_rep zg globals **
       data_at (field_addr fn Tcm_function Flocals) Tptr zl **
       cm_slot_list_rep zl locals **
       cm_expr_rep expr e **
       undef_data_at lvalue Tint **
       undef_data_at rvalue Tint`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(structs == cm_program_structs p) **
       fact(globals == cm_program_globals p) **
       fact(locals == cm_function_locals f) **
       fact(cm_expr_wf p f e <=> true) **
       fact(cm_expr_counts_representable p fid e <=> true) **
       fact(cm_type_code_wf (cm_expr_type e) <=> true) **
       fact(cm_i32_code_count
         (cm_type_encode (cm_expr_type e)) <=> true) **
       fact(cm_rep_structs_safe structs <=> true) **
       data_at (field_addr program Tcm_program Fstructs) Tptr zs **
       cm_struct_list_rep zs structs **
       data_at (field_addr program Tcm_program Fglobals) Tptr zg **
       cm_global_list_rep zg globals **
       data_at (field_addr fn Tcm_function Flocals) Tptr zl **
       cm_slot_list_rep zl locals **
       cm_expr_rep expr e **
       data_at lvalue Tint
         (cm_lcount_of (cm_expr_code_counts p fid e)) **
       data_at rvalue Tint
         (cm_rcount_of (cm_expr_code_counts p fid e)) **
       fact(cm_i32_code_count
         (cm_lcount_of (cm_expr_code_counts p fid e)) <=> true) **
       fact(cm_i32_code_count
         (cm_rcount_of (cm_expr_code_counts p fid e)) <=> true)`)]];

int cm_expr_lvalue_count(struct cm_program *program, int fid,
                                struct cm_function *fn,
                                struct cm_expr *expr)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `e:cm_expr`,
                 `structs:(cm_struct_d)list`,
                 `globals:(cm_global_d)list`,
                 `locals:(cm_slot_d)list`,
                 `zs:int`, `zg:int`, `zl:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(structs == cm_program_structs p) **
       fact(globals == cm_program_globals p) **
       fact(locals == cm_function_locals f) **
       fact(cm_expr_wf p f e <=> true) **
       fact(cm_expr_counts_representable p fid e <=> true) **
       fact(cm_rep_structs_safe structs <=> true) **
       data_at (field_addr program Tcm_program Fstructs) Tptr zs **
       cm_struct_list_rep zs structs **
       data_at (field_addr program Tcm_program Fglobals) Tptr zg **
       cm_global_list_rep zg globals **
       data_at (field_addr fn Tcm_function Flocals) Tptr zl **
       cm_slot_list_rep zl locals **
       cm_expr_rep expr e`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(structs == cm_program_structs p) **
       fact(globals == cm_program_globals p) **
       fact(locals == cm_function_locals f) **
       fact(cm_expr_wf p f e <=> true) **
       fact(cm_expr_counts_representable p fid e <=> true) **
       fact(cm_rep_structs_safe structs <=> true) **
       data_at (field_addr program Tcm_program Fstructs) Tptr zs **
       cm_struct_list_rep zs structs **
       data_at (field_addr program Tcm_program Fglobals) Tptr zg **
       cm_global_list_rep zg globals **
       data_at (field_addr fn Tcm_function Flocals) Tptr zl **
       cm_slot_list_rep zl locals **
       cm_expr_rep expr e **
       fact((__return:int) ==
         cm_lcount_of (cm_expr_code_counts p fid e)) **
       fact(cm_i32_code_count (__return:int) <=> true)`)]]
{
  int lvalue;
  int rvalue;
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`f`, `(f:cm_function_d)`)]]
  [[cst::where(`e`, `(e:cm_expr)`)]]
  [[cst::where(`structs`, `structs:(cm_struct_d)list`)]]
  [[cst::where(`globals`, `globals:(cm_global_d)list`)]]
  [[cst::where(`locals`, `locals:(cm_slot_d)list`)]]
  [[cst::where(`zs`, `(zs:int)`)]]
  [[cst::where(`zg`, `(zg:int)`)]]
  [[cst::where(`zl`, `(zl:int)`)]]
  cm_expr_counts(program, fid, fn, expr, &lvalue, &rvalue);
  return lvalue;
}

int cm_expr_rvalue_count(struct cm_program *program, int fid,
                                struct cm_function *fn,
                                struct cm_expr *expr)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `e:cm_expr`,
                 `structs:(cm_struct_d)list`,
                 `globals:(cm_global_d)list`,
                 `locals:(cm_slot_d)list`,
                 `zs:int`, `zg:int`, `zl:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(structs == cm_program_structs p) **
       fact(globals == cm_program_globals p) **
       fact(locals == cm_function_locals f) **
       fact(cm_expr_wf p f e <=> true) **
       fact(cm_expr_counts_representable p fid e <=> true) **
       fact(cm_rep_structs_safe structs <=> true) **
       data_at (field_addr program Tcm_program Fstructs) Tptr zs **
       cm_struct_list_rep zs structs **
       data_at (field_addr program Tcm_program Fglobals) Tptr zg **
       cm_global_list_rep zg globals **
       data_at (field_addr fn Tcm_function Flocals) Tptr zl **
       cm_slot_list_rep zl locals **
       cm_expr_rep expr e`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(structs == cm_program_structs p) **
       fact(globals == cm_program_globals p) **
       fact(locals == cm_function_locals f) **
       fact(cm_expr_wf p f e <=> true) **
       fact(cm_expr_counts_representable p fid e <=> true) **
       fact(cm_rep_structs_safe structs <=> true) **
       data_at (field_addr program Tcm_program Fstructs) Tptr zs **
       cm_struct_list_rep zs structs **
       data_at (field_addr program Tcm_program Fglobals) Tptr zg **
       cm_global_list_rep zg globals **
       data_at (field_addr fn Tcm_function Flocals) Tptr zl **
       cm_slot_list_rep zl locals **
       cm_expr_rep expr e **
       fact((__return:int) ==
         cm_rcount_of (cm_expr_code_counts p fid e)) **
       fact(cm_i32_code_count (__return:int) <=> true)`)]]
{
  int lvalue;
  int rvalue;
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`f`, `(f:cm_function_d)`)]]
  [[cst::where(`e`, `(e:cm_expr)`)]]
  [[cst::where(`structs`, `structs:(cm_struct_d)list`)]]
  [[cst::where(`globals`, `globals:(cm_global_d)list`)]]
  [[cst::where(`locals`, `locals:(cm_slot_d)list`)]]
  [[cst::where(`zs`, `(zs:int)`)]]
  [[cst::where(`zg`, `(zg:int)`)]]
  [[cst::where(`zl`, `(zl:int)`)]]
  cm_expr_counts(program, fid, fn, expr, &lvalue, &rvalue);
  return rvalue;
}

static void cmc_args_code_count(struct cm_program *program, int fid,
                                struct cm_function *fn,
                                struct cm_arg *arg, int *count)
    [[cst::param(`p:cm_program`, `f:cm_function_d`,
                 `args:(cm_expr)list`, `slots:(cm_slot_d)list`,
                 `structs:(cm_struct_d)list`,
                 `globals:(cm_global_d)list`,
                 `locals:(cm_slot_d)list`,
                 `zs:int`, `zg:int`, `zl:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(structs == cm_program_structs p) **
       fact(globals == cm_program_globals p) **
       fact(locals == cm_function_locals f) **
       fact(cm_args_wf p f args slots <=> true) **
       fact(cm_args_counts_representable p fid args <=> true) **
       fact(cm_rep_structs_safe structs <=> true) **
       data_at (field_addr program Tcm_program Fstructs) Tptr zs **
       cm_struct_list_rep zs structs **
       data_at (field_addr program Tcm_program Fglobals) Tptr zg **
       cm_global_list_rep zg globals **
       data_at (field_addr fn Tcm_function Flocals) Tptr zl **
       cm_slot_list_rep zl locals **
       cm_arg_list_rep arg args **
       undef_data_at count Tint`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(structs == cm_program_structs p) **
       fact(globals == cm_program_globals p) **
       fact(locals == cm_function_locals f) **
       fact(cm_args_wf p f args slots <=> true) **
       fact(cm_args_counts_representable p fid args <=> true) **
       fact(cm_rep_structs_safe structs <=> true) **
       data_at (field_addr program Tcm_program Fstructs) Tptr zs **
       cm_struct_list_rep zs structs **
       data_at (field_addr program Tcm_program Fglobals) Tptr zg **
       cm_global_list_rep zg globals **
       data_at (field_addr fn Tcm_function Flocals) Tptr zl **
       cm_slot_list_rep zl locals **
       cm_arg_list_rep arg args **
       data_at count Tint
         (cm_args_code_count_of (cm_args_code_counts p fid args)) **
       fact(cm_i32_code_count
         (cm_args_code_count_of
           (cm_args_code_counts p fid args)) <=> true)`)]]
{
  if (arg == 0) {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`arg__pre:addr`, `args:(cm_expr)list`),
              get_cm_arg_null()),
            assume_rule(`arg__pre == 0i`))));
      thm args_equal = assume_rule(
          `args == ([]:(cm_expr)list)`);
      thm representable = conv_rule(rewrite_conv(THM_LIST(
          args_equal, get_cm_args_counts_representable_def(),
          get_cm_args_code_counts_def(),
          get_cm_args_code_count_of_def())),
          from_state_bool(
            `cm_args_counts_representable
              (p:cm_program) (fid__pre:int)
              (args:(cm_expr)list)`));
      cm_add_count_facts(representable);
      thm well_formed = conv_rule(rewrite_conv(THM_LIST(
          args_equal, get_cm_args_wf_def())),
          from_state_bool(
            `cm_args_wf (p:cm_program) (f:cm_function_d)
              (args:(cm_expr)list) (slots:(cm_slot_d)list)`));
      cm_add_count_facts(well_formed);
      add_fact_st(sym_rule(by_rewrite(
          `cm_args_code_count_of
             (cm_args_code_counts (p:cm_program) (fid__pre:int)
               (args:(cm_expr)list)) == 1i`,
          THM_LIST(args_equal, get_cm_args_code_counts_def(),
            get_cm_args_code_count_of_def()))));
      thm nil_view = by_rewrite(
          `cm_arg_list_rep (arg__pre:int)
              ([]:(cm_expr)list) -|-
           fact(arg__pre == 0i)`,
          THM_LIST(get_cm_arg_list_rep_def(),
            get_cm_expr_payload_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(nil_view))));
    }
    *count = 1;
    return;
  } else {
  [[cst::proof]] {
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        mp_rule(specl_rule(
            TERM_LIST(`arg__pre:addr`, `args:(cm_expr)list`),
            get_cm_arg_unfold()),
          assume_rule(`~(arg__pre == 0i)`))));
    thm args_equal = assume_rule(
        `args == (arg_:cm_expr) :: (rest_:(cm_expr)list)`);
    thm representable = conv_rule(rewrite_conv(THM_LIST(
        args_equal, get_cm_args_counts_representable_def(),
        get_cm_args_code_counts_def(),
        get_cm_args_code_count_of_def())),
        from_state_bool(
          `cm_args_counts_representable
            (p:cm_program) (fid__pre:int)
            (args:(cm_expr)list)`));
    cm_add_count_facts(representable);
    thm well_formed = conv_rule(rewrite_conv(THM_LIST(
        args_equal, get_cm_args_wf_def(),
        gsym_rule(cm_args_tail_slots_def))),
        from_state_bool(
          `cm_args_wf (p:cm_program) (f:cm_function_d)
            (args:(cm_expr)list) (slots:(cm_slot_d)list)`));
    cm_add_count_facts(well_formed);
  }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`f`, `(f:cm_function_d)`)]]
  [[cst::where(`structs`, `structs:(cm_struct_d)list`)]]
  [[cst::where(`globals`, `globals:(cm_global_d)list`)]]
  [[cst::where(`locals`, `locals:(cm_slot_d)list`)]]
  [[cst::where(`zs`, `(zs:int)`)]]
  [[cst::where(`zg`, `(zg:int)`)]]
  [[cst::where(`zl`, `(zl:int)`)]]
  int head_lvalue;
  int head_count;
  cm_expr_counts(program, fid, fn, arg->expr,
                 &head_lvalue, &head_count);
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`f`, `(f:cm_function_d)`)]]
  [[cst::where(`slots`,
                `cm_args_tail_slots (slots:(cm_slot_d)list)`)]]
  [[cst::where(`structs`, `structs:(cm_struct_d)list`)]]
  [[cst::where(`globals`, `globals:(cm_global_d)list`)]]
  [[cst::where(`locals`, `locals:(cm_slot_d)list`)]]
  [[cst::where(`zs`, `(zs:int)`)]]
  [[cst::where(`zg`, `(zg:int)`)]]
  [[cst::where(`zl`, `(zl:int)`)]]
  int tail_count;
  cmc_args_code_count(program, fid, fn, arg->next, &tail_count);
  [[cst::proof]] {
    cm_add_count_facts(from_state_bool(
        `cm_i32_code_count
          (cm_rcount_of
            (cm_expr_code_counts (p:cm_program)
              (fid__pre:int) (arg_:cm_expr)))`));
    cm_add_count_facts(from_state_bool(
        `cm_i32_code_count
          (cm_args_code_count_of
            (cm_args_code_counts (p:cm_program)
              (fid__pre:int) (rest_:(cm_expr)list)))`));
    add_fact_st(int_arith_rule(
        `0i <=
           cm_rcount_of
             (cm_expr_code_counts (p:cm_program)
               (fid__pre:int) (arg_:cm_expr)) ==>
         0i <=
           cm_args_code_count_of
             (cm_args_code_counts p fid__pre
               (rest_:(cm_expr)list)) ==>
         cm_rcount_of
             (cm_expr_code_counts p fid__pre arg_) +
           10i +
           cm_args_code_count_of
             (cm_args_code_counts p fid__pre rest_) <=
           2147483647i ==>
         -- 2147483648i <=
           cm_rcount_of
             (cm_expr_code_counts p fid__pre arg_) + 10i &&
         cm_rcount_of
             (cm_expr_code_counts p fid__pre arg_) + 10i <=
           2147483647i`));
    thm args_equal = assume_rule(
        `args == (arg_:cm_expr) :: (rest_:(cm_expr)list)`);
    thm cons_model = by_rewrite(
        `cm_args_code_count_of
           (cm_args_code_counts (p:cm_program) (fid__pre:int)
             ((arg_:cm_expr) :: (rest_:(cm_expr)list))) ==
         cm_rcount_of (cm_expr_code_counts p fid__pre arg_) +
           10i +
           cm_args_code_count_of
             (cm_args_code_counts p fid__pre rest_)`,
        THM_LIST(get_cm_args_code_counts_def(),
          get_cm_args_code_count_of_def()));
    thm original_model = trans_rule(beta_norm(ap_term_rule(
        `\xs:(cm_expr)list.
           cm_args_code_count_of
             (cm_args_code_counts (p:cm_program)
               (fid__pre:int) xs)`, args_equal)), cons_model);
    add_fact_st(sym_rule(original_model));
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
  *count = head_count + 10 + tail_count;
  [[cst::proof]] {
    thm args_equal = assume_rule(
        `args == (arg_:cm_expr) :: (rest_:(cm_expr)list)`);
    thm cons_model = by_rewrite(
        `cm_args_code_count_of
           (cm_args_code_counts (p:cm_program) (fid__pre:int)
             ((arg_:cm_expr) :: (rest_:(cm_expr)list))) ==
         cm_rcount_of (cm_expr_code_counts p fid__pre arg_) +
           10i +
           cm_args_code_count_of
             (cm_args_code_counts p fid__pre rest_)`,
        THM_LIST(get_cm_args_code_counts_def(),
          get_cm_args_code_count_of_def()));
    thm original_model = trans_rule(beta_norm(ap_term_rule(
        `\xs:(cm_expr)list.
           cm_args_code_count_of
             (cm_args_code_counts (p:cm_program)
               (fid__pre:int) xs)`, args_equal)), cons_model);
    thm current_model = mp_rule(int_arith_rule(
        `cm_args_code_count_of
             (cm_args_code_counts (p:cm_program)
               (fid__pre:int) (args:(cm_expr)list)) ==
           cm_rcount_of
             (cm_expr_code_counts p fid__pre (arg_:cm_expr)) +
             10i +
             cm_args_code_count_of
               (cm_args_code_counts p fid__pre
                 (rest_:(cm_expr)list)) ==>
         (cm_rcount_of
              (cm_expr_code_counts p fid__pre arg_) + 10i) +
             cm_args_code_count_of
               (cm_args_code_counts p fid__pre rest_) ==
           cm_args_code_count_of
             (cm_args_code_counts p fid__pre args)`),
        original_model);
    substitute_st(current_model);
    substitute_st(sym_rule(args_equal));
  }
  }
}

PROOF static void cm_finish_expr_count_cells_with_rules(
    const thm shape, const term concrete_lvalue,
    const term concrete_rvalue, const thm_list extra_rules) {
  term model_lvalue =
      `cm_lcount_of
         (cm_expr_code_counts (p:cm_program)
           (fid__pre:int) (e:cm_expr))`;
  term model_rvalue =
      `cm_rcount_of
         (cm_expr_code_counts (p:cm_program)
           (fid__pre:int) (e:cm_expr))`;
  thm_list rules = THM_LIST(
      shape, get_cm_expr_code_counts_def(),
      get_cm_lcount_of_def(), get_cm_rcount_of_def());
  for (size_t i = 0; i < vector_size(extra_rules); ++i) {
    vector_add(&rules, extra_rules[i]);
  }
  thm lvalue_model =
      by_rewrite(mk_eq(model_lvalue, concrete_lvalue), rules);
  thm rvalue_model =
      by_rewrite(mk_eq(model_rvalue, concrete_rvalue), rules);
  add_fact_st(sym_rule(lvalue_model));
  add_fact_st(sym_rule(rvalue_model));
  cst_set_symbolic_state(retarget_cell_st(
      cst_get_symbolic_state(), `out_lvalue__addr:addr`,
      concrete_lvalue, model_lvalue));
  cst_set_symbolic_state(retarget_cell_st(
      cst_get_symbolic_state(), `out_rvalue__addr:addr`,
      concrete_rvalue, model_rvalue));
}

PROOF static void cm_finish_expr_count_cells(
    const thm shape, const term concrete_lvalue,
    const term concrete_rvalue) {
  cm_finish_expr_count_cells_with_rules(
      shape, concrete_lvalue, concrete_rvalue, THM_LIST());
}

PROOF static void cm_prepare_binary_count_sum(
    const term concrete_count, const term tail_count,
    const thm tail_nonnegative, const thm_list extra_rules) {
  term left_count =
      `cm_rcount_of
         (cm_expr_code_counts (p:cm_program)
           (fid__pre:int) (left_:cm_expr))`;
  term right_count =
      `cm_rcount_of
         (cm_expr_code_counts (p:cm_program)
           (fid__pre:int) (right_:cm_expr))`;
  term model_count =
      `cm_rcount_of
         (cm_expr_code_counts (p:cm_program) (fid__pre:int)
           (CMBinaryE (op_:int) (left_:cm_expr)
             (right_:cm_expr) (ty_:cm_type)))`;
  thm_list rules = THM_LIST(
      get_cm_expr_code_counts_def(), get_cm_rcount_of_def(),
      get_cm_binary_tail_count_def(),
      eqf_intro_rule(int_arith_rule(`~(9i == 8i)`)),
      get_theorem_by_name("COND_ID"),
      int_ring_rule(
        `!(l:int) (r:int). l + r + 10i + 4i == l + r + 14i`),
      int_ring_rule(
        `!(l:int) (r:int). l + r + 10i + 2i == l + r + 12i`),
      int_ring_rule(
        `!(l:int) (r:int).
           l + r + 10i + 1i + 3i == l + r + 14i`),
      int_ring_rule(
        `!(l:int) (r:int).
           l + r + 10i + 1i + 1i == l + r + 12i`));
  for (size_t i = 0; i < vector_size(extra_rules); ++i) {
    vector_add(&rules, extra_rules[i]);
  }
  thm model = by_rewrite(mk_eq(model_count, concrete_count), rules);
  thm upper = assume_rule(
      `cm_rcount_of
         (cm_expr_code_counts (p:cm_program) (fid__pre:int)
           (CMBinaryE (op_:int) (left_:cm_expr)
             (right_:cm_expr) (ty_:cm_type))) <= 2147483647i`);
  thm upper_equivalence = beta_norm(ap_term_rule(
      `\n:int. n <= 2147483647i`, model));
  thm concrete_upper = eq_mp_rule(upper_equivalence, upper);
  cm_add_count_facts(from_state_bool(
      `cm_i32_code_count
         (cm_rcount_of
           (cm_expr_code_counts (p:cm_program)
             (fid__pre:int) (left_:cm_expr)))`));
  cm_add_count_facts(from_state_bool(
      `cm_i32_code_count
         (cm_rcount_of
           (cm_expr_code_counts (p:cm_program)
             (fid__pre:int) (right_:cm_expr)))`));
  thm bounds = specl_rule(
      TERM_LIST(left_count, right_count, tail_count),
      int_arith_rule(
        `!(left_count:int) (right_count:int) (tail_count:int).
           0i <= left_count ==> 0i <= right_count ==>
           0i <= tail_count ==>
           left_count + (right_count + tail_count) <=
             2147483647i ==>
           (--2147483648i <= right_count + tail_count &&
            right_count + tail_count <= 2147483647i &&
            --2147483648i <=
              left_count + (right_count + tail_count) &&
            left_count + (right_count + tail_count) <=
              2147483647i)`));
  bounds = mp_rule(bounds, assume_rule(
      `0i <= cm_rcount_of
        (cm_expr_code_counts (p:cm_program)
          (fid__pre:int) (left_:cm_expr))`));
  bounds = mp_rule(bounds, assume_rule(
      `0i <= cm_rcount_of
        (cm_expr_code_counts (p:cm_program)
          (fid__pre:int) (right_:cm_expr))`));
  bounds = mp_rule(bounds, tail_nonnegative);
  bounds = mp_rule(bounds, concrete_upper);
  add_fact_st(conjunct1_rule(bounds));
  thm rest = conjunct2_rule(bounds);
  add_fact_st(conjunct1_rule(rest));
  rest = conjunct2_rule(rest);
  add_fact_st(conjunct1_rule(rest));
  add_fact_st(conjunct2_rule(rest));
}

PROOF static void cm_close_binary_count_payload(const thm shape) {
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
      THM_LIST(shape, get_cm_expr_payload_def()));
  apply_hconv_st(eq2ent(sym_rule(payload_view)));
}

PROOF static void cm_finish_binary_count_branch(
    const thm shape, const term concrete_count,
    const thm_list extra_rules) {
  thm_list rules = THM_LIST(
      get_cm_binary_tail_count_def(),
      eqf_intro_rule(int_arith_rule(
        `~(8i == 0i || 8i == 1i)`)),
      eqf_intro_rule(int_arith_rule(
        `~(9i == 0i || 9i == 1i)`)),
      eqf_intro_rule(int_arith_rule(`~(9i == 8i)`)),
      get_theorem_by_name("COND_ID"),
      int_ring_rule(
        `!(l:int) (r:int). l + r + 10i + 4i == l + r + 14i`),
      int_ring_rule(
        `!(l:int) (r:int). l + r + 10i + 2i == l + r + 12i`),
      int_ring_rule(
        `!(l:int) (r:int).
           l + r + 10i + 1i + 3i == l + r + 14i`),
      int_ring_rule(
        `!(l:int) (r:int).
           l + r + 10i + 1i + 1i == l + r + 12i`));
  for (size_t i = 0; i < vector_size(extra_rules); ++i) {
    vector_add(&rules, extra_rules[i]);
  }
  cm_finish_expr_count_cells_with_rules(
      shape, `0i`, concrete_count, rules);
  cm_close_binary_count_payload(shape);
}


PROOF static void cm_prepare_single_child_add(
    const term model_count, const term concrete_count,
    const thm model_upper, const term child_count,
    const thm child_i32, const term increment,
    const thm increment_nonnegative, const thm_list rules) {
  thm model = by_rewrite(
      mk_eq(model_count, concrete_count), rules);
  thm concrete_upper = eq_mp_rule(beta_norm(ap_term_rule(
      `\n:int. n <= 2147483647i`, model)), model_upper);
  thm child_bounds = conv_rule(rewrite_conv(
      THM_LIST(get_cm_i32_code_count_def())), child_i32);
  thm addition_bounds = specl_rule(
      TERM_LIST(child_count, increment),
      int_arith_rule(
        `!(child_count:int) (increment:int).
           0i <= child_count ==> 0i <= increment ==>
           child_count + increment <= 2147483647i ==>
           (--2147483648i <= child_count + increment &&
            child_count + increment <= 2147483647i)`));
  addition_bounds = mp_rule(
      addition_bounds, conjunct1_rule(child_bounds));
  addition_bounds = mp_rule(
      addition_bounds, increment_nonnegative);
  addition_bounds = mp_rule(addition_bounds, concrete_upper);
  add_fact_st(conjunct1_rule(addition_bounds));
  add_fact_st(conjunct2_rule(addition_bounds));
  cm_add_count_facts(child_i32);
}

static void cm_binding_address_count_value(int scope, int *count)
    [[cst::require(
      `undef_data_at count Tint`)]]
    [[cst::ensure(
      `data_at count Tint
         (cm_binding_address_count (scope:int)) **
       fact(cm_i32_code_count
         (cm_binding_address_count (scope:int)) <=> true)`)]]
{
  if (scope == CMC_BIND_GLOBAL) {
    *count = 1;
    [[cst::proof]] {
      thm model = by_rewrite(
          `cm_binding_address_count (scope__pre:int) == 1i`,
          THM_LIST(assume_rule(`scope__pre == 0i`),
            get_cm_binding_address_count_def()));
      add_fact_st(sym_rule(model));
      add_fact_st(eqt_intro_rule(by_rewrite(
          `cm_i32_code_count
             (cm_binding_address_count (scope__pre:int))`,
          THM_LIST(model, get_cm_i32_code_count_def(),
            int_arith_rule(
              `0i <= 1i && 1i <= 2147483647i`)))));
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `count__pre:addr`, `1i`,
          `cm_binding_address_count (scope__pre:int)`));
    }
  } else {
    *count = 4;
    [[cst::proof]] {
      thm model = by_rewrite(
          `cm_binding_address_count (scope__pre:int) == 4i`,
          THM_LIST(assume_rule(`~(scope__pre == 0i)`),
            get_cm_binding_address_count_def()));
      add_fact_st(sym_rule(model));
      add_fact_st(eqt_intro_rule(by_rewrite(
          `cm_i32_code_count
             (cm_binding_address_count (scope__pre:int))`,
          THM_LIST(model, get_cm_i32_code_count_def(),
            int_arith_rule(
              `0i <= 4i && 4i <= 2147483647i`)))));
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `count__pre:addr`, `4i`,
          `cm_binding_address_count (scope__pre:int)`));
    }
  }
}

static void cm_expr_counts(struct cm_program *program, int fid,
                           struct cm_function *fn,
                           struct cm_expr *expr, int *lvalue, int *rvalue)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `e:cm_expr`,
                 `structs:(cm_struct_d)list`,
                 `globals:(cm_global_d)list`,
                 `locals:(cm_slot_d)list`,
                 `zs:int`, `zg:int`, `zl:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(structs == cm_program_structs p) **
       fact(globals == cm_program_globals p) **
       fact(locals == cm_function_locals f) **
       fact(cm_expr_wf p f e <=> true) **
       fact(cm_expr_counts_representable p fid e <=> true) **
       fact(cm_rep_structs_safe structs <=> true) **
       data_at (field_addr program Tcm_program Fstructs) Tptr zs **
       cm_struct_list_rep zs structs **
       data_at (field_addr program Tcm_program Fglobals) Tptr zg **
       cm_global_list_rep zg globals **
       data_at (field_addr fn Tcm_function Flocals) Tptr zl **
       cm_slot_list_rep zl locals **
       cm_expr_rep expr e **
       undef_data_at lvalue Tint **
       undef_data_at rvalue Tint`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(structs == cm_program_structs p) **
       fact(globals == cm_program_globals p) **
       fact(locals == cm_function_locals f) **
       fact(cm_expr_wf p f e <=> true) **
       fact(cm_expr_counts_representable p fid e <=> true) **
       fact(cm_type_code_wf (cm_expr_type e) <=> true) **
       fact(cm_i32_code_count
         (cm_type_encode (cm_expr_type e)) <=> true) **
       fact(cm_rep_structs_safe structs <=> true) **
       data_at (field_addr program Tcm_program Fstructs) Tptr zs **
       cm_struct_list_rep zs structs **
       data_at (field_addr program Tcm_program Fglobals) Tptr zg **
       cm_global_list_rep zg globals **
       data_at (field_addr fn Tcm_function Flocals) Tptr zl **
       cm_slot_list_rep zl locals **
       cm_expr_rep expr e **
       data_at lvalue Tint
         (cm_lcount_of (cm_expr_code_counts p fid e)) **
       data_at rvalue Tint
         (cm_rcount_of (cm_expr_code_counts p fid e)) **
       fact(cm_i32_code_count
         (cm_lcount_of (cm_expr_code_counts p fid e)) <=> true) **
       fact(cm_i32_code_count
         (cm_rcount_of (cm_expr_code_counts p fid e)) <=> true)`)]]
{
  [[cst::proof]] {
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        specl_rule(TERM_LIST(`expr__pre:int`, `e:cm_expr`),
          get_cm_expr_open())));
  }
  int out_lvalue = 0;
  int out_rvalue = 0;
  if (expr->kind == CMC_EXPR_CONST) {
    out_rvalue = 1;
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`e:cm_expr`,
          get_cm_expr_const_shape_ent()),
          assume_rule(`cm_rep_expr_kind (e:cm_expr) == 0i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`n_:int`, `ty_:cm_type`))));
      thm shape = assume_rule(
          `e == CMConstE (n_:int) (ty_:cm_type)`);
      cm_open_expr_count_facts(shape);
      cm_finish_expr_count_cells(shape, `0i`, `1i`);
    }
  } else if (expr->kind == CMC_EXPR_STRING) {
    out_rvalue = 1;
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`e:cm_expr`,
          get_cm_expr_string_shape_ent()),
          assume_rule(`cm_rep_expr_kind (e:cm_expr) == 1i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`sid_:int`, `ty_:cm_type`))));
      thm shape = assume_rule(
          `e == CMStringE (sid_:int) (ty_:cm_type)`);
      cm_open_expr_count_facts(shape);
      cm_finish_expr_count_cells(shape, `0i`, `1i`);
    }
  } else if (expr->kind == CMC_EXPR_SIZEOF) {
    out_rvalue = 1;
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`e:cm_expr`,
          get_cm_expr_sizeof_shape_ent()),
          assume_rule(`cm_rep_expr_kind (e:cm_expr) == 9i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`asked_:cm_type`, `ty_:cm_type`))));
      thm shape = assume_rule(
          `e == CMSizeofE (asked_:cm_type) (ty_:cm_type)`);
      cm_open_expr_count_facts(shape);
      cm_finish_expr_count_cells(shape, `0i`, `1i`);
    }
  } else if (expr->kind == CMC_EXPR_GETC) {
    out_rvalue = 1;
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`e:cm_expr`,
          get_cm_expr_getc_shape_ent()),
          assume_rule(`cm_rep_expr_kind (e:cm_expr) == 10i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`ty_:cm_type`))));
      thm shape = assume_rule(`e == CMGetcE (ty_:cm_type)`);
      cm_open_expr_count_facts(shape);
      cm_finish_expr_count_cells(shape, `0i`, `1i`);
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
      cm_open_expr_count_facts(shape);
      thm slot_nonnegative = mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `f:cm_function_d`, `scope_:int`,
          `slot_:int`), cm_binding_valid_slot_nonnegative),
          from_state_bool(
            `cm_binding_valid (p:cm_program) (f:cm_function_d)
              (scope_:int) (slot_:int)`));
      add_fact_st(slot_nonnegative);
    }
    int address_count;
    cm_binding_address_count_value(expr->op, &address_count);
    out_lvalue = address_count;
    out_rvalue = address_count;
    int array;
    [[cst::proof]] {
      thm shape = assume_rule(
          `e == CMVarE (scope_:int) (slot_:int) (ty_:cm_type)`);
      thm op_model = by_rewrite(
          `cm_rep_expr_op (e:cm_expr) == (scope_:int)`,
          THM_LIST(shape, get_cm_rep_expr_op_def()));
      thm value_model = by_rewrite(
          `cm_rep_expr_value (e:cm_expr) == (slot_:int)`,
          THM_LIST(shape, get_cm_rep_expr_value_def()));
      thm slot_cast = mp_rule(mp_rule(
          spec_rule(`slot_:int`, cm_nonnegative_i32_cast),
          assume_rule(`0i <= (slot_:int)`)),
          assume_rule(`(slot_:int) <= 2147483647i`));
      thm cast_model = trans_rule(beta_norm(ap_term_rule(
          `\n:int. signed_last_nbits n 32i`, value_model)),
          slot_cast);
      thm passed_nonnegative = conv_rule(
          rewrite_conv(THM_LIST(sym_rule(cast_model))),
          assume_rule(`0i <= (slot_:int)`));
      add_fact_st(passed_nonnegative);
      thm passed_valid = conv_rule(
          rewrite_conv(THM_LIST(sym_rule(cast_model))),
          from_state_bool(
            `cm_binding_valid (p:cm_program) (f:cm_function_d)
              (scope_:int) (slot_:int)`));
      add_fact_st(eqt_intro_rule(passed_valid));
      thm fn_model = assume_rule(
          `f == inth (fid__pre:int) (cm_program_functions (p:cm_program))`);
      thm canonical_nonnegative = conv_rule(
          rewrite_conv(THM_LIST(shape)), passed_nonnegative);
      add_fact_st(canonical_nonnegative);
      thm canonical_valid = conv_rule(
          rewrite_conv(THM_LIST(shape, fn_model)), passed_valid);
      add_fact_st(eqt_intro_rule(canonical_valid));
      substitute_st(op_model);
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`globals`, `globals:(cm_global_d)list`)]]
    [[cst::where(`locals`, `locals:(cm_slot_d)list`)]]
    [[cst::where(`zg`, `(zg:int)`)]]
    [[cst::where(`zl`, `(zl:int)`)]]
    cmc_binding_array_value(program, fid, fn, expr->op,
                            (int)expr->value, &array);
    [[cst::proof]] {
      thm shape = assume_rule(
          `e == CMVarE (scope_:int) (slot_:int) (ty_:cm_type)`);
      thm value_model = by_rewrite(
          `cm_rep_expr_value (e:cm_expr) == (slot_:int)`,
          THM_LIST(shape, get_cm_rep_expr_value_def()));
      thm slot_cast = mp_rule(mp_rule(
          spec_rule(`slot_:int`, cm_nonnegative_i32_cast),
          assume_rule(`0i <= (slot_:int)`)),
          assume_rule(`(slot_:int) <= 2147483647i`));
      thm cast_model = trans_rule(beta_norm(ap_term_rule(
          `\n:int. signed_last_nbits n 32i`, value_model)),
          slot_cast);
      substitute_st(cast_model);
    }
    if (!array) {
      [[cst::proof]] {
        thm code_cases = specl_rule(TERM_LIST(
            `p:cm_program`, `fid__pre:int`,
            `scope_:int`, `slot_:int`),
            cm_binding_array_code_cases);
        thm not_array = eq_mp_rule(conjunct1_rule(code_cases),
            assume_rule(
              `cm_binding_array_code (p:cm_program) (fid__pre:int)
                (scope_:int) (slot_:int) == 0i`));
        thm count_i32 = from_state_bool(
            `cm_i32_code_count
              (cm_rcount_of
                (cm_expr_code_counts (p:cm_program) (fid__pre:int)
                  (CMVarE (scope_:int) (slot_:int) (ty_:cm_type))))`);
        thm concrete_i32 = conv_rule(rewrite_conv(THM_LIST(
            get_cm_expr_code_counts_def(), get_cm_rcount_of_def(),
            not_array)), count_i32);
        cm_add_count_facts(concrete_i32);
      }
      out_rvalue = out_rvalue + 1;
      [[cst::proof]] {
        thm shape = assume_rule(
            `e == CMVarE (scope_:int) (slot_:int) (ty_:cm_type)`);
        thm code_cases = specl_rule(TERM_LIST(
            `p:cm_program`, `fid__pre:int`,
            `scope_:int`, `slot_:int`),
            cm_binding_array_code_cases);
        thm not_array = eq_mp_rule(conjunct1_rule(code_cases),
            assume_rule(
              `cm_binding_array_code (p:cm_program) (fid__pre:int)
                (scope_:int) (slot_:int) == 0i`));
        cm_finish_expr_count_cells_with_rules(shape,
            `cm_binding_address_count (scope_:int)`,
            `cm_binding_address_count (scope_:int) + 1i`,
            THM_LIST(not_array));
      }
    } else {
      [[cst::proof]] {
        thm shape = assume_rule(
            `e == CMVarE (scope_:int) (slot_:int) (ty_:cm_type)`);
        thm code_cases = specl_rule(TERM_LIST(
            `p:cm_program`, `fid__pre:int`,
            `scope_:int`, `slot_:int`),
            cm_binding_array_code_cases);
        thm is_array = eq_mp_rule(conjunct2_rule(code_cases),
            assume_rule(
              `~(cm_binding_array_code (p:cm_program)
                   (fid__pre:int) (scope_:int) (slot_:int) == 0i)`));
        cm_finish_expr_count_cells_with_rules(shape,
            `cm_binding_address_count (scope_:int)`,
            `cm_binding_address_count (scope_:int)`,
            THM_LIST(is_array,
              int_arith_rule(`!x:int. x + 0i == x`)));
      }
    }
    [[cst::proof]] {
      thm shape = assume_rule(
          `e == CMVarE (scope_:int) (slot_:int) (ty_:cm_type)`);
      thm op_model = by_rewrite(
          `cm_rep_expr_op (e:cm_expr) == (scope_:int)`,
          THM_LIST(shape, get_cm_rep_expr_op_def()));
      substitute_st(sym_rule(op_model));
    }
  } else if (expr->kind == CMC_EXPR_ASSIGN) {
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
      cm_open_expr_count_facts(shape);
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
    int dst_lvalue;
    int dst_rvalue;
    int src_lvalue;
    int src_rvalue;
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`structs`, `structs:(cm_struct_d)list`)]]
    [[cst::where(`globals`, `globals:(cm_global_d)list`)]]
    [[cst::where(`locals`, `locals:(cm_slot_d)list`)]]
    [[cst::where(`zs`, `(zs:int)`)]]
    [[cst::where(`zg`, `(zg:int)`)]]
    [[cst::where(`zl`, `(zl:int)`)]]
    cm_expr_counts(program, fid, fn, expr->a,
                   &dst_lvalue, &dst_rvalue);
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`structs`, `structs:(cm_struct_d)list`)]]
    [[cst::where(`globals`, `globals:(cm_global_d)list`)]]
    [[cst::where(`locals`, `locals:(cm_slot_d)list`)]]
    [[cst::where(`zs`, `(zs:int)`)]]
    [[cst::where(`zg`, `(zg:int)`)]]
    [[cst::where(`zl`, `(zl:int)`)]]
    cm_expr_counts(program, fid, fn, expr->b,
                   &src_lvalue, &src_rvalue);
    int normalize_count = cm_normalize_count(expr->ty);
    [[cst::proof]] {
      thm shape = assume_rule(
          `e == CMAssignE (dst_:cm_expr)
             (src_:cm_expr) (ty_:cm_type)`);
      thm type_wf = from_state_bool(
          `cm_type_code_wf (ty_:cm_type)`);
      thm normalize_bridge = mp_rule(
          spec_rule(`ty_:cm_type`, cm_char_normalize_bridge), type_wf);
      thm normalize_model = by_rewrite(
          `cm_normalize_code_value
             (cm_type_encode (cm_expr_type (e:cm_expr))) ==
           cm_char_normalize_count (ty_:cm_type)`,
          THM_LIST(shape, get_cm_expr_type_def(), normalize_bridge));
      substitute_st(normalize_model);
      substitute_fact_st(
          `retval ==
           cm_char_normalize_count (ty_:cm_type)`);
      thm normalize_nonnegative = spec_rule(
          `ty_:cm_type`, cm_char_normalize_nonnegative);
      add_fact_st(normalize_nonnegative);
      cm_add_count_facts(from_state_bool(
          `cm_i32_code_count
             (cm_lcount_of
               (cm_expr_code_counts (p:cm_program)
                 (fid__pre:int) (dst_:cm_expr)))`));
      cm_add_count_facts(from_state_bool(
          `cm_i32_code_count
             (cm_rcount_of
               (cm_expr_code_counts (p:cm_program)
                 (fid__pre:int) (src_:cm_expr)))`));
      thm count_upper = conv_rule(rewrite_conv(THM_LIST(
          get_cm_expr_code_counts_def(), get_cm_rcount_of_def())),
          assume_rule(
            `cm_rcount_of
               (cm_expr_code_counts (p:cm_program) (fid__pre:int)
                 (CMAssignE (dst_:cm_expr) (src_:cm_expr)
                   (ty_:cm_type))) <= 2147483647i`));
      add_fact_st(count_upper);
      add_arith_fact_st(cst_get_symbolic_state(),
          "0i <= cm_lcount_of (cm_expr_code_counts p fid__pre dst_) ==>"
          "0i <= cm_rcount_of (cm_expr_code_counts p fid__pre src_) ==>"
          "0i <= cm_char_normalize_count ty_ ==>"
          "cm_lcount_of (cm_expr_code_counts p fid__pre dst_) +"
          " (5i + (cm_rcount_of"
          "   (cm_expr_code_counts p fid__pre src_) +"
          "   (cm_char_normalize_count ty_ + 12i))) <= 2147483647i ==>"
          "(--2147483648i <= cm_char_normalize_count ty_ + 12i &&"
          " cm_char_normalize_count ty_ + 12i <= 2147483647i &&"
          " --2147483648i <="
          "   cm_rcount_of (cm_expr_code_counts p fid__pre src_) +"
          "     (cm_char_normalize_count ty_ + 12i) &&"
          " cm_rcount_of (cm_expr_code_counts p fid__pre src_) +"
          "   (cm_char_normalize_count ty_ + 12i) <= 2147483647i &&"
          " --2147483648i <= 5i +"
          "   (cm_rcount_of (cm_expr_code_counts p fid__pre src_) +"
          "     (cm_char_normalize_count ty_ + 12i)) &&"
          " 5i + (cm_rcount_of"
          "   (cm_expr_code_counts p fid__pre src_) +"
          "   (cm_char_normalize_count ty_ + 12i)) <= 2147483647i &&"
          " --2147483648i <="
          "   cm_lcount_of (cm_expr_code_counts p fid__pre dst_) +"
          "     (5i + (cm_rcount_of"
          "       (cm_expr_code_counts p fid__pre src_) +"
          "       (cm_char_normalize_count ty_ + 12i))) &&"
          " cm_lcount_of (cm_expr_code_counts p fid__pre dst_) +"
          "   (5i + (cm_rcount_of"
          "     (cm_expr_code_counts p fid__pre src_) +"
          "     (cm_char_normalize_count ty_ + 12i))) <= 2147483647i)");
    }
    out_rvalue = dst_lvalue +
                 (5 + (src_rvalue + (normalize_count + 12)));
    [[cst::proof]] {
      thm shape = assume_rule(
          `e == CMAssignE (dst_:cm_expr)
             (src_:cm_expr) (ty_:cm_type)`);
      cm_finish_expr_count_cells(shape, `0i`,
          `cm_lcount_of (cm_expr_code_counts
             (p:cm_program) (fid__pre:int) (dst_:cm_expr)) +
           (5i + (cm_rcount_of (cm_expr_code_counts
             p fid__pre (src_:cm_expr)) +
             (cm_char_normalize_count (ty_:cm_type) + 12i)))`);
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
          THM_LIST(shape, get_cm_expr_payload_def()));
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
      cm_open_expr_count_facts(shape);
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
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`structs`, `structs:(cm_struct_d)list`)]]
    [[cst::where(`globals`, `globals:(cm_global_d)list`)]]
    [[cst::where(`locals`, `locals:(cm_slot_d)list`)]]
    [[cst::where(`zs`, `(zs:int)`)]]
    [[cst::where(`zg`, `(zg:int)`)]]
    [[cst::where(`zl`, `(zl:int)`)]]
    cm_expr_counts(program, fid, fn, expr->a,
                   &left_lvalue, &left_rvalue);
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`structs`, `structs:(cm_struct_d)list`)]]
    [[cst::where(`globals`, `globals:(cm_global_d)list`)]]
    [[cst::where(`locals`, `locals:(cm_slot_d)list`)]]
    [[cst::where(`zs`, `(zs:int)`)]]
    [[cst::where(`zg`, `(zg:int)`)]]
    [[cst::where(`zl`, `(zl:int)`)]]
    cm_expr_counts(program, fid, fn, expr->b,
                   &right_lvalue, &right_rvalue);
    [[cst::proof]] {
      thm shape = assume_rule(
          `e == CMBinaryE (op_:int) (left_:cm_expr)
             (right_:cm_expr) (ty_:cm_type)`);
      thm op_model = by_rewrite(
          `cm_rep_expr_op (e:cm_expr) == (op_:int)`,
          THM_LIST(shape, get_cm_rep_expr_op_def()));
      substitute_st(op_model);
    }
    if (expr->op == CMC_BIN_OR) {
      [[cst::proof]] {
        thm short_case = mp_rule(int_arith_rule(
            `(op_:int) == 0i ==> op_ == 0i || op_ == 1i`),
            assume_rule(`(op_:int) == 0i`));
        term concrete =
            `cm_rcount_of (cm_expr_code_counts
               (p:cm_program) (fid__pre:int) (left_:cm_expr)) +
             (cm_rcount_of (cm_expr_code_counts
               p fid__pre (right_:cm_expr)) + 5i)`;
        cm_prepare_binary_count_sum(
            concrete, `5i`, int_arith_rule(`0i <= 5i`),
            THM_LIST(eqt_intro_rule(short_case)));
      }
      out_rvalue = left_rvalue + (right_rvalue + 5);
      [[cst::proof]] {
        thm shape = assume_rule(
            `e == CMBinaryE (op_:int) (left_:cm_expr)
               (right_:cm_expr) (ty_:cm_type)`);
        thm short_case = mp_rule(int_arith_rule(
            `(op_:int) == 0i ==> op_ == 0i || op_ == 1i`),
            assume_rule(`(op_:int) == 0i`));
        term concrete =
            `cm_rcount_of (cm_expr_code_counts
               (p:cm_program) (fid__pre:int) (left_:cm_expr)) +
             (cm_rcount_of (cm_expr_code_counts
               p fid__pre (right_:cm_expr)) + 5i)`;
        cm_finish_binary_count_branch(
            shape, concrete, THM_LIST(eqt_intro_rule(short_case)));
      }
    } else if (expr->op == CMC_BIN_AND) {
      [[cst::proof]] {
        thm short_case = mp_rule(int_arith_rule(
            `(op_:int) == 1i ==> op_ == 0i || op_ == 1i`),
            assume_rule(`(op_:int) == 1i`));
        term concrete =
            `cm_rcount_of (cm_expr_code_counts
               (p:cm_program) (fid__pre:int) (left_:cm_expr)) +
             (cm_rcount_of (cm_expr_code_counts
               p fid__pre (right_:cm_expr)) + 5i)`;
        cm_prepare_binary_count_sum(
            concrete, `5i`, int_arith_rule(`0i <= 5i`),
            THM_LIST(eqt_intro_rule(short_case)));
      }
      out_rvalue = left_rvalue + (right_rvalue + 5);
      [[cst::proof]] {
        thm shape = assume_rule(
            `e == CMBinaryE (op_:int) (left_:cm_expr)
               (right_:cm_expr) (ty_:cm_type)`);
        thm short_case = mp_rule(int_arith_rule(
            `(op_:int) == 1i ==> op_ == 0i || op_ == 1i`),
            assume_rule(`(op_:int) == 1i`));
        term concrete =
            `cm_rcount_of (cm_expr_code_counts
               (p:cm_program) (fid__pre:int) (left_:cm_expr)) +
             (cm_rcount_of (cm_expr_code_counts
               p fid__pre (right_:cm_expr)) + 5i)`;
        cm_finish_binary_count_branch(
            shape, concrete, THM_LIST(eqt_intro_rule(short_case)));
      }
    } else {
      [[cst::proof]] {
        thm long_case = mp_rule(mp_rule(int_arith_rule(
            `~((op_:int) == 0i) ==> ~(op_ == 1i) ==>
             ~(op_ == 0i || op_ == 1i)`),
            assume_rule(`~((op_:int) == 0i)`)),
            assume_rule(`~((op_:int) == 1i)`));
        add_fact_st(long_case);
      }
      if (expr->op == CMC_BIN_ADD) {
        int right_type;
        cmc_expr_type_code_value(expr->b, &right_type);
        int right_pointer;
        cmc_is_pointer_value(right_type, &right_pointer);
        [[cst::proof]] {
          thm bridge = mp_rule(spec_rule(
              `cm_expr_type (right_:cm_expr)`,
              cm_pointer_code_bridge),
              from_state_bool(
                `cm_type_code_wf
                   (cm_expr_type (right_:cm_expr))`));
          substitute_st(bridge);
        }
        if (right_pointer) {
          [[cst::proof]] {
            thm right_pointer_case = eq_mp_rule(
                conjunct2_rule(spec_rule(
                  `cm_expr_type (right_:cm_expr)`,
                  cm_pointer_code_value_cases)),
                assume_rule(
                  `~(cm_pointer_code_value
                       (cm_expr_type (right_:cm_expr)) == 0i)`));
            term concrete =
                `cm_rcount_of (cm_expr_code_counts
                   (p:cm_program) (fid__pre:int) (left_:cm_expr)) +
                 (cm_rcount_of (cm_expr_code_counts
                   p fid__pre (right_:cm_expr)) + 14i)`;
            cm_prepare_binary_count_sum(
                concrete, `14i`, int_arith_rule(`0i <= 14i`),
                THM_LIST(
                  eqf_intro_rule(assume_rule(
                    `~((op_:int) == 0i || op_ == 1i)`)),
                  assume_rule(`(op_:int) == 8i`),
                  eqt_intro_rule(right_pointer_case)));
          }
          out_rvalue = left_rvalue + (right_rvalue + 14);
          [[cst::proof]] {
            thm shape = assume_rule(
                `e == CMBinaryE (op_:int) (left_:cm_expr)
                   (right_:cm_expr) (ty_:cm_type)`);
            thm right_pointer_case = eq_mp_rule(
                conjunct2_rule(spec_rule(
                  `cm_expr_type (right_:cm_expr)`,
                  cm_pointer_code_value_cases)),
                assume_rule(
                  `~(cm_pointer_code_value
                       (cm_expr_type (right_:cm_expr)) == 0i)`));
            term concrete =
                `cm_rcount_of (cm_expr_code_counts
                   (p:cm_program) (fid__pre:int) (left_:cm_expr)) +
                 (cm_rcount_of (cm_expr_code_counts
                   p fid__pre (right_:cm_expr)) + 14i)`;
            cm_finish_binary_count_branch(
                shape, concrete, THM_LIST(
                  eqf_intro_rule(assume_rule(
                    `~((op_:int) == 0i || op_ == 1i)`)),
                  assume_rule(`(op_:int) == 8i`),
                  eqt_intro_rule(right_pointer_case)));
          }
        } else {
          int left_type;
          cmc_expr_type_code_value(expr->a, &left_type);
          int left_pointer;
          cmc_is_pointer_value(left_type, &left_pointer);
          [[cst::proof]] {
            thm bridge = mp_rule(spec_rule(
                `cm_expr_type (left_:cm_expr)`,
                cm_pointer_code_bridge),
                from_state_bool(
                  `cm_type_code_wf
                     (cm_expr_type (left_:cm_expr))`));
            substitute_st(bridge);
          }
          if (left_pointer) {
            [[cst::proof]] {
              thm right_nonpointer_case = eq_mp_rule(
                  conjunct1_rule(spec_rule(
                    `cm_expr_type (right_:cm_expr)`,
                    cm_pointer_code_value_cases)),
                  assume_rule(
                    `cm_pointer_code_value
                       (cm_expr_type (right_:cm_expr)) == 0i`));
              thm left_pointer_case = eq_mp_rule(
                  conjunct2_rule(spec_rule(
                    `cm_expr_type (left_:cm_expr)`,
                    cm_pointer_code_value_cases)),
                  assume_rule(
                    `~(cm_pointer_code_value
                         (cm_expr_type (left_:cm_expr)) == 0i)`));
              term concrete =
                  `cm_rcount_of (cm_expr_code_counts
                     (p:cm_program) (fid__pre:int) (left_:cm_expr)) +
                   (cm_rcount_of (cm_expr_code_counts
                     p fid__pre (right_:cm_expr)) + 14i)`;
              cm_prepare_binary_count_sum(
                  concrete, `14i`, int_arith_rule(`0i <= 14i`),
                  THM_LIST(
                    eqf_intro_rule(assume_rule(
                      `~((op_:int) == 0i || op_ == 1i)`)),
                    assume_rule(`(op_:int) == 8i`),
                    eqf_intro_rule(right_nonpointer_case),
                    eqt_intro_rule(left_pointer_case)));
            }
            out_rvalue = left_rvalue + (right_rvalue + 14);
            [[cst::proof]] {
              thm shape = assume_rule(
                  `e == CMBinaryE (op_:int) (left_:cm_expr)
                     (right_:cm_expr) (ty_:cm_type)`);
              thm right_nonpointer_case = eq_mp_rule(
                  conjunct1_rule(spec_rule(
                    `cm_expr_type (right_:cm_expr)`,
                    cm_pointer_code_value_cases)),
                  assume_rule(
                    `cm_pointer_code_value
                       (cm_expr_type (right_:cm_expr)) == 0i`));
              thm left_pointer_case = eq_mp_rule(
                  conjunct2_rule(spec_rule(
                    `cm_expr_type (left_:cm_expr)`,
                    cm_pointer_code_value_cases)),
                  assume_rule(
                    `~(cm_pointer_code_value
                         (cm_expr_type (left_:cm_expr)) == 0i)`));
              term concrete =
                  `cm_rcount_of (cm_expr_code_counts
                     (p:cm_program) (fid__pre:int) (left_:cm_expr)) +
                   (cm_rcount_of (cm_expr_code_counts
                     p fid__pre (right_:cm_expr)) + 14i)`;
              cm_finish_binary_count_branch(
                  shape, concrete, THM_LIST(
                    eqf_intro_rule(assume_rule(
                      `~((op_:int) == 0i || op_ == 1i)`)),
                    assume_rule(`(op_:int) == 8i`),
                    eqf_intro_rule(right_nonpointer_case),
                    eqt_intro_rule(left_pointer_case)));
            }
          } else {
            [[cst::proof]] {
              thm right_nonpointer_case = eq_mp_rule(
                  conjunct1_rule(spec_rule(
                    `cm_expr_type (right_:cm_expr)`,
                    cm_pointer_code_value_cases)),
                  assume_rule(
                    `cm_pointer_code_value
                       (cm_expr_type (right_:cm_expr)) == 0i`));
              thm left_nonpointer_case = eq_mp_rule(
                  conjunct1_rule(spec_rule(
                    `cm_expr_type (left_:cm_expr)`,
                    cm_pointer_code_value_cases)),
                  assume_rule(
                    `cm_pointer_code_value
                       (cm_expr_type (left_:cm_expr)) == 0i`));
              term concrete =
                  `cm_rcount_of (cm_expr_code_counts
                     (p:cm_program) (fid__pre:int) (left_:cm_expr)) +
                   (cm_rcount_of (cm_expr_code_counts
                     p fid__pre (right_:cm_expr)) + 12i)`;
              cm_prepare_binary_count_sum(
                  concrete, `12i`, int_arith_rule(`0i <= 12i`),
                  THM_LIST(
                    eqf_intro_rule(assume_rule(
                      `~((op_:int) == 0i || op_ == 1i)`)),
                    assume_rule(`(op_:int) == 8i`),
                    eqf_intro_rule(right_nonpointer_case),
                    eqf_intro_rule(left_nonpointer_case)));
            }
            out_rvalue = left_rvalue + (right_rvalue + 12);
            [[cst::proof]] {
              thm shape = assume_rule(
                  `e == CMBinaryE (op_:int) (left_:cm_expr)
                     (right_:cm_expr) (ty_:cm_type)`);
              thm right_nonpointer_case = eq_mp_rule(
                  conjunct1_rule(spec_rule(
                    `cm_expr_type (right_:cm_expr)`,
                    cm_pointer_code_value_cases)),
                  assume_rule(
                    `cm_pointer_code_value
                       (cm_expr_type (right_:cm_expr)) == 0i`));
              thm left_nonpointer_case = eq_mp_rule(
                  conjunct1_rule(spec_rule(
                    `cm_expr_type (left_:cm_expr)`,
                    cm_pointer_code_value_cases)),
                  assume_rule(
                    `cm_pointer_code_value
                       (cm_expr_type (left_:cm_expr)) == 0i`));
              term concrete =
                  `cm_rcount_of (cm_expr_code_counts
                     (p:cm_program) (fid__pre:int) (left_:cm_expr)) +
                   (cm_rcount_of (cm_expr_code_counts
                     p fid__pre (right_:cm_expr)) + 12i)`;
              cm_finish_binary_count_branch(
                  shape, concrete, THM_LIST(
                    eqf_intro_rule(assume_rule(
                      `~((op_:int) == 0i || op_ == 1i)`)),
                    assume_rule(`(op_:int) == 8i`),
                    eqf_intro_rule(right_nonpointer_case),
                    eqf_intro_rule(left_nonpointer_case)));
            }
          }
        }
      } else if (expr->op == CMC_BIN_SUB) {
        int left_type;
        cmc_expr_type_code_value(expr->a, &left_type);
        int left_pointer;
        cmc_is_pointer_value(left_type, &left_pointer);
        [[cst::proof]] {
          thm bridge = mp_rule(spec_rule(
              `cm_expr_type (left_:cm_expr)`,
              cm_pointer_code_bridge),
              from_state_bool(
                `cm_type_code_wf
                   (cm_expr_type (left_:cm_expr))`));
          substitute_st(bridge);
        }
        if (left_pointer) {
          [[cst::proof]] {
            thm left_pointer_case = eq_mp_rule(
                conjunct2_rule(spec_rule(
                  `cm_expr_type (left_:cm_expr)`,
                  cm_pointer_code_value_cases)),
                assume_rule(
                  `~(cm_pointer_code_value
                       (cm_expr_type (left_:cm_expr)) == 0i)`));
            term concrete =
                `cm_rcount_of (cm_expr_code_counts
                   (p:cm_program) (fid__pre:int) (left_:cm_expr)) +
                 (cm_rcount_of (cm_expr_code_counts
                   p fid__pre (right_:cm_expr)) + 14i)`;
            cm_prepare_binary_count_sum(
                concrete, `14i`, int_arith_rule(`0i <= 14i`),
                THM_LIST(
                  eqf_intro_rule(assume_rule(
                    `~((op_:int) == 0i || op_ == 1i)`)),
                  assume_rule(`(op_:int) == 9i`),
                  eqt_intro_rule(left_pointer_case)));
          }
          out_rvalue = left_rvalue + (right_rvalue + 14);
          [[cst::proof]] {
            thm shape = assume_rule(
                `e == CMBinaryE (op_:int) (left_:cm_expr)
                   (right_:cm_expr) (ty_:cm_type)`);
            thm left_pointer_case = eq_mp_rule(
                conjunct2_rule(spec_rule(
                  `cm_expr_type (left_:cm_expr)`,
                  cm_pointer_code_value_cases)),
                assume_rule(
                  `~(cm_pointer_code_value
                       (cm_expr_type (left_:cm_expr)) == 0i)`));
            term concrete =
                `cm_rcount_of (cm_expr_code_counts
                   (p:cm_program) (fid__pre:int) (left_:cm_expr)) +
                 (cm_rcount_of (cm_expr_code_counts
                   p fid__pre (right_:cm_expr)) + 14i)`;
            cm_finish_binary_count_branch(
                shape, concrete, THM_LIST(
                  eqf_intro_rule(assume_rule(
                    `~((op_:int) == 0i || op_ == 1i)`)),
                  assume_rule(`(op_:int) == 9i`),
                  eqt_intro_rule(left_pointer_case)));
          }
        } else {
          [[cst::proof]] {
            thm left_nonpointer_case = eq_mp_rule(
                conjunct1_rule(spec_rule(
                  `cm_expr_type (left_:cm_expr)`,
                  cm_pointer_code_value_cases)),
                assume_rule(
                  `cm_pointer_code_value
                     (cm_expr_type (left_:cm_expr)) == 0i`));
            term concrete =
                `cm_rcount_of (cm_expr_code_counts
                   (p:cm_program) (fid__pre:int) (left_:cm_expr)) +
                 (cm_rcount_of (cm_expr_code_counts
                   p fid__pre (right_:cm_expr)) + 12i)`;
            cm_prepare_binary_count_sum(
                concrete, `12i`, int_arith_rule(`0i <= 12i`),
                THM_LIST(
                  eqf_intro_rule(assume_rule(
                    `~((op_:int) == 0i || op_ == 1i)`)),
                  assume_rule(`(op_:int) == 9i`),
                  eqf_intro_rule(left_nonpointer_case)));
          }
          out_rvalue = left_rvalue + (right_rvalue + 12);
          [[cst::proof]] {
            thm shape = assume_rule(
                `e == CMBinaryE (op_:int) (left_:cm_expr)
                   (right_:cm_expr) (ty_:cm_type)`);
            thm left_nonpointer_case = eq_mp_rule(
                conjunct1_rule(spec_rule(
                  `cm_expr_type (left_:cm_expr)`,
                  cm_pointer_code_value_cases)),
                assume_rule(
                  `cm_pointer_code_value
                     (cm_expr_type (left_:cm_expr)) == 0i`));
            term concrete =
                `cm_rcount_of (cm_expr_code_counts
                   (p:cm_program) (fid__pre:int) (left_:cm_expr)) +
                 (cm_rcount_of (cm_expr_code_counts
                   p fid__pre (right_:cm_expr)) + 12i)`;
            cm_finish_binary_count_branch(
                shape, concrete, THM_LIST(
                  eqf_intro_rule(assume_rule(
                    `~((op_:int) == 0i || op_ == 1i)`)),
                  assume_rule(`(op_:int) == 9i`),
                  eqf_intro_rule(left_nonpointer_case)));
          }
        }
      } else {
        [[cst::proof]] {
          term concrete =
              `cm_rcount_of (cm_expr_code_counts
                 (p:cm_program) (fid__pre:int) (left_:cm_expr)) +
               (cm_rcount_of (cm_expr_code_counts
                 p fid__pre (right_:cm_expr)) + 12i)`;
          cm_prepare_binary_count_sum(
              concrete, `12i`, int_arith_rule(`0i <= 12i`),
              THM_LIST(
                eqf_intro_rule(assume_rule(
                  `~((op_:int) == 0i || op_ == 1i)`)),
                assume_rule(`~((op_:int) == 8i)`),
                assume_rule(`~((op_:int) == 9i)`)));
        }
        out_rvalue = left_rvalue + (right_rvalue + 12);
        [[cst::proof]] {
          thm shape = assume_rule(
              `e == CMBinaryE (op_:int) (left_:cm_expr)
                 (right_:cm_expr) (ty_:cm_type)`);
          term concrete =
              `cm_rcount_of (cm_expr_code_counts
                 (p:cm_program) (fid__pre:int) (left_:cm_expr)) +
               (cm_rcount_of (cm_expr_code_counts
                 p fid__pre (right_:cm_expr)) + 12i)`;
          cm_finish_binary_count_branch(
              shape, concrete, THM_LIST(
                eqf_intro_rule(assume_rule(
                  `~((op_:int) == 0i || op_ == 1i)`)),
                assume_rule(`~((op_:int) == 8i)`),
                assume_rule(`~((op_:int) == 9i)`)));
        }
      }
    }
    [[cst::proof]] {
      thm shape = assume_rule(
          `e == CMBinaryE (op_:int) (left_:cm_expr)
             (right_:cm_expr) (ty_:cm_type)`);
      thm op_model = by_rewrite(
          `cm_rep_expr_op (e:cm_expr) == (op_:int)`,
          THM_LIST(shape, get_cm_rep_expr_op_def()));
      substitute_st(sym_rule(op_model));
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
      cm_open_expr_count_facts(shape);
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
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`structs`, `structs:(cm_struct_d)list`)]]
    [[cst::where(`globals`, `globals:(cm_global_d)list`)]]
    [[cst::where(`locals`, `locals:(cm_slot_d)list`)]]
    [[cst::where(`zs`, `(zs:int)`)]]
    [[cst::where(`zg`, `(zg:int)`)]]
    [[cst::where(`zl`, `(zl:int)`)]]
    cm_expr_counts(program, fid, fn, expr->a,
                   &child_lvalue, &child_rvalue);
    [[cst::proof]] {
      thm shape = assume_rule(
          `e == CMUnaryE (op_:int)
             (arg_:cm_expr) (ty_:cm_type)`);
      thm op_model = by_rewrite(
          `cm_rep_expr_op (e:cm_expr) == (op_:int)`,
          THM_LIST(shape, get_cm_rep_expr_op_def()));
      substitute_st(op_model);
    }
    if (expr->op == CMC_UN_DEREF) {
      [[cst::proof]] {
        term model_count =
            `cm_rcount_of
               (cm_expr_code_counts (p:cm_program) (fid__pre:int)
                 (CMUnaryE (op_:int) (arg_:cm_expr)
                   (ty_:cm_type)))`;
        term concrete_count =
            `cm_rcount_of
               (cm_expr_code_counts (p:cm_program)
                 (fid__pre:int) (arg_:cm_expr)) + 1i`;
        thm model = by_rewrite(mk_eq(model_count, concrete_count),
            THM_LIST(get_cm_expr_code_counts_def(),
              get_cm_rcount_of_def(),
              eqt_intro_rule(assume_rule(`(op_:int) == 2i`))));
        thm upper_equivalence = beta_norm(ap_term_rule(
            `\n:int. n <= 2147483647i`, model));
        thm concrete_upper = eq_mp_rule(upper_equivalence,
            assume_rule(
              `cm_rcount_of
                 (cm_expr_code_counts (p:cm_program) (fid__pre:int)
                   (CMUnaryE (op_:int) (arg_:cm_expr)
                     (ty_:cm_type))) <= 2147483647i`));
        add_fact_st(concrete_upper);
        cm_add_count_facts(from_state_bool(
            `cm_i32_code_count
               (cm_rcount_of
                 (cm_expr_code_counts (p:cm_program)
                   (fid__pre:int) (arg_:cm_expr)))`));
        add_fact_st(mp_rule(int_arith_rule(
            `0i <= cm_rcount_of
               (cm_expr_code_counts (p:cm_program)
                 (fid__pre:int) (arg_:cm_expr)) ==>
             --2147483648i <=
               cm_rcount_of
                 (cm_expr_code_counts p fid__pre arg_) + 1i`),
            assume_rule(
              `0i <= cm_rcount_of
                 (cm_expr_code_counts (p:cm_program)
                   (fid__pre:int) (arg_:cm_expr))`)));
      }
      out_lvalue = child_rvalue;
      out_rvalue = child_rvalue + 1;
      [[cst::proof]] {
        thm shape = assume_rule(
            `e == CMUnaryE (op_:int)
               (arg_:cm_expr) (ty_:cm_type)`);
        cm_finish_expr_count_cells_with_rules(shape,
            `cm_rcount_of
               (cm_expr_code_counts (p:cm_program)
                 (fid__pre:int) (arg_:cm_expr))`,
            `cm_rcount_of
               (cm_expr_code_counts (p:cm_program)
                 (fid__pre:int) (arg_:cm_expr)) + 1i`,
            THM_LIST(eqt_intro_rule(
              assume_rule(`(op_:int) == 2i`))));
      }
    } else if (expr->op == CMC_UN_ADDR) {
      out_rvalue = child_lvalue;
      [[cst::proof]] {
        thm shape = assume_rule(
            `e == CMUnaryE (op_:int)
               (arg_:cm_expr) (ty_:cm_type)`);
        cm_finish_expr_count_cells_with_rules(shape, `0i`,
            `cm_lcount_of
               (cm_expr_code_counts (p:cm_program)
                 (fid__pre:int) (arg_:cm_expr))`,
            THM_LIST(
              eqf_intro_rule(
                assume_rule(`~((op_:int) == 2i)`)),
              eqt_intro_rule(
                assume_rule(`(op_:int) == 3i`))));
      }
    } else {
      [[cst::proof]] {
        term model_count =
            `cm_rcount_of
               (cm_expr_code_counts (p:cm_program) (fid__pre:int)
                 (CMUnaryE (op_:int) (arg_:cm_expr)
                   (ty_:cm_type)))`;
        term concrete_count =
            `cm_rcount_of
               (cm_expr_code_counts (p:cm_program)
                 (fid__pre:int) (arg_:cm_expr)) + 2i`;
        thm_list rules = THM_LIST(
            get_cm_expr_code_counts_def(), get_cm_rcount_of_def(),
            eqf_intro_rule(
              assume_rule(`~((op_:int) == 2i)`)),
            eqf_intro_rule(
              assume_rule(`~((op_:int) == 3i)`)));
        thm model = by_rewrite(
            mk_eq(model_count, concrete_count), rules);
        thm upper_equivalence = beta_norm(ap_term_rule(
            `\n:int. n <= 2147483647i`, model));
        thm concrete_upper = eq_mp_rule(upper_equivalence,
            assume_rule(
              `cm_rcount_of
                 (cm_expr_code_counts (p:cm_program) (fid__pre:int)
                   (CMUnaryE (op_:int) (arg_:cm_expr)
                     (ty_:cm_type))) <= 2147483647i`));
        add_fact_st(concrete_upper);
        cm_add_count_facts(from_state_bool(
            `cm_i32_code_count
               (cm_rcount_of
                 (cm_expr_code_counts (p:cm_program)
                   (fid__pre:int) (arg_:cm_expr)))`));
        add_fact_st(mp_rule(int_arith_rule(
            `0i <= cm_rcount_of
               (cm_expr_code_counts (p:cm_program)
                 (fid__pre:int) (arg_:cm_expr)) ==>
             --2147483648i <=
               cm_rcount_of
                 (cm_expr_code_counts p fid__pre arg_) + 2i`),
            assume_rule(
              `0i <= cm_rcount_of
                 (cm_expr_code_counts (p:cm_program)
                   (fid__pre:int) (arg_:cm_expr))`)));
      }
      out_rvalue = child_rvalue + 2;
      [[cst::proof]] {
        thm shape = assume_rule(
            `e == CMUnaryE (op_:int)
               (arg_:cm_expr) (ty_:cm_type)`);
        cm_finish_expr_count_cells_with_rules(shape, `0i`,
            `cm_rcount_of
               (cm_expr_code_counts (p:cm_program)
                 (fid__pre:int) (arg_:cm_expr)) + 2i`,
            THM_LIST(
              eqf_intro_rule(
                assume_rule(`~((op_:int) == 2i)`)),
              eqf_intro_rule(
                assume_rule(`~((op_:int) == 3i)`))));
      }
    }
    [[cst::proof]] {
      thm shape = assume_rule(
          `e == CMUnaryE (op_:int)
             (arg_:cm_expr) (ty_:cm_type)`);
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
      apply_hconv_st(payload_fold);
    }
    [[cst::proof]] {
      thm shape = assume_rule(
          `e == CMUnaryE (op_:int)
             (arg_:cm_expr) (ty_:cm_type)`);
      thm op_model = by_rewrite(
          `cm_rep_expr_op (e:cm_expr) == (op_:int)`,
          THM_LIST(shape, get_cm_rep_expr_op_def()));
      substitute_st(sym_rule(op_model));
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
      cm_open_expr_count_facts(shape);
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
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`structs`, `structs:(cm_struct_d)list`)]]
    [[cst::where(`globals`, `globals:(cm_global_d)list`)]]
    [[cst::where(`locals`, `locals:(cm_slot_d)list`)]]
    [[cst::where(`zs`, `(zs:int)`)]]
    [[cst::where(`zg`, `(zg:int)`)]]
    [[cst::where(`zl`, `(zl:int)`)]]
    cm_expr_counts(program, fid, fn, expr->a,
                   &base_lvalue, &base_rvalue);
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`structs`, `structs:(cm_struct_d)list`)]]
    [[cst::where(`globals`, `globals:(cm_global_d)list`)]]
    [[cst::where(`locals`, `locals:(cm_slot_d)list`)]]
    [[cst::where(`zs`, `(zs:int)`)]]
    [[cst::where(`zg`, `(zg:int)`)]]
    [[cst::where(`zl`, `(zl:int)`)]]
    cm_expr_counts(program, fid, fn, expr->b,
                   &index_lvalue, &index_rvalue);
    [[cst::proof]] {
      term base_count =
          `cm_rcount_of
             (cm_expr_code_counts (p:cm_program)
               (fid__pre:int) (base_:cm_expr))`;
      term index_count =
          `cm_rcount_of
             (cm_expr_code_counts (p:cm_program)
               (fid__pre:int) (index_:cm_expr))`;
      term model_lvalue =
          `cm_lcount_of
             (cm_expr_code_counts (p:cm_program) (fid__pre:int)
               (CMIndexE (base_:cm_expr) (index_:cm_expr)
                 (ty_:cm_type)))`;
      term model_rvalue =
          `cm_rcount_of
             (cm_expr_code_counts (p:cm_program) (fid__pre:int)
               (CMIndexE (base_:cm_expr) (index_:cm_expr)
                 (ty_:cm_type)))`;
      term concrete_lvalue =
          `cm_rcount_of (cm_expr_code_counts
             (p:cm_program) (fid__pre:int) (base_:cm_expr)) +
           (cm_rcount_of (cm_expr_code_counts
             p fid__pre (index_:cm_expr)) + 13i)`;
      term concrete_rvalue =
          `(cm_rcount_of (cm_expr_code_counts
              (p:cm_program) (fid__pre:int) (base_:cm_expr)) +
            (cm_rcount_of (cm_expr_code_counts
              p fid__pre (index_:cm_expr)) + 13i)) + 1i`;
      thm_list rules = THM_LIST(
          get_cm_expr_code_counts_def(), get_cm_lcount_of_def(),
          get_cm_rcount_of_def(),
          int_ring_rule(
            `!(base_count:int) (index_count:int).
               base_count + index_count + 13i ==
               base_count + (index_count + 13i)`),
          int_ring_rule(
            `!(base_count:int) (index_count:int).
               base_count + index_count + 14i ==
               (base_count + (index_count + 13i)) + 1i`));
      thm lvalue_model =
          by_rewrite(mk_eq(model_lvalue, concrete_lvalue), rules);
      thm rvalue_model =
          by_rewrite(mk_eq(model_rvalue, concrete_rvalue), rules);
      thm lvalue_upper = eq_mp_rule(beta_norm(ap_term_rule(
          `\n:int. n <= 2147483647i`, lvalue_model)),
          assume_rule(
            `cm_lcount_of
               (cm_expr_code_counts (p:cm_program) (fid__pre:int)
                 (CMIndexE (base_:cm_expr) (index_:cm_expr)
                   (ty_:cm_type))) <= 2147483647i`));
      thm rvalue_upper = eq_mp_rule(beta_norm(ap_term_rule(
          `\n:int. n <= 2147483647i`, rvalue_model)),
          assume_rule(
            `cm_rcount_of
               (cm_expr_code_counts (p:cm_program) (fid__pre:int)
                 (CMIndexE (base_:cm_expr) (index_:cm_expr)
                   (ty_:cm_type))) <= 2147483647i`));
      cm_add_count_facts(from_state_bool(
          `cm_i32_code_count
             (cm_rcount_of
               (cm_expr_code_counts (p:cm_program)
                 (fid__pre:int) (base_:cm_expr)))`));
      cm_add_count_facts(from_state_bool(
          `cm_i32_code_count
             (cm_rcount_of
               (cm_expr_code_counts (p:cm_program)
                 (fid__pre:int) (index_:cm_expr)))`));
      thm bounds = specl_rule(TERM_LIST(base_count, index_count),
          int_arith_rule(
            `!(base_count:int) (index_count:int).
               0i <= base_count ==> 0i <= index_count ==>
               base_count + (index_count + 13i) <= 2147483647i ==>
               (base_count + (index_count + 13i)) + 1i <=
                 2147483647i ==>
               (--2147483648i <= index_count + 13i &&
                index_count + 13i <= 2147483647i &&
                --2147483648i <=
                  base_count + (index_count + 13i) &&
                base_count + (index_count + 13i) <= 2147483647i &&
                --2147483648i <=
                  (base_count + (index_count + 13i)) + 1i &&
                (base_count + (index_count + 13i)) + 1i <=
                  2147483647i)`));
      bounds = mp_rule(bounds, assume_rule(
          `0i <= cm_rcount_of
             (cm_expr_code_counts (p:cm_program)
               (fid__pre:int) (base_:cm_expr))`));
      bounds = mp_rule(bounds, assume_rule(
          `0i <= cm_rcount_of
             (cm_expr_code_counts (p:cm_program)
               (fid__pre:int) (index_:cm_expr))`));
      bounds = mp_rule(bounds, lvalue_upper);
      bounds = mp_rule(bounds, rvalue_upper);
      add_fact_st(conjunct1_rule(bounds));
      thm rest = conjunct2_rule(bounds);
      add_fact_st(conjunct1_rule(rest));
      rest = conjunct2_rule(rest);
      add_fact_st(conjunct1_rule(rest));
      rest = conjunct2_rule(rest);
      add_fact_st(conjunct1_rule(rest));
      rest = conjunct2_rule(rest);
      add_fact_st(conjunct1_rule(rest));
      add_fact_st(conjunct2_rule(rest));
    }
    out_lvalue = base_rvalue + (index_rvalue + 13);
    out_rvalue = out_lvalue + 1;
    [[cst::proof]] {
      thm shape = assume_rule(
          `e == CMIndexE (base_:cm_expr)
             (index_:cm_expr) (ty_:cm_type)`);
      thm_list rules = THM_LIST(
          int_ring_rule(
            `!(base_count:int) (index_count:int).
               base_count + index_count + 13i ==
               base_count + (index_count + 13i)`),
          int_ring_rule(
            `!(base_count:int) (index_count:int).
               base_count + index_count + 14i ==
               (base_count + (index_count + 13i)) + 1i`));
      cm_finish_expr_count_cells_with_rules(shape,
          `cm_rcount_of (cm_expr_code_counts
             (p:cm_program) (fid__pre:int) (base_:cm_expr)) +
           (cm_rcount_of (cm_expr_code_counts
             p fid__pre (index_:cm_expr)) + 13i)`,
          `(cm_rcount_of (cm_expr_code_counts
              (p:cm_program) (fid__pre:int) (base_:cm_expr)) +
            (cm_rcount_of (cm_expr_code_counts
              p fid__pre (index_:cm_expr)) + 13i)) + 1i`,
          rules);
      thm base_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`za:int`, `p:int`},
          (term_pair){`base_:cm_expr`, `e:cm_expr`}),
          get_cm_expr_rep_def());
      apply_hconv_st(eq2ent(base_view));
      thm index_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`zb:int`, `p:int`},
          (term_pair){`index_:cm_expr`, `e:cm_expr`}),
          get_cm_expr_rep_def());
      apply_hconv_st(eq2ent(index_view));
      thm payload_view = by_rewrite(
          `cm_expr_payload (e:cm_expr)
             (za:int) (zb:int) (zargs:int) -|-
           fact(zargs == 0i) **
           cm_expr_node za (base_:cm_expr)
             (cm_expr_payload base_) **
           cm_expr_node zb (index_:cm_expr)
             (cm_expr_payload index_)`,
          THM_LIST(shape, get_cm_expr_payload_def()));
      apply_hconv_st(eq2ent(sym_rule(payload_view)));
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
      cm_open_expr_count_facts(shape);
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
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`structs`, `structs:(cm_struct_d)list`)]]
    [[cst::where(`globals`, `globals:(cm_global_d)list`)]]
    [[cst::where(`locals`, `locals:(cm_slot_d)list`)]]
    [[cst::where(`zs`, `(zs:int)`)]]
    [[cst::where(`zg`, `(zg:int)`)]]
    [[cst::where(`zl`, `(zl:int)`)]]
    cm_expr_counts(program, fid, fn, expr->a,
                   &base_lvalue, &base_rvalue);
    [[cst::proof]] {
      term model_lvalue =
          `cm_lcount_of
             (cm_expr_code_counts (p:cm_program) (fid__pre:int)
               (CMMemberE (base_:cm_expr) (mid_:int)
                 (ty_:cm_type)))`;
      term concrete_lvalue =
          `cm_rcount_of
             (cm_expr_code_counts (p:cm_program)
               (fid__pre:int) (base_:cm_expr)) + 2i`;
      thm model = by_rewrite(mk_eq(model_lvalue, concrete_lvalue),
          THM_LIST(get_cm_expr_code_counts_def(),
            get_cm_lcount_of_def()));
      thm concrete_upper = eq_mp_rule(beta_norm(ap_term_rule(
          `\n:int. n <= 2147483647i`, model)),
          assume_rule(
            `cm_lcount_of
               (cm_expr_code_counts (p:cm_program) (fid__pre:int)
                 (CMMemberE (base_:cm_expr) (mid_:int)
                   (ty_:cm_type))) <= 2147483647i`));
      add_fact_st(concrete_upper);
      cm_add_count_facts(from_state_bool(
          `cm_i32_code_count
             (cm_rcount_of
               (cm_expr_code_counts (p:cm_program)
                 (fid__pre:int) (base_:cm_expr)))`));
      add_fact_st(mp_rule(int_arith_rule(
          `0i <= cm_rcount_of
             (cm_expr_code_counts (p:cm_program)
               (fid__pre:int) (base_:cm_expr)) ==>
           --2147483648i <=
             cm_rcount_of
               (cm_expr_code_counts p fid__pre base_) + 2i`),
          assume_rule(
            `0i <= cm_rcount_of
               (cm_expr_code_counts (p:cm_program)
                 (fid__pre:int) (base_:cm_expr))`)));
    }
    out_lvalue = base_rvalue + 2;
    out_rvalue = out_lvalue;
    int base_type;
    cmc_expr_type_code_value(expr->a, &base_type);
    int member_id = (int)expr->value;
    [[cst::proof]] {
      thm shape = assume_rule(
          `e == CMMemberE (base_:cm_expr)
             (mid_:int) (ty_:cm_type)`);
      thm value_model = by_rewrite(
          `cm_rep_expr_value (e:cm_expr) == (mid_:int)`,
          THM_LIST(shape, get_cm_rep_expr_value_def()));
      thm member_cast = mp_rule(mp_rule(
          spec_rule(`mid_:int`, cm_nonnegative_i32_cast),
          assume_rule(`0i <= (mid_:int)`)),
          assume_rule(`(mid_:int) <= 2147483647i`));
      thm cast_model = trans_rule(beta_norm(ap_term_rule(
          `\n:int. signed_last_nbits n 32i`, value_model)),
          member_cast);
      substitute_st(cast_model);
      cm_add_count_facts(from_state_bool(
          `cm_i32_code_count
             (cm_type_encode (cm_expr_type (base_:cm_expr)))`));
      thm valid = conv_rule(rewrite_conv(THM_LIST(
          get_cm_member_valid_def())), from_state_bool(
            `cm_member_valid (p:cm_program)
               (cm_expr_type (base_:cm_expr)) (mid_:int)`));
      thm pointer = conjunct1_rule(valid);
      thm rest = conjunct2_rule(valid);
      thm structure = conjunct1_rule(rest);
      rest = conjunct2_rule(rest);
      thm sid_nonnegative = conjunct1_rule(rest);
      thm type_wf = from_state_bool(
          `cm_type_code_wf (cm_expr_type (base_:cm_expr))`);
      thm threshold = mp_rule(spec_rule(
          `cm_expr_type (base_:cm_expr)`,
          cm_pointer_encode_threshold), type_wf);
      add_fact_st(eq_mp_rule(sym_rule(threshold), pointer));
      thm sid_model = match_mp_rule(match_mp_rule(match_mp_rule(
          spec_rule(`cm_expr_type (base_:cm_expr)`,
            cm_encoded_member_sid),
          type_wf), pointer), structure);
      thm sid_nonnegative_model = eq_mp_rule(sym_rule(
          beta_norm(ap_term_rule(`\z:int. 0i <= z`, sid_model))),
          sid_nonnegative);
      add_fact_st(sid_nonnegative_model);
    }
    int array;
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`structs`, `structs:(cm_struct_d)list`)]]
    [[cst::where(`zs`, `(zs:int)`)]]
    cmc_member_array_value(
        program, base_type, member_id, &array);
    if (!array) {
      [[cst::proof]] {
        thm code_cases = specl_rule(TERM_LIST(
            `p:cm_program`, `cm_expr_type (base_:cm_expr)`,
            `mid_:int`), cm_member_array_code_cases);
        thm not_array = eq_mp_rule(conjunct1_rule(code_cases),
            assume_rule(
              `cm_member_array_code (p:cm_program)
                 (cm_expr_type (base_:cm_expr)) (mid_:int) == 0i`));
        term model_rvalue =
            `cm_rcount_of
               (cm_expr_code_counts (p:cm_program) (fid__pre:int)
                 (CMMemberE (base_:cm_expr) (mid_:int)
                   (ty_:cm_type)))`;
        term concrete_rvalue =
            `(cm_rcount_of
                (cm_expr_code_counts (p:cm_program)
                  (fid__pre:int) (base_:cm_expr)) + 2i) + 1i`;
        thm model = by_rewrite(mk_eq(model_rvalue, concrete_rvalue),
            THM_LIST(get_cm_expr_code_counts_def(),
              get_cm_rcount_of_def(), eqf_intro_rule(not_array),
              int_ring_rule(
                `!b:int. b + 2i + 1i == (b + 2i) + 1i`)));
        thm concrete_upper = eq_mp_rule(beta_norm(ap_term_rule(
            `\n:int. n <= 2147483647i`, model)),
            assume_rule(
              `cm_rcount_of
                 (cm_expr_code_counts (p:cm_program) (fid__pre:int)
                   (CMMemberE (base_:cm_expr) (mid_:int)
                     (ty_:cm_type))) <= 2147483647i`));
        add_fact_st(concrete_upper);
        add_fact_st(mp_rule(int_arith_rule(
            `0i <= cm_rcount_of
               (cm_expr_code_counts (p:cm_program)
                 (fid__pre:int) (base_:cm_expr)) ==>
             --2147483648i <=
               (cm_rcount_of
                  (cm_expr_code_counts p fid__pre base_) + 2i) + 1i`),
            assume_rule(
              `0i <= cm_rcount_of
                 (cm_expr_code_counts (p:cm_program)
                   (fid__pre:int) (base_:cm_expr))`)));
      }
      out_rvalue = out_rvalue + 1;
      [[cst::proof]] {
        thm shape = assume_rule(
            `e == CMMemberE (base_:cm_expr)
               (mid_:int) (ty_:cm_type)`);
        thm code_cases = specl_rule(TERM_LIST(
            `p:cm_program`, `cm_expr_type (base_:cm_expr)`,
            `mid_:int`), cm_member_array_code_cases);
        thm not_array = eq_mp_rule(conjunct1_rule(code_cases),
            assume_rule(
              `cm_member_array_code (p:cm_program)
                 (cm_expr_type (base_:cm_expr)) (mid_:int) == 0i`));
        cm_finish_expr_count_cells_with_rules(shape,
            `cm_rcount_of
               (cm_expr_code_counts (p:cm_program)
                 (fid__pre:int) (base_:cm_expr)) + 2i`,
            `(cm_rcount_of
                (cm_expr_code_counts (p:cm_program)
                  (fid__pre:int) (base_:cm_expr)) + 2i) + 1i`,
            THM_LIST(eqf_intro_rule(not_array),
              int_ring_rule(
                `!b:int. b + 2i + 1i == (b + 2i) + 1i`)));
      }
    } else {
      [[cst::proof]] {
        thm shape = assume_rule(
            `e == CMMemberE (base_:cm_expr)
               (mid_:int) (ty_:cm_type)`);
        thm code_cases = specl_rule(TERM_LIST(
            `p:cm_program`, `cm_expr_type (base_:cm_expr)`,
            `mid_:int`), cm_member_array_code_cases);
        thm is_array = eq_mp_rule(conjunct2_rule(code_cases),
            assume_rule(
              `~(cm_member_array_code (p:cm_program)
                   (cm_expr_type (base_:cm_expr)) (mid_:int) == 0i)`));
        cm_finish_expr_count_cells_with_rules(shape,
            `cm_rcount_of
               (cm_expr_code_counts (p:cm_program)
                 (fid__pre:int) (base_:cm_expr)) + 2i`,
            `cm_rcount_of
               (cm_expr_code_counts (p:cm_program)
                 (fid__pre:int) (base_:cm_expr)) + 2i`,
            THM_LIST(eqt_intro_rule(is_array),
              int_arith_rule(`!x:int. x + 0i == x`)));
      }
    }
    [[cst::proof]] {
      thm shape = assume_rule(
          `e == CMMemberE (base_:cm_expr)
             (mid_:int) (ty_:cm_type)`);
      thm base_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`za:int`, `p:int`},
          (term_pair){`base_:cm_expr`, `e:cm_expr`}),
          get_cm_expr_rep_def());
      apply_hconv_st(eq2ent(base_view));
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
      apply_hconv_st(payload_fold);
    }
  } else if (expr->kind == CMC_EXPR_CALL) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`e:cm_expr`,
          get_cm_expr_call_shape_ent()),
          assume_rule(`cm_rep_expr_kind (e:cm_expr) == 8i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`callee_:int`, `args_:(cm_expr)list`,
                      `ty_:cm_type`))));
      thm shape = assume_rule(
          `e == CMCallE (callee_:int)
             (args_:(cm_expr)list) (ty_:cm_type)`);
      cm_open_expr_count_facts(shape);
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
    int args_count;
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`structs`, `structs:(cm_struct_d)list`)]]
    [[cst::where(`globals`, `globals:(cm_global_d)list`)]]
    [[cst::where(`locals`, `locals:(cm_slot_d)list`)]]
    [[cst::where(`zs`, `(zs:int)`)]]
    [[cst::where(`zg`, `(zg:int)`)]]
    [[cst::where(`zl`, `(zl:int)`)]]
    cmc_args_code_count(
        program, fid, fn, expr->args, &args_count);
    out_rvalue = args_count;
    [[cst::proof]] {
      thm shape = assume_rule(
          `e == CMCallE (callee_:int)
             (args_:(cm_expr)list) (ty_:cm_type)`);
      cm_finish_expr_count_cells(shape, `0i`,
          `cm_args_code_count_of
             (cm_args_code_counts (p:cm_program)
               (fid__pre:int) (args_:(cm_expr)list))`);
      thm args_view = inst_rule(TERM_PAIR_LIST(
          (term_pair){`zargs:int`, `p:int`},
          (term_pair){`args_:(cm_expr)list`,
                      `args:(cm_expr)list`}),
          get_cm_arg_list_rep_def());
      apply_hconv_st(eq2ent(args_view));
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
      apply_hconv_st(payload_fold);
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
      cm_open_expr_count_facts(shape);
      cm_open_single_child_count_payload(shape);
    }
    int child_lvalue;
    int child_rvalue;
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`structs`, `structs:(cm_struct_d)list`)]]
    [[cst::where(`globals`, `globals:(cm_global_d)list`)]]
    [[cst::where(`locals`, `locals:(cm_slot_d)list`)]]
    [[cst::where(`zs`, `(zs:int)`)]]
    [[cst::where(`zg`, `(zg:int)`)]]
    [[cst::where(`zl`, `(zl:int)`)]]
    cm_expr_counts(program, fid, fn, expr->a,
                   &child_lvalue, &child_rvalue);
    [[cst::proof]] {
      term child_count =
          `cm_rcount_of
             (cm_expr_code_counts (p:cm_program)
               (fid__pre:int) (arg_:cm_expr))`;
      term model_count =
          `cm_rcount_of
             (cm_expr_code_counts (p:cm_program) (fid__pre:int)
               (CMPutcE (arg_:cm_expr) (ty_:cm_type)))`;
      term concrete_count =
          `cm_rcount_of
             (cm_expr_code_counts (p:cm_program)
               (fid__pre:int) (arg_:cm_expr)) + 2i`;
      cm_prepare_single_child_add(
          model_count, concrete_count,
          assume_rule(
            `cm_rcount_of
               (cm_expr_code_counts (p:cm_program) (fid__pre:int)
                 (CMPutcE (arg_:cm_expr) (ty_:cm_type))) <=
             2147483647i`),
          child_count,
          from_state_bool(
            `cm_i32_code_count
               (cm_rcount_of
                 (cm_expr_code_counts (p:cm_program)
                   (fid__pre:int) (arg_:cm_expr)))`),
          `2i`, int_arith_rule(`0i <= 2i`),
          THM_LIST(get_cm_expr_code_counts_def(),
            get_cm_rcount_of_def()));
    }
    out_rvalue = child_rvalue + 2;
    [[cst::proof]] {
      thm shape = assume_rule(
          `e == CMPutcE (arg_:cm_expr) (ty_:cm_type)`);
      cm_finish_expr_count_cells(shape, `0i`,
          `cm_rcount_of
             (cm_expr_code_counts (p:cm_program)
               (fid__pre:int) (arg_:cm_expr)) + 2i`);
      cm_close_single_child_count_payload(shape);
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
      cm_open_expr_count_facts(shape);
      cm_open_single_child_count_payload(shape);
    }
    int child_lvalue;
    int child_rvalue;
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`structs`, `structs:(cm_struct_d)list`)]]
    [[cst::where(`globals`, `globals:(cm_global_d)list`)]]
    [[cst::where(`locals`, `locals:(cm_slot_d)list`)]]
    [[cst::where(`zs`, `(zs:int)`)]]
    [[cst::where(`zg`, `(zg:int)`)]]
    [[cst::where(`zl`, `(zl:int)`)]]
    cm_expr_counts(program, fid, fn, expr->a,
                   &child_lvalue, &child_rvalue);
    [[cst::proof]] {
      term child_count =
          `cm_rcount_of
             (cm_expr_code_counts (p:cm_program)
               (fid__pre:int) (arg_:cm_expr))`;
      term model_count =
          `cm_rcount_of
             (cm_expr_code_counts (p:cm_program) (fid__pre:int)
               (CMPutiE (arg_:cm_expr) (ty_:cm_type)))`;
      term concrete_count =
          `cm_rcount_of
             (cm_expr_code_counts (p:cm_program)
               (fid__pre:int) (arg_:cm_expr)) + 2i`;
      cm_prepare_single_child_add(
          model_count, concrete_count,
          assume_rule(
            `cm_rcount_of
               (cm_expr_code_counts (p:cm_program) (fid__pre:int)
                 (CMPutiE (arg_:cm_expr) (ty_:cm_type))) <=
             2147483647i`),
          child_count,
          from_state_bool(
            `cm_i32_code_count
               (cm_rcount_of
                 (cm_expr_code_counts (p:cm_program)
                   (fid__pre:int) (arg_:cm_expr)))`),
          `2i`, int_arith_rule(`0i <= 2i`),
          THM_LIST(get_cm_expr_code_counts_def(),
            get_cm_rcount_of_def()));
    }
    out_rvalue = child_rvalue + 2;
    [[cst::proof]] {
      thm shape = assume_rule(
          `e == CMPutiE (arg_:cm_expr) (ty_:cm_type)`);
      cm_finish_expr_count_cells(shape, `0i`,
          `cm_rcount_of
             (cm_expr_code_counts (p:cm_program)
               (fid__pre:int) (arg_:cm_expr)) + 2i`);
      cm_close_single_child_count_payload(shape);
    }
  } else {
    [[cst::proof]] {
      thm kind = mp_rule(int_arith_rule(
          `(0i <= cm_rep_expr_kind (e:cm_expr) &&
            cm_rep_expr_kind e <= 13i) ==>
           ~(cm_rep_expr_kind e == 0i) ==>
           ~(cm_rep_expr_kind e == 1i) ==>
           ~(cm_rep_expr_kind e == 2i) ==>
           ~(cm_rep_expr_kind e == 3i) ==>
           ~(cm_rep_expr_kind e == 4i) ==>
           ~(cm_rep_expr_kind e == 5i) ==>
           ~(cm_rep_expr_kind e == 6i) ==>
           ~(cm_rep_expr_kind e == 7i) ==>
           ~(cm_rep_expr_kind e == 8i) ==>
           ~(cm_rep_expr_kind e == 9i) ==>
           ~(cm_rep_expr_kind e == 10i) ==>
           ~(cm_rep_expr_kind e == 11i) ==>
           ~(cm_rep_expr_kind e == 12i) ==>
           cm_rep_expr_kind e == 13i`),
          spec_rule(`e:cm_expr`, get_cm_rep_expr_kind_bounds()));
      kind = mp_rule(kind,
          assume_rule(`~(cm_rep_expr_kind (e:cm_expr) == 0i)`));
      kind = mp_rule(kind,
          assume_rule(`~(cm_rep_expr_kind (e:cm_expr) == 1i)`));
      kind = mp_rule(kind,
          assume_rule(`~(cm_rep_expr_kind (e:cm_expr) == 2i)`));
      kind = mp_rule(kind,
          assume_rule(`~(cm_rep_expr_kind (e:cm_expr) == 3i)`));
      kind = mp_rule(kind,
          assume_rule(`~(cm_rep_expr_kind (e:cm_expr) == 4i)`));
      kind = mp_rule(kind,
          assume_rule(`~(cm_rep_expr_kind (e:cm_expr) == 5i)`));
      kind = mp_rule(kind,
          assume_rule(`~(cm_rep_expr_kind (e:cm_expr) == 6i)`));
      kind = mp_rule(kind,
          assume_rule(`~(cm_rep_expr_kind (e:cm_expr) == 7i)`));
      kind = mp_rule(kind,
          assume_rule(`~(cm_rep_expr_kind (e:cm_expr) == 8i)`));
      kind = mp_rule(kind,
          assume_rule(`~(cm_rep_expr_kind (e:cm_expr) == 9i)`));
      kind = mp_rule(kind,
          assume_rule(`~(cm_rep_expr_kind (e:cm_expr) == 10i)`));
      kind = mp_rule(kind,
          assume_rule(`~(cm_rep_expr_kind (e:cm_expr) == 11i)`));
      kind = mp_rule(kind,
          assume_rule(`~(cm_rep_expr_kind (e:cm_expr) == 12i)`));
      add_fact_st(kind);
      thm shape_ent = mp_rule(spec_rule(`e:cm_expr`,
          get_cm_expr_exit_shape_ent()),
          assume_rule(`cm_rep_expr_kind (e:cm_expr) == 13i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`arg_:cm_expr`, `ty_:cm_type`))));
      thm shape = assume_rule(
          `e == CMExitE (arg_:cm_expr) (ty_:cm_type)`);
      cm_open_expr_count_facts(shape);
      cm_open_single_child_count_payload(shape);
    }
    int child_lvalue;
    int child_rvalue;
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`structs`, `structs:(cm_struct_d)list`)]]
    [[cst::where(`globals`, `globals:(cm_global_d)list`)]]
    [[cst::where(`locals`, `locals:(cm_slot_d)list`)]]
    [[cst::where(`zs`, `(zs:int)`)]]
    [[cst::where(`zg`, `(zg:int)`)]]
    [[cst::where(`zl`, `(zl:int)`)]]
    cm_expr_counts(program, fid, fn, expr->a,
                   &child_lvalue, &child_rvalue);
    [[cst::proof]] {
      term child_count =
          `cm_rcount_of
             (cm_expr_code_counts (p:cm_program)
               (fid__pre:int) (arg_:cm_expr))`;
      term model_count =
          `cm_rcount_of
             (cm_expr_code_counts (p:cm_program) (fid__pre:int)
               (CMExitE (arg_:cm_expr) (ty_:cm_type)))`;
      term concrete_count =
          `cm_rcount_of
             (cm_expr_code_counts (p:cm_program)
               (fid__pre:int) (arg_:cm_expr)) + 7i`;
      cm_prepare_single_child_add(
          model_count, concrete_count,
          assume_rule(
            `cm_rcount_of
               (cm_expr_code_counts (p:cm_program) (fid__pre:int)
                 (CMExitE (arg_:cm_expr) (ty_:cm_type))) <=
             2147483647i`),
          child_count,
          from_state_bool(
            `cm_i32_code_count
               (cm_rcount_of
                 (cm_expr_code_counts (p:cm_program)
                   (fid__pre:int) (arg_:cm_expr)))`),
          `7i`, int_arith_rule(`0i <= 7i`),
          THM_LIST(get_cm_expr_code_counts_def(),
            get_cm_rcount_of_def()));
    }
    out_rvalue = child_rvalue + 7;
    [[cst::proof]] {
      thm shape = assume_rule(
          `e == CMExitE (arg_:cm_expr) (ty_:cm_type)`);
      cm_finish_expr_count_cells(shape, `0i`,
          `cm_rcount_of
             (cm_expr_code_counts (p:cm_program)
               (fid__pre:int) (arg_:cm_expr)) + 7i`);
      cm_close_single_child_count_payload(shape);
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

PROOF static thm cm_prove_rep_slot_type_at(void) {
  gnode root = gnode_new_with_ccl(
      `!(slots:(cm_slot_d)list) index.
         0i <= index ==>
         index < ilength slots ==>
         cm_rep_slot_type slots index ==
           cm_type_encode (cm_slot_ty (inth index slots))`);
  gnode_list cases = INDUCT_TAC(root, `slots:(cm_slot_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm upper = pure_rewrite_rule(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF")), assume_rule(
          `(index:int) < ilength ([]:(cm_slot_d)list)`));
    CONTR_TAC(leaf, mp_rule(mp_rule(int_arith_rule(
        `0i <= (index:int) ==> index < 0i ==> F`),
        assume_rule(`0i <= (index:int)`)), upper));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    gnode_list index_cases =
        BOOL_CASES_TAC(leaf, `(index:int) == 0i`, "Hindex");
    CONV_WITH_ASMP_TAC(index_cases[0], reduce_rewrite_conv, THM_LIST(
        get_cm_rep_slot_type_def(),
        get_theorem_by_name("INTH_DEF"),
        get_theorem_by_name("NUM_OF_INT_OF_NUM"),
        get_theorem_by_name("NTH_DEF")));
    thm nonnegative = assume_rule(`0i <= (index:int)`);
    thm nonzero = assume_rule(`~((index:int) == 0i)`);
    thm lower = mp_rule(mp_rule(int_arith_rule(
        `0i <= (index:int) ==> ~(index == 0i) ==> 1i <= index`),
        nonnegative), nonzero);
    thm length_step = pure_rewrite_rule(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF")), assume_rule(
          `(index:int) <
             ilength ((a0:cm_slot_d) :: (a1:(cm_slot_d)list))`));
    thm tail_bound = mp_rule(int_arith_rule(
        `(index:int) < 1i + ilength (a1:(cm_slot_d)list) ==>
         index - 1i < ilength a1`), length_step);
    thm tail_nonnegative = mp_rule(int_arith_rule(
        `1i <= (index:int) ==> 0i <= index - 1i`), lower);
    thm ih = mp_rule(mp_rule(spec_rule(
        `(index:int) - 1i`, assume_rule(
          `!index.
             0i <= index ==>
             index < ilength (a1:(cm_slot_d)list) ==>
             cm_rep_slot_type a1 index ==
               cm_type_encode (cm_slot_ty (inth index a1))`)),
        tail_nonnegative), tail_bound);
    thm lookup = mp_rule(ispecl_rule(TERM_LIST(
        `a0:cm_slot_d`, `a1:(cm_slot_d)list`, `index:int`),
        get_cm_rep_inth_cons_tail()), lower);
    gnode reduced = CONV_WITH_ASMP_TAC(
        index_cases[1], reduce_rewrite_conv, THM_LIST(
          get_cm_rep_slot_type_def(), lookup));
    ACCEPT_TAC(reduced, ih);
  }
  return gnode_prove(root);
}
PROOF thm cm_rep_slot_type_at = cm_prove_rep_slot_type_at();

PROOF thm cm_rep_slot_type_model(
    const term slots, const term index) {
  return specl_rule(TERM_LIST(slots, index), cm_rep_slot_type_at);
}

PROOF static thm cm_first_stmt_count_node_fact(const thm theorem) {
  if (is_conj(concl(theorem))) {
    return cm_first_stmt_count_node_fact(conjunct1_rule(theorem));
  }
  return theorem;
}

PROOF static void cm_open_stmt_count_facts(const thm shape) {
  thm source = from_state_bool(
      `cm_stmt_counts_representable
        (p:cm_program) (fid__pre:int) (s:cm_stmt)`);
  thm shallow = conv_rule(rewrite_conv(THM_LIST(
      shape, get_cm_stmt_counts_representable_def())), source);
  thm node = cm_first_stmt_count_node_fact(shallow);
  thm generic_node = conv_rule(
      rewrite_conv(THM_LIST(sym_rule(shape))), node);
  cm_add_count_facts(generic_node);
  thm representable = conv_rule(rewrite_conv(THM_LIST(
      shape, get_cm_stmt_counts_representable_def())), source);
  cm_add_count_facts(representable);
  thm well_formed = conv_rule(rewrite_conv(THM_LIST(
      shape, get_cm_stmt_wf_def())),
      from_state_bool(
        `cm_stmt_wf (p:cm_program) (f:cm_function_d)
          (loop_:bool) (s:cm_stmt)`));
  cm_add_count_facts(well_formed);
}

PROOF static void cm_prepare_stmt_count_value(
    const thm shape, const term concrete_count,
    const thm_list extra_rules) {
  term model_count =
      `cm_stmt_code_count
        (p:cm_program) (fid__pre:int) (s:cm_stmt)`;
  thm_list rules = THM_LIST(
      shape, get_cm_stmt_code_count_def(),
      get_cm_rvalue_code_count_def(),
      int_arith_rule(
        `!(x:int) (y:int) (z:int).
           x + (y + z) == (x + y) + z`));
  for (size_t i = 0; i < vector_size(extra_rules); ++i) {
    vector_add(&rules, extra_rules[i]);
  }
  thm concrete_i32 = conv_rule(rewrite_conv(rules),
      from_state_bool(
        `cm_i32_code_count
          (cm_stmt_code_count
            (p:cm_program) (fid__pre:int) (s:cm_stmt))`));
  cm_add_count_facts(concrete_i32);
}

PROOF static void cm_finish_stmt_count_value(
    const thm shape, const term concrete_count,
    const thm_list extra_rules) {
  term model_count =
      `cm_stmt_code_count
        (p:cm_program) (fid__pre:int) (s:cm_stmt)`;
  thm_list rules = THM_LIST(
      shape, get_cm_stmt_code_count_def(),
      get_cm_rvalue_code_count_def(),
      int_arith_rule(
        `!(x:int) (y:int) (z:int).
           x + (y + z) == (x + y) + z`));
  for (size_t i = 0; i < vector_size(extra_rules); ++i) {
    vector_add(&rules, extra_rules[i]);
  }
  thm model = by_rewrite(mk_eq(model_count, concrete_count), rules);
  add_fact_st(sym_rule(model));
  cst_set_symbolic_state(retarget_cell_st(
      cst_get_symbolic_state(), `result__addr:addr`,
      concrete_count, model_count));
}

PROOF static void cm_retarget_call_result(
    const term cell, const thm result) {
  struct dest_eq_results sides = dest_eq(concl(result));
  add_fact_st(result);
  cst_set_symbolic_state(retarget_cell_st(
      cst_get_symbolic_state(), cell, sides.tm1, sides.tm2));
}

PROOF void cm_commit_arith_fact(const char *chain) {
  cst_set_symbolic_state(add_arith_fact_st(
      cst_get_symbolic_state(), chain));
}

PROOF static size_t cm_term_occurrences(
    const term value, const term_list values) {
  size_t count = 0;
  for (size_t i = 0; i < vector_size(values); ++i) {
    if (alpha_compare(value, values[i]) == 0) ++count;
  }
  return count;
}

PROOF static void cm_keep_only_facts(const term_list kept) {
  term symbolic = cst_get_symbolic_state();
  strip_sl_exists_results opened = strip_sl_exists(symbolic);
  term_list conjuncts = strip_sl_sep(opened.hp);
  for (size_t i = 0; i < vector_size(conjuncts); ++i) {
    if (!is_sl_fact(conjuncts[i])) continue;
    term proposition = dest_sl_fact(conjuncts[i]);
    bool seen = false;
    for (size_t j = 0; j < i; ++j) {
      if (is_sl_fact(conjuncts[j]) &&
          alpha_compare(proposition,
            dest_sl_fact(conjuncts[j])) == 0) {
        seen = true;
        break;
      }
    }
    if (seen) continue;
    size_t available = 0;
    for (size_t j = i; j < vector_size(conjuncts); ++j) {
      if (is_sl_fact(conjuncts[j]) &&
          alpha_compare(proposition,
            dest_sl_fact(conjuncts[j])) == 0) {
        ++available;
      }
    }
    size_t wanted = cm_term_occurrences(proposition, kept);
    while (available > wanted) {
      remove_fact_st(proposition);
      --available;
    }
  }
}

PROOF static void cm_open_stmt_expr_count_payload(const thm shape) {
  thm payload_view = by_rewrite(
      `cm_stmt_payload (s:cm_stmt)
         (ze:int) (za:int) (zb:int) -|-
       fact(~(ze == 0i) && za == 0i && zb == 0i) **
       cm_expr_rep ze (expr_:cm_expr)`,
      THM_LIST(shape, get_cm_stmt_payload_def()));
  cst_set_symbolic_state(local_apply(
      cst_get_symbolic_state(), eq2ent(payload_view)));
}

PROOF static void cm_close_stmt_expr_count_payload(const thm shape) {
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
      trans_slrule(payload_intro, eq2ent(sym_rule(payload_view)))));
}

PROOF static void cm_open_stmt_seq_count_payload(const thm shape) {
  thm payload_view = by_rewrite(
      `cm_stmt_payload (s:cm_stmt)
         (ze:int) (za:int) (zb:int) -|-
       fact(ze == 0i) **
       cm_stmt_node za (first_:cm_stmt)
         (cm_stmt_payload first_) **
       cm_stmt_node zb (second_:cm_stmt)
         (cm_stmt_payload second_)`,
      THM_LIST(shape, get_cm_stmt_payload_def()));
  cst_set_symbolic_state(local_apply(
      cst_get_symbolic_state(), eq2ent(payload_view)));
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

PROOF static void cm_close_stmt_seq_count_payload(const thm shape) {
  thm first_view = inst_rule(TERM_PAIR_LIST(
      (term_pair){`za:int`, `p:int`},
      (term_pair){`first_:cm_stmt`, `s:cm_stmt`}),
      get_cm_stmt_rep_def());
  thm second_view = inst_rule(TERM_PAIR_LIST(
      (term_pair){`zb:int`, `p:int`},
      (term_pair){`second_:cm_stmt`, `s:cm_stmt`}),
      get_cm_stmt_rep_def());
  cst_set_symbolic_state(local_apply(
      cst_get_symbolic_state(), eq2ent(first_view)));
  cst_set_symbolic_state(local_apply(
      cst_get_symbolic_state(), eq2ent(second_view)));
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

PROOF static void cm_open_stmt_block_count_payload(const thm shape) {
  term body = dest_comb(dest_eq(concl(shape)).tm2).tm2;
  term payload_subject = subst(TERM_PAIR_LIST(
      (term_pair){body, `first_:cm_stmt`}),
      `cm_stmt_payload (s:cm_stmt)
         (ze:int) (za:int) (zb:int) -|-
       fact(ze == 0i && ~(za == 0i) && zb == 0i) **
       cm_stmt_node za (first_:cm_stmt)
         (cm_stmt_payload first_)`);
  thm payload_view = by_rewrite(payload_subject,
      THM_LIST(shape, get_cm_stmt_payload_def()));
  cst_set_symbolic_state(local_apply(
      cst_get_symbolic_state(), eq2ent(payload_view)));
  thm body_view = inst_rule(TERM_PAIR_LIST(
      (term_pair){`za:int`, `p:int`},
      (term_pair){body, `s:cm_stmt`}),
      get_cm_stmt_rep_def());
  cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
      eq2ent(sym_rule(body_view))));
}

PROOF static void cm_close_stmt_block_count_payload(const thm shape) {
  term body = dest_comb(dest_eq(concl(shape)).tm2).tm2;
  thm body_view = inst_rule(TERM_PAIR_LIST(
      (term_pair){`za:int`, `p:int`},
      (term_pair){body, `s:cm_stmt`}),
      get_cm_stmt_rep_def());
  cst_set_symbolic_state(local_apply(
      cst_get_symbolic_state(), eq2ent(body_view)));
  term payload_subject = subst(TERM_PAIR_LIST(
      (term_pair){body, `first_:cm_stmt`}),
      `cm_stmt_payload (s:cm_stmt)
         (ze:int) (za:int) (zb:int) -|-
       fact(ze == 0i && ~(za == 0i) && zb == 0i) **
       cm_stmt_node za (first_:cm_stmt)
         (cm_stmt_payload first_)`);
  thm payload_view = by_rewrite(payload_subject,
      THM_LIST(shape, get_cm_stmt_payload_def()));
  thm payload_facts = conj_rule(
      assume_rule(`(ze:int) == 0i`),
      conj_rule(assume_rule(`~((za:int) == 0i)`),
        assume_rule(`(zb:int) == 0i`)));
  term body_rep = subst(TERM_PAIR_LIST(
      (term_pair){body, `first_:cm_stmt`}),
      `cm_stmt_node (za:int) (first_:cm_stmt)
         (cm_stmt_payload first_)`);
  thm payload_intro = frame_right_slrule(
      add_fact_hconv(payload_facts), body_rep);
  cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
      trans_slrule(payload_intro, eq2ent(sym_rule(payload_view)))));
}

PROOF static void cm_open_stmt_if_count_payload(const thm shape) {
  dest_comb_results outer = dest_comb(dest_eq(concl(shape)).tm2);
  dest_comb_results middle = dest_comb(outer.tm1);
  term guard = dest_comb(middle.tm1).tm2;
  term yes_branch = middle.tm2;
  term no_branch = outer.tm2;
  term payload_subject = subst(TERM_PAIR_LIST(
      (term_pair){guard, `expr_:cm_expr`},
      (term_pair){yes_branch, `first_:cm_stmt`},
      (term_pair){no_branch, `second_:cm_stmt`}),
      `cm_stmt_payload (s:cm_stmt)
         (ze:int) (za:int) (zb:int) -|-
       cm_expr_rep ze (expr_:cm_expr) **
       cm_stmt_node za (first_:cm_stmt)
         (cm_stmt_payload first_) **
       cm_stmt_node zb (second_:cm_stmt)
         (cm_stmt_payload second_)`);
  thm payload_view = by_rewrite(payload_subject,
      THM_LIST(shape, get_cm_stmt_payload_def()));
  cst_set_symbolic_state(local_apply(
      cst_get_symbolic_state(), eq2ent(payload_view)));
  thm yes_view = inst_rule(TERM_PAIR_LIST(
      (term_pair){`za:int`, `p:int`},
      (term_pair){yes_branch, `s:cm_stmt`}),
      get_cm_stmt_rep_def());
  thm no_view = inst_rule(TERM_PAIR_LIST(
      (term_pair){`zb:int`, `p:int`},
      (term_pair){no_branch, `s:cm_stmt`}),
      get_cm_stmt_rep_def());
  cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
      eq2ent(sym_rule(yes_view))));
  cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
      eq2ent(sym_rule(no_view))));
}

PROOF static void cm_close_stmt_if_count_payload(const thm shape) {
  dest_comb_results outer = dest_comb(dest_eq(concl(shape)).tm2);
  dest_comb_results middle = dest_comb(outer.tm1);
  term guard = dest_comb(middle.tm1).tm2;
  term yes_branch = middle.tm2;
  term no_branch = outer.tm2;
  thm yes_view = inst_rule(TERM_PAIR_LIST(
      (term_pair){`za:int`, `p:int`},
      (term_pair){yes_branch, `s:cm_stmt`}),
      get_cm_stmt_rep_def());
  thm no_view = inst_rule(TERM_PAIR_LIST(
      (term_pair){`zb:int`, `p:int`},
      (term_pair){no_branch, `s:cm_stmt`}),
      get_cm_stmt_rep_def());
  cst_set_symbolic_state(local_apply(
      cst_get_symbolic_state(), eq2ent(yes_view)));
  cst_set_symbolic_state(local_apply(
      cst_get_symbolic_state(), eq2ent(no_view)));
  term payload_subject = subst(TERM_PAIR_LIST(
      (term_pair){guard, `expr_:cm_expr`},
      (term_pair){yes_branch, `first_:cm_stmt`},
      (term_pair){no_branch, `second_:cm_stmt`}),
      `cm_stmt_payload (s:cm_stmt)
         (ze:int) (za:int) (zb:int) -|-
       cm_expr_rep ze (expr_:cm_expr) **
       cm_stmt_node za (first_:cm_stmt)
         (cm_stmt_payload first_) **
       cm_stmt_node zb (second_:cm_stmt)
         (cm_stmt_payload second_)`);
  thm payload_view = by_rewrite(payload_subject,
      THM_LIST(shape, get_cm_stmt_payload_def()));
  cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
      eq2ent(sym_rule(payload_view))));
}

PROOF static void cm_open_stmt_while_count_payload(const thm shape) {
  dest_comb_results outer = dest_comb(dest_eq(concl(shape)).tm2);
  term guard_term = dest_comb(outer.tm1).tm2;
  term body_term = outer.tm2;
  term payload_subject = subst(TERM_PAIR_LIST(
      (term_pair){guard_term, `expr_:cm_expr`},
      (term_pair){body_term, `first_:cm_stmt`}),
      `cm_stmt_payload (s:cm_stmt)
         (ze:int) (za:int) (zb:int) -|-
       fact(~(ze == 0i) && ~(za == 0i) && zb == 0i) **
       cm_expr_rep ze (expr_:cm_expr) **
       cm_stmt_node za (first_:cm_stmt)
         (cm_stmt_payload first_)`);
  thm payload_view = by_rewrite(payload_subject,
      THM_LIST(shape, get_cm_stmt_payload_def()));
  cst_set_symbolic_state(local_apply(
      cst_get_symbolic_state(), eq2ent(payload_view)));
  thm body_view = inst_rule(TERM_PAIR_LIST(
      (term_pair){`za:int`, `p:int`},
      (term_pair){body_term, `s:cm_stmt`}),
      get_cm_stmt_rep_def());
  cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
      eq2ent(sym_rule(body_view))));
}

PROOF static void cm_close_stmt_while_count_payload(const thm shape) {
  dest_comb_results outer = dest_comb(dest_eq(concl(shape)).tm2);
  term guard_term = dest_comb(outer.tm1).tm2;
  term body_term = outer.tm2;
  thm body_view = inst_rule(TERM_PAIR_LIST(
      (term_pair){`za:int`, `p:int`},
      (term_pair){body_term, `s:cm_stmt`}),
      get_cm_stmt_rep_def());
  cst_set_symbolic_state(local_apply(
      cst_get_symbolic_state(), eq2ent(body_view)));
  term payload_subject = subst(TERM_PAIR_LIST(
      (term_pair){guard_term, `expr_:cm_expr`},
      (term_pair){body_term, `first_:cm_stmt`}),
      `cm_stmt_payload (s:cm_stmt)
         (ze:int) (za:int) (zb:int) -|-
       fact(~(ze == 0i) && ~(za == 0i) && zb == 0i) **
       cm_expr_rep ze (expr_:cm_expr) **
       cm_stmt_node za (first_:cm_stmt)
         (cm_stmt_payload first_)`);
  thm payload_view = by_rewrite(payload_subject,
      THM_LIST(shape, get_cm_stmt_payload_def()));
  thm payload_facts = conj_rule(
      assume_rule(`~((ze:int) == 0i)`),
      conj_rule(assume_rule(`~((za:int) == 0i)`),
        assume_rule(`(zb:int) == 0i`)));
  term payload_frame = subst(TERM_PAIR_LIST(
      (term_pair){guard_term, `expr_:cm_expr`},
      (term_pair){body_term, `first_:cm_stmt`}),
      `cm_expr_rep (ze:int) (expr_:cm_expr) **
       cm_stmt_node (za:int) (first_:cm_stmt)
         (cm_stmt_payload first_)`);
  thm payload_intro = frame_right_slrule(
      add_fact_hconv(payload_facts), payload_frame);
  cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
      trans_slrule(payload_intro, eq2ent(sym_rule(payload_view)))));
}

PROOF void cm_open_stmt_case_st(const thm shape, int kind) {
  cm_open_stmt_count_facts(shape);
  if (kind == 1 || kind == 3 || kind == 10) {
    cm_open_stmt_expr_count_payload(shape);
  } else if (kind == 4) {
    cm_open_stmt_seq_count_payload(shape);
  } else if (kind == 5) {
    cm_open_stmt_block_count_payload(shape);
  } else if (kind == 6) {
    cm_open_stmt_if_count_payload(shape);
  } else if (kind == 7) {
    cm_open_stmt_while_count_payload(shape);
  }
}

PROOF void cm_close_stmt_case_st(const thm shape, int kind) {
  if (kind == 1 || kind == 3 || kind == 10) {
    cm_close_stmt_expr_count_payload(shape);
  } else if (kind == 4) {
    cm_close_stmt_seq_count_payload(shape);
  } else if (kind == 5) {
    cm_close_stmt_block_count_payload(shape);
  } else if (kind == 6) {
    cm_close_stmt_if_count_payload(shape);
  } else if (kind == 7) {
    cm_close_stmt_while_count_payload(shape);
  }
}

int cmc_stmt_code_count(struct cm_program *program, int fid,
                               struct cm_function *fn,
                               struct cm_stmt *stmt)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `s:cm_stmt`,
                 `loop_:bool`, `structs:(cm_struct_d)list`,
                 `globals:(cm_global_d)list`,
                 `locals:(cm_slot_d)list`,
                 `zs:int`, `zg:int`, `zl:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(structs == cm_program_structs p) **
       fact(globals == cm_program_globals p) **
       fact(locals == cm_function_locals f) **
       fact(cm_stmt_wf p f loop_ s <=> true) **
       fact(cm_stmt_counts_representable p fid s <=> true) **
       fact(cm_rep_structs_safe structs <=> true) **
       data_at (field_addr program Tcm_program Fstructs) Tptr zs **
       cm_struct_list_rep zs structs **
       data_at (field_addr program Tcm_program Fglobals) Tptr zg **
       cm_global_list_rep zg globals **
       data_at (field_addr fn Tcm_function Fret_ty) Tint
         (cm_type_encode (cm_function_ret f)) **
       data_at (field_addr fn Tcm_function Flocals) Tptr zl **
       cm_slot_list_rep zl locals **
       cm_stmt_rep stmt s`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(structs == cm_program_structs p) **
       fact(globals == cm_program_globals p) **
       fact(locals == cm_function_locals f) **
       fact(cm_stmt_wf p f loop_ s <=> true) **
       fact(cm_stmt_counts_representable p fid s <=> true) **
       fact(cm_rep_structs_safe structs <=> true) **
       fact(cm_i32_code_count (cm_stmt_code_count p fid s) <=> true) **
       data_at (field_addr program Tcm_program Fstructs) Tptr zs **
       cm_struct_list_rep zs structs **
       data_at (field_addr program Tcm_program Fglobals) Tptr zg **
       cm_global_list_rep zg globals **
       data_at (field_addr fn Tcm_function Fret_ty) Tint
         (cm_type_encode (cm_function_ret f)) **
       data_at (field_addr fn Tcm_function Flocals) Tptr zl **
       cm_slot_list_rep zl locals **
       cm_stmt_rep stmt s **
       fact((__return:int) == cm_stmt_code_count p fid s)`)]]
{
  [[cst::proof]] {
    apply_hconv_st(specl_rule(TERM_LIST(
        `stmt__pre:int`, `s:cm_stmt`), get_cm_stmt_open()));
  }
  int result = 0;
  if (stmt->kind == CMC_STMT_SKIP) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`s:cm_stmt`,
          get_cm_stmt_skip_shape_ent()),
          assume_rule(`cm_rep_stmt_kind (s:cm_stmt) == 0i`));
      cst_set_symbolic_state(local_apply(
          cst_get_symbolic_state(), shape_ent));
      thm shape = assume_rule(`s == CMSkipS`);
      cm_open_stmt_count_facts(shape);
      cm_finish_stmt_count_value(shape, `0i`, THM_LIST());
    }
  } else if (stmt->kind == CMC_STMT_DECL) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`s:cm_stmt`,
          get_cm_stmt_decl_shape_ent()),
          assume_rule(`cm_rep_stmt_kind (s:cm_stmt) == 2i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent, TERM_LIST(`slot_:int`))));
      thm shape = assume_rule(`s == CMDeclS (slot_:int)`);
      cm_open_stmt_count_facts(shape);
      cm_finish_stmt_count_value(shape, `0i`, THM_LIST());
    }
  } else if (stmt->kind == CMC_STMT_EXPR) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`s:cm_stmt`,
          get_cm_stmt_expr_shape_ent()),
          assume_rule(`cm_rep_stmt_kind (s:cm_stmt) == 1i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent, TERM_LIST(`expr_:cm_expr`))));
      thm shape = assume_rule(`s == CMExprS (expr_:cm_expr)`);
      cm_open_stmt_count_facts(shape);
      cm_open_stmt_expr_count_payload(shape);
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`structs`, `structs:(cm_struct_d)list`)]]
    [[cst::where(`globals`, `globals:(cm_global_d)list`)]]
    [[cst::where(`locals`, `locals:(cm_slot_d)list`)]]
    [[cst::where(`zs`, `(zs:int)`)]]
    [[cst::where(`zg`, `(zg:int)`)]]
    [[cst::where(`zl`, `(zl:int)`)]]
    int expr_count =
        cm_expr_rvalue_count(program, fid, fn, stmt->expr);
    [[cst::proof]] {
      cm_retarget_call_result(`expr_count__addr:addr`,
          assume_rule(
            `(retval:int) ==
             cm_rcount_of
               (cm_expr_code_counts (p:cm_program)
                 (fid__pre:int) (expr_:cm_expr))`));
      thm shape = assume_rule(`s == CMExprS (expr_:cm_expr)`);
      cm_prepare_stmt_count_value(shape,
          `cm_rcount_of
             (cm_expr_code_counts (p:cm_program)
               (fid__pre:int) (expr_:cm_expr)) + 1i`,
          THM_LIST());
    }
    result = expr_count + 1;
    [[cst::proof]] {
      thm shape = assume_rule(`s == CMExprS (expr_:cm_expr)`);
      cm_finish_stmt_count_value(shape,
          `cm_rcount_of
             (cm_expr_code_counts (p:cm_program)
               (fid__pre:int) (expr_:cm_expr)) + 1i`,
          THM_LIST());
      cm_close_stmt_expr_count_payload(shape);
    }
  } else if (stmt->kind == CMC_STMT_INIT) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`s:cm_stmt`,
          get_cm_stmt_init_shape_ent()),
          assume_rule(`cm_rep_stmt_kind (s:cm_stmt) == 3i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`slot_:int`, `expr_:cm_expr`))));
      thm shape = assume_rule(
          `s == CMInitS (slot_:int) (expr_:cm_expr)`);
      cm_open_stmt_count_facts(shape);
      thm well_formed = conv_rule(rewrite_conv(THM_LIST(
          shape, get_cm_stmt_wf_def())),
          from_state_bool(
            `cm_stmt_wf (p:cm_program) (f:cm_function_d)
              (loop_:bool) (s:cm_stmt)`));
      add_fact_st(conjunct1_rule(well_formed));
      thm function_bound =
          conjunct1_rule(conjunct2_rule(well_formed));
      add_fact_st(function_bound);
      thm locals_model = assume_rule(
          `locals == cm_function_locals (f:cm_function_d)`);
      thm local_bound = conv_rule(
          rewrite_conv(THM_LIST(sym_rule(locals_model))),
          function_bound);
      add_fact_st(local_bound);
      thm fn_model = assume_rule(
          `f == inth (fid__pre:int)
            (cm_program_functions (p:cm_program))`);
      thm local_type_wf = conv_rule(rewrite_conv(THM_LIST(
          sym_rule(fn_model), sym_rule(locals_model))),
          from_state_bool(
            `cm_type_code_wf
              (cm_slot_ty
                (inth (slot_:int)
                  (cm_function_locals
                    (inth (fid__pre:int)
                      (cm_program_functions (p:cm_program))))))`));
      add_fact_st(eqt_intro_rule(local_type_wf));
      thm slot_model = by_rewrite(
          `cm_rep_stmt_slot (s:cm_stmt) == (slot_:int)`,
          THM_LIST(shape, get_cm_rep_stmt_slot_def()));
      thm concrete_slot_lower = conv_rule(
          rewrite_conv(THM_LIST(sym_rule(slot_model))),
          assume_rule(`0i <= (slot_:int)`));
      add_fact_st(concrete_slot_lower);
      cm_open_stmt_expr_count_payload(shape);
    }
    [[cst::where(`slots`, `locals:(cm_slot_d)list`)]]
    int ty_code = cmc_slot_type_at(fn->locals, stmt->slot);
    [[cst::proof]] {
      thm lookup = mp_rule(mp_rule(specl_rule(TERM_LIST(
          `locals:(cm_slot_d)list`, `slot_:int`),
          cm_rep_slot_type_at),
          assume_rule(`0i <= (slot_:int)`)),
          assume_rule(
            `(slot_:int) < ilength (locals:(cm_slot_d)list)`));
      thm shape = assume_rule(
          `s == CMInitS (slot_:int) (expr_:cm_expr)`);
      thm returned = conv_rule(rewrite_conv(THM_LIST(
          shape, get_cm_rep_stmt_slot_def())), assume_rule(
          `(retval:int) ==
           cm_rep_slot_type (locals:(cm_slot_d)list)
             (cm_rep_stmt_slot (s:cm_stmt))`));
      thm encoded = trans_rule(returned, lookup);
      cm_retarget_call_result(`ty_code__addr:addr`, encoded);
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`structs`, `structs:(cm_struct_d)list`)]]
    [[cst::where(`globals`, `globals:(cm_global_d)list`)]]
    [[cst::where(`locals`, `locals:(cm_slot_d)list`)]]
    [[cst::where(`zs`, `(zs:int)`)]]
    [[cst::where(`zg`, `(zg:int)`)]]
    [[cst::where(`zl`, `(zl:int)`)]]
    int expr_count =
        cm_expr_rvalue_count(program, fid, fn, stmt->expr);
    [[cst::proof]] {
      cm_retarget_call_result(`expr_count__addr:addr`,
          assume_rule(
            `(retval_1:int) ==
             cm_rcount_of
               (cm_expr_code_counts (p:cm_program)
                 (fid__pre:int) (expr_:cm_expr))`));
    }
    int normalize = cm_normalize_count(ty_code);
    [[cst::proof]] {
      term slot_ty =
          `cm_slot_ty
            (inth (slot_:int) (locals:(cm_slot_d)list))`;
      thm bridge = mp_rule(spec_rule(slot_ty,
          cm_char_normalize_bridge),
          from_state_bool(
            `cm_type_code_wf
              (cm_slot_ty
                (inth (slot_:int) (locals:(cm_slot_d)list)))`));
      thm model = trans_rule(assume_rule(
          `(retval_1:int) ==
           cm_normalize_code_value
             (cm_type_encode
               (cm_slot_ty
                 (inth (slot_:int) (locals:(cm_slot_d)list))))`),
          bridge);
      cm_retarget_call_result(`normalize__addr:addr`, model);
      thm shape = assume_rule(
          `s == CMInitS (slot_:int) (expr_:cm_expr)`);
      thm fn_model = assume_rule(
          `f == inth (fid__pre:int)
            (cm_program_functions (p:cm_program))`);
      thm locals_model = assume_rule(
          `locals == cm_function_locals (f:cm_function_d)`);
      cm_prepare_stmt_count_value(shape,
          `(cm_rcount_of
              (cm_expr_code_counts (p:cm_program)
                (fid__pre:int) (expr_:cm_expr)) +
            cm_char_normalize_count
              (cm_slot_ty
                (inth (slot_:int) (locals:(cm_slot_d)list)))) + 5i`,
          THM_LIST(sym_rule(fn_model), sym_rule(locals_model)));
    }
    result = expr_count + normalize + 5;
    [[cst::proof]] {
      thm shape = assume_rule(
          `s == CMInitS (slot_:int) (expr_:cm_expr)`);
      thm fn_model = assume_rule(
          `f == inth (fid__pre:int)
            (cm_program_functions (p:cm_program))`);
      thm locals_model = assume_rule(
          `locals == cm_function_locals (f:cm_function_d)`);
      cm_finish_stmt_count_value(shape,
          `(cm_rcount_of
              (cm_expr_code_counts (p:cm_program)
                (fid__pre:int) (expr_:cm_expr)) +
            cm_char_normalize_count
              (cm_slot_ty
                (inth (slot_:int) (locals:(cm_slot_d)list)))) + 5i`,
          THM_LIST(sym_rule(fn_model), sym_rule(locals_model)));
      cm_close_stmt_expr_count_payload(shape);
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
      cm_open_stmt_count_facts(shape);
      cm_open_stmt_seq_count_payload(shape);
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`loop_`, `(loop_:bool)`)]]
    [[cst::where(`structs`, `structs:(cm_struct_d)list`)]]
    [[cst::where(`globals`, `globals:(cm_global_d)list`)]]
    [[cst::where(`locals`, `locals:(cm_slot_d)list`)]]
    [[cst::where(`zs`, `(zs:int)`)]]
    [[cst::where(`zg`, `(zg:int)`)]]
    [[cst::where(`zl`, `(zl:int)`)]]
    int first_count =
        cmc_stmt_code_count(program, fid, fn, stmt->a);
    [[cst::proof]] {
      cm_retarget_call_result(`first_count__addr:addr`,
          assume_rule(
            `(retval:int) ==
             cm_stmt_code_count (p:cm_program) (fid__pre:int)
               (first_:cm_stmt)`));
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`loop_`, `(loop_:bool)`)]]
    [[cst::where(`structs`, `structs:(cm_struct_d)list`)]]
    [[cst::where(`globals`, `globals:(cm_global_d)list`)]]
    [[cst::where(`locals`, `locals:(cm_slot_d)list`)]]
    [[cst::where(`zs`, `(zs:int)`)]]
    [[cst::where(`zg`, `(zg:int)`)]]
    [[cst::where(`zl`, `(zl:int)`)]]
    int second_count =
        cmc_stmt_code_count(program, fid, fn, stmt->b);
    [[cst::proof]] {
      cm_retarget_call_result(`second_count__addr:addr`,
          assume_rule(
            `(retval_1:int) ==
             cm_stmt_code_count (p:cm_program) (fid__pre:int)
               (second_:cm_stmt)`));
      thm shape = assume_rule(
          `s == CMSeqS (first_:cm_stmt) (second_:cm_stmt)`);
      cm_prepare_stmt_count_value(shape,
          `cm_stmt_code_count (p:cm_program) (fid__pre:int)
               (first_:cm_stmt) +
           cm_stmt_code_count p fid__pre (second_:cm_stmt)`,
          THM_LIST());
    }
    result = first_count + second_count;
    [[cst::proof]] {
      thm shape = assume_rule(
          `s == CMSeqS (first_:cm_stmt) (second_:cm_stmt)`);
      cm_finish_stmt_count_value(shape,
          `cm_stmt_code_count (p:cm_program) (fid__pre:int)
               (first_:cm_stmt) +
           cm_stmt_code_count p fid__pre (second_:cm_stmt)`,
          THM_LIST());
      cm_close_stmt_seq_count_payload(shape);
    }
  } else if (stmt->kind == CMC_STMT_BLOCK) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`s:cm_stmt`,
          get_cm_stmt_block_shape_ent()),
          assume_rule(`cm_rep_stmt_kind (s:cm_stmt) == 5i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent, TERM_LIST(`first_:cm_stmt`))));
      thm shape = assume_rule(`s == CMBlockS (first_:cm_stmt)`);
      cm_open_stmt_count_facts(shape);
      cm_open_stmt_block_count_payload(shape);
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`loop_`, `(loop_:bool)`)]]
    [[cst::where(`structs`, `structs:(cm_struct_d)list`)]]
    [[cst::where(`globals`, `globals:(cm_global_d)list`)]]
    [[cst::where(`locals`, `locals:(cm_slot_d)list`)]]
    [[cst::where(`zs`, `(zs:int)`)]]
    [[cst::where(`zg`, `(zg:int)`)]]
    [[cst::where(`zl`, `(zl:int)`)]]
    int first_count =
        cmc_stmt_code_count(program, fid, fn, stmt->a);
    [[cst::proof]] {
      cm_retarget_call_result(`first_count__addr:addr`,
          assume_rule(
            `(retval:int) ==
             cm_stmt_code_count (p:cm_program) (fid__pre:int)
               (first_:cm_stmt)`));
    }
    result = first_count;
    [[cst::proof]] {
      thm shape = assume_rule(`s == CMBlockS (first_:cm_stmt)`);
      cm_finish_stmt_count_value(shape,
          `cm_stmt_code_count (p:cm_program) (fid__pre:int)
            (first_:cm_stmt)`, THM_LIST());
      cm_close_stmt_block_count_payload(shape);
    }
  } else if (stmt->kind == CMC_STMT_IF) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`s:cm_stmt`,
          get_cm_stmt_if_shape_ent()),
          assume_rule(`cm_rep_stmt_kind (s:cm_stmt) == 6i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`expr_:cm_expr`, `first_:cm_stmt`,
              `second_:cm_stmt`))));
      thm shape = assume_rule(
          `s == CMIfS (expr_:cm_expr) (first_:cm_stmt)
             (second_:cm_stmt)`);
      cm_open_stmt_count_facts(shape);
      cm_open_stmt_if_count_payload(shape);
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`structs`, `structs:(cm_struct_d)list`)]]
    [[cst::where(`globals`, `globals:(cm_global_d)list`)]]
    [[cst::where(`locals`, `locals:(cm_slot_d)list`)]]
    [[cst::where(`zs`, `(zs:int)`)]]
    [[cst::where(`zg`, `(zg:int)`)]]
    [[cst::where(`zl`, `(zl:int)`)]]
    int expr_count =
        cm_expr_rvalue_count(program, fid, fn, stmt->expr);
    [[cst::proof]] {
      cm_retarget_call_result(`expr_count__addr:addr`,
          assume_rule(
            `(retval:int) ==
             cm_rcount_of
               (cm_expr_code_counts (p:cm_program)
                 (fid__pre:int) (expr_:cm_expr))`));
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`loop_`, `(loop_:bool)`)]]
    [[cst::where(`structs`, `structs:(cm_struct_d)list`)]]
    [[cst::where(`globals`, `globals:(cm_global_d)list`)]]
    [[cst::where(`locals`, `locals:(cm_slot_d)list`)]]
    [[cst::where(`zs`, `(zs:int)`)]]
    [[cst::where(`zg`, `(zg:int)`)]]
    [[cst::where(`zl`, `(zl:int)`)]]
    int first_count =
        cmc_stmt_code_count(program, fid, fn, stmt->a);
    [[cst::proof]] {
      cm_retarget_call_result(`first_count__addr:addr`,
          assume_rule(
            `(retval_1:int) ==
             cm_stmt_code_count (p:cm_program) (fid__pre:int)
               (first_:cm_stmt)`));
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`loop_`, `(loop_:bool)`)]]
    [[cst::where(`structs`, `structs:(cm_struct_d)list`)]]
    [[cst::where(`globals`, `globals:(cm_global_d)list`)]]
    [[cst::where(`locals`, `locals:(cm_slot_d)list`)]]
    [[cst::where(`zs`, `(zs:int)`)]]
    [[cst::where(`zg`, `(zg:int)`)]]
    [[cst::where(`zl`, `(zl:int)`)]]
    int second_count =
        cmc_stmt_code_count(program, fid, fn, stmt->b);
    [[cst::proof]] {
      cm_retarget_call_result(`second_count__addr:addr`,
          assume_rule(
            `(retval_1:int) ==
             cm_stmt_code_count (p:cm_program) (fid__pre:int)
               (second_:cm_stmt)`));
      thm shape = assume_rule(
          `s == CMIfS (expr_:cm_expr) (first_:cm_stmt)
             (second_:cm_stmt)`);
      thm expr_return = assume_rule(
          `(retval:int) ==
           cm_rcount_of
             (cm_expr_code_counts (p:cm_program)
               (fid__pre:int) (expr_:cm_expr))`);
      cm_add_count_facts(conv_rule(
          rewrite_conv(THM_LIST(expr_return)),
          from_state_bool(`cm_i32_code_count (retval:int)`)));
      cm_add_count_facts(from_state_bool(
          `cm_i32_code_count
            (cm_stmt_code_count (p:cm_program) (fid__pre:int)
              (first_:cm_stmt))`));
      cm_add_count_facts(from_state_bool(
          `cm_i32_code_count
            (cm_stmt_code_count (p:cm_program) (fid__pre:int)
              (second_:cm_stmt))`));
      cm_prepare_stmt_count_value(shape,
          `(((cm_rcount_of
                (cm_expr_code_counts (p:cm_program)
                  (fid__pre:int) (expr_:cm_expr)) + 1i) +
             cm_stmt_code_count p fid__pre
               (first_:cm_stmt)) + 1i) +
           cm_stmt_code_count p fid__pre (second_:cm_stmt)`,
          THM_LIST());
      add_arith_fact_st(cst_get_symbolic_state(),
          "0i <= cm_rcount_of (cm_expr_code_counts p fid__pre expr_) ==>"
          "0i <= cm_stmt_code_count p fid__pre first_ ==>"
          "0i <= cm_stmt_code_count p fid__pre second_ ==>"
          "(((cm_rcount_of (cm_expr_code_counts p fid__pre expr_) + 1i) +"
          " cm_stmt_code_count p fid__pre first_) + 1i) +"
          " cm_stmt_code_count p fid__pre second_ <= 2147483647i ==>"
          "(--2147483648i <="
          " cm_rcount_of (cm_expr_code_counts p fid__pre expr_) + 1i &&"
          " cm_rcount_of (cm_expr_code_counts p fid__pre expr_) + 1i"
          " <= 2147483647i &&"
          " --2147483648i <="
          " (cm_rcount_of (cm_expr_code_counts p fid__pre expr_) + 1i) +"
          " cm_stmt_code_count p fid__pre first_ &&"
          " (cm_rcount_of (cm_expr_code_counts p fid__pre expr_) + 1i) +"
          " cm_stmt_code_count p fid__pre first_ <= 2147483647i &&"
          " --2147483648i <="
          " ((cm_rcount_of (cm_expr_code_counts p fid__pre expr_) + 1i) +"
          " cm_stmt_code_count p fid__pre first_) + 1i &&"
          " ((cm_rcount_of (cm_expr_code_counts p fid__pre expr_) + 1i) +"
          " cm_stmt_code_count p fid__pre first_) + 1i"
          " <= 2147483647i)");
    }
    result = expr_count + 1 + first_count + 1 + second_count;
    [[cst::proof]] {
      thm shape = assume_rule(
          `s == CMIfS (expr_:cm_expr) (first_:cm_stmt)
             (second_:cm_stmt)`);
      cm_finish_stmt_count_value(shape,
          `(((cm_rcount_of
                (cm_expr_code_counts (p:cm_program)
                  (fid__pre:int) (expr_:cm_expr)) + 1i) +
             cm_stmt_code_count p fid__pre
               (first_:cm_stmt)) + 1i) +
           cm_stmt_code_count p fid__pre (second_:cm_stmt)`,
          THM_LIST());
      cm_close_stmt_if_count_payload(shape);
    }
  } else if (stmt->kind == CMC_STMT_WHILE) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`s:cm_stmt`,
          get_cm_stmt_while_shape_ent()),
          assume_rule(`cm_rep_stmt_kind (s:cm_stmt) == 7i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`expr_:cm_expr`, `first_:cm_stmt`))));
      thm shape = assume_rule(
          `s == CMWhileS (expr_:cm_expr) (first_:cm_stmt)`);
      cm_open_stmt_count_facts(shape);
      cm_open_stmt_while_count_payload(shape);
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`structs`, `structs:(cm_struct_d)list`)]]
    [[cst::where(`globals`, `globals:(cm_global_d)list`)]]
    [[cst::where(`locals`, `locals:(cm_slot_d)list`)]]
    [[cst::where(`zs`, `(zs:int)`)]]
    [[cst::where(`zg`, `(zg:int)`)]]
    [[cst::where(`zl`, `(zl:int)`)]]
    int expr_count =
        cm_expr_rvalue_count(program, fid, fn, stmt->expr);
    [[cst::proof]] {
      cm_retarget_call_result(`expr_count__addr:addr`,
          assume_rule(
            `(retval:int) ==
             cm_rcount_of
               (cm_expr_code_counts (p:cm_program)
                 (fid__pre:int) (expr_:cm_expr))`));
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`loop_`, `T`)]]
    [[cst::where(`structs`, `structs:(cm_struct_d)list`)]]
    [[cst::where(`globals`, `globals:(cm_global_d)list`)]]
    [[cst::where(`locals`, `locals:(cm_slot_d)list`)]]
    [[cst::where(`zs`, `(zs:int)`)]]
    [[cst::where(`zg`, `(zg:int)`)]]
    [[cst::where(`zl`, `(zl:int)`)]]
    int first_count =
        cmc_stmt_code_count(program, fid, fn, stmt->a);
    [[cst::proof]] {
      cm_retarget_call_result(`first_count__addr:addr`,
          assume_rule(
            `(retval_1:int) ==
             cm_stmt_code_count (p:cm_program) (fid__pre:int)
               (first_:cm_stmt)`));
      thm shape = assume_rule(
          `s == CMWhileS (expr_:cm_expr) (first_:cm_stmt)`);
      thm expr_return = assume_rule(
          `(retval:int) ==
           cm_rcount_of
             (cm_expr_code_counts (p:cm_program)
               (fid__pre:int) (expr_:cm_expr))`);
      cm_add_count_facts(conv_rule(
          rewrite_conv(THM_LIST(expr_return)),
          from_state_bool(`cm_i32_code_count (retval:int)`)));
      cm_add_count_facts(from_state_bool(
          `cm_i32_code_count
            (cm_stmt_code_count (p:cm_program) (fid__pre:int)
              (first_:cm_stmt))`));
      cm_prepare_stmt_count_value(shape,
          `((cm_rcount_of
               (cm_expr_code_counts (p:cm_program)
                 (fid__pre:int) (expr_:cm_expr)) + 1i) +
            cm_stmt_code_count p fid__pre (first_:cm_stmt)) + 1i`,
          THM_LIST());
      add_arith_fact_st(cst_get_symbolic_state(),
          "0i <= cm_rcount_of (cm_expr_code_counts p fid__pre expr_) ==>"
          "0i <= cm_stmt_code_count p fid__pre first_ ==>"
          "((cm_rcount_of (cm_expr_code_counts p fid__pre expr_) + 1i) +"
          " cm_stmt_code_count p fid__pre first_) + 1i <= 2147483647i ==>"
          "(--2147483648i <="
          " cm_rcount_of (cm_expr_code_counts p fid__pre expr_) + 1i &&"
          " cm_rcount_of (cm_expr_code_counts p fid__pre expr_) + 1i"
          " <= 2147483647i &&"
          " --2147483648i <="
          " (cm_rcount_of (cm_expr_code_counts p fid__pre expr_) + 1i) +"
          " cm_stmt_code_count p fid__pre first_ &&"
          " (cm_rcount_of (cm_expr_code_counts p fid__pre expr_) + 1i) +"
          " cm_stmt_code_count p fid__pre first_ <= 2147483647i)");
    }
    result = expr_count + 1 + first_count + 1;
    [[cst::proof]] {
      thm shape = assume_rule(
          `s == CMWhileS (expr_:cm_expr) (first_:cm_stmt)`);
      cm_finish_stmt_count_value(shape,
          `((cm_rcount_of
               (cm_expr_code_counts (p:cm_program)
                 (fid__pre:int) (expr_:cm_expr)) + 1i) +
            cm_stmt_code_count p fid__pre (first_:cm_stmt)) + 1i`,
          THM_LIST());
      cm_close_stmt_while_count_payload(shape);
    }
  } else if (stmt->kind == CMC_STMT_BREAK) {
    result = 1;
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`s:cm_stmt`,
          get_cm_stmt_break_shape_ent()),
          assume_rule(`cm_rep_stmt_kind (s:cm_stmt) == 8i`));
      cst_set_symbolic_state(local_apply(
          cst_get_symbolic_state(), shape_ent));
      thm shape = assume_rule(`s == CMBreakS`);
      cm_open_stmt_count_facts(shape);
      cm_finish_stmt_count_value(shape, `1i`, THM_LIST());
    }
  } else if (stmt->kind == CMC_STMT_CONTINUE) {
    result = 1;
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`s:cm_stmt`,
          get_cm_stmt_continue_shape_ent()),
          assume_rule(`cm_rep_stmt_kind (s:cm_stmt) == 9i`));
      cst_set_symbolic_state(local_apply(
          cst_get_symbolic_state(), shape_ent));
      thm shape = assume_rule(`s == CMContinueS`);
      cm_open_stmt_count_facts(shape);
      cm_finish_stmt_count_value(shape, `1i`, THM_LIST());
    }
  } else {
    [[cst::proof]] {
      thm kind = mp_rule(int_arith_rule(
          `(0i <= cm_rep_stmt_kind (s:cm_stmt) &&
            cm_rep_stmt_kind s <= 10i) ==>
           ~(cm_rep_stmt_kind s == 0i) ==>
           ~(cm_rep_stmt_kind s == 1i) ==>
           ~(cm_rep_stmt_kind s == 2i) ==>
           ~(cm_rep_stmt_kind s == 3i) ==>
           ~(cm_rep_stmt_kind s == 4i) ==>
           ~(cm_rep_stmt_kind s == 5i) ==>
           ~(cm_rep_stmt_kind s == 6i) ==>
           ~(cm_rep_stmt_kind s == 7i) ==>
           ~(cm_rep_stmt_kind s == 8i) ==>
           ~(cm_rep_stmt_kind s == 9i) ==>
           cm_rep_stmt_kind s == 10i`),
          spec_rule(`s:cm_stmt`, get_cm_rep_stmt_kind_bounds()));
      kind = mp_rule(kind,
          assume_rule(`~(cm_rep_stmt_kind (s:cm_stmt) == 0i)`));
      kind = mp_rule(kind,
          assume_rule(`~(cm_rep_stmt_kind (s:cm_stmt) == 1i)`));
      kind = mp_rule(kind,
          assume_rule(`~(cm_rep_stmt_kind (s:cm_stmt) == 2i)`));
      kind = mp_rule(kind,
          assume_rule(`~(cm_rep_stmt_kind (s:cm_stmt) == 3i)`));
      kind = mp_rule(kind,
          assume_rule(`~(cm_rep_stmt_kind (s:cm_stmt) == 4i)`));
      kind = mp_rule(kind,
          assume_rule(`~(cm_rep_stmt_kind (s:cm_stmt) == 5i)`));
      kind = mp_rule(kind,
          assume_rule(`~(cm_rep_stmt_kind (s:cm_stmt) == 6i)`));
      kind = mp_rule(kind,
          assume_rule(`~(cm_rep_stmt_kind (s:cm_stmt) == 7i)`));
      kind = mp_rule(kind,
          assume_rule(`~(cm_rep_stmt_kind (s:cm_stmt) == 8i)`));
      kind = mp_rule(kind,
          assume_rule(`~(cm_rep_stmt_kind (s:cm_stmt) == 9i)`));
      add_fact_st(kind);
      thm shape_ent = mp_rule(spec_rule(`s:cm_stmt`,
          get_cm_stmt_return_shape_ent()), kind);
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent, TERM_LIST(`expr_:cm_expr`))));
      thm shape = assume_rule(`s == CMReturnS (expr_:cm_expr)`);
      cm_open_stmt_count_facts(shape);
      thm fn_model = assume_rule(
          `f == inth (fid__pre:int)
            (cm_program_functions (p:cm_program))`);
      thm ret_type_wf = conv_rule(
          rewrite_conv(THM_LIST(sym_rule(fn_model))),
          from_state_bool(
            `cm_type_code_wf
              (cm_function_ret
                (inth (fid__pre:int)
                  (cm_program_functions (p:cm_program))))`));
      add_fact_st(eqt_intro_rule(ret_type_wf));
      cm_open_stmt_expr_count_payload(shape);
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`structs`, `structs:(cm_struct_d)list`)]]
    [[cst::where(`globals`, `globals:(cm_global_d)list`)]]
    [[cst::where(`locals`, `locals:(cm_slot_d)list`)]]
    [[cst::where(`zs`, `(zs:int)`)]]
    [[cst::where(`zg`, `(zg:int)`)]]
    [[cst::where(`zl`, `(zl:int)`)]]
    int expr_count =
        cm_expr_rvalue_count(program, fid, fn, stmt->expr);
    [[cst::proof]] {
      cm_retarget_call_result(`expr_count__addr:addr`,
          assume_rule(
            `(retval:int) ==
             cm_rcount_of
               (cm_expr_code_counts (p:cm_program)
                 (fid__pre:int) (expr_:cm_expr))`));
    }
    int normalize = cm_normalize_count(fn->ret_ty);
    [[cst::proof]] {
      thm bridge = mp_rule(spec_rule(
          `cm_function_ret (f:cm_function_d)`,
          cm_char_normalize_bridge),
          from_state_bool(
            `cm_type_code_wf (cm_function_ret (f:cm_function_d))`));
      thm model = trans_rule(assume_rule(
          `(retval_1:int) ==
           cm_normalize_code_value
             (cm_type_encode (cm_function_ret (f:cm_function_d)))`),
          bridge);
      cm_retarget_call_result(`normalize__addr:addr`, model);
      thm fn_model = assume_rule(
          `f == inth (fid__pre:int)
            (cm_program_functions (p:cm_program))`);
      thm shape = assume_rule(`s == CMReturnS (expr_:cm_expr)`);
      cm_prepare_stmt_count_value(shape,
          `(cm_rcount_of
               (cm_expr_code_counts (p:cm_program)
                 (fid__pre:int) (expr_:cm_expr)) +
             cm_char_normalize_count (cm_function_ret f)) + 6i`,
          THM_LIST(sym_rule(fn_model)));
    }
    result = expr_count + normalize + 6;
    [[cst::proof]] {
      thm fn_model = assume_rule(
          `f == inth (fid__pre:int)
            (cm_program_functions (p:cm_program))`);
      thm shape = assume_rule(`s == CMReturnS (expr_:cm_expr)`);
      cm_finish_stmt_count_value(shape,
          `(cm_rcount_of
               (cm_expr_code_counts (p:cm_program)
                 (fid__pre:int) (expr_:cm_expr)) +
             cm_char_normalize_count (cm_function_ret f)) + 6i`,
          THM_LIST(sym_rule(fn_model)));
      cm_close_stmt_expr_count_payload(shape);
    }
  }
  [[cst::proof]] {
    apply_hconv_st(specl_rule(TERM_LIST(
        `stmt__pre:int`, `s:cm_stmt`, `ze:int`, `za:int`,
        `zb:int`), get_cm_stmt_close_witness()));
  }
  return result;
}

static int cmc_param_stores_count(struct cm_slot *param)
    [[cst::param(`params:(cm_slot_d)list`)]]
    [[cst::require(
      `fact(cm_param_counts_representable params <=> true) **
       cm_slot_list_rep param params`)]]
    [[cst::ensure(
      `fact(cm_param_counts_representable params <=> true) **
       cm_slot_list_rep param params **
       fact((__return:int) == cm_param_stores_count params) **
       fact(cm_i32_code_count (__return:int) <=> true)`)]]
{
  int result;
  if (param == 0) {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`param__pre:addr`,
                `params:(cm_slot_d)list`),
              get_cm_slot_null()),
            assume_rule(`param__pre == 0i`))));
      thm shape = assume_rule(
          `params == ([]:(cm_slot_d)list)`);
      thm model = by_rewrite(
          `cm_param_stores_count
             (params:(cm_slot_d)list) == 0i`,
          THM_LIST(shape, get_cm_param_stores_count_def()));
      add_fact_st(sym_rule(model));
      cm_add_count_facts(eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(
            THM_LIST(get_cm_i32_code_count_def())),
          `cm_i32_code_count 0i`)));
      thm nil_view = spec_rule(`param__pre:addr`,
          conjunct1_rule(get_cm_slot_list_rep_def()));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          eq2ent(sym_rule(nil_view))));
    }
    result = 0;
  } else {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(
              TERM_LIST(`param__pre:addr`,
                `params:(cm_slot_d)list`),
              get_cm_slot_unfold()),
            assume_rule(`~(param__pre == 0i)`))));
      thm shape = assume_rule(
          `params == (slot_:cm_slot_d) ::
            (rest_:(cm_slot_d)list)`);
      thm represented = conv_rule(rewrite_conv(THM_LIST(
          shape, get_cm_param_counts_representable_def())),
          from_state_bool(
            `cm_param_counts_representable
              (params:(cm_slot_d)list)`));
      cm_add_count_facts(conjunct1_rule(represented));
      add_fact_st(eqt_intro_rule(
          conjunct1_rule(conjunct2_rule(represented))));
      add_fact_st(eqt_intro_rule(
          conjunct2_rule(conjunct2_rule(represented))));
    }
    int normalize = cm_normalize_count(param->ty);
    [[cst::proof]] {
      thm type_wf = from_state_bool(
          `cm_type_code_wf (cm_slot_ty (slot_:cm_slot_d))`);
      thm bridge = mp_rule(spec_rule(
          `cm_slot_ty (slot_:cm_slot_d)`,
          cm_char_normalize_bridge), type_wf);
      thm model = trans_rule(assume_rule(
          `(retval:int) ==
           cm_normalize_code_value
             (cm_type_encode
               (cm_slot_ty (slot_:cm_slot_d)))`), bridge);
      cm_retarget_call_result(`normalize__addr:addr`, model);
      add_fact_st(spec_rule(
          `cm_slot_ty (slot_:cm_slot_d)`,
          cm_char_normalize_nonnegative));
    }
    struct cm_slot *next = param->next;
    int rest = cmc_param_stores_count(next);
    [[cst::proof]] {
      thm return_model = assume_rule(
          `(retval_1:int) ==
           cm_param_stores_count
             (rest_:(cm_slot_d)list)`);
      cm_retarget_call_result(`rest__addr:addr`, return_model);
      thm rest_i32 = conv_rule(
          rewrite_conv(THM_LIST(return_model)),
          from_state_bool(
            `cm_i32_code_count (retval_1:int)`));
      cm_add_count_facts(rest_i32);
      thm concrete_upper = conv_rule(rewrite_conv(THM_LIST(
          get_cm_param_stores_count_def(),
          int_arith_rule(
            `!(x:int) (y:int) (z:int).
               x + (y + z) == (x + y) + z`))),
          assume_rule(
            `cm_param_stores_count
               ((slot_:cm_slot_d) ::
                 (rest_:(cm_slot_d)list)) <=
             2147483647i`));
      add_fact_st(concrete_upper);
      add_arith_fact_st(cst_get_symbolic_state(),
          "0i <= cm_param_stores_count rest_ ==>"
          "0i <= cm_char_normalize_count (cm_slot_ty slot_) ==>"
          "(cm_param_stores_count rest_ +"
          " cm_char_normalize_count (cm_slot_ty slot_)) + 5i"
          " <= 2147483647i ==>"
          "(--2147483648i <="
          " cm_param_stores_count rest_ +"
          " cm_char_normalize_count (cm_slot_ty slot_) &&"
          " cm_param_stores_count rest_ +"
          " cm_char_normalize_count (cm_slot_ty slot_)"
          " <= 2147483647i)");
    }
    result = rest + normalize + 5;
    [[cst::proof]] {
      thm shape = assume_rule(
          `params == (slot_:cm_slot_d) ::
            (rest_:(cm_slot_d)list)`);
      term concrete =
          `(cm_param_stores_count
              (rest_:(cm_slot_d)list) +
            cm_char_normalize_count
              (cm_slot_ty (slot_:cm_slot_d))) + 5i`;
      thm model = by_rewrite(
          mk_eq(concrete,
            `cm_param_stores_count
              (params:(cm_slot_d)list)`),
          THM_LIST(shape, get_cm_param_stores_count_def(),
            int_arith_rule(
              `!(x:int) (y:int) (z:int).
                 x + (y + z) == (x + y) + z`)));
      add_fact_st(model);
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `result__addr:addr`,
          concrete,
          `cm_param_stores_count
            (params:(cm_slot_d)list)`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(TERM_LIST(`param__pre:addr`,
              `slot_:cm_slot_d`, `rest_:(cm_slot_d)list`,
              `zn_:int`), get_cm_slot_fold()),
            assume_rule(`~(param__pre == 0i)`))));
    }
  }
  return result;
}

int cmc_function_prologue_count(struct cm_function *fn)
    [[cst::param(`f:cm_function_d`, `body:int`, `next:int`)]]
    [[cst::require(
      `fact(cm_param_counts_representable
              (cm_function_params f) <=> true) **
       fact(cm_i32_code_count
              (cm_function_prologue_count f) <=> true) **
       cm_function_context_rep fn f body next`)]]
    [[cst::ensure(
      `fact(cm_param_counts_representable
              (cm_function_params f) <=> true) **
       fact(cm_i32_code_count
              (cm_function_prologue_count f) <=> true) **
       cm_function_context_rep fn f body next **
       fact((__return:int) == cm_function_prologue_count f) **
       fact(cm_i32_code_count (__return:int) <=> true)`)]]
{
  [[cst::proof]] {
    thm context_view = apply_conversion(
        pure_rewrite_conv(THM_LIST(cm_function_context_rep_def)),
        `cm_function_context_rep (fn__pre:int)
          (f:cm_function_d) (body:int) (next:int)`);
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        rename_exists_hconv(eq2ent(context_view),
          TERM_LIST(`params_ptr_:int`, `locals_ptr_:int`))));
  }
  int params_count = cmc_param_stores_count(fn->params);
  [[cst::proof]] {
    thm return_model = assume_rule(
        `(retval:int) ==
         cm_param_stores_count
           (cm_function_params (f:cm_function_d))`);
    cm_retarget_call_result(`params_count__addr:addr`,
        return_model);
    thm concrete_i32 = conv_rule(
        rewrite_conv(
          THM_LIST(get_cm_function_prologue_count_def())),
        from_state_bool(
          `cm_i32_code_count
            (cm_function_prologue_count (f:cm_function_d))`));
    cm_add_count_facts(concrete_i32);
  }
  int result = 14 + params_count;
  [[cst::proof]] {
    thm model = by_rewrite(
        `14i +
           cm_param_stores_count
             (cm_function_params (f:cm_function_d)) ==
         cm_function_prologue_count f`,
        THM_LIST(get_cm_function_prologue_count_def()));
    add_fact_st(model);
    cst_set_symbolic_state(retarget_cell_st(
        cst_get_symbolic_state(), `result__addr:addr`,
        `14i +
          cm_param_stores_count
            (cm_function_params (f:cm_function_d))`,
        `cm_function_prologue_count f`));
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        cm_function_context_fold_hconv(
          `fn__pre:int`, `f:cm_function_d`,
          `body:int`, `next:int`,
          `params_ptr_:int`, `locals_ptr_:int`)));
  }
  return result;
}

int cmc_function_code_count(struct cm_program *program, int fid,
                                   struct cm_function *fn)
    [[cst::param(`p:cm_program`, `f:cm_function_d`,
                 `functions_ptr:int`, `body_ptr:int`,
                 `next_ptr:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(cm_function_counts_representable p fid f <=> true) **
       fact(cm_stmt_wf p f F (cm_function_body f) <=> true) **
       fact(cm_rep_structs_safe
              (cm_program_structs p) <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body_ptr next_ptr **
       cm_stmt_rep body_ptr (cm_function_body f)`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(cm_function_counts_representable p fid f <=> true) **
       fact(cm_stmt_wf p f F (cm_function_body f) <=> true) **
       fact(cm_rep_structs_safe
              (cm_program_structs p) <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body_ptr next_ptr **
       cm_stmt_rep body_ptr (cm_function_body f) **
       fact((__return:int) == cm_function_code_count p fid) **
       fact(cm_i32_code_count (__return:int) <=> true)`)]]
{
  [[cst::proof]] {
    thm represented = conv_rule(
        rewrite_conv(
          THM_LIST(get_cm_function_counts_representable_def())),
        from_state_bool(
          `cm_function_counts_representable
            (p:cm_program) (fid__pre:int)
            (f:cm_function_d)`));
    add_fact_st(conjunct1_rule(represented));
    add_fact_st(eqt_intro_rule(
        conjunct1_rule(conjunct2_rule(represented))));
    cm_add_count_facts(
        conjunct1_rule(conjunct2_rule(
          conjunct2_rule(represented))));
    thm body_counts =
        conjunct1_rule(conjunct2_rule(conjunct2_rule(
          conjunct2_rule(represented))));
    add_fact_st(eqt_intro_rule(body_counts));
    cm_add_count_facts(
        conjunct2_rule(conjunct2_rule(conjunct2_rule(
          conjunct2_rule(represented)))));
  }
  int prologue_count = cmc_function_prologue_count(fn);
  [[cst::proof]] {
    cm_retarget_call_result(`prologue_count__addr:addr`,
        assume_rule(
          `(retval:int) ==
           cm_function_prologue_count (f:cm_function_d)`));
    thm program_view = apply_conversion(
        pure_rewrite_conv(THM_LIST(cm_program_context_rep_def)),
        `cm_program_context_rep (program__pre:int)
          (p:cm_program) (functions_ptr:int)`);
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        rename_exists_hconv(eq2ent(program_view),
          TERM_LIST(`structs_ptr_:int`, `globals_ptr_:int`,
            `strings_ptr_:int`))));
    thm function_view = apply_conversion(
        pure_rewrite_conv(THM_LIST(cm_function_context_rep_def)),
        `cm_function_context_rep (fn__pre:int)
          (f:cm_function_d) (body_ptr:int) (next_ptr:int)`);
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        rename_exists_hconv(eq2ent(function_view),
          TERM_LIST(`params_ptr_:int`, `locals_ptr_:int`))));
  }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`f`, `(f:cm_function_d)`)]]
  [[cst::where(`loop_`, `F`)]]
  [[cst::where(`structs`, `cm_program_structs (p:cm_program)`)]]
  [[cst::where(`globals`, `cm_program_globals (p:cm_program)`)]]
  [[cst::where(`locals`, `cm_function_locals (f:cm_function_d)`)]]
  [[cst::where(`s`, `cm_function_body (f:cm_function_d)`)]]
  int body_count =
      cmc_stmt_code_count(program, fid, fn, fn->body);
  [[cst::proof]] {
    cm_retarget_call_result(`body_count__addr:addr`,
        assume_rule(
          `(retval_1:int) ==
           cm_stmt_code_count (p:cm_program)
             (fid__pre:int) (cm_function_body (f:cm_function_d))`));
    thm function_model = assume_rule(
        `(f:cm_function_d) ==
         inth (fid__pre:int)
           (cm_program_functions (p:cm_program))`);
    thm concrete_i32 = conv_rule(rewrite_conv(THM_LIST(
        get_cm_function_code_count_def(),
        sym_rule(function_model),
        int_arith_rule(
          `!(x:int) (y:int) (z:int).
             x + (y + z) == (x + y) + z`))),
        from_state_bool(
          `cm_i32_code_count
            (cm_function_code_count
              (p:cm_program) (fid__pre:int))`));
    cm_add_count_facts(concrete_i32);
    add_arith_fact_st(cst_get_symbolic_state(),
        "0i <= (cm_function_prologue_count f +"
        " cm_stmt_code_count p fid__pre (cm_function_body f)) + 7i ==>"
        "(cm_function_prologue_count f +"
        " cm_stmt_code_count p fid__pre (cm_function_body f)) + 7i"
        " <= 2147483647i ==>"
        "(--2147483648i <="
        " cm_function_prologue_count f +"
        " cm_stmt_code_count p fid__pre (cm_function_body f) &&"
        " cm_function_prologue_count f +"
        " cm_stmt_code_count p fid__pre (cm_function_body f)"
        " <= 2147483647i)");
  }
  int result = prologue_count + body_count + 7;
  [[cst::proof]] {
    thm function_model = assume_rule(
        `(f:cm_function_d) ==
         inth (fid__pre:int)
           (cm_program_functions (p:cm_program))`);
    term concrete =
        `(cm_function_prologue_count (f:cm_function_d) +
          cm_stmt_code_count (p:cm_program)
            (fid__pre:int) (cm_function_body (f:cm_function_d))) + 7i`;
    thm model = by_rewrite(
        mk_eq(concrete,
          `cm_function_code_count
            (p:cm_program) (fid__pre:int)`),
        THM_LIST(get_cm_function_code_count_def(),
          sym_rule(function_model),
          int_arith_rule(
            `!(x:int) (y:int) (z:int).
               x + (y + z) == (x + y) + z`)));
    add_fact_st(model);
    cst_set_symbolic_state(retarget_cell_st(
        cst_get_symbolic_state(), `result__addr:addr`, concrete,
        `cm_function_code_count
          (p:cm_program) (fid__pre:int)`));
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        cm_function_context_fold_hconv(
          `fn__pre:int`, `f:cm_function_d`,
          `body_ptr:int`, `next_ptr:int`,
          `params_ptr_:int`, `locals_ptr_:int`)));
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        cm_program_context_fold_hconv(
          `program__pre:int`, `p:cm_program`,
          `functions_ptr:int`, `structs_ptr_:int`,
          `globals_ptr_:int`, `strings_ptr_:int`)));
  }
  return result;
}

static int cmc_function_prefix_count(
    struct cm_program *program, struct cm_function *fn,
    int index, int remaining)
    [[cst::param(`p:cm_program`,
                 `functions:(cm_function_d)list`,
                 `functions_ptr:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(cm_rep_structs_safe
              (cm_program_structs p) <=> true) **
       fact(0i <= index) **
       fact(0i <= remaining) **
       fact(remaining <= ilength functions) **
       fact(index ==
         ilength (cm_program_functions p) -
         ilength functions) **
       fact(index + remaining <= 2147483647i) **
       fact(cm_functions_counts_representable
              p functions index <=> true) **
       fact(cm_i32_code_count
              (11i + cm_function_prefix
                p functions remaining) <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_list_rep fn functions`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(cm_rep_structs_safe
              (cm_program_structs p) <=> true) **
       fact(0i <= index) **
       fact(0i <= remaining) **
       fact(remaining <= ilength functions) **
       fact(index ==
         ilength (cm_program_functions p) -
         ilength functions) **
       fact(index + remaining <= 2147483647i) **
       fact(cm_functions_counts_representable
              p functions index <=> true) **
       fact(cm_i32_code_count
              (11i + cm_function_prefix
                p functions remaining) <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_list_rep fn functions **
       fact((__return:int) ==
         cm_function_prefix p functions remaining) **
       fact(cm_i32_code_count (__return:int) <=> true)`)]]
{
  [[cst::proof]] {
    cm_add_count_facts(from_state_bool(
        `cm_i32_code_count
          (11i + cm_function_prefix
            (p:cm_program) (functions:(cm_function_d)list)
            (remaining__pre:int))`));
    add_fact_st(specl_rule(TERM_LIST(
        `functions:(cm_function_d)list`, `p:cm_program`,
        `remaining__pre:int`),
        cm_function_prefix_nonnegative));
  }
  if (remaining == 0) {
    [[cst::proof]] {
      thm model = by_rewrite(
          `cm_function_prefix (p:cm_program)
             (functions:(cm_function_d)list)
             (remaining__pre:int) == 0i`,
          THM_LIST(
            assume_rule(`(remaining__pre:int) == 0i`),
            cm_function_prefix_zero));
      add_fact_st(sym_rule(model));
      cm_add_count_facts(eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(
            THM_LIST(get_cm_i32_code_count_def())),
          `cm_i32_code_count 0i`)));
      cm_keep_only_facts(TERM_LIST(
          `cm_wf_program (p:cm_program) <=> true`,
          `cm_rep_structs_safe
             (cm_program_structs (p:cm_program)) <=> true`,
          `0i <= (index__pre:int)`,
          `0i <= (remaining__pre:int)`,
          `(remaining__pre:int) <=
             ilength (functions:(cm_function_d)list)`,
          `(index__pre:int) ==
             ilength (cm_program_functions (p:cm_program)) -
             ilength (functions:(cm_function_d)list)`,
          `(index__pre:int) + (remaining__pre:int) <=
             2147483647i`,
          `cm_functions_counts_representable
             (p:cm_program) (functions:(cm_function_d)list)
             (index__pre:int) <=> true`,
          `cm_i32_code_count
             (11i + cm_function_prefix
               (p:cm_program) (functions:(cm_function_d)list)
               (remaining__pre:int)) <=> true`,
          `0i == cm_function_prefix
             (p:cm_program) (functions:(cm_function_d)list)
             (remaining__pre:int)`,
          `cm_i32_code_count 0i <=> true`));
    }
    return 0;
  };
  if (fn == 0) {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(TERM_LIST(
              `fn__pre:int`,
              `functions:(cm_function_d)list`),
              cm_function_list_null_shape),
            assume_rule(`fn__pre == 0i`))));
      thm nil_model = assume_rule(
          `functions == ([]:(cm_function_d)list)`);
      thm upper = conv_rule(rewrite_conv(THM_LIST(
          nil_model, get_theorem_by_name("ILENGTH_DEF"))),
          assume_rule(
            `(remaining__pre:int) <=
             ilength (functions:(cm_function_d)list)`));
      thm positive = mp_rule(mp_rule(int_arith_rule(
          `0i <= (remaining__pre:int) ==>
           ~(remaining__pre == 0i) ==>
           1i <= remaining__pre`),
          assume_rule(`0i <= (remaining__pre:int)`)),
          assume_rule(`~((remaining__pre:int) == 0i)`));
      add_fact_st(upper);
      add_fact_st(positive);
    }
    return 0;
  };
  [[cst::proof]] {
    thm shape_open = mp_rule(specl_rule(TERM_LIST(
        `fn__pre:int`, `functions:(cm_function_d)list`),
        cm_function_list_nonnull_shape),
        assume_rule(`~(fn__pre == 0i)`));
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        rename_exists_hconv(shape_open,
          TERM_LIST(`f_:cm_function_d`,
            `rest_:(cm_function_d)list`))));
    thm shape = assume_rule(
        `functions == (f_:cm_function_d) ::
          (rest_:(cm_function_d)list)`);
    substitute_st(shape);
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        rename_exists_hconv(specl_rule(TERM_LIST(
            `fn__pre:int`, `f_:cm_function_d`,
            `rest_:(cm_function_d)list`),
            cm_function_context_cons_open),
          TERM_LIST(`body_ptr_:int`, `next_ptr_:int`))));

    thm represented = conv_rule(rewrite_conv(
        THM_LIST(get_cm_functions_counts_representable_def())),
        from_state_bool(
          `cm_functions_counts_representable
            (p:cm_program)
            ((f_:cm_function_d) ::
              (rest_:(cm_function_d)list))
            (index__pre:int)`));
    cm_add_count_facts(conjunct1_rule(represented));
    thm function_counts =
        conjunct1_rule(conjunct2_rule(represented));
    add_fact_st(eqt_intro_rule(function_counts));
    add_fact_st(eqt_intro_rule(
        conjunct2_rule(conjunct2_rule(represented))));

    thm rest_length = ispec_rule(
        `rest_:(cm_function_d)list`,
        get_theorem_by_name("ILENGTH_NONNEG"));
    thm cons_length = apply_conversion(rewrite_conv(
        THM_LIST(get_theorem_by_name("ILENGTH_DEF"))),
        `ilength ((f_:cm_function_d) ::
          (rest_:(cm_function_d)list))`);
    add_fact_st(rest_length);
    add_fact_st(cons_length);
    cm_commit_arith_fact(
        "0i <= (index__pre:int) ==>"
        "index__pre =="
        " ilength (cm_program_functions (p:cm_program)) -"
        " ilength ((f_:cm_function_d) :: rest_) ==>"
        "ilength ((f_:cm_function_d) :: rest_) =="
        " 1i + ilength rest_ ==>"
        "0i <= ilength (rest_:(cm_function_d)list) ==>"
        "index__pre <"
        " ilength (cm_program_functions p)");

    thm wf = conv_rule(rewrite_conv(THM_LIST(
        get_cm_wf_program_def(),
        get_cm_codegen_admissible_def())),
        from_state_bool(`cm_wf_program (p:cm_program)`));
    thm typed = conv_rule(rewrite_conv(
        THM_LIST(get_cm_typed_program_def())),
        conjunct1_rule(wf));
    thm function_rule = conjunct1_rule(conjunct2_rule(
        conjunct2_rule(conjunct2_rule(typed))));
    thm function_wf = mp_rule(mp_rule(spec_rule(
        `index__pre:int`, function_rule),
        assume_rule(`0i <= (index__pre:int)`)),
        assume_rule(
          `(index__pre:int) <
           ilength (cm_program_functions (p:cm_program))`));
    thm function_model = conjunct1_rule(conv_rule(
        rewrite_conv(
          THM_LIST(get_cm_function_counts_representable_def())),
        function_counts));
    thm concrete_wf = conv_rule(
        rewrite_conv(THM_LIST(sym_rule(function_model))),
        function_wf);
    thm opened_wf = conv_rule(rewrite_conv(
        THM_LIST(get_cm_function_wf_def())), concrete_wf);
    thm stmt_wf = conjunct1_rule(conjunct2_rule(
        conjunct2_rule(conjunct2_rule(opened_wf))));
    add_fact_st(eqt_intro_rule(stmt_wf));
  }
  int head_count =
      cmc_function_code_count(program, index, fn);
  [[cst::proof]] {
    cm_retarget_call_result(`head_count__addr:addr`,
        assume_rule(
          `(retval:int) ==
           cm_function_code_count
             (p:cm_program) (index__pre:int)`));
    thm prefix_model = by_rewrite(
        `cm_function_prefix (p:cm_program)
           ((f_:cm_function_d) ::
             (rest_:(cm_function_d)list))
           (remaining__pre:int) ==
         cm_function_code_count p index__pre +
         cm_function_prefix p rest_ (remaining__pre - 1i)`,
        THM_LIST(get_cm_function_prefix_def(),
          assume_rule(`~((remaining__pre:int) == 0i)`),
          sym_rule(assume_rule(
            `(index__pre:int) ==
             ilength (cm_program_functions (p:cm_program)) -
             ilength ((f_:cm_function_d) ::
               (rest_:(cm_function_d)list))`))));
    add_fact_st(prefix_model);
    add_fact_st(specl_rule(TERM_LIST(
        `rest_:(cm_function_d)list`, `p:cm_program`,
        `(remaining__pre:int) - 1i`),
        cm_function_prefix_nonnegative));
    add_fact_st(specl_rule(TERM_LIST(
        `p:cm_program`, `index__pre:int`),
        cm_function_code_count_nonnegative));

    cm_commit_arith_fact(
        "0i <= (remaining__pre:int) ==> "
        "~(remaining__pre == 0i) ==>"
        "1i <= remaining__pre");
    cm_commit_arith_fact(
        "remaining__pre <="
        " ilength ((f_:cm_function_d) ::"
        " (rest_:(cm_function_d)list)) ==>"
        "ilength ((f_:cm_function_d) :: rest_) =="
        " 1i + ilength rest_ ==>"
        "1i <= remaining__pre ==>"
        "remaining__pre - 1i <= ilength rest_");
    cm_commit_arith_fact(
        "0i <= (remaining__pre:int) ==>"
        "1i <= remaining__pre ==>"
        "0i <= remaining__pre - 1i");
    cm_commit_arith_fact(
        "0i <= (index__pre:int) ==>"
        "0i <= index__pre + 1i");
    cm_commit_arith_fact(
        "index__pre =="
        " ilength (cm_program_functions (p:cm_program)) -"
        " ilength ((f_:cm_function_d) :: rest_) ==>"
        "ilength ((f_:cm_function_d) :: rest_) =="
        " 1i + ilength (rest_:(cm_function_d)list) ==>"
        "index__pre + 1i =="
        " ilength (cm_program_functions p) - ilength rest_");
    cm_commit_arith_fact(
        "index__pre + remaining__pre <= 2147483647i ==>"
        "(index__pre + 1i) +"
        " (remaining__pre - 1i) <= 2147483647i");

    cm_commit_arith_fact(
        "0i <= cm_function_prefix"
        " (p:cm_program) rest_ (remaining__pre - 1i) ==>"
        "0i <= 11i + cm_function_prefix"
        " p rest_ (remaining__pre - 1i)");
    cm_commit_arith_fact(
        "0i <= cm_function_code_count"
        " (p:cm_program) index__pre ==>"
        "cm_function_prefix p ((f_:cm_function_d) :: rest_)"
        " remaining__pre =="
        " cm_function_code_count p index__pre +"
        " cm_function_prefix p rest_ (remaining__pre - 1i) ==>"
        "11i + cm_function_prefix p"
        " ((f_:cm_function_d) :: rest_) remaining__pre"
        " <= 2147483647i ==>"
        "11i + cm_function_prefix p rest_"
        " (remaining__pre - 1i) <= 2147483647i");
    term child =
        `11i + cm_function_prefix (p:cm_program)
          (rest_:(cm_function_d)list)
          ((remaining__pre:int) - 1i)`;
    thm child_bounds = conj_rule(
        assume_rule(mk_binop(`(<=):int->int->bool`,
          `0i:int`, child)),
        assume_rule(mk_binop(`(<=):int->int->bool`,
          child, `2147483647i:int`)));
    thm child_view = apply_conversion(
        rewrite_conv(THM_LIST(get_cm_i32_code_count_def())),
        mk_comb(`cm_i32_code_count:int->bool`, child));
    add_fact_st(eqt_intro_rule(
        eq_mp_rule(sym_rule(child_view), child_bounds)));
  }
  [[cst::proof]] {
    thm function_view = apply_conversion(
        pure_rewrite_conv(THM_LIST(cm_function_context_rep_def)),
        `cm_function_context_rep (fn__pre:int)
          (f_:cm_function_d) (body_ptr_:int) (next_ptr_:int)`);
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        rename_exists_hconv(eq2ent(function_view),
          TERM_LIST(`params_ptr_head_:int`,
            `locals_ptr_head_:int`))));
  }
  struct cm_function *next = fn->next;
  int tail_count = cmc_function_prefix_count(
      program, next, index + 1, remaining - 1);
  [[cst::proof]] {
    thm tail_model = assume_rule(
        `(retval_1:int) ==
         cm_function_prefix (p:cm_program)
           (rest_:(cm_function_d)list)
           ((remaining__pre:int) - 1i)`);
    cm_retarget_call_result(
        `tail_count__addr:addr`, tail_model);
    cm_add_count_facts(conv_rule(
        rewrite_conv(THM_LIST(tail_model)),
        from_state_bool(`cm_i32_code_count (retval_1:int)`)));
    cm_commit_arith_fact(
        "cm_function_prefix (p:cm_program)"
        " ((f_:cm_function_d) :: rest_) remaining__pre =="
        " cm_function_code_count p index__pre +"
        " cm_function_prefix p rest_ (remaining__pre - 1i) ==>"
        "11i + cm_function_prefix p"
        " ((f_:cm_function_d) :: rest_) remaining__pre"
        " <= 2147483647i ==>"
        "cm_function_code_count p index__pre +"
        " cm_function_prefix p rest_ (remaining__pre - 1i)"
        " <= 2147483647i");
    cm_commit_arith_fact(
        "0i <= cm_function_code_count"
        " (p:cm_program) index__pre ==>"
        "0i <= cm_function_prefix p"
        " (rest_:(cm_function_d)list)"
        " (remaining__pre - 1i) ==> "
        "--2147483648i <="
        " cm_function_code_count p index__pre +"
        " cm_function_prefix p rest_ (remaining__pre - 1i)");
  }
  int result = head_count + tail_count;
  [[cst::proof]] {
    term concrete =
        `cm_function_code_count (p:cm_program)
           (index__pre:int) +
         cm_function_prefix p
           (rest_:(cm_function_d)list)
           ((remaining__pre:int) - 1i)`;
    thm model = by_rewrite(mk_eq(concrete,
        `cm_function_prefix (p:cm_program)
          ((f_:cm_function_d) ::
            (rest_:(cm_function_d)list))
          (remaining__pre:int)`),
        THM_LIST(get_cm_function_prefix_def(),
          assume_rule(`~((remaining__pre:int) == 0i)`),
          sym_rule(assume_rule(
            `(index__pre:int) ==
             ilength (cm_program_functions (p:cm_program)) -
             ilength ((f_:cm_function_d) ::
               (rest_:(cm_function_d)list))`))));
    add_fact_st(model);
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        cm_function_context_fold_hconv(
          `fn__pre:int`, `f_:cm_function_d`,
          `body_ptr_:int`, `next_ptr_:int`,
          `params_ptr_head_:int`, `locals_ptr_head_:int`)));
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        specl_rule(TERM_LIST(
            `fn__pre:int`, `f_:cm_function_d`,
            `rest_:(cm_function_d)list`,
            `body_ptr_:int`, `next_ptr_:int`),
            cm_function_context_cons_close)));
    substitute_st(sym_rule(assume_rule(
        `functions == (f_:cm_function_d) ::
          (rest_:(cm_function_d)list)`)));
    cm_commit_arith_fact(
        "0i <= cm_function_code_count"
        " (p:cm_program) (index__pre:int) ==>"
        "0i <= cm_function_prefix p"
        " (rest_:(cm_function_d)list)"
        " ((remaining__pre:int) - 1i) ==>"
        "0i <= cm_function_code_count p index__pre +"
        " cm_function_prefix p rest_ (remaining__pre - 1i)");
    thm concrete_bounds = conj_rule(
        assume_rule(mk_binop(`(<=):int->int->bool`,
          `0i:int`, concrete)),
        assume_rule(mk_binop(`(<=):int->int->bool`,
          concrete, `2147483647i:int`)));
    thm concrete_view = apply_conversion(
        rewrite_conv(THM_LIST(get_cm_i32_code_count_def())),
        mk_comb(`cm_i32_code_count:int->bool`, concrete));
    add_fact_st(eqt_intro_rule(
        eq_mp_rule(sym_rule(concrete_view), concrete_bounds)));
    term result_model =
        `cm_function_prefix (p:cm_program)
          (functions:(cm_function_d)list)
          (remaining__pre:int)`;
    cm_keep_only_facts(TERM_LIST(
        `cm_wf_program (p:cm_program) <=> true`,
        `cm_rep_structs_safe
           (cm_program_structs (p:cm_program)) <=> true`,
        `0i <= (index__pre:int)`,
        `0i <= (remaining__pre:int)`,
        `(remaining__pre:int) <=
           ilength (functions:(cm_function_d)list)`,
        `(index__pre:int) ==
           ilength (cm_program_functions (p:cm_program)) -
           ilength (functions:(cm_function_d)list)`,
        `(index__pre:int) + (remaining__pre:int) <=
           2147483647i`,
        `cm_functions_counts_representable
           (p:cm_program) (functions:(cm_function_d)list)
           (index__pre:int) <=> true`,
        `cm_i32_code_count
           (11i + cm_function_prefix
             (p:cm_program) (functions:(cm_function_d)list)
             (remaining__pre:int)) <=> true`,
        `${concrete:int} == ${result_model:int}`,
        `cm_i32_code_count ${concrete:int} <=> true`));
  }
  return result;
}

int cmc_function_pc(struct cm_program *program, int fid)
    [[cst::param(`p:cm_program`, `functions_ptr:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(cm_rep_structs_safe
              (cm_program_structs p) <=> true) **
       fact(0i <= fid) **
       fact(fid <= ilength (cm_program_functions p)) **
       fact(cm_i32_code_count
              (cm_function_pc p fid) <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_list_rep functions_ptr
         (cm_program_functions p)`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(cm_rep_structs_safe
              (cm_program_structs p) <=> true) **
       fact(0i <= fid) **
       fact(fid <= ilength (cm_program_functions p)) **
       fact(cm_i32_code_count
              (cm_function_pc p fid) <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_list_rep functions_ptr
         (cm_program_functions p) **
       fact((__return:int) == cm_function_pc p fid) **
       fact(cm_i32_code_count (__return:int) <=> true)`)]]
{
  [[cst::proof]] {
    thm program_view = apply_conversion(
        pure_rewrite_conv(THM_LIST(cm_program_context_rep_def)),
        `cm_program_context_rep (program__pre:int)
          (p:cm_program) (functions_ptr:int)`);
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        rename_exists_hconv(eq2ent(program_view),
          TERM_LIST(`structs_ptr_:int`, `globals_ptr_:int`,
            `strings_ptr_:int`))));
  }
  struct cm_function *fn = program->functions;
  [[cst::proof]] {
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        cm_program_context_fold_hconv(
          `program__pre:int`, `p:cm_program`,
          `functions_ptr:int`, `structs_ptr_:int`,
          `globals_ptr_:int`, `strings_ptr_:int`)));
    thm wf = conv_rule(rewrite_conv(THM_LIST(
        get_cm_wf_program_def(),
        get_cm_codegen_admissible_def())),
        from_state_bool(`cm_wf_program (p:cm_program)`));
    thm counts = conv_rule(rewrite_conv(
        THM_LIST(get_cm_codegen_counts_representable_def())),
        conjunct2_rule(conjunct2_rule(conjunct2_rule(
          conjunct2_rule(conjunct2_rule(conjunct2_rule(
            conjunct2_rule(conjunct2_rule(wf)))))))));
    add_fact_st(eqt_intro_rule(conjunct1_rule(counts)));
    thm pc_i32 = conv_rule(
        rewrite_conv(THM_LIST(get_cm_function_pc_def())),
        from_state_bool(
          `cm_i32_code_count
            (cm_function_pc (p:cm_program) (fid__pre:int))`));
    add_fact_st(eqt_intro_rule(pc_i32));
    add_data_at_range_st(
        `fid__addr:addr`, `Tint`, `fid__pre:int`);
    cm_commit_arith_fact(
        "0i <= (fid__pre:int) ==>"
        "fid__pre <= 2147483647i ==>"
        "0i + fid__pre <= 2147483647i");
  }
  int prefix =
      cmc_function_prefix_count(program, fn, 0, fid);
  [[cst::proof]] {
    thm prefix_model = assume_rule(
        `(retval:int) ==
         cm_function_prefix (p:cm_program)
           (cm_program_functions p) (fid__pre:int)`);
    cm_retarget_call_result(`prefix__addr:addr`, prefix_model);
    cm_add_count_facts(conv_rule(
        rewrite_conv(THM_LIST(prefix_model)),
        from_state_bool(`cm_i32_code_count (retval:int)`)));
    thm pc_i32 = from_state_bool(
        `cm_i32_code_count
          (cm_function_pc (p:cm_program) (fid__pre:int))`);
    cm_add_count_facts(conv_rule(rewrite_conv(
        THM_LIST(get_cm_function_pc_def())), pc_i32));
  }
  int result = 11 + prefix;
  [[cst::proof]] {
    thm model = by_rewrite(
        `11i + cm_function_prefix (p:cm_program)
           (cm_program_functions p) (fid__pre:int) ==
         cm_function_pc p fid__pre`,
        THM_LIST(get_cm_function_pc_def()));
    add_fact_st(model);
    cst_set_symbolic_state(retarget_cell_st(
        cst_get_symbolic_state(), `result__addr:addr`,
        `11i + cm_function_prefix (p:cm_program)
          (cm_program_functions p) (fid__pre:int)`,
        `cm_function_pc (p:cm_program) (fid__pre:int)`));
  }
  return result;
}

static int cmc_functions_code_size_count(
    struct cm_program *program, struct cm_function *fn, int index)
    [[cst::param(`p:cm_program`,
                 `functions:(cm_function_d)list`,
                 `functions_ptr:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(cm_rep_structs_safe
              (cm_program_structs p) <=> true) **
       fact(0i <= index) **
       fact(index ==
         ilength (cm_program_functions p) -
         ilength functions) **
       fact(index + ilength functions <= 2147483647i) **
       fact(cm_functions_counts_representable
              p functions index <=> true) **
       fact(cm_i32_code_count
              (cm_functions_code_size
                p functions index) <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_list_rep fn functions`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(cm_rep_structs_safe
              (cm_program_structs p) <=> true) **
       fact(0i <= index) **
       fact(index ==
         ilength (cm_program_functions p) -
         ilength functions) **
       fact(index + ilength functions <= 2147483647i) **
       fact(cm_functions_counts_representable
              p functions index <=> true) **
       fact(cm_i32_code_count
              (cm_functions_code_size
                p functions index) <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_list_rep fn functions **
       fact((__return:int) ==
         cm_functions_code_size p functions index) **
       fact(cm_i32_code_count (__return:int) <=> true)`)]]
{
  [[cst::proof]] {
    cm_add_count_facts(from_state_bool(
        `cm_i32_code_count
          (cm_functions_code_size
            (p:cm_program) (functions:(cm_function_d)list)
            (index__pre:int))`));
    add_fact_st(specl_rule(TERM_LIST(
        `functions:(cm_function_d)list`, `p:cm_program`,
        `index__pre:int`),
        cm_functions_code_size_nonnegative));
  }
  if (fn == 0) {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(TERM_LIST(
              `fn__pre:int`,
              `functions:(cm_function_d)list`),
              cm_function_list_null_shape),
            assume_rule(`fn__pre == 0i`))));
      thm nil_model = assume_rule(
          `functions == ([]:(cm_function_d)list)`);
      thm model = by_rewrite(
          `cm_functions_code_size
             (p:cm_program) (functions:(cm_function_d)list)
             (index__pre:int) == 0i`,
          THM_LIST(nil_model,
            get_cm_functions_code_size_def()));
      add_fact_st(sym_rule(model));
      cm_add_count_facts(eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(
            THM_LIST(get_cm_i32_code_count_def())),
          `cm_i32_code_count 0i`)));
      cm_keep_only_facts(TERM_LIST(
          `cm_wf_program (p:cm_program) <=> true`,
          `cm_rep_structs_safe
             (cm_program_structs (p:cm_program)) <=> true`,
          `0i <= (index__pre:int)`,
          `(index__pre:int) ==
             ilength (cm_program_functions (p:cm_program)) -
             ilength (functions:(cm_function_d)list)`,
          `(index__pre:int) +
             ilength (functions:(cm_function_d)list) <=
             2147483647i`,
          `cm_functions_counts_representable
             (p:cm_program) (functions:(cm_function_d)list)
             (index__pre:int) <=> true`,
          `cm_i32_code_count
             (cm_functions_code_size
               (p:cm_program) (functions:(cm_function_d)list)
               (index__pre:int)) <=> true`,
          `0i ==
             cm_functions_code_size
               (p:cm_program) (functions:(cm_function_d)list)
               (index__pre:int)`,
          `cm_i32_code_count 0i <=> true`));
    }
    return 0;
  };
  [[cst::proof]] {
    thm shape_open = mp_rule(specl_rule(TERM_LIST(
        `fn__pre:int`, `functions:(cm_function_d)list`),
        cm_function_list_nonnull_shape),
        assume_rule(`~(fn__pre == 0i)`));
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        rename_exists_hconv(shape_open,
          TERM_LIST(`f_:cm_function_d`,
            `rest_:(cm_function_d)list`))));
    thm shape = assume_rule(
        `functions == (f_:cm_function_d) ::
          (rest_:(cm_function_d)list)`);
    substitute_st(shape);
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        rename_exists_hconv(specl_rule(TERM_LIST(
            `fn__pre:int`, `f_:cm_function_d`,
            `rest_:(cm_function_d)list`),
            cm_function_context_cons_open),
          TERM_LIST(`body_ptr_:int`, `next_ptr_:int`))));

    thm represented = conv_rule(rewrite_conv(
        THM_LIST(get_cm_functions_counts_representable_def())),
        from_state_bool(
          `cm_functions_counts_representable
            (p:cm_program)
            ((f_:cm_function_d) ::
              (rest_:(cm_function_d)list))
            (index__pre:int)`));
    cm_add_count_facts(conjunct1_rule(represented));
    thm function_counts =
        conjunct1_rule(conjunct2_rule(represented));
    add_fact_st(eqt_intro_rule(function_counts));
    add_fact_st(eqt_intro_rule(
        conjunct2_rule(conjunct2_rule(represented))));

    thm rest_length = ispec_rule(
        `rest_:(cm_function_d)list`,
        get_theorem_by_name("ILENGTH_NONNEG"));
    thm cons_length = apply_conversion(rewrite_conv(
        THM_LIST(get_theorem_by_name("ILENGTH_DEF"))),
        `ilength ((f_:cm_function_d) ::
          (rest_:(cm_function_d)list))`);
    add_fact_st(rest_length);
    add_fact_st(cons_length);
    cm_commit_arith_fact(
        "0i <= (index__pre:int) ==>"
        "index__pre =="
        " ilength (cm_program_functions (p:cm_program)) -"
        " ilength ((f_:cm_function_d) :: rest_) ==>"
        "ilength ((f_:cm_function_d) :: rest_) =="
        " 1i + ilength rest_ ==>"
        "0i <= ilength (rest_:(cm_function_d)list) ==>"
        "index__pre <"
        " ilength (cm_program_functions p)");

    thm wf = conv_rule(rewrite_conv(THM_LIST(
        get_cm_wf_program_def(),
        get_cm_codegen_admissible_def())),
        from_state_bool(`cm_wf_program (p:cm_program)`));
    thm typed = conv_rule(rewrite_conv(
        THM_LIST(get_cm_typed_program_def())),
        conjunct1_rule(wf));
    thm function_rule = conjunct1_rule(conjunct2_rule(
        conjunct2_rule(conjunct2_rule(typed))));
    thm function_wf = mp_rule(mp_rule(spec_rule(
        `index__pre:int`, function_rule),
        assume_rule(`0i <= (index__pre:int)`)),
        assume_rule(
          `(index__pre:int) <
           ilength (cm_program_functions (p:cm_program))`));
    thm function_model = conjunct1_rule(conv_rule(
        rewrite_conv(
          THM_LIST(get_cm_function_counts_representable_def())),
        function_counts));
    thm concrete_wf = conv_rule(
        rewrite_conv(THM_LIST(sym_rule(function_model))),
        function_wf);
    thm opened_wf = conv_rule(rewrite_conv(
        THM_LIST(get_cm_function_wf_def())), concrete_wf);
    thm stmt_wf = conjunct1_rule(conjunct2_rule(
        conjunct2_rule(conjunct2_rule(opened_wf))));
    add_fact_st(eqt_intro_rule(stmt_wf));
  }
  int head_count =
      cmc_function_code_count(program, index, fn);
  [[cst::proof]] {
    cm_retarget_call_result(`head_count__addr:addr`,
        assume_rule(
          `(retval:int) ==
           cm_function_code_count
             (p:cm_program) (index__pre:int)`));
    thm size_model = by_rewrite(
        `cm_functions_code_size (p:cm_program)
           ((f_:cm_function_d) ::
             (rest_:(cm_function_d)list))
           (index__pre:int) ==
         cm_function_code_count p index__pre +
         cm_functions_code_size p rest_ (index__pre + 1i)`,
        THM_LIST(get_cm_functions_code_size_def()));
    add_fact_st(size_model);
    add_fact_st(specl_rule(TERM_LIST(
        `rest_:(cm_function_d)list`, `p:cm_program`,
        `(index__pre:int) + 1i`),
        cm_functions_code_size_nonnegative));
    add_fact_st(specl_rule(TERM_LIST(
        `p:cm_program`, `index__pre:int`),
        cm_function_code_count_nonnegative));

    cm_commit_arith_fact(
        "0i <= (index__pre:int) ==>"
        "0i <= index__pre + 1i");
    cm_commit_arith_fact(
        "index__pre =="
        " ilength (cm_program_functions (p:cm_program)) -"
        " ilength ((f_:cm_function_d) :: rest_) ==>"
        "ilength ((f_:cm_function_d) :: rest_) =="
        " 1i + ilength (rest_:(cm_function_d)list) ==>"
        "index__pre + 1i =="
        " ilength (cm_program_functions p) - ilength rest_");
    cm_commit_arith_fact(
        "index__pre +"
        " ilength ((f_:cm_function_d) :: rest_) <="
        " 2147483647i ==>"
        "ilength ((f_:cm_function_d) :: rest_) =="
        " 1i + ilength (rest_:(cm_function_d)list) ==>"
        "(index__pre + 1i) + ilength rest_ <= 2147483647i");
    cm_commit_arith_fact(
        "0i <= cm_function_code_count"
        " (p:cm_program) index__pre ==>"
        "cm_functions_code_size p ((f_:cm_function_d) :: rest_)"
        " index__pre =="
        " cm_function_code_count p index__pre +"
        " cm_functions_code_size p rest_ (index__pre + 1i) ==>"
        "cm_functions_code_size p"
        " ((f_:cm_function_d) :: rest_) index__pre <="
        " 2147483647i ==>"
        "cm_functions_code_size p rest_ (index__pre + 1i)"
        " <= 2147483647i");
    term child =
        `cm_functions_code_size (p:cm_program)
          (rest_:(cm_function_d)list)
          ((index__pre:int) + 1i)`;
    thm child_bounds = conj_rule(
        assume_rule(mk_binop(`(<=):int->int->bool`,
          `0i:int`, child)),
        assume_rule(mk_binop(`(<=):int->int->bool`,
          child, `2147483647i:int`)));
    thm child_view = apply_conversion(
        rewrite_conv(THM_LIST(get_cm_i32_code_count_def())),
        mk_comb(`cm_i32_code_count:int->bool`, child));
    add_fact_st(eqt_intro_rule(
        eq_mp_rule(sym_rule(child_view), child_bounds)));

    thm function_view = apply_conversion(
        pure_rewrite_conv(THM_LIST(cm_function_context_rep_def)),
        `cm_function_context_rep (fn__pre:int)
          (f_:cm_function_d) (body_ptr_:int) (next_ptr_:int)`);
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        rename_exists_hconv(eq2ent(function_view),
          TERM_LIST(`params_ptr_head_:int`,
            `locals_ptr_head_:int`))));
  }
  struct cm_function *next = fn->next;
  int tail_count =
      cmc_functions_code_size_count(program, next, index + 1);
  [[cst::proof]] {
    thm tail_model = assume_rule(
        `(retval_1:int) ==
         cm_functions_code_size (p:cm_program)
           (rest_:(cm_function_d)list)
           ((index__pre:int) + 1i)`);
    cm_retarget_call_result(
        `tail_count__addr:addr`, tail_model);
    cm_add_count_facts(conv_rule(
        rewrite_conv(THM_LIST(tail_model)),
        from_state_bool(`cm_i32_code_count (retval_1:int)`)));
    cm_commit_arith_fact(
        "cm_functions_code_size (p:cm_program)"
        " ((f_:cm_function_d) :: rest_) index__pre =="
        " cm_function_code_count p index__pre +"
        " cm_functions_code_size p rest_ (index__pre + 1i) ==>"
        "cm_functions_code_size p"
        " ((f_:cm_function_d) :: rest_) index__pre <="
        " 2147483647i ==>"
        "cm_function_code_count p index__pre +"
        " cm_functions_code_size p rest_ (index__pre + 1i)"
        " <= 2147483647i");
    cm_commit_arith_fact(
        "0i <= cm_function_code_count"
        " (p:cm_program) index__pre ==>"
        "0i <= cm_functions_code_size p"
        " (rest_:(cm_function_d)list) (index__pre + 1i) ==> "
        "--2147483648i <="
        " cm_function_code_count p index__pre +"
        " cm_functions_code_size p rest_ (index__pre + 1i)");
  }
  int result = head_count + tail_count;
  [[cst::proof]] {
    term concrete =
        `cm_function_code_count (p:cm_program)
           (index__pre:int) +
         cm_functions_code_size p
           (rest_:(cm_function_d)list)
           ((index__pre:int) + 1i)`;
    thm model = by_rewrite(mk_eq(concrete,
        `cm_functions_code_size (p:cm_program)
          ((f_:cm_function_d) ::
            (rest_:(cm_function_d)list))
          (index__pre:int)`),
        THM_LIST(get_cm_functions_code_size_def()));
    add_fact_st(model);
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        cm_function_context_fold_hconv(
          `fn__pre:int`, `f_:cm_function_d`,
          `body_ptr_:int`, `next_ptr_:int`,
          `params_ptr_head_:int`, `locals_ptr_head_:int`)));
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        specl_rule(TERM_LIST(
            `fn__pre:int`, `f_:cm_function_d`,
            `rest_:(cm_function_d)list`,
            `body_ptr_:int`, `next_ptr_:int`),
            cm_function_context_cons_close)));
    substitute_st(sym_rule(assume_rule(
        `functions == (f_:cm_function_d) ::
          (rest_:(cm_function_d)list)`)));
    cm_commit_arith_fact(
        "0i <= cm_function_code_count"
        " (p:cm_program) (index__pre:int) ==>"
        "0i <= cm_functions_code_size p"
        " (rest_:(cm_function_d)list) (index__pre + 1i) ==>"
        "0i <= cm_function_code_count p index__pre +"
        " cm_functions_code_size p rest_ (index__pre + 1i)");
    thm concrete_bounds = conj_rule(
        assume_rule(mk_binop(`(<=):int->int->bool`,
          `0i:int`, concrete)),
        assume_rule(mk_binop(`(<=):int->int->bool`,
          concrete, `2147483647i:int`)));
    thm concrete_view = apply_conversion(
        rewrite_conv(THM_LIST(get_cm_i32_code_count_def())),
        mk_comb(`cm_i32_code_count:int->bool`, concrete));
    add_fact_st(eqt_intro_rule(
        eq_mp_rule(sym_rule(concrete_view), concrete_bounds)));
    term result_model =
        `cm_functions_code_size (p:cm_program)
          (functions:(cm_function_d)list) (index__pre:int)`;
    cm_keep_only_facts(TERM_LIST(
        `cm_wf_program (p:cm_program) <=> true`,
        `cm_rep_structs_safe
           (cm_program_structs (p:cm_program)) <=> true`,
        `0i <= (index__pre:int)`,
        `(index__pre:int) ==
           ilength (cm_program_functions (p:cm_program)) -
           ilength (functions:(cm_function_d)list)`,
        `(index__pre:int) +
           ilength (functions:(cm_function_d)list) <=
           2147483647i`,
        `cm_functions_counts_representable
           (p:cm_program) (functions:(cm_function_d)list)
           (index__pre:int) <=> true`,
        `cm_i32_code_count ${result_model:int} <=> true`,
        `${concrete:int} == ${result_model:int}`,
        `cm_i32_code_count ${concrete:int} <=> true`));
  }
  return result;
}

int cmc_model_code_length(struct cm_program *program)
    [[cst::param(`p:cm_program`, `functions_ptr:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(cm_rep_structs_safe
              (cm_program_structs p) <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_list_rep functions_ptr
         (cm_program_functions p)`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(cm_rep_structs_safe
              (cm_program_structs p) <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_list_rep functions_ptr
         (cm_program_functions p) **
       fact((__return:int) == cm_model_code_length p) **
       fact(cm_i32_code_count (__return:int) <=> true)`)]]
{
  [[cst::proof]] {
    thm program_view = apply_conversion(
        pure_rewrite_conv(THM_LIST(cm_program_context_rep_def)),
        `cm_program_context_rep (program__pre:int)
          (p:cm_program) (functions_ptr:int)`);
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        rename_exists_hconv(eq2ent(program_view),
          TERM_LIST(`structs_ptr_:int`, `globals_ptr_:int`,
            `strings_ptr_:int`))));
  }
  struct cm_function *functions = program->functions;
  [[cst::proof]] {
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        cm_program_context_fold_hconv(
          `program__pre:int`, `p:cm_program`,
          `functions_ptr:int`, `structs_ptr_:int`,
          `globals_ptr_:int`, `strings_ptr_:int`)));
    thm wf = conv_rule(rewrite_conv(THM_LIST(
        get_cm_wf_program_def(),
        get_cm_codegen_admissible_def())),
        from_state_bool(`cm_wf_program (p:cm_program)`));
    thm counts = conv_rule(rewrite_conv(
        THM_LIST(get_cm_codegen_counts_representable_def())),
        conjunct2_rule(conjunct2_rule(conjunct2_rule(
          conjunct2_rule(conjunct2_rule(conjunct2_rule(
            conjunct2_rule(conjunct2_rule(wf)))))))));
    add_fact_st(eqt_intro_rule(conjunct1_rule(counts)));
    thm code_lower = conjunct1_rule(conjunct2_rule(wf));
    thm code_upper =
        conjunct1_rule(conjunct2_rule(conjunct2_rule(wf)));
    thm code_bounds = conj_rule(code_lower, code_upper);
    thm code_view = apply_conversion(
        rewrite_conv(THM_LIST(get_cm_i32_code_count_def())),
        `cm_i32_code_count (cm_model_code_length (p:cm_program))`);
    add_fact_st(eqt_intro_rule(
        eq_mp_rule(sym_rule(code_view), code_bounds)));
    cm_add_count_facts(eqt_elim_rule(assume_rule(
        `cm_i32_code_count
          (cm_model_code_length (p:cm_program)) <=> true`)));
    add_fact_st(specl_rule(TERM_LIST(
        `cm_program_functions (p:cm_program)`,
        `p:cm_program`, `0i:int`),
        cm_functions_code_size_nonnegative));
    add_fact_st(specl_rule(TERM_LIST(
        `cm_program_functions (p:cm_program)`,
        `p:cm_program`, `0i:int`),
        cm_functions_length_le_code_size));
    thm length_model = by_rewrite(
        `cm_model_code_length (p:cm_program) ==
         11i + cm_functions_code_size p
           (cm_program_functions p) 0i`,
        THM_LIST(get_cm_model_code_length_def()));
    add_fact_st(length_model);
    cm_commit_arith_fact(
        "0i <= cm_functions_code_size (p:cm_program)"
        " (cm_program_functions p) 0i ==>"
        "cm_model_code_length p =="
        " 11i + cm_functions_code_size p"
        " (cm_program_functions p) 0i ==>"
        "cm_model_code_length p <= 2147483647i ==>"
        "cm_functions_code_size p"
        " (cm_program_functions p) 0i <= 2147483647i");
    term size =
        `cm_functions_code_size (p:cm_program)
          (cm_program_functions p) 0i`;
    thm size_bounds = conj_rule(
        assume_rule(mk_binop(`(<=):int->int->bool`,
          `0i:int`, size)),
        assume_rule(mk_binop(`(<=):int->int->bool`,
          size, `2147483647i:int`)));
    thm size_view = apply_conversion(
        rewrite_conv(THM_LIST(get_cm_i32_code_count_def())),
        mk_comb(`cm_i32_code_count:int->bool`, size));
    add_fact_st(eqt_intro_rule(
        eq_mp_rule(sym_rule(size_view), size_bounds)));
    add_fact_st(int_arith_rule(
        `0i <= (0i:int)`));
    cm_commit_arith_fact(
        "ilength (cm_program_functions (p:cm_program)) <="
        " cm_functions_code_size p (cm_program_functions p) 0i ==>"
        "cm_functions_code_size p (cm_program_functions p) 0i"
        " <= 2147483647i ==>"
        "0i + ilength (cm_program_functions p) <= 2147483647i");
    cm_commit_arith_fact(
        "0i =="
        " ilength (cm_program_functions (p:cm_program)) -"
        " ilength (cm_program_functions p)");
  }
  int functions_size =
      cmc_functions_code_size_count(program, functions, 0);
  [[cst::proof]] {
    thm size_model = assume_rule(
        `(retval:int) ==
         cm_functions_code_size (p:cm_program)
           (cm_program_functions p) 0i`);
    cm_retarget_call_result(
        `functions_size__addr:addr`, size_model);
    cm_add_count_facts(conv_rule(
        rewrite_conv(THM_LIST(size_model)),
        from_state_bool(`cm_i32_code_count (retval:int)`)));
    cm_commit_arith_fact(
        "cm_model_code_length (p:cm_program) =="
        " 11i + cm_functions_code_size p"
        " (cm_program_functions p) 0i ==>"
        "cm_model_code_length p <= 2147483647i ==>"
        "11i + cm_functions_code_size p"
        " (cm_program_functions p) 0i <= 2147483647i");
    cm_commit_arith_fact(
        "0i <= cm_functions_code_size (p:cm_program)"
        " (cm_program_functions p) 0i ==> "
        "--2147483648i <= 11i + cm_functions_code_size p"
        " (cm_program_functions p) 0i");
  }
  int result = 11 + functions_size;
  [[cst::proof]] {
    term concrete =
        `11i + cm_functions_code_size (p:cm_program)
          (cm_program_functions p) 0i`;
    thm model = by_rewrite(
        mk_eq(concrete,
          `cm_model_code_length (p:cm_program)`),
        THM_LIST(get_cm_model_code_length_def()));
    add_fact_st(model);
    cm_commit_arith_fact(
        "0i <= cm_functions_code_size (p:cm_program)"
        " (cm_program_functions p) 0i ==>"
        "0i <= 11i + cm_functions_code_size p"
        " (cm_program_functions p) 0i");
    thm concrete_bounds = conj_rule(
        assume_rule(mk_binop(`(<=):int->int->bool`,
          `0i:int`, concrete)),
        assume_rule(mk_binop(`(<=):int->int->bool`,
          concrete, `2147483647i:int`)));
    thm concrete_view = apply_conversion(
        rewrite_conv(THM_LIST(get_cm_i32_code_count_def())),
        mk_comb(`cm_i32_code_count:int->bool`, concrete));
    add_fact_st(eqt_intro_rule(
        eq_mp_rule(sym_rule(concrete_view), concrete_bounds)));
    cm_keep_only_facts(TERM_LIST(
        `cm_wf_program (p:cm_program) <=> true`,
        `cm_rep_structs_safe
           (cm_program_structs (p:cm_program)) <=> true`,
        `${concrete:int} == cm_model_code_length (p:cm_program)`,
        `cm_i32_code_count ${concrete:int} <=> true`));
  }
  return result;
}

int cmc_model_data_length(struct cm_program *program)
    [[cst::param(`p:cm_program`, `functions_ptr:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(cm_rep_globals_safe
              (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe
              (cm_program_strings p) <=> true) **
       fact(cm_model_data_length p ==
         (8i + cm_rep_globals_size
           (cm_program_globals p)) +
         cm_rep_strings_size
           (cm_program_strings p)) **
       cm_program_context_rep program p functions_ptr`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(cm_rep_globals_safe
              (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe
              (cm_program_strings p) <=> true) **
       fact(cm_model_data_length p ==
         (8i + cm_rep_globals_size
           (cm_program_globals p)) +
         cm_rep_strings_size
           (cm_program_strings p)) **
       cm_program_context_rep program p functions_ptr **
       fact((__return:int) == cm_model_data_length p) **
       fact(cm_i32_code_count (__return:int) <=> true)`)]]
{
  [[cst::proof]] {
    thm program_view = apply_conversion(
        pure_rewrite_conv(THM_LIST(cm_program_context_rep_def)),
        `cm_program_context_rep (program__pre:int)
          (p:cm_program) (functions_ptr:int)`);
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        rename_exists_hconv(eq2ent(program_view),
          TERM_LIST(`structs_ptr_:int`, `globals_ptr_:int`,
            `strings_ptr_:int`))));
  }
  struct cm_global *globals = program->globals;
  struct cm_string *strings = program->strings;
  long long global_size = cmc_globals_size(globals);
  [[cst::proof]] {
    thm global_model = assume_rule(
        `(retval:int) ==
         cm_rep_globals_size
           (cm_program_globals (p:cm_program))`);
    add_fact_st(conv_rule(rewrite_conv(THM_LIST(global_model)),
        assume_rule(`0i <= (retval:int)`)));
    add_fact_st(conv_rule(rewrite_conv(THM_LIST(global_model)),
        assume_rule(`(retval:int) <= 1048560i`)));
    cst_set_symbolic_state(retarget_cell64_st(
        cst_get_symbolic_state(), `global_size__addr:addr`,
        `retval:int`,
        `cm_rep_globals_size
          (cm_program_globals (p:cm_program))`));
  }
  long long string_size = cmc_strings_size(strings);
  [[cst::proof]] {
    thm string_model = assume_rule(
        `(retval_1:int) ==
         cm_rep_strings_size
           (cm_program_strings (p:cm_program))`);
    add_fact_st(conv_rule(rewrite_conv(THM_LIST(string_model)),
        assume_rule(`0i <= (retval_1:int)`)));
    add_fact_st(conv_rule(rewrite_conv(THM_LIST(string_model)),
        assume_rule(`(retval_1:int) <= 1048560i`)));
    cst_set_symbolic_state(retarget_cell64_st(
        cst_get_symbolic_state(), `string_size__addr:addr`,
        `retval_1:int`,
        `cm_rep_strings_size
          (cm_program_strings (p:cm_program))`));
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        cm_program_context_fold_hconv(
          `program__pre:int`, `p:cm_program`,
          `functions_ptr:int`, `structs_ptr_:int`,
          `globals_ptr_:int`, `strings_ptr_:int`)));
    thm wf = conv_rule(rewrite_conv(THM_LIST(
        get_cm_wf_program_def(),
        get_cm_codegen_admissible_def())),
        from_state_bool(`cm_wf_program (p:cm_program)`));
    thm data_lower = conjunct1_rule(conjunct2_rule(
        conjunct2_rule(conjunct2_rule(wf))));
    thm data_upper = conjunct1_rule(conjunct2_rule(
        conjunct2_rule(conjunct2_rule(
          conjunct2_rule(wf)))));
    add_fact_st(data_lower);
    add_fact_st(data_upper);
    cm_commit_arith_fact(
        "cm_model_data_length (p:cm_program) =="
        " (8i + cm_rep_globals_size (cm_program_globals p)) +"
        " cm_rep_strings_size (cm_program_strings p) ==>"
        "cm_model_data_length p <= 1048568i ==>"
        "(8i + cm_rep_globals_size (cm_program_globals p)) +"
        " cm_rep_strings_size (cm_program_strings p) <= 1048568i");
    cm_commit_arith_fact(
        "0i <= cm_rep_globals_size"
        " (cm_program_globals (p:cm_program)) ==>"
        "0i <= cm_rep_strings_size (cm_program_strings p) ==>"
        "0i <= (8i + cm_rep_globals_size"
        " (cm_program_globals p)) +"
        " cm_rep_strings_size (cm_program_strings p)");
  }
  long long total = 8LL + global_size;
  total = total + string_size;
  [[cst::proof]] {
    term concrete =
        `(8i + cm_rep_globals_size
          (cm_program_globals (p:cm_program))) +
         cm_rep_strings_size (cm_program_strings p)`;
    thm model = sym_rule(assume_rule(
        `cm_model_data_length (p:cm_program) ==
         (8i + cm_rep_globals_size
           (cm_program_globals p)) +
         cm_rep_strings_size (cm_program_strings p)`));
    add_fact_st(model);
    thm cast = mp_rule(mp_rule(spec_rule(concrete,
        cm_nonnegative_i32_cast),
        assume_rule(mk_binop(`(<=):int->int->bool`,
          `0i:int`, concrete))),
        mp_rule(int_arith_rule(
          `${concrete:int} <= 1048568i ==>
           ${concrete:int} <= 2147483647i`),
          assume_rule(mk_binop(`(<=):int->int->bool`,
            concrete, `1048568i:int`))));
    add_fact_st(cast);
  }
  int result = (int)total;
  [[cst::proof]] {
    term concrete =
        `(8i + cm_rep_globals_size
          (cm_program_globals (p:cm_program))) +
         cm_rep_strings_size (cm_program_strings p)`;
    thm concrete_bounds = conj_rule(
        assume_rule(mk_binop(`(<=):int->int->bool`,
          `0i:int`, concrete)),
        mp_rule(int_arith_rule(
          `${concrete:int} <= 1048568i ==>
           ${concrete:int} <= 2147483647i`),
          assume_rule(mk_binop(`(<=):int->int->bool`,
            concrete, `1048568i:int`))));
    thm concrete_view = apply_conversion(
        rewrite_conv(THM_LIST(get_cm_i32_code_count_def())),
        mk_comb(`cm_i32_code_count:int->bool`, concrete));
    add_fact_st(eqt_intro_rule(
        eq_mp_rule(sym_rule(concrete_view), concrete_bounds)));
    cm_keep_only_facts(TERM_LIST(
        `cm_wf_program (p:cm_program) <=> true`,
        `cm_rep_globals_safe
           (cm_program_globals (p:cm_program)) <=> true`,
        `cm_rep_strings_safe
           (cm_program_strings (p:cm_program)) <=> true`,
        `cm_model_data_length (p:cm_program) ==
           (8i + cm_rep_globals_size
             (cm_program_globals p)) +
           cm_rep_strings_size (cm_program_strings p)`,
        `${concrete:int} == cm_model_data_length (p:cm_program)`,
        `cm_i32_code_count ${concrete:int} <=> true`));
  }
  return result;
}


PROOF thm cm_concrete_function_ready_def = new_fun_definition(
    `cm_concrete_function_ready (p:cm_program) (fid:int)
       (f:cm_function_d) : bool =
       (f == inth fid (cm_program_functions p) &&
        cm_function_counts_representable p fid f &&
        cm_stmt_wf p f F (cm_function_body f) &&
        cm_stmt_counts_representable p fid (cm_function_body f) &&
        cm_param_counts_representable (cm_function_params f) &&
        cm_i32_code_count (cm_function_prologue_count f) &&
        cm_i32_code_count (cm_function_pc p fid) &&
        cm_i32_code_count
          (cm_function_pc p fid + cm_function_prologue_count f) &&
        cm_i32_code_count
          ((cm_function_pc p fid + cm_function_prologue_count f) +
           ilength
             (cm_emit_stmt p fid
               (cm_function_pc p fid +
                cm_function_prologue_count f)
               0i 0i 0i (cm_function_body f))) &&
        cm_slots_wf (cm_program_structs p) (cm_function_params f) &&
        cm_slots_wf (cm_program_structs p) (cm_function_locals f) &&
        cm_rep_members_safe (cm_function_params f) &&
        cm_rep_members_safe (cm_function_locals f) &&
        cm_rep_stmt_temps_safe (cm_function_body f) &&
        8i + cm_rep_members_size (cm_function_params f) +
          cm_rep_members_size (cm_function_locals f) +
          8i * cm_stemps (cm_function_body f) <= 2147483647i &&
        cm_temp_offset p fid (cm_stemps (cm_function_body f)) <=
          2147483647i &&
        cm_function_pc p (fid + 1i) ==
          cm_function_pc p fid + cm_function_code_count p fid &&
        cm_i32_code_count (cm_function_pc p (fid + 1i)))`);
PROOF int _e_cm_concrete_function_ready =
    cst_add_const_to_header(`cm_concrete_function_ready`);

PROOF thm cm_concrete_functions_ready_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p fid.
       cm_concrete_functions_ready (p:cm_program) (fid:int)
         ([]:(cm_function_d)list) = T) &&
     (!p fid f rest.
       (cm_concrete_functions_ready (p:cm_program) (fid:int)
          ((f:cm_function_d) :: (rest:(cm_function_d)list)) <=>
        cm_i32_code_count (fid + 1i) &&
        cm_concrete_function_ready p fid f &&
        cm_concrete_functions_ready p (fid + 1i) rest))`);
PROOF int _e_cm_concrete_functions_ready =
    cst_add_const_to_header(`cm_concrete_functions_ready`);

PROOF thm get_cm_concrete_function_ready_def(void) {
  return cm_concrete_function_ready_def;
}

PROOF thm get_cm_concrete_functions_ready_def(void) {
  return cm_concrete_functions_ready_def;
}
