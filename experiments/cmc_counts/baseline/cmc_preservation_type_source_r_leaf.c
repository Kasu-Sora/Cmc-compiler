#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_type_source_r_leaf.h"

#require "cmc_preservation_type_cursor.c"
#require "cmc_preservation_type_value.c"
#require "cmc_preservation_source_conditions.c"

PROOF static size_t _cmc_preservation_type_source_r_leaf_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_tsrl_pick_conjunct(thm fact, term wanted) {
  if (alpha_compare(concl(fact), wanted) == 0) return fact;
  if (!is_conj(concl(fact))) return empty_theorem;
  thm left = cm_tsrl_pick_conjunct(conjunct1_rule(fact), wanted);
  if (!IS_NULL(left)) return left;
  return cm_tsrl_pick_conjunct(conjunct2_rule(fact), wanted);
}

PROOF static thm cm_prove_const_expr_value_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (f:cm_function_d) (st:cm_src_state)
         (n:int) (ty:cm_type).
         cm_expr_wf p f (CMConstE n ty) ==>
         cm_expr_value_type_ready (CMConstE n ty)
           (cm_convert_value st ty (CMIntV n))`);
  gnode_list type_cases = INDUCT_TAC(root, `ty:cm_type`);
  for (size_t i = 0; i < vector_size(type_cases); ++i) {
    if (i == 0) {
      gnode leaf = AUTO_INTROS_TAC(type_cases[i]);
      thm integer = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(get_cm_integer_type_def())),
          `cm_integer_type CMIntTy`));
      thm compatible = mp_rule(specl_rule(TERM_LIST(
          `st:cm_src_state`, `n:int`, `CMIntTy`),
          cm_const_value_type_ready), integer);
      term zero_term =
          `cm_zero_literal (CMConstE (n:int) CMIntTy)`;
      thm zero_assumed = assume_rule(zero_term);
      thm n_zero = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_cm_zero_literal_def(),
          get_datatype_injectivity("cm_expr"))), zero_assumed);
      term value_equal_term =
          `cm_convert_value (st:cm_src_state) CMIntTy (CMIntV (n:int)) ==
           CMIntV 0i`;
      thm first = apply_conversion(reduce_rewrite_conv(THM_LIST(
          n_zero, get_cm_convert_value_def(), get_cm_value_number_def(),
          get_tower_wrap64_def(), get_cm_integer_type_def(),
          get_cm_is_pointer_def(), get_theorem_by_name("COND_CLAUSES"))),
          value_equal_term);
      thm value_equal = eqt_elim_rule(trans_rule(first,
          apply_conversion(get_conversion_by_name("NUM_REDUCE_CONV"),
            rhs_of(first))));
      thm zero_clause = disch_rule(zero_term, value_equal);
      thm opened = conj_rule(compatible, zero_clause);
      thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
          get_cm_expr_value_type_ready_def(), get_cm_expr_type_def())),
          goal_ccl(leaf->g));
      ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), opened));
    } else {
      thm view = apply_conversion(reduce_rewrite_conv(THM_LIST(
          get_cm_expr_wf_def(), get_cm_expr_value_type_ready_def(),
          get_cm_value_type_compatible_def(), get_cm_zero_literal_def(),
          get_cm_expr_type_def(), get_cm_integer_type_def(),
          get_cm_convert_value_def(), get_cm_value_number_def(),
          get_cm_value_type_def(), get_cm_is_pointer_def(),
          get_tower_wrap64_def(), get_datatype_distinctness("cm_type"),
          get_datatype_injectivity("cm_type"),
          get_datatype_distinctness("cm_value"),
          get_datatype_distinctness("cm_expr"),
          get_datatype_injectivity("cm_expr"),
          get_datatype_injectivity("cm_value"),
          get_theorem_by_name("COND_CLAUSES"))),
          goal_ccl(type_cases[i]->g));
      ACCEPT_TAC(type_cases[i], eqt_elim_rule(view));
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_const_expr_value_ready =
    cm_prove_const_expr_value_ready();

PROOF static thm cm_prove_r_const_type_ready_step(void) {
  term expression = `CMConstE (n:int) (ty:cm_type)`;
  term task =
      `CMRTask (q:cm_program) (fid:int) ${expression:cm_expr}
        (st:cm_src_state) (ks:(cm_frame)list)`;
  term value = `cm_convert_value (st:cm_src_state) (ty:cm_type)
      (CMIntV (n:int))`;
  term next_ann =
      `cm_ann_linear
        (cm_push_code (cm_const_immediate (ty:cm_type) (n:int)))
        (ann:cm_annotation)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (q:cm_program) (fid:int) (n:int)
         (ty:cm_type) (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         cm_task_succeeds
           (CMRTask q fid (CMConstE n ty) st ks) ==>
         cm_task_type_ready p
           (CMRTask q fid (CMConstE n ty) st ks) ann ==>
         cm_task_type_ready p
           (cm_step (CMRTask q fid (CMConstE n ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask q fid (CMConstE n ty) st ks) ann))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm task_ready = assume_rule(
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        (ann:cm_annotation)`);
  thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_task_type_ready_def())), task_ready);
  thm expression_wf = cm_tsrl_pick_conjunct(opened,
      `cm_expr_wf (p:cm_program)
        (inth (fid:int) (cm_program_functions p))
        ${expression:cm_expr}`);
  thm value_ready = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`,
      `inth (fid:int) (cm_program_functions (p:cm_program))`,
      `st:cm_src_state`, `n:int`, `ty:cm_type`),
      cm_const_expr_value_ready), expression_wf);
  thm cursor_equal = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_ann_linear_def, cm_ann_plain_def, cm_ann_cursors_def)),
      `cm_ann_cursors ${next_ann:cm_annotation} ==
       cm_ann_cursors (ann:cm_annotation)`));
  thm result = mp_rule(mp_rule(mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `q:cm_program`, `fid:int`, expression,
      `st:cm_src_state`, `ks:(cm_frame)list`, `ann:cm_annotation`,
      value, `st:cm_src_state`, next_ann), cm_r_value_task_ready),
      task_ready), value_ready), cursor_equal);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_step_def(), get_cm_rstart_def(), cm_annotation_step_def,
      cm_update_r_def, cm_update_annotation_def)), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), result));
  return gnode_prove(root);
}
PROOF thm cm_r_const_type_ready_step =
    cm_prove_r_const_type_ready_step();

PROOF static thm cm_prove_string_expr_value_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (q:cm_program) (f:cm_function_d)
         (sid:int) (ty:cm_type).
         cm_expr_wf p f (CMStringE sid ty) ==>
         cm_expr_value_type_ready (CMStringE sid ty)
           (cm_string_pointer q sid)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm wf_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_expr_wf_def())), assume_rule(
      `cm_expr_wf (p:cm_program) (f:cm_function_d)
        (CMStringE (sid:int) (ty:cm_type))`));
  thm type_equal = cm_tsrl_pick_conjunct(wf_open,
      `(ty:cm_type) == CMPtrTy CMCharTy`);
  thm compatible = specl_rule(TERM_LIST(
      `q:cm_program`, `sid:int`), cm_string_value_type_ready);
  compatible = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(type_equal))), compatible);
  thm zero_clause = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_zero_literal_def(),
        get_datatype_distinctness("cm_expr"))),
      `cm_zero_literal (CMStringE (sid:int) (ty:cm_type)) ==>
       cm_string_pointer (q:cm_program) sid == CMIntV 0i`));
  thm opened = conj_rule(compatible, zero_clause);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_expr_value_type_ready_def(), get_cm_expr_type_def())),
      goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), opened));
  return gnode_prove(root);
}
PROOF static thm cm_string_expr_value_ready =
    cm_prove_string_expr_value_ready();

PROOF static thm cm_prove_r_string_type_ready_step(void) {
  term expression = `CMStringE (sid:int) (ty:cm_type)`;
  term task =
      `CMRTask (q:cm_program) (fid:int) ${expression:cm_expr}
        (st:cm_src_state) (ks:(cm_frame)list)`;
  term value = `cm_string_pointer (q:cm_program) (sid:int)`;
  term next_ann =
      `cm_ann_linear
        (cm_push_code (cm_string_address (q:cm_program) (sid:int)))
        (ann:cm_annotation)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (q:cm_program) (fid:int) (sid:int)
         (ty:cm_type) (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         cm_task_succeeds
           (CMRTask q fid (CMStringE sid ty) st ks) ==>
         cm_task_type_ready p
           (CMRTask q fid (CMStringE sid ty) st ks) ann ==>
         cm_task_type_ready p
           (cm_step (CMRTask q fid (CMStringE sid ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask q fid (CMStringE sid ty) st ks) ann))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm task_ready = assume_rule(
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        (ann:cm_annotation)`);
  thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_task_type_ready_def())), task_ready);
  thm expression_wf = cm_tsrl_pick_conjunct(opened,
      `cm_expr_wf (p:cm_program)
        (inth (fid:int) (cm_program_functions p))
        ${expression:cm_expr}`);
  thm value_ready = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `q:cm_program`,
      `inth (fid:int) (cm_program_functions (p:cm_program))`,
      `sid:int`, `ty:cm_type`), cm_string_expr_value_ready),
      expression_wf);
  thm cursor_equal = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_ann_linear_def, cm_ann_plain_def, cm_ann_cursors_def)),
      `cm_ann_cursors ${next_ann:cm_annotation} ==
       cm_ann_cursors (ann:cm_annotation)`));
  thm result = mp_rule(mp_rule(mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `q:cm_program`, `fid:int`, expression,
      `st:cm_src_state`, `ks:(cm_frame)list`, `ann:cm_annotation`,
      value, `st:cm_src_state`, next_ann), cm_r_value_task_ready),
      task_ready), value_ready), cursor_equal);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_step_def(), get_cm_rstart_def(), cm_annotation_step_def,
      cm_update_r_def, cm_update_annotation_def)), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), result));
  return gnode_prove(root);
}
PROOF thm cm_r_string_type_ready_step =
    cm_prove_r_string_type_ready_step();

PROOF static thm cm_prove_sizeof_expr_value_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (f:cm_function_d) (asked:cm_type)
         (ty:cm_type) (n:int).
         cm_expr_wf p f (CMSizeofE asked ty) ==>
         cm_expr_value_type_ready (CMSizeofE asked ty) (CMIntV n)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm wf_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_expr_wf_def())), assume_rule(
      `cm_expr_wf (p:cm_program) (f:cm_function_d)
        (CMSizeofE (asked:cm_type) (ty:cm_type))`));
  thm type_equal = cm_tsrl_pick_conjunct(wf_open,
      `(ty:cm_type) == CMIntTy`);
  thm compatible = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_value_type_compatible_def(), get_cm_value_type_def(),
        get_cm_is_pointer_def(), get_datatype_distinctness("cm_type"),
        get_datatype_distinctness("cm_value"))),
      `cm_value_type_compatible (CMIntV (n:int)) CMIntTy`));
  compatible = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(type_equal))), compatible);
  thm zero_clause = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_zero_literal_def(),
        get_datatype_distinctness("cm_expr"))),
      `cm_zero_literal
         (CMSizeofE (asked:cm_type) (ty:cm_type)) ==>
       CMIntV (n:int) == CMIntV 0i`));
  thm opened = conj_rule(compatible, zero_clause);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_expr_value_type_ready_def(), get_cm_expr_type_def())),
      goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), opened));
  return gnode_prove(root);
}
PROOF static thm cm_sizeof_expr_value_ready =
    cm_prove_sizeof_expr_value_ready();

PROOF static thm cm_prove_r_sizeof_type_ready_step(void) {
  term expression = `CMSizeofE (asked:cm_type) (ty:cm_type)`;
  term task =
      `CMRTask (q:cm_program) (fid:int) ${expression:cm_expr}
        (st:cm_src_state) (ks:(cm_frame)list)`;
  term value =
      `CMIntV (cm_type_size
        (cm_program_structs (q:cm_program)) (asked:cm_type))`;
  term next_ann =
      `cm_ann_linear
        (cm_push_code
          (cm_type_size (cm_program_structs (q:cm_program))
            (asked:cm_type)))
        (ann:cm_annotation)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (q:cm_program) (fid:int) (asked:cm_type)
         (ty:cm_type) (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         cm_task_succeeds
           (CMRTask q fid (CMSizeofE asked ty) st ks) ==>
         cm_task_type_ready p
           (CMRTask q fid (CMSizeofE asked ty) st ks) ann ==>
         cm_task_type_ready p
           (cm_step (CMRTask q fid (CMSizeofE asked ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask q fid (CMSizeofE asked ty) st ks) ann))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm task_ready = assume_rule(
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        (ann:cm_annotation)`);
  thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_task_type_ready_def())), task_ready);
  thm expression_wf = cm_tsrl_pick_conjunct(opened,
      `cm_expr_wf (p:cm_program)
        (inth (fid:int) (cm_program_functions p))
        ${expression:cm_expr}`);
  thm value_ready = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`,
      `inth (fid:int) (cm_program_functions (p:cm_program))`,
      `asked:cm_type`, `ty:cm_type`,
      `cm_type_size (cm_program_structs (q:cm_program))
        (asked:cm_type)`), cm_sizeof_expr_value_ready), expression_wf);
  thm cursor_equal = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_ann_linear_def, cm_ann_plain_def, cm_ann_cursors_def)),
      `cm_ann_cursors ${next_ann:cm_annotation} ==
       cm_ann_cursors (ann:cm_annotation)`));
  thm result = mp_rule(mp_rule(mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `q:cm_program`, `fid:int`, expression,
      `st:cm_src_state`, `ks:(cm_frame)list`, `ann:cm_annotation`,
      value, `st:cm_src_state`, next_ann), cm_r_value_task_ready),
      task_ready), value_ready), cursor_equal);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_step_def(), get_cm_rstart_def(), cm_annotation_step_def,
      cm_update_r_def, cm_update_annotation_def)), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), result));
  return gnode_prove(root);
}
PROOF thm cm_r_sizeof_type_ready_step =
    cm_prove_r_sizeof_type_ready_step();

PROOF static thm cm_prove_getc_expr_value_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (f:cm_function_d) (ty:cm_type) (n:int).
         cm_expr_wf p f (CMGetcE ty) ==>
         cm_expr_value_type_ready (CMGetcE ty) (CMIntV n)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm wf_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_expr_wf_def())), assume_rule(
      `cm_expr_wf (p:cm_program) (f:cm_function_d)
        (CMGetcE (ty:cm_type))`));
  thm compatible = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_value_type_compatible_def(), get_cm_value_type_def(),
        get_cm_is_pointer_def(), get_datatype_distinctness("cm_type"),
        get_datatype_distinctness("cm_value"))),
      `cm_value_type_compatible (CMIntV (n:int)) CMIntTy`));
  compatible = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(wf_open))), compatible);
  thm zero_clause = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_zero_literal_def(),
        get_datatype_distinctness("cm_expr"))),
      `cm_zero_literal (CMGetcE (ty:cm_type)) ==>
       CMIntV (n:int) == CMIntV 0i`));
  thm opened = conj_rule(compatible, zero_clause);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_expr_value_type_ready_def(), get_cm_expr_type_def())),
      goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), opened));
  return gnode_prove(root);
}
PROOF static thm cm_getc_expr_value_ready =
    cm_prove_getc_expr_value_ready();

PROOF static thm cm_prove_r_getc_type_ready_step(void) {
  term expression = `CMGetcE (ty:cm_type)`;
  term task =
      `CMRTask (q:cm_program) (fid:int) ${expression:cm_expr}
        (st:cm_src_state) (ks:(cm_frame)list)`;
  term next_ann =
      `cm_ann_plain (cm_ann_pc (ann:cm_annotation) + 1i)
        (cm_ann_temp ann) (cm_ann_break ann)
        (cm_ann_continue ann) ann`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (q:cm_program) (fid:int) (ty:cm_type)
         (st:cm_src_state) (ks:(cm_frame)list) (ann:cm_annotation).
         cm_task_succeeds
           (CMRTask q fid (CMGetcE ty) st ks) ==>
         cm_task_type_ready p
           (CMRTask q fid (CMGetcE ty) st ks) ann ==>
         cm_task_type_ready p
           (cm_step (CMRTask q fid (CMGetcE ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask q fid (CMGetcE ty) st ks) ann))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm succeeds = assume_rule(`cm_task_succeeds ${task:cm_task}`);
  thm task_ready = assume_rule(
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        (ann:cm_annotation)`);
  thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_task_type_ready_def())), task_ready);
  thm expression_wf = cm_tsrl_pick_conjunct(opened,
      `cm_expr_wf (p:cm_program)
        (inth (fid:int) (cm_program_functions p))
        ${expression:cm_expr}`);
  thm input_ready = mp_rule(specl_rule(TERM_LIST(
      `q:cm_program`, `fid:int`, `ty:cm_type`, `st:cm_src_state`,
      `ks:(cm_frame)list`), cm_r_getc_succeeds_input), succeeds);
  thm cursor_equal = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_ann_plain_def, cm_ann_cursors_def)),
      `cm_ann_cursors ${next_ann:cm_annotation} ==
       cm_ann_cursors (ann:cm_annotation)`));
  gnode_list empty_cases = BOOL_CASES_TAC(
      leaf, `cm_state_input (st:cm_src_state) == []`, "Hempty");
  for (size_t i = 0; i < vector_size(empty_cases); ++i) {
    thm empty_fact = assume_rule(i == 0
        ? `cm_state_input (st:cm_src_state) == []`
        : `~(cm_state_input (st:cm_src_state) == [])`);
    term number = i == 0
        ? `--1i`
        : `HD (cm_state_input (st:cm_src_state))`;
    term next_state = i == 0
        ? `st:cm_src_state`
        : `cm_state_io (st:cm_src_state)
            (TL (cm_state_input st)) (cm_state_output st)`;
    thm value_ready = mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`,
        `inth (fid:int) (cm_program_functions (p:cm_program))`,
        `ty:cm_type`, number), cm_getc_expr_value_ready),
        expression_wf);
    thm result = mp_rule(mp_rule(mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `q:cm_program`, `fid:int`, expression,
        `st:cm_src_state`, `ks:(cm_frame)list`, `ann:cm_annotation`,
        mk_comb(`CMIntV`, number), next_state, next_ann),
        cm_r_value_task_ready), task_ready), value_ready), cursor_equal);
    thm_list rules = THM_LIST(
        empty_fact, get_cm_step_def(), get_cm_rstart_def(),
        cm_annotation_step_def, cm_update_r_def,
        cm_update_annotation_def, get_theorem_by_name("COND_CLAUSES"));
    if (i == 1) {
      thm byte_ready = mp_rule(mp_rule(taut_rule(
          `(cm_state_input (st:cm_src_state) == [] ||
            tower_byte_value (HD (cm_state_input st))) ==>
           ~(cm_state_input st == []) ==>
           tower_byte_value (HD (cm_state_input st))`),
          input_ready), empty_fact);
      vector_add(&rules, byte_ready);
    }
    thm target_view = apply_conversion(reduce_rewrite_conv(rules),
        goal_ccl(empty_cases[i]->g));
    ACCEPT_TAC(empty_cases[i],
        eq_mp_rule(sym_rule(target_view), result));
  }
  return gnode_prove(root);
}
PROOF thm cm_r_getc_type_ready_step =
    cm_prove_r_getc_type_ready_step();

PROOF static int cmc_preservation_type_source_r_leaf_final_checks(void) {
  ENSURE_COND(vector_size(hyp(cm_r_const_type_ready_step)) == 0 &&
      vector_size(hyp(cm_r_string_type_ready_step)) == 0 &&
      vector_size(hyp(cm_r_sizeof_type_ready_step)) == 0 &&
      vector_size(hyp(cm_r_getc_type_ready_step)) == 0,
      "rvalue leaf type-step theorem has assumptions");
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_type_source_r_leaf_axioms_before,
      "cmc_preservation_type_source_r_leaf introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_type_source_r_leaf_checks =
    cmc_preservation_type_source_r_leaf_final_checks();
