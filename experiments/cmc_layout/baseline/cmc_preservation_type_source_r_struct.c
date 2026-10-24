#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_type_source_r_struct.h"
#include "cmc_preservation_ready_coordinate.h"
#include "cmc_preservation_type_value.h"

#require "cmc_preservation_type_source_r_var.c"

PROOF static size_t _cmc_preservation_type_source_r_struct_axioms_before =
    vector_size(get_all_axioms());

PROOF static bool cm_tsrs_has_conjunct(term fact, term wanted) {
  if (alpha_compare(fact, wanted) == 0) return true;
  if (!is_conj(fact)) return false;
  struct dest_conj_results parts = dest_conj(fact);
  return cm_tsrs_has_conjunct(parts.tm1, wanted) ||
      cm_tsrs_has_conjunct(parts.tm2, wanted);
}

PROOF static thm cm_tsrs_pick_conjunct(thm fact, term wanted) {
  if (alpha_compare(concl(fact), wanted) == 0) return fact;
  struct dest_conj_results parts = dest_conj(concl(fact));
  return cm_tsrs_has_conjunct(parts.tm1, wanted)
      ? cm_tsrs_pick_conjunct(conjunct1_rule(fact), wanted)
      : cm_tsrs_pick_conjunct(conjunct2_rule(fact), wanted);
}

PROOF static thm cm_tsrs_parent_nonzero(term expression) {
  return eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_zero_literal_def(),
        get_datatype_distinctness("cm_expr"))),
      `~cm_zero_literal ${expression:cm_expr}`));
}

PROOF static thm cm_tsrs_phase_results(
    term phase, term expression, thm_list facts) {
  thm_list rules = THM_LIST(
      get_cm_phase_result_type_def(), get_cm_expr_type_def());
  for (size_t i = 0; i < vector_size(facts); ++i) {
    vector_add(&rules, facts[i]);
  }
  return eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(rules),
      `!(result_ty:cm_type).
         cm_phase_result_type (p:cm_program) (fid:int)
           ${phase:cm_aphase} result_ty ==>
         result_ty == cm_expr_type ${expression:cm_expr}`));
}

PROOF static thm cm_prove_r_assign_type_ready_step(void) {
  term expression =
      `CMAssignE (dst:cm_expr) (src:cm_expr) (ty:cm_type)`;
  term task =
      `CMRTask (q:cm_program) (fid:int) ${expression:cm_expr}
        (st:cm_src_state) (ks:(cm_frame)list)`;
  term function =
      `inth (fid:int) (cm_program_functions (p:cm_program))`;
  term phase = `CAAssignLP (src:cm_expr) (ty:cm_type)`;
  term output =
      `cm_lvalue_output_type (p:cm_program) ${function:cm_function_d}
        (dst:cm_expr)`;
  term old_cursors = `cm_ann_cursors (ann:cm_annotation)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (q:cm_program) (fid:int)
         (dst:cm_expr) (src:cm_expr) (ty:cm_type)
         (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         cm_typed_program p ==>
         cm_task_succeeds
           (CMRTask q fid (CMAssignE dst src ty) st ks) ==>
         cm_task_type_ready p
           (CMRTask q fid (CMAssignE dst src ty) st ks) ann ==>
         cm_task_type_ready p
           (cm_step (CMRTask q fid (CMAssignE dst src ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask q fid (CMAssignE dst src ty) st ks) ann))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm task_ready = assume_rule(
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        (ann:cm_annotation)`);
  thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_task_type_ready_def())), task_ready);
  thm same_program = cm_tsrs_pick_conjunct(
      opened, `(q:cm_program) == (p:cm_program)`);
  thm fid_low = cm_tsrs_pick_conjunct(opened, `0i <= (fid:int)`);
  thm fid_high = cm_tsrs_pick_conjunct(opened,
      `(fid:int) < ilength (cm_program_functions (p:cm_program))`);
  thm expression_wf = cm_tsrs_pick_conjunct(opened,
      `cm_expr_wf (p:cm_program) ${function:cm_function_d}
        ${expression:cm_expr}`);
  thm expression_scalar = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_expr_type_def())), cm_tsrs_pick_conjunct(opened,
        `cm_scalar_expr_type (cm_expr_type ${expression:cm_expr})`));
  thm parent_input = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_expr_type_def())), cm_tsrs_pick_conjunct(opened,
        `cm_cursor_head_input_type_ready (p:cm_program) (fid:int)
          (cm_expr_type ${expression:cm_expr})
          ${old_cursors:(cm_acursor)list}`));
  thm wf_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_expr_wf_def())), expression_wf);
  thm dst_wf = cm_tsrs_pick_conjunct(wf_open,
      `cm_expr_wf (p:cm_program) ${function:cm_function_d}
        (dst:cm_expr)`);
  thm src_wf = cm_tsrs_pick_conjunct(wf_open,
      `cm_expr_wf (p:cm_program) ${function:cm_function_d}
        (src:cm_expr)`);
  thm dst_lvalue = cm_tsrs_pick_conjunct(
      wf_open, `cm_lvalue (dst:cm_expr)`);
  thm dst_nonarray = cm_tsrs_pick_conjunct(wf_open,
      `~cm_expr_array (p:cm_program) ${function:cm_function_d}
        (dst:cm_expr)`);
  thm result_type = cm_tsrs_pick_conjunct(
      wf_open, `(ty:cm_type) == cm_expr_type (dst:cm_expr)`);
  thm src_convertible = cm_tsrs_pick_conjunct(wf_open,
      `cm_expr_convertible (src:cm_expr) (ty:cm_type)`);
  thm output_equal = mp_rule(mp_rule(mp_rule(mp_rule(mp_rule(
      specl_rule(TERM_LIST(`dst:cm_expr`, `p:cm_program`, `fid:int`),
        cm_nonarray_lvalue_output_type),
      assume_rule(`cm_typed_program (p:cm_program)`)), fid_low),
      fid_high), dst_wf), dst_lvalue);
  output_equal = mp_rule(output_equal, dst_nonarray);
  output_equal = trans_rule(output_equal,
      beta_norm(ap_term_rule(`\source:cm_type. CMPtrTy source`,
        sym_rule(result_type))));
  thm phase_static = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_static_type_ready_def(), src_wf,
        src_convertible, expression_scalar)),
      `cm_phase_static_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase}`));
  thm phase_parent = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_parent_type_ready_def(), parent_input)),
      `cm_phase_parent_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase} ${old_cursors:(cm_acursor)list}`));
  thm next_fid = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(cm_phase_next_fid_def)),
      `cm_phase_next_fid (fid:int) ${phase:cm_aphase} == fid`));
  thm phase_input = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_input_type_ready_def(), output_equal)),
      `cm_phase_input_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase} ${output:cm_type}`));
  thm phase_lvalue = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_lvalue_type_ready_def(),
        get_cm_phase_value_type_ready_def(), output_equal)),
      `cm_phase_lvalue_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase} ${output:cm_type}`));
  thm parent_nonzero = cm_tsrs_parent_nonzero(expression);
  thm phase_results =
      cm_tsrs_phase_results(phase, expression, THM_LIST());
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `q:cm_program`, `fid:int`, expression,
      `dst:cm_expr`, `st:cm_src_state`, `ks:(cm_frame)list`,
      `CMAssignLK (src:cm_expr) (ty:cm_type)`,
      `ann:cm_annotation`, phase), cm_l_push_task_ready);
  thm_list premises = THM_LIST(task_ready, parent_nonzero,
      phase_results, dst_wf, dst_lvalue, phase_static,
      phase_parent, next_fid, phase_input, phase_lvalue);
  for (size_t i = 0; i < vector_size(premises); ++i) {
    result = mp_rule(result, premises[i]);
  }
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      same_program, get_cm_step_def(), get_cm_rstart_def(),
      cm_annotation_step_def, cm_update_r_def,
      cm_update_annotation_def)), goal_ccl(leaf->g));
  result = conv_rule(rewrite_conv(THM_LIST(same_program)), result);
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), result));
  return gnode_prove(root);
}
PROOF thm cm_r_assign_type_ready_step =
    cm_prove_r_assign_type_ready_step();

PROOF static thm cm_tsrs_last_conjunct(thm fact) {
  thm current = fact;
  while (is_conj(concl(current))) {
    current = conjunct2_rule(current);
  }
  return current;
}

PROOF static thm cm_tsrs_binary_integer_scalars(thm mode) {
  thm left_integer = cm_tsrs_pick_conjunct(
      mode, `cm_integer_type (left_ty:cm_type)`);
  thm right_integer = cm_tsrs_pick_conjunct(
      mode, `cm_integer_type (right_ty:cm_type)`);
  return conj_rule(
      mp_rule(spec_rule(`left_ty:cm_type`, cm_integer_expr_type),
        left_integer),
      mp_rule(spec_rule(`right_ty:cm_type`, cm_integer_expr_type),
        right_integer));
}

PROOF static thm cm_tsrs_binary_left_pointer_scalars(thm mode) {
  thm left_pointer = cm_tsrs_pick_conjunct(
      mode, `cm_is_pointer (left_ty:cm_type)`);
  thm right_integer = cm_tsrs_pick_conjunct(
      mode, `cm_integer_type (right_ty:cm_type)`);
  return conj_rule(
      mp_rule(spec_rule(`left_ty:cm_type`, cm_pointer_expr_type),
        left_pointer),
      mp_rule(spec_rule(`right_ty:cm_type`, cm_integer_expr_type),
        right_integer));
}

PROOF static thm cm_tsrs_binary_right_pointer_scalars(thm mode) {
  thm left_integer = cm_tsrs_pick_conjunct(
      mode, `cm_integer_type (left_ty:cm_type)`);
  thm right_pointer = cm_tsrs_pick_conjunct(
      mode, `cm_is_pointer (right_ty:cm_type)`);
  return conj_rule(
      mp_rule(spec_rule(`left_ty:cm_type`, cm_integer_expr_type),
        left_integer),
      mp_rule(spec_rule(`right_ty:cm_type`, cm_pointer_expr_type),
        right_pointer));
}

PROOF static thm cm_tsrs_binary_equal_pointer_scalars(thm mode) {
  thm types_equal = cm_tsrs_pick_conjunct(
      mode, `(left_ty:cm_type) == (right_ty:cm_type)`);
  thm left_pointer = cm_tsrs_pick_conjunct(
      mode, `cm_is_pointer (left_ty:cm_type)`);
  thm right_pointer = conv_rule(
      rewrite_conv(THM_LIST(types_equal)), left_pointer);
  return conj_rule(
      mp_rule(spec_rule(`left_ty:cm_type`, cm_pointer_expr_type),
        left_pointer),
      mp_rule(spec_rule(`right_ty:cm_type`, cm_pointer_expr_type),
        right_pointer));
}

PROOF static thm cm_prove_binary_operand_scalars(void) {
  gnode root = gnode_new_with_ccl(
      `!(op:int) (left_ty:cm_type) (right_ty:cm_type)
         (result:cm_type).
         cm_binary_types op left_ty right_ty result ==>
         cm_scalar_expr_type left_ty &&
         cm_scalar_expr_type right_ty`);
  gnode current = AUTO_INTROS_TAC(root);
  term_list op_cases = TERM_LIST(
      `(op:int) == 0i`, `(op:int) == 1i`,
      `(op:int) == 2i`, `(op:int) == 3i`,
      `(op:int) == 4i`, `(op:int) == 5i`,
      `(op:int) == 6i`, `(op:int) == 7i`,
      `(op:int) == 8i`, `(op:int) == 9i`,
      `(op:int) == 10i`, `(op:int) == 11i`,
      `(op:int) == 12i`);
  thm_list negative_cases = vector_create();
  for (size_t i = 0; i < vector_size(op_cases); ++i) {
    gnode_list cases = BOOL_CASES_TAC(
        current, op_cases[i], gc_sprintf("Hop_%zu", i));
    thm op_equal = assume_rule(op_cases[i]);
    thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_binary_types_def(), op_equal)), assume_rule(
          `cm_binary_types (op:int) (left_ty:cm_type)
            (right_ty:cm_type) (result:cm_type)`));
    if (i <= 1) {
      ACCEPT_TAC(cases[0], conj_rule(
          cm_tsrs_pick_conjunct(opened,
            `cm_scalar_expr_type (left_ty:cm_type)`),
          cm_tsrs_pick_conjunct(opened,
            `cm_scalar_expr_type (right_ty:cm_type)`)));
    } else if (i <= 7) {
      thm modes = cm_tsrs_last_conjunct(opened);
      struct dest_disj_results parts = dest_disj(concl(modes));
      gnode_list mode_cases = DISJ_CASES_TAC(
          cases[0], modes, "Hbinary_mode");
      ACCEPT_TAC(mode_cases[0],
          cm_tsrs_binary_integer_scalars(assume_rule(parts.tm1)));
      ACCEPT_TAC(mode_cases[1],
          cm_tsrs_binary_equal_pointer_scalars(
            assume_rule(parts.tm2)));
    } else if (i == 8) {
      thm modes = cm_tsrs_last_conjunct(opened);
      struct dest_disj_results first = dest_disj(concl(modes));
      struct dest_disj_results second = dest_disj(first.tm2);
      gnode_list mode_cases = DISJ_CASES_TAC(
          cases[0], modes, "Hbinary_mode");
      ACCEPT_TAC(mode_cases[0],
          cm_tsrs_binary_integer_scalars(assume_rule(first.tm1)));
      ACCEPT_TAC(mode_cases[1],
          cm_tsrs_binary_left_pointer_scalars(
            assume_rule(second.tm1)));
      ACCEPT_TAC(mode_cases[2],
          cm_tsrs_binary_right_pointer_scalars(
            assume_rule(second.tm2)));
    } else if (i == 9) {
      thm modes = cm_tsrs_last_conjunct(opened);
      struct dest_disj_results first = dest_disj(concl(modes));
      struct dest_disj_results second = dest_disj(first.tm2);
      gnode_list mode_cases = DISJ_CASES_TAC(
          cases[0], modes, "Hbinary_mode");
      ACCEPT_TAC(mode_cases[0],
          cm_tsrs_binary_integer_scalars(assume_rule(first.tm1)));
      ACCEPT_TAC(mode_cases[1],
          cm_tsrs_binary_left_pointer_scalars(
            assume_rule(second.tm1)));
      ACCEPT_TAC(mode_cases[2],
          cm_tsrs_binary_equal_pointer_scalars(
            assume_rule(second.tm2)));
    } else {
      ACCEPT_TAC(cases[0],
          cm_tsrs_binary_integer_scalars(opened));
    }
    thm negative = assume_rule(mk_not(op_cases[i]));
    vector_add(&negative_cases, negative);
    current = cases[1];
  }
  thm opened = conv_rule(rewrite_conv(THM_LIST(
      get_cm_binary_types_def())), assume_rule(
        `cm_binary_types (op:int) (left_ty:cm_type)
          (right_ty:cm_type) (result:cm_type)`));
  thm lower = cm_tsrs_pick_conjunct(opened, `0i <= (op:int)`);
  thm upper = cm_tsrs_pick_conjunct(opened, `(op:int) <= 12i`);
  thm_list facts = THM_LIST(lower, upper);
  for (size_t i = 0; i < vector_size(negative_cases); ++i) {
    vector_add(&facts, negative_cases[i]);
  }
  term_list terms = vector_create();
  for (size_t i = 0; i < vector_size(facts); ++i) {
    vector_add(&terms, concl(facts[i]));
  }
  thm impossible = int_arith_rule(imp_chain(terms, mk_false()));
  for (size_t i = 0; i < vector_size(facts); ++i) {
    impossible = mp_rule(impossible, facts[i]);
  }
  CONTR_TAC(current, impossible);
  return gnode_prove(root);
}
PROOF thm cm_binary_operand_scalars =
    cm_prove_binary_operand_scalars();

PROOF static thm cm_prove_r_binary_type_ready_step(void) {
  term expression =
      `CMBinaryE (op:int) (left:cm_expr) (right:cm_expr)
        (ty:cm_type)`;
  term task =
      `CMRTask (q:cm_program) (fid:int) ${expression:cm_expr}
        (st:cm_src_state) (ks:(cm_frame)list)`;
  term function =
      `inth (fid:int) (cm_program_functions (p:cm_program))`;
  term phase =
      `CABinLP (op:int) (left:cm_expr) (right:cm_expr)
        (ty:cm_type)`;
  term old_cursors = `cm_ann_cursors (ann:cm_annotation)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (q:cm_program) (fid:int) (op:int)
         (left:cm_expr) (right:cm_expr) (ty:cm_type)
         (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         cm_typed_program p ==>
         cm_task_succeeds
           (CMRTask q fid (CMBinaryE op left right ty) st ks) ==>
         cm_task_type_ready p
           (CMRTask q fid (CMBinaryE op left right ty) st ks) ann ==>
         cm_task_type_ready p
           (cm_step
             (CMRTask q fid (CMBinaryE op left right ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask q fid (CMBinaryE op left right ty) st ks)
               ann))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm task_ready = assume_rule(
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        (ann:cm_annotation)`);
  thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_task_type_ready_def())), task_ready);
  thm expression_wf = cm_tsrs_pick_conjunct(opened,
      `cm_expr_wf (p:cm_program) ${function:cm_function_d}
        ${expression:cm_expr}`);
  thm parent_input = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_expr_type_def())), cm_tsrs_pick_conjunct(opened,
        `cm_cursor_head_input_type_ready (p:cm_program) (fid:int)
          (cm_expr_type ${expression:cm_expr})
          ${old_cursors:(cm_acursor)list}`));
  thm wf_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_expr_wf_def())), expression_wf);
  thm left_wf = cm_tsrs_pick_conjunct(wf_open,
      `cm_expr_wf (p:cm_program) ${function:cm_function_d}
        (left:cm_expr)`);
  thm binary_types = cm_tsrs_pick_conjunct(wf_open,
      `cm_binary_types (op:int) (cm_expr_type (left:cm_expr))
        (cm_expr_type (right:cm_expr)) (ty:cm_type)`);
  thm scalar_pair = mp_rule(specl_rule(TERM_LIST(
      `op:int`, `cm_expr_type (left:cm_expr)`,
      `cm_expr_type (right:cm_expr)`, `ty:cm_type`),
      cm_binary_operand_scalars), binary_types);
  thm left_scalar = conjunct1_rule(scalar_pair);
  thm phase_static = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_static_type_ready_def(), expression_wf)),
      `cm_phase_static_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase}`));
  thm phase_parent = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_parent_type_ready_def(), parent_input)),
      `cm_phase_parent_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase} ${old_cursors:(cm_acursor)list}`));
  thm next_fid = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(cm_phase_next_fid_def)),
      `cm_phase_next_fid (fid:int) ${phase:cm_aphase} == fid`));
  thm phase_input = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_input_type_ready_def())),
      `cm_phase_input_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase} (cm_expr_type (left:cm_expr))`));
  thm phase_expr = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_expr_type_ready_def())),
      `cm_phase_expr_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase} (left:cm_expr)`));
  thm parent_nonzero = cm_tsrs_parent_nonzero(expression);
  thm phase_results =
      cm_tsrs_phase_results(phase, expression, THM_LIST());
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `q:cm_program`, `fid:int`, expression,
      `left:cm_expr`, `st:cm_src_state`, `ks:(cm_frame)list`,
      `CMBinLK (op:int) (right:cm_expr) (ty:cm_type)`,
      `ann:cm_annotation`, phase), cm_r_push_task_ready);
  thm_list premises = THM_LIST(task_ready, parent_nonzero,
      phase_results, left_wf, left_scalar, phase_static,
      phase_parent, next_fid, phase_input, phase_expr);
  for (size_t i = 0; i < vector_size(premises); ++i) {
    result = mp_rule(result, premises[i]);
  }
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_step_def(), get_cm_rstart_def(),
      cm_annotation_step_def, cm_update_r_def,
      cm_update_annotation_def)), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), result));
  return gnode_prove(root);
}
PROOF thm cm_r_binary_type_ready_step =
    cm_prove_r_binary_type_ready_step();

PROOF static thm cm_prove_int_or_char_integer(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type).
         (ty == CMIntTy || ty == CMCharTy) ==>
         cm_integer_type ty`);
  gnode_list cases = INDUCT_TAC(root, `ty:cm_type`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    thm view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        get_cm_integer_type_def(),
        get_datatype_distinctness("cm_type"),
        get_datatype_injectivity("cm_type"))),
        goal_ccl(cases[i]->g));
    ACCEPT_TAC(cases[i], eqt_elim_rule(view));
  }
  return gnode_prove(root);
}
PROOF static thm cm_int_or_char_integer =
    cm_prove_int_or_char_integer();

PROOF static thm cm_prove_r_unary_type_ready_step(void) {
  term expression =
      `CMUnaryE (op:int) (arg:cm_expr) (ty:cm_type)`;
  term task =
      `CMRTask (q:cm_program) (fid:int) ${expression:cm_expr}
        (st:cm_src_state) (ks:(cm_frame)list)`;
  term function =
      `inth (fid:int) (cm_program_functions (p:cm_program))`;
  term old_cursors = `cm_ann_cursors (ann:cm_annotation)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (q:cm_program) (fid:int) (op:int)
         (arg:cm_expr) (ty:cm_type) (st:cm_src_state)
         (ks:(cm_frame)list) (ann:cm_annotation).
         cm_typed_program p ==>
         cm_task_succeeds
           (CMRTask q fid (CMUnaryE op arg ty) st ks) ==>
         cm_task_type_ready p
           (CMRTask q fid (CMUnaryE op arg ty) st ks) ann ==>
         cm_task_type_ready p
           (cm_step (CMRTask q fid (CMUnaryE op arg ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask q fid (CMUnaryE op arg ty) st ks) ann))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm task_ready = assume_rule(
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        (ann:cm_annotation)`);
  thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_task_type_ready_def())), task_ready);
  thm same_program = cm_tsrs_pick_conjunct(
      opened, `(q:cm_program) == (p:cm_program)`);
  thm fid_low = cm_tsrs_pick_conjunct(opened, `0i <= (fid:int)`);
  thm fid_high = cm_tsrs_pick_conjunct(opened,
      `(fid:int) < ilength (cm_program_functions (p:cm_program))`);
  thm expression_wf = cm_tsrs_pick_conjunct(opened,
      `cm_expr_wf (p:cm_program) ${function:cm_function_d}
        ${expression:cm_expr}`);
  thm expression_scalar = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_expr_type_def())), cm_tsrs_pick_conjunct(opened,
        `cm_scalar_expr_type (cm_expr_type ${expression:cm_expr})`));
  thm cursors_ready = cm_tsrs_pick_conjunct(opened,
      `cm_cursors_type_ready (p:cm_program) (fid:int)
        ${old_cursors:(cm_acursor)list}`);
  thm parent_input = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_expr_type_def())), cm_tsrs_pick_conjunct(opened,
        `cm_cursor_head_input_type_ready (p:cm_program) (fid:int)
          (cm_expr_type ${expression:cm_expr})
          ${old_cursors:(cm_acursor)list}`));
  thm parent_values = cm_tsrs_pick_conjunct(opened,
      `cm_cursor_expr_values_type_ready (p:cm_program) (fid:int)
        ${expression:cm_expr} ${old_cursors:(cm_acursor)list}`);
  thm wf_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_expr_wf_def())), expression_wf);
  thm arg_wf = cm_tsrs_pick_conjunct(wf_open,
      `cm_expr_wf (p:cm_program) ${function:cm_function_d}
        (arg:cm_expr)`);
  thm unary_types = cm_tsrs_pick_conjunct(wf_open,
      `cm_unary_types (op:int) (cm_expr_type (arg:cm_expr))
        (ty:cm_type)`);
  gnode_list deref_cases = BOOL_CASES_TAC(
      leaf, `(op:int) == 2i`, "Hderef");
  {
    thm op_equal = assume_rule(`(op:int) == 2i`);
    thm mode = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_unary_types_def(), op_equal)), unary_types);
    thm arg_pointer = cm_tsrs_pick_conjunct(
        mode, `cm_is_pointer (cm_expr_type (arg:cm_expr))`);
    thm result_type = cm_tsrs_pick_conjunct(
        mode, `(ty:cm_type) == cm_pointee (cm_expr_type (arg:cm_expr))`);
    thm pointer_shape = mp_rule(spec_rule(
        `cm_expr_type (arg:cm_expr)`, cm_pointer_type_reconstruct),
        arg_pointer);
    thm result_pointer = beta_norm(ap_term_rule(
        `\source:cm_type. CMPtrTy source`, sym_rule(result_type)));
    thm input_type = trans_rule(sym_rule(pointer_shape), result_pointer);
    thm arg_scalar = mp_rule(spec_rule(
        `cm_expr_type (arg:cm_expr)`, cm_pointer_expr_type),
        arg_pointer);
    term phase = `CALoadP (ty:cm_type)`;
    thm phase_static = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_phase_static_type_ready_def(), expression_scalar)),
        `cm_phase_static_type_ready (p:cm_program) (fid:int)
          ${phase:cm_aphase}`));
    thm phase_parent = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_phase_parent_type_ready_def(), parent_input)),
        `cm_phase_parent_type_ready (p:cm_program) (fid:int)
          ${phase:cm_aphase} ${old_cursors:(cm_acursor)list}`));
    thm next_fid = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(cm_phase_next_fid_def)),
        `cm_phase_next_fid (fid:int) ${phase:cm_aphase} == fid`));
    thm phase_input = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_phase_input_type_ready_def(), input_type)),
        `cm_phase_input_type_ready (p:cm_program) (fid:int)
          ${phase:cm_aphase} (cm_expr_type (arg:cm_expr))`));
    thm phase_expr = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_phase_expr_type_ready_def(), input_type)),
        `cm_phase_expr_type_ready (p:cm_program) (fid:int)
          ${phase:cm_aphase} (arg:cm_expr)`));
    thm parent_nonzero = cm_tsrs_parent_nonzero(expression);
    thm phase_results =
        cm_tsrs_phase_results(phase, expression, THM_LIST());
    thm result = specl_rule(TERM_LIST(
        `p:cm_program`, `q:cm_program`, `fid:int`, expression,
        `arg:cm_expr`, `st:cm_src_state`, `ks:(cm_frame)list`,
        `CMLoadK (ty:cm_type)`, `ann:cm_annotation`, phase),
        cm_r_push_task_ready);
    thm_list premises = THM_LIST(task_ready, parent_nonzero,
        phase_results, arg_wf, arg_scalar, phase_static,
        phase_parent, next_fid, phase_input, phase_expr);
    for (size_t i = 0; i < vector_size(premises); ++i) {
      result = mp_rule(result, premises[i]);
    }
    thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        op_equal, get_cm_step_def(), get_cm_rstart_def(),
        cm_annotation_step_def, cm_update_r_def,
        cm_update_annotation_def)), goal_ccl(deref_cases[0]->g));
    ACCEPT_TAC(deref_cases[0],
        eq_mp_rule(sym_rule(target_view), result));
  }
  gnode_list address_cases = BOOL_CASES_TAC(
      deref_cases[1], `(op:int) == 3i`, "Haddress");
  {
    thm op_equal = assume_rule(`(op:int) == 3i`);
    thm wf_mode = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_expr_wf_def(), get_cm_unary_types_def(), op_equal)),
        expression_wf);
    thm arg_lvalue = cm_tsrs_pick_conjunct(
        wf_mode, `cm_lvalue (arg:cm_expr)`);
    thm arg_nonarray = cm_tsrs_pick_conjunct(wf_mode,
        `~cm_expr_array (p:cm_program) ${function:cm_function_d}
          (arg:cm_expr)`);
    thm result_type = cm_tsrs_pick_conjunct(wf_mode,
        `(ty:cm_type) == CMPtrTy (cm_expr_type (arg:cm_expr))`);
    term output =
        `cm_lvalue_output_type (p:cm_program)
          ${function:cm_function_d} (arg:cm_expr)`;
    thm output_pointer = mp_rule(mp_rule(mp_rule(mp_rule(mp_rule(
        specl_rule(TERM_LIST(
          `arg:cm_expr`, `p:cm_program`, `fid:int`),
          cm_nonarray_lvalue_output_type),
        assume_rule(`cm_typed_program (p:cm_program)`)), fid_low),
        fid_high), arg_wf), arg_lvalue);
    output_pointer = mp_rule(output_pointer, arg_nonarray);
    thm output_ty = trans_rule(output_pointer, sym_rule(result_type));
    thm output_parent_view = apply_conversion(
        reduce_rewrite_conv(THM_LIST(get_cm_expr_type_def())),
        `(${output:cm_type}) == cm_expr_type ${expression:cm_expr}`);
    thm output_parent =
        eq_mp_rule(sym_rule(output_parent_view), output_ty);
    thm lvalue_input = conv_rule(rewrite_conv(THM_LIST(
        sym_rule(output_ty))), parent_input);
    thm nonzero = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_zero_literal_def(),
          get_datatype_distinctness("cm_expr"))),
        `~cm_zero_literal ${expression:cm_expr}`));
    thm null_compatible = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          output_pointer, get_cm_value_type_compatible_def(),
          get_cm_value_type_def(), get_cm_is_pointer_def(),
          get_datatype_distinctness("cm_value"),
          get_datatype_distinctness("cm_type"))),
        `cm_value_type_compatible CMNullV ${output:cm_type}`));
    thm compatible_exists = exists_rule(
        `?w. cm_value_type_compatible (w:cm_value) ${output:cm_type}`,
        `CMNullV`, null_compatible);
    thm lvalue_ready = mp_rule(mp_rule(mp_rule(mp_rule(specl_rule(
        TERM_LIST(`p:cm_program`, `fid:int`, expression, output,
          old_cursors), cm_expr_cursor_values_lvalue),
        parent_values), output_parent), nonzero), compatible_exists);
    thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        same_program, fid_low, fid_high, arg_wf, arg_lvalue,
        cursors_ready, lvalue_input, lvalue_ready, op_equal,
        get_cm_task_type_ready_def(), get_cm_step_def(),
        get_cm_rstart_def(), cm_annotation_step_def,
        cm_update_r_def, cm_update_annotation_def)),
        goal_ccl(address_cases[0]->g));
    thm target_final = apply_conversion(reduce_rewrite_conv(THM_LIST(
        same_program, fid_low, fid_high, arg_wf, arg_lvalue,
        cursors_ready, lvalue_input, lvalue_ready, op_equal,
        get_cm_task_type_ready_def(), cm_update_annotation_def)),
        rhs_of(target_view));
    ACCEPT_TAC(address_cases[0],
        eqt_elim_rule(trans_rule(target_view, target_final)));
  }
  gnode current = address_cases[1];
  term_list ordinary_ops = TERM_LIST(
      `(op:int) == 0i`, `(op:int) == 1i`);
  thm_list ordinary_negative = vector_create();
  vector_add(&ordinary_negative, assume_rule(`~((op:int) == 2i)`));
  vector_add(&ordinary_negative, assume_rule(`~((op:int) == 3i)`));
  for (size_t j = 0; j < vector_size(ordinary_ops); ++j) {
    gnode_list ordinary_cases = BOOL_CASES_TAC(
        current, ordinary_ops[j], gc_sprintf("Hordinary_%zu", j));
    thm op_equal = assume_rule(ordinary_ops[j]);
    thm mode = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_unary_types_def(), op_equal)), unary_types);
    thm arg_kinds = cm_tsrs_pick_conjunct(mode,
        `(cm_expr_type (arg:cm_expr) == CMIntTy ||
         cm_expr_type arg == CMCharTy)`);
    thm arg_integer = mp_rule(spec_rule(
        `cm_expr_type (arg:cm_expr)`, cm_int_or_char_integer),
        arg_kinds);
    thm result_type = cm_tsrs_pick_conjunct(
        mode, `(ty:cm_type) == CMIntTy`);
    thm arg_scalar = mp_rule(spec_rule(
        `cm_expr_type (arg:cm_expr)`, cm_integer_expr_type),
        arg_integer);
    term phase = `CAUnaryP (op:int)`;
    thm phase_static = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_phase_static_type_ready_def(), op_equal)),
        `cm_phase_static_type_ready (p:cm_program) (fid:int)
          ${phase:cm_aphase}`));
    thm ordinary_parent = conv_rule(rewrite_conv(
        THM_LIST(result_type)), parent_input);
    thm phase_parent = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_phase_parent_type_ready_def(), ordinary_parent)),
        `cm_phase_parent_type_ready (p:cm_program) (fid:int)
          ${phase:cm_aphase} ${old_cursors:(cm_acursor)list}`));
    thm next_fid = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(cm_phase_next_fid_def)),
        `cm_phase_next_fid (fid:int) ${phase:cm_aphase} == fid`));
    thm phase_input = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_phase_input_type_ready_def(), arg_integer)),
        `cm_phase_input_type_ready (p:cm_program) (fid:int)
          ${phase:cm_aphase} (cm_expr_type (arg:cm_expr))`));
    thm phase_expr = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_phase_expr_type_ready_def(), arg_integer)),
        `cm_phase_expr_type_ready (p:cm_program) (fid:int)
          ${phase:cm_aphase} (arg:cm_expr)`));
    thm parent_nonzero = cm_tsrs_parent_nonzero(expression);
    thm phase_results =
        cm_tsrs_phase_results(phase, expression, THM_LIST(result_type));
    thm result = specl_rule(TERM_LIST(
        `p:cm_program`, `q:cm_program`, `fid:int`, expression,
        `arg:cm_expr`, `st:cm_src_state`, `ks:(cm_frame)list`,
        `CMUnaryK (op:int)`, `ann:cm_annotation`, phase),
        cm_r_push_task_ready);
    thm_list premises = THM_LIST(task_ready, parent_nonzero,
        phase_results, arg_wf, arg_scalar, phase_static,
        phase_parent, next_fid, phase_input, phase_expr);
    for (size_t i = 0; i < vector_size(premises); ++i) {
      result = mp_rule(result, premises[i]);
    }
    result = conv_rule(rewrite_conv(THM_LIST(op_equal)), result);
    thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        op_equal, get_cm_step_def(), get_cm_rstart_def(),
        cm_annotation_step_def, cm_update_r_def,
        cm_update_annotation_def)), goal_ccl(ordinary_cases[0]->g));
    thm target_final = apply_conversion(
        reduce_rewrite_conv(THM_LIST(cm_update_annotation_def)),
        rhs_of(target_view));
    ACCEPT_TAC(ordinary_cases[0], eq_mp_rule(
        sym_rule(trans_rule(target_view, target_final)), result));
    thm negative = assume_rule(mk_not(ordinary_ops[j]));
    vector_add(&ordinary_negative, negative);
    current = ordinary_cases[1];
  }
  thm unary_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_unary_types_def())), unary_types);
  thm lower = cm_tsrs_pick_conjunct(
      unary_open, `0i <= (op:int)`);
  thm upper = cm_tsrs_pick_conjunct(
      unary_open, `(op:int) <= 3i`);
  thm_list contradiction_facts = THM_LIST(lower, upper);
  for (size_t i = 0; i < vector_size(ordinary_negative); ++i) {
    vector_add(&contradiction_facts, ordinary_negative[i]);
  }
  term_list contradiction_terms = vector_create();
  for (size_t i = 0; i < vector_size(contradiction_facts); ++i) {
    vector_add(&contradiction_terms, concl(contradiction_facts[i]));
  }
  thm impossible = int_arith_rule(
      imp_chain(contradiction_terms, mk_false()));
  for (size_t i = 0; i < vector_size(contradiction_facts); ++i) {
    impossible = mp_rule(impossible, contradiction_facts[i]);
  }
  CONTR_TAC(current, impossible);
  return gnode_prove(root);
}
PROOF thm cm_r_unary_type_ready_step =
    cm_prove_r_unary_type_ready_step();
PROOF static thm cm_prove_r_index_type_ready_step(void) {
  term expression =
      `CMIndexE (base:cm_expr) (index:cm_expr) (ty:cm_type)`;
  term task =
      `CMRTask (q:cm_program) (fid:int) ${expression:cm_expr}
        (st:cm_src_state) (ks:(cm_frame)list)`;
  term phase = `CALoadP (ty:cm_type)`;
  term output =
      `cm_lvalue_output_type (p:cm_program)
        (inth (fid:int) (cm_program_functions p))
        ${expression:cm_expr}`;
  term old_cursors = `cm_ann_cursors (ann:cm_annotation)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (q:cm_program) (fid:int)
         (base:cm_expr) (index:cm_expr) (ty:cm_type)
         (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         cm_typed_program p ==>
         cm_task_succeeds
           (CMRTask q fid (CMIndexE base index ty) st ks) ==>
         cm_task_type_ready p
           (CMRTask q fid (CMIndexE base index ty) st ks) ann ==>
         cm_task_type_ready p
           (cm_step (CMRTask q fid (CMIndexE base index ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask q fid (CMIndexE base index ty) st ks) ann))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm task_ready = assume_rule(
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        (ann:cm_annotation)`);
  thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_task_type_ready_def())), task_ready);
  thm expression_wf = cm_tsrs_pick_conjunct(opened,
      `cm_expr_wf (p:cm_program)
        (inth (fid:int) (cm_program_functions p))
        ${expression:cm_expr}`);
  thm expression_scalar = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_expr_type_def())), cm_tsrs_pick_conjunct(opened,
        `cm_scalar_expr_type (cm_expr_type ${expression:cm_expr})`));
  thm parent_input = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_expr_type_def())), cm_tsrs_pick_conjunct(opened,
        `cm_cursor_head_input_type_ready (p:cm_program) (fid:int)
          (cm_expr_type ${expression:cm_expr})
          ${old_cursors:(cm_acursor)list}`));
  thm expression_lvalue = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_cm_lvalue_def())),
      `cm_lvalue ${expression:cm_expr}`));
  thm output_equal = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_lvalue_output_type_def(), get_cm_expr_type_def())),
      `(${output:cm_type}) == CMPtrTy (ty:cm_type)`));
  thm phase_static = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_static_type_ready_def(), expression_scalar)),
      `cm_phase_static_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase}`));
  thm phase_parent = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_parent_type_ready_def(), parent_input)),
      `cm_phase_parent_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase} ${old_cursors:(cm_acursor)list}`));
  thm next_fid = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(cm_phase_next_fid_def)),
      `cm_phase_next_fid (fid:int) ${phase:cm_aphase} == fid`));
  thm phase_input = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_input_type_ready_def(), output_equal)),
      `cm_phase_input_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase} ${output:cm_type}`));
  thm phase_lvalue = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_lvalue_type_ready_def(),
        get_cm_phase_value_type_ready_def(), output_equal)),
      `cm_phase_lvalue_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase} ${output:cm_type}`));
  thm parent_nonzero = cm_tsrs_parent_nonzero(expression);
  thm phase_results =
      cm_tsrs_phase_results(phase, expression, THM_LIST());
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `q:cm_program`, `fid:int`, expression,
      expression, `st:cm_src_state`, `ks:(cm_frame)list`,
      `CMLoadK (ty:cm_type)`, `ann:cm_annotation`, phase),
      cm_l_push_task_ready);
  thm_list premises = THM_LIST(task_ready, parent_nonzero,
      phase_results, expression_wf, expression_lvalue, phase_static,
      phase_parent, next_fid, phase_input, phase_lvalue);
  for (size_t i = 0; i < vector_size(premises); ++i) {
    result = mp_rule(result, premises[i]);
  }
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_step_def(), get_cm_rstart_def(),
      cm_annotation_step_def, cm_update_r_def,
      cm_update_annotation_def)), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), result));
  return gnode_prove(root);
}
PROOF thm cm_r_index_type_ready_step =
    cm_prove_r_index_type_ready_step();

PROOF static thm cm_prove_member_array_output_type(void) {
  term expression =
      `CMMemberE (base:cm_expr) (mid:int) (ty:cm_type)`;
  term function =
      `inth (fid:int) (cm_program_functions (p:cm_program))`;
  term output =
      `cm_lvalue_output_type (p:cm_program) ${function:cm_function_d}
        ${expression:cm_expr}`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (base:cm_expr) (mid:int)
         (ty:cm_type).
         cm_expr_wf p (inth fid (cm_program_functions p))
           (CMMemberE base mid ty) ==>
         cm_member_array p (cm_expr_type base) mid ==>
         cm_lvalue_output_type p
           (inth fid (cm_program_functions p))
           (CMMemberE base mid ty) ==
         cm_expr_type (CMMemberE base mid ty)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm expression_wf = assume_rule(
      `cm_expr_wf (p:cm_program) ${function:cm_function_d}
        ${expression:cm_expr}`);
  thm wf_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_expr_wf_def())), expression_wf);
  thm result_type = cm_tsrs_pick_conjunct(wf_open,
      `(ty:cm_type) ==
       cm_member_type (p:cm_program)
         (cm_expr_type (base:cm_expr)) (mid:int)`);
  thm array_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_member_array_def())), assume_rule(
        `cm_member_array (p:cm_program)
          (cm_expr_type (base:cm_expr)) (mid:int)`));
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      result_type, array_open, get_cm_lvalue_output_type_def(),
      get_cm_member_lvalue_type_def(), get_cm_member_type_def(),
      get_cm_slot_expr_type_def(), get_cm_expr_type_def(),
      get_theorem_by_name("COND_CLAUSES"))), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eqt_elim_rule(target_view));
  return gnode_prove(root);
}
PROOF static thm cm_member_array_output_type =
    cm_prove_member_array_output_type();

PROOF static thm cm_prove_r_member_type_ready_step(void) {
  term expression =
      `CMMemberE (base:cm_expr) (mid:int) (ty:cm_type)`;
  term task =
      `CMRTask (q:cm_program) (fid:int) ${expression:cm_expr}
        (st:cm_src_state) (ks:(cm_frame)list)`;
  term function =
      `inth (fid:int) (cm_program_functions (p:cm_program))`;
  term output =
      `cm_lvalue_output_type (p:cm_program) ${function:cm_function_d}
        ${expression:cm_expr}`;
  term phase = `CALoadP (ty:cm_type)`;
  term old_cursors = `cm_ann_cursors (ann:cm_annotation)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (q:cm_program) (fid:int)
         (base:cm_expr) (mid:int) (ty:cm_type)
         (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         cm_typed_program p ==>
         cm_task_succeeds
           (CMRTask q fid (CMMemberE base mid ty) st ks) ==>
         cm_task_type_ready p
           (CMRTask q fid (CMMemberE base mid ty) st ks) ann ==>
         cm_task_type_ready p
           (cm_step (CMRTask q fid (CMMemberE base mid ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask q fid (CMMemberE base mid ty) st ks) ann))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm task_ready = assume_rule(
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        (ann:cm_annotation)`);
  thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_task_type_ready_def())), task_ready);
  thm same_program = cm_tsrs_pick_conjunct(
      opened, `(q:cm_program) == (p:cm_program)`);
  thm fid_low = cm_tsrs_pick_conjunct(opened, `0i <= (fid:int)`);
  thm fid_high = cm_tsrs_pick_conjunct(opened,
      `(fid:int) < ilength (cm_program_functions (p:cm_program))`);
  thm expression_wf = cm_tsrs_pick_conjunct(opened,
      `cm_expr_wf (p:cm_program) ${function:cm_function_d}
        ${expression:cm_expr}`);
  thm expression_scalar = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_expr_type_def())), cm_tsrs_pick_conjunct(opened,
        `cm_scalar_expr_type (cm_expr_type ${expression:cm_expr})`));
  thm cursors_ready = cm_tsrs_pick_conjunct(opened,
      `cm_cursors_type_ready (p:cm_program) (fid:int)
        ${old_cursors:(cm_acursor)list}`);
  thm parent_input = cm_tsrs_pick_conjunct(opened,
      `cm_cursor_head_input_type_ready (p:cm_program) (fid:int)
        (cm_expr_type ${expression:cm_expr})
        ${old_cursors:(cm_acursor)list}`);
  thm parent_values = cm_tsrs_pick_conjunct(opened,
      `cm_cursor_expr_values_type_ready (p:cm_program) (fid:int)
        ${expression:cm_expr} ${old_cursors:(cm_acursor)list}`);
  thm expression_lvalue = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_cm_lvalue_def())),
      `cm_lvalue ${expression:cm_expr}`));
  gnode_list array_cases = BOOL_CASES_TAC(leaf,
      `cm_member_array (p:cm_program)
        (cm_expr_type (base:cm_expr)) (mid:int)`, "Harray");
  {
    thm array_ready = assume_rule(
        `cm_member_array (p:cm_program)
          (cm_expr_type (base:cm_expr)) (mid:int)`);
    thm array_q = conv_rule(rewrite_conv(THM_LIST(
        sym_rule(same_program))), array_ready);
    thm output_equal = mp_rule(mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `base:cm_expr`, `mid:int`,
        `ty:cm_type`), cm_member_array_output_type), expression_wf),
        array_ready);
    thm lvalue_input = conv_rule(rewrite_conv(THM_LIST(
        sym_rule(output_equal))), parent_input);
    thm nonzero = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_zero_literal_def(),
          get_datatype_distinctness("cm_expr"))),
        `~cm_zero_literal ${expression:cm_expr}`));
    thm null_compatible = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_lvalue_output_type_def(),
          get_cm_member_lvalue_type_def(),
          get_cm_value_type_compatible_def(),
          get_cm_value_type_def(), get_cm_is_pointer_def(),
          get_datatype_distinctness("cm_value"),
          get_datatype_distinctness("cm_type"))),
        `cm_value_type_compatible CMNullV ${output:cm_type}`));
    thm compatible_exists = exists_rule(
        `?w. cm_value_type_compatible (w:cm_value) ${output:cm_type}`,
        `CMNullV`, null_compatible);
    thm lvalue_ready = mp_rule(mp_rule(mp_rule(mp_rule(specl_rule(
        TERM_LIST(`p:cm_program`, `fid:int`, expression, output,
          old_cursors), cm_expr_cursor_values_lvalue),
        parent_values), output_equal), nonzero), compatible_exists);
    thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        same_program, fid_low, fid_high, expression_wf,
        expression_lvalue, cursors_ready, lvalue_input,
        lvalue_ready, array_q, get_cm_task_type_ready_def(),
        get_cm_step_def(), get_cm_rstart_def(),
        cm_annotation_step_def, cm_update_r_def,
        cm_update_annotation_def)), goal_ccl(array_cases[0]->g));
    thm target_final = apply_conversion(reduce_rewrite_conv(THM_LIST(
        same_program, fid_low, fid_high, expression_wf,
        expression_lvalue, cursors_ready, lvalue_input,
        lvalue_ready, get_cm_task_type_ready_def(),
        cm_update_annotation_def)), rhs_of(target_view));
    ACCEPT_TAC(array_cases[0],
        eqt_elim_rule(trans_rule(target_view, target_final)));
  }
  {
    thm not_array = assume_rule(
        `~cm_member_array (p:cm_program)
          (cm_expr_type (base:cm_expr)) (mid:int)`);
    thm not_array_q = conv_rule(rewrite_conv(THM_LIST(
        sym_rule(same_program))), not_array);
    thm normalized_nonarray = conv_rule(
        reduce_rewrite_conv(THM_LIST(get_cm_member_array_def())),
        not_array);
    thm expression_view = apply_conversion(
        reduce_rewrite_conv(THM_LIST(get_cm_expr_array_def())),
        `~cm_expr_array (p:cm_program) ${function:cm_function_d}
          ${expression:cm_expr}`);
    thm expression_nonarray =
        eq_mp_rule(sym_rule(expression_view), normalized_nonarray);
    thm output_equal = mp_rule(mp_rule(mp_rule(mp_rule(mp_rule(
        specl_rule(TERM_LIST(expression, `p:cm_program`, `fid:int`),
          cm_nonarray_lvalue_output_type),
        assume_rule(`cm_typed_program (p:cm_program)`)), fid_low),
        fid_high), expression_wf), expression_lvalue);
    output_equal = mp_rule(output_equal, expression_nonarray);
    output_equal = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_expr_type_def())), output_equal);
    thm normalized_parent = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_expr_type_def())), parent_input);
    thm phase_static = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_phase_static_type_ready_def(), expression_scalar)),
        `cm_phase_static_type_ready (p:cm_program) (fid:int)
          ${phase:cm_aphase}`));
    thm phase_parent = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_phase_parent_type_ready_def(), normalized_parent)),
        `cm_phase_parent_type_ready (p:cm_program) (fid:int)
          ${phase:cm_aphase} ${old_cursors:(cm_acursor)list}`));
    thm next_fid = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(cm_phase_next_fid_def)),
        `cm_phase_next_fid (fid:int) ${phase:cm_aphase} == fid`));
    thm phase_input = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_phase_input_type_ready_def(), output_equal)),
        `cm_phase_input_type_ready (p:cm_program) (fid:int)
          ${phase:cm_aphase} ${output:cm_type}`));
    thm phase_lvalue = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_phase_lvalue_type_ready_def(),
          get_cm_phase_value_type_ready_def(), output_equal)),
        `cm_phase_lvalue_type_ready (p:cm_program) (fid:int)
          ${phase:cm_aphase} ${output:cm_type}`));
    thm parent_nonzero = cm_tsrs_parent_nonzero(expression);
    thm phase_results =
        cm_tsrs_phase_results(phase, expression, THM_LIST());
    thm result = specl_rule(TERM_LIST(
        `p:cm_program`, `q:cm_program`, `fid:int`, expression,
        expression, `st:cm_src_state`, `ks:(cm_frame)list`,
        `CMLoadK (ty:cm_type)`, `ann:cm_annotation`, phase),
        cm_l_push_task_ready);
    thm_list premises = THM_LIST(task_ready, parent_nonzero,
        phase_results, expression_wf, expression_lvalue, phase_static,
        phase_parent, next_fid, phase_input, phase_lvalue);
    for (size_t i = 0; i < vector_size(premises); ++i) {
      result = mp_rule(result, premises[i]);
    }
    thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        not_array_q, get_cm_step_def(), get_cm_rstart_def(),
        cm_annotation_step_def, cm_update_r_def,
        cm_update_annotation_def)), goal_ccl(array_cases[1]->g));
    ACCEPT_TAC(array_cases[1],
        eq_mp_rule(sym_rule(target_view), result));
  }
  return gnode_prove(root);
}
PROOF thm cm_r_member_type_ready_step =
    cm_prove_r_member_type_ready_step();

PROOF static thm cm_prove_r_putc_type_ready_step(void) {
  term expression =
      `CMPutcE (arg:cm_expr) (ty:cm_type)`;
  term task =
      `CMRTask (q:cm_program) (fid:int) ${expression:cm_expr}
        (st:cm_src_state) (ks:(cm_frame)list)`;
  term function =
      `inth (fid:int) (cm_program_functions (p:cm_program))`;
  term phase = `CAPutcP`;
  term old_cursors = `cm_ann_cursors (ann:cm_annotation)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (q:cm_program) (fid:int)
         (arg:cm_expr) (ty:cm_type) (st:cm_src_state)
         (ks:(cm_frame)list) (ann:cm_annotation).
         cm_typed_program p ==>
         cm_task_succeeds
           (CMRTask q fid (CMPutcE arg ty) st ks) ==>
         cm_task_type_ready p
           (CMRTask q fid (CMPutcE arg ty) st ks) ann ==>
         cm_task_type_ready p
           (cm_step (CMRTask q fid (CMPutcE arg ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask q fid (CMPutcE arg ty) st ks) ann))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm task_ready = assume_rule(
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        (ann:cm_annotation)`);
  thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_task_type_ready_def())), task_ready);
  thm expression_wf = cm_tsrs_pick_conjunct(opened,
      `cm_expr_wf (p:cm_program) ${function:cm_function_d}
        ${expression:cm_expr}`);
  thm parent_input = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_expr_type_def())), cm_tsrs_pick_conjunct(opened,
        `cm_cursor_head_input_type_ready (p:cm_program) (fid:int)
          (cm_expr_type ${expression:cm_expr})
          ${old_cursors:(cm_acursor)list}`));
  thm wf_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_expr_wf_def())), expression_wf);
  thm arg_wf = cm_tsrs_pick_conjunct(wf_open,
      `cm_expr_wf (p:cm_program) ${function:cm_function_d}
        (arg:cm_expr)`);
  thm arg_static = cm_tsrs_pick_conjunct(wf_open,
      `cm_scalar_type (cm_program_structs (p:cm_program))
        (cm_expr_type (arg:cm_expr))`);
  thm result_type = cm_tsrs_pick_conjunct(
      wf_open, `(ty:cm_type) == CMIntTy`);
  thm arg_scalar = mp_rule(specl_rule(TERM_LIST(
      `cm_expr_type (arg:cm_expr)`,
      `cm_program_structs (p:cm_program)`),
      cm_scalar_type_is_expr_type), arg_static);
  thm phase_static = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_static_type_ready_def())),
      `cm_phase_static_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase}`));
  thm int_parent = conv_rule(
      rewrite_conv(THM_LIST(result_type)), parent_input);
  thm phase_parent = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_parent_type_ready_def(), int_parent)),
      `cm_phase_parent_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase} ${old_cursors:(cm_acursor)list}`));
  thm next_fid = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(cm_phase_next_fid_def)),
      `cm_phase_next_fid (fid:int) ${phase:cm_aphase} == fid`));
  thm phase_input = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_input_type_ready_def(), arg_scalar)),
      `cm_phase_input_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase} (cm_expr_type (arg:cm_expr))`));
  thm phase_expr = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_expr_type_ready_def(), arg_scalar)),
      `cm_phase_expr_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase} (arg:cm_expr)`));
  thm parent_nonzero = cm_tsrs_parent_nonzero(expression);
  thm phase_results =
      cm_tsrs_phase_results(phase, expression, THM_LIST(result_type));
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `q:cm_program`, `fid:int`, expression,
      `arg:cm_expr`, `st:cm_src_state`, `ks:(cm_frame)list`,
      `CMPutcK`, `ann:cm_annotation`, phase),
      cm_r_push_task_ready);
  thm_list premises = THM_LIST(task_ready, parent_nonzero,
      phase_results, arg_wf, arg_scalar, phase_static,
      phase_parent, next_fid, phase_input, phase_expr);
  for (size_t i = 0; i < vector_size(premises); ++i) {
    result = mp_rule(result, premises[i]);
  }
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_step_def(), get_cm_rstart_def(),
      cm_annotation_step_def, cm_update_r_def,
      cm_update_annotation_def)), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), result));
  return gnode_prove(root);
}
PROOF thm cm_r_putc_type_ready_step =
    cm_prove_r_putc_type_ready_step();

PROOF static void cm_tsrs_close_integer_io(
    gnode leaf, term expression, term phase, term frame) {
  term task =
      `CMRTask (q:cm_program) (fid:int) ${expression:cm_expr}
        (st:cm_src_state) (ks:(cm_frame)list)`;
  term function =
      `inth (fid:int) (cm_program_functions (p:cm_program))`;
  term old_cursors = `cm_ann_cursors (ann:cm_annotation)`;
  thm task_ready = assume_rule(
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        (ann:cm_annotation)`);
  thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_task_type_ready_def())), task_ready);
  thm expression_wf = cm_tsrs_pick_conjunct(opened,
      `cm_expr_wf (p:cm_program) ${function:cm_function_d}
        ${expression:cm_expr}`);
  thm parent_input = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_expr_type_def())), cm_tsrs_pick_conjunct(opened,
        `cm_cursor_head_input_type_ready (p:cm_program) (fid:int)
          (cm_expr_type ${expression:cm_expr})
          ${old_cursors:(cm_acursor)list}`));
  thm wf_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_expr_wf_def())), expression_wf);
  thm arg_wf = cm_tsrs_pick_conjunct(wf_open,
      `cm_expr_wf (p:cm_program) ${function:cm_function_d}
        (arg:cm_expr)`);
  thm arg_kinds = cm_tsrs_pick_conjunct(wf_open,
      `(cm_expr_type (arg:cm_expr) == CMIntTy ||
       cm_expr_type arg == CMCharTy)`);
  thm result_type = cm_tsrs_pick_conjunct(
      wf_open, `(ty:cm_type) == CMIntTy`);
  thm arg_integer = mp_rule(spec_rule(
      `cm_expr_type (arg:cm_expr)`, cm_int_or_char_integer),
      arg_kinds);
  thm arg_scalar = mp_rule(spec_rule(
      `cm_expr_type (arg:cm_expr)`, cm_integer_expr_type),
      arg_integer);
  thm phase_static = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_static_type_ready_def())),
      `cm_phase_static_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase}`));
  thm int_parent = conv_rule(
      rewrite_conv(THM_LIST(result_type)), parent_input);
  thm phase_parent = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_parent_type_ready_def(), int_parent)),
      `cm_phase_parent_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase} ${old_cursors:(cm_acursor)list}`));
  thm next_fid = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(cm_phase_next_fid_def)),
      `cm_phase_next_fid (fid:int) ${phase:cm_aphase} == fid`));
  thm phase_input = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_input_type_ready_def(), arg_integer)),
      `cm_phase_input_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase} (cm_expr_type (arg:cm_expr))`));
  thm phase_expr = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_expr_type_ready_def(), arg_integer)),
      `cm_phase_expr_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase} (arg:cm_expr)`));
  thm parent_nonzero = cm_tsrs_parent_nonzero(expression);
  thm phase_results =
      cm_tsrs_phase_results(phase, expression, THM_LIST(result_type));
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `q:cm_program`, `fid:int`, expression,
      `arg:cm_expr`, `st:cm_src_state`, `ks:(cm_frame)list`,
      frame, `ann:cm_annotation`, phase), cm_r_push_task_ready);
  thm_list premises = THM_LIST(task_ready, parent_nonzero,
      phase_results, arg_wf, arg_scalar, phase_static,
      phase_parent, next_fid, phase_input, phase_expr);
  for (size_t i = 0; i < vector_size(premises); ++i) {
    result = mp_rule(result, premises[i]);
  }
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_step_def(), get_cm_rstart_def(),
      cm_annotation_step_def, cm_update_r_def,
      cm_update_annotation_def)), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), result));
}

PROOF static thm cm_prove_r_puti_type_ready_step(void) {
  term expression =
      `CMPutiE (arg:cm_expr) (ty:cm_type)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (q:cm_program) (fid:int)
         (arg:cm_expr) (ty:cm_type) (st:cm_src_state)
         (ks:(cm_frame)list) (ann:cm_annotation).
         cm_typed_program p ==>
         cm_task_succeeds
           (CMRTask q fid (CMPutiE arg ty) st ks) ==>
         cm_task_type_ready p
           (CMRTask q fid (CMPutiE arg ty) st ks) ann ==>
         cm_task_type_ready p
           (cm_step (CMRTask q fid (CMPutiE arg ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask q fid (CMPutiE arg ty) st ks) ann))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  cm_tsrs_close_integer_io(
      leaf, expression, `CAPutiP`, `CMPutiK`);
  return gnode_prove(root);
}
PROOF thm cm_r_puti_type_ready_step =
    cm_prove_r_puti_type_ready_step();

PROOF static thm cm_prove_r_exit_type_ready_step(void) {
  term expression =
      `CMExitE (arg:cm_expr) (ty:cm_type)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (q:cm_program) (fid:int)
         (arg:cm_expr) (ty:cm_type) (st:cm_src_state)
         (ks:(cm_frame)list) (ann:cm_annotation).
         cm_typed_program p ==>
         cm_task_succeeds
           (CMRTask q fid (CMExitE arg ty) st ks) ==>
         cm_task_type_ready p
           (CMRTask q fid (CMExitE arg ty) st ks) ann ==>
         cm_task_type_ready p
           (cm_step (CMRTask q fid (CMExitE arg ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask q fid (CMExitE arg ty) st ks) ann))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  cm_tsrs_close_integer_io(
      leaf, expression, `CAExitP`, `CMExitK`);
  return gnode_prove(root);
}
PROOF thm cm_r_exit_type_ready_step =
    cm_prove_r_exit_type_ready_step();

PROOF static int cmc_preservation_type_source_r_struct_final_checks(void) {
  ENSURE_COND(vector_size(hyp(cm_r_assign_type_ready_step)) == 0 &&
      vector_size(hyp(cm_binary_operand_scalars)) == 0 &&
      vector_size(hyp(cm_int_or_char_integer)) == 0 &&
      vector_size(hyp(cm_r_binary_type_ready_step)) == 0 &&
      vector_size(hyp(cm_r_unary_type_ready_step)) == 0 &&
      vector_size(hyp(cm_r_index_type_ready_step)) == 0 &&
      vector_size(hyp(cm_member_array_output_type)) == 0 &&
      vector_size(hyp(cm_r_member_type_ready_step)) == 0 &&
      vector_size(hyp(cm_r_putc_type_ready_step)) == 0 &&
      vector_size(hyp(cm_r_puti_type_ready_step)) == 0 &&
      vector_size(hyp(cm_r_exit_type_ready_step)) == 0,
      "structural rvalue type theorem has assumptions");
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_type_source_r_struct_axioms_before,
      "cmc_preservation_type_source_r_struct introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_type_source_r_struct_checks =
    cmc_preservation_type_source_r_struct_final_checks();
