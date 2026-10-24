#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_type_source_s.h"
#include "cmc_preservation_ready_coordinate.h"

#require "cmc_preservation_type_source_s_support.c"

PROOF static size_t _cmc_preservation_type_source_s_axioms_before =
    vector_size(get_all_axioms());

PROOF static bool cm_tss_has_conjunct(term whole, term wanted) {
  if (alpha_compare(whole, wanted) == 0) return true;
  if (!is_conj(whole)) return false;
  struct dest_conj_results parts = dest_conj(whole);
  return cm_tss_has_conjunct(parts.tm1, wanted) ||
      cm_tss_has_conjunct(parts.tm2, wanted);
}

PROOF static thm cm_tss_pick_conjunct(thm fact, term wanted) {
  if (alpha_compare(concl(fact), wanted) == 0) return fact;
  struct dest_conj_results parts = dest_conj(concl(fact));
  return cm_tss_has_conjunct(parts.tm1, wanted)
      ? cm_tss_pick_conjunct(conjunct1_rule(fact), wanted)
      : cm_tss_pick_conjunct(conjunct2_rule(fact), wanted);
}

PROOF static thm cm_tss_r_push_result(
    term parent, term child, term old_st, term next_st,
    term frame, term phase, thm task_ready, thm child_wf,
    thm child_scalar, thm phase_static, thm phase_parent,
    thm next_fid, thm phase_input, thm phase_expr) {
  thm phase_result = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_result_type_ready_def(),
        get_cm_phase_result_type_def())),
      `cm_phase_result_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase} (cm_ann_cursors (ann:cm_annotation))`));
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `q:cm_program`, `fid:int`, parent, child,
      old_st, next_st, `ks:(cm_frame)list`, frame,
      `ann:cm_annotation`, phase, `cm_ann_pc (ann:cm_annotation)`,
      `cm_ann_temp (ann:cm_annotation)`,
      `cm_ann_break (ann:cm_annotation)`,
      `cm_ann_continue (ann:cm_annotation)`),
      cm_s_r_push_task_ready);
  thm_list premises = THM_LIST(task_ready, child_wf, child_scalar,
      phase_static, phase_parent, phase_result, next_fid,
      phase_input, phase_expr);
  for (size_t i = 0; i < vector_size(premises); ++i) {
    result = mp_rule(result, premises[i]);
  }
  return result;
}

PROOF static thm cm_tss_s_push_result(
    term parent, term child, term old_st, term next_st,
    term frame, term phase, thm task_ready, thm child_wf,
    thm phase_static, thm phase_parent, thm next_fid) {
  thm phase_result = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_result_type_ready_def(),
        get_cm_phase_result_type_def())),
      `cm_phase_result_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase} (cm_ann_cursors (ann:cm_annotation))`));
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `q:cm_program`, `fid:int`, parent, child,
      old_st, next_st, `ks:(cm_frame)list`, frame,
      `ann:cm_annotation`, phase, `cm_ann_pc (ann:cm_annotation)`,
      `cm_ann_temp (ann:cm_annotation)`,
      `cm_ann_break (ann:cm_annotation)`,
      `cm_ann_continue (ann:cm_annotation)`),
      cm_s_s_push_task_ready);
  thm_list premises = THM_LIST(task_ready, child_wf,
      phase_static, phase_parent, phase_result, next_fid);
  for (size_t i = 0; i < vector_size(premises); ++i) {
    result = mp_rule(result, premises[i]);
  }
  return result;
}

PROOF static thm cm_tss_control_result(
    term parent, term control, term old_st, term next_st,
    thm task_ready, thm control_ready) {
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `q:cm_program`, `fid:int`, parent, control,
      old_st, next_st, `ks:(cm_frame)list`, `ann:cm_annotation`,
      `ann:cm_annotation`), cm_s_control_task_ready);
  result = mp_rule(result, task_ready);
  result = mp_rule(result, control_ready);
  return mp_rule(result, refl_rule(
      `cm_ann_cursors (ann:cm_annotation)`));
}

PROOF static void cm_tss_finish(
    gnode branch, thm shape, thm same_program,
    thm result, thm_list extra_rules) {
  thm_list rules = THM_LIST(
      shape, same_program, get_cm_step_def(), get_cm_sstart_def(),
      cm_annotation_step_def, cm_update_s_def,
      cm_update_annotation_def);
  for (size_t i = 0; i < vector_size(extra_rules); ++i) {
    vector_add(&rules, extra_rules[i]);
  }
  thm normalized = conv_rule(reduce_rewrite_conv(rules), result);
  thm target_view = apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(branch->g));
  ACCEPT_TAC(branch, eq_mp_rule(sym_rule(target_view), normalized));
}

PROOF static thm cm_tss_trivial_phase(term assertion, thm definition) {
  return eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(definition)), assertion));
}

PROOF static thm cm_prove_s_type_ready_step(void) {
  term task =
      `CMSTask (q:cm_program) (fid:int) (stmt:cm_stmt)
        (st:cm_src_state) (ks:(cm_frame)list)`;
  term function =
      `inth (fid:int) (cm_program_functions (p:cm_program))`;
  term old_cursors = `cm_ann_cursors (ann:cm_annotation)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (q:cm_program) (fid:int) (stmt:cm_stmt)
         (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         cm_typed_program p ==>
         cm_task_succeeds (CMSTask q fid stmt st ks) ==>
         cm_annotation_erases (CMSTask q fid stmt st ks) ann ==>
         cm_task_type_ready p (CMSTask q fid stmt st ks) ann ==>
         cm_task_type_ready p
           (cm_step (CMSTask q fid stmt st ks))
           (cm_update_annotation
             (cm_annotation_step (CMSTask q fid stmt st ks) ann))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm typed = assume_rule(`cm_typed_program (p:cm_program)`);
  thm task_ready = assume_rule(
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        (ann:cm_annotation)`);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`stmt:cm_stmt`, get_cm_stmt_cases()), "Hstmt");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (is_exists(goal_lasmps(branch->g)[
        labeled_term_list_index(goal_lasmps(branch->g), "Hstmt")].tm)) {
      branch = ASMP_EXISTS_TAC(branch, "Hstmt", NULL);
    }
    thm shape = assume_rule(goal_lasmps(branch->g)[
        labeled_term_list_index(goal_lasmps(branch->g), "Hstmt")].tm);
    thm shaped_ready = conv_rule(rewrite_conv(THM_LIST(shape)),
        task_ready);
    thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_task_type_ready_def())), shaped_ready);
    thm same_program = cm_tss_pick_conjunct(
        opened, `(q:cm_program) == (p:cm_program)`);
    thm fid_low = cm_tss_pick_conjunct(opened, `0i <= (fid:int)`);
    thm fid_high = cm_tss_pick_conjunct(opened,
        `(fid:int) < ilength
          (cm_program_functions (p:cm_program))`);
    thm cursors_ready = cm_tss_pick_conjunct(opened,
        `cm_cursors_type_ready (p:cm_program) (fid:int)
          ${old_cursors:(cm_acursor)list}`);
    term concrete_stmt = rhs_of(shape);
    thm statement_wf = cm_tss_pick_conjunct(opened,
        mk_comb(mk_comb(mk_comb(mk_comb(`cm_stmt_wf`,
          `p:cm_program`), function), `T`), concrete_stmt));
    thm wf_open = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_stmt_wf_def())), statement_wf);
    if (i == 0 || i == 2 || i == 8 || i == 9) {
      term control = i == 0 || i == 2 ? `CMNormal` :
          (i == 8 ? `CMBreak` : `CMContinue`);
      term next_state = i == 2
          ? `cm_activate_local (p:cm_program) (fid:int)
              (a:int) (st:cm_src_state)`
          : `st:cm_src_state`;
      thm control_ready = cm_tss_trivial_phase(
          `cm_control_type_ready (p:cm_program) (fid:int)
            ${control:cm_control}`,
          get_cm_control_type_ready_def());
      thm result = cm_tss_control_result(
          concrete_stmt, control, `st:cm_src_state`, next_state,
          shaped_ready, control_ready);
      thm_list extras = THM_LIST();
      if (i == 2) {
        thm slot_low = cm_tss_pick_conjunct(wf_open,
            `0i <= (a:int)`);
        thm slot_high = cm_tss_pick_conjunct(wf_open,
            `(a:int) < ilength
              (cm_function_locals ${function:cm_function_d})`);
        thm local_ok = eqt_elim_rule(apply_conversion(
            reduce_rewrite_conv(THM_LIST(
              get_cm_local_slot_ok_def(), fid_low, fid_high,
              slot_low, slot_high)),
            `cm_local_slot_ok (p:cm_program) (fid:int) (a:int)`));
        vector_add(&extras, local_ok);
      }
      cm_tss_finish(branch, shape, same_program, result, extras);
    } else if (i == 1) {
      term child = `a:cm_expr`;
      term phase = `CAExprStmtP`;
      thm child_wf = cm_tss_pick_conjunct(wf_open,
          `cm_expr_wf (p:cm_program) ${function:cm_function_d}
            ${child:cm_expr}`);
      thm child_scalar = cm_tss_pick_conjunct(wf_open,
          `cm_scalar_expr_type (cm_expr_type ${child:cm_expr})`);
      thm phase_static = cm_tss_trivial_phase(
          `cm_phase_static_type_ready (p:cm_program) (fid:int)
            ${phase:cm_aphase}`,
          get_cm_phase_static_type_ready_def());
      thm phase_parent = cm_tss_trivial_phase(
          `cm_phase_parent_type_ready (p:cm_program) (fid:int)
            ${phase:cm_aphase} ${old_cursors:(cm_acursor)list}`,
          get_cm_phase_parent_type_ready_def());
      thm next_fid = cm_tss_trivial_phase(
          `cm_phase_next_fid (fid:int) ${phase:cm_aphase} == fid`,
          cm_phase_next_fid_def);
      thm phase_input = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_cm_phase_input_type_ready_def(), child_scalar)),
          `cm_phase_input_type_ready (p:cm_program) (fid:int)
            ${phase:cm_aphase} (cm_expr_type ${child:cm_expr})`));
      thm phase_expr = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_cm_phase_expr_type_ready_def(), child_scalar)),
          `cm_phase_expr_type_ready (p:cm_program) (fid:int)
            ${phase:cm_aphase} ${child:cm_expr}`));
      thm result = cm_tss_r_push_result(concrete_stmt, child,
          `st:cm_src_state`, `st:cm_src_state`, `CMExprStmtK`, phase,
          shaped_ready, child_wf, child_scalar, phase_static,
          phase_parent, next_fid, phase_input, phase_expr);
      cm_tss_finish(branch, shape, same_program, result, THM_LIST());
    } else if (i == 3) {
      term child = `a1:cm_expr`;
      term phase = `CAInitP (a0:int)`;
      thm slot_low = cm_tss_pick_conjunct(wf_open,
          `0i <= (a0:int)`);
      thm slot_high = cm_tss_pick_conjunct(wf_open,
          `(a0:int) < ilength
            (cm_function_locals ${function:cm_function_d})`);
      thm count_zero = cm_tss_pick_conjunct(wf_open,
          `cm_slot_count
            (inth (a0:int) (cm_function_locals ${function:cm_function_d}))
           == 0i`);
      thm child_wf = cm_tss_pick_conjunct(wf_open,
          `cm_expr_wf (p:cm_program) ${function:cm_function_d}
            ${child:cm_expr}`);
      term slot_type =
          `cm_slot_ty
            (inth (a0:int) (cm_function_locals ${function:cm_function_d}))`;
      thm convertible = cm_tss_pick_conjunct(wf_open,
          `cm_expr_convertible ${child:cm_expr} ${slot_type:cm_type}`);
      thm child_scalar = match_mp_rule(specl_rule(TERM_LIST(
          child, slot_type), cm_expr_convertible_source_scalar),
          convertible);
      thm slot_scalar = mp_rule(mp_rule(mp_rule(mp_rule(mp_rule(
          specl_rule(TERM_LIST(`p:cm_program`, `fid:int`, `a0:int`),
            cm_local_slot_scalar_type), typed), fid_low), fid_high),
          slot_low), slot_high);
      thm phase_static = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_cm_phase_static_type_ready_def(), slot_low, slot_high,
            count_zero, slot_scalar)),
          `cm_phase_static_type_ready (p:cm_program) (fid:int)
            ${phase:cm_aphase}`));
      thm phase_parent = cm_tss_trivial_phase(
          `cm_phase_parent_type_ready (p:cm_program) (fid:int)
            ${phase:cm_aphase} ${old_cursors:(cm_acursor)list}`,
          get_cm_phase_parent_type_ready_def());
      thm next_fid = cm_tss_trivial_phase(
          `cm_phase_next_fid (fid:int) ${phase:cm_aphase} == fid`,
          cm_phase_next_fid_def);
      thm phase_input = cm_tss_trivial_phase(
          `cm_phase_input_type_ready (p:cm_program) (fid:int)
            ${phase:cm_aphase} (cm_expr_type ${child:cm_expr})`,
          get_cm_phase_input_type_ready_def());
      thm phase_expr = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_cm_phase_expr_type_ready_def(), convertible)),
          `cm_phase_expr_type_ready (p:cm_program) (fid:int)
            ${phase:cm_aphase} ${child:cm_expr}`));
      term next_state =
          `cm_activate_local (p:cm_program) (fid:int)
            (a0:int) (st:cm_src_state)`;
      thm result = cm_tss_r_push_result(concrete_stmt, child,
          `st:cm_src_state`, next_state, `CMInitK (a0:int)`, phase,
          shaped_ready, child_wf, child_scalar, phase_static,
          phase_parent, next_fid, phase_input, phase_expr);
      thm local_ok = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_cm_local_slot_ok_def(), fid_low, fid_high,
            slot_low, slot_high)),
          `cm_local_slot_ok (p:cm_program) (fid:int) (a0:int)`));
      cm_tss_finish(branch, shape, same_program, result,
          THM_LIST(local_ok));
    } else if (i == 4 || i == 5) {
      term child = i == 4 ? `a0:cm_stmt` : `a:cm_stmt`;
      term phase = i == 4
          ? `CASeqP (a1:cm_stmt)`
          : `CABlockP (cm_state_env (st:cm_src_state))
              (cm_state_regions st) F 0i`;
      term frame = i == 4
          ? `CMSeqK (a1:cm_stmt)`
          : `CMBlockK (cm_state_env (st:cm_src_state))
              (cm_state_regions st)`;
      thm child_wf = cm_tss_pick_conjunct(wf_open,
          `cm_stmt_wf (p:cm_program) ${function:cm_function_d}
            T ${child:cm_stmt}`);
      thm phase_static;
      if (i == 4) {
        thm second_wf = cm_tss_pick_conjunct(wf_open,
            `cm_stmt_wf (p:cm_program) ${function:cm_function_d}
              T (a1:cm_stmt)`);
        phase_static = eqt_elim_rule(apply_conversion(
            reduce_rewrite_conv(THM_LIST(
              get_cm_phase_static_type_ready_def(), second_wf)),
            `cm_phase_static_type_ready (p:cm_program) (fid:int)
              ${phase:cm_aphase}`));
      } else {
        phase_static = cm_tss_trivial_phase(
            `cm_phase_static_type_ready (p:cm_program) (fid:int)
              ${phase:cm_aphase}`,
            get_cm_phase_static_type_ready_def());
      }
      thm phase_parent = cm_tss_trivial_phase(
          `cm_phase_parent_type_ready (p:cm_program) (fid:int)
            ${phase:cm_aphase} ${old_cursors:(cm_acursor)list}`,
          get_cm_phase_parent_type_ready_def());
      thm next_fid = cm_tss_trivial_phase(
          `cm_phase_next_fid (fid:int) ${phase:cm_aphase} == fid`,
          cm_phase_next_fid_def);
      thm result = cm_tss_s_push_result(concrete_stmt, child,
          `st:cm_src_state`, `st:cm_src_state`, frame, phase,
          shaped_ready, child_wf, phase_static, phase_parent, next_fid);
      cm_tss_finish(branch, shape, same_program, result, THM_LIST());
    } else if (i == 6 || i == 7) {
      term child = `a0:cm_expr`;
      term phase = i == 6
          ? `CAIfP (a1:cm_stmt) (a2:cm_stmt)`
          : `CAWhileGuardP (a0:cm_expr) (a1:cm_stmt)
              (cm_ann_pc (ann:cm_annotation))
              (cm_ann_pc ann +
               cm_stmt_code_count (p:cm_program) (fid:int)
                 (CMWhileS (a0:cm_expr) (a1:cm_stmt)))`;
      term frame = i == 6
          ? `CMIfK (a1:cm_stmt) (a2:cm_stmt)`
          : `CMWhileGuardK (a0:cm_expr) (a1:cm_stmt)`;
      thm child_wf = cm_tss_pick_conjunct(wf_open,
          `cm_expr_wf (p:cm_program) ${function:cm_function_d}
            ${child:cm_expr}`);
      thm condition_kind = cm_tss_pick_conjunct(wf_open,
          `cm_expr_type ${child:cm_expr} == CMIntTy ||
           cm_expr_type ${child:cm_expr} == CMCharTy ||
           cm_is_pointer (cm_expr_type ${child:cm_expr})`);
      thm child_scalar = match_mp_rule(spec_rule(
          `cm_expr_type ${child:cm_expr}`, cm_condition_type_scalar),
          condition_kind);
      thm phase_static;
      if (i == 6) {
        thm yes_wf = cm_tss_pick_conjunct(wf_open,
            `cm_stmt_wf (p:cm_program) ${function:cm_function_d}
              T (a1:cm_stmt)`);
        thm no_wf = cm_tss_pick_conjunct(wf_open,
            `cm_stmt_wf (p:cm_program) ${function:cm_function_d}
              T (a2:cm_stmt)`);
        phase_static = eqt_elim_rule(apply_conversion(
            reduce_rewrite_conv(THM_LIST(
              get_cm_phase_static_type_ready_def(), yes_wf, no_wf)),
            `cm_phase_static_type_ready (p:cm_program) (fid:int)
              ${phase:cm_aphase}`));
      } else {
        thm body_wf = cm_tss_pick_conjunct(wf_open,
            `cm_stmt_wf (p:cm_program) ${function:cm_function_d}
              T (a1:cm_stmt)`);
        phase_static = eqt_elim_rule(apply_conversion(
            reduce_rewrite_conv(THM_LIST(
              get_cm_phase_static_type_ready_def(), child_wf,
              child_scalar, body_wf)),
            `cm_phase_static_type_ready (p:cm_program) (fid:int)
              ${phase:cm_aphase}`));
      }
      thm phase_parent = cm_tss_trivial_phase(
          `cm_phase_parent_type_ready (p:cm_program) (fid:int)
            ${phase:cm_aphase} ${old_cursors:(cm_acursor)list}`,
          get_cm_phase_parent_type_ready_def());
      thm next_fid = cm_tss_trivial_phase(
          `cm_phase_next_fid (fid:int) ${phase:cm_aphase} == fid`,
          cm_phase_next_fid_def);
      thm phase_input = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_cm_phase_input_type_ready_def(), child_scalar)),
          `cm_phase_input_type_ready (p:cm_program) (fid:int)
            ${phase:cm_aphase} (cm_expr_type ${child:cm_expr})`));
      thm phase_expr = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_cm_phase_expr_type_ready_def(), child_scalar)),
          `cm_phase_expr_type_ready (p:cm_program) (fid:int)
            ${phase:cm_aphase} ${child:cm_expr}`));
      thm result = cm_tss_r_push_result(concrete_stmt, child,
          `st:cm_src_state`, `st:cm_src_state`, frame, phase,
          shaped_ready, child_wf, child_scalar, phase_static,
          phase_parent, next_fid, phase_input, phase_expr);
      cm_tss_finish(branch, shape, same_program, result, THM_LIST());
    } else {
      term child = `a:cm_expr`;
      term phase = `CAReturnP`;
      thm child_wf = cm_tss_pick_conjunct(wf_open,
          `cm_expr_wf (p:cm_program) ${function:cm_function_d}
            ${child:cm_expr}`);
      thm convertible = cm_tss_pick_conjunct(wf_open,
          `cm_expr_convertible ${child:cm_expr}
            (cm_function_ret ${function:cm_function_d})`);
      thm child_scalar = match_mp_rule(specl_rule(TERM_LIST(
          child, `cm_function_ret ${function:cm_function_d}`),
          cm_expr_convertible_source_scalar), convertible);
      thm phase_static = cm_tss_trivial_phase(
          `cm_phase_static_type_ready (p:cm_program) (fid:int)
            ${phase:cm_aphase}`,
          get_cm_phase_static_type_ready_def());
      thm phase_parent = cm_tss_trivial_phase(
          `cm_phase_parent_type_ready (p:cm_program) (fid:int)
            ${phase:cm_aphase} ${old_cursors:(cm_acursor)list}`,
          get_cm_phase_parent_type_ready_def());
      thm next_fid = cm_tss_trivial_phase(
          `cm_phase_next_fid (fid:int) ${phase:cm_aphase} == fid`,
          cm_phase_next_fid_def);
      thm phase_input = cm_tss_trivial_phase(
          `cm_phase_input_type_ready (p:cm_program) (fid:int)
            ${phase:cm_aphase} (cm_expr_type ${child:cm_expr})`,
          get_cm_phase_input_type_ready_def());
      thm phase_expr = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_cm_phase_expr_type_ready_def(), convertible)),
          `cm_phase_expr_type_ready (p:cm_program) (fid:int)
            ${phase:cm_aphase} ${child:cm_expr}`));
      thm result = cm_tss_r_push_result(concrete_stmt, child,
          `st:cm_src_state`, `st:cm_src_state`, `CMReturnK`, phase,
          shaped_ready, child_wf, child_scalar, phase_static,
          phase_parent, next_fid, phase_input, phase_expr);
      cm_tss_finish(branch, shape, same_program, result, THM_LIST());
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_s_type_ready_step = cm_prove_s_type_ready_step();

PROOF static int cmc_preservation_type_source_s_final_checks(void) {
  ENSURE_COND(vector_size(hyp(cm_s_type_ready_step)) == 0,
      "statement type theorem has assumptions");
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_type_source_s_axioms_before,
      "cmc_preservation_type_source_s introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_type_source_s_checks =
    cmc_preservation_type_source_s_final_checks();
