#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "userlib/proof_patterns.h"
#include "cmc_preservation_target_stmt.h"
#include "cmc_preservation_invariant_transition.h"

#require "userlib/proof_patterns.c"
#require "cmc_preservation_target_state.c"
#require "cmc_preservation_generation.c"
#require "cmc_preservation_binding_numeric.c"
#require "cmc_preservation_invariant_transition.c"

PROOF static size_t _cmc_preservation_target_stmt_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_target_stmt_consequence(
    const thm premise, const term conclusion) {
  return mp_rule(taut_rule(mk_imp(concl(premise), conclusion)), premise);
}
PROOF static term cm_target_stmt_app_arg_from_right(
    term application, size_t offset) {
  for (size_t i = 0; i < offset; ++i) {
    application = dest_comb(application).tm1;
  }
  return dest_comb(application).tm2;
}

PROOF static term cm_target_stmt_constructor_arg(
    term constructor, size_t arity, size_t index) {
  return cm_target_stmt_app_arg_from_right(
      constructor, arity - index - 1);
}


PROOF static void cm_target_stmt_accept(
    const gnode branch, const thm shape, const thm result) {
  thm_list rules = THM_LIST(shape);
  thm normalized = conv_rule(reduce_rewrite_conv(rules), result);
  thm target_view = apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(branch->g));
  ACCEPT_TAC(branch, eq_mp_rule(sym_rule(target_view), normalized));
}

PROOF static thm cm_prove_target_s_same_step(const term statement) {
  term task =
      `CMSTask (p:cm_program) (fid:int) ${statement:cm_stmt}
        (st:cm_src_state) (ks:(cm_frame)list)`;
  term update =
      `cm_annotation_step ${task:cm_task} (ann:cm_annotation)`;
  term target_sim =
      `cm_task_target_sim (p:cm_program)
        (cm_step ${task:cm_task})
        (tvm_iter (cm_update_steps ${update:cm_aupdate})
          (target:tvm_task))
        (cm_update_annotation ${update:cm_aupdate})`;
  term body = mk_imp(
      `cm_task_target_sim (p:cm_program) ${task:cm_task}
        (target:tvm_task) (ann:cm_annotation)`, target_sim);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm running = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_target_sim_def)), assume_rule(
        `cm_task_target_sim (p:cm_program) ${task:cm_task}
          (target:tvm_task) (ann:cm_annotation)`));
  term updated = `cm_update_annotation ${update:cm_aupdate}`;
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `[]:(cm_value)list`, `ann:cm_annotation`, updated,
      `target:tvm_task`), get_cm_target_reannotate());
  thm_list annotation_rules = THM_LIST(
      cm_annotation_step_def, cm_update_s_def,
      cm_update_annotation_def, cm_ann_push_def,
      cm_ann_pc_def, cm_ann_calls_def, cm_ann_spills_def,
      cm_ann_saved_def);
  term_list selectors = TERM_LIST(
      `cm_ann_pc:cm_annotation->int`,
      `cm_ann_calls:cm_annotation->(cm_call_sim_frame)list`,
      `cm_ann_spills:cm_annotation->(cm_spill)list`,
      `cm_ann_saved:cm_annotation->(cm_spill_frame)list`);
  for (size_t i = 0; i < vector_size(selectors); ++i) {
    term equality = mk_eq(
        mk_comb(selectors[i], updated),
        mk_comb(selectors[i], `ann:cm_annotation`));
    result = match_mp_rule(result, eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(annotation_rules), equality)));
  }
  result = match_mp_rule(result, running);
  result = conv_rule(reduce_rewrite_conv(annotation_rules), result);
  thm_list finish_rules = THM_LIST(
      get_cm_step_def(), get_cm_sstart_def(),
      cm_annotation_step_def, cm_update_s_def,
      cm_update_steps_def, cm_update_annotation_def,
      cm_ann_push_def, get_tvm_iter_def(),
      cm_task_target_sim_def, get_cm_control_kind_def(),
      get_cm_control_value_def(), get_cm_control_status_def());
  thm normalized = conv_rule(reduce_rewrite_conv(finish_rules), result);
  thm target_view = apply_conversion(
      reduce_rewrite_conv(finish_rules), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), normalized));
  return gnode_prove(root);
}

PROOF static thm cm_target_s_skip_step =
    cm_prove_target_s_same_step(`CMSkipS:cm_stmt`);
PROOF static thm cm_target_s_expr_step =
    cm_prove_target_s_same_step(`CMExprS (expr:cm_expr)`);
PROOF static thm cm_target_s_seq_step =
    cm_prove_target_s_same_step(
      `CMSeqS (first:cm_stmt) (second:cm_stmt)`);
PROOF static thm cm_target_s_block_step =
    cm_prove_target_s_same_step(`CMBlockS (body:cm_stmt)`);
PROOF static thm cm_target_s_if_step =
    cm_prove_target_s_same_step(
      `CMIfS (guard:cm_expr) (yes:cm_stmt) (no:cm_stmt)`);
PROOF static thm cm_target_s_while_step =
    cm_prove_target_s_same_step(
      `CMWhileS (guard:cm_expr) (body:cm_stmt)`);
PROOF static thm cm_target_s_break_step =
    cm_prove_target_s_same_step(`CMBreakS:cm_stmt`);
PROOF static thm cm_target_s_continue_step =
    cm_prove_target_s_same_step(`CMContinueS:cm_stmt`);
PROOF static thm cm_target_s_return_step =
    cm_prove_target_s_same_step(`CMReturnS (expr:cm_expr)`);

PROOF static thm cm_prove_target_s_activate_step(const bool initialized) {
  term statement = initialized
      ? `CMInitS (slot:int) (expr:cm_expr)`
      : `CMDeclS (slot:int)`;
  term task =
      `CMSTask (p:cm_program) (fid:int) ${statement:cm_stmt}
        (st:cm_src_state) (ks:(cm_frame)list)`;
  term update =
      `cm_annotation_step ${task:cm_task} (ann:cm_annotation)`;
  term width =
      `cm_slot_size (cm_program_structs (p:cm_program))
        (inth (slot:int) (cm_function_locals
          (inth (fid:int) (cm_program_functions p))))`;
  term target_sim =
      `cm_task_target_sim (p:cm_program)
        (cm_step ${task:cm_task})
        (tvm_iter (cm_update_steps ${update:cm_aupdate})
          (target:tvm_task))
        (cm_update_annotation ${update:cm_aupdate})`;
  term body = imp_chain(TERM_LIST(
      `cm_local_slot_ok (p:cm_program) (fid:int) (slot:int)`,
      `cm_regions_before (cm_state_regions (st:cm_src_state))
        (cm_state_nextgen st)`,
      `cm_state_tags_generation_below (st:cm_src_state)
        (cm_state_nextgen st)`,
      `0i < ${width:int}`,
      `cm_spill_frames_generation_below (cm_state_nextgen st)
        (cm_active_spill_frames fid st (ann:cm_annotation))`,
      `cm_task_target_sim p ${task:cm_task}
        (target:tvm_task) ann`), target_sim);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm running = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_target_sim_def)), assume_rule(
        `cm_task_target_sim (p:cm_program) ${task:cm_task}
          (target:tvm_task) (ann:cm_annotation)`));
  thm activated = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `slot:int`, `st:cm_src_state`,
      `ann:cm_annotation`, `target:tvm_task`),
      get_cm_target_activate_local_empty());
  activated = match_mp_rule(activated, assume_rule(
      `cm_regions_before (cm_state_regions (st:cm_src_state))
        (cm_state_nextgen st)`));
  activated = match_mp_rule(activated, assume_rule(
      `cm_state_tags_generation_below (st:cm_src_state)
        (cm_state_nextgen st)`));
  activated = match_mp_rule(activated,
      assume_rule(`0i < ${width:int}`));
  activated = match_mp_rule(activated, assume_rule(
      `cm_spill_frames_generation_below (cm_state_nextgen st)
        (cm_active_spill_frames (fid:int) st (ann:cm_annotation))`));
  activated = match_mp_rule(activated, running);
  term updated = `cm_update_annotation ${update:cm_aupdate}`;
  term new_state =
      `cm_activate_local (p:cm_program) (fid:int) (slot:int)
        (st:cm_src_state)`;
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, new_state,
      `[]:(cm_value)list`, `ann:cm_annotation`, updated,
      `target:tvm_task`), get_cm_target_reannotate());
  thm_list annotation_rules = THM_LIST(
      cm_annotation_step_def, cm_update_s_def,
      cm_update_annotation_def, cm_ann_push_def,
      cm_ann_pc_def, cm_ann_calls_def, cm_ann_spills_def,
      cm_ann_saved_def,
      assume_rule(`cm_local_slot_ok (p:cm_program) (fid:int) (slot:int)`));
  term_list selectors = TERM_LIST(
      `cm_ann_pc:cm_annotation->int`,
      `cm_ann_calls:cm_annotation->(cm_call_sim_frame)list`,
      `cm_ann_spills:cm_annotation->(cm_spill)list`,
      `cm_ann_saved:cm_annotation->(cm_spill_frame)list`);
  for (size_t i = 0; i < vector_size(selectors); ++i) {
    term equality = mk_eq(
        mk_comb(selectors[i], updated),
        mk_comb(selectors[i], `ann:cm_annotation`));
    result = match_mp_rule(result, eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(annotation_rules), equality)));
  }
  result = match_mp_rule(result, activated);
  thm_list finish_rules = THM_LIST(
      get_cm_step_def(), get_cm_sstart_def(),
      cm_annotation_step_def, cm_update_s_def,
      cm_update_steps_def, cm_update_annotation_def,
      cm_ann_push_def, get_tvm_iter_def(),
      cm_task_target_sim_def, get_cm_control_kind_def(),
      get_cm_control_value_def(), get_cm_control_status_def(),
      assume_rule(`cm_local_slot_ok (p:cm_program) (fid:int) (slot:int)`));
  thm normalized = conv_rule(reduce_rewrite_conv(finish_rules), result);
  thm target_view = apply_conversion(
      reduce_rewrite_conv(finish_rules), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), normalized));
  return gnode_prove(root);
}

PROOF static thm cm_target_s_decl_step =
    cm_prove_target_s_activate_step(false);
PROOF static thm cm_target_s_init_step =
    cm_prove_target_s_activate_step(true);

PROOF static thm cm_prove_target_s_step(void) {
  term task =
      `CMSTask (p:cm_program) (fid:int) (stmt:cm_stmt)
        (st:cm_src_state) (ks:(cm_frame)list)`;
  term update =
      `cm_annotation_step ${task:cm_task} (ann:cm_annotation)`;
  term result_term =
      `cm_task_target_sim (p:cm_program) (cm_step ${task:cm_task})
        (tvm_iter (cm_update_steps ${update:cm_aupdate})
          (target:tvm_task))
        (cm_update_annotation ${update:cm_aupdate})`;
  term body = imp_chain(TERM_LIST(
      `cm_runtime_step_ready p ${task:cm_task} (ann:cm_annotation)`,
      `cm_task_runtime_invariant p ${task:cm_task} ann`,
      `cm_task_generation_safe p ${task:cm_task} ann`,
      `cm_task_target_sim p ${task:cm_task}
        (target:tvm_task) ann`), result_term);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);
  thm readiness = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_runtime_step_ready_def)), assume_rule(
        `cm_runtime_step_ready (p:cm_program) ${task:cm_task}
          (ann:cm_annotation)`));
  thm typed = conjunct1_rule(readiness);
  thm fid_lower = conjunct1_rule(conjunct2_rule(readiness));
  thm layout_ready = conjunct2_rule(conjunct2_rule(readiness));
  thm stmt_ready = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_layout_ready_def)), layout_ready);
  thm runtime = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_runtime_invariant_def)), assume_rule(
        `cm_task_runtime_invariant (p:cm_program) ${task:cm_task}
          (ann:cm_annotation)`));
  thm regions_before = conjunct1_rule(runtime);
  thm runtime_stack = conjunct2_rule(runtime);
  thm generation_safe = conv_rule(rewrite_conv(THM_LIST(
      cm_task_generation_safe_def)), assume_rule(
        `cm_task_generation_safe (p:cm_program) ${task:cm_task}
          (ann:cm_annotation)`));
  thm task_generation = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_generation_below_def)), conjunct1_rule(generation_safe));
  thm state_generation = conv_rule(rewrite_conv(THM_LIST(
      cm_state_generation_below_def)), conjunct1_rule(task_generation));
  thm all_tags = cm_target_stmt_consequence(state_generation,
      `cm_tags_generation_below (cm_state_nextgen (st:cm_src_state))
        (cm_state_tags st)`);
  thm state_tags = match_mp_rule(specl_rule(TERM_LIST(
      `st:cm_src_state`, `cm_state_nextgen (st:cm_src_state)`),
      get_cm_state_tags_generation_from_all()), all_tags);
  thm spill_below = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_annotation_generation_below_def)),
      conjunct2_rule(generation_safe));
  thm fid_valid = match_mp_rule(cm_runtime_stack_fid_valid,
      runtime_stack);
  thm fid_bounds = mp_rule(int_arith_rule(mk_imp(
      concl(conj_rule(fid_lower, fid_valid)),
      `0i <= (fid:int) &&
       fid < ilength (cm_program_functions (p:cm_program))`)),
      conj_rule(fid_lower, fid_valid));
  thm typed_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_typed_program_def())), typed);
  thm functions_wf = cm_target_stmt_consequence(typed_open,
      `!(i:int). 0i <= i ==>
        i < ilength (cm_program_functions (p:cm_program)) ==>
        cm_function_wf p (inth i (cm_program_functions p))`);
  thm function_wf = match_mp_rule(match_mp_rule(
      spec_rule(`fid:int`, functions_wf),
      conjunct1_rule(fid_bounds)), conjunct2_rule(fid_bounds));
  thm function_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_function_wf_def())), function_wf);
  term locals =
      `cm_function_locals
        (inth (fid:int) (cm_program_functions (p:cm_program)))`;
  thm locals_wf = cm_target_stmt_consequence(function_open,
      `cm_slots_wf (cm_program_structs (p:cm_program))
        ${locals:(cm_slot_d)list}`);
  thm slots_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_slots_wf_def())), locals_wf);
  thm old_sim = assume_rule(
      `cm_task_target_sim (p:cm_program) ${task:cm_task}
        (target:tvm_task) (ann:cm_annotation)`);

  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`stmt:cm_stmt`, get_cm_stmt_cases()), "Hstmt");
  thm same_steps[11] = {
    cm_target_s_skip_step, cm_target_s_expr_step,
    empty_theorem, empty_theorem,
    cm_target_s_seq_step, cm_target_s_block_step,
    cm_target_s_if_step, cm_target_s_while_step,
    cm_target_s_break_step, cm_target_s_continue_step,
    cm_target_s_return_step
  };
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (is_exists(goal_lasmps(branch->g)[
        labeled_term_list_index(goal_lasmps(branch->g), "Hstmt")].tm)) {
      branch = ASMP_EXISTS_TAC(branch, "Hstmt", NULL);
    }
    thm shape = assume_rule(goal_lasmps(branch->g)[
        labeled_term_list_index(goal_lasmps(branch->g), "Hstmt")].tm);
    term concrete = rhs_of(shape);
    thm shaped_sim = conv_rule(rewrite_conv(THM_LIST(shape)), old_sim);
    if (i != 2 && i != 3) {
      cm_target_stmt_accept(branch, shape,
          match_mp_rule(same_steps[i], shaped_sim));
      continue;
    }
    term slot = cm_target_stmt_constructor_arg(
        concrete, i == 2 ? 1 : 2, 0);
    thm local_ok = conv_rule(reduce_rewrite_conv(THM_LIST(
        shape, get_cm_stmt_start_safe_def())), stmt_ready);
    thm local_open = conv_rule(rewrite_conv(THM_LIST(
        get_cm_local_slot_ok_def())), local_ok);
    thm slot_lower =
        conjunct1_rule(conjunct2_rule(conjunct2_rule(local_open)));
    thm slot_upper =
        conjunct2_rule(conjunct2_rule(conjunct2_rule(local_open)));
    thm slot_wf = match_mp_rule(match_mp_rule(
        spec_rule(slot, slots_open), slot_lower), slot_upper);
    thm width_positive = cm_target_stmt_consequence(
        conv_rule(rewrite_conv(THM_LIST(get_cm_slot_wf_def())), slot_wf),
        `0i < cm_slot_size (cm_program_structs (p:cm_program))
          (inth ${slot:int} ${locals:(cm_slot_d)list})`);
    thm result = i == 2 ? cm_target_s_decl_step : cm_target_s_init_step;
    result = match_mp_rule(result, local_ok);
    result = match_mp_rule(result, regions_before);
    result = match_mp_rule(result, state_tags);
    result = match_mp_rule(result, width_positive);
    result = match_mp_rule(result, spill_below);
    result = match_mp_rule(result, shaped_sim);
    cm_target_stmt_accept(branch, shape, result);
  }
  return gnode_prove(root);
}
PROOF thm cm_target_s_step = cm_prove_target_s_step();

PROOF thm get_cm_target_s_step(void) {
  return cm_target_s_step;
}

PROOF static int cmc_preservation_target_stmt_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_stmt_axioms_before,
      "cmc_preservation_target_stmt introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_target_s_step)) == 0,
      "total statement target theorem has hypotheses");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_stmt_checks =
    cmc_preservation_target_stmt_final_checks();
