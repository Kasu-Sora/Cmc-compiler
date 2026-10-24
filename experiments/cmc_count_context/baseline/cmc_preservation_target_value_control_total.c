#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_target_value_control_total.h"
#include "cmc_preservation_target_value_branch.h"
#include "cmc_preservation_target_value_context.h"

#include "cmc_preservation_target_jump_valid.h"
#require "cmc_preservation_target_value_branch.c"
#require "cmc_preservation_target_value_context.c"

#require "cmc_preservation_target_jump_valid.c"
PROOF static size_t _cmc_preservation_target_value_control_total_axioms_before =
    vector_size(get_all_axioms());


PROOF static thm cm_control_total_apply(thm result, thm_list premises) {
  for (size_t i = 0; i < vector_size(premises); ++i) {
    result = match_mp_rule(result, premises[i]);
  }
  return result;
}

PROOF static void cm_control_total_accept(
    const gnode branch, const thm shape, const thm result) {
  thm_list rules = THM_LIST(shape, cm_phase_frame_def);
  thm normalized = conv_rule(reduce_rewrite_conv(rules), result);
  thm target_view = apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(branch->g));
  ACCEPT_TAC(branch, eq_mp_rule(sym_rule(target_view), normalized));
}


PROOF static thm cm_prove_target_v_control_step(void) {
  term phase = `phase:cm_aphase`;
  term cursors =
      `CMACursor ${phase:cm_aphase} (owner:int) (saved_break:int)
        (saved_continue:int) :: (rest:(cm_acursor)list)`;
  term frames =
      `cm_phase_frame ${phase:cm_aphase} ::
       cm_cursor_frames (rest:(cm_acursor)list)`;
  term task =
      `CMVTask (p:cm_program) (fid:int) (incoming:cm_value)
        (st:cm_src_state) ${frames:(cm_frame)list}`;
  term ann =
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
        ${cursors:(cm_acursor)list} (spills:(cm_spill)list)
        (saved:(cm_spill_frame)list) (calls:(cm_call_sim_frame)list)`;
  term update = `cm_annotation_step ${task:cm_task} ${ann:cm_annotation}`;
  term result_term =
      `cm_task_target_sim (p:cm_program) (cm_step ${task:cm_task})
        (tvm_iter (cm_update_steps ${update:cm_aupdate})
          (target:tvm_task))
        (cm_update_annotation ${update:cm_aupdate})`;
  term body = imp_chain(TERM_LIST(
      `cm_wf_program (p:cm_program)`,
      `cm_runtime_step_ready p ${task:cm_task} ${ann:cm_annotation}`,
      `cm_task_runtime_invariant p ${task:cm_task} ${ann:cm_annotation}`,
      `cm_task_type_ready p ${task:cm_task} ${ann:cm_annotation}`,
      `cm_task_fid_ready p ${task:cm_task}`,
      `cm_annotation_spill_consistent ${ann:cm_annotation}`,
      `cm_task_generation_safe p ${task:cm_task} ${ann:cm_annotation}`,
      `cm_task_tagged_valid ${task:cm_task}`,
      `cm_task_layout p ${task:cm_task} ${ann:cm_annotation}`,
      `cm_task_target_sim p ${task:cm_task} (target:tvm_task)
        ${ann:cm_annotation}`,
      `cm_v_phase_family ${phase:cm_aphase} == 3i`), result_term);
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);

  thm context = get_cm_target_v_context();
  context = cm_control_total_apply(context, THM_LIST(
      assume_rule(`cm_wf_program (p:cm_program)`),
      assume_rule(`cm_runtime_step_ready (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`),
      assume_rule(`cm_task_runtime_invariant (p:cm_program)
        ${task:cm_task} ${ann:cm_annotation}`),
      assume_rule(`cm_task_type_ready (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`),
      assume_rule(`cm_task_fid_ready (p:cm_program) ${task:cm_task}`),
      assume_rule(`cm_annotation_spill_consistent ${ann:cm_annotation}`),
      assume_rule(`cm_task_generation_safe (p:cm_program)
        ${task:cm_task} ${ann:cm_annotation}`),
      assume_rule(`cm_task_tagged_valid ${task:cm_task}`)));
  thm layout = assume_rule(
      `cm_task_layout (p:cm_program) ${task:cm_task} ${ann:cm_annotation}`);
  thm sim = assume_rule(
      `cm_task_target_sim (p:cm_program) ${task:cm_task}
        (target:tvm_task) ${ann:cm_annotation}`);
  thm family = assume_rule(`cm_v_phase_family ${phase:cm_aphase} == 3i`);
  thm wf = assume_rule(`cm_wf_program (p:cm_program)`);

  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(phase, get_datatype_cases("cm_aphase")), "Hphase");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(branch->g);
      int index = labeled_term_list_index(assumptions, "Hphase");
      if (!is_exists(assumptions[index].tm)) break;
      branch = ASMP_EXISTS_TAC(branch, "Hphase", NULL);
    }
    thm shape = assume_rule(goal_lasmps(branch->g)[
        labeled_term_list_index(goal_lasmps(branch->g), "Hphase")].tm);
    if (i != 17 && i != 18) {
      thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
          shape, get_cm_v_phase_family_def())), family);
      CONTR_TAC(branch, impossible);
      continue;
    }

    term concrete_phase = rhs_of(shape);
    thm_list shape_rules = THM_LIST(shape, cm_phase_frame_def);
    thm shaped_layout = conv_rule(reduce_rewrite_conv(shape_rules), layout);
    thm shaped_sim = conv_rule(reduce_rewrite_conv(shape_rules), sim);
    thm_list layout_rules = cm_v_layout_rules();
    vector_add(&layout_rules, get_cm_stmt_code_length());
    vector_add(&layout_rules, int_ring_rule(
        `!(a:int) (b:int) (c:int).
           a + 2i + b + c == a + 1i + b + 1i + c`));
    vector_add(&layout_rules, int_ring_rule(
        `!(a:int) (b:int). a + 2i + b == a + 1i + b + 1i`));
    vector_add(&layout_rules, get_theorem_by_name("ILENGTH_DEF"));
    vector_add(&layout_rules, get_theorem_by_name("APPEND"));
    vector_add(&layout_rules, get_theorem_by_name("APPEND_NIL"));
    thm opened = conv_rule(reduce_rewrite_conv(layout_rules), shaped_layout);
    opened = conv_rule(reduce_rewrite_conv(layout_rules), opened);
    thm code_at = conjunct1_rule(opened);
    term jump_pc = i == 17
        ? `(pc:int) + 1i +
            cm_stmt_code_count (p:cm_program) (fid:int) (a0:cm_stmt) + 1i`
        : `a3:int`;
    thm target_valid = match_mp_rule(cm_model_jump_valid, wf);
    target_valid = match_mp_rule(target_valid, code_at);
    target_valid = match_mp_rule(target_valid,
        eqt_elim_rule(apply_conversion(reduce_rewrite_conv(THM_LIST(
          get_tvm_opcode_is_target_def())),
          dest_imp(concl(target_valid)).tm1)));
    thm local = i == 17
        ? get_cm_target_v_if_step()
        : get_cm_target_v_while_guard_step();
    thm proved = cm_control_total_apply(local,
        THM_LIST(shaped_layout, shaped_sim, target_valid));
    cm_control_total_accept(branch, shape, proved);
  }
  (void)context;
  return gnode_prove(root);
}

PROOF thm cm_target_v_control_step =
    cm_prove_target_v_control_step();

PROOF thm get_cm_target_v_control_step(void) {
  return cm_target_v_control_step;
}

PROOF static int cmc_preservation_target_value_control_total_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_value_control_total_axioms_before,
      "cmc_preservation_target_value_control_total introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_target_v_control_step)) == 0,
      "control value target theorem is not closed");
  return 0;
err:
  return 1;
}
