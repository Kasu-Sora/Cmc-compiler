#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_target_task.h"
#include "cmc_preservation_state.h"
#include "cmc_preservation_type_ready.h"
#include "cmc_preservation_fid.h"
#include "cmc_preservation_spill_semantic.h"
#include "cmc_preservation_generation.h"
#include "cmc_preservation_tagged_task.h"
#include "cmc_preservation_layout.h"

#require "cmc_preservation_target_start.c"
#require "cmc_preservation_target_expr_total.c"
#require "cmc_preservation_target_stmt.c"
#require "cmc_preservation_target_value_total.c"
#require "cmc_preservation_target_control_total.c"
#require "cmc_preservation_target_control_halt.c"
#require "cmc_preservation_source.c"

PROOF static size_t _cmc_preservation_target_task_axioms_before =
    vector_size(get_all_axioms());

PROOF static term cm_target_task_app_arg_from_right(
    term application, size_t offset) {
  for (size_t i = 0; i < offset; ++i) {
    application = dest_comb(application).tm1;
  }
  return dest_comb(application).tm2;
}

PROOF static term cm_target_task_constructor_arg(
    term constructor, size_t arity, size_t index) {
  return cm_target_task_app_arg_from_right(
      constructor, arity - index - 1);
}

PROOF static thm cm_target_task_apply(
    thm result, const thm_list premises) {
  for (size_t i = 0; i < vector_size(premises); ++i) {
    result = match_mp_rule(result, premises[i]);
  }
  return result;
}

PROOF static void cm_target_task_accept(
    gnode branch, const thm_list rules, thm result) {
  result = conv_rule(rewrite_conv(rules), result);
  thm target_view = apply_conversion(
      rewrite_conv(rules), goal_ccl(branch->g));
  ACCEPT_TAC(branch, eq_mp_rule(sym_rule(target_view), result));
}

PROOF static thm cm_prove_target_task_step(void) {
  term source_task = `task:cm_task`;
  term annotation = `ann:cm_annotation`;
  term update =
      `cm_annotation_step ${source_task:cm_task} ${annotation:cm_annotation}`;
  term wf = `cm_wf_program (p:cm_program)`;
  term succeeds = `cm_task_succeeds ${source_task:cm_task}`;
  term static_valid = `cm_task_static_valid ${source_task:cm_task}`;
  term static_bases =
      `cm_task_static_bases (p:cm_program) ${source_task:cm_task}`;
  term runtime_ready =
      `cm_runtime_step_ready (p:cm_program) ${source_task:cm_task}
        ${annotation:cm_annotation}`;
  term runtime =
      `cm_task_runtime_invariant (p:cm_program) ${source_task:cm_task}
        ${annotation:cm_annotation}`;
  term typed =
      `cm_task_type_ready (p:cm_program) ${source_task:cm_task}
        ${annotation:cm_annotation}`;
  term fid_ready =
      `cm_task_fid_ready (p:cm_program) ${source_task:cm_task}`;
  term spill_consistent =
      `cm_annotation_spill_consistent ${annotation:cm_annotation}`;
  term generation =
      `cm_task_generation_safe (p:cm_program) ${source_task:cm_task}
        ${annotation:cm_annotation}`;
  term tagged = `cm_task_tagged_valid ${source_task:cm_task}`;
  term erases =
      `cm_annotation_erases ${source_task:cm_task}
        ${annotation:cm_annotation}`;
  term layout =
      `cm_task_layout (p:cm_program) ${source_task:cm_task}
        ${annotation:cm_annotation}`;
  term simulation =
      `cm_task_target_sim (p:cm_program) ${source_task:cm_task}
        (target:tvm_task) ${annotation:cm_annotation}`;
  term next_simulation =
      `cm_task_target_sim (p:cm_program)
        (cm_step ${source_task:cm_task})
        (tvm_iter (cm_update_steps ${update:cm_aupdate})
          (target:tvm_task))
        (cm_update_annotation ${update:cm_aupdate})`;
  term body = imp_chain(TERM_LIST(
      wf, succeeds, static_valid, static_bases, runtime_ready, runtime,
      typed, fid_ready, spill_consistent, generation, tagged, erases,
      layout, simulation), next_simulation);
  gnode root_node = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root_node);

  thm wf_fact = assume_rule(wf);
  thm succeeds_fact = assume_rule(succeeds);
  thm static_valid_fact = assume_rule(static_valid);
  thm static_bases_fact = assume_rule(static_bases);
  thm runtime_ready_fact = assume_rule(runtime_ready);
  thm runtime_fact = assume_rule(runtime);
  thm typed_fact = assume_rule(typed);
  thm fid_ready_fact = assume_rule(fid_ready);
  thm spill_fact = assume_rule(spill_consistent);
  thm generation_fact = assume_rule(generation);
  thm tagged_fact = assume_rule(tagged);
  thm erases_fact = assume_rule(erases);
  thm layout_fact = assume_rule(layout);
  thm simulation_fact = assume_rule(simulation);

  gnode_list task_cases = DISJ_CASES_TAC(introduced,
      ispec_rule(source_task, get_datatype_cases("cm_task")),
      "Htarget_task");
  for (size_t task_index = 0;
       task_index < vector_size(task_cases); ++task_index) {
    gnode branch = task_cases[task_index];
    while (is_exists(goal_lasmps(branch->g)[
        labeled_term_list_index(
          goal_lasmps(branch->g), "Htarget_task")].tm)) {
      branch = ASMP_EXISTS_TAC(branch, "Htarget_task", NULL);
    }
    thm task_shape = assume_rule(goal_lasmps(branch->g)[
        labeled_term_list_index(
          goal_lasmps(branch->g), "Htarget_task")].tm);
    term concrete_task = rhs_of(task_shape);

    if (task_index == 6) {
      thm_list done_rules = THM_LIST(
          task_shape, get_cm_step_def(), cm_annotation_step_def,
          cm_update_steps_def, cm_update_annotation_def,
          get_tvm_iter_def());
      thm result = conv_rule(
          reduce_rewrite_conv(done_rules), simulation_fact);
      thm target_view = apply_conversion(
          reduce_rewrite_conv(done_rules), goal_ccl(branch->g));
      ACCEPT_TAC(branch, eq_mp_rule(sym_rule(target_view), result));
      continue;
    }

    thm opened_runtime_ready = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          task_shape, cm_runtime_step_ready_def)),
        runtime_ready_fact);
    thm task_layout_ready = empty_theorem;
    thm fid_nonnegative = empty_theorem;
    if (task_index == 0) {
      task_layout_ready = conjunct2_rule(opened_runtime_ready);
    } else if (task_index == 1 || task_index == 2) {
      fid_nonnegative = conjunct1_rule(opened_runtime_ready);
      task_layout_ready = conjunct2_rule(opened_runtime_ready);
    } else if (task_index == 3) {
      fid_nonnegative = conjunct1_rule(conjunct2_rule(
          opened_runtime_ready));
      task_layout_ready = conjunct2_rule(conjunct2_rule(
          opened_runtime_ready));
    } else if (task_index == 4) {
      task_layout_ready = conjunct1_rule(opened_runtime_ready);
    } else {
      task_layout_ready = opened_runtime_ready;
    }
    thm opened_task_layout_ready = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          task_shape, cm_task_layout_ready_def)),
        task_layout_ready);
    thm program_equality = conjunct1_rule(opened_task_layout_ready);
    thm_list task_rules = THM_LIST(task_shape, program_equality);
    thm shaped_task_layout_ready = conv_rule(
        rewrite_conv(task_rules), task_layout_ready);

    thm shaped_runtime_ready = conv_rule(
        rewrite_conv(task_rules), runtime_ready_fact);
    thm shaped_runtime = conv_rule(
        rewrite_conv(task_rules), runtime_fact);
    thm shaped_type = conv_rule(
        rewrite_conv(task_rules), typed_fact);
    thm shaped_fid = conv_rule(
        rewrite_conv(task_rules), fid_ready_fact);
    thm shaped_generation = conv_rule(
        rewrite_conv(task_rules), generation_fact);
    thm shaped_tagged = conv_rule(
        rewrite_conv(task_rules), tagged_fact);
    thm shaped_erases = conv_rule(
        rewrite_conv(task_rules), erases_fact);
    thm shaped_layout = conv_rule(
        rewrite_conv(task_rules), layout_fact);
    thm shaped_simulation = conv_rule(
        rewrite_conv(task_rules), simulation_fact);

    if (task_index == 0) {
      thm result = cm_target_task_apply(
          get_cm_target_start_step(), THM_LIST(
            wf_fact, shaped_runtime_ready, shaped_simulation));
      cm_target_task_accept(branch, task_rules, result);
      continue;
    }

    if (task_index == 1) {
      thm result = cm_target_task_apply(
          get_cm_target_r_step(), THM_LIST(
            wf_fact,
            conv_rule(rewrite_conv(task_rules), static_valid_fact),
            conv_rule(rewrite_conv(task_rules), static_bases_fact),
            fid_nonnegative, shaped_task_layout_ready, shaped_runtime,
            shaped_generation, shaped_tagged, shaped_erases,
            shaped_layout, shaped_simulation));
      cm_target_task_accept(branch, task_rules, result);
      continue;
    }

    if (task_index == 2) {
      thm result = cm_target_task_apply(
          get_cm_target_l_step(), THM_LIST(
            wf_fact,
            conv_rule(rewrite_conv(task_rules), static_valid_fact),
            fid_nonnegative, shaped_task_layout_ready, shaped_runtime,
            shaped_layout, shaped_simulation));
      cm_target_task_accept(branch, task_rules, result);
      continue;
    }

    if (task_index == 3) {
      thm result = cm_target_task_apply(
          get_cm_target_s_step(), THM_LIST(
            shaped_runtime_ready, shaped_runtime,
            shaped_generation, shaped_simulation));
      cm_target_task_accept(branch, task_rules, result);
      continue;
    }

    if (task_index == 5) {
      term control = cm_target_task_constructor_arg(
          concrete_task, 5, 2);
      gnode_list exit_cases = BOOL_CASES_TAC(branch,
          `cm_control_kind ${control:cm_control} == 4i`,
          "Htarget_exit");
      thm exit_kind = assume_rule(
          `cm_control_kind ${control:cm_control} == 4i`);
      thm halted = cm_target_task_apply(
          get_cm_target_c_halt_step(), THM_LIST(
            wf_fact, shaped_runtime_ready, shaped_runtime,
            shaped_generation, shaped_layout,
            shaped_simulation, exit_kind));
      cm_target_task_accept(exit_cases[0], task_rules, halted);
      branch = exit_cases[1];
    }

    thm nonexit = empty_theorem;
    if (task_index == 5) {
      term control = cm_target_task_constructor_arg(
          concrete_task, 5, 2);
      nonexit = assume_rule(
          `~(cm_control_kind ${control:cm_control} == 4i)`);
    }

    gnode_list annotation_cases = DISJ_CASES_TAC(branch,
        ispec_rule(annotation, get_datatype_cases("cm_annotation")),
        task_index == 4 ? "Htarget_v_ann" : "Htarget_c_ann");
    gnode annotation_branch = annotation_cases[0];
    const char *annotation_label =
        task_index == 4 ? "Htarget_v_ann" : "Htarget_c_ann";
    while (is_exists(goal_lasmps(annotation_branch->g)[
        labeled_term_list_index(
          goal_lasmps(annotation_branch->g), annotation_label)].tm)) {
      annotation_branch = ASMP_EXISTS_TAC(
          annotation_branch, annotation_label, NULL);
    }
    thm annotation_shape = assume_rule(
        goal_lasmps(annotation_branch->g)[labeled_term_list_index(
          goal_lasmps(annotation_branch->g), annotation_label)].tm);
    term concrete_annotation = rhs_of(annotation_shape);
    term cursors = cm_target_task_constructor_arg(
        concrete_annotation, 8, 4);
    const char *cursors_label =
        task_index == 4 ? "Htarget_v_cursors" : "Htarget_c_cursors";
    gnode_list cursor_list_cases = DISJ_CASES_TAC(annotation_branch,
        ispec_rule(cursors, get_theorem_by_name("list_CASES")),
        cursors_label);

    {
      gnode nil_branch = cursor_list_cases[0];
      thm cursors_nil = assume_rule(
          goal_lasmps(nil_branch->g)[labeled_term_list_index(
            goal_lasmps(nil_branch->g), cursors_label)].tm);
      thm_list nil_rules = THM_LIST(
          task_shape, program_equality, annotation_shape, cursors_nil);
      if (task_index == 4) {
        thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
            task_shape, program_equality, annotation_shape, cursors_nil,
            get_cm_task_type_ready_def(), cm_ann_cursors_def,
            get_cm_cursor_head_value_type_ready_def())), typed_fact);
        CONTR_TAC(nil_branch, impossible);
      } else {
        thm nil_erases = conv_rule(reduce_rewrite_conv(THM_LIST(
            task_shape, program_equality, annotation_shape, cursors_nil,
            cm_annotation_erases_def, cm_ann_cursors_def,
            cm_cursor_frames_def)), erases_fact);
        thm frames_nil = sym_rule(nil_erases);
        term shaped_task = rhs_of(task_shape);
        thm not_done = eqt_elim_rule(apply_conversion(
            reduce_rewrite_conv(THM_LIST(
              get_cm_task_done_def())),
            mk_not(mk_comb(`cm_task_done`, shaped_task))));
        thm current_succeeds = conv_rule(
            rewrite_conv(THM_LIST(task_shape)), succeeds_fact);
        thm next_succeeds = match_mp_rule(match_mp_rule(
            cm_task_succeeds_step, not_done), current_succeeds);
        term control = cm_target_task_constructor_arg(
            concrete_task, 5, 2);
        gnode_list error_cases = BOOL_CASES_TAC(nil_branch,
            `cm_control_kind ${control:cm_control} == 5i`,
            "Htarget_nil_error");
        for (size_t i = 0; i < vector_size(error_cases); ++i) {
          thm error_kind = assume_rule(
              goal_lasmps(error_cases[i]->g)[labeled_term_list_index(
                goal_lasmps(error_cases[i]->g),
                "Htarget_nil_error")].tm);
          thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
              task_shape, program_equality, frames_nil, nonexit,
              error_kind, get_cm_step_def(), cm_done_succeeds,
              get_cm_success_control_def(), get_cm_control_kind_def())),
              next_succeeds);
          CONTR_TAC(error_cases[i], impossible);
        }
      }
      (void)nil_rules;
    }

    gnode cons_branch = ASMP_EXISTS_TAC(
        cursor_list_cases[1], cursors_label, NULL);
    cons_branch = ASMP_EXISTS_TAC(cons_branch, cursors_label, NULL);
    thm cursors_cons = assume_rule(
        goal_lasmps(cons_branch->g)[labeled_term_list_index(
          goal_lasmps(cons_branch->g), cursors_label)].tm);
    term cursor = cm_target_task_app_arg_from_right(
        rhs_of(cursors_cons), 1);
    const char *cursor_label =
        task_index == 4 ? "Htarget_v_cursor" : "Htarget_c_cursor";
    gnode_list cursor_cases = DISJ_CASES_TAC(cons_branch,
        ispec_rule(cursor, get_datatype_cases("cm_acursor")),
        cursor_label);
    gnode cursor_branch = cursor_cases[0];
    while (is_exists(goal_lasmps(cursor_branch->g)[
        labeled_term_list_index(
          goal_lasmps(cursor_branch->g), cursor_label)].tm)) {
      cursor_branch = ASMP_EXISTS_TAC(
          cursor_branch, cursor_label, NULL);
    }
    thm cursor_shape = assume_rule(
        goal_lasmps(cursor_branch->g)[labeled_term_list_index(
          goal_lasmps(cursor_branch->g), cursor_label)].tm);
    thm full_annotation_shape = conv_rule(rewrite_conv(THM_LIST(
        cursors_cons, cursor_shape)), annotation_shape);
    thm frames_equal = conv_rule(reduce_rewrite_conv(THM_LIST(
        task_shape, program_equality, full_annotation_shape,
        cm_annotation_erases_def, cm_ann_cursors_def,
        cm_cursor_frames_def, cm_cursor_phase_def)), erases_fact);
    thm_list full_rules = THM_LIST(
        task_shape, program_equality, full_annotation_shape,
        gsym_rule(frames_equal));

    if (task_index == 4) {
      thm result = cm_target_task_apply(
          get_cm_target_v_step(), THM_LIST(
            wf_fact,
            conv_rule(rewrite_conv(full_rules), runtime_ready_fact),
            conv_rule(rewrite_conv(full_rules), runtime_fact),
            conv_rule(rewrite_conv(full_rules), typed_fact),
            conv_rule(rewrite_conv(full_rules), fid_ready_fact),
            conv_rule(rewrite_conv(full_rules), spill_fact),
            conv_rule(rewrite_conv(full_rules), generation_fact),
            conv_rule(rewrite_conv(full_rules), tagged_fact),
            conv_rule(rewrite_conv(full_rules), layout_fact),
            conv_rule(rewrite_conv(full_rules), simulation_fact)));
      cm_target_task_accept(cursor_branch, full_rules, result);
    } else {
      term state = cm_target_task_constructor_arg(
          concrete_task, 5, 3);
      thm state_tagged = conv_rule(reduce_rewrite_conv(THM_LIST(
          task_shape, program_equality,
          cm_task_tagged_valid_def)), tagged_fact);
      thm result = cm_target_task_apply(
          get_cm_target_c_step(), THM_LIST(
            wf_fact,
            conv_rule(rewrite_conv(full_rules), runtime_ready_fact),
            conv_rule(rewrite_conv(full_rules), runtime_fact),
            conv_rule(rewrite_conv(full_rules), generation_fact),
            conv_rule(rewrite_conv(full_rules), typed_fact),
            state_tagged,
            conv_rule(rewrite_conv(full_rules), layout_fact),
            conv_rule(rewrite_conv(full_rules), simulation_fact)));
      cm_target_task_accept(cursor_branch, full_rules, result);
      (void)state;
    }
  }
  return gnode_prove(root_node);
}

PROOF thm cm_target_task_step = cm_prove_target_task_step();

PROOF thm get_cm_target_task_step(void) {
  return cm_target_task_step;
}

PROOF static int cmc_preservation_target_task_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_task_axioms_before,
      "cmc_preservation_target_task introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_target_task_step)) == 0,
      "total target task theorem has hypotheses");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_task_checks =
    cmc_preservation_target_task_final_checks();
