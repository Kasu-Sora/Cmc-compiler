#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_tagged_step.h"
#include "cmc_preservation_generation_state.h"

#require "cmc_preservation_tagged_apply.c"

PROOF static size_t _cmc_preservation_tagged_step_axioms_before =
    vector_size(get_all_axioms());

PROOF static term cm_tgs_app_arg_from_right(
    term application, size_t offset) {
  for (size_t i = 0; i < offset; ++i) {
    application = dest_comb(application).tm1;
  }
  return dest_comb(application).tm2;
}

PROOF static term cm_tgs_constructor_arg(
    term constructor, size_t arity, size_t index) {
  return cm_tgs_app_arg_from_right(
      constructor, arity - index - 1);
}

PROOF static thm cm_tgs_runtime_core(const thm opened_invariant) {
  return conv_rule(rewrite_conv(THM_LIST(
      gsym_rule(cm_runtime_core_def))),
      conjunct2_rule(opened_invariant));
}

PROOF static thm cm_prove_initial_halt_runtime_core(void) {
  gnode root_node = gnode_new_with_ccl(
      `!(p:cm_program) (input:(int)list).
         cm_typed_program p ==>
         cm_runtime_core p (--1i) (cm_initial_state p input)
           (CMAnnotation 0i 0i 0i 0i
             [CMACursor CAHaltP 0i 0i 0i] [] [] [])`);
  gnode leaf = AUTO_INTROS_TAC(root_node);
  term initial =
      `cm_initial_state (p:cm_program) (input:(int)list)`;
  conv initial_reduction = then_conv(
      rewrite_conv(THM_LIST(get_cm_initial_state_def())),
      reduce_rewrite_conv(get_cm_state_core_defs()));
  thm initial_fp = apply_conversion(initial_reduction,
      `cm_state_fp ${initial:cm_src_state}`);
  thm initial_nextgen = apply_conversion(initial_reduction,
      `cm_state_nextgen ${initial:cm_src_state}`);
  thm initial_regions_raw = apply_conversion(initial_reduction,
      `cm_state_regions ${initial:cm_src_state}`);
  thm initial_regions = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(cm_static_regions_def))), initial_regions_raw);
  thm before = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(initial_regions), sym_rule(initial_nextgen))),
      spec_rule(`p:cm_program`, cm_static_regions_before_dynamic));
  thm stack = match_mp_rule(
      spec_rule(`p:cm_program`, cm_runtime_stack_halt_initial),
      assume_rule(`cm_typed_program (p:cm_program)`));
  stack = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(initial_regions), sym_rule(initial_fp))), stack);
  thm result = conj_rule(before, stack);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      cm_runtime_core_def, cm_ann_cursors_def,
      cm_ann_spills_def, cm_ann_saved_def, cm_ann_calls_def)),
      goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), result));
  return gnode_prove(root_node);
}
PROOF static thm cm_initial_halt_runtime_core =
    cm_prove_initial_halt_runtime_core();

PROOF static thm cm_prove_task_tagged_step(void) {
  term typed = `cm_typed_program (root:cm_program)`;
  term erases =
      `cm_annotation_erases (task:cm_task) (ann:cm_annotation)`;
  term runtime =
      `cm_task_runtime_invariant (root:cm_program)
        (task:cm_task) (ann:cm_annotation)`;
  term generation =
      `cm_task_generation_below (root:cm_program) (task:cm_task)`;
  term tagged = `cm_task_tagged_valid (task:cm_task)`;
  term target =
      `cm_task_tagged_valid (cm_step (task:cm_task))`;
  term body = imp_chain(
      TERM_LIST(typed, erases, runtime, generation, tagged), target);
  gnode root_node = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root_node);
  gnode_list cases = DISJ_CASES_TAC(
      introduced,
      ispec_rule(`task:cm_task`, get_datatype_cases("cm_task")),
      "Htask");

  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(branch->g);
      int index = labeled_term_list_index(assumptions, "Htask");
      if (!is_exists(assumptions[index].tm)) break;
      branch = ASMP_EXISTS_TAC(branch, "Htask", NULL);
    }
    thm task_shape = assume_rule(
        goal_lasmps(branch->g)[labeled_term_list_index(
          goal_lasmps(branch->g), "Htask")].tm);
    term concrete = rhs_of(task_shape);
    thm runtime_open = conv_rule(reduce_rewrite_conv(THM_LIST(
        task_shape, cm_task_runtime_invariant_def)),
        assume_rule(runtime));
    thm generation_open = conv_rule(reduce_rewrite_conv(THM_LIST(
        task_shape, cm_task_generation_below_def)),
        assume_rule(generation));
    thm tagged_open = conv_rule(reduce_rewrite_conv(THM_LIST(
        task_shape, cm_task_tagged_valid_def)),
        assume_rule(tagged));
    thm shaped_erases = conv_rule(rewrite_conv(THM_LIST(
        task_shape)), assume_rule(erases));
    thm result = empty_theorem;

    if (i == 0) {
      term input = cm_tgs_constructor_arg(concrete, 2, 1);
      thm program_eq = conjunct1_rule(runtime_open);
      thm core = match_mp_rule(specl_rule(TERM_LIST(
          `root:cm_program`, input), cm_initial_halt_runtime_core),
          assume_rule(typed));
      result = specl_rule(TERM_LIST(
          `root:cm_program`, `--1i`,
          `cm_program_main (root:cm_program)`,
          `[]:(cm_value)list`,
          `cm_initial_state (root:cm_program) ${input:(int)list}`,
          `CMIntTy`, `[CMHaltK]:(cm_frame)list`,
          `CMAnnotation 0i 0i 0i 0i
            [CMACursor CAHaltP 0i 0i 0i] [] [] []`),
          cm_tagged_span_begin_call_runtime);
      result = match_mp_rule(result, assume_rule(typed));
      result = match_mp_rule(result, specl_rule(TERM_LIST(
          `root:cm_program`, input), cm_state_generation_initial));
      result = match_mp_rule(result, core);
      result = match_mp_rule(result, spec_rule(input,
          spec_rule(`root:cm_program`, cm_tagged_span_initial)));
      thm_list rules = THM_LIST(
          task_shape, program_eq, get_cm_step_def());
      result = conv_rule(rewrite_conv(rules), result);
      gnode reduced = CONV_TAC(branch, rewrite_conv(rules));
      ACCEPT_TAC(reduced, result);
      continue;
    }

    if (i == 6) {
      thm_list rules = THM_LIST(
          task_shape, get_cm_step_def(), cm_task_tagged_valid_def);
      result = conv_rule(reduce_rewrite_conv(rules), tagged_open);
      gnode reduced = CONV_TAC(branch, reduce_rewrite_conv(rules));
      ACCEPT_TAC(reduced, result);
      continue;
    }

    term program = cm_tgs_constructor_arg(concrete, 5, 0);
    term fid = cm_tgs_constructor_arg(concrete, 5, 1);
    term payload = cm_tgs_constructor_arg(concrete, 5, 2);
    term state = cm_tgs_constructor_arg(concrete, 5, 3);
    term frames = cm_tgs_constructor_arg(concrete, 5, 4);
    thm program_eq = conjunct1_rule(runtime_open);
    thm core = cm_tgs_runtime_core(runtime_open);
    thm state_below = conjunct1_rule(conjunct2_rule(generation_open));
    thm rooted_erases = conv_rule(rewrite_conv(THM_LIST(
        program_eq)), shaped_erases);
    thm rooted_tagged = conv_rule(rewrite_conv(THM_LIST(
        task_shape, program_eq)), assume_rule(tagged));

    if (i == 1) {
      result = specl_rule(TERM_LIST(
          `root:cm_program`, fid, payload, state, frames,
          `ann:cm_annotation`), cm_tagged_span_rstart);
      result = match_mp_rule(result, assume_rule(typed));
      result = match_mp_rule(result, state_below);
      result = match_mp_rule(result, core);
      result = match_mp_rule(result, tagged_open);
    } else if (i == 2) {
      result = specl_rule(TERM_LIST(
          `root:cm_program`, fid, payload, state, frames),
          cm_tagged_span_lstart);
      result = match_mp_rule(result, tagged_open);
    } else if (i == 3) {
      result = specl_rule(TERM_LIST(
          `root:cm_program`, fid, payload, state, frames),
          cm_tagged_span_sstart);
      result = match_mp_rule(result,
          conjunct1_rule(conjunct2_rule(runtime_open)));
      result = match_mp_rule(result, tagged_open);
    } else if (i == 4) {
      result = specl_rule(TERM_LIST(
          `root:cm_program`, fid, payload, state, frames,
          `ann:cm_annotation`), cm_tagged_span_vstep);
      result = match_mp_rule(result, assume_rule(typed));
      result = match_mp_rule(result, state_below);
      result = match_mp_rule(result, rooted_erases);
      result = match_mp_rule(result, core);
      result = match_mp_rule(result, rooted_tagged);
    } else {
      result = specl_rule(TERM_LIST(
          `root:cm_program`, fid, payload, state, frames,
          `ann:cm_annotation`), cm_tagged_span_cstep);
      result = match_mp_rule(result, rooted_erases);
      result = match_mp_rule(result, core);
      result = match_mp_rule(result, rooted_tagged);
    }

    thm_list rules = THM_LIST(task_shape, program_eq, get_cm_step_def());
    result = conv_rule(rewrite_conv(rules), result);
    gnode reduced = CONV_TAC(branch, rewrite_conv(rules));
    ACCEPT_TAC(reduced, result);
  }
  return gnode_prove(root_node);
}
PROOF thm cm_task_tagged_step = cm_prove_task_tagged_step();

PROOF static int cmc_preservation_tagged_step_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_tagged_step_axioms_before,
      "cmc_preservation_tagged_step introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_initial_halt_runtime_core)) == 0,
      "initial halt runtime-core theorem is not closed");
  ENSURE_COND(vector_size(hyp(cm_task_tagged_step)) == 0,
      "task tagged-step theorem is not closed");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_tagged_step_checks =
    cmc_preservation_tagged_step_final_checks();
