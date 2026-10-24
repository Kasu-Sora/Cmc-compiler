#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "userlib/proof_patterns.h"
#include "cmc_preservation_total.h"
#include "cmc_preservation_runtime_ready.h"
#include "cmc_preservation_target_task.h"
#include "cmc_preservation_ready_semantic.h"
#include "cmc_preservation_invariant_task.h"
#include "cmc_preservation_type_step.h"
#include "cmc_preservation_fid_step.h"
#include "cmc_preservation_spill_update.h"
#include "cmc_preservation_generation_annotation_transition.h"
#include "cmc_preservation_generation_static_task.h"
#include "cmc_preservation_static_bases_step.h"
#include "cmc_preservation_tagged_step.h"
#include "cmc_preservation_budget_step.h"
#include "cmc_preservation_short_step.h"
#include "cmc_preservation_code_task.h"
#include "cmc_preservation_type_ready.h"
#include "cmc_preservation_generation.h"
#include "cmc_annotate_preservation.h"

#require "cmc_preservation_total.c"
#require "cmc_preservation_runtime_ready.c"
#require "cmc_preservation_target_task.c"
#require "cmc_preservation_ready_semantic.c"
#require "cmc_preservation_invariant_task.c"
#require "cmc_preservation_type_step.c"
#require "cmc_preservation_fid_step.c"
#require "cmc_preservation_spill_update.c"
#require "cmc_preservation_generation_annotation_transition.c"
#require "cmc_preservation_generation_static_task.c"
#require "cmc_preservation_static_bases_step.c"
#require "cmc_preservation_tagged_step.c"
#require "cmc_preservation_budget_step.c"
#require "cmc_preservation_short_step.c"
#require "cmc_preservation_code_task.c"

PROOF static size_t _cmc_preservation_total_step_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_pts_pick(thm source, term wanted) {
  if (alpha_compare(concl(source), wanted) == 0) return source;
  if (!is_conj(concl(source))) return empty_theorem;
  thm left = cm_pts_pick(conjunct1_rule(source), wanted);
  if (!IS_NULL(left)) return left;
  return cm_pts_pick(conjunct2_rule(source), wanted);
}

PROOF static thm cm_pts_apply(thm result, thm_list premises) {
  for (size_t i = 0; i < vector_size(premises); ++i) {
    result = match_mp_rule(result, premises[i]);
  }
  return result;
}

PROOF static thm cm_prove_preservation_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (ast:cm_astate).
         cm_wf_program p ==>
         cm_preservation_invariant p ast ==>
         cm_preservation_invariant p (cm_annotated_step ast)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  term task = `cm_astate_task (ast:cm_astate)`;
  term ann = `cm_astate_annotation (ast:cm_astate)`;
  term target = `cm_astate_target (ast:cm_astate)`;
  thm wf = assume_rule(`cm_wf_program (p:cm_program)`);
  thm typed = cm_pts_pick(conv_rule(rewrite_conv(THM_LIST(
      get_cm_wf_program_def(), get_cm_codegen_admissible_def())), wf),
      `cm_typed_program (p:cm_program)`);
  thm invariant = conv_rule(rewrite_conv(THM_LIST(
      get_cm_preservation_invariant_def())), assume_rule(
        `cm_preservation_invariant (p:cm_program) (ast:cm_astate)`));
  thm succeeds = cm_pts_pick(invariant,
      `cm_task_succeeds ${task:cm_task}`);
  thm erases = cm_pts_pick(invariant,
      `cm_annotation_erases ${task:cm_task} ${ann:cm_annotation}`);
  thm rooted = cm_pts_pick(invariant,
      `cm_annotation_rooted ${ann:cm_annotation}`);
  thm coordinate = cm_pts_pick(invariant,
      `cm_task_coordinate_ready (p:cm_program)
        ${task:cm_task} ${ann:cm_annotation}`);
  thm ready = cm_pts_pick(invariant,
      `cm_task_layout_ready (p:cm_program)
        ${task:cm_task} ${ann:cm_annotation}`);
  thm context = cm_pts_pick(invariant,
      `cm_task_context_ready ${task:cm_task} ${ann:cm_annotation}`);
  thm runtime = cm_pts_pick(invariant,
      `cm_task_runtime_invariant (p:cm_program)
        ${task:cm_task} ${ann:cm_annotation}`);
  thm type_ready = cm_pts_pick(invariant,
      `cm_task_type_ready (p:cm_program)
        ${task:cm_task} ${ann:cm_annotation}`);
  thm fid_ready = cm_pts_pick(invariant,
      `cm_task_fid_ready (p:cm_program) ${task:cm_task}`);
  thm spill = cm_pts_pick(invariant,
      `cm_annotation_spill_consistent ${ann:cm_annotation}`);
  thm generation = cm_pts_pick(invariant,
      `cm_task_generation_safe (p:cm_program)
        ${task:cm_task} ${ann:cm_annotation}`);
  thm static_valid = cm_pts_pick(invariant,
      `cm_task_static_valid ${task:cm_task}`);
  thm static_bases = cm_pts_pick(invariant,
      `cm_task_static_bases (p:cm_program) ${task:cm_task}`);
  thm tagged = cm_pts_pick(invariant,
      `cm_task_tagged_valid ${task:cm_task}`);
  thm budget = cm_pts_pick(invariant,
      `cm_task_budget (p:cm_program)
        ${task:cm_task} ${ann:cm_annotation}`);
  thm short_ready = cm_pts_pick(invariant,
      `cm_task_short_ready ${task:cm_task}`);
  thm layout = cm_pts_pick(invariant,
      `cm_task_layout (p:cm_program)
        ${task:cm_task} ${ann:cm_annotation}`);
  thm simulation = cm_pts_pick(invariant,
      `cm_task_target_sim (p:cm_program) ${task:cm_task}
        ${target:tvm_task} ${ann:cm_annotation}`);

  thm runtime_ready = cm_pts_apply(cm_invariants_runtime_step_ready,
      THM_LIST(typed, type_ready, coordinate, ready, budget, fid_ready,
        succeeds, erases, short_ready));
  thm next_succeeds = match_mp_rule(
      get_cm_succeeds_step_total(), succeeds);
  thm annotation_sound = match_mp_rule(
      cm_annotation_step_sound, conj_rule(rooted, erases));
  thm next_erases = conjunct1_rule(annotation_sound);
  thm next_rooted = conjunct2_rule(annotation_sound);
  thm next_coordinate = cm_pts_apply(cm_task_coordinate_step,
      THM_LIST(erases, coordinate));
  thm next_ready = cm_pts_apply(cm_task_ready_step,
      THM_LIST(typed, erases, rooted, coordinate, runtime,
        ready, context, succeeds));
  thm next_context = cm_pts_apply(cm_task_context_step,
      THM_LIST(typed, erases, rooted, coordinate, runtime,
        ready, context, succeeds));
  thm next_runtime = cm_pts_apply(cm_task_runtime_step,
      THM_LIST(typed, erases, runtime_ready, runtime));
  thm next_type = cm_pts_apply(cm_task_type_ready_step,
      THM_LIST(typed, erases, ready, type_ready, fid_ready, succeeds));
  thm next_fid = cm_pts_apply(cm_task_fid_ready_step,
      THM_LIST(typed, static_valid, ready, type_ready, fid_ready, succeeds));
  thm next_spill = cm_pts_apply(cm_annotation_step_spill_consistent,
      THM_LIST(spill, ready));
  thm next_generation = cm_pts_apply(cm_task_generation_safe_step,
      THM_LIST(static_valid, generation, spill, succeeds));
  thm next_static = cm_pts_apply(cm_task_static_valid_step,
      THM_LIST(typed, ready, static_valid, succeeds));
  thm next_bases = cm_pts_apply(cm_task_static_bases_step,
      THM_LIST(erases, generation, runtime, succeeds, static_bases));
  thm generation_below = conjunct1_rule(conv_rule(rewrite_conv(
      THM_LIST(cm_task_generation_safe_def)), generation));
  thm next_tagged = cm_pts_apply(cm_task_tagged_step,
      THM_LIST(typed, erases, runtime, generation_below, tagged));
  thm next_budget = cm_pts_apply(cm_task_budget_step,
      THM_LIST(erases, type_ready, coordinate, budget));
  thm next_short = cm_pts_apply(cm_task_short_step,
      THM_LIST(generation, erases, runtime, short_ready));
  thm next_layout = cm_pts_apply(cm_task_layout_step,
      THM_LIST(erases, ready, layout));
  thm next_simulation = cm_pts_apply(get_cm_target_task_step(),
      THM_LIST(wf, succeeds, static_valid, static_bases, runtime_ready,
        runtime, type_ready, fid_ready, spill, generation, tagged,
        erases, layout, simulation));
  thm packed = list_conj_rule(THM_LIST(next_succeeds, next_erases,
      next_rooted, next_coordinate, next_ready, next_context,
      next_runtime, next_type, next_fid, next_spill, next_generation,
      next_static, next_bases, next_tagged, next_budget, next_short,
      next_layout, next_simulation));
  gnode unfolded = CONV_TAC(introduced,
      rewrite_conv(THM_LIST(get_cm_preservation_invariant_def())));
  gnode normalized = CONV_TAC(unfolded,
      reduce_rewrite_conv(THM_LIST(
        cm_astate_task_def, cm_astate_target_def,
        cm_astate_annotation_def, cm_annotated_step_def)));
  ACCEPT_TAC(normalized, packed);
  return gnode_prove(root);
}

PROOF thm cm_preservation_step = cm_prove_preservation_step();

PROOF thm get_cm_preservation_step(void) {
  return cm_preservation_step;
}

PROOF static int cmc_preservation_total_step_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_total_step_axioms_before,
      "preservation transition introduced an axiom");
  ENSURE_COND(!IS_NULL(get_cm_preservation_step()) &&
      vector_size(hyp(get_cm_preservation_step())) == 0 &&
      vector_size(free_vars(concl(get_cm_preservation_step()))) == 0 &&
      alpha_compare(concl(get_cm_preservation_step()),
        `!(p:cm_program) (ast:cm_astate).
           cm_wf_program p ==>
           cm_preservation_invariant p ast ==>
           cm_preservation_invariant p (cm_annotated_step ast)`) == 0,
      "preservation transition theorem has the wrong contract");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_total_step_checks =
    cmc_preservation_total_step_final_checks();
