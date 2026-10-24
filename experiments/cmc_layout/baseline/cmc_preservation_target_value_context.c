#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "userlib/proof_patterns.h"
#include "cmc_preservation_target_value_context.h"
#include "cmc_preservation_generation.h"
#include "cmc_preservation_tagged_task.h"
#include "cmc_preservation_invariant.h"

#require "userlib/proof_patterns.c"
#require "cmc_preservation_target_access.c"
#require "cmc_preservation_fid.c"
#require "cmc_preservation_type_source_v_support.c"
#require "cmc_preservation_spill_semantic.c"
#require "cmc_preservation_invariant_transition.c"
#require "cmc_preservation_generation.c"
#require "cmc_preservation_tagged_task.c"
#require "cmc_preservation_invariant.c"

PROOF static size_t _cmc_preservation_target_value_context_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_target_v_context_consequence(
    const thm premise, const term conclusion) {
  return mp_rule(taut_rule(mk_imp(concl(premise), conclusion)), premise);
}

PROOF static thm cm_prove_target_v_context(void) {
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
  term runtime_stack =
      `cm_runtime_stack (p:cm_program)
        (cm_state_regions (st:cm_src_state)) (fid:int)
        (cm_state_fp st) (cm_state_regions st)
        ${cursors:(cm_acursor)list} (spills:(cm_spill)list)
        (saved:(cm_spill_frame)list) (calls:(cm_call_sim_frame)list)`;
  term conclusion = list_mk_conj(TERM_LIST(
      `cm_typed_program (p:cm_program)`,
      `cm_phase_is_halt ${phase:cm_aphase} ||
       (0i <= (fid:int) &&
        fid < ilength (cm_program_functions (p:cm_program)))`,
      `cm_v_temp_ready ${ann:cm_annotation} ${phase:cm_aphase}`,
      `cm_v_phase_ready (p:cm_program) (incoming:cm_value)
        (st:cm_src_state) ${ann:cm_annotation} ${phase:cm_aphase}`,
      `cm_v_spill_ready (p:cm_program) (fid:int)
        ${ann:cm_annotation} ${phase:cm_aphase}`,
      `cm_v_source_ready (p:cm_program) (fid:int)
        (st:cm_src_state) ${phase:cm_aphase}`,
      `cm_phase_static_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase}`,
      `cm_phase_parent_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase} (rest:(cm_acursor)list)`,
      `cm_phase_result_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase} (rest:(cm_acursor)list)`,
      `cm_cursors_type_ready (p:cm_program)
        (cm_phase_next_fid (fid:int) ${phase:cm_aphase})
        (rest:(cm_acursor)list)`,
      `cm_phase_value_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase} (incoming:cm_value)`,
      `cm_phase_spill_consistent (temp:int) (owner:int)
        ${phase:cm_aphase} (spills:(cm_spill)list)`,
      `cm_regions_before (cm_state_regions (st:cm_src_state))
        (cm_state_nextgen st)`,
      runtime_stack,
      `cm_runtime_memory_layout (p:cm_program) (st:cm_src_state)
        (calls:(cm_call_sim_frame)list)
        (CMSpillFrame (fid:int) (cm_state_fp st)
          (spills:(cm_spill)list) ::
         (saved:(cm_spill_frame)list))`,
      `cm_state_generation_below (p:cm_program) (fid:int)
        (st:cm_src_state)`,
      `cm_annotation_generation_below ${task:cm_task}
        ${ann:cm_annotation}`,
      `cm_tagged_span_valid (st:cm_src_state)`));
  term body = imp_chain(TERM_LIST(
      `cm_wf_program (p:cm_program)`,
      `cm_runtime_step_ready (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`,
      `cm_task_runtime_invariant (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`,
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`,
      `cm_task_fid_ready (p:cm_program) ${task:cm_task}`,
      `cm_annotation_spill_consistent ${ann:cm_annotation}`,
      `cm_task_generation_safe (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`,
      `cm_task_tagged_valid ${task:cm_task}`), conclusion);
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);

  thm wf_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_wf_program_def(), get_cm_codegen_admissible_def())),
      assume_rule(`cm_wf_program (p:cm_program)`));
  thm typed = cm_target_v_context_consequence(wf_open,
      `cm_typed_program (p:cm_program)`);

  thm ready_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_runtime_step_ready_def, cm_task_layout_ready_def,
      cm_v_layout_ready_def, cm_ann_cursors_def,
      cm_cursor_phase_def, get_theorem_by_name("HD"),
      get_theorem_by_name("NOT_CONS_NIL"))),
      assume_rule(
        `cm_runtime_step_ready (p:cm_program) ${task:cm_task}
          ${ann:cm_annotation}`));
  thm temp_ready = cm_target_v_context_consequence(ready_open,
      `cm_v_temp_ready ${ann:cm_annotation} ${phase:cm_aphase}`);
  thm phase_ready = cm_target_v_context_consequence(ready_open,
      `cm_v_phase_ready (p:cm_program) (incoming:cm_value)
        (st:cm_src_state) ${ann:cm_annotation} ${phase:cm_aphase}`);
  thm spill_ready = cm_target_v_context_consequence(ready_open,
      `cm_v_spill_ready (p:cm_program) (fid:int)
        ${ann:cm_annotation} ${phase:cm_aphase}`);
  thm source_ready = cm_target_v_context_consequence(ready_open,
      `cm_v_source_ready (p:cm_program) (fid:int)
        (st:cm_src_state) ${phase:cm_aphase}`);

  thm fid_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_fid_ready_def, cm_frames_fid_ready_def)), assume_rule(
        `cm_task_fid_ready (p:cm_program) ${task:cm_task}`));
  thm phase_fid = match_mp_rule(
      specl_rule(TERM_LIST(phase, `fid:int`, `p:cm_program`),
        cm_phase_frame_fid_ready), conjunct1_rule(fid_open));

  thm components = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `p:cm_program`, `fid:int`, `incoming:cm_value`,
      `st:cm_src_state`, frames, phase, `pc:int`, `temp:int`,
      `breakpc:int`, `continuepc:int`, `owner:int`, `saved_break:int`,
      `saved_continue:int`, `rest:(cm_acursor)list`,
      `spills:(cm_spill)list`, `saved:(cm_spill_frame)list`,
      `calls:(cm_call_sim_frame)list`), cm_v_cursor_type_components),
      assume_rule(
        `cm_task_type_ready (p:cm_program) ${task:cm_task}
          ${ann:cm_annotation}`));
  thm static_type = conjunct1_rule(conjunct2_rule(components));
  thm parent_type = conjunct1_rule(conjunct2_rule(conjunct2_rule(components)));
  thm result_type = conjunct1_rule(conjunct2_rule(conjunct2_rule(
      conjunct2_rule(components))));
  thm cursors_type = conjunct1_rule(conjunct2_rule(conjunct2_rule(
      conjunct2_rule(conjunct2_rule(components)))));
  thm value_type = conjunct2_rule(conjunct2_rule(conjunct2_rule(
      conjunct2_rule(conjunct2_rule(components)))));

  thm spill_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_annotation_spill_consistent_def,
      cm_cursors_spill_consistent_def,
      cm_ann_temp_def, cm_ann_cursors_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_cursor_temp_def, cm_cursor_phase_def)),
      assume_rule(`cm_annotation_spill_consistent ${ann:cm_annotation}`));
  thm phase_spill = conjunct1_rule(spill_open);

  thm runtime_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_runtime_invariant_def, cm_ann_cursors_def,
      cm_ann_spills_def, cm_ann_saved_def, cm_ann_calls_def)),
      assume_rule(
        `cm_task_runtime_invariant (p:cm_program) ${task:cm_task}
          ${ann:cm_annotation}`));
  thm regions_before = conjunct1_rule(runtime_open);
  thm stack = conjunct2_rule(runtime_open);
  thm memory_layout = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `fid:int`, cursors,
      `spills:(cm_spill)list`, `saved:(cm_spill_frame)list`,
      `calls:(cm_call_sim_frame)list`), cm_runtime_stack_memory_layout),
      stack);

  thm generation_open = conv_rule(rewrite_conv(THM_LIST(
      cm_task_generation_safe_def)), assume_rule(
        `cm_task_generation_safe (p:cm_program) ${task:cm_task}
          ${ann:cm_annotation}`));
  thm task_generation = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_generation_below_def)), conjunct1_rule(generation_open));
  thm state_generation = conjunct1_rule(task_generation);
  thm annotation_generation = conjunct2_rule(generation_open);
  thm tagged = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_tagged_valid_def)), assume_rule(
        `cm_task_tagged_valid ${task:cm_task}`));

  ACCEPT_TAC(leaf, list_conj_rule(THM_LIST(
      typed, phase_fid, temp_ready, phase_ready, spill_ready,
      source_ready, static_type, parent_type, result_type, cursors_type,
      value_type, phase_spill, regions_before, stack, memory_layout,
      state_generation, annotation_generation, tagged)));
  return gnode_prove(root);
}
PROOF thm cm_target_v_context = cm_prove_target_v_context();

PROOF thm get_cm_target_v_context(void) {
  return cm_target_v_context;
}

PROOF static int cmc_preservation_target_value_context_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_value_context_axioms_before,
      "cmc_preservation_target_value_context introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_target_v_context)) == 0,
      "target value context theorem has hypotheses");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_value_context_checks =
    cmc_preservation_target_value_context_final_checks();
