#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_short_control.h"
#include "cmc_preservation_short_defs.h"
#include "cmc_preservation_short_bases.h"
#include "cmc_preservation_generation.h"
#include "cmc_preservation_invariant_transition.h"

#require "cmc_preservation_short_value.c"

PROOF static size_t _cmc_preservation_short_control_axioms_before =
    vector_size(get_all_axioms());

PROOF static term cm_sc_app_arg_from_right(
    term application, size_t offset) {
  for (size_t i = 0; i < offset; ++i) {
    application = dest_comb(application).tm1;
  }
  return dest_comb(application).tm2;
}

PROOF static term cm_sc_constructor_arg(
    term constructor, size_t arity, size_t index) {
  return cm_sc_app_arg_from_right(
      constructor, arity - index - 1);
}

PROOF static thm cm_sc_named_shape(
    gnode *node, const char *label) {
  while (true) {
    labeled_term_list assumptions = goal_lasmps((*node)->g);
    int index = labeled_term_list_index(assumptions, label);
    if (!is_exists(assumptions[index].tm)) {
      return assume_rule(assumptions[index].tm);
    }
    *node = ASMP_EXISTS_TAC(*node, label, NULL);
  }
}

PROOF static term cm_sc_runtime_annotation(term phase) {
  return `CMAnnotation (pc:int) (temp:int) (breakpc:int)
    (continuepc:int)
    (CMACursor ${phase:cm_aphase} (owner:int)
       (saved_break:int) (saved_continue:int) ::
     (rest:(cm_acursor)list))
    (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
    (calls:(cm_call_sim_frame)list)`;
}

PROOF static thm cm_sc_cursor_eq(term ann, term phase) {
  return eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_ann_cursors_def, cm_cursor_phase_def,
        cm_cursor_temp_def, cm_cursor_break_def,
        cm_cursor_continue_def)),
      `cm_ann_cursors ${ann:cm_annotation} ==
       CMACursor ${phase:cm_aphase} (owner:int)
         (saved_break:int) (saved_continue:int) ::
       (rest:(cm_acursor)list)`));
}

PROOF static thm cm_sc_consequence(thm given, term wanted) {
  return mp_rule(taut_rule(mk_imp(concl(given), wanted)), given);
}

PROOF static thm cm_sc_transport_frames(
    term p, term fid, term old_state, term new_state,
    term frames, thm bases, thm generation, thm ready) {
  return match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        frames, p, fid, old_state, new_state,
        mk_comb(`cm_state_nextgen`, old_state)),
        cm_frames_short_ready_bases), bases), generation), ready);
}

PROOF static thm cm_prove_sc_task_cond(void) {
  gnode root = gnode_new_with_ccl(
      `!(condition:bool) (yes:cm_task) (no:cm_task).
         cm_task_short_ready (if condition then yes else no) <=>
         (if condition
          then cm_task_short_ready yes
          else cm_task_short_ready no)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      introduced, `condition:bool`, "Hsc_condition");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_WITH_ASMP_TAC(cases[i], reduce_rewrite_conv, THM_LIST());
  }
  return gnode_prove(root);
}
PROOF static thm cm_sc_task_cond = cm_prove_sc_task_cond();

PROOF static thm cm_sc_scope_bases(
    term phase, term ann, term oldenv, term oldregions,
    thm core) {
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`, ann,
      phase, oldenv, oldregions, `owner:int`,
      `saved_break:int`, `saved_continue:int`,
      `rest:(cm_acursor)list`),
      cm_runtime_scope_restore_region_bases);
  result = match_mp_rule(result, cm_sc_cursor_eq(ann, phase));
  thm_list phase_rules = THM_LIST(
      cm_phase_is_scope_def, cm_phase_is_call_def,
      cm_phase_oldregions_def);
  for (size_t i = 0; i < 3; ++i) {
    result = match_mp_rule(result, eqt_elim_rule(
        apply_conversion(reduce_rewrite_conv(phase_rules),
          dest_imp(concl(result)).tm1)));
  }
  return match_mp_rule(result, core);
}

PROOF static thm cm_prove_sc_spill_frame_reconstruct(void) {
  gnode root = gnode_new_with_ccl(
      `!(frame:cm_spill_frame).
         CMSpillFrame (cm_spill_frame_fid frame)
           (cm_spill_frame_fp frame)
           (cm_spill_frame_spills frame) == frame`);
  gnode_list cases = INDUCT_TAC(root, `frame:cm_spill_frame`);
  CONV_TAC(cases[0], reduce_rewrite_conv(THM_LIST(
      cm_spill_frame_fid_def, cm_spill_frame_fp_def,
      cm_spill_frame_spills_def)));
  return gnode_prove(root);
}
PROOF static thm cm_sc_spill_frame_reconstruct =
    cm_prove_sc_spill_frame_reconstruct();

PROOF static thm cm_prove_sc_call_frame_reconstruct(void) {
  gnode root = gnode_new_with_ccl(
      `!(frame:cm_call_sim_frame).
         CMCallSimFrame (cm_call_sim_base frame)
           (cm_call_sim_saved frame)
           (cm_call_sim_return frame) == frame`);
  gnode_list cases = INDUCT_TAC(root, `frame:cm_call_sim_frame`);
  CONV_TAC(cases[0], reduce_rewrite_conv(THM_LIST(
      cm_call_sim_base_def, cm_call_sim_saved_def,
      cm_call_sim_return_def)));
  return gnode_prove(root);
}
PROOF static thm cm_sc_call_frame_reconstruct =
    cm_prove_sc_call_frame_reconstruct();

PROOF static thm cm_sc_cons_reconstruct(
    term list_term, term cons_constant, term tail_term,
    thm head_reconstruct, thm nonempty) {
  thm list_shape = mp_rule(
      ispec_rule(list_term, get_theorem_by_name("CONS_HD_TL")),
      nonempty);
  thm rebuilt = mk_comb_rule(mk_comb_rule(
      refl_rule(cons_constant), head_reconstruct),
      refl_rule(tail_term));
  return sym_rule(trans_rule(rebuilt, sym_rule(list_shape)));
}

PROOF static thm cm_sc_call_bases(
    term phase, term ann, term caller, term oldenv,
    term oldfp, term oldregions, term ret, thm core) {
  thm opened_core = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_runtime_core_def, cm_ann_cursors_def,
      cm_ann_spills_def, cm_ann_saved_def, cm_ann_calls_def)), core);
  thm stack = conjunct2_rule(opened_core);
  thm opened_stack = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_runtime_stack_def, cm_cursor_phase_def,
      cm_phase_is_call_def, cm_phase_oldregions_def,
      cm_phase_oldfp_def, cm_phase_caller_def)), stack);
  term saved_list = cm_sc_constructor_arg(ann, 8, 6);
  term calls_list = cm_sc_constructor_arg(ann, 8, 7);
  thm saved_nonempty = cm_sc_consequence(opened_stack,
      `~(${saved_list:(cm_spill_frame)list} == [])`);
  thm calls_nonempty = cm_sc_consequence(opened_stack,
      `~(${calls_list:(cm_call_sim_frame)list} == [])`);
  thm saved_fid = cm_sc_consequence(opened_stack,
      `cm_spill_frame_fid
         (HD ${saved_list:(cm_spill_frame)list}) == ${caller:int}`);
  thm saved_fp = cm_sc_consequence(opened_stack,
      `cm_spill_frame_fp
         (HD ${saved_list:(cm_spill_frame)list}) == ${oldfp:int}`);
  thm call_base = cm_sc_consequence(opened_stack,
      `cm_call_sim_base
         (HD ${calls_list:(cm_call_sim_frame)list}) ==
       cm_state_fp (st:cm_src_state)`);
  thm call_saved = cm_sc_consequence(opened_stack,
      `cm_call_sim_saved
         (HD ${calls_list:(cm_call_sim_frame)list}) == ${oldfp:int}`);
  thm saved_head = spec_rule(
      `HD ${saved_list:(cm_spill_frame)list}`,
      cm_sc_spill_frame_reconstruct);
  saved_head = conv_rule(rewrite_conv(THM_LIST(
      saved_fid, saved_fp)), saved_head);
  thm saved_shape = cm_sc_cons_reconstruct(
      saved_list,
      `CONS:cm_spill_frame->(cm_spill_frame)list->
        (cm_spill_frame)list`,
      `TL ${saved_list:(cm_spill_frame)list}`,
      saved_head, saved_nonempty);
  thm call_head = spec_rule(
      `HD ${calls_list:(cm_call_sim_frame)list}`,
      cm_sc_call_frame_reconstruct);
  call_head = conv_rule(rewrite_conv(THM_LIST(
      call_base, call_saved)), call_head);
  thm calls_shape = cm_sc_cons_reconstruct(
      calls_list,
      `CONS:cm_call_sim_frame->(cm_call_sim_frame)list->
        (cm_call_sim_frame)list`,
      `TL ${calls_list:(cm_call_sim_frame)list}`,
      call_head, calls_nonempty);
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, caller, `st:cm_src_state`, ann,
      oldenv, oldfp, oldregions, ret, `owner:int`,
      `saved_break:int`, `saved_continue:int`,
      `rest:(cm_acursor)list`,
      `cm_spill_frame_spills
        (HD ${saved_list:(cm_spill_frame)list})`,
      `TL ${saved_list:(cm_spill_frame)list}`,
      `cm_call_sim_return
        (HD ${calls_list:(cm_call_sim_frame)list})`,
      `TL ${calls_list:(cm_call_sim_frame)list}`),
      cm_runtime_call_restore_region_bases);
  result = match_mp_rule(result, cm_sc_cursor_eq(ann, phase));
  result = conv_rule(rewrite_conv(THM_LIST(
      cm_ann_saved_def, cm_ann_calls_def)), result);
  result = match_mp_rule(result, saved_shape);
  result = match_mp_rule(result, calls_shape);
  return match_mp_rule(result, core);
}

PROOF static void cm_sc_accept(
    gnode branch, thm phase_shape, thm frames_eq,
    thm_list extra) {
  thm_list rules = THM_LIST(
      phase_shape, sym_rule(frames_eq),
      get_cm_step_def(), get_cm_capply_def(),
      get_cm_control_kind_def(), get_cm_control_value_def(),
      get_cm_control_status_def(), cm_sc_task_cond,
      cm_task_short_ready_def, cm_frames_short_ready_def,
      cm_frame_short_ready_def, cm_cursor_frames_def,
      cm_phase_frame_def, get_theorem_by_name("COND_CLAUSES"),
      get_theorem_by_name("COND_ID"),
      get_theorem_by_name("NOT_CONS_NIL"),
      get_theorem_by_name("HD"), get_theorem_by_name("TL"));
  for (size_t i = 0; i < vector_size(extra); ++i) {
    vector_add(&rules, extra[i]);
  }
  labeled_term_list assumptions = goal_lasmps(branch->g);
  for (size_t i = 0; i < vector_size(assumptions); ++i) {
    vector_add(&rules, assume_rule(assumptions[i].tm));
  }
  ACCEPT_TAC(branch, eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(branch->g))));
}

PROOF static thm cm_prove_task_short_c_phase_step(void) {
  term phase = `phase:cm_aphase`;
  term ann = cm_sc_runtime_annotation(phase);
  term task =
      `CMCTask (p:cm_program) (fid:int) (ctl:cm_control)
        (st:cm_src_state) (ks:(cm_frame)list)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (ctl:cm_control)
         (st:cm_src_state) (ks:(cm_frame)list)
         (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (phase:cm_aphase) (owner:int)
         (saved_break:int) (saved_continue:int)
         (rest:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         cm_task_generation_safe p
           (CMCTask p fid ctl st ks)
           (CMAnnotation pc temp breakpc continuepc
             (CMACursor phase owner saved_break saved_continue :: rest)
             spills saved calls) ==>
         cm_annotation_erases
           (CMCTask p fid ctl st ks)
           (CMAnnotation pc temp breakpc continuepc
             (CMACursor phase owner saved_break saved_continue :: rest)
             spills saved calls) ==>
         cm_runtime_core p fid st
           (CMAnnotation pc temp breakpc continuepc
             (CMACursor phase owner saved_break saved_continue :: rest)
             spills saved calls) ==>
         cm_task_short_ready (CMCTask p fid ctl st ks) ==>
         cm_task_short_ready
           (cm_step (CMCTask p fid ctl st ks))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm generation_safe = assume_rule(
      `cm_task_generation_safe (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`);
  thm task_generation = conjunct1_rule(conv_rule(
      rewrite_conv(THM_LIST(cm_task_generation_safe_def)),
      generation_safe));
  thm frames_generation = conjunct2_rule(conv_rule(
      reduce_rewrite_conv(THM_LIST(cm_task_generation_below_def)),
      task_generation));
  thm old_ready = conv_rule(rewrite_conv(THM_LIST(
      cm_task_short_ready_def)), assume_rule(
        `cm_task_short_ready ${task:cm_task}`));
  thm erases = assume_rule(
      `cm_annotation_erases ${task:cm_task} ${ann:cm_annotation}`);
  thm frames_eq = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_annotation_erases_def, cm_ann_cursors_def,
      cm_cursor_frames_def, cm_cursor_phase_def)), erases);
  thm core = assume_rule(
      `cm_runtime_core (p:cm_program) (fid:int)
        (st:cm_src_state) ${ann:cm_annotation}`);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(phase, get_datatype_cases("cm_aphase")),
      "Hsc_phase");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    thm phase_shape = cm_sc_named_shape(&branch, "Hsc_phase");
    term concrete_phase = rhs_of(phase_shape);
    term concrete_ann = cm_sc_runtime_annotation(concrete_phase);
    term tail = `cm_cursor_frames (rest:(cm_acursor)list)`;
    term parent_fid = i == 22
        ? cm_sc_constructor_arg(concrete_phase, 5, 0)
        : `fid:int`;
    thm concrete_generation = conv_rule(
        rewrite_conv(THM_LIST(sym_rule(frames_eq), phase_shape)),
        frames_generation);
    thm opened_generation = conv_rule(reduce_rewrite_conv(THM_LIST(
        cm_frames_generation_below_def,
        cm_frame_generation_below_def,
        cm_frame_parent_fid_def, cm_phase_frame_def)),
        concrete_generation);
    thm tail_generation = cm_sc_consequence(opened_generation,
        `cm_frames_generation_below (p:cm_program)
          ${parent_fid:int}
          (cm_state_nextgen (st:cm_src_state))
          ${tail:(cm_frame)list}`);
    thm concrete_ready = conv_rule(
        rewrite_conv(THM_LIST(sym_rule(frames_eq), phase_shape)),
        old_ready);
    thm opened_ready = conv_rule(reduce_rewrite_conv(THM_LIST(
        cm_frames_short_ready_def, cm_frame_short_ready_def,
        cm_phase_frame_def)), concrete_ready);
    thm tail_ready = cm_sc_consequence(opened_ready,
        `cm_frames_short_ready (st:cm_src_state)
          ${tail:(cm_frame)list}`);
    thm concrete_core = conv_rule(
        rewrite_conv(THM_LIST(phase_shape)), core);
    thm changed_ready = empty_theorem;
    if (i == 15 || i == 19) {
      size_t arity = i == 15 ? 4 : 6;
      size_t env_index = i == 15 ? 0 : 2;
      size_t regions_index = i == 15 ? 1 : 3;
      term oldenv = cm_sc_constructor_arg(
          concrete_phase, arity, env_index);
      term oldregions = cm_sc_constructor_arg(
          concrete_phase, arity, regions_index);
      term next_state =
          `cm_restore_scope (st:cm_src_state)
            ${oldenv:int->int->cm_value}
            ${oldregions:(cm_region)list}`;
      thm bases = cm_sc_scope_bases(
          concrete_phase, concrete_ann, oldenv, oldregions,
          concrete_core);
      changed_ready = cm_sc_transport_frames(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          next_state, tail, bases, tail_generation, tail_ready);
    } else if (i == 22) {
      term caller = cm_sc_constructor_arg(concrete_phase, 5, 0);
      term oldenv = cm_sc_constructor_arg(concrete_phase, 5, 1);
      term oldfp = cm_sc_constructor_arg(concrete_phase, 5, 2);
      term oldregions = cm_sc_constructor_arg(concrete_phase, 5, 3);
      term ret = cm_sc_constructor_arg(concrete_phase, 5, 4);
      term next_state =
          `cm_restore_call (st:cm_src_state)
            ${oldenv:int->int->cm_value} ${oldfp:int}
            ${oldregions:(cm_region)list}`;
      thm bases = cm_sc_call_bases(
          concrete_phase, concrete_ann, caller, oldenv,
          oldfp, oldregions, ret, concrete_core);
      changed_ready = cm_sc_transport_frames(
          `p:cm_program`, caller, `st:cm_src_state`,
          next_state, tail, bases, tail_generation, tail_ready);
    }
    if (IS_NULL(changed_ready)) {
      cm_sc_accept(branch, phase_shape, frames_eq,
          THM_LIST(tail_ready));
    } else {
      cm_sc_accept(branch, phase_shape, frames_eq,
          THM_LIST(tail_ready, changed_ready));
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_task_short_c_phase_step =
    cm_prove_task_short_c_phase_step();

PROOF static thm cm_prove_task_short_c_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (ctl:cm_control)
         (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         cm_task_generation_safe p (CMCTask p fid ctl st ks) ann ==>
         cm_annotation_erases (CMCTask p fid ctl st ks) ann ==>
         cm_task_runtime_invariant p (CMCTask p fid ctl st ks) ann ==>
         cm_task_short_ready (CMCTask p fid ctl st ks) ==>
         cm_task_short_ready
           (cm_step (CMCTask p fid ctl st ks))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list ann_cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`ann:cm_annotation`,
        get_datatype_cases("cm_annotation")),
      "Hsc_ann");
  gnode branch = ann_cases[0];
  thm ann_shape = cm_sc_named_shape(&branch, "Hsc_ann");
  term cursors = cm_sc_constructor_arg(rhs_of(ann_shape), 8, 4);
  gnode_list cursor_cases = DISJ_CASES_TAC(branch,
      ispec_rule(cursors, get_theorem_by_name("list_CASES")),
      "Hsc_cursors");
  {
    gnode nil = cursor_cases[0];
    thm cursors_nil = cm_sc_named_shape(&nil, "Hsc_cursors");
    thm runtime = conv_rule(rewrite_conv(THM_LIST(
        ann_shape, cursors_nil)), assume_rule(
          `cm_task_runtime_invariant (p:cm_program)
            (CMCTask p (fid:int) (ctl:cm_control)
              (st:cm_src_state) (ks:(cm_frame)list))
            (ann:cm_annotation)`));
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        cm_task_runtime_invariant_def, cm_runtime_stack_def,
        cm_ann_cursors_def)), runtime);
    CONTR_TAC(nil, impossible);
  }
  gnode cons = cursor_cases[1];
  thm cursors_cons = cm_sc_named_shape(&cons, "Hsc_cursors");
  term cursor = cm_sc_app_arg_from_right(rhs_of(cursors_cons), 1);
  gnode_list cursor_shapes = DISJ_CASES_TAC(cons,
      ispec_rule(cursor, get_datatype_cases("cm_acursor")),
      "Hsc_cursor");
  gnode cursor_branch = cursor_shapes[0];
  thm cursor_shape = cm_sc_named_shape(&cursor_branch, "Hsc_cursor");
  thm full_shape = conv_rule(rewrite_conv(THM_LIST(
      cursors_cons, cursor_shape)), ann_shape);
  term shaped_ann = rhs_of(full_shape);
  term pc_value = cm_sc_constructor_arg(shaped_ann, 8, 0);
  term temp_value = cm_sc_constructor_arg(shaped_ann, 8, 1);
  term break_value = cm_sc_constructor_arg(shaped_ann, 8, 2);
  term continue_value = cm_sc_constructor_arg(shaped_ann, 8, 3);
  term spills_value = cm_sc_constructor_arg(shaped_ann, 8, 5);
  term saved_value = cm_sc_constructor_arg(shaped_ann, 8, 6);
  term calls_value = cm_sc_constructor_arg(shaped_ann, 8, 7);
  term shaped_cursor = rhs_of(cursor_shape);
  term phase_value = cm_sc_constructor_arg(shaped_cursor, 4, 0);
  term owner_value = cm_sc_constructor_arg(shaped_cursor, 4, 1);
  term owner_break_value = cm_sc_constructor_arg(shaped_cursor, 4, 2);
  term owner_continue_value = cm_sc_constructor_arg(shaped_cursor, 4, 3);
  term rest_value = cm_sc_app_arg_from_right(
      rhs_of(cursors_cons), 0);
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `ctl:cm_control`,
      `st:cm_src_state`, `ks:(cm_frame)list`,
      pc_value, temp_value, break_value, continue_value,
      phase_value, owner_value, owner_break_value,
      owner_continue_value, rest_value, spills_value,
      saved_value, calls_value), cm_task_short_c_phase_step);
  thm_list premises = THM_LIST(
      assume_rule(
        `cm_task_generation_safe (p:cm_program)
          (CMCTask p (fid:int) (ctl:cm_control)
            (st:cm_src_state) (ks:(cm_frame)list))
          (ann:cm_annotation)`),
      assume_rule(
        `cm_annotation_erases
          (CMCTask (p:cm_program) (fid:int) (ctl:cm_control)
            (st:cm_src_state) (ks:(cm_frame)list))
          (ann:cm_annotation)`));
  for (size_t i = 0; i < vector_size(premises); ++i) {
    result = match_mp_rule(result, conv_rule(
        rewrite_conv(THM_LIST(full_shape)), premises[i]));
  }
  thm runtime = conv_rule(rewrite_conv(THM_LIST(full_shape)),
      assume_rule(
        `cm_task_runtime_invariant (p:cm_program)
          (CMCTask p (fid:int) (ctl:cm_control)
            (st:cm_src_state) (ks:(cm_frame)list))
          (ann:cm_annotation)`));
  thm opened_runtime = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_runtime_invariant_def)), runtime);
  term core_term = `cm_runtime_core (p:cm_program) (fid:int)
      (st:cm_src_state) ${shaped_ann:cm_annotation}`;
  thm core_view = apply_conversion(
      rewrite_conv(THM_LIST(cm_runtime_core_def)), core_term);
  thm concrete_core = eq_mp_rule(
      sym_rule(core_view), opened_runtime);
  result = match_mp_rule(result, concrete_core);
  result = match_mp_rule(result, assume_rule(
      `cm_task_short_ready
        (CMCTask (p:cm_program) (fid:int) (ctl:cm_control)
          (st:cm_src_state) (ks:(cm_frame)list))`));
  gnode reduced = CONV_TAC(cursor_branch,
      rewrite_conv(THM_LIST(full_shape)));
  ACCEPT_TAC(reduced, result);
  return gnode_prove(root);
}
PROOF thm cm_task_short_c_step = cm_prove_task_short_c_step();

PROOF static int cmc_preservation_short_control_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_short_control_axioms_before,
      "cmc_preservation_short_control introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_short_control_checks =
    cmc_preservation_short_control_final_checks();
