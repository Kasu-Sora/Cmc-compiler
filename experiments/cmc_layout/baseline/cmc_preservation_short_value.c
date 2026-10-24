#include "proof/proof.h"
#include "userlib/renderers.h"
#include "cmc_preservation_invariant_transition.h"
#include "userlib/proof.h"
#include "cmc_preservation_short_value.h"
#include "cmc_preservation_short_defs.h"
#include "cmc_preservation_short_bases.h"
#include "cmc_preservation_generation.h"
#include "cmc_preservation_call_value.h"

#require "cmc_preservation_short_start.c"
#require "cmc_preservation_call_value.c"

PROOF static size_t _cmc_preservation_short_value_axioms_before =
    vector_size(get_all_axioms());

PROOF static term cm_sv_app_arg_from_right(
    term application, size_t offset) {
  for (size_t i = 0; i < offset; ++i) {
    application = dest_comb(application).tm1;
  }
  return dest_comb(application).tm2;
}

PROOF static term cm_sv_constructor_arg(
    term constructor, size_t arity, size_t index) {
  return cm_sv_app_arg_from_right(
      constructor, arity - index - 1);
}

PROOF static thm cm_sv_named_shape(
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

PROOF static term cm_sv_runtime_annotation(term phase) {
  return `CMAnnotation (pc:int) (temp:int) (breakpc:int)
    (continuepc:int)
    (CMACursor ${phase:cm_aphase} (owner:int)
       (saved_break:int) (saved_continue:int) ::
     (rest:(cm_acursor)list))
    (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
    (calls:(cm_call_sim_frame)list)`;
}

PROOF static thm cm_sv_cursor_eq(term ann, term phase) {
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

PROOF static thm cm_sv_same_region_bases(
    term old_state, term new_state, thm_list state_rules) {
  term limit = mk_comb(`cm_state_nextgen`, old_state);
  term proposition =
      mk_comb(mk_comb(mk_comb(`cm_region_bases_below_equal`,
        mk_comb(`cm_state_regions`, new_state)),
        mk_comb(`cm_state_regions`, old_state)), limit);
  thm target_view = apply_conversion(
      reduce_rewrite_conv(state_rules), proposition);
  thm reflexive = specl_rule(TERM_LIST(
      mk_comb(`cm_state_regions`, old_state), limit),
      cm_region_bases_below_equal_refl);
  return eq_mp_rule(sym_rule(target_view), reflexive);
}

PROOF static thm cm_sv_transport_frames(
    term p, term fid, term old_state, term new_state,
    term frames, thm bases, thm generation, thm ready) {
  return match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        frames, p, fid, old_state, new_state,
        mk_comb(`cm_state_nextgen`, old_state)),
        cm_frames_short_ready_bases), bases), generation), ready);
}
PROOF static thm cm_sv_consequence(thm given, term wanted) {
  return mp_rule(taut_rule(mk_imp(concl(given), wanted)), given);
}


PROOF static thm cm_prove_sv_task_cond(void) {
  gnode root = gnode_new_with_ccl(
      `!(condition:bool) (yes:cm_task) (no:cm_task).
         cm_task_short_ready (if condition then yes else no) <=>
         (if condition
          then cm_task_short_ready yes
          else cm_task_short_ready no)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      introduced, `condition:bool`, "Hsv_condition");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_WITH_ASMP_TAC(cases[i], reduce_rewrite_conv, THM_LIST());
  }
  return gnode_prove(root);
}
PROOF static thm cm_sv_task_cond = cm_prove_sv_task_cond();

PROOF static thm cm_sv_scope_bases(
    term phase, term ann, term oldenv, term oldregions,
    thm core) {
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`, ann,
      phase, oldenv, oldregions, `owner:int`,
      `saved_break:int`, `saved_continue:int`,
      `rest:(cm_acursor)list`),
      cm_runtime_scope_restore_region_bases);
  result = match_mp_rule(result, cm_sv_cursor_eq(ann, phase));
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

PROOF static void cm_sv_accept(
    gnode branch, thm phase_shape, thm frames_eq,
    thm_list extra) {
  thm_list rules = THM_LIST(
      phase_shape, sym_rule(frames_eq),
      get_cm_step_def(), get_cm_vapply_def(),
      get_cm_begin_call_def(), cm_sv_task_cond,
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

PROOF static thm cm_prove_task_short_v_phase_step(void) {
  term phase = `phase:cm_aphase`;
  term ann = cm_sv_runtime_annotation(phase);
  term task =
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
        (st:cm_src_state) (ks:(cm_frame)list)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (v:cm_value)
         (st:cm_src_state) (ks:(cm_frame)list)
         (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (phase:cm_aphase) (owner:int)
         (saved_break:int) (saved_continue:int)
         (rest:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         cm_task_generation_safe p
           (CMVTask p fid v st ks)
           (CMAnnotation pc temp breakpc continuepc
             (CMACursor phase owner saved_break saved_continue :: rest)
             spills saved calls) ==>
         cm_annotation_erases
           (CMVTask p fid v st ks)
           (CMAnnotation pc temp breakpc continuepc
             (CMACursor phase owner saved_break saved_continue :: rest)
             spills saved calls) ==>
         cm_runtime_core p fid st
           (CMAnnotation pc temp breakpc continuepc
             (CMACursor phase owner saved_break saved_continue :: rest)
             spills saved calls) ==>
         cm_task_short_ready (CMVTask p fid v st ks) ==>
         cm_task_short_ready
           (cm_step (CMVTask p fid v st ks))`);
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
      "Hsv_phase");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    thm phase_shape = cm_sv_named_shape(&branch, "Hsv_phase");
    term concrete_phase = rhs_of(phase_shape);
    term concrete_ann = cm_sv_runtime_annotation(concrete_phase);
    term tail = `cm_cursor_frames (rest:(cm_acursor)list)`;
    term parent_fid = i == 22
        ? cm_sv_constructor_arg(concrete_phase, 5, 0)
        : `fid:int`;
    thm concrete_generation = conv_rule(
        rewrite_conv(THM_LIST(sym_rule(frames_eq), phase_shape)),
        frames_generation);
    thm opened_generation = conv_rule(reduce_rewrite_conv(THM_LIST(
        cm_frames_generation_below_def,
        cm_frame_generation_below_def,
        cm_frame_parent_fid_def, cm_phase_frame_def)),
        concrete_generation);
    thm tail_generation = cm_sv_consequence(opened_generation,
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
    thm tail_ready = cm_sv_consequence(opened_ready,
        `cm_frames_short_ready (st:cm_src_state)
          ${tail:(cm_frame)list}`);
    thm concrete_core = conv_rule(
        rewrite_conv(THM_LIST(phase_shape)), core);
    thm changed_ready = empty_theorem;
    if (i == 3) {
      term ptr = cm_sv_constructor_arg(concrete_phase, 2, 0);
      term ty = cm_sv_constructor_arg(concrete_phase, 2, 1);
      term next_state =
          `cm_state_store ${ty:cm_type} ${ptr:cm_value}
            (v:cm_value) (st:cm_src_state)`;
      thm_list state_rules = get_cm_state_core_defs();
      vector_add(&state_rules, get_cm_state_store_def());
      changed_ready = cm_sv_transport_frames(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          next_state, tail,
          cm_sv_same_region_bases(
            `st:cm_src_state`, next_state, state_rules),
          tail_generation, tail_ready);
    } else if (i == 10 || i == 11) {
      term next_output = i == 10
          ? `(APPEND (cm_state_output (st:cm_src_state))
               [tower_u8 (cm_value_number st (v:cm_value))])`
          : `(APPEND (cm_state_output (st:cm_src_state))
               (tower_decimal (cm_value_number st (v:cm_value))))`;
      term next_state =
          `cm_state_io (st:cm_src_state)
            (cm_state_input st) ${next_output:(int)list}`;
      changed_ready = cm_sv_transport_frames(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          next_state, tail,
          cm_sv_same_region_bases(`st:cm_src_state`, next_state,
            get_cm_state_core_defs()),
          tail_generation, tail_ready);
    } else if (i == 14) {
      term slot = cm_sv_constructor_arg(concrete_phase, 1, 0);
      term next_state =
          `cm_state_store
            (cm_slot_ty (inth ${slot:int}
              (cm_function_locals
                (inth (fid:int)
                  (cm_program_functions (p:cm_program))))))
            (cm_state_env (st:cm_src_state) 1i ${slot:int})
            (v:cm_value) st`;
      thm_list state_rules = get_cm_state_core_defs();
      vector_add(&state_rules, get_cm_state_store_def());
      changed_ready = cm_sv_transport_frames(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          next_state, tail,
          cm_sv_same_region_bases(
            `st:cm_src_state`, next_state, state_rules),
          tail_generation, tail_ready);
    } else if (i == 15 || i == 19) {
      size_t arity = i == 15 ? 4 : 6;
      size_t env_index = i == 15 ? 0 : 2;
      size_t regions_index = i == 15 ? 1 : 3;
      term oldenv = cm_sv_constructor_arg(
          concrete_phase, arity, env_index);
      term oldregions = cm_sv_constructor_arg(
          concrete_phase, arity, regions_index);
      term next_state =
          `cm_restore_scope (st:cm_src_state)
            ${oldenv:int->int->cm_value}
            ${oldregions:(cm_region)list}`;
      thm bases = cm_sv_scope_bases(
          concrete_phase, concrete_ann, oldenv, oldregions,
          concrete_core);
      changed_ready = cm_sv_transport_frames(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          next_state, tail, bases, tail_generation, tail_ready);
    } else if (i == 21) {
      term callee = cm_sv_constructor_arg(concrete_phase, 8, 0);
      term values = cm_sv_constructor_arg(concrete_phase, 8, 2);
      term entered_state =
          `cm_enter_call (p:cm_program) ${callee:int}
            (REVERSE ((v:cm_value) :: ${values:(cm_value)list}))
            (st:cm_src_state)`;
      thm bases = specl_rule(TERM_LIST(
          `p:cm_program`, callee, `st:cm_src_state`,
          `REVERSE ((v:cm_value) :: ${values:(cm_value)list})`),
          cm_call_regions_bases);
      changed_ready = cm_sv_transport_frames(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          entered_state, tail, bases, tail_generation, tail_ready);
    }
    if (i == 4) {
      term op = cm_sv_constructor_arg(concrete_phase, 4, 0);
      gnode_list zero_cases = BOOL_CASES_TAC(
          branch, `${op:int} == 0i`, "Hsv_op_zero");
      for (size_t j = 0; j < vector_size(zero_cases); ++j) {
        gnode_list one_cases = BOOL_CASES_TAC(
            zero_cases[j], `${op:int} == 1i`, "Hsv_op_one");
        for (size_t k = 0; k < vector_size(one_cases); ++k) {
          gnode_list truth_cases = BOOL_CASES_TAC(
              one_cases[k],
              `cm_truth (st:cm_src_state) (v:cm_value)`,
              "Hsv_truth");
          for (size_t m = 0; m < vector_size(truth_cases); ++m) {
            cm_sv_accept(truth_cases[m], phase_shape, frames_eq,
                THM_LIST(tail_ready));
          }
        }
      }
      continue;
    }
    if (IS_NULL(changed_ready)) {
      cm_sv_accept(branch, phase_shape, frames_eq,
          THM_LIST(tail_ready));
    } else {
      cm_sv_accept(branch, phase_shape, frames_eq,
          THM_LIST(tail_ready, changed_ready));
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_task_short_v_phase_step =
    cm_prove_task_short_v_phase_step();

PROOF static thm cm_prove_task_short_v_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (v:cm_value)
         (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         cm_task_generation_safe p (CMVTask p fid v st ks) ann ==>
         cm_annotation_erases (CMVTask p fid v st ks) ann ==>
         cm_task_runtime_invariant p (CMVTask p fid v st ks) ann ==>
         cm_task_short_ready (CMVTask p fid v st ks) ==>
         cm_task_short_ready
           (cm_step (CMVTask p fid v st ks))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list ann_cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`ann:cm_annotation`,
        get_datatype_cases("cm_annotation")),
      "Hsv_ann");
  gnode branch = ann_cases[0];
  thm ann_shape = cm_sv_named_shape(&branch, "Hsv_ann");
  term cursors = cm_sv_constructor_arg(rhs_of(ann_shape), 8, 4);
  gnode_list cursor_cases = DISJ_CASES_TAC(branch,
      ispec_rule(cursors, get_theorem_by_name("list_CASES")),
      "Hsv_cursors");
  {
    gnode nil = cursor_cases[0];
    thm cursors_nil = cm_sv_named_shape(&nil, "Hsv_cursors");
    thm runtime = conv_rule(rewrite_conv(THM_LIST(
        ann_shape, cursors_nil)), assume_rule(
          `cm_task_runtime_invariant (p:cm_program)
            (CMVTask p (fid:int) (v:cm_value)
              (st:cm_src_state) (ks:(cm_frame)list))
            (ann:cm_annotation)`));
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        cm_task_runtime_invariant_def, cm_runtime_stack_def,
        cm_ann_cursors_def)), runtime);
    CONTR_TAC(nil, impossible);
  }
  gnode cons = cursor_cases[1];
  thm cursors_cons = cm_sv_named_shape(&cons, "Hsv_cursors");
  term cursor = cm_sv_app_arg_from_right(rhs_of(cursors_cons), 1);
  gnode_list cursor_shapes = DISJ_CASES_TAC(cons,
      ispec_rule(cursor, get_datatype_cases("cm_acursor")),
      "Hsv_cursor");
  gnode cursor_branch = cursor_shapes[0];
  thm cursor_shape = cm_sv_named_shape(&cursor_branch, "Hsv_cursor");
  thm full_shape = conv_rule(rewrite_conv(THM_LIST(
      cursors_cons, cursor_shape)), ann_shape);
  term shaped_ann = rhs_of(full_shape);
  term pc_value = cm_sv_constructor_arg(shaped_ann, 8, 0);
  term temp_value = cm_sv_constructor_arg(shaped_ann, 8, 1);
  term break_value = cm_sv_constructor_arg(shaped_ann, 8, 2);
  term continue_value = cm_sv_constructor_arg(shaped_ann, 8, 3);
  term spills_value = cm_sv_constructor_arg(shaped_ann, 8, 5);
  term saved_value = cm_sv_constructor_arg(shaped_ann, 8, 6);
  term calls_value = cm_sv_constructor_arg(shaped_ann, 8, 7);
  term shaped_cursor = rhs_of(cursor_shape);
  term phase_value = cm_sv_constructor_arg(shaped_cursor, 4, 0);
  term owner_value = cm_sv_constructor_arg(shaped_cursor, 4, 1);
  term owner_break_value = cm_sv_constructor_arg(shaped_cursor, 4, 2);
  term owner_continue_value = cm_sv_constructor_arg(shaped_cursor, 4, 3);
  term rest_value = cm_sv_app_arg_from_right(
      rhs_of(cursors_cons), 0);
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `v:cm_value`,
      `st:cm_src_state`, `ks:(cm_frame)list`,
      pc_value, temp_value, break_value, continue_value,
      phase_value, owner_value, owner_break_value,
      owner_continue_value, rest_value, spills_value,
      saved_value, calls_value), cm_task_short_v_phase_step);
  thm_list premises = THM_LIST(
      assume_rule(
        `cm_task_generation_safe (p:cm_program)
          (CMVTask p (fid:int) (v:cm_value)
            (st:cm_src_state) (ks:(cm_frame)list))
          (ann:cm_annotation)`),
      assume_rule(
        `cm_annotation_erases
          (CMVTask (p:cm_program) (fid:int) (v:cm_value)
            (st:cm_src_state) (ks:(cm_frame)list))
          (ann:cm_annotation)`));
  for (size_t i = 0; i < vector_size(premises); ++i) {
    result = match_mp_rule(result, conv_rule(
        rewrite_conv(THM_LIST(full_shape)), premises[i]));
  }
  thm runtime = conv_rule(rewrite_conv(THM_LIST(full_shape)),
      assume_rule(
        `cm_task_runtime_invariant (p:cm_program)
          (CMVTask p (fid:int) (v:cm_value)
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
        (CMVTask (p:cm_program) (fid:int) (v:cm_value)
          (st:cm_src_state) (ks:(cm_frame)list))`));
  gnode reduced = CONV_TAC(cursor_branch,
      rewrite_conv(THM_LIST(full_shape)));
  ACCEPT_TAC(reduced, result);
  return gnode_prove(root);
}
PROOF thm cm_task_short_v_step = cm_prove_task_short_v_step();

PROOF static int cmc_preservation_short_value_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_short_value_axioms_before,
      "cmc_preservation_short_value introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_short_value_checks =
    cmc_preservation_short_value_final_checks();
