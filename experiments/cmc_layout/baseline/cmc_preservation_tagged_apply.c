#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_tagged_apply.h"

#require "cmc_preservation_tagged_start.c"

PROOF static size_t _cmc_preservation_tagged_apply_axioms_before =
    vector_size(get_all_axioms());

PROOF static term cm_tga_annotation(term phase) {
  return `CMAnnotation (pc:int) (temp:int) (breakpc:int)
    (continuepc:int)
    (CMACursor ${phase:cm_aphase} (owner:int)
       (saved_break:int) (saved_continue:int) ::
     (rest:(cm_acursor)list))
    (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
    (calls:(cm_call_sim_frame)list)`;
}

PROOF static term cm_tga_app_arg_from_right(
    term application, size_t offset) {
  for (size_t i = 0; i < offset; ++i) {
    application = dest_comb(application).tm1;
  }
  return dest_comb(application).tm2;
}

PROOF static term cm_tga_phase_arg(
    term phase, size_t arity, size_t index) {
  return cm_tga_app_arg_from_right(
      phase, arity - index - 1);
}

PROOF static gnode cm_tga_open_shape(
    gnode branch, const char *label) {
  while (true) {
    labeled_term_list assumptions = goal_lasmps(branch->g);
    int index = labeled_term_list_index(assumptions, label);
    if (!is_exists(assumptions[index].tm)) break;
    branch = ASMP_EXISTS_TAC(branch, label, NULL);
  }
  return branch;
}

PROOF static thm cm_tga_shape(gnode branch, const char *label) {
  labeled_term_list assumptions = goal_lasmps(branch->g);
  return assume_rule(assumptions[
      labeled_term_list_index(assumptions, label)].tm);
}

PROOF static thm_list cm_tga_core_rules(void) {
  return THM_LIST(
      cm_runtime_core_def, cm_runtime_stack_def,
      cm_phase_is_call_def, cm_phase_is_scope_def,
      cm_phase_is_halt_def, cm_phase_oldregions_def,
      cm_phase_oldfp_def, cm_phase_caller_def,
      cm_ann_cursors_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_ann_calls_def,
      cm_cursor_phase_def, cm_cursor_temp_def,
      cm_cursor_break_def, cm_cursor_continue_def,
      get_theorem_by_name("HD"), get_theorem_by_name("TL"),
      get_theorem_by_name("NOT_CONS_NIL"));
}

PROOF static thm cm_tga_runtime_layout(
    term ann, thm core) {
  thm opened = conv_rule(rewrite_conv(THM_LIST(
      cm_runtime_core_def)), core);
  thm stack = conjunct2_rule(opened);
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `fid:int`,
      `cm_ann_cursors ${ann:cm_annotation}`,
      `cm_ann_spills ${ann:cm_annotation}`,
      `cm_ann_saved ${ann:cm_annotation}`,
      `cm_ann_calls ${ann:cm_annotation}`),
      cm_runtime_stack_memory_layout);
  return match_mp_rule(result, stack);
}

PROOF static thm cm_tga_scope_prefix(
    term phase, term ann, thm core) {
  thm stack = conjunct2_rule(conv_rule(rewrite_conv(THM_LIST(
      cm_runtime_core_def)), core));
  thm opened = conv_rule(reduce_rewrite_conv(
      cm_tga_core_rules()), stack);
  term target =
      `cm_region_prefix_safe (p:cm_program)
        (cm_state_regions (st:cm_src_state)) (fid:int)
        (cm_state_fp st) (cm_state_regions st)
        (cm_phase_oldregions ${phase:cm_aphase})`;
  thm target_view = apply_conversion(
      reduce_rewrite_conv(THM_LIST(cm_phase_oldregions_def)), target);
  thm normalized = mp_rule(taut_rule(mk_imp(
      concl(opened), rhs_of(target_view))), opened);
  return eq_mp_rule(sym_rule(target_view), normalized);
}

PROOF static void cm_tga_accept_v(
    gnode branch, thm source, thm phase_shape, thm_list extra) {
  thm_list rules = THM_LIST(
      phase_shape, cm_phase_frame_def, get_cm_vapply_def(),
      cm_task_tagged_valid_cond, cm_task_tagged_valid_def,
      get_theorem_by_name("COND_ID"));
  for (size_t i = 0; i < vector_size(extra); ++i) {
    vector_add(&rules, extra[i]);
  }
  thm normalized = conv_rule(reduce_rewrite_conv(rules), source);
  thm target_view = apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(branch->g));
  ACCEPT_TAC(branch, eq_mp_rule(sym_rule(target_view), normalized));
}

PROOF static thm cm_prove_tagged_span_vapply_phase(void) {
  term phase = `phase:cm_aphase`;
  term ann = cm_tga_annotation(phase);
  term body = imp_chain(TERM_LIST(
      `cm_typed_program (p:cm_program)`,
      `cm_state_generation_below (p:cm_program) (fid:int)
        (st:cm_src_state)`,
      `cm_runtime_core (p:cm_program) (fid:int)
        (st:cm_src_state) ${ann:cm_annotation}`,
      `cm_tagged_span_valid (st:cm_src_state)`),
      `cm_task_tagged_valid
        (cm_vapply (p:cm_program) (fid:int)
          (cm_phase_frame ${phase:cm_aphase}) (v:cm_value)
          (st:cm_src_state) (cm_cursor_frames (rest:(cm_acursor)list)))`);
  gnode root_node = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root_node);
  thm typed = assume_rule(`cm_typed_program (p:cm_program)`);
  thm generation = assume_rule(
      `cm_state_generation_below (p:cm_program) (fid:int)
        (st:cm_src_state)`);
  thm core = assume_rule(
      `cm_runtime_core (p:cm_program) (fid:int)
        (st:cm_src_state) ${ann:cm_annotation}`);
  thm old_valid = assume_rule(
      `cm_tagged_span_valid (st:cm_src_state)`);
  gnode_list cases = DISJ_CASES_TAC(
      introduced,
      ispec_rule(phase, get_datatype_cases("cm_aphase")),
      "Hphase");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cm_tga_open_shape(cases[i], "Hphase");
    thm phase_shape = cm_tga_shape(branch, "Hphase");
    term concrete_phase = rhs_of(phase_shape);
    term concrete_ann = cm_tga_annotation(concrete_phase);
    thm concrete_core = conv_rule(
        rewrite_conv(THM_LIST(phase_shape)), core);
    if (i == 3) {
      term ptr = cm_tga_phase_arg(concrete_phase, 2, 0);
      term ty = cm_tga_phase_arg(concrete_phase, 2, 1);
      term store_term =
          `cm_store_ok ${ty:cm_type} ${ptr:cm_value}
            (st:cm_src_state)`;
      gnode_list store_cases = BOOL_CASES_TAC(
          branch, store_term, "Hstore_ok");
      {
        thm layout = cm_tga_runtime_layout(
            concrete_ann, concrete_core);
        thm stored = specl_rule(TERM_LIST(
            `p:cm_program`, `st:cm_src_state`,
            `cm_ann_calls ${concrete_ann:cm_annotation}`,
            `CMSpillFrame (fid:int) (cm_state_fp (st:cm_src_state))
               (cm_ann_spills ${concrete_ann:cm_annotation}) ::
             cm_ann_saved ${concrete_ann:cm_annotation}`,
            ty, ptr, `v:cm_value`), cm_tagged_span_store);
        stored = match_mp_rule(stored, layout);
        stored = match_mp_rule(stored, assume_rule(store_term));
        stored = match_mp_rule(stored, old_valid);
        cm_tga_accept_v(store_cases[0], stored, phase_shape,
            THM_LIST(assume_rule(store_term)));
      }
      {
        cm_tga_accept_v(store_cases[1], old_valid, phase_shape,
            THM_LIST(assume_rule(mk_not(store_term))));
      }
    } else if (i == 10 || i == 11) {
      term output = i == 10
          ? `APPEND (cm_state_output (st:cm_src_state))
              [tower_u8 (cm_value_number st (v:cm_value))]`
          : `APPEND (cm_state_output (st:cm_src_state))
              (tower_decimal (cm_value_number st (v:cm_value)))`;
      thm io_valid = specl_rule(TERM_LIST(
          `st:cm_src_state`, `cm_state_input (st:cm_src_state)`,
          output), cm_tagged_span_io);
      io_valid = match_mp_rule(io_valid, old_valid);
      cm_tga_accept_v(branch, io_valid, phase_shape, THM_LIST());
    } else if (i == 14) {
      term slot = cm_tga_phase_arg(concrete_phase, 1, 0);
      term init_ty =
          `cm_slot_ty (inth ${slot:int}
            (cm_function_locals
              (inth (fid:int) (cm_program_functions (p:cm_program)))))`;
      term init_ptr =
          `cm_state_env (st:cm_src_state) 1i ${slot:int}`;
      term store_term =
          `cm_store_ok ${init_ty:cm_type} ${init_ptr:cm_value}
            (st:cm_src_state)`;
      term address_term =
          `cm_binding_address_ok (p:cm_program) (fid:int)
            1i ${slot:int} (st:cm_src_state)`;
      gnode_list store_cases = BOOL_CASES_TAC(
          branch, store_term, "Hinit_store_ok");
      gnode_list address_cases = BOOL_CASES_TAC(
          store_cases[0], address_term, "Hinit_address_ok");
      {
        thm layout = cm_tga_runtime_layout(
            concrete_ann, concrete_core);
        thm stored = specl_rule(TERM_LIST(
            `p:cm_program`, `st:cm_src_state`,
            `cm_ann_calls ${concrete_ann:cm_annotation}`,
            `CMSpillFrame (fid:int) (cm_state_fp (st:cm_src_state))
               (cm_ann_spills ${concrete_ann:cm_annotation}) ::
             cm_ann_saved ${concrete_ann:cm_annotation}`,
            init_ty, init_ptr, `v:cm_value`), cm_tagged_span_store);
        stored = match_mp_rule(stored, layout);
        stored = match_mp_rule(stored, assume_rule(store_term));
        stored = match_mp_rule(stored, old_valid);
        cm_tga_accept_v(address_cases[0], stored, phase_shape,
            THM_LIST(assume_rule(store_term),
              assume_rule(address_term)));
      }
      {
        cm_tga_accept_v(address_cases[1], old_valid, phase_shape,
            THM_LIST(assume_rule(store_term),
              assume_rule(mk_not(address_term))));
      }
      gnode_list failed_address_cases = BOOL_CASES_TAC(
          store_cases[1], address_term, "Hinit_address_failed_store");
      for (size_t j = 0;
           j < vector_size(failed_address_cases); ++j) {
        cm_tga_accept_v(failed_address_cases[j], old_valid, phase_shape,
            THM_LIST(assume_rule(mk_not(store_term))));
      }
    } else if (i == 15 || i == 19) {
      size_t phase_arity = i == 15 ? 4 : 6;
      size_t env_index = i == 15 ? 0 : 2;
      size_t regions_index = i == 15 ? 1 : 3;
      term oldenv = cm_tga_phase_arg(
          concrete_phase, phase_arity, env_index);
      term oldregions = cm_tga_phase_arg(
          concrete_phase, phase_arity, regions_index);
      thm prefix = cm_tga_scope_prefix(
          concrete_phase, concrete_ann, concrete_core);
      thm oldregions_eq = apply_conversion(
          reduce_rewrite_conv(THM_LIST(cm_phase_oldregions_def)),
          `cm_phase_oldregions ${concrete_phase:cm_aphase}`);
      prefix = conv_rule(rewrite_conv(THM_LIST(oldregions_eq)), prefix);
      thm restored = specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`,
          `cm_state_fp (st:cm_src_state)`, `st:cm_src_state`,
          oldenv, oldregions), cm_tagged_span_restore_scope);
      restored = match_mp_rule(restored, prefix);
      restored = match_mp_rule(restored, old_valid);
      cm_tga_accept_v(branch, restored, phase_shape, THM_LIST());
    } else if (i == 21) {
      term callee = cm_tga_phase_arg(concrete_phase, 8, 0);
      term rest_args = cm_tga_phase_arg(concrete_phase, 8, 1);
      term values = cm_tga_phase_arg(concrete_phase, 8, 2);
      term ret = cm_tga_phase_arg(concrete_phase, 8, 3);
      term rest_nil_term =
          `${rest_args:(cm_expr)list} == ([]:(cm_expr)list)`;
      gnode_list rest_cases = BOOL_CASES_TAC(
          branch, rest_nil_term, "Hrest_nil");
      {
        thm result = specl_rule(TERM_LIST(
            `p:cm_program`, `fid:int`, callee,
            `REVERSE ((v:cm_value) :: ${values:(cm_value)list})`,
            `st:cm_src_state`, ret,
            `cm_cursor_frames (rest:(cm_acursor)list)`,
            concrete_ann), cm_tagged_span_begin_call_runtime);
        result = match_mp_rule(result, typed);
        result = match_mp_rule(result, generation);
        result = match_mp_rule(result, concrete_core);
        result = match_mp_rule(result, old_valid);
        cm_tga_accept_v(rest_cases[0], result, phase_shape,
            THM_LIST(assume_rule(rest_nil_term)));
      }
      {
        cm_tga_accept_v(rest_cases[1], old_valid, phase_shape,
            THM_LIST(assume_rule(mk_not(rest_nil_term))));
      }
    } else {
      cm_tga_accept_v(branch, old_valid, phase_shape, THM_LIST());
    }
  }
  return gnode_prove(root_node);
}
PROOF thm cm_tagged_span_vapply_phase =
    cm_prove_tagged_span_vapply_phase();

PROOF static void cm_tga_accept_c(
    gnode branch, thm source, thm phase_shape) {
  thm_list rules = THM_LIST(
      phase_shape, cm_phase_frame_def, get_cm_capply_def(),
      cm_task_tagged_valid_cond, cm_task_tagged_valid_def,
      get_theorem_by_name("COND_ID"));
  thm normalized = conv_rule(reduce_rewrite_conv(rules), source);
  thm target_view = apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(branch->g));
  ACCEPT_TAC(branch, eq_mp_rule(sym_rule(target_view), normalized));
}

PROOF static thm cm_prove_tagged_span_capply_phase(void) {
  term phase = `phase:cm_aphase`;
  term ann = cm_tga_annotation(phase);
  term body = imp_chain(TERM_LIST(
      `cm_runtime_core (p:cm_program) (fid:int)
        (st:cm_src_state) ${ann:cm_annotation}`,
      `cm_tagged_span_valid (st:cm_src_state)`),
      `cm_task_tagged_valid
        (cm_capply (p:cm_program) (fid:int)
          (cm_phase_frame ${phase:cm_aphase}) (ctl:cm_control)
          (st:cm_src_state) (cm_cursor_frames (rest:(cm_acursor)list)))`);
  gnode root_node = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root_node);
  thm core = assume_rule(
      `cm_runtime_core (p:cm_program) (fid:int)
        (st:cm_src_state) ${ann:cm_annotation}`);
  thm old_valid = assume_rule(
      `cm_tagged_span_valid (st:cm_src_state)`);
  gnode_list cases = DISJ_CASES_TAC(
      introduced,
      ispec_rule(phase, get_datatype_cases("cm_aphase")),
      "Hphase");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cm_tga_open_shape(cases[i], "Hphase");
    thm phase_shape = cm_tga_shape(branch, "Hphase");
    term concrete_phase = rhs_of(phase_shape);
    term concrete_ann = cm_tga_annotation(concrete_phase);
    thm concrete_core = conv_rule(
        rewrite_conv(THM_LIST(phase_shape)), core);
    if (i == 15 || i == 19) {
      size_t phase_arity = i == 15 ? 4 : 6;
      size_t env_index = i == 15 ? 0 : 2;
      size_t regions_index = i == 15 ? 1 : 3;
      term oldenv = cm_tga_phase_arg(
          concrete_phase, phase_arity, env_index);
      term oldregions = cm_tga_phase_arg(
          concrete_phase, phase_arity, regions_index);
      thm prefix = cm_tga_scope_prefix(
          concrete_phase, concrete_ann, concrete_core);
      thm oldregions_eq = apply_conversion(
          reduce_rewrite_conv(THM_LIST(cm_phase_oldregions_def)),
          `cm_phase_oldregions ${concrete_phase:cm_aphase}`);
      prefix = conv_rule(rewrite_conv(THM_LIST(oldregions_eq)), prefix);
      thm restored = specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`,
          `cm_state_fp (st:cm_src_state)`, `st:cm_src_state`,
          oldenv, oldregions), cm_tagged_span_restore_scope);
      restored = match_mp_rule(restored, prefix);
      restored = match_mp_rule(restored, old_valid);
      cm_tga_accept_c(branch, restored, phase_shape);
    } else if (i == 22) {
      term oldenv = cm_tga_phase_arg(concrete_phase, 5, 1);
      term oldfp = cm_tga_phase_arg(concrete_phase, 5, 2);
      term oldregions = cm_tga_phase_arg(concrete_phase, 5, 3);
      thm prefix = cm_tga_scope_prefix(
          concrete_phase, concrete_ann, concrete_core);
      thm oldregions_eq = apply_conversion(
          reduce_rewrite_conv(THM_LIST(cm_phase_oldregions_def)),
          `cm_phase_oldregions ${concrete_phase:cm_aphase}`);
      prefix = conv_rule(rewrite_conv(THM_LIST(oldregions_eq)), prefix);
      thm restored = specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`,
          `cm_state_fp (st:cm_src_state)`, `st:cm_src_state`,
          oldenv, oldfp, oldregions), cm_tagged_span_restore_call);
      restored = match_mp_rule(restored, prefix);
      restored = match_mp_rule(restored, old_valid);
      cm_tga_accept_c(branch, restored, phase_shape);
    } else {
      cm_tga_accept_c(branch, old_valid, phase_shape);
    }
  }
  return gnode_prove(root_node);
}
PROOF thm cm_tagged_span_capply_phase =
    cm_prove_tagged_span_capply_phase();

PROOF static thm cm_prove_tagged_span_vstep(void) {
  gnode root_node = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (v:cm_value)
         (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         cm_typed_program p ==>
         cm_state_generation_below p fid st ==>
         cm_annotation_erases (CMVTask p fid v st ks) ann ==>
         cm_runtime_core p fid st ann ==>
         cm_task_tagged_valid (CMVTask p fid v st ks) ==>
         cm_task_tagged_valid (cm_step (CMVTask p fid v st ks))`);
  gnode introduced = AUTO_INTROS_TAC(root_node);
  thm old_valid = conv_rule(rewrite_conv(THM_LIST(
      cm_task_tagged_valid_def)), assume_rule(
        `cm_task_tagged_valid
          (CMVTask (p:cm_program) (fid:int) (v:cm_value)
            (st:cm_src_state) (ks:(cm_frame)list))`));
  gnode_list stack_cases = DISJ_CASES_TAC(
      introduced,
      ispec_rule(`ks:(cm_frame)list`,
        get_theorem_by_name("list_CASES")),
      "Hstack");
  {
    thm stack_nil = cm_tga_shape(stack_cases[0], "Hstack");
    thm result = conv_rule(reduce_rewrite_conv(THM_LIST(
        stack_nil, get_cm_step_def(), cm_task_tagged_valid_def)),
        old_valid);
    thm target_view = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          stack_nil, get_cm_step_def(), cm_task_tagged_valid_def)),
        goal_ccl(stack_cases[0]->g));
    ACCEPT_TAC(stack_cases[0],
        eq_mp_rule(sym_rule(target_view), result));
  }
  gnode stack_cons = ASMP_EXISTS_TAC(
      stack_cases[1], "Hstack", NULL);
  stack_cons = ASMP_EXISTS_TAC(stack_cons, "Hstack", NULL);
  thm stack_shape = cm_tga_shape(stack_cons, "Hstack");
  gnode_list ann_cases = DISJ_CASES_TAC(
      stack_cons,
      ispec_rule(`ann:cm_annotation`,
        get_datatype_cases("cm_annotation")),
      "Hann");
  gnode ann_branch = cm_tga_open_shape(ann_cases[0], "Hann");
  thm ann_shape = cm_tga_shape(ann_branch, "Hann");
  term cursors = cm_tga_app_arg_from_right(rhs_of(ann_shape), 3);
  gnode_list cursor_list_cases = DISJ_CASES_TAC(
      ann_branch,
      ispec_rule(cursors, get_theorem_by_name("list_CASES")),
      "Hcursors");
  {
    thm cursors_nil = cm_tga_shape(
        cursor_list_cases[0], "Hcursors");
    thm erases = conv_rule(reduce_rewrite_conv(THM_LIST(
        ann_shape, cursors_nil, stack_shape,
        cm_annotation_erases_def, cm_ann_cursors_def,
        cm_cursor_frames_def)), assume_rule(
          `cm_annotation_erases
            (CMVTask (p:cm_program) (fid:int) (v:cm_value)
              (st:cm_src_state) (ks:(cm_frame)list))
            (ann:cm_annotation)`));
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("NOT_CONS_NIL"))), sym_rule(erases));
    CONTR_TAC(cursor_list_cases[0], impossible);
  }
  gnode cursor_cons = ASMP_EXISTS_TAC(
      cursor_list_cases[1], "Hcursors", NULL);
  cursor_cons = ASMP_EXISTS_TAC(
      cursor_cons, "Hcursors", NULL);
  thm cursors_shape = cm_tga_shape(cursor_cons, "Hcursors");
  term cursor =
      cm_tga_app_arg_from_right(rhs_of(cursors_shape), 1);
  gnode_list cursor_cases = DISJ_CASES_TAC(
      cursor_cons,
      ispec_rule(cursor, get_datatype_cases("cm_acursor")),
      "Hcursor");
  gnode cursor_branch = cm_tga_open_shape(
      cursor_cases[0], "Hcursor");
  thm cursor_shape = cm_tga_shape(cursor_branch, "Hcursor");
  thm full_ann_shape = conv_rule(rewrite_conv(THM_LIST(
      cursors_shape, cursor_shape)), ann_shape);
  term shaped_ann = rhs_of(full_ann_shape);
  term pc = cm_tga_phase_arg(shaped_ann, 8, 0);
  term temp = cm_tga_phase_arg(shaped_ann, 8, 1);
  term breakpc = cm_tga_phase_arg(shaped_ann, 8, 2);
  term continuepc = cm_tga_phase_arg(shaped_ann, 8, 3);
  term spills = cm_tga_phase_arg(shaped_ann, 8, 5);
  term saved = cm_tga_phase_arg(shaped_ann, 8, 6);
  term calls = cm_tga_phase_arg(shaped_ann, 8, 7);
  term shaped_cursor = rhs_of(cursor_shape);
  term phase = cm_tga_phase_arg(shaped_cursor, 4, 0);
  term owner = cm_tga_phase_arg(shaped_cursor, 4, 1);
  term saved_break = cm_tga_phase_arg(shaped_cursor, 4, 2);
  term saved_continue = cm_tga_phase_arg(shaped_cursor, 4, 3);
  term cursor_rest =
      cm_tga_app_arg_from_right(rhs_of(cursors_shape), 0);
  thm frames_equal = conv_rule(reduce_rewrite_conv(THM_LIST(
      full_ann_shape, stack_shape, cm_annotation_erases_def,
      cm_ann_cursors_def, cm_cursor_frames_def,
      cm_cursor_phase_def)), assume_rule(
        `cm_annotation_erases
          (CMVTask (p:cm_program) (fid:int) (v:cm_value)
            (st:cm_src_state) (ks:(cm_frame)list))
          (ann:cm_annotation)`));
  thm frame_equal = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_theorem_by_name("HD"))), beta_norm(ap_term_rule(
        `\xs:(cm_frame)list. HD xs`, frames_equal)));
  thm tail_equal = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_theorem_by_name("TL"))), beta_norm(ap_term_rule(
        `\xs:(cm_frame)list. TL xs`, frames_equal)));
  thm result = specl_rule(TERM_LIST(
      pc, temp, breakpc, continuepc, owner, saved_break,
      saved_continue, spills, saved, calls,
      `p:cm_program`, `fid:int`, phase, `v:cm_value`,
      `st:cm_src_state`, cursor_rest),
      cm_tagged_span_vapply_phase);
  result = match_mp_rule(result, assume_rule(
      `cm_typed_program (p:cm_program)`));
  result = match_mp_rule(result, assume_rule(
      `cm_state_generation_below (p:cm_program) (fid:int)
        (st:cm_src_state)`));
  result = match_mp_rule(result, conv_rule(
      rewrite_conv(THM_LIST(full_ann_shape)), assume_rule(
        `cm_runtime_core (p:cm_program) (fid:int)
          (st:cm_src_state) (ann:cm_annotation)`)));
  result = match_mp_rule(result, old_valid);
  result = conv_rule(rewrite_conv(THM_LIST(
      frame_equal, tail_equal)), result);
  thm target_view = apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        stack_shape, get_cm_step_def(),
        get_theorem_by_name("HD"), get_theorem_by_name("TL"),
        get_theorem_by_name("NOT_CONS_NIL"))),
      goal_ccl(cursor_branch->g));
  ACCEPT_TAC(cursor_branch,
      eq_mp_rule(sym_rule(target_view), result));
  return gnode_prove(root_node);
}
PROOF thm cm_tagged_span_vstep =
    cm_prove_tagged_span_vstep();

PROOF static thm cm_prove_tagged_span_cstep(void) {
  gnode root_node = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (ctl:cm_control)
         (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         cm_annotation_erases (CMCTask p fid ctl st ks) ann ==>
         cm_runtime_core p fid st ann ==>
         cm_task_tagged_valid (CMCTask p fid ctl st ks) ==>
         cm_task_tagged_valid (cm_step (CMCTask p fid ctl st ks))`);
  gnode introduced = AUTO_INTROS_TAC(root_node);
  thm old_valid = conv_rule(rewrite_conv(THM_LIST(
      cm_task_tagged_valid_def)), assume_rule(
        `cm_task_tagged_valid
          (CMCTask (p:cm_program) (fid:int) (ctl:cm_control)
            (st:cm_src_state) (ks:(cm_frame)list))`));
  thm conditional = ispecl_rule(TERM_LIST(
      `condition:bool`, `cm_task_tagged_valid`,
      `yes_task:cm_task`, `no_task:cm_task`),
      get_theorem_by_name("COND_RAND"));
  gnode_list stack_cases = DISJ_CASES_TAC(
      introduced,
      ispec_rule(`ks:(cm_frame)list`,
        get_theorem_by_name("list_CASES")),
      "Hstack");
  {
    thm stack_nil = cm_tga_shape(stack_cases[0], "Hstack");
    thm result = conv_rule(reduce_rewrite_conv(THM_LIST(
        stack_nil, get_cm_step_def(), cm_task_tagged_valid_def)),
        old_valid);
    thm target_view = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          stack_nil, get_cm_step_def(), cm_task_tagged_valid_def,
          conditional, get_theorem_by_name("COND_ID"))),
        goal_ccl(stack_cases[0]->g));
    ACCEPT_TAC(stack_cases[0],
        eq_mp_rule(sym_rule(target_view), result));
  }
  gnode stack_cons = ASMP_EXISTS_TAC(
      stack_cases[1], "Hstack", NULL);
  stack_cons = ASMP_EXISTS_TAC(stack_cons, "Hstack", NULL);
  thm stack_shape = cm_tga_shape(stack_cons, "Hstack");
  gnode_list ann_cases = DISJ_CASES_TAC(
      stack_cons,
      ispec_rule(`ann:cm_annotation`,
        get_datatype_cases("cm_annotation")),
      "Hann");
  gnode ann_branch = cm_tga_open_shape(ann_cases[0], "Hann");
  thm ann_shape = cm_tga_shape(ann_branch, "Hann");
  term cursors = cm_tga_app_arg_from_right(rhs_of(ann_shape), 3);
  gnode_list cursor_list_cases = DISJ_CASES_TAC(
      ann_branch,
      ispec_rule(cursors, get_theorem_by_name("list_CASES")),
      "Hcursors");
  {
    thm cursors_nil = cm_tga_shape(
        cursor_list_cases[0], "Hcursors");
    thm erases = conv_rule(reduce_rewrite_conv(THM_LIST(
        ann_shape, cursors_nil, stack_shape,
        cm_annotation_erases_def, cm_ann_cursors_def,
        cm_cursor_frames_def)), assume_rule(
          `cm_annotation_erases
            (CMCTask (p:cm_program) (fid:int) (ctl:cm_control)
              (st:cm_src_state) (ks:(cm_frame)list))
            (ann:cm_annotation)`));
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("NOT_CONS_NIL"))), sym_rule(erases));
    CONTR_TAC(cursor_list_cases[0], impossible);
  }
  gnode cursor_cons = ASMP_EXISTS_TAC(
      cursor_list_cases[1], "Hcursors", NULL);
  cursor_cons = ASMP_EXISTS_TAC(
      cursor_cons, "Hcursors", NULL);
  thm cursors_shape = cm_tga_shape(cursor_cons, "Hcursors");
  term cursor =
      cm_tga_app_arg_from_right(rhs_of(cursors_shape), 1);
  gnode_list cursor_cases = DISJ_CASES_TAC(
      cursor_cons,
      ispec_rule(cursor, get_datatype_cases("cm_acursor")),
      "Hcursor");
  gnode cursor_branch = cm_tga_open_shape(
      cursor_cases[0], "Hcursor");
  thm cursor_shape = cm_tga_shape(cursor_branch, "Hcursor");
  thm full_ann_shape = conv_rule(rewrite_conv(THM_LIST(
      cursors_shape, cursor_shape)), ann_shape);
  term shaped_ann = rhs_of(full_ann_shape);
  term pc = cm_tga_phase_arg(shaped_ann, 8, 0);
  term temp = cm_tga_phase_arg(shaped_ann, 8, 1);
  term breakpc = cm_tga_phase_arg(shaped_ann, 8, 2);
  term continuepc = cm_tga_phase_arg(shaped_ann, 8, 3);
  term spills = cm_tga_phase_arg(shaped_ann, 8, 5);
  term saved = cm_tga_phase_arg(shaped_ann, 8, 6);
  term calls = cm_tga_phase_arg(shaped_ann, 8, 7);
  term shaped_cursor = rhs_of(cursor_shape);
  term phase = cm_tga_phase_arg(shaped_cursor, 4, 0);
  term owner = cm_tga_phase_arg(shaped_cursor, 4, 1);
  term saved_break = cm_tga_phase_arg(shaped_cursor, 4, 2);
  term saved_continue = cm_tga_phase_arg(shaped_cursor, 4, 3);
  term cursor_rest =
      cm_tga_app_arg_from_right(rhs_of(cursors_shape), 0);
  thm frames_equal = conv_rule(reduce_rewrite_conv(THM_LIST(
      full_ann_shape, stack_shape, cm_annotation_erases_def,
      cm_ann_cursors_def, cm_cursor_frames_def,
      cm_cursor_phase_def)), assume_rule(
        `cm_annotation_erases
          (CMCTask (p:cm_program) (fid:int) (ctl:cm_control)
            (st:cm_src_state) (ks:(cm_frame)list))
          (ann:cm_annotation)`));
  thm frame_equal = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_theorem_by_name("HD"))), beta_norm(ap_term_rule(
        `\xs:(cm_frame)list. HD xs`, frames_equal)));
  thm tail_equal = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_theorem_by_name("TL"))), beta_norm(ap_term_rule(
        `\xs:(cm_frame)list. TL xs`, frames_equal)));
  thm result = specl_rule(TERM_LIST(
      pc, temp, breakpc, continuepc, owner, saved_break,
      saved_continue, spills, saved, calls,
      `p:cm_program`, `fid:int`, phase, `ctl:cm_control`,
      `st:cm_src_state`, cursor_rest),
      cm_tagged_span_capply_phase);
  result = match_mp_rule(result, conv_rule(
      rewrite_conv(THM_LIST(full_ann_shape)), assume_rule(
        `cm_runtime_core (p:cm_program) (fid:int)
          (st:cm_src_state) (ann:cm_annotation)`)));
  result = match_mp_rule(result, old_valid);
  result = conv_rule(rewrite_conv(THM_LIST(
      frame_equal, tail_equal)), result);
  thm target_view = apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        stack_shape, get_cm_step_def(), cm_task_tagged_valid_def,
        conditional, old_valid, result, get_theorem_by_name("COND_ID"),
        get_theorem_by_name("HD"), get_theorem_by_name("TL"),
        get_theorem_by_name("NOT_CONS_NIL"))),
      goal_ccl(cursor_branch->g));
  ACCEPT_TAC(cursor_branch, eqt_elim_rule(target_view));
  return gnode_prove(root_node);
}
PROOF thm cm_tagged_span_cstep =
    cm_prove_tagged_span_cstep();

PROOF static int cmc_preservation_tagged_apply_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_tagged_apply_axioms_before,
      "cmc_preservation_tagged_apply introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_tagged_span_vapply_phase)) == 0,
      "vapply tagged-span theorem is not closed");
  ENSURE_COND(vector_size(hyp(cm_tagged_span_capply_phase)) == 0,
      "capply tagged-span theorem is not closed");
  ENSURE_COND(vector_size(hyp(cm_tagged_span_vstep)) == 0,
      "value-step tagged-span theorem is not closed");
  ENSURE_COND(vector_size(hyp(cm_tagged_span_cstep)) == 0,
      "control-step tagged-span theorem is not closed");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_tagged_apply_checks =
    cmc_preservation_tagged_apply_final_checks();
