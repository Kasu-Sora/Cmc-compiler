#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_invariant_transition.h"

#require "cmc_preservation_invariant_runtime.c"
#require "cmc_preservation_source.c"

PROOF static size_t _cmc_preservation_invariant_transition_axioms_before =
    vector_size(get_all_axioms());

PROOF thm cm_runtime_core_def = new_fun_definition(
    `cm_runtime_core (p:cm_program) (fid:int)
       (st:cm_src_state) (ann:cm_annotation) : bool =
       (cm_regions_before
          (cm_state_regions st) (cm_state_nextgen st) &&
        cm_runtime_stack p (cm_state_regions st) fid
          (cm_state_fp st) (cm_state_regions st)
          (cm_ann_cursors ann) (cm_ann_spills ann)
          (cm_ann_saved ann) (cm_ann_calls ann))`);
PROOF static int _c_cm_runtime_core =
    cst_add_const_to_header(`cm_runtime_core`);

PROOF static thm cm_prove_runtime_core_fields(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (ann:cm_annotation) (st2:cm_src_state)
         (ann2:cm_annotation).
         cm_runtime_core p fid st ann ==>
         cm_state_fp st2 == cm_state_fp st ==>
         cm_state_nextgen st2 == cm_state_nextgen st ==>
         cm_state_regions st2 == cm_state_regions st ==>
         cm_ann_cursors ann2 == cm_ann_cursors ann ==>
         cm_ann_spills ann2 == cm_ann_spills ann ==>
         cm_ann_saved ann2 == cm_ann_saved ann ==>
         cm_ann_calls ann2 == cm_ann_calls ann ==>
         cm_runtime_core p fid st2 ann2`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm core = conv_rule(rewrite_conv(THM_LIST(
      cm_runtime_core_def)), assume_rule(
        `cm_runtime_core (p:cm_program) (fid:int)
          (st:cm_src_state) (ann:cm_annotation)`));
  gnode reduced = CONV_WITH_ASMP_TAC(
      leaf, reduce_rewrite_conv, THM_LIST(cm_runtime_core_def));
  if (IS_NULL(reduced->solved)) {
    ACCEPT_TAC(reduced, core);
  }
  return gnode_prove(root);
}
PROOF thm cm_runtime_core_fields =
    cm_prove_runtime_core_fields();

PROOF static thm cm_prove_runtime_core_plain(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (ann:cm_annotation) (pc:int) (temp:int)
         (breakpc:int) (continuepc:int).
         cm_runtime_core p fid st ann ==>
         cm_runtime_core p fid st
           (cm_ann_plain pc temp breakpc continuepc ann)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `ann:cm_annotation`, `st:cm_src_state`,
      `cm_ann_plain (pc:int) (temp:int) (breakpc:int)
         (continuepc:int) ann`), cm_runtime_core_fields);
  result = match_mp_rule(result,
      assume_rule(`cm_runtime_core (p:cm_program) (fid:int)
        (st:cm_src_state) (ann:cm_annotation)`));
  thm_list rules = THM_LIST(
      cm_ann_plain_def, cm_ann_cursors_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_ann_calls_def);
  for (size_t i = 0; i < 7; ++i) {
    result = match_mp_rule(result, eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(rules), dest_imp(concl(result)).tm1)));
  }
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_runtime_core_plain =
    cm_prove_runtime_core_plain();

PROOF static thm_list cm_runtime_core_rules(void) {
  return THM_LIST(
      cm_runtime_core_def,
      cm_ann_plain_def, cm_ann_linear_def,
      cm_ann_push_def, cm_ann_replace_def, cm_ann_pop_def,
      cm_ann_spills_set_def, cm_ann_put_spill_def,
      cm_ann_enter_call_def, cm_ann_leave_call_def,
      cm_ann_cursors_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_ann_calls_def,
      cm_cursor_phase_def, cm_cursor_temp_def,
      cm_cursor_break_def, cm_cursor_continue_def,
      cm_spill_frame_fid_def, cm_spill_frame_fp_def,
      cm_spill_frame_spills_def,
      cm_call_sim_base_def, cm_call_sim_saved_def,
      cm_call_sim_return_def,
      get_theorem_by_name("HD"), get_theorem_by_name("TL"));
}

PROOF static thm cm_close_runtime_core(
    term target, thm body, thm_list extra) {
  thm_list rules = cm_runtime_core_rules();
  for (size_t i = 0; i < vector_size(extra); ++i) {
    vector_add(&rules, extra[i]);
  }
  thm opened = apply_conversion(
      reduce_rewrite_conv(rules), target);
  return eq_mp_rule(sym_rule(opened), body);
}

PROOF static thm cm_open_runtime_core(thm core) {
  return conv_rule(rewrite_conv(
      THM_LIST(cm_runtime_core_def)), core);
}

PROOF static thm cm_prove_runtime_core_linear(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (ann:cm_annotation) (code:(tvm_inst)list).
         cm_runtime_core p fid st ann ==>
         cm_runtime_core p fid st (cm_ann_linear code ann)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm result = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `ann:cm_annotation`,
      `cm_ann_pc (ann:cm_annotation) +
        ilength (code:(tvm_inst)list)`,
      `cm_ann_temp (ann:cm_annotation)`,
      `cm_ann_break (ann:cm_annotation)`,
      `cm_ann_continue (ann:cm_annotation)`),
      cm_runtime_core_plain), assume_rule(
        `cm_runtime_core (p:cm_program) (fid:int)
          (st:cm_src_state) (ann:cm_annotation)`));
  thm opened = apply_conversion(rewrite_conv(
      THM_LIST(cm_ann_linear_def)),
      `cm_runtime_core (p:cm_program) (fid:int)
        (st:cm_src_state)
        (cm_ann_linear (code:(tvm_inst)list)
          (ann:cm_annotation))`);
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(opened), result));
  return gnode_prove(root);
}
PROOF thm cm_runtime_core_linear =
    cm_prove_runtime_core_linear();

PROOF static thm cm_prove_runtime_core_push_plain(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (ann:cm_annotation) (phase:cm_aphase) (pc:int)
         (temp:int) (breakpc:int) (continuepc:int).
         ~cm_phase_is_call phase ==>
         ~cm_phase_is_scope phase ==>
         ~cm_phase_is_halt phase ==>
         cm_runtime_core p fid st ann ==>
         cm_runtime_core p fid st
           (cm_ann_push phase pc temp breakpc continuepc ann)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm opened = cm_open_runtime_core(assume_rule(
      `cm_runtime_core (p:cm_program) (fid:int)
        (st:cm_src_state) (ann:cm_annotation)`));
  thm pushed = match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `cm_state_regions (st:cm_src_state)`,
        `fid:int`, `cm_state_fp (st:cm_src_state)`,
        `phase:cm_aphase`,
        `cm_ann_temp (ann:cm_annotation)`,
        `cm_ann_break (ann:cm_annotation)`,
        `cm_ann_continue (ann:cm_annotation)`,
        `cm_ann_cursors (ann:cm_annotation)`,
        `cm_ann_spills (ann:cm_annotation)`,
        `cm_ann_saved (ann:cm_annotation)`,
        `cm_ann_calls (ann:cm_annotation)`),
        cm_runtime_stack_plain_push),
      assume_rule(`~cm_phase_is_call (phase:cm_aphase)`)),
      assume_rule(`~cm_phase_is_scope (phase:cm_aphase)`)),
      assume_rule(`~cm_phase_is_halt (phase:cm_aphase)`)),
      conjunct2_rule(opened));
  thm result = cm_close_runtime_core(
      `cm_runtime_core (p:cm_program) (fid:int)
        (st:cm_src_state)
        (cm_ann_push (phase:cm_aphase) (pc:int) (temp:int)
          (breakpc:int) (continuepc:int) (ann:cm_annotation))`,
      conj_rule(conjunct1_rule(opened), pushed), THM_LIST());
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_runtime_core_push_plain =
    cm_prove_runtime_core_push_plain();

PROOF static thm cm_prove_runtime_core_pop_plain(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (ann:cm_annotation) (phase:cm_aphase)
         (owner:int) (owner_break:int) (owner_continue:int)
         (rest:(cm_acursor)list) (pc:int).
         cm_ann_cursors ann ==
           CMACursor phase owner owner_break owner_continue :: rest ==>
         ~cm_phase_is_call phase ==>
         ~cm_phase_is_scope phase ==>
         ~cm_phase_is_halt phase ==>
         cm_runtime_core p fid st ann ==>
         cm_runtime_core p fid st (cm_ann_pop pc ann)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm cursor_eq = assume_rule(
      `cm_ann_cursors (ann:cm_annotation) ==
       CMACursor (phase:cm_aphase) (owner:int)
         (owner_break:int) (owner_continue:int) ::
       (rest:(cm_acursor)list)`);
  thm opened = cm_open_runtime_core(assume_rule(
      `cm_runtime_core (p:cm_program) (fid:int)
        (st:cm_src_state) (ann:cm_annotation)`));
  thm shaped_stack = conv_rule(
      rewrite_conv(THM_LIST(cursor_eq)), conjunct2_rule(opened));
  thm popped = match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `cm_state_regions (st:cm_src_state)`,
        `fid:int`, `cm_state_fp (st:cm_src_state)`,
        `phase:cm_aphase`, `owner:int`,
        `owner_break:int`, `owner_continue:int`,
        `rest:(cm_acursor)list`,
        `cm_ann_spills (ann:cm_annotation)`,
        `cm_ann_saved (ann:cm_annotation)`,
        `cm_ann_calls (ann:cm_annotation)`),
        cm_runtime_stack_plain_pop),
      assume_rule(`~cm_phase_is_call (phase:cm_aphase)`)),
      assume_rule(`~cm_phase_is_scope (phase:cm_aphase)`)),
      assume_rule(`~cm_phase_is_halt (phase:cm_aphase)`)),
      shaped_stack);
  thm result = cm_close_runtime_core(
      `cm_runtime_core (p:cm_program) (fid:int)
        (st:cm_src_state)
        (cm_ann_pop (pc:int) (ann:cm_annotation))`,
      conj_rule(conjunct1_rule(opened), popped),
      THM_LIST(cursor_eq));
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_runtime_core_pop_plain =
    cm_prove_runtime_core_pop_plain();

PROOF static thm cm_prove_runtime_core_replace_plain(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (ann:cm_annotation) (oldphase:cm_aphase)
         (newphase:cm_aphase) (owner:int) (owner_break:int)
         (owner_continue:int) (rest:(cm_acursor)list)
         (pc:int) (temp:int) (breakpc:int) (continuepc:int).
         cm_ann_cursors ann ==
           CMACursor oldphase owner owner_break owner_continue :: rest ==>
         ~cm_phase_is_call oldphase ==>
         ~cm_phase_is_scope oldphase ==>
         ~cm_phase_is_halt oldphase ==>
         ~cm_phase_is_call newphase ==>
         ~cm_phase_is_scope newphase ==>
         ~cm_phase_is_halt newphase ==>
         cm_runtime_core p fid st ann ==>
         cm_runtime_core p fid st
           (cm_ann_replace newphase pc temp breakpc continuepc ann)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm cursor_eq = assume_rule(
      `cm_ann_cursors (ann:cm_annotation) ==
       CMACursor (oldphase:cm_aphase) (owner:int)
         (owner_break:int) (owner_continue:int) ::
       (rest:(cm_acursor)list)`);
  thm opened = cm_open_runtime_core(assume_rule(
      `cm_runtime_core (p:cm_program) (fid:int)
        (st:cm_src_state) (ann:cm_annotation)`));
  thm shaped_stack = conv_rule(
      rewrite_conv(THM_LIST(cursor_eq)), conjunct2_rule(opened));
  thm replaced = specl_rule(TERM_LIST(
      `p:cm_program`, `cm_state_regions (st:cm_src_state)`,
      `fid:int`, `cm_state_fp (st:cm_src_state)`,
      `oldphase:cm_aphase`, `newphase:cm_aphase`,
      `owner:int`, `owner_break:int`, `owner_continue:int`,
      `owner:int`, `owner_break:int`, `owner_continue:int`,
      `rest:(cm_acursor)list`,
      `cm_ann_spills (ann:cm_annotation)`,
      `cm_ann_saved (ann:cm_annotation)`,
      `cm_ann_calls (ann:cm_annotation)`),
      cm_runtime_stack_plain_replace);
  thm_list premises = THM_LIST(
      assume_rule(`~cm_phase_is_call (oldphase:cm_aphase)`),
      assume_rule(`~cm_phase_is_scope (oldphase:cm_aphase)`),
      assume_rule(`~cm_phase_is_halt (oldphase:cm_aphase)`),
      assume_rule(`~cm_phase_is_call (newphase:cm_aphase)`),
      assume_rule(`~cm_phase_is_scope (newphase:cm_aphase)`),
      assume_rule(`~cm_phase_is_halt (newphase:cm_aphase)`),
      shaped_stack);
  for (size_t i = 0; i < vector_size(premises); ++i) {
    replaced = match_mp_rule(replaced, premises[i]);
  }
  thm result = cm_close_runtime_core(
      `cm_runtime_core (p:cm_program) (fid:int)
        (st:cm_src_state)
        (cm_ann_replace (newphase:cm_aphase) (pc:int)
          (temp:int) (breakpc:int) (continuepc:int)
          (ann:cm_annotation))`,
      conj_rule(conjunct1_rule(opened), replaced),
      THM_LIST(cursor_eq));
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_runtime_core_replace_plain =
    cm_prove_runtime_core_replace_plain();

PROOF static thm cm_prove_runtime_core_spill_put(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (ann:cm_annotation) (slot:int) (spill_value:cm_value).
         0i <= fid ==>
         0i <= slot ==>
         slot < cm_temp_slots
           (inth fid (cm_program_functions p)) ==>
         cm_runtime_core p fid st ann ==>
         cm_runtime_core p fid st
           (cm_ann_put_spill slot spill_value ann)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm opened = cm_open_runtime_core(assume_rule(
      `cm_runtime_core (p:cm_program) (fid:int)
        (st:cm_src_state) (ann:cm_annotation)`));
  thm slot_bound = conv_rule(rewrite_conv(THM_LIST(
      get_cm_temp_slots_def())), assume_rule(
        `(slot:int) <
         cm_temp_slots
           (inth (fid:int) (cm_program_functions (p:cm_program)))`));
  thm updated = match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `cm_state_regions (st:cm_src_state)`,
        `fid:int`, `cm_state_fp (st:cm_src_state)`,
        `cm_ann_cursors (ann:cm_annotation)`,
        `cm_state_regions (st:cm_src_state)`, `slot:int`,
        `spill_value:cm_value`, `cm_ann_spills (ann:cm_annotation)`,
        `cm_ann_saved (ann:cm_annotation)`,
        `cm_ann_calls (ann:cm_annotation)`),
        cm_runtime_stack_spill_put),
      assume_rule(`0i <= (fid:int)`)),
      assume_rule(`0i <= (slot:int)`)),
      slot_bound), conjunct2_rule(opened));
  thm result = cm_close_runtime_core(
      `cm_runtime_core (p:cm_program) (fid:int)
        (st:cm_src_state)
        (cm_ann_put_spill (slot:int) (spill_value:cm_value)
          (ann:cm_annotation))`,
      conj_rule(conjunct1_rule(opened), updated), THM_LIST());
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_runtime_core_spill_put =
    cm_prove_runtime_core_spill_put();
PROOF static thm cm_prove_runtime_core_activate_local(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (slot:int)
         (st:cm_src_state) (ann:cm_annotation).
         cm_function_wf p
           (inth fid (cm_program_functions p)) ==>
         0i <= fid ==>
         0i <= slot ==>
         slot < ilength
           (cm_function_locals
             (inth fid (cm_program_functions p))) ==>
         cm_runtime_core p fid st ann ==>
         cm_runtime_core p fid
           (cm_activate_local p fid slot st) ann`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm opened = cm_open_runtime_core(assume_rule(
      `cm_runtime_core (p:cm_program) (fid:int)
        (st:cm_src_state) (ann:cm_annotation)`));
  thm updated_stack = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `slot:int`, `st:cm_src_state`,
      `cm_ann_cursors (ann:cm_annotation)`,
      `cm_ann_spills (ann:cm_annotation)`,
      `cm_ann_saved (ann:cm_annotation)`,
      `cm_ann_calls (ann:cm_annotation)`),
      cm_runtime_stack_activate_local);
  thm_list stack_premises = THM_LIST(
      assume_rule(
        `cm_function_wf (p:cm_program)
          (inth (fid:int) (cm_program_functions p))`),
      assume_rule(`0i <= (fid:int)`),
      assume_rule(`0i <= (slot:int)`),
      assume_rule(
        `(slot:int) <
         ilength
           (cm_function_locals
             (inth fid (cm_program_functions (p:cm_program))))`),
      conjunct1_rule(opened), conjunct2_rule(opened));
  for (size_t i = 0; i < vector_size(stack_premises); ++i) {
    updated_stack =
        match_mp_rule(updated_stack, stack_premises[i]);
  }
  term fresh =
      `CMRegion (cm_state_nextgen (st:cm_src_state))
        (cm_local_base (p:cm_program) (fid:int) (slot:int)
          (cm_state_fp st)) 0i
        (cm_slot_size (cm_program_structs p)
          (inth slot (cm_function_locals
            (inth fid (cm_program_functions p))))) T T`;
  thm head_gen = apply_conversion(reduce_rewrite_conv(
      THM_LIST(get_cm_region_gen_def())),
      `cm_region_gen ${fresh:cm_region}`);
  thm head_bound = mp_rule(int_arith_rule(mk_imp(
      concl(head_gen),
      `cm_region_gen ${fresh:cm_region} <
       cm_state_nextgen (st:cm_src_state) + 1i`)), head_gen);
  thm tail_bound = match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `cm_state_regions (st:cm_src_state)`,
        `cm_state_nextgen (st:cm_src_state)`,
        `cm_state_nextgen (st:cm_src_state) + 1i`),
        cm_regions_before_mono),
      conjunct1_rule(opened)),
      int_arith_rule(
        `cm_state_nextgen (st:cm_src_state) <=
         cm_state_nextgen st + 1i`));
  thm updated_before = match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        fresh, `cm_state_regions (st:cm_src_state)`,
        `cm_state_nextgen (st:cm_src_state) + 1i`),
        cm_regions_before_cons), head_bound), tail_bound);
  thm structure = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `slot:int`,
      `st:cm_src_state`), cm_activate_local_structure);
  thm fp_structure = conjunct1_rule(structure);
  thm nextgen_structure =
      conjunct1_rule(conjunct2_rule(structure));
  thm regions_structure =
      conjunct2_rule(conjunct2_rule(structure));
  thm result = cm_close_runtime_core(
      `cm_runtime_core (p:cm_program) (fid:int)
        (cm_activate_local p fid (slot:int) (st:cm_src_state))
        (ann:cm_annotation)`,
      conj_rule(updated_before, updated_stack),
      THM_LIST(fp_structure, nextgen_structure, regions_structure));
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_runtime_core_activate_local =
    cm_prove_runtime_core_activate_local();

PROOF static thm cm_prove_runtime_core_enter_scope(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (ann:cm_annotation) (phase:cm_aphase) (pc:int)
         (temp:int) (breakpc:int) (continuepc:int).
         0i <= fid ==>
         cm_phase_is_scope phase ==>
         ~cm_phase_is_call phase ==>
         cm_phase_oldregions phase == cm_state_regions st ==>
         cm_runtime_core p fid st ann ==>
         cm_runtime_core p fid st
           (cm_ann_push phase pc temp breakpc continuepc ann)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm opened = cm_open_runtime_core(assume_rule(
      `cm_runtime_core (p:cm_program) (fid:int)
        (st:cm_src_state) (ann:cm_annotation)`));
  thm entered = match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `cm_state_regions (st:cm_src_state)`,
        `fid:int`, `cm_state_fp (st:cm_src_state)`,
        `phase:cm_aphase`,
        `cm_ann_temp (ann:cm_annotation)`,
        `cm_ann_break (ann:cm_annotation)`,
        `cm_ann_continue (ann:cm_annotation)`,
        `cm_ann_cursors (ann:cm_annotation)`,
        `cm_ann_spills (ann:cm_annotation)`,
        `cm_ann_saved (ann:cm_annotation)`,
        `cm_ann_calls (ann:cm_annotation)`),
        cm_runtime_stack_enter_scope),
      assume_rule(`0i <= (fid:int)`)),
      assume_rule(`cm_phase_is_scope (phase:cm_aphase)`)),
      assume_rule(`~cm_phase_is_call (phase:cm_aphase)`)),
      assume_rule(
        `cm_phase_oldregions (phase:cm_aphase) ==
         cm_state_regions (st:cm_src_state)`)),
      conjunct2_rule(opened));
  thm result = cm_close_runtime_core(
      `cm_runtime_core (p:cm_program) (fid:int)
        (st:cm_src_state)
        (cm_ann_push (phase:cm_aphase) (pc:int) (temp:int)
          (breakpc:int) (continuepc:int) (ann:cm_annotation))`,
      conj_rule(conjunct1_rule(opened), entered), THM_LIST());
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_runtime_core_enter_scope =
    cm_prove_runtime_core_enter_scope();
PROOF static thm cm_prove_runtime_core_leave_scope(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (ann:cm_annotation) (phase:cm_aphase)
         (oldenv:int->int->cm_value)
         (oldregions:(cm_region)list)
         (owner:int) (owner_break:int) (owner_continue:int)
         (rest:(cm_acursor)list) (pc:int).
         cm_ann_cursors ann ==
           CMACursor phase owner owner_break owner_continue :: rest ==>
         cm_phase_is_scope phase ==>
         ~cm_phase_is_call phase ==>
         cm_phase_oldregions phase == oldregions ==>
         cm_runtime_core p fid st ann ==>
         cm_runtime_core p fid
           (cm_restore_scope st oldenv oldregions)
           (cm_ann_pop pc ann)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm cursor_eq = assume_rule(
      `cm_ann_cursors (ann:cm_annotation) ==
       CMACursor (phase:cm_aphase) (owner:int)
         (owner_break:int) (owner_continue:int) ::
       (rest:(cm_acursor)list)`);
  thm scope = assume_rule(
      `cm_phase_is_scope (phase:cm_aphase)`);
  thm not_call = assume_rule(
      `~cm_phase_is_call (phase:cm_aphase)`);
  thm oldregions_eq = assume_rule(
      `cm_phase_oldregions (phase:cm_aphase) ==
       (oldregions:(cm_region)list)`);
  thm opened = cm_open_runtime_core(assume_rule(
      `cm_runtime_core (p:cm_program) (fid:int)
        (st:cm_src_state) (ann:cm_annotation)`));
  thm shaped_stack = conv_rule(
      rewrite_conv(THM_LIST(cursor_eq)), conjunct2_rule(opened));
  thm stack_body = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_runtime_stack_def, cm_cursor_phase_def,
      not_call, scope, oldregions_eq)),
      shaped_stack);
  thm prefix = conjunct1_rule(conjunct2_rule(stack_body));
  thm restored_before = match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `cm_state_regions (st:cm_src_state)`,
        `fid:int`, `cm_state_fp (st:cm_src_state)`,
        `cm_state_regions (st:cm_src_state)`,
        `oldregions:(cm_region)list`,
        `cm_state_nextgen (st:cm_src_state)`),
        cm_restore_regions_before),
      prefix), conjunct1_rule(opened));
  thm restored_stack = match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `cm_state_regions (st:cm_src_state)`,
        `fid:int`, `cm_state_fp (st:cm_src_state)`,
        `phase:cm_aphase`, `oldregions:(cm_region)list`,
        `owner:int`, `owner_break:int`, `owner_continue:int`,
        `rest:(cm_acursor)list`,
        `cm_ann_spills (ann:cm_annotation)`,
        `cm_ann_saved (ann:cm_annotation)`,
        `cm_ann_calls (ann:cm_annotation)`),
        cm_runtime_stack_leave_scope),
      scope), not_call), oldregions_eq), shaped_stack);
  thm structure = specl_rule(TERM_LIST(
      `st:cm_src_state`, `oldenv:int->int->cm_value`,
      `oldregions:(cm_region)list`),
      cm_restore_scope_structure);
  thm fp_structure = conjunct1_rule(structure);
  thm nextgen_structure =
      conjunct1_rule(conjunct2_rule(structure));
  thm regions_structure =
      conjunct2_rule(conjunct2_rule(structure));
  thm result = cm_close_runtime_core(
      `cm_runtime_core (p:cm_program) (fid:int)
        (cm_restore_scope (st:cm_src_state)
          (oldenv:int->int->cm_value)
          (oldregions:(cm_region)list))
        (cm_ann_pop (pc:int) (ann:cm_annotation))`,
      conj_rule(restored_before, restored_stack),
      THM_LIST(cursor_eq, fp_structure,
        nextgen_structure, regions_structure));
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_runtime_core_leave_scope =
    cm_prove_runtime_core_leave_scope();
PROOF static thm cm_prove_runtime_core_enter_call(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (caller:int) (callee:int)
         (values:(cm_value)list) (st:cm_src_state)
         (ret:cm_type) (returnpc:int) (parent_temp:int)
         (parent_break:int) (parent_continue:int)
         (ann:cm_annotation).
         cm_typed_program p ==>
         cm_call_ok p callee values st ==>
         cm_runtime_core p caller st ann ==>
         cm_runtime_core p callee
           (cm_enter_call p callee values st)
           (cm_ann_enter_call p caller callee st ret returnpc
             parent_temp parent_break parent_continue
             (cm_ann_cursors ann) (cm_ann_spills ann)
             (cm_ann_saved ann) (cm_ann_calls ann))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm typed = assume_rule(
      `cm_typed_program (p:cm_program)`);
  thm call_ok = assume_rule(
      `cm_call_ok (p:cm_program) (callee:int)
        (values:(cm_value)list) (st:cm_src_state)`);
  thm opened = cm_open_runtime_core(assume_rule(
      `cm_runtime_core (p:cm_program) (caller:int)
        (st:cm_src_state) (ann:cm_annotation)`));
  thm entered_stack = match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `caller:int`, `callee:int`,
        `values:(cm_value)list`, `st:cm_src_state`,
        `ret:cm_type`, `returnpc:int`, `parent_temp:int`,
        `parent_break:int`, `parent_continue:int`,
        `cm_ann_cursors (ann:cm_annotation)`,
        `cm_ann_spills (ann:cm_annotation)`,
        `cm_ann_saved (ann:cm_annotation)`,
        `cm_ann_calls (ann:cm_annotation)`),
        cm_runtime_stack_enter_call),
      typed), call_ok), conjunct1_rule(opened)),
      conjunct2_rule(opened));
  thm entered_before = match_mp_rule(specl_rule(TERM_LIST(
      `cm_program_structs (p:cm_program)`,
      `cm_function_params
        (inth (callee:int) (cm_program_functions p))`,
      `cm_state_nextgen (st:cm_src_state)`,
      `(cm_state_fp (st:cm_src_state) -
        cm_frame_size (cm_program_structs p)
          (inth callee (cm_program_functions p))) + 8i`,
      `cm_state_regions (st:cm_src_state)`),
      cm_regions_for_slots_append_before),
      conjunct1_rule(opened));
  thm structure = specl_rule(TERM_LIST(
      `p:cm_program`, `callee:int`, `values:(cm_value)list`,
      `st:cm_src_state`), cm_enter_call_structure);
  thm fp_structure = conjunct1_rule(structure);
  thm nextgen_structure =
      conjunct1_rule(conjunct2_rule(structure));
  thm regions_structure =
      conjunct2_rule(conjunct2_rule(structure));
  thm result = cm_close_runtime_core(
      `cm_runtime_core (p:cm_program) (callee:int)
        (cm_enter_call p callee (values:(cm_value)list)
          (st:cm_src_state))
        (cm_ann_enter_call p (caller:int) callee st
          (ret:cm_type) (returnpc:int) (parent_temp:int)
          (parent_break:int) (parent_continue:int)
          (cm_ann_cursors (ann:cm_annotation))
          (cm_ann_spills ann) (cm_ann_saved ann)
          (cm_ann_calls ann))`,
      conj_rule(entered_before, entered_stack),
      THM_LIST(fp_structure, nextgen_structure, regions_structure));
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_runtime_core_enter_call =
    cm_prove_runtime_core_enter_call();
PROOF static thm cm_prove_runtime_core_leave_call(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (caller:int)
         (st:cm_src_state) (ann:cm_annotation)
         (oldenv:int->int->cm_value) (oldfp:int)
         (oldregions:(cm_region)list) (ret:cm_type)
         (owner:int) (owner_break:int) (owner_continue:int)
         (rest:(cm_acursor)list)
         (caller_spills:(cm_spill)list)
         (saved:(cm_spill_frame)list) (returnpc:int)
         (calls:(cm_call_sim_frame)list) (targetpc:int).
         cm_ann_cursors ann ==
           CMACursor
             (CACallP caller oldenv oldfp oldregions ret)
             owner owner_break owner_continue :: rest ==>
         cm_ann_saved ann ==
           CMSpillFrame caller oldfp caller_spills :: saved ==>
         cm_ann_calls ann ==
           CMCallSimFrame (cm_state_fp st) oldfp returnpc :: calls ==>
         cm_runtime_core p fid st ann ==>
         cm_runtime_core p caller
           (cm_restore_call st oldenv oldfp oldregions)
           (cm_ann_leave_call targetpc ann)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm cursor_eq = assume_rule(
      `cm_ann_cursors (ann:cm_annotation) ==
       CMACursor
         (CACallP (caller:int) (oldenv:int->int->cm_value)
           (oldfp:int) (oldregions:(cm_region)list) (ret:cm_type))
         (owner:int) (owner_break:int) (owner_continue:int) ::
       (rest:(cm_acursor)list)`);
  thm saved_eq = assume_rule(
      `cm_ann_saved (ann:cm_annotation) ==
       CMSpillFrame (caller:int) (oldfp:int)
         (caller_spills:(cm_spill)list) ::
       (saved:(cm_spill_frame)list)`);
  thm calls_eq = assume_rule(
      `cm_ann_calls (ann:cm_annotation) ==
       CMCallSimFrame (cm_state_fp (st:cm_src_state))
         (oldfp:int) (returnpc:int) ::
       (calls:(cm_call_sim_frame)list)`);
  thm opened = cm_open_runtime_core(assume_rule(
      `cm_runtime_core (p:cm_program) (fid:int)
        (st:cm_src_state) (ann:cm_annotation)`));
  thm shaped_stack = conv_rule(rewrite_conv(THM_LIST(
      cursor_eq, saved_eq, calls_eq)), conjunct2_rule(opened));
  thm call_phase = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_phase_is_call_def)),
      `cm_phase_is_call
        (CACallP (caller:int) (oldenv:int->int->cm_value)
          (oldfp:int) (oldregions:(cm_region)list) (ret:cm_type))`));
  thm stack_body = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_runtime_stack_def, cm_cursor_phase_def, call_phase,
      cm_phase_oldregions_def, cm_phase_oldfp_def,
      cm_phase_caller_def)), shaped_stack);
  thm prefix = conjunct1_rule(stack_body);
  thm restored_before = match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `cm_state_regions (st:cm_src_state)`,
        `fid:int`, `cm_state_fp (st:cm_src_state)`,
        `cm_state_regions (st:cm_src_state)`,
        `oldregions:(cm_region)list`,
        `cm_state_nextgen (st:cm_src_state)`),
        cm_restore_regions_before),
      prefix), conjunct1_rule(opened));
  thm restored_stack = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `cm_state_regions (st:cm_src_state)`,
      `fid:int`, `cm_state_fp (st:cm_src_state)`,
      `caller:int`, `oldenv:int->int->cm_value`,
      `oldfp:int`, `oldregions:(cm_region)list`, `ret:cm_type`,
      `owner:int`, `owner_break:int`, `owner_continue:int`,
      `rest:(cm_acursor)list`,
      `cm_ann_spills (ann:cm_annotation)`,
      `caller_spills:(cm_spill)list`,
      `saved:(cm_spill_frame)list`, `returnpc:int`,
      `calls:(cm_call_sim_frame)list`),
      cm_runtime_stack_leave_call), shaped_stack);
  thm structure = specl_rule(TERM_LIST(
      `st:cm_src_state`, `oldenv:int->int->cm_value`,
      `oldfp:int`, `oldregions:(cm_region)list`),
      cm_restore_call_structure);
  thm fp_structure = conjunct1_rule(structure);
  thm nextgen_structure =
      conjunct1_rule(conjunct2_rule(structure));
  thm regions_structure =
      conjunct2_rule(conjunct2_rule(structure));
  thm result = cm_close_runtime_core(
      `cm_runtime_core (p:cm_program) (caller:int)
        (cm_restore_call (st:cm_src_state)
          (oldenv:int->int->cm_value) (oldfp:int)
          (oldregions:(cm_region)list))
        (cm_ann_leave_call (targetpc:int) (ann:cm_annotation))`,
      conj_rule(restored_before, restored_stack),
      THM_LIST(cursor_eq, saved_eq, calls_eq,
        fp_structure, nextgen_structure, regions_structure));
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_runtime_core_leave_call =
    cm_prove_runtime_core_leave_call();
PROOF static thm cm_prove_runtime_core_io(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (ann:cm_annotation) (input:(int)list)
         (output:(int)list).
         cm_runtime_core p fid st ann ==>
         cm_runtime_core p fid
           (cm_state_io st input output) ann`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm opened = cm_open_runtime_core(assume_rule(
      `cm_runtime_core (p:cm_program) (fid:int)
        (st:cm_src_state) (ann:cm_annotation)`));
  thm_list rules = cm_runtime_core_rules();
  thm_list state_rules = get_cm_state_core_defs();
  for (size_t i = 0; i < vector_size(state_rules); ++i) {
    vector_add(&rules, state_rules[i]);
  }
  thm target = apply_conversion(reduce_rewrite_conv(rules),
      `cm_runtime_core (p:cm_program) (fid:int)
        (cm_state_io (st:cm_src_state)
          (input:(int)list) (output:(int)list))
        (ann:cm_annotation)`);
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target), opened));
  return gnode_prove(root);
}
PROOF thm cm_runtime_core_io =
    cm_prove_runtime_core_io();

PROOF static thm cm_prove_runtime_core_store(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (ann:cm_annotation) (ty:cm_type) (ptr:cm_value)
         (v:cm_value).
         cm_runtime_core p fid st ann ==>
         cm_runtime_core p fid
           (cm_state_store ty ptr v st) ann`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm opened = cm_open_runtime_core(assume_rule(
      `cm_runtime_core (p:cm_program) (fid:int)
        (st:cm_src_state) (ann:cm_annotation)`));
  thm_list rules = cm_runtime_core_rules();
  vector_add(&rules, get_cm_state_store_def());
  thm_list state_rules = get_cm_state_core_defs();
  for (size_t i = 0; i < vector_size(state_rules); ++i) {
    vector_add(&rules, state_rules[i]);
  }
  thm target = apply_conversion(reduce_rewrite_conv(rules),
      `cm_runtime_core (p:cm_program) (fid:int)
        (cm_state_store (ty:cm_type) (ptr:cm_value)
          (v:cm_value) (st:cm_src_state))
        (ann:cm_annotation)`);
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target), opened));
  return gnode_prove(root);
}
PROOF thm cm_runtime_core_store =
    cm_prove_runtime_core_store();
PROOF static thm cm_prove_runtime_core_replace_scope(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (ann:cm_annotation) (oldphase:cm_aphase)
         (newphase:cm_aphase) (owner:int) (owner_break:int)
         (owner_continue:int) (rest:(cm_acursor)list)
         (pc:int) (temp:int) (breakpc:int) (continuepc:int).
         cm_ann_cursors ann ==
           CMACursor oldphase owner owner_break owner_continue :: rest ==>
         0i <= fid ==>
         ~cm_phase_is_call oldphase ==>
         ~cm_phase_is_scope oldphase ==>
         ~cm_phase_is_halt oldphase ==>
         cm_phase_is_scope newphase ==>
         ~cm_phase_is_call newphase ==>
         cm_phase_oldregions newphase == cm_state_regions st ==>
         cm_runtime_core p fid st ann ==>
         cm_runtime_core p fid st
           (cm_ann_replace newphase pc temp breakpc continuepc ann)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm cursor_eq = assume_rule(
      `cm_ann_cursors (ann:cm_annotation) ==
       CMACursor (oldphase:cm_aphase) (owner:int)
         (owner_break:int) (owner_continue:int) ::
       (rest:(cm_acursor)list)`);
  thm opened = cm_open_runtime_core(assume_rule(
      `cm_runtime_core (p:cm_program) (fid:int)
        (st:cm_src_state) (ann:cm_annotation)`));
  thm shaped_stack = conv_rule(
      rewrite_conv(THM_LIST(cursor_eq)), conjunct2_rule(opened));
  thm popped = match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `cm_state_regions (st:cm_src_state)`,
        `fid:int`, `cm_state_fp (st:cm_src_state)`,
        `oldphase:cm_aphase`, `owner:int`, `owner_break:int`,
        `owner_continue:int`, `rest:(cm_acursor)list`,
        `cm_ann_spills (ann:cm_annotation)`,
        `cm_ann_saved (ann:cm_annotation)`,
        `cm_ann_calls (ann:cm_annotation)`),
        cm_runtime_stack_plain_pop),
      assume_rule(`~cm_phase_is_call (oldphase:cm_aphase)`)),
      assume_rule(`~cm_phase_is_scope (oldphase:cm_aphase)`)),
      assume_rule(`~cm_phase_is_halt (oldphase:cm_aphase)`)),
      shaped_stack);
  thm entered = match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `cm_state_regions (st:cm_src_state)`,
        `fid:int`, `cm_state_fp (st:cm_src_state)`,
        `newphase:cm_aphase`, `owner:int`,
        `owner_break:int`, `owner_continue:int`,
        `rest:(cm_acursor)list`,
        `cm_ann_spills (ann:cm_annotation)`,
        `cm_ann_saved (ann:cm_annotation)`,
        `cm_ann_calls (ann:cm_annotation)`),
        cm_runtime_stack_enter_scope),
      assume_rule(`0i <= (fid:int)`)),
      assume_rule(`cm_phase_is_scope (newphase:cm_aphase)`)),
      assume_rule(`~cm_phase_is_call (newphase:cm_aphase)`)),
      assume_rule(
        `cm_phase_oldregions (newphase:cm_aphase) ==
         cm_state_regions (st:cm_src_state)`)),
      popped);
  thm result = cm_close_runtime_core(
      `cm_runtime_core (p:cm_program) (fid:int)
        (st:cm_src_state)
        (cm_ann_replace (newphase:cm_aphase) (pc:int)
          (temp:int) (breakpc:int) (continuepc:int)
          (ann:cm_annotation))`,
      conj_rule(conjunct1_rule(opened), entered),
      THM_LIST(cursor_eq));
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_runtime_core_replace_scope =
    cm_prove_runtime_core_replace_scope();

PROOF static thm cm_prove_runtime_core_done(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (ann:cm_annotation) (ctl:cm_control) (status:int)
         (next_ann:cm_annotation).
         cm_runtime_core p fid st ann ==>
         cm_task_runtime_invariant p
           (CMDoneTask st ctl status) next_ann`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm opened = cm_open_runtime_core(assume_rule(
      `cm_runtime_core (p:cm_program) (fid:int)
        (st:cm_src_state) (ann:cm_annotation)`));
  thm target_view = apply_conversion(
      rewrite_conv(THM_LIST(cm_task_runtime_invariant_def)),
      goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(
      sym_rule(target_view), conjunct1_rule(opened)));
  return gnode_prove(root);
}
PROOF thm cm_runtime_core_done = cm_prove_runtime_core_done();

PROOF static thm cm_prove_runtime_halt_done(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (ann:cm_annotation) (owner:int) (owner_break:int)
         (owner_continue:int) (rest:(cm_acursor)list)
         (ctl:cm_control) (status:int) (pc:int).
         cm_ann_cursors ann ==
           CMACursor CAHaltP owner owner_break owner_continue :: rest ==>
         cm_runtime_core p fid st ann ==>
         cm_task_runtime_invariant p
           (CMDoneTask st ctl status) (cm_ann_pop pc ann)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm cursor_eq = assume_rule(
      `cm_ann_cursors (ann:cm_annotation) ==
       CMACursor CAHaltP (owner:int) (owner_break:int)
         (owner_continue:int) :: (rest:(cm_acursor)list)`);
  thm opened = cm_open_runtime_core(assume_rule(
      `cm_runtime_core (p:cm_program) (fid:int)
        (st:cm_src_state) (ann:cm_annotation)`));
  thm shaped_stack = conv_rule(
      rewrite_conv(THM_LIST(cursor_eq)), conjunct2_rule(opened));
  thm halt_phase = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(cm_phase_is_halt_def)),
      `cm_phase_is_halt CAHaltP`));
  thm not_call = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(cm_phase_is_call_def)),
      `~cm_phase_is_call CAHaltP`));
  thm not_scope = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(cm_phase_is_scope_def)),
      `~cm_phase_is_scope CAHaltP`));
  thm stack_body = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_runtime_stack_def, cm_cursor_phase_def,
      not_call, not_scope, halt_phase)), shaped_stack);
  thm fp_eq = mp_rule(taut_rule(mk_imp(concl(stack_body),
      `cm_state_fp (st:cm_src_state) == 1048576i`)),
      stack_body);
  thm rest_nil = mp_rule(taut_rule(mk_imp(concl(stack_body),
      `(rest:(cm_acursor)list) == []`)), stack_body);
  thm spills_nil = mp_rule(taut_rule(mk_imp(concl(stack_body),
      `cm_ann_spills (ann:cm_annotation) == []`)), stack_body);
  thm saved_nil = mp_rule(taut_rule(mk_imp(concl(stack_body),
      `cm_ann_saved (ann:cm_annotation) == []`)), stack_body);
  thm calls_nil = mp_rule(taut_rule(mk_imp(concl(stack_body),
      `cm_ann_calls (ann:cm_annotation) == []`)), stack_body);
  thm layout = mp_rule(taut_rule(mk_imp(concl(stack_body),
      `cm_static_regions_layout (p:cm_program)
        (cm_state_regions (st:cm_src_state))`)), stack_body);
  thm_list rules = THM_LIST(
      cm_task_runtime_invariant_def, cm_ann_pop_def,
      cm_ann_cursors_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_ann_calls_def,
      cm_cursor_temp_def, cm_cursor_break_def,
      cm_cursor_continue_def, get_theorem_by_name("HD"),
      get_theorem_by_name("TL"), cursor_eq, fp_eq,
      rest_nil, spills_nil, saved_nil, calls_nil, layout);
  thm target = apply_conversion(reduce_rewrite_conv(rules),
      `cm_task_runtime_invariant (p:cm_program)
        (CMDoneTask (st:cm_src_state) (ctl:cm_control)
          (status:int))
        (cm_ann_pop (pc:int) (ann:cm_annotation))`);
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target),
      conjunct1_rule(opened)));
  return gnode_prove(root);
}
PROOF thm cm_runtime_halt_done =
    cm_prove_runtime_halt_done();

PROOF static thm cm_runtime_push_known(
    term p, term fid, term st, term ann, term phase,
    term pc, term temp, term breakpc, term continuepc,
    thm core) {
  thm result = specl_rule(TERM_LIST(
      p, fid, st, ann, phase, pc, temp, breakpc, continuepc),
      cm_runtime_core_push_plain);
  thm_list phase_rules = THM_LIST(
      cm_phase_is_call_def, cm_phase_is_scope_def,
      cm_phase_is_halt_def);
  for (size_t i = 0; i < 3; ++i) {
    result = match_mp_rule(result, eqt_elim_rule(
        apply_conversion(reduce_rewrite_conv(phase_rules),
          dest_imp(concl(result)).tm1)));
  }
  return match_mp_rule(result, core);
}
PROOF static thm cm_runtime_pop_known(
    term p, term fid, term st, term ann, term phase,
    term owner, term owner_break, term owner_continue,
    term rest, term pc, thm cursor_eq, thm core) {
  thm result = specl_rule(TERM_LIST(
      p, fid, st, ann, phase, owner, owner_break,
      owner_continue, rest, pc), cm_runtime_core_pop_plain);
  result = match_mp_rule(result, cursor_eq);
  thm_list phase_rules = THM_LIST(
      cm_phase_is_call_def, cm_phase_is_scope_def,
      cm_phase_is_halt_def);
  for (size_t i = 0; i < 3; ++i) {
    result = match_mp_rule(result, eqt_elim_rule(
        apply_conversion(reduce_rewrite_conv(phase_rules),
          dest_imp(concl(result)).tm1)));
  }
  return match_mp_rule(result, core);
}

PROOF static thm cm_runtime_replace_known(
    term p, term fid, term st, term ann,
    term oldphase, term newphase, term owner,
    term owner_break, term owner_continue, term rest,
    term pc, term temp, term breakpc, term continuepc,
    thm cursor_eq, thm core) {
  thm result = specl_rule(TERM_LIST(
      p, fid, st, ann, oldphase, newphase, owner,
      owner_break, owner_continue, rest,
      pc, temp, breakpc, continuepc),
      cm_runtime_core_replace_plain);
  result = match_mp_rule(result, cursor_eq);
  thm_list phase_rules = THM_LIST(
      cm_phase_is_call_def, cm_phase_is_scope_def,
      cm_phase_is_halt_def);
  for (size_t i = 0; i < 6; ++i) {
    result = match_mp_rule(result, eqt_elim_rule(
        apply_conversion(reduce_rewrite_conv(phase_rules),
          dest_imp(concl(result)).tm1)));
  }
  return match_mp_rule(result, core);
}

PROOF static thm cm_runtime_spill_known(
    term p, term fid, term st, term ann, term slot,
    term spill_value, thm fid_lower, thm slot_lower,
    thm slot_upper, thm core) {
  thm result = specl_rule(TERM_LIST(
      p, fid, st, ann, slot, spill_value),
      cm_runtime_core_spill_put);
  result = match_mp_rule(result, fid_lower);
  result = match_mp_rule(result, slot_lower);
  result = match_mp_rule(result, slot_upper);
  return match_mp_rule(result, core);
}

PROOF static thm cm_runtime_replace_scope_known(
    term p, term fid, term st, term ann,
    term oldphase, term newphase, term owner,
    term owner_break, term owner_continue, term rest,
    term pc, term temp, term breakpc, term continuepc,
    thm cursor_eq, thm fid_lower, thm core) {
  thm result = specl_rule(TERM_LIST(
      p, fid, st, ann, oldphase, newphase, owner,
      owner_break, owner_continue, rest,
      pc, temp, breakpc, continuepc),
      cm_runtime_core_replace_scope);
  result = match_mp_rule(result, cursor_eq);
  result = match_mp_rule(result, fid_lower);
  thm_list phase_rules = THM_LIST(
      cm_phase_is_call_def, cm_phase_is_scope_def,
      cm_phase_is_halt_def, cm_phase_oldregions_def);
  for (size_t i = 0; i < 6; ++i) {
    result = match_mp_rule(result, eqt_elim_rule(
        apply_conversion(reduce_rewrite_conv(phase_rules),
          dest_imp(concl(result)).tm1)));
  }
  return match_mp_rule(result, core);
}

PROOF static thm cm_runtime_leave_scope_known(
    term p, term fid, term st, term ann, term phase,
    term oldenv, term oldregions, term owner,
    term owner_break, term owner_continue, term rest,
    term pc, thm cursor_eq, thm core) {
  thm result = specl_rule(TERM_LIST(
      p, fid, st, ann, phase, oldenv, oldregions,
      owner, owner_break, owner_continue, rest, pc),
      cm_runtime_core_leave_scope);
  result = match_mp_rule(result, cursor_eq);
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
PROOF static thm_list cm_runtime_annotation_reduction_rules(void) {
  return THM_LIST(
      cm_ann_plain_def, cm_ann_linear_def,
      cm_ann_push_def, cm_ann_replace_def, cm_ann_pop_def,
      cm_ann_spills_set_def, cm_ann_put_spill_def,
      cm_ann_enter_call_def, cm_ann_leave_call_def,
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def,
      cm_ann_spills_def, cm_ann_saved_def, cm_ann_calls_def,
      cm_cursor_phase_def, cm_cursor_temp_def,
      cm_cursor_break_def, cm_cursor_continue_def,
      get_theorem_by_name("HD"), get_theorem_by_name("TL"));
}

PROOF static thm cm_runtime_cursor_eq(
    term ann, term phase, term owner, term owner_break,
    term owner_continue, term rest) {
  return eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(cm_runtime_annotation_reduction_rules()),
      `cm_ann_cursors ${ann:cm_annotation} ==
       CMACursor ${phase:cm_aphase} ${owner:int}
         ${owner_break:int} ${owner_continue:int} ::
       ${rest:(cm_acursor)list}`));
}


PROOF static thm cm_function_wf_from_typed(
    term p, term fid, thm typed, thm fid_lower, thm fid_upper) {
  thm opened = conv_rule(rewrite_conv(THM_LIST(
      get_cm_typed_program_def())), typed);
  thm all_functions = mp_rule(taut_rule(mk_imp(
      concl(opened),
      `!index.
         0i <= index ==>
         index < ilength (cm_program_functions ${p:cm_program}) ==>
         cm_function_wf ${p:cm_program}
           (inth index (cm_program_functions ${p:cm_program}))`)),
      opened);
  return match_mp_rule(match_mp_rule(
      spec_rule(fid, all_functions), fid_lower), fid_upper);
}

PROOF static thm cm_runtime_enter_scope_known(
    term p, term fid, term st, term ann, term phase,
    term pc, term temp, term breakpc, term continuepc,
    thm fid_lower, thm core) {
  thm result = specl_rule(TERM_LIST(
      p, fid, st, ann, phase, pc, temp, breakpc, continuepc),
      cm_runtime_core_enter_scope);
  result = match_mp_rule(result, fid_lower);
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


PROOF static void cm_accept_runtime_result(
    gnode branch, thm result, thm shape,
    thm_list extra_rules) {
  thm_list rules = THM_LIST(
      shape, get_cm_step_def(), get_cm_rstart_def(),
      get_cm_begin_call_def(),
      get_cm_lstart_def(), get_cm_sstart_def(),
      cm_annotation_step_def, cm_update_annotation_def,
      cm_update_r_def, cm_update_l_def, cm_update_s_def,
      cm_update_v_def, cm_update_c_def,
      get_cm_vapply_def(), get_cm_capply_def(),
      cm_task_runtime_invariant_def, cm_runtime_core_def,
      cm_cursor_frames_def, cm_phase_frame_def,
      cm_cursor_phase_def, cm_cursor_temp_def,
      cm_cursor_break_def, cm_cursor_continue_def,
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def,
      cm_ann_spills_def, cm_ann_saved_def, cm_ann_calls_def,
      get_theorem_by_name("HD"), get_theorem_by_name("TL"));
  for (size_t i = 0; i < vector_size(extra_rules); ++i) {
    vector_add(&rules, extra_rules[i]);
  }
  thm expanded = conv_rule(
      rewrite_conv(THM_LIST(cm_runtime_core_def)), result);
  gnode reduced =
      CONV_WITH_ASMP_TAC(branch, reduce_rewrite_conv, rules);
  if (IS_NULL(reduced->solved)) {
    reduced =
        CONV_WITH_ASMP_TAC(reduced, reduce_rewrite_conv, rules);
  }
  if (IS_NULL(reduced->solved)) {
    ACCEPT_TAC(reduced, mp_rule(taut_rule(mk_imp(
        concl(expanded), goal_ccl(reduced->g))), expanded));
  }
}







PROOF thm cm_v_spill_ready_def = new_rec_definition(
    get_cm_aphase_recursion(),
    `(!p fid ann. cm_v_spill_ready (p:cm_program) (fid:int)
        (ann:cm_annotation) CAHaltP = T) &&
     (!p fid ann ty. cm_v_spill_ready p fid ann (CALoadP (ty:cm_type)) = T) &&
     (!p fid ann src ty.
        cm_v_spill_ready p fid ann
          (CAAssignLP (src:cm_expr) (ty:cm_type)) =
        (0i <= cm_ann_temp ann &&
         cm_ann_temp ann < cm_temp_slots
           (inth fid (cm_program_functions p)))) &&
     (!p fid ann ptr ty.
        cm_v_spill_ready p fid ann
          (CAAssignRP (ptr:cm_value) (ty:cm_type)) = T) &&
     (!p fid ann op left right ty.
        cm_v_spill_ready p fid ann
          (CABinLP (op:int) (left:cm_expr) (right:cm_expr)
             (ty:cm_type)) =
        (if op == 0i || op == 1i
         then T
         else 0i <= cm_ann_temp ann &&
              cm_ann_temp ann < cm_temp_slots
                (inth fid (cm_program_functions p)))) &&
     (!p fid ann op left right left_value ty.
        cm_v_spill_ready p fid ann
          (CABinRP (op:int) (left:cm_expr) (right:cm_expr)
             (left_value:cm_value) (ty:cm_type)) = T) &&
     (!p fid ann op.
        cm_v_spill_ready p fid ann (CAUnaryP (op:int)) = T) &&
     (!p fid ann index ty.
        cm_v_spill_ready p fid ann
          (CAIndexLP (index:cm_expr) (ty:cm_type)) =
        (0i <= cm_ann_temp ann &&
         cm_ann_temp ann < cm_temp_slots
           (inth fid (cm_program_functions p)))) &&
     (!p fid ann base ty.
        cm_v_spill_ready p fid ann
          (CAIndexRP (base:cm_value) (ty:cm_type)) = T) &&
     (!p fid ann mid ty.
        cm_v_spill_ready p fid ann
          (CAMemberP (mid:int) (ty:cm_type)) = T) &&
     (!p fid ann. cm_v_spill_ready p fid ann CAPutcP = T) &&
     (!p fid ann. cm_v_spill_ready p fid ann CAPutiP = T) &&
     (!p fid ann. cm_v_spill_ready p fid ann CAExitP = T) &&
     (!p fid ann. cm_v_spill_ready p fid ann CAExprStmtP = T) &&
     (!p fid ann slot.
        cm_v_spill_ready p fid ann (CAInitP (slot:int)) = T) &&
     (!p fid ann env regions jump target.
        cm_v_spill_ready p fid ann
          (CABlockP (env:int->int->cm_value)
             (regions:(cm_region)list) (jump:bool) (target:int)) = T) &&
     (!p fid ann second.
        cm_v_spill_ready p fid ann (CASeqP (second:cm_stmt)) = T) &&
     (!p fid ann yes no.
        cm_v_spill_ready p fid ann
          (CAIfP (yes:cm_stmt) (no:cm_stmt)) = T) &&
     (!p fid ann guard body loop_start loop_end.
        cm_v_spill_ready p fid ann
          (CAWhileGuardP (guard:cm_expr) (body:cm_stmt)
             (loop_start:int) (loop_end:int)) = T) &&
     (!p fid ann guard body env regions loop_start loop_end.
        cm_v_spill_ready p fid ann
          (CAWhileBodyP (guard:cm_expr) (body:cm_stmt)
             (env:int->int->cm_value) (regions:(cm_region)list)
             (loop_start:int) (loop_end:int)) = T) &&
     (!p fid ann. cm_v_spill_ready p fid ann CAReturnP = T) &&
     (!p fid ann callee rest values ret all_args base_slot current_slot
         scratch.
        cm_v_spill_ready p fid ann
          (CAArgP (callee:int) (rest:(cm_expr)list)
             (values:(cm_value)list) (ret:cm_type)
             (all_args:(cm_expr)list) (base_slot:int)
             (current_slot:int) (scratch:int)) =
        (0i <= base_slot &&
         0i <= current_slot &&
         current_slot < cm_temp_slots
           (inth fid (cm_program_functions p)))) &&
     (!p fid ann caller env fp regions ret.
        cm_v_spill_ready p fid ann
          (CACallP (caller:int) (env:int->int->cm_value) (fp:int)
             (regions:(cm_region)list) (ret:cm_type)) = T)`);
PROOF static int _c_cm_v_spill_ready =
    cst_add_const_to_header(`cm_v_spill_ready`);
PROOF thm cm_v_source_ready_def = new_fun_definition(
    `cm_v_source_ready (p:cm_program) (fid:int)
       (st:cm_src_state) (phase:cm_aphase) : bool =
       ((!slot. phase == CAInitP (slot:int) ==>
          (cm_binding_address_ok p fid 1i slot st &&
           cm_store_ok
             (cm_slot_ty
               (inth slot
                 (cm_function_locals
                   (inth fid (cm_program_functions p)))))
             (cm_state_env st 1i slot) st)) &&
        (!op left right left_value ty.
          phase ==
            CABinRP (op:int) (left:cm_expr) (right:cm_expr)
              (left_value:cm_value) (ty:cm_type) ==>
          (op == 0i ==> ~cm_truth st left_value) &&
          (op == 1i ==> cm_truth st left_value)))`);
PROOF static int _c_cm_v_source_ready =
    cst_add_const_to_header(`cm_v_source_ready`);


PROOF thm cm_runtime_step_ready_def = new_rec_definition(
    get_cm_task_recursion(),
    `(!root p input ann.
        cm_runtime_step_ready (root:cm_program)
          (CMStartTask (p:cm_program) (input:(int)list))
          (ann:cm_annotation) =
        (cm_typed_program root &&
         cm_task_layout_ready root (CMStartTask p input) ann)) &&
     (!root p fid expr st ks ann.
        cm_runtime_step_ready root
          (CMRTask (p:cm_program) (fid:int) (expr:cm_expr)
             (st:cm_src_state) (ks:(cm_frame)list)) ann =
        (0i <= fid &&
         cm_task_layout_ready root
           (CMRTask p fid expr st ks) ann)) &&
     (!root p fid expr st ks ann.
        cm_runtime_step_ready root
          (CMLTask (p:cm_program) (fid:int) (expr:cm_expr)
             (st:cm_src_state) (ks:(cm_frame)list)) ann =
        (0i <= fid &&
         cm_task_layout_ready root
           (CMLTask p fid expr st ks) ann)) &&
     (!root p fid stmt st ks ann.
        cm_runtime_step_ready root
          (CMSTask (p:cm_program) (fid:int) (stmt:cm_stmt)
             (st:cm_src_state) (ks:(cm_frame)list)) ann =
        (cm_typed_program root && 0i <= fid &&
         cm_task_layout_ready root
           (CMSTask p fid stmt st ks) ann)) &&
     (!root p fid v st ks ann.
        cm_runtime_step_ready root
          (CMVTask (p:cm_program) (fid:int) (v:cm_value)
             (st:cm_src_state) (ks:(cm_frame)list)) ann =
        (cm_task_layout_ready root
           (CMVTask p fid v st ks) ann &&
         (~(cm_ann_cursors ann == []) ==>
          (cm_phase_is_halt
             (cm_cursor_phase (HD (cm_ann_cursors ann))) ||
           0i <= fid)) &&
         (~(cm_ann_cursors ann == []) ==>
          cm_v_spill_ready root fid ann
            (cm_cursor_phase (HD (cm_ann_cursors ann)))) &&
         (~(cm_ann_cursors ann == []) ==>
          cm_v_source_ready root fid st
            (cm_cursor_phase (HD (cm_ann_cursors ann)))))) &&
     (!root p fid ctl st ks ann.
        cm_runtime_step_ready root
          (CMCTask (p:cm_program) (fid:int) (ctl:cm_control)
             (st:cm_src_state) (ks:(cm_frame)list)) ann =
        (cm_task_layout_ready root
           (CMCTask p fid ctl st ks) ann)) &&
     (!root st ctl status ann.
        cm_runtime_step_ready (root:cm_program)
          (CMDoneTask (st:cm_src_state) (ctl:cm_control)
             (status:int)) (ann:cm_annotation) = T)`);
PROOF static int _c_cm_runtime_step_ready =
    cst_add_const_to_header(`cm_runtime_step_ready`);

PROOF static thm cm_prove_task_runtime_r_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (expr:cm_expr)
         (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         cm_typed_program p ==>
         0i <= fid ==>
         cm_r_layout_ready p fid expr st ks ann ==>
         cm_runtime_core p fid st ann ==>
         cm_task_runtime_invariant p
           (cm_step (CMRTask p fid expr st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask p fid expr st ks) ann))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(
      introduced,
      ispec_rule(`expr:cm_expr`, get_cm_expr_cases()),
      "Hex");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    while (true) {
      labeled_term_list assumptions = goal_lasmps(cases[i]->g);
      int index =
          labeled_term_list_index(assumptions, "Hex");
      if (!is_exists(assumptions[index].tm)) break;
      cases[i] = ASMP_EXISTS_TAC(cases[i], "Hex", NULL);
    }
    labeled_term_list assumptions = goal_lasmps(cases[i]->g);
    thm shape = assume_rule(
        assumptions[
          labeled_term_list_index(assumptions, "Hex")].tm);
    thm core = assume_rule(
        `cm_runtime_core (p:cm_program) (fid:int)
          (st:cm_src_state) (ann:cm_annotation)`);
    thm ready = assume_rule(
        `cm_r_layout_ready (p:cm_program) (fid:int)
          (expr:cm_expr) (st:cm_src_state)
          (ks:(cm_frame)list) (ann:cm_annotation)`);
    thm result = empty_theorem;
    if (i == 0) {
      result = match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          `ann:cm_annotation`,
          `cm_push_code
            (cm_const_immediate (a1:cm_type) (a0:int))`),
          cm_runtime_core_linear), core);
    } else if (i == 1) {
      result = match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          `ann:cm_annotation`,
          `cm_push_code
            (cm_string_address (p:cm_program) (a0:int))`),
          cm_runtime_core_linear), core);
    } else if (i == 2) {
      gnode_list binding_cases = BOOL_CASES_TAC(
          cases[i],
          `cm_binding_array (p:cm_program) (fid:int)
             (a0:int) (a1:int)`,
          "Harray");
      {
        thm ready_open = conv_rule(
            rewrite_conv(THM_LIST(cm_r_layout_ready_def)), ready);
        thm address_ready = match_mp_rule(specl_rule(TERM_LIST(
            `a0:int`, `a1:int`, `a2:cm_type`),
            conjunct2_rule(conjunct2_rule(ready_open))), shape);
        thm address_ok = match_mp_rule(address_ready, assume_rule(
            `cm_binding_array (p:cm_program) (fid:int)
              (a0:int) (a1:int)`));
        thm linear = match_mp_rule(specl_rule(TERM_LIST(
            `p:cm_program`, `fid:int`, `st:cm_src_state`,
            `ann:cm_annotation`,
            `cm_binding_address_code (p:cm_program)
              (fid:int) (a0:int) (a1:int)`),
            cm_runtime_core_linear), core);
        cm_accept_runtime_result(
            binding_cases[0], linear, shape, THM_LIST(address_ok));
      }
      {
        thm pushed = cm_runtime_push_known(
            `p:cm_program`, `fid:int`, `st:cm_src_state`,
            `ann:cm_annotation`, `CALoadP (a2:cm_type)`,
            `cm_ann_pc (ann:cm_annotation)`,
            `cm_ann_temp (ann:cm_annotation)`,
            `cm_ann_break (ann:cm_annotation)`,
            `cm_ann_continue (ann:cm_annotation)`, core);
        cm_accept_runtime_result(
            binding_cases[1], pushed, shape, THM_LIST());
      }
      continue;
    } else if (i == 3) {
      result = cm_runtime_push_known(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          `ann:cm_annotation`,
          `CAAssignLP (a1:cm_expr) (a2:cm_type)`,
          `cm_ann_pc (ann:cm_annotation)`,
          `cm_ann_temp (ann:cm_annotation)`,
          `cm_ann_break (ann:cm_annotation)`,
          `cm_ann_continue (ann:cm_annotation)`, core);
    } else if (i == 4) {
      result = cm_runtime_push_known(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          `ann:cm_annotation`,
          `CABinLP (a0:int) (a1:cm_expr) (a2:cm_expr)
            (a3:cm_type)`,
          `cm_ann_pc (ann:cm_annotation)`,
          `cm_ann_temp (ann:cm_annotation)`,
          `cm_ann_break (ann:cm_annotation)`,
          `cm_ann_continue (ann:cm_annotation)`, core);
    } else if (i == 5) {
      gnode_list two_cases = BOOL_CASES_TAC(
          cases[i], `(a0:int) == 2i`, "Hop_two");
      {
        thm pushed = cm_runtime_push_known(
            `p:cm_program`, `fid:int`, `st:cm_src_state`,
            `ann:cm_annotation`, `CALoadP (a2:cm_type)`,
            `cm_ann_pc (ann:cm_annotation)`,
            `cm_ann_temp (ann:cm_annotation)`,
            `cm_ann_break (ann:cm_annotation)`,
            `cm_ann_continue (ann:cm_annotation)`, core);
        cm_accept_runtime_result(
            two_cases[0], pushed, shape, THM_LIST());
      }
      gnode_list three_cases = BOOL_CASES_TAC(
          two_cases[1], `(a0:int) == 3i`, "Hop_three");
      cm_accept_runtime_result(
          three_cases[0], core, shape, THM_LIST());
      {
        thm pushed = cm_runtime_push_known(
            `p:cm_program`, `fid:int`, `st:cm_src_state`,
            `ann:cm_annotation`, `CAUnaryP (a0:int)`,
            `cm_ann_pc (ann:cm_annotation)`,
            `cm_ann_temp (ann:cm_annotation)`,
            `cm_ann_break (ann:cm_annotation)`,
            `cm_ann_continue (ann:cm_annotation)`, core);
        cm_accept_runtime_result(
            three_cases[1], pushed, shape, THM_LIST());
      }
      continue;
    } else if (i == 6) {
      result = cm_runtime_push_known(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          `ann:cm_annotation`, `CALoadP (a2:cm_type)`,
          `cm_ann_pc (ann:cm_annotation)`,
          `cm_ann_temp (ann:cm_annotation)`,
          `cm_ann_break (ann:cm_annotation)`,
          `cm_ann_continue (ann:cm_annotation)`, core);
    } else if (i == 7) {
      gnode_list member_cases = BOOL_CASES_TAC(
          cases[i],
          `cm_member_array (p:cm_program)
             (cm_expr_type (a0:cm_expr)) (a1:int)`,
          "Hmember_array");
      cm_accept_runtime_result(
          member_cases[0], core, shape, THM_LIST());
      {
        thm pushed = cm_runtime_push_known(
            `p:cm_program`, `fid:int`, `st:cm_src_state`,
            `ann:cm_annotation`, `CALoadP (a2:cm_type)`,
            `cm_ann_pc (ann:cm_annotation)`,
            `cm_ann_temp (ann:cm_annotation)`,
            `cm_ann_break (ann:cm_annotation)`,
            `cm_ann_continue (ann:cm_annotation)`, core);
        cm_accept_runtime_result(
            member_cases[1], pushed, shape, THM_LIST());
      }
      continue;
    } else if (i == 8) {
      gnode_list args_cases = BOOL_CASES_TAC(
          cases[i],
          `(a1:(cm_expr)list) == ([]:(cm_expr)list)`,
          "Hargs");
      {
        thm args_nil = assume_rule(
            `(a1:(cm_expr)list) == []`);
        thm call_shape = conv_rule(
            rewrite_conv(THM_LIST(args_nil)), shape);
        thm ready_open = conjunct1_rule(conv_rule(
            rewrite_conv(THM_LIST(cm_r_layout_ready_def)),
            assume_rule(
              `cm_r_layout_ready (p:cm_program) (fid:int)
                (expr:cm_expr) (st:cm_src_state)
                (ks:(cm_frame)list) (ann:cm_annotation)`)));
        thm conditions = match_mp_rule(
            specl_rule(TERM_LIST(`a0:int`, `a2:cm_type`),
              ready_open), call_shape);
        thm call_ok = conjunct1_rule(conditions);
        thm source_depth =
            conjunct1_rule(conjunct2_rule(conditions));
        thm annotation_depth =
            conjunct2_rule(conjunct2_rule(conditions));
        thm entered = match_mp_rule(match_mp_rule(
            match_mp_rule(specl_rule(TERM_LIST(
              `p:cm_program`, `fid:int`, `a0:int`,
              `[]:(cm_value)list`, `st:cm_src_state`,
              `a2:cm_type`,
              `cm_ann_pc (ann:cm_annotation) + 1i`,
              `cm_ann_temp (ann:cm_annotation)`,
              `cm_ann_break (ann:cm_annotation)`,
              `cm_ann_continue (ann:cm_annotation)`,
              `ann:cm_annotation`),
              cm_runtime_core_enter_call),
            assume_rule(`cm_typed_program (p:cm_program)`)),
            call_ok), core);
        cm_accept_runtime_result(
            args_cases[0], entered, call_shape,
            THM_LIST(args_nil, call_ok,
              source_depth, annotation_depth));
      }
      {
        thm args_nonempty = assume_rule(
            `~((a1:(cm_expr)list) == [])`);
        thm source_nonempty = match_mp_rule(
            specl_rule(TERM_LIST(
              `p:cm_program`, `fid:int`,
              `a1:(cm_expr)list`, `st:cm_src_state`,
              `ks:(cm_frame)list`, `a0:int`, `a2:cm_type`),
              cm_args_start_nonempty), args_nonempty);
        thm pushed = cm_runtime_push_known(
            `p:cm_program`, `fid:int`, `st:cm_src_state`,
            `ann:cm_annotation`,
            `CAArgP (a0:int) (TL (a1:(cm_expr)list))
              ([]:(cm_value)list) (a2:cm_type)
              (a1:(cm_expr)list)
              (cm_ann_temp (ann:cm_annotation))
              (cm_ann_temp ann)
              (cm_ann_temp ann + ilength a1)`,
            `cm_ann_pc (ann:cm_annotation)`,
            `cm_ann_temp (ann:cm_annotation) +
              ilength (a1:(cm_expr)list)`,
            `cm_ann_break (ann:cm_annotation)`,
            `cm_ann_continue (ann:cm_annotation)`, core);
        cm_accept_runtime_result(
            args_cases[1], pushed, shape,
            THM_LIST(args_nonempty, source_nonempty));
      }
      continue;
    } else if (i == 9) {
      result = match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          `ann:cm_annotation`,
          `cm_push_code
            (cm_type_size (cm_program_structs (p:cm_program))
              (a0:cm_type))`),
          cm_runtime_core_linear), core);
    } else if (i == 10) {
      gnode_list input_cases = BOOL_CASES_TAC(
          cases[i],
          `cm_state_input (st:cm_src_state) ==
             ([]:(int)list)`,
          "Hinput");
      {
        thm plain = match_mp_rule(specl_rule(TERM_LIST(
            `p:cm_program`, `fid:int`, `st:cm_src_state`,
            `ann:cm_annotation`,
            `cm_ann_pc (ann:cm_annotation) + 1i`,
            `cm_ann_temp (ann:cm_annotation)`,
            `cm_ann_break (ann:cm_annotation)`,
            `cm_ann_continue (ann:cm_annotation)`),
            cm_runtime_core_plain), core);
        cm_accept_runtime_result(
            input_cases[0], plain, shape, THM_LIST());
      }
      {
        thm ready_open = conv_rule(
            rewrite_conv(THM_LIST(cm_r_layout_ready_def)), ready);
        thm input_ready = match_mp_rule(
            spec_rule(`a:cm_type`,
              conjunct1_rule(conjunct2_rule(ready_open))), shape);
        thm head_byte = mp_rule(mp_rule(
            taut_rule(imp_chain(TERM_LIST(
              concl(input_ready),
              `~(cm_state_input (st:cm_src_state) == [])`),
              `tower_byte_value
                (HD (cm_state_input (st:cm_src_state)))`)),
            input_ready), assume_rule(
              `~(cm_state_input (st:cm_src_state) == [])`));
        thm io_core = match_mp_rule(specl_rule(TERM_LIST(
            `p:cm_program`, `fid:int`, `st:cm_src_state`,
            `ann:cm_annotation`,
            `TL (cm_state_input (st:cm_src_state))`,
            `cm_state_output (st:cm_src_state)`),
            cm_runtime_core_io), core);
        thm plain = match_mp_rule(specl_rule(TERM_LIST(
            `p:cm_program`, `fid:int`,
            `cm_state_io (st:cm_src_state)
              (TL (cm_state_input st)) (cm_state_output st)`,
            `ann:cm_annotation`,
            `cm_ann_pc (ann:cm_annotation) + 1i`,
            `cm_ann_temp (ann:cm_annotation)`,
            `cm_ann_break (ann:cm_annotation)`,
            `cm_ann_continue (ann:cm_annotation)`),
            cm_runtime_core_plain), io_core);
        cm_accept_runtime_result(
            input_cases[1], plain, shape, THM_LIST(head_byte));
      }
      continue;
    } else if (i == 11) {
      result = cm_runtime_push_known(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          `ann:cm_annotation`, `CAPutcP`,
          `cm_ann_pc (ann:cm_annotation)`,
          `cm_ann_temp (ann:cm_annotation)`,
          `cm_ann_break (ann:cm_annotation)`,
          `cm_ann_continue (ann:cm_annotation)`, core);
    } else if (i == 12) {
      result = cm_runtime_push_known(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          `ann:cm_annotation`, `CAPutiP`,
          `cm_ann_pc (ann:cm_annotation)`,
          `cm_ann_temp (ann:cm_annotation)`,
          `cm_ann_break (ann:cm_annotation)`,
          `cm_ann_continue (ann:cm_annotation)`, core);
    } else {
      result = cm_runtime_push_known(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          `ann:cm_annotation`, `CAExitP`,
          `cm_ann_pc (ann:cm_annotation)`,
          `cm_ann_temp (ann:cm_annotation)`,
          `cm_ann_break (ann:cm_annotation)`,
          `cm_ann_continue (ann:cm_annotation)`, core);
    }
    cm_accept_runtime_result(
        cases[i], result, shape, THM_LIST());
  }
  return gnode_prove(root);
}
PROOF thm cm_task_runtime_r_step =
    cm_prove_task_runtime_r_step();

PROOF static thm cm_prove_task_runtime_l_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (expr:cm_expr)
         (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         cm_l_layout_ready p fid expr st ==>
         cm_runtime_core p fid st ann ==>
         cm_task_runtime_invariant p
           (cm_step (CMLTask p fid expr st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMLTask p fid expr st ks) ann))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(
      introduced,
      ispec_rule(`expr:cm_expr`, get_cm_expr_cases()),
      "Hex");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    while (true) {
      labeled_term_list assumptions = goal_lasmps(cases[i]->g);
      int index =
          labeled_term_list_index(assumptions, "Hex");
      if (!is_exists(assumptions[index].tm)) break;
      cases[i] = ASMP_EXISTS_TAC(cases[i], "Hex", NULL);
    }
    labeled_term_list assumptions = goal_lasmps(cases[i]->g);
    thm shape = assume_rule(
        assumptions[
          labeled_term_list_index(assumptions, "Hex")].tm);
    thm ready_open = conv_rule(
        rewrite_conv(THM_LIST(cm_l_layout_ready_def)),
        assume_rule(
          `cm_l_layout_ready (p:cm_program) (fid:int)
            (expr:cm_expr) (st:cm_src_state)`));
    thm lvalue = conv_rule(
        rewrite_conv(THM_LIST(shape)), conjunct1_rule(ready_open));
    thm core = assume_rule(
        `cm_runtime_core (p:cm_program) (fid:int)
          (st:cm_src_state) (ann:cm_annotation)`);
    if (i == 2) {
      thm address_ok = match_mp_rule(specl_rule(TERM_LIST(
          `a0:int`, `a1:int`, `a2:cm_type`),
          conjunct2_rule(ready_open)), shape);
      thm linear = match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          `ann:cm_annotation`,
          `cm_binding_address_code (p:cm_program)
            (fid:int) (a0:int) (a1:int)`),
          cm_runtime_core_linear), core);
      cm_accept_runtime_result(
          cases[i], linear, shape, THM_LIST(address_ok));
      continue;
    }
    if (i == 5) {
      thm op_two = conv_rule(
          reduce_rewrite_conv(THM_LIST(get_cm_lvalue_def())),
          lvalue);
      cm_accept_runtime_result(
          cases[i], core, shape, THM_LIST(op_two));
      continue;
    }
    if (i == 6) {
      thm pushed = cm_runtime_push_known(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          `ann:cm_annotation`,
          `CAIndexLP (a1:cm_expr) (a2:cm_type)`,
          `cm_ann_pc (ann:cm_annotation)`,
          `cm_ann_temp (ann:cm_annotation)`,
          `cm_ann_break (ann:cm_annotation)`,
          `cm_ann_continue (ann:cm_annotation)`, core);
      cm_accept_runtime_result(
          cases[i], pushed, shape, THM_LIST());
      continue;
    }
    if (i == 7) {
      thm pushed = cm_runtime_push_known(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          `ann:cm_annotation`,
          `CAMemberP (a1:int) (cm_expr_type (a0:cm_expr))`,
          `cm_ann_pc (ann:cm_annotation)`,
          `cm_ann_temp (ann:cm_annotation)`,
          `cm_ann_break (ann:cm_annotation)`,
          `cm_ann_continue (ann:cm_annotation)`, core);
      cm_accept_runtime_result(
          cases[i], pushed, shape, THM_LIST());
      continue;
    }
    thm impossible = conv_rule(
        reduce_rewrite_conv(THM_LIST(get_cm_lvalue_def())),
        lvalue);
    CONTR_TAC(cases[i], impossible);
  }
  return gnode_prove(root);
}
PROOF thm cm_task_runtime_l_step =
    cm_prove_task_runtime_l_step();

PROOF static thm cm_prove_task_runtime_s_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (stmt:cm_stmt)
         (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         cm_typed_program p ==>
         0i <= fid ==>
         cm_stmt_start_safe p fid stmt ==>
         cm_runtime_core p fid st ann ==>
         cm_task_runtime_invariant p
           (cm_step (CMSTask p fid stmt st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMSTask p fid stmt st ks) ann))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(
      introduced,
      ispec_rule(`stmt:cm_stmt`, get_cm_stmt_cases()),
      "Hstmt");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    while (true) {
      labeled_term_list assumptions = goal_lasmps(cases[i]->g);
      int index =
          labeled_term_list_index(assumptions, "Hstmt");
      if (!is_exists(assumptions[index].tm)) break;
      cases[i] = ASMP_EXISTS_TAC(cases[i], "Hstmt", NULL);
    }
    labeled_term_list assumptions = goal_lasmps(cases[i]->g);
    thm shape = assume_rule(
        assumptions[
          labeled_term_list_index(assumptions, "Hstmt")].tm);
    thm core = assume_rule(
        `cm_runtime_core (p:cm_program) (fid:int)
          (st:cm_src_state) (ann:cm_annotation)`);
    thm fid_lower = assume_rule(`0i <= (fid:int)`);
    thm result = empty_theorem;
    if (i == 0) {
      result = core;
    } else if (i == 1) {
      result = cm_runtime_push_known(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          `ann:cm_annotation`, `CAExprStmtP`,
          `cm_ann_pc (ann:cm_annotation)`,
          `cm_ann_temp (ann:cm_annotation)`,
          `cm_ann_break (ann:cm_annotation)`,
          `cm_ann_continue (ann:cm_annotation)`, core);
    } else if (i == 2 || i == 3) {
      thm safe = conv_rule(rewrite_conv(THM_LIST(shape)),
          assume_rule(
            `cm_stmt_start_safe (p:cm_program) (fid:int)
              (stmt:cm_stmt)`));
      thm local_ok = conv_rule(reduce_rewrite_conv(
          THM_LIST(get_cm_stmt_start_safe_def())), safe);
      thm local_open = conv_rule(rewrite_conv(
          THM_LIST(get_cm_local_slot_ok_def())), local_ok);
      thm fid_upper =
          conjunct1_rule(conjunct2_rule(local_open));
      thm slot_lower =
          conjunct1_rule(conjunct2_rule(conjunct2_rule(local_open)));
      thm slot_upper =
          conjunct2_rule(conjunct2_rule(conjunct2_rule(local_open)));
      thm function_wf = cm_function_wf_from_typed(
          `p:cm_program`, `fid:int`,
          assume_rule(`cm_typed_program (p:cm_program)`),
          conjunct1_rule(local_open), fid_upper);
      thm activated = specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `a0:int`,
          `st:cm_src_state`, `ann:cm_annotation`),
          cm_runtime_core_activate_local);
      activated = match_mp_rule(activated, function_wf);
      activated = match_mp_rule(activated, fid_lower);
      activated = match_mp_rule(activated, slot_lower);
      activated = match_mp_rule(activated, slot_upper);
      activated = match_mp_rule(activated, core);
      if (i == 2) {
        result = activated;
      } else {
        result = cm_runtime_push_known(
            `p:cm_program`, `fid:int`,
            `cm_activate_local (p:cm_program) (fid:int)
              (a0:int) (st:cm_src_state)`,
            `ann:cm_annotation`, `CAInitP (a0:int)`,
            `cm_ann_pc (ann:cm_annotation)`,
            `cm_ann_temp (ann:cm_annotation)`,
            `cm_ann_break (ann:cm_annotation)`,
            `cm_ann_continue (ann:cm_annotation)`, activated);
      }
      cm_accept_runtime_result(
          cases[i], result, shape, THM_LIST(local_ok));
      continue;
    } else if (i == 4) {
      result = cm_runtime_push_known(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          `ann:cm_annotation`, `CASeqP (a1:cm_stmt)`,
          `cm_ann_pc (ann:cm_annotation)`,
          `cm_ann_temp (ann:cm_annotation)`,
          `cm_ann_break (ann:cm_annotation)`,
          `cm_ann_continue (ann:cm_annotation)`, core);
    } else if (i == 5) {
      result = cm_runtime_enter_scope_known(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          `ann:cm_annotation`,
          `CABlockP (cm_state_env (st:cm_src_state))
            (cm_state_regions st) F 0i`,
          `cm_ann_pc (ann:cm_annotation)`,
          `cm_ann_temp (ann:cm_annotation)`,
          `cm_ann_break (ann:cm_annotation)`,
          `cm_ann_continue (ann:cm_annotation)`,
          fid_lower, core);
    } else if (i == 6) {
      result = cm_runtime_push_known(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          `ann:cm_annotation`,
          `CAIfP (a1:cm_stmt) (a2:cm_stmt)`,
          `cm_ann_pc (ann:cm_annotation)`,
          `cm_ann_temp (ann:cm_annotation)`,
          `cm_ann_break (ann:cm_annotation)`,
          `cm_ann_continue (ann:cm_annotation)`, core);
    } else if (i == 7) {
      result = cm_runtime_push_known(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          `ann:cm_annotation`,
          `CAWhileGuardP (a0:cm_expr) (a1:cm_stmt)
            (cm_ann_pc (ann:cm_annotation))
            (cm_ann_pc ann +
              cm_stmt_code_count p fid
                (CMWhileS (a0:cm_expr) (a1:cm_stmt)))`,
          `cm_ann_pc (ann:cm_annotation)`,
          `cm_ann_temp (ann:cm_annotation)`,
          `cm_ann_break (ann:cm_annotation)`,
          `cm_ann_continue (ann:cm_annotation)`, core);
    } else if (i == 8 || i == 9) {
      result = core;
    } else {
      result = cm_runtime_push_known(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          `ann:cm_annotation`, `CAReturnP`,
          `cm_ann_pc (ann:cm_annotation)`,
          `cm_ann_temp (ann:cm_annotation)`,
          `cm_ann_break (ann:cm_annotation)`,
          `cm_ann_continue (ann:cm_annotation)`, core);
    }
    cm_accept_runtime_result(
        cases[i], result, shape, THM_LIST());
  }
  return gnode_prove(root);
}
PROOF thm cm_task_runtime_s_step =
    cm_prove_task_runtime_s_step();

PROOF static thm cm_prove_task_runtime_start_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (input:(int)list).
         cm_typed_program p ==>
         cm_call_ok p (cm_program_main p) []
           (cm_initial_state p input) ==>
         cm_task_runtime_invariant p
           (cm_step (CMStartTask p input))
           (cm_update_annotation
            (cm_annotation_step
              (CMStartTask p input) cm_initial_annotation))`);
  gnode leaf = AUTO_INTROS_TAC(root);
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
      spec_rule(`p:cm_program`,
        cm_static_regions_before_dynamic));
  thm halt_stack = match_mp_rule(
      spec_rule(`p:cm_program`, cm_runtime_stack_halt_initial),
      assume_rule(`cm_typed_program (p:cm_program)`));
  halt_stack = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(initial_regions), sym_rule(initial_fp))), halt_stack);
  thm entered_stack = match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `--1i`, `cm_program_main (p:cm_program)`,
        `[]:(cm_value)list`, initial, `CMIntTy`, `4i`, `0i`, `0i`,
        `0i`, `[CMACursor CAHaltP 0i 0i 0i]:(cm_acursor)list`,
        `[]:(cm_spill)list`, `[]:(cm_spill_frame)list`,
        `[]:(cm_call_sim_frame)list`),
        cm_runtime_stack_enter_call),
      assume_rule(`cm_typed_program (p:cm_program)`)),
      assume_rule(
        `cm_call_ok (p:cm_program) (cm_program_main p)
          ([]:(cm_value)list) ${initial:cm_src_state}`)),
      before), halt_stack);
  thm entered_before = match_mp_rule(specl_rule(TERM_LIST(
      `cm_program_structs (p:cm_program)`,
      `cm_function_params
        (inth (cm_program_main p) (cm_program_functions p))`,
      `cm_state_nextgen ${initial:cm_src_state}`,
      `(cm_state_fp ${initial:cm_src_state} -
        cm_frame_size (cm_program_structs p)
          (inth (cm_program_main p) (cm_program_functions p))) + 8i`,
      `cm_state_regions ${initial:cm_src_state}`),
      cm_regions_for_slots_append_before), before);
  thm structure = specl_rule(TERM_LIST(
      `p:cm_program`, `cm_program_main (p:cm_program)`,
      `[]:(cm_value)list`, initial), cm_enter_call_structure);
  thm structure_before = conj_rule(entered_before,
      entered_stack);
  thm depth = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_call_depth_def(), get_cm_is_call_frame_def(),
        get_theorem_by_name("ILENGTH_DEF"))),
      `cm_call_depth ([CMHaltK]:(cm_frame)list) < 65536i`));
  thm call_ok = assume_rule(
      `cm_call_ok (p:cm_program) (cm_program_main p)
        ([]:(cm_value)list) ${initial:cm_src_state}`);
  thm_list rules = THM_LIST(
      get_cm_step_def(), get_cm_begin_call_def(), call_ok, depth,
      cm_annotation_step_def, cm_update_annotation_def,
      cm_initial_annotation_def, cm_ann_enter_call_def,
      cm_task_runtime_invariant_def,
      cm_ann_cursors_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_ann_calls_def);
  gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(rules));
  reduced = CONV_TAC(reduced, reduce_rewrite_conv(rules));
  thm fp_structure = conjunct1_rule(structure);
  thm nextgen_structure =
      conjunct1_rule(conjunct2_rule(structure));
  thm regions_structure =
      conjunct2_rule(conjunct2_rule(structure));
  gnode normalized = CONV_TAC(reduced, rewrite_conv(THM_LIST(
      fp_structure, nextgen_structure, regions_structure)));
  ACCEPT_TAC(normalized, structure_before);
  return gnode_prove(root);
}
PROOF thm cm_task_runtime_start_step =
    cm_prove_task_runtime_start_step();

PROOF static int cmc_preservation_invariant_transition_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_invariant_transition_axioms_before,
      "cmc_preservation_invariant_transition introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_invariant_transition_checks =
    cmc_preservation_invariant_transition_final_checks();
