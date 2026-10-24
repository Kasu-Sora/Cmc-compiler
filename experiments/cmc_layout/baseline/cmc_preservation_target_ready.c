#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_target_ready.h"
#include "cmc_preservation_invariant_transition.h"
#include "cmc_preservation_spill_safety.h"
#include "cmc_stack_bound.h"
#include "cmc_preservation_generation_step_apply.h"
#include "userlib/proof_patterns.h"

#require "cmc_preservation_target_call_complete.c"
#require "cmc_preservation_invariant_transition.c"
#require "cmc_preservation_spill_safety.c"
#require "cmc_preservation_binding_numeric.c"
#require "cmc_stack_bound.c"
#require "cmc_preservation_generation_step_apply.c"

#require "userlib/proof_patterns.c"
PROOF static size_t _cmc_preservation_target_ready_axioms_before =
    vector_size(get_all_axioms());

PROOF thm cm_call_target_ready_def = new_fun_definition(
    `cm_call_target_ready (p:cm_program) (caller:int) (callee:int)
       (values:(cm_value)list) (st:cm_src_state) (ret:cm_type)
       (returnpc:int) (parent_temp:int) (parent_break:int)
       (parent_continue:int) (cursors:(cm_acursor)list)
       (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
       (calls:(cm_call_sim_frame)list) : bool =
       (tvm_target_valid (cm_model_code p) (cm_function_pc p callee) &&
        cm_function_wf p
          (inth callee (cm_program_functions p)) &&
        cm_frame_segment p callee
          (cm_state_fp st -
            cm_frame_size (cm_program_structs p)
              (inth callee (cm_program_functions p)))
          (cm_state_fp st) &&
        0i <= cm_state_nextgen st &&
        ilength calls < 65536i &&
        ilength values < 65534i &&
        (!addr. cm_live_address st addr ==>
          ~(cm_state_fp st -
              cm_frame_size (cm_program_structs p)
                (inth callee (cm_program_functions p)) <= addr &&
            addr <
              (cm_state_fp st -
                cm_frame_size (cm_program_structs p)
                  (inth callee (cm_program_functions p))) + 8i)) &&
        (!addr. cm_live_address st addr ==>
          ~(8i <= addr && addr < 16i)) &&
        cm_range_disjoint
          (cm_state_fp st -
            cm_frame_size (cm_program_structs p)
              (inth callee (cm_program_functions p)))
          8i 8i 8i &&
        cm_range_disjoint 8i 8i
          (cm_state_fp st -
            cm_frame_size (cm_program_structs p)
              (inth callee (cm_program_functions p)))
          8i &&
        cm_call_frames_store_safe CMIntTy
          (cm_state_fp st -
            cm_frame_size (cm_program_structs p)
              (inth callee (cm_program_functions p)))
          calls &&
        cm_spill_frames_store_safe p CMIntTy
          (cm_state_fp st -
            cm_frame_size (cm_program_structs p)
              (inth callee (cm_program_functions p)))
          (CMSpillFrame caller (cm_state_fp st) spills :: saved) &&
        cm_call_frames_store_safe CMIntTy 8i calls &&
        cm_spill_frames_store_safe p CMIntTy 8i
          (CMSpillFrame caller (cm_state_fp st) spills :: saved) &&
        tower_signed64 (cm_state_fp st) &&
        tower_signed64
          (cm_frame_size (cm_program_structs p)
            (inth callee (cm_program_functions p))) &&
        tower_signed64
          (cm_state_fp st -
            cm_frame_size (cm_program_structs p)
              (inth callee (cm_program_functions p))) &&
        tower_word_valid
          (cm_state_fp st -
            cm_frame_size (cm_program_structs p)
              (inth callee (cm_program_functions p))) &&
        cm_runtime_memory_layout p
          (cm_call_pending_base p callee st)
          (cm_ann_calls
            (cm_ann_enter_call p caller callee st ret returnpc
              parent_temp parent_break parent_continue cursors
              spills saved calls))
          (cm_active_spill_frames callee
            (cm_call_pending_base p callee st)
            (cm_ann_enter_call p caller callee st ret returnpc
              parent_temp parent_break parent_continue cursors
              spills saved calls)))`);
PROOF static int _c_cm_call_target_ready =
    cst_add_const_to_header(`cm_call_target_ready`);

PROOF static thm cm_target_ready_consequence(
    const thm premise, const term conclusion) {
  return mp_rule(taut_rule(mk_imp(concl(premise), conclusion)), premise);
}

PROOF static thm cm_prove_phase_call_frame(void) {
  gnode root = gnode_new_with_ccl(
      `!(phase:cm_aphase).
         cm_is_call_frame (cm_phase_frame phase) ==
         cm_phase_is_call phase`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`phase:cm_aphase`, get_datatype_cases("cm_aphase")),
      "Hphase");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(branch->g);
      int index = labeled_term_list_index(assumptions, "Hphase");
      if (!is_exists(assumptions[index].tm)) break;
      branch = ASMP_EXISTS_TAC(branch, "Hphase", NULL);
    }
    thm shape = assume_rule(
        goal_lasmps(branch->g)[labeled_term_list_index(
          goal_lasmps(branch->g), "Hphase")].tm);
    gnode reduced = CONV_TAC(branch, reduce_rewrite_conv(THM_LIST(
        shape, cm_phase_frame_def, cm_phase_is_call_def,
        get_cm_is_call_frame_def())));
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_phase_call_frame = cm_prove_phase_call_frame();

PROOF static thm cm_prove_runtime_calls_depth(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (all_regions:(cm_region)list)
         (cursors:(cm_acursor)list).
       !(fid:int) (fp:int) (active:(cm_region)list)
         (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         cm_runtime_stack p all_regions fid fp active cursors
           spills saved calls ==>
         ilength calls == cm_call_depth (cm_cursor_frames cursors)`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_regions = GEN_TAC(with_program, "all_regions");
  gnode_list cases = INDUCT_TAC(with_regions,
      `cursors:(cm_acursor)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        cm_runtime_stack_def)), assume_rule(
          `cm_runtime_stack (p:cm_program)
            (all_regions:(cm_region)list) (fid:int) (fp:int)
            (active:(cm_region)list) ([]:(cm_acursor)list)
            (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
            (calls:(cm_call_sim_frame)list)`));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    term phase = `cm_cursor_phase (a0:cm_acursor)`;
    thm stack = assume_rule(
        `cm_runtime_stack (p:cm_program)
          (all_regions:(cm_region)list) (fid:int) (fp:int)
          (active:(cm_region)list)
          ((a0:cm_acursor) :: (a1:(cm_acursor)list))
          (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list)`);
    gnode_list call_cases = BOOL_CASES_TAC(
        leaf, `cm_phase_is_call ${phase:cm_aphase}`, "Hcall");
    thm call_true =
        assume_rule(`cm_phase_is_call ${phase:cm_aphase}`);
    thm call_opened = conv_rule(reduce_rewrite_conv(THM_LIST(
        cm_runtime_stack_def, call_true)), stack);
    thm call_recursive = cm_target_ready_consequence(call_opened,
        `cm_runtime_stack (p:cm_program)
          (all_regions:(cm_region)list)
          (cm_phase_caller ${phase:cm_aphase})
          (cm_phase_oldfp ${phase:cm_aphase})
          (cm_phase_oldregions ${phase:cm_aphase})
          (a1:(cm_acursor)list)
          (cm_spill_frame_spills
            (HD (saved:(cm_spill_frame)list)))
          (TL saved) (TL (calls:(cm_call_sim_frame)list))`);
    thm call_ih =
        assume_rule(goal_lasmps(call_cases[0]->g)[0].tm);
    thm call_depth = match_mp_rule(call_ih, call_recursive);
    thm calls_nonempty = cm_target_ready_consequence(call_opened,
        `~((calls:(cm_call_sim_frame)list) == [])`);
    thm calls_shape = mp_rule(
        ispec_rule(`calls:(cm_call_sim_frame)list`,
          get_theorem_by_name("CONS_HD_TL")), calls_nonempty);
    thm calls_length = conv_rule(rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))), beta_norm(ap_term_rule(
          `\xs:(cm_call_sim_frame)list. ilength xs`, calls_shape)));
    thm depth_lifted = beta_norm(ap_term_rule(
        `\n:int. 1i + n`, call_depth));
    thm call_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        cm_cursor_frames_def, get_cm_call_depth_def(),
        cm_phase_call_frame, call_true)), goal_ccl(call_cases[0]->g));
    ACCEPT_TAC(call_cases[0], eq_mp_rule(sym_rule(call_view),
        trans_rule(calls_length, depth_lifted)));

    thm call_false =
        assume_rule(`~cm_phase_is_call ${phase:cm_aphase}`);
    gnode_list scope_cases = BOOL_CASES_TAC(call_cases[1],
        `cm_phase_is_scope ${phase:cm_aphase}`, "Hscope");
    thm scope_true =
        assume_rule(`cm_phase_is_scope ${phase:cm_aphase}`);
    thm scope_opened = conv_rule(reduce_rewrite_conv(THM_LIST(
        cm_runtime_stack_def, call_false, scope_true)), stack);
    thm scope_recursive = cm_target_ready_consequence(scope_opened,
        `cm_runtime_stack (p:cm_program)
          (all_regions:(cm_region)list) (fid:int) (fp:int)
          (cm_phase_oldregions ${phase:cm_aphase})
          (a1:(cm_acursor)list) (spills:(cm_spill)list)
          (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list)`);
    thm scope_ih =
        assume_rule(goal_lasmps(scope_cases[0]->g)[0].tm);
    thm scope_depth = match_mp_rule(scope_ih, scope_recursive);
    gnode scope_closed = CONV_TAC(scope_cases[0],
        reduce_rewrite_conv(THM_LIST(
          cm_cursor_frames_def, get_cm_call_depth_def(),
          cm_phase_call_frame, call_false, scope_depth,
          int_arith_rule(`!(x:int). x == 0i + x`))));
    ENSURE_COND(!IS_NULL(scope_closed->solved),
        "call-depth scope case remains open: %s", cstr_gnode(scope_closed));

    thm scope_false =
        assume_rule(`~cm_phase_is_scope ${phase:cm_aphase}`);
    gnode_list halt_cases = BOOL_CASES_TAC(scope_cases[1],
        `cm_phase_is_halt ${phase:cm_aphase}`, "Hhalt");
    thm halt_true =
        assume_rule(`cm_phase_is_halt ${phase:cm_aphase}`);
    thm halt_opened = conv_rule(reduce_rewrite_conv(THM_LIST(
        cm_runtime_stack_def, call_false, scope_false, halt_true)), stack);
    thm tail_nil = cm_target_ready_consequence(
        halt_opened, `(a1:(cm_acursor)list) == []`);
    thm calls_nil = cm_target_ready_consequence(
        halt_opened, `(calls:(cm_call_sim_frame)list) == []`);
    gnode halt_closed = CONV_TAC(halt_cases[0],
        reduce_rewrite_conv(THM_LIST(
          cm_cursor_frames_def, get_cm_call_depth_def(),
          cm_phase_call_frame, call_false, tail_nil, calls_nil,
          get_theorem_by_name("ILENGTH_DEF"),
          int_arith_rule(`!(x:int). x == 0i + x`))));
    ENSURE_COND(!IS_NULL(halt_closed->solved),
        "call-depth halt case remains open: %s", cstr_gnode(halt_closed));

    thm halt_false =
        assume_rule(`~cm_phase_is_halt ${phase:cm_aphase}`);
    thm plain_opened = conv_rule(reduce_rewrite_conv(THM_LIST(
        cm_runtime_stack_def, call_false, scope_false, halt_false)), stack);
    thm plain_recursive = cm_target_ready_consequence(plain_opened,
        `cm_runtime_stack (p:cm_program)
          (all_regions:(cm_region)list) (fid:int) (fp:int)
          (active:(cm_region)list) (a1:(cm_acursor)list)
          (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list)`);
    thm plain_ih =
        assume_rule(goal_lasmps(halt_cases[1]->g)[0].tm);
    thm plain_depth = match_mp_rule(plain_ih, plain_recursive);
    gnode plain_closed = CONV_TAC(halt_cases[1],
        reduce_rewrite_conv(THM_LIST(
          cm_cursor_frames_def, get_cm_call_depth_def(),
          cm_phase_call_frame, call_false, plain_depth,
          int_arith_rule(`!(x:int). x == 0i + x`))));
    ENSURE_COND(!IS_NULL(plain_closed->solved),
        "call-depth plain case remains open: %s", cstr_gnode(plain_closed));
  }
  return gnode_prove(root);
err:
  return empty_theorem;
}
PROOF thm cm_runtime_calls_depth = cm_prove_runtime_calls_depth();

PROOF static thm cm_prove_function_pc_valid(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (callee:int).
         cm_wf_program p ==>
         0i <= callee ==>
         callee < ilength (cm_program_functions p) ==>
         tvm_target_valid (cm_model_code p)
           (cm_function_pc p callee)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm wf = assume_rule(`cm_wf_program (p:cm_program)`);
  thm callee_nonnegative = assume_rule(`0i <= (callee:int)`);
  thm callee_upper =
      assume_rule(`(callee:int) < ilength (cm_program_functions p)`);
  thm function_at = match_mp_rule(
      specl_rule(TERM_LIST(`p:cm_program`, `callee:int`),
        get_cm_model_function_at()),
      conj_rule(callee_nonnegative, callee_upper));
  thm normalized_at = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_emit_function_def(), get_cm_emit_prologue_def(),
      get_theorem_by_name("APPEND"))), function_at);
  thm head = match_mp_rule(get_cm_code_at_head(), normalized_at);
  thm bounds = conj_rule(conjunct1_rule(head),
      conjunct1_rule(conjunct2_rule(head)));
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_tvm_target_valid_def())), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), bounds));
  return gnode_prove(root);
}
PROOF static thm cm_function_pc_valid =
    cm_prove_function_pc_valid();

PROOF static thm cm_prove_call_frame_outside_live(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) caller callee values st
         cursors spills saved calls addr.
         cm_runtime_stack p (cm_state_regions st) caller
           (cm_state_fp st) (cm_state_regions st)
           cursors spills saved calls ==>
         cm_call_ok p callee values st ==>
         cm_live_address st addr ==>
         ~(cm_state_fp st - cm_frame_size (cm_program_structs p)
             (inth callee (cm_program_functions p)) <= addr &&
           addr <
             (cm_state_fp st - cm_frame_size (cm_program_structs p)
               (inth callee (cm_program_functions p))) + 8i)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm stack = assume_rule(
      `cm_runtime_stack (p:cm_program)
        (cm_state_regions (st:cm_src_state)) (caller:int)
        (cm_state_fp st) (cm_state_regions st)
        (cursors:(cm_acursor)list) (spills:(cm_spill)list)
        (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`);
  thm call_ok =
      assume_rule(`cm_call_ok p (callee:int) (values:(cm_value)list) st`);
  thm live =
      assume_rule(`cm_live_address (st:cm_src_state) (addr:int)`);
  thm live_exists = eq_mp_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_live_address_def)), concl(live)), live);
  thm call_opened = conv_rule(
      rewrite_conv(THM_LIST(get_cm_call_ok_def())), call_ok);
  thm member_body = assume_rule(
      `MEM (region:cm_region) (cm_state_regions (st:cm_src_state)) &&
       cm_region_live region &&
       cm_region_base (cm_state_regions st) (cm_region_gen region) +
           cm_region_lo region <= (addr:int) &&
       addr < cm_region_base (cm_state_regions st)
           (cm_region_gen region) + cm_region_hi region`);
  thm region_bounds = match_mp_rule(
      match_mp_rule(
        match_mp_rule(
          specl_rule(TERM_LIST(
              `p:cm_program`, `cm_state_regions (st:cm_src_state)`,
              `cursors:(cm_acursor)list`, `caller:int`,
              `cm_state_fp (st:cm_src_state)`,
              `cm_state_regions (st:cm_src_state)`,
              `spills:(cm_spill)list`, `saved:(cm_spill_frame)list`,
              `calls:(cm_call_sim_frame)list`,
              `region:cm_region`),
            cm_runtime_stack_region_bounds),
          stack),
        conjunct1_rule(member_body)),
      conjunct1_rule(conjunct2_rule(member_body)));
  thm inside = assume_rule(
      `cm_state_fp (st:cm_src_state) -
          cm_frame_size (cm_program_structs (p:cm_program))
            (inth (callee:int) (cm_program_functions p)) <=
        (addr:int) &&
       addr < cm_state_fp st -
          cm_frame_size (cm_program_structs p)
            (inth callee (cm_program_functions p)) + 8i`);
  thm facts = conj_rule(call_opened,
      conj_rule(region_bounds, conj_rule(member_body, inside)));
  thm outside = mp_rule(int_arith_rule(mk_imp(
      concl(facts), goal_ccl(leaf->g))), facts);
  ACCEPT_TAC(leaf, choose_rule(`region:cm_region`,
      live_exists, outside));
  return gnode_prove(root);
}
PROOF static thm cm_call_frame_outside_live =
    cm_prove_call_frame_outside_live();

PROOF static thm cm_prove_scratch_outside_live(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) caller st cursors spills saved calls addr.
         cm_runtime_stack p (cm_state_regions st) caller
           (cm_state_fp st) (cm_state_regions st)
           cursors spills saved calls ==>
         cm_live_address st addr ==>
         ~(8i <= addr && addr < 16i)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm stack = assume_rule(
      `cm_runtime_stack (p:cm_program)
        (cm_state_regions (st:cm_src_state)) (caller:int)
        (cm_state_fp st) (cm_state_regions st)
        (cursors:(cm_acursor)list) (spills:(cm_spill)list)
        (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`);
  thm live =
      assume_rule(`cm_live_address (st:cm_src_state) (addr:int)`);
  thm live_exists = eq_mp_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_live_address_def)), concl(live)), live);
  thm member_body = assume_rule(
      `MEM (region:cm_region) (cm_state_regions (st:cm_src_state)) &&
       cm_region_live region &&
       cm_region_base (cm_state_regions st) (cm_region_gen region) +
           cm_region_lo region <= (addr:int) &&
       addr < cm_region_base (cm_state_regions st)
           (cm_region_gen region) + cm_region_hi region`);
  thm region_bounds = match_mp_rule(
      match_mp_rule(
        match_mp_rule(
          specl_rule(TERM_LIST(
              `p:cm_program`, `cm_state_regions (st:cm_src_state)`,
              `cursors:(cm_acursor)list`, `caller:int`,
              `cm_state_fp (st:cm_src_state)`,
              `cm_state_regions (st:cm_src_state)`,
              `spills:(cm_spill)list`, `saved:(cm_spill_frame)list`,
              `calls:(cm_call_sim_frame)list`, `region:cm_region`),
            cm_runtime_stack_region_bounds),
          stack),
        conjunct1_rule(member_body)),
      conjunct1_rule(conjunct2_rule(member_body)));
  thm inside = assume_rule(`8i <= (addr:int) && addr < 16i`);
  thm facts = conj_rule(region_bounds, conj_rule(member_body, inside));
  thm outside = mp_rule(int_arith_rule(mk_imp(
      concl(facts), goal_ccl(leaf->g))), facts);
  ACCEPT_TAC(leaf, choose_rule(`region:cm_region`,
      live_exists, outside));
  return gnode_prove(root);
}
PROOF static thm cm_scratch_outside_live =
    cm_prove_scratch_outside_live();

PROOF static thm cm_prove_call_metadata_safe(void) {
  term frame_bytes =
      `cm_frame_size (cm_program_structs (p:cm_program))
        (inth (callee:int) (cm_program_functions p))`;
  term frame_base =
      `cm_state_fp (st:cm_src_state) - ${frame_bytes:int}`;
  term active =
      `(CMSpillFrame (caller:int) (cm_state_fp (st:cm_src_state))
          (spills:(cm_spill)list)) :: (saved:(cm_spill_frame)list)`;
  term body = imp_chain(TERM_LIST(
      `cm_runtime_stack (p:cm_program) (cm_state_regions st)
        (caller:int) (cm_state_fp (st:cm_src_state))
        (cm_state_regions st) (cursors:(cm_acursor)list)
        (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`,
      `cm_call_ok p (callee:int) (values:(cm_value)list) st`),
      list_mk_conj(TERM_LIST(
        `cm_call_frames_store_safe CMIntTy ${frame_base:int} calls`,
        `cm_spill_frames_store_safe p CMIntTy ${frame_base:int}
          ${active:(cm_spill_frame)list}`,
        `cm_call_frames_store_safe CMIntTy 8i calls`,
        `cm_spill_frames_store_safe p CMIntTy 8i
          ${active:(cm_spill_frame)list}`)));
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm stack = assume_rule(
      `cm_runtime_stack (p:cm_program) (cm_state_regions st)
        (caller:int) (cm_state_fp (st:cm_src_state))
        (cm_state_regions st) (cursors:(cm_acursor)list)
        (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`);
  thm call_ok =
      assume_rule(`cm_call_ok p (callee:int) (values:(cm_value)list) st`);
  thm call_opened = conv_rule(
      rewrite_conv(THM_LIST(get_cm_call_ok_def())), call_ok);
  thm lower = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `cm_state_regions (st:cm_src_state)`,
      `cursors:(cm_acursor)list`, `caller:int`,
      `cm_state_fp (st:cm_src_state)`,
      `cm_state_regions (st:cm_src_state)`,
      `spills:(cm_spill)list`, `saved:(cm_spill_frame)list`,
      `calls:(cm_call_sim_frame)list`), cm_runtime_stack_lower), stack);
  thm active_lower_raw = conj_rule(
      conjunct1_rule(conjunct2_rule(lower)),
      conjunct2_rule(conjunct2_rule(lower)));
  thm active_lower_view = apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_spill_frames_lower_def, cm_spill_frame_fid_def,
        cm_spill_frame_fp_def, cm_spill_frame_spills_def)),
      `cm_spill_frames_lower (p:cm_program)
        (cm_state_fp (st:cm_src_state))
        ${active:(cm_spill_frame)list}`);
  thm active_lower =
      eq_mp_rule(sym_rule(active_lower_view), active_lower_raw);
  thm fp_bounds = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `cm_state_regions (st:cm_src_state)`,
      `cursors:(cm_acursor)list`, `caller:int`,
      `cm_state_fp (st:cm_src_state)`,
      `cm_state_regions (st:cm_src_state)`,
      `spills:(cm_spill)list`, `saved:(cm_spill_frame)list`,
      `calls:(cm_call_sim_frame)list`), cm_runtime_stack_fp_bounds), stack);
  thm frame_before_fp = mp_rule(int_arith_rule(mk_imp(
      concl(call_opened),
      `${frame_base:int} + 8i <= cm_state_fp (st:cm_src_state)`)),
      call_opened);
  thm scratch_before_fp = mp_rule(int_arith_rule(mk_imp(
      concl(fp_bounds), `8i + 8i <= cm_state_fp (st:cm_src_state)`)),
      fp_bounds);
  thm frame_call_range = match_mp_rule(
      match_mp_rule(specl_rule(TERM_LIST(
        frame_base, `8i`, `cm_state_fp (st:cm_src_state)`,
        `calls:(cm_call_sim_frame)list`), cm_call_lower_range_safe),
        frame_before_fp),
      conjunct1_rule(lower));
  thm frame_spill_range = match_mp_rule(
      match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, frame_base, `8i`,
        `cm_state_fp (st:cm_src_state)`,
        active), cm_spill_frames_lower_range_safe),
        frame_before_fp),
      active_lower);
  thm scratch_call_range = match_mp_rule(
      match_mp_rule(specl_rule(TERM_LIST(
        `8i`, `8i`, `cm_state_fp (st:cm_src_state)`,
        `calls:(cm_call_sim_frame)list`), cm_call_lower_range_safe),
        scratch_before_fp),
      conjunct1_rule(lower));
  thm scratch_spill_range = match_mp_rule(
      match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `8i`, `8i`,
        `cm_state_fp (st:cm_src_state)`,
        active), cm_spill_frames_lower_range_safe),
        scratch_before_fp),
      active_lower);
  thm frame_store_upper = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_store_width_def(), get_cm_type_int_char_distinct(),
        int_arith_rule(`!(x:int). x + 8i <= x + 8i`))),
      `${frame_base:int} + cm_store_width CMIntTy <=
        ${frame_base:int} + 8i`));
  thm scratch_store_upper = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_store_width_def(), get_cm_type_int_char_distinct(),
        int_arith_rule(`!(x:int). x + 8i <= x + 8i`))),
      `8i + cm_store_width CMIntTy <= 8i + 8i`));
  thm frame_call_store = match_mp_rule(
      match_mp_rule(
        match_mp_rule(specl_rule(TERM_LIST(
          frame_base, `8i`, frame_base, `CMIntTy:cm_type`,
          `calls:(cm_call_sim_frame)list`),
          cm_call_frames_range_subrange),
          int_arith_rule(`(${frame_base:int}) <= ${frame_base:int}`)),
        frame_store_upper),
      frame_call_range);
  thm frame_spill_store = match_mp_rule(
      match_mp_rule(
        match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, frame_base, `8i`, frame_base,
          `CMIntTy:cm_type`, active),
          cm_spill_frames_range_subrange),
          int_arith_rule(`(${frame_base:int}) <= ${frame_base:int}`)),
        frame_store_upper),
      frame_spill_range);
  thm scratch_call_store = match_mp_rule(
      match_mp_rule(
        match_mp_rule(specl_rule(TERM_LIST(
          `8i`, `8i`, `8i`, `CMIntTy:cm_type`,
          `calls:(cm_call_sim_frame)list`),
          cm_call_frames_range_subrange),
          int_arith_rule(`8i <= 8i`)),
        scratch_store_upper),
      scratch_call_range);
  thm scratch_spill_store = match_mp_rule(
      match_mp_rule(
        match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `8i`, `8i`, `8i`,
          `CMIntTy:cm_type`, active),
          cm_spill_frames_range_subrange),
          int_arith_rule(`8i <= 8i`)),
        scratch_store_upper),
      scratch_spill_range);
  ACCEPT_TAC(leaf, conj_rule(frame_call_store,
      conj_rule(frame_spill_store,
        conj_rule(scratch_call_store, scratch_spill_store))));
  return gnode_prove(root);
}
PROOF static thm cm_call_metadata_safe =
    cm_prove_call_metadata_safe();

PROOF static thm cm_prove_call_pending_layout(void) {
  term pending =
      `cm_call_pending_base (p:cm_program) (callee:int)
        (st:cm_src_state)`;
  term entered =
      `cm_ann_enter_call (p:cm_program) (caller:int) (callee:int)
        (st:cm_src_state) (ret:cm_type) (returnpc:int)
        (parent_temp:int) (parent_break:int) (parent_continue:int)
        (cursors:(cm_acursor)list) (spills:(cm_spill)list)
        (saved:(cm_spill_frame)list) (calls:(cm_call_sim_frame)list)`;
  term target =
      `cm_runtime_memory_layout (p:cm_program) ${pending:cm_src_state}
        (cm_ann_calls ${entered:cm_annotation})
        (cm_active_spill_frames (callee:int) ${pending:cm_src_state}
          ${entered:cm_annotation})`;
  term body = imp_chain(TERM_LIST(
      `cm_typed_program (p:cm_program)`,
      `cm_call_ok p (callee:int) (values:(cm_value)list)
        (st:cm_src_state)`,
      `cm_regions_before (cm_state_regions st)
        (cm_state_nextgen st)`,
      `cm_runtime_stack p (cm_state_regions st) (caller:int)
        (cm_state_fp st) (cm_state_regions st)
        (cursors:(cm_acursor)list) (spills:(cm_spill)list)
        (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`), target);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm entered_stack = specl_rule(TERM_LIST(
      `p:cm_program`, `caller:int`, `callee:int`,
      `values:(cm_value)list`, `st:cm_src_state`, `ret:cm_type`,
      `returnpc:int`, `parent_temp:int`, `parent_break:int`,
      `parent_continue:int`, `cursors:(cm_acursor)list`,
      `spills:(cm_spill)list`, `saved:(cm_spill_frame)list`,
      `calls:(cm_call_sim_frame)list`), cm_runtime_stack_enter_call);
  entered_stack = match_mp_rule(entered_stack,
      assume_rule(`cm_typed_program (p:cm_program)`));
  entered_stack = match_mp_rule(entered_stack,
      assume_rule(`cm_call_ok p (callee:int) (values:(cm_value)list)
        (st:cm_src_state)`));
  entered_stack = match_mp_rule(entered_stack,
      assume_rule(`cm_regions_before (cm_state_regions st)
        (cm_state_nextgen st)`));
  entered_stack = match_mp_rule(entered_stack,
      assume_rule(
        `cm_runtime_stack p (cm_state_regions st) (caller:int)
          (cm_state_fp st) (cm_state_regions st)
          (cursors:(cm_acursor)list) (spills:(cm_spill)list)
          (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list)`));
  thm layout_rule = specl_rule(TERM_LIST(
      `p:cm_program`, pending, `callee:int`,
      `cm_ann_cursors ${entered:cm_annotation}`,
      `cm_ann_spills ${entered:cm_annotation}`,
      `cm_ann_saved ${entered:cm_annotation}`,
      `cm_ann_calls ${entered:cm_annotation}`),
      cm_runtime_stack_memory_layout);
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, get_cm_call_pending_base_def());
  vector_add(&rules, cm_ann_enter_call_def);
  vector_add(&rules, cm_ann_cursors_def);
  vector_add(&rules, cm_ann_spills_def);
  vector_add(&rules, cm_ann_saved_def);
  vector_add(&rules, cm_ann_calls_def);
  vector_add(&rules, cm_active_spill_frames_def);
  vector_add(&rules, cm_spill_frame_fid_def);
  vector_add(&rules, cm_spill_frame_fp_def);
  vector_add(&rules, cm_spill_frame_spills_def);
  thm normalized_rule =
      conv_rule(reduce_rewrite_conv(rules), layout_rule);
  thm normalized_layout =
      match_mp_rule(normalized_rule, entered_stack);
  thm target_view =
      apply_conversion(reduce_rewrite_conv(rules), target);
  ACCEPT_TAC(leaf,
      eq_mp_rule(sym_rule(target_view), normalized_layout));
  return gnode_prove(root);
}
PROOF static thm cm_call_pending_layout =
    cm_prove_call_pending_layout();

PROOF static thm cm_prove_target_call_ready(void) {
  term frame_bytes =
      `cm_frame_size (cm_program_structs (p:cm_program))
        (inth (callee:int) (cm_program_functions p))`;
  term frame_base =
      `cm_state_fp (st:cm_src_state) - ${frame_bytes:int}`;
  term target =
      `cm_call_target_ready (p:cm_program) (caller:int) (callee:int)
        (values:(cm_value)list) (st:cm_src_state) (ret:cm_type)
        (returnpc:int) (parent_temp:int) (parent_break:int)
        (parent_continue:int) (cursors:(cm_acursor)list)
        (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`;
  term body = imp_chain(TERM_LIST(
      `cm_wf_program (p:cm_program)`,
      `cm_state_generation_below p (caller:int) (st:cm_src_state)`,
      `cm_call_ok p (callee:int) (values:(cm_value)list) st`,
      `cm_call_depth (cm_cursor_frames (cursors:(cm_acursor)list)) <
        65536i`,
      `cm_regions_before (cm_state_regions st)
        (cm_state_nextgen st)`,
      `cm_runtime_stack p (cm_state_regions st) caller
        (cm_state_fp st) (cm_state_regions st) cursors
        (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`), target);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm wf = assume_rule(`cm_wf_program (p:cm_program)`);
  thm wf_opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_wf_program_def(), get_cm_codegen_admissible_def())), wf);
  thm typed = cm_target_ready_consequence(
      wf_opened, `cm_typed_program (p:cm_program)`);
  thm typed_opened = conv_rule(
      rewrite_conv(THM_LIST(get_cm_typed_program_def())), typed);
  thm call_ok =
      assume_rule(`cm_call_ok p (callee:int) (values:(cm_value)list) st`);
  thm call_opened = conv_rule(
      rewrite_conv(THM_LIST(get_cm_call_ok_def())), call_ok);
  thm callee_nonnegative = cm_target_ready_consequence(
      call_opened, `0i <= (callee:int)`);
  thm callee_upper = cm_target_ready_consequence(
      call_opened,
      `(callee:int) < ilength (cm_program_functions (p:cm_program))`);
  thm callee_bounds =
      conj_rule(callee_nonnegative, callee_upper);
  thm target_valid = match_mp_rule(
      match_mp_rule(
        match_mp_rule(specl_rule(TERM_LIST(
            `p:cm_program`, `callee:int`), cm_function_pc_valid), wf),
        callee_nonnegative),
      callee_upper);
  thm function_rule = spec_rule(`callee:int`,
      cm_target_ready_consequence(typed_opened,
        `!(i:int). 0i <= i ==>
          i < ilength (cm_program_functions (p:cm_program)) ==>
          cm_function_wf p (inth i (cm_program_functions p))`));
  thm function_wf = match_mp_rule(
      match_mp_rule(function_rule, callee_nonnegative), callee_upper);
  thm frame_segment = match_mp_rule(
      match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `callee:int`, `values:(cm_value)list`,
        `st:cm_src_state`), cm_call_frame_segment), typed), call_ok);
  thm nextgen_positive = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `caller:int`, `st:cm_src_state`),
      cm_state_nextgen_positive), assume_rule(
        `cm_state_generation_below (p:cm_program) (caller:int)
          (st:cm_src_state)`));
  thm nextgen_nonnegative = mp_rule(int_arith_rule(
      `0i < cm_state_nextgen (st:cm_src_state) ==>
       0i <= cm_state_nextgen st`), nextgen_positive);
  thm stack = assume_rule(
      `cm_runtime_stack (p:cm_program) (cm_state_regions st)
        (caller:int) (cm_state_fp st) (cm_state_regions st)
        (cursors:(cm_acursor)list) (spills:(cm_spill)list)
        (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`);
  thm calls_depth = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `cm_state_regions (st:cm_src_state)`,
      `cursors:(cm_acursor)list`, `caller:int`,
      `cm_state_fp (st:cm_src_state)`,
      `cm_state_regions (st:cm_src_state)`,
      `spills:(cm_spill)list`, `saved:(cm_spill_frame)list`,
      `calls:(cm_call_sim_frame)list`), cm_runtime_calls_depth), stack);
  thm source_depth = assume_rule(
      `cm_call_depth (cm_cursor_frames (cursors:(cm_acursor)list)) <
        65536i`);
  thm calls_capacity = mp_rule(int_arith_rule(mk_imp(
      concl(conj_rule(calls_depth, source_depth)),
      `ilength (calls:(cm_call_sim_frame)list) < 65536i`)),
      conj_rule(calls_depth, source_depth));
  thm arity_max = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `callee:int`), cm_function_arity_le_max),
      callee_bounds);
  thm stack_upper = conv_rule(rewrite_conv(THM_LIST(
      get_cm_stack_bound_model_def())),
      cm_target_ready_consequence(wf_opened,
        `cm_stack_bound_model (p:cm_program) <= 65536i`));
  thm values_capacity_facts =
      conj_rule(call_opened, conj_rule(arity_max, stack_upper));
  thm values_capacity = mp_rule(int_arith_rule(mk_imp(
      concl(values_capacity_facts),
      `ilength (values:(cm_value)list) < 65534i`)),
      values_capacity_facts);
  thm outside_frame = match_mp_rule(
      match_mp_rule(cm_call_frame_outside_live, stack), call_ok);
  thm outside_scratch =
      match_mp_rule(cm_scratch_outside_live, stack);
  thm disjoint_facts = conj_rule(call_opened, typed_opened);
  thm left_disjoint_raw = mp_rule(int_arith_rule(mk_imp(
      concl(disjoint_facts),
      `(${frame_base:int}) + 8i <= 8i ||
       8i + 8i <= ${frame_base:int}`)), disjoint_facts);
  thm right_disjoint_raw = mp_rule(int_arith_rule(mk_imp(
      concl(disjoint_facts),
      `8i + 8i <= ${frame_base:int} ||
       (${frame_base:int}) + 8i <= 8i`)), disjoint_facts);
  thm left_disjoint = eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_range_disjoint_def)),
      `cm_range_disjoint ${frame_base:int} 8i 8i 8i`)),
      left_disjoint_raw);
  thm right_disjoint = eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_range_disjoint_def)),
      `cm_range_disjoint 8i 8i ${frame_base:int} 8i`)),
      right_disjoint_raw);
  thm metadata =
      match_mp_rule(match_mp_rule(cm_call_metadata_safe, stack), call_ok);
  thm fp_bounds = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `cm_state_regions (st:cm_src_state)`,
      `cursors:(cm_acursor)list`, `caller:int`,
      `cm_state_fp (st:cm_src_state)`,
      `cm_state_regions (st:cm_src_state)`,
      `spills:(cm_spill)list`, `saved:(cm_spill_frame)list`,
      `calls:(cm_call_sim_frame)list`),
      cm_runtime_stack_fp_bounds), stack);
  thm function_opened = conv_rule(
      rewrite_conv(THM_LIST(get_cm_function_wf_def())), function_wf);
  thm fp_signed_raw = mp_rule(int_arith_rule(mk_imp(
      concl(fp_bounds),
      `--9223372036854775808i <= cm_state_fp (st:cm_src_state) &&
       cm_state_fp st <= 9223372036854775807i`)), fp_bounds);
  thm frame_signed_raw = mp_rule(int_arith_rule(mk_imp(
      concl(function_opened),
      `--9223372036854775808i <= ${frame_bytes:int} &&
       ${frame_bytes:int} <= 9223372036854775807i`)), function_opened);
  thm base_signed_raw = mp_rule(int_arith_rule(mk_imp(
      concl(disjoint_facts),
      `--9223372036854775808i <= ${frame_base:int} &&
       ${frame_base:int} <= 9223372036854775807i`)), disjoint_facts);
  thm fp_signed = eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(get_tower_signed64_def())),
      `tower_signed64 (cm_state_fp (st:cm_src_state))`)),
      fp_signed_raw);
  thm frame_signed = eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(get_tower_signed64_def())),
      `tower_signed64 ${frame_bytes:int}`)), frame_signed_raw);
  thm base_signed = eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(get_tower_signed64_def())),
      `tower_signed64 ${frame_base:int}`)), base_signed_raw);
  thm base_word = cm_target_ready_consequence(
      call_opened, `tower_word_valid ${frame_base:int}`);
  thm pending_layout = match_mp_rule(
      match_mp_rule(
        match_mp_rule(
          match_mp_rule(cm_call_pending_layout, typed), call_ok),
        assume_rule(`cm_regions_before
          (cm_state_regions (st:cm_src_state))
          (cm_state_nextgen st)`)),
      stack);
  pending_layout = spec_rule(`ret:cm_type`, pending_layout);
  pending_layout = spec_rule(`returnpc:int`, pending_layout);
  pending_layout = spec_rule(`parent_temp:int`, pending_layout);
  pending_layout = spec_rule(`parent_break:int`, pending_layout);
  pending_layout = spec_rule(`parent_continue:int`, pending_layout);
  thm opened_target = list_conj_rule(THM_LIST(
      target_valid, function_wf, frame_segment, nextgen_nonnegative,
      calls_capacity, values_capacity, outside_frame, outside_scratch,
      left_disjoint, right_disjoint,
      conjunct1_rule(metadata),
      conjunct1_rule(conjunct2_rule(metadata)),
      conjunct1_rule(conjunct2_rule(conjunct2_rule(metadata))),
      conjunct2_rule(conjunct2_rule(conjunct2_rule(metadata))),
      fp_signed, frame_signed, base_signed, base_word, pending_layout));
  thm target_view = apply_conversion(
      rewrite_conv(THM_LIST(cm_call_target_ready_def)), target);
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), opened_target));
  return gnode_prove(root);
}
PROOF thm cm_target_call_ready =
    cm_prove_target_call_ready();

PROOF thm get_cm_function_arity_le_max(void) {
  return cm_function_arity_le_max;
}
PROOF thm get_cm_runtime_calls_depth(void) {
  return cm_runtime_calls_depth;
}
PROOF thm get_cm_target_call_ready(void) {
  return cm_target_call_ready;
}
PROOF thm get_cm_scratch_outside_live(void) {
  return cm_scratch_outside_live;
}


PROOF static int cmc_preservation_target_ready_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_ready_axioms_before,
      "cmc_preservation_target_ready introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_runtime_calls_depth)) == 0,
      "runtime call-depth theorem has hypotheses");
  ENSURE_COND(vector_size(hyp(cm_target_call_ready)) == 0,
      "target call-readiness theorem has hypotheses");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_ready_checks =
    cmc_preservation_target_ready_final_checks();
