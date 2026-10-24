#include "proof/proof.h"
#include "userlib/proof.h"
#include "cmc_preservation_binding_numeric.h"
#include "cmc_codegen.h"

#require "cmc_preservation_invariant_frame.c"
#require "cmc_codegen.c"

PROOF static size_t _cmc_preservation_binding_numeric_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_binding_numeric_consequence(
    const thm premise, const term conclusion) {
  return mp_rule(taut_rule(mk_imp(concl(premise), conclusion)), premise);
}

PROOF static thm cm_prove_binding_offset_signed(const bool is_local) {
  term function =
      `inth (fid:int) (cm_program_functions (p:cm_program))`;
  term structs = `cm_program_structs (p:cm_program)`;
  term params = `cm_function_params ${function:cm_function_d}`;
  term locals = `cm_function_locals ${function:cm_function_d}`;
  term slots = is_local ? locals : params;
  term prefix =
      `cm_slots_prefix ${structs:(cm_struct_d)list}
        ${slots:(cm_slot_d)list} (slot:int)`;
  term slot_size =
      `cm_slot_size ${structs:(cm_struct_d)list}
        (inth (slot:int) ${slots:(cm_slot_d)list})`;
  term params_size =
      `cm_slots_size ${structs:(cm_struct_d)list}
        ${params:(cm_slot_d)list}`;
  term locals_size =
      `cm_slots_size ${structs:(cm_struct_d)list}
        ${locals:(cm_slot_d)list}`;
  term offset = is_local
      ? `cm_local_offset (p:cm_program) (fid:int) (slot:int)`
      : `cm_param_offset (p:cm_program) (fid:int) (slot:int)`;
  term body = imp_chain(TERM_LIST(
      `cm_function_wf (p:cm_program) ${function:cm_function_d}`,
      `0i <= (slot:int)`,
      `(slot:int) < ilength ${slots:(cm_slot_d)list}`),
      `tower_signed64 ${offset:int}`);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);

  thm function_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_function_wf_def())), assume_rule(
        `cm_function_wf (p:cm_program) ${function:cm_function_d}`));
  thm params_wf = cm_binding_numeric_consequence(function_open,
      `cm_params_wf ${structs:(cm_struct_d)list}
        ${params:(cm_slot_d)list}`);
  thm params_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_params_wf_def())), params_wf);
  thm params_slots_wf = conjunct1_rule(params_open);
  thm locals_slots_wf = cm_binding_numeric_consequence(function_open,
      `cm_slots_wf ${structs:(cm_struct_d)list}
        ${locals:(cm_slot_d)list}`);
  thm selected_slots_wf = is_local ? locals_slots_wf : params_slots_wf;

  thm params_positive = match_mp_rule(ispecl_rule(TERM_LIST(
      structs, params), cm_slots_wf_sizes_positive), params_slots_wf);
  thm locals_positive = match_mp_rule(ispecl_rule(TERM_LIST(
      structs, locals), cm_slots_wf_sizes_positive), locals_slots_wf);
  thm selected_positive = is_local ? locals_positive : params_positive;
  thm params_nonnegative = match_mp_rule(ispecl_rule(TERM_LIST(
      structs, params), cm_slot_sizes_positive_total), params_positive);
  thm locals_nonnegative = match_mp_rule(ispecl_rule(TERM_LIST(
      structs, locals), cm_slot_sizes_positive_total), locals_positive);
  thm prefix_bounds = match_mp_rule(match_mp_rule(
      spec_rule(`slot:int`, match_mp_rule(ispecl_rule(TERM_LIST(
        structs, slots), cm_slots_prefix_cell_bounds), selected_positive)),
      assume_rule(`0i <= (slot:int)`)),
      assume_rule(`(slot:int) < ilength ${slots:(cm_slot_d)list}`));
  thm prefix_nonnegative = conjunct1_rule(prefix_bounds);
  thm cell_upper = conjunct2_rule(prefix_bounds);

  thm selected_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_slots_wf_def())), selected_slots_wf);
  thm slot_wf = match_mp_rule(match_mp_rule(
      spec_rule(`slot:int`, selected_open),
      assume_rule(`0i <= (slot:int)`)),
      assume_rule(`(slot:int) < ilength ${slots:(cm_slot_d)list}`));
  thm slot_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_slot_wf_def())), slot_wf);
  thm slot_positive = cm_binding_numeric_consequence(
      slot_open, `0i < ${slot_size:int}`);
  thm temp_nonnegative = cm_binding_numeric_consequence(function_open,
      `0i <= cm_temp_slots ${function:cm_function_d}`);
  term frame_size =
      `cm_frame_size ${structs:(cm_struct_d)list}
        ${function:cm_function_d}`;
  thm frame_upper = cm_binding_numeric_consequence(function_open,
      `${frame_size:int} <= 1048560i`);
  thm frame_upper_raw = conv_rule(rewrite_conv(THM_LIST(
      get_cm_frame_size_def())), frame_upper);

  term lower_raw_term = is_local
      ? `0i <= 8i + ${params_size:int} + ${prefix:int}`
      : `0i <= 8i + ${prefix:int}`;
  thm lower_raw;
  if (is_local) {
    lower_raw = mp_rule(mp_rule(int_arith_rule(imp_chain(TERM_LIST(
        `0i <= ${params_size:int}`,
        `0i <= ${prefix:int}`), lower_raw_term)),
        params_nonnegative), prefix_nonnegative);
  } else {
    lower_raw = mp_rule(int_arith_rule(mk_imp(
        `0i <= ${prefix:int}`, lower_raw_term)), prefix_nonnegative);
  }

  term upper_raw_term = is_local
      ? `8i + ${params_size:int} + ${prefix:int} <= 1048560i`
      : `8i + ${prefix:int} <= 1048560i`;
  thm upper_raw;
  if (is_local) {
    upper_raw = int_arith_rule(imp_chain(TERM_LIST(
        `${prefix:int} + ${slot_size:int} <= ${locals_size:int}`,
        `0i < ${slot_size:int}`,
        `0i <= cm_temp_slots ${function:cm_function_d}`,
        concl(frame_upper_raw)), upper_raw_term));
    upper_raw = match_mp_rule(upper_raw, cell_upper);
    upper_raw = match_mp_rule(upper_raw, slot_positive);
    upper_raw = match_mp_rule(upper_raw, temp_nonnegative);
    upper_raw = match_mp_rule(upper_raw, frame_upper_raw);
  } else {
    upper_raw = int_arith_rule(imp_chain(TERM_LIST(
        `${prefix:int} + ${slot_size:int} <= ${params_size:int}`,
        `0i < ${slot_size:int}`,
        `0i <= ${locals_size:int}`,
        `0i <= cm_temp_slots ${function:cm_function_d}`,
        concl(frame_upper_raw)), upper_raw_term));
    upper_raw = match_mp_rule(upper_raw, cell_upper);
    upper_raw = match_mp_rule(upper_raw, slot_positive);
    upper_raw = match_mp_rule(upper_raw, locals_nonnegative);
    upper_raw = match_mp_rule(upper_raw, temp_nonnegative);
    upper_raw = match_mp_rule(upper_raw, frame_upper_raw);
  }

  thm_list offset_rules = THM_LIST(is_local
      ? get_cm_local_offset_def()
      : get_cm_param_offset_def());
  thm lower_view = apply_conversion(rewrite_conv(offset_rules),
      `0i <= ${offset:int}`);
  thm lower = eq_mp_rule(sym_rule(lower_view), lower_raw);
  thm upper_view = apply_conversion(rewrite_conv(offset_rules),
      `${offset:int} <= 1048560i`);
  thm upper = eq_mp_rule(sym_rule(upper_view), upper_raw);
  thm bounds = mp_rule(mp_rule(int_arith_rule(
      `0i <= ${offset:int} ==>
       ${offset:int} <= 1048560i ==>
       --9223372036854775808i <= ${offset:int} &&
       ${offset:int} <= 9223372036854775807i`), lower), upper);
  thm signed_view = apply_conversion(rewrite_conv(THM_LIST(
      get_tower_signed64_def())), `tower_signed64 ${offset:int}`);
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(signed_view), bounds));
  return gnode_prove(root);
}

PROOF thm cm_local_offset_signed =
    cm_prove_binding_offset_signed(true);
PROOF thm cm_param_offset_signed =
    cm_prove_binding_offset_signed(false);

PROOF thm get_cm_local_offset_signed(void) {
  return cm_local_offset_signed;
}
PROOF thm get_cm_param_offset_signed(void) {
  return cm_param_offset_signed;
}

PROOF static thm cm_prove_runtime_stack_fid_valid(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (all_regions:(cm_region)list)
         (cursors:(cm_acursor)list).
       !(fid:int) (fp:int) (active:(cm_region)list)
         (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         cm_runtime_stack p all_regions fid fp active cursors
           spills saved calls ==>
         (fid == --1i ||
          (0i <= fid &&
           fid < ilength (cm_program_functions p)))`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_regions = GEN_TAC(with_program, "all_regions");
  gnode_list cases =
      INDUCT_TAC(with_regions, `cursors:(cm_acursor)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(
        THM_LIST(cm_runtime_stack_def)), assume_rule(
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
    term target =
        `(fid:int) == --1i ||
         (0i <= fid &&
          fid < ilength (cm_program_functions (p:cm_program)))`;
    term stack =
        `cm_runtime_stack (p:cm_program)
          (all_regions:(cm_region)list) (fid:int) (fp:int)
          (active:(cm_region)list)
          ((a0:cm_acursor) :: (a1:(cm_acursor)list))
          (spills:(cm_spill)list)
          (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list)`;
    gnode_list call_cases = BOOL_CASES_TAC(
        leaf, `cm_phase_is_call ${phase:cm_aphase}`, "Hcall");
    {
      thm call = assume_rule(
          `cm_phase_is_call ${phase:cm_aphase}`);
      thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_runtime_stack_def, call)), assume_rule(stack));
      thm segment = cm_binding_numeric_consequence(opened,
          `cm_frame_segment (p:cm_program) (fid:int) (fp:int)
            (cm_phase_oldfp ${phase:cm_aphase})`);
      thm segment_open = conv_rule(rewrite_conv(
          THM_LIST(cm_frame_segment_def)), segment);
      thm fid_pair = cm_binding_numeric_consequence(segment_open,
          `0i <= (fid:int) &&
           fid < ilength (cm_program_functions (p:cm_program))`);
      ACCEPT_TAC(call_cases[0], disj2_rule(
          `(fid:int) == --1i`, fid_pair));
    }
    {
      thm not_call = assume_rule(
          `~cm_phase_is_call ${phase:cm_aphase}`);
      gnode_list scope_cases = BOOL_CASES_TAC(
          call_cases[1], `cm_phase_is_scope ${phase:cm_aphase}`,
          "Hscope");
      {
        thm scope = assume_rule(
            `cm_phase_is_scope ${phase:cm_aphase}`);
        thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
            cm_runtime_stack_def, not_call, scope)),
            assume_rule(stack));
        thm nonnegative = conjunct1_rule(opened);
        thm recursive = conjunct2_rule(conjunct2_rule(opened));
        thm ih = specl_rule(TERM_LIST(
            `fid:int`, `fp:int`,
            `cm_phase_oldregions ${phase:cm_aphase}`,
            `spills:(cm_spill)list`,
            `saved:(cm_spill_frame)list`,
            `calls:(cm_call_sim_frame)list`),
            assume_rule(goal_lasmps(scope_cases[0]->g)[0].tm));
        thm recursive_valid = match_mp_rule(ih, recursive);
        thm not_root = mp_rule(int_arith_rule(
            `0i <= (fid:int) ==> ~((fid:int) == --1i)`),
            nonnegative);
        thm result = mp_rule(mp_rule(
            taut_rule(imp_chain(TERM_LIST(
              concl(recursive_valid), concl(not_root)), target)),
            recursive_valid), not_root);
        ACCEPT_TAC(scope_cases[0], result);
      }
      {
        thm not_scope = assume_rule(
            `~cm_phase_is_scope ${phase:cm_aphase}`);
        gnode_list halt_cases = BOOL_CASES_TAC(
            scope_cases[1], `cm_phase_is_halt ${phase:cm_aphase}`,
            "Hhalt");
        {
          thm halt = assume_rule(
              `cm_phase_is_halt ${phase:cm_aphase}`);
          thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
              cm_runtime_stack_def, not_call, not_scope, halt)),
              assume_rule(stack));
          thm root_fid = cm_binding_numeric_consequence(
              opened, `(fid:int) == --1i`);
          ACCEPT_TAC(halt_cases[0], disj1_rule(
              root_fid,
              `0i <= (fid:int) &&
               fid < ilength
                 (cm_program_functions (p:cm_program))`));
        }
        {
          thm not_halt = assume_rule(
              `~cm_phase_is_halt ${phase:cm_aphase}`);
          thm recursive = conv_rule(reduce_rewrite_conv(THM_LIST(
              cm_runtime_stack_def, not_call, not_scope, not_halt)),
              assume_rule(stack));
          thm ih = specl_rule(TERM_LIST(
              `fid:int`, `fp:int`, `active:(cm_region)list`,
              `spills:(cm_spill)list`,
              `saved:(cm_spill_frame)list`,
              `calls:(cm_call_sim_frame)list`),
              assume_rule(goal_lasmps(halt_cases[1]->g)[0].tm));
          ACCEPT_TAC(halt_cases[1], match_mp_rule(ih, recursive));
        }
      }
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_runtime_stack_fid_valid =
    cm_prove_runtime_stack_fid_valid();
PROOF thm get_cm_runtime_stack_fid_valid(void) {
  return cm_runtime_stack_fid_valid;
}


PROOF static int cmc_preservation_binding_numeric_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_binding_numeric_axioms_before,
      "cmc_preservation_binding_numeric introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_local_offset_signed)) == 0,
      "cm_local_offset_signed has hypotheses");
  ENSURE_COND(vector_size(hyp(cm_param_offset_signed)) == 0,
      "cm_param_offset_signed has hypotheses");
  ENSURE_COND(vector_size(hyp(cm_runtime_stack_fid_valid)) == 0,
      "cm_runtime_stack_fid_valid has hypotheses");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_binding_numeric_checks =
    cmc_preservation_binding_numeric_final_checks();
