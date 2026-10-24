#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_tagged_transition.h"

#require "cmc_preservation_tagged_task.c"

PROOF static size_t _cmc_preservation_tagged_transition_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_slot_list_ilength_zero_nil(void) {
  gnode root_node = gnode_new_with_ccl(
      `!(slots:(cm_slot_d)list).
         ilength slots == 0i ==> slots == []`);
  gnode_list cases = INDUCT_TAC(root_node, `slots:(cm_slot_d)list`);
  CONV_TAC(AUTO_INTROS_TAC(cases[0]),
      reduce_rewrite_conv(THM_LIST()));
  gnode cons = AUTO_INTROS_TAC(cases[1]);
  thm length_step = apply_conversion(
      rewrite_conv(THM_LIST(get_theorem_by_name("ILENGTH_DEF"))),
      `ilength ((a0:cm_slot_d) :: (a1:(cm_slot_d)list))`);
  thm tail_nonnegative = ispec_rule(
      `a1:(cm_slot_d)list`, get_theorem_by_name("ILENGTH_NONNEG"));
  thm contradiction = mp_rule(mp_rule(int_arith_rule(
      `ilength ((a0:cm_slot_d) :: (a1:(cm_slot_d)list)) == 0i ==>
       ilength (a0 :: a1) == 1i + ilength a1 ==>
       0i <= ilength a1 ==> F`),
      assume_rule(
        `ilength ((a0:cm_slot_d) :: (a1:(cm_slot_d)list)) == 0i`)),
      length_step);
  CONTR_TAC(cons, mp_rule(contradiction, tail_nonnegative));
  return gnode_prove(root_node);
}
PROOF static thm cm_slot_list_ilength_zero_nil =
    cm_prove_slot_list_ilength_zero_nil();

PROOF static thm cm_prove_tagged_span_io(void) {
  gnode root_node = gnode_new_with_ccl(
      `!(st:cm_src_state) (input:(int)list) (output:(int)list).
         cm_tagged_span_valid st ==>
         cm_tagged_span_valid (cm_state_io st input output)`);
  gnode leaf = AUTO_INTROS_TAC(root_node);
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, get_cm_state_io_def());
  vector_add(&rules, cm_tagged_span_valid_def);
  vector_add(&rules, cm_live_span_def);
  vector_add(&rules, cm_live_address_def);
  thm normalized = conv_rule(reduce_rewrite_conv(rules),
      assume_rule(`cm_tagged_span_valid (st:cm_src_state)`));
  thm target_view = apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), normalized));
  return gnode_prove(root_node);
}
PROOF thm cm_tagged_span_io = cm_prove_tagged_span_io();

PROOF static thm cm_prove_tagged_span_begin_call(void) {
  gnode root_node = gnode_new_with_ccl(
      `!(p:cm_program) (caller:int) (fid:int)
         (values:(cm_value)list) (st:cm_src_state) (ret:cm_type)
         (ks:(cm_frame)list) (calls:(cm_call_sim_frame)list)
         (frames:(cm_spill_frame)list).
         cm_function_wf p
           (inth fid (cm_program_functions p)) ==>
         cm_frame_segment p fid
           (cm_state_fp st -
            cm_frame_size (cm_program_structs p)
              (inth fid (cm_program_functions p)))
           (cm_state_fp st) ==>
         cm_regions_before (cm_state_regions st)
           (cm_state_nextgen st) ==>
         0i <= cm_state_nextgen st ==>
         cm_runtime_memory_layout p
           (cm_call_pending_base p fid st) calls frames ==>
         cm_tagged_span_valid st ==>
         cm_task_tagged_valid
           (cm_begin_call p caller fid values st ret ks)`);
  gnode leaf = AUTO_INTROS_TAC(root_node);
  term call_guard =
      `cm_call_ok (p:cm_program) (fid:int)
         (values:(cm_value)list) (st:cm_src_state) &&
       cm_call_depth (ks:(cm_frame)list) < 65536i`;
  gnode_list guard_cases = BOOL_CASES_TAC(
      leaf, call_guard, "Hcall_guard");
  {
    thm not_guard = assume_rule(mk_not(call_guard));
    gnode reduced = CONV_TAC(guard_cases[1],
        reduce_rewrite_conv(THM_LIST(
          get_cm_begin_call_def(), not_guard,
          cm_task_tagged_valid_def)));
    ACCEPT_TAC(reduced,
        assume_rule(`cm_tagged_span_valid (st:cm_src_state)`));
  }
  {
    thm guard = assume_rule(call_guard);
    thm call_ok = mp_rule(taut_rule(mk_imp(
        call_guard,
        `cm_call_ok (p:cm_program) (fid:int)
          (values:(cm_value)list) (st:cm_src_state)`)), guard);
    thm opened_call = conv_rule(rewrite_conv(THM_LIST(
        get_cm_call_ok_def())), call_ok);
    thm arity = mp_rule(taut_rule(mk_imp(concl(opened_call),
        `ilength (values:(cm_value)list) ==
         ilength (cm_function_params
           (inth (fid:int) (cm_program_functions (p:cm_program))))`)),
        opened_call);
    gnode_list value_cases = BOOL_CASES_TAC(
        guard_cases[0],
        `(values:(cm_value)list) == []`, "Hvalues_nil");
    {
      thm values_nil = assume_rule(
          `(values:(cm_value)list) == []`);
      thm normalized_arity = conv_rule(reduce_rewrite_conv(THM_LIST(
          values_nil, get_theorem_by_name("ILENGTH_DEF"))), arity);
      thm params_zero = mp_rule(int_arith_rule(mk_imp(
          concl(normalized_arity),
          `ilength (cm_function_params
             (inth (fid:int) (cm_program_functions (p:cm_program)))) ==
           0i`)), normalized_arity);
      thm params_nil = mp_rule(spec_rule(
          `cm_function_params
            (inth (fid:int) (cm_program_functions (p:cm_program)))`,
          cm_slot_list_ilength_zero_nil), params_zero);
      thm entered = specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `st:cm_src_state`),
          cm_tagged_span_enter_call_empty);
      entered = match_mp_rule(entered, params_nil);
      entered = match_mp_rule(entered, assume_rule(
          `cm_tagged_span_valid (st:cm_src_state)`));
      gnode reduced = CONV_TAC(value_cases[0],
          reduce_rewrite_conv(THM_LIST(
            get_cm_begin_call_def(), guard, values_nil,
            cm_task_tagged_valid_def)));
      ACCEPT_TAC(reduced, entered);
    }
    {
      thm entered = specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `values:(cm_value)list`,
          `st:cm_src_state`, `calls:(cm_call_sim_frame)list`,
          `frames:(cm_spill_frame)list`),
          cm_tagged_span_enter_call);
      entered = match_mp_rule(entered, assume_rule(
          `cm_function_wf (p:cm_program)
            (inth (fid:int) (cm_program_functions p))`));
      entered = match_mp_rule(entered, assume_rule(
          `cm_frame_segment (p:cm_program) (fid:int)
            (cm_state_fp (st:cm_src_state) -
             cm_frame_size (cm_program_structs p)
               (inth fid (cm_program_functions p)))
            (cm_state_fp st)`));
      entered = match_mp_rule(entered, assume_rule(
          `cm_regions_before (cm_state_regions (st:cm_src_state))
            (cm_state_nextgen st)`));
      entered = match_mp_rule(entered, assume_rule(
          `0i <= cm_state_nextgen (st:cm_src_state)`));
      entered = match_mp_rule(entered, assume_rule(
          `~((values:(cm_value)list) == [])`));
      entered = match_mp_rule(entered, arity);
      entered = match_mp_rule(entered, assume_rule(
          `cm_runtime_memory_layout (p:cm_program)
            (cm_call_pending_base p (fid:int) (st:cm_src_state))
            (calls:(cm_call_sim_frame)list)
            (frames:(cm_spill_frame)list)`));
      entered = match_mp_rule(entered, assume_rule(
          `cm_tagged_span_valid (st:cm_src_state)`));
      gnode reduced = CONV_TAC(value_cases[1],
          reduce_rewrite_conv(THM_LIST(
            get_cm_begin_call_def(), guard,
            cm_task_tagged_valid_def)));
      ACCEPT_TAC(reduced, entered);
    }
  }
  return gnode_prove(root_node);
}
PROOF thm cm_tagged_span_begin_call =
    cm_prove_tagged_span_begin_call();

PROOF static thm cm_prove_tagged_span_begin_call_runtime(void) {
  gnode root_node = gnode_new_with_ccl(
      `!(p:cm_program) (caller:int) (fid:int)
         (values:(cm_value)list) (st:cm_src_state) (ret:cm_type)
         (ks:(cm_frame)list) (ann:cm_annotation).
         cm_typed_program p ==>
         cm_state_generation_below p caller st ==>
         cm_runtime_core p caller st ann ==>
         cm_tagged_span_valid st ==>
         cm_task_tagged_valid
           (cm_begin_call p caller fid values st ret ks)`);
  gnode leaf = AUTO_INTROS_TAC(root_node);
  term call_guard =
      `cm_call_ok (p:cm_program) (fid:int)
         (values:(cm_value)list) (st:cm_src_state) &&
       cm_call_depth (ks:(cm_frame)list) < 65536i`;
  gnode_list guard_cases = BOOL_CASES_TAC(
      leaf, call_guard, "Hcall_guard");
  {
    thm guard = assume_rule(call_guard);
    thm call_ok = mp_rule(taut_rule(mk_imp(
        call_guard,
        `cm_call_ok (p:cm_program) (fid:int)
          (values:(cm_value)list) (st:cm_src_state)`)), guard);
    thm call_open = conv_rule(rewrite_conv(THM_LIST(
        get_cm_call_ok_def())), call_ok);
    thm fid_lower = mp_rule(taut_rule(mk_imp(concl(call_open),
        `0i <= (fid:int)`)), call_open);
    thm fid_upper = mp_rule(taut_rule(mk_imp(concl(call_open),
        `(fid:int) <
         ilength (cm_program_functions (p:cm_program))`)), call_open);
    thm typed = assume_rule(`cm_typed_program (p:cm_program)`);
    thm typed_open = conv_rule(rewrite_conv(THM_LIST(
        get_cm_typed_program_def())), typed);
    thm all_functions = mp_rule(taut_rule(mk_imp(
        concl(typed_open),
        `!index.
           0i <= index ==>
           index < ilength (cm_program_functions (p:cm_program)) ==>
           cm_function_wf p
             (inth index (cm_program_functions p))`)), typed_open);
    thm function_wf = match_mp_rule(match_mp_rule(
        spec_rule(`fid:int`, all_functions), fid_lower), fid_upper);
    thm segment = match_mp_rule(match_mp_rule(
        specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `values:(cm_value)list`,
          `st:cm_src_state`), cm_call_frame_segment),
        typed), call_ok);
    thm core = assume_rule(
        `cm_runtime_core (p:cm_program) (caller:int)
          (st:cm_src_state) (ann:cm_annotation)`);
    thm core_open = conv_rule(rewrite_conv(THM_LIST(
        cm_runtime_core_def)), core);
    thm before = conjunct1_rule(core_open);
    thm positive = match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `caller:int`, `st:cm_src_state`),
        cm_state_nextgen_positive), assume_rule(
          `cm_state_generation_below (p:cm_program) (caller:int)
            (st:cm_src_state)`));
    thm nonnegative = mp_rule(int_arith_rule(
        `0i < cm_state_nextgen (st:cm_src_state) ==>
         0i <= cm_state_nextgen st`), positive);

    term entered_state =
        `cm_enter_call (p:cm_program) (fid:int)
          (values:(cm_value)list) (st:cm_src_state)`;
    term entered_ann =
        `cm_ann_enter_call (p:cm_program) (caller:int) (fid:int)
          (st:cm_src_state) (ret:cm_type) 0i 0i 0i 0i
          (cm_ann_cursors (ann:cm_annotation))
          (cm_ann_spills ann) (cm_ann_saved ann)
          (cm_ann_calls ann)`;
    thm entered_core = specl_rule(TERM_LIST(
        `p:cm_program`, `caller:int`, `fid:int`,
        `values:(cm_value)list`, `st:cm_src_state`,
        `ret:cm_type`, `0i`, `0i`, `0i`, `0i`,
        `ann:cm_annotation`), cm_runtime_core_enter_call);
    entered_core = match_mp_rule(entered_core, typed);
    entered_core = match_mp_rule(entered_core, call_ok);
    entered_core = match_mp_rule(entered_core, core);
    thm entered_open = conv_rule(rewrite_conv(THM_LIST(
        cm_runtime_core_def)), entered_core);
    thm entered_stack = conjunct2_rule(entered_open);
    term entered_frames =
        `CMSpillFrame (fid:int)
           (cm_state_fp ${entered_state:cm_src_state})
           (cm_ann_spills ${entered_ann:cm_annotation}) ::
         cm_ann_saved ${entered_ann:cm_annotation}`;
    term entered_calls =
        `cm_ann_calls ${entered_ann:cm_annotation}`;
    thm entered_layout = specl_rule(TERM_LIST(
        `p:cm_program`, entered_state, `fid:int`,
        `cm_ann_cursors ${entered_ann:cm_annotation}`,
        `cm_ann_spills ${entered_ann:cm_annotation}`,
        `cm_ann_saved ${entered_ann:cm_annotation}`,
        entered_calls), cm_runtime_stack_memory_layout);
    entered_layout = match_mp_rule(entered_layout, entered_stack);

    thm enter_structure = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `values:(cm_value)list`,
        `st:cm_src_state`), cm_enter_call_structure);
    thm enter_regions =
        conjunct2_rule(conjunct2_rule(enter_structure));
    thm pending_structure = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`),
        cm_call_pending_structure);
    thm pending_regions = conjunct1_rule(conjunct2_rule(
        conjunct2_rule(pending_structure)));
    thm regions_equal =
        trans_rule(pending_regions, sym_rule(enter_regions));
    thm entered_layout_open = conv_rule(rewrite_conv(THM_LIST(
        cm_runtime_memory_layout_def)), entered_layout);
    thm layout_equal = beta_norm(ap_term_rule(
        `\regions:(cm_region)list.
           cm_regions_runtime_safe (p:cm_program)
             ${entered_calls:(cm_call_sim_frame)list}
             ${entered_frames:(cm_spill_frame)list} regions`,
        regions_equal));
    thm pending_layout_open =
        eq_mp_rule(sym_rule(layout_equal), entered_layout_open);
    term pending_layout_term =
        `cm_runtime_memory_layout (p:cm_program)
          (cm_call_pending_base p (fid:int) (st:cm_src_state))
          ${entered_calls:(cm_call_sim_frame)list}
          ${entered_frames:(cm_spill_frame)list}`;
    thm pending_layout = eq_mp_rule(sym_rule(apply_conversion(
        rewrite_conv(THM_LIST(cm_runtime_memory_layout_def)),
        pending_layout_term)), pending_layout_open);

    thm result = specl_rule(TERM_LIST(
        `p:cm_program`, `caller:int`, `fid:int`,
        `values:(cm_value)list`, `st:cm_src_state`,
        `ret:cm_type`, `ks:(cm_frame)list`,
        entered_calls, entered_frames),
        cm_tagged_span_begin_call);
    result = match_mp_rule(result, function_wf);
    result = match_mp_rule(result, segment);
    result = match_mp_rule(result, before);
    result = match_mp_rule(result, nonnegative);
    result = match_mp_rule(result, pending_layout);
    result = match_mp_rule(result, assume_rule(
        `cm_tagged_span_valid (st:cm_src_state)`));
    ACCEPT_TAC(guard_cases[0], result);
  }
  {
    thm not_guard = assume_rule(mk_not(call_guard));
    gnode reduced = CONV_TAC(guard_cases[1],
        reduce_rewrite_conv(THM_LIST(
          get_cm_begin_call_def(), not_guard,
          cm_task_tagged_valid_def)));
    ACCEPT_TAC(reduced, assume_rule(
        `cm_tagged_span_valid (st:cm_src_state)`));
  }
  return gnode_prove(root_node);
}
PROOF thm cm_tagged_span_begin_call_runtime =
    cm_prove_tagged_span_begin_call_runtime();

PROOF static int cmc_preservation_tagged_transition_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_tagged_transition_axioms_before,
      "cmc_preservation_tagged_transition introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_tagged_span_io)) == 0,
      "tagged-span IO theorem is not closed");
  ENSURE_COND(vector_size(hyp(cm_tagged_span_begin_call)) == 0,
      "tagged-span begin-call theorem is not closed");
  ENSURE_COND(vector_size(hyp(cm_tagged_span_begin_call_runtime)) == 0,
      "runtime begin-call tagged-span theorem is not closed");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_tagged_transition_checks =
    cmc_preservation_tagged_transition_final_checks();
