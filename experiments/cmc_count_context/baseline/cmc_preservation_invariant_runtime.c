#include "proof/proof.h"
#include "userlib/proof.h"
#include "cmc_preservation_invariant_runtime.h"

#require "cmc_preservation_invariant_frame.c"

PROOF static size_t _cmc_preservation_invariant_runtime_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_runtime_assumption(gnode node, term wanted) {
  labeled_term_list assumptions = goal_lasmps(node->g);
  for (size_t index = 0; index < vector_size(assumptions); ++index) {
    if (alpha_compare(assumptions[index].tm, wanted) == 0) {
      return assume_rule(assumptions[index].tm);
    }
  }
  ENSURE_COND(false, "missing runtime proof assumption: %s in %s",
      cstr_term(wanted), cstr_gnode(node));
err:
  return empty_theorem;
}

PROOF static thm cm_prove_runtime_stack_plain_cons(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (all_regions:(cm_region)list)
         (fid:int) (fp:int) (active:(cm_region)list)
         (phase:cm_aphase) (temp:int) (breakpc:int) (continuepc:int)
         (rest:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list) (calls:(cm_call_sim_frame)list).
         ~cm_phase_is_call phase ==>
         ~cm_phase_is_scope phase ==>
         ~cm_phase_is_halt phase ==>
         (cm_runtime_stack p all_regions fid fp active
            (CMACursor phase temp breakpc continuepc :: rest)
            spills saved calls <=>
          cm_runtime_stack p all_regions fid fp active rest
            spills saved calls)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, THM_LIST(
      cm_runtime_stack_def, cm_cursor_phase_def));
  return gnode_prove(root);
}
PROOF thm cm_runtime_stack_plain_cons =
    cm_prove_runtime_stack_plain_cons();

PROOF static thm cm_prove_runtime_stack_call_cons(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (all_regions:(cm_region)list)
         (fid:int) (fp:int) (active:(cm_region)list)
         (caller:int) (env:int->int->cm_value) (oldfp:int)
         (oldregions:(cm_region)list) (ret:cm_type)
         (temp:int) (breakpc:int) (continuepc:int)
         (rest:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list) (calls:(cm_call_sim_frame)list).
         (cm_runtime_stack p all_regions fid fp active
            (CMACursor (CACallP caller env oldfp oldregions ret)
               temp breakpc continuepc :: rest)
            spills saved calls <=>
          cm_region_prefix_safe p all_regions fid fp active oldregions &&
          cm_frame_segment p fid fp oldfp &&
          cm_spills_within_frame p fid fp oldfp spills &&
          ~(saved == []) && ~(calls == []) &&
          cm_call_sim_base (HD calls) == fp &&
          cm_call_sim_saved (HD calls) == oldfp &&
          cm_spill_frame_fid (HD saved) == caller &&
          cm_spill_frame_fp (HD saved) == oldfp &&
          cm_runtime_stack p all_regions caller oldfp oldregions rest
            (cm_spill_frame_spills (HD saved)) (TL saved) (TL calls))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      cm_runtime_stack_def, cm_cursor_phase_def,
      cm_phase_is_call_def, cm_phase_oldfp_def,
      cm_phase_oldregions_def, cm_phase_caller_def)));
  return gnode_prove(root);
}
PROOF thm cm_runtime_stack_call_cons =
    cm_prove_runtime_stack_call_cons();

PROOF static thm cm_prove_runtime_stack_scope_cons(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (all_regions:(cm_region)list)
         (fid:int) (fp:int) (active:(cm_region)list)
         (phase:cm_aphase) (oldregions:(cm_region)list)
         (temp:int) (breakpc:int) (continuepc:int)
         (rest:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list) (calls:(cm_call_sim_frame)list).
         cm_phase_is_scope phase ==>
         ~cm_phase_is_call phase ==>
         cm_phase_oldregions phase == oldregions ==>
         (cm_runtime_stack p all_regions fid fp active
            (CMACursor phase temp breakpc continuepc :: rest)
            spills saved calls <=>
          0i <= fid &&
          cm_region_prefix_safe p all_regions fid fp active oldregions &&
          cm_runtime_stack p all_regions fid fp oldregions rest
            spills saved calls)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode reduced = CONV_WITH_ASMP_TAC(
      leaf, reduce_rewrite_conv, THM_LIST(
        cm_runtime_stack_def, cm_cursor_phase_def));
  if (IS_NULL(reduced->solved)) {
    ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
  }
  return gnode_prove(root);
}
PROOF thm cm_runtime_stack_scope_cons =
    cm_prove_runtime_stack_scope_cons();


PROOF static thm cm_prove_region_prefix_safe_old_length(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (all_regions:(cm_region)list)
         (fid:int) (fp:int) (active:(cm_region)list)
         (old:(cm_region)list).
         cm_region_prefix_safe p all_regions fid fp active old ==>
         ilength old <= ilength active`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_all = GEN_TAC(with_program, "all_regions");
  gnode with_fid = GEN_TAC(with_all, "fid");
  gnode with_fp = GEN_TAC(with_fid, "fp");
  gnode_list cases =
      INDUCT_TAC(with_fp, `active:(cm_region)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm prefix = conv_rule(reduce_rewrite_conv(THM_LIST(
        cm_region_prefix_safe_def)), assume_rule(
          `cm_region_prefix_safe
            (p:cm_program) (all_regions:(cm_region)list)
            (fid:int) (fp:int) ([]:(cm_region)list)
            (old:(cm_region)list)`));
    gnode reduced = CONV_WITH_ASMP_TAC(
        leaf, reduce_rewrite_conv,
        THM_LIST(prefix, get_theorem_by_name("ILENGTH_DEF")));
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, int_arith_rule(goal_ccl(reduced->g)));
    }
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    term active =
        `(a0:cm_region) :: (a1:(cm_region)list)`;
    gnode_list equal_cases = BOOL_CASES_TAC(
        leaf, `${active:(cm_region)list} ==
          (old:(cm_region)list)`, "Hprefix_equal");
    {
      thm equal = assume_rule(
          `${active:(cm_region)list} ==
           (old:(cm_region)list)`);
      thm lengths = ap_term_rule(
          `ilength:(cm_region)list->int`, equal);
      ACCEPT_TAC(equal_cases[0], mp_rule(
          int_arith_rule(mk_imp(concl(lengths),
            `ilength (old:(cm_region)list) <=
             ilength ${active:(cm_region)list}`)), lengths));
    }
    {
      thm not_equal = assume_rule(
          `~(${active:(cm_region)list} ==
             (old:(cm_region)list))`);
      thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_region_prefix_safe_def, not_equal)), assume_rule(
            `cm_region_prefix_safe
              (p:cm_program) (all_regions:(cm_region)list)
              (fid:int) (fp:int) ${active:(cm_region)list}
              (old:(cm_region)list)`));
      thm tail_prefix = conjunct2_rule(opened);
      thm ih = spec_rule(`old:(cm_region)list`,
          cm_runtime_assumption(equal_cases[1],
            `!remaining:(cm_region)list.
               cm_region_prefix_safe
                 (p:cm_program) (all_regions:(cm_region)list)
                 (fid:int) (fp:int) (a1:(cm_region)list)
                 remaining ==>
               ilength remaining <= ilength a1`));
      thm tail_length = match_mp_rule(ih, tail_prefix);
      thm active_length = apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_theorem_by_name("ILENGTH_DEF"))),
          `ilength ${active:(cm_region)list}`);
      thm inputs = conj_rule(tail_length, active_length);
      ACCEPT_TAC(equal_cases[1], mp_rule(
          int_arith_rule(mk_imp(concl(inputs),
            `ilength (old:(cm_region)list) <=
             ilength ${active:(cm_region)list}`)), inputs));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_region_prefix_safe_old_length =
    cm_prove_region_prefix_safe_old_length();

PROOF static thm cm_prove_region_prefix_safe_cons(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (all_regions:(cm_region)list)
         (fid:int) (fp:int) (region:cm_region)
         (active:(cm_region)list) (old:(cm_region)list).
         cm_region_frame_safe p all_regions fid fp region ==>
         cm_region_prefix_safe p all_regions fid fp active old ==>
         cm_region_prefix_safe p all_regions fid fp
           (region :: active) old`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm prefix = assume_rule(
      `cm_region_prefix_safe
        (p:cm_program) (all_regions:(cm_region)list)
        (fid:int) (fp:int) (active:(cm_region)list)
        (old:(cm_region)list)`);
  thm old_length = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `all_regions:(cm_region)list`,
      `fid:int`, `fp:int`, `active:(cm_region)list`,
      `old:(cm_region)list`), cm_region_prefix_safe_old_length),
      prefix);
  thm active_length = apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))),
      `ilength
        ((region:cm_region) :: (active:(cm_region)list))`);
  term equal_term =
      `((region:cm_region) :: (active:(cm_region)list)) ==
       (old:(cm_region)list)`;
  thm equal_lengths = ap_term_rule(
      `ilength:(cm_region)list->int`,
      assume_rule(equal_term));
  thm impossible = mp_rule(int_arith_rule(mk_imp(
      mk_conj(concl(old_length),
        mk_conj(concl(active_length), concl(equal_lengths))),
      `F`)), conj_rule(old_length,
        conj_rule(active_length, equal_lengths)));
  thm distinct = not_intro(equal_term, impossible);
  gnode reduced = CONV_TAC(leaf,
      reduce_rewrite_conv(THM_LIST(
        cm_region_prefix_safe_def, distinct)));
  ACCEPT_TAC(reduced, conj_rule(
      assume_rule(
        `cm_region_frame_safe
          (p:cm_program) (all_regions:(cm_region)list)
          (fid:int) (fp:int) (region:cm_region)`),
      prefix));
  return gnode_prove(root);
}
PROOF thm cm_region_prefix_safe_cons =
    cm_prove_region_prefix_safe_cons();

PROOF static thm cm_prove_runtime_stack_active_cons(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (all_regions:(cm_region)list)
         (fid:int) (fp:int) (region:cm_region)
         (active:(cm_region)list) (cursors:(cm_acursor)list)
         (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         0i <= fid ==>
         cm_region_frame_safe p all_regions fid fp region ==>
         cm_runtime_stack p all_regions fid fp active cursors
           spills saved calls ==>
         cm_runtime_stack p all_regions fid fp
           (region :: active) cursors spills saved calls`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_all = GEN_TAC(with_program, "all_regions");
  gnode with_fid = GEN_TAC(with_all, "fid");
  gnode with_fp = GEN_TAC(with_fid, "fp");
  gnode with_region = GEN_TAC(with_fp, "region");
  gnode with_active = GEN_TAC(with_region, "active");
  gnode_list cases =
      INDUCT_TAC(with_active, `cursors:(cm_acursor)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        cm_runtime_stack_def)), assume_rule(
          `cm_runtime_stack
            (p:cm_program) (all_regions:(cm_region)list)
            (fid:int) (fp:int) (active:(cm_region)list)
            ([]:(cm_acursor)list) (spills:(cm_spill)list)
            (saved:(cm_spill_frame)list)
            (calls:(cm_call_sim_frame)list)`));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    term phase = `cm_cursor_phase (a0:cm_acursor)`;
    thm stack = assume_rule(
        `cm_runtime_stack
          (p:cm_program) (all_regions:(cm_region)list)
          (fid:int) (fp:int) (active:(cm_region)list)
          ((a0:cm_acursor) :: (a1:(cm_acursor)list))
          (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list)`);
    thm frame_safe = assume_rule(
        `cm_region_frame_safe
          (p:cm_program) (all_regions:(cm_region)list)
          (fid:int) (fp:int) (region:cm_region)`);
    gnode_list call_cases = BOOL_CASES_TAC(
        leaf, `cm_phase_is_call ${phase:cm_aphase}`,
        "Hactive_call");
    {
      thm call = assume_rule(
          `cm_phase_is_call ${phase:cm_aphase}`);
      thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_runtime_stack_def, call)), stack);
      thm old_prefix = mp_rule(taut_rule(mk_imp(
          concl(opened),
          `cm_region_prefix_safe
            (p:cm_program) (all_regions:(cm_region)list)
            (fid:int) (fp:int) (active:(cm_region)list)
            (cm_phase_oldregions ${phase:cm_aphase})`)), opened);
      thm new_prefix = match_mp_rule(match_mp_rule(
          specl_rule(TERM_LIST(
            `p:cm_program`, `all_regions:(cm_region)list`,
            `fid:int`, `fp:int`, `region:cm_region`,
            `active:(cm_region)list`,
            `cm_phase_oldregions ${phase:cm_aphase}`),
            cm_region_prefix_safe_cons),
          frame_safe), old_prefix);
      gnode reduced = CONV_WITH_ASMP_TAC(
          call_cases[0], reduce_rewrite_conv,
          THM_LIST(cm_runtime_stack_def));
      thm facts = conj_rule(opened, new_prefix);
      ACCEPT_TAC(reduced, mp_rule(taut_rule(mk_imp(
          concl(facts), goal_ccl(reduced->g))), facts));
    }
    {
      thm not_call = assume_rule(
          `~cm_phase_is_call ${phase:cm_aphase}`);
      gnode_list scope_cases = BOOL_CASES_TAC(
          call_cases[1],
          `cm_phase_is_scope ${phase:cm_aphase}`,
          "Hactive_scope");
      {
        thm scope = assume_rule(
            `cm_phase_is_scope ${phase:cm_aphase}`);
        thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
            cm_runtime_stack_def, not_call, scope)), stack);
        thm old_prefix = mp_rule(taut_rule(mk_imp(
            concl(opened),
            `cm_region_prefix_safe
              (p:cm_program) (all_regions:(cm_region)list)
              (fid:int) (fp:int) (active:(cm_region)list)
              (cm_phase_oldregions ${phase:cm_aphase})`)), opened);
        thm new_prefix = match_mp_rule(match_mp_rule(
            specl_rule(TERM_LIST(
              `p:cm_program`, `all_regions:(cm_region)list`,
              `fid:int`, `fp:int`, `region:cm_region`,
              `active:(cm_region)list`,
              `cm_phase_oldregions ${phase:cm_aphase}`),
              cm_region_prefix_safe_cons),
            frame_safe), old_prefix);
        gnode reduced = CONV_WITH_ASMP_TAC(
            scope_cases[0], reduce_rewrite_conv,
            THM_LIST(cm_runtime_stack_def));
        thm facts = conj_rule(opened, new_prefix);
        ACCEPT_TAC(reduced, mp_rule(taut_rule(mk_imp(
            concl(facts), goal_ccl(reduced->g))), facts));
      }
      {
        thm not_scope = assume_rule(
            `~cm_phase_is_scope ${phase:cm_aphase}`);
        gnode_list halt_cases = BOOL_CASES_TAC(
            scope_cases[1],
            `cm_phase_is_halt ${phase:cm_aphase}`,
            "Hactive_halt");
        {
          thm halt = assume_rule(
              `cm_phase_is_halt ${phase:cm_aphase}`);
          thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
              cm_runtime_stack_def, not_call, not_scope, halt)), stack);
          thm fid_halt = mp_rule(taut_rule(mk_imp(
              concl(opened), `(fid:int) == --1i`)), opened);
          thm contradiction = mp_rule(mp_rule(int_arith_rule(
              `0i <= (fid:int) ==> fid == --1i ==> F`),
              assume_rule(`0i <= (fid:int)`)), fid_halt);
          CONTR_TAC(halt_cases[0], contradiction);
        }
        {
          thm not_halt = assume_rule(
              `~cm_phase_is_halt ${phase:cm_aphase}`);
          thm recursive = conv_rule(reduce_rewrite_conv(THM_LIST(
              cm_runtime_stack_def, not_call, not_scope, not_halt)),
              stack);
          thm ih = specl_rule(TERM_LIST(
              `spills:(cm_spill)list`,
              `saved:(cm_spill_frame)list`,
              `calls:(cm_call_sim_frame)list`),
              cm_runtime_assumption(halt_cases[1],
                `!(next_spills:(cm_spill)list)
                   (next_saved:(cm_spill_frame)list)
                   (next_calls:(cm_call_sim_frame)list).
                   0i <= (fid:int) ==>
                   cm_region_frame_safe
                     (p:cm_program) (all_regions:(cm_region)list)
                     fid (fp:int) (region:cm_region) ==>
                   cm_runtime_stack p all_regions fid fp
                     (active:(cm_region)list)
                     (a1:(cm_acursor)list)
                     next_spills next_saved next_calls ==>
                   cm_runtime_stack p all_regions fid fp
                     (region :: active) a1
                     next_spills next_saved next_calls`));
          thm next = match_mp_rule(match_mp_rule(match_mp_rule(
              ih, assume_rule(`0i <= (fid:int)`)),
              frame_safe), recursive);
          gnode reduced = CONV_WITH_ASMP_TAC(
              halt_cases[1], reduce_rewrite_conv,
              THM_LIST(cm_runtime_stack_def));
          ACCEPT_TAC(reduced, next);
        }
      }
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_runtime_stack_active_cons =
    cm_prove_runtime_stack_active_cons();

PROOF static thm cm_prove_runtime_stack_fresh_cons(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (region:cm_region)
         (regions:(cm_region)list) (gen:int)
         (fid:int) (fp:int) (cursors:(cm_acursor)list)
         (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         0i <= fid ==>
         cm_regions_before regions gen ==>
         gen <= cm_region_gen region ==>
         cm_region_frame_safe p (region :: regions) fid fp region ==>
         cm_runtime_stack p regions fid fp regions cursors
           spills saved calls ==>
         cm_runtime_stack p (region :: regions) fid fp
           (region :: regions) cursors spills saved calls`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm bases = match_mp_rule(specl_rule(TERM_LIST(
      `region:cm_region`, `regions:(cm_region)list`, `gen:int`),
      cm_region_bases_fresh_cons), assume_rule(
        `(gen:int) <= cm_region_gen (region:cm_region)`));
  thm transported = match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`,
        `(region:cm_region) :: (regions:(cm_region)list)`,
        `regions:(cm_region)list`, `gen:int`,
        `cursors:(cm_acursor)list`, `fid:int`, `fp:int`,
        `regions:(cm_region)list`, `spills:(cm_spill)list`,
        `saved:(cm_spill_frame)list`,
        `calls:(cm_call_sim_frame)list`),
        cm_runtime_stack_below_bases),
      bases), assume_rule(
        `cm_regions_before (regions:(cm_region)list) (gen:int)`)),
      assume_rule(
        `cm_runtime_stack
          (p:cm_program) (regions:(cm_region)list)
          (fid:int) (fp:int) regions (cursors:(cm_acursor)list)
          (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list)`));
  ACCEPT_TAC(leaf, match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`,
        `(region:cm_region) :: (regions:(cm_region)list)`,
        `fid:int`, `fp:int`, `region:cm_region`,
        `regions:(cm_region)list`, `cursors:(cm_acursor)list`,
        `spills:(cm_spill)list`, `saved:(cm_spill_frame)list`,
        `calls:(cm_call_sim_frame)list`),
        cm_runtime_stack_active_cons),
      assume_rule(`0i <= (fid:int)`)),
      assume_rule(
        `cm_region_frame_safe
          (p:cm_program)
          ((region:cm_region) :: (regions:(cm_region)list))
          (fid:int) (fp:int) region`)),
      transported));
  return gnode_prove(root);
}
PROOF thm cm_runtime_stack_fresh_cons =
    cm_prove_runtime_stack_fresh_cons();

PROOF static thm cm_prove_store_params_structure(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (values:(cm_value)list).
         !index st.
           cm_state_fp (cm_store_params p fid values index st) ==
             cm_state_fp st &&
           cm_state_nextgen (cm_store_params p fid values index st) ==
             cm_state_nextgen st &&
           cm_state_regions (cm_store_params p fid values index st) ==
             cm_state_regions st`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_fid = GEN_TAC(with_program, "fid");
  gnode_list cases =
      INDUCT_TAC(with_fid, `values:(cm_value)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(
        get_cm_runtime_defs()));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    term next_state =
        `cm_state_store
          (cm_slot_ty
            (inth (index:int)
              (cm_function_params
                (inth (fid:int)
                  (cm_program_functions (p:cm_program))))))
          (cm_state_env (st:cm_src_state) 2i index)
          (a0:cm_value) st`;
    thm ih = specl_rule(TERM_LIST(
        `(index:int) + 1i`, next_state),
        cm_runtime_assumption(leaf,
          `!next_index next_state.
             cm_state_fp
               (cm_store_params
                 (p:cm_program) (fid:int)
                 (a1:(cm_value)list) next_index next_state) ==
               cm_state_fp next_state &&
             cm_state_nextgen
               (cm_store_params p fid a1 next_index next_state) ==
               cm_state_nextgen next_state &&
             cm_state_regions
               (cm_store_params p fid a1 next_index next_state) ==
               cm_state_regions next_state`));
    thm normalized_ih = conv_rule(
        reduce_rewrite_conv(get_cm_runtime_defs()), ih);
    gnode reduced = CONV_TAC(leaf,
        reduce_rewrite_conv(get_cm_runtime_defs()));
    ACCEPT_TAC(reduced, normalized_ih);
  }
  return gnode_prove(root);
}
PROOF thm cm_store_params_structure =
    cm_prove_store_params_structure();

PROOF static thm cm_prove_enter_call_structure(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (values:(cm_value)list)
         (st:cm_src_state).
         cm_state_fp (cm_enter_call p fid values st) ==
           cm_state_fp st -
             cm_frame_size (cm_program_structs p)
               (inth fid (cm_program_functions p)) &&
         cm_state_nextgen (cm_enter_call p fid values st) ==
           cm_state_nextgen st +
             ilength (cm_function_params
               (inth fid (cm_program_functions p))) &&
         cm_state_regions (cm_enter_call p fid values st) ==
           cm_regions_for_slots
             (cm_program_structs p)
             (cm_function_params
               (inth fid (cm_program_functions p)))
             (cm_state_nextgen st)
             ((cm_state_fp st -
               cm_frame_size (cm_program_structs p)
                 (inth fid (cm_program_functions p))) + 8i) ++
           cm_state_regions st`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term base_state =
      `cm_call_base_state
        (p:cm_program) (fid:int) (st:cm_src_state)`;
  thm structure = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `values:(cm_value)list`,
      `0i`, base_state), cm_store_params_structure);
  thm enter_def = get_cm_enter_call_def();
  conv base_reduction = then_conv(
      rewrite_conv(THM_LIST(get_cm_call_base_state_def())),
      reduce_rewrite_conv(get_cm_state_core_defs()));
  thm fp_bridge = ap_term_rule(`cm_state_fp`, enter_def);
  thm fp_base = apply_conversion(base_reduction,
      `cm_state_fp ${base_state:cm_src_state}`);
  thm fp_result = trans_rule(fp_bridge,
      trans_rule(conjunct1_rule(structure), fp_base));
  thm nextgen_bridge =
      ap_term_rule(`cm_state_nextgen`, enter_def);
  thm nextgen_base = apply_conversion(base_reduction,
      `cm_state_nextgen ${base_state:cm_src_state}`);
  thm nextgen_result = trans_rule(nextgen_bridge,
      trans_rule(conjunct1_rule(conjunct2_rule(structure)),
        nextgen_base));
  thm regions_bridge =
      ap_term_rule(`cm_state_regions`, enter_def);
  thm regions_base = apply_conversion(base_reduction,
      `cm_state_regions ${base_state:cm_src_state}`);
  thm regions_result = trans_rule(regions_bridge,
      trans_rule(conjunct2_rule(conjunct2_rule(structure)),
        regions_base));
  ACCEPT_TAC(leaf, conj_rule(fp_result,
      conj_rule(nextgen_result, regions_result)));
  return gnode_prove(root);
}
PROOF thm cm_enter_call_structure =
    cm_prove_enter_call_structure();
PROOF static thm cm_prove_runtime_stack_enter_call(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (caller:int) (fid:int)
         (values:(cm_value)list) (st:cm_src_state) (ret:cm_type)
         (returnpc:int) (parent_temp:int) (parent_break:int)
         (parent_continue:int) (tail:(cm_acursor)list)
         (caller_spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         cm_typed_program p ==>
         cm_call_ok p fid values st ==>
         cm_regions_before
           (cm_state_regions st) (cm_state_nextgen st) ==>
         cm_runtime_stack p (cm_state_regions st)
           caller (cm_state_fp st) (cm_state_regions st) tail
           caller_spills saved calls ==>
         cm_runtime_stack p
           (cm_regions_for_slots
              (cm_program_structs p)
              (cm_function_params
                (inth fid (cm_program_functions p)))
              (cm_state_nextgen st)
              ((cm_state_fp st -
                cm_frame_size (cm_program_structs p)
                  (inth fid (cm_program_functions p))) + 8i) ++
            cm_state_regions st)
           fid
           (cm_state_fp st -
             cm_frame_size (cm_program_structs p)
               (inth fid (cm_program_functions p)))
           (cm_regions_for_slots
              (cm_program_structs p)
              (cm_function_params
                (inth fid (cm_program_functions p)))
              (cm_state_nextgen st)
              ((cm_state_fp st -
                cm_frame_size (cm_program_structs p)
                  (inth fid (cm_program_functions p))) + 8i) ++
            cm_state_regions st)
           (CMACursor
              (CACallP caller (cm_state_env st) (cm_state_fp st)
                (cm_state_regions st) ret)
              parent_temp parent_break parent_continue :: tail)
           []
           (CMSpillFrame caller (cm_state_fp st) caller_spills :: saved)
           (CMCallSimFrame
              (cm_state_fp st -
               cm_frame_size (cm_program_structs p)
                 (inth fid (cm_program_functions p)))
              (cm_state_fp st) returnpc :: calls)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term parameters =
      `cm_function_params
        (inth (fid:int)
          (cm_program_functions (p:cm_program)))`;
  term new_fp =
      `cm_state_fp (st:cm_src_state) -
       cm_frame_size (cm_program_structs (p:cm_program))
         (inth (fid:int) (cm_program_functions p))`;
  term fresh =
      `cm_regions_for_slots
        (cm_program_structs (p:cm_program))
        ${parameters:(cm_slot_d)list}
        (cm_state_nextgen (st:cm_src_state))
        (${new_fp:int} + 8i)`;
  term all_regions =
      `${fresh:(cm_region)list} ++
       cm_state_regions (st:cm_src_state)`;
  thm typed_assumption =
      assume_rule(`cm_typed_program (p:cm_program)`);
  thm call_assumption = assume_rule(
      `cm_call_ok (p:cm_program) (fid:int)
        (values:(cm_value)list) (st:cm_src_state)`);
  thm before = assume_rule(
      `cm_regions_before
        (cm_state_regions (st:cm_src_state))
        (cm_state_nextgen st)`);
  thm typed = conv_rule(rewrite_conv(THM_LIST(
      get_cm_typed_program_def())), typed_assumption);
  thm call_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_call_ok_def())), call_assumption);
  thm fid_lower = mp_rule(taut_rule(mk_imp(
      concl(call_open), `0i <= (fid:int)`)), call_open);
  thm fid_upper = mp_rule(taut_rule(mk_imp(
      concl(call_open),
      `(fid:int) <
       ilength (cm_program_functions (p:cm_program))`)), call_open);
  thm function_all = mp_rule(taut_rule(mk_imp(
      concl(typed),
      `!index.
         0i <= index ==>
         index < ilength (cm_program_functions (p:cm_program)) ==>
         cm_function_wf p
           (inth index (cm_program_functions p))`)), typed);
  thm function_wf = match_mp_rule(match_mp_rule(
      spec_rule(`fid:int`, function_all), fid_lower), fid_upper);
  thm prefix = match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, new_fp,
        `cm_state_nextgen (st:cm_src_state)`,
        `cm_state_regions (st:cm_src_state)`),
        cm_parameter_region_prefix_safe),
      function_wf), before);
  thm segment = match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `values:(cm_value)list`,
        `st:cm_src_state`), cm_call_frame_segment),
      typed_assumption), call_assumption);
  thm outer = match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `cm_program_structs (p:cm_program)`,
        parameters, `cm_state_nextgen (st:cm_src_state)`,
        `${new_fp:int} + 8i`,
        `cm_state_regions (st:cm_src_state)`,
        `caller:int`, `cm_state_fp (st:cm_src_state)`,
        `tail:(cm_acursor)list`, `caller_spills:(cm_spill)list`,
        `saved:(cm_spill_frame)list`,
        `calls:(cm_call_sim_frame)list`),
        cm_runtime_stack_regions_for_slots),
      before), assume_rule(
        `cm_runtime_stack
          (p:cm_program) (cm_state_regions (st:cm_src_state))
          (caller:int) (cm_state_fp st) (cm_state_regions st)
          (tail:(cm_acursor)list) (caller_spills:(cm_spill)list)
          (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list)`));
  thm spill_empty = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_spills_within_frame_def)),
      `cm_spills_within_frame (p:cm_program) (fid:int)
        ${new_fp:int} (cm_state_fp (st:cm_src_state))
        ([]:(cm_spill)list)`));
  thm saved_nonempty = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("NOT_CONS_NIL"))),
      `~((CMSpillFrame (caller:int) (cm_state_fp (st:cm_src_state))
            (caller_spills:(cm_spill)list) ::
          (saved:(cm_spill_frame)list)) == [])`));
  thm calls_nonempty = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("NOT_CONS_NIL"))),
      `~((CMCallSimFrame ${new_fp:int}
            (cm_state_fp (st:cm_src_state)) (returnpc:int) ::
          (calls:(cm_call_sim_frame)list)) == [])`));
  thm call_base = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("HD"), cm_call_sim_base_def)),
      `cm_call_sim_base
         (HD (CMCallSimFrame ${new_fp:int}
           (cm_state_fp (st:cm_src_state)) (returnpc:int) ::
           (calls:(cm_call_sim_frame)list))) == ${new_fp:int}`));
  thm call_saved = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("HD"), cm_call_sim_saved_def)),
      `cm_call_sim_saved
         (HD (CMCallSimFrame ${new_fp:int}
           (cm_state_fp (st:cm_src_state)) (returnpc:int) ::
           (calls:(cm_call_sim_frame)list))) ==
       cm_state_fp (st:cm_src_state)`));
  thm saved_fid = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("HD"), cm_spill_frame_fid_def)),
      `cm_spill_frame_fid
         (HD (CMSpillFrame (caller:int)
           (cm_state_fp (st:cm_src_state))
           (caller_spills:(cm_spill)list) ::
           (saved:(cm_spill_frame)list))) == caller`));
  thm saved_fp = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("HD"), cm_spill_frame_fp_def)),
      `cm_spill_frame_fp
         (HD (CMSpillFrame (caller:int)
           (cm_state_fp (st:cm_src_state))
           (caller_spills:(cm_spill)list) ::
           (saved:(cm_spill_frame)list))) ==
       cm_state_fp (st:cm_src_state)`));
  thm outer_exact = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_theorem_by_name("HD"), get_theorem_by_name("TL"),
      cm_spill_frame_spills_def)), outer);
  thm call_iff = specl_rule(TERM_LIST(
      `p:cm_program`, all_regions, `fid:int`, new_fp, all_regions,
      `caller:int`, `cm_state_env (st:cm_src_state)`,
      `cm_state_fp (st:cm_src_state)`,
      `cm_state_regions (st:cm_src_state)`, `ret:cm_type`,
      `parent_temp:int`, `parent_break:int`, `parent_continue:int`,
      `tail:(cm_acursor)list`, `[]:(cm_spill)list`,
      `CMSpillFrame (caller:int) (cm_state_fp st)
         (caller_spills:(cm_spill)list) ::
       (saved:(cm_spill_frame)list)`,
      `CMCallSimFrame ${new_fp:int} (cm_state_fp st)
         (returnpc:int) :: (calls:(cm_call_sim_frame)list)`),
      cm_runtime_stack_call_cons);
  struct dest_eq_results call_parts = dest_eq(concl(call_iff));
  thm facts = conj_rule(prefix,
      conj_rule(segment,
        conj_rule(spill_empty,
          conj_rule(saved_nonempty,
            conj_rule(calls_nonempty,
              conj_rule(call_base,
                conj_rule(call_saved,
                  conj_rule(saved_fid,
                    conj_rule(saved_fp, outer_exact)))))))));
  thm body_reduction = apply_conversion(then_conv(
      reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("HD"), get_theorem_by_name("TL"))),
      reduce_rewrite_conv(THM_LIST(
        cm_call_sim_base_def, cm_call_sim_saved_def,
        cm_spill_frame_fid_def, cm_spill_frame_fp_def,
        cm_spill_frame_spills_def))), call_parts.tm2);
  struct dest_eq_results body_parts =
      dest_eq(concl(body_reduction));
  thm normalized_body = mp_rule(taut_rule(mk_imp(
      concl(facts), body_parts.tm2)), facts);
  thm body = eq_mp_rule(sym_rule(body_reduction),
      normalized_body);
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(call_iff), body));
  return gnode_prove(root);
}
PROOF thm cm_runtime_stack_enter_call =
    cm_prove_runtime_stack_enter_call();

PROOF static thm cm_prove_activate_local_structure(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (slot:int) (st:cm_src_state).
         cm_state_fp (cm_activate_local p fid slot st) ==
           cm_state_fp st &&
         cm_state_nextgen (cm_activate_local p fid slot st) ==
           cm_state_nextgen st + 1i &&
         cm_state_regions (cm_activate_local p fid slot st) ==
           CMRegion (cm_state_nextgen st)
             (cm_local_base p fid slot (cm_state_fp st)) 0i
             (cm_slot_size (cm_program_structs p)
               (inth slot (cm_function_locals
                 (inth fid (cm_program_functions p))))) T T ::
           cm_state_regions st`);
  gnode leaf = AUTO_INTROS_TAC(root);
  conv activate_reduction = then_conv(
      rewrite_conv(THM_LIST(get_cm_activate_local_def())),
      reduce_rewrite_conv(get_cm_state_core_defs()));
  thm fp = apply_conversion(activate_reduction,
      `cm_state_fp
        (cm_activate_local (p:cm_program) (fid:int)
          (slot:int) (st:cm_src_state))`);
  thm nextgen = apply_conversion(activate_reduction,
      `cm_state_nextgen
        (cm_activate_local (p:cm_program) (fid:int)
          (slot:int) (st:cm_src_state))`);
  thm regions = apply_conversion(activate_reduction,
      `cm_state_regions
        (cm_activate_local (p:cm_program) (fid:int)
          (slot:int) (st:cm_src_state))`);
  ACCEPT_TAC(leaf, conj_rule(fp, conj_rule(nextgen, regions)));
  return gnode_prove(root);
}
PROOF thm cm_activate_local_structure =
    cm_prove_activate_local_structure();

PROOF static thm cm_prove_runtime_stack_activate_local(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (slot:int) (st:cm_src_state)
         (cursors:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         cm_function_wf p
           (inth fid (cm_program_functions p)) ==>
         0i <= fid ==>
         0i <= slot ==>
         slot < ilength
           (cm_function_locals
             (inth fid (cm_program_functions p))) ==>
         cm_regions_before
           (cm_state_regions st) (cm_state_nextgen st) ==>
         cm_runtime_stack p (cm_state_regions st) fid
           (cm_state_fp st) (cm_state_regions st) cursors
           spills saved calls ==>
         cm_runtime_stack p
           (CMRegion (cm_state_nextgen st)
              (cm_local_base p fid slot (cm_state_fp st)) 0i
              (cm_slot_size (cm_program_structs p)
                (inth slot (cm_function_locals
                  (inth fid (cm_program_functions p))))) T T ::
            cm_state_regions st)
           fid (cm_state_fp st)
           (CMRegion (cm_state_nextgen st)
              (cm_local_base p fid slot (cm_state_fp st)) 0i
              (cm_slot_size (cm_program_structs p)
                (inth slot (cm_function_locals
                  (inth fid (cm_program_functions p))))) T T ::
            cm_state_regions st)
           cursors spills saved calls`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term region =
      `CMRegion (cm_state_nextgen (st:cm_src_state))
        (cm_local_base (p:cm_program) (fid:int) (slot:int)
          (cm_state_fp st)) 0i
        (cm_slot_size (cm_program_structs p)
          (inth slot (cm_function_locals
            (inth fid (cm_program_functions p))))) T T`;
  thm frame = match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `cm_state_fp (st:cm_src_state)`,
        `cm_state_nextgen (st:cm_src_state)`,
        `cm_state_regions (st:cm_src_state)`, `slot:int`),
        cm_local_region_frame_safe),
      assume_rule(
        `cm_function_wf (p:cm_program)
          (inth (fid:int) (cm_program_functions p))`)),
      assume_rule(`0i <= (slot:int)`)),
      assume_rule(
        `(slot:int) <
         ilength (cm_function_locals
           (inth (fid:int) (cm_program_functions (p:cm_program))))`));
  thm generation_value = apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_cm_region_gen_def())),
      `cm_region_gen ${region:cm_region}`);
  thm generation = mp_rule(int_arith_rule(mk_imp(
      concl(generation_value),
      `cm_state_nextgen (st:cm_src_state) <=
       cm_region_gen ${region:cm_region}`)), generation_value);
  thm result = match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(match_mp_rule(
        specl_rule(TERM_LIST(
          `p:cm_program`, region,
          `cm_state_regions (st:cm_src_state)`,
          `cm_state_nextgen (st:cm_src_state)`, `fid:int`,
          `cm_state_fp (st:cm_src_state)`,
          `cursors:(cm_acursor)list`, `spills:(cm_spill)list`,
          `saved:(cm_spill_frame)list`,
          `calls:(cm_call_sim_frame)list`),
          cm_runtime_stack_fresh_cons),
        assume_rule(`0i <= (fid:int)`)),
        assume_rule(
          `cm_regions_before
            (cm_state_regions (st:cm_src_state))
            (cm_state_nextgen st)`)),
      generation), frame),
      assume_rule(
        `cm_runtime_stack
          (p:cm_program) (cm_state_regions (st:cm_src_state))
          (fid:int) (cm_state_fp st) (cm_state_regions st)
          (cursors:(cm_acursor)list) (spills:(cm_spill)list)
          (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list)`));
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_runtime_stack_activate_local =
    cm_prove_runtime_stack_activate_local();

PROOF static thm cm_prove_restore_scope_structure(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (oldenv:int->int->cm_value)
         (oldregions:(cm_region)list).
         cm_state_fp (cm_restore_scope st oldenv oldregions) ==
           cm_state_fp st &&
         cm_state_nextgen (cm_restore_scope st oldenv oldregions) ==
           cm_state_nextgen st &&
         cm_state_regions (cm_restore_scope st oldenv oldregions) ==
           cm_restore_regions (cm_state_regions st) oldregions`);
  gnode leaf = AUTO_INTROS_TAC(root);
  conv restore_reduction = then_conv(
      rewrite_conv(THM_LIST(get_cm_restore_scope_def())),
      reduce_rewrite_conv(get_cm_state_core_defs()));
  thm fp = apply_conversion(restore_reduction,
      `cm_state_fp
        (cm_restore_scope (st:cm_src_state)
          (oldenv:int->int->cm_value)
          (oldregions:(cm_region)list))`);
  thm nextgen = apply_conversion(restore_reduction,
      `cm_state_nextgen
        (cm_restore_scope (st:cm_src_state)
          (oldenv:int->int->cm_value)
          (oldregions:(cm_region)list))`);
  thm regions = apply_conversion(restore_reduction,
      `cm_state_regions
        (cm_restore_scope (st:cm_src_state)
          (oldenv:int->int->cm_value)
          (oldregions:(cm_region)list))`);
  ACCEPT_TAC(leaf, conj_rule(fp, conj_rule(nextgen, regions)));
  return gnode_prove(root);
}
PROOF thm cm_restore_scope_structure =
    cm_prove_restore_scope_structure();

PROOF static thm cm_prove_restore_call_structure(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (oldenv:int->int->cm_value)
         (oldfp:int) (oldregions:(cm_region)list).
         cm_state_fp
           (cm_restore_call st oldenv oldfp oldregions) == oldfp &&
         cm_state_nextgen
           (cm_restore_call st oldenv oldfp oldregions) ==
           cm_state_nextgen st &&
         cm_state_regions
           (cm_restore_call st oldenv oldfp oldregions) ==
           cm_restore_regions (cm_state_regions st) oldregions`);
  gnode leaf = AUTO_INTROS_TAC(root);
  conv restore_reduction = then_conv(
      rewrite_conv(THM_LIST(get_cm_restore_call_def())),
      reduce_rewrite_conv(get_cm_state_core_defs()));
  thm fp = apply_conversion(restore_reduction,
      `cm_state_fp
        (cm_restore_call (st:cm_src_state)
          (oldenv:int->int->cm_value) (oldfp:int)
          (oldregions:(cm_region)list))`);
  thm nextgen = apply_conversion(restore_reduction,
      `cm_state_nextgen
        (cm_restore_call (st:cm_src_state)
          (oldenv:int->int->cm_value) (oldfp:int)
          (oldregions:(cm_region)list))`);
  thm regions = apply_conversion(restore_reduction,
      `cm_state_regions
        (cm_restore_call (st:cm_src_state)
          (oldenv:int->int->cm_value) (oldfp:int)
          (oldregions:(cm_region)list))`);
  ACCEPT_TAC(leaf, conj_rule(fp, conj_rule(nextgen, regions)));
  return gnode_prove(root);
}
PROOF thm cm_restore_call_structure =
    cm_prove_restore_call_structure();

PROOF static thm cm_prove_runtime_stack_enter_scope(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (regions:(cm_region)list)
         (fid:int) (fp:int) (phase:cm_aphase)
         (temp:int) (breakpc:int) (continuepc:int)
         (rest:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         0i <= fid ==>
         cm_phase_is_scope phase ==>
         ~cm_phase_is_call phase ==>
         cm_phase_oldregions phase == regions ==>
         cm_runtime_stack p regions fid fp regions rest
           spills saved calls ==>
         cm_runtime_stack p regions fid fp regions
           (CMACursor phase temp breakpc continuepc :: rest)
           spills saved calls`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm stack_iff = match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `regions:(cm_region)list`, `fid:int`,
        `fp:int`, `regions:(cm_region)list`, `phase:cm_aphase`,
        `regions:(cm_region)list`, `temp:int`, `breakpc:int`,
        `continuepc:int`, `rest:(cm_acursor)list`,
        `spills:(cm_spill)list`, `saved:(cm_spill_frame)list`,
        `calls:(cm_call_sim_frame)list`),
        cm_runtime_stack_scope_cons),
      assume_rule(`cm_phase_is_scope (phase:cm_aphase)`)),
      assume_rule(`~cm_phase_is_call (phase:cm_aphase)`)),
      assume_rule(
        `cm_phase_oldregions (phase:cm_aphase) ==
         (regions:(cm_region)list)`));
  thm body = conj_rule(assume_rule(`0i <= (fid:int)`),
      conj_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `regions:(cm_region)list`,
        `fid:int`, `fp:int`, `regions:(cm_region)list`),
        cm_region_prefix_safe_refl),
      assume_rule(
        `cm_runtime_stack
          (p:cm_program) (regions:(cm_region)list)
          (fid:int) (fp:int) regions (rest:(cm_acursor)list)
          (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list)`)));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(stack_iff), body));
  return gnode_prove(root);
}
PROOF thm cm_runtime_stack_enter_scope =
    cm_prove_runtime_stack_enter_scope();

PROOF static thm cm_prove_runtime_stack_leave_scope(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (active:(cm_region)list)
         (fid:int) (fp:int) (phase:cm_aphase)
         (oldregions:(cm_region)list)
         (temp:int) (breakpc:int) (continuepc:int)
         (rest:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         cm_phase_is_scope phase ==>
         ~cm_phase_is_call phase ==>
         cm_phase_oldregions phase == oldregions ==>
         cm_runtime_stack p active fid fp active
           (CMACursor phase temp breakpc continuepc :: rest)
           spills saved calls ==>
         cm_runtime_stack p
           (cm_restore_regions active oldregions)
           fid fp (cm_restore_regions active oldregions)
           rest spills saved calls`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm stack_iff = match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `active:(cm_region)list`, `fid:int`,
        `fp:int`, `active:(cm_region)list`, `phase:cm_aphase`,
        `oldregions:(cm_region)list`, `temp:int`, `breakpc:int`,
        `continuepc:int`, `rest:(cm_acursor)list`,
        `spills:(cm_spill)list`, `saved:(cm_spill_frame)list`,
        `calls:(cm_call_sim_frame)list`),
        cm_runtime_stack_scope_cons),
      assume_rule(`cm_phase_is_scope (phase:cm_aphase)`)),
      assume_rule(`~cm_phase_is_call (phase:cm_aphase)`)),
      assume_rule(
        `cm_phase_oldregions (phase:cm_aphase) ==
         (oldregions:(cm_region)list)`));
  thm opened = eq_mp_rule(stack_iff, assume_rule(
      `cm_runtime_stack (p:cm_program)
        (active:(cm_region)list) (fid:int) (fp:int) active
        (CMACursor (phase:cm_aphase)
           (temp:int) (breakpc:int) (continuepc:int) ::
         (rest:(cm_acursor)list))
        (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`));
  thm prefix = conjunct1_rule(conjunct2_rule(opened));
  thm outer = conjunct2_rule(conjunct2_rule(opened));
  ACCEPT_TAC(leaf, match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `fp:int`,
        `active:(cm_region)list`, `oldregions:(cm_region)list`,
        `fid:int`, `fp:int`, `rest:(cm_acursor)list`,
        `spills:(cm_spill)list`, `saved:(cm_spill_frame)list`,
        `calls:(cm_call_sim_frame)list`),
        cm_runtime_stack_restore),
      prefix), outer));
  return gnode_prove(root);
}
PROOF thm cm_runtime_stack_leave_scope =
    cm_prove_runtime_stack_leave_scope();

PROOF static thm cm_prove_runtime_stack_leave_call(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (active:(cm_region)list)
         (fid:int) (fp:int) (caller:int)
         (oldenv:int->int->cm_value) (oldfp:int)
         (oldregions:(cm_region)list) (ret:cm_type)
         (temp:int) (breakpc:int) (continuepc:int)
         (rest:(cm_acursor)list) (spills:(cm_spill)list)
         (caller_spills:(cm_spill)list)
         (saved:(cm_spill_frame)list) (returnpc:int)
         (calls:(cm_call_sim_frame)list).
         cm_runtime_stack p active fid fp active
           (CMACursor
              (CACallP caller oldenv oldfp oldregions ret)
              temp breakpc continuepc :: rest)
           spills
           (CMSpillFrame caller oldfp caller_spills :: saved)
           (CMCallSimFrame fp oldfp returnpc :: calls) ==>
         cm_runtime_stack p
           (cm_restore_regions active oldregions)
           caller oldfp (cm_restore_regions active oldregions)
           rest caller_spills saved calls`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm stack_iff = specl_rule(TERM_LIST(
      `p:cm_program`, `active:(cm_region)list`, `fid:int`,
      `fp:int`, `active:(cm_region)list`, `caller:int`,
      `oldenv:int->int->cm_value`, `oldfp:int`,
      `oldregions:(cm_region)list`, `ret:cm_type`,
      `temp:int`, `breakpc:int`, `continuepc:int`,
      `rest:(cm_acursor)list`, `spills:(cm_spill)list`,
      `CMSpillFrame (caller:int) (oldfp:int)
         (caller_spills:(cm_spill)list) ::
       (saved:(cm_spill_frame)list)`,
      `CMCallSimFrame (fp:int) (oldfp:int) (returnpc:int) ::
       (calls:(cm_call_sim_frame)list)`),
      cm_runtime_stack_call_cons);
  thm opened = eq_mp_rule(stack_iff, assume_rule(
      `cm_runtime_stack (p:cm_program)
        (active:(cm_region)list) (fid:int) (fp:int) active
        (CMACursor
           (CACallP (caller:int) (oldenv:int->int->cm_value)
             (oldfp:int) (oldregions:(cm_region)list) (ret:cm_type))
           (temp:int) (breakpc:int) (continuepc:int) ::
         (rest:(cm_acursor)list))
        (spills:(cm_spill)list)
        (CMSpillFrame caller oldfp
           (caller_spills:(cm_spill)list) :: saved)
        (CMCallSimFrame fp oldfp (returnpc:int) :: calls)`));
  thm prefix = conjunct1_rule(opened);
  thm outer = opened;
  for (size_t index = 0; index < 9; ++index) {
    outer = conjunct2_rule(outer);
  }
  thm outer_exact = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_theorem_by_name("HD"), get_theorem_by_name("TL"),
      cm_spill_frame_spills_def)), outer);
  ACCEPT_TAC(leaf, match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `fp:int`,
        `active:(cm_region)list`, `oldregions:(cm_region)list`,
        `caller:int`, `oldfp:int`, `rest:(cm_acursor)list`,
        `caller_spills:(cm_spill)list`,
        `saved:(cm_spill_frame)list`,
        `calls:(cm_call_sim_frame)list`),
        cm_runtime_stack_restore),
      prefix), outer_exact));
  return gnode_prove(root);
}
PROOF thm cm_runtime_stack_leave_call =
    cm_prove_runtime_stack_leave_call();

PROOF static thm cm_prove_runtime_stack_plain_push(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (regions:(cm_region)list)
         (fid:int) (fp:int) (phase:cm_aphase)
         (temp:int) (breakpc:int) (continuepc:int)
         (rest:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         ~cm_phase_is_call phase ==>
         ~cm_phase_is_scope phase ==>
         ~cm_phase_is_halt phase ==>
         cm_runtime_stack p regions fid fp regions rest
           spills saved calls ==>
         cm_runtime_stack p regions fid fp regions
           (CMACursor phase temp breakpc continuepc :: rest)
           spills saved calls`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm stack_iff = match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `regions:(cm_region)list`, `fid:int`,
        `fp:int`, `regions:(cm_region)list`, `phase:cm_aphase`,
        `temp:int`, `breakpc:int`, `continuepc:int`,
        `rest:(cm_acursor)list`, `spills:(cm_spill)list`,
        `saved:(cm_spill_frame)list`,
        `calls:(cm_call_sim_frame)list`),
        cm_runtime_stack_plain_cons),
      assume_rule(`~cm_phase_is_call (phase:cm_aphase)`)),
      assume_rule(`~cm_phase_is_scope (phase:cm_aphase)`)),
      assume_rule(`~cm_phase_is_halt (phase:cm_aphase)`));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(stack_iff), assume_rule(
      `cm_runtime_stack (p:cm_program)
        (regions:(cm_region)list) (fid:int) (fp:int) regions
        (rest:(cm_acursor)list) (spills:(cm_spill)list)
        (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`)));
  return gnode_prove(root);
}
PROOF thm cm_runtime_stack_plain_push =
    cm_prove_runtime_stack_plain_push();

PROOF static thm cm_prove_runtime_stack_plain_pop(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (regions:(cm_region)list)
         (fid:int) (fp:int) (phase:cm_aphase)
         (temp:int) (breakpc:int) (continuepc:int)
         (rest:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         ~cm_phase_is_call phase ==>
         ~cm_phase_is_scope phase ==>
         ~cm_phase_is_halt phase ==>
         cm_runtime_stack p regions fid fp regions
           (CMACursor phase temp breakpc continuepc :: rest)
           spills saved calls ==>
         cm_runtime_stack p regions fid fp regions rest
           spills saved calls`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm stack_iff = match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `regions:(cm_region)list`, `fid:int`,
        `fp:int`, `regions:(cm_region)list`, `phase:cm_aphase`,
        `temp:int`, `breakpc:int`, `continuepc:int`,
        `rest:(cm_acursor)list`, `spills:(cm_spill)list`,
        `saved:(cm_spill_frame)list`,
        `calls:(cm_call_sim_frame)list`),
        cm_runtime_stack_plain_cons),
      assume_rule(`~cm_phase_is_call (phase:cm_aphase)`)),
      assume_rule(`~cm_phase_is_scope (phase:cm_aphase)`)),
      assume_rule(`~cm_phase_is_halt (phase:cm_aphase)`));
  ACCEPT_TAC(leaf, eq_mp_rule(stack_iff, assume_rule(
      `cm_runtime_stack (p:cm_program)
        (regions:(cm_region)list) (fid:int) (fp:int) regions
        (CMACursor (phase:cm_aphase)
           (temp:int) (breakpc:int) (continuepc:int) ::
         (rest:(cm_acursor)list))
        (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`)));
  return gnode_prove(root);
}
PROOF thm cm_runtime_stack_plain_pop =
    cm_prove_runtime_stack_plain_pop();

PROOF static thm cm_prove_runtime_stack_plain_replace(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (regions:(cm_region)list)
         (fid:int) (fp:int) (oldphase:cm_aphase)
         (newphase:cm_aphase)
         (oldtemp:int) (oldbreak:int) (oldcontinue:int)
         (newtemp:int) (newbreak:int) (newcontinue:int)
         (rest:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         ~cm_phase_is_call oldphase ==>
         ~cm_phase_is_scope oldphase ==>
         ~cm_phase_is_halt oldphase ==>
         ~cm_phase_is_call newphase ==>
         ~cm_phase_is_scope newphase ==>
         ~cm_phase_is_halt newphase ==>
         cm_runtime_stack p regions fid fp regions
           (CMACursor oldphase oldtemp oldbreak oldcontinue :: rest)
           spills saved calls ==>
         cm_runtime_stack p regions fid fp regions
           (CMACursor newphase newtemp newbreak newcontinue :: rest)
           spills saved calls`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm popped = match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `regions:(cm_region)list`, `fid:int`,
        `fp:int`, `oldphase:cm_aphase`, `oldtemp:int`,
        `oldbreak:int`, `oldcontinue:int`,
        `rest:(cm_acursor)list`, `spills:(cm_spill)list`,
        `saved:(cm_spill_frame)list`,
        `calls:(cm_call_sim_frame)list`),
        cm_runtime_stack_plain_pop),
      assume_rule(`~cm_phase_is_call (oldphase:cm_aphase)`)),
      assume_rule(`~cm_phase_is_scope (oldphase:cm_aphase)`)),
      assume_rule(`~cm_phase_is_halt (oldphase:cm_aphase)`)),
      assume_rule(
        `cm_runtime_stack (p:cm_program)
          (regions:(cm_region)list) (fid:int) (fp:int) regions
          (CMACursor (oldphase:cm_aphase)
             (oldtemp:int) (oldbreak:int) (oldcontinue:int) ::
           (rest:(cm_acursor)list))
          (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list)`));
  ACCEPT_TAC(leaf, match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `regions:(cm_region)list`, `fid:int`,
        `fp:int`, `newphase:cm_aphase`, `newtemp:int`,
        `newbreak:int`, `newcontinue:int`,
        `rest:(cm_acursor)list`, `spills:(cm_spill)list`,
        `saved:(cm_spill_frame)list`,
        `calls:(cm_call_sim_frame)list`),
        cm_runtime_stack_plain_push),
      assume_rule(`~cm_phase_is_call (newphase:cm_aphase)`)),
      assume_rule(`~cm_phase_is_scope (newphase:cm_aphase)`)),
      assume_rule(`~cm_phase_is_halt (newphase:cm_aphase)`)),
      popped));
  return gnode_prove(root);
}
PROOF thm cm_runtime_stack_plain_replace =
    cm_prove_runtime_stack_plain_replace();

PROOF static thm cm_prove_spills_within_remove(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (fp:int) (oldfp:int)
         (slot:int) (spills:(cm_spill)list).
         cm_spills_within_frame p fid fp oldfp spills ==>
         cm_spills_within_frame p fid fp oldfp
           (cm_spill_remove slot spills)`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_fid = GEN_TAC(with_program, "fid");
  gnode with_fp = GEN_TAC(with_fid, "fp");
  gnode with_oldfp = GEN_TAC(with_fp, "oldfp");
  gnode with_slot = GEN_TAC(with_oldfp, "slot");
  gnode_list cases =
      INDUCT_TAC(with_slot, `spills:(cm_spill)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        cm_spill_remove_def, cm_spills_within_frame_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm within = conv_rule(rewrite_conv(THM_LIST(
        cm_spills_within_frame_def)), assume_rule(
          `cm_spills_within_frame
            (p:cm_program) (fid:int) (fp:int) (oldfp:int)
            ((a0:cm_spill) :: (a1:(cm_spill)list))`));
    thm tail_within = conjunct2_rule(conjunct2_rule(within));
    thm ih = match_mp_rule(assume_rule(
        `cm_spills_within_frame
           (p:cm_program) (fid:int) (fp:int) (oldfp:int)
           (a1:(cm_spill)list) ==>
         cm_spills_within_frame p fid fp oldfp
           (cm_spill_remove (slot:int) a1)`), tail_within);
    gnode_list equal_cases = BOOL_CASES_TAC(
        leaf,
        `cm_spill_slot (a0:cm_spill) == (slot:int)`,
        "Hspill_slot");
    {
      gnode reduced = CONV_TAC(equal_cases[0],
          reduce_rewrite_conv(THM_LIST(
            cm_spill_remove_def,
            assume_rule(
              `cm_spill_slot (a0:cm_spill) == (slot:int)`))));
      ACCEPT_TAC(reduced, ih);
    }
    {
      gnode reduced = CONV_TAC(equal_cases[1],
          reduce_rewrite_conv(THM_LIST(
            cm_spill_remove_def, cm_spills_within_frame_def,
            assume_rule(
              `~(cm_spill_slot (a0:cm_spill) == (slot:int))`))));
      ACCEPT_TAC(reduced, conj_rule(conjunct1_rule(within),
          conj_rule(conjunct1_rule(conjunct2_rule(within)), ih)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_spills_within_remove =
    cm_prove_spills_within_remove();

PROOF static thm cm_prove_spills_within_put(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (fp:int) (oldfp:int)
         (slot:int) (spill_value:cm_value) (spills:(cm_spill)list).
         cm_frame_segment p fid fp oldfp ==>
         0i <= slot ==>
         slot < cm_stemps
           (cm_function_body
             (inth fid (cm_program_functions p))) ==>
         cm_spills_within_frame p fid fp oldfp spills ==>
         cm_spills_within_frame p fid fp oldfp
           (cm_spill_put slot spill_value spills)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm frame = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_frame_segment_def, get_cm_frame_size_def(),
      get_cm_temp_slots_def(), get_cm_temp_offset_def())),
      assume_rule(
        `cm_frame_segment
          (p:cm_program) (fid:int) (fp:int) (oldfp:int)`));
  term head_conditions =
      `(fp:int) + cm_temp_offset (p:cm_program) (fid:int) 0i <=
         fp + cm_temp_offset p fid (slot:int) &&
       fp + cm_temp_offset p fid slot + 8i <= (oldfp:int)`;
  thm head_reduction = apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_cm_temp_offset_def())),
      head_conditions);
  struct dest_eq_results head_parts =
      dest_eq(concl(head_reduction));
  thm numeric_facts = conj_rule(frame,
      conj_rule(assume_rule(`0i <= (slot:int)`),
        assume_rule(
          `(slot:int) <
           cm_stemps
             (cm_function_body
               (inth (fid:int)
                 (cm_program_functions (p:cm_program))))`)));
  thm normalized_head = mp_rule(int_arith_rule(mk_imp(
      concl(numeric_facts), head_parts.tm2)), numeric_facts);
  thm head = eq_mp_rule(sym_rule(head_reduction),
      normalized_head);
  thm tail = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `fp:int`, `oldfp:int`,
      `slot:int`, `spills:(cm_spill)list`),
      cm_spills_within_remove), assume_rule(
        `cm_spills_within_frame
          (p:cm_program) (fid:int) (fp:int) (oldfp:int)
          (spills:(cm_spill)list)`));
  gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      cm_spill_put_def, cm_spills_within_frame_def,
      cm_spill_slot_def)));
  ACCEPT_TAC(reduced, conj_rule(conjunct1_rule(head),
      conj_rule(conjunct2_rule(head), tail)));
  return gnode_prove(root);
}
PROOF thm cm_spills_within_put =
    cm_prove_spills_within_put();

PROOF static thm cm_prove_runtime_stack_spill_put(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (all_regions:(cm_region)list)
         (fid:int) (fp:int) (cursors:(cm_acursor)list).
         !(active:(cm_region)list) (slot:int)
           (spill_value:cm_value) (spills:(cm_spill)list)
           (saved:(cm_spill_frame)list)
           (calls:(cm_call_sim_frame)list).
         0i <= fid ==>
         0i <= slot ==>
         slot < cm_stemps
           (cm_function_body
             (inth fid (cm_program_functions p))) ==>
         cm_runtime_stack p all_regions fid fp active cursors
           spills saved calls ==>
         cm_runtime_stack p all_regions fid fp active cursors
           (cm_spill_put slot spill_value spills) saved calls`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_all = GEN_TAC(with_program, "all_regions");
  gnode with_fid = GEN_TAC(with_all, "fid");
  gnode with_fp = GEN_TAC(with_fid, "fp");
  gnode_list cases =
      INDUCT_TAC(with_fp, `cursors:(cm_acursor)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        cm_runtime_stack_def)), assume_rule(
          `cm_runtime_stack
            (p:cm_program) (all_regions:(cm_region)list)
            (fid:int) (fp:int) (active:(cm_region)list)
            ([]:(cm_acursor)list) (spills:(cm_spill)list)
            (saved:(cm_spill_frame)list)
            (calls:(cm_call_sim_frame)list)`));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    term phase = `cm_cursor_phase (a0:cm_acursor)`;
    thm stack = assume_rule(
        `cm_runtime_stack
          (p:cm_program) (all_regions:(cm_region)list)
          (fid:int) (fp:int) (active:(cm_region)list)
          ((a0:cm_acursor) :: (a1:(cm_acursor)list))
          (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list)`);
    term ih_body =
        `!(active:(cm_region)list) (slot:int)
           (spill_value:cm_value) (spills:(cm_spill)list)
           (saved:(cm_spill_frame)list)
           (calls:(cm_call_sim_frame)list).
           0i <= (fid:int) ==>
           0i <= slot ==>
           slot < cm_stemps
             (cm_function_body
               (inth fid (cm_program_functions (p:cm_program)))) ==>
           cm_runtime_stack p (all_regions:(cm_region)list)
             fid (fp:int) active (a1:(cm_acursor)list)
             spills saved calls ==>
           cm_runtime_stack p all_regions fid fp active a1
             (cm_spill_put slot spill_value spills) saved calls`;
    thm ih = assume_rule(ih_body);
    gnode_list call_cases = BOOL_CASES_TAC(
        leaf, `cm_phase_is_call ${phase:cm_aphase}`, "Hspill_call");
    {
      thm call = assume_rule(
          `cm_phase_is_call ${phase:cm_aphase}`);
      thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_runtime_stack_def, call)), stack);
      thm segment = conjunct1_rule(conjunct2_rule(opened));
      thm within =
          conjunct1_rule(conjunct2_rule(conjunct2_rule(opened)));
      thm updated = match_mp_rule(match_mp_rule(match_mp_rule(
          match_mp_rule(specl_rule(TERM_LIST(
            `p:cm_program`, `fid:int`, `fp:int`,
            `cm_phase_oldfp ${phase:cm_aphase}`,
            `slot:int`, `spill_value:cm_value`,
            `spills:(cm_spill)list`),
            cm_spills_within_put),
          segment), assume_rule(`0i <= (slot:int)`)),
          assume_rule(
            `(slot:int) <
             cm_stemps
               (cm_function_body
                 (inth (fid:int)
                   (cm_program_functions (p:cm_program))))`)),
          within);
      gnode reduced = CONV_TAC(call_cases[0],
          reduce_rewrite_conv(THM_LIST(
            cm_runtime_stack_def, call)));
      thm facts = conj_rule(opened, updated);
      ACCEPT_TAC(reduced, mp_rule(taut_rule(mk_imp(
          concl(facts), goal_ccl(reduced->g))), facts));
    }
    {
      thm not_call = assume_rule(
          `~cm_phase_is_call ${phase:cm_aphase}`);
      gnode_list scope_cases = BOOL_CASES_TAC(
          call_cases[1], `cm_phase_is_scope ${phase:cm_aphase}`,
          "Hspill_scope");
      {
        thm scope = assume_rule(
            `cm_phase_is_scope ${phase:cm_aphase}`);
        thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
            cm_runtime_stack_def, not_call, scope)), stack);
        thm outer = conjunct2_rule(conjunct2_rule(opened));
        thm updated_outer = match_mp_rule(match_mp_rule(
            match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
              `cm_phase_oldregions ${phase:cm_aphase}`,
              `slot:int`, `spill_value:cm_value`,
              `spills:(cm_spill)list`,
              `saved:(cm_spill_frame)list`,
              `calls:(cm_call_sim_frame)list`), ih),
            assume_rule(`0i <= (fid:int)`)),
            assume_rule(`0i <= (slot:int)`)),
            assume_rule(
              `(slot:int) <
               cm_stemps
                 (cm_function_body
                   (inth (fid:int)
                     (cm_program_functions (p:cm_program))))`)),
            outer);
        gnode reduced = CONV_TAC(scope_cases[0],
            reduce_rewrite_conv(THM_LIST(
              cm_runtime_stack_def, not_call, scope)));
        thm facts = conj_rule(opened, updated_outer);
        ACCEPT_TAC(reduced, mp_rule(taut_rule(mk_imp(
            concl(facts), goal_ccl(reduced->g))), facts));
      }
      {
        thm not_scope = assume_rule(
            `~cm_phase_is_scope ${phase:cm_aphase}`);
        gnode_list halt_cases = BOOL_CASES_TAC(
            scope_cases[1], `cm_phase_is_halt ${phase:cm_aphase}`,
            "Hspill_halt");
        {
          thm halt = assume_rule(
              `cm_phase_is_halt ${phase:cm_aphase}`);
          thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
              cm_runtime_stack_def, not_call, not_scope, halt)),
              stack);
          thm fid_halt = conjunct1_rule(opened);
          thm contradiction = mp_rule(int_arith_rule(
              `0i <= (fid:int) ==> fid == --1i ==> F`),
              assume_rule(`0i <= (fid:int)`));
          CONTR_TAC(halt_cases[0],
              mp_rule(contradiction, fid_halt));
        }
        {
          thm not_halt = assume_rule(
              `~cm_phase_is_halt ${phase:cm_aphase}`);
          thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
              cm_runtime_stack_def, not_call, not_scope, not_halt)),
              stack);
          thm updated_outer = match_mp_rule(match_mp_rule(
              match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
                `active:(cm_region)list`, `slot:int`,
                `spill_value:cm_value`, `spills:(cm_spill)list`,
                `saved:(cm_spill_frame)list`,
                `calls:(cm_call_sim_frame)list`), ih),
              assume_rule(`0i <= (fid:int)`)),
              assume_rule(`0i <= (slot:int)`)),
              assume_rule(
                `(slot:int) <
                 cm_stemps
                   (cm_function_body
                     (inth (fid:int)
                       (cm_program_functions (p:cm_program))))`)),
              opened);
          gnode reduced = CONV_TAC(halt_cases[1],
              reduce_rewrite_conv(THM_LIST(
                cm_runtime_stack_def, not_call, not_scope, not_halt)));
          ACCEPT_TAC(reduced, updated_outer);
        }
      }
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_runtime_stack_spill_put =
    cm_prove_runtime_stack_spill_put();

PROOF static thm cm_prove_runtime_stack_spill_remove(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (all_regions:(cm_region)list)
         (fid:int) (fp:int) (cursors:(cm_acursor)list).
         !(active:(cm_region)list) (slot:int)
           (spills:(cm_spill)list)
           (saved:(cm_spill_frame)list)
           (calls:(cm_call_sim_frame)list).
         cm_runtime_stack p all_regions fid fp active cursors
           spills saved calls ==>
         cm_runtime_stack p all_regions fid fp active cursors
           (cm_spill_remove slot spills) saved calls`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_all = GEN_TAC(with_program, "all_regions");
  gnode with_fid = GEN_TAC(with_all, "fid");
  gnode with_fp = GEN_TAC(with_fid, "fp");
  gnode_list cases =
      INDUCT_TAC(with_fp, `cursors:(cm_acursor)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        cm_runtime_stack_def)), assume_rule(
          `cm_runtime_stack
            (p:cm_program) (all_regions:(cm_region)list)
            (fid:int) (fp:int) (active:(cm_region)list)
            ([]:(cm_acursor)list) (spills:(cm_spill)list)
            (saved:(cm_spill_frame)list)
            (calls:(cm_call_sim_frame)list)`));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    term phase = `cm_cursor_phase (a0:cm_acursor)`;
    thm stack = assume_rule(
        `cm_runtime_stack
          (p:cm_program) (all_regions:(cm_region)list)
          (fid:int) (fp:int) (active:(cm_region)list)
          ((a0:cm_acursor) :: (a1:(cm_acursor)list))
          (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list)`);
    thm ih = assume_rule(
        `!(active:(cm_region)list) (slot:int)
           (spills:(cm_spill)list)
           (saved:(cm_spill_frame)list)
           (calls:(cm_call_sim_frame)list).
           cm_runtime_stack
             (p:cm_program) (all_regions:(cm_region)list)
             (fid:int) (fp:int) active
             (a1:(cm_acursor)list) spills saved calls ==>
           cm_runtime_stack p all_regions fid fp active a1
             (cm_spill_remove slot spills) saved calls`);
    gnode_list call_cases = BOOL_CASES_TAC(
        leaf, `cm_phase_is_call ${phase:cm_aphase}`,
        "Hremove_call");
    {
      thm call = assume_rule(
          `cm_phase_is_call ${phase:cm_aphase}`);
      thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_runtime_stack_def, call)), stack);
      thm within =
          conjunct1_rule(conjunct2_rule(conjunct2_rule(opened)));
      thm updated = match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `fp:int`,
          `cm_phase_oldfp ${phase:cm_aphase}`,
          `slot:int`, `spills:(cm_spill)list`),
          cm_spills_within_remove), within);
      gnode reduced = CONV_TAC(call_cases[0],
          reduce_rewrite_conv(THM_LIST(
            cm_runtime_stack_def, call)));
      thm facts = conj_rule(opened, updated);
      ACCEPT_TAC(reduced, mp_rule(taut_rule(mk_imp(
          concl(facts), goal_ccl(reduced->g))), facts));
    }
    {
      thm not_call = assume_rule(
          `~cm_phase_is_call ${phase:cm_aphase}`);
      gnode_list scope_cases = BOOL_CASES_TAC(
          call_cases[1], `cm_phase_is_scope ${phase:cm_aphase}`,
          "Hremove_scope");
      {
        thm scope = assume_rule(
            `cm_phase_is_scope ${phase:cm_aphase}`);
        thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
            cm_runtime_stack_def, not_call, scope)), stack);
        thm outer = conjunct2_rule(conjunct2_rule(opened));
        thm updated_outer = match_mp_rule(specl_rule(TERM_LIST(
            `cm_phase_oldregions ${phase:cm_aphase}`,
            `slot:int`, `spills:(cm_spill)list`,
            `saved:(cm_spill_frame)list`,
            `calls:(cm_call_sim_frame)list`), ih), outer);
        gnode reduced = CONV_TAC(scope_cases[0],
            reduce_rewrite_conv(THM_LIST(
              cm_runtime_stack_def, not_call, scope)));
        thm facts = conj_rule(opened, updated_outer);
        ACCEPT_TAC(reduced, mp_rule(taut_rule(mk_imp(
            concl(facts), goal_ccl(reduced->g))), facts));
      }
      {
        thm not_scope = assume_rule(
            `~cm_phase_is_scope ${phase:cm_aphase}`);
        gnode_list halt_cases = BOOL_CASES_TAC(
            scope_cases[1], `cm_phase_is_halt ${phase:cm_aphase}`,
            "Hremove_halt");
        {
          thm halt = assume_rule(
              `cm_phase_is_halt ${phase:cm_aphase}`);
          thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
              cm_runtime_stack_def, not_call, not_scope, halt)),
              stack);
          thm spills_empty = mp_rule(taut_rule(mk_imp(
              concl(opened), `(spills:(cm_spill)list) == []`)),
              opened);
          thm removed_empty = apply_conversion(
              reduce_rewrite_conv(THM_LIST(
                spills_empty, cm_spill_remove_def)),
              `cm_spill_remove (slot:int)
                (spills:(cm_spill)list)`);
          gnode reduced = CONV_TAC(halt_cases[0],
              reduce_rewrite_conv(THM_LIST(
                cm_runtime_stack_def, not_call, not_scope, halt,
                cm_spill_remove_def)));
          thm facts = conj_rule(opened, removed_empty);
          ACCEPT_TAC(reduced, mp_rule(taut_rule(mk_imp(
              concl(facts), goal_ccl(reduced->g))), facts));
        }
        {
          thm not_halt = assume_rule(
              `~cm_phase_is_halt ${phase:cm_aphase}`);
          thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
              cm_runtime_stack_def, not_call, not_scope, not_halt)),
              stack);
          thm updated_outer = match_mp_rule(specl_rule(TERM_LIST(
              `active:(cm_region)list`, `slot:int`,
              `spills:(cm_spill)list`,
              `saved:(cm_spill_frame)list`,
              `calls:(cm_call_sim_frame)list`), ih), opened);
          gnode reduced = CONV_TAC(halt_cases[1],
              reduce_rewrite_conv(THM_LIST(
                cm_runtime_stack_def, not_call, not_scope, not_halt)));
          ACCEPT_TAC(reduced, updated_outer);
        }
      }
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_runtime_stack_spill_remove =
    cm_prove_runtime_stack_spill_remove();
PROOF static int cmc_preservation_invariant_runtime_final_checks(void) {

  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_invariant_runtime_axioms_before,
      "cmc_preservation_invariant_runtime introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_invariant_runtime_checks =
    cmc_preservation_invariant_runtime_final_checks();
