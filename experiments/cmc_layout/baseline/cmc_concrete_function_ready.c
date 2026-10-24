#include "cmc_concrete_function_ready.h"
#include "cmc_stack_local_syntax.h"
#require "cmc_concrete_code_ready.c"
#require "cmc_concrete_temp_ready.c"
#require "cmc_stack_local_syntax.c"

PROOF static size_t _cmc_function_ready_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_join_ready_facts(const thm_list facts) {
  size_t count = vector_size(facts);
  if (count == 0) abort();
  thm result = facts[count - 1];
  for (size_t i = count - 1; i > 0; --i) {
    result = conj_rule(facts[i - 1], result);
  }
  return result;
}

PROOF static thm cm_i32_from_bounds(
    const term value, const thm bounds) {
  thm view = apply_conversion(rewrite_conv(THM_LIST(
      get_cm_i32_code_count_def())),
      mk_comb(`cm_i32_code_count:int->bool`, value));
  return eq_mp_rule(sym_rule(view), bounds);
}

PROOF static thm cm_prove_function_pcs_current(void) {
  gnode root = gnode_new_with_ccl(
      `!(functions:(cm_function_d)list). !(p:cm_program) fid.
         cm_function_pcs_representable p functions fid ==>
         cm_i32_code_count (cm_function_pc p fid)`);
  gnode_list cases = INDUCT_TAC(root,
      `functions:(cm_function_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm represented = assume_rule(
        `cm_function_pcs_representable (p:cm_program)
          ([]:(cm_function_d)list) (fid:int)`);
    ACCEPT_TAC(leaf, conv_rule(rewrite_conv(THM_LIST(
        get_cm_function_pcs_representable_def())), represented));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm represented = assume_rule(
        `cm_function_pcs_representable (p:cm_program)
          ((a0:cm_function_d) :: (a1:(cm_function_d)list))
          (fid:int)`);
    thm opened = conv_rule(rewrite_conv(THM_LIST(
        get_cm_function_pcs_representable_def())), represented);
    ACCEPT_TAC(leaf, conjunct1_rule(opened));
  }
  return gnode_prove(root);
}
PROOF thm cm_function_pcs_current =
    cm_prove_function_pcs_current();

PROOF static thm cm_prove_function_id_ready_from_wf(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) fid.
         cm_wf_program p ==>
         0i <= fid ==>
         fid < ilength (cm_program_functions p) ==>
         cm_i32_code_count (fid + 1i)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm wf = assume_rule(`cm_wf_program (p:cm_program)`);
  thm lower = assume_rule(`0i <= (fid:int)`);
  thm upper = assume_rule(
      `(fid:int) < ilength (cm_program_functions (p:cm_program))`);
  thm opened = conv_rule(rewrite_conv(THM_LIST(
      get_cm_wf_program_def(), get_cm_codegen_admissible_def())), wf);
  thm model_upper = cm_pick_conjunct(opened,
      `cm_model_code_length (p:cm_program) <= 2147483647i`);
  thm functions_bound = specl_rule(TERM_LIST(
      `cm_program_functions (p:cm_program)`, `p:cm_program`, `0i`),
      cm_functions_length_le_code_size);
  thm model_view = apply_conversion(rewrite_conv(THM_LIST(
      get_cm_model_code_length_def())),
      `cm_model_code_length (p:cm_program)`);
  thm facts = cm_join_ready_facts(THM_LIST(
      lower, upper, model_upper, functions_bound, model_view));
  thm bounds = mp_rule(int_arith_rule(mk_imp(concl(facts),
      `0i <= (fid:int) + 1i && fid + 1i <= 2147483647i`)),
      facts);
  ACCEPT_TAC(leaf, cm_i32_from_bounds(`(fid:int) + 1i`, bounds));
  return gnode_prove(root);
}
PROOF thm cm_function_id_ready_from_wf =
    cm_prove_function_id_ready_from_wf();

PROOF static thm cm_prove_concrete_function_ready_from_wf(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) fid (f:cm_function_d).
         cm_wf_program p ==>
         0i <= fid ==>
         fid < ilength (cm_program_functions p) ==>
         cm_function_counts_representable p fid f ==>
         cm_i32_code_count (cm_function_pc p fid) ==>
         cm_i32_code_count (cm_function_pc p (fid + 1i)) ==>
         cm_concrete_function_ready p fid f`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm wf = assume_rule(`cm_wf_program (p:cm_program)`);
  thm fid_lower = assume_rule(`0i <= (fid:int)`);
  thm fid_upper = assume_rule(
      `(fid:int) < ilength (cm_program_functions (p:cm_program))`);
  thm function_counts = assume_rule(
      `cm_function_counts_representable
        (p:cm_program) (fid:int) (f:cm_function_d)`);
  thm current_i32 = assume_rule(
      `cm_i32_code_count (cm_function_pc (p:cm_program) (fid:int))`);
  thm next_i32 = assume_rule(
      `cm_i32_code_count
        (cm_function_pc (p:cm_program) ((fid:int) + 1i))`);

  thm wf_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_wf_program_def(), get_cm_codegen_admissible_def())), wf);
  thm typed = cm_pick_conjunct(wf_open,
      `cm_typed_program (p:cm_program)`);
  thm typed_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_typed_program_def())), typed);
  thm all_functions = cm_pick_conjunct(typed_open,
      `!i. 0i <= i ==>
         i < ilength (cm_program_functions (p:cm_program)) ==>
         cm_function_wf p (inth i (cm_program_functions p))`);
  thm selected_wf = match_mp_rule(match_mp_rule(
      spec_rule(`fid:int`, all_functions), fid_lower), fid_upper);

  thm count_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_function_counts_representable_def())), function_counts);
  thm function_model = cm_pick_conjunct(count_open,
      `(f:cm_function_d) ==
       inth (fid:int) (cm_program_functions (p:cm_program))`);
  thm param_counts = cm_pick_conjunct(count_open,
      `cm_param_counts_representable
        (cm_function_params (f:cm_function_d))`);
  thm prologue_i32 = cm_pick_conjunct(count_open,
      `cm_i32_code_count
        (cm_function_prologue_count (f:cm_function_d))`);
  thm stmt_counts = cm_pick_conjunct(count_open,
      `cm_stmt_counts_representable (p:cm_program) (fid:int)
        (cm_function_body (f:cm_function_d))`);

  thm concrete_wf = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(function_model))), selected_wf);
  thm function_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_function_wf_def())), concrete_wf);
  thm params_wf_full = cm_pick_conjunct(function_open,
      `cm_params_wf (cm_program_structs (p:cm_program))
        (cm_function_params (f:cm_function_d))`);
  thm params_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_params_wf_def())), params_wf_full);
  thm params_wf = conjunct1_rule(params_open);
  thm locals_wf = cm_pick_conjunct(function_open,
      `cm_slots_wf (cm_program_structs (p:cm_program))
        (cm_function_locals (f:cm_function_d))`);
  thm stmt_wf = cm_pick_conjunct(function_open,
      `cm_stmt_wf (p:cm_program) (f:cm_function_d) F
        (cm_function_body f)`);
  thm frame_upper = cm_pick_conjunct(function_open,
      `cm_frame_size (cm_program_structs (p:cm_program))
        (f:cm_function_d) <= 1048560i`);

  thm temp_ready = mp_rule(specl_rule(TERM_LIST(
      `cm_function_body (f:cm_function_d)`, `p:cm_program`,
      `fid:int`), cm_stmt_temps_ready_with_bound), stmt_counts);
  thm temp_safe = conjunct1_rule(temp_ready);
  thm temp_le_stmt = conjunct2_rule(temp_ready);
  thm temp_bounds = mp_rule(spec_rule(
      `cm_function_body (f:cm_function_d)`,
      get_cm_rep_stmt_temps_safe_bounds()), temp_safe);
  thm temp_nonnegative = conjunct1_rule(temp_bounds);
  thm stmt_nonnegative_facts = conj_rule(
      temp_nonnegative, temp_le_stmt);
  thm stmt_nonnegative = mp_rule(int_arith_rule(mk_imp(
      concl(stmt_nonnegative_facts),
      `0i <= cm_stmt_code_count (p:cm_program) (fid:int)
        (cm_function_body (f:cm_function_d))`)),
      stmt_nonnegative_facts);

  thm current_bounds = conv_rule(rewrite_conv(THM_LIST(
      get_cm_i32_code_count_def())), current_i32);
  thm next_bounds = conv_rule(rewrite_conv(THM_LIST(
      get_cm_i32_code_count_def())), next_i32);
  thm prologue_bounds = conv_rule(rewrite_conv(THM_LIST(
      get_cm_i32_code_count_def())), prologue_i32);
  thm pc_step = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`), cm_function_pc_step),
      conj_rule(fid_lower, fid_upper));
  thm code_count_view = apply_conversion(rewrite_conv(THM_LIST(
      get_cm_function_code_count_def(), sym_rule(function_model))),
      `cm_function_code_count (p:cm_program) (fid:int)`);
  thm pc_facts = cm_join_ready_facts(THM_LIST(
      current_bounds, next_bounds, prologue_bounds,
      stmt_nonnegative, pc_step, code_count_view));
  term body_pc =
      `cm_function_pc (p:cm_program) (fid:int) +
       cm_function_prologue_count (f:cm_function_d)`;
  thm body_bounds = mp_rule(int_arith_rule(mk_imp(
      concl(pc_facts),
      `0i <= cm_function_pc (p:cm_program) (fid:int) +
          cm_function_prologue_count (f:cm_function_d) &&
       cm_function_pc p fid + cm_function_prologue_count f <=
          2147483647i`)), pc_facts);
  thm body_pc_i32 = cm_i32_from_bounds(body_pc, body_bounds);

  term stmt_end_count =
      `(cm_function_pc (p:cm_program) (fid:int) +
        cm_function_prologue_count (f:cm_function_d)) +
       cm_stmt_code_count p fid (cm_function_body f)`;
  thm stmt_end_bounds = mp_rule(int_arith_rule(mk_imp(
      concl(pc_facts),
      `0i <=
         (cm_function_pc (p:cm_program) (fid:int) +
          cm_function_prologue_count (f:cm_function_d)) +
         cm_stmt_code_count p fid (cm_function_body f) &&
       (cm_function_pc p fid + cm_function_prologue_count f) +
         cm_stmt_code_count p fid (cm_function_body f) <=
           2147483647i`)), pc_facts);
  thm stmt_end_count_i32 =
      cm_i32_from_bounds(stmt_end_count, stmt_end_bounds);
  thm stmt_length = specl_rule(TERM_LIST(
      `cm_function_body (f:cm_function_d)`, `p:cm_program`,
      `fid:int`, body_pc, `0i`, `0i`, `0i`),
      get_cm_stmt_code_length());
  term stmt_end_emitted =
      `(cm_function_pc (p:cm_program) (fid:int) +
        cm_function_prologue_count (f:cm_function_d)) +
       ilength (cm_emit_stmt p fid
         (cm_function_pc p fid + cm_function_prologue_count f)
         0i 0i 0i (cm_function_body f))`;
  thm stmt_end_view = apply_conversion(rewrite_conv(THM_LIST(
      stmt_length)),
      mk_comb(`cm_i32_code_count:int->bool`, stmt_end_emitted));
  thm stmt_end_i32 = eq_mp_rule(
      sym_rule(stmt_end_view), stmt_end_count_i32);

  thm params_bridge = mp_rule(specl_rule(TERM_LIST(
      `cm_program_structs (p:cm_program)`,
      `cm_function_params (f:cm_function_d)`),
      cm_rep_members_size_matches), params_wf);
  thm locals_bridge = mp_rule(specl_rule(TERM_LIST(
      `cm_program_structs (p:cm_program)`,
      `cm_function_locals (f:cm_function_d)`),
      cm_rep_members_size_matches), locals_wf);
  thm concrete_frame_upper = conv_rule(rewrite_conv(THM_LIST(
      get_cm_frame_size_def(), get_cm_temp_slots_def(),
      sym_rule(params_bridge), sym_rule(locals_bridge))), frame_upper);
  thm params_nonnegative = mp_rule(specl_rule(TERM_LIST(
      `cm_program_structs (p:cm_program)`,
      `cm_function_params (f:cm_function_d)`),
      get_cm_slots_nonnegative()), params_wf);
  thm locals_nonnegative = mp_rule(specl_rule(TERM_LIST(
      `cm_program_structs (p:cm_program)`,
      `cm_function_locals (f:cm_function_d)`),
      get_cm_slots_nonnegative()), locals_wf);
  thm frame_facts = cm_join_ready_facts(THM_LIST(
      concrete_frame_upper, params_nonnegative,
      locals_nonnegative, temp_nonnegative));
  thm params_upper = mp_rule(int_arith_rule(mk_imp(
      concl(frame_facts),
      `cm_rep_members_size (cm_function_params (f:cm_function_d)) <=
       1048576i`)), frame_facts);
  thm locals_upper = mp_rule(int_arith_rule(mk_imp(
      concl(frame_facts),
      `cm_rep_members_size (cm_function_locals (f:cm_function_d)) <=
       1048576i`)), frame_facts);
  thm params_safe = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `cm_program_structs (p:cm_program)`,
      `cm_function_params (f:cm_function_d)`), get_cm_slots_safe()),
      params_wf), params_upper);
  thm locals_safe = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `cm_program_structs (p:cm_program)`,
      `cm_function_locals (f:cm_function_d)`), get_cm_slots_safe()),
      locals_wf), locals_upper);
  thm frame_i32_upper = mp_rule(int_arith_rule(mk_imp(
      concl(concrete_frame_upper),
      `8i + cm_rep_members_size (cm_function_params (f:cm_function_d)) +
        cm_rep_members_size (cm_function_locals f) +
        8i * cm_stemps (cm_function_body f) <= 2147483647i`)),
      concrete_frame_upper);

  term temp_offset =
      `cm_temp_offset (p:cm_program) (fid:int)
        (cm_stemps (cm_function_body (f:cm_function_d)))`;
  thm temp_offset_view = apply_conversion(rewrite_conv(THM_LIST(
      get_cm_temp_offset_def(), sym_rule(function_model),
      sym_rule(params_bridge), sym_rule(locals_bridge))), temp_offset);
  thm offset_facts = conj_rule(temp_offset_view, concrete_frame_upper);
  thm temp_offset_upper = mp_rule(int_arith_rule(mk_imp(
      concl(offset_facts),
      `cm_temp_offset (p:cm_program) (fid:int)
         (cm_stemps (cm_function_body (f:cm_function_d))) <=
       2147483647i`)), offset_facts);

  thm parts = cm_join_ready_facts(THM_LIST(
      function_model, function_counts, stmt_wf, stmt_counts,
      param_counts, prologue_i32, current_i32, body_pc_i32,
      stmt_end_i32, params_wf, locals_wf, params_safe,
      locals_safe, temp_safe, frame_i32_upper,
      temp_offset_upper, pc_step, next_i32));
  gnode opened_target = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      get_cm_concrete_function_ready_def())));
  ACCEPT_TAC(opened_target, mp_rule(taut_rule(mk_imp(
      concl(parts), goal_ccl(opened_target->g))), parts));
  return gnode_prove(root);
}
PROOF thm cm_concrete_function_ready_from_wf =
    cm_prove_concrete_function_ready_from_wf();

PROOF static thm cm_prove_concrete_functions_suffix_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(functions:(cm_function_d)list). !(p:cm_program) fid.
         cm_wf_program p ==>
         0i <= fid ==>
         fid + ilength functions ==
           ilength (cm_program_functions p) ==>
         cm_functions_counts_representable p functions fid ==>
         cm_function_pcs_representable p functions fid ==>
         cm_concrete_functions_ready p fid functions`);
  gnode_list cases = INDUCT_TAC(root,
      `functions:(cm_function_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_concrete_functions_ready_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm wf = assume_rule(`cm_wf_program (p:cm_program)`);
    thm fid_lower = assume_rule(`0i <= (fid:int)`);
    thm alignment = assume_rule(
        `(fid:int) + ilength
          ((a0:cm_function_d) :: (a1:(cm_function_d)list)) ==
         ilength (cm_program_functions (p:cm_program))`);
    thm counts = assume_rule(
        `cm_functions_counts_representable (p:cm_program)
          ((a0:cm_function_d) :: (a1:(cm_function_d)list))
          (fid:int)`);
    thm pcs = assume_rule(
        `cm_function_pcs_representable (p:cm_program)
          ((a0:cm_function_d) :: (a1:(cm_function_d)list))
          (fid:int)`);
    thm induction = assume_rule(
        `!(p:cm_program) fid.
           cm_wf_program p ==>
           0i <= fid ==>
           fid + ilength (a1:(cm_function_d)list) ==
             ilength (cm_program_functions p) ==>
           cm_functions_counts_representable p a1 fid ==>
           cm_function_pcs_representable p a1 fid ==>
           cm_concrete_functions_ready p fid a1`);

    thm counts_open = conv_rule(rewrite_conv(THM_LIST(
        get_cm_functions_counts_representable_def())), counts);
    thm head_counts = cm_pick_conjunct(counts_open,
        `cm_function_counts_representable
          (p:cm_program) (fid:int) (a0:cm_function_d)`);
    thm tail_counts = cm_pick_conjunct(counts_open,
        `cm_functions_counts_representable (p:cm_program)
          (a1:(cm_function_d)list) ((fid:int) + 1i)`);
    thm pcs_open = conv_rule(rewrite_conv(THM_LIST(
        get_cm_function_pcs_representable_def())), pcs);
    thm current_i32 = conjunct1_rule(pcs_open);
    thm tail_pcs = conjunct2_rule(pcs_open);
    thm next_i32 = mp_rule(specl_rule(TERM_LIST(
        `a1:(cm_function_d)list`, `p:cm_program`,
        `(fid:int) + 1i`), cm_function_pcs_current), tail_pcs);

    thm cons_length = apply_conversion(rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))),
        `ilength ((a0:cm_function_d) :: (a1:(cm_function_d)list))`);
    thm tail_length_nonnegative = ispec_rule(
        `a1:(cm_function_d)list`,
        get_theorem_by_name("ILENGTH_NONNEG"));
    thm numeric = cm_join_ready_facts(THM_LIST(
        fid_lower, alignment, cons_length, tail_length_nonnegative));
    thm fid_upper = mp_rule(int_arith_rule(mk_imp(concl(numeric),
        `(fid:int) < ilength
          (cm_program_functions (p:cm_program))`)), numeric);
    thm tail_lower = mp_rule(int_arith_rule(mk_imp(
        concl(fid_lower), `0i <= (fid:int) + 1i`)), fid_lower);
    thm tail_alignment = mp_rule(int_arith_rule(mk_imp(
        concl(numeric),
        `((fid:int) + 1i) + ilength (a1:(cm_function_d)list) ==
         ilength (cm_program_functions (p:cm_program))`)), numeric);

    thm head_ready = mp_rule(mp_rule(mp_rule(mp_rule(mp_rule(mp_rule(
        specl_rule(TERM_LIST(`p:cm_program`, `fid:int`,
          `a0:cm_function_d`), cm_concrete_function_ready_from_wf),
        wf), fid_lower), fid_upper), head_counts), current_i32), next_i32);
    thm id_ready = mp_rule(mp_rule(mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`), cm_function_id_ready_from_wf),
        wf), fid_lower), fid_upper);
    thm tail_ready = mp_rule(mp_rule(mp_rule(mp_rule(mp_rule(
        specl_rule(TERM_LIST(`p:cm_program`, `(fid:int) + 1i`),
          induction), wf), tail_lower), tail_alignment),
        tail_counts), tail_pcs);
    thm parts = cm_join_ready_facts(THM_LIST(
        id_ready, head_ready, tail_ready));
    gnode opened_target = CONV_TAC(leaf,
        rewrite_conv(THM_LIST(get_cm_concrete_functions_ready_def())));
    ACCEPT_TAC(opened_target, mp_rule(taut_rule(mk_imp(
        concl(parts), goal_ccl(opened_target->g))), parts));
  }
  return gnode_prove(root);
}
PROOF static thm cm_concrete_functions_suffix_ready =
    cm_prove_concrete_functions_suffix_ready();

PROOF static thm cm_prove_concrete_functions_ready_from_wf(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program).
         cm_wf_program p ==>
         cm_concrete_functions_ready p 0i
           (cm_program_functions p)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm wf = assume_rule(`cm_wf_program (p:cm_program)`);
  thm opened = conv_rule(rewrite_conv(THM_LIST(
      get_cm_wf_program_def(), get_cm_codegen_admissible_def())), wf);
  thm count_ready = cm_pick_conjunct(opened,
      `cm_codegen_counts_representable (p:cm_program)`);
  thm count_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_codegen_counts_representable_def())), count_ready);
  thm function_counts = conjunct1_rule(count_open);
  thm function_pcs = conjunct2_rule(count_open);
  thm result = mp_rule(mp_rule(mp_rule(mp_rule(mp_rule(
      specl_rule(TERM_LIST(`cm_program_functions (p:cm_program)`,
        `p:cm_program`, `0i`), cm_concrete_functions_suffix_ready),
      wf), int_arith_rule(`0i <= 0i`)),
      int_arith_rule(
        `0i + ilength (cm_program_functions (p:cm_program)) ==
         ilength (cm_program_functions p)`)),
      function_counts), function_pcs);
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_concrete_functions_ready_from_wf =
    cm_prove_concrete_functions_ready_from_wf();

PROOF static int _cmc_function_ready_no_axioms =
    vector_size(get_all_axioms()) == _cmc_function_ready_axioms_before
        ? 1 : (abort(), 0);
