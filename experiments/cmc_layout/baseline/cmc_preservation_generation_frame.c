#include "proof/proof.h"
#include "userlib/proof.h"
#include "cmc_preservation_generation_frame.h"
#include "cmc_preservation_generation_state.h"

#require "cmc_preservation_generation_state.c"

PROOF static size_t _cmc_preservation_generation_frame_axioms_before =
    vector_size(get_all_axioms());

PROOF static term cm_gfm_app_arg_from_right(
    term application, size_t offset) {
  for (size_t i = 0; i < offset; ++i) {
    application = dest_comb(application).tm1;
  }
  return dest_comb(application).tm2;
}

PROOF static thm cm_prove_frame_generation_below_mono(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (frame:cm_frame)
         (old:int) (new:int).
         old <= new ==>
         cm_frame_generation_below p fid old frame ==>
         cm_frame_generation_below p fid new frame`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`frame:cm_frame`, get_datatype_cases("cm_frame")),
      "Hframe");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(branch->g);
      int index = labeled_term_list_index(assumptions, "Hframe");
      if (!is_exists(assumptions[index].tm)) break;
      branch = ASMP_EXISTS_TAC(branch, "Hframe", NULL);
    }
    thm shape = assume_rule(
        goal_lasmps(branch->g)[labeled_term_list_index(
          goal_lasmps(branch->g), "Hframe")].tm);
    thm source = conv_rule(reduce_rewrite_conv(THM_LIST(
        shape, cm_frame_generation_below_def)), assume_rule(
          `cm_frame_generation_below (p:cm_program) (fid:int)
            (old:int) (frame:cm_frame)`));
    thm result = empty_theorem;
    if (i == 0) {
      result = source;
    } else if (i == 3 || i == 5 || i == 8) {
      term value = cm_gfm_app_arg_from_right(concl(source), 0);
      result = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
          value, `old:int`, `new:int`),
          cm_value_generation_below_mono), assume_rule(
            `(old:int) <= (new:int)`)), source);
    } else if (i == 15 || i == 19 || i == 22) {
      term source_term = concl(source);
      term env = cm_gfm_app_arg_from_right(source_term, 0);
      term source_fid = cm_gfm_app_arg_from_right(source_term, 2);
      result = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, source_fid, env, `old:int`, `new:int`),
          get_cm_env_generation_below_mono()), assume_rule(
            `(old:int) <= (new:int)`)), source);
    } else if (i == 21) {
      term values = cm_gfm_app_arg_from_right(concl(source), 0);
      result = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
          values, `old:int`, `new:int`),
          cm_values_generation_below_mono), assume_rule(
            `(old:int) <= (new:int)`)), source);
    } else {
      CONV_TAC(branch, reduce_rewrite_conv(THM_LIST(
          shape, cm_frame_generation_below_def)));
      continue;
    }
    thm target_view = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          shape, cm_frame_generation_below_def)),
        goal_ccl(branch->g));
    ACCEPT_TAC(branch, eq_mp_rule(sym_rule(target_view), result));
  }
  return gnode_prove(root);
}
PROOF thm cm_frame_generation_below_mono =
    cm_prove_frame_generation_below_mono();

PROOF static thm cm_prove_frames_generation_below_mono(void) {
  gnode root = gnode_new_with_ccl(
      `!(frames:(cm_frame)list).
         !(p:cm_program) (fid:int) (old:int) (new:int).
           old <= new ==>
           cm_frames_generation_below p fid old frames ==>
           cm_frames_generation_below p fid new frames`);
  gnode_list cases = INDUCT_TAC(root, `frames:(cm_frame)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm source = conv_rule(rewrite_conv(THM_LIST(
        cm_frames_generation_below_def)), assume_rule(
          `cm_frames_generation_below (p:cm_program) (fid:int)
            (old:int) ([]:(cm_frame)list)`));
    thm target_view = apply_conversion(rewrite_conv(THM_LIST(
        cm_frames_generation_below_def)), goal_ccl(leaf->g));
    ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), source));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm source = conv_rule(rewrite_conv(THM_LIST(
        cm_frames_generation_below_def)), assume_rule(
          `cm_frames_generation_below (p:cm_program) (fid:int)
            (old:int) ((a0:cm_frame) :: (a1:(cm_frame)list))`));
    thm head = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `a0:cm_frame`, `old:int`, `new:int`),
        cm_frame_generation_below_mono), assume_rule(
          `(old:int) <= (new:int)`)), conjunct1_rule(source));
    thm ih = assume_rule(goal_lasmps(leaf->g)[0].tm);
    thm tail = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`,
        `cm_frame_parent_fid (a0:cm_frame) (fid:int)`,
        `old:int`, `new:int`), ih), assume_rule(
          `(old:int) <= (new:int)`)), conjunct2_rule(source));
    thm body = conj_rule(head, tail);
    thm target_view = apply_conversion(rewrite_conv(THM_LIST(
        cm_frames_generation_below_def)), goal_ccl(leaf->g));
    ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), body));
  }
  return gnode_prove(root);
}
PROOF thm cm_frames_generation_below_mono =
    cm_prove_frames_generation_below_mono();

PROOF static int cmc_preservation_generation_frame_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_generation_frame_axioms_before,
      "cmc_preservation_generation_frame introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_frames_generation_below_mono)) == 0,
      "frame generation monotonicity theorem is not closed");
  return 0;
err:
  return -1;
}

PROOF static int _cmc_preservation_generation_frame_checks =
    cmc_preservation_generation_frame_final_checks();
