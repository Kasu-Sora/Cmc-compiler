#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_type_source_r_total.h"

#require "cmc_preservation_type_source_r_leaf.c"
#require "cmc_preservation_type_source_r_call.c"

PROOF static size_t _cmc_preservation_type_source_r_total_axioms_before =
    vector_size(get_all_axioms());

PROOF static void cm_tsrt_accept(
    const gnode branch, const thm shape, const thm result) {
  thm normalized = conv_rule(rewrite_conv(THM_LIST(shape)), result);
  thm target_view = apply_conversion(
      rewrite_conv(THM_LIST(shape)), goal_ccl(branch->g));
  ACCEPT_TAC(branch, eq_mp_rule(sym_rule(target_view), normalized));
}

PROOF static thm cm_prove_r_type_ready_step(void) {
  term task =
      `CMRTask (q:cm_program) (fid:int) (expr:cm_expr)
        (st:cm_src_state) (ks:(cm_frame)list)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (q:cm_program) (fid:int) (expr:cm_expr)
         (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         cm_typed_program p ==>
         cm_task_succeeds (CMRTask q fid expr st ks) ==>
         cm_annotation_erases (CMRTask q fid expr st ks) ann ==>
         cm_task_type_ready p (CMRTask q fid expr st ks) ann ==>
         cm_task_type_ready p
           (cm_step (CMRTask q fid expr st ks))
           (cm_update_annotation
             (cm_annotation_step (CMRTask q fid expr st ks) ann))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm typed = assume_rule(`cm_typed_program (p:cm_program)`);
  thm succeeds = assume_rule(
      `cm_task_succeeds ${task:cm_task}`);
  thm erases = assume_rule(
      `cm_annotation_erases ${task:cm_task} (ann:cm_annotation)`);
  thm ready = assume_rule(
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        (ann:cm_annotation)`);
  thm case_theorems[] = {
    cm_r_const_type_ready_step,
    cm_r_string_type_ready_step,
    cm_r_var_type_ready_step,
    cm_r_assign_type_ready_step,
    cm_r_binary_type_ready_step,
    cm_r_unary_type_ready_step,
    cm_r_index_type_ready_step,
    cm_r_member_type_ready_step,
    cm_r_call_type_ready_step,
    cm_r_sizeof_type_ready_step,
    cm_r_getc_type_ready_step,
    cm_r_putc_type_ready_step,
    cm_r_puti_type_ready_step,
    cm_r_exit_type_ready_step
  };
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`expr:cm_expr`, get_cm_expr_cases()), "Hex");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (is_exists(goal_lasmps(branch->g)[
        labeled_term_list_index(goal_lasmps(branch->g), "Hex")].tm)) {
      branch = ASMP_EXISTS_TAC(branch, "Hex", NULL);
    }
    thm shape = assume_rule(goal_lasmps(branch->g)[
        labeled_term_list_index(goal_lasmps(branch->g), "Hex")].tm);
    thm shaped_succeeds = conv_rule(
        rewrite_conv(THM_LIST(shape)), succeeds);
    thm shaped_erases = conv_rule(
        rewrite_conv(THM_LIST(shape)), erases);
    thm shaped_ready = conv_rule(
        rewrite_conv(THM_LIST(shape)), ready);
    thm result = case_theorems[i];
    if (i == 0 || i == 1 || i == 9 || i == 10) {
      result = match_mp_rule(result, shaped_succeeds);
    } else {
      result = match_mp_rule(result, typed);
      result = match_mp_rule(result, shaped_succeeds);
    }
    if (i == 8) {
      result = match_mp_rule(result, shaped_erases);
    }
    result = match_mp_rule(result, shaped_ready);
    cm_tsrt_accept(branch, shape, result);
  }
  return gnode_prove(root);
}
PROOF thm cm_r_type_ready_step = cm_prove_r_type_ready_step();

PROOF static int cmc_preservation_type_source_r_total_final_checks(void) {
  ENSURE_COND(vector_size(hyp(cm_r_type_ready_step)) == 0,
      "total rvalue type theorem has assumptions");
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_type_source_r_total_axioms_before,
      "cmc_preservation_type_source_r_total introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_type_source_r_total_checks =
    cmc_preservation_type_source_r_total_final_checks();
