#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_total.h"
#include "cmc_annotate_preservation.h"
#include "tvm_model.h"

#require "cmc_preservation_total_step.c"
#require "cmc_annotate_preservation.c"

PROOF static size_t _cmc_preservation_total_iter_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_preservation_iter(void) {
  gnode root = gnode_new_with_ccl(
      `!(n:num) (p:cm_program) (ast:cm_astate).
         cm_wf_program p ==>
         cm_preservation_invariant p ast ==>
         cm_preservation_invariant p (cm_annotated_iter n ast)`);
  gnode_list cases = INDUCT_TAC(root, `n:num`);
  {
    gnode base = AUTO_INTROS_TAC(cases[0]);
    CONV_WITH_ASMP_TAC(base, reduce_rewrite_conv,
        THM_LIST(cm_annotated_iter_def));
  }
  {
    gnode step = AUTO_INTROS_TAC(cases[1]);
    thm wf = assume_rule(`cm_wf_program (p:cm_program)`);
    thm invariant = assume_rule(
        `cm_preservation_invariant (p:cm_program) (ast:cm_astate)`);
    thm next = match_mp_rule(match_mp_rule(
        get_cm_preservation_step(), wf), invariant);
    thm ih = assume_rule(
        `!(p:cm_program) (ast:cm_astate).
           cm_wf_program p ==>
           cm_preservation_invariant p ast ==>
           cm_preservation_invariant p (cm_annotated_iter (n:num) ast)`);
    thm iterated = mp_rule(mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `cm_annotated_step (ast:cm_astate)`), ih), wf), next);
    gnode normalized = CONV_TAC(step,
        reduce_rewrite_conv(THM_LIST(cm_annotated_iter_def)));
    ACCEPT_TAC(normalized, iterated);
  }
  return gnode_prove(root);
}
PROOF thm cm_preservation_iter = cm_prove_preservation_iter();

PROOF static thm cm_prove_annotated_step_exec_prefix(void) {
  gnode root = gnode_new_with_ccl(
      `!(ast:cm_astate) (out:tvm_outcome).
         tvm_exec (cm_astate_target (cm_annotated_step ast)) out ==>
         tvm_exec (cm_astate_target ast) out`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm run = assume_rule(
      `tvm_exec (cm_astate_target (cm_annotated_step (ast:cm_astate)))
        (out:tvm_outcome)`);
  thm iterated = conv_rule(rewrite_conv(THM_LIST(
      cm_annotated_step_target)), run);
  thm result = match_mp_rule(get_tvm_exec_prefix(), iterated);
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF static thm cm_annotated_step_exec_prefix =
    cm_prove_annotated_step_exec_prefix();

PROOF static thm cm_prove_annotated_iter_exec_prefix(void) {
  gnode root = gnode_new_with_ccl(
      `!(n:num) (ast:cm_astate) (out:tvm_outcome).
         tvm_exec (cm_astate_target (cm_annotated_iter n ast)) out ==>
         tvm_exec (cm_astate_target ast) out`);
  gnode_list cases = INDUCT_TAC(root, `n:num`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm run = assume_rule(
        `tvm_exec (cm_astate_target
          (cm_annotated_iter 0 (ast:cm_astate))) (out:tvm_outcome)`);
    thm normalized = conv_rule(reduce_rewrite_conv(
        THM_LIST(cm_annotated_iter_def)), run);
    ACCEPT_TAC(leaf, normalized);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm final_run = assume_rule(
        `tvm_exec
          (cm_astate_target (cm_annotated_iter (SUC (n:num))
            (ast:cm_astate))) (out:tvm_outcome)`);
    thm run_tail = conv_rule(reduce_rewrite_conv(THM_LIST(
        cm_annotated_iter_def)), final_run);
    thm ih = assume_rule(
        `!(ast:cm_astate) (out:tvm_outcome).
           tvm_exec (cm_astate_target (cm_annotated_iter (n:num) ast)) out
           ==> tvm_exec (cm_astate_target ast) out`);
    thm after_step = mp_rule(specl_rule(TERM_LIST(
        `cm_annotated_step (ast:cm_astate)`, `out:tvm_outcome`), ih),
        run_tail);
    thm result = mp_rule(specl_rule(TERM_LIST(
        `ast:cm_astate`, `out:tvm_outcome`),
        cm_annotated_step_exec_prefix), after_step);
    ACCEPT_TAC(leaf, result);
  }
  return gnode_prove(root);
}
PROOF thm cm_annotated_iter_exec_prefix =
    cm_prove_annotated_iter_exec_prefix();

PROOF thm get_cm_preservation_iter(void) {
  return cm_preservation_iter;
}
PROOF thm get_cm_annotated_iter_exec_prefix(void) {
  return cm_annotated_iter_exec_prefix;
}

PROOF static int cmc_preservation_total_iter_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_total_iter_axioms_before,
      "preservation iteration introduced an axiom");
  ENSURE_COND(!IS_NULL(get_cm_preservation_iter()) &&
      vector_size(hyp(get_cm_preservation_iter())) == 0 &&
      vector_size(free_vars(concl(get_cm_preservation_iter()))) == 0 &&
      alpha_compare(concl(get_cm_preservation_iter()),
        `!(n:num) (p:cm_program) (ast:cm_astate).
           cm_wf_program p ==>
           cm_preservation_invariant p ast ==>
           cm_preservation_invariant p (cm_annotated_iter n ast)`) == 0,
      "preservation iteration theorem has the wrong contract");
  ENSURE_COND(!IS_NULL(get_cm_annotated_iter_exec_prefix()) &&
      vector_size(hyp(get_cm_annotated_iter_exec_prefix())) == 0 &&
      vector_size(free_vars(
        concl(get_cm_annotated_iter_exec_prefix()))) == 0 &&
      alpha_compare(concl(get_cm_annotated_iter_exec_prefix()),
        `!(n:num) (ast:cm_astate) (out:tvm_outcome).
           tvm_exec (cm_astate_target (cm_annotated_iter n ast)) out ==>
           tvm_exec (cm_astate_target ast) out`) == 0,
      "annotated execution prefix theorem has the wrong contract");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_total_iter_checks =
    cmc_preservation_total_iter_final_checks();
