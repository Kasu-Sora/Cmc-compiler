#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_examples.h"
#include "cmc_examples_internal.h"
#require "cmc_examples.c"

PROOF static size_t _cmc_examples_calls_axioms_before =
    vector_size(get_all_axioms());

PROOF static term cm_example_call_order_program(void) {
  return
    `CMProgram [] [] []
       [CMFunctionD CMIntTy [] []
         (CMReturnS
           (CMCallE 3i
             [CMCallE 1i [] CMIntTy;
              CMCallE 2i [] CMIntTy]
             CMIntTy));
        CMFunctionD CMIntTy [] []
         (CMSeqS
           (CMExprS (CMPutcE (CMConstE 49i CMIntTy) CMIntTy))
           (CMReturnS (CMConstE 1i CMIntTy)));
        CMFunctionD CMIntTy [] []
         (CMSeqS
           (CMExprS (CMPutcE (CMConstE 50i CMIntTy) CMIntTy))
           (CMReturnS (CMConstE 2i CMIntTy)));
        CMFunctionD CMIntTy
         [CMSlotD CMIntTy 0i; CMSlotD CMIntTy 0i] []
         (CMSeqS
           (CMExprS (CMPutcE (CMConstE 51i CMIntTy) CMIntTy))
           (CMReturnS
             (CMBinaryE 8i
               (CMVarE 2i 0i CMIntTy)
               (CMBinaryE 8i
                 (CMVarE 2i 1i CMIntTy)
                 (CMConstE 3i CMIntTy) CMIntTy)
               CMIntTy)))]
       0i`;
}

PROOF static conv cm_example_call_order_wf_conv(void) {
  thm_list rules = get_cm_runtime_defs();
  vector_add(&rules, get_theorem_by_name("HD"));
  vector_add(&rules, get_theorem_by_name("TL"));
  vector_add(&rules, get_theorem_by_name("NOT_CONS_NIL"));
  conv pass = reduce_rewrite_conv(rules);
  conv result = cm_closed_wf_conv();
  for (size_t i = 0; i < 16; ++i) {
    result = then_conv(result, pass);
  }
  return result;
}

PROOF thm cm_example_call_order_wf = eqt_elim_rule(apply_conversion(
    cm_example_call_order_wf_conv(),
    mk_comb(`cm_wf_program`, cm_example_call_order_program())));

PROOF thm cm_example_call_order_source_iter = apply_conversion(
    cm_source_closed_eval_conv_count(120),
    mk_comb(mk_comb(`cm_iter`, `120`),
      mk_comb(mk_comb(`CMStartTask`, cm_example_call_order_program()),
        `[]:(int)list`)));

PROOF thm cm_example_call_order_target_iter = apply_conversion(
    cm_target_closed_eval_conv_count(500),
    mk_comb(mk_comb(`tvm_iter`, `500`),
      mk_comb(mk_comb(`TVMRunTask`,
        mk_comb(`cm_compile_model`, cm_example_call_order_program())),
        mk_comb(mk_comb(`tvm_initial_state`,
          mk_comb(`cm_compile_model`, cm_example_call_order_program())),
          `[]:(int)list`))));


PROOF thm cm_example_call_order_source = cm_prove_closed_example_source(
    cm_example_call_order_program(), `[]:(int)list`, `[49i; 50i; 51i]`,
    `6i`, `120`, 120, cm_example_call_order_source_iter);

PROOF thm cm_example_call_order_target = cm_prove_closed_example_target(
    cm_example_call_order_program(), `[]:(int)list`, `[49i; 50i; 51i]`,
    `6i`, `500`, cm_example_call_order_wf,
    cm_example_call_order_target_iter);

PROOF thm cmc_example_call_order = conj_rule(cm_example_call_order_wf,
    conj_rule(cm_example_call_order_source,
    conj_rule(cm_example_call_order_target,
      spec_rule(cm_example_call_order_program(),
        get_cm_codegen_two_pass_layout()))));

PROOF thm get_cmc_example_call_order(void) {
  return cmc_example_call_order;
}

PROOF static int cmc_examples_calls_final_checks(void) {
  term program = cm_example_call_order_program();
  term source = `cm_source_terminates (${program:cm_program})
      ([]:(int)list) [49i; 50i; 51i] 6i`;
  term target = `tvm_terminates
      (cm_compile_model (${program:cm_program}))
      ([]:(int)list) [49i; 50i; 51i] 6i`;
  term expected = mk_conj(mk_comb(`cm_wf_program`, program),
      mk_conj(source, mk_conj(target,
        concl(spec_rule(program, get_cm_codegen_two_pass_layout())))));
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_examples_calls_axioms_before,
      "cmc_examples_calls introduced an axiom");
  ENSURE_COND(!IS_NULL(get_cmc_example_call_order()) &&
      vector_size(hyp(get_cmc_example_call_order())) == 0 &&
      vector_size(free_vars(concl(get_cmc_example_call_order()))) == 0 &&
      alpha_compare(concl(get_cmc_example_call_order()), expected) == 0,
      "call-order example has the wrong contract");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_examples_calls_checks =
    cmc_examples_calls_final_checks();
