#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_examples.h"
#include "cmc_examples_internal.h"
#require "cmc_examples.c"

PROOF static size_t _cmc_examples_conversion_axioms_before =
    vector_size(get_all_axioms());

PROOF static term cm_example_char_conversion_program(void) {
  return
    `CMProgram [] [] []
       [CMFunctionD CMIntTy [] [CMSlotD CMCharTy 0i]
         (CMSeqS (CMDeclS 0i)
           (CMSeqS
             (CMExprS
               (CMPutiE
                 (CMAssignE
                   (CMVarE 1i 0i CMCharTy)
                   (CMConstE (--1i) CMIntTy) CMCharTy)
                 CMIntTy))
             (CMSeqS
               (CMExprS
                 (CMPutiE (CMVarE 1i 0i CMCharTy) CMIntTy))
               (CMReturnS
                 (CMCallE 1i [CMConstE (--1i) CMIntTy]
                   CMCharTy)))));
        CMFunctionD CMCharTy [CMSlotD CMCharTy 0i] []
          (CMReturnS (CMVarE 2i 0i CMCharTy))]
       0i`;
}

PROOF static conv cm_example_char_conversion_wf_conv(void) {
  thm_list rules = get_cm_runtime_defs();
  vector_add(&rules, get_theorem_by_name("HD"));
  vector_add(&rules, get_theorem_by_name("TL"));
  vector_add(&rules, get_theorem_by_name("NOT_CONS_NIL"));
  conv pass = reduce_rewrite_conv(rules);
  conv result = cm_closed_wf_conv();
  for (size_t i = 0; i < 8; ++i) {
    result = then_conv(result, pass);
  }
  return result;
}

PROOF thm cm_example_char_conversion_wf =
    eqt_elim_rule(apply_conversion(
      cm_example_char_conversion_wf_conv(),
      mk_comb(`cm_wf_program`, cm_example_char_conversion_program())));

PROOF thm cm_example_char_conversion_source_iter = apply_conversion(
    cm_source_closed_eval_conv_count(100),
    mk_comb(mk_comb(`cm_iter`, `100`),
      mk_comb(mk_comb(`CMStartTask`, cm_example_char_conversion_program()),
        `[]:(int)list`)));

PROOF thm cm_example_char_conversion_target_iter = apply_conversion(
    cm_target_closed_eval_conv_count(400),
    mk_comb(mk_comb(`tvm_iter`, `400`),
      mk_comb(mk_comb(`TVMRunTask`,
        mk_comb(`cm_compile_model`, cm_example_char_conversion_program())),
        mk_comb(mk_comb(`tvm_initial_state`,
          mk_comb(`cm_compile_model`, cm_example_char_conversion_program())),
          `[]:(int)list`))));

PROOF thm cm_example_char_conversion_source =
    cm_prove_closed_example_source(
      cm_example_char_conversion_program(), `[]:(int)list`,
      `[50i; 53i; 53i; 50i; 53i; 53i]`, `255i`, `100`, 100,
      cm_example_char_conversion_source_iter);

PROOF thm cm_example_char_conversion_target =
    cm_prove_closed_example_target(
      cm_example_char_conversion_program(), `[]:(int)list`,
      `[50i; 53i; 53i; 50i; 53i; 53i]`, `255i`, `400`,
      cm_example_char_conversion_wf,
      cm_example_char_conversion_target_iter);

PROOF thm cm_example_char_conversion_fact =
    eqt_elim_rule(apply_conversion(
      cm_source_closed_eval_conv_count(0),
      `(!(st:cm_src_state).
          cm_value_number st
            (cm_convert_value st CMCharTy (CMIntV (--1i))) == 255i) &&
       cm_convertible CMCharTy CMIntTy`));

PROOF thm cmc_example_char_conversion =
    conj_rule(cm_example_char_conversion_wf,
    conj_rule(cm_example_char_conversion_source,
    conj_rule(cm_example_char_conversion_target,
      cm_example_char_conversion_fact)));

PROOF thm get_cmc_example_char_conversion(void) {
  return cmc_example_char_conversion;
}

PROOF static int cmc_examples_conversion_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_examples_conversion_axioms_before,
      "cmc_examples_conversion introduced an axiom");
  term program = cm_example_char_conversion_program();
  term source = `cm_source_terminates (${program:cm_program})
      ([]:(int)list) [50i; 53i; 53i; 50i; 53i; 53i] 255i`;
  term target = `tvm_terminates
      (cm_compile_model (${program:cm_program}))
      ([]:(int)list) [50i; 53i; 53i; 50i; 53i; 53i] 255i`;
  term conversion =
      `(!(st:cm_src_state).
          cm_value_number st
            (cm_convert_value st CMCharTy (CMIntV (--1i))) == 255i) &&
       cm_convertible CMCharTy CMIntTy`;
  term expected = mk_conj(mk_comb(`cm_wf_program`, program),
      mk_conj(source, mk_conj(target, conversion)));
  ENSURE_COND(!IS_NULL(get_cmc_example_char_conversion()) &&
      vector_size(hyp(get_cmc_example_char_conversion())) == 0 &&
      vector_size(free_vars(concl(get_cmc_example_char_conversion()))) == 0 &&
      alpha_compare(concl(get_cmc_example_char_conversion()),
        expected) == 0,
      "character-conversion example has the wrong contract");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_examples_conversion_checks =
    cmc_examples_conversion_final_checks();
