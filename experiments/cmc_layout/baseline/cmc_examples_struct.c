#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_examples.h"
#include "cmc_examples_internal.h"
#require "cmc_examples.c"

PROOF static size_t _cmc_examples_struct_axioms_before =
    vector_size(get_all_axioms());

PROOF static term cm_example_struct_layout_program(void) {
  return
    `CMProgram
       [CMStructD [CMSlotD CMCharTy 0i; CMSlotD CMIntTy 0i]]
       [CMGlobalD CMCharTy 9i F 0i] []
       [CMFunctionD CMIntTy []
         [CMSlotD (CMPtrTy (CMStructTy 0i)) 0i]
         (CMSeqS
           (CMInitS 0i
             (CMVarE 0i 0i (CMPtrTy CMCharTy)))
           (CMSeqS
             (CMExprS
               (CMAssignE
                 (CMMemberE
                   (CMVarE 1i 0i
                     (CMPtrTy (CMStructTy 0i)))
                   0i CMCharTy)
                 (CMConstE 1i CMIntTy) CMCharTy))
             (CMSeqS
               (CMExprS
                 (CMAssignE
                   (CMMemberE
                     (CMVarE 1i 0i
                       (CMPtrTy (CMStructTy 0i)))
                     1i CMIntTy)
                   (CMConstE 7i CMIntTy) CMIntTy))
               (CMSeqS
                 (CMExprS
                   (CMPutiE
                     (CMMemberE
                       (CMVarE 1i 0i
                         (CMPtrTy (CMStructTy 0i)))
                       0i CMCharTy)
                     CMIntTy))
                 (CMSeqS
                   (CMExprS
                     (CMPutiE
                       (CMMemberE
                         (CMVarE 1i 0i
                           (CMPtrTy (CMStructTy 0i)))
                         1i CMIntTy)
                       CMIntTy))
                   (CMReturnS
                     (CMSizeofE (CMStructTy 0i)
                       CMIntTy)))))))]
       0i`;
}

PROOF static conv cm_example_struct_layout_wf_conv(void) {
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

PROOF thm cm_example_struct_layout_wf =
    eqt_elim_rule(apply_conversion(
      cm_example_struct_layout_wf_conv(),
      mk_comb(`cm_wf_program`, cm_example_struct_layout_program())));

PROOF thm cm_example_struct_layout_source_iter = apply_conversion(
    cm_source_closed_eval_conv_count(200),
    mk_comb(mk_comb(`cm_iter`, `200`),
      mk_comb(mk_comb(`CMStartTask`, cm_example_struct_layout_program()),
        `[]:(int)list`)));

PROOF thm cm_example_struct_layout_target_iter = apply_conversion(
    cm_target_closed_eval_conv_count(700),
    mk_comb(mk_comb(`tvm_iter`, `700`),
      mk_comb(mk_comb(`TVMRunTask`,
        mk_comb(`cm_compile_model`, cm_example_struct_layout_program())),
        mk_comb(mk_comb(`tvm_initial_state`,
          mk_comb(`cm_compile_model`, cm_example_struct_layout_program())),
          `[]:(int)list`))));


PROOF thm cm_example_struct_layout_source =
    cm_prove_closed_example_source(
      cm_example_struct_layout_program(), `[]:(int)list`, `[49i; 55i]`,
      `9i`, `200`, 200, cm_example_struct_layout_source_iter);

PROOF thm cm_example_struct_layout_target =
    cm_prove_closed_example_target(
      cm_example_struct_layout_program(), `[]:(int)list`, `[49i; 55i]`,
      `9i`, `700`, cm_example_struct_layout_wf,
      cm_example_struct_layout_target_iter);

PROOF thm cm_example_struct_packed_layout =
    eqt_elim_rule(apply_conversion(
      cm_source_closed_eval_conv_count(0),
      `cm_member_offset
         [CMStructD [CMSlotD CMCharTy 0i; CMSlotD CMIntTy 0i]]
         0i 0i == 0i &&
       cm_member_offset
         [CMStructD [CMSlotD CMCharTy 0i; CMSlotD CMIntTy 0i]]
         0i 1i == 1i &&
       cm_type_size
         [CMStructD [CMSlotD CMCharTy 0i; CMSlotD CMIntTy 0i]]
         (CMStructTy 0i) == 9i`));

PROOF thm cm_example_struct_byte_pointer =
    eqt_elim_rule(apply_conversion(
      cm_source_closed_eval_conv_count(0),
      `cm_global_address
         (CMProgram
           [CMStructD [CMSlotD CMCharTy 0i; CMSlotD CMIntTy 0i]]
           [CMGlobalD CMCharTy 9i F 0i] [] [] 0i) 0i == 16i &&
       (!(st:cm_src_state) gen lo hi off.
          cm_convertible (CMPtrTy (CMStructTy 0i))
            (CMPtrTy CMCharTy) &&
          cm_value_number st
            (cm_convert_value st (CMPtrTy (CMStructTy 0i))
              (CMPtrV gen lo hi off CMCharTy)) ==
          cm_value_number st
            (CMPtrV gen lo hi off CMCharTy))`));

PROOF thm cmc_example_struct_layout =
    conj_rule(cm_example_struct_layout_wf,
    conj_rule(cm_example_struct_layout_source,
    conj_rule(cm_example_struct_layout_target,
    conj_rule(cm_example_struct_packed_layout,
      cm_example_struct_byte_pointer))));

PROOF thm get_cmc_example_struct_layout(void) {
  return cmc_example_struct_layout;
}

PROOF static int cmc_examples_struct_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_examples_struct_axioms_before,
      "cmc_examples_struct introduced an axiom");
  term program = cm_example_struct_layout_program();
  term source = `cm_source_terminates (${program:cm_program})
      ([]:(int)list) [49i; 55i] 9i`;
  term target = `tvm_terminates
      (cm_compile_model (${program:cm_program}))
      ([]:(int)list) [49i; 55i] 9i`;
  term layout =
      `cm_member_offset
         [CMStructD [CMSlotD CMCharTy 0i; CMSlotD CMIntTy 0i]]
         0i 0i == 0i &&
       cm_member_offset
         [CMStructD [CMSlotD CMCharTy 0i; CMSlotD CMIntTy 0i]]
         0i 1i == 1i &&
       cm_type_size
         [CMStructD [CMSlotD CMCharTy 0i; CMSlotD CMIntTy 0i]]
         (CMStructTy 0i) == 9i`;
  term bridge =
      `cm_global_address
         (CMProgram
           [CMStructD [CMSlotD CMCharTy 0i; CMSlotD CMIntTy 0i]]
           [CMGlobalD CMCharTy 9i F 0i] [] [] 0i) 0i == 16i &&
       (!(st:cm_src_state) gen lo hi off.
          cm_convertible (CMPtrTy (CMStructTy 0i))
            (CMPtrTy CMCharTy) &&
          cm_value_number st
            (cm_convert_value st (CMPtrTy (CMStructTy 0i))
              (CMPtrV gen lo hi off CMCharTy)) ==
          cm_value_number st
            (CMPtrV gen lo hi off CMCharTy))`;
  term expected = mk_conj(mk_comb(`cm_wf_program`, program),
      mk_conj(source, mk_conj(target, mk_conj(layout, bridge))));
  ENSURE_COND(!IS_NULL(get_cmc_example_struct_layout()) &&
      vector_size(hyp(get_cmc_example_struct_layout())) == 0 &&
      vector_size(free_vars(concl(get_cmc_example_struct_layout()))) == 0 &&
      alpha_compare(concl(get_cmc_example_struct_layout()),
        expected) == 0,
      "struct-layout example has the wrong contract");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_examples_struct_checks =
    cmc_examples_struct_final_checks();
