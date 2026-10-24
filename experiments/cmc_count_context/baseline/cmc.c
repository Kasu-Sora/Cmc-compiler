#define CSTAR_VERIFY 1

#include "cmc.h"
#include "cmc_concrete_compile_ready.h"
#include "cmc_concrete_emit_code.h"
#include "cmc_concrete_patch_calls.h"
#include "cmc_concrete_emit_data.h"
#include "cmc_correct.h"

#require "cmc_concrete_compile_ready.c"
#require "cmc_concrete_emit_code.c"
#require "cmc_concrete_patch_calls.c"
#require "cmc_concrete_emit_data.c"
#require "cmc_correct.c"

PROOF static size_t _cmc_axioms_before =
    vector_size(get_all_axioms());


PROOF static thm cmc_prove_program_valid_wf(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program).
         cm_rep_program_valid p == 1i ==> cm_wf_program p`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      leaf, `cm_wf_program (p:cm_program)`, "Hwf");
  ACCEPT_TAC(cases[0],
      assume_rule(`cm_wf_program (p:cm_program)`));
  thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_rep_program_valid_def(),
      assume_rule(`~cm_wf_program (p:cm_program)`))),
      assume_rule(`cm_rep_program_valid (p:cm_program) == 1i`));
  CONTR_TAC(cases[1], impossible);
  return gnode_prove(root);
}

PROOF static thm cmc_program_valid_wf =
    cmc_prove_program_valid_wf();

PROOF static thm cmc_fold_output_view(
    const thm view, const term ops, const term imms, const term data) {
  term existential = dest_eq(concl(view)).tm2;
  dest_binder_results outer = dest_sl_exists(existential);
  dest_binder_results middle = dest_sl_exists(outer.tm);
  dest_binder_results inner = dest_sl_exists(middle.tm);
  term body = subst(TERM_PAIR_LIST(
      (term_pair){ops, outer.v},
      (term_pair){imms, middle.v},
      (term_pair){data, inner.v}), inner.tm);
  term data_existential = subst(TERM_PAIR_LIST(
      (term_pair){ops, outer.v},
      (term_pair){imms, middle.v}), middle.tm);
  term imms_existential = subst(TERM_PAIR_LIST(
      (term_pair){ops, outer.v}), outer.tm);
  thm introduced = refl_slrule(body);
  introduced = exists_slrule(data_existential, data, introduced);
  introduced = exists_slrule(imms_existential, imms, introduced);
  introduced = exists_slrule(existential, ops, introduced);
  return trans_slrule(introduced, eq2ent(sym_rule(view)));
}

PROOF static thm cmc_fold_two_exists_view(
    const thm view, const term first, const term second) {
  term existential = dest_eq(concl(view)).tm2;
  dest_binder_results outer = dest_sl_exists(existential);
  dest_binder_results inner = dest_sl_exists(outer.tm);
  term body = subst(TERM_PAIR_LIST(
      (term_pair){first, outer.v},
      (term_pair){second, inner.v}), inner.tm);
  term inner_existential = subst(TERM_PAIR_LIST(
      (term_pair){first, outer.v}), outer.tm);
  thm introduced = refl_slrule(body);
  introduced = exists_slrule(inner_existential, second, introduced);
  introduced = exists_slrule(existential, first, introduced);
  return trans_slrule(introduced, eq2ent(sym_rule(view)));
}

PROOF static thm cmc_fold_one_exists_view(
    const thm view, const term witness) {
  term existential = dest_eq(concl(view)).tm2;
  dest_binder_results outer = dest_sl_exists(existential);
  term body = subst(TERM_PAIR_LIST(
      (term_pair){witness, outer.v}), outer.tm);
  thm introduced = exists_slrule(
      existential, witness, refl_slrule(body));
  return trans_slrule(introduced, eq2ent(sym_rule(view)));
}

PROOF static size_t _cmc_bridge_axioms_before =
    vector_size(get_all_axioms());



PROOF static thm cmc_prove_compile_success_bridge(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (obj:tvm_object) (input:(int)list)
         (output:(int)list) (status:int).
         cm_wf_program p &&
         cm_source_terminates p input output status &&
         cm_output_decodes 0i
           (cm_rep_ops (cm_model_code p))
           (cm_rep_imms (cm_model_code p))
           (cm_model_data_bytes p) obj ==>
         tvm_terminates obj input output status`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm premises = assume_rule(
      `cm_wf_program (p:cm_program) &&
       cm_source_terminates p (input:(int)list)
         (output:(int)list) (status:int) &&
       cm_output_decodes 0i
         (cm_rep_ops (cm_model_code p))
         (cm_rep_imms (cm_model_code p))
         (cm_model_data_bytes p) (obj:tvm_object)`);
  thm wf = conjunct1_rule(premises);
  thm source = conjunct1_rule(conjunct2_rule(premises));
  thm decoded = conjunct2_rule(conjunct2_rule(premises));
  thm modeled = match_mp_rule(get_cm_model_output_decodes(), wf);
  thm same_object = match_mp_rule(specl_rule(TERM_LIST(
      `0i:int`, `cm_rep_ops (cm_model_code (p:cm_program))`,
      `cm_rep_imms (cm_model_code (p:cm_program))`,
      `cm_model_data_bytes (p:cm_program)`, `obj:tvm_object`,
      `cm_compile_model (p:cm_program)`),
      get_cm_output_decode_unique()), conj_rule(decoded, modeled));
  thm preserved = match_mp_rule(
      get_cmc_preservation(), conj_rule(wf, source));
  thm lifted = beta_norm(ap_term_rule(
      `\candidate:tvm_object.
         tvm_terminates candidate (input:(int)list)
           (output:(int)list) (status:int)`,
      same_object));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(lifted), preserved));
  return gnode_prove(root);
}
PROOF static thm cmc_compile_success_bridge =
    cmc_prove_compile_success_bridge();
PROOF thm get_cmc_compile_success_bridge(void) {
  return cmc_compile_success_bridge;
}

PROOF static int _cmc_pre_body_no_axioms =
    vector_size(get_all_axioms()) == _cmc_axioms_before
        ? 1 : (abort(), 0);

int cmc_compile(struct cm_program *program, struct cm_output *output)
    [[cst::param(`p:cm_program`, `code_capacity:int`,
                 `data_capacity:int`)]]
    [[cst::require(
      `cm_program_rep program p **
       cm_output_pre output code_capacity data_capacity`)]]
    [[cst::ensure(
      `(fact((__return:int) == 0i) **
        cm_program_rep program p **
        cm_output_ok output code_capacity data_capacity p) ||
       (fact((__return:int) == 1i) **
        cm_program_rep program p **
        cm_output_capacity output code_capacity data_capacity p)`)]]
{
  [[cst::proof]] {
    thm program_open = specl_rule(
        TERM_LIST(`program__pre:int`, `p:cm_program`),
        get_cm_program_open());
    cst_set_symbolic_state(local_apply(
        cst_get_symbolic_state(), program_open));
    rename_exists_st(TERM_LIST(
        `functions_ptr:int`, `strings_ptr_:int`,
        `globals_ptr_:int`, `structs_ptr_:int`));

    thm output_view = apply_conversion(
        pure_rewrite_conv(THM_LIST(get_cm_output_pre_def())),
        `cm_output_pre (output__pre:int) (code_capacity:int)
          (data_capacity:int)`);
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        rename_exists_hconv(eq2ent(output_view), TERM_LIST(
          `ops_:int`, `imms_:int`, `data_:int`,
          `old_code_:int`, `old_data_:int`, `old_entry_:int`))));

    thm wf = mp_rule(spec_rule(`p:cm_program`, cmc_program_valid_wf),
        assume_rule(`cm_rep_program_valid (p:cm_program) == 1i`));
    add_fact_st(eqt_intro_rule(wf));
    thm wf_parts = conv_rule(rewrite_conv(THM_LIST(
        get_cm_wf_program_def(), get_cm_codegen_admissible_def())), wf);
    thm typed = cm_pick_conjunct(wf_parts,
        `cm_typed_program (p:cm_program)`);
    add_fact_st(eqt_intro_rule(typed));

    thm code_ready = mp_rule(spec_rule(`p:cm_program`,
        cm_concrete_code_ready_from_wf), wf);
    add_fact_st(eqt_intro_rule(code_ready));
    thm code_parts = conv_rule(rewrite_conv(THM_LIST(
        get_cm_concrete_code_ready_def())), code_ready);
    thm structs_ready = cm_pick_conjunct(code_parts,
        `cm_concrete_structs_ready (p:cm_program)`);
    thm functions_ready = cm_pick_conjunct(code_parts,
        `cm_concrete_functions_ready p 0i (cm_program_functions p)`);
    thm structs_safe = conv_rule(rewrite_conv(THM_LIST(
        get_cm_concrete_structs_ready_def())), structs_ready);
    add_fact_st(eqt_intro_rule(structs_safe));
    add_fact_st(eqt_intro_rule(functions_ready));

    thm data_ready = mp_rule(spec_rule(`p:cm_program`,
        get_cmc_data_ready_from_typed()), typed);
    thm data_parts = conv_rule(rewrite_conv(THM_LIST(
        get_cm_concrete_data_ready_def())), data_ready);
    add_fact_st(eqt_intro_rule(cm_pick_conjunct(data_parts,
        `cm_rep_globals_safe (cm_program_globals (p:cm_program))`)));
    add_fact_st(eqt_intro_rule(cm_pick_conjunct(data_parts,
        `cm_data_globals_wf (cm_program_structs (p:cm_program))
          (cm_program_globals p)`)));
    add_fact_st(eqt_intro_rule(cm_pick_conjunct(data_parts,
        `cm_rep_strings_safe (cm_program_strings (p:cm_program))`)));
    add_fact_st(cm_pick_conjunct(data_parts,
        `0i <= cm_rep_globals_size (cm_program_globals (p:cm_program))`));
    add_fact_st(cm_pick_conjunct(data_parts,
        `0i <= cm_rep_strings_size (cm_program_strings (p:cm_program))`));
    add_fact_st(cm_pick_conjunct(data_parts,
        `cm_rep_globals_size (cm_program_globals (p:cm_program)) +
           cm_rep_strings_size (cm_program_strings p) <= 1048560i`));
    add_fact_st(cm_pick_conjunct(data_parts,
        `cm_model_data_length (p:cm_program) ==
          (8i + cm_rep_globals_size (cm_program_globals p)) +
            cm_rep_strings_size (cm_program_strings p)`));

    cm_close_program_context_st();
  }

  int code_length = cmc_model_code_length(program);
  int data_length = cmc_model_data_length(program);

  output->code_length = code_length;
  output->data_length = data_length;
  output->entry = -1;

  if (code_length > output->code_capacity) {
    [[cst::proof]] {
      substitute_st(assume_rule(
          `retval == cm_model_code_length (p:cm_program)`));
      substitute_st(assume_rule(
          `retval_1 == cm_model_data_length (p:cm_program)`));
      thm capacity_case = disj1_rule(assume_rule(
          `cm_model_code_length (p:cm_program) > (code_capacity:int)`),
          `cm_model_data_length (p:cm_program) > (data_capacity:int)`);
      thm output_view = apply_conversion(
          reduce_rewrite_conv(THM_LIST(get_cm_output_capacity_def(),
            eqt_intro_rule(capacity_case), sl_fact_true_emp(),
            sl_sep_emp_left(), sl_sep_emp_right())),
          `cm_output_capacity (output__pre:int) (code_capacity:int)
            (data_capacity:int) (p:cm_program)`);
      apply_hconv_st(cmc_fold_output_view(
          output_view, `ops_:int`, `imms_:int`, `data_:int`));
      cm_open_program_context_st();
      apply_hconv_st(specl_rule(TERM_LIST(
          `program__pre:int`, `p:cm_program`,
          `structs_ptr_:int`, `globals_ptr_:int`,
          `strings_ptr_:int`, `functions_ptr:int`),
          get_cm_program_fold()));
    }
    return CMC_CAPACITY;
  }

  if (data_length > output->data_capacity) {
    [[cst::proof]] {
      substitute_st(assume_rule(
          `retval == cm_model_code_length (p:cm_program)`));
      substitute_st(assume_rule(
          `retval_1 == cm_model_data_length (p:cm_program)`));
      thm capacity_case = disj2_rule(
          `cm_model_code_length (p:cm_program) > (code_capacity:int)`,
          assume_rule(
            `cm_model_data_length (p:cm_program) > (data_capacity:int)`));
      thm output_view = apply_conversion(
          reduce_rewrite_conv(THM_LIST(get_cm_output_capacity_def(),
            eqt_intro_rule(capacity_case), sl_fact_true_emp(),
            sl_sep_emp_left(), sl_sep_emp_right())),
          `cm_output_capacity (output__pre:int) (code_capacity:int)
            (data_capacity:int) (p:cm_program)`);
      apply_hconv_st(cmc_fold_output_view(
          output_view, `ops_:int`, `imms_:int`, `data_:int`));
      cm_open_program_context_st();
      apply_hconv_st(specl_rule(TERM_LIST(
          `program__pre:int`, `p:cm_program`,
          `structs_ptr_:int`, `globals_ptr_:int`,
          `strings_ptr_:int`, `functions_ptr:int`),
          get_cm_program_fold()));
    }
    return CMC_CAPACITY;
  }

  struct cm_emitter emitter;
  emitter.output = output;
  emitter.pc = 0;

  [[cst::proof]] {
    substitute_st(assume_rule(
        `retval == cm_model_code_length (p:cm_program)`));
    substitute_st(assume_rule(
        `retval_1 == cm_model_data_length (p:cm_program)`));
    thm code_size_nonnegative = specl_rule(TERM_LIST(
        `cm_program_functions (p:cm_program)`,
        `p:cm_program`, `0i:int`),
        cm_functions_code_size_nonnegative);
    thm code_shape = apply_conversion(
        rewrite_conv(THM_LIST(get_cm_model_code_length_def())),
        `cm_model_code_length (p:cm_program)`);
    thm code_capacity_nonzero = mp_rule(mp_rule(mp_rule(
        int_arith_rule(
          `0i <= cm_functions_code_size (p:cm_program)
                  (cm_program_functions p) 0i ==>
           cm_model_code_length p ==
             11i + cm_functions_code_size p
                     (cm_program_functions p) 0i ==>
           cm_model_code_length p <= (code_capacity:int) ==>
           ~(code_capacity == 0i)`),
        code_size_nonnegative), code_shape),
        assume_rule(
          `cm_model_code_length (p:cm_program) <= (code_capacity:int)`));
    thm ops_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        get_cm_undef_int_buffer_def(),
        eqf_intro_rule(code_capacity_nonzero))),
        `cm_undef_int_buffer (ops_:int) (code_capacity:int)`);
    apply_hconv_st(eq2ent(ops_view));
    thm imms_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        get_cm_undef_int64_buffer_def(),
        eqf_intro_rule(code_capacity_nonzero))),
        `cm_undef_int64_buffer (imms_:int) (code_capacity:int)`);
    apply_hconv_st(eq2ent(imms_view));
    apply_hconv_st(specl_rule(TERM_LIST(`ops_:int`, `code_capacity:int`),
        get_cm_begin_int_fill()));
    apply_hconv_st(specl_rule(TERM_LIST(`imms_:int`, `code_capacity:int`),
        get_cm_begin_int64_fill()));

    term emitter_initial =
        `cm_emitter_rep (emitter__addr:int) (output__pre:int)
          (code_capacity:int)
          (cm_rep_ops ([]:(tvm_inst)list))
          (cm_rep_imms ([]:(tvm_inst)list))`;
    thm emitter_view = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          cm_emitter_rep_def, get_cm_rep_ops_def(),
          get_cm_rep_imms_def(), get_theorem_by_name("ILENGTH_DEF"),
          eqt_intro_rule(assume_rule(`0i <= (code_capacity:int)`)),
          sl_fact_true_emp(), sl_sep_emp_left(), sl_sep_emp_right())),
        emitter_initial);
    apply_hconv_st(cmc_fold_two_exists_view(
        emitter_view, `ops_:int`, `imms_:int`));

    thm patch_nil = by_rewrite(
        `cm_patch_code (p:cm_program) ([]:(tvm_inst)list) ==
           ([]:(tvm_inst)list)`,
        THM_LIST(cm_patch_code_def));
    add_fact_st(patch_nil);
    term resolved_initial =
        `cm_resolved_emitter_rep (p:cm_program)
          (emitter__addr:int) (output__pre:int) (code_capacity:int)
          ([]:(tvm_inst)list)`;
    thm resolved_view = apply_conversion(
        pure_rewrite_conv(THM_LIST(cm_resolved_emitter_rep_def)),
        resolved_initial);
    apply_hconv_st(cmc_fold_one_exists_view(
        resolved_view, `[]:(tvm_inst)list`));

    thm code_length_exact = spec_rule(
        `p:cm_program`, get_cm_model_code_length_exact());
    thm base_capacity = mp_rule(mp_rule(int_arith_rule(
        `ilength (cm_model_code (p:cm_program)) ==
             cm_model_code_length p ==>
         cm_model_code_length p <= (code_capacity:int) ==>
         0i + ilength (cm_model_code p) <= code_capacity`),
        code_length_exact),
        assume_rule(
          `cm_model_code_length (p:cm_program) <= (code_capacity:int)`));
    thm append_nil = ispec_rule(
        `cm_model_code (p:cm_program)`,
        get_theorem_by_name("APPEND_NIL"));
    thm append_length = beta_norm(ap_term_rule(
        `\xs:(tvm_inst)list. ilength xs`, append_nil));
    thm plan_capacity = mp_rule(mp_rule(int_arith_rule(
        `ilength (cm_model_code (p:cm_program) ++ []) ==
             ilength (cm_model_code p) ==>
         0i + ilength (cm_model_code p) <= (code_capacity:int) ==>
         0i + ilength (cm_model_code p ++ []) <= code_capacity`),
        append_length), base_capacity);
    term initial =
        `cm_resolved_emitter_plan_rep (p:cm_program)
          (emitter__addr:int) (output__pre:int) (code_capacity:int)
          ([]:(tvm_inst)list) (cm_model_code p ++ [])`;
    thm initial_view = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          cm_resolved_emitter_plan_rep_def,
          get_theorem_by_name("ILENGTH_DEF"),
          eqt_intro_rule(plan_capacity),
          sl_fact_true_emp(), sl_sep_emp_left(), sl_sep_emp_right())),
        initial);
    apply_hconv_st(eq2ent(sym_rule(initial_view)));
  }

  [[cst::where(`done`, `[]:(tvm_inst)list`)]]
  [[cst::where(`tail`, `[]:(tvm_inst)list`)]]
  cmc_emit_code(program, &emitter);

  [[cst::proof]] {
    rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
    term completed =
        `cm_resolved_emitter_plan_rep (p:cm_program)
          (emitter__addr:int) (output__pre:int) (code_capacity:int)
          (cm_model_code p) ([]:(tvm_inst)list)`;
    thm completed_view = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          cm_resolved_emitter_plan_rep_def,
          get_theorem_by_name("ILENGTH_DEF"))), completed);
    apply_hconv_st(eq2ent(completed_view));
  }

  cmc_patch_resolved_calls(program, &emitter);
  [[cst::proof]] {
    cm_open_program_context_st();
    thm data_capacity_nonzero = mp_rule(mp_rule(mp_rule(mp_rule(
        int_arith_rule(
          `0i <= cm_rep_globals_size
                    (cm_program_globals (p:cm_program)) ==>
           0i <= cm_rep_strings_size (cm_program_strings p) ==>
           cm_model_data_length p ==
             (8i + cm_rep_globals_size (cm_program_globals p)) +
               cm_rep_strings_size (cm_program_strings p) ==>
           cm_model_data_length p <= (data_capacity:int) ==>
           ~(data_capacity == 0i)`),
        assume_rule(
          `0i <= cm_rep_globals_size
                    (cm_program_globals (p:cm_program))`)),
        assume_rule(
          `0i <= cm_rep_strings_size
                    (cm_program_strings (p:cm_program))`)),
        assume_rule(
          `cm_model_data_length (p:cm_program) ==
             (8i + cm_rep_globals_size (cm_program_globals p)) +
               cm_rep_strings_size (cm_program_strings p)`)),
        assume_rule(
          `cm_model_data_length (p:cm_program) <=
             (data_capacity:int)`));
    thm data_view = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_undef_uint8_buffer_def(),
          eqf_intro_rule(data_capacity_nonzero))),
        `cm_undef_uint8_buffer (data_:int) (data_capacity:int)`);
    apply_hconv_st(eq2ent(data_view));
    apply_hconv_st(specl_rule(TERM_LIST(`data_:int`, `data_capacity:int`),
        get_cm_begin_uint8_fill()));
    thm data_fits = mp_rule(mp_rule(int_arith_rule(
        `cm_model_data_length (p:cm_program) ==
             (8i + cm_rep_globals_size (cm_program_globals p)) +
               cm_rep_strings_size (cm_program_strings p) ==>
         cm_model_data_length p <= (data_capacity:int) ==>
         (8i + cm_rep_globals_size (cm_program_globals p)) +
           cm_rep_strings_size (cm_program_strings p) <= data_capacity`),
        assume_rule(
          `cm_model_data_length (p:cm_program) ==
             (8i + cm_rep_globals_size (cm_program_globals p)) +
               cm_rep_strings_size (cm_program_strings p)`)),
        assume_rule(
          `cm_model_data_length (p:cm_program) <=
             (data_capacity:int)`));
    add_fact_st(data_fits);
    rewrite_st(THM_LIST(
        get_theorem_by_name("INT_MUL_LZERO"),
        get_theorem_by_name("INT_ADD_RID"),
        get_theorem_by_name("INT_SUB_RZERO")));
    add_data_at_range_st(
        `field_addr (output__pre:int) Tcm_output Fdata_capacity`,
        `Tint`, `data_capacity:int`);
  }

  struct cm_global *globals = program->globals;
  struct cm_string *strings = program->strings;
  unsigned char *data = output->data;
  int output_data_capacity = output->data_capacity;
  int emitted_data = cmc_emit_data(
      globals, strings, data, output_data_capacity);

  output->entry = 0;

  [[cst::proof]] {
    term emitter_final =
        `cm_emitter_rep (emitter__addr:int) (output__pre:int)
          (code_capacity:int)
          (cm_rep_ops (cm_model_code (p:cm_program)))
          (cm_rep_imms (cm_model_code p))`;
    thm emitter_view = apply_conversion(
        pure_rewrite_conv(THM_LIST(cm_emitter_rep_def)),
        emitter_final);
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        rename_exists_hconv(eq2ent(emitter_view),
          TERM_LIST(`final_ops_:int`, `final_imms_:int`))));

    thm code_size_nonnegative = specl_rule(TERM_LIST(
        `cm_program_functions (p:cm_program)`,
        `p:cm_program`, `0i:int`),
        cm_functions_code_size_nonnegative);
    thm code_shape = apply_conversion(
        rewrite_conv(THM_LIST(get_cm_model_code_length_def())),
        `cm_model_code_length (p:cm_program)`);
    thm code_positive = mp_rule(mp_rule(int_arith_rule(
        `0i <= cm_functions_code_size (p:cm_program)
                (cm_program_functions p) 0i ==>
         cm_model_code_length p ==
           11i + cm_functions_code_size p
                   (cm_program_functions p) 0i ==>
         0i < cm_model_code_length p`),
        code_size_nonnegative), code_shape);
    thm code_nonnegative = mp_rule(int_arith_rule(
        `0i < cm_model_code_length (p:cm_program) ==>
         0i <= cm_model_code_length p`), code_positive);
    thm ops_length = spec_rule(
        `cm_model_code (p:cm_program)`, cm_rep_ops_length);
    thm ops_nonzero = mp_rule(mp_rule(int_arith_rule(
        `ilength (cm_rep_ops (cm_model_code (p:cm_program))) ==
             ilength (cm_model_code p) ==>
         0i < cm_model_code_length p ==>
         ilength (cm_rep_ops (cm_model_code p)) ==
             cm_model_code_length p ==>
         ~(ilength (cm_rep_ops (cm_model_code p)) == 0i)`),
        ops_length), code_positive);
    ops_nonzero = mp_rule(ops_nonzero,
        trans_rule(ops_length, spec_rule(
          `p:cm_program`, get_cm_model_code_length_exact())));
    thm imms_nonzero = mp_rule(mp_rule(int_arith_rule(
        `ilength (cm_rep_ops (cm_model_code (p:cm_program))) ==
             ilength (cm_rep_imms (cm_model_code p)) ==>
         ~(ilength (cm_rep_ops (cm_model_code p)) == 0i) ==>
         ~(ilength (cm_rep_imms (cm_model_code p)) == 0i)`),
        assume_rule(
          `ilength (cm_rep_ops (cm_model_code (p:cm_program))) ==
             ilength (cm_rep_imms (cm_model_code p))`)),
        ops_nonzero);

    term ops_buffer =
        `cm_int_prefix_buffer (final_ops_:int) (code_capacity:int)
          (cm_rep_ops (cm_model_code (p:cm_program)))`;
    thm ops_buffer_view = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_int_prefix_buffer_def(),
          eqf_intro_rule(ops_nonzero))),
        ops_buffer);
    apply_hconv_st(eq2ent(sym_rule(ops_buffer_view)));

    term imms_buffer =
        `cm_int64_prefix_buffer (final_imms_:int) (code_capacity:int)
          (cm_rep_imms (cm_model_code (p:cm_program)))`;
    thm imms_buffer_view = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_int64_prefix_buffer_def(),
          gsym_rule(assume_rule(
            `ilength (cm_rep_ops (cm_model_code (p:cm_program))) ==
               ilength (cm_rep_imms (cm_model_code p))`)),
          eqf_intro_rule(imms_nonzero))),
        imms_buffer);
    apply_hconv_st(eq2ent(sym_rule(imms_buffer_view)));

    thm data_positive = mp_rule(mp_rule(mp_rule(int_arith_rule(
        `0i <= cm_rep_globals_size
                  (cm_program_globals (p:cm_program)) ==>
         0i <= cm_rep_strings_size (cm_program_strings p) ==>
         cm_model_data_length p ==
           (8i + cm_rep_globals_size (cm_program_globals p)) +
             cm_rep_strings_size (cm_program_strings p) ==>
         0i < cm_model_data_length p`),
        assume_rule(
          `0i <= cm_rep_globals_size
                    (cm_program_globals (p:cm_program))`)),
        assume_rule(
          `0i <= cm_rep_strings_size
                    (cm_program_strings (p:cm_program))`)),
        assume_rule(
          `cm_model_data_length (p:cm_program) ==
             (8i + cm_rep_globals_size (cm_program_globals p)) +
               cm_rep_strings_size (cm_program_strings p)`));
    thm data_nonnegative = mp_rule(int_arith_rule(
        `0i < cm_model_data_length (p:cm_program) ==>
         0i <= cm_model_data_length p`), data_positive);
    thm data_nonzero = mp_rule(int_arith_rule(
        `0i < cm_model_data_length (p:cm_program) ==>
         ~(cm_model_data_length p == 0i)`), data_positive);
    thm data_count_nonzero = conv_rule(rewrite_conv(THM_LIST(
        assume_rule(
          `cm_model_data_length (p:cm_program) ==
             (8i + cm_rep_globals_size (cm_program_globals p)) +
               cm_rep_strings_size (cm_program_strings p)`))),
        data_nonzero);
    term data_buffer =
        `cm_uint8_prefix_buffer (data_:int) (data_capacity:int)
          (cm_model_data_bytes (p:cm_program))`;
    thm data_buffer_view = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_uint8_prefix_buffer_def(),
          gsym_rule(get_cm_model_data_length_def()),
          assume_rule(
            `cm_model_data_length (p:cm_program) ==
               (8i + cm_rep_globals_size (cm_program_globals p)) +
                 cm_rep_strings_size (cm_program_strings p)`),
          eqf_intro_rule(data_count_nonzero),
          get_cm_model_data_bytes_def(),
          get_theorem_by_name("APPEND_ASSOC"))),
        data_buffer);
    apply_hconv_st(eq2ent(sym_rule(data_buffer_view)));

    // Bind preservation to the exact contents of the returned buffers.
    term observations =
        `cm_source_terminates (p:cm_program) (input:(int)list)
           (trace:(int)list) (status:int) &&
         cm_output_decodes 0i
           (cm_rep_ops (cm_model_code p))
           (cm_rep_imms (cm_model_code p))
           (cm_model_data_bytes p) (obj:tvm_object)`;
    thm preservation = match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `obj:tvm_object`, `input:(int)list`,
        `trace:(int)list`, `status:int`), cmc_compile_success_bridge),
        conj_rule(from_state_bool(`cm_wf_program (p:cm_program)`),
          assume_rule(observations)));
    preservation = genl_rule(TERM_LIST(
        `obj:tvm_object`, `input:(int)list`, `trace:(int)list`, `status:int`),
        disch_rule(observations, preservation));

    thm output_view = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_output_ok_def(),
          eqt_intro_rule(preservation),
          eqt_intro_rule(assume_rule(`~((output__pre:int) == 0i)`)),
          eqt_intro_rule(code_nonnegative),
          eqt_intro_rule(assume_rule(
            `cm_model_code_length (p:cm_program) <=
               (code_capacity:int)`)),
          eqt_intro_rule(data_nonnegative),
          eqt_intro_rule(assume_rule(
            `cm_model_data_length (p:cm_program) <=
               (data_capacity:int)`)),
          sl_fact_true_emp(), sl_sep_emp_left(), sl_sep_emp_right())),
        `cm_output_ok (output__pre:int) (code_capacity:int)
          (data_capacity:int) (p:cm_program)`);
    apply_hconv_st(cmc_fold_output_view(
        output_view, `final_ops_:int`, `final_imms_:int`, `data_:int`));

    apply_hconv_st(specl_rule(TERM_LIST(
        `program__pre:int`, `p:cm_program`,
        `structs_ptr_:int`, `globals_ptr_:int`,
        `strings_ptr_:int`, `functions_ptr:int`),
        get_cm_program_fold()));
  }

  return CMC_OK;
}

PROOF static int cmc_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) == _cmc_bridge_axioms_before,
      "cmc logical bridge introduced an axiom");
  ENSURE_COND(!IS_NULL(get_cmc_compile_success_bridge()) &&
      vector_size(hyp(get_cmc_compile_success_bridge())) == 0 &&
      vector_size(free_vars(concl(get_cmc_compile_success_bridge()))) == 0 &&
      alpha_compare(concl(get_cmc_compile_success_bridge()),
        `!(p:cm_program) (obj:tvm_object) (input:(int)list)
           (output:(int)list) (status:int).
           cm_wf_program p &&
           cm_source_terminates p input output status &&
           cm_output_decodes 0i
             (cm_rep_ops (cm_model_code p))
             (cm_rep_imms (cm_model_code p))
             (cm_model_data_bytes p) obj ==>
           tvm_terminates obj input output status`) == 0,
      "concrete compiler success bridge has the wrong contract");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_checks = cmc_final_checks();
