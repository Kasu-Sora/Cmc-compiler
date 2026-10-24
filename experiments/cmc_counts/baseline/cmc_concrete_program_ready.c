#include "cmc_concrete_program_ready.h"
#require "cmc_concrete_data_ready.c"
#require "cmc_concrete_defs.c"
#require "cmc_codegen.c"

PROOF static size_t _cmc_program_ready_axioms_before =
    vector_size(get_all_axioms());

PROOF thm cm_concrete_data_ready_def = new_fun_definition(
    `cm_concrete_data_ready (p:cm_program) : bool =
       (cm_rep_globals_safe (cm_program_globals p) &&
        cm_data_globals_wf (cm_program_structs p)
          (cm_program_globals p) &&
        cm_rep_strings_safe (cm_program_strings p) &&
        0i <= cm_rep_globals_size (cm_program_globals p) &&
        0i <= cm_rep_strings_size (cm_program_strings p) &&
        cm_rep_globals_size (cm_program_globals p) +
          cm_rep_strings_size (cm_program_strings p) <= 1048560i &&
        cm_model_data_length p ==
          (8i + cm_rep_globals_size (cm_program_globals p)) +
            cm_rep_strings_size (cm_program_strings p))`);
PROOF static int _e_cm_concrete_data_ready =
    cst_add_const_to_header(`cm_concrete_data_ready`);

PROOF static thm cm_prove_data_globals_from_indexed(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (globals:(cm_global_d)list).
         (!i. 0i <= i ==> i < ilength globals ==>
              cm_global_wf structs (inth i globals)) ==>
         cm_data_globals_wf structs globals`);
  gnode with_structs = GEN_TAC(root, "structs");
  gnode_list cases = INDUCT_TAC(with_structs,
      `globals:(cm_global_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_data_globals_wf_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm all_wf = assume_rule(
        `!i. 0i <= i ==>
           i < ilength ((a0:cm_global_d) ::
             (a1:(cm_global_d)list)) ==>
           cm_global_wf (structs:(cm_struct_d)list)
             (inth i (a0 :: a1))`);
    thm head_wf = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`, `a0:cm_global_d`,
        `a1:(cm_global_d)list`), cm_globals_wf_head), all_wf);
    thm tail_wf = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`, `a0:cm_global_d`,
        `a1:(cm_global_d)list`), cm_globals_wf_tail), all_wf);
    thm tail_ready = mp_rule(assume_rule(
        `(!i. 0i <= i ==>
             i < ilength (a1:(cm_global_d)list) ==>
             cm_global_wf (structs:(cm_struct_d)list)
               (inth i a1)) ==>
         cm_data_globals_wf structs a1`), tail_wf);
    thm parts = conj_rule(head_wf, tail_ready);
    thm view = apply_conversion(rewrite_conv(THM_LIST(
        get_cm_data_globals_wf_def())),
        `cm_data_globals_wf (structs:(cm_struct_d)list)
          ((a0:cm_global_d) :: (a1:(cm_global_d)list))`);
    ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(view), parts));
  }
  return gnode_prove(root);
}
PROOF static thm cm_data_globals_from_indexed =
    cm_prove_data_globals_from_indexed();

PROOF static thm cm_global_rep_positive(
    const term structs, const term global, const thm global_wf) {
  thm opened = conv_rule(rewrite_conv(THM_LIST(
      get_cm_global_wf_def())), global_wf);
  thm semantic_positive = conjunct1_rule(conjunct2_rule(
      conjunct2_rule(opened)));
  thm bridge = mp_rule(specl_rule(TERM_LIST(structs, global),
      cm_rep_global_size_matches), global_wf);
  return conv_rule(rewrite_conv(THM_LIST(sym_rule(bridge))),
      semantic_positive);
}

PROOF static thm cm_prove_globals_nonnegative(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (globals:(cm_global_d)list).
         (!i. 0i <= i ==> i < ilength globals ==>
              cm_global_wf structs (inth i globals)) ==>
         0i <= cm_rep_globals_size globals`);
  gnode with_structs = GEN_TAC(root, "structs");
  gnode_list cases = INDUCT_TAC(with_structs,
      `globals:(cm_global_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_rep_globals_size_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm all_wf = assume_rule(
        `!i. 0i <= i ==>
           i < ilength ((a0:cm_global_d) ::
             (a1:(cm_global_d)list)) ==>
           cm_global_wf (structs:(cm_struct_d)list)
             (inth i (a0 :: a1))`);
    thm head_wf = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`, `a0:cm_global_d`,
        `a1:(cm_global_d)list`), cm_globals_wf_head), all_wf);
    thm tail_wf = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`, `a0:cm_global_d`,
        `a1:(cm_global_d)list`), cm_globals_wf_tail), all_wf);
    thm head_positive = cm_global_rep_positive(
        `structs:(cm_struct_d)list`, `a0:cm_global_d`, head_wf);
    thm tail_nonnegative = mp_rule(assume_rule(
        `(!i. 0i <= i ==>
             i < ilength (a1:(cm_global_d)list) ==>
             cm_global_wf (structs:(cm_struct_d)list)
               (inth i a1)) ==>
         0i <= cm_rep_globals_size a1`), tail_wf);
    thm sum = mp_rule(mp_rule(int_arith_rule(
        `0i < cm_rep_global_size (a0:cm_global_d) ==>
         0i <= cm_rep_globals_size (a1:(cm_global_d)list) ==>
         0i <= cm_rep_global_size a0 + cm_rep_globals_size a1`),
        head_positive), tail_nonnegative);
    thm view = apply_conversion(rewrite_conv(THM_LIST(
        get_cm_rep_globals_size_def())),
        `0i <= cm_rep_globals_size
          ((a0:cm_global_d) :: (a1:(cm_global_d)list))`);
    ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(view), sum));
  }
  return gnode_prove(root);
}
PROOF static thm cm_globals_nonnegative =
    cm_prove_globals_nonnegative();

PROOF static thm cm_prove_globals_safe(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (globals:(cm_global_d)list).
         (!i. 0i <= i ==> i < ilength globals ==>
              cm_global_wf structs (inth i globals)) ==>
         cm_rep_globals_size globals <= 1048560i ==>
         cm_rep_globals_safe globals`);
  gnode with_structs = GEN_TAC(root, "structs");
  gnode_list cases = INDUCT_TAC(with_structs,
      `globals:(cm_global_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_rep_globals_safe_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm all_wf = assume_rule(
        `!i. 0i <= i ==>
           i < ilength ((a0:cm_global_d) ::
             (a1:(cm_global_d)list)) ==>
           cm_global_wf (structs:(cm_struct_d)list)
             (inth i (a0 :: a1))`);
    thm full_bound = assume_rule(
        `cm_rep_globals_size
           ((a0:cm_global_d) :: (a1:(cm_global_d)list)) <= 1048560i`);
    thm head_wf = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`, `a0:cm_global_d`,
        `a1:(cm_global_d)list`), cm_globals_wf_head), all_wf);
    thm tail_wf = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`, `a0:cm_global_d`,
        `a1:(cm_global_d)list`), cm_globals_wf_tail), all_wf);
    thm head_positive = cm_global_rep_positive(
        `structs:(cm_struct_d)list`, `a0:cm_global_d`, head_wf);
    thm head_nonnegative = mp_rule(int_arith_rule(
        `0i < cm_rep_global_size (a0:cm_global_d) ==>
         0i <= cm_rep_global_size a0`), head_positive);
    thm tail_nonnegative = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`, `a1:(cm_global_d)list`),
        cm_globals_nonnegative), tail_wf);
    thm unfolded_bound = conv_rule(rewrite_conv(THM_LIST(
        get_cm_rep_globals_size_def())), full_bound);
    thm tail_bound = mp_rule(mp_rule(int_arith_rule(
        `0i <= cm_rep_global_size (a0:cm_global_d) ==>
         cm_rep_global_size a0 +
           cm_rep_globals_size (a1:(cm_global_d)list) <= 1048560i ==>
         cm_rep_globals_size a1 <= 1048560i`),
        head_nonnegative), unfolded_bound);
    thm tail_safe = mp_rule(mp_rule(assume_rule(
        `(!i. 0i <= i ==>
             i < ilength (a1:(cm_global_d)list) ==>
             cm_global_wf (structs:(cm_struct_d)list)
               (inth i a1)) ==>
         cm_rep_globals_size a1 <= 1048560i ==>
         cm_rep_globals_safe a1`), tail_wf), tail_bound);
    thm parts = conj_rule(head_nonnegative,
        conj_rule(tail_nonnegative,
          conj_rule(full_bound, tail_safe)));
    thm view = apply_conversion(rewrite_conv(THM_LIST(
        get_cm_rep_globals_safe_def())),
        `cm_rep_globals_safe
          ((a0:cm_global_d) :: (a1:(cm_global_d)list))`);
    ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(view), parts));
  }
  return gnode_prove(root);
}
PROOF static thm cm_globals_safe = cm_prove_globals_safe();

PROOF static thm cm_prove_strings_nonnegative(void) {
  gnode root = gnode_new_with_ccl(
      `!(strings:(cm_string_d)list).
         0i <= cm_rep_strings_size strings`);
  gnode_list cases = INDUCT_TAC(root,
      `strings:(cm_string_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_rep_strings_size_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm length_nonnegative = ispec_rule(
        `cm_string_bytes (a0:cm_string_d)`,
        get_theorem_by_name("ILENGTH_NONNEG"));
    thm tail_nonnegative = assume_rule(
        `0i <= cm_rep_strings_size (a1:(cm_string_d)list)`);
    thm sum = mp_rule(mp_rule(int_arith_rule(
        `0i <= ilength (cm_string_bytes (a0:cm_string_d)) ==>
         0i <= cm_rep_strings_size (a1:(cm_string_d)list) ==>
         0i <= (ilength (cm_string_bytes a0) + 1i) +
           cm_rep_strings_size a1`),
        length_nonnegative), tail_nonnegative);
    thm view = apply_conversion(rewrite_conv(THM_LIST(
        get_cm_rep_strings_size_def(),
        get_cm_rep_string_size_def(),
        get_cm_rep_string_length_def())),
        `0i <= cm_rep_strings_size
          ((a0:cm_string_d) :: (a1:(cm_string_d)list))`);
    ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(view), sum));
  }
  return gnode_prove(root);
}
PROOF static thm cm_strings_nonnegative =
    cm_prove_strings_nonnegative();

PROOF static thm cm_prove_strings_safe(void) {
  gnode root = gnode_new_with_ccl(
      `!(strings:(cm_string_d)list).
         cm_rep_strings_size strings <= 1048560i ==>
         cm_rep_strings_safe strings`);
  gnode_list cases = INDUCT_TAC(root,
      `strings:(cm_string_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_rep_strings_safe_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm full_bound = assume_rule(
        `cm_rep_strings_size
          ((a0:cm_string_d) :: (a1:(cm_string_d)list)) <= 1048560i`);
    thm length_nonnegative = ispec_rule(
        `cm_string_bytes (a0:cm_string_d)`,
        get_theorem_by_name("ILENGTH_NONNEG"));
    thm head_nonnegative = mp_rule(int_arith_rule(
        `0i <= ilength (cm_string_bytes (a0:cm_string_d)) ==>
         0i <= ilength (cm_string_bytes a0) + 1i`),
        length_nonnegative);
    thm head_model = conv_rule(rewrite_conv(THM_LIST(
        get_cm_rep_string_length_def())), inst_rule(TERM_PAIR_LIST(
          (term_pair){`a0:cm_string_d`, `string:cm_string_d`}),
        get_cm_rep_string_size_def()));
    head_nonnegative = conv_rule(rewrite_conv(THM_LIST(
        sym_rule(head_model))), head_nonnegative);
    thm tail_nonnegative = spec_rule(
        `a1:(cm_string_d)list`, cm_strings_nonnegative);
    thm unfolded_bound = conv_rule(rewrite_conv(THM_LIST(
        get_cm_rep_strings_size_def())), full_bound);
    thm tail_bound = mp_rule(mp_rule(int_arith_rule(
        `0i <= cm_rep_string_size (a0:cm_string_d) ==>
         cm_rep_string_size a0 +
           cm_rep_strings_size (a1:(cm_string_d)list) <= 1048560i ==>
         cm_rep_strings_size a1 <= 1048560i`),
        head_nonnegative), unfolded_bound);
    thm tail_safe = mp_rule(assume_rule(
        `cm_rep_strings_size (a1:(cm_string_d)list) <= 1048560i ==>
         cm_rep_strings_safe a1`), tail_bound);
    thm parts = conj_rule(head_nonnegative,
        conj_rule(tail_nonnegative,
          conj_rule(full_bound, tail_safe)));
    thm view = apply_conversion(rewrite_conv(THM_LIST(
        get_cm_rep_strings_safe_def())),
        `cm_rep_strings_safe
          ((a0:cm_string_d) :: (a1:(cm_string_d)list))`);
    ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(view), parts));
  }
  return gnode_prove(root);
}
PROOF static thm cm_strings_safe = cm_prove_strings_safe();

PROOF static thm cm_prove_strings_size_matches(void) {
  return induct_rewrite_close(
      `!(strings:(cm_string_d)list).
         cm_rep_strings_size strings == cm_strings_size strings`,
      `strings:(cm_string_d)list`,
      THM_LIST(get_cm_rep_strings_size_def(),
        get_cm_strings_size_def()),
      THM_LIST(get_cm_rep_strings_size_def(),
        get_cm_rep_string_size_def(),
        get_cm_rep_string_length_def(),
        get_cm_strings_size_def(),
        get_theorem_by_name("INT_ADD_ASSOC")));
}
PROOF static thm cm_strings_size_matches =
    cm_prove_strings_size_matches();

PROOF static thm cm_prove_globals_model_size_matches(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (globals:(cm_global_d)list).
         (!i. 0i <= i ==> i < ilength globals ==>
              cm_global_wf structs (inth i globals)) ==>
         cm_globals_model_size structs globals ==
           cm_globals_size structs globals`);
  gnode with_structs = GEN_TAC(root, "structs");
  gnode_list cases = INDUCT_TAC(with_structs,
      `globals:(cm_global_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_globals_model_size_def(), get_cm_globals_size_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm all_wf = assume_rule(
        `!i. 0i <= i ==>
           i < ilength ((a0:cm_global_d) ::
             (a1:(cm_global_d)list)) ==>
           cm_global_wf (structs:(cm_struct_d)list)
             (inth i (a0 :: a1))`);
    thm head_wf = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`, `a0:cm_global_d`,
        `a1:(cm_global_d)list`), cm_globals_wf_head), all_wf);
    thm tail_wf = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`, `a0:cm_global_d`,
        `a1:(cm_global_d)list`), cm_globals_wf_tail), all_wf);
    thm opened = conv_rule(rewrite_conv(THM_LIST(
        get_cm_global_wf_def())), head_wf);
    thm positive = conjunct1_rule(conjunct2_rule(
        conjunct2_rule(opened)));
    thm nonnegative = mp_rule(int_arith_rule(
        `0i < cm_global_size (structs:(cm_struct_d)list)
          (a0:cm_global_d) ==>
         0i <= cm_global_size structs a0`), positive);
    thm tail = mp_rule(assume_rule(
        `(!i. 0i <= i ==>
             i < ilength (a1:(cm_global_d)list) ==>
             cm_global_wf (structs:(cm_struct_d)list)
               (inth i a1)) ==>
         cm_globals_model_size structs a1 ==
           cm_globals_size structs a1`), tail_wf);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_globals_model_size_def(),
        get_cm_global_model_size_def(), get_cm_globals_size_def(),
        nonnegative, tail)));
  }
  return gnode_prove(root);
}
PROOF static thm cm_globals_model_size_matches =
    cm_prove_globals_model_size_matches();

PROOF static thm cm_prove_data_ready_from_typed(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program).
         cm_typed_program p ==> cm_concrete_data_ready p`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm typed = assume_rule(`cm_typed_program (p:cm_program)`);
  thm opened = conv_rule(rewrite_conv(THM_LIST(
      get_cm_typed_program_def())), typed);
  thm globals_wf = mp_rule(taut_rule(mk_imp(concl(opened),
      `!i. 0i <= i ==>
         i < ilength (cm_program_globals (p:cm_program)) ==>
         cm_global_wf (cm_program_structs p)
           (inth i (cm_program_globals p))`)), opened);
  thm static_upper = mp_rule(taut_rule(mk_imp(concl(opened),
      `cm_static_size (p:cm_program) <= 1048576i`)), opened);
  thm global_size_match = mp_rule(specl_rule(TERM_LIST(
      `cm_program_structs (p:cm_program)`,
      `cm_program_globals (p:cm_program)`),
      cm_rep_globals_size_matches), globals_wf);
  thm global_model_match = mp_rule(specl_rule(TERM_LIST(
      `cm_program_structs (p:cm_program)`,
      `cm_program_globals (p:cm_program)`),
      cm_globals_model_size_matches), globals_wf);
  thm string_size_match = spec_rule(
      `cm_program_strings (p:cm_program)`, cm_strings_size_matches);
  thm global_nonnegative = mp_rule(specl_rule(TERM_LIST(
      `cm_program_structs (p:cm_program)`,
      `cm_program_globals (p:cm_program)`),
      cm_globals_nonnegative), globals_wf);
  thm string_nonnegative = spec_rule(
      `cm_program_strings (p:cm_program)`, cm_strings_nonnegative);
  thm static_data_bound = conv_rule(rewrite_conv(THM_LIST(
      get_cm_static_size_def(), sym_rule(global_size_match),
      sym_rule(string_size_match))), static_upper);
  thm total_bound = mp_rule(int_arith_rule(
      `16i + cm_rep_globals_size
          (cm_program_globals (p:cm_program)) +
          cm_rep_strings_size (cm_program_strings p) <= 1048576i ==>
       cm_rep_globals_size (cm_program_globals p) +
         cm_rep_strings_size (cm_program_strings p) <= 1048560i`),
      static_data_bound);
  thm globals_bound = mp_rule(mp_rule(int_arith_rule(
      `0i <= cm_rep_strings_size (cm_program_strings (p:cm_program)) ==>
       cm_rep_globals_size (cm_program_globals p) +
         cm_rep_strings_size (cm_program_strings p) <= 1048560i ==>
       cm_rep_globals_size (cm_program_globals p) <= 1048560i`),
      string_nonnegative), total_bound);
  thm strings_bound = mp_rule(mp_rule(int_arith_rule(
      `0i <= cm_rep_globals_size (cm_program_globals (p:cm_program)) ==>
       cm_rep_globals_size (cm_program_globals p) +
         cm_rep_strings_size (cm_program_strings p) <= 1048560i ==>
       cm_rep_strings_size (cm_program_strings p) <= 1048560i`),
      global_nonnegative), total_bound);
  thm globals_safe = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `cm_program_structs (p:cm_program)`,
      `cm_program_globals (p:cm_program)`), cm_globals_safe),
      globals_wf), globals_bound);
  thm strings_safe = mp_rule(spec_rule(
      `cm_program_strings (p:cm_program)`, cm_strings_safe),
      strings_bound);
  thm globals_ready = mp_rule(specl_rule(TERM_LIST(
      `cm_program_structs (p:cm_program)`,
      `cm_program_globals (p:cm_program)`),
      cm_data_globals_from_indexed), globals_wf);
  thm length_exact = spec_rule(`p:cm_program`,
      get_cm_model_data_length_exact());
  thm length_model = conv_rule(rewrite_conv(THM_LIST(
      get_cm_model_data_size_count_def(), global_model_match,
      sym_rule(global_size_match), sym_rule(string_size_match),
      get_theorem_by_name("INT_ADD_ASSOC"))), length_exact);
  thm parts = conj_rule(globals_safe,
      conj_rule(globals_ready,
        conj_rule(strings_safe,
          conj_rule(global_nonnegative,
            conj_rule(string_nonnegative,
              conj_rule(total_bound, length_model))))));
  thm view = apply_conversion(rewrite_conv(THM_LIST(
      cm_concrete_data_ready_def)),
      `cm_concrete_data_ready (p:cm_program)`);
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(view), parts));
  return gnode_prove(root);
}
PROOF thm cmc_data_ready_from_typed =
    cm_prove_data_ready_from_typed();

PROOF thm get_cm_concrete_data_ready_def(void) {
  return cm_concrete_data_ready_def;
}
PROOF thm get_cmc_data_ready_from_typed(void) {
  return cmc_data_ready_from_typed;
}

PROOF static int _cmc_program_ready_no_axioms =
    vector_size(get_all_axioms()) == _cmc_program_ready_axioms_before
        ? 1 : (abort(), 0);
