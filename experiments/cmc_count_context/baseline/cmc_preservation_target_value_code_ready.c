#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_code_value.h"
#require "cmc_preservation_code_value.c"
#include "cmc_preservation_layout.h"
#require "cmc_preservation_layout.c"
#include "cmc_preservation_type_ready.h"
#require "cmc_preservation_type_ready.c"
#include "cmc_preservation_target_value_code_ready.h"

PROOF static size_t _cmc_preservation_target_value_code_ready_axioms_before =
    vector_size(get_all_axioms());


PROOF static thm_list cm_value_code_nonempty_rules(void) {
  return THM_LIST(
      get_cm_phase_input_type_ready_def(),
      cm_value_phase_code_def,
      get_cm_load_code_def(), get_cm_store_code_def(),
      get_cm_char_normalize_code_def(),
      get_cm_fp_relative_address_code_def(),
      get_cm_temp_store_code_def(), get_cm_temp_load_code_def(),
      get_cm_binary_finish_code_def(),
      cm_assign_tail_code_def, cm_index_tail_code_def,
      cm_member_tail_code_def, cm_init_tail_code_def,
      cm_status_tail_code_def, cm_return_tail_code_def,
      get_cm_return_epilogue_def(),
      get_theorem_by_name("APPEND_EQ_NIL"),
      get_theorem_by_name("APPEND"),
      get_theorem_by_name("APPEND_NIL"),
      get_theorem_by_name("NOT_CONS_NIL"));
}

PROOF static thm cm_prove_value_phase_code_nonempty(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (pc:int) (temp:int) (owner:int)
         (breakpc:int) (continuepc:int) (phase:cm_aphase)
         (incoming:cm_type).
         cm_phase_input_type_ready p fid phase incoming ==>
         ~(cm_value_phase_code p fid pc temp owner breakpc continuepc
           phase == [])`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list phase_cases = INDUCT_TAC(leaf, `phase:cm_aphase`);
  thm_list rules = cm_value_code_nonempty_rules();

  for (size_t i = 0; i < vector_size(phase_cases); ++i) {
    if (i == 4 || i == 5) {
      gnode_list zero_cases = BOOL_CASES_TAC(
          phase_cases[i], `(a0:int) == 0i`, "Hop_zero");
      for (size_t j = 0; j < vector_size(zero_cases); ++j) {
        gnode_list one_cases = BOOL_CASES_TAC(
            zero_cases[j], `(a0:int) == 1i`, "Hop_one");
        for (size_t k = 0; k < vector_size(one_cases); ++k) {
          CONV_WITH_ASMP_TAC(one_cases[k], reduce_rewrite_conv, rules);
        }
      }
    } else {
      CONV_WITH_ASMP_TAC(phase_cases[i], reduce_rewrite_conv, rules);
    }
  }

  return gnode_prove(root);
}
PROOF static thm cm_value_phase_code_nonempty =
    cm_prove_value_phase_code_nonempty();

PROOF static thm cm_prove_value_cursor_code_nonempty(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (pc:int) (temp:int)
         (incoming:cm_type) (cursors:(cm_acursor)list).
         cm_cursor_head_input_type_ready p fid incoming cursors ==>
         ~(cm_cursor_code p fid pc temp F cursors == [])`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cursor_cases = DISJ_CASES_TAC(
      leaf,
      ispec_rule(`cursors:(cm_acursor)list`,
        get_theorem_by_name("list_CASES")),
      "Hcursors");

  thm nil_shape = assume_rule(
      goal_lasmps(cursor_cases[0]->g)[labeled_term_list_index(
        goal_lasmps(cursor_cases[0]->g), "Hcursors")].tm);
  thm nil_result = conv_rule(
      reduce_rewrite_conv(THM_LIST(
        nil_shape, get_cm_cursor_head_input_type_ready_def())),
      assume_rule(
        `cm_cursor_head_input_type_ready (p:cm_program) (fid:int)
          (incoming:cm_type) (cursors:(cm_acursor)list)`));
  ACCEPT_TAC(cursor_cases[0], nil_result);

  gnode cons = ASMP_EXISTS_TAC(cursor_cases[1], "Hcursors", "cursor");
  cons = ASMP_EXISTS_TAC(cons, "Hcursors", "rest");
  thm cursor_shape = assume_rule(
      goal_lasmps(cons->g)[labeled_term_list_index(
        goal_lasmps(cons->g), "Hcursors")].tm);
  thm input_ready = conv_rule(
      reduce_rewrite_conv(THM_LIST(
        cursor_shape, get_cm_cursor_head_input_type_ready_def())),
      assume_rule(
        `cm_cursor_head_input_type_ready (p:cm_program) (fid:int)
          (incoming:cm_type) (cursors:(cm_acursor)list)`));
  thm phase_nonempty = match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `pc:int`, `temp:int`,
        `cm_cursor_temp (cursor:cm_acursor)`,
        `cm_cursor_break (cursor:cm_acursor)`,
        `cm_cursor_continue (cursor:cm_acursor)`,
        `cm_cursor_phase (cursor:cm_acursor)`,
        `incoming:cm_type`), cm_value_phase_code_nonempty),
      input_ready);
  thm_list closing_rules = THM_LIST(
      cursor_shape, cm_cursor_code_def,
      get_theorem_by_name("APPEND_EQ_NIL"), phase_nonempty);
  thm cons_result = conv_rule(
      reduce_rewrite_conv(closing_rules),
      assume_rule(
        `cm_cursor_code (p:cm_program) (fid:int) (pc:int) (temp:int)
          F (cursors:(cm_acursor)list) == []`));
  ACCEPT_TAC(cons, cons_result);

  return gnode_prove(root);
}
PROOF thm cm_value_cursor_code_nonempty =
    cm_prove_value_cursor_code_nonempty();

PROOF static thm cm_prove_code_at_suffix_head_target_valid(void) {
  gnode root = gnode_new_with_ccl(
      `!(code:(tvm_inst)list) (pc:int) (prefix:(tvm_inst)list)
         (head:tvm_inst) (suffix:(tvm_inst)list).
         cm_code_at code pc (prefix ++ head :: suffix) ==>
         tvm_target_valid code (pc + ilength prefix)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm tail_at = match_mp_rule(ispecl_rule(TERM_LIST(
      `code:(tvm_inst)list`, `pc:int`, `prefix:(tvm_inst)list`,
      `(head:tvm_inst) :: (suffix:(tvm_inst)list)`),
      get_cm_code_at_append_right()), assume_rule(
        `cm_code_at (code:(tvm_inst)list) (pc:int)
          ((prefix:(tvm_inst)list) ++
           (head:tvm_inst) :: (suffix:(tvm_inst)list))`));
  thm at_head = match_mp_rule(get_cm_code_at_head(), tail_at);
  thm bounds = conj_rule(conjunct1_rule(at_head),
      conjunct1_rule(conjunct2_rule(at_head)));
  thm target_view = apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_tvm_target_valid_def())),
      goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), bounds));
  return gnode_prove(root);
}
PROOF thm cm_code_at_suffix_head_target_valid =
    cm_prove_code_at_suffix_head_target_valid();

PROOF static thm cm_prove_value_continuation_target_valid(void) {
  gnode root = gnode_new_with_ccl(
      `!(code:(tvm_inst)list) (p:cm_program) (fid:int) (pc:int)
         (temp:int) (incoming:cm_type) (prefix:(tvm_inst)list)
         (cursors:(cm_acursor)list).
         cm_code_at code pc
           (prefix ++
            cm_cursor_code p fid (pc + ilength prefix) temp F cursors) ==>
         cm_cursor_head_input_type_ready p fid incoming cursors ==>
         tvm_target_valid code (pc + ilength prefix)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm code_at = assume_rule(
      `cm_code_at (code:(tvm_inst)list) (pc:int)
        ((prefix:(tvm_inst)list) ++
         cm_cursor_code (p:cm_program) (fid:int)
           (pc + ilength prefix) (temp:int) F
           (cursors:(cm_acursor)list))`);
  thm suffix_at = match_mp_rule(ispecl_rule(TERM_LIST(
      `code:(tvm_inst)list`, `pc:int`, `prefix:(tvm_inst)list`,
      `cm_cursor_code (p:cm_program) (fid:int)
        (pc + ilength (prefix:(tvm_inst)list)) (temp:int) F
        (cursors:(cm_acursor)list)`), get_cm_code_at_append_right()),
      code_at);
  thm nonempty = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`,
      `pc + ilength (prefix:(tvm_inst)list)`, `temp:int`,
      `incoming:cm_type`, `cursors:(cm_acursor)list`),
      cm_value_cursor_code_nonempty),
      assume_rule(
        `cm_cursor_head_input_type_ready (p:cm_program) (fid:int)
          (incoming:cm_type) (cursors:(cm_acursor)list)`));
  term suffix = `cm_cursor_code (p:cm_program) (fid:int)
      ((pc:int) + ilength (prefix:(tvm_inst)list)) (temp:int) F
      (cursors:(cm_acursor)list)`;
  gnode_list suffix_cases = DISJ_CASES_TAC(
      leaf, ispec_rule(suffix, get_theorem_by_name("list_CASES")),
      "Hsuffix");
  CONTR_TAC(suffix_cases[0], contra(nonempty, assume_rule(
      `${suffix:(tvm_inst)list} == ([]:(tvm_inst)list)`)));

  gnode cons = ASMP_EXISTS_TAC(suffix_cases[1], "Hsuffix", "head");
  cons = ASMP_EXISTS_TAC(cons, "Hsuffix", "rest");
  thm suffix_shape = assume_rule(
      goal_lasmps(cons->g)[labeled_term_list_index(
        goal_lasmps(cons->g), "Hsuffix")].tm);
  thm head_at = match_mp_rule(get_cm_code_at_head(),
      conv_rule(rewrite_conv(THM_LIST(suffix_shape)), suffix_at));
  thm bounds = conj_rule(conjunct1_rule(head_at),
      conjunct1_rule(conjunct2_rule(head_at)));
  thm target_view = apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_tvm_target_valid_def())),
      goal_ccl(cons->g));
  ACCEPT_TAC(cons, eq_mp_rule(sym_rule(target_view), bounds));

  return gnode_prove(root);
}
PROOF thm cm_value_continuation_target_valid =
    cm_prove_value_continuation_target_valid();

PROOF thm get_cm_code_at_suffix_head_target_valid(void) {
  return cm_code_at_suffix_head_target_valid;
}
PROOF thm get_cm_value_cursor_code_nonempty(void) {
  return cm_value_cursor_code_nonempty;
}
PROOF thm get_cm_value_continuation_target_valid(void) {
  return cm_value_continuation_target_valid;
}

PROOF static int cmc_preservation_target_value_code_ready_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_value_code_ready_axioms_before,
      "cmc_preservation_target_value_code_ready introduced axioms");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_value_code_ready_checked =
    cmc_preservation_target_value_code_ready_final_checks();
