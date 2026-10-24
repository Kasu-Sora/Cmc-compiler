#include "proof/proof.h"
#include "userlib/proof.h"
#include "cmc_preservation_source_conditions.h"
#include "cmc_preservation_source.h"
#include "cmc_lang.h"

#require "cmc_preservation_source.c"

PROOF static size_t _cmc_preservation_source_conditions_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_successor_not_error(const term task) {
  thm not_done = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_cm_task_done_def())),
      mk_not(mk_comb(`cm_task_done`, task))));
  thm next_succeeds = match_mp_rule(
      match_mp_rule(spec_rule(task, cm_task_succeeds_step), not_done),
      assume_rule(mk_comb(`cm_task_succeeds`, task)));
  return match_mp_rule(specl_rule(TERM_LIST(
      `1i:int`, mk_comb(`cm_step`, task)),
      cm_task_succeeds_not_error), next_succeeds);
}

PROOF static thm cm_prove_r_getc_succeeds_input(void) {
  term task =
      `CMRTask (p:cm_program) (fid:int) (CMGetcE (ty:cm_type))
        (st:cm_src_state) (ks:(cm_frame)list)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (ty:cm_type)
         (st:cm_src_state) (ks:(cm_frame)list).
         cm_task_succeeds
           (CMRTask p fid (CMGetcE ty) st ks) ==>
         cm_state_input st == [] ||
         tower_byte_value (HD (cm_state_input st))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm next_not_error = cm_successor_not_error(task);
  gnode_list empty_cases = BOOL_CASES_TAC(
      leaf, `cm_state_input (st:cm_src_state) == []`, "Hempty");
  CONV_WITH_ASMP_TAC(empty_cases[0], reduce_rewrite_conv, THM_LIST());
  gnode_list byte_cases = BOOL_CASES_TAC(empty_cases[1],
      `tower_byte_value (HD (cm_state_input (st:cm_src_state)))`,
      "Hbyte");
  CONV_WITH_ASMP_TAC(byte_cases[0], reduce_rewrite_conv, THM_LIST());
  thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
      assume_rule(`~(cm_state_input (st:cm_src_state) == [])`),
      assume_rule(`~tower_byte_value
        (HD (cm_state_input (st:cm_src_state)))`),
      get_cm_step_def(), get_cm_rstart_def(), cm_error_task_def,
      get_datatype_distinctness("cm_control"),
      get_datatype_injectivity("cm_control"))), next_not_error);
  CONTR_TAC(byte_cases[1], impossible);
  return gnode_prove(root);
}
PROOF thm cm_r_getc_succeeds_input =
    cm_prove_r_getc_succeeds_input();

PROOF static thm cm_prove_r_array_succeeds_address(void) {
  term task =
      `CMRTask (p:cm_program) (fid:int)
        (CMVarE (scope:int) (slot:int) (ty:cm_type))
        (st:cm_src_state) (ks:(cm_frame)list)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (scope:int) (slot:int)
         (ty:cm_type) (st:cm_src_state) (ks:(cm_frame)list).
         cm_task_succeeds
           (CMRTask p fid (CMVarE scope slot ty) st ks) ==>
         cm_binding_array p fid scope slot ==>
         cm_binding_address_ok p fid scope slot st`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm next_not_error = cm_successor_not_error(task);
  gnode_list address_cases = BOOL_CASES_TAC(leaf,
      `cm_binding_address_ok (p:cm_program) (fid:int)
        (scope:int) (slot:int) (st:cm_src_state)`, "Haddress");
  ACCEPT_TAC(address_cases[0], assume_rule(
      `cm_binding_address_ok (p:cm_program) (fid:int)
        (scope:int) (slot:int) (st:cm_src_state)`));
  thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
      assume_rule(`cm_binding_array (p:cm_program) (fid:int)
        (scope:int) (slot:int)`),
      assume_rule(`~cm_binding_address_ok (p:cm_program) (fid:int)
        (scope:int) (slot:int) (st:cm_src_state)`),
      get_cm_step_def(), get_cm_rstart_def(), cm_error_task_def,
      get_datatype_distinctness("cm_control"),
      get_datatype_injectivity("cm_control"))), next_not_error);
  CONTR_TAC(address_cases[1], impossible);
  return gnode_prove(root);
}
PROOF thm cm_r_array_succeeds_address =
    cm_prove_r_array_succeeds_address();

PROOF static thm cm_prove_l_var_succeeds_address(void) {
  term task =
      `CMLTask (p:cm_program) (fid:int)
        (CMVarE (scope:int) (slot:int) (ty:cm_type))
        (st:cm_src_state) (ks:(cm_frame)list)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (scope:int) (slot:int)
         (ty:cm_type) (st:cm_src_state) (ks:(cm_frame)list).
         cm_task_succeeds
           (CMLTask p fid (CMVarE scope slot ty) st ks) ==>
         cm_binding_address_ok p fid scope slot st`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm next_not_error = cm_successor_not_error(task);
  gnode_list address_cases = BOOL_CASES_TAC(leaf,
      `cm_binding_address_ok (p:cm_program) (fid:int)
        (scope:int) (slot:int) (st:cm_src_state)`, "Haddress");
  ACCEPT_TAC(address_cases[0], assume_rule(
      `cm_binding_address_ok (p:cm_program) (fid:int)
        (scope:int) (slot:int) (st:cm_src_state)`));
  thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
      assume_rule(`~cm_binding_address_ok (p:cm_program) (fid:int)
        (scope:int) (slot:int) (st:cm_src_state)`),
      get_cm_step_def(), get_cm_lstart_def(), cm_error_task_def,
      get_datatype_distinctness("cm_control"),
      get_datatype_injectivity("cm_control"))), next_not_error);
  CONTR_TAC(address_cases[1], impossible);
  return gnode_prove(root);
}
PROOF thm cm_l_var_succeeds_address =
    cm_prove_l_var_succeeds_address();

PROOF static thm cm_prove_v_init_succeeds_store(void) {
  term task =
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
        (st:cm_src_state)
        (CMInitK (slot:int) :: (ks:(cm_frame)list))`;
  term store_ok =
      `cm_store_ok
        (cm_slot_ty
          (inth (slot:int)
            (cm_function_locals
              (inth (fid:int) (cm_program_functions (p:cm_program))))))
        (cm_state_env (st:cm_src_state) 1i (slot:int)) st`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (v:cm_value)
         (st:cm_src_state) (slot:int) (ks:(cm_frame)list).
         cm_task_succeeds
           (CMVTask p fid v st (CMInitK slot :: ks)) ==>
         cm_binding_address_ok p fid 1i slot st &&
         cm_store_ok
           (cm_slot_ty
             (inth slot
               (cm_function_locals
                 (inth fid (cm_program_functions p)))))
           (cm_state_env st 1i slot) st`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm next_not_error = cm_successor_not_error(task);
  term address_ok =
      `cm_binding_address_ok (p:cm_program) (fid:int) 1i
        (slot:int) (st:cm_src_state)`;
  gnode_list address_cases = BOOL_CASES_TAC(
      leaf, address_ok, "Haddress");
  {
    gnode_list store_cases = BOOL_CASES_TAC(
        address_cases[0], store_ok, "Hstore");
    ACCEPT_TAC(store_cases[0], conj_rule(
        assume_rule(address_ok), assume_rule(store_ok)));
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        assume_rule(address_ok), assume_rule(mk_not(store_ok)),
        get_cm_step_def(), get_cm_vapply_def(), cm_error_task_def,
        get_theorem_by_name("NOT_CONS_NIL"),
        get_theorem_by_name("HD"), get_theorem_by_name("TL"),
        get_datatype_distinctness("cm_control"),
        get_datatype_injectivity("cm_control"))), next_not_error);
    CONTR_TAC(store_cases[1], impossible);
  }
  thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
      assume_rule(mk_not(address_ok)), get_cm_step_def(),
      get_cm_vapply_def(), cm_error_task_def,
      get_theorem_by_name("NOT_CONS_NIL"),
      get_theorem_by_name("HD"), get_theorem_by_name("TL"),
      get_datatype_distinctness("cm_control"),
      get_datatype_injectivity("cm_control"))), next_not_error);
  CONTR_TAC(address_cases[1], impossible);
  return gnode_prove(root);
}
PROOF thm cm_v_init_succeeds_store =
    cm_prove_v_init_succeeds_store();

PROOF static thm cm_prove_rtask_succeeds_call_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (expr:cm_expr)
         (st:cm_src_state) (ks:(cm_frame)list).
         cm_task_succeeds (CMRTask p fid expr st ks) ==>
         !callee ty.
           expr == CMCallE (callee:int) [] (ty:cm_type) ==>
           cm_call_ok p callee [] st &&
           cm_call_depth ks < 65536i`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term source_task =
      `CMRTask (p:cm_program) (fid:int) (expr:cm_expr)
         (st:cm_src_state) (ks:(cm_frame)list)`;
  thm source_succeeds = assume_rule(
      `cm_task_succeeds
         (CMRTask (p:cm_program) (fid:int) (expr:cm_expr)
           (st:cm_src_state) (ks:(cm_frame)list))`);
  thm source_not_done = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_cm_task_done_def())),
      mk_not(mk_comb(`cm_task_done`, source_task))));
  thm next_succeeds = match_mp_rule(
      match_mp_rule(cm_task_succeeds_step, source_not_done),
      source_succeeds);
  thm next_not_error = match_mp_rule(
      specl_rule(TERM_LIST(
        `1i:int`, mk_comb(`cm_step`, source_task)),
        cm_task_succeeds_not_error),
      next_succeeds);
  term call_ready =
      `cm_call_ok (p:cm_program) (callee:int) []
         (st:cm_src_state) &&
       cm_call_depth (ks:(cm_frame)list) < 65536i`;
  gnode_list ready_cases = BOOL_CASES_TAC(
      leaf, call_ready, "Hcall_ready");
  ACCEPT_TAC(ready_cases[0], assume_rule(call_ready));
  thm shape = assume_rule(
      `(expr:cm_expr) ==
       CMCallE (callee:int) [] (ty:cm_type)`);
  thm_list rules = THM_LIST(
      shape, assume_rule(mk_not(call_ready)),
      get_cm_step_def(), get_cm_rstart_def(),
      get_cm_args_start_def(), get_cm_begin_call_def(),
      cm_error_task_def,
      get_datatype_distinctness("cm_control"),
      get_datatype_injectivity("cm_control"));
  thm impossible = conv_rule(
      reduce_rewrite_conv(rules), next_not_error);
  CONTR_TAC(ready_cases[1], impossible);
  return gnode_prove(root);
}
PROOF thm cm_rtask_succeeds_call_ready =
    cm_prove_rtask_succeeds_call_ready();

PROOF thm get_cm_r_getc_succeeds_input(void) {
  return cm_r_getc_succeeds_input;
}
PROOF thm get_cm_r_array_succeeds_address(void) {
  return cm_r_array_succeeds_address;
}
PROOF thm get_cm_l_var_succeeds_address(void) {
  return cm_l_var_succeeds_address;
}
PROOF thm get_cm_v_init_succeeds_store(void) {
  return cm_v_init_succeeds_store;
}
PROOF thm get_cm_rtask_succeeds_call_ready(void) {
  return cm_rtask_succeeds_call_ready;
}

PROOF static int cmc_preservation_source_conditions_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_source_conditions_axioms_before,
      "cmc_preservation_source_conditions introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_r_getc_succeeds_input)) == 0 &&
      vector_size(hyp(cm_r_array_succeeds_address)) == 0 &&
      vector_size(hyp(cm_l_var_succeeds_address)) == 0 &&
      vector_size(hyp(cm_v_init_succeeds_store)) == 0 &&
      vector_size(hyp(cm_rtask_succeeds_call_ready)) == 0,
      "source condition theorem is not closed");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_source_conditions_checks =
    cmc_preservation_source_conditions_final_checks();
