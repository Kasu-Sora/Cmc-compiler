#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_correct.h"
#include "cmc_preservation_total.h"
#include "cmc_preservation_state.h"
#include "cmc_annotate_preservation.h"
#include "cmc_lang.h"
#include "tvm_model.h"

#require "cmc_preservation_total_iter.c"
#require "cmc_examples.c"
#require "cmc_examples_calls.c"
#require "cmc_examples_conversion.c"
#require "cmc_examples_struct.c"

PROOF static size_t _cmc_correct_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cmc_pick_fact(thm source, term wanted) {
  if (alpha_compare(concl(source), wanted) == 0) return source;
  if (!is_conj(concl(source))) return empty_theorem;
  thm left = cmc_pick_fact(conjunct1_rule(source), wanted);
  if (!IS_NULL(left)) return left;
  return cmc_pick_fact(conjunct2_rule(source), wanted);
}

PROOF static thm cmc_named_fact(gnode node, const char *label) {
  labeled_term_list assumptions = goal_lasmps(node->g);
  return assume_rule(assumptions[labeled_term_list_index(
      assumptions, label)].tm);
}

PROOF static thm cmc_prove_successful_exec_simulation(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (input:(int)list) (st:cm_src_state)
         (ctl:cm_control) (status:int).
         cm_wf_program p ==>
         cm_exec (CMStartTask p input) (CMOutcome st ctl status) ==>
         cm_success_control ctl ==>
         ?vm.
           tvm_exec (TVMBoot (cm_compile_model p) input)
             (TVMOutcome (vm:tvm_state) status 0i) &&
           tvm_output vm == cm_state_output st`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm wf = assume_rule(`cm_wf_program (p:cm_program)`);
  thm source_run = assume_rule(
      `cm_exec (CMStartTask (p:cm_program) (input:(int)list))
        (CMOutcome (st:cm_src_state) (ctl:cm_control) (status:int))`);
  thm success = assume_rule(`cm_success_control (ctl:cm_control)`);
  thm succeeds_witness = exists_rule(
      `?st0 ctl0 status0.
         cm_exec (CMStartTask (p:cm_program) (input:(int)list))
           (CMOutcome (st0:cm_src_state) (ctl0:cm_control) (status0:int)) &&
         cm_success_control ctl0`, `st:cm_src_state`, exists_rule(
        `?ctl0 status0.
           cm_exec (CMStartTask (p:cm_program) (input:(int)list))
             (CMOutcome (st:cm_src_state) (ctl0:cm_control) (status0:int)) &&
           cm_success_control ctl0`, `ctl:cm_control`, exists_rule(
          `?status0.
             cm_exec (CMStartTask (p:cm_program) (input:(int)list))
               (CMOutcome (st:cm_src_state) (ctl:cm_control) (status0:int)) &&
             cm_success_control ctl`, `status:int`,
          conj_rule(source_run, success))));
  thm succeeds = eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(get_cm_task_succeeds_def())),
      `cm_task_succeeds (CMStartTask (p:cm_program) (input:(int)list))`)),
      succeeds_witness);
  thm initial = match_mp_rule(match_mp_rule(
      get_cm_preservation_initial(), wf), succeeds);
  thm source_witness = match_mp_rule(get_cm_exec_witness(), source_run);
  leaf = ASSUME_TAC(leaf, source_witness, "Hsource_witness");
  leaf = ASMP_EXISTS_TAC(leaf, "Hsource_witness", "steps");
  leaf = ASMP_EXISTS_TAC(leaf, "Hsource_witness", "last_state");
  leaf = ASMP_EXISTS_TAC(leaf, "Hsource_witness", "last_control");
  leaf = ASMP_EXISTS_TAC(leaf, "Hsource_witness", "last_status");
  thm witness_body = cmc_named_fact(leaf, "Hsource_witness");
  thm outcome_same = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_datatype_injectivity("cm_outcome"))), conjunct2_rule(witness_body));
  thm_list outcome_rewrites = THM_LIST(
      sym_rule(conjunct1_rule(outcome_same)),
      sym_rule(conjunct1_rule(conjunct2_rule(outcome_same))),
      sym_rule(conjunct2_rule(conjunct2_rule(outcome_same))));
  thm done_task = conv_rule(rewrite_conv(outcome_rewrites),
      conjunct1_rule(witness_body));
  term initial_ast = `cm_annotated_start (p:cm_program) (input:(int)list)`;
  term final_ast = `cm_annotated_iter (steps:num) ${initial_ast:cm_astate}`;
  thm final_invariant = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `steps:num`, `p:cm_program`, initial_ast),
      get_cm_preservation_iter()), wf), initial);
  thm iter_task_raw = specl_rule(
      TERM_LIST(`steps:num`, initial_ast), cm_annotated_iter_task);
  thm initial_task = apply_conversion(reduce_rewrite_conv(THM_LIST(
      cm_annotated_start_def, cm_astate_task_def)),
      `cm_astate_task ${initial_ast:cm_astate}`);
  thm initial_iter = beta_norm(ap_term_rule(
      `\task:cm_task. cm_iter (steps:num) task`, initial_task));
  thm iter_task = trans_rule(iter_task_raw, initial_iter);
  thm final_task = trans_rule(iter_task, done_task);
  thm expanded = conv_rule(rewrite_conv(THM_LIST(
      get_cm_preservation_invariant_def())), final_invariant);
  thm final_sim = cmc_pick_fact(expanded,
      `cm_task_target_sim (p:cm_program) (cm_astate_task ${final_ast:cm_astate})
        (cm_astate_target ${final_ast:cm_astate})
        (cm_astate_annotation ${final_ast:cm_astate})`);
  thm sim_task_equality = beta_norm(ap_term_rule(
      `\task:cm_task.
         cm_task_target_sim (p:cm_program) task
           (cm_astate_target ${final_ast:cm_astate})
           (cm_astate_annotation ${final_ast:cm_astate})`,
      final_task));
  thm done_sim = eq_mp_rule(sim_task_equality, final_sim);
  thm target_witness = match_mp_rule(get_cm_done_target_observation(), done_sim);
  leaf = ASSUME_TAC(leaf, target_witness, "Htarget_witness");
  leaf = ASMP_EXISTS_TAC(leaf, "Htarget_witness", "vm");
  thm target_body = cmc_named_fact(leaf, "Htarget_witness");
  thm target_done = specl_rule(TERM_LIST(
      `vm:tvm_state`, `status:int`, `0i:int`), get_tvm_exec_done());
  thm target_equality = beta_norm(ap_term_rule(
      `\at:tvm_task.
         tvm_exec at (TVMOutcome (vm:tvm_state) (status:int) 0i)`,
      conjunct1_rule(target_body)));
  thm final_run = eq_mp_rule(sym_rule(target_equality), target_done);
  thm lifted = match_mp_rule(get_cm_annotated_iter_exec_prefix(), final_run);
  thm boot_run = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_annotated_start_def, cm_astate_target_def)), lifted);
  thm observation = exists_rule(goal_ccl(leaf->g), `vm:tvm_state`,
      conj_rule(boot_run, conjunct2_rule(target_body)));
  ACCEPT_TAC(leaf, observation);
  return gnode_prove(root);
}
PROOF static thm cmc_successful_exec_simulation =
    cmc_prove_successful_exec_simulation();

PROOF static thm cmc_prove_valid_input_bridge(void) {
  thm_list definitions = get_tvm_eval_defs();
  vector_add(&definitions, get_cm_valid_input_def());
  gnode root = gnode_new_with_ccl(
      `!(input:(int)list). cm_valid_input input ==> tvm_valid_input input`);
  CONV_TAC(root, reduce_rewrite_conv(definitions));
  return gnode_prove(root);
}
PROOF static thm cmc_valid_input_bridge = cmc_prove_valid_input_bridge();

PROOF static thm cmc_prove_preservation(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (input:(int)list) (output:(int)list) (status:int).
         cm_wf_program p && cm_source_terminates p input output status ==>
         tvm_terminates (cm_compile_model p) input output status`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm premises = assume_rule(
      `cm_wf_program (p:cm_program) &&
       cm_source_terminates p (input:(int)list) (output:(int)list) (status:int)`);
  thm wf = conjunct1_rule(premises);
  thm source = conv_rule(rewrite_conv(THM_LIST(
      get_cm_source_terminates_def())), conjunct2_rule(premises));
  thm target_input = match_mp_rule(cmc_valid_input_bridge, conjunct1_rule(source));
  thm status_byte = conjunct1_rule(conjunct2_rule(source));
  leaf = ASSUME_TAC(leaf, conjunct2_rule(conjunct2_rule(source)), "Hsource_run");
  leaf = ASMP_EXISTS_TAC(leaf, "Hsource_run", "st");
  leaf = ASMP_EXISTS_TAC(leaf, "Hsource_run", "ctl");
  thm source_body = cmc_named_fact(leaf, "Hsource_run");
  thm target = match_mp_rule(match_mp_rule(match_mp_rule(
      cmc_successful_exec_simulation, wf), conjunct1_rule(source_body)),
      conjunct1_rule(conjunct2_rule(source_body)));
  leaf = ASSUME_TAC(leaf, target, "Htarget_run");
  leaf = ASMP_EXISTS_TAC(leaf, "Htarget_run", "vm");
  thm target_body = cmc_named_fact(leaf, "Htarget_run");
  thm output_equal = trans_rule(conjunct2_rule(target_body),
      conjunct2_rule(conjunct2_rule(source_body)));
  thm run = exists_rule(
      `?vm.
         tvm_exec (TVMBoot (cm_compile_model (p:cm_program)) (input:(int)list))
           (TVMOutcome (vm:tvm_state) (status:int) 0i) &&
         tvm_output vm == (output:(int)list)`, `vm:tvm_state`,
      conj_rule(conjunct1_rule(target_body), output_equal));
  gnode unfolded = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(get_tvm_terminates_def())));
  ACCEPT_TAC(unfolded, conj_rule(target_input, conj_rule(status_byte, run)));
  return gnode_prove(root);
}
PROOF static thm cmc_preservation = cmc_prove_preservation();

PROOF static thm cmc_prove_target_normal_excludes_error(void) {
  gnode root = gnode_new_with_ccl(
      `!(obj:tvm_object) (input:(int)list) (output:(int)list)
         (status:int) (error_output:(int)list).
         tvm_terminates obj input output status ==>
         ~tvm_errors obj input error_output`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm normal = conv_rule(rewrite_conv(THM_LIST(get_tvm_terminates_def())),
      assume_rule(`tvm_terminates (obj:tvm_object) (input:(int)list)
        (output:(int)list) (status:int)`));
  thm error = conv_rule(rewrite_conv(THM_LIST(get_tvm_errors_def())),
      assume_rule(`tvm_errors (obj:tvm_object) (input:(int)list)
        (error_output:(int)list)`));
  leaf = ASSUME_TAC(leaf, conjunct2_rule(conjunct2_rule(normal)), "Hnormal");
  leaf = ASMP_EXISTS_TAC(leaf, "Hnormal", "normal_vm");
  leaf = ASSUME_TAC(leaf, conjunct2_rule(error), "Herror");
  leaf = ASMP_EXISTS_TAC(leaf, "Herror", "error_vm");
  thm same_outcome = match_mp_rule(match_mp_rule(get_tvm_deterministic(),
      conjunct1_rule(cmc_named_fact(leaf, "Hnormal"))),
      conjunct1_rule(cmc_named_fact(leaf, "Herror")));
  thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_datatype_injectivity("tvm_outcome"))), same_outcome);
  CONTR_TAC(leaf, impossible);
  return gnode_prove(root);
}
PROOF static thm cmc_target_normal_excludes_error =
    cmc_prove_target_normal_excludes_error();

PROOF static thm cmc_prove_no_vm_error(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (input:(int)list) (output:(int)list)
         (status:int) (error_output:(int)list).
         cm_wf_program p && cm_source_terminates p input output status ==>
         ~tvm_errors (cm_compile_model p) input error_output`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm premises = assume_rule(
      `cm_wf_program (p:cm_program) &&
       cm_source_terminates p (input:(int)list) (output:(int)list) (status:int)`);
  thm preserved = match_mp_rule(cmc_preservation, premises);
  thm not_error = match_mp_rule(specl_rule(TERM_LIST(
      `cm_compile_model (p:cm_program)`, `input:(int)list`,
      `output:(int)list`, `status:int`, `error_output:(int)list`),
      cmc_target_normal_excludes_error), preserved);
  thm impossible = not_elim_rule(not_error,
      assume_rule(`tvm_errors (cm_compile_model (p:cm_program))
        (input:(int)list) (error_output:(int)list)`));
  CONTR_TAC(leaf, impossible);
  return gnode_prove(root);
}
PROOF static thm cmc_no_vm_error = cmc_prove_no_vm_error();

PROOF thm get_cmc_preservation(void) { return cmc_preservation; }
PROOF thm get_cmc_no_vm_error(void) { return cmc_no_vm_error; }

PROOF static int cmc_correct_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) == _cmc_correct_axioms_before,
      "cmc_correct introduced an axiom");
  ENSURE_COND(!IS_NULL(cmc_successful_exec_simulation) &&
      vector_size(hyp(cmc_successful_exec_simulation)) == 0 &&
      vector_size(free_vars(concl(cmc_successful_exec_simulation))) == 0 &&
      alpha_compare(concl(cmc_successful_exec_simulation),
        `!(p:cm_program) (input:(int)list) (st:cm_src_state)
           (ctl:cm_control) (status:int).
           cm_wf_program p ==>
           cm_exec (CMStartTask p input) (CMOutcome st ctl status) ==>
           cm_success_control ctl ==>
           ?vm.
             tvm_exec (TVMBoot (cm_compile_model p) input)
               (TVMOutcome (vm:tvm_state) status 0i) &&
             tvm_output vm == cm_state_output st`) == 0,
      "successful execution simulation has the wrong contract");
  ENSURE_COND(!IS_NULL(get_cmc_preservation()) &&
      vector_size(hyp(get_cmc_preservation())) == 0 &&
      vector_size(free_vars(concl(get_cmc_preservation()))) == 0 &&
      alpha_compare(concl(get_cmc_preservation()),
        `!(p:cm_program) (input:(int)list) (output:(int)list) (status:int).
           cm_wf_program p && cm_source_terminates p input output status ==>
           tvm_terminates (cm_compile_model p) input output status`) == 0,
      "compiler preservation theorem has the wrong contract");
  ENSURE_COND(!IS_NULL(get_cmc_no_vm_error()) &&
      vector_size(hyp(get_cmc_no_vm_error())) == 0 &&
      vector_size(free_vars(concl(get_cmc_no_vm_error()))) == 0 &&
      alpha_compare(concl(get_cmc_no_vm_error()),
        `!(p:cm_program) (input:(int)list) (output:(int)list)
           (status:int) (error_output:(int)list).
           cm_wf_program p && cm_source_terminates p input output status ==>
           ~tvm_errors (cm_compile_model p) input error_output`) == 0,
      "compiler VM-error exclusion theorem has the wrong contract");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_correct_checks = cmc_correct_final_checks();
