#include "proof/proof.h"
#include "cmc_preservation_code_value.h"
#include "userlib/proof.h"
#include "cmc_preservation_target_value_return.h"
#include "cmc_preservation_target_machine.h"

#require "cmc_preservation_target_value_branch.c"

PROOF static size_t _cmc_preservation_target_value_return_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_target_v_return_step(void) {
  term task =
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
        (st:cm_src_state)
        (CMReturnK :: cm_cursor_frames (rest:(cm_acursor)list))`;
  term ann =
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
        (CMACursor CAReturnP (owner:int)
          (saved_break:int) (saved_continue:int) ::
         (rest:(cm_acursor)list))
        (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`;
  term next_ann =
      `cm_update_annotation
        (cm_annotation_step ${task:cm_task} ${ann:cm_annotation})`;
  term body = imp_chain(TERM_LIST(
      `cm_task_target_sim (p:cm_program) ${task:cm_task}
        (target:tvm_task) ${ann:cm_annotation}`),
      `cm_task_target_sim (p:cm_program)
        (cm_step ${task:cm_task})
        (tvm_iter
          (cm_update_steps
            (cm_annotation_step ${task:cm_task} ${ann:cm_annotation}))
          (target:tvm_task))
        ${next_ann:cm_annotation}`);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm running = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_target_sim_def)), assume_rule(
        `cm_task_target_sim (p:cm_program) ${task:cm_task}
          (target:tvm_task) ${ann:cm_annotation}`));
  thm reannotated = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `[v:cm_value]`, ann, next_ann, `target:tvm_task`),
      get_cm_target_reannotate());
  thm_list ann_rules = cm_v_layout_rules();
  vector_add(&ann_rules, cm_ann_linear_def);
  vector_add(&ann_rules, cm_ann_plain_def);
  for (size_t premise = 0; premise < 4; ++premise) {
    reannotated = match_mp_rule(reannotated,
        eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(ann_rules),
          dest_imp(concl(reannotated)).tm1)));
  }
  thm result = match_mp_rule(reannotated, running);
  thm_list finish_rules = cm_v_layout_rules();
  vector_add(&finish_rules, cm_task_target_sim_def);
  vector_add(&finish_rules, cm_running_target_sim_def);
  vector_add(&finish_rules, cm_active_spill_frames_def);
  vector_add(&finish_rules, cm_update_steps_def);
  vector_add(&finish_rules, get_tvm_iter_def());
  vector_add(&finish_rules, get_cm_control_value_def());
  gnode reduced = CONV_TAC(
      leaf, reduce_rewrite_conv(finish_rules));
  result = conv_rule(reduce_rewrite_conv(finish_rules), result);
  ACCEPT_TAC(reduced, result);
  return gnode_prove(root);
}

PROOF thm cm_target_v_return_step =
    cm_prove_target_v_return_step();

PROOF thm get_cm_target_v_return_step(void) {
  return cm_target_v_return_step;
}

PROOF static int cmc_preservation_target_value_return_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_value_return_axioms_before,
      "cmc_preservation_target_value_return introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_value_return_checks =
    cmc_preservation_target_value_return_final_checks();
