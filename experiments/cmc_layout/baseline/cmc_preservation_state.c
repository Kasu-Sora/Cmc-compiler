#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_annotate.h"
#require "cmc_annotate.c"
#include "cmc_sim_ops.h"
#require "cmc_sim_ops.c"
#include "cmc_preservation_state.h"

PROOF static size_t _cmc_preservation_state_axioms_before =
    vector_size(get_all_axioms());

PROOF thm cm_active_spill_frames_def = new_fun_definition(
    `cm_active_spill_frames (fid:int) (st:cm_src_state)
       (ann:cm_annotation) : (cm_spill_frame)list =
       CMSpillFrame fid (cm_state_fp st) (cm_ann_spills ann) ::
         cm_ann_saved ann`);

PROOF thm cm_running_target_sim_def = new_fun_definition(
    `cm_running_target_sim (p:cm_program) (fid:int)
       (st:cm_src_state) (values:(cm_value)list)
       (ann:cm_annotation) (target:tvm_task) : bool =
       (?vm.
          target == TVMRunTask (cm_compile_model p) (vm:tvm_state) &&
          tvm_pc vm == cm_ann_pc ann &&
          cm_machine_state_sim p st vm (cm_ann_calls ann)
            (cm_active_spill_frames fid st ann) values [])`);

PROOF thm cm_halted_target_sim_def = new_fun_definition(
    `cm_halted_target_sim (p:cm_program) (fid:int)
       (st:cm_src_state) (status:int) (active:bool)
       (ann:cm_annotation) (target:tvm_task) : bool =
       (?vm.
          target == TVMDoneTask (vm:tvm_state) status 0i &&
          tvm_pc vm == cm_ann_pc ann &&
          cm_machine_state_sim p st vm (cm_ann_calls ann)
            (if active then cm_active_spill_frames fid st ann
             else cm_ann_saved ann) [] [])`);

PROOF thm cm_task_target_sim_def = new_rec_definition(
    get_cm_task_recursion(),
    `(!rootp p input ann target.
        cm_task_target_sim (rootp:cm_program)
          (CMStartTask (p:cm_program) (input:(int)list))
          (target:tvm_task) (ann:cm_annotation) =
        (p == rootp &&
         target == TVMBoot (cm_compile_model rootp) input &&
         ann == cm_initial_annotation)) &&
     (!rootp p fid expr st ks ann target.
        cm_task_target_sim rootp
          (CMRTask (p:cm_program) (fid:int) (expr:cm_expr)
             (st:cm_src_state) (ks:(cm_frame)list)) target ann =
        (p == rootp &&
         cm_running_target_sim rootp fid st [] ann target)) &&
     (!rootp p fid expr st ks ann target.
        cm_task_target_sim rootp
          (CMLTask (p:cm_program) (fid:int) (expr:cm_expr)
             (st:cm_src_state) (ks:(cm_frame)list)) target ann =
        (p == rootp &&
         cm_running_target_sim rootp fid st [] ann target)) &&
     (!rootp p fid stmt st ks ann target.
        cm_task_target_sim rootp
          (CMSTask (p:cm_program) (fid:int) (stmt:cm_stmt)
             (st:cm_src_state) (ks:(cm_frame)list)) target ann =
        (p == rootp &&
         cm_running_target_sim rootp fid st [] ann target)) &&
     (!rootp p fid v st ks ann target.
        cm_task_target_sim rootp
          (CMVTask (p:cm_program) (fid:int) (v:cm_value)
             (st:cm_src_state) (ks:(cm_frame)list)) target ann =
        (p == rootp &&
         cm_running_target_sim rootp fid st [v] ann target)) &&
     (!rootp p fid ctl st ks ann target.
        cm_task_target_sim rootp
          (CMCTask (p:cm_program) (fid:int) (ctl:cm_control)
             (st:cm_src_state) (ks:(cm_frame)list)) target ann =
        (p == rootp &&
        (if cm_control_kind ctl == 4i
         then cm_halted_target_sim rootp fid st
                (cm_control_status ctl) T ann target
         else cm_running_target_sim rootp fid st
                (if cm_control_kind ctl == 3i
                 then [cm_control_value ctl] else []) ann target))) &&
     (!rootp st ctl status ann target.
        cm_task_target_sim (rootp:cm_program)
          (CMDoneTask (st:cm_src_state) (ctl:cm_control)
             (status:int)) target ann =
        cm_halted_target_sim rootp (--1i) st status F ann target)`);

PROOF thm cm_astate_sim_def = new_fun_definition(
    `cm_astate_sim (p:cm_program) (ast:cm_astate) : bool =
       cm_task_target_sim p (cm_astate_task ast)
         (cm_astate_target ast) (cm_astate_annotation ast)`);

PROOF thm cm_task_succeeds_def = new_fun_definition(
    `cm_task_succeeds (task:cm_task) : bool =
       (?st ctl status.
          cm_exec task
            (CMOutcome (st:cm_src_state) (ctl:cm_control) (status:int)) &&
          cm_success_control ctl)`);

PROOF static thm cm_prove_done_target_observation(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state) (ctl:cm_control)
         (status:int) (target:tvm_task) (ann:cm_annotation).
         cm_task_target_sim p (CMDoneTask st ctl status) target ann ==>
         ?vm.
           target == TVMDoneTask (vm:tvm_state) status 0i &&
           tvm_output vm == cm_state_output st`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm sim = assume_rule(goal_lasmps(leaf->g)[0].tm);
  thm expanded = eq_mp_rule(apply_conversion(
      rewrite_conv(THM_LIST(
        cm_task_target_sim_def, cm_halted_target_sim_def)),
      concl(sim)), sim);
  thm body = assume_rule(
      `(target:tvm_task) ==
         TVMDoneTask (vm:tvm_state) (status:int) 0i &&
       tvm_pc vm == cm_ann_pc (ann:cm_annotation) &&
       cm_machine_state_sim (p:cm_program) (st:cm_src_state) vm
         (cm_ann_calls ann) (cm_ann_saved ann) [] []`);
  thm machine = conjunct2_rule(conjunct2_rule(body));
  thm io = specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_ann_saved (ann:cm_annotation)`,
      `[]:(cm_value)list`, `[]:(int)list`), cm_machine_sim_io);
  thm output = conjunct2_rule(mp_rule(io, machine));
  thm witness = exists_rule(
      `?vm.
         (target:tvm_task) ==
           TVMDoneTask (vm:tvm_state) (status:int) 0i &&
         tvm_output vm == cm_state_output (st:cm_src_state)`,
      `vm:tvm_state`,
      conj_rule(conjunct1_rule(body), output));
  thm result = choose_rule(`vm:tvm_state`, expanded, witness);
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_done_target_observation =
    cm_prove_done_target_observation();

PROOF int _e_cm_task_target_sim =
    cst_add_const_to_header(`cm_task_target_sim`);
PROOF int _e_cm_astate_sim = cst_add_const_to_header(`cm_astate_sim`);
PROOF int _e_cm_task_succeeds =
    cst_add_const_to_header(`cm_task_succeeds`);

PROOF thm get_cm_task_target_sim_def(void) {
  return cm_task_target_sim_def;
}
PROOF thm get_cm_astate_sim_def(void) { return cm_astate_sim_def; }
PROOF thm get_cm_task_succeeds_def(void) {
  return cm_task_succeeds_def;
}
PROOF thm get_cm_done_target_observation(void) {
  return cm_done_target_observation;
}

PROOF static int cmc_preservation_state_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_state_axioms_before,
      "cmc_preservation_state introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_state_checks =
    cmc_preservation_state_final_checks();
