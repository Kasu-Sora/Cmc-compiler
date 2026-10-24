#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_target_call_jump.h"
#include "cmc_preservation_machine.h"

#require "cmc_preservation_target_machine.c"

PROOF static size_t _cmc_preservation_target_call_jump_axioms_before =
    vector_size(get_all_axioms());

PROOF thm cm_ann_call_jump_def = new_fun_definition(
    `cm_ann_call_jump (jump_pc:int) (saved_fp:int) (return_pc:int)
       (ann:cm_annotation) : cm_annotation =
       CMAnnotation jump_pc (cm_ann_temp ann) (cm_ann_break ann)
         (cm_ann_continue ann) (cm_ann_cursors ann)
         (cm_ann_spills ann) (cm_ann_saved ann)
         (CMCallSimFrame 8i saved_fp return_pc :: cm_ann_calls ann)`);

PROOF static thm cm_prove_call_frames_sim_length(void) {
  gnode root = gnode_new_with_ccl(
      `!(frames:(cm_call_sim_frame)list).
         !(mem:int->int) (calls:(int)list).
           cm_call_frames_sim mem frames calls ==>
           ilength calls == ilength frames`);
  gnode_list cases = INDUCT_TAC(root, `frames:(cm_call_sim_frame)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm calls_nil = conv_rule(
        rewrite_conv(THM_LIST(cm_call_frames_sim_def)),
        assume_rule(
          `cm_call_frames_sim (mem:int->int)
             ([]:(cm_call_sim_frame)list) (calls:(int)list)`));
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        calls_nil, get_theorem_by_name("ILENGTH_DEF"))));
  }
  {
    gnode branch = AUTO_INTROS_TAC(cases[1]);
    gnode_list call_cases = DISJ_CASES_TAC(
        branch,
        ispec_rule(`calls:(int)list`,
          get_theorem_by_name("list_CASES")),
        "Hcalls");
    {
      thm calls_nil = assume_rule(
          goal_lasmps(call_cases[0]->g)[
            labeled_term_list_index(
              goal_lasmps(call_cases[0]->g), "Hcalls")].tm);
      thm impossible = conv_rule(
          reduce_rewrite_conv(THM_LIST(
            calls_nil, cm_call_frames_sim_def)),
          assume_rule(
            `cm_call_frames_sim (mem:int->int)
               ((a0:cm_call_sim_frame) ::
                 (a1:(cm_call_sim_frame)list))
               (calls:(int)list)`));
      CONTR_TAC(call_cases[0], impossible);
    }
    {
      gnode call_cons = ASMP_EXISTS_TAC(
          call_cases[1], "Hcalls", NULL);
      call_cons = ASMP_EXISTS_TAC(call_cons, "Hcalls", NULL);
      thm calls_cons = assume_rule(
          goal_lasmps(call_cons->g)[
            labeled_term_list_index(
              goal_lasmps(call_cons->g), "Hcalls")].tm);
      thm simulation = conv_rule(
          reduce_rewrite_conv(THM_LIST(
            calls_cons, cm_call_frames_sim_def,
            get_theorem_by_name("HD"), get_theorem_by_name("TL"))),
          assume_rule(
            `cm_call_frames_sim (mem:int->int)
               ((a0:cm_call_sim_frame) ::
                 (a1:(cm_call_sim_frame)list))
               (calls:(int)list)`));
      thm tail_sim = conjunct2_rule(conjunct2_rule(
          conjunct2_rule(simulation)));
      thm tail_length = mp_rule(
          specl_rule(TERM_LIST(`mem:int->int`,
            `t:(int)list`),
            assume_rule(goal_lasmps(call_cons->g)[0].tm)),
          tail_sim);
      CONV_TAC(call_cons, reduce_rewrite_conv(THM_LIST(
          calls_cons, tail_length,
          get_theorem_by_name("ILENGTH_DEF"))));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_call_frames_sim_length =
    cm_prove_call_frames_sim_length();

PROOF static thm cm_prove_machine_call_jump(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state) (target:tvm_state)
         (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         (values:(cm_value)list) (suffix:(int)list)
         (jump_pc:int) (return_pc:int).
         cm_machine_state_sim p st target frames spill_frames
           values suffix ==>
         cm_machine_state_sim p st
           (tvm_jump_state target jump_pc (tvm_stack target)
             (return_pc :: tvm_calls target) (tvm_mem target)
             (tvm_input target) (tvm_output target))
           (CMCallSimFrame 8i (cm_state_fp st) return_pc :: frames)
           spill_frames values suffix`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm simulation = conv_rule(rewrite_conv(THM_LIST(
      cm_machine_sim_parts)), assume_rule(
        `cm_machine_state_sim (p:cm_program) (st:cm_src_state)
           (target:tvm_state) (frames:(cm_call_sim_frame)list)
           (spill_frames:(cm_spill_frame)list)
           (values:(cm_value)list) (suffix:(int)list)`));
  thm initialized = conjunct1_rule(simulation);
  thm after_initialized = conjunct2_rule(simulation);
  thm provenance = conjunct1_rule(after_initialized);
  thm after_provenance = conjunct2_rule(after_initialized);
  thm fp_word = conjunct1_rule(after_provenance);
  thm after_fp = conjunct2_rule(after_provenance);
  thm calls = conjunct1_rule(after_fp);
  thm after_calls = conjunct2_rule(after_fp);
  thm spills = conjunct1_rule(after_calls);
  thm after_spills = conjunct2_rule(after_calls);
  thm input_equal = conjunct1_rule(after_spills);
  thm after_input = conjunct2_rule(after_spills);
  thm output_equal = conjunct1_rule(after_input);
  thm operand = conjunct2_rule(after_input);
  thm new_calls = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_call_frames_sim_def, cm_call_sim_base_def,
        cm_call_sim_saved_def, cm_call_sim_return_def,
        get_theorem_by_name("HD"), get_theorem_by_name("TL"),
        get_theorem_by_name("NOT_CONS_NIL"), fp_word, calls)),
      `cm_call_frames_sim (tvm_mem (target:tvm_state))
         (CMCallSimFrame 8i (cm_state_fp (st:cm_src_state))
            (return_pc:int) :: (frames:(cm_call_sim_frame)list))
         (return_pc :: tvm_calls target)`));
  thm result = conj_rule(initialized,
      conj_rule(provenance,
      conj_rule(fp_word,
      conj_rule(new_calls,
      conj_rule(spills,
      conj_rule(input_equal,
      conj_rule(output_equal, operand)))))));
  thm_list rules = THM_LIST(
      cm_machine_sim_parts, get_tvm_jump_state_def(),
      get_tvm_state_selectors_def());
  gnode opened = CONV_TAC(leaf, reduce_rewrite_conv(rules));
  ACCEPT_TAC(opened, conv_rule(reduce_rewrite_conv(rules), result));
  return gnode_prove(root);
}
PROOF thm cm_machine_call_jump = cm_prove_machine_call_jump();

PROOF static thm cm_prove_target_call_jump(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (values:(cm_value)list) (ann:cm_annotation)
         (target:tvm_task) (jump_pc:int)
         (rest:(tvm_inst)list).
         cm_code_at (cm_model_code p) (cm_ann_pc ann)
           (TVMInst TVMCallOp jump_pc :: rest) ==>
         tvm_target_valid (cm_model_code p) jump_pc ==>
         ilength (cm_ann_calls ann) < 65536i ==>
         cm_running_target_sim p fid st values ann target ==>
         cm_running_target_sim p fid st values
           (cm_ann_call_jump jump_pc (cm_state_fp st)
             (cm_ann_pc ann + 1i) ann)
           (tvm_iter 1 target)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm code_at = assume_rule(
      `cm_code_at (cm_model_code (p:cm_program))
         (cm_ann_pc (ann:cm_annotation))
         (TVMInst TVMCallOp (jump_pc:int) ::
           (rest:(tvm_inst)list))`);
  thm valid = assume_rule(
      `tvm_target_valid (cm_model_code (p:cm_program))
         (jump_pc:int)`);
  thm running = assume_rule(
      `cm_running_target_sim (p:cm_program) (fid:int)
         (st:cm_src_state) (values:(cm_value)list)
         (ann:cm_annotation) (target:tvm_task)`);
  thm expanded = eq_mp_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_running_target_sim_def)),
      concl(running)), running);
  thm body = assume_rule(
      `(target:tvm_task) ==
           TVMRunTask (cm_compile_model (p:cm_program)) (vm:tvm_state) &&
       tvm_pc vm == cm_ann_pc (ann:cm_annotation) &&
       cm_machine_state_sim p (st:cm_src_state) vm
         (cm_ann_calls ann)
         (cm_active_spill_frames (fid:int) st ann)
         (values:(cm_value)list) []`);
  thm target_equal = conjunct1_rule(body);
  thm pc_equal = conjunct1_rule(conjunct2_rule(body));
  thm machine = conjunct2_rule(conjunct2_rule(body));
  thm machine_parts = conv_rule(rewrite_conv(THM_LIST(
      cm_machine_sim_parts)), machine);
  thm call_sim = conjunct1_rule(conjunct2_rule(conjunct2_rule(
      conjunct2_rule(machine_parts))));
  thm call_length = mp_rule(specl_rule(TERM_LIST(
      `cm_ann_calls (ann:cm_annotation)`,
      `tvm_mem (vm:tvm_state)`, `tvm_calls (vm:tvm_state)`),
      cm_call_frames_sim_length), call_sim);
  thm call_bound = mp_rule(int_arith_rule(
      `ilength (tvm_calls (vm:tvm_state)) ==
         ilength (cm_ann_calls (ann:cm_annotation)) ==>
       ilength (cm_ann_calls ann) < 65536i ==>
       ilength (tvm_calls vm) < 65536i`), call_length);
  call_bound = match_mp_rule(call_bound, assume_rule(
      `ilength (cm_ann_calls (ann:cm_annotation)) < 65536i`));
  thm valid_object = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_compile_model_def(), get_tvm_object_code_def(), valid)),
      `tvm_target_valid
         (tvm_object_code (cm_compile_model (p:cm_program)))
         (jump_pc:int)`));
  term next =
      `tvm_jump_state (vm:tvm_state) (jump_pc:int)
         (tvm_stack vm) ((tvm_pc vm + 1i) :: tvm_calls vm)
         (tvm_mem vm) (tvm_input vm) (tvm_output vm)`;
  thm action = specl_rule(TERM_LIST(
      `tvm_object_code (cm_compile_model (p:cm_program))`,
      `jump_pc:int`, `vm:tvm_state`), get_tvm_call_transition());
  action = conv_rule(reduce_rewrite_conv(THM_LIST(
      valid_object, call_bound)), action);
  thm compiled_code = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_compile_model_def(), get_tvm_object_code_def(),
        pc_equal, code_at)),
      `cm_code_at
         (tvm_object_code (cm_compile_model (p:cm_program)))
         (tvm_pc (vm:tvm_state))
         (TVMInst TVMCallOp (jump_pc:int) ::
           (rest:(tvm_inst)list))`));
  thm stepped = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `cm_compile_model (p:cm_program)`, `vm:tvm_state`,
      `TVMCallOp:tvm_opcode`, `jump_pc:int`,
      `rest:(tvm_inst)list`, next), cm_tvm_state_iter_one),
      compiled_code), action);
  stepped = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(target_equal))), stepped);
  thm machine_after = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `values:(cm_value)list`, `[]:(int)list`,
      `jump_pc:int`, `tvm_pc (vm:tvm_state) + 1i`),
      cm_machine_call_jump), machine);
  thm return_equal = beta_norm(ap_term_rule(
      `\x:int. x + 1i`, pc_equal));
  thm frame_equal = beta_norm(ap_term_rule(
      `\x:int.
         CMCallSimFrame 8i (cm_state_fp (st:cm_src_state)) x`,
      return_equal));
  machine_after = conv_rule(
      once_rewrite_conv(THM_LIST(frame_equal)), machine_after);
  term updated =
      `cm_ann_call_jump (jump_pc:int) (cm_state_fp (st:cm_src_state))
         (cm_ann_pc (ann:cm_annotation) + 1i) ann`;
  thm next_pc = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_tvm_jump_state_def(), get_tvm_state_selectors_def(),
        cm_ann_call_jump_def, cm_ann_pc_def)),
      `tvm_pc ${next:tvm_state} ==
       cm_ann_pc ${updated:cm_annotation}`));
  thm normalized_body =
      conj_rule(stepped, conj_rule(next_pc, machine_after));
  thm_list update_rules = THM_LIST(
      cm_ann_call_jump_def, cm_ann_pc_def, cm_ann_calls_def,
      cm_ann_spills_def, cm_ann_saved_def,
      cm_active_spill_frames_def);
  normalized_body = conv_rule(
      reduce_rewrite_conv(update_rules), normalized_body);
  term exists_goal =
      `?next_vm.
         tvm_iter 1 (target:tvm_task) ==
           TVMRunTask (cm_compile_model (p:cm_program)) next_vm &&
         tvm_pc next_vm == cm_ann_pc ${updated:cm_annotation} &&
         cm_machine_state_sim p (st:cm_src_state) next_vm
           (cm_ann_calls ${updated:cm_annotation})
           (cm_active_spill_frames (fid:int) st
             ${updated:cm_annotation})
           (values:(cm_value)list) []`;
  dest_exists_results exists_parts = dest_exists(exists_goal);
  term instantiated_body = subst_one(next, exists_parts.v,
      exists_parts.tm);
  thm body_reduction = apply_conversion(
      reduce_rewrite_conv(update_rules), instantiated_body);
  thm adjusted_body = eq_mp_rule(
      sym_rule(body_reduction), normalized_body);
  thm witness = exists_rule(exists_goal, next, adjusted_body);
  thm selected = choose_rule(`vm:tvm_state`, expanded, witness);
  gnode opened = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(cm_running_target_sim_def)));
  ACCEPT_TAC(opened, selected);
  return gnode_prove(root);
}
PROOF thm cm_target_call_jump = cm_prove_target_call_jump();

PROOF thm get_cm_ann_call_jump_def(void) {
  return cm_ann_call_jump_def;
}
PROOF thm get_cm_call_frames_sim_length(void) {
  return cm_call_frames_sim_length;
}
PROOF thm get_cm_machine_call_jump(void) {
  return cm_machine_call_jump;
}
PROOF thm get_cm_target_call_jump(void) {
  return cm_target_call_jump;
}

PROOF static int cmc_preservation_target_call_jump_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_call_jump_axioms_before,
      "cmc_preservation_target_call_jump introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_call_jump_checks =
    cmc_preservation_target_call_jump_final_checks();
