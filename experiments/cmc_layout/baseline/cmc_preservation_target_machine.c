#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_runtime.h"
#include "cmc_preservation_machine_io.h"
#include "cmc_preservation_tvm.h"
#include "cmc_preservation_target_machine.h"

#require "cmc_preservation_runtime.c"
#require "cmc_preservation_machine_io.c"
#require "cmc_preservation_tvm.c"

PROOF static size_t _cmc_preservation_target_machine_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_target_reannotate(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (values:(cm_value)list) (ann:cm_annotation)
         (ann2:cm_annotation) (target:tvm_task).
         cm_ann_pc ann2 == cm_ann_pc ann ==>
         cm_ann_calls ann2 == cm_ann_calls ann ==>
         cm_ann_spills ann2 == cm_ann_spills ann ==>
         cm_ann_saved ann2 == cm_ann_saved ann ==>
         cm_running_target_sim p fid st values ann target ==>
         cm_running_target_sim p fid st values ann2 target`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm running = assume_rule(
      `cm_running_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state) (values:(cm_value)list)
        (ann:cm_annotation) (target:tvm_task)`);
  thm expanded = conv_rule(rewrite_conv(THM_LIST(
      cm_running_target_sim_def, cm_active_spill_frames_def)), running);
  gnode opened = CONV_WITH_ASMP_TAC(
      leaf, rewrite_conv, THM_LIST(
        cm_running_target_sim_def, cm_active_spill_frames_def));
  ACCEPT_TAC(opened, expanded);
  return gnode_prove(root);
}
PROOF thm cm_target_reannotate = cm_prove_target_reannotate();

PROOF static thm cm_prove_target_halted_reannotate(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (status:int) (active:bool) (ann:cm_annotation)
         (ann2:cm_annotation) (target:tvm_task).
         cm_ann_pc ann2 == cm_ann_pc ann ==>
         cm_ann_calls ann2 == cm_ann_calls ann ==>
         cm_ann_spills ann2 == cm_ann_spills ann ==>
         cm_ann_saved ann2 == cm_ann_saved ann ==>
         cm_halted_target_sim p fid st status active ann target ==>
         cm_halted_target_sim p fid st status active ann2 target`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm halted = assume_rule(
      `cm_halted_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state) (status:int) (active:bool)
        (ann:cm_annotation) (target:tvm_task)`);
  thm expanded = conv_rule(rewrite_conv(THM_LIST(
      cm_halted_target_sim_def, cm_active_spill_frames_def)), halted);
  gnode opened = CONV_WITH_ASMP_TAC(
      leaf, rewrite_conv, THM_LIST(
        cm_halted_target_sim_def, cm_active_spill_frames_def));
  ACCEPT_TAC(opened, expanded);
  return gnode_prove(root);
}
PROOF thm cm_target_halted_reannotate =
    cm_prove_target_halted_reannotate();

PROOF static thm cm_prove_machine_drop_spill_frame(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state) (target:tvm_state)
         (frames:(cm_call_sim_frame)list)
         (current:cm_spill_frame) (saved:(cm_spill_frame)list)
         (values:(cm_value)list) (suffix:(int)list).
         cm_machine_state_sim p st target frames (current :: saved)
           values suffix ==>
         cm_machine_state_sim p st target frames saved values suffix`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm old_sim = assume_rule(
      `cm_machine_state_sim (p:cm_program) (st:cm_src_state)
        (target:tvm_state) (frames:(cm_call_sim_frame)list)
        ((current:cm_spill_frame) :: (saved:(cm_spill_frame)list))
        (values:(cm_value)list) (suffix:(int)list)`);
  thm parts = eq_mp_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_machine_state_sim_def)),
      concl(old_sim)), old_sim);
  thm initialized = conjunct1_rule(parts);
  parts = conjunct2_rule(parts);
  thm provenance = conjunct1_rule(parts);
  parts = conjunct2_rule(parts);
  thm frame_pointer = conjunct1_rule(parts);
  parts = conjunct2_rule(parts);
  thm calls = conjunct1_rule(parts);
  parts = conjunct2_rule(parts);
  thm spills = conjunct1_rule(parts);
  parts = conjunct2_rule(parts);
  thm input = conjunct1_rule(parts);
  parts = conjunct2_rule(parts);
  thm output = conjunct1_rule(parts);
  thm operands = conjunct2_rule(parts);
  thm saved_spills = conjunct2_rule(conv_rule(
      rewrite_conv(THM_LIST(cm_spill_frames_sim_def)), spills));
  thm rebuilt = conj_rule(initialized, conj_rule(provenance,
      conj_rule(frame_pointer, conj_rule(calls,
        conj_rule(saved_spills, conj_rule(input,
          conj_rule(output, operands)))))));
  thm target_view = apply_conversion(
      rewrite_conv(THM_LIST(cm_machine_state_sim_def)),
      goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), rebuilt));
  return gnode_prove(root);
}
PROOF static thm cm_machine_drop_spill_frame =
    cm_prove_machine_drop_spill_frame();

PROOF static thm cm_prove_target_halted_deactivate(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (status:int) (ann:cm_annotation) (target:tvm_task).
         cm_halted_target_sim p fid st status T ann target ==>
         cm_halted_target_sim p fid st status F ann target`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm halted = assume_rule(
      `cm_halted_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state) (status:int) T
        (ann:cm_annotation) (target:tvm_task)`);
  conv expand = reduce_rewrite_conv(THM_LIST(
      cm_halted_target_sim_def, cm_active_spill_frames_def));
  thm expanded = eq_mp_rule(
      apply_conversion(expand, concl(halted)), halted);
  thm body = assume_rule(
      `(target:tvm_task) ==
          TVMDoneTask (vm:tvm_state) (status:int) 0i &&
       tvm_pc vm == cm_ann_pc (ann:cm_annotation) &&
       cm_machine_state_sim p st vm (cm_ann_calls ann)
         (CMSpillFrame (fid:int) (cm_state_fp st)
            (cm_ann_spills ann) ::
          cm_ann_saved ann)
         [] []`);
  thm reduced_machine = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `CMSpillFrame (fid:int) (cm_state_fp st) (cm_ann_spills ann)`,
      `cm_ann_saved (ann:cm_annotation)`,
      `[]:(cm_value)list`, `[]:(int)list`),
      cm_machine_drop_spill_frame),
      conjunct2_rule(conjunct2_rule(body)));
  term exists_goal =
      `?next_vm.
         (target:tvm_task) ==
           TVMDoneTask (next_vm:tvm_state) (status:int) 0i &&
         tvm_pc next_vm == cm_ann_pc (ann:cm_annotation) &&
         cm_machine_state_sim p st next_vm (cm_ann_calls ann)
           (cm_ann_saved ann) [] []`;
  thm witness = exists_rule(exists_goal, `vm:tvm_state`,
      conj_rule(conjunct1_rule(body),
        conj_rule(conjunct1_rule(conjunct2_rule(body)),
          reduced_machine)));
  thm selected = choose_rule(`vm:tvm_state`, expanded, witness);
  gnode opened = CONV_TAC(leaf, expand);
  selected = conv_rule(expand, selected);
  ACCEPT_TAC(opened, selected);
  return gnode_prove(root);
}
PROOF thm cm_target_halted_deactivate =
    cm_prove_target_halted_deactivate();

PROOF static thm cm_prove_target_push(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (values:(cm_value)list) (ann:cm_annotation)
         (target:tvm_task) (v:cm_value) (imm:int)
         (rest:(tvm_inst)list).
         cm_code_at (cm_model_code p) (cm_ann_pc ann)
           (TVMInst TVMPushOp imm :: rest) ==>
         cm_running_target_sim p fid st values ann target ==>
         ilength values < 65536i ==>
         tower_wrap64 imm == cm_value_number st v ==>
         cm_running_target_sim p fid st (v :: values)
           (cm_ann_linear (cm_push_code imm) ann)
           (tvm_iter 1 target)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm code_at = assume_rule(
      `cm_code_at (cm_model_code (p:cm_program))
        (cm_ann_pc (ann:cm_annotation))
        (TVMInst TVMPushOp (imm:int) :: (rest:(tvm_inst)list))`);
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

  thm stack_length = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `values:(cm_value)list`, `[]:(int)list`),
      get_cm_machine_sim_stack_length()), machine);
  thm stack_room = mp_rule(int_arith_rule(
      `ilength (tvm_stack (vm:tvm_state)) ==
         ilength (values:(cm_value)list) + 0i ==>
       ilength values < 65536i ==>
       ilength (tvm_stack vm) < 65536i`),
      conv_rule(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))), stack_length));
  stack_room = match_mp_rule(stack_room,
      assume_rule(`ilength (values:(cm_value)list) < 65536i`));

  term next =
      `tvm_next_state (vm:tvm_state)
        (tower_wrap64 (imm:int) :: tvm_stack vm)
        (tvm_calls vm) (tvm_mem vm) (tvm_input vm) (tvm_output vm)`;
  thm action = specl_rule(TERM_LIST(
      `tvm_object_code (cm_compile_model (p:cm_program))`,
      `imm:int`, `vm:tvm_state`),
      get_tvm_push_transition());
  action = conv_rule(reduce_rewrite_conv(THM_LIST(stack_room)), action);
  thm compiled_code = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_compile_model_def(), get_tvm_object_code_def(),
        pc_equal, code_at)),
      `cm_code_at
        (tvm_object_code (cm_compile_model (p:cm_program)))
        (tvm_pc (vm:tvm_state))
        (TVMInst TVMPushOp (imm:int) :: (rest:(tvm_inst)list))`));
  thm stepped = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `cm_compile_model (p:cm_program)`, `vm:tvm_state`,
      `TVMPushOp:tvm_opcode`, `imm:int`, `rest:(tvm_inst)list`, next),
      cm_tvm_state_iter_one), compiled_code), action);
  stepped = conv_rule(rewrite_conv(THM_LIST(sym_rule(target_equal))),
      stepped);

  thm machine_after = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `values:(cm_value)list`, `[]:(int)list`, `v:cm_value`,
      `imm:int`), get_cm_machine_push()), machine),
      assume_rule(
        `tower_wrap64 (imm:int) ==
         cm_value_number (st:cm_src_state) (v:cm_value)`));
  thm next_pc = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_tvm_next_state_def(), get_tvm_state_selectors_def(),
        cm_ann_linear_def, cm_ann_plain_def, cm_ann_pc_def,
        get_cm_push_code_def(), get_theorem_by_name("ILENGTH_DEF"),
        pc_equal)),
      `tvm_pc ${next:tvm_state} ==
       cm_ann_pc
         (cm_ann_linear (cm_push_code (imm:int))
           (ann:cm_annotation))`));
  thm normalized_body = conj_rule(stepped,
      conj_rule(next_pc, machine_after));
  thm_list update_rules = THM_LIST(
      cm_ann_linear_def, cm_ann_plain_def,
      cm_ann_pc_def, cm_ann_calls_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_active_spill_frames_def,
      get_cm_push_code_def(), get_theorem_by_name("ILENGTH_DEF"));
  normalized_body =
      conv_rule(reduce_rewrite_conv(update_rules), normalized_body);
  term updated =
      `cm_ann_linear (cm_push_code (imm:int)) (ann:cm_annotation)`;
  term exists_goal =
      `?next_vm.
         tvm_iter 1 (target:tvm_task) ==
           TVMRunTask (cm_compile_model (p:cm_program)) next_vm &&
         tvm_pc next_vm == cm_ann_pc ${updated:cm_annotation} &&
         cm_machine_state_sim p (st:cm_src_state) next_vm
           (cm_ann_calls ${updated:cm_annotation})
           (cm_active_spill_frames (fid:int) st ${updated:cm_annotation})
           ((v:cm_value) :: (values:(cm_value)list)) []`;
  dest_exists_results exists_parts = dest_exists(exists_goal);
  term instantiated_body =
      subst_one(next, exists_parts.v, exists_parts.tm);
  thm body_reduction = apply_conversion(
      reduce_rewrite_conv(update_rules), instantiated_body);
  thm adjusted_body = eq_mp_rule(sym_rule(body_reduction),
      normalized_body);
  thm witness = exists_rule(exists_goal, next, adjusted_body);
  thm selected = choose_rule(`vm:tvm_state`, expanded, witness);
  gnode opened = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(cm_running_target_sim_def)));
  ACCEPT_TAC(opened, selected);
  return gnode_prove(root);
}
PROOF thm cm_target_push = cm_prove_target_push();

PROOF static thm cm_prove_valid_input_head(void) {
  gnode root = gnode_new_with_ccl(
      `!(input:(int)list).
         cm_valid_input input ==>
         ~(input == []) ==>
         tower_byte_value (HD input)`);
  gnode with_input = GEN_TAC(root, "input");
  gnode_list cases =
      CASES_TAC(with_input, `input:(int)list`, "Hinput");
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm shape = assume_rule(
        goal_lasmps(leaf->g)[labeled_term_list_index(
          goal_lasmps(leaf->g), "Hinput")].tm);
    thm impossible = conv_rule(
        reduce_rewrite_conv(THM_LIST(shape)),
        assume_rule(`~((input:(int)list) == [])`));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm shape = assume_rule(
        goal_lasmps(leaf->g)[labeled_term_list_index(
          goal_lasmps(leaf->g), "Hinput")].tm);
    thm valid = conv_rule(reduce_rewrite_conv(THM_LIST(
        shape, get_cm_valid_input_def(),
        get_theorem_by_name("ALL"))),
        assume_rule(`cm_valid_input (input:(int)list)`));
    gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        shape, get_theorem_by_name("HD"))));
    ACCEPT_TAC(reduced, conjunct1_rule(valid));
  }
  return gnode_prove(root);
}
PROOF static thm cm_valid_input_head =
    cm_prove_valid_input_head();

PROOF static thm cm_prove_target_getc(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (values:(cm_value)list) (ann:cm_annotation)
         (target:tvm_task) (rest:(tvm_inst)list).
         cm_code_at (cm_model_code p) (cm_ann_pc ann)
           (TVMInst TVMGetcOp 0i :: rest) ==>
         cm_running_target_sim p fid st values ann target ==>
         ilength values < 65536i ==>
         (cm_state_input st == [] ||
          tower_byte_value (HD (cm_state_input st))) ==>
         cm_running_target_sim p fid
           (if cm_state_input st == [] then st
            else cm_state_io st (TL (cm_state_input st))
                   (cm_state_output st))
           (CMIntV
              (if cm_state_input st == [] then --1i
               else HD (cm_state_input st)) :: values)
           (cm_ann_linear [TVMInst TVMGetcOp 0i] ann)
           (tvm_iter 1 target)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm code_at = assume_rule(
      `cm_code_at (cm_model_code (p:cm_program))
        (cm_ann_pc (ann:cm_annotation))
        (TVMInst TVMGetcOp 0i :: (rest:(tvm_inst)list))`);
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
  thm stack_length = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `values:(cm_value)list`, `[]:(int)list`),
      get_cm_machine_sim_stack_length()), machine);
  thm stack_room = mp_rule(int_arith_rule(
      `ilength (tvm_stack (vm:tvm_state)) ==
         ilength (values:(cm_value)list) + 0i ==>
       ilength values < 65536i ==>
       ilength (tvm_stack vm) < 65536i`),
      conv_rule(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))), stack_length));
  stack_room = match_mp_rule(stack_room,
      assume_rule(`ilength (values:(cm_value)list) < 65536i`));
  thm io = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `values:(cm_value)list`, `[]:(int)list`),
      cm_machine_sim_io), machine);

  gnode_list cases = BOOL_CASES_TAC(
      leaf, `cm_state_input (st:cm_src_state) == []`, "Hempty");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    bool empty = i == 0;
    thm input_case = assume_rule(empty
        ? `cm_state_input (st:cm_src_state) == []`
        : `~(cm_state_input (st:cm_src_state) == [])`);
    term next = empty
        ? `tvm_next_state (vm:tvm_state)
            ((--1i) :: tvm_stack vm) (tvm_calls vm) (tvm_mem vm)
            ([]:(int)list) (tvm_output vm)`
        : `tvm_next_state (vm:tvm_state)
            (tower_u8
               (HD (cm_state_input (st:cm_src_state))) ::
             tvm_stack vm)
            (tvm_calls vm) (tvm_mem vm)
            (TL (cm_state_input st)) (tvm_output vm)`;
    term next_state = empty
        ? `st:cm_src_state`
        : `cm_state_io (st:cm_src_state)
            (TL (cm_state_input st)) (cm_state_output st)`;
    term next_value = empty
        ? `CMIntV (--1i)`
        : `CMIntV (HD (cm_state_input (st:cm_src_state)))`;
    thm action = specl_rule(TERM_LIST(
        `tvm_object_code (cm_compile_model (p:cm_program))`,
        `0i:int`, `vm:tvm_state`), get_tvm_getc_transition());
    action = conv_rule(reduce_rewrite_conv(THM_LIST(
        stack_room, conjunct1_rule(io), input_case)), action);
    thm compiled_code = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_compile_model_def(), get_tvm_object_code_def(),
          pc_equal, code_at)),
        `cm_code_at
          (tvm_object_code (cm_compile_model (p:cm_program)))
          (tvm_pc (vm:tvm_state))
          (TVMInst TVMGetcOp 0i :: (rest:(tvm_inst)list))`));
    thm stepped = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
        `cm_compile_model (p:cm_program)`, `vm:tvm_state`,
        `TVMGetcOp:tvm_opcode`, `0i:int`,
        `rest:(tvm_inst)list`, next),
        cm_tvm_state_iter_one), compiled_code), action);
    stepped = conv_rule(rewrite_conv(THM_LIST(
        sym_rule(target_equal))), stepped);

    thm machine_after;
    if (empty) {
      machine_after = match_mp_rule(match_mp_rule(
          specl_rule(TERM_LIST(
            `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
            `cm_ann_calls (ann:cm_annotation)`,
            `cm_active_spill_frames (fid:int) st ann`,
            `values:(cm_value)list`, `[]:(int)list`),
            get_cm_machine_getc_empty()),
          machine), input_case);
    } else {
      thm input_ready = assume_rule(
          `cm_state_input (st:cm_src_state) == [] ||
           tower_byte_value
             (HD (cm_state_input (st:cm_src_state)))`);
      thm byte = mp_rule(mp_rule(
          taut_rule(imp_chain(TERM_LIST(
            concl(input_ready),
            `~(cm_state_input (st:cm_src_state) == [])`),
            `tower_byte_value
              (HD (cm_state_input (st:cm_src_state)))`)),
          input_ready), input_case);
      machine_after = match_mp_rule(match_mp_rule(match_mp_rule(
          specl_rule(TERM_LIST(
            `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
            `cm_ann_calls (ann:cm_annotation)`,
            `cm_active_spill_frames (fid:int) st ann`,
            `values:(cm_value)list`, `[]:(int)list`),
            get_cm_machine_getc_nonempty()),
          machine), input_case), byte);
    }
    term updated =
        `cm_ann_linear [TVMInst TVMGetcOp 0i]
          (ann:cm_annotation)`;
    thm next_pc = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_tvm_next_state_def(), get_tvm_state_selectors_def(),
          cm_ann_linear_def, cm_ann_plain_def, cm_ann_pc_def,
          get_theorem_by_name("ILENGTH_DEF"), pc_equal)),
        `tvm_pc ${next:tvm_state} ==
         cm_ann_pc ${updated:cm_annotation}`));
    thm normalized_body = conj_rule(
        stepped, conj_rule(next_pc, machine_after));
    thm_list update_rules = get_cm_state_core_defs();
    vector_add(&update_rules, conjunct1_rule(io));
    vector_add(&update_rules, input_case);
    vector_add(&update_rules, cm_ann_linear_def);
    vector_add(&update_rules, cm_ann_plain_def);
    vector_add(&update_rules, cm_ann_pc_def);
    vector_add(&update_rules, cm_ann_calls_def);
    vector_add(&update_rules, cm_ann_spills_def);
    vector_add(&update_rules, cm_ann_saved_def);
    vector_add(&update_rules, cm_active_spill_frames_def);
    vector_add(&update_rules, get_theorem_by_name("ILENGTH_DEF"));
    normalized_body =
        conv_rule(reduce_rewrite_conv(update_rules), normalized_body);
    term exists_goal =
        `?next_vm.
           tvm_iter 1 (target:tvm_task) ==
             TVMRunTask (cm_compile_model (p:cm_program)) next_vm &&
           tvm_pc next_vm == cm_ann_pc ${updated:cm_annotation} &&
           cm_machine_state_sim p ${next_state:cm_src_state} next_vm
             (cm_ann_calls ${updated:cm_annotation})
             (cm_active_spill_frames
               (fid:int) ${next_state:cm_src_state}
               ${updated:cm_annotation})
             (${next_value:cm_value} :: (values:(cm_value)list)) []`;
    dest_exists_results exists_parts = dest_exists(exists_goal);
    term instantiated_body =
        subst_one(next, exists_parts.v, exists_parts.tm);
    thm body_reduction = apply_conversion(
        reduce_rewrite_conv(update_rules), instantiated_body);
    thm adjusted_body = eq_mp_rule(
        sym_rule(body_reduction), normalized_body);
    thm witness =
        exists_rule(exists_goal, next, adjusted_body);
    thm selected =
        choose_rule(`vm:tvm_state`, expanded, witness);
    gnode opened = CONV_TAC(cases[i],
        reduce_rewrite_conv(THM_LIST(
          cm_running_target_sim_def, input_case)));
    ACCEPT_TAC(opened, selected);
  }
  return gnode_prove(root);
}
PROOF thm cm_target_getc = cm_prove_target_getc();

PROOF static thm cm_prove_target_load(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (ptr:cm_value) (values:(cm_value)list)
         (ann:cm_annotation) (target:tvm_task)
         (ty:cm_type) (rest:(tvm_inst)list).
         cm_code_at (cm_model_code p) (cm_ann_pc ann)
           (TVMInst
             (if ty == CMCharTy then TVMLoadBOp else TVMLoadOp)
             0i :: rest) ==>
         cm_running_target_sim p fid st (ptr :: values) ann target ==>
         cm_runtime_memory_layout p st (cm_ann_calls ann)
           (cm_active_spill_frames fid st ann) ==>
         cm_load_ok ty ptr st ==>
         (ty == CMCharTy || ty == CMIntTy || cm_is_pointer ty) ==>
         cm_live_span st (cm_value_number st ptr)
           (cm_store_width ty) ==>
         cm_running_target_sim p fid st
           (cm_load_value ty ptr st :: values)
           (cm_ann_linear (cm_load_code ty) ann)
           (tvm_iter 1 target)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm code_at = assume_rule(
      `cm_code_at (cm_model_code (p:cm_program))
        (cm_ann_pc (ann:cm_annotation))
        (TVMInst
          (if (ty:cm_type) == CMCharTy
           then TVMLoadBOp else TVMLoadOp)
          0i :: (rest:(tvm_inst)list))`);
  thm running = assume_rule(
      `cm_running_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state)
        ((ptr:cm_value) :: (values:(cm_value)list))
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
         ((ptr:cm_value) :: (values:(cm_value)list)) []`);
  thm target_equal = conjunct1_rule(body);
  thm pc_equal = conjunct1_rule(conjunct2_rule(body));
  thm machine = conjunct2_rule(conjunct2_rule(body));
  thm stack_length = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `(ptr:cm_value) :: (values:(cm_value)list)`,
      `[]:(int)list`), get_cm_machine_sim_stack_length()), machine);
  thm stack_nonempty = mp_rule(int_arith_rule(
      `ilength (tvm_stack (vm:tvm_state)) ==
         (1i + ilength (values:(cm_value)list)) + 0i ==>
       0i <= ilength values ==>
       1i <= ilength (tvm_stack vm)`),
      conv_rule(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))), stack_length));
  stack_nonempty = match_mp_rule(stack_nonempty,
      ispec_rule(`values:(cm_value)list`,
        get_theorem_by_name("ILENGTH_NONNEG")));
  thm stack_head = conjunct1_rule(mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `ptr:cm_value`, `values:(cm_value)list`, `[]:(int)list`),
      get_cm_machine_sim_stack_head()), machine));
  thm width_positive =
      spec_rule(`ty:cm_type`, get_cm_store_width_positive());
  thm address_bounds = match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `st:cm_src_state`,
        `cm_ann_calls (ann:cm_annotation)`,
        `cm_active_spill_frames (fid:int) st ann`,
        `cm_value_number st (ptr:cm_value)`,
        `cm_store_width (ty:cm_type)`),
        get_cm_runtime_live_span_bounds()),
      assume_rule(
        `cm_runtime_memory_layout (p:cm_program) (st:cm_src_state)
          (cm_ann_calls (ann:cm_annotation))
          (cm_active_spill_frames (fid:int) st ann)`)),
      assume_rule(
        `cm_live_span (st:cm_src_state)
          (cm_value_number st (ptr:cm_value))
          (cm_store_width (ty:cm_type))`)),
      width_positive);

  gnode_list cases =
      BOOL_CASES_TAC(leaf, `(ty:cm_type) == CMCharTy`, "Hchar");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    bool is_char = i == 0;
    thm char_case = assume_rule(is_char
        ? `(ty:cm_type) == CMCharTy`
        : `~((ty:cm_type) == CMCharTy)`);
    thm branch_code_at = conv_rule(
        reduce_rewrite_conv(THM_LIST(char_case)), code_at);
    term opcode = is_char
        ? `TVMLoadBOp:tvm_opcode`
        : `TVMLoadOp:tvm_opcode`;
    term loaded = is_char
        ? `tower_getb (tvm_mem (vm:tvm_state))
            (cm_value_number (st:cm_src_state) (ptr:cm_value))`
        : `tower_getw (tvm_mem (vm:tvm_state))
            (cm_value_number (st:cm_src_state) (ptr:cm_value))`;
    term next =
        `tvm_next_state (vm:tvm_state)
          (${loaded:int} :: TL (tvm_stack vm))
          (tvm_calls vm) (tvm_mem vm)
          (tvm_input vm) (tvm_output vm)`;
    term address_valid = is_char
        ? `tower_addr_valid
            (cm_value_number (st:cm_src_state) (ptr:cm_value))`
        : `tower_word_valid
            (cm_value_number (st:cm_src_state) (ptr:cm_value))`;
    thm raw_bounds = conv_rule(reduce_rewrite_conv(THM_LIST(
        char_case, get_cm_store_width_def())), address_bounds);
    term number =
        `cm_value_number (st:cm_src_state) (ptr:cm_value)`;
    thm raw_valid = match_mp_rule(
        is_char
          ? int_arith_rule(
              `0i <= ${number:int} &&
               ${number:int} + 1i <= 1048576i ==>
               0i <= ${number:int} &&
               ${number:int} < 1048576i`)
          : int_arith_rule(
              `0i <= ${number:int} &&
               ${number:int} + 8i <= 1048576i ==>
               0i <= ${number:int} &&
               ${number:int} + 7i < 1048576i`),
        raw_bounds);
    thm valid_expansion = apply_conversion(
        rewrite_conv(THM_LIST(
          is_char
            ? get_tower_addr_valid_def()
            : get_tower_word_valid_def())),
        address_valid);
    thm address_ok =
        eq_mp_rule(sym_rule(valid_expansion), raw_valid);
    thm action = specl_rule(TERM_LIST(
        `tvm_object_code (cm_compile_model (p:cm_program))`,
        `0i:int`, `vm:tvm_state`),
        is_char
          ? get_tvm_loadb_transition()
          : get_tvm_load_transition());
    action = conv_rule(reduce_rewrite_conv(THM_LIST(
        stack_nonempty, stack_head, address_ok)), action);
    thm compiled_code = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_compile_model_def(), get_tvm_object_code_def(),
          pc_equal, branch_code_at)),
        `cm_code_at
          (tvm_object_code (cm_compile_model (p:cm_program)))
          (tvm_pc (vm:tvm_state))
          (TVMInst ${opcode:tvm_opcode} 0i ::
            (rest:(tvm_inst)list))`));
    thm stepped = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
        `cm_compile_model (p:cm_program)`, `vm:tvm_state`,
        opcode, `0i:int`, `rest:(tvm_inst)list`, next),
        cm_tvm_state_iter_one), compiled_code), action);
    stepped = conv_rule(rewrite_conv(THM_LIST(
        sym_rule(target_equal))), stepped);

    thm machine_after = match_mp_rule(match_mp_rule(match_mp_rule(
        match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
          `cm_ann_calls (ann:cm_annotation)`,
          `cm_active_spill_frames (fid:int) st ann`,
          `ptr:cm_value`, `values:(cm_value)list`, `[]:(int)list`,
          `ty:cm_type`), get_cm_machine_load()), machine),
        assume_rule(
          `cm_load_ok (ty:cm_type) (ptr:cm_value)
            (st:cm_src_state)`)),
        assume_rule(
          `(ty:cm_type) == CMCharTy || ty == CMIntTy ||
           cm_is_pointer ty`)),
        assume_rule(
          `cm_live_span (st:cm_src_state)
            (cm_value_number st (ptr:cm_value))
            (cm_store_width (ty:cm_type))`));
    term updated =
        `cm_ann_linear (cm_load_code (ty:cm_type))
          (ann:cm_annotation)`;
    thm next_pc = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_tvm_next_state_def(), get_tvm_state_selectors_def(),
          cm_ann_linear_def, cm_ann_plain_def, cm_ann_pc_def,
          get_cm_load_code_def(), get_theorem_by_name("ILENGTH_DEF"),
          char_case, pc_equal)),
        `tvm_pc ${next:tvm_state} ==
         cm_ann_pc ${updated:cm_annotation}`));
    thm normalized_body =
        conj_rule(stepped, conj_rule(next_pc, machine_after));
    thm_list update_rules = THM_LIST(
        cm_ann_linear_def, cm_ann_plain_def,
        cm_ann_pc_def, cm_ann_calls_def, cm_ann_spills_def,
        cm_ann_saved_def, cm_active_spill_frames_def,
        get_cm_load_code_def(), get_theorem_by_name("ILENGTH_DEF"),
        char_case, stack_head);
    normalized_body =
        conv_rule(reduce_rewrite_conv(update_rules), normalized_body);
    term exists_goal =
        `?next_vm.
           tvm_iter 1 (target:tvm_task) ==
             TVMRunTask (cm_compile_model (p:cm_program)) next_vm &&
           tvm_pc next_vm == cm_ann_pc ${updated:cm_annotation} &&
           cm_machine_state_sim p (st:cm_src_state) next_vm
             (cm_ann_calls ${updated:cm_annotation})
             (cm_active_spill_frames (fid:int) st
               ${updated:cm_annotation})
             (cm_load_value (ty:cm_type) (ptr:cm_value) st ::
               (values:(cm_value)list)) []`;
    dest_exists_results exists_parts = dest_exists(exists_goal);
    term instantiated_body =
        subst_one(next, exists_parts.v, exists_parts.tm);
    thm body_reduction = apply_conversion(
        reduce_rewrite_conv(update_rules), instantiated_body);
    thm adjusted_body = eq_mp_rule(
        sym_rule(body_reduction), normalized_body);
    thm witness =
        exists_rule(exists_goal, next, adjusted_body);
    thm selected =
        choose_rule(`vm:tvm_state`, expanded, witness);
    gnode opened = CONV_TAC(cases[i],
        rewrite_conv(THM_LIST(cm_running_target_sim_def)));
    ACCEPT_TAC(opened, selected);
  }
  return gnode_prove(root);
}
PROOF thm cm_target_load = cm_prove_target_load();

PROOF static thm cm_prove_target_pop(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (v:cm_value) (values:(cm_value)list)
         (ann:cm_annotation) (target:tvm_task)
         (rest:(tvm_inst)list).
         cm_code_at (cm_model_code p) (cm_ann_pc ann)
           (TVMInst TVMPopOp 0i :: rest) ==>
         cm_running_target_sim p fid st (v :: values) ann target ==>
         cm_running_target_sim p fid st values
           (cm_ann_linear [TVMInst TVMPopOp 0i] ann)
           (tvm_iter 1 target)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm code_at = assume_rule(
      `cm_code_at (cm_model_code (p:cm_program))
        (cm_ann_pc (ann:cm_annotation))
        (TVMInst TVMPopOp 0i :: (rest:(tvm_inst)list))`);
  thm running = assume_rule(
      `cm_running_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state)
        ((v:cm_value) :: (values:(cm_value)list))
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
         ((v:cm_value) :: (values:(cm_value)list)) []`);
  thm target_equal = conjunct1_rule(body);
  thm pc_equal = conjunct1_rule(conjunct2_rule(body));
  thm machine = conjunct2_rule(conjunct2_rule(body));
  thm stack_length = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `(v:cm_value) :: (values:(cm_value)list)`,
      `[]:(int)list`), get_cm_machine_sim_stack_length()), machine);
  thm stack_nonempty = mp_rule(int_arith_rule(
      `ilength (tvm_stack (vm:tvm_state)) ==
         (1i + ilength (values:(cm_value)list)) + 0i ==>
       0i <= ilength values ==>
       1i <= ilength (tvm_stack vm)`),
      conv_rule(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))), stack_length));
  stack_nonempty = match_mp_rule(stack_nonempty,
      ispec_rule(`values:(cm_value)list`,
        get_theorem_by_name("ILENGTH_NONNEG")));
  term next =
      `tvm_next_state (vm:tvm_state)
        (TL (tvm_stack vm)) (tvm_calls vm) (tvm_mem vm)
        (tvm_input vm) (tvm_output vm)`;
  thm action = specl_rule(TERM_LIST(
      `tvm_object_code (cm_compile_model (p:cm_program))`,
      `0i:int`, `vm:tvm_state`), get_tvm_pop_transition());
  action = conv_rule(
      reduce_rewrite_conv(THM_LIST(stack_nonempty)), action);
  thm compiled_code = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_compile_model_def(), get_tvm_object_code_def(),
        pc_equal, code_at)),
      `cm_code_at
        (tvm_object_code (cm_compile_model (p:cm_program)))
        (tvm_pc (vm:tvm_state))
        (TVMInst TVMPopOp 0i :: (rest:(tvm_inst)list))`));
  thm stepped = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `cm_compile_model (p:cm_program)`, `vm:tvm_state`,
      `TVMPopOp:tvm_opcode`, `0i:int`, `rest:(tvm_inst)list`, next),
      cm_tvm_state_iter_one), compiled_code), action);
  stepped = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(target_equal))), stepped);
  thm machine_after = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `v:cm_value`, `values:(cm_value)list`, `[]:(int)list`),
      get_cm_machine_pop()), machine);
  term updated =
      `cm_ann_linear [TVMInst TVMPopOp 0i]
        (ann:cm_annotation)`;
  thm next_pc = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_tvm_next_state_def(), get_tvm_state_selectors_def(),
        cm_ann_linear_def, cm_ann_plain_def, cm_ann_pc_def,
        get_theorem_by_name("ILENGTH_DEF"), pc_equal)),
      `tvm_pc ${next:tvm_state} ==
       cm_ann_pc ${updated:cm_annotation}`));
  thm normalized_body =
      conj_rule(stepped, conj_rule(next_pc, machine_after));
  thm_list update_rules = THM_LIST(
      cm_ann_linear_def, cm_ann_plain_def,
      cm_ann_pc_def, cm_ann_calls_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_active_spill_frames_def,
      get_theorem_by_name("ILENGTH_DEF"));
  normalized_body =
      conv_rule(reduce_rewrite_conv(update_rules), normalized_body);
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
  term instantiated_body =
      subst_one(next, exists_parts.v, exists_parts.tm);
  thm body_reduction = apply_conversion(
      reduce_rewrite_conv(update_rules), instantiated_body);
  thm adjusted_body = eq_mp_rule(
      sym_rule(body_reduction), normalized_body);
  thm witness =
      exists_rule(exists_goal, next, adjusted_body);
  thm selected =
      choose_rule(`vm:tvm_state`, expanded, witness);
  gnode opened = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(cm_running_target_sim_def)));
  ACCEPT_TAC(opened, selected);
  return gnode_prove(root);
}
PROOF thm cm_target_pop = cm_prove_target_pop();

PROOF static thm cm_prove_target_dup(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (v:cm_value) (values:(cm_value)list)
         (ann:cm_annotation) (target:tvm_task)
         (rest:(tvm_inst)list).
         cm_code_at (cm_model_code p) (cm_ann_pc ann)
           (TVMInst TVMDupOp 0i :: rest) ==>
         cm_running_target_sim p fid st (v :: values) ann target ==>
         ilength (v :: values) < 65536i ==>
         cm_running_target_sim p fid st (v :: v :: values)
           (cm_ann_linear [TVMInst TVMDupOp 0i] ann)
           (tvm_iter 1 target)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm code_at = assume_rule(
      `cm_code_at (cm_model_code (p:cm_program))
        (cm_ann_pc (ann:cm_annotation))
        (TVMInst TVMDupOp 0i :: (rest:(tvm_inst)list))`);
  thm running = assume_rule(
      `cm_running_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state)
        ((v:cm_value) :: (values:(cm_value)list))
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
         ((v:cm_value) :: (values:(cm_value)list)) []`);
  thm target_equal = conjunct1_rule(body);
  thm pc_equal = conjunct1_rule(conjunct2_rule(body));
  thm machine = conjunct2_rule(conjunct2_rule(body));
  thm stack_length = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `(v:cm_value) :: (values:(cm_value)list)`,
      `[]:(int)list`), get_cm_machine_sim_stack_length()), machine);
  thm stack_nonempty = mp_rule(int_arith_rule(
      `ilength (tvm_stack (vm:tvm_state)) ==
         (1i + ilength (values:(cm_value)list)) + 0i ==>
       0i <= ilength values ==>
       1i <= ilength (tvm_stack vm)`),
      conv_rule(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))), stack_length));
  stack_nonempty = match_mp_rule(stack_nonempty,
      ispec_rule(`values:(cm_value)list`,
        get_theorem_by_name("ILENGTH_NONNEG")));
  thm stack_room = mp_rule(int_arith_rule(
      `ilength (tvm_stack (vm:tvm_state)) ==
         (1i + ilength (values:(cm_value)list)) + 0i ==>
       1i + ilength values < 65536i ==>
       ilength (tvm_stack vm) < 65536i`),
      conv_rule(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))), stack_length));
  stack_room = match_mp_rule(stack_room,
      conv_rule(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))),
        assume_rule(
          `ilength ((v:cm_value) :: (values:(cm_value)list)) <
           65536i`)));
  term next =
      `tvm_next_state (vm:tvm_state)
        (HD (tvm_stack vm) :: tvm_stack vm)
        (tvm_calls vm) (tvm_mem vm)
        (tvm_input vm) (tvm_output vm)`;
  thm action = specl_rule(TERM_LIST(
      `tvm_object_code (cm_compile_model (p:cm_program))`,
      `0i:int`, `vm:tvm_state`), get_tvm_dup_transition());
  action = conv_rule(reduce_rewrite_conv(THM_LIST(
      stack_nonempty, stack_room)), action);
  thm compiled_code = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_compile_model_def(), get_tvm_object_code_def(),
        pc_equal, code_at)),
      `cm_code_at
        (tvm_object_code (cm_compile_model (p:cm_program)))
        (tvm_pc (vm:tvm_state))
        (TVMInst TVMDupOp 0i :: (rest:(tvm_inst)list))`));
  thm stepped = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `cm_compile_model (p:cm_program)`, `vm:tvm_state`,
      `TVMDupOp:tvm_opcode`, `0i:int`,
      `rest:(tvm_inst)list`, next),
      cm_tvm_state_iter_one), compiled_code), action);
  stepped = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(target_equal))), stepped);
  thm machine_after = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `v:cm_value`, `values:(cm_value)list`,
      `[]:(int)list`), get_cm_machine_dup()), machine);
  term updated =
      `cm_ann_linear [TVMInst TVMDupOp 0i]
        (ann:cm_annotation)`;
  thm next_pc = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_tvm_next_state_def(), get_tvm_state_selectors_def(),
        cm_ann_linear_def, cm_ann_plain_def, cm_ann_pc_def,
        get_theorem_by_name("ILENGTH_DEF"), pc_equal)),
      `tvm_pc ${next:tvm_state} ==
       cm_ann_pc ${updated:cm_annotation}`));
  thm normalized_body =
      conj_rule(stepped, conj_rule(next_pc, machine_after));
  thm_list update_rules = THM_LIST(
      cm_ann_linear_def, cm_ann_plain_def,
      cm_ann_pc_def, cm_ann_calls_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_active_spill_frames_def,
      get_theorem_by_name("ILENGTH_DEF"));
  normalized_body =
      conv_rule(reduce_rewrite_conv(update_rules), normalized_body);
  term exists_goal =
      `?next_vm.
         tvm_iter 1 (target:tvm_task) ==
           TVMRunTask (cm_compile_model (p:cm_program)) next_vm &&
         tvm_pc next_vm == cm_ann_pc ${updated:cm_annotation} &&
         cm_machine_state_sim p (st:cm_src_state) next_vm
           (cm_ann_calls ${updated:cm_annotation})
           (cm_active_spill_frames (fid:int) st
             ${updated:cm_annotation})
           ((v:cm_value) :: v :: (values:(cm_value)list)) []`;
  dest_exists_results exists_parts = dest_exists(exists_goal);
  term instantiated_body =
      subst_one(next, exists_parts.v, exists_parts.tm);
  thm body_reduction = apply_conversion(
      reduce_rewrite_conv(update_rules), instantiated_body);
  thm adjusted_body = eq_mp_rule(
      sym_rule(body_reduction), normalized_body);
  thm witness =
      exists_rule(exists_goal, next, adjusted_body);
  thm selected =
      choose_rule(`vm:tvm_state`, expanded, witness);
  gnode opened = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(cm_running_target_sim_def)));
  ACCEPT_TAC(opened, selected);
  return gnode_prove(root);
}
PROOF thm cm_target_dup = cm_prove_target_dup();
PROOF static thm cm_prove_target_swap(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (first:cm_value) (second:cm_value)
         (values:(cm_value)list) (ann:cm_annotation)
         (target:tvm_task) (rest:(tvm_inst)list).
         cm_code_at (cm_model_code p) (cm_ann_pc ann)
           (TVMInst TVMSwapOp 0i :: rest) ==>
         cm_running_target_sim p fid st
           (first :: second :: values) ann target ==>
         cm_running_target_sim p fid st
           (second :: first :: values)
           (cm_ann_linear [TVMInst TVMSwapOp 0i] ann)
           (tvm_iter 1 target)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm code_at = assume_rule(
      `cm_code_at (cm_model_code (p:cm_program))
        (cm_ann_pc (ann:cm_annotation))
        (TVMInst TVMSwapOp 0i :: (rest:(tvm_inst)list))`);
  thm running = assume_rule(
      `cm_running_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state)
        ((first:cm_value) :: (second:cm_value) ::
          (values:(cm_value)list))
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
         ((first:cm_value) :: (second:cm_value) ::
           (values:(cm_value)list)) []`);
  thm target_equal = conjunct1_rule(body);
  thm pc_equal = conjunct1_rule(conjunct2_rule(body));
  thm machine = conjunct2_rule(conjunct2_rule(body));
  thm stack_length = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `(first:cm_value) :: (second:cm_value) ::
        (values:(cm_value)list)`,
      `[]:(int)list`), get_cm_machine_sim_stack_length()), machine);
  thm stack_two = mp_rule(int_arith_rule(
      `ilength (tvm_stack (vm:tvm_state)) ==
         (1i + 1i + ilength (values:(cm_value)list)) + 0i ==>
       0i <= ilength values ==>
       2i <= ilength (tvm_stack vm)`),
      conv_rule(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))), stack_length));
  stack_two = match_mp_rule(stack_two,
      ispec_rule(`values:(cm_value)list`,
        get_theorem_by_name("ILENGTH_NONNEG")));
  term next =
      `tvm_next_state (vm:tvm_state)
        (HD (TL (tvm_stack vm)) :: HD (tvm_stack vm) ::
         TL (TL (tvm_stack vm)))
        (tvm_calls vm) (tvm_mem vm)
        (tvm_input vm) (tvm_output vm)`;
  thm action = specl_rule(TERM_LIST(
      `tvm_object_code (cm_compile_model (p:cm_program))`,
      `0i:int`, `vm:tvm_state`), get_tvm_swap_transition());
  action = conv_rule(reduce_rewrite_conv(THM_LIST(stack_two)), action);
  thm compiled_code = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_compile_model_def(), get_tvm_object_code_def(),
        pc_equal, code_at)),
      `cm_code_at
        (tvm_object_code (cm_compile_model (p:cm_program)))
        (tvm_pc (vm:tvm_state))
        (TVMInst TVMSwapOp 0i :: (rest:(tvm_inst)list))`));
  thm stepped = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `cm_compile_model (p:cm_program)`, `vm:tvm_state`,
      `TVMSwapOp:tvm_opcode`, `0i:int`,
      `rest:(tvm_inst)list`, next),
      cm_tvm_state_iter_one), compiled_code), action);
  stepped = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(target_equal))), stepped);
  thm machine_after = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `first:cm_value`, `second:cm_value`,
      `values:(cm_value)list`, `[]:(int)list`),
      get_cm_machine_swap()), machine);
  term updated =
      `cm_ann_linear [TVMInst TVMSwapOp 0i] (ann:cm_annotation)`;
  thm next_pc = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_tvm_next_state_def(), get_tvm_state_selectors_def(),
        cm_ann_linear_def, cm_ann_plain_def, cm_ann_pc_def,
        get_theorem_by_name("ILENGTH_DEF"), pc_equal)),
      `tvm_pc ${next:tvm_state} ==
       cm_ann_pc ${updated:cm_annotation}`));
  thm normalized_body =
      conj_rule(stepped, conj_rule(next_pc, machine_after));
  thm_list update_rules = THM_LIST(
      cm_ann_linear_def, cm_ann_plain_def,
      cm_ann_pc_def, cm_ann_calls_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_active_spill_frames_def,
      get_theorem_by_name("ILENGTH_DEF"));
  normalized_body =
      conv_rule(reduce_rewrite_conv(update_rules), normalized_body);
  term exists_goal =
      `?next_vm.
         tvm_iter 1 (target:tvm_task) ==
           TVMRunTask (cm_compile_model (p:cm_program)) next_vm &&
         tvm_pc next_vm == cm_ann_pc ${updated:cm_annotation} &&
         cm_machine_state_sim p (st:cm_src_state) next_vm
           (cm_ann_calls ${updated:cm_annotation})
           (cm_active_spill_frames (fid:int) st
             ${updated:cm_annotation})
           ((second:cm_value) :: (first:cm_value) ::
             (values:(cm_value)list)) []`;
  dest_exists_results exists_parts = dest_exists(exists_goal);
  term instantiated_body =
      subst_one(next, exists_parts.v, exists_parts.tm);
  thm body_reduction = apply_conversion(
      reduce_rewrite_conv(update_rules), instantiated_body);
  thm adjusted_body = eq_mp_rule(
      sym_rule(body_reduction), normalized_body);
  thm witness =
      exists_rule(exists_goal, next, adjusted_body);
  thm selected =
      choose_rule(`vm:tvm_state`, expanded, witness);
  gnode opened = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(cm_running_target_sim_def)));
  ACCEPT_TAC(opened, selected);
  return gnode_prove(root);
}
PROOF thm cm_target_swap = cm_prove_target_swap();


PROOF static thm cm_prove_target_putc(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (v:cm_value) (values:(cm_value)list)
         (ann:cm_annotation) (target:tvm_task)
         (rest:(tvm_inst)list).
         cm_code_at (cm_model_code p) (cm_ann_pc ann)
           (TVMInst TVMPutcOp 0i :: rest) ==>
         cm_running_target_sim p fid st (v :: v :: values)
           ann target ==>
         cm_running_target_sim p fid
           (cm_state_io st (cm_state_input st)
             (cm_state_output st ++
              [tower_u8 (cm_value_number st v)]))
           (CMIntV (cm_value_number st v) :: values)
           (cm_ann_linear [TVMInst TVMPutcOp 0i] ann)
           (tvm_iter 1 target)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm code_at = assume_rule(
      `cm_code_at (cm_model_code (p:cm_program))
        (cm_ann_pc (ann:cm_annotation))
        (TVMInst TVMPutcOp 0i :: (rest:(tvm_inst)list))`);
  thm running = assume_rule(
      `cm_running_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state)
        ((v:cm_value) :: v :: (values:(cm_value)list))
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
         ((v:cm_value) :: v :: (values:(cm_value)list)) []`);
  thm target_equal = conjunct1_rule(body);
  thm pc_equal = conjunct1_rule(conjunct2_rule(body));
  thm machine = conjunct2_rule(conjunct2_rule(body));
  thm stack_length = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `(v:cm_value) :: v :: (values:(cm_value)list)`,
      `[]:(int)list`), get_cm_machine_sim_stack_length()), machine);
  thm stack_nonempty = mp_rule(int_arith_rule(
      `ilength (tvm_stack (vm:tvm_state)) ==
         (1i + 1i + ilength (values:(cm_value)list)) + 0i ==>
       0i <= ilength values ==>
       1i <= ilength (tvm_stack vm)`),
      conv_rule(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))), stack_length));
  stack_nonempty = match_mp_rule(stack_nonempty,
      ispec_rule(`values:(cm_value)list`,
        get_theorem_by_name("ILENGTH_NONNEG")));
  thm io = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `(v:cm_value) :: v :: (values:(cm_value)list)`,
      `[]:(int)list`), cm_machine_sim_io), machine);
  term next =
      `tvm_next_state (vm:tvm_state)
        (TL (tvm_stack vm)) (tvm_calls vm) (tvm_mem vm)
        (tvm_input vm)
        (tvm_output vm ++ [tower_u8 (HD (tvm_stack vm))])`;
  thm action = specl_rule(TERM_LIST(
      `tvm_object_code (cm_compile_model (p:cm_program))`,
      `0i:int`, `vm:tvm_state`), get_tvm_putc_transition());
  action = conv_rule(reduce_rewrite_conv(THM_LIST(
      stack_nonempty)), action);
  thm compiled_code = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_compile_model_def(), get_tvm_object_code_def(),
        pc_equal, code_at)),
      `cm_code_at
        (tvm_object_code (cm_compile_model (p:cm_program)))
        (tvm_pc (vm:tvm_state))
        (TVMInst TVMPutcOp 0i :: (rest:(tvm_inst)list))`));
  thm stepped = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `cm_compile_model (p:cm_program)`, `vm:tvm_state`,
      `TVMPutcOp:tvm_opcode`, `0i:int`,
      `rest:(tvm_inst)list`, next),
      cm_tvm_state_iter_one), compiled_code), action);
  stepped = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(target_equal))), stepped);
  thm machine_after = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `v:cm_value`, `values:(cm_value)list`,
      `[]:(int)list`), get_cm_machine_putc()), machine);
  term next_state =
      `cm_state_io (st:cm_src_state) (cm_state_input st)
        (cm_state_output st ++
         [tower_u8 (cm_value_number st (v:cm_value))])`;
  term updated =
      `cm_ann_linear [TVMInst TVMPutcOp 0i]
        (ann:cm_annotation)`;
  thm next_pc = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_tvm_next_state_def(), get_tvm_state_selectors_def(),
        cm_ann_linear_def, cm_ann_plain_def, cm_ann_pc_def,
        get_theorem_by_name("ILENGTH_DEF"), pc_equal)),
      `tvm_pc ${next:tvm_state} ==
       cm_ann_pc ${updated:cm_annotation}`));
  thm normalized_body =
      conj_rule(stepped, conj_rule(next_pc, machine_after));
  thm_list update_rules = get_cm_state_core_defs();
  vector_add(&update_rules, conjunct1_rule(io));
  vector_add(&update_rules, cm_ann_linear_def);
  vector_add(&update_rules, cm_ann_plain_def);
  vector_add(&update_rules, cm_ann_pc_def);
  vector_add(&update_rules, cm_ann_calls_def);
  vector_add(&update_rules, cm_ann_spills_def);
  vector_add(&update_rules, cm_ann_saved_def);
  vector_add(&update_rules, cm_active_spill_frames_def);
  vector_add(&update_rules, get_theorem_by_name("ILENGTH_DEF"));
  normalized_body =
      conv_rule(reduce_rewrite_conv(update_rules), normalized_body);
  term exists_goal =
      `?next_vm.
         tvm_iter 1 (target:tvm_task) ==
           TVMRunTask (cm_compile_model (p:cm_program)) next_vm &&
         tvm_pc next_vm == cm_ann_pc ${updated:cm_annotation} &&
         cm_machine_state_sim p ${next_state:cm_src_state} next_vm
           (cm_ann_calls ${updated:cm_annotation})
           (cm_active_spill_frames (fid:int)
             ${next_state:cm_src_state} ${updated:cm_annotation})
           ((CMIntV (cm_value_number st (v:cm_value))) ::
             (values:(cm_value)list)) []`;
  dest_exists_results exists_parts = dest_exists(exists_goal);
  term instantiated_body =
      subst_one(next, exists_parts.v, exists_parts.tm);
  thm body_reduction = apply_conversion(
      reduce_rewrite_conv(update_rules), instantiated_body);
  thm adjusted_body = eq_mp_rule(
      sym_rule(body_reduction), normalized_body);
  thm witness =
      exists_rule(exists_goal, next, adjusted_body);
  thm selected =
      choose_rule(`vm:tvm_state`, expanded, witness);
  gnode opened = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(cm_running_target_sim_def)));
  ACCEPT_TAC(opened, selected);
  return gnode_prove(root);
}
PROOF thm cm_target_putc = cm_prove_target_putc();

PROOF static thm cm_prove_target_puti(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (v:cm_value) (values:(cm_value)list)
         (ann:cm_annotation) (target:tvm_task)
         (rest:(tvm_inst)list).
         cm_code_at (cm_model_code p) (cm_ann_pc ann)
           (TVMInst TVMPutiOp 0i :: rest) ==>
         cm_running_target_sim p fid st (v :: v :: values)
           ann target ==>
         cm_running_target_sim p fid
           (cm_state_io st (cm_state_input st)
             (cm_state_output st ++
              tower_decimal (cm_value_number st v)))
           (CMIntV (cm_value_number st v) :: values)
           (cm_ann_linear [TVMInst TVMPutiOp 0i] ann)
           (tvm_iter 1 target)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm code_at = assume_rule(
      `cm_code_at (cm_model_code (p:cm_program))
        (cm_ann_pc (ann:cm_annotation))
        (TVMInst TVMPutiOp 0i :: (rest:(tvm_inst)list))`);
  thm running = assume_rule(
      `cm_running_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state)
        ((v:cm_value) :: v :: (values:(cm_value)list))
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
         ((v:cm_value) :: v :: (values:(cm_value)list)) []`);
  thm target_equal = conjunct1_rule(body);
  thm pc_equal = conjunct1_rule(conjunct2_rule(body));
  thm machine = conjunct2_rule(conjunct2_rule(body));
  thm stack_length = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `(v:cm_value) :: v :: (values:(cm_value)list)`,
      `[]:(int)list`), get_cm_machine_sim_stack_length()), machine);
  thm stack_nonempty = mp_rule(int_arith_rule(
      `ilength (tvm_stack (vm:tvm_state)) ==
         (1i + 1i + ilength (values:(cm_value)list)) + 0i ==>
       0i <= ilength values ==>
       1i <= ilength (tvm_stack vm)`),
      conv_rule(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))), stack_length));
  stack_nonempty = match_mp_rule(stack_nonempty,
      ispec_rule(`values:(cm_value)list`,
        get_theorem_by_name("ILENGTH_NONNEG")));
  thm io = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `(v:cm_value) :: v :: (values:(cm_value)list)`,
      `[]:(int)list`), cm_machine_sim_io), machine);
  term next =
      `tvm_next_state (vm:tvm_state)
        (TL (tvm_stack vm)) (tvm_calls vm) (tvm_mem vm)
        (tvm_input vm)
        (tvm_output vm ++ tower_decimal (HD (tvm_stack vm)))`;
  thm action = specl_rule(TERM_LIST(
      `tvm_object_code (cm_compile_model (p:cm_program))`,
      `0i:int`, `vm:tvm_state`), get_tvm_puti_transition());
  action = conv_rule(reduce_rewrite_conv(THM_LIST(
      stack_nonempty)), action);
  thm compiled_code = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_compile_model_def(), get_tvm_object_code_def(),
        pc_equal, code_at)),
      `cm_code_at
        (tvm_object_code (cm_compile_model (p:cm_program)))
        (tvm_pc (vm:tvm_state))
        (TVMInst TVMPutiOp 0i :: (rest:(tvm_inst)list))`));
  thm stepped = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `cm_compile_model (p:cm_program)`, `vm:tvm_state`,
      `TVMPutiOp:tvm_opcode`, `0i:int`,
      `rest:(tvm_inst)list`, next),
      cm_tvm_state_iter_one), compiled_code), action);
  stepped = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(target_equal))), stepped);
  thm machine_after = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `v:cm_value`, `values:(cm_value)list`,
      `[]:(int)list`), get_cm_machine_puti()), machine);
  term next_state =
      `cm_state_io (st:cm_src_state) (cm_state_input st)
        (cm_state_output st ++
         tower_decimal (cm_value_number st (v:cm_value)))`;
  term updated =
      `cm_ann_linear [TVMInst TVMPutiOp 0i]
        (ann:cm_annotation)`;
  thm next_pc = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_tvm_next_state_def(), get_tvm_state_selectors_def(),
        cm_ann_linear_def, cm_ann_plain_def, cm_ann_pc_def,
        get_theorem_by_name("ILENGTH_DEF"), pc_equal)),
      `tvm_pc ${next:tvm_state} ==
       cm_ann_pc ${updated:cm_annotation}`));
  thm normalized_body =
      conj_rule(stepped, conj_rule(next_pc, machine_after));
  thm_list update_rules = get_cm_state_core_defs();
  vector_add(&update_rules, conjunct1_rule(io));
  vector_add(&update_rules, cm_ann_linear_def);
  vector_add(&update_rules, cm_ann_plain_def);
  vector_add(&update_rules, cm_ann_pc_def);
  vector_add(&update_rules, cm_ann_calls_def);
  vector_add(&update_rules, cm_ann_spills_def);
  vector_add(&update_rules, cm_ann_saved_def);
  vector_add(&update_rules, cm_active_spill_frames_def);
  vector_add(&update_rules, get_theorem_by_name("ILENGTH_DEF"));
  normalized_body =
      conv_rule(reduce_rewrite_conv(update_rules), normalized_body);
  term exists_goal =
      `?next_vm.
         tvm_iter 1 (target:tvm_task) ==
           TVMRunTask (cm_compile_model (p:cm_program)) next_vm &&
         tvm_pc next_vm == cm_ann_pc ${updated:cm_annotation} &&
         cm_machine_state_sim p ${next_state:cm_src_state} next_vm
           (cm_ann_calls ${updated:cm_annotation})
           (cm_active_spill_frames (fid:int)
             ${next_state:cm_src_state} ${updated:cm_annotation})
           ((CMIntV (cm_value_number st (v:cm_value))) ::
             (values:(cm_value)list)) []`;
  dest_exists_results exists_parts = dest_exists(exists_goal);
  term instantiated_body =
      subst_one(next, exists_parts.v, exists_parts.tm);
  thm body_reduction = apply_conversion(
      reduce_rewrite_conv(update_rules), instantiated_body);
  thm adjusted_body = eq_mp_rule(
      sym_rule(body_reduction), normalized_body);
  thm witness =
      exists_rule(exists_goal, next, adjusted_body);
  thm selected =
      choose_rule(`vm:tvm_state`, expanded, witness);
  gnode opened = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(cm_running_target_sim_def)));
  ACCEPT_TAC(opened, selected);
  return gnode_prove(root);
}
PROOF thm cm_target_puti = cm_prove_target_puti();

PROOF static thm cm_prove_target_binary_total(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (right:cm_value) (left:cm_value)
         (values:(cm_value)list) (ann:cm_annotation)
         (target:tvm_task) (opcode:tvm_opcode)
         (operation:int->int->int) (result:cm_value)
         (rest:(tvm_inst)list).
         (!code imm vm.
            tvm_inst_step (code:(tvm_inst)list) opcode (imm:int)
              (vm:tvm_state) =
            (if 2i <= ilength (tvm_stack vm)
             then TVMStepState
               (tvm_next_state vm
                 (operation (HD (TL (tvm_stack vm)))
                    (HD (tvm_stack vm)) ::
                  TL (TL (tvm_stack vm)))
                 (tvm_calls vm) (tvm_mem vm)
                 (tvm_input vm) (tvm_output vm))
             else TVMStepError vm)) ==>
         cm_code_at (cm_model_code p) (cm_ann_pc ann)
           (TVMInst opcode 0i :: rest) ==>
         cm_running_target_sim p fid st
           (right :: left :: values) ann target ==>
         operation (cm_value_number st left)
             (cm_value_number st right) ==
           cm_value_number st result ==>
         cm_running_target_sim p fid st (result :: values)
           (cm_ann_linear [TVMInst opcode 0i] ann)
           (tvm_iter 1 target)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm transition = assume_rule(
      `!code imm vm.
         tvm_inst_step (code:(tvm_inst)list)
           (opcode:tvm_opcode) (imm:int) (vm:tvm_state) =
         (if 2i <= ilength (tvm_stack vm)
          then TVMStepState
            (tvm_next_state vm
              ((operation:int->int->int)
                 (HD (TL (tvm_stack vm)))
                 (HD (tvm_stack vm)) ::
               TL (TL (tvm_stack vm)))
              (tvm_calls vm) (tvm_mem vm)
              (tvm_input vm) (tvm_output vm))
          else TVMStepError vm)`);
  thm code_at = assume_rule(
      `cm_code_at (cm_model_code (p:cm_program))
        (cm_ann_pc (ann:cm_annotation))
        (TVMInst (opcode:tvm_opcode) 0i ::
          (rest:(tvm_inst)list))`);
  thm running = assume_rule(
      `cm_running_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state)
        ((right:cm_value) :: (left:cm_value) ::
          (values:(cm_value)list))
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
         ((right:cm_value) :: (left:cm_value) ::
           (values:(cm_value)list)) []`);
  thm target_equal = conjunct1_rule(body);
  thm pc_equal = conjunct1_rule(conjunct2_rule(body));
  thm machine = conjunct2_rule(conjunct2_rule(body));
  thm stack_length = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `(right:cm_value) :: (left:cm_value) ::
        (values:(cm_value)list)`,
      `[]:(int)list`), get_cm_machine_sim_stack_length()), machine);
  thm stack_two = mp_rule(int_arith_rule(
      `ilength (tvm_stack (vm:tvm_state)) ==
         (1i + 1i + ilength (values:(cm_value)list)) + 0i ==>
       0i <= ilength values ==>
       2i <= ilength (tvm_stack vm)`),
      conv_rule(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))), stack_length));
  stack_two = match_mp_rule(stack_two,
      ispec_rule(`values:(cm_value)list`,
        get_theorem_by_name("ILENGTH_NONNEG")));
  term next =
      `tvm_next_state (vm:tvm_state)
        ((operation:int->int->int)
           (HD (TL (tvm_stack vm))) (HD (tvm_stack vm)) ::
         TL (TL (tvm_stack vm)))
        (tvm_calls vm) (tvm_mem vm)
        (tvm_input vm) (tvm_output vm)`;
  thm action = specl_rule(TERM_LIST(
      `tvm_object_code (cm_compile_model (p:cm_program))`,
      `0i:int`, `vm:tvm_state`), transition);
  action = conv_rule(reduce_rewrite_conv(THM_LIST(
      stack_two)), action);
  thm compiled_code = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_compile_model_def(), get_tvm_object_code_def(),
        pc_equal, code_at)),
      `cm_code_at
        (tvm_object_code (cm_compile_model (p:cm_program)))
        (tvm_pc (vm:tvm_state))
        (TVMInst (opcode:tvm_opcode) 0i ::
          (rest:(tvm_inst)list))`));
  thm stepped = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `cm_compile_model (p:cm_program)`, `vm:tvm_state`,
      `opcode:tvm_opcode`, `0i:int`,
      `rest:(tvm_inst)list`, next),
      cm_tvm_state_iter_one), compiled_code), action);
  stepped = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(target_equal))), stepped);
  thm machine_after = match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
        `cm_ann_calls (ann:cm_annotation)`,
        `cm_active_spill_frames (fid:int) st ann`,
        `right:cm_value`, `left:cm_value`,
        `values:(cm_value)list`, `[]:(int)list`,
        `result:cm_value`, `operation:int->int->int`),
        get_cm_machine_binary_operation()),
      machine), assume_rule(
        `(operation:int->int->int)
           (cm_value_number (st:cm_src_state) (left:cm_value))
           (cm_value_number st (right:cm_value)) ==
         cm_value_number st (result:cm_value)`));
  term updated =
      `cm_ann_linear [TVMInst (opcode:tvm_opcode) 0i]
        (ann:cm_annotation)`;
  thm next_pc = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_tvm_next_state_def(), get_tvm_state_selectors_def(),
        cm_ann_linear_def, cm_ann_plain_def, cm_ann_pc_def,
        get_theorem_by_name("ILENGTH_DEF"), pc_equal)),
      `tvm_pc ${next:tvm_state} ==
       cm_ann_pc ${updated:cm_annotation}`));
  thm normalized_body =
      conj_rule(stepped, conj_rule(next_pc, machine_after));
  thm_list update_rules = THM_LIST(
      cm_ann_linear_def, cm_ann_plain_def,
      cm_ann_pc_def, cm_ann_calls_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_active_spill_frames_def,
      get_theorem_by_name("ILENGTH_DEF"));
  normalized_body =
      conv_rule(reduce_rewrite_conv(update_rules), normalized_body);
  term exists_goal =
      `?next_vm.
         tvm_iter 1 (target:tvm_task) ==
           TVMRunTask (cm_compile_model (p:cm_program)) next_vm &&
         tvm_pc next_vm == cm_ann_pc ${updated:cm_annotation} &&
         cm_machine_state_sim p (st:cm_src_state) next_vm
           (cm_ann_calls ${updated:cm_annotation})
           (cm_active_spill_frames (fid:int) st
             ${updated:cm_annotation})
           ((result:cm_value) :: (values:(cm_value)list)) []`;
  dest_exists_results exists_parts = dest_exists(exists_goal);
  term instantiated_body =
      subst_one(next, exists_parts.v, exists_parts.tm);
  thm body_reduction = apply_conversion(
      reduce_rewrite_conv(update_rules), instantiated_body);
  thm adjusted_body = eq_mp_rule(
      sym_rule(body_reduction), normalized_body);
  thm witness =
      exists_rule(exists_goal, next, adjusted_body);
  thm selected =
      choose_rule(`vm:tvm_state`, expanded, witness);
  gnode opened = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(cm_running_target_sim_def)));
  ACCEPT_TAC(opened, selected);
  return gnode_prove(root);
}
PROOF thm cm_target_binary_total =
    cm_prove_target_binary_total();

PROOF static thm cm_prove_target_binary_nonzero(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (right:cm_value) (left:cm_value)
         (values:(cm_value)list) (ann:cm_annotation)
         (target:tvm_task) (opcode:tvm_opcode)
         (operation:int->int->int) (result:cm_value)
         (rest:(tvm_inst)list).
         (!code imm vm.
            tvm_inst_step (code:(tvm_inst)list) opcode (imm:int)
              (vm:tvm_state) =
            (if 2i <= ilength (tvm_stack vm) &&
                ~(HD (tvm_stack vm) == 0i)
             then TVMStepState
               (tvm_next_state vm
                 (operation (HD (TL (tvm_stack vm)))
                    (HD (tvm_stack vm)) ::
                  TL (TL (tvm_stack vm)))
                 (tvm_calls vm) (tvm_mem vm)
                 (tvm_input vm) (tvm_output vm))
             else TVMStepError vm)) ==>
         cm_code_at (cm_model_code p) (cm_ann_pc ann)
           (TVMInst opcode 0i :: rest) ==>
         cm_running_target_sim p fid st
           (right :: left :: values) ann target ==>
         ~(cm_value_number st right == 0i) ==>
         operation (cm_value_number st left)
             (cm_value_number st right) ==
           cm_value_number st result ==>
         cm_running_target_sim p fid st (result :: values)
           (cm_ann_linear [TVMInst opcode 0i] ann)
           (tvm_iter 1 target)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm transition = assume_rule(
      `!code imm vm.
         tvm_inst_step (code:(tvm_inst)list)
           (opcode:tvm_opcode) (imm:int) (vm:tvm_state) =
         (if 2i <= ilength (tvm_stack vm) &&
             ~(HD (tvm_stack vm) == 0i)
          then TVMStepState
            (tvm_next_state vm
              ((operation:int->int->int)
                 (HD (TL (tvm_stack vm)))
                 (HD (tvm_stack vm)) ::
               TL (TL (tvm_stack vm)))
              (tvm_calls vm) (tvm_mem vm)
              (tvm_input vm) (tvm_output vm))
          else TVMStepError vm)`);
  thm code_at = assume_rule(
      `cm_code_at (cm_model_code (p:cm_program))
        (cm_ann_pc (ann:cm_annotation))
        (TVMInst (opcode:tvm_opcode) 0i ::
          (rest:(tvm_inst)list))`);
  thm running = assume_rule(
      `cm_running_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state)
        ((right:cm_value) :: (left:cm_value) ::
          (values:(cm_value)list))
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
         ((right:cm_value) :: (left:cm_value) ::
           (values:(cm_value)list)) []`);
  thm target_equal = conjunct1_rule(body);
  thm pc_equal = conjunct1_rule(conjunct2_rule(body));
  thm machine = conjunct2_rule(conjunct2_rule(body));
  thm stack_length = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `(right:cm_value) :: (left:cm_value) ::
        (values:(cm_value)list)`,
      `[]:(int)list`), get_cm_machine_sim_stack_length()), machine);
  thm stack_two = mp_rule(int_arith_rule(
      `ilength (tvm_stack (vm:tvm_state)) ==
         (1i + 1i + ilength (values:(cm_value)list)) + 0i ==>
       0i <= ilength values ==>
       2i <= ilength (tvm_stack vm)`),
      conv_rule(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))), stack_length));
  stack_two = match_mp_rule(stack_two,
      ispec_rule(`values:(cm_value)list`,
        get_theorem_by_name("ILENGTH_NONNEG")));
  thm stack_head = conjunct1_rule(mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `right:cm_value`,
      `(left:cm_value) :: (values:(cm_value)list)`,
      `[]:(int)list`), get_cm_machine_sim_stack_head()), machine));
  thm right_nonzero = assume_rule(
      `~(cm_value_number (st:cm_src_state) (right:cm_value) == 0i)`);
  thm raw_nonzero = conv_rule(
      rewrite_conv(THM_LIST(sym_rule(stack_head))), right_nonzero);
  term next =
      `tvm_next_state (vm:tvm_state)
        ((operation:int->int->int)
           (HD (TL (tvm_stack vm))) (HD (tvm_stack vm)) ::
         TL (TL (tvm_stack vm)))
        (tvm_calls vm) (tvm_mem vm)
        (tvm_input vm) (tvm_output vm)`;
  thm action = specl_rule(TERM_LIST(
      `tvm_object_code (cm_compile_model (p:cm_program))`,
      `0i:int`, `vm:tvm_state`), transition);
  action = conv_rule(reduce_rewrite_conv(THM_LIST(
      stack_two, raw_nonzero)), action);
  thm compiled_code = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_compile_model_def(), get_tvm_object_code_def(),
        pc_equal, code_at)),
      `cm_code_at
        (tvm_object_code (cm_compile_model (p:cm_program)))
        (tvm_pc (vm:tvm_state))
        (TVMInst (opcode:tvm_opcode) 0i ::
          (rest:(tvm_inst)list))`));
  thm stepped = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `cm_compile_model (p:cm_program)`, `vm:tvm_state`,
      `opcode:tvm_opcode`, `0i:int`,
      `rest:(tvm_inst)list`, next),
      cm_tvm_state_iter_one), compiled_code), action);
  stepped = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(target_equal))), stepped);
  thm machine_after = match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
        `cm_ann_calls (ann:cm_annotation)`,
        `cm_active_spill_frames (fid:int) st ann`,
        `right:cm_value`, `left:cm_value`,
        `values:(cm_value)list`, `[]:(int)list`,
        `result:cm_value`, `operation:int->int->int`),
        get_cm_machine_binary_operation()),
      machine), assume_rule(
        `(operation:int->int->int)
           (cm_value_number (st:cm_src_state) (left:cm_value))
           (cm_value_number st (right:cm_value)) ==
         cm_value_number st (result:cm_value)`));
  term updated =
      `cm_ann_linear [TVMInst (opcode:tvm_opcode) 0i]
        (ann:cm_annotation)`;
  thm next_pc = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_tvm_next_state_def(), get_tvm_state_selectors_def(),
        cm_ann_linear_def, cm_ann_plain_def, cm_ann_pc_def,
        get_theorem_by_name("ILENGTH_DEF"), pc_equal)),
      `tvm_pc ${next:tvm_state} ==
       cm_ann_pc ${updated:cm_annotation}`));
  thm normalized_body =
      conj_rule(stepped, conj_rule(next_pc, machine_after));
  thm_list update_rules = THM_LIST(
      cm_ann_linear_def, cm_ann_plain_def,
      cm_ann_pc_def, cm_ann_calls_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_active_spill_frames_def,
      get_theorem_by_name("ILENGTH_DEF"));
  normalized_body =
      conv_rule(reduce_rewrite_conv(update_rules), normalized_body);
  term exists_goal =
      `?next_vm.
         tvm_iter 1 (target:tvm_task) ==
           TVMRunTask (cm_compile_model (p:cm_program)) next_vm &&
         tvm_pc next_vm == cm_ann_pc ${updated:cm_annotation} &&
         cm_machine_state_sim p (st:cm_src_state) next_vm
           (cm_ann_calls ${updated:cm_annotation})
           (cm_active_spill_frames (fid:int) st
             ${updated:cm_annotation})
           ((result:cm_value) :: (values:(cm_value)list)) []`;
  dest_exists_results exists_parts = dest_exists(exists_goal);
  term instantiated_body =
      subst_one(next, exists_parts.v, exists_parts.tm);
  thm body_reduction = apply_conversion(
      reduce_rewrite_conv(update_rules), instantiated_body);
  thm adjusted_body = eq_mp_rule(
      sym_rule(body_reduction), normalized_body);
  thm witness =
      exists_rule(exists_goal, next, adjusted_body);
  thm selected =
      choose_rule(`vm:tvm_state`, expanded, witness);
  gnode opened = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(cm_running_target_sim_def)));
  ACCEPT_TAC(opened, selected);
  return gnode_prove(root);
}
PROOF thm cm_target_binary_nonzero =
    cm_prove_target_binary_nonzero();

PROOF static thm cm_prove_target_jump(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (values:(cm_value)list) (ann:cm_annotation)
         (target:tvm_task) (jump_pc:int)
         (rest:(tvm_inst)list).
         cm_code_at (cm_model_code p) (cm_ann_pc ann)
           (TVMInst TVMJmpOp jump_pc :: rest) ==>
         tvm_target_valid (cm_model_code p) jump_pc ==>
         cm_running_target_sim p fid st values ann target ==>
         cm_running_target_sim p fid st values
           (cm_ann_plain jump_pc (cm_ann_temp ann)
             (cm_ann_break ann) (cm_ann_continue ann) ann)
           (tvm_iter 1 target)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm code_at = assume_rule(
      `cm_code_at (cm_model_code (p:cm_program))
        (cm_ann_pc (ann:cm_annotation))
        (TVMInst TVMJmpOp (jump_pc:int) ::
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
  term next =
      `tvm_jump_state (vm:tvm_state) (jump_pc:int)
        (tvm_stack vm) (tvm_calls vm) (tvm_mem vm)
        (tvm_input vm) (tvm_output vm)`;
  thm valid_object = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_compile_model_def(), get_tvm_object_code_def(), valid)),
      `tvm_target_valid
        (tvm_object_code (cm_compile_model (p:cm_program)))
        (jump_pc:int)`));
  thm action = specl_rule(TERM_LIST(
      `tvm_object_code (cm_compile_model (p:cm_program))`,
      `jump_pc:int`, `vm:tvm_state`), get_tvm_jmp_transition());
  action = conv_rule(
      reduce_rewrite_conv(THM_LIST(valid_object)), action);
  thm compiled_code = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_compile_model_def(), get_tvm_object_code_def(),
        pc_equal, code_at)),
      `cm_code_at
        (tvm_object_code (cm_compile_model (p:cm_program)))
        (tvm_pc (vm:tvm_state))
        (TVMInst TVMJmpOp (jump_pc:int) ::
          (rest:(tvm_inst)list))`));
  thm stepped = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `cm_compile_model (p:cm_program)`, `vm:tvm_state`,
      `TVMJmpOp:tvm_opcode`, `jump_pc:int`,
      `rest:(tvm_inst)list`, next),
      cm_tvm_state_iter_one), compiled_code), action);
  stepped = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(target_equal))), stepped);
  thm machine_after = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `values:(cm_value)list`, `[]:(int)list`,
      `jump_pc:int`), get_cm_machine_jump()), machine);
  term updated =
      `cm_ann_plain (jump_pc:int) (cm_ann_temp ann)
        (cm_ann_break ann) (cm_ann_continue ann)
        (ann:cm_annotation)`;
  thm next_pc = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_tvm_jump_state_def(), get_tvm_state_selectors_def(),
        cm_ann_plain_def, cm_ann_pc_def)),
      `tvm_pc ${next:tvm_state} ==
       cm_ann_pc ${updated:cm_annotation}`));
  thm normalized_body =
      conj_rule(stepped, conj_rule(next_pc, machine_after));
  thm_list update_rules = THM_LIST(
      cm_ann_plain_def, cm_ann_pc_def,
      cm_ann_calls_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_active_spill_frames_def);
  normalized_body =
      conv_rule(reduce_rewrite_conv(update_rules), normalized_body);
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
  term instantiated_body =
      subst_one(next, exists_parts.v, exists_parts.tm);
  thm body_reduction = apply_conversion(
      reduce_rewrite_conv(update_rules), instantiated_body);
  thm adjusted_body = eq_mp_rule(
      sym_rule(body_reduction), normalized_body);
  thm witness =
      exists_rule(exists_goal, next, adjusted_body);
  thm selected =
      choose_rule(`vm:tvm_state`, expanded, witness);
  gnode opened = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(cm_running_target_sim_def)));
  ACCEPT_TAC(opened, selected);
  return gnode_prove(root);
}
PROOF thm cm_target_jump = cm_prove_target_jump();

PROOF static thm cm_prove_target_jz(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (condition:cm_value) (values:(cm_value)list)
         (ann:cm_annotation) (target:tvm_task) (jump_pc:int)
         (rest:(tvm_inst)list).
         cm_code_at (cm_model_code p) (cm_ann_pc ann)
           (TVMInst TVMJzOp jump_pc :: rest) ==>
         tvm_target_valid (cm_model_code p) jump_pc ==>
         cm_running_target_sim p fid st
           (condition :: values) ann target ==>
         cm_running_target_sim p fid st values
           (if cm_truth st condition
            then cm_ann_linear [TVMInst TVMJzOp jump_pc] ann
            else cm_ann_plain jump_pc (cm_ann_temp ann)
                   (cm_ann_break ann) (cm_ann_continue ann) ann)
           (tvm_iter 1 target)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm code_at = assume_rule(
      `cm_code_at (cm_model_code (p:cm_program))
        (cm_ann_pc (ann:cm_annotation))
        (TVMInst TVMJzOp (jump_pc:int) ::
          (rest:(tvm_inst)list))`);
  thm valid = assume_rule(
      `tvm_target_valid (cm_model_code (p:cm_program))
        (jump_pc:int)`);
  thm running = assume_rule(
      `cm_running_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state)
        ((condition:cm_value) :: (values:(cm_value)list))
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
         ((condition:cm_value) :: (values:(cm_value)list)) []`);
  thm target_equal = conjunct1_rule(body);
  thm pc_equal = conjunct1_rule(conjunct2_rule(body));
  thm machine = conjunct2_rule(conjunct2_rule(body));
  thm stack_length = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `(condition:cm_value) :: (values:(cm_value)list)`,
      `[]:(int)list`), get_cm_machine_sim_stack_length()), machine);
  thm stack_nonempty = mp_rule(int_arith_rule(
      `ilength (tvm_stack (vm:tvm_state)) ==
         (1i + ilength (values:(cm_value)list)) + 0i ==>
       0i <= ilength values ==>
       1i <= ilength (tvm_stack vm)`),
      conv_rule(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))), stack_length));
  stack_nonempty = match_mp_rule(stack_nonempty,
      ispec_rule(`values:(cm_value)list`,
        get_theorem_by_name("ILENGTH_NONNEG")));
  thm head = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `condition:cm_value`, `values:(cm_value)list`,
      `[]:(int)list`), cm_machine_sim_stack_head), machine);
  thm valid_object = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_compile_model_def(), get_tvm_object_code_def(), valid)),
      `tvm_target_valid
        (tvm_object_code (cm_compile_model (p:cm_program)))
        (jump_pc:int)`));
  thm compiled_code = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_compile_model_def(), get_tvm_object_code_def(),
        pc_equal, code_at)),
      `cm_code_at
        (tvm_object_code (cm_compile_model (p:cm_program)))
        (tvm_pc (vm:tvm_state))
        (TVMInst TVMJzOp (jump_pc:int) ::
          (rest:(tvm_inst)list))`));
  gnode_list cases = BOOL_CASES_TAC(
      leaf, `cm_truth (st:cm_src_state) (condition:cm_value)`,
      "Htruth");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    bool truth = i == 0;
    thm truth_case = assume_rule(truth
        ? `cm_truth (st:cm_src_state) (condition:cm_value)`
        : `~cm_truth (st:cm_src_state) (condition:cm_value)`);
    thm numeric_case = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          get_cm_truth_number_bridge())), truth_case);
    term next = truth
        ? `tvm_next_state (vm:tvm_state)
            (TL (tvm_stack vm)) (tvm_calls vm) (tvm_mem vm)
            (tvm_input vm) (tvm_output vm)`
        : `tvm_jump_state (vm:tvm_state) (jump_pc:int)
            (TL (tvm_stack vm)) (tvm_calls vm) (tvm_mem vm)
            (tvm_input vm) (tvm_output vm)`;
    term updated = truth
        ? `cm_ann_linear [TVMInst TVMJzOp (jump_pc:int)]
            (ann:cm_annotation)`
        : `cm_ann_plain (jump_pc:int) (cm_ann_temp ann)
            (cm_ann_break ann) (cm_ann_continue ann)
            (ann:cm_annotation)`;
    term selected_pc = truth
        ? `tvm_pc (vm:tvm_state) + 1i`
        : `jump_pc:int`;
    thm action = specl_rule(TERM_LIST(
        `tvm_object_code (cm_compile_model (p:cm_program))`,
        `jump_pc:int`, `vm:tvm_state`), get_tvm_jz_transition());
    action = conv_rule(reduce_rewrite_conv(THM_LIST(
        stack_nonempty, conjunct1_rule(head),
        numeric_case, valid_object)), action);
    thm stepped = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
        `cm_compile_model (p:cm_program)`, `vm:tvm_state`,
        `TVMJzOp:tvm_opcode`, `jump_pc:int`,
        `rest:(tvm_inst)list`, next),
        cm_tvm_state_iter_one), compiled_code), action);
    stepped = conv_rule(rewrite_conv(THM_LIST(
        sym_rule(target_equal))), stepped);
    thm machine_after = match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
        `cm_ann_calls (ann:cm_annotation)`,
        `cm_active_spill_frames (fid:int) st ann`,
        `condition:cm_value`, `values:(cm_value)list`,
        `[]:(int)list`, selected_pc),
        get_cm_machine_branch_pop()), machine);
    machine_after = conv_rule(rewrite_conv(THM_LIST(
        truth ? get_tvm_next_state_def() : get_tvm_jump_state_def())),
        machine_after);
    thm next_pc = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          truth ? get_tvm_next_state_def() : get_tvm_jump_state_def(),
          get_tvm_state_selectors_def(), cm_ann_linear_def,
          cm_ann_plain_def, cm_ann_pc_def,
          get_theorem_by_name("ILENGTH_DEF"), pc_equal)),
        `tvm_pc ${next:tvm_state} ==
         cm_ann_pc ${updated:cm_annotation}`));
    thm normalized_body =
        conj_rule(stepped, conj_rule(next_pc, machine_after));
    thm_list update_rules = THM_LIST(
        cm_ann_linear_def, cm_ann_plain_def,
        cm_ann_pc_def, cm_ann_calls_def, cm_ann_spills_def,
        cm_ann_saved_def, cm_active_spill_frames_def,
        get_theorem_by_name("ILENGTH_DEF"), truth_case);
    vector_add(&update_rules,
        truth ? get_tvm_next_state_def() : get_tvm_jump_state_def());
    normalized_body =
        conv_rule(reduce_rewrite_conv(update_rules), normalized_body);
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
    term instantiated_body =
        subst_one(next, exists_parts.v, exists_parts.tm);
    thm body_reduction = apply_conversion(
        reduce_rewrite_conv(update_rules), instantiated_body);
    thm adjusted_body = eq_mp_rule(
        sym_rule(body_reduction), normalized_body);
    thm witness =
        exists_rule(exists_goal, next, adjusted_body);
    thm selected =
        choose_rule(`vm:tvm_state`, expanded, witness);
    gnode opened = CONV_TAC(cases[i],
        reduce_rewrite_conv(THM_LIST(
          cm_running_target_sim_def, truth_case)));
    ACCEPT_TAC(opened, selected);
  }
  return gnode_prove(root);
}
PROOF thm cm_target_jz = cm_prove_target_jz();

PROOF static thm cm_prove_target_jnz(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (condition:cm_value) (values:(cm_value)list)
         (ann:cm_annotation) (target:tvm_task) (jump_pc:int)
         (rest:(tvm_inst)list).
         cm_code_at (cm_model_code p) (cm_ann_pc ann)
           (TVMInst TVMJnzOp jump_pc :: rest) ==>
         tvm_target_valid (cm_model_code p) jump_pc ==>
         cm_running_target_sim p fid st
           (condition :: values) ann target ==>
         cm_running_target_sim p fid st values
           (if cm_truth st condition
            then cm_ann_plain jump_pc (cm_ann_temp ann)
                   (cm_ann_break ann) (cm_ann_continue ann) ann
            else cm_ann_linear [TVMInst TVMJnzOp jump_pc] ann)
           (tvm_iter 1 target)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm code_at = assume_rule(
      `cm_code_at (cm_model_code (p:cm_program))
        (cm_ann_pc (ann:cm_annotation))
        (TVMInst TVMJnzOp (jump_pc:int) ::
          (rest:(tvm_inst)list))`);
  thm valid = assume_rule(
      `tvm_target_valid (cm_model_code (p:cm_program))
        (jump_pc:int)`);
  thm running = assume_rule(
      `cm_running_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state)
        ((condition:cm_value) :: (values:(cm_value)list))
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
         ((condition:cm_value) :: (values:(cm_value)list)) []`);
  thm target_equal = conjunct1_rule(body);
  thm pc_equal = conjunct1_rule(conjunct2_rule(body));
  thm machine = conjunct2_rule(conjunct2_rule(body));
  thm stack_length = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `(condition:cm_value) :: (values:(cm_value)list)`,
      `[]:(int)list`), get_cm_machine_sim_stack_length()), machine);
  thm stack_nonempty = mp_rule(int_arith_rule(
      `ilength (tvm_stack (vm:tvm_state)) ==
         (1i + ilength (values:(cm_value)list)) + 0i ==>
       0i <= ilength values ==>
       1i <= ilength (tvm_stack vm)`),
      conv_rule(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))), stack_length));
  stack_nonempty = match_mp_rule(stack_nonempty,
      ispec_rule(`values:(cm_value)list`,
        get_theorem_by_name("ILENGTH_NONNEG")));
  thm head = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `condition:cm_value`, `values:(cm_value)list`,
      `[]:(int)list`), cm_machine_sim_stack_head), machine);
  thm valid_object = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_compile_model_def(), get_tvm_object_code_def(), valid)),
      `tvm_target_valid
        (tvm_object_code (cm_compile_model (p:cm_program)))
        (jump_pc:int)`));
  thm compiled_code = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_compile_model_def(), get_tvm_object_code_def(),
        pc_equal, code_at)),
      `cm_code_at
        (tvm_object_code (cm_compile_model (p:cm_program)))
        (tvm_pc (vm:tvm_state))
        (TVMInst TVMJnzOp (jump_pc:int) ::
          (rest:(tvm_inst)list))`));
  gnode_list cases = BOOL_CASES_TAC(
      leaf, `cm_truth (st:cm_src_state) (condition:cm_value)`,
      "Htruth");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    bool truth = i == 0;
    thm truth_case = assume_rule(truth
        ? `cm_truth (st:cm_src_state) (condition:cm_value)`
        : `~cm_truth (st:cm_src_state) (condition:cm_value)`);
    thm numeric_case = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          get_cm_truth_number_bridge())), truth_case);
    term next = truth
        ? `tvm_jump_state (vm:tvm_state) (jump_pc:int)
            (TL (tvm_stack vm)) (tvm_calls vm) (tvm_mem vm)
            (tvm_input vm) (tvm_output vm)`
        : `tvm_next_state (vm:tvm_state)
            (TL (tvm_stack vm)) (tvm_calls vm) (tvm_mem vm)
            (tvm_input vm) (tvm_output vm)`;
    term updated = truth
        ? `cm_ann_plain (jump_pc:int) (cm_ann_temp ann)
            (cm_ann_break ann) (cm_ann_continue ann)
            (ann:cm_annotation)`
        : `cm_ann_linear [TVMInst TVMJnzOp (jump_pc:int)]
            (ann:cm_annotation)`;
    term selected_pc = truth
        ? `jump_pc:int`
        : `tvm_pc (vm:tvm_state) + 1i`;
    thm action = specl_rule(TERM_LIST(
        `tvm_object_code (cm_compile_model (p:cm_program))`,
        `jump_pc:int`, `vm:tvm_state`), get_tvm_jnz_transition());
    action = conv_rule(reduce_rewrite_conv(THM_LIST(
        stack_nonempty, conjunct1_rule(head),
        numeric_case, valid_object)), action);
    thm stepped = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
        `cm_compile_model (p:cm_program)`, `vm:tvm_state`,
        `TVMJnzOp:tvm_opcode`, `jump_pc:int`,
        `rest:(tvm_inst)list`, next),
        cm_tvm_state_iter_one), compiled_code), action);
    stepped = conv_rule(rewrite_conv(THM_LIST(
        sym_rule(target_equal))), stepped);
    thm machine_after = match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
        `cm_ann_calls (ann:cm_annotation)`,
        `cm_active_spill_frames (fid:int) st ann`,
        `condition:cm_value`, `values:(cm_value)list`,
        `[]:(int)list`, selected_pc),
        get_cm_machine_branch_pop()), machine);
    machine_after = conv_rule(rewrite_conv(THM_LIST(
        truth ? get_tvm_jump_state_def() : get_tvm_next_state_def())),
        machine_after);
    thm next_pc = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          truth ? get_tvm_jump_state_def() : get_tvm_next_state_def(),
          get_tvm_state_selectors_def(), cm_ann_linear_def,
          cm_ann_plain_def, cm_ann_pc_def,
          get_theorem_by_name("ILENGTH_DEF"), pc_equal)),
        `tvm_pc ${next:tvm_state} ==
         cm_ann_pc ${updated:cm_annotation}`));
    thm normalized_body =
        conj_rule(stepped, conj_rule(next_pc, machine_after));
    thm_list update_rules = THM_LIST(
        cm_ann_linear_def, cm_ann_plain_def,
        cm_ann_pc_def, cm_ann_calls_def, cm_ann_spills_def,
        cm_ann_saved_def, cm_active_spill_frames_def,
        get_theorem_by_name("ILENGTH_DEF"), truth_case);
    vector_add(&update_rules,
        truth ? get_tvm_jump_state_def() : get_tvm_next_state_def());
    normalized_body =
        conv_rule(reduce_rewrite_conv(update_rules), normalized_body);
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
    term instantiated_body =
        subst_one(next, exists_parts.v, exists_parts.tm);
    thm body_reduction = apply_conversion(
        reduce_rewrite_conv(update_rules), instantiated_body);
    thm adjusted_body = eq_mp_rule(
        sym_rule(body_reduction), normalized_body);
    thm witness =
        exists_rule(exists_goal, next, adjusted_body);
    thm selected =
        choose_rule(`vm:tvm_state`, expanded, witness);
    gnode opened = CONV_TAC(cases[i],
        reduce_rewrite_conv(THM_LIST(
          cm_running_target_sim_def, truth_case)));
    ACCEPT_TAC(opened, selected);
  }
  return gnode_prove(root);
}
PROOF thm cm_target_jnz = cm_prove_target_jnz();

PROOF static thm cm_prove_target_load_fp(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (values:(cm_value)list) (ann:cm_annotation)
         (target:tvm_task) (rest:(tvm_inst)list).
         cm_code_at (cm_model_code p) (cm_ann_pc ann)
           (TVMInst TVMLoadOp 0i :: rest) ==>
         cm_running_target_sim p fid st
           (CMIntV 8i :: values) ann target ==>
         tower_signed64 (cm_state_fp st) ==>
         cm_running_target_sim p fid st
           (CMIntV (cm_state_fp st) :: values)
           (cm_ann_linear [TVMInst TVMLoadOp 0i] ann)
           (tvm_iter 1 target)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm code_at = assume_rule(
      `cm_code_at (cm_model_code (p:cm_program))
        (cm_ann_pc (ann:cm_annotation))
        (TVMInst TVMLoadOp 0i :: (rest:(tvm_inst)list))`);
  thm running = assume_rule(
      `cm_running_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state)
        (CMIntV 8i :: (values:(cm_value)list))
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
         (CMIntV 8i :: (values:(cm_value)list)) []`);
  thm target_equal = conjunct1_rule(body);
  thm pc_equal = conjunct1_rule(conjunct2_rule(body));
  thm machine = conjunct2_rule(conjunct2_rule(body));
  thm stack_length = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `CMIntV 8i :: (values:(cm_value)list)`,
      `[]:(int)list`), get_cm_machine_sim_stack_length()), machine);
  thm stack_nonempty = mp_rule(int_arith_rule(
      `ilength (tvm_stack (vm:tvm_state)) ==
         (1i + ilength (values:(cm_value)list)) + 0i ==>
       0i <= ilength values ==>
       1i <= ilength (tvm_stack vm)`),
      conv_rule(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))), stack_length));
  stack_nonempty = match_mp_rule(stack_nonempty,
      ispec_rule(`values:(cm_value)list`,
        get_theorem_by_name("ILENGTH_NONNEG")));
  thm head = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `CMIntV 8i`, `values:(cm_value)list`,
      `[]:(int)list`), cm_machine_sim_stack_head), machine);
  thm address_valid = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        conjunct1_rule(head), get_cm_value_number_def(),
        get_tower_wrap64_def(), get_tower_word_valid_def())),
      `tower_word_valid (HD (tvm_stack (vm:tvm_state)))`));
  term next =
      `tvm_next_state (vm:tvm_state)
        (tower_getw (tvm_mem vm) (HD (tvm_stack vm)) ::
         TL (tvm_stack vm))
        (tvm_calls vm) (tvm_mem vm)
        (tvm_input vm) (tvm_output vm)`;
  thm action = specl_rule(TERM_LIST(
      `tvm_object_code (cm_compile_model (p:cm_program))`,
      `0i:int`, `vm:tvm_state`), get_tvm_load_transition());
  action = conv_rule(reduce_rewrite_conv(THM_LIST(
      stack_nonempty, address_valid)), action);
  thm compiled_code = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_compile_model_def(), get_tvm_object_code_def(),
        pc_equal, code_at)),
      `cm_code_at
        (tvm_object_code (cm_compile_model (p:cm_program)))
        (tvm_pc (vm:tvm_state))
        (TVMInst TVMLoadOp 0i :: (rest:(tvm_inst)list))`));
  thm stepped = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `cm_compile_model (p:cm_program)`, `vm:tvm_state`,
      `TVMLoadOp:tvm_opcode`, `0i:int`,
      `rest:(tvm_inst)list`, next),
      cm_tvm_state_iter_one), compiled_code), action);
  stepped = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(target_equal))), stepped);
  thm machine_after = match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
        `cm_ann_calls (ann:cm_annotation)`,
        `cm_active_spill_frames (fid:int) st ann`,
        `values:(cm_value)list`, `[]:(int)list`),
        get_cm_machine_load_fp()), machine),
      assume_rule(
        `tower_signed64 (cm_state_fp (st:cm_src_state))`));
  term updated =
      `cm_ann_linear [TVMInst TVMLoadOp 0i]
        (ann:cm_annotation)`;
  thm next_pc = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_tvm_next_state_def(), get_tvm_state_selectors_def(),
        cm_ann_linear_def, cm_ann_plain_def, cm_ann_pc_def,
        get_theorem_by_name("ILENGTH_DEF"), pc_equal)),
      `tvm_pc ${next:tvm_state} ==
       cm_ann_pc ${updated:cm_annotation}`));
  thm normalized_body =
      conj_rule(stepped, conj_rule(next_pc, machine_after));
  thm_list update_rules = THM_LIST(
      cm_ann_linear_def, cm_ann_plain_def,
      cm_ann_pc_def, cm_ann_calls_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_active_spill_frames_def,
      get_theorem_by_name("ILENGTH_DEF"));
  normalized_body =
      conv_rule(reduce_rewrite_conv(update_rules), normalized_body);
  term exists_goal =
      `?next_vm.
         tvm_iter 1 (target:tvm_task) ==
           TVMRunTask (cm_compile_model (p:cm_program)) next_vm &&
         tvm_pc next_vm == cm_ann_pc ${updated:cm_annotation} &&
         cm_machine_state_sim p (st:cm_src_state) next_vm
           (cm_ann_calls ${updated:cm_annotation})
           (cm_active_spill_frames (fid:int) st
             ${updated:cm_annotation})
           (CMIntV (cm_state_fp st) ::
             (values:(cm_value)list)) []`;
  dest_exists_results exists_parts = dest_exists(exists_goal);
  term instantiated_body =
      subst_one(next, exists_parts.v, exists_parts.tm);
  thm body_reduction = apply_conversion(
      reduce_rewrite_conv(update_rules), instantiated_body);
  thm adjusted_body = eq_mp_rule(
      sym_rule(body_reduction), normalized_body);
  thm witness =
      exists_rule(exists_goal, next, adjusted_body);
  thm selected =
      choose_rule(`vm:tvm_state`, expanded, witness);
  gnode opened = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(cm_running_target_sim_def)));
  ACCEPT_TAC(opened, selected);
  return gnode_prove(root);
}
PROOF thm cm_target_load_fp = cm_prove_target_load_fp();

PROOF static thm cm_prove_target_spill_load(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (slot:int) (spill_value:cm_value) (address:int)
         (values:(cm_value)list) (ann:cm_annotation)
         (target:tvm_task) (rest:(tvm_inst)list).
         cm_code_at (cm_model_code p) (cm_ann_pc ann)
           (TVMInst TVMLoadOp 0i :: rest) ==>
         cm_running_target_sim p fid st
           (CMIntV address :: values) ann target ==>
         cm_spill_holds slot spill_value (cm_ann_spills ann) ==>
         address ==
           cm_state_fp st + cm_temp_offset p fid slot ==>
         tower_signed64 address ==>
         tower_word_valid address ==>
         cm_running_target_sim p fid st
           (spill_value :: values)
           (cm_ann_linear [TVMInst TVMLoadOp 0i] ann)
           (tvm_iter 1 target)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm code_at = assume_rule(
      `cm_code_at (cm_model_code (p:cm_program))
        (cm_ann_pc (ann:cm_annotation))
        (TVMInst TVMLoadOp 0i :: (rest:(tvm_inst)list))`);
  thm running = assume_rule(
      `cm_running_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state)
        (CMIntV (address:int) :: (values:(cm_value)list))
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
         (CMIntV (address:int) :: (values:(cm_value)list)) []`);
  thm target_equal = conjunct1_rule(body);
  thm pc_equal = conjunct1_rule(conjunct2_rule(body));
  thm machine = conjunct2_rule(conjunct2_rule(body));
  thm stack_length = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `CMIntV (address:int) :: (values:(cm_value)list)`,
      `[]:(int)list`), get_cm_machine_sim_stack_length()), machine);
  thm stack_nonempty = mp_rule(int_arith_rule(
      `ilength (tvm_stack (vm:tvm_state)) ==
         (1i + ilength (values:(cm_value)list)) + 0i ==>
       0i <= ilength values ==>
       1i <= ilength (tvm_stack vm)`),
      conv_rule(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))), stack_length));
  stack_nonempty = match_mp_rule(stack_nonempty,
      ispec_rule(`values:(cm_value)list`,
        get_theorem_by_name("ILENGTH_NONNEG")));
  thm head = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `CMIntV (address:int)`, `values:(cm_value)list`,
      `[]:(int)list`), cm_machine_sim_stack_head), machine);
  thm fixed = mp_rule(spec_rule(
      `address:int`, get_tower_wrap64_fixed()), assume_rule(
        `tower_signed64 (address:int)`));
  thm address_valid_reduction = apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        conjunct1_rule(head), get_cm_value_number_def(), fixed)),
      `tower_word_valid (HD (tvm_stack (vm:tvm_state)))`);
  thm address_valid = eq_mp_rule(
      sym_rule(address_valid_reduction),
      assume_rule(`tower_word_valid (address:int)`));
  term next =
      `tvm_next_state (vm:tvm_state)
        (tower_getw (tvm_mem vm) (HD (tvm_stack vm)) ::
         TL (tvm_stack vm))
        (tvm_calls vm) (tvm_mem vm)
        (tvm_input vm) (tvm_output vm)`;
  thm action = specl_rule(TERM_LIST(
      `tvm_object_code (cm_compile_model (p:cm_program))`,
      `0i:int`, `vm:tvm_state`), get_tvm_load_transition());
  action = conv_rule(reduce_rewrite_conv(THM_LIST(
      stack_nonempty, address_valid)), action);
  thm compiled_code = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_compile_model_def(), get_tvm_object_code_def(),
        pc_equal, code_at)),
      `cm_code_at
        (tvm_object_code (cm_compile_model (p:cm_program)))
        (tvm_pc (vm:tvm_state))
        (TVMInst TVMLoadOp 0i :: (rest:(tvm_inst)list))`));
  thm stepped = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `cm_compile_model (p:cm_program)`, `vm:tvm_state`,
      `TVMLoadOp:tvm_opcode`, `0i:int`,
      `rest:(tvm_inst)list`, next),
      cm_tvm_state_iter_one), compiled_code), action);
  stepped = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(target_equal))), stepped);
  thm machine_after = match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
        `cm_ann_calls (ann:cm_annotation)`,
        `fid:int`, `cm_state_fp (st:cm_src_state)`,
        `cm_ann_spills (ann:cm_annotation)`,
        `cm_ann_saved (ann:cm_annotation)`,
        `slot:int`, `spill_value:cm_value`, `address:int`,
        `values:(cm_value)list`, `[]:(int)list`),
        get_cm_machine_spill_load()),
      conv_rule(rewrite_conv(THM_LIST(
        cm_active_spill_frames_def)), machine)),
      assume_rule(
        `cm_spill_holds (slot:int) (spill_value:cm_value)
          (cm_ann_spills (ann:cm_annotation))`)),
      assume_rule(
        `(address:int) ==
         cm_state_fp (st:cm_src_state) +
           cm_temp_offset (p:cm_program) (fid:int) (slot:int)`)),
      assume_rule(`tower_signed64 (address:int)`));
  term updated =
      `cm_ann_linear [TVMInst TVMLoadOp 0i]
        (ann:cm_annotation)`;
  thm next_pc = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_tvm_next_state_def(), get_tvm_state_selectors_def(),
        cm_ann_linear_def, cm_ann_plain_def, cm_ann_pc_def,
        get_theorem_by_name("ILENGTH_DEF"), pc_equal)),
      `tvm_pc ${next:tvm_state} ==
       cm_ann_pc ${updated:cm_annotation}`));
  thm normalized_body =
      conj_rule(stepped, conj_rule(next_pc, machine_after));
  thm_list update_rules = THM_LIST(
      cm_ann_linear_def, cm_ann_plain_def,
      cm_ann_pc_def, cm_ann_calls_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_active_spill_frames_def,
      get_theorem_by_name("ILENGTH_DEF"));
  normalized_body =
      conv_rule(reduce_rewrite_conv(update_rules), normalized_body);
  term exists_goal =
      `?next_vm.
         tvm_iter 1 (target:tvm_task) ==
           TVMRunTask (cm_compile_model (p:cm_program)) next_vm &&
         tvm_pc next_vm == cm_ann_pc ${updated:cm_annotation} &&
         cm_machine_state_sim p (st:cm_src_state) next_vm
           (cm_ann_calls ${updated:cm_annotation})
           (cm_active_spill_frames (fid:int) st
             ${updated:cm_annotation})
           ((spill_value:cm_value) ::
             (values:(cm_value)list)) []`;
  dest_exists_results exists_parts = dest_exists(exists_goal);
  term instantiated_body =
      subst_one(next, exists_parts.v, exists_parts.tm);
  thm body_reduction = apply_conversion(
      reduce_rewrite_conv(update_rules), instantiated_body);
  thm adjusted_body = eq_mp_rule(
      sym_rule(body_reduction), normalized_body);
  thm witness =
      exists_rule(exists_goal, next, adjusted_body);
  thm selected =
      choose_rule(`vm:tvm_state`, expanded, witness);
  gnode opened = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(cm_running_target_sim_def)));
  ACCEPT_TAC(opened, selected);
  return gnode_prove(root);
}
PROOF thm cm_target_spill_load =
    cm_prove_target_spill_load();

PROOF static thm cm_prove_target_spill_store(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (slot:int) (address:int) (v:cm_value)
         (values:(cm_value)list) (ann:cm_annotation)
         (target:tvm_task) (rest:(tvm_inst)list).
         cm_code_at (cm_model_code p) (cm_ann_pc ann)
           (TVMInst TVMStoreOp 0i :: rest) ==>
         cm_running_target_sim p fid st
           (CMIntV address :: v :: values) ann target ==>
         cm_tagged_span_valid st ==>
         (!addr.
            cm_live_address st addr ==>
            ~(address <= addr && addr < address + 8i)) ==>
         cm_range_disjoint address 8i 8i 8i ==>
         cm_call_frames_store_safe CMIntTy address
           (cm_ann_calls ann) ==>
         cm_spill_frames_store_safe p CMIntTy address
           (cm_ann_saved ann) ==>
         address ==
           cm_state_fp st + cm_temp_offset p fid slot ==>
         tower_signed64 address ==>
         tower_word_valid address ==>
         cm_running_target_sim p fid st values
           (cm_ann_put_spill slot v
             (cm_ann_linear [TVMInst TVMStoreOp 0i] ann))
           (tvm_iter 1 target)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm code_at = assume_rule(
      `cm_code_at (cm_model_code (p:cm_program))
        (cm_ann_pc (ann:cm_annotation))
        (TVMInst TVMStoreOp 0i :: (rest:(tvm_inst)list))`);
  thm running = assume_rule(
      `cm_running_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state)
        (CMIntV (address:int) :: (v:cm_value) ::
          (values:(cm_value)list))
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
         (CMIntV (address:int) :: (v:cm_value) ::
           (values:(cm_value)list)) []`);
  thm target_equal = conjunct1_rule(body);
  thm pc_equal = conjunct1_rule(conjunct2_rule(body));
  thm machine = conjunct2_rule(conjunct2_rule(body));
  thm stack_length = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `CMIntV (address:int) :: (v:cm_value) ::
        (values:(cm_value)list)`,
      `[]:(int)list`), get_cm_machine_sim_stack_length()), machine);
  thm stack_two = mp_rule(int_arith_rule(
      `ilength (tvm_stack (vm:tvm_state)) ==
         (1i + 1i + ilength (values:(cm_value)list)) + 0i ==>
       0i <= ilength values ==>
       2i <= ilength (tvm_stack vm)`),
      conv_rule(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))), stack_length));
  stack_two = match_mp_rule(stack_two,
      ispec_rule(`values:(cm_value)list`,
        get_theorem_by_name("ILENGTH_NONNEG")));
  thm shape = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `CMIntV (address:int) :: (v:cm_value) ::
        (values:(cm_value)list)`,
      `[]:(int)list`), get_cm_machine_sim_stack_shape()), machine);
  thm address_fixed = mp_rule(spec_rule(
      `address:int`, get_tower_wrap64_fixed()), assume_rule(
        `tower_signed64 (address:int)`));
  thm head_equal = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        shape, cm_encode_values_def, get_cm_value_number_def(),
        address_fixed, get_theorem_by_name("APPEND"),
        get_theorem_by_name("HD"))),
      `HD (tvm_stack (vm:tvm_state)) == (address:int)`));
  thm second_equal = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        shape, cm_encode_values_def, get_cm_value_number_def(),
        address_fixed, get_theorem_by_name("APPEND"),
        get_theorem_by_name("TL"), get_theorem_by_name("HD"))),
      `HD (TL (tvm_stack (vm:tvm_state))) ==
       cm_value_number (st:cm_src_state) (v:cm_value)`));
  thm address_valid = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(head_equal))), assume_rule(
        `tower_word_valid (address:int)`));
  term next =
      `tvm_next_state (vm:tvm_state)
        (TL (TL (tvm_stack vm))) (tvm_calls vm)
        (tower_setw (tvm_mem vm) (HD (tvm_stack vm))
          (HD (TL (tvm_stack vm))))
        (tvm_input vm) (tvm_output vm)`;
  thm action = specl_rule(TERM_LIST(
      `tvm_object_code (cm_compile_model (p:cm_program))`,
      `0i:int`, `vm:tvm_state`), get_tvm_store_transition());
  action = conv_rule(reduce_rewrite_conv(THM_LIST(
      stack_two, address_valid)), action);
  thm compiled_code = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_compile_model_def(), get_tvm_object_code_def(),
        pc_equal, code_at)),
      `cm_code_at
        (tvm_object_code (cm_compile_model (p:cm_program)))
        (tvm_pc (vm:tvm_state))
        (TVMInst TVMStoreOp 0i :: (rest:(tvm_inst)list))`));
  thm stepped = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `cm_compile_model (p:cm_program)`, `vm:tvm_state`,
      `TVMStoreOp:tvm_opcode`, `0i:int`,
      `rest:(tvm_inst)list`, next),
      cm_tvm_state_iter_one), compiled_code), action);
  stepped = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(target_equal))), stepped);
  thm machine_after = match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(match_mp_rule(match_mp_rule(match_mp_rule(
        specl_rule(TERM_LIST(
          `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
          `cm_ann_calls (ann:cm_annotation)`,
          `fid:int`, `cm_state_fp (st:cm_src_state)`,
          `cm_ann_spills (ann:cm_annotation)`,
          `cm_ann_saved (ann:cm_annotation)`,
          `slot:int`, `address:int`, `v:cm_value`,
          `values:(cm_value)list`, `[]:(int)list`),
          get_cm_machine_spill_store()),
        conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_active_spill_frames_def)), machine)),
        assume_rule(`cm_tagged_span_valid (st:cm_src_state)`)),
        assume_rule(
          `!addr.
             cm_live_address (st:cm_src_state) addr ==>
             ~((address:int) <= addr &&
               addr < address + 8i)`)),
        assume_rule(
          `cm_range_disjoint (address:int) 8i 8i 8i`)),
        assume_rule(
          `cm_call_frames_store_safe CMIntTy (address:int)
             (cm_ann_calls (ann:cm_annotation))`)),
        assume_rule(
          `cm_spill_frames_store_safe (p:cm_program) CMIntTy
             (address:int) (cm_ann_saved (ann:cm_annotation))`)),
        assume_rule(
          `(address:int) ==
           cm_state_fp (st:cm_src_state) +
             cm_temp_offset (p:cm_program) (fid:int) (slot:int)`));
  machine_after = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(head_equal), sym_rule(second_equal))), machine_after);
  term updated =
      `cm_ann_put_spill (slot:int) (v:cm_value)
        (cm_ann_linear [TVMInst TVMStoreOp 0i]
          (ann:cm_annotation))`;
  thm_list update_rules = THM_LIST(
      cm_ann_put_spill_def, cm_ann_spills_set_def,
      cm_ann_linear_def, cm_ann_plain_def,
      cm_ann_pc_def, cm_ann_temp_def,
      cm_ann_break_def, cm_ann_continue_def,
      cm_ann_cursors_def, cm_ann_calls_def,
      cm_ann_spills_def, cm_ann_saved_def,
      cm_active_spill_frames_def,
      get_theorem_by_name("ILENGTH_DEF"));
  thm_list pc_rules = (thm_list)vector_copy(update_rules);
  vector_add(&pc_rules, get_tvm_next_state_def());
  vector_add(&pc_rules, get_tvm_state_selectors_def());
  vector_add(&pc_rules, pc_equal);
  thm next_pc = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(pc_rules),
      `tvm_pc ${next:tvm_state} ==
       cm_ann_pc ${updated:cm_annotation}`));
  thm normalized_body =
      conj_rule(stepped, conj_rule(next_pc, machine_after));
  normalized_body =
      conv_rule(reduce_rewrite_conv(update_rules), normalized_body);
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
  term instantiated_body =
      subst_one(next, exists_parts.v, exists_parts.tm);
  thm body_reduction = apply_conversion(
      reduce_rewrite_conv(update_rules), instantiated_body);
  thm adjusted_body = eq_mp_rule(
      sym_rule(body_reduction), normalized_body);
  thm witness =
      exists_rule(exists_goal, next, adjusted_body);
  thm selected =
      choose_rule(`vm:tvm_state`, expanded, witness);
  gnode opened = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(cm_running_target_sim_def)));
  ACCEPT_TAC(opened, selected);
  return gnode_prove(root);
}
PROOF thm cm_target_spill_store =
    cm_prove_target_spill_store();

PROOF static thm cm_prove_target_halt(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (v:cm_value) (ann:cm_annotation) (target:tvm_task)
         (rest:(tvm_inst)list).
         cm_code_at (cm_model_code p) (cm_ann_pc ann)
           (TVMInst TVMHaltOp 0i :: rest) ==>
         cm_running_target_sim p fid st [v] ann target ==>
         tower_byte_value (cm_value_number st v) ==>
         cm_halted_target_sim p fid st (cm_value_number st v) T
           ann (tvm_iter 1 target)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm code_at = assume_rule(
      `cm_code_at (cm_model_code (p:cm_program))
        (cm_ann_pc (ann:cm_annotation))
        (TVMInst TVMHaltOp 0i :: (rest:(tvm_inst)list))`);
  thm running = assume_rule(
      `cm_running_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state) [v:cm_value]
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
         [v:cm_value] []`);
  thm target_equal = conjunct1_rule(body);
  thm pc_equal = conjunct1_rule(conjunct2_rule(body));
  thm machine = conjunct2_rule(conjunct2_rule(body));
  thm stack_length = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `[v:cm_value]:(cm_value)list`, `[]:(int)list`),
      get_cm_machine_sim_stack_length()), machine);
  thm stack_nonempty = mp_rule(int_arith_rule(
      `ilength (tvm_stack (vm:tvm_state)) == 1i ==>
       1i <= ilength (tvm_stack vm)`),
      conv_rule(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))), stack_length));
  thm head = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
      `cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (fid:int) st ann`,
      `v:cm_value`, `[]:(cm_value)list`, `[]:(int)list`),
      get_cm_machine_sim_stack_head()), machine);
  term next =
      `TVMState (tvm_pc (vm:tvm_state)) (TL (tvm_stack vm))
        (tvm_calls vm) (tvm_mem vm)
        (tvm_input vm) (tvm_output vm)`;
  thm action = specl_rule(TERM_LIST(
      `tvm_object_code (cm_compile_model (p:cm_program))`,
      `0i:int`, `vm:tvm_state`), get_tvm_halt_transition());
  action = conv_rule(reduce_rewrite_conv(THM_LIST(
      stack_nonempty, conjunct1_rule(head),
      assume_rule(
        `tower_byte_value
          (cm_value_number (st:cm_src_state) (v:cm_value))`))),
      action);
  thm compiled_code = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_compile_model_def(), get_tvm_object_code_def(),
        pc_equal, code_at)),
      `cm_code_at
        (tvm_object_code (cm_compile_model (p:cm_program)))
        (tvm_pc (vm:tvm_state))
        (TVMInst TVMHaltOp 0i :: (rest:(tvm_inst)list))`));
  thm stepped = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `cm_compile_model (p:cm_program)`, `vm:tvm_state`,
      `TVMHaltOp:tvm_opcode`, `0i:int`, `rest:(tvm_inst)list`,
      next, `cm_value_number (st:cm_src_state) (v:cm_value)`),
      cm_tvm_halt_iter_one), compiled_code), action);
  stepped = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(target_equal))), stepped);
  thm machine_after = match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `st:cm_src_state`, `vm:tvm_state`,
        `cm_ann_calls (ann:cm_annotation)`,
        `cm_active_spill_frames (fid:int) st ann`,
        `[v:cm_value]:(cm_value)list`, `[]:(cm_value)list`,
        `[]:(int)list`, `tvm_pc (vm:tvm_state)`,
        `TL (tvm_stack (vm:tvm_state))`),
        get_cm_machine_sim_restack()),
      machine), conjunct2_rule(head));
  thm next_pc = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_tvm_state_selectors_def(), pc_equal)),
      `tvm_pc ${next:tvm_state} ==
       cm_ann_pc (ann:cm_annotation)`));
  thm normalized_body =
      conj_rule(stepped, conj_rule(next_pc, machine_after));
  thm_list update_rules = THM_LIST(
      cm_halted_target_sim_def, cm_active_spill_frames_def);
  normalized_body =
      conv_rule(reduce_rewrite_conv(update_rules), normalized_body);
  term exists_goal =
      `?next_vm.
         tvm_iter 1 (target:tvm_task) ==
           TVMDoneTask (next_vm:tvm_state)
             (cm_value_number (st:cm_src_state) (v:cm_value)) 0i &&
         tvm_pc next_vm == cm_ann_pc (ann:cm_annotation) &&
         cm_machine_state_sim p st next_vm
           (cm_ann_calls ann)
           (cm_active_spill_frames (fid:int) st ann) [] []`;
  dest_exists_results exists_parts = dest_exists(exists_goal);
  term instantiated_body =
      subst_one(next, exists_parts.v, exists_parts.tm);
  thm body_reduction = apply_conversion(
      reduce_rewrite_conv(update_rules), instantiated_body);
  thm adjusted_body = eq_mp_rule(
      sym_rule(body_reduction), normalized_body);
  thm witness =
      exists_rule(exists_goal, next, adjusted_body);
  thm selected =
      choose_rule(`vm:tvm_state`, expanded, witness);
  conv halt_normalize = reduce_rewrite_conv(THM_LIST(
      cm_halted_target_sim_def, cm_active_spill_frames_def));
  gnode opened = CONV_TAC(leaf, halt_normalize);
  selected = conv_rule(halt_normalize, selected);
  ACCEPT_TAC(opened, selected);
  return gnode_prove(root);
}
PROOF thm cm_target_halt = cm_prove_target_halt();

PROOF static thm cm_prove_target_revalue(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (old_value:cm_value) (new_value:cm_value)
         (values:(cm_value)list) (ann:cm_annotation)
         (target:tvm_task).
         cm_value_number st old_value ==
           cm_value_number st new_value ==>
         cm_running_target_sim p fid st
           (old_value :: values) ann target ==>
         cm_running_target_sim p fid st
           (new_value :: values) ann target`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm number_equal = assume_rule(
      `cm_value_number (st:cm_src_state) (old_value:cm_value) ==
       cm_value_number st (new_value:cm_value)`);
  thm old_sim = assume_rule(
      `cm_running_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state)
        ((old_value:cm_value) :: (values:(cm_value)list))
        (ann:cm_annotation) (target:tvm_task)`);
  thm_list rules = THM_LIST(
      cm_running_target_sim_def, cm_machine_state_sim_def,
      cm_operand_suffix_sim_def, cm_encode_values_def,
      number_equal, get_theorem_by_name("APPEND"));
  thm normalized = conv_rule(reduce_rewrite_conv(rules), old_sim);
  thm target_view =
      apply_conversion(reduce_rewrite_conv(rules), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), normalized));
  return gnode_prove(root);
}

PROOF thm cm_target_revalue = cm_prove_target_revalue();


PROOF thm get_cm_target_push(void) { return cm_target_push; }
PROOF thm get_cm_target_getc(void) { return cm_target_getc; }
PROOF thm get_cm_target_load(void) { return cm_target_load; }
PROOF thm get_cm_target_pop(void) { return cm_target_pop; }
PROOF thm get_cm_target_dup(void) { return cm_target_dup; }
PROOF thm get_cm_target_swap(void) { return cm_target_swap; }
PROOF thm get_cm_target_putc(void) { return cm_target_putc; }
PROOF thm get_cm_target_puti(void) { return cm_target_puti; }
PROOF thm get_cm_target_halt(void) { return cm_target_halt; }
PROOF thm get_cm_target_reannotate(void) {
  return cm_target_reannotate;
}
PROOF thm get_cm_target_halted_reannotate(void) {
  return cm_target_halted_reannotate;
}
PROOF thm get_cm_target_halted_deactivate(void) {
  return cm_target_halted_deactivate;
}
PROOF thm get_cm_target_binary_total(void) {
  return cm_target_binary_total;
}
PROOF thm get_cm_target_binary_nonzero(void) {
  return cm_target_binary_nonzero;
}
PROOF thm get_cm_target_jump(void) { return cm_target_jump; }
PROOF thm get_cm_target_jz(void) { return cm_target_jz; }
PROOF thm get_cm_target_jnz(void) { return cm_target_jnz; }
PROOF thm get_cm_target_load_fp(void) {
  return cm_target_load_fp;
}
PROOF thm get_cm_target_spill_load(void) {
  return cm_target_spill_load;
}
PROOF thm get_cm_target_spill_store(void) {
  return cm_target_spill_store;
}
PROOF thm get_cm_target_revalue(void) {
  return cm_target_revalue;
}



PROOF static int cmc_preservation_target_machine_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_machine_axioms_before,
      "cmc_preservation_target_machine introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_machine_checks =
    cmc_preservation_target_machine_final_checks();
