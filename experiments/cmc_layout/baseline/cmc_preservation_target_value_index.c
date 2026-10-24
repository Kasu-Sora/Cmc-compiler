#include "proof/proof.h"
#include "userlib/proof.h"
#include "cmc_preservation_target_value_index.h"
#include "cmc_preservation_target_value_binary.h"
#include "cmc_preservation_target_machine.h"
#include "cmc_preservation_code_value.h"
#include "cmc_preservation_target_spill_runtime.h"
#include "cmc_preservation_code_expr.h"
#include "cmc_preservation_target_spill.h"

#require "cmc_preservation_target_value_binary.c"

PROOF static size_t _cmc_preservation_target_value_index_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_target_index_code_suffix(
    const thm current_code, const term code,
    const term current_ann, const term prefix,
    const term suffix, const term next_ann,
    const thm_list rules) {
  thm current_normal =
      conv_rule(reduce_rewrite_conv(rules), current_code);
  thm tail_rule = ispecl_rule(TERM_LIST(
      code, `cm_ann_pc ${current_ann:cm_annotation}`,
      prefix, suffix), get_cm_code_at_append_right());
  thm tail_raw = mp_rule(
      conv_rule(reduce_rewrite_conv(rules), tail_rule),
      current_normal);
  thm tail_normal =
      conv_rule(reduce_rewrite_conv(rules), tail_raw);
  thm tail_view = apply_conversion(
      reduce_rewrite_conv(rules),
      `cm_code_at ${code:(tvm_inst)list}
        (cm_ann_pc ${next_ann:cm_annotation})
        ${suffix:(tvm_inst)list}`);
  return eq_mp_rule(sym_rule(tail_view), tail_normal);
}

PROOF static thm cm_prove_target_v_index_left_step(void) {
  term task =
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
        (st:cm_src_state)
        (CMIndexLK (index:cm_expr) (ty:cm_type) ::
         cm_cursor_frames (rest:(cm_acursor)list))`;
  term ann =
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
        (CMACursor (CAIndexLP (index:cm_expr) (ty:cm_type))
          (owner:int) (saved_break:int) (saved_continue:int) ::
         (rest:(cm_acursor)list))
        (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`;
  term body = imp_chain(TERM_LIST(
      `cm_task_layout (p:cm_program) ${task:cm_task} ${ann:cm_annotation}`,
      `cm_task_target_sim (p:cm_program) ${task:cm_task}
        (target:tvm_task) ${ann:cm_annotation}`,
      `cm_runtime_stack p (cm_state_regions (st:cm_src_state)) (fid:int)
        (cm_state_fp st) (cm_state_regions st)
        (CMACursor (CAIndexLP (index:cm_expr) (ty:cm_type))
          (owner:int) (saved_break:int) (saved_continue:int) ::
         (rest:(cm_acursor)list))
        (cm_spill_put owner (v:cm_value) (spills:(cm_spill)list))
        (saved:(cm_spill_frame)list) (calls:(cm_call_sim_frame)list)`,
      `0i <= (fid:int)`, `(temp:int) == (owner:int)`,
      `cm_tagged_span_valid (st:cm_src_state)`,
      `tower_signed64 (cm_state_fp (st:cm_src_state))`,
      `tower_signed64 (cm_temp_offset (p:cm_program) fid owner)`,
      `(address:int) == cm_state_fp st + cm_temp_offset p fid owner`,
      `tower_signed64 (address:int)`, `tower_word_valid (address:int)`),
      `cm_task_target_sim (p:cm_program)
        (cm_step ${task:cm_task})
        (tvm_iter
          (cm_update_steps
            (cm_annotation_step ${task:cm_task} ${ann:cm_annotation}))
          (target:tvm_task))
        (cm_update_annotation
          (cm_annotation_step ${task:cm_task} ${ann:cm_annotation}))`);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm layout = assume_rule(
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`);
  thm code_at = conjunct1_rule(conv_rule(
      reduce_rewrite_conv(cm_v_layout_rules()), layout));
  thm running = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_target_sim_def)), assume_rule(
        `cm_task_target_sim (p:cm_program) ${task:cm_task}
          (target:tvm_task) ${ann:cm_annotation}`));
  term code_rest =
      `cm_emit_rvalue (p:cm_program) (fid:int)
         ((pc:int) + 5i) ((owner:int) + 1i) (index:cm_expr) ++
       cm_index_tail_code p fid (ty:cm_type) owner ++
       cm_cursor_code p fid
         ((pc:int) + 5i + cm_rvalue_code_count p fid index + 8i)
         owner F (rest:(cm_acursor)list)`;
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`, `owner:int`,
      `v:cm_value`, `[]:(cm_value)list`, ann, `target:tvm_task`,
      code_rest, `address:int`), get_cm_target_temp_store_runtime());
  thm_list target_rules = cm_v_layout_rules();
  vector_add(&target_rules, cm_active_spill_frames_def);
  vector_add(&target_rules, get_theorem_by_name("APPEND"));
  vector_add(&target_rules, get_theorem_by_name("APPEND_NIL"));
  vector_add(&target_rules, cm_index_tail_code_def);
  vector_add(&target_rules, get_cm_layout_index_tail_length());
  vector_add(&target_rules, int_ring_rule(
      `!(a:int) (b:int). a + 5i + b + 8i == a + (5i + b + 8i)`));
  code_at = conv_rule(reduce_rewrite_conv(target_rules), code_at);
  result = conv_rule(reduce_rewrite_conv(target_rules), result);
  result = match_mp_rule(result, code_at);
  result = match_mp_rule(result, running);
  result = match_mp_rule(result, conv_rule(
      reduce_rewrite_conv(target_rules), assume_rule(
        `cm_runtime_stack (p:cm_program)
          (cm_state_regions (st:cm_src_state)) (fid:int)
          (cm_state_fp st) (cm_state_regions st)
          (CMACursor (CAIndexLP (index:cm_expr) (ty:cm_type))
            (owner:int) (saved_break:int) (saved_continue:int) ::
           (rest:(cm_acursor)list))
          (cm_spill_put owner (v:cm_value) (spills:(cm_spill)list))
          (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list)`)));
  result = match_mp_rule(result, assume_rule(`0i <= (fid:int)`));
  result = match_mp_rule(result,
      assume_rule(`cm_tagged_span_valid (st:cm_src_state)`));
  result = match_mp_rule(result, assume_rule(
      `tower_signed64 (cm_state_fp (st:cm_src_state))`));
  result = match_mp_rule(result, assume_rule(
      `tower_signed64
        (cm_temp_offset (p:cm_program) (fid:int) (owner:int))`));
  result = match_mp_rule(result, assume_rule(
      `(address:int) == cm_state_fp (st:cm_src_state) +
        cm_temp_offset (p:cm_program) (fid:int) (owner:int)`));
  result = match_mp_rule(result,
      assume_rule(`tower_signed64 (address:int)`));
  result = match_mp_rule(result,
      assume_rule(`tower_word_valid (address:int)`));
  term stored_ann =
      `cm_ann_put_spill (owner:int) (v:cm_value)
        (cm_ann_linear
          (cm_temp_store_code (p:cm_program) (fid:int) owner)
          ${ann:cm_annotation})`;
  term next_ann =
      `cm_ann_put_spill (owner:int) (v:cm_value)
        (cm_ann_replace (CAIndexRP (v:cm_value) (ty:cm_type))
          ((pc:int) +
           ilength (cm_temp_store_code (p:cm_program) (fid:int) owner))
          ((owner:int) + 1i) (breakpc:int) (continuepc:int)
          ${ann:cm_annotation})`;
  thm reannotated = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `[]:(cm_value)list`, stored_ann, next_ann,
      `tvm_iter 5 (target:tvm_task)`), get_cm_target_reannotate());
  thm_list ann_rules = THM_LIST(
      cm_ann_linear_def, cm_ann_plain_def, cm_ann_replace_def,
      cm_ann_put_spill_def, cm_ann_spills_set_def, cm_spill_put_def,
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def,
      cm_ann_calls_def, cm_ann_spills_def, cm_ann_saved_def,
      get_theorem_by_name("ILENGTH_DEF"));
  for (size_t index = 0; index < 4; ++index) {
    reannotated = match_mp_rule(reannotated,
        eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(ann_rules),
          dest_imp(concl(reannotated)).tm1)));
  }
  reannotated = conv_rule(
      reduce_rewrite_conv(ann_rules), reannotated);
  reannotated = conv_rule(
      reduce_rewrite_conv(ann_rules), reannotated);
  result = conv_rule(reduce_rewrite_conv(ann_rules), result);
  result = conv_rule(reduce_rewrite_conv(ann_rules), result);
  result = match_mp_rule(reannotated, result);
  thm_list finish_rules = cm_v_layout_rules();
  vector_add(&finish_rules, cm_update_steps_def);
  vector_add(&finish_rules, cm_task_target_sim_def);
  vector_add(&finish_rules, cm_active_spill_frames_def);
  vector_add(&finish_rules, cm_ann_linear_def);
  vector_add(&finish_rules, cm_ann_plain_def);
  vector_add(&finish_rules, cm_ann_replace_def);
  vector_add(&finish_rules, cm_ann_put_spill_def);
  vector_add(&finish_rules, cm_ann_spills_set_def);
  vector_add(&finish_rules, cm_code_steps_def);
  vector_add(&finish_rules, get_cm_layout_temp_store_length());
  vector_add(&finish_rules, assume_rule(`(temp:int) == (owner:int)`));
  gnode reduced = CONV_TAC(
      leaf, reduce_rewrite_conv(finish_rules));
  reduced = CONV_TAC(reduced, rewrite_conv(THM_LIST(
      spec_rule(`5:num`, get_theorem_by_name("NUM_OF_INT_OF_NUM")))));
  reduced = CONV_TAC(
      reduced, reduce_rewrite_conv(finish_rules));
  thm normalized = conv_rule(
      reduce_rewrite_conv(finish_rules), result);
  normalized = conv_rule(
      reduce_rewrite_conv(finish_rules), normalized);
  ACCEPT_TAC(reduced, normalized);
  return gnode_prove(root);
}

PROOF thm cm_target_v_index_left_step =
    cm_prove_target_v_index_left_step();

PROOF thm get_cm_target_v_index_left_step(void) {
  return cm_target_v_index_left_step;
}

PROOF static thm cm_prove_tower_add_commutative(void) {
  gnode root = gnode_new_with_ccl(
      `!(x:int) (y:int). tower_add x y == tower_add y x`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      get_tower_add_def(),
      int_ring_rule(`!(x:int) (y:int). x + y == y + x`))));
  return gnode_prove(root);
}
PROOF static thm cm_tower_add_commutative =
    cm_prove_tower_add_commutative();

PROOF static thm cm_prove_target_v_index_right_step(void) {
  term scale =
      `cm_type_size (cm_program_structs (p:cm_program)) (ty:cm_type)`;
  term product =
      `tower_mul (cm_value_number (st:cm_src_state) (v:cm_value))
        ${scale:int}`;
  term result_value =
      `cm_ptr_add (cm_program_structs (p:cm_program))
        (base:cm_value)
        (cm_value_number (st:cm_src_state) (v:cm_value))`;
  term task =
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
        (st:cm_src_state)
        (CMIndexRK (base:cm_value) (ty:cm_type) ::
         cm_cursor_frames (rest:(cm_acursor)list))`;
  term ann =
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
        (CMACursor (CAIndexRP (base:cm_value) (ty:cm_type))
          (owner:int) (saved_break:int) (saved_continue:int) ::
         (rest:(cm_acursor)list))
        (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`;
  term body = imp_chain(TERM_LIST(
      `cm_task_layout (p:cm_program) ${task:cm_task} ${ann:cm_annotation}`,
      `cm_task_target_sim (p:cm_program) ${task:cm_task}
        (target:tvm_task) ${ann:cm_annotation}`,
      `cm_ptr_shift_ok (cm_program_structs (p:cm_program))
        (base:cm_value)
        (cm_value_number (st:cm_src_state) (v:cm_value)) st`,
      `cm_pointer_live (st:cm_src_state) (base:cm_value)`,
      `(cm_ptr_view (base:cm_value)) == (ty:cm_type)`,
      `cm_spill_holds (owner:int) (base:cm_value)
        (spills:(cm_spill)list)`,
      `tower_signed64 ${scale:int}`,
      `tower_signed64 (cm_state_fp (st:cm_src_state))`,
      `tower_signed64
        (cm_temp_offset (p:cm_program) (fid:int) (owner:int))`,
      `(address:int) == cm_state_fp st + cm_temp_offset p fid owner`,
      `tower_signed64 (address:int)`, `tower_word_valid (address:int)`),
      `cm_task_target_sim (p:cm_program)
        (cm_step ${task:cm_task})
        (tvm_iter
          (cm_update_steps
            (cm_annotation_step ${task:cm_task} ${ann:cm_annotation}))
          (target:tvm_task))
        (cm_update_annotation
          (cm_annotation_step ${task:cm_task} ${ann:cm_annotation}))`);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm layout = assume_rule(
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`);
  thm code_at = conjunct1_rule(conv_rule(
      reduce_rewrite_conv(cm_v_layout_rules()), layout));
  thm running = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_target_sim_def)), assume_rule(
        `cm_task_target_sim (p:cm_program) ${task:cm_task}
          (target:tvm_task) ${ann:cm_annotation}`));
  term continuation =
      `cm_cursor_code (p:cm_program) (fid:int) ((pc:int) + 8i)
        (owner:int) F (rest:(cm_acursor)list)`;
  term after_push =
      `TVMInst TVMMulOp 0i ::
       cm_temp_load_code (p:cm_program) (fid:int) (owner:int) ++
       TVMInst TVMAddOp 0i ::
       ${continuation:(tvm_inst)list}`;
  thm_list rules = cm_v_layout_rules();
  vector_add(&rules, cm_index_tail_code_def);
  vector_add(&rules, cm_active_spill_frames_def);
  vector_add(&rules, cm_ann_linear_def);
  vector_add(&rules, cm_ann_plain_def);
  vector_add(&rules, cm_ann_pc_def);
  vector_add(&rules, cm_ann_temp_def);
  vector_add(&rules, cm_ann_break_def);
  vector_add(&rules, cm_ann_continue_def);
  vector_add(&rules, cm_ann_cursors_def);
  vector_add(&rules, cm_ann_spills_def);
  vector_add(&rules, cm_ann_saved_def);
  vector_add(&rules, cm_ann_calls_def);
  vector_add(&rules, get_cm_push_code_def());
  vector_add(&rules, get_theorem_by_name("APPEND"));
  vector_add(&rules, get_theorem_by_name("APPEND_NIL"));
  vector_add(&rules, get_theorem_by_name("ILENGTH_DEF"));
  code_at = conv_rule(reduce_rewrite_conv(rules), code_at);
  thm pushed = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `[v:cm_value]:(cm_value)list`, ann, `target:tvm_task`,
      `CMIntV ${scale:int}`, scale, after_push), get_cm_target_push());
  pushed = conv_rule(reduce_rewrite_conv(rules), pushed);
  pushed = match_mp_rule(pushed, code_at);
  pushed = match_mp_rule(pushed, running);
  thm scale_fixed = mp_rule(
      spec_rule(scale, get_tower_wrap64_fixed()),
      assume_rule(`tower_signed64 ${scale:int}`));
  pushed = match_mp_rule(pushed, eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_value_number_def(), scale_fixed)),
      `tower_wrap64 ${scale:int} ==
       cm_value_number (st:cm_src_state) (CMIntV ${scale:int})`)));

  term push_ann =
      `cm_ann_linear [TVMInst TVMPushOp ${scale:int}]
        ${ann:cm_annotation}`;
  thm mul_code = cm_target_index_code_suffix(
      code_at, `cm_model_code (p:cm_program)`, ann,
      `[TVMInst TVMPushOp ${scale:int}]:(tvm_inst)list`,
      after_push, push_ann, rules);
  mul_code = conv_rule(reduce_rewrite_conv(rules), mul_code);
  thm multiplied = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `CMIntV ${scale:int}`, `v:cm_value`,
      `[]:(cm_value)list`, push_ann,
      `tvm_iter 1 (target:tvm_task)`, `TVMMulOp:tvm_opcode`,
      `tower_mul:int->int->int`, `CMIntV ${product:int}`,
      `cm_temp_load_code (p:cm_program) (fid:int) (owner:int) ++
       TVMInst TVMAddOp 0i ::
       ${continuation:(tvm_inst)list}`),
      get_cm_target_binary_total());
  multiplied = match_mp_rule(multiplied, get_tvm_mul_transition());
  multiplied = conv_rule(reduce_rewrite_conv(rules), multiplied);
  multiplied = match_mp_rule(multiplied, mul_code);
  pushed = conv_rule(reduce_rewrite_conv(rules), pushed);
  multiplied = match_mp_rule(multiplied, pushed);
  multiplied = match_mp_rule(multiplied,
      eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_value_number_def(), get_tower_mul_def(),
          get_tower_wrap64_idempotent(), scale_fixed)),
        `tower_mul
            (cm_value_number (st:cm_src_state) (v:cm_value))
            (cm_value_number st (CMIntV ${scale:int})) ==
         cm_value_number st (CMIntV ${product:int})`)));
  thm iter_two = specl_rule(TERM_LIST(
      `1:num`, `1:num`, `target:tvm_task`), get_cm_tvm_iter_add());
  multiplied = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(iter_two),
      apply_conversion(get_conversion_by_name("NUM_REDUCE_CONV"),
        `(1:num) + 1`))), multiplied);

  term mul_ann =
      `cm_ann_linear [TVMInst TVMMulOp 0i] ${push_ann:cm_annotation}`;
  term load_suffix =
      `cm_temp_load_code (p:cm_program) (fid:int) (owner:int) ++
       TVMInst TVMAddOp 0i :: ${continuation:(tvm_inst)list}`;
  thm load_code = cm_target_index_code_suffix(
      code_at, `cm_model_code (p:cm_program)`, ann,
      `[TVMInst TVMPushOp ${scale:int};
        TVMInst TVMMulOp 0i]:(tvm_inst)list`,
      load_suffix, mul_ann, rules);
  load_code = conv_rule(reduce_rewrite_conv(rules), load_code);
  thm loaded = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`, `owner:int`,
      `base:cm_value`, `[CMIntV ${product:int}]:(cm_value)list`,
      mul_ann, `tvm_iter 2 (target:tvm_task)`,
      `TVMInst TVMAddOp 0i :: ${continuation:(tvm_inst)list}`,
      `address:int`), get_cm_target_temp_load());
  loaded = conv_rule(reduce_rewrite_conv(rules), loaded);
  loaded = match_mp_rule(loaded, load_code);
  loaded = match_mp_rule(loaded, multiplied);
  loaded = match_mp_rule(loaded, assume_rule(
      `cm_spill_holds (owner:int) (base:cm_value)
        (spills:(cm_spill)list)`));
  loaded = match_mp_rule(loaded, assume_rule(
      `tower_signed64 (cm_state_fp (st:cm_src_state))`));
  loaded = match_mp_rule(loaded, assume_rule(
      `tower_signed64
        (cm_temp_offset (p:cm_program) (fid:int) (owner:int))`));
  loaded = match_mp_rule(loaded, assume_rule(
      `(address:int) == cm_state_fp (st:cm_src_state) +
        cm_temp_offset (p:cm_program) (fid:int) (owner:int)`));
  loaded = match_mp_rule(loaded,
      assume_rule(`tower_signed64 (address:int)`));
  loaded = match_mp_rule(loaded,
      assume_rule(`tower_word_valid (address:int)`));
  thm iter_seven = specl_rule(TERM_LIST(
      `2:num`, `5:num`, `target:tvm_task`), get_cm_tvm_iter_add());
  loaded = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(iter_seven),
      apply_conversion(get_conversion_by_name("NUM_REDUCE_CONV"),
        `(2:num) + 5`))), loaded);

  term load_ann =
      `cm_ann_linear
        (cm_temp_load_code (p:cm_program) (fid:int) (owner:int))
        ${mul_ann:cm_annotation}`;
  thm add_code = cm_target_index_code_suffix(
      code_at, `cm_model_code (p:cm_program)`, ann,
      `[TVMInst TVMPushOp ${scale:int};
        TVMInst TVMMulOp 0i] ++
       cm_temp_load_code p fid (owner:int)`,
      `TVMInst TVMAddOp 0i :: ${continuation:(tvm_inst)list}`,
      load_ann, rules);
  add_code = conv_rule(reduce_rewrite_conv(rules), add_code);
  thm added = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `base:cm_value`, `CMIntV ${product:int}`,
      `[]:(cm_value)list`, load_ann,
      `tvm_iter 7 (target:tvm_task)`, `TVMAddOp:tvm_opcode`,
      `tower_add:int->int->int`, result_value, continuation),
      get_cm_target_binary_total());
  added = match_mp_rule(added, get_tvm_add_transition());
  added = conv_rule(reduce_rewrite_conv(rules), added);
  added = match_mp_rule(added, add_code);
  loaded = conv_rule(reduce_rewrite_conv(rules), loaded);
  added = match_mp_rule(added, loaded);
  thm ptr_bridge = mp_rule(specl_rule(TERM_LIST(
      `cm_program_structs (p:cm_program)`, `base:cm_value`,
      `cm_value_number (st:cm_src_state) (v:cm_value)`,
      `st:cm_src_state`),
      get_cm_ptr_add_number_bridge()), assume_rule(
        `cm_pointer_live (st:cm_src_state) (base:cm_value)`));
  added = match_mp_rule(added,
      eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          ptr_bridge, get_cm_value_number_def(),
          get_tower_mul_def(), get_tower_wrap64_idempotent(),
          cm_tower_add_commutative,
          assume_rule(
            `(cm_ptr_view (base:cm_value)) == (ty:cm_type)`))),
        `tower_add
            (cm_value_number (st:cm_src_state)
              (CMIntV ${product:int}))
            (cm_value_number st (base:cm_value)) ==
         cm_value_number st ${result_value:cm_value}`)));
  thm iter_eight = specl_rule(TERM_LIST(
      `7:num`, `1:num`, `target:tvm_task`), get_cm_tvm_iter_add());
  added = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(iter_eight),
      apply_conversion(get_conversion_by_name("NUM_REDUCE_CONV"),
        `(7:num) + 1`))), added);

  term add_ann =
      `cm_ann_linear [TVMInst TVMAddOp 0i] ${load_ann:cm_annotation}`;
  term next_ann = `cm_ann_pop ((pc:int) + 8i) ${ann:cm_annotation}`;
  thm reannotated = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `[${result_value:cm_value}]:(cm_value)list`,
      add_ann, next_ann, `tvm_iter 8 (target:tvm_task)`),
      get_cm_target_reannotate());
  thm_list ann_rules = THM_LIST(
      cm_ann_linear_def, cm_ann_plain_def, cm_ann_pop_def,
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def,
      cm_ann_calls_def, cm_ann_spills_def, cm_ann_saved_def,
      get_cm_layout_temp_load_length(),
      get_theorem_by_name("ILENGTH_DEF"),
      int_ring_rule(`!(a:int). a + 8i == (((a + 1i) + 1i) + 5i) + 1i`));
  for (size_t index = 0; index < 4; ++index) {
    reannotated = match_mp_rule(reannotated,
        eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(ann_rules),
          dest_imp(concl(reannotated)).tm1)));
  }
  reannotated = conv_rule(
      reduce_rewrite_conv(ann_rules), reannotated);
  added = conv_rule(reduce_rewrite_conv(ann_rules), added);
  thm result = match_mp_rule(reannotated, added);

  thm_list finish_rules = cm_v_layout_rules();
  vector_add(&finish_rules, cm_update_steps_def);
  vector_add(&finish_rules, cm_task_target_sim_def);
  vector_add(&finish_rules, cm_active_spill_frames_def);
  vector_add(&finish_rules, cm_ann_linear_def);
  vector_add(&finish_rules, cm_ann_plain_def);
  vector_add(&finish_rules, cm_ann_pop_def);
  vector_add(&finish_rules, cm_code_steps_def);
  vector_add(&finish_rules, cm_index_tail_code_def);
  vector_add(&finish_rules, get_cm_layout_index_tail_length());
  vector_add(&finish_rules, assume_rule(
      `cm_ptr_shift_ok (cm_program_structs (p:cm_program))
        (base:cm_value)
        (cm_value_number (st:cm_src_state) (v:cm_value)) st`));
  gnode reduced = CONV_TAC(
      leaf, reduce_rewrite_conv(finish_rules));
  reduced = CONV_TAC(reduced, rewrite_conv(THM_LIST(
      spec_rule(`8:num`, get_theorem_by_name("NUM_OF_INT_OF_NUM")))));
  reduced = CONV_TAC(
      reduced, reduce_rewrite_conv(finish_rules));
  thm normalized = conv_rule(
      reduce_rewrite_conv(finish_rules), result);
  normalized = conv_rule(
      reduce_rewrite_conv(finish_rules), normalized);
  ACCEPT_TAC(reduced, normalized);
  return gnode_prove(root);
}

PROOF thm cm_target_v_index_right_step =
    cm_prove_target_v_index_right_step();

PROOF thm get_cm_target_v_index_right_step(void) {
  return cm_target_v_index_right_step;
}

PROOF static int cmc_preservation_target_value_index_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_value_index_axioms_before,
      "cmc_preservation_target_value_index introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_value_index_checks =
    cmc_preservation_target_value_index_final_checks();
