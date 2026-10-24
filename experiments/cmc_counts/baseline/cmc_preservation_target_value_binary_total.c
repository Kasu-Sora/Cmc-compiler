#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_target_value_binary_total.h"
#include "cmc_concrete_defs.h"
#include "cmc_preservation_target_value_binary.h"
#include "cmc_preservation_target_value_binary_finish.h"
#include "cmc_preservation_target_value_binary_pointer.h"
#include "cmc_preservation_target_value_code_ready.h"
#include "cmc_preservation_target_value_context.h"
#include "cmc_preservation_spill_safety.h"
#include "cmc_preservation_spill_holds_safety.h"
#include "cmc_preservation_type_value.h"
#include "cmc_preservation_type_source_v_total.h"
#include "cmc_sim_ops.h"

#require "cmc_concrete_defs.c"
#require "cmc_preservation_target_value_binary.c"
#require "cmc_preservation_target_value_binary_finish.c"
#require "cmc_preservation_target_value_binary_pointer.c"
#require "cmc_preservation_target_value_code_ready.c"
#require "cmc_preservation_target_value_context.c"
#require "cmc_preservation_spill_safety.c"
#require "cmc_preservation_spill_holds_safety.c"
#require "cmc_preservation_type_value.c"
#require "cmc_preservation_type_source_v_total.c"
#require "cmc_sim_ops.c"

PROOF static size_t _cmc_preservation_target_value_binary_total_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_binary_total_pick(thm fact, term wanted) {
  if (alpha_compare(concl(fact), wanted) == 0) return fact;
  if (!is_conj(concl(fact))) return empty_theorem;
  thm left = cm_binary_total_pick(conjunct1_rule(fact), wanted);
  if (!IS_NULL(left)) return left;
  return cm_binary_total_pick(conjunct2_rule(fact), wanted);
}

PROOF static thm cm_prove_referenced_type_size_fixed(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (ty:cm_type).
         cm_typed_program p ==>
         cm_type_refs (cm_program_structs p) ty ==>
         tower_wrap64 (cm_type_size (cm_program_structs p) ty) ==
         cm_type_size (cm_program_structs p) ty`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term size =
      `cm_type_size (cm_program_structs (p:cm_program)) (ty:cm_type)`;
  thm size_is_signed = cm_referenced_type_size_signed;
  size_is_signed = match_mp_rule(size_is_signed,
      assume_rule(`cm_typed_program (p:cm_program)`));
  size_is_signed = match_mp_rule(size_is_signed, assume_rule(
      `cm_type_refs (cm_program_structs (p:cm_program)) (ty:cm_type)`));
  ACCEPT_TAC(leaf, match_mp_rule(
      spec_rule(size, get_tower_wrap64_fixed()), size_is_signed));
  return gnode_prove(root);
}
PROOF thm cm_referenced_type_size_fixed =
    cm_prove_referenced_type_size_fixed();

PROOF static thm cm_prove_binary_total_integer_not_pointer(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type). cm_integer_type ty ==> ~cm_is_pointer ty`);
  gnode_list cases = INDUCT_TAC(root, `ty:cm_type`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    thm view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        get_cm_integer_type_def(), get_cm_is_pointer_def(),
        get_datatype_distinctness("cm_type"))), goal_ccl(cases[i]->g));
    ACCEPT_TAC(cases[i], eqt_elim_rule(view));
  }
  return gnode_prove(root);
}
PROOF static thm cm_binary_total_integer_not_pointer =
    cm_prove_binary_total_integer_not_pointer();

PROOF static thm cm_prove_binary_total_add_commutative(void) {
  gnode root = gnode_new_with_ccl(
      `!(a:int) (b:int). tower_add a b == tower_add b a`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm target_view = apply_conversion(
      rewrite_conv(THM_LIST(get_tower_add_def())), goal_ccl(leaf->g));
  struct dest_eq_results target_parts = dest_eq(rhs_of(target_view));
  thm arguments = int_ring_rule(mk_eq(
      dest_comb(target_parts.tm1).tm2,
      dest_comb(target_parts.tm2).tm2));
  thm result = mk_comb_rule(refl_rule(`tower_wrap64:int->int`), arguments);
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), result));
  return gnode_prove(root);
}
PROOF static thm cm_binary_total_add_commutative =
    cm_prove_binary_total_add_commutative();
PROOF static thm cm_prove_binary_total_gt_orientation(void) {
  gnode root = gnode_new_with_ccl(
      `!(a:int) (b:int).
         tower_bool (b < a) == tower_bool (a > b)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm relation = int_arith_rule(
      `((b:int) < (a:int)) <=> ((a:int) > (b:int))`);
  ACCEPT_TAC(leaf, beta_norm(ap_term_rule(
      `tower_bool:bool->int`, relation)));
  return gnode_prove(root);
}
PROOF static thm cm_binary_total_gt_orientation =
    cm_prove_binary_total_gt_orientation();

PROOF static thm cm_prove_binary_total_ge_orientation(void) {
  gnode root = gnode_new_with_ccl(
      `!(a:int) (b:int).
         tower_bool (b <= a) == tower_bool (a >= b)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm relation = int_arith_rule(
      `((b:int) <= (a:int)) <=> ((a:int) >= (b:int))`);
  ACCEPT_TAC(leaf, beta_norm(ap_term_rule(
      `tower_bool:bool->int`, relation)));
  return gnode_prove(root);
}
PROOF static thm cm_binary_total_ge_orientation =
    cm_prove_binary_total_ge_orientation();


PROOF static thm cm_binary_total_function_wf(
    thm typed, thm fid_lower, thm fid_upper) {
  thm typed_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_typed_program_def())), typed);
  thm all_functions = cm_binary_total_pick(typed_open,
      `!(index:int). 0i <= index ==>
         index < ilength (cm_program_functions (p:cm_program)) ==>
         cm_function_wf p (inth index (cm_program_functions p))`);
  thm result = spec_rule(`fid:int`, all_functions);
  result = match_mp_rule(result, fid_lower);
  return match_mp_rule(result, fid_upper);
}

PROOF static thm cm_binary_total_expr_refs(
    term expr, thm typed, thm function_wf, thm expr_wf) {
  thm function_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_function_wf_def())), function_wf);
  thm params_wf = cm_binary_total_pick(function_open,
      `cm_params_wf (cm_program_structs (p:cm_program))
        (cm_function_params
          (inth (fid:int) (cm_program_functions p)))`);
  thm params_slots = conjunct1_rule(conv_rule(
      rewrite_conv(THM_LIST(get_cm_params_wf_def())), params_wf));
  thm locals_slots = cm_binary_total_pick(function_open,
      `cm_slots_wf (cm_program_structs (p:cm_program))
        (cm_function_locals
          (inth (fid:int) (cm_program_functions p)))`);
  thm result = specl_rule(TERM_LIST(
      expr, `p:cm_program`,
      `inth (fid:int) (cm_program_functions (p:cm_program))`),
      cm_expr_result_refs);
  result = match_mp_rule(result, typed);
  result = match_mp_rule(result, params_slots);
  result = match_mp_rule(result, locals_slots);
  return match_mp_rule(result, expr_wf);
}

PROOF static thm cm_binary_total_scale_fixed(
    term expr, thm typed, thm expr_refs, thm pointer_kind) {
  thm pointee_refs = match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `cm_program_structs (p:cm_program)`,
        `cm_expr_type ${expr:cm_expr}`), cm_type_refs_pointee),
      expr_refs), pointer_kind);
  thm result = match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `cm_pointee (cm_expr_type ${expr:cm_expr})`),
        cm_referenced_type_size_fixed),
      typed), pointee_refs);
  term target =
      `tower_wrap64 (cm_pointer_scale (p:cm_program) ${expr:cm_expr}) ==
       cm_pointer_scale p ${expr:cm_expr}`;
  thm view = apply_conversion(rewrite_conv(THM_LIST(
      get_cm_pointer_scale_def(), pointer_kind)), target);
  return eq_mp_rule(sym_rule(view), result);
}

PROOF static thm cm_binary_total_runtime_pointer(
    term value, term ty, thm pointer_kind, thm compatible) {
  thm scalar = match_mp_rule(spec_rule(ty, cm_pointer_expr_type),
      pointer_kind);
  thm bridge = match_mp_rule(match_mp_rule(specl_rule(
      TERM_LIST(value, ty), cm_compatible_pointer_kind),
      scalar), compatible);
  return eq_mp_rule(sym_rule(bridge), pointer_kind);
}

PROOF static thm cm_binary_total_runtime_integer(
    term value, term ty, thm integer_kind, thm compatible) {
  thm scalar = match_mp_rule(spec_rule(ty, cm_integer_expr_type),
      integer_kind);
  thm bridge = match_mp_rule(match_mp_rule(specl_rule(
      TERM_LIST(value, ty), cm_compatible_pointer_kind),
      scalar), compatible);
  thm static_not = match_mp_rule(spec_rule(
      ty, cm_binary_total_integer_not_pointer), integer_kind);
  dest_iff_results bridge_parts = dest_iff(concl(bridge));
  return mp_rule(taut_rule(mk_imp(
      list_mk_conj(TERM_LIST(concl(bridge), concl(static_not))),
      mk_not(bridge_parts.tm1))), conj_rule(bridge, static_not));
}

PROOF static thm cm_binary_total_address_facts(
    thm runtime, thm held, thm fid_lower) {
  term cursors =
      `CMACursor
        (CABinRP (op:int) (left:cm_expr) (right:cm_expr)
          (left_value:cm_value) (ty:cm_type))
        (owner:int) (saved_break:int) (saved_continue:int) ::
       (rest:(cm_acursor)list)`;
  term address =
      `cm_state_fp (st:cm_src_state) +
       cm_temp_offset (p:cm_program) (fid:int) (owner:int)`;
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `cm_state_regions (st:cm_src_state)`,
      cursors, `fid:int`, `cm_state_fp (st:cm_src_state)`,
      `cm_state_regions (st:cm_src_state)`,
      `spills:(cm_spill)list`, `saved:(cm_spill_frame)list`,
      `calls:(cm_call_sim_frame)list`, `owner:int`,
      `left_value:cm_value`, address),
      get_cm_runtime_spill_holds_address_safe());
  result = match_mp_rule(result, runtime);
  result = match_mp_rule(result, held);
  result = match_mp_rule(result, fid_lower);
  return match_mp_rule(result, refl_rule(address));
}
PROOF static thm cm_binary_total_runtime_scale(
    term expr, term value, term static_type, thm compatible,
    thm pointer_kind, thm pointer_live) {
  thm static_view = specl_rule(TERM_LIST(
      `st:cm_src_state`, value, static_type), cm_pointer_view_type);
  static_view = match_mp_rule(static_view, compatible);
  static_view = match_mp_rule(static_view, pointer_kind);
  static_view = match_mp_rule(static_view, pointer_live);
  thm runtime_view = spec_rule(value, get_cm_pointer_type_view());
  thm pointees = trans_rule(runtime_view, static_view);
  thm sizes = beta_norm(ap_term_rule(
      `\(item:cm_type).
         cm_type_size (cm_program_structs (p:cm_program)) item`,
      pointees));
  term target =
      `cm_pointer_scale (p:cm_program) ${expr:cm_expr} ==
       cm_type_size (cm_program_structs p)
         (cm_pointee (cm_value_type ${value:cm_value}))`;
  thm target_view = apply_conversion(rewrite_conv(THM_LIST(
      get_cm_pointer_scale_def())), target);
  return eq_mp_rule(sym_rule(target_view), sym_rule(sizes));
}


PROOF static thm cm_prove_target_v_bin_l_jump_valid(void) {
  term task =
      `CMVTask (p:cm_program) (fid:int) (incoming:cm_value)
        (st:cm_src_state)
        (CMBinLK (op:int) (right:cm_expr) (ty:cm_type) ::
         cm_cursor_frames (rest:(cm_acursor)list))`;
  term ann =
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
        (CMACursor
          (CABinLP (op:int) (left:cm_expr) (right:cm_expr)
            (ty:cm_type))
          (owner:int) (saved_break:int) (saved_continue:int) ::
         (rest:(cm_acursor)list))
        (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`;
  term jump_pc =
      `(pc:int) + cm_rvalue_code_count (p:cm_program) (fid:int)
        (right:cm_expr) + 4i`;
  term body = imp_chain(TERM_LIST(
      `(op:int) == 0i || op == 1i`,
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`),
      `tvm_target_valid (cm_model_code (p:cm_program))
        ${jump_pc:int}`);
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm layout = assume_rule(
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`);
  gnode_list op_cases = DISJ_CASES_TAC(leaf,
      assume_rule(`(op:int) == 0i || op == 1i`), "Hop");
  for (size_t i = 0; i < vector_size(op_cases); ++i) {
    thm op_equal = assume_rule(goal_lasmps(op_cases[i]->g)[
        labeled_term_list_index(goal_lasmps(op_cases[i]->g), "Hop")].tm);
    term opcode = i == 0 ? `TVMJnzOp:tvm_opcode` : `TVMJzOp:tvm_opcode`;
    term short_value = i == 0 ? `1i:int` : `0i:int`;
    term prefix =
        `[TVMInst ${opcode:tvm_opcode} ${jump_pc:int}] ++
         cm_emit_rvalue (p:cm_program) (fid:int) ((pc:int) + 1i)
           (owner:int) (right:cm_expr) ++
         [TVMInst TVMPushOp 0i; TVMInst TVMNeOp 0i;
          TVMInst TVMJmpOp ((pc:int) +
            cm_rvalue_code_count p fid right + 5i)]`;
    term suffix =
        `cm_cursor_code (p:cm_program) (fid:int)
          ((pc:int) + cm_rvalue_code_count p fid (right:cm_expr) + 5i)
          (owner:int) F (rest:(cm_acursor)list)`;
    thm generic = specl_rule(TERM_LIST(
        `cm_model_code (p:cm_program)`, `pc:int`, prefix,
        `TVMInst TVMPushOp ${short_value:int}`, suffix),
        get_cm_code_at_suffix_head_target_valid());
    thm code_at = conjunct1_rule(conv_rule(
        reduce_rewrite_conv(cm_v_layout_rules()), layout));
    thm_list rules = cm_v_layout_rules();
    vector_add(&rules, op_equal);
    vector_add(&rules, get_theorem_by_name("APPEND"));
    vector_add(&rules, get_theorem_by_name("APPEND_NIL"));
    vector_add(&rules, gsym_rule(get_theorem_by_name("APPEND_ASSOC")));
    vector_add(&rules, int_ring_rule(
        `!(a:int) (b:int). a + 1i + b + 3i == a + b + 4i`));
    vector_add(&rules, int_ring_rule(
        `!(a:int) (b:int). a + 1i + b + 4i == a + b + 5i`));
    generic = conv_rule(reduce_rewrite_conv(rules), generic);
    generic = conv_rule(reduce_rewrite_conv(rules), generic);
    code_at = conv_rule(reduce_rewrite_conv(rules), code_at);
    code_at = conv_rule(reduce_rewrite_conv(rules), code_at);
    thm result = match_mp_rule(generic, code_at);
    thm target_view = apply_conversion(
        reduce_rewrite_conv(rules), goal_ccl(op_cases[i]->g));
    ACCEPT_TAC(op_cases[i], eq_mp_rule(sym_rule(target_view), result));
  }
  return gnode_prove(root);
}
PROOF thm cm_target_v_bin_l_jump_valid =
    cm_prove_target_v_bin_l_jump_valid();

PROOF static thm cm_prove_target_v_bin_r_end_valid(void) {
  term phase =
      `CABinRP (op:int) (left:cm_expr) (right:cm_expr)
        (left_value:cm_value) (ty:cm_type)`;
  term task =
      `CMVTask (p:cm_program) (fid:int) (incoming:cm_value)
        (st:cm_src_state)
        (CMBinRK (op:int) (left_value:cm_value) (ty:cm_type) ::
         cm_cursor_frames (rest:(cm_acursor)list))`;
  term ann =
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
        (CMACursor ${phase:cm_aphase} (owner:int) (saved_break:int)
          (saved_continue:int) :: (rest:(cm_acursor)list))
        (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`;
  term body = imp_chain(TERM_LIST(
      `(op:int) == 0i || op == 1i`,
      `cm_phase_parent_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase} (rest:(cm_acursor)list)`,
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`),
      `tvm_target_valid (cm_model_code (p:cm_program)) ((pc:int) + 4i)`);
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm layout = assume_rule(
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`);
  thm parent = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_phase_parent_type_ready_def())), assume_rule(
        `cm_phase_parent_type_ready (p:cm_program) (fid:int)
          ${phase:cm_aphase} (rest:(cm_acursor)list)`));
  gnode_list op_cases = DISJ_CASES_TAC(leaf,
      assume_rule(`(op:int) == 0i || op == 1i`), "Hop");
  for (size_t i = 0; i < vector_size(op_cases); ++i) {
    thm op_equal = assume_rule(goal_lasmps(op_cases[i]->g)[
        labeled_term_list_index(goal_lasmps(op_cases[i]->g), "Hop")].tm);
    term short_value = i == 0 ? `1i:int` : `0i:int`;
    term prefix =
        `[TVMInst TVMPushOp 0i; TVMInst TVMNeOp 0i;
          TVMInst TVMJmpOp ((pc:int) + 4i);
          TVMInst TVMPushOp ${short_value:int}]`;
    thm generic = specl_rule(TERM_LIST(
        `cm_model_code (p:cm_program)`, `p:cm_program`, `fid:int`,
        `pc:int`, `owner:int`, `ty:cm_type`, prefix,
        `rest:(cm_acursor)list`),
        get_cm_value_continuation_target_valid());
    thm code_at = conjunct1_rule(conv_rule(
        reduce_rewrite_conv(cm_v_layout_rules()), layout));
    thm_list rules = cm_v_layout_rules();
    vector_add(&rules, op_equal);
    vector_add(&rules, get_theorem_by_name("APPEND"));
    vector_add(&rules, get_theorem_by_name("APPEND_NIL"));
    vector_add(&rules, get_theorem_by_name("ILENGTH_DEF"));
    generic = conv_rule(reduce_rewrite_conv(rules), generic);
    code_at = conv_rule(reduce_rewrite_conv(rules), code_at);
    thm result = match_mp_rule(match_mp_rule(generic, code_at), parent);
    thm target_view = apply_conversion(
        reduce_rewrite_conv(rules), goal_ccl(op_cases[i]->g));
    ACCEPT_TAC(op_cases[i], eq_mp_rule(sym_rule(target_view), result));
  }
  return gnode_prove(root);
}
PROOF thm cm_target_v_bin_r_end_valid =
    cm_prove_target_v_bin_r_end_valid();


PROOF static void cm_binary_total_accept(
    gnode branch, thm_list rules, thm result) {
  thm normalized = conv_rule(reduce_rewrite_conv(rules), result);
  thm target_view = apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(branch->g));
  ACCEPT_TAC(branch, eq_mp_rule(sym_rule(target_view), normalized));
}
PROOF static thm cm_binary_total_semantic_bridge(
    thm binary_ok, thm not_both_pointers) {
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `op:int`, `left_value:cm_value`,
      `incoming:cm_value`, `ty:cm_type`, `st:cm_src_state`),
      get_cm_binary_value_number_bridge());
  result = match_mp_rule(result, binary_ok);
  return match_mp_rule(result, not_both_pointers);
}

PROOF static thm cm_binary_total_ordinary_shape(
    term opcode, thm_list branch_rules) {
  thm_list rules = THM_LIST(
      get_cm_binary_finish_code_def(), get_cm_binary_opcode_def(),
      get_theorem_by_name("APPEND"), get_theorem_by_name("APPEND_NIL"));
  for (size_t i = 0; i < vector_size(branch_rules); ++i) {
    vector_add(&rules, branch_rules[i]);
  }
  term target =
      `cm_binary_finish_code (p:cm_program) (fid:int) (op:int)
        (left:cm_expr) (right:cm_expr) (owner:int) ==
       cm_temp_load_code p fid owner ++
         [TVMInst TVMSwapOp 0i; TVMInst ${opcode:tvm_opcode} 0i]`;
  thm view = apply_conversion(reduce_rewrite_conv(rules), target);
  return eqt_elim_rule(view);
}

PROOF static thm cm_binary_total_ordinary_operation(
    term operation, thm bridge, thm_list branch_rules) {
  thm_list rules = THM_LIST(
      bridge, get_cm_binary_machine_number_def(),
      cm_binary_total_gt_orientation,
      cm_binary_total_ge_orientation);
  for (size_t i = 0; i < vector_size(branch_rules); ++i) {
    vector_add(&rules, branch_rules[i]);
  }
  term semantic_result =
      `cm_binary_value (p:cm_program) (op:int)
        (left_value:cm_value) (incoming:cm_value) (ty:cm_type)
        (st:cm_src_state)`;
  term target =
      `${operation:int->int->int}
        (cm_value_number (st:cm_src_state) (left_value:cm_value))
        (cm_value_number st (incoming:cm_value)) ==
       cm_value_number st ${semantic_result:cm_value}`;
  thm view = apply_conversion(reduce_rewrite_conv(rules), target);
  return beta_norm(eqt_elim_rule(view));
}

PROOF static thm cm_binary_total_apply_ordinary(
    bool nonzero, term opcode, term operation, thm transition,
    thm binary_ok, thm op_not_zero, thm op_not_one, thm held,
    thm temp_equal, thm shape, thm operation_equal,
    thm divisor_nonzero, thm layout, thm sim, thm address_facts) {
  thm result = nonzero
      ? get_cm_target_v_bin_r_ordinary_nonzero_step()
      : get_cm_target_v_bin_r_ordinary_total_step();
  result = match_mp_rule(result, layout);
  result = match_mp_rule(result, sim);
  result = match_mp_rule(result, binary_ok);
  result = match_mp_rule(result, op_not_zero);
  result = match_mp_rule(result, op_not_one);
  result = match_mp_rule(result, held);
  result = match_mp_rule(result, temp_equal);
  result = match_mp_rule(result, shape);
  result = match_mp_rule(result, transition);
  result = match_mp_rule(result, operation_equal);
  if (nonzero) {
    result = match_mp_rule(result, divisor_nonzero);
  }
  result = match_mp_rule(result, cm_binary_total_pick(address_facts,
      `tower_signed64 (cm_state_fp (st:cm_src_state))`));
  result = match_mp_rule(result, cm_binary_total_pick(address_facts,
      `tower_signed64
        (cm_temp_offset (p:cm_program) (fid:int) (owner:int))`));
  result = match_mp_rule(result, refl_rule(
      `cm_state_fp (st:cm_src_state) +
       cm_temp_offset (p:cm_program) (fid:int) (owner:int)`));
  result = match_mp_rule(result, cm_binary_total_pick(address_facts,
      `tower_signed64
        (cm_state_fp (st:cm_src_state) +
         cm_temp_offset (p:cm_program) (fid:int) (owner:int))`));
  return match_mp_rule(result, cm_binary_total_pick(address_facts,
      `tower_word_valid
        (cm_state_fp (st:cm_src_state) +
         cm_temp_offset (p:cm_program) (fid:int) (owner:int))`));
}


PROOF static thm cm_prove_target_v_bin_l_total_step(void) {
  term phase =
      `CABinLP (op:int) (left:cm_expr) (right:cm_expr) (ty:cm_type)`;
  term cursors =
      `CMACursor ${phase:cm_aphase} (owner:int) (saved_break:int)
        (saved_continue:int) :: (rest:(cm_acursor)list)`;
  term task =
      `CMVTask (p:cm_program) (fid:int) (incoming:cm_value)
        (st:cm_src_state)
        (CMBinLK (op:int) (right:cm_expr) (ty:cm_type) ::
         cm_cursor_frames (rest:(cm_acursor)list))`;
  term ann =
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
        ${cursors:(cm_acursor)list} (spills:(cm_spill)list)
        (saved:(cm_spill_frame)list) (calls:(cm_call_sim_frame)list)`;
  term result =
      `cm_task_target_sim (p:cm_program) (cm_step ${task:cm_task})
        (tvm_iter
          (cm_update_steps
            (cm_annotation_step ${task:cm_task} ${ann:cm_annotation}))
          (target:tvm_task))
        (cm_update_annotation
          (cm_annotation_step ${task:cm_task} ${ann:cm_annotation}))`;
  term body = imp_chain(TERM_LIST(
      `0i <= (fid:int)`,
      `cm_v_temp_ready ${ann:cm_annotation} ${phase:cm_aphase}`,
      `cm_v_spill_ready (p:cm_program) (fid:int)
        ${ann:cm_annotation} ${phase:cm_aphase}`,
      `cm_runtime_stack (p:cm_program) (cm_state_regions (st:cm_src_state))
        (fid:int) (cm_state_fp st) (cm_state_regions st)
        ${cursors:(cm_acursor)list} (spills:(cm_spill)list)
        (saved:(cm_spill_frame)list) (calls:(cm_call_sim_frame)list)`,
      `cm_tagged_span_valid (st:cm_src_state)`,
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`,
      `cm_task_target_sim (p:cm_program) ${task:cm_task}
        (target:tvm_task) ${ann:cm_annotation}`), result);
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);

  thm fid_nonnegative = assume_rule(`0i <= (fid:int)`);
  thm temp_equal = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_v_temp_ready_def, cm_phase_child_temp_def,
      cm_ann_temp_def, cm_ann_cursors_def, cm_cursor_temp_def,
      get_theorem_by_name("HD"))), assume_rule(
        `cm_v_temp_ready ${ann:cm_annotation} ${phase:cm_aphase}`));
  thm runtime = assume_rule(
      `cm_runtime_stack (p:cm_program) (cm_state_regions (st:cm_src_state))
        (fid:int) (cm_state_fp st) (cm_state_regions st)
        ${cursors:(cm_acursor)list} (spills:(cm_spill)list)
        (saved:(cm_spill_frame)list) (calls:(cm_call_sim_frame)list)`);
  thm layout = assume_rule(
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`);
  thm sim = assume_rule(
      `cm_task_target_sim (p:cm_program) ${task:cm_task}
        (target:tvm_task) ${ann:cm_annotation}`);
  thm tagged = assume_rule(`cm_tagged_span_valid (st:cm_src_state)`);

  gnode_list zero_cases =
      BOOL_CASES_TAC(introduced, `(op:int) == 0i`, "Hop_zero");
  {
    thm op_equal = assume_rule(`(op:int) == 0i`);
    thm logical = disj1_rule(op_equal, `(op:int) == 1i`);
    thm jump_valid = match_mp_rule(match_mp_rule(
        specl_rule(TERM_LIST(
          `incoming:cm_value`, `st:cm_src_state`, `temp:int`,
          `breakpc:int`, `continuepc:int`, `op:int`, `left:cm_expr`,
          `ty:cm_type`, `owner:int`, `saved_break:int`,
          `saved_continue:int`, `rest:(cm_acursor)list`,
          `spills:(cm_spill)list`, `saved:(cm_spill_frame)list`,
          `calls:(cm_call_sim_frame)list`, `pc:int`, `p:cm_program`,
          `fid:int`, `right:cm_expr`),
          get_cm_target_v_bin_l_jump_valid()), logical), layout);
    thm_list shaped = THM_LIST(op_equal);
    thm shaped_layout = conv_rule(rewrite_conv(shaped), layout);
    thm shaped_sim = conv_rule(rewrite_conv(shaped), sim);
    gnode_list truth_cases = BOOL_CASES_TAC(
        zero_cases[0],
        `cm_truth (st:cm_src_state) (incoming:cm_value)`, "Htruth");
    for (size_t i = 0; i < vector_size(truth_cases); ++i) {
      thm local = i == 0
          ? get_cm_target_v_bin_l_short_zero_step()
          : get_cm_target_v_bin_l_eval_zero_step();
      thm proved = match_mp_rule(local, shaped_layout);
      proved = match_mp_rule(proved, shaped_sim);
      proved = match_mp_rule(proved, jump_valid);
      proved = match_mp_rule(proved,
          i == 0
            ? assume_rule(
                `cm_truth (st:cm_src_state) (incoming:cm_value)`)
            : assume_rule(
                `~cm_truth (st:cm_src_state) (incoming:cm_value)`));
      proved = match_mp_rule(proved, temp_equal);
      cm_binary_total_accept(truth_cases[i], shaped, proved);
    }
  }
  {
    gnode_list one_cases = BOOL_CASES_TAC(
        zero_cases[1], `(op:int) == 1i`, "Hop_one");
    {
      thm op_equal = assume_rule(`(op:int) == 1i`);
      thm logical = disj2_rule(`(op:int) == 0i`, op_equal);
      thm jump_valid = match_mp_rule(match_mp_rule(
          specl_rule(TERM_LIST(
            `incoming:cm_value`, `st:cm_src_state`, `temp:int`,
            `breakpc:int`, `continuepc:int`, `op:int`, `left:cm_expr`,
            `ty:cm_type`, `owner:int`, `saved_break:int`,
            `saved_continue:int`, `rest:(cm_acursor)list`,
            `spills:(cm_spill)list`, `saved:(cm_spill_frame)list`,
            `calls:(cm_call_sim_frame)list`, `pc:int`, `p:cm_program`,
            `fid:int`, `right:cm_expr`),
            get_cm_target_v_bin_l_jump_valid()), logical), layout);
      thm_list shaped = THM_LIST(op_equal);
      thm shaped_layout = conv_rule(rewrite_conv(shaped), layout);
      thm shaped_sim = conv_rule(rewrite_conv(shaped), sim);
      gnode_list truth_cases = BOOL_CASES_TAC(
          one_cases[0],
          `cm_truth (st:cm_src_state) (incoming:cm_value)`, "Htruth");
      for (size_t i = 0; i < vector_size(truth_cases); ++i) {
        thm local = i == 0
            ? get_cm_target_v_bin_l_eval_one_step()
            : get_cm_target_v_bin_l_short_one_step();
        thm proved = match_mp_rule(local, shaped_layout);
        proved = match_mp_rule(proved, shaped_sim);
        proved = match_mp_rule(proved, jump_valid);
        proved = match_mp_rule(proved,
            i == 0
              ? assume_rule(
                  `cm_truth (st:cm_src_state) (incoming:cm_value)`)
              : assume_rule(
                  `~cm_truth (st:cm_src_state) (incoming:cm_value)`));
        proved = match_mp_rule(proved, temp_equal);
        cm_binary_total_accept(truth_cases[i], shaped, proved);
      }
    }
    {
      thm op_not_zero = assume_rule(`~((op:int) == 0i)`);
      thm op_not_one = assume_rule(`~((op:int) == 1i)`);
      thm spill_bounds = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_v_spill_ready_def, cm_ann_temp_def, temp_equal,
          get_cm_temp_slots_def(), op_not_zero, op_not_one)),
          assume_rule(
            `cm_v_spill_ready (p:cm_program) (fid:int)
              ${ann:cm_annotation} ${phase:cm_aphase}`));
      thm slot_nonnegative = conjunct1_rule(spill_bounds);
      thm slot_upper = conjunct2_rule(spill_bounds);
      thm runtime_put = match_mp_rule(match_mp_rule(match_mp_rule(
          match_mp_rule(specl_rule(TERM_LIST(
            `p:cm_program`, `cm_state_regions (st:cm_src_state)`,
            `fid:int`, `cm_state_fp (st:cm_src_state)`,
            cursors, `cm_state_regions (st:cm_src_state)`, `owner:int`,
            `incoming:cm_value`, `spills:(cm_spill)list`,
            `saved:(cm_spill_frame)list`,
            `calls:(cm_call_sim_frame)list`), cm_runtime_stack_spill_put),
          fid_nonnegative), slot_nonnegative), slot_upper), runtime);
      term address =
          `cm_state_fp (st:cm_src_state) +
           cm_temp_offset (p:cm_program) (fid:int) (owner:int)`;
      thm address_equal = refl_rule(address);
      thm address_facts = match_mp_rule(match_mp_rule(
          specl_rule(TERM_LIST(
            `p:cm_program`, `cm_state_regions (st:cm_src_state)`,
            cursors, `fid:int`, `cm_state_fp (st:cm_src_state)`,
            `cm_state_regions (st:cm_src_state)`,
            `spills:(cm_spill)list`, `saved:(cm_spill_frame)list`,
            `calls:(cm_call_sim_frame)list`, `owner:int`,
            `incoming:cm_value`, address),
            get_cm_runtime_spill_address_safe()),
          runtime_put), fid_nonnegative);
      address_facts = match_mp_rule(address_facts, address_equal);
      thm fp_signed = cm_binary_total_pick(address_facts,
          `tower_signed64 (cm_state_fp (st:cm_src_state))`);
      thm offset_signed = cm_binary_total_pick(address_facts,
          `tower_signed64
            (cm_temp_offset (p:cm_program) (fid:int) (owner:int))`);
      thm address_signed = cm_binary_total_pick(address_facts,
          `tower_signed64 ${address:int}`);
      thm address_valid = cm_binary_total_pick(address_facts,
          `tower_word_valid ${address:int}`);
      thm proved = get_cm_target_v_bin_l_other_step();
      proved = match_mp_rule(proved, layout);
      proved = match_mp_rule(proved, sim);
      proved = match_mp_rule(proved, runtime_put);
      proved = match_mp_rule(proved, fid_nonnegative);
      proved = match_mp_rule(proved, temp_equal);
      proved = match_mp_rule(proved,
          assume_rule(`~((op:int) == 0i)`));
      proved = match_mp_rule(proved,
          assume_rule(`~((op:int) == 1i)`));
      proved = match_mp_rule(proved, tagged);
      proved = match_mp_rule(proved, fp_signed);
      proved = match_mp_rule(proved, offset_signed);
      proved = match_mp_rule(proved, address_equal);
      proved = match_mp_rule(proved, address_signed);
      proved = match_mp_rule(proved, address_valid);
      ACCEPT_TAC(one_cases[1], proved);
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_target_v_bin_l_total_step =
    cm_prove_target_v_bin_l_total_step();
PROOF static void cm_binary_total_simple_branch(
    gnode branch, term op_test, term opcode, term operation,
    thm transition, bool nonzero, thm binary_ok, thm op_not_zero,
    thm op_not_one, thm held, thm temp_equal, thm layout, thm sim,
    thm address_facts) {
  thm op_equal = assume_rule(op_test);
  thm not_both = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(op_equal)),
      `~((op:int) == 8i &&
         cm_is_pointer (cm_value_type (left_value:cm_value)) &&
         cm_is_pointer (cm_value_type (incoming:cm_value)))`));
  thm bridge = cm_binary_total_semantic_bridge(binary_ok, not_both);
  thm_list branch_rules = THM_LIST(op_equal);
  thm shape = cm_binary_total_ordinary_shape(opcode, branch_rules);
  thm operation_equal = cm_binary_total_ordinary_operation(
      operation, bridge, branch_rules);
  thm divisor_nonzero = empty_theorem;
  if (nonzero) {
    divisor_nonzero = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_binary_ok_def(), op_equal)), binary_ok);
  }
  thm result = cm_binary_total_apply_ordinary(
      nonzero, opcode, operation, transition, binary_ok,
      op_not_zero, op_not_one, held, temp_equal, shape,
      operation_equal, divisor_nonzero, layout, sim, address_facts);
  ACCEPT_TAC(branch, result);
}

PROOF static thm cm_binary_total_apply_pointer(
    thm local, thm layout, thm sim, thm binary_ok, thm held,
    thm temp_equal, thm shape, thm scale_fixed, thm final_equal,
    thm address_facts, thm scale_nonzero) {
  thm result = match_mp_rule(local, layout);
  result = match_mp_rule(result, sim);
  result = match_mp_rule(result, binary_ok);
  result = match_mp_rule(result, held);
  result = match_mp_rule(result, temp_equal);
  result = match_mp_rule(result, shape);
  result = match_mp_rule(result, scale_fixed);
  result = match_mp_rule(result, final_equal);
  result = match_mp_rule(result, cm_binary_total_pick(address_facts,
      `tower_signed64 (cm_state_fp (st:cm_src_state))`));
  result = match_mp_rule(result, cm_binary_total_pick(address_facts,
      `tower_signed64
        (cm_temp_offset (p:cm_program) (fid:int) (owner:int))`));
  result = match_mp_rule(result, refl_rule(
      `cm_state_fp (st:cm_src_state) +
       cm_temp_offset (p:cm_program) (fid:int) (owner:int)`));
  result = match_mp_rule(result, cm_binary_total_pick(address_facts,
      `tower_signed64
        (cm_state_fp (st:cm_src_state) +
         cm_temp_offset (p:cm_program) (fid:int) (owner:int))`));
  result = match_mp_rule(result, cm_binary_total_pick(address_facts,
      `tower_word_valid
        (cm_state_fp (st:cm_src_state) +
         cm_temp_offset (p:cm_program) (fid:int) (owner:int))`));
  if (!IS_NULL(scale_nonzero)) {
    result = match_mp_rule(result, scale_nonzero);
  }
  return result;
}
PROOF static thm cm_binary_total_pointer_shape(
    term op_value, term instructions, thm_list branch_rules) {
  thm_list rules = THM_LIST(
      get_cm_binary_finish_code_def(), get_theorem_by_name("APPEND"),
      get_theorem_by_name("APPEND_NIL"));
  for (size_t i = 0; i < vector_size(branch_rules); ++i) {
    vector_add(&rules, branch_rules[i]);
  }
  term target =
      `cm_binary_finish_code (p:cm_program) (fid:int) ${op_value:int}
        (left:cm_expr) (right:cm_expr) (owner:int) ==
       cm_temp_load_code p fid owner ++ ${instructions:(tvm_inst)list}`;
  return eqt_elim_rule(
      apply_conversion(reduce_rewrite_conv(rules), target));
}

PROOF static thm cm_binary_total_pointer_final(
    term target, thm bridge, thm_list branch_rules) {
  thm_list rules = THM_LIST(
      bridge, get_cm_binary_machine_number_def(),
      get_cm_value_number_def(), get_tower_mul_def(),
      get_tower_sub_def(), get_tower_wrap64_idempotent(),
      cm_binary_total_add_commutative);
  for (size_t i = 0; i < vector_size(branch_rules); ++i) {
    vector_add(&rules, branch_rules[i]);
  }
  return eqt_elim_rule(
      apply_conversion(reduce_rewrite_conv(rules), target));
}
PROOF static void cm_binary_total_add_right_pointer(
    gnode branch, thm mode_fact, thm typed, thm function_wf,
    thm right_wf, thm left_compatible, thm right_compatible,
    thm binary_ok, thm held, thm temp_equal, thm layout, thm sim,
    thm address_facts) {
  thm op_equal = assume_rule(`(op:int) == 8i`);
  thm right_pointer = cm_binary_total_pick(mode_fact,
      `cm_is_pointer (cm_expr_type (right:cm_expr))`);
  thm left_integer = cm_binary_total_pick(mode_fact,
      `cm_integer_type (cm_expr_type (left:cm_expr))`);
  thm runtime_right = cm_binary_total_runtime_pointer(
      `incoming:cm_value`, `cm_expr_type (right:cm_expr)`,
      right_pointer, right_compatible);
  thm runtime_left_not = cm_binary_total_runtime_integer(
      `left_value:cm_value`, `cm_expr_type (left:cm_expr)`,
      left_integer, left_compatible);
  thm shaped_binary = conv_rule(
      rewrite_conv(THM_LIST(op_equal)), binary_ok);
  thm safe = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_binary_ok_def(), runtime_left_not, runtime_right)),
      shaped_binary);
  thm safe_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_ptr_shift_ok_def())), safe);
  thm pointer_live = conjunct1_rule(safe_open);
  thm right_refs = cm_binary_total_expr_refs(
      `right:cm_expr`, typed, function_wf, right_wf);
  thm scale_fixed = cm_binary_total_scale_fixed(
      `right:cm_expr`, typed, right_refs, right_pointer);
  thm runtime_scale = cm_binary_total_runtime_scale(
      `right:cm_expr`, `incoming:cm_value`,
      `cm_expr_type (right:cm_expr)`, right_compatible,
      right_pointer, pointer_live);
  thm not_both = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(op_equal, runtime_left_not)),
      `~((op:int) == 8i &&
         cm_is_pointer (cm_value_type (left_value:cm_value)) &&
         cm_is_pointer (cm_value_type (incoming:cm_value)))`));
  thm bridge = cm_binary_total_semantic_bridge(binary_ok, not_both);
  thm shaped_bridge = conv_rule(
      rewrite_conv(THM_LIST(op_equal)), bridge);
  thm shape = cm_binary_total_pointer_shape(`8i:int`,
      `[TVMInst TVMPushOp (cm_pointer_scale (p:cm_program)
          (right:cm_expr));
        TVMInst TVMMulOp 0i; TVMInst TVMSwapOp 0i;
        TVMInst TVMAddOp 0i]:(tvm_inst)list`,
      THM_LIST(right_pointer));
  term final_target =
      `tower_add
        (cm_value_number (st:cm_src_state)
          (CMIntV
            (tower_mul
              (cm_value_number st (left_value:cm_value))
              (cm_pointer_scale (p:cm_program) (right:cm_expr)))))
        (cm_value_number st (incoming:cm_value)) ==
       cm_value_number st
         (cm_binary_value p 8i left_value incoming (ty:cm_type) st)`;
  thm final_equal = cm_binary_total_pointer_final(
      final_target, shaped_bridge, THM_LIST(
        op_equal, runtime_right, runtime_left_not, runtime_scale));
  thm proved = cm_binary_total_apply_pointer(
      get_cm_target_v_bin_r_add_right_pointer_step(),
      conv_rule(rewrite_conv(THM_LIST(op_equal)), layout),
      conv_rule(rewrite_conv(THM_LIST(op_equal)), sim),
      shaped_binary, held, temp_equal, shape, scale_fixed,
      final_equal, address_facts, empty_theorem);
  cm_binary_total_accept(branch, THM_LIST(op_equal), proved);
}
PROOF static void cm_binary_total_add_left_pointer(
    gnode branch, thm mode_fact, thm typed, thm function_wf,
    thm left_wf, thm left_compatible, thm right_compatible,
    thm binary_ok, thm held, thm temp_equal, thm layout, thm sim,
    thm address_facts) {
  thm op_equal = assume_rule(`(op:int) == 8i`);
  thm left_pointer = cm_binary_total_pick(mode_fact,
      `cm_is_pointer (cm_expr_type (left:cm_expr))`);
  thm right_integer = cm_binary_total_pick(mode_fact,
      `cm_integer_type (cm_expr_type (right:cm_expr))`);
  thm runtime_left = cm_binary_total_runtime_pointer(
      `left_value:cm_value`, `cm_expr_type (left:cm_expr)`,
      left_pointer, left_compatible);
  thm runtime_right_not = cm_binary_total_runtime_integer(
      `incoming:cm_value`, `cm_expr_type (right:cm_expr)`,
      right_integer, right_compatible);
  thm shaped_binary = conv_rule(
      rewrite_conv(THM_LIST(op_equal)), binary_ok);
  thm safe = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_binary_ok_def(), runtime_left, runtime_right_not)),
      shaped_binary);
  thm safe_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_ptr_shift_ok_def())), safe);
  thm pointer_live = conjunct1_rule(safe_open);
  thm left_refs = cm_binary_total_expr_refs(
      `left:cm_expr`, typed, function_wf, left_wf);
  thm scale_fixed = cm_binary_total_scale_fixed(
      `left:cm_expr`, typed, left_refs, left_pointer);
  thm runtime_scale = cm_binary_total_runtime_scale(
      `left:cm_expr`, `left_value:cm_value`,
      `cm_expr_type (left:cm_expr)`, left_compatible,
      left_pointer, pointer_live);
  thm not_both = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(op_equal, runtime_right_not)),
      `~((op:int) == 8i &&
         cm_is_pointer (cm_value_type (left_value:cm_value)) &&
         cm_is_pointer (cm_value_type (incoming:cm_value)))`));
  thm bridge = cm_binary_total_semantic_bridge(binary_ok, not_both);
  thm shaped_bridge = conv_rule(
      rewrite_conv(THM_LIST(op_equal)), bridge);
  thm static_right_not = match_mp_rule(spec_rule(
      `cm_expr_type (right:cm_expr)`,
      cm_binary_total_integer_not_pointer), right_integer);
  thm shape = cm_binary_total_pointer_shape(`8i:int`,
      `[TVMInst TVMSwapOp 0i;
        TVMInst TVMPushOp (cm_pointer_scale (p:cm_program)
          (left:cm_expr));
        TVMInst TVMMulOp 0i; TVMInst TVMAddOp 0i]:(tvm_inst)list`,
      THM_LIST(left_pointer, static_right_not));
  term final_target =
      `tower_add
        (cm_value_number (st:cm_src_state) (left_value:cm_value))
        (cm_value_number st
          (CMIntV
            (tower_mul
              (cm_value_number st (incoming:cm_value))
              (cm_pointer_scale (p:cm_program) (left:cm_expr))))) ==
       cm_value_number st
         (cm_binary_value p 8i left_value incoming (ty:cm_type) st)`;
  thm final_equal = cm_binary_total_pointer_final(
      final_target, shaped_bridge, THM_LIST(
        op_equal, runtime_left, runtime_right_not, runtime_scale));
  thm proved = cm_binary_total_apply_pointer(
      get_cm_target_v_bin_r_add_left_pointer_step(),
      conv_rule(rewrite_conv(THM_LIST(op_equal)), layout),
      conv_rule(rewrite_conv(THM_LIST(op_equal)), sim),
      shaped_binary, held, temp_equal, shape, scale_fixed,
      final_equal, address_facts, empty_theorem);
  cm_binary_total_accept(branch, THM_LIST(op_equal), proved);
}
PROOF static void cm_binary_total_add_integer(
    gnode branch, thm mode_fact, thm left_compatible,
    thm right_compatible, thm binary_ok, thm op_not_zero,
    thm op_not_one, thm held, thm temp_equal, thm layout, thm sim,
    thm address_facts) {
  thm op_equal = assume_rule(`(op:int) == 8i`);
  thm left_integer = cm_binary_total_pick(mode_fact,
      `cm_integer_type (cm_expr_type (left:cm_expr))`);
  thm right_integer = cm_binary_total_pick(mode_fact,
      `cm_integer_type (cm_expr_type (right:cm_expr))`);
  thm runtime_left_not = cm_binary_total_runtime_integer(
      `left_value:cm_value`, `cm_expr_type (left:cm_expr)`,
      left_integer, left_compatible);
  thm runtime_right_not = cm_binary_total_runtime_integer(
      `incoming:cm_value`, `cm_expr_type (right:cm_expr)`,
      right_integer, right_compatible);
  thm not_both = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        op_equal, runtime_left_not, runtime_right_not)),
      `~((op:int) == 8i &&
         cm_is_pointer (cm_value_type (left_value:cm_value)) &&
         cm_is_pointer (cm_value_type (incoming:cm_value)))`));
  thm bridge = cm_binary_total_semantic_bridge(binary_ok, not_both);
  thm_list branch_rules = THM_LIST(
      op_equal, runtime_left_not, runtime_right_not,
      match_mp_rule(spec_rule(`cm_expr_type (left:cm_expr)`,
        cm_binary_total_integer_not_pointer), left_integer),
      match_mp_rule(spec_rule(`cm_expr_type (right:cm_expr)`,
        cm_binary_total_integer_not_pointer), right_integer));
  thm shape = cm_binary_total_ordinary_shape(
      `TVMAddOp:tvm_opcode`, branch_rules);
  thm operation_equal = cm_binary_total_ordinary_operation(
      `tower_add:int->int->int`, bridge, branch_rules);
  thm proved = cm_binary_total_apply_ordinary(
      false, `TVMAddOp:tvm_opcode`, `tower_add:int->int->int`,
      get_tvm_add_transition(), binary_ok, op_not_zero, op_not_one,
      held, temp_equal, shape, operation_equal, empty_theorem,
      layout, sim, address_facts);
  ACCEPT_TAC(branch, proved);
}
PROOF static void cm_binary_total_subtract_integer(
    gnode branch, thm mode_fact, thm left_compatible,
    thm right_compatible, thm binary_ok, thm op_not_zero,
    thm op_not_one, thm held, thm temp_equal, thm layout, thm sim,
    thm address_facts) {
  thm op_equal = assume_rule(`(op:int) == 9i`);
  thm left_integer = cm_binary_total_pick(mode_fact,
      `cm_integer_type (cm_expr_type (left:cm_expr))`);
  thm right_integer = cm_binary_total_pick(mode_fact,
      `cm_integer_type (cm_expr_type (right:cm_expr))`);
  thm runtime_left_not = cm_binary_total_runtime_integer(
      `left_value:cm_value`, `cm_expr_type (left:cm_expr)`,
      left_integer, left_compatible);
  thm runtime_right_not = cm_binary_total_runtime_integer(
      `incoming:cm_value`, `cm_expr_type (right:cm_expr)`,
      right_integer, right_compatible);
  thm not_both = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(op_equal)),
      `~((op:int) == 8i &&
         cm_is_pointer (cm_value_type (left_value:cm_value)) &&
         cm_is_pointer (cm_value_type (incoming:cm_value)))`));
  thm bridge = cm_binary_total_semantic_bridge(binary_ok, not_both);
  thm static_left_not = match_mp_rule(spec_rule(
      `cm_expr_type (left:cm_expr)`,
      cm_binary_total_integer_not_pointer), left_integer);
  thm static_right_not = match_mp_rule(spec_rule(
      `cm_expr_type (right:cm_expr)`,
      cm_binary_total_integer_not_pointer), right_integer);
  thm_list branch_rules = THM_LIST(
      op_equal, static_left_not, static_right_not,
      runtime_left_not, runtime_right_not);
  thm shape = cm_binary_total_ordinary_shape(
      `TVMSubOp:tvm_opcode`, branch_rules);
  thm operation_equal = cm_binary_total_ordinary_operation(
      `tower_sub:int->int->int`, bridge, branch_rules);
  thm proved = cm_binary_total_apply_ordinary(
      false, `TVMSubOp:tvm_opcode`, `tower_sub:int->int->int`,
      get_tvm_sub_transition(), binary_ok, op_not_zero, op_not_one,
      held, temp_equal, shape, operation_equal, empty_theorem,
      layout, sim, address_facts);
  ACCEPT_TAC(branch, proved);
}

PROOF static void cm_binary_total_subtract_pointer_number(
    gnode branch, thm mode_fact, thm typed, thm function_wf,
    thm left_wf, thm left_compatible, thm right_compatible,
    thm binary_ok, thm held, thm temp_equal, thm layout, thm sim,
    thm address_facts) {
  thm op_equal = assume_rule(`(op:int) == 9i`);
  thm left_pointer = cm_binary_total_pick(mode_fact,
      `cm_is_pointer (cm_expr_type (left:cm_expr))`);
  thm right_integer = cm_binary_total_pick(mode_fact,
      `cm_integer_type (cm_expr_type (right:cm_expr))`);
  thm runtime_left = cm_binary_total_runtime_pointer(
      `left_value:cm_value`, `cm_expr_type (left:cm_expr)`,
      left_pointer, left_compatible);
  thm runtime_right_not = cm_binary_total_runtime_integer(
      `incoming:cm_value`, `cm_expr_type (right:cm_expr)`,
      right_integer, right_compatible);
  thm shaped_binary = conv_rule(
      rewrite_conv(THM_LIST(op_equal)), binary_ok);
  thm safe = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_binary_ok_def(), runtime_left, runtime_right_not)),
      shaped_binary);
  thm safe_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_ptr_shift_ok_def())), safe);
  thm pointer_live = conjunct1_rule(safe_open);
  thm left_refs = cm_binary_total_expr_refs(
      `left:cm_expr`, typed, function_wf, left_wf);
  thm scale_fixed = cm_binary_total_scale_fixed(
      `left:cm_expr`, typed, left_refs, left_pointer);
  thm runtime_scale = cm_binary_total_runtime_scale(
      `left:cm_expr`, `left_value:cm_value`,
      `cm_expr_type (left:cm_expr)`, left_compatible,
      left_pointer, pointer_live);
  thm not_both = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(op_equal)),
      `~((op:int) == 8i &&
         cm_is_pointer (cm_value_type (left_value:cm_value)) &&
         cm_is_pointer (cm_value_type (incoming:cm_value)))`));
  thm bridge = cm_binary_total_semantic_bridge(binary_ok, not_both);
  thm shaped_bridge = conv_rule(
      rewrite_conv(THM_LIST(op_equal)), bridge);
  thm static_right_not = match_mp_rule(spec_rule(
      `cm_expr_type (right:cm_expr)`,
      cm_binary_total_integer_not_pointer), right_integer);
  thm shape = cm_binary_total_pointer_shape(`9i:int`,
      `[TVMInst TVMSwapOp 0i;
        TVMInst TVMPushOp (cm_pointer_scale (p:cm_program)
          (left:cm_expr));
        TVMInst TVMMulOp 0i; TVMInst TVMSubOp 0i]:(tvm_inst)list`,
      THM_LIST(left_pointer, static_right_not));
  term final_target =
      `tower_sub
        (cm_value_number (st:cm_src_state) (left_value:cm_value))
        (cm_value_number st
          (CMIntV
            (tower_mul
              (cm_value_number st (incoming:cm_value))
              (cm_pointer_scale (p:cm_program) (left:cm_expr))))) ==
       cm_value_number st
         (cm_binary_value p 9i left_value incoming (ty:cm_type) st)`;
  thm final_equal = cm_binary_total_pointer_final(
      final_target, shaped_bridge, THM_LIST(
        op_equal, runtime_left, runtime_right_not, runtime_scale));
  thm proved = cm_binary_total_apply_pointer(
      get_cm_target_v_bin_r_subtract_pointer_number_step(),
      conv_rule(rewrite_conv(THM_LIST(op_equal)), layout),
      conv_rule(rewrite_conv(THM_LIST(op_equal)), sim),
      shaped_binary, held, temp_equal, shape, scale_fixed,
      final_equal, address_facts, empty_theorem);
  cm_binary_total_accept(branch, THM_LIST(op_equal), proved);
}
PROOF static void cm_binary_total_subtract_pointers(
    gnode branch, thm mode_fact, thm typed, thm function_wf,
    thm left_wf, thm left_compatible, thm right_compatible,
    thm binary_ok, thm held, thm temp_equal, thm layout, thm sim,
    thm address_facts) {
  thm op_equal = assume_rule(`(op:int) == 9i`);
  thm types_equal = cm_binary_total_pick(mode_fact,
      `cm_expr_type (left:cm_expr) ==
       cm_expr_type (right:cm_expr)`);
  thm left_pointer = cm_binary_total_pick(mode_fact,
      `cm_is_pointer (cm_expr_type (left:cm_expr))`);
  thm right_pointer = conv_rule(
      rewrite_conv(THM_LIST(types_equal)), left_pointer);
  thm runtime_left = cm_binary_total_runtime_pointer(
      `left_value:cm_value`, `cm_expr_type (left:cm_expr)`,
      left_pointer, left_compatible);
  thm runtime_right = cm_binary_total_runtime_pointer(
      `incoming:cm_value`, `cm_expr_type (right:cm_expr)`,
      right_pointer, right_compatible);
  thm shaped_binary = conv_rule(
      rewrite_conv(THM_LIST(op_equal)), binary_ok);
  thm safe = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_binary_ok_def(), runtime_left, runtime_right)),
      shaped_binary);
  thm safe_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_ptr_diff_ok_def())), safe);
  thm compatible_pointers = conjunct1_rule(safe_open);
  thm compatibility_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_pointer_compatible_def())), compatible_pointers);
  thm left_live = cm_binary_total_pick(compatibility_open,
      `cm_pointer_live (st:cm_src_state) (left_value:cm_value)`);
  thm left_refs = cm_binary_total_expr_refs(
      `left:cm_expr`, typed, function_wf, left_wf);
  thm scale_fixed = cm_binary_total_scale_fixed(
      `left:cm_expr`, typed, left_refs, left_pointer);
  thm runtime_scale = cm_binary_total_runtime_scale(
      `left:cm_expr`, `left_value:cm_value`,
      `cm_expr_type (left:cm_expr)`, left_compatible,
      left_pointer, left_live);
  thm positive = cm_binary_total_pick(safe_open,
      `0i < cm_type_size (cm_program_structs (p:cm_program))
        (cm_ptr_view (left_value:cm_value))`);
  thm raw_nonzero = match_mp_rule(int_arith_rule(mk_imp(
      concl(positive),
      `~(cm_type_size (cm_program_structs (p:cm_program))
          (cm_ptr_view (left_value:cm_value)) == 0i)`)), positive);
  term nonzero_target =
      `~(cm_pointer_scale (p:cm_program) (left:cm_expr) == 0i)`;
  thm nonzero_view = apply_conversion(rewrite_conv(THM_LIST(
      runtime_scale,
      spec_rule(`left_value:cm_value`, get_cm_pointer_type_view()))),
      nonzero_target);
  thm scale_nonzero =
      eq_mp_rule(sym_rule(nonzero_view), raw_nonzero);
  thm not_both = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(op_equal)),
      `~((op:int) == 8i &&
         cm_is_pointer (cm_value_type (left_value:cm_value)) &&
         cm_is_pointer (cm_value_type (incoming:cm_value)))`));
  thm bridge = cm_binary_total_semantic_bridge(binary_ok, not_both);
  thm shaped_bridge = conv_rule(
      rewrite_conv(THM_LIST(op_equal)), bridge);
  thm shape = cm_binary_total_pointer_shape(`9i:int`,
      `[TVMInst TVMSwapOp 0i; TVMInst TVMSubOp 0i;
        TVMInst TVMPushOp (cm_pointer_scale (p:cm_program)
          (left:cm_expr));
        TVMInst TVMDivOp 0i]:(tvm_inst)list`,
      THM_LIST(left_pointer, right_pointer));
  term final_target =
      `tower_div
        (cm_value_number (st:cm_src_state)
          (CMIntV
            (tower_sub
              (cm_value_number st (left_value:cm_value))
              (cm_value_number st (incoming:cm_value)))))
        (cm_value_number st
          (CMIntV
            (cm_pointer_scale (p:cm_program) (left:cm_expr)))) ==
       cm_value_number st
         (cm_binary_value p 9i left_value incoming (ty:cm_type) st)`;
  thm final_equal = cm_binary_total_pointer_final(
      final_target, shaped_bridge, THM_LIST(
        op_equal, runtime_left, runtime_right,
        runtime_scale, scale_fixed));
  thm proved = cm_binary_total_apply_pointer(
      get_cm_target_v_bin_r_subtract_pointers_step(),
      conv_rule(rewrite_conv(THM_LIST(op_equal)), layout),
      conv_rule(rewrite_conv(THM_LIST(op_equal)), sim),
      shaped_binary, held, temp_equal, shape, scale_fixed,
      final_equal, address_facts, scale_nonzero);
  cm_binary_total_accept(branch, THM_LIST(op_equal), proved);
}
PROOF static void cm_binary_total_logical_branch(
    gnode branch, bool zero, thm historical, thm parent,
    thm binary_ok, thm layout, thm sim) {
  thm op_equal = zero
      ? assume_rule(`(op:int) == 0i`)
      : assume_rule(`(op:int) == 1i`);
  thm logical = zero
      ? disj1_rule(op_equal, `(op:int) == 1i`)
      : disj2_rule(`(op:int) == 0i`, op_equal);
  thm left_condition = match_mp_rule(
      zero ? conjunct1_rule(historical) : conjunct2_rule(historical),
      op_equal);
  thm end_valid = get_cm_target_v_bin_r_end_valid();
  end_valid = match_mp_rule(end_valid, logical);
  end_valid = match_mp_rule(end_valid, parent);
  end_valid = match_mp_rule(end_valid, layout);
  thm_list shaped = THM_LIST(op_equal);
  thm proved = zero
      ? get_cm_target_v_bin_r_zero_step()
      : get_cm_target_v_bin_r_one_step();
  proved = match_mp_rule(proved,
      conv_rule(rewrite_conv(shaped), layout));
  proved = match_mp_rule(proved,
      conv_rule(rewrite_conv(shaped), sim));
  proved = match_mp_rule(proved,
      conv_rule(rewrite_conv(shaped), binary_ok));
  proved = match_mp_rule(proved, left_condition);
  proved = match_mp_rule(proved, end_valid);
  cm_binary_total_accept(branch, shaped, proved);
}
PROOF static thm cm_prove_target_v_bin_r_total_step(void) {
  term phase =
      `CABinRP (op:int) (left:cm_expr) (right:cm_expr)
        (left_value:cm_value) (ty:cm_type)`;
  term cursors =
      `CMACursor ${phase:cm_aphase} (owner:int) (saved_break:int)
        (saved_continue:int) :: (rest:(cm_acursor)list)`;
  term task =
      `CMVTask (p:cm_program) (fid:int) (incoming:cm_value)
        (st:cm_src_state)
        (CMBinRK (op:int) (left_value:cm_value) (ty:cm_type) ::
         cm_cursor_frames (rest:(cm_acursor)list))`;
  term ann =
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
        ${cursors:(cm_acursor)list} (spills:(cm_spill)list)
        (saved:(cm_spill_frame)list) (calls:(cm_call_sim_frame)list)`;
  term result =
      `cm_task_target_sim (p:cm_program) (cm_step ${task:cm_task})
        (tvm_iter
          (cm_update_steps
            (cm_annotation_step ${task:cm_task} ${ann:cm_annotation}))
          (target:tvm_task))
        (cm_update_annotation
          (cm_annotation_step ${task:cm_task} ${ann:cm_annotation}))`;
  term body = imp_chain(TERM_LIST(
      `cm_typed_program (p:cm_program)`,
      `0i <= (fid:int)`,
      `(fid:int) < ilength (cm_program_functions (p:cm_program))`,
      `cm_phase_static_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase}`,
      `cm_phase_parent_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase} (rest:(cm_acursor)list)`,
      `cm_phase_value_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase} (incoming:cm_value)`,
      `cm_v_phase_ready (p:cm_program) (incoming:cm_value)
        (st:cm_src_state) ${ann:cm_annotation} ${phase:cm_aphase}`,
      `cm_v_source_ready (p:cm_program) (fid:int)
        (st:cm_src_state) ${phase:cm_aphase}`,
      `cm_phase_spill_consistent (temp:int) (owner:int)
        ${phase:cm_aphase} (spills:(cm_spill)list)`,
      `cm_v_temp_ready ${ann:cm_annotation} ${phase:cm_aphase}`,
      `cm_runtime_stack (p:cm_program)
        (cm_state_regions (st:cm_src_state)) (fid:int)
        (cm_state_fp st) (cm_state_regions st)
        ${cursors:(cm_acursor)list} (spills:(cm_spill)list)
        (saved:(cm_spill_frame)list) (calls:(cm_call_sim_frame)list)`,
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`,
      `cm_task_target_sim (p:cm_program) ${task:cm_task}
        (target:tvm_task) ${ann:cm_annotation}`), result);
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);

  thm typed = assume_rule(`cm_typed_program (p:cm_program)`);
  thm fid_lower = assume_rule(`0i <= (fid:int)`);
  thm fid_upper = assume_rule(
      `(fid:int) < ilength (cm_program_functions (p:cm_program))`);
  thm static_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_phase_static_type_ready_def())), assume_rule(
        `cm_phase_static_type_ready (p:cm_program) (fid:int)
          ${phase:cm_aphase}`));
  thm expression_wf = conjunct1_rule(static_open);
  thm left_compatible = conjunct2_rule(static_open);
  thm expression_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_expr_wf_def())), expression_wf);
  thm left_wf = conjunct1_rule(expression_open);
  thm right_wf = conjunct1_rule(conjunct2_rule(expression_open));
  thm binary_types = conjunct2_rule(conjunct2_rule(expression_open));
  thm right_compatible = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_phase_value_type_ready_def())), assume_rule(
        `cm_phase_value_type_ready (p:cm_program) (fid:int)
          ${phase:cm_aphase} (incoming:cm_value)`));
  thm binary_ok = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_v_phase_ready_def)), assume_rule(
        `cm_v_phase_ready (p:cm_program) (incoming:cm_value)
          (st:cm_src_state) ${ann:cm_annotation} ${phase:cm_aphase}`));
  thm source_open = conv_rule(rewrite_conv(THM_LIST(
      cm_v_source_ready_def)), assume_rule(
        `cm_v_source_ready (p:cm_program) (fid:int)
          (st:cm_src_state) ${phase:cm_aphase}`));
  thm historical = specl_rule(TERM_LIST(
      `op:int`, `left:cm_expr`, `right:cm_expr`,
      `left_value:cm_value`, `ty:cm_type`), conjunct2_rule(source_open));
  historical = match_mp_rule(historical, refl_rule(phase));
  thm parent = assume_rule(
      `cm_phase_parent_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase} (rest:(cm_acursor)list)`);
  thm layout = assume_rule(
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`);
  thm sim = assume_rule(
      `cm_task_target_sim (p:cm_program) ${task:cm_task}
        (target:tvm_task) ${ann:cm_annotation}`);

  gnode_list zero_cases =
      BOOL_CASES_TAC(introduced, `(op:int) == 0i`, "Hop_zero");
  cm_binary_total_logical_branch(
      zero_cases[0], true, historical, parent, binary_ok, layout, sim);
  gnode_list one_cases =
      BOOL_CASES_TAC(zero_cases[1], `(op:int) == 1i`, "Hop_one");
  cm_binary_total_logical_branch(
      one_cases[0], false, historical, parent, binary_ok, layout, sim);

  thm op_not_zero = assume_rule(`~((op:int) == 0i)`);
  thm op_not_one = assume_rule(`~((op:int) == 1i)`);
  thm temp_equal = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_v_temp_ready_def, cm_phase_child_temp_def,
      cm_ann_temp_def, cm_ann_cursors_def, cm_cursor_temp_def,
      get_theorem_by_name("HD"), op_not_zero, op_not_one)),
      assume_rule(`cm_v_temp_ready ${ann:cm_annotation}
        ${phase:cm_aphase}`));
  thm spill_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_phase_spill_consistent_def, op_not_zero, op_not_one)),
      assume_rule(
        `cm_phase_spill_consistent (temp:int) (owner:int)
          ${phase:cm_aphase} (spills:(cm_spill)list)`));
  thm held = cm_binary_total_pick(spill_open,
      `cm_spill_holds (owner:int) (left_value:cm_value)
        (spills:(cm_spill)list)`);
  thm runtime = assume_rule(
      `cm_runtime_stack (p:cm_program)
        (cm_state_regions (st:cm_src_state)) (fid:int)
        (cm_state_fp st) (cm_state_regions st)
        ${cursors:(cm_acursor)list} (spills:(cm_spill)list)
        (saved:(cm_spill_frame)list) (calls:(cm_call_sim_frame)list)`);
  thm address_facts =
      cm_binary_total_address_facts(runtime, held, fid_lower);
  thm function_wf =
      cm_binary_total_function_wf(typed, fid_lower, fid_upper);

  term comparison_tests[6] = {
    `(op:int) == 2i`, `(op:int) == 3i`, `(op:int) == 4i`,
    `(op:int) == 5i`, `(op:int) == 6i`, `(op:int) == 7i`
  };
  const char *comparison_labels[6] = {
    "Hop_eq", "Hop_ne", "Hop_lt", "Hop_le", "Hop_gt", "Hop_ge"
  };
  term comparison_opcodes[6] = {
    `TVMEqOp:tvm_opcode`, `TVMNeOp:tvm_opcode`, `TVMLtOp:tvm_opcode`,
    `TVMLeOp:tvm_opcode`, `TVMGtOp:tvm_opcode`, `TVMGeOp:tvm_opcode`
  };
  term comparison_operations[6] = {
    `\(x:int) (y:int). tower_bool (x == y)`,
    `\(x:int) (y:int). tower_bool (~(x == y))`,
    `\(x:int) (y:int). tower_bool (x < y)`,
    `\(x:int) (y:int). tower_bool (x <= y)`,
    `\(x:int) (y:int). tower_bool (y < x)`,
    `\(x:int) (y:int). tower_bool (y <= x)`
  };
  thm comparison_transitions[6] = {
    get_tvm_eq_transition(), get_tvm_ne_transition(),
    get_tvm_lt_transition(), get_tvm_le_transition(),
    get_tvm_gt_transition(), get_tvm_ge_transition()
  };
  gnode current = one_cases[1];
  for (size_t i = 0; i < 6; ++i) {
    gnode_list cases = BOOL_CASES_TAC(
        current, comparison_tests[i], comparison_labels[i]);
    cm_binary_total_simple_branch(
        cases[0], comparison_tests[i], comparison_opcodes[i],
        comparison_operations[i], comparison_transitions[i], false,
        binary_ok, op_not_zero, op_not_one, held, temp_equal,
        layout, sim, address_facts);
    current = cases[1];
  }

  gnode_list add_cases =
      BOOL_CASES_TAC(current, `(op:int) == 8i`, "Hop_add");
  {
    thm op_equal = assume_rule(`(op:int) == 8i`);
    thm modes = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_binary_types_def(), op_equal)), binary_types);
    gnode_list mode_cases =
        DISJ_CASES_TAC(add_cases[0], modes, "Hadd_mode");
    labeled_term_list facts0 = goal_lasmps(mode_cases[0]->g);
    thm mode0 = assume_rule(facts0[
        labeled_term_list_index(facts0, "Hadd_mode")].tm);
    cm_binary_total_add_integer(
        mode_cases[0], mode0, left_compatible, right_compatible,
        binary_ok, op_not_zero, op_not_one, held, temp_equal,
        layout, sim, address_facts);
    labeled_term_list facts1 = goal_lasmps(mode_cases[1]->g);
    thm mode1 = assume_rule(facts1[
        labeled_term_list_index(facts1, "Hadd_mode")].tm);
    cm_binary_total_add_left_pointer(
        mode_cases[1], mode1, typed, function_wf, left_wf,
        left_compatible, right_compatible, binary_ok, held, temp_equal,
        layout, sim, address_facts);
    labeled_term_list facts2 = goal_lasmps(mode_cases[2]->g);
    thm mode2 = assume_rule(facts2[
        labeled_term_list_index(facts2, "Hadd_mode")].tm);
    cm_binary_total_add_right_pointer(
        mode_cases[2], mode2, typed, function_wf, right_wf,
        left_compatible, right_compatible, binary_ok, held, temp_equal,
        layout, sim, address_facts);
  }

  gnode_list subtract_cases =
      BOOL_CASES_TAC(add_cases[1], `(op:int) == 9i`, "Hop_subtract");
  {
    thm op_equal = assume_rule(`(op:int) == 9i`);
    thm modes = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_binary_types_def(), op_equal)), binary_types);
    gnode_list mode_cases =
        DISJ_CASES_TAC(subtract_cases[0], modes, "Hsubtract_mode");
    labeled_term_list facts0 = goal_lasmps(mode_cases[0]->g);
    thm mode0 = assume_rule(facts0[
        labeled_term_list_index(facts0, "Hsubtract_mode")].tm);
    cm_binary_total_subtract_integer(
        mode_cases[0], mode0, left_compatible, right_compatible,
        binary_ok, op_not_zero, op_not_one, held, temp_equal,
        layout, sim, address_facts);
    labeled_term_list facts1 = goal_lasmps(mode_cases[1]->g);
    thm mode1 = assume_rule(facts1[
        labeled_term_list_index(facts1, "Hsubtract_mode")].tm);
    cm_binary_total_subtract_pointer_number(
        mode_cases[1], mode1, typed, function_wf, left_wf,
        left_compatible, right_compatible, binary_ok, held, temp_equal,
        layout, sim, address_facts);
    labeled_term_list facts2 = goal_lasmps(mode_cases[2]->g);
    thm mode2 = assume_rule(facts2[
        labeled_term_list_index(facts2, "Hsubtract_mode")].tm);
    cm_binary_total_subtract_pointers(
        mode_cases[2], mode2, typed, function_wf, left_wf,
        left_compatible, right_compatible, binary_ok, held, temp_equal,
        layout, sim, address_facts);
  }

  term arithmetic_tests[3] = {
    `(op:int) == 10i`, `(op:int) == 11i`, `(op:int) == 12i`
  };
  const char *arithmetic_labels[3] = {
    "Hop_mul", "Hop_div", "Hop_mod"
  };
  term arithmetic_opcodes[3] = {
    `TVMMulOp:tvm_opcode`, `TVMDivOp:tvm_opcode`, `TVMModOp:tvm_opcode`
  };
  term arithmetic_operations[3] = {
    `tower_mul:int->int->int`,
    `tower_div:int->int->int`,
    `tower_mod:int->int->int`
  };
  thm arithmetic_transitions[3] = {
    get_tvm_mul_transition(), get_tvm_div_transition(),
    get_tvm_mod_transition()
  };
  current = subtract_cases[1];
  for (size_t i = 0; i < 3; ++i) {
    gnode_list cases = BOOL_CASES_TAC(
        current, arithmetic_tests[i], arithmetic_labels[i]);
    cm_binary_total_simple_branch(
        cases[0], arithmetic_tests[i], arithmetic_opcodes[i],
        arithmetic_operations[i], arithmetic_transitions[i], i > 0,
        binary_ok, op_not_zero, op_not_one, held, temp_equal,
        layout, sim, address_facts);
    current = cases[1];
  }

  thm binary_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_binary_types_def())), binary_types);
  thm lower = cm_binary_total_pick(binary_open, `0i <= (op:int)`);
  thm upper = cm_binary_total_pick(binary_open, `(op:int) <= 12i`);
  thm_list contradiction_facts = THM_LIST(lower, upper);
  term opcode_tests[13] = {
    `(op:int) == 0i`, `(op:int) == 1i`, `(op:int) == 2i`,
    `(op:int) == 3i`, `(op:int) == 4i`, `(op:int) == 5i`,
    `(op:int) == 6i`, `(op:int) == 7i`, `(op:int) == 8i`,
    `(op:int) == 9i`, `(op:int) == 10i`, `(op:int) == 11i`,
    `(op:int) == 12i`
  };
  for (size_t i = 0; i < 13; ++i) {
    vector_add(&contradiction_facts,
        assume_rule(mk_not(opcode_tests[i])));
  }
  term_list contradiction_terms = vector_create();
  for (size_t i = 0; i < vector_size(contradiction_facts); ++i) {
    vector_add(&contradiction_terms, concl(contradiction_facts[i]));
  }
  thm impossible = int_arith_rule(
      imp_chain(contradiction_terms, mk_false()));
  for (size_t i = 0; i < vector_size(contradiction_facts); ++i) {
    impossible = mp_rule(impossible, contradiction_facts[i]);
  }
  CONTR_TAC(current, impossible);
  return gnode_prove(root);
}
PROOF thm cm_target_v_bin_r_total_step =
    cm_prove_target_v_bin_r_total_step();

PROOF static thm cm_prove_target_v_binary_step(void) {
  term phase = `phase:cm_aphase`;
  term cursors =
      `CMACursor ${phase:cm_aphase} (owner:int) (saved_break:int)
        (saved_continue:int) :: (rest:(cm_acursor)list)`;
  term frames =
      `cm_phase_frame ${phase:cm_aphase} ::
       cm_cursor_frames (rest:(cm_acursor)list)`;
  term task =
      `CMVTask (p:cm_program) (fid:int) (incoming:cm_value)
        (st:cm_src_state) ${frames:(cm_frame)list}`;
  term ann =
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
        ${cursors:(cm_acursor)list} (spills:(cm_spill)list)
        (saved:(cm_spill_frame)list) (calls:(cm_call_sim_frame)list)`;
  term update =
      `cm_annotation_step ${task:cm_task} ${ann:cm_annotation}`;
  term target_term =
      `cm_task_target_sim (p:cm_program) (cm_step ${task:cm_task})
        (tvm_iter (cm_update_steps ${update:cm_aupdate})
          (target:tvm_task))
        (cm_update_annotation ${update:cm_aupdate})`;
  term body = imp_chain(TERM_LIST(
      `cm_wf_program (p:cm_program)`,
      `cm_runtime_step_ready p ${task:cm_task} ${ann:cm_annotation}`,
      `cm_task_runtime_invariant p ${task:cm_task}
        ${ann:cm_annotation}`,
      `cm_task_type_ready p ${task:cm_task} ${ann:cm_annotation}`,
      `cm_task_fid_ready p ${task:cm_task}`,
      `cm_annotation_spill_consistent ${ann:cm_annotation}`,
      `cm_task_generation_safe p ${task:cm_task}
        ${ann:cm_annotation}`,
      `cm_task_tagged_valid ${task:cm_task}`,
      `cm_task_layout p ${task:cm_task} ${ann:cm_annotation}`,
      `cm_task_target_sim p ${task:cm_task} (target:tvm_task)
        ${ann:cm_annotation}`,
      `cm_v_phase_family ${phase:cm_aphase} == 1i`), target_term);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);

  thm context = cm_target_v_context;
  thm_list context_premises = THM_LIST(
      assume_rule(`cm_wf_program (p:cm_program)`),
      assume_rule(
        `cm_runtime_step_ready (p:cm_program) ${task:cm_task}
          ${ann:cm_annotation}`),
      assume_rule(
        `cm_task_runtime_invariant (p:cm_program) ${task:cm_task}
          ${ann:cm_annotation}`),
      assume_rule(
        `cm_task_type_ready (p:cm_program) ${task:cm_task}
          ${ann:cm_annotation}`),
      assume_rule(`cm_task_fid_ready (p:cm_program) ${task:cm_task}`),
      assume_rule(`cm_annotation_spill_consistent ${ann:cm_annotation}`),
      assume_rule(
        `cm_task_generation_safe (p:cm_program) ${task:cm_task}
          ${ann:cm_annotation}`),
      assume_rule(`cm_task_tagged_valid ${task:cm_task}`));
  for (size_t i = 0; i < vector_size(context_premises); ++i) {
    context = match_mp_rule(context, context_premises[i]);
  }
  thm layout = assume_rule(
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`);
  thm sim = assume_rule(
      `cm_task_target_sim (p:cm_program) ${task:cm_task}
        (target:tvm_task) ${ann:cm_annotation}`);
  thm family =
      assume_rule(`cm_v_phase_family ${phase:cm_aphase} == 1i`);

  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(phase, get_datatype_cases("cm_aphase")), "Hphase");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(branch->g);
      int index = labeled_term_list_index(assumptions, "Hphase");
      if (!is_exists(assumptions[index].tm)) break;
      branch = ASMP_EXISTS_TAC(branch, "Hphase", NULL);
    }
    thm shape = assume_rule(goal_lasmps(branch->g)[
        labeled_term_list_index(goal_lasmps(branch->g), "Hphase")].tm);
    if (i != 4 && i != 5) {
      thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
          shape, get_cm_v_phase_family_def())), family);
      CONTR_TAC(branch, impossible);
      continue;
    }

    term concrete_phase = rhs_of(shape);
    term concrete_cursors =
        `CMACursor ${concrete_phase:cm_aphase} (owner:int)
          (saved_break:int) (saved_continue:int) ::
         (rest:(cm_acursor)list)`;
    term concrete_ann =
        `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
          ${concrete_cursors:(cm_acursor)list} (spills:(cm_spill)list)
          (saved:(cm_spill_frame)list) (calls:(cm_call_sim_frame)list)`;
    thm_list shape_rules = THM_LIST(shape, cm_phase_frame_def);
    thm shaped_context =
        conv_rule(rewrite_conv(THM_LIST(shape)), context);
    thm shaped_layout = conv_rule(
        reduce_rewrite_conv(shape_rules), layout);
    thm shaped_sim = conv_rule(
        reduce_rewrite_conv(shape_rules), sim);
    thm bounds_disjunction = cm_binary_total_pick(shaped_context,
        `cm_phase_is_halt ${concrete_phase:cm_aphase} ||
         (0i <= (fid:int) &&
          fid < ilength (cm_program_functions (p:cm_program)))`);
    thm bounds = conv_rule(reduce_rewrite_conv(THM_LIST(
        cm_phase_is_halt_def)), bounds_disjunction);
    thm temp_ready = cm_binary_total_pick(shaped_context,
        `cm_v_temp_ready ${concrete_ann:cm_annotation}
          ${concrete_phase:cm_aphase}`);
    thm runtime_stack = cm_binary_total_pick(shaped_context,
        `cm_runtime_stack (p:cm_program)
          (cm_state_regions (st:cm_src_state)) (fid:int)
          (cm_state_fp st) (cm_state_regions st)
          ${concrete_cursors:(cm_acursor)list} (spills:(cm_spill)list)
          (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list)`);
    if (i == 4) {
      thm spill_ready = cm_binary_total_pick(shaped_context,
          `cm_v_spill_ready (p:cm_program) (fid:int)
            ${concrete_ann:cm_annotation} ${concrete_phase:cm_aphase}`);
      thm tagged = cm_binary_total_pick(shaped_context,
          `cm_tagged_span_valid (st:cm_src_state)`);
      thm proved = cm_target_v_bin_l_total_step;
      thm_list premises = THM_LIST(
          conjunct1_rule(bounds), temp_ready, spill_ready,
          runtime_stack, tagged, shaped_layout, shaped_sim);
      for (size_t j = 0; j < vector_size(premises); ++j) {
        proved = match_mp_rule(proved, premises[j]);
      }
      thm normalized =
          conv_rule(reduce_rewrite_conv(shape_rules), proved);
      thm target_view = apply_conversion(
          reduce_rewrite_conv(shape_rules), goal_ccl(branch->g));
      ACCEPT_TAC(branch, eq_mp_rule(sym_rule(target_view), normalized));
      continue;
    }

    thm typed = cm_binary_total_pick(shaped_context,
        `cm_typed_program (p:cm_program)`);
    thm static_type = cm_binary_total_pick(shaped_context,
        `cm_phase_static_type_ready (p:cm_program) (fid:int)
          ${concrete_phase:cm_aphase}`);
    thm parent_type = cm_binary_total_pick(shaped_context,
        `cm_phase_parent_type_ready (p:cm_program) (fid:int)
          ${concrete_phase:cm_aphase} (rest:(cm_acursor)list)`);
    thm value_type = cm_binary_total_pick(shaped_context,
        `cm_phase_value_type_ready (p:cm_program) (fid:int)
          ${concrete_phase:cm_aphase} (incoming:cm_value)`);
    thm phase_ready = cm_binary_total_pick(shaped_context,
        `cm_v_phase_ready (p:cm_program) (incoming:cm_value)
          (st:cm_src_state) ${concrete_ann:cm_annotation}
          ${concrete_phase:cm_aphase}`);
    thm source_ready = cm_binary_total_pick(shaped_context,
        `cm_v_source_ready (p:cm_program) (fid:int)
          (st:cm_src_state) ${concrete_phase:cm_aphase}`);
    thm phase_spill = cm_binary_total_pick(shaped_context,
        `cm_phase_spill_consistent (temp:int) (owner:int)
          ${concrete_phase:cm_aphase} (spills:(cm_spill)list)`);
    thm proved = cm_target_v_bin_r_total_step;
    thm_list premises = THM_LIST(
        typed, conjunct1_rule(bounds), conjunct2_rule(bounds),
        static_type, parent_type, value_type, phase_ready,
        source_ready, phase_spill, temp_ready, runtime_stack,
        shaped_layout, shaped_sim);
    for (size_t j = 0; j < vector_size(premises); ++j) {
      proved = match_mp_rule(proved, premises[j]);
    }
    thm normalized =
        conv_rule(reduce_rewrite_conv(shape_rules), proved);
    thm target_view = apply_conversion(
        reduce_rewrite_conv(shape_rules), goal_ccl(branch->g));
    ACCEPT_TAC(branch, eq_mp_rule(sym_rule(target_view), normalized));
  }
  return gnode_prove(root);
}
PROOF thm cm_target_v_binary_step =
    cm_prove_target_v_binary_step();










PROOF thm get_cm_referenced_type_size_fixed(void) {
  return cm_referenced_type_size_fixed;
}
PROOF thm get_cm_target_v_bin_l_jump_valid(void) {
  return cm_target_v_bin_l_jump_valid;
}
PROOF thm get_cm_target_v_bin_l_total_step(void) {
  return cm_target_v_bin_l_total_step;
}
PROOF thm get_cm_target_v_bin_r_end_valid(void) {
  return cm_target_v_bin_r_end_valid;
}
PROOF thm get_cm_target_v_bin_r_total_step(void) {
  return cm_target_v_bin_r_total_step;
}
PROOF thm get_cm_target_v_binary_step(void) {
  return cm_target_v_binary_step;
}

PROOF static int cmc_preservation_target_value_binary_total_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_value_binary_total_axioms_before,
      "cmc_preservation_target_value_binary_total introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_referenced_type_size_fixed)) == 0 &&
      vector_size(hyp(cm_target_v_bin_l_jump_valid)) == 0 &&
      vector_size(hyp(cm_target_v_bin_l_total_step)) == 0 &&
      vector_size(hyp(cm_target_v_bin_r_end_valid)) == 0 &&
      vector_size(hyp(cm_target_v_bin_r_total_step)) == 0 &&
      vector_size(hyp(cm_target_v_binary_step)) == 0,
      "binary target theorem has assumptions");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_value_binary_total_checked =
    cmc_preservation_target_value_binary_total_final_checks();
