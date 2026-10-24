#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_type_source_l.h"
#include "cmc_concrete_defs.h"
#include "cmc_preservation_type_facts.h"

#require "cmc_concrete_defs.c"
#require "cmc_preservation_type_facts.c"
#require "cmc_preservation_type_cursor.c"
#require "cmc_preservation_type_lvalue.c"
#require "cmc_preservation_source_conditions.c"

PROOF static size_t _cmc_preservation_type_source_l_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_tsl_pick_conjunct(thm fact, term wanted) {
  if (alpha_compare(concl(fact), wanted) == 0) return fact;
  if (!is_conj(concl(fact))) return empty_theorem;
  thm left = cm_tsl_pick_conjunct(conjunct1_rule(fact), wanted);
  if (!IS_NULL(left)) return left;
  return cm_tsl_pick_conjunct(conjunct2_rule(fact), wanted);
}

PROOF static thm cm_prove_l_var_type_ready_step(void) {
  term task =
      `CMLTask (q:cm_program) (fid:int)
        (CMVarE (scope:int) (slot:int) (ty:cm_type))
        (st:cm_src_state) (ks:(cm_frame)list)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (q:cm_program) (fid:int) (scope:int)
         (slot:int) (ty:cm_type) (st:cm_src_state)
         (ks:(cm_frame)list) (ann:cm_annotation).
         cm_task_succeeds
           (CMLTask q fid (CMVarE scope slot ty) st ks) ==>
         cm_task_type_ready p
           (CMLTask q fid (CMVarE scope slot ty) st ks) ann ==>
         cm_task_type_ready p
           (cm_step (CMLTask q fid (CMVarE scope slot ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMLTask q fid (CMVarE scope slot ty) st ks) ann))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm ready = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_task_type_ready_def())), assume_rule(
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        (ann:cm_annotation)`));
  thm same_program = cm_tsl_pick_conjunct(ready,
      `(q:cm_program) == (p:cm_program)`);
  thm expression_wf = cm_tsl_pick_conjunct(ready,
      `cm_expr_wf (p:cm_program)
        (inth (fid:int) (cm_program_functions p))
        (CMVarE (scope:int) (slot:int) (ty:cm_type))`);
  thm cursors_ready = cm_tsl_pick_conjunct(ready,
      `cm_cursors_type_ready (p:cm_program) (fid:int)
        (cm_ann_cursors (ann:cm_annotation))`);
  thm lvalue_ready = cm_tsl_pick_conjunct(ready,
      `cm_cursor_head_lvalue_type_ready (p:cm_program) (fid:int)
        (cm_lvalue_output_type p
          (inth fid (cm_program_functions p))
          (CMVarE (scope:int) (slot:int) (ty:cm_type)))
        (cm_ann_cursors (ann:cm_annotation))`);
  thm succeeds = conv_rule(rewrite_conv(THM_LIST(same_program)),
      assume_rule(`cm_task_succeeds ${task:cm_task}`));
  thm address_ok = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `scope:int`, `slot:int`, `ty:cm_type`,
      `st:cm_src_state`, `ks:(cm_frame)list`),
      cm_l_var_succeeds_address), succeeds);
  thm compatible = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `scope:int`, `slot:int`, `ty:cm_type`,
      `st:cm_src_state`), cm_binding_lvalue_type_ready), expression_wf),
      address_ok);
  thm head_value = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `cm_ann_cursors (ann:cm_annotation)`, `p:cm_program`, `fid:int`,
      `cm_lvalue_output_type p (inth fid (cm_program_functions p))
        (CMVarE (scope:int) (slot:int) (ty:cm_type))`,
      `(if (scope:int) == 0i then cm_global_pointer p (slot:int)
        else cm_state_env (st:cm_src_state) scope slot)`),
      cm_cursor_lvalue_value_ready), lvalue_ready), compatible);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      same_program, address_ok, cursors_ready, head_value,
      get_cm_task_type_ready_def(), get_cm_step_def(),
      get_cm_lstart_def(), cm_annotation_step_def, cm_update_l_def,
      cm_update_annotation_def, cm_ann_linear_def, cm_ann_plain_def,
      cm_ann_cursors_def, get_theorem_by_name("COND_CLAUSES"))),
      goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eqt_elim_rule(target_view));
  return gnode_prove(root);
}
PROOF static thm cm_l_var_type_ready_step =
    cm_prove_l_var_type_ready_step();

PROOF static thm cm_prove_l_unary_type_ready_step(void) {
  term expression =
      `CMUnaryE (op:int) (arg:cm_expr) (ty:cm_type)`;
  term task =
      `CMLTask (q:cm_program) (fid:int) ${expression:cm_expr}
        (st:cm_src_state) (ks:(cm_frame)list)`;
  term function =
      `inth (fid:int) (cm_program_functions (p:cm_program))`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (q:cm_program) (fid:int) (op:int)
         (arg:cm_expr) (ty:cm_type) (st:cm_src_state)
         (ks:(cm_frame)list) (ann:cm_annotation).
         cm_task_succeeds
           (CMLTask q fid (CMUnaryE op arg ty) st ks) ==>
         cm_task_type_ready p
           (CMLTask q fid (CMUnaryE op arg ty) st ks) ann ==>
         cm_task_type_ready p
           (cm_step (CMLTask q fid (CMUnaryE op arg ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMLTask q fid (CMUnaryE op arg ty) st ks) ann))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm ready = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_task_type_ready_def())), assume_rule(
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        (ann:cm_annotation)`));
  thm same_program = cm_tsl_pick_conjunct(ready,
      `(q:cm_program) == (p:cm_program)`);
  thm fid_low = cm_tsl_pick_conjunct(ready, `0i <= (fid:int)`);
  thm fid_high = cm_tsl_pick_conjunct(ready,
      `(fid:int) < ilength (cm_program_functions (p:cm_program))`);
  thm expression_wf = cm_tsl_pick_conjunct(ready,
      `cm_expr_wf (p:cm_program) ${function:cm_function_d}
        ${expression:cm_expr}`);
  thm lvalue = cm_tsl_pick_conjunct(ready,
      `cm_lvalue ${expression:cm_expr}`);
  thm cursors_ready = cm_tsl_pick_conjunct(ready,
      `cm_cursors_type_ready (p:cm_program) (fid:int)
        (cm_ann_cursors (ann:cm_annotation))`);
  term output_type =
      `cm_lvalue_output_type (p:cm_program) ${function:cm_function_d}
        ${expression:cm_expr}`;
  thm input_ready = cm_tsl_pick_conjunct(ready,
      `cm_cursor_head_input_type_ready (p:cm_program) (fid:int)
        ${output_type:cm_type} (cm_ann_cursors (ann:cm_annotation))`);
  thm lvalue_ready = cm_tsl_pick_conjunct(ready,
      `cm_cursor_head_lvalue_type_ready (p:cm_program) (fid:int)
        ${output_type:cm_type} (cm_ann_cursors (ann:cm_annotation))`);
  thm op_two = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_lvalue_def())), lvalue);
  thm wf_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      op_two, get_cm_expr_wf_def(), get_cm_unary_types_def(),
      get_cm_expr_type_def(), get_theorem_by_name("COND_CLAUSES"))),
      expression_wf);
  thm arg_wf = cm_tsl_pick_conjunct(wf_open,
      `cm_expr_wf (p:cm_program) ${function:cm_function_d}
        (arg:cm_expr)`);
  thm arg_pointer = cm_tsl_pick_conjunct(wf_open,
      `cm_is_pointer (cm_expr_type (arg:cm_expr))`);
  thm result_type = cm_tsl_pick_conjunct(wf_open,
      `(ty:cm_type) == cm_pointee (cm_expr_type (arg:cm_expr))`);
  thm pointer_shape = mp_rule(spec_rule(
      `cm_expr_type (arg:cm_expr)`, cm_pointer_type_reconstruct),
      arg_pointer);
  thm output_equal = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        op_two, result_type, pointer_shape,
        get_cm_lvalue_output_type_def(), get_cm_expr_array_def(),
        get_cm_expr_type_def(), get_theorem_by_name("COND_CLAUSES"))),
      mk_eq(output_type, `cm_expr_type (arg:cm_expr)`)));
  thm arg_scalar = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        arg_pointer, get_cm_scalar_expr_type_def(),
        get_cm_integer_type_def(), get_cm_is_pointer_def())),
      `cm_scalar_expr_type (cm_expr_type (arg:cm_expr))`));
  thm arg_input = conv_rule(rewrite_conv(THM_LIST(output_equal)),
      input_ready);
  thm arg_values = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, output_type, `arg:cm_expr`,
      `cm_ann_cursors (ann:cm_annotation)`),
      cm_lvalue_cursor_expr_values), lvalue_ready), output_equal);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      same_program, op_two, fid_low, fid_high, arg_wf, arg_scalar,
      cursors_ready, arg_input, arg_values,
      get_cm_task_type_ready_def(), get_cm_step_def(),
      get_cm_lstart_def(), cm_annotation_step_def, cm_update_l_def,
      cm_update_annotation_def, cm_ann_cursors_def,
      get_theorem_by_name("COND_CLAUSES"))), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eqt_elim_rule(target_view));
  return gnode_prove(root);
}
PROOF static thm cm_l_unary_type_ready_step =
    cm_prove_l_unary_type_ready_step();

PROOF static thm cm_prove_l_index_type_ready_step(void) {
  term expression =
      `CMIndexE (base:cm_expr) (index:cm_expr) (ty:cm_type)`;
  term task =
      `CMLTask (q:cm_program) (fid:int) ${expression:cm_expr}
        (st:cm_src_state) (ks:(cm_frame)list)`;
  term function =
      `inth (fid:int) (cm_program_functions (p:cm_program))`;
  term phase =
      `CAIndexLP (index:cm_expr) (ty:cm_type)`;
  term old_cursors = `cm_ann_cursors (ann:cm_annotation)`;
  term new_cursors =
      `CMACursor ${phase:cm_aphase} (cm_ann_temp (ann:cm_annotation))
        (cm_ann_break ann) (cm_ann_continue ann) ::
        ${old_cursors:(cm_acursor)list}`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (q:cm_program) (fid:int)
         (base:cm_expr) (index:cm_expr) (ty:cm_type)
         (st:cm_src_state) (ks:(cm_frame)list) (ann:cm_annotation).
         cm_typed_program p ==>
         cm_task_succeeds
           (CMLTask q fid (CMIndexE base index ty) st ks) ==>
         cm_task_type_ready p
           (CMLTask q fid (CMIndexE base index ty) st ks) ann ==>
         cm_task_type_ready p
           (cm_step (CMLTask q fid (CMIndexE base index ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMLTask q fid (CMIndexE base index ty) st ks) ann))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm ready = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_task_type_ready_def())), assume_rule(
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        (ann:cm_annotation)`));
  thm same_program = cm_tsl_pick_conjunct(ready,
      `(q:cm_program) == (p:cm_program)`);
  thm fid_low = cm_tsl_pick_conjunct(ready, `0i <= (fid:int)`);
  thm fid_high = cm_tsl_pick_conjunct(ready,
      `(fid:int) < ilength (cm_program_functions (p:cm_program))`);
  thm expression_wf = cm_tsl_pick_conjunct(ready,
      `cm_expr_wf (p:cm_program) ${function:cm_function_d}
        ${expression:cm_expr}`);
  thm wf_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_expr_wf_def())), expression_wf);
  thm base_wf = cm_tsl_pick_conjunct(wf_open,
      `cm_expr_wf (p:cm_program) ${function:cm_function_d}
        (base:cm_expr)`);
  thm index_wf = cm_tsl_pick_conjunct(wf_open,
      `cm_expr_wf (p:cm_program) ${function:cm_function_d}
        (index:cm_expr)`);
  thm base_pointer = cm_tsl_pick_conjunct(wf_open,
      `cm_is_pointer (cm_expr_type (base:cm_expr))`);
  thm index_integer = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        wf_open, get_cm_integer_type_def())),
      `cm_integer_type (cm_expr_type (index:cm_expr))`));
  thm result_type = cm_tsl_pick_conjunct(wf_open,
      `(ty:cm_type) == cm_pointee (cm_expr_type (base:cm_expr))`);
  thm pointer_shape = mp_rule(spec_rule(
      `cm_expr_type (base:cm_expr)`, cm_pointer_type_reconstruct),
      base_pointer);
  thm output_base = trans_rule(
      beta_norm(ap_term_rule(`\source:cm_type. CMPtrTy source`,
        result_type)), pointer_shape);
  term output_type =
      `cm_lvalue_output_type (p:cm_program) ${function:cm_function_d}
        ${expression:cm_expr}`;
  thm output_ptr = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_lvalue_output_type_def(), get_cm_expr_array_def(),
        get_cm_expr_type_def(), get_theorem_by_name("COND_CLAUSES"))),
      mk_eq(output_type, `CMPtrTy (ty:cm_type)`)));
  thm base_scalar = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        base_pointer, get_cm_scalar_expr_type_def(),
        get_cm_integer_type_def(), get_cm_is_pointer_def())),
      `cm_scalar_expr_type (cm_expr_type (base:cm_expr))`));
  thm cursors_ready = cm_tsl_pick_conjunct(ready,
      `cm_cursors_type_ready (p:cm_program) (fid:int)
        ${old_cursors:(cm_acursor)list}`);
  thm input_ready = cm_tsl_pick_conjunct(ready,
      `cm_cursor_head_input_type_ready (p:cm_program) (fid:int)
        ${output_type:cm_type} ${old_cursors:(cm_acursor)list}`);
  thm lvalue_ready = cm_tsl_pick_conjunct(ready,
      `cm_cursor_head_lvalue_type_ready (p:cm_program) (fid:int)
        ${output_type:cm_type} ${old_cursors:(cm_acursor)list}`);
  thm parent_input = conv_rule(rewrite_conv(THM_LIST(output_ptr)),
      input_ready);
  thm typed = assume_rule(`cm_typed_program (p:cm_program)`);
  thm function_wf = match_mp_rule(match_mp_rule(
      spec_rule(`fid:int`, conjunct1_rule(conjunct2_rule(
        conjunct2_rule(conjunct2_rule(conv_rule(
          rewrite_conv(THM_LIST(get_cm_typed_program_def())),
          typed)))))),
      fid_low), fid_high);
  thm function_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_function_wf_def())), function_wf);
  thm params_wf = conjunct1_rule(conjunct2_rule(function_open));
  thm params_slots = conjunct1_rule(conv_rule(rewrite_conv(THM_LIST(
      get_cm_params_wf_def())), params_wf));
  thm locals_slots = conjunct1_rule(conjunct2_rule(
      conjunct2_rule(function_open)));
  thm base_refs = match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `base:cm_expr`, `p:cm_program`, function),
        cm_expr_result_refs), typed), params_slots), locals_slots);
  base_refs = match_mp_rule(base_refs, base_wf);
  thm ty_refs = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `cm_program_structs (p:cm_program)`,
      `cm_expr_type (base:cm_expr)`), cm_type_refs_pointee),
      base_refs), base_pointer);
  thm ty_refs_equal = beta_norm(ap_term_rule(
      `\subject:cm_type.
         cm_type_refs (cm_program_structs (p:cm_program)) subject`,
      sym_rule(result_type)));
  ty_refs = eq_mp_rule(ty_refs_equal, ty_refs);
  thm phase_static = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_static_type_ready_def(), index_wf, index_integer,
        ty_refs)),
      `cm_phase_static_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase}`));
  thm phase_parent = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_parent_type_ready_def(), parent_input)),
      `cm_phase_parent_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase} ${old_cursors:(cm_acursor)list}`));
  thm next_fid = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(cm_phase_next_fid_def)),
      `cm_phase_next_fid (fid:int) ${phase:cm_aphase} == fid`));
  thm phase_results = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_result_type_def(), output_ptr)),
      `!(result_ty:cm_type).
         cm_phase_result_type (p:cm_program) (fid:int)
           ${phase:cm_aphase} result_ty ==>
         result_ty == ${output_type:cm_type}`));
  thm phase_result = mp_rule(mp_rule(mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, phase, output_type, old_cursors),
      cm_phase_result_from_lvalue), lvalue_ready), phase_results),
      next_fid);
  term next_rest_term =
      `cm_cursors_type_ready (p:cm_program)
        (cm_phase_next_fid (fid:int) ${phase:cm_aphase})
        ${old_cursors:(cm_acursor)list}`;
  thm next_rest_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      cm_phase_next_fid_def)), next_rest_term);
  thm next_rest = eq_mp_rule(sym_rule(next_rest_view), cursors_ready);
  thm new_ready = mp_rule(mp_rule(mp_rule(mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, phase,
        `cm_ann_temp (ann:cm_annotation)`, `cm_ann_break ann`,
        `cm_ann_continue ann`, old_cursors), cm_cursor_push_type_ready),
      phase_static), phase_parent), phase_result), next_rest);
  thm phase_input = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_input_type_ready_def(), output_base)),
      `cm_phase_input_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase} (cm_expr_type (base:cm_expr))`));
  thm new_input = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, phase,
      `cm_expr_type (base:cm_expr)`,
      `cm_ann_temp (ann:cm_annotation)`, `cm_ann_break ann`,
      `cm_ann_continue ann`, old_cursors),
      cm_cursor_push_input_ready), phase_input);
  thm phase_expr = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_expr_type_ready_def(), output_base)),
      `cm_phase_expr_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase} (base:cm_expr)`));
  thm new_values = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, phase, `base:cm_expr`,
      `cm_ann_temp (ann:cm_annotation)`, `cm_ann_break ann`,
      `cm_ann_continue ann`, old_cursors),
      cm_cursor_push_expr_values_ready), phase_expr);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      same_program, fid_low, fid_high, base_wf, base_scalar,
      new_ready, new_input, new_values,
      get_cm_task_type_ready_def(), get_cm_step_def(),
      get_cm_lstart_def(), cm_annotation_step_def, cm_update_l_def,
      cm_update_annotation_def, cm_ann_push_def, cm_ann_cursors_def)),
      goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eqt_elim_rule(target_view));
  return gnode_prove(root);
}
PROOF static thm cm_l_index_type_ready_step =
    cm_prove_l_index_type_ready_step();

PROOF static thm cm_prove_l_member_type_ready_step(void) {
  term expression =
      `CMMemberE (base:cm_expr) (mid:int) (ty:cm_type)`;
  term task =
      `CMLTask (q:cm_program) (fid:int) ${expression:cm_expr}
        (st:cm_src_state) (ks:(cm_frame)list)`;
  term function =
      `inth (fid:int) (cm_program_functions (p:cm_program))`;
  term phase =
      `CAMemberP (mid:int) (cm_expr_type (base:cm_expr))`;
  term old_cursors = `cm_ann_cursors (ann:cm_annotation)`;
  term new_cursors =
      `CMACursor ${phase:cm_aphase} (cm_ann_temp (ann:cm_annotation))
        (cm_ann_break ann) (cm_ann_continue ann) ::
        ${old_cursors:(cm_acursor)list}`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (q:cm_program) (fid:int)
         (base:cm_expr) (mid:int) (ty:cm_type)
         (st:cm_src_state) (ks:(cm_frame)list) (ann:cm_annotation).
         cm_task_succeeds
           (CMLTask q fid (CMMemberE base mid ty) st ks) ==>
         cm_task_type_ready p
           (CMLTask q fid (CMMemberE base mid ty) st ks) ann ==>
         cm_task_type_ready p
           (cm_step (CMLTask q fid (CMMemberE base mid ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMLTask q fid (CMMemberE base mid ty) st ks) ann))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm ready = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_task_type_ready_def())), assume_rule(
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        (ann:cm_annotation)`));
  thm same_program = cm_tsl_pick_conjunct(ready,
      `(q:cm_program) == (p:cm_program)`);
  thm fid_low = cm_tsl_pick_conjunct(ready, `0i <= (fid:int)`);
  thm fid_high = cm_tsl_pick_conjunct(ready,
      `(fid:int) < ilength (cm_program_functions (p:cm_program))`);
  thm expression_wf = cm_tsl_pick_conjunct(ready,
      `cm_expr_wf (p:cm_program) ${function:cm_function_d}
        ${expression:cm_expr}`);
  thm wf_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_expr_wf_def())), expression_wf);
  thm base_wf = cm_tsl_pick_conjunct(wf_open,
      `cm_expr_wf (p:cm_program) ${function:cm_function_d}
        (base:cm_expr)`);
  thm member_valid = cm_tsl_pick_conjunct(wf_open,
      `cm_member_valid (p:cm_program)
        (cm_expr_type (base:cm_expr)) (mid:int)`);
  thm valid_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_member_valid_def())), member_valid);
  thm base_pointer = cm_tsl_pick_conjunct(valid_open,
      `cm_is_pointer (cm_expr_type (base:cm_expr))`);
  thm base_scalar = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        base_pointer, get_cm_scalar_expr_type_def(),
        get_cm_integer_type_def(), get_cm_is_pointer_def())),
      `cm_scalar_expr_type (cm_expr_type (base:cm_expr))`));
  term output_type =
      `cm_lvalue_output_type (p:cm_program) ${function:cm_function_d}
        ${expression:cm_expr}`;
  thm output_raw = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, function, `base:cm_expr`, `mid:int`, `ty:cm_type`),
      cm_member_lvalue_output_type), expression_wf);
  thm output_view = apply_conversion(rewrite_conv(THM_LIST(
      get_cm_member_lvalue_type_def())),
      mk_eq(output_type,
        `cm_member_lvalue_type (p:cm_program)
          (cm_expr_type (base:cm_expr)) (mid:int)`));
  thm output_equal = eq_mp_rule(sym_rule(output_view), output_raw);
  thm cursors_ready = cm_tsl_pick_conjunct(ready,
      `cm_cursors_type_ready (p:cm_program) (fid:int)
        ${old_cursors:(cm_acursor)list}`);
  thm input_ready = cm_tsl_pick_conjunct(ready,
      `cm_cursor_head_input_type_ready (p:cm_program) (fid:int)
        ${output_type:cm_type} ${old_cursors:(cm_acursor)list}`);
  thm lvalue_ready = cm_tsl_pick_conjunct(ready,
      `cm_cursor_head_lvalue_type_ready (p:cm_program) (fid:int)
        ${output_type:cm_type} ${old_cursors:(cm_acursor)list}`);
  thm parent_input = conv_rule(rewrite_conv(THM_LIST(output_equal)),
      input_ready);
  thm phase_static = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_static_type_ready_def(), member_valid)),
      `cm_phase_static_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase}`));
  thm phase_parent = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_parent_type_ready_def(), parent_input)),
      `cm_phase_parent_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase} ${old_cursors:(cm_acursor)list}`));
  thm next_fid = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(cm_phase_next_fid_def)),
      `cm_phase_next_fid (fid:int) ${phase:cm_aphase} == fid`));
  thm phase_results = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_result_type_def(), output_equal)),
      `!(result_ty:cm_type).
         cm_phase_result_type (p:cm_program) (fid:int)
           ${phase:cm_aphase} result_ty ==>
         result_ty == ${output_type:cm_type}`));
  thm phase_result = mp_rule(mp_rule(mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, phase, output_type, old_cursors),
      cm_phase_result_from_lvalue), lvalue_ready), phase_results),
      next_fid);
  term next_rest_term =
      `cm_cursors_type_ready (p:cm_program)
        (cm_phase_next_fid (fid:int) ${phase:cm_aphase})
        ${old_cursors:(cm_acursor)list}`;
  thm next_rest_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      cm_phase_next_fid_def)), next_rest_term);
  thm next_rest = eq_mp_rule(sym_rule(next_rest_view), cursors_ready);
  thm new_ready = mp_rule(mp_rule(mp_rule(mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, phase,
        `cm_ann_temp (ann:cm_annotation)`, `cm_ann_break ann`,
        `cm_ann_continue ann`, old_cursors), cm_cursor_push_type_ready),
      phase_static), phase_parent), phase_result), next_rest);
  thm phase_input = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_input_type_ready_def())),
      `cm_phase_input_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase} (cm_expr_type (base:cm_expr))`));
  thm new_input = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, phase,
      `cm_expr_type (base:cm_expr)`,
      `cm_ann_temp (ann:cm_annotation)`, `cm_ann_break ann`,
      `cm_ann_continue ann`, old_cursors),
      cm_cursor_push_input_ready), phase_input);
  thm phase_expr = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_expr_type_ready_def())),
      `cm_phase_expr_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase} (base:cm_expr)`));
  thm new_values = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, phase, `base:cm_expr`,
      `cm_ann_temp (ann:cm_annotation)`, `cm_ann_break ann`,
      `cm_ann_continue ann`, old_cursors),
      cm_cursor_push_expr_values_ready), phase_expr);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      same_program, fid_low, fid_high, base_wf, base_scalar,
      new_ready, new_input, new_values,
      get_cm_task_type_ready_def(), get_cm_step_def(),
      get_cm_lstart_def(), cm_annotation_step_def, cm_update_l_def,
      cm_update_annotation_def, cm_ann_push_def, cm_ann_cursors_def)),
      goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eqt_elim_rule(target_view));
  return gnode_prove(root);
}
PROOF static thm cm_l_member_type_ready_step =
    cm_prove_l_member_type_ready_step();

PROOF static void cm_tsl_close_invalid(
    gnode node, thm ready, term expression) {
  thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_task_type_ready_def())), ready);
  thm lvalue = cm_tsl_pick_conjunct(opened,
      mk_comb(`cm_lvalue`, expression));
  thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_lvalue_def())), lvalue);
  CONTR_TAC(node, impossible);
}

PROOF static thm cm_prove_l_type_ready_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(expr:cm_expr) (p:cm_program) (q:cm_program) (fid:int)
         (st:cm_src_state) (ks:(cm_frame)list) (ann:cm_annotation).
         cm_typed_program p ==>
         cm_task_succeeds (CMLTask q fid expr st ks) ==>
         cm_task_type_ready p (CMLTask q fid expr st ks) ann ==>
         cm_task_type_ready p
           (cm_step (CMLTask q fid expr st ks))
           (cm_update_annotation
             (cm_annotation_step (CMLTask q fid expr st ks) ann))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`expr:cm_expr`, get_cm_expr_cases()), "Hex");
  term constructors[14] = {
    `CMConstE (a0:int) (a1:cm_type)`,
    `CMStringE (a0:int) (a1:cm_type)`,
    `CMVarE (a0:int) (a1:int) (a2:cm_type)`,
    `CMAssignE (a0:cm_expr) (a1:cm_expr) (a2:cm_type)`,
    `CMBinaryE (a0:int) (a1:cm_expr) (a2:cm_expr) (a3:cm_type)`,
    `CMUnaryE (a0:int) (a1:cm_expr) (a2:cm_type)`,
    `CMIndexE (a0:cm_expr) (a1:cm_expr) (a2:cm_type)`,
    `CMMemberE (a0:cm_expr) (a1:int) (a2:cm_type)`,
    `CMCallE (a0:int) (a1:(cm_expr)list) (a2:cm_type)`,
    `CMSizeofE (a0:cm_type) (a1:cm_type)`,
    `CMGetcE (a:cm_type)`,
    `CMPutcE (a0:cm_expr) (a1:cm_type)`,
    `CMPutiE (a0:cm_expr) (a1:cm_type)`,
    `CMExitE (a0:cm_expr) (a1:cm_type)`
  };
  for (size_t i = 0; i < vector_size(cases); ++i) {
    while (true) {
      labeled_term_list assumptions = goal_lasmps(cases[i]->g);
      int shape_index = labeled_term_list_index(assumptions, "Hex");
      if (!is_exists(assumptions[shape_index].tm)) break;
      cases[i] = ASMP_EXISTS_TAC(cases[i], "Hex", NULL);
    }
    gnode leaf = cases[i];
    labeled_term_list assumptions = goal_lasmps(leaf->g);
    thm shape = assume_rule(assumptions[
        labeled_term_list_index(assumptions, "Hex")].tm);
    term generic_task =
        `CMLTask (q:cm_program) (fid:int) (expr:cm_expr)
          (st:cm_src_state) (ks:(cm_frame)list)`;
    thm typed = assume_rule(`cm_typed_program (p:cm_program)`);
    thm succeeds = conv_rule(rewrite_conv(THM_LIST(shape)),
        assume_rule(`cm_task_succeeds ${generic_task:cm_task}`));
    thm ready = conv_rule(rewrite_conv(THM_LIST(shape)), assume_rule(
        `cm_task_type_ready (p:cm_program) ${generic_task:cm_task}
          (ann:cm_annotation)`));
    thm target_view = apply_conversion(rewrite_conv(THM_LIST(shape)),
        goal_ccl(leaf->g));
    thm result = empty_theorem;
    if (i == 2) {
      result = specl_rule(TERM_LIST(
          `p:cm_program`, `q:cm_program`, `fid:int`, `a0:int`,
          `a1:int`, `a2:cm_type`, `st:cm_src_state`,
          `ks:(cm_frame)list`, `ann:cm_annotation`),
          cm_l_var_type_ready_step);
    } else if (i == 5) {
      result = specl_rule(TERM_LIST(
          `p:cm_program`, `q:cm_program`, `fid:int`, `a0:int`,
          `a1:cm_expr`, `a2:cm_type`, `st:cm_src_state`,
          `ks:(cm_frame)list`, `ann:cm_annotation`),
          cm_l_unary_type_ready_step);
    } else if (i == 6) {
      result = specl_rule(TERM_LIST(
          `p:cm_program`, `q:cm_program`, `fid:int`, `a0:cm_expr`,
          `a1:cm_expr`, `a2:cm_type`, `st:cm_src_state`,
          `ks:(cm_frame)list`, `ann:cm_annotation`),
          cm_l_index_type_ready_step);
      result = mp_rule(result, typed);
    } else if (i == 7) {
      result = specl_rule(TERM_LIST(
          `p:cm_program`, `q:cm_program`, `fid:int`, `a0:cm_expr`,
          `a1:int`, `a2:cm_type`, `st:cm_src_state`,
          `ks:(cm_frame)list`, `ann:cm_annotation`),
          cm_l_member_type_ready_step);
    } else {
      cm_tsl_close_invalid(leaf, ready, constructors[i]);
      continue;
    }
    result = mp_rule(mp_rule(result, succeeds), ready);
    if (alpha_compare(concl(result), rhs_of(target_view)) != 0) {
      result = conv_rule(rewrite_conv(THM_LIST(shape)), result);
    }
    ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), result));
  }
  return gnode_prove(root);
}
PROOF thm cm_l_type_ready_step =
    cm_prove_l_type_ready_step();

PROOF static int cmc_preservation_type_source_l_final_checks(void) {
  ENSURE_COND(vector_size(hyp(cm_l_var_type_ready_step)) == 0 &&
      vector_size(hyp(cm_l_unary_type_ready_step)) == 0 &&
      vector_size(hyp(cm_l_index_type_ready_step)) == 0 &&
      vector_size(hyp(cm_l_member_type_ready_step)) == 0 &&
      vector_size(hyp(cm_l_type_ready_step)) == 0,
      "lvalue type-step theorem has assumptions");
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_type_source_l_axioms_before,
      "cmc_preservation_type_source_l introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_type_source_l_checks =
    cmc_preservation_type_source_l_final_checks();
