#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_code.h"
#include "cmc_preservation_target_expr.h"
#include "cmc_preservation_target_address.h"
#include "cmc_preservation_target_call_complete.h"

#require "cmc_preservation_code.c"
#require "cmc_preservation_target_machine.c"
#require "cmc_preservation_target_address.c"
#require "cmc_preservation_target_call_complete.c"

PROOF static size_t _cmc_preservation_target_expr_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_target_r_zero_step(
    const term expr, const term_list premises) {
  term task =
      `CMRTask (p:cm_program) (fid:int) ${expr:cm_expr}
        (st:cm_src_state) (ks:(cm_frame)list)`;
  term old_sim =
      `cm_task_target_sim (p:cm_program) ${task:cm_task}
        (target:tvm_task) (ann:cm_annotation)`;
  term update =
      `cm_annotation_step ${task:cm_task} (ann:cm_annotation)`;
  term target_sim =
      `cm_task_target_sim (p:cm_program)
        (cm_step ${task:cm_task})
        (tvm_iter (cm_update_steps ${update:cm_aupdate})
          (target:tvm_task))
        (cm_update_annotation ${update:cm_aupdate})`;
  term_list antecedents = (term_list)vector_copy(premises);
  vector_add(&antecedents, old_sim);
  term body = imp_chain(antecedents, target_sim);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm running = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_target_sim_def)), assume_rule(old_sim));
  term updated =
      `cm_update_annotation ${update:cm_aupdate}`;
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `[]:(cm_value)list`, `ann:cm_annotation`,
      updated, `target:tvm_task`), get_cm_target_reannotate());
  thm_list annotation_rules = THM_LIST(
      cm_annotation_step_def, cm_update_r_def,
      cm_update_annotation_def, cm_ann_push_def,
      cm_ann_pc_def, cm_ann_calls_def, cm_ann_spills_def,
      cm_ann_saved_def, get_theorem_by_name("NOT_CONS_NIL"));
  for (size_t i = 0; i < vector_size(premises); ++i) {
    vector_add(&annotation_rules, assume_rule(premises[i]));
  }
  term_list selectors = TERM_LIST(
      `cm_ann_pc:cm_annotation->int`,
      `cm_ann_calls:cm_annotation->(cm_call_sim_frame)list`,
      `cm_ann_spills:cm_annotation->(cm_spill)list`,
      `cm_ann_saved:cm_annotation->(cm_spill_frame)list`);
  for (size_t i = 0; i < vector_size(selectors); ++i) {
    term equality = mk_eq(
        mk_comb(selectors[i], updated),
        mk_comb(selectors[i], `ann:cm_annotation`));
    result = match_mp_rule(result, eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(annotation_rules), equality)));
  }
  result = match_mp_rule(result, running);
  result = conv_rule(
      reduce_rewrite_conv(annotation_rules), result);
  thm_list goal_rules = THM_LIST(
      get_cm_step_def(), get_cm_rstart_def(),
      cm_annotation_step_def, cm_update_r_def,
      cm_update_steps_def, cm_update_annotation_def,
      cm_ann_push_def, get_tvm_iter_def(),
      cm_task_target_sim_def,
      get_theorem_by_name("NOT_CONS_NIL"));
  for (size_t i = 0; i < vector_size(premises); ++i) {
    vector_add(&goal_rules, assume_rule(premises[i]));
  }
  gnode reduced = CONV_TAC(
      leaf, reduce_rewrite_conv(goal_rules));
  ACCEPT_TAC(reduced, result);
  return gnode_prove(root);
}

PROOF static thm cm_target_r_assign_step =
    cm_prove_target_r_zero_step(
      `CMAssignE (dst:cm_expr) (src:cm_expr) (ty:cm_type)`,
      TERM_LIST());
PROOF static thm cm_target_r_binary_start_step =
    cm_prove_target_r_zero_step(
      `CMBinaryE (op:int) (left:cm_expr) (right:cm_expr)
        (ty:cm_type)`,
      TERM_LIST());
PROOF static thm cm_target_r_index_start_step =
    cm_prove_target_r_zero_step(
      `CMIndexE (base:cm_expr) (index:cm_expr) (ty:cm_type)`,
      TERM_LIST());
PROOF static thm cm_target_r_putc_start_step =
    cm_prove_target_r_zero_step(
      `CMPutcE (arg:cm_expr) (ty:cm_type)`,
      TERM_LIST());
PROOF static thm cm_target_r_puti_start_step =
    cm_prove_target_r_zero_step(
      `CMPutiE (arg:cm_expr) (ty:cm_type)`,
      TERM_LIST());
PROOF static thm cm_target_r_exit_start_step =
    cm_prove_target_r_zero_step(
      `CMExitE (arg:cm_expr) (ty:cm_type)`,
      TERM_LIST());

PROOF static thm cm_target_r_var_scalar_step =
    cm_prove_target_r_zero_step(
      `CMVarE (scope:int) (slot:int) (ty:cm_type)`,
      TERM_LIST(
        `~cm_binding_array (p:cm_program) (fid:int)
          (scope:int) (slot:int)`));
PROOF static thm cm_target_r_unary_load_start_step =
    cm_prove_target_r_zero_step(
      `CMUnaryE (op:int) (arg:cm_expr) (ty:cm_type)`,
      TERM_LIST(`(op:int) == 2i`));
PROOF static thm cm_target_r_unary_address_start_step =
    cm_prove_target_r_zero_step(
      `CMUnaryE (op:int) (arg:cm_expr) (ty:cm_type)`,
      TERM_LIST(`~((op:int) == 2i)`, `(op:int) == 3i`));
PROOF static thm cm_target_r_unary_value_start_step =
    cm_prove_target_r_zero_step(
      `CMUnaryE (op:int) (arg:cm_expr) (ty:cm_type)`,
      TERM_LIST(`~((op:int) == 2i)`, `~((op:int) == 3i)`));
PROOF static thm cm_target_r_member_array_start_step =
    cm_prove_target_r_zero_step(
      `CMMemberE (base:cm_expr) (mid:int) (ty:cm_type)`,
      TERM_LIST(
        `cm_member_array (p:cm_program)
          (cm_expr_type (base:cm_expr)) (mid:int)`));
PROOF static thm cm_target_r_member_scalar_start_step =
    cm_prove_target_r_zero_step(
      `CMMemberE (base:cm_expr) (mid:int) (ty:cm_type)`,
      TERM_LIST(
        `~cm_member_array (p:cm_program)
          (cm_expr_type (base:cm_expr)) (mid:int)`));
PROOF static thm cm_target_r_call_args_start_step =
    cm_prove_target_r_zero_step(
      `CMCallE (callee:int)
        ((arg:cm_expr) :: (args:(cm_expr)list)) (ty:cm_type)`,
      TERM_LIST());

PROOF static thm cm_prove_target_l_zero_step(
    const term expr, const term_list premises) {
  term task =
      `CMLTask (p:cm_program) (fid:int) ${expr:cm_expr}
        (st:cm_src_state) (ks:(cm_frame)list)`;
  term old_sim =
      `cm_task_target_sim (p:cm_program) ${task:cm_task}
        (target:tvm_task) (ann:cm_annotation)`;
  term update =
      `cm_annotation_step ${task:cm_task} (ann:cm_annotation)`;
  term target_sim =
      `cm_task_target_sim (p:cm_program)
        (cm_step ${task:cm_task})
        (tvm_iter (cm_update_steps ${update:cm_aupdate})
          (target:tvm_task))
        (cm_update_annotation ${update:cm_aupdate})`;
  term_list antecedents = (term_list)vector_copy(premises);
  vector_add(&antecedents, old_sim);
  term body = imp_chain(antecedents, target_sim);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm running = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_target_sim_def)), assume_rule(old_sim));
  term updated =
      `cm_update_annotation ${update:cm_aupdate}`;
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `[]:(cm_value)list`, `ann:cm_annotation`,
      updated, `target:tvm_task`), get_cm_target_reannotate());
  thm_list annotation_rules = THM_LIST(
      cm_annotation_step_def, cm_update_l_def,
      cm_update_annotation_def, cm_ann_push_def,
      cm_ann_pc_def, cm_ann_calls_def, cm_ann_spills_def,
      cm_ann_saved_def);
  for (size_t i = 0; i < vector_size(premises); ++i) {
    vector_add(&annotation_rules, assume_rule(premises[i]));
  }
  term_list selectors = TERM_LIST(
      `cm_ann_pc:cm_annotation->int`,
      `cm_ann_calls:cm_annotation->(cm_call_sim_frame)list`,
      `cm_ann_spills:cm_annotation->(cm_spill)list`,
      `cm_ann_saved:cm_annotation->(cm_spill_frame)list`);
  for (size_t i = 0; i < vector_size(selectors); ++i) {
    term equality = mk_eq(
        mk_comb(selectors[i], updated),
        mk_comb(selectors[i], `ann:cm_annotation`));
    result = match_mp_rule(result, eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(annotation_rules), equality)));
  }
  result = match_mp_rule(result, running);
  result = conv_rule(
      reduce_rewrite_conv(annotation_rules), result);
  thm_list goal_rules = THM_LIST(
      get_cm_step_def(), get_cm_lstart_def(),
      cm_annotation_step_def, cm_update_l_def,
      cm_update_steps_def, cm_update_annotation_def,
      cm_ann_push_def, get_tvm_iter_def(),
      cm_task_target_sim_def);
  for (size_t i = 0; i < vector_size(premises); ++i) {
    vector_add(&goal_rules, assume_rule(premises[i]));
  }
  gnode reduced = CONV_TAC(
      leaf, reduce_rewrite_conv(goal_rules));
  ACCEPT_TAC(reduced, result);
  return gnode_prove(root);
}

PROOF static thm cm_target_l_unary_address_step =
    cm_prove_target_l_zero_step(
      `CMUnaryE (op:int) (arg:cm_expr) (ty:cm_type)`,
      TERM_LIST(`(op:int) == 2i`));
PROOF static thm cm_target_l_index_start_step =
    cm_prove_target_l_zero_step(
      `CMIndexE (base:cm_expr) (index:cm_expr) (ty:cm_type)`,
      TERM_LIST());
PROOF static thm cm_target_l_member_start_step =
    cm_prove_target_l_zero_step(
      `CMMemberE (base:cm_expr) (mid:int) (ty:cm_type)`,
      TERM_LIST());

PROOF static thm cm_prove_target_r_push_step(
    const term expr, const term immediate, const term value,
    const thm_list number_rules) {
  term task =
      `CMRTask (p:cm_program) (fid:int) ${expr:cm_expr}
        (st:cm_src_state) (ks:(cm_frame)list)`;
  term layout =
      `cm_task_layout (p:cm_program) ${task:cm_task}
        (ann:cm_annotation)`;
  term target_sim =
      `cm_task_target_sim (p:cm_program) ${task:cm_task}
        (target:tvm_task) (ann:cm_annotation)`;
  term update =
      `cm_annotation_step ${task:cm_task} (ann:cm_annotation)`;
  term next_sim =
      `cm_task_target_sim (p:cm_program)
        (cm_step ${task:cm_task})
        (tvm_iter (cm_update_steps ${update:cm_aupdate})
          (target:tvm_task))
        (cm_update_annotation ${update:cm_aupdate})`;
  term body = mk_imp(layout, mk_imp(target_sim, next_sim));
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);

  thm layout_open = conv_rule(rewrite_conv(THM_LIST(
      cm_task_layout_def)), assume_rule(layout));
  thm code_at = conjunct1_rule(layout_open);
  thm_list code_rules = THM_LIST(
      cm_task_code_def, get_cm_emit_rvalue_def(),
      get_cm_emit_expr_pair_def(), get_cm_rcode_of_def(),
      get_cm_push_code_def(), get_theorem_by_name("APPEND"));
  code_at = conv_rule(reduce_rewrite_conv(code_rules), code_at);

  thm running = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_target_sim_def)), assume_rule(target_sim));
  term rest =
      `cm_cont_code (p:cm_program) (fid:int)
        (cm_ann_pc (ann:cm_annotation) +
         cm_rvalue_code_count p fid ${expr:cm_expr})
        (cm_ann_temp ann) (cm_ann_cursors ann)`;
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `[]:(cm_value)list`, `ann:cm_annotation`,
      `target:tvm_task`, value, immediate, rest),
      get_cm_target_push());
  result = match_mp_rule(result, code_at);
  result = match_mp_rule(result, running);
  result = match_mp_rule(result, eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))),
      `ilength ([]:(cm_value)list) < 65536i`)));
  term number_equality =
      `tower_wrap64 ${immediate:int} ==
       cm_value_number (st:cm_src_state) ${value:cm_value}`;
  result = match_mp_rule(result, eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(number_rules), number_equality)));
  thm_list goal_rules = THM_LIST(
      get_cm_step_def(), get_cm_rstart_def(),
      cm_annotation_step_def, cm_update_r_def,
      cm_update_steps_def, cm_update_annotation_def,
      cm_task_target_sim_def);
  gnode reduced = CONV_TAC(
      leaf, reduce_rewrite_conv(goal_rules));
  ACCEPT_TAC(reduced, result);
  return gnode_prove(root);
}

PROOF thm cm_target_r_const_step =
    cm_prove_target_r_push_step(
      `CMConstE (n:int) (ty:cm_type)`,
      `cm_const_immediate (ty:cm_type) (n:int)`,
      `cm_convert_value (st:cm_src_state)
        (ty:cm_type) (CMIntV (n:int))`,
      THM_LIST(get_cm_const_immediate_number_bridge()));
PROOF static thm cm_target_r_sizeof_step =
    cm_prove_target_r_push_step(
      `CMSizeofE (asked:cm_type) (ty:cm_type)`,
      `cm_type_size (cm_program_structs (p:cm_program))
        (asked:cm_type)`,
      `CMIntV
        (cm_type_size (cm_program_structs (p:cm_program))
          (asked:cm_type))`,
      THM_LIST(get_cm_value_number_def()));

PROOF static thm cm_prove_target_r_getc_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (ty:cm_type)
         (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation) (target:tvm_task).
         cm_task_layout p
           (CMRTask p fid (CMGetcE ty) st ks) ann ==>
         cm_task_target_sim p
           (CMRTask p fid (CMGetcE ty) st ks) target ann ==>
         (cm_state_input st == [] ||
          tower_byte_value (HD (cm_state_input st))) ==>
         cm_task_target_sim p
           (cm_step (CMRTask p fid (CMGetcE ty) st ks))
           (tvm_iter
             (cm_update_steps
               (cm_annotation_step
                 (CMRTask p fid (CMGetcE ty) st ks) ann))
             target)
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask p fid (CMGetcE ty) st ks) ann))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm layout = assume_rule(
      `cm_task_layout (p:cm_program)
        (CMRTask p (fid:int) (CMGetcE (ty:cm_type))
          (st:cm_src_state) (ks:(cm_frame)list))
        (ann:cm_annotation)`);
  thm code_at = conjunct1_rule(conv_rule(
      rewrite_conv(THM_LIST(cm_task_layout_def)), layout));
  code_at = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_code_def, get_cm_emit_rvalue_def(),
      get_cm_emit_expr_pair_def(), get_cm_rcode_of_def(),
      get_theorem_by_name("APPEND"))), code_at);
  thm running = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_target_sim_def)), assume_rule(
        `cm_task_target_sim (p:cm_program)
          (CMRTask p (fid:int) (CMGetcE (ty:cm_type))
            (st:cm_src_state) (ks:(cm_frame)list))
          (target:tvm_task) (ann:cm_annotation)`));
  term rest =
      `cm_cont_code (p:cm_program) (fid:int)
        (cm_ann_pc (ann:cm_annotation) +
         cm_rvalue_code_count p fid (CMGetcE (ty:cm_type)))
        (cm_ann_temp ann) (cm_ann_cursors ann)`;
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `[]:(cm_value)list`, `ann:cm_annotation`,
      `target:tvm_task`, rest), get_cm_target_getc());
  result = match_mp_rule(result, code_at);
  result = match_mp_rule(result, running);
  result = match_mp_rule(result, eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))),
      `ilength ([]:(cm_value)list) < 65536i`)));
  result = match_mp_rule(result,
      assume_rule(
        `cm_state_input (st:cm_src_state) == [] ||
         tower_byte_value
           (HD (cm_state_input (st:cm_src_state)))`));
  thm_list goal_rules = THM_LIST(
      get_cm_step_def(), get_cm_rstart_def(),
      cm_annotation_step_def, cm_update_r_def,
      cm_update_steps_def, cm_update_annotation_def,
      cm_task_target_sim_def);
  gnode_list cases = BOOL_CASES_TAC(
      leaf, `cm_state_input (st:cm_src_state) == []`, "Hempty");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    thm input_case = assume_rule(i == 0
        ? `cm_state_input (st:cm_src_state) == []`
        : `~(cm_state_input (st:cm_src_state) == [])`);
    thm head_byte = empty_theorem;
    if (i == 1) {
      thm input_ready = assume_rule(
          `cm_state_input (st:cm_src_state) == [] ||
           tower_byte_value
             (HD (cm_state_input (st:cm_src_state)))`);
      head_byte = mp_rule(mp_rule(
          taut_rule(imp_chain(TERM_LIST(
            concl(input_ready),
            `~(cm_state_input (st:cm_src_state) == [])`),
            `tower_byte_value
              (HD (cm_state_input (st:cm_src_state)))`)),
          input_ready), input_case);
    }
    thm branch_result = conv_rule(reduce_rewrite_conv(THM_LIST(
        input_case, cm_ann_linear_def,
        get_theorem_by_name("ILENGTH_DEF"))), result);
    thm_list branch_rules = (thm_list)vector_copy(goal_rules);
    vector_add(&branch_rules, input_case);
    if (!IS_NULL(head_byte)) vector_add(&branch_rules, head_byte);
    gnode reduced = CONV_TAC(
        cases[i], reduce_rewrite_conv(branch_rules));
    ACCEPT_TAC(reduced, branch_result);
  }
  return gnode_prove(root);
}
PROOF static thm cm_target_r_getc_step =
    cm_prove_target_r_getc_step();

PROOF static thm cm_prove_target_r_string_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (sid:int) (ty:cm_type)
         (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation) (target:tvm_task).
         cm_task_layout p
           (CMRTask p fid (CMStringE sid ty) st ks) ann ==>
         cm_task_target_sim p
           (CMRTask p fid (CMStringE sid ty) st ks) target ann ==>
         tower_wrap64 (cm_string_address p sid) ==
           cm_value_number st (cm_string_pointer p sid) ==>
         cm_task_target_sim p
           (cm_step (CMRTask p fid (CMStringE sid ty) st ks))
           (tvm_iter
             (cm_update_steps
               (cm_annotation_step
                 (CMRTask p fid (CMStringE sid ty) st ks) ann))
             target)
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask p fid (CMStringE sid ty) st ks) ann))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm layout = assume_rule(
      `cm_task_layout (p:cm_program)
        (CMRTask p (fid:int)
          (CMStringE (sid:int) (ty:cm_type))
          (st:cm_src_state) (ks:(cm_frame)list))
        (ann:cm_annotation)`);
  thm code_at = conjunct1_rule(conv_rule(
      rewrite_conv(THM_LIST(cm_task_layout_def)), layout));
  code_at = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_code_def, get_cm_emit_rvalue_def(),
      get_cm_emit_expr_pair_def(), get_cm_rcode_of_def(),
      get_cm_push_code_def(), get_theorem_by_name("APPEND"))),
      code_at);
  thm running = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_target_sim_def)), assume_rule(
        `cm_task_target_sim (p:cm_program)
          (CMRTask p (fid:int)
            (CMStringE (sid:int) (ty:cm_type))
            (st:cm_src_state) (ks:(cm_frame)list))
          (target:tvm_task) (ann:cm_annotation)`));
  term rest =
      `cm_cont_code (p:cm_program) (fid:int)
        (cm_ann_pc (ann:cm_annotation) +
         cm_rvalue_code_count p fid
           (CMStringE (sid:int) (ty:cm_type)))
        (cm_ann_temp ann) (cm_ann_cursors ann)`;
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `[]:(cm_value)list`, `ann:cm_annotation`,
      `target:tvm_task`, `cm_string_pointer p (sid:int)`,
      `cm_string_address p sid`, rest), get_cm_target_push());
  result = match_mp_rule(result, code_at);
  result = match_mp_rule(result, running);
  result = match_mp_rule(result, eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))),
      `ilength ([]:(cm_value)list) < 65536i`)));
  result = match_mp_rule(result, assume_rule(
      `tower_wrap64 (cm_string_address (p:cm_program) (sid:int)) ==
       cm_value_number (st:cm_src_state) (cm_string_pointer p sid)`));
  thm_list rules = THM_LIST(
      get_cm_step_def(), get_cm_rstart_def(),
      cm_annotation_step_def, cm_update_r_def,
      cm_update_steps_def, cm_update_annotation_def,
      cm_task_target_sim_def);
  thm normalized = conv_rule(reduce_rewrite_conv(rules), result);
  thm target_view =
      apply_conversion(reduce_rewrite_conv(rules), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), normalized));
  return gnode_prove(root);
}

PROOF thm cm_target_r_string_step =
    cm_prove_target_r_string_step();

PROOF static thm cm_prove_target_r_array_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (scope:int) (slot:int)
         (ty:cm_type) (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation) (target:tvm_task) (address:int).
         cm_task_layout p
           (CMRTask p fid (CMVarE scope slot ty) st ks) ann ==>
         cm_task_target_sim p
           (CMRTask p fid (CMVarE scope slot ty) st ks)
           target ann ==>
         cm_binding_array p fid scope slot ==>
         cm_binding_address_ok p fid scope slot st ==>
         (scope == 0i ||
          (tower_signed64 (cm_state_fp st) &&
           tower_signed64
             (if scope == 1i then cm_local_offset p fid slot
              else cm_param_offset p fid slot))) ==>
         address ==
           (if scope == 0i then cm_global_address p slot
            else cm_state_fp st +
              (if scope == 1i then cm_local_offset p fid slot
               else cm_param_offset p fid slot)) ==>
         tower_signed64 address ==>
         tower_wrap64 address ==
           cm_value_number st
             (if scope == 0i then cm_global_pointer p slot
              else cm_state_env st scope slot) ==>
         cm_task_target_sim p
           (cm_step (CMRTask p fid (CMVarE scope slot ty) st ks))
           (tvm_iter
             (cm_update_steps
               (cm_annotation_step
                 (CMRTask p fid (CMVarE scope slot ty) st ks) ann))
             target)
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask p fid (CMVarE scope slot ty) st ks) ann))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term task =
      `CMRTask (p:cm_program) (fid:int)
        (CMVarE (scope:int) (slot:int) (ty:cm_type))
        (st:cm_src_state) (ks:(cm_frame)list)`;
  term address_value =
      `(if (scope:int) == 0i
        then cm_global_pointer (p:cm_program) (slot:int)
        else cm_state_env (st:cm_src_state) scope slot)`;
  thm array = assume_rule(
      `cm_binding_array (p:cm_program) (fid:int)
        (scope:int) (slot:int)`);
  thm binding_ok = assume_rule(
      `cm_binding_address_ok (p:cm_program) (fid:int)
        (scope:int) (slot:int) (st:cm_src_state)`);
  thm layout = assume_rule(
      `cm_task_layout (p:cm_program) ${task:cm_task}
        (ann:cm_annotation)`);
  thm code_at = conjunct1_rule(conv_rule(
      rewrite_conv(THM_LIST(cm_task_layout_def)), layout));
  code_at = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_code_def, get_cm_emit_rvalue_def(),
      get_cm_emit_expr_pair_def(), get_cm_rcode_of_def(),
      array, get_theorem_by_name("APPEND"))), code_at);
  code_at = conv_rule(
      reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("APPEND"),
        get_theorem_by_name("APPEND_NIL"))),
      code_at);
  thm running = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_target_sim_def)), assume_rule(
        `cm_task_target_sim (p:cm_program) ${task:cm_task}
          (target:tvm_task) (ann:cm_annotation)`));
  term rest =
      `cm_cont_code (p:cm_program) (fid:int)
        (cm_ann_pc (ann:cm_annotation) +
         cm_rvalue_code_count p fid
           (CMVarE (scope:int) (slot:int) (ty:cm_type)))
        (cm_ann_temp ann) (cm_ann_cursors ann)`;
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `scope:int`, `slot:int`, `address:int`, address_value,
      `[]:(cm_value)list`, `ann:cm_annotation`,
      `target:tvm_task`, rest), get_cm_target_binding_address());
  result = match_mp_rule(result, code_at);
  result = match_mp_rule(result, running);
  result = match_mp_rule(result, eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))),
      `ilength ([]:(cm_value)list) < 65535i`)));
  result = match_mp_rule(result, assume_rule(
      `(scope:int) == 0i ||
       (tower_signed64 (cm_state_fp (st:cm_src_state)) &&
        tower_signed64
          (if scope == 1i
           then cm_local_offset (p:cm_program) (fid:int) (slot:int)
           else cm_param_offset p fid slot))`));
  result = match_mp_rule(result, assume_rule(
      `(address:int) ==
       (if (scope:int) == 0i
        then cm_global_address (p:cm_program) (slot:int)
        else cm_state_fp (st:cm_src_state) +
          (if scope == 1i then cm_local_offset p fid slot
           else cm_param_offset p fid slot))`));
  result = match_mp_rule(result,
      assume_rule(`tower_signed64 (address:int)`));
  result = match_mp_rule(result, assume_rule(
      `tower_wrap64 (address:int) ==
       cm_value_number (st:cm_src_state) ${address_value:cm_value}`));
  thm_list rules = THM_LIST(
      get_cm_step_def(), get_cm_rstart_def(), array, binding_ok,
      cm_annotation_step_def, cm_update_r_def,
      cm_update_steps_def, cm_update_annotation_def,
      cm_task_target_sim_def);
  thm normalized = conv_rule(reduce_rewrite_conv(rules), result);
  thm target_view =
      apply_conversion(reduce_rewrite_conv(rules), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), normalized));
  return gnode_prove(root);
}

PROOF thm cm_target_r_array_step =
    cm_prove_target_r_array_step();

PROOF static thm cm_prove_target_l_var_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (scope:int) (slot:int)
         (ty:cm_type) (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation) (target:tvm_task) (address:int).
         cm_task_layout p
           (CMLTask p fid (CMVarE scope slot ty) st ks) ann ==>
         cm_task_target_sim p
           (CMLTask p fid (CMVarE scope slot ty) st ks)
           target ann ==>
         cm_binding_address_ok p fid scope slot st ==>
         (scope == 0i ||
          (tower_signed64 (cm_state_fp st) &&
           tower_signed64
             (if scope == 1i then cm_local_offset p fid slot
              else cm_param_offset p fid slot))) ==>
         address ==
           (if scope == 0i then cm_global_address p slot
            else cm_state_fp st +
              (if scope == 1i then cm_local_offset p fid slot
               else cm_param_offset p fid slot)) ==>
         tower_signed64 address ==>
         tower_wrap64 address ==
           cm_value_number st
             (if scope == 0i then cm_global_pointer p slot
              else cm_state_env st scope slot) ==>
         cm_task_target_sim p
           (cm_step (CMLTask p fid (CMVarE scope slot ty) st ks))
           (tvm_iter
             (cm_update_steps
               (cm_annotation_step
                 (CMLTask p fid (CMVarE scope slot ty) st ks) ann))
             target)
           (cm_update_annotation
             (cm_annotation_step
               (CMLTask p fid (CMVarE scope slot ty) st ks) ann))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term task =
      `CMLTask (p:cm_program) (fid:int)
        (CMVarE (scope:int) (slot:int) (ty:cm_type))
        (st:cm_src_state) (ks:(cm_frame)list)`;
  term address_value =
      `(if (scope:int) == 0i
        then cm_global_pointer (p:cm_program) (slot:int)
        else cm_state_env (st:cm_src_state) scope slot)`;
  thm binding_ok = assume_rule(
      `cm_binding_address_ok (p:cm_program) (fid:int)
        (scope:int) (slot:int) (st:cm_src_state)`);
  thm layout = assume_rule(
      `cm_task_layout (p:cm_program) ${task:cm_task}
        (ann:cm_annotation)`);
  thm code_at = conjunct1_rule(conv_rule(
      rewrite_conv(THM_LIST(cm_task_layout_def)), layout));
  code_at = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_code_def, get_cm_emit_lvalue_def(),
      get_cm_emit_expr_pair_def(), get_cm_lcode_of_def(),
      get_theorem_by_name("APPEND"))), code_at);
  code_at = conv_rule(
      reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("APPEND"),
        get_theorem_by_name("APPEND_NIL"))),
      code_at);
  thm running = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_target_sim_def)), assume_rule(
        `cm_task_target_sim (p:cm_program) ${task:cm_task}
          (target:tvm_task) (ann:cm_annotation)`));
  term rest =
      `cm_cont_code (p:cm_program) (fid:int)
        (cm_ann_pc (ann:cm_annotation) +
         cm_lvalue_code_count p fid
           (CMVarE (scope:int) (slot:int) (ty:cm_type)))
        (cm_ann_temp ann) (cm_ann_cursors ann)`;
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `scope:int`, `slot:int`, `address:int`, address_value,
      `[]:(cm_value)list`, `ann:cm_annotation`,
      `target:tvm_task`, rest), get_cm_target_binding_address());
  result = match_mp_rule(result, code_at);
  result = match_mp_rule(result, running);
  result = match_mp_rule(result, eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))),
      `ilength ([]:(cm_value)list) < 65535i`)));
  result = match_mp_rule(result, assume_rule(
      `(scope:int) == 0i ||
       (tower_signed64 (cm_state_fp (st:cm_src_state)) &&
        tower_signed64
          (if scope == 1i
           then cm_local_offset (p:cm_program) (fid:int) (slot:int)
           else cm_param_offset p fid slot))`));
  result = match_mp_rule(result, assume_rule(
      `(address:int) ==
       (if (scope:int) == 0i
        then cm_global_address (p:cm_program) (slot:int)
        else cm_state_fp (st:cm_src_state) +
          (if scope == 1i then cm_local_offset p fid slot
           else cm_param_offset p fid slot))`));
  result = match_mp_rule(result,
      assume_rule(`tower_signed64 (address:int)`));
  result = match_mp_rule(result, assume_rule(
      `tower_wrap64 (address:int) ==
       cm_value_number (st:cm_src_state) ${address_value:cm_value}`));
  thm_list rules = THM_LIST(
      get_cm_step_def(), get_cm_lstart_def(), binding_ok,
      cm_annotation_step_def, cm_update_l_def,
      cm_update_steps_def, cm_update_annotation_def,
      cm_task_target_sim_def);
  thm normalized = conv_rule(reduce_rewrite_conv(rules), result);
  thm target_view =
      apply_conversion(reduce_rewrite_conv(rules), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), normalized));
  return gnode_prove(root);
}

PROOF static thm cm_prove_target_expr_code_steps_append(void) {
  gnode root = gnode_new_with_ccl(
      `!(left:(tvm_inst)list) (right:(tvm_inst)list).
         cm_code_steps (left ++ right) ==
         cm_code_steps left + cm_code_steps right`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm left_nonnegative = ispec_rule(
      `left:(tvm_inst)list`, get_theorem_by_name("ILENGTH_NONNEG"));
  thm right_nonnegative = ispec_rule(
      `right:(tvm_inst)list`, get_theorem_by_name("ILENGTH_NONNEG"));
  thm count_add = match_mp_rule(specl_rule(TERM_LIST(
      `ilength (left:(tvm_inst)list)`,
      `ilength (right:(tvm_inst)list)`),
      get_theorem_by_name("NUM_OF_INT_ADD")),
      conj_rule(left_nonnegative, right_nonnegative));
  CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      cm_code_steps_def, get_theorem_by_name("ILENGTH_APPEND"),
      count_add)));
  return gnode_prove(root);
}
PROOF static thm cm_target_expr_code_steps_append =
    cm_prove_target_expr_code_steps_append();

PROOF static thm cm_prove_target_r_empty_call_steps(void) {
  term equation =
      `SUC (cm_code_steps
         (cm_emit_prologue (p:cm_program) (callee:int))) ==
       1 + (6 + (6 + (2 +
         cm_code_steps
           (cm_emit_param_stores p callee 0i
             (cm_function_params
               (inth callee (cm_program_functions p)))))))`;
  thm view = apply_conversion(
      then_conv(
        then_conv(
          rewrite_conv(THM_LIST(
            get_cm_emit_prologue_def(),
            cm_target_expr_code_steps_append)),
          reduce_rewrite_conv(THM_LIST(
            cm_code_steps_def,
            get_theorem_by_name("ILENGTH_APPEND"),
            get_theorem_by_name("ILENGTH_DEF")))),
        rewrite_conv(THM_LIST(
          spec_rule(`14:num`,
            get_theorem_by_name("NUM_OF_INT_OF_NUM"))))),
      equation);
  struct dest_iff_results sides = dest_iff(concl(view));
  thm result = eq_mp_rule(sym_rule(view), arith_rule(sides.tm2));
  return gen_rule(`p:cm_program`,
      gen_rule(`callee:int`, result));
}
PROOF static thm cm_target_r_empty_call_steps =
    cm_prove_target_r_empty_call_steps();

PROOF static thm cm_prove_target_r_empty_call_step(void) {
  term task =
      `CMRTask (p:cm_program) (fid:int)
        (CMCallE (callee:int) [] (ty:cm_type))
        (st:cm_src_state) (ks:(cm_frame)list)`;
  term entered =
      `cm_ann_enter_call (p:cm_program) (fid:int) (callee:int)
        (st:cm_src_state) (ty:cm_type)
        (cm_ann_pc (ann:cm_annotation) + 1i)
        (cm_ann_temp ann) (cm_ann_break ann) (cm_ann_continue ann)
        (cm_ann_cursors ann) (cm_ann_spills ann)
        (cm_ann_saved ann) (cm_ann_calls ann)`;
  term frame_bytes =
      `cm_frame_size (cm_program_structs (p:cm_program))
        (inth (callee:int) (cm_program_functions p))`;
  term frame_base =
      `cm_state_fp (st:cm_src_state) - ${frame_bytes:int}`;
  term active =
      `cm_active_spill_frames (fid:int) (st:cm_src_state)
        (ann:cm_annotation)`;
  term pending =
      `cm_call_pending_base (p:cm_program) (callee:int)
        (st:cm_src_state)`;
  term body = imp_chain(TERM_LIST(
      `cm_task_layout (p:cm_program) ${task:cm_task}
        (ann:cm_annotation)`,
      `cm_annotation_erases ${task:cm_task}
        (ann:cm_annotation)`,
      `cm_task_target_sim (p:cm_program) ${task:cm_task}
        (target:tvm_task) (ann:cm_annotation)`,
      `cm_typed_program (p:cm_program)`,
      `cm_call_ok (p:cm_program) (callee:int) []
        (st:cm_src_state)`,
      `cm_call_depth (ks:(cm_frame)list) < 65536i`,
      `tvm_target_valid (cm_model_code (p:cm_program))
        (cm_function_pc p (callee:int))`,
      `cm_function_wf (p:cm_program)
        (inth (callee:int) (cm_program_functions p))`,
      `cm_frame_segment (p:cm_program) (callee:int)
        ${frame_base:int} (cm_state_fp (st:cm_src_state))`,
      `cm_regions_before (cm_state_regions (st:cm_src_state))
        (cm_state_nextgen st)`,
      `0i <= cm_state_nextgen (st:cm_src_state)`,
      `ilength (cm_ann_calls (ann:cm_annotation)) < 65536i`,
      `cm_state_tags_generation_below (st:cm_src_state)
        (cm_state_nextgen st)`,
      `cm_spill_frames_generation_below (cm_state_nextgen st)
        ${active:(cm_spill_frame)list}`,
      `cm_tagged_span_valid (st:cm_src_state)`,
      `!addr. cm_live_address (st:cm_src_state) addr ==>
        ~(${frame_base:int} <= addr && addr < ${frame_base:int} + 8i)`,
      `!addr. cm_live_address (st:cm_src_state) addr ==>
        ~(8i <= addr && addr < 8i + 8i)`,
      `cm_range_disjoint ${frame_base:int} 8i 8i 8i`,
      `cm_range_disjoint 8i 8i ${frame_base:int} 8i`,
      `cm_call_frames_store_safe CMIntTy ${frame_base:int}
        (cm_ann_calls (ann:cm_annotation))`,
      `cm_spill_frames_store_safe (p:cm_program) CMIntTy
        ${frame_base:int} ${active:(cm_spill_frame)list}`,
      `cm_call_frames_store_safe CMIntTy 8i
        (cm_ann_calls (ann:cm_annotation))`,
      `cm_spill_frames_store_safe (p:cm_program) CMIntTy 8i
        ${active:(cm_spill_frame)list}`,
      `tower_signed64 (cm_state_fp (st:cm_src_state))`,
      `tower_signed64 ${frame_bytes:int}`,
      `tower_signed64 ${frame_base:int}`,
      `tower_word_valid ${frame_base:int}`,
      `cm_runtime_memory_layout (p:cm_program)
        ${pending:cm_src_state}
        (cm_ann_calls ${entered:cm_annotation})
        (cm_active_spill_frames (callee:int) ${pending:cm_src_state}
          ${entered:cm_annotation})`),
      `cm_task_target_sim (p:cm_program)
        (cm_step ${task:cm_task})
        (tvm_iter
          (cm_update_steps
            (cm_annotation_step ${task:cm_task} (ann:cm_annotation)))
          (target:tvm_task))
        (cm_update_annotation
          (cm_annotation_step ${task:cm_task} (ann:cm_annotation)))`);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);

  thm layout = assume_rule(
      `cm_task_layout (p:cm_program) ${task:cm_task}
        (ann:cm_annotation)`);
  thm frames_equal = conv_rule(
      reduce_rewrite_conv(THM_LIST(
        cm_annotation_erases_def, cm_ann_cursors_def,
        cm_cursor_frames_def)),
      assume_rule(
        `cm_annotation_erases ${task:cm_task}
          (ann:cm_annotation)`));
  thm code_at = conjunct1_rule(conv_rule(
      rewrite_conv(THM_LIST(cm_task_layout_def)), layout));
  term continuation =
      `cm_cont_code (p:cm_program) (fid:int)
        (cm_ann_pc (ann:cm_annotation) +
         cm_rvalue_code_count p fid
           (CMCallE (callee:int) [] (ty:cm_type)))
        (cm_ann_temp ann) (cm_ann_cursors ann)`;
  thm_list code_rules = THM_LIST(
      cm_task_code_def, get_cm_emit_rvalue_def(),
      get_cm_emit_expr_pair_def(), get_cm_rcode_of_def(),
      get_theorem_by_name("APPEND"));
  code_at = conv_rule(reduce_rewrite_conv(code_rules), code_at);
  thm running = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_target_sim_def, get_theorem_by_name("REVERSE"))),
      assume_rule(
        `cm_task_target_sim (p:cm_program) ${task:cm_task}
          (target:tvm_task) (ann:cm_annotation)`));
  thm call_ok = assume_rule(
      `cm_call_ok (p:cm_program) (callee:int) []
        (st:cm_src_state)`);
  thm call_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_call_ok_def())), call_ok);
  thm callee_bounds = mp_rule(taut_rule(mk_imp(
      concl(call_open),
      `0i <= (callee:int) &&
       callee < ilength (cm_program_functions (p:cm_program))`)),
      call_open);
  thm call_arity = mp_rule(taut_rule(mk_imp(
      concl(call_open),
      `ilength ([]:(cm_value)list) ==
       ilength (cm_function_params
         (inth (callee:int)
           (cm_program_functions (p:cm_program))))`)), call_open);
  thm empty_capacity = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))),
      `ilength ([]:(cm_value)list) < 65534i`));
  thm empty_generations = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_values_generation_below_def)),
      `cm_values_generation_below
        (cm_state_nextgen (st:cm_src_state))
        ([]:(cm_value)list)`));
  thm entered_pc = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_ann_enter_call_def, cm_ann_pc_def)),
      `cm_ann_pc ${entered:cm_annotation} ==
       cm_call_body_pc (p:cm_program) (callee:int)`));
  thm entered_calls = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_ann_enter_call_def, cm_ann_calls_def)),
      `cm_ann_calls ${entered:cm_annotation} ==
       CMCallSimFrame ${frame_base:int}
         (cm_state_fp (st:cm_src_state))
         (cm_ann_pc (ann:cm_annotation) + 1i) ::
       cm_ann_calls (ann:cm_annotation)`));
  thm pending_structure = specl_rule(TERM_LIST(
      `p:cm_program`, `callee:int`, `st:cm_src_state`),
      get_cm_call_pending_structure());
  thm pending_fp = conjunct1_rule(pending_structure);
  thm entered_active = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_active_spill_frames_def, cm_ann_enter_call_def,
        cm_ann_spills_def, cm_ann_saved_def, pending_fp)),
      `cm_active_spill_frames (callee:int) ${pending:cm_src_state}
          ${entered:cm_annotation} ==
       CMSpillFrame (callee:int) ${frame_base:int} [] ::
         ${active:(cm_spill_frame)list}`));

  thm result = specl_rule(TERM_LIST(
      continuation, `fid:int`, `ann:cm_annotation`,
      `[]:(cm_value)list`, `st:cm_src_state`, entered,
      `callee:int`, `p:cm_program`, `target:tvm_task`),
      get_cm_target_call_complete());
  code_at = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_emit_args_reload_def(),
      get_theorem_by_name("APPEND"))), code_at);
  result = match_mp_rule(result, code_at);
  result = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_theorem_by_name("REVERSE"))), result);
  result = match_mp_rule(result, running);
  result = match_mp_rule(result, callee_bounds);
  result = match_mp_rule(result, assume_rule(
      `tvm_target_valid (cm_model_code (p:cm_program))
        (cm_function_pc p (callee:int))`));
  result = match_mp_rule(result, assume_rule(
      `cm_function_wf (p:cm_program)
        (inth (callee:int) (cm_program_functions p))`));
  result = match_mp_rule(result, assume_rule(
      `cm_frame_segment (p:cm_program) (callee:int)
        ${frame_base:int} (cm_state_fp (st:cm_src_state))`));
  result = match_mp_rule(result, assume_rule(
      `cm_regions_before (cm_state_regions (st:cm_src_state))
        (cm_state_nextgen st)`));
  result = match_mp_rule(result, assume_rule(
      `0i <= cm_state_nextgen (st:cm_src_state)`));
  result = match_mp_rule(result, assume_rule(
      `ilength (cm_ann_calls (ann:cm_annotation)) < 65536i`));
  result = match_mp_rule(result, empty_capacity);
  result = match_mp_rule(result, assume_rule(
      `cm_state_tags_generation_below (st:cm_src_state)
        (cm_state_nextgen st)`));
  result = match_mp_rule(result, empty_generations);
  result = match_mp_rule(result, assume_rule(
      `cm_spill_frames_generation_below (cm_state_nextgen st)
        ${active:(cm_spill_frame)list}`));
  result = match_mp_rule(result,
      assume_rule(`cm_tagged_span_valid (st:cm_src_state)`));
  result = match_mp_rule(result, assume_rule(
      `!addr. cm_live_address (st:cm_src_state) addr ==>
        ~(${frame_base:int} <= addr && addr < ${frame_base:int} + 8i)`));
  thm scratch_live = conv_rule(rewrite_conv(THM_LIST(
      int_arith_rule(`8i + 8i == 16i`))), assume_rule(
      `!addr. cm_live_address (st:cm_src_state) addr ==>
        ~(8i <= addr && addr < 8i + 8i)`));
  result = match_mp_rule(result, scratch_live);
  result = match_mp_rule(result, assume_rule(
      `cm_range_disjoint ${frame_base:int} 8i 8i 8i`));
  result = match_mp_rule(result, assume_rule(
      `cm_range_disjoint 8i 8i ${frame_base:int} 8i`));
  result = match_mp_rule(result, assume_rule(
      `cm_call_frames_store_safe CMIntTy ${frame_base:int}
        (cm_ann_calls (ann:cm_annotation))`));
  result = match_mp_rule(result, assume_rule(
      `cm_spill_frames_store_safe (p:cm_program) CMIntTy
        ${frame_base:int} ${active:(cm_spill_frame)list}`));
  result = match_mp_rule(result, assume_rule(
      `cm_call_frames_store_safe CMIntTy 8i
        (cm_ann_calls (ann:cm_annotation))`));
  result = match_mp_rule(result, assume_rule(
      `cm_spill_frames_store_safe (p:cm_program) CMIntTy 8i
        ${active:(cm_spill_frame)list}`));
  result = match_mp_rule(result, assume_rule(
      `tower_signed64 (cm_state_fp (st:cm_src_state))`));
  result = match_mp_rule(result,
      assume_rule(`tower_signed64 ${frame_bytes:int}`));
  result = match_mp_rule(result,
      assume_rule(`tower_signed64 ${frame_base:int}`));
  result = match_mp_rule(result,
      assume_rule(`tower_word_valid ${frame_base:int}`));
  result = match_mp_rule(result, assume_rule(
      `cm_runtime_memory_layout (p:cm_program)
        ${pending:cm_src_state}
        (cm_ann_calls ${entered:cm_annotation})
        (cm_active_spill_frames (callee:int) ${pending:cm_src_state}
          ${entered:cm_annotation})`));
  result = match_mp_rule(result, entered_pc);
  result = match_mp_rule(result, entered_calls);
  result = match_mp_rule(result, entered_active);
  result = match_mp_rule(result, call_arity);

  thm step_count = specl_rule(TERM_LIST(
      `p:cm_program`, `callee:int`), cm_target_r_empty_call_steps);
  result = conv_rule(reduce_rewrite_conv(THM_LIST(
      gsym_rule(get_cm_tvm_iter_add()),
      get_theorem_by_name("ADD_ASSOC"), gsym_rule(step_count))),
      result);
  thm_list finish_rules = THM_LIST(
      get_cm_step_def(), get_cm_rstart_def(), get_cm_args_start_def(),
      get_cm_begin_call_def(), cm_task_target_sim_def,
      cm_annotation_step_def, cm_update_r_def,
      cm_update_steps_def, cm_update_annotation_def,
      cm_ann_enter_call_def, get_theorem_by_name("REVERSE"),
      get_theorem_by_name("ILENGTH_DEF"), call_ok, frames_equal,
      assume_rule(`cm_call_depth (ks:(cm_frame)list) < 65536i`));
  conv finish = then_conv(
      reduce_rewrite_conv(finish_rules),
      reduce_rewrite_conv(finish_rules));
  thm target_view = apply_conversion(finish, goal_ccl(leaf->g));
  thm normalized = conv_rule(finish, result);
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), normalized));
  return gnode_prove(root);
}
PROOF static thm cm_target_r_empty_call_step =
    cm_prove_target_r_empty_call_step();

PROOF thm cm_target_l_var_step =
    cm_prove_target_l_var_step();


PROOF thm get_cm_target_r_const_step(void) {
  return cm_target_r_const_step;
}
PROOF thm get_cm_target_r_string_step(void) {
  return cm_target_r_string_step;
}
PROOF thm get_cm_target_r_array_step(void) {
  return cm_target_r_array_step;
}
PROOF thm get_cm_target_l_var_step(void) {
  return cm_target_l_var_step;
}
PROOF thm get_cm_target_r_sizeof_step(void) {
  return cm_target_r_sizeof_step;
}
PROOF thm get_cm_target_r_getc_step(void) {
  return cm_target_r_getc_step;
}
PROOF thm get_cm_target_r_assign_step(void) {
  return cm_target_r_assign_step;
}
PROOF thm get_cm_target_r_binary_start_step(void) {
  return cm_target_r_binary_start_step;
}
PROOF thm get_cm_target_r_index_start_step(void) {
  return cm_target_r_index_start_step;
}
PROOF thm get_cm_target_r_putc_start_step(void) {
  return cm_target_r_putc_start_step;
}
PROOF thm get_cm_target_r_puti_start_step(void) {
  return cm_target_r_puti_start_step;
}
PROOF thm get_cm_target_r_exit_start_step(void) {
  return cm_target_r_exit_start_step;
}
PROOF thm get_cm_target_r_var_scalar_step(void) {
  return cm_target_r_var_scalar_step;
}
PROOF thm get_cm_target_r_unary_load_start_step(void) {
  return cm_target_r_unary_load_start_step;
}
PROOF thm get_cm_target_r_unary_address_start_step(void) {
  return cm_target_r_unary_address_start_step;
}
PROOF thm get_cm_target_r_unary_value_start_step(void) {
  return cm_target_r_unary_value_start_step;
}
PROOF thm get_cm_target_r_member_array_start_step(void) {
  return cm_target_r_member_array_start_step;
}
PROOF thm get_cm_target_r_member_scalar_start_step(void) {
  return cm_target_r_member_scalar_start_step;
}
PROOF thm get_cm_target_r_call_args_start_step(void) {
  return cm_target_r_call_args_start_step;
}
PROOF thm get_cm_target_r_empty_call_step(void) {
  return cm_target_r_empty_call_step;
}
PROOF thm get_cm_target_l_unary_address_step(void) {
  return cm_target_l_unary_address_step;
}
PROOF thm get_cm_target_l_index_start_step(void) {
  return cm_target_l_index_start_step;
}
PROOF thm get_cm_target_l_member_start_step(void) {
  return cm_target_l_member_start_step;
}


PROOF static int cmc_preservation_target_expr_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_expr_axioms_before,
      "cmc_preservation_target_expr introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_expr_checks =
    cmc_preservation_target_expr_final_checks();
