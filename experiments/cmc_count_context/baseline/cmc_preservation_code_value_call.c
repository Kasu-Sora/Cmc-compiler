#include "proof/proof.h"
#include "userlib/proof.h"
#include "cmc_codegen.h"
#include "cmc_annotate_model.h"
#include "cmc_sim.h"
#include "cmc_preservation_code_expr.h"
#include "cmc_preservation_code_stmt.h"
#include "cmc_preservation_layout.h"
#include "cmc_preservation_code_value_call.h"

#require "cmc_preservation_code_value_branch.c"

PROOF size_t _cmc_preservation_code_value_call_axioms_before =
    vector_size(get_all_axioms());

PROOF static term cm_v_arg_cons_task_term(void) {
  return `CMVTask (p:cm_program) (fid:int) (v:cm_value)
      (st:cm_src_state)
      (CMArgK (callee:int) ((arg:cm_expr) :: (more:(cm_expr)list))
        (values:(cm_value)list) (ret:cm_type) ::
       cm_cursor_frames (rest:(cm_acursor)list))`;
}

PROOF static term cm_v_arg_cons_annotation_term(void) {
  return `CMAnnotation (pc:int) (temp:int) (breakpc:int)
      (continuepc:int)
      (CMACursor
        (CAArgP (callee:int) ((arg:cm_expr) :: (more:(cm_expr)list))
          (values:(cm_value)list) (ret:cm_type)
          (all_args:(cm_expr)list) (base_slot:int)
          (current_slot:int) (scratch:int))
        (owner:int) (saved_break:int) (saved_continue:int) ::
       (rest:(cm_acursor)list))
      (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
      (calls:(cm_call_sim_frame)list)`;
}

PROOF static thm cm_prove_v_arg_cons_layout_step(void) {
  term task = cm_v_arg_cons_task_term();
  term annotation = cm_v_arg_cons_annotation_term();
  term aligned = `(temp:int) == (scratch:int)`;
  term old_layout =
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${annotation:cm_annotation}`;
  term target =
      `cm_task_layout (p:cm_program) (cm_step ${task:cm_task})
        (cm_update_annotation
          (cm_annotation_step ${task:cm_task}
            ${annotation:cm_annotation}))`;
  term body = imp_chain(TERM_LIST(aligned, old_layout), target);
  return cm_prove_v_linear_layout_step(
      list_mk_forall(free_vars(body), body), task, annotation,
      `cm_temp_store_code (p:cm_program) (fid:int) (current_slot:int)`,
      TERM_LIST(aligned),
      THM_LIST(get_cm_emit_expr_pair_def(),
        get_cm_emit_args_reload_def(),
        get_cm_layout_rcode_length(),
        get_cm_layout_temp_store_length(),
        get_cm_stmt_fp_relative_length(),
        int_ring_rule(
          `(a:int) + 5i + (b:int) + 5i == a + 10i + b`)));
}
PROOF thm cm_v_arg_cons_layout_step =
    cm_prove_v_arg_cons_layout_step();

PROOF static term cm_v_arg_nil_task_term(void) {
  return `CMVTask (p:cm_program) (fid:int) (v:cm_value)
      (st:cm_src_state)
      (CMArgK (callee:int) [] (values:(cm_value)list) (ret:cm_type) ::
       cm_cursor_frames (rest:(cm_acursor)list))`;
}

PROOF static term cm_v_arg_nil_annotation_term(void) {
  return `CMAnnotation (pc:int) (temp:int) (breakpc:int)
      (continuepc:int)
      (CMACursor
        (CAArgP (callee:int) [] (values:(cm_value)list) (ret:cm_type)
          (all_args:(cm_expr)list) (base_slot:int)
          (current_slot:int) (scratch:int))
        (owner:int) (saved_break:int) (saved_continue:int) ::
       (rest:(cm_acursor)list))
      (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
      (calls:(cm_call_sim_frame)list)`;
}

PROOF static thm cm_prove_v_arg_nil_layout_step(void) {
  term task = cm_v_arg_nil_task_term();
  term annotation = cm_v_arg_nil_annotation_term();
  term aligned = `(temp:int) == (scratch:int)`;
  term call_ok =
      `cm_call_ok (p:cm_program) (callee:int)
        (REVERSE ((v:cm_value) :: (values:(cm_value)list)))
        (st:cm_src_state)`;
  term depth =
      `cm_call_depth
        (cm_cursor_frames (rest:(cm_acursor)list)) < 65536i`;
  term old_layout =
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${annotation:cm_annotation}`;
  term target =
      `cm_task_layout (p:cm_program) (cm_step ${task:cm_task})
        (cm_update_annotation
          (cm_annotation_step ${task:cm_task}
            ${annotation:cm_annotation}))`;
  term body = imp_chain(
      TERM_LIST(aligned, call_ok, depth, old_layout), target);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);

  thm_list rules = THM_LIST(
      assume_rule(aligned), assume_rule(call_ok), assume_rule(depth));
  thm_list base = cm_v_layout_rules();
  for (size_t i = 0; i < vector_size(base); ++i) {
    vector_add(&rules, base[i]);
  }
  vector_add(&rules, get_cm_begin_call_def());
  vector_add(&rules, cm_call_body_pc_def);
  vector_add(&rules, cm_ann_enter_call_def);
  vector_add(&rules, cm_fallthrough_tail_code_def);
  vector_add(&rules, cm_arg_final_code_def);
  vector_add(&rules, cm_ann_spills_def);
  vector_add(&rules, cm_ann_saved_def);
  vector_add(&rules, cm_call_sim_base_def);
  vector_add(&rules, cm_call_sim_saved_def);
  vector_add(&rules, cm_call_sim_return_def);
  vector_add(&rules, get_cm_emit_args_reload_def());
  vector_add(&rules, get_cm_args_code_lengths());
  vector_add(&rules, get_cm_layout_temp_store_length());
  vector_add(&rules, get_cm_stmt_fp_relative_length());

  thm opened = conv_rule(reduce_rewrite_conv(rules),
      assume_rule(old_layout));
  opened = conv_rule(reduce_rewrite_conv(rules), opened);
  thm old_code = conjunct1_rule(opened);
  thm old_sites = conjunct2_rule(opened);

  term call_site_code =
      `cm_temp_store_code (p:cm_program) (fid:int) (current_slot:int) ++
       cm_emit_args_reload p fid (base_slot:int)
         (all_args:(cm_expr)list) ++
       [TVMInst TVMCallOp (cm_function_pc p (callee:int))]`;
  term return_code =
      `cm_cont_code (p:cm_program) (fid:int)
         ((pc:int) + ilength ${call_site_code:(tvm_inst)list})
         (owner:int) (rest:(cm_acursor)list)`;
  thm return_rule = ispecl_rule(TERM_LIST(
      `cm_model_code (p:cm_program)`, `pc:int`,
      call_site_code, return_code), cm_code_at_append_right);
  thm return_at = mp_rule(
      conv_rule(reduce_rewrite_conv(rules), return_rule), old_code);

  thm opened_ok = conv_rule(
      reduce_rewrite_conv(THM_LIST(get_cm_call_ok_def())),
      assume_rule(call_ok));
  thm bounds = conj_rule(
      conjunct1_rule(opened_ok),
      conjunct1_rule(conjunct2_rule(opened_ok)));
  thm body_at = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `callee:int`),
      cm_model_function_body_tail_at), bounds);
  body_at = conv_rule(reduce_rewrite_conv(rules), body_at);
  body_at = conv_rule(reduce_rewrite_conv(rules), body_at);

  thm result = conj_rule(body_at,
      conj_rule(return_at, old_sites));
  result = conv_rule(reduce_rewrite_conv(rules), result);
  result = conv_rule(reduce_rewrite_conv(rules), result);
  gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(rules));
  reduced = CONV_TAC(reduced, reduce_rewrite_conv(rules));
  ACCEPT_TAC(reduced, result);
  return gnode_prove(root);
}
PROOF thm cm_v_arg_nil_layout_step =
    cm_prove_v_arg_nil_layout_step();

PROOF static int cmc_preservation_code_value_call_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_code_value_call_axioms_before,
      "cmc_preservation_code_value_call introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_code_value_call_checks =
    cmc_preservation_code_value_call_final_checks();
