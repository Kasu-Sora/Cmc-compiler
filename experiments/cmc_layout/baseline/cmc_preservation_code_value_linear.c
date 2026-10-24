#include "proof/proof.h"
#include "userlib/proof.h"
#include "cmc_preservation_code_stmt.h"
#include "cmc_preservation_code_value_linear.h"

#require "cmc_preservation_code_stmt.c"

PROOF size_t _cmc_preservation_code_value_linear_axioms_before =
    vector_size(get_all_axioms());

/* Local source safety needed by a value-continuation step.  Impossible
 * value/frame combinations are rejected rather than assigning them code. */
PROOF thm cm_v_phase_ready_def = new_rec_definition(
    get_cm_aphase_recursion(),
    `(!p v st ann.
        cm_v_phase_ready (p:cm_program) (v:cm_value)
          (st:cm_src_state) (ann:cm_annotation) CAHaltP =
        (TL (cm_ann_cursors ann) == [])) &&
     (!p v st ann ty.
        cm_v_phase_ready p v st ann (CALoadP (ty:cm_type)) =
        cm_load_ok ty v st) &&
     (!p v st ann src ty.
        cm_v_phase_ready p v st ann
          (CAAssignLP (src:cm_expr) (ty:cm_type)) = T) &&
     (!p v st ann ptr ty.
        cm_v_phase_ready p v st ann
          (CAAssignRP (ptr:cm_value) (ty:cm_type)) =
        cm_store_ok ty ptr st) &&
     (!p v st ann op left right ty.
        cm_v_phase_ready p v st ann
          (CABinLP (op:int) (left:cm_expr) (right:cm_expr)
             (ty:cm_type)) = T) &&
     (!p v st ann op left right left_value ty.
        cm_v_phase_ready p v st ann
          (CABinRP (op:int) (left:cm_expr) (right:cm_expr)
             (left_value:cm_value) (ty:cm_type)) =
        cm_binary_ok p op left_value v st) &&
     (!p v st ann op.
        cm_v_phase_ready p v st ann (CAUnaryP (op:int)) = T) &&
     (!p v st ann index ty.
        cm_v_phase_ready p v st ann
          (CAIndexLP (index:cm_expr) (ty:cm_type)) = T) &&
     (!p v st ann base ty.
        cm_v_phase_ready p v st ann
          (CAIndexRP (base:cm_value) (ty:cm_type)) =
        cm_ptr_shift_ok (cm_program_structs p) base
          (cm_value_number st v) st) &&
     (!p v st ann mid base_ty.
        cm_v_phase_ready p v st ann
          (CAMemberP (mid:int) (base_ty:cm_type)) =
        cm_ptr_member_ok p v mid st) &&
     (!p v st ann. cm_v_phase_ready p v st ann CAPutcP = T) &&
     (!p v st ann. cm_v_phase_ready p v st ann CAPutiP = T) &&
     (!p v st ann. cm_v_phase_ready p v st ann CAExitP = T) &&
     (!p v st ann. cm_v_phase_ready p v st ann CAExprStmtP = T) &&
     (!p v st ann slot.
        cm_v_phase_ready p v st ann (CAInitP (slot:int)) = T) &&
     (!p v st ann env regions jump target.
        cm_v_phase_ready p v st ann
          (CABlockP (env:int->int->cm_value)
             (regions:(cm_region)list) (jump:bool) (target:int)) = F) &&
     (!p v st ann second.
        cm_v_phase_ready p v st ann (CASeqP (second:cm_stmt)) = F) &&
     (!p v st ann yes no.
        cm_v_phase_ready p v st ann
          (CAIfP (yes:cm_stmt) (no:cm_stmt)) = T) &&
     (!p v st ann guard body loop_start loop_end.
        cm_v_phase_ready p v st ann
          (CAWhileGuardP (guard:cm_expr) (body:cm_stmt)
             (loop_start:int) (loop_end:int)) = T) &&
     (!p v st ann guard body env regions loop_start loop_end.
        cm_v_phase_ready p v st ann
          (CAWhileBodyP (guard:cm_expr) (body:cm_stmt)
             (env:int->int->cm_value) (regions:(cm_region)list)
             (loop_start:int) (loop_end:int)) = F) &&
     (!p v st ann. cm_v_phase_ready p v st ann CAReturnP = T) &&
     (!p v st ann callee rest values ret all_args base_slot current_slot
         scratch.
        cm_v_phase_ready p v st ann
          (CAArgP (callee:int) (rest:(cm_expr)list)
             (values:(cm_value)list) (ret:cm_type)
             (all_args:(cm_expr)list) (base_slot:int)
             (current_slot:int) (scratch:int)) =
        (~(rest == []) ||
         (cm_call_ok p callee (REVERSE (v :: values)) st &&
          cm_call_depth
            (cm_cursor_frames (TL (cm_ann_cursors ann))) < 65536i))) &&
     (!p v st ann caller env fp regions ret.
        cm_v_phase_ready p v st ann
          (CACallP (caller:int) (env:int->int->cm_value) (fp:int)
             (regions:(cm_region)list) (ret:cm_type)) = F)`);
PROOF static int _c_cm_v_phase_ready =
    cst_add_const_to_header(`cm_v_phase_ready`);

/* Temporary coordinates are attached to the child currently executing under
 * a cursor.  Saved operands move the child one slot above the cursor owner;
 * argument evaluation uses its dedicated scratch coordinate; function bodies
 * restart at slot zero. */
PROOF thm cm_phase_child_temp_def = new_rec_definition(
    get_cm_aphase_recursion(),
    `(!owner. cm_phase_child_temp CAHaltP (owner:int) = owner) &&
     (!ty owner. cm_phase_child_temp (CALoadP (ty:cm_type)) owner =
        owner) &&
     (!src ty owner. cm_phase_child_temp
        (CAAssignLP (src:cm_expr) (ty:cm_type)) owner = owner) &&
     (!ptr ty owner. cm_phase_child_temp
        (CAAssignRP (ptr:cm_value) (ty:cm_type)) owner = owner + 1i) &&
     (!op left right ty owner. cm_phase_child_temp
        (CABinLP (op:int) (left:cm_expr) (right:cm_expr)
          (ty:cm_type)) owner = owner) &&
     (!op left right value ty owner. cm_phase_child_temp
        (CABinRP (op:int) (left:cm_expr) (right:cm_expr)
          (value:cm_value) (ty:cm_type)) owner =
        (if op == 0i || op == 1i then owner else owner + 1i)) &&
     (!op owner. cm_phase_child_temp (CAUnaryP (op:int)) owner =
        owner) &&
     (!index ty owner. cm_phase_child_temp
        (CAIndexLP (index:cm_expr) (ty:cm_type)) owner = owner) &&
     (!base ty owner. cm_phase_child_temp
        (CAIndexRP (base:cm_value) (ty:cm_type)) owner = owner + 1i) &&
     (!mid base_ty owner. cm_phase_child_temp
        (CAMemberP (mid:int) (base_ty:cm_type)) owner = owner) &&
     (!owner. cm_phase_child_temp CAPutcP (owner:int) = owner) &&
     (!owner. cm_phase_child_temp CAPutiP (owner:int) = owner) &&
     (!owner. cm_phase_child_temp CAExitP (owner:int) = owner) &&
     (!owner. cm_phase_child_temp CAExprStmtP (owner:int) = owner) &&
     (!slot owner. cm_phase_child_temp (CAInitP (slot:int)) owner =
        owner) &&
     (!env regions jump target owner. cm_phase_child_temp
        (CABlockP (env:int->int->cm_value) (regions:(cm_region)list)
          (jump:bool) (target:int)) owner = owner) &&
     (!second owner. cm_phase_child_temp
        (CASeqP (second:cm_stmt)) owner = owner) &&
     (!yes no owner. cm_phase_child_temp
        (CAIfP (yes:cm_stmt) (no:cm_stmt)) owner = owner) &&
     (!guard body loop_start loop_end owner. cm_phase_child_temp
        (CAWhileGuardP (guard:cm_expr) (body:cm_stmt)
          (loop_start:int) (loop_end:int)) owner = owner) &&
     (!guard body env regions loop_start loop_end owner.
        cm_phase_child_temp
          (CAWhileBodyP (guard:cm_expr) (body:cm_stmt)
            (env:int->int->cm_value) (regions:(cm_region)list)
            (loop_start:int) (loop_end:int)) owner = owner) &&
     (!owner. cm_phase_child_temp CAReturnP (owner:int) = owner) &&
     (!callee rest values ret all_args base_slot current_slot scratch
         owner. cm_phase_child_temp
        (CAArgP (callee:int) (rest:(cm_expr)list)
          (values:(cm_value)list) (ret:cm_type)
          (all_args:(cm_expr)list) (base_slot:int)
          (current_slot:int) (scratch:int)) owner = scratch) &&
     (!caller env fp regions ret owner. cm_phase_child_temp
        (CACallP (caller:int) (env:int->int->cm_value) (fp:int)
          (regions:(cm_region)list) (ret:cm_type)) owner = 0i)`);

PROOF thm cm_v_temp_ready_def = new_fun_definition(
    `cm_v_temp_ready (ann:cm_annotation)
       (phase:cm_aphase) : bool =
       (cm_ann_temp ann ==
        cm_phase_child_temp phase
          (cm_cursor_temp (HD (cm_ann_cursors ann))))`);

PROOF thm cm_v_layout_ready_def = new_fun_definition(
    `cm_v_layout_ready (p:cm_program) (v:cm_value)
       (st:cm_src_state) (ann:cm_annotation) : bool =
       ((cm_ann_cursors ann == []) ||
        (~(cm_ann_cursors ann == []) &&
         cm_v_temp_ready ann
           (cm_cursor_phase (HD (cm_ann_cursors ann))) &&
         cm_v_phase_ready p v st ann
           (cm_cursor_phase (HD (cm_ann_cursors ann)))))`);
PROOF static int _c_cm_v_layout_ready =
    cst_add_const_to_header(`cm_v_layout_ready`);

PROOF thm_list cm_v_layout_rules(void) {
  return THM_LIST(
      cm_phase_child_temp_def,
      cm_v_temp_ready_def,
      cm_task_layout_def, get_cm_task_done_def(),
      cm_task_code_def, cm_task_fid_def,
      cm_saved_layout_def, cm_phase_site_def,
      cm_cont_code_def, cm_normal_cont_code_def,
      cm_cursor_code_def, cm_value_phase_code_def,
      cm_normal_phase_code_def, cm_phase_stops_def,
      cm_normal_phase_stops_def, cm_phase_yields_normal_def,
      cm_phase_is_call_def, cm_phase_caller_def,
      cm_control_phase_code_def,
      cm_cursor_phase_def, cm_cursor_temp_def, cm_cursor_break_def,
      cm_cursor_continue_def, cm_cursor_frames_def,
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_ann_calls_def,
      cm_ann_done_def, cm_ann_pop_def, cm_ann_replace_def,
      cm_ann_put_spill_def,
      cm_ann_spills_set_def, cm_spill_put_def, cm_spill_remove_def,
      get_cm_control_kind_def(),
      cm_update_annotation_def, cm_annotation_step_def,
      cm_update_v_def, get_cm_step_def(), get_cm_vapply_def(),
      cm_assign_tail_code_def, cm_index_tail_code_def,
      cm_status_tail_code_def,
      cm_member_tail_code_def, cm_init_tail_code_def,
      get_cm_emit_rvalue_def(), get_cm_emit_expr_pair_def(),
      get_cm_emit_args_reload_def(),
      get_cm_layout_rcode_length(),
      get_cm_layout_char_normalize_length(),
      get_cm_char_normalize_count_def(),
      get_cm_rvalue_code_count_def(), get_cm_args_code_count_of_def(),
      get_cm_layout_load_length(), get_cm_layout_store_length(),
      get_cm_layout_temp_store_length(),
      get_cm_layout_temp_load_length(),
      get_cm_layout_assign_tail_length(),
      get_cm_layout_index_tail_length(),
      get_cm_layout_member_tail_length(),
      get_cm_layout_binary_finish_length(),
      get_cm_stmt_fp_relative_length(),
      get_cm_stmt_char_normalize_expanded_length(),
      get_cm_cursor_code_empty_cond(),
      get_theorem_by_name("ILENGTH_DEF"),
      cm_update_annotation_def,
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def, cm_ann_calls_def,
      cm_task_code_def, cm_task_fid_def,
      cm_cont_code_def, cm_normal_cont_code_def,
      cm_control_phase_code_def, cm_cursor_code_def,
      cm_value_phase_code_def, cm_normal_phase_code_def,
      cm_phase_stops_def, cm_normal_phase_stops_def,
      cm_phase_yields_normal_def,
      get_theorem_by_name("ILENGTH_APPEND"),
      get_theorem_by_name("APPEND"),
      get_theorem_by_name("APPEND_NIL"),
      gsym_rule(get_theorem_by_name("APPEND_ASSOC")),
      int_ring_rule(
        `((a:int) + (b:int)) + (c:int) == a + (b + c)`),
      int_ring_rule(`(a:int) + 0i == a`),
      int_ring_rule(
        `(a:int) + 5i + 1i + 5i + 1i == a + 12i`),
      get_theorem_by_name("HD"), get_theorem_by_name("TL"),
      get_theorem_by_name("NOT_CONS_NIL"));
}

PROOF static thm cm_prove_v_load_layout_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (v:cm_value) (st:cm_src_state)
         (ty:cm_type) (pc:int) (temp:int) (breakpc:int)
         (continuepc:int) (owner:int) (saved_break:int)
         (saved_continue:int) (rest:(cm_acursor)list)
         (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         cm_load_ok ty v st ==>
         cm_task_layout p
           (CMVTask p fid v st
             (CMLoadK ty :: cm_cursor_frames rest))
           (CMAnnotation pc temp breakpc continuepc
             (CMACursor (CALoadP ty) owner saved_break saved_continue ::
              rest) spills saved calls) ==>
         cm_task_layout p
           (cm_step
             (CMVTask p fid v st
               (CMLoadK ty :: cm_cursor_frames rest)))
           (cm_update_annotation
             (cm_annotation_step
               (CMVTask p fid v st
                 (CMLoadK ty :: cm_cursor_frames rest))
               (CMAnnotation pc temp breakpc continuepc
                 (CMACursor (CALoadP ty) owner saved_break
                   saved_continue :: rest) spills saved calls)))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm_list rules = cm_v_layout_rules();
  thm ready = assume_rule(`cm_load_ok (ty:cm_type) (v:cm_value)
      (st:cm_src_state)`);
  vector_add(&rules, ready);
  thm old_layout = assume_rule(
      `cm_task_layout (p:cm_program)
         (CMVTask p (fid:int) (v:cm_value) (st:cm_src_state)
           (CMLoadK (ty:cm_type) ::
            cm_cursor_frames (rest:(cm_acursor)list)))
         (CMAnnotation (pc:int) (temp:int) (breakpc:int)
           (continuepc:int)
           (CMACursor (CALoadP ty) (owner:int) (saved_break:int)
             (saved_continue:int) :: rest)
           (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
           (calls:(cm_call_sim_frame)list))`);
  thm opened = conv_rule(reduce_rewrite_conv(rules), old_layout);
  thm old_code = conjunct1_rule(opened);
  thm old_sites = conjunct2_rule(opened);
  thm suffix_rule = ispecl_rule(TERM_LIST(
      `cm_model_code (p:cm_program)`, `pc:int`,
      `cm_load_code (ty:cm_type)`,
      `cm_cont_code (p:cm_program) (fid:int)
         ((pc:int) + ilength (cm_load_code (ty:cm_type)))
         (owner:int) (rest:(cm_acursor)list)`),
      cm_code_at_append_right);
  thm suffix = mp_rule(
      conv_rule(reduce_rewrite_conv(rules), suffix_rule), old_code);
  thm result = conv_rule(reduce_rewrite_conv(rules),
      conj_rule(suffix, old_sites));
  gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(rules));
  ACCEPT_TAC(reduced, result);
  return gnode_prove(root);
}
PROOF thm cm_v_load_layout_step = cm_prove_v_load_layout_step();


PROOF thm cm_prove_v_linear_layout_step(
    const term statement, const term task, const term annotation,
    const term prefix, const term_list conditions,
    const thm_list extra_rules) {
  gnode root = gnode_new_with_ccl(statement);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm_list rules = THM_LIST();
  for (size_t i = 0; i < vector_size(conditions); ++i) {
    vector_add(&rules, assume_rule(conditions[i]));
  }
  thm_list base_rules = cm_v_layout_rules();
  for (size_t i = 0; i < vector_size(base_rules); ++i) {
    vector_add(&rules, base_rules[i]);
  }
  for (size_t i = 0; i < vector_size(extra_rules); ++i) {
    vector_add(&rules, extra_rules[i]);
  }
  term new_task = `cm_step ${task:cm_task}`;
  term new_annotation =
      `cm_update_annotation
         (cm_annotation_step ${task:cm_task}
           ${annotation:cm_annotation})`;
  thm old_layout = assume_rule(
      `cm_task_layout (p:cm_program) ${task:cm_task}
         ${annotation:cm_annotation}`);
  thm opened = conv_rule(reduce_rewrite_conv(rules), old_layout);
  thm old_code = conjunct1_rule(opened);
  thm old_sites = conjunct2_rule(opened);
  old_code = conv_rule(reduce_rewrite_conv(rules), old_code);
  old_code = conv_rule(
      rewrite_conv(THM_LIST(get_cm_cursor_code_empty_cond())),
      old_code);
  thm suffix = old_code;
  if (!equals_term(prefix, `[]:(tvm_inst)list`)) {
    thm suffix_rule = ispecl_rule(TERM_LIST(
        `cm_model_code (p:cm_program)`, `pc:int`,
        prefix,
        `cm_task_code (p:cm_program) ${new_task:cm_task}
           ${new_annotation:cm_annotation}`),
        cm_code_at_append_right);
    thm normalized_suffix_rule =
        conv_rule(reduce_rewrite_conv(rules), suffix_rule);
    normalized_suffix_rule =
        conv_rule(reduce_rewrite_conv(rules), normalized_suffix_rule);
    normalized_suffix_rule = conv_rule(
        rewrite_conv(THM_LIST(get_cm_cursor_code_empty_cond())),
        normalized_suffix_rule);
    suffix = mp_rule(normalized_suffix_rule, old_code);
  }
  thm result = conv_rule(reduce_rewrite_conv(rules),
      conj_rule(suffix, old_sites));
  result = conv_rule(reduce_rewrite_conv(rules), result);
  result = conv_rule(
      rewrite_conv(THM_LIST(get_cm_cursor_code_empty_cond())),
      result);
  gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(rules));
  reduced = CONV_TAC(reduced, reduce_rewrite_conv(rules));
  reduced = CONV_TAC(reduced,
      rewrite_conv(THM_LIST(get_cm_cursor_code_empty_cond())));
  ACCEPT_TAC(reduced, result);
  return gnode_prove(root);
}


PROOF thm cm_v_assign_l_layout_step =
    cm_prove_v_linear_layout_step(
      `!(p:cm_program) (fid:int) (v:cm_value) (st:cm_src_state)
         (src:cm_expr) (ty:cm_type)
         (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (owner:int) (saved_break:int) (saved_continue:int)
         (rest:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         temp == owner ==>
         cm_task_layout p
           (CMVTask p fid v st
             (CMAssignLK src ty :: cm_cursor_frames rest))
           (CMAnnotation pc temp breakpc continuepc
             (CMACursor (CAAssignLP src ty) owner saved_break
               saved_continue :: rest) spills saved calls) ==>
         cm_task_layout p
           (cm_step
             (CMVTask p fid v st
               (CMAssignLK src ty :: cm_cursor_frames rest)))
           (cm_update_annotation
             (cm_annotation_step
               (CMVTask p fid v st
                 (CMAssignLK src ty :: cm_cursor_frames rest))
               (CMAnnotation pc temp breakpc continuepc
                 (CMACursor (CAAssignLP src ty) owner saved_break
                   saved_continue :: rest) spills saved calls)))`,
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
         (st:cm_src_state)
         (CMAssignLK (src:cm_expr) (ty:cm_type) ::
          cm_cursor_frames (rest:(cm_acursor)list))`,
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (CMACursor (CAAssignLP (src:cm_expr) (ty:cm_type))
           (owner:int) (saved_break:int) (saved_continue:int) ::
          (rest:(cm_acursor)list))
         (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list)`,
      `cm_temp_store_code (p:cm_program) (fid:int) (owner:int)`,
      TERM_LIST(`(temp:int) == (owner:int)`), THM_LIST());

PROOF thm cm_v_assign_r_layout_step =
    cm_prove_v_linear_layout_step(
      `!(p:cm_program) (fid:int) (v:cm_value) (st:cm_src_state)
         (ptr:cm_value) (ty:cm_type)
         (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (owner:int) (saved_break:int) (saved_continue:int)
         (rest:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         cm_store_ok ty ptr st ==>
         cm_task_layout p
           (CMVTask p fid v st
             (CMAssignRK ptr ty :: cm_cursor_frames rest))
           (CMAnnotation pc temp breakpc continuepc
             (CMACursor (CAAssignRP ptr ty) owner saved_break
               saved_continue :: rest) spills saved calls) ==>
         cm_task_layout p
           (cm_step
             (CMVTask p fid v st
               (CMAssignRK ptr ty :: cm_cursor_frames rest)))
           (cm_update_annotation
             (cm_annotation_step
               (CMVTask p fid v st
                 (CMAssignRK ptr ty :: cm_cursor_frames rest))
               (CMAnnotation pc temp breakpc continuepc
                 (CMACursor (CAAssignRP ptr ty) owner saved_break
                   saved_continue :: rest) spills saved calls)))`,
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
         (st:cm_src_state)
         (CMAssignRK (ptr:cm_value) (ty:cm_type) ::
          cm_cursor_frames (rest:(cm_acursor)list))`,
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (CMACursor (CAAssignRP (ptr:cm_value) (ty:cm_type))
           (owner:int) (saved_break:int) (saved_continue:int) ::
          (rest:(cm_acursor)list))
         (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list)`,
      `cm_assign_tail_code (p:cm_program) (fid:int) (ty:cm_type)
         (owner:int)`,
      TERM_LIST(`cm_store_ok (ty:cm_type) (ptr:cm_value)
        (st:cm_src_state)`), THM_LIST());

PROOF thm cm_v_unary_layout_step =
    cm_prove_v_linear_layout_step(
      `!(p:cm_program) (fid:int) (v:cm_value) (st:cm_src_state)
         (op:int) (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (owner:int) (saved_break:int) (saved_continue:int)
         (rest:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         cm_task_layout p
           (CMVTask p fid v st
             (CMUnaryK op :: cm_cursor_frames rest))
           (CMAnnotation pc temp breakpc continuepc
             (CMACursor (CAUnaryP op) owner saved_break saved_continue ::
              rest) spills saved calls) ==>
         cm_task_layout p
           (cm_step
             (CMVTask p fid v st
               (CMUnaryK op :: cm_cursor_frames rest)))
           (cm_update_annotation
             (cm_annotation_step
               (CMVTask p fid v st
                 (CMUnaryK op :: cm_cursor_frames rest))
               (CMAnnotation pc temp breakpc continuepc
                 (CMACursor (CAUnaryP op) owner saved_break
                   saved_continue :: rest) spills saved calls)))`,
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
         (st:cm_src_state)
         (CMUnaryK (op:int) :: cm_cursor_frames (rest:(cm_acursor)list))`,
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (CMACursor (CAUnaryP (op:int)) (owner:int) (saved_break:int)
           (saved_continue:int) :: (rest:(cm_acursor)list))
         (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list)`,
      `[TVMInst TVMPushOp
          (if (op:int) == 0i then --1i else 0i);
        TVMInst (if op == 0i then TVMMulOp else TVMEqOp) 0i]:
       (tvm_inst)list`,
      TERM_LIST(), THM_LIST());

PROOF thm cm_v_index_l_layout_step =
    cm_prove_v_linear_layout_step(
      `!(p:cm_program) (fid:int) (v:cm_value) (st:cm_src_state)
         (index:cm_expr) (ty:cm_type)
         (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (owner:int) (saved_break:int) (saved_continue:int)
         (rest:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         temp == owner ==>
         cm_task_layout p
           (CMVTask p fid v st
             (CMIndexLK index ty :: cm_cursor_frames rest))
           (CMAnnotation pc temp breakpc continuepc
             (CMACursor (CAIndexLP index ty) owner saved_break
               saved_continue :: rest) spills saved calls) ==>
         cm_task_layout p
           (cm_step
             (CMVTask p fid v st
               (CMIndexLK index ty :: cm_cursor_frames rest)))
           (cm_update_annotation
             (cm_annotation_step
               (CMVTask p fid v st
                 (CMIndexLK index ty :: cm_cursor_frames rest))
               (CMAnnotation pc temp breakpc continuepc
                 (CMACursor (CAIndexLP index ty) owner saved_break
                   saved_continue :: rest) spills saved calls)))`,
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
         (st:cm_src_state)
         (CMIndexLK (index:cm_expr) (ty:cm_type) ::
          cm_cursor_frames (rest:(cm_acursor)list))`,
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (CMACursor (CAIndexLP (index:cm_expr) (ty:cm_type))
           (owner:int) (saved_break:int) (saved_continue:int) ::
          (rest:(cm_acursor)list))
         (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list)`,
      `cm_temp_store_code (p:cm_program) (fid:int) (owner:int)`,
      TERM_LIST(`(temp:int) == (owner:int)`), THM_LIST());

PROOF thm cm_v_index_r_layout_step =
    cm_prove_v_linear_layout_step(
      `!(p:cm_program) (fid:int) (v:cm_value) (st:cm_src_state)
         (base:cm_value) (ty:cm_type)
         (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (owner:int) (saved_break:int) (saved_continue:int)
         (rest:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         cm_ptr_shift_ok (cm_program_structs p) base
           (cm_value_number st v) st ==>
         cm_task_layout p
           (CMVTask p fid v st
             (CMIndexRK base ty :: cm_cursor_frames rest))
           (CMAnnotation pc temp breakpc continuepc
             (CMACursor (CAIndexRP base ty) owner saved_break
               saved_continue :: rest) spills saved calls) ==>
         cm_task_layout p
           (cm_step
             (CMVTask p fid v st
               (CMIndexRK base ty :: cm_cursor_frames rest)))
           (cm_update_annotation
             (cm_annotation_step
               (CMVTask p fid v st
                 (CMIndexRK base ty :: cm_cursor_frames rest))
               (CMAnnotation pc temp breakpc continuepc
                 (CMACursor (CAIndexRP base ty) owner saved_break
                   saved_continue :: rest) spills saved calls)))`,
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
         (st:cm_src_state)
         (CMIndexRK (base:cm_value) (ty:cm_type) ::
          cm_cursor_frames (rest:(cm_acursor)list))`,
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (CMACursor (CAIndexRP (base:cm_value) (ty:cm_type))
           (owner:int) (saved_break:int) (saved_continue:int) ::
          (rest:(cm_acursor)list))
         (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list)`,
      `cm_index_tail_code (p:cm_program) (fid:int) (ty:cm_type)
         (owner:int)`,
      TERM_LIST(
        `cm_ptr_shift_ok (cm_program_structs (p:cm_program))
           (base:cm_value)
           (cm_value_number (st:cm_src_state) (v:cm_value)) st`),
      THM_LIST());

PROOF thm cm_v_member_layout_step =
    cm_prove_v_linear_layout_step(
      `!(p:cm_program) (fid:int) (v:cm_value) (st:cm_src_state)
         (mid:int) (base_ty:cm_type)
         (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (owner:int) (saved_break:int) (saved_continue:int)
         (rest:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         cm_ptr_member_ok p v mid st ==>
         cm_task_layout p
           (CMVTask p fid v st
             (CMMemberK mid :: cm_cursor_frames rest))
           (CMAnnotation pc temp breakpc continuepc
             (CMACursor (CAMemberP mid base_ty) owner saved_break
               saved_continue :: rest) spills saved calls) ==>
         cm_task_layout p
           (cm_step
             (CMVTask p fid v st
               (CMMemberK mid :: cm_cursor_frames rest)))
           (cm_update_annotation
             (cm_annotation_step
               (CMVTask p fid v st
                 (CMMemberK mid :: cm_cursor_frames rest))
               (CMAnnotation pc temp breakpc continuepc
                 (CMACursor (CAMemberP mid base_ty) owner saved_break
                   saved_continue :: rest) spills saved calls)))`,
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
         (st:cm_src_state)
         (CMMemberK (mid:int) ::
          cm_cursor_frames (rest:(cm_acursor)list))`,
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (CMACursor (CAMemberP (mid:int) (base_ty:cm_type))
           (owner:int) (saved_break:int) (saved_continue:int) ::
          (rest:(cm_acursor)list))
         (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list)`,
      `cm_member_tail_code (p:cm_program) (base_ty:cm_type)
         (mid:int)`,
      TERM_LIST(`cm_ptr_member_ok (p:cm_program) (v:cm_value)
        (mid:int) (st:cm_src_state)`), THM_LIST());

PROOF thm cm_v_putc_layout_step =
    cm_prove_v_linear_layout_step(
      `!(p:cm_program) (fid:int) (v:cm_value) (st:cm_src_state)
         (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (owner:int) (saved_break:int) (saved_continue:int)
         (rest:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         cm_task_layout p
           (CMVTask p fid v st (CMPutcK :: cm_cursor_frames rest))
           (CMAnnotation pc temp breakpc continuepc
             (CMACursor CAPutcP owner saved_break saved_continue :: rest)
             spills saved calls) ==>
         cm_task_layout p
           (cm_step
             (CMVTask p fid v st (CMPutcK :: cm_cursor_frames rest)))
           (cm_update_annotation
             (cm_annotation_step
               (CMVTask p fid v st
                 (CMPutcK :: cm_cursor_frames rest))
               (CMAnnotation pc temp breakpc continuepc
                 (CMACursor CAPutcP owner saved_break saved_continue ::
                  rest) spills saved calls)))`,
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
         (st:cm_src_state)
         (CMPutcK :: cm_cursor_frames (rest:(cm_acursor)list))`,
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (CMACursor CAPutcP (owner:int) (saved_break:int)
           (saved_continue:int) :: (rest:(cm_acursor)list))
         (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list)`,
      `[TVMInst TVMDupOp 0i; TVMInst TVMPutcOp 0i]:(tvm_inst)list`,
      TERM_LIST(), THM_LIST());

PROOF thm cm_v_puti_layout_step =
    cm_prove_v_linear_layout_step(
      `!(p:cm_program) (fid:int) (v:cm_value) (st:cm_src_state)
         (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (owner:int) (saved_break:int) (saved_continue:int)
         (rest:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         cm_task_layout p
           (CMVTask p fid v st (CMPutiK :: cm_cursor_frames rest))
           (CMAnnotation pc temp breakpc continuepc
             (CMACursor CAPutiP owner saved_break saved_continue :: rest)
             spills saved calls) ==>
         cm_task_layout p
           (cm_step
             (CMVTask p fid v st (CMPutiK :: cm_cursor_frames rest)))
           (cm_update_annotation
             (cm_annotation_step
               (CMVTask p fid v st
                 (CMPutiK :: cm_cursor_frames rest))
               (CMAnnotation pc temp breakpc continuepc
                 (CMACursor CAPutiP owner saved_break saved_continue ::
                  rest) spills saved calls)))`,
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
         (st:cm_src_state)
         (CMPutiK :: cm_cursor_frames (rest:(cm_acursor)list))`,
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (CMACursor CAPutiP (owner:int) (saved_break:int)
           (saved_continue:int) :: (rest:(cm_acursor)list))
         (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list)`,
      `[TVMInst TVMDupOp 0i; TVMInst TVMPutiOp 0i]:(tvm_inst)list`,
      TERM_LIST(), THM_LIST());

PROOF thm cm_v_expr_stmt_layout_step =
    cm_prove_v_linear_layout_step(
      `!(p:cm_program) (fid:int) (v:cm_value) (st:cm_src_state)
         (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (owner:int) (saved_break:int) (saved_continue:int)
         (rest:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         cm_task_layout p
           (CMVTask p fid v st
             (CMExprStmtK :: cm_cursor_frames rest))
           (CMAnnotation pc temp breakpc continuepc
             (CMACursor CAExprStmtP owner saved_break saved_continue ::
              rest) spills saved calls) ==>
         cm_task_layout p
           (cm_step
             (CMVTask p fid v st
               (CMExprStmtK :: cm_cursor_frames rest)))
           (cm_update_annotation
             (cm_annotation_step
               (CMVTask p fid v st
                 (CMExprStmtK :: cm_cursor_frames rest))
               (CMAnnotation pc temp breakpc continuepc
                 (CMACursor CAExprStmtP owner saved_break
                   saved_continue :: rest) spills saved calls)))`,
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
         (st:cm_src_state)
         (CMExprStmtK :: cm_cursor_frames (rest:(cm_acursor)list))`,
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (CMACursor CAExprStmtP (owner:int) (saved_break:int)
           (saved_continue:int) :: (rest:(cm_acursor)list))
         (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list)`,
      `[TVMInst TVMPopOp 0i]:(tvm_inst)list`,
      TERM_LIST(), THM_LIST());

PROOF thm cm_v_return_layout_step =
    cm_prove_v_linear_layout_step(
      `!(p:cm_program) (fid:int) (v:cm_value) (st:cm_src_state)
         (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (owner:int) (saved_break:int) (saved_continue:int)
         (rest:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         cm_task_layout p
           (CMVTask p fid v st (CMReturnK :: cm_cursor_frames rest))
           (CMAnnotation pc temp breakpc continuepc
             (CMACursor CAReturnP owner saved_break saved_continue :: rest)
             spills saved calls) ==>
         cm_task_layout p
           (cm_step
             (CMVTask p fid v st (CMReturnK :: cm_cursor_frames rest)))
           (cm_update_annotation
             (cm_annotation_step
               (CMVTask p fid v st
                 (CMReturnK :: cm_cursor_frames rest))
               (CMAnnotation pc temp breakpc continuepc
                 (CMACursor CAReturnP owner saved_break saved_continue ::
                  rest) spills saved calls)))`,
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
         (st:cm_src_state)
         (CMReturnK :: cm_cursor_frames (rest:(cm_acursor)list))`,
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (CMACursor CAReturnP (owner:int) (saved_break:int)
           (saved_continue:int) :: (rest:(cm_acursor)list))
         (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list)`,
      `[]:(tvm_inst)list`,
      TERM_LIST(), THM_LIST());

PROOF static thm cm_prove_v_init_branch(const bool succeeds) {
  term condition =
      `cm_binding_address_ok (p:cm_program) (fid:int) 1i
         (slot:int) (st:cm_src_state) &&
       cm_store_ok
         (cm_slot_ty (inth slot
           (cm_function_locals
             (inth fid
               (cm_program_functions p)))))
         (cm_state_env st 1i slot) st`;
  if (!succeeds) condition = mk_not(condition);
  term task =
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
         (st:cm_src_state)
         (CMInitK (slot:int) ::
          cm_cursor_frames (rest:(cm_acursor)list))`;
  term annotation =
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (CMACursor (CAInitP (slot:int)) (owner:int)
           (saved_break:int) (saved_continue:int) ::
          (rest:(cm_acursor)list))
         (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list)`;
  term body =
      `${condition:bool} ==>
       cm_task_layout (p:cm_program) ${task:cm_task}
         ${annotation:cm_annotation} ==>
       cm_task_layout p (cm_step ${task:cm_task})
         (cm_update_annotation
           (cm_annotation_step ${task:cm_task}
             ${annotation:cm_annotation}))`;
  term statement = list_mk_forall(free_vars(body), body);
  return cm_prove_v_linear_layout_step(
      statement, task, annotation,
      `cm_init_tail_code (p:cm_program) (fid:int) (slot:int)`,
      TERM_LIST(condition), THM_LIST());
}
PROOF thm cm_v_init_ok_layout_step =
    cm_prove_v_init_branch(true);
PROOF thm cm_v_init_bad_layout_step =
    cm_prove_v_init_branch(false);

PROOF static thm cm_prove_v_init_layout_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (v:cm_value) (st:cm_src_state)
         (slot:int) (pc:int) (temp:int) (breakpc:int)
         (continuepc:int) (owner:int) (saved_break:int)
         (saved_continue:int) (rest:(cm_acursor)list)
         (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         cm_task_layout p
           (CMVTask p fid v st
             (CMInitK slot :: cm_cursor_frames rest))
           (CMAnnotation pc temp breakpc continuepc
             (CMACursor (CAInitP slot) owner saved_break saved_continue ::
              rest) spills saved calls) ==>
         cm_task_layout p
           (cm_step
             (CMVTask p fid v st
               (CMInitK slot :: cm_cursor_frames rest)))
           (cm_update_annotation
             (cm_annotation_step
               (CMVTask p fid v st
                 (CMInitK slot :: cm_cursor_frames rest))
               (CMAnnotation pc temp breakpc continuepc
                 (CMACursor (CAInitP slot) owner saved_break
                   saved_continue :: rest) spills saved calls)))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term condition =
      `cm_binding_address_ok (p:cm_program) (fid:int) 1i
         (slot:int) (st:cm_src_state) &&
       cm_store_ok
         (cm_slot_ty (inth slot
           (cm_function_locals
             (inth fid
               (cm_program_functions p)))))
         (cm_state_env st 1i slot) st`;
  gnode_list cases = BOOL_CASES_TAC(leaf, condition, "Hstore");
  for (size_t i = 0; i < 2; ++i) {
    labeled_term_list assumptions = goal_lasmps(cases[i]->g);
    thm branch = assume_rule(
        assumptions[
          labeled_term_list_index(assumptions, "Hstore")].tm);
    thm layout = assume_rule(
        `cm_task_layout (p:cm_program)
           (CMVTask p (fid:int) (v:cm_value) (st:cm_src_state)
             (CMInitK (slot:int) ::
              cm_cursor_frames (rest:(cm_acursor)list)))
           (CMAnnotation (pc:int) (temp:int) (breakpc:int)
             (continuepc:int)
             (CMACursor (CAInitP slot) (owner:int) (saved_break:int)
               (saved_continue:int) :: rest)
             (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
             (calls:(cm_call_sim_frame)list))`);
    thm result = match_mp_rule(
        i == 0 ? cm_v_init_ok_layout_step :
                 cm_v_init_bad_layout_step,
        branch);
    result = match_mp_rule(result, layout);
    ACCEPT_TAC(cases[i], result);
  }
  return gnode_prove(root);
}
PROOF thm cm_v_init_layout_step =
    cm_prove_v_init_layout_step();

PROOF static thm cm_prove_v_status_layout_step(
    const term statement, const term task,
    const term annotation) {
  gnode root = gnode_new_with_ccl(statement);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm_list rules = cm_v_layout_rules();
  thm old_layout = assume_rule(
      `cm_task_layout (p:cm_program) ${task:cm_task}
         ${annotation:cm_annotation}`);
  thm opened = conv_rule(reduce_rewrite_conv(rules), old_layout);
  thm old_code = conjunct1_rule(opened);
  thm old_sites = conjunct2_rule(opened);
  thm tail_rule = ispecl_rule(TERM_LIST(
      `cm_model_code (p:cm_program)`, `pc:int`,
      `cm_char_normalize_code CMCharTy`,
      `[TVMInst TVMHaltOp 0i]:(tvm_inst)list`),
      cm_code_at_append_right);
  thm tail = mp_rule(
      conv_rule(reduce_rewrite_conv(rules), tail_rule),
      old_code);
  thm empty_rule = ispecl_rule(TERM_LIST(
      `cm_model_code (p:cm_program)`, `pc + 6i`,
      `[]:(tvm_inst)list`,
      `[TVMInst TVMHaltOp 0i]:(tvm_inst)list`),
      cm_code_at_append_left);
  thm empty_at = mp_rule(
      conv_rule(reduce_rewrite_conv(rules), empty_rule), tail);
  thm result = conv_rule(reduce_rewrite_conv(rules),
      conj_rule(empty_at, old_sites));
  gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(rules));
  if (IS_NULL(reduced->solved)) {
    ACCEPT_TAC(reduced, result);
  }
  return gnode_prove(root);
}

PROOF thm cm_v_halt_layout_step =
    cm_prove_v_status_layout_step(
      `!(p:cm_program) (fid:int) (v:cm_value) (st:cm_src_state)
         (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (owner:int) (saved_break:int) (saved_continue:int)
         (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         cm_task_layout p
           (CMVTask p fid v st [CMHaltK])
           (CMAnnotation pc temp breakpc continuepc
             [CMACursor CAHaltP owner saved_break saved_continue]
             spills saved calls) ==>
         cm_task_layout p
           (cm_step (CMVTask p fid v st [CMHaltK]))
           (cm_update_annotation
             (cm_annotation_step
               (CMVTask p fid v st [CMHaltK])
               (CMAnnotation pc temp breakpc continuepc
                 [CMACursor CAHaltP owner saved_break saved_continue]
                 spills saved calls)))`,
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
         (st:cm_src_state) [CMHaltK]`,
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         [CMACursor CAHaltP (owner:int) (saved_break:int)
           (saved_continue:int)]
         (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list)`);

PROOF thm cm_v_exit_layout_step =
    cm_prove_v_status_layout_step(
      `!(p:cm_program) (fid:int) (v:cm_value) (st:cm_src_state)
         (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (owner:int) (saved_break:int) (saved_continue:int)
         (rest:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         cm_task_layout p
           (CMVTask p fid v st (CMExitK :: cm_cursor_frames rest))
           (CMAnnotation pc temp breakpc continuepc
             (CMACursor CAExitP owner saved_break saved_continue :: rest)
             spills saved calls) ==>
         cm_task_layout p
           (cm_step
             (CMVTask p fid v st
               (CMExitK :: cm_cursor_frames rest)))
           (cm_update_annotation
             (cm_annotation_step
               (CMVTask p fid v st
                 (CMExitK :: cm_cursor_frames rest))
               (CMAnnotation pc temp breakpc continuepc
                 (CMACursor CAExitP owner saved_break saved_continue ::
                  rest) spills saved calls)))`,
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
         (st:cm_src_state)
         (CMExitK :: cm_cursor_frames (rest:(cm_acursor)list))`,
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (CMACursor CAExitP (owner:int) (saved_break:int)
           (saved_continue:int) :: (rest:(cm_acursor)list))
         (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list)`);
/* The aggregate theorem is added after all phase-local layout lemmas. */

PROOF static int cmc_preservation_code_value_linear_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_code_value_linear_axioms_before,
      "cmc_preservation_code_value_linear introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_code_value_linear_checks =
    cmc_preservation_code_value_linear_final_checks();
