#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_ready_coordinate.h"

#require "cmc_preservation_invariant_task.c"

PROOF static size_t _cmc_preservation_ready_coordinate_axioms_before =
    vector_size(get_all_axioms());


PROOF thm cm_phase_control_regular_def = new_rec_definition(
    get_cm_aphase_recursion(),
    `(cm_phase_control_regular CAHaltP = T) &&
     (!ty. cm_phase_control_regular (CALoadP (ty:cm_type)) = T) &&
     (!src ty. cm_phase_control_regular
        (CAAssignLP (src:cm_expr) (ty:cm_type)) = T) &&
     (!ptr ty. cm_phase_control_regular
        (CAAssignRP (ptr:cm_value) (ty:cm_type)) = T) &&
     (!op left right ty. cm_phase_control_regular
        (CABinLP (op:int) (left:cm_expr) (right:cm_expr)
          (ty:cm_type)) = T) &&
     (!op left right value ty. cm_phase_control_regular
        (CABinRP (op:int) (left:cm_expr) (right:cm_expr)
          (value:cm_value) (ty:cm_type)) = T) &&
     (!op. cm_phase_control_regular (CAUnaryP (op:int)) = T) &&
     (!index ty. cm_phase_control_regular
        (CAIndexLP (index:cm_expr) (ty:cm_type)) = T) &&
     (!base ty. cm_phase_control_regular
        (CAIndexRP (base:cm_value) (ty:cm_type)) = T) &&
     (!mid base_ty. cm_phase_control_regular
        (CAMemberP (mid:int) (base_ty:cm_type)) = T) &&
     (cm_phase_control_regular CAPutcP = T) &&
     (cm_phase_control_regular CAPutiP = T) &&
     (cm_phase_control_regular CAExitP = T) &&
     (cm_phase_control_regular CAExprStmtP = T) &&
     (!slot. cm_phase_control_regular (CAInitP (slot:int)) = T) &&
     (!env regions jump target. cm_phase_control_regular
        (CABlockP (env:int->int->cm_value) (regions:(cm_region)list)
          (jump:bool) (target:int)) = T) &&
     (!second. cm_phase_control_regular
        (CASeqP (second:cm_stmt)) = T) &&
     (!yes no. cm_phase_control_regular
        (CAIfP (yes:cm_stmt) (no:cm_stmt)) = T) &&
     (!guard body loop_start loop_end. cm_phase_control_regular
        (CAWhileGuardP (guard:cm_expr) (body:cm_stmt)
          (loop_start:int) (loop_end:int)) = F) &&
     (!guard body env regions loop_start loop_end.
        cm_phase_control_regular
          (CAWhileBodyP (guard:cm_expr) (body:cm_stmt)
            (env:int->int->cm_value) (regions:(cm_region)list)
            (loop_start:int) (loop_end:int)) = F) &&
     (cm_phase_control_regular CAReturnP = T) &&
     (!callee rest values ret all_args base_slot current_slot scratch.
        cm_phase_control_regular
          (CAArgP (callee:int) (rest:(cm_expr)list)
            (values:(cm_value)list) (ret:cm_type)
            (all_args:(cm_expr)list) (base_slot:int)
            (current_slot:int) (scratch:int)) = T) &&
     (!caller env fp regions ret. cm_phase_control_regular
        (CACallP (caller:int) (env:int->int->cm_value) (fp:int)
          (regions:(cm_region)list) (ret:cm_type)) = F)`);
PROOF thm cm_phase_next_fid_def = new_rec_definition(
    get_cm_aphase_recursion(),
    `(!fid. cm_phase_next_fid (fid:int) CAHaltP = fid) &&
     (!fid ty. cm_phase_next_fid fid (CALoadP (ty:cm_type)) = fid) &&
     (!fid src ty. cm_phase_next_fid fid
        (CAAssignLP (src:cm_expr) (ty:cm_type)) = fid) &&
     (!fid ptr ty. cm_phase_next_fid fid
        (CAAssignRP (ptr:cm_value) (ty:cm_type)) = fid) &&
     (!fid op left right ty. cm_phase_next_fid fid
        (CABinLP (op:int) (left:cm_expr) (right:cm_expr)
          (ty:cm_type)) = fid) &&
     (!fid op left right value ty. cm_phase_next_fid fid
        (CABinRP (op:int) (left:cm_expr) (right:cm_expr)
          (value:cm_value) (ty:cm_type)) = fid) &&
     (!fid op. cm_phase_next_fid fid (CAUnaryP (op:int)) = fid) &&
     (!fid index ty. cm_phase_next_fid fid
        (CAIndexLP (index:cm_expr) (ty:cm_type)) = fid) &&
     (!fid base ty. cm_phase_next_fid fid
        (CAIndexRP (base:cm_value) (ty:cm_type)) = fid) &&
     (!fid mid base_ty. cm_phase_next_fid fid
        (CAMemberP (mid:int) (base_ty:cm_type)) = fid) &&
     (!fid. cm_phase_next_fid fid CAPutcP = fid) &&
     (!fid. cm_phase_next_fid fid CAPutiP = fid) &&
     (!fid. cm_phase_next_fid fid CAExitP = fid) &&
     (!fid. cm_phase_next_fid fid CAExprStmtP = fid) &&
     (!fid slot. cm_phase_next_fid fid (CAInitP (slot:int)) = fid) &&
     (!fid env regions jump target. cm_phase_next_fid fid
        (CABlockP (env:int->int->cm_value) (regions:(cm_region)list)
          (jump:bool) (target:int)) = fid) &&
     (!fid second. cm_phase_next_fid fid
        (CASeqP (second:cm_stmt)) = fid) &&
     (!fid yes no. cm_phase_next_fid fid
        (CAIfP (yes:cm_stmt) (no:cm_stmt)) = fid) &&
     (!fid guard body loop_start loop_end. cm_phase_next_fid fid
        (CAWhileGuardP (guard:cm_expr) (body:cm_stmt)
          (loop_start:int) (loop_end:int)) = fid) &&
     (!fid guard body env regions loop_start loop_end.
        cm_phase_next_fid fid
          (CAWhileBodyP (guard:cm_expr) (body:cm_stmt)
            (env:int->int->cm_value) (regions:(cm_region)list)
            (loop_start:int) (loop_end:int)) = fid) &&
     (!fid. cm_phase_next_fid fid CAReturnP = fid) &&
     (!fid callee rest values ret all_args base_slot current_slot scratch.
        cm_phase_next_fid fid
          (CAArgP (callee:int) (rest:(cm_expr)list)
            (values:(cm_value)list) (ret:cm_type)
            (all_args:(cm_expr)list) (base_slot:int)
            (current_slot:int) (scratch:int)) = fid) &&
     (!fid caller env fp regions ret.
        cm_phase_next_fid fid
          (CACallP (caller:int) (env:int->int->cm_value) (fp:int)
            (regions:(cm_region)list) (ret:cm_type)) = caller)`);

PROOF thm cm_phase_code_ready_at_def = new_rec_definition(
    get_cm_aphase_recursion(),
    `(!p fid breakpc continuepc.
        cm_phase_code_ready_at (p:cm_program) (fid:int)
          (breakpc:int) (continuepc:int) CAHaltP = T) &&
     (!p fid breakpc continuepc ty.
        cm_phase_code_ready_at p fid breakpc continuepc
          (CALoadP (ty:cm_type)) = T) &&
     (!p fid breakpc continuepc src ty.
        cm_phase_code_ready_at p fid breakpc continuepc
          (CAAssignLP (src:cm_expr) (ty:cm_type)) = T) &&
     (!p fid breakpc continuepc ptr ty.
        cm_phase_code_ready_at p fid breakpc continuepc
          (CAAssignRP (ptr:cm_value) (ty:cm_type)) = T) &&
     (!p fid breakpc continuepc op left right ty.
        cm_phase_code_ready_at p fid breakpc continuepc
          (CABinLP (op:int) (left:cm_expr) (right:cm_expr)
            (ty:cm_type)) = T) &&
     (!p fid breakpc continuepc op left right value ty.
        cm_phase_code_ready_at p fid breakpc continuepc
          (CABinRP (op:int) (left:cm_expr) (right:cm_expr)
            (value:cm_value) (ty:cm_type)) = T) &&
     (!p fid breakpc continuepc op.
        cm_phase_code_ready_at p fid breakpc continuepc
          (CAUnaryP (op:int)) = T) &&
     (!p fid breakpc continuepc index ty.
        cm_phase_code_ready_at p fid breakpc continuepc
          (CAIndexLP (index:cm_expr) (ty:cm_type)) = T) &&
     (!p fid breakpc continuepc base ty.
        cm_phase_code_ready_at p fid breakpc continuepc
          (CAIndexRP (base:cm_value) (ty:cm_type)) = T) &&
     (!p fid breakpc continuepc mid base_ty.
        cm_phase_code_ready_at p fid breakpc continuepc
          (CAMemberP (mid:int) (base_ty:cm_type)) = T) &&
     (!p fid breakpc continuepc.
        cm_phase_code_ready_at p fid breakpc continuepc CAPutcP = T) &&
     (!p fid breakpc continuepc.
        cm_phase_code_ready_at p fid breakpc continuepc CAPutiP = T) &&
     (!p fid breakpc continuepc.
        cm_phase_code_ready_at p fid breakpc continuepc CAExitP = T) &&
     (!p fid breakpc continuepc.
        cm_phase_code_ready_at p fid breakpc continuepc CAExprStmtP = T) &&
     (!p fid breakpc continuepc slot.
        cm_phase_code_ready_at p fid breakpc continuepc
          (CAInitP (slot:int)) = T) &&
     (!p fid breakpc continuepc env regions jump target.
        cm_phase_code_ready_at p fid breakpc continuepc
          (CABlockP (env:int->int->cm_value) (regions:(cm_region)list)
            (jump:bool) (target:int)) = T) &&
     (!p fid breakpc continuepc second.
        cm_phase_code_ready_at p fid breakpc continuepc
          (CASeqP (second:cm_stmt)) = T) &&
     (!p fid breakpc continuepc yes no.
        cm_phase_code_ready_at p fid breakpc continuepc
          (CAIfP (yes:cm_stmt) (no:cm_stmt)) = T) &&
     (!p fid breakpc continuepc guard body loop_start loop_end.
        cm_phase_code_ready_at p fid breakpc continuepc
          (CAWhileGuardP (guard:cm_expr) (body:cm_stmt)
            (loop_start:int) (loop_end:int)) =
        (loop_end ==
          loop_start + cm_rvalue_code_count p fid guard + 1i +
          cm_stmt_code_count p fid body + 1i)) &&
     (!p fid breakpc continuepc guard body env regions
         loop_start loop_end.
        cm_phase_code_ready_at p fid breakpc continuepc
          (CAWhileBodyP (guard:cm_expr) (body:cm_stmt)
            (env:int->int->cm_value) (regions:(cm_region)list)
            (loop_start:int) (loop_end:int)) =
        (breakpc == loop_end &&
         continuepc == loop_start &&
         loop_end ==
           loop_start + cm_rvalue_code_count p fid guard + 1i +
           cm_stmt_code_count p fid body + 1i)) &&
     (!p fid breakpc continuepc.
        cm_phase_code_ready_at p fid breakpc continuepc CAReturnP = T) &&
     (!p fid breakpc continuepc callee rest values ret all_args
         base_slot current_slot scratch.
        cm_phase_code_ready_at p fid breakpc continuepc
          (CAArgP (callee:int) (rest:(cm_expr)list)
            (values:(cm_value)list) (ret:cm_type)
            (all_args:(cm_expr)list) (base_slot:int)
            (current_slot:int) (scratch:int)) = T) &&
     (!p fid breakpc continuepc caller env fp regions ret.
        cm_phase_code_ready_at p fid breakpc continuepc
          (CACallP (caller:int) (env:int->int->cm_value) (fp:int)
            (regions:(cm_region)list) (ret:cm_type)) = T)`);

PROOF thm cm_cursors_coordinate_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p fid temp breakpc continuepc.
        cm_cursors_coordinate (p:cm_program) (fid:int)
          (temp:int) (breakpc:int) (continuepc:int)
          ([]:(cm_acursor)list) = T) &&
     (!p fid temp breakpc continuepc cursor rest.
        cm_cursors_coordinate p fid temp breakpc continuepc
          ((cursor:cm_acursor) :: (rest:(cm_acursor)list)) =
        (temp ==
           cm_phase_child_temp
             (cm_cursor_phase cursor) (cm_cursor_temp cursor) &&
         (cm_phase_control_regular (cm_cursor_phase cursor) ==>
          breakpc == cm_cursor_break cursor &&
          continuepc == cm_cursor_continue cursor) &&
         cm_phase_code_ready_at p fid breakpc continuepc
           (cm_cursor_phase cursor) &&
         cm_cursors_coordinate p
           (cm_phase_next_fid fid (cm_cursor_phase cursor))
           (cm_cursor_temp cursor)
           (cm_cursor_break cursor)
           (cm_cursor_continue cursor) rest))`);

PROOF thm cm_annotation_child_ready_def = new_fun_definition(
    `cm_annotation_child_ready (p:cm_program) (fid:int)
       (ann:cm_annotation) : bool =
       cm_cursors_coordinate p fid
         (cm_ann_temp ann) (cm_ann_break ann)
         (cm_ann_continue ann) (cm_ann_cursors ann)`);

PROOF thm cm_c_coordinate_ready_def = new_fun_definition(
    `cm_c_coordinate_ready (p:cm_program) (fid:int)
       (ctl:cm_control) (ann:cm_annotation)
       (phase:cm_aphase) : bool =
       ((cm_phase_control_regular phase ==>
         cm_c_regular_ready ctl ann) &&
        cm_c_code_ready p fid ann phase)`);

PROOF thm cm_task_coordinate_ready_def = new_rec_definition(
    get_cm_task_recursion(),
    `(!p0 input p ann.
        cm_task_coordinate_ready (p:cm_program)
          (CMStartTask (p0:cm_program) (input:(int)list))
          (ann:cm_annotation) =
        (p0 == p && ann == cm_initial_annotation)) &&
     (!p0 fid expr st ks p ann.
        cm_task_coordinate_ready p
          (CMRTask (p0:cm_program) (fid:int) (expr:cm_expr)
            (st:cm_src_state) (ks:(cm_frame)list)) ann =
        (p0 == p && cm_annotation_child_ready p fid ann)) &&
     (!p0 fid expr st ks p ann.
        cm_task_coordinate_ready p
          (CMLTask (p0:cm_program) (fid:int) (expr:cm_expr)
            (st:cm_src_state) (ks:(cm_frame)list)) ann =
        (p0 == p && cm_annotation_child_ready p fid ann)) &&
     (!p0 fid stmt st ks p ann.
        cm_task_coordinate_ready p
          (CMSTask (p0:cm_program) (fid:int) (stmt:cm_stmt)
            (st:cm_src_state) (ks:(cm_frame)list)) ann =
        (p0 == p && cm_annotation_child_ready p fid ann)) &&
     (!p0 fid value st ks p ann.
        cm_task_coordinate_ready p
          (CMVTask (p0:cm_program) (fid:int) (value:cm_value)
            (st:cm_src_state) (ks:(cm_frame)list)) ann =
        (p0 == p && cm_annotation_child_ready p fid ann)) &&
     (!p0 fid ctl st ks p ann.
        cm_task_coordinate_ready p
          (CMCTask (p0:cm_program) (fid:int) (ctl:cm_control)
            (st:cm_src_state) (ks:(cm_frame)list)) ann =
        (p0 == p &&
         ((cm_control_kind ctl == 5i) ||
          cm_annotation_child_ready p fid ann))) &&
     (!st ctl status p ann.
        cm_task_coordinate_ready (p:cm_program)
          (CMDoneTask (st:cm_src_state) (ctl:cm_control) (status:int))
          (ann:cm_annotation) = T)`);

PROOF static thm cm_prove_task_coordinate_initial(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (input:(int)list).
         cm_task_coordinate_ready p (CMStartTask p input)
           cm_initial_annotation`);
  CONV_TAC(root, reduce_rewrite_conv(THM_LIST(
      cm_task_coordinate_ready_def)));
  return gnode_prove(root);
}
PROOF thm cm_task_coordinate_initial =
    cm_prove_task_coordinate_initial();

PROOF static term cm_rc_app_arg_from_right(
    term application, size_t offset) {
  for (size_t i = 0; i < offset; ++i) {
    application = dest_comb(application).tm1;
  }
  return dest_comb(application).tm2;
}

PROOF static term cm_rc_constructor_arg(
    term constructor, size_t arity, size_t index) {
  return cm_rc_app_arg_from_right(
      constructor, arity - index - 1);
}

PROOF static thm_list cm_coordinate_rules(void) {
  return THM_LIST(
      cm_task_coordinate_ready_def, cm_annotation_child_ready_def,
      cm_cursors_coordinate_def, cm_phase_code_ready_at_def,
      cm_phase_next_fid_def, cm_c_coordinate_ready_def,
      cm_phase_control_regular_def, cm_phase_child_temp_def,
      get_cm_step_def(), get_cm_begin_call_def(),
      get_cm_rstart_def(), get_cm_lstart_def(), get_cm_sstart_def(),
      get_cm_vapply_def(), get_cm_capply_def(),
      cm_annotation_step_def, cm_update_annotation_def,
      cm_update_r_def, cm_update_l_def, cm_update_s_def,
      cm_update_v_def, cm_update_c_def,
      cm_ann_plain_def, cm_ann_linear_def, cm_ann_done_def,
      cm_ann_push_def, cm_ann_replace_def, cm_ann_pop_def,
      cm_ann_enter_call_def, cm_ann_leave_call_def,
      cm_ann_spills_set_def,
      cm_initial_annotation_def, cm_call_body_pc_def,
      get_cm_stmt_code_count_def(),
      cm_ann_put_spill_def,
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_ann_calls_def,
      cm_cursor_phase_def, cm_cursor_temp_def,
      cm_cursor_frames_def, cm_phase_frame_def,
      cm_cursor_break_def, cm_cursor_continue_def,
      cm_c_regular_ready_def, cm_c_code_ready_def,
      get_cm_control_kind_def(), get_cm_call_depth_def(),
      cm_args_start_nonempty,
      get_theorem_by_name("COND_ID"),
      get_theorem_by_name("HD"), get_theorem_by_name("TL"),
      get_theorem_by_name("NOT_CONS_NIL"));
}

PROOF static void cm_coordinate_add_fact_rules(
    thm_list *rules, const thm fact) {
  if (is_conj(concl(fact))) {
    cm_coordinate_add_fact_rules(rules, conjunct1_rule(fact));
    cm_coordinate_add_fact_rules(rules, conjunct2_rule(fact));
  } else {
    vector_add(rules, fact);
  }
}

PROOF static void cm_coordinate_close(
    gnode branch, const thm_list extra_rules) {
  thm_list rules = (thm_list)vector_create();
  for (size_t i = 0; i < vector_size(extra_rules); ++i) {
    cm_coordinate_add_fact_rules(&rules, extra_rules[i]);
  }
  thm_list definitions = cm_coordinate_rules();
  for (size_t i = 0; i < vector_size(definitions); ++i) {
    vector_add(&rules, definitions[i]);
  }
  gnode reduced = CONV_WITH_ASMP_TAC(
      branch, reduce_rewrite_conv, rules);
  if (IS_NULL(reduced->solved)) {
    reduced = CONV_WITH_ASMP_TAC(
        reduced, reduce_rewrite_conv, rules);
  }
  if (IS_NULL(reduced->solved)) {
    gnode_list decomposed = AUTO_ASMP_DESTRUCT_TAC(reduced);
    for (size_t i = 0; i < vector_size(decomposed); ++i) {
      gnode leaf = decomposed[i];
      if (IS_NULL(leaf->solved)) {
        leaf = CONV_WITH_ASMP_TAC(
            leaf, reduce_rewrite_conv, rules);
      }
      if (IS_NULL(leaf->solved)) {
        labeled_term_list assumptions = goal_lasmps(leaf->g);
        thm facts = extra_rules[0];
        for (size_t j = 1; j < vector_size(extra_rules); ++j) {
          facts = conj_rule(facts, extra_rules[j]);
        }
        for (size_t j = 0; j < vector_size(assumptions); ++j) {
          facts = conj_rule(facts, assume_rule(assumptions[j].tm));
        }
        ACCEPT_TAC(leaf, mp_rule(
            taut_rule(mk_imp(concl(facts), goal_ccl(leaf->g))),
            facts));
      }
    }
  }
}

PROOF static void cm_coordinate_cases_close(
    gnode branch, term subject, const thm cases_theorem,
    const char *label, const thm_list base_rules) {
  gnode_list cases = DISJ_CASES_TAC(branch,
      ispec_rule(subject, cases_theorem), label);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(leaf->g);
      int index = labeled_term_list_index(assumptions, label);
      if (!is_exists(assumptions[index].tm)) break;
      leaf = ASMP_EXISTS_TAC(leaf, label, NULL);
    }
    thm shape = assume_rule(
        goal_lasmps(leaf->g)[labeled_term_list_index(
          goal_lasmps(leaf->g), label)].tm);
    thm_list rules = (thm_list)vector_create();
    for (size_t j = 0; j < vector_size(base_rules); ++j) {
      vector_add(&rules, base_rules[j]);
    }
    vector_add(&rules, shape);
    if (strcmp(label, "Hexpr") == 0 && i == 2) {
      term concrete_task = rhs_of(base_rules[0]);
      term program = cm_rc_constructor_arg(concrete_task, 5, 0);
      term fid = cm_rc_constructor_arg(concrete_task, 5, 1);
      term state = cm_rc_constructor_arg(concrete_task, 5, 3);
      term concrete_expr = rhs_of(shape);
      term scope = cm_rc_constructor_arg(concrete_expr, 3, 0);
      term slot = cm_rc_constructor_arg(concrete_expr, 3, 1);
      gnode_list binding_cases = BOOL_CASES_TAC(leaf,
          `cm_binding_array (p:cm_program) ${fid:int}
             ${scope:int} ${slot:int}`,
          "Hbinding");
      for (size_t j = 0; j < vector_size(binding_cases); ++j) {
        gnode_list address_cases = BOOL_CASES_TAC(binding_cases[j],
            `cm_binding_address_ok (p:cm_program) ${fid:int}
               ${scope:int} ${slot:int} ${state:cm_src_state}`,
            "Hbinding_address");
        for (size_t k = 0; k < vector_size(address_cases); ++k) {
          cm_coordinate_close(address_cases[k], rules);
        }
      }
    } else if (strcmp(label, "Hexpr") == 0 && i == 5) {
      term concrete_expr = rhs_of(shape);
      term op = cm_rc_constructor_arg(concrete_expr, 3, 0);
      gnode_list load_cases = BOOL_CASES_TAC(
          leaf, `${op:int} == 2i`, "Hunary_load");
      cm_coordinate_close(load_cases[0], rules);
      gnode_list address_cases = BOOL_CASES_TAC(
          load_cases[1], `${op:int} == 3i`, "Hunary_address");
      for (size_t j = 0; j < vector_size(address_cases); ++j) {
        cm_coordinate_close(address_cases[j], rules);
      }
    } else if (strcmp(label, "Hexpr") == 0 && i == 7) {
      term concrete_task = rhs_of(base_rules[0]);
      term program = cm_rc_constructor_arg(concrete_task, 5, 0);
      term concrete_expr = rhs_of(shape);
      term base = cm_rc_constructor_arg(concrete_expr, 3, 0);
      term mid = cm_rc_constructor_arg(concrete_expr, 3, 1);
      gnode_list member_cases = BOOL_CASES_TAC(leaf,
          `cm_member_array (p:cm_program)
             (cm_expr_type ${base:cm_expr}) ${mid:int}`,
          "Hmember_array");
      for (size_t j = 0; j < vector_size(member_cases); ++j) {
        cm_coordinate_close(member_cases[j], rules);
      }
    } else if (strcmp(label, "Hexpr") == 0 && i == 8) {
      term concrete_task = rhs_of(base_rules[0]);
      term program = cm_rc_constructor_arg(concrete_task, 5, 0);
      term caller = cm_rc_constructor_arg(concrete_task, 5, 1);
      term state = cm_rc_constructor_arg(concrete_task, 5, 3);
      term frames = cm_rc_constructor_arg(concrete_task, 5, 4);
      term concrete_expr = rhs_of(shape);
      term callee = cm_rc_constructor_arg(concrete_expr, 3, 0);
      term args = cm_rc_constructor_arg(concrete_expr, 3, 1);
      term ret = cm_rc_constructor_arg(concrete_expr, 3, 2);
      vector_add(&rules, conjunct2_rule(base_rules[1]));
      gnode_list args_cases = BOOL_CASES_TAC(
          leaf, `${args:(cm_expr)list} == []`, "Hargs_nil");
      gnode_list call_cases = BOOL_CASES_TAC(args_cases[0],
          `cm_call_ok (p:cm_program) ${callee:int}
               ([]:(cm_value)list) ${state:cm_src_state} &&
             cm_call_depth ${frames:(cm_frame)list} < 65536i`,
          "Hcall_ready");
      for (size_t j = 0; j < vector_size(call_cases); ++j) {
        cm_coordinate_close(call_cases[j], rules);
      }
      thm args_start = mp_rule(
          ispecl_rule(TERM_LIST(
            program, caller, args, state, frames, callee, ret),
            cm_args_start_nonempty),
          assume_rule(`~(${args:(cm_expr)list} == [])`));
      vector_add(&rules, args_start);
      cm_coordinate_close(args_cases[1], rules);
    } else if (strcmp(label, "Hexpr") == 0 && i == 10) {
      term concrete_task = rhs_of(base_rules[0]);
      term state = cm_rc_constructor_arg(concrete_task, 5, 3);
      gnode_list input_cases = BOOL_CASES_TAC(leaf,
          `cm_state_input ${state:cm_src_state} == []`, "Hinput_nil");
      cm_coordinate_close(input_cases[0], rules);
      gnode_list byte_cases = BOOL_CASES_TAC(input_cases[1],
          `tower_byte_value
             (HD (cm_state_input ${state:cm_src_state}))`,
          "Hinput_byte");
      for (size_t j = 0; j < vector_size(byte_cases); ++j) {
        cm_coordinate_close(byte_cases[j], rules);
      }
    } else if (strcmp(label, "Hstmt") == 0 &&
        (i == 2 || i == 3)) {
      term concrete_task = rhs_of(base_rules[0]);
      term program = cm_rc_constructor_arg(concrete_task, 5, 0);
      term fid = cm_rc_constructor_arg(concrete_task, 5, 1);
      term concrete_stmt = rhs_of(shape);
      term slot = cm_rc_constructor_arg(
          concrete_stmt, i == 2 ? 1 : 2, 0);
      gnode_list slot_cases = BOOL_CASES_TAC(leaf,
          `cm_local_slot_ok (p:cm_program) ${fid:int} ${slot:int}`,
          "Hlocal_slot");
      for (size_t j = 0; j < vector_size(slot_cases); ++j) {
        cm_coordinate_close(slot_cases[j], rules);
      }
    } else if (strcmp(label, "Hcontrol") == 0) {
      thm child_coordinate = conv_rule(
          reduce_rewrite_conv(THM_LIST(
            shape, get_cm_control_kind_def())),
          conjunct2_rule(conjunct1_rule(base_rules[1])));
      vector_add(&rules, child_coordinate);
      thm control_cons = conv_rule(
          reduce_rewrite_conv(THM_LIST(
            base_rules[3], base_rules[4], base_rules[5],
            cm_cursors_coordinate_def, cm_phase_child_temp_def,
            cm_phase_control_regular_def, cm_phase_code_ready_at_def,
            cm_phase_next_fid_def,
            cm_cursor_phase_def, cm_cursor_temp_def,
            cm_cursor_break_def, cm_cursor_continue_def)),
          child_coordinate);
      vector_add(&rules, control_cons);
      cm_coordinate_close(leaf, rules);
    } else {
      cm_coordinate_close(leaf, rules);
    }
  }
}

PROOF static void cm_coordinate_value_control_close(
    gnode branch, bool control_task, const thm task_shape,
    const thm task_ready) {
  term ann_cursors = `cm_ann_cursors (ann:cm_annotation)`;
  gnode_list cursor_cases = DISJ_CASES_TAC(branch,
      ispec_rule(ann_cursors, get_theorem_by_name("list_CASES")),
      "Hcursors");
  {
    thm nil_shape = assume_rule(
        goal_lasmps(cursor_cases[0]->g)[labeled_term_list_index(
          goal_lasmps(cursor_cases[0]->g), "Hcursors")].tm);
    thm frames_nil = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          nil_shape, cm_cursor_frames_def)),
        conjunct2_rule(task_ready));
    thm_list nil_rules = THM_LIST(
        task_shape, task_ready, nil_shape, sym_rule(frames_nil));
    if (!control_task) {
      cm_coordinate_close(cursor_cases[0], nil_rules);
    } else {
      term concrete_task = rhs_of(task_shape);
      term control = cm_rc_constructor_arg(concrete_task, 5, 2);
      gnode_list exit_cases = BOOL_CASES_TAC(cursor_cases[0],
          `cm_control_kind ${control:cm_control} == 4i`,
          "Hnil_exit");
      cm_coordinate_close(exit_cases[0], nil_rules);
      gnode_list error_cases = BOOL_CASES_TAC(exit_cases[1],
          `cm_control_kind ${control:cm_control} == 5i`,
          "Hnil_error");
      cm_coordinate_close(error_cases[0], nil_rules);
      cm_coordinate_close(error_cases[1], nil_rules);
    }
  }
  gnode cons = ASMP_EXISTS_TAC(
      cursor_cases[1], "Hcursors", NULL);
  cons = ASMP_EXISTS_TAC(cons, "Hcursors", NULL);
  thm cursors_shape = assume_rule(
      goal_lasmps(cons->g)[labeled_term_list_index(
        goal_lasmps(cons->g), "Hcursors")].tm);
  term cursor = cm_rc_app_arg_from_right(rhs_of(cursors_shape), 1);
  term cursor_tail = cm_rc_app_arg_from_right(rhs_of(cursors_shape), 0);
  gnode_list cursor_shapes = DISJ_CASES_TAC(cons,
      ispec_rule(cursor, get_datatype_cases("cm_acursor")),
      "Hcursor");
  gnode cursor_branch = cursor_shapes[0];
  while (true) {
    labeled_term_list assumptions = goal_lasmps(cursor_branch->g);
    int index = labeled_term_list_index(assumptions, "Hcursor");
    if (!is_exists(assumptions[index].tm)) break;
    cursor_branch = ASMP_EXISTS_TAC(
        cursor_branch, "Hcursor", NULL);
  }
  thm cursor_shape = assume_rule(
      goal_lasmps(cursor_branch->g)[labeled_term_list_index(
        goal_lasmps(cursor_branch->g), "Hcursor")].tm);
  term concrete_cursor = rhs_of(cursor_shape);
  term phase = cm_rc_constructor_arg(concrete_cursor, 4, 0);
  gnode_list phase_cases = DISJ_CASES_TAC(cursor_branch,
      ispec_rule(phase, get_datatype_cases("cm_aphase")),
      "Hphase");
  for (size_t i = 0; i < vector_size(phase_cases); ++i) {
    gnode phase_branch = phase_cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(phase_branch->g);
      int index = labeled_term_list_index(assumptions, "Hphase");
      if (!is_exists(assumptions[index].tm)) break;
      phase_branch = ASMP_EXISTS_TAC(
          phase_branch, "Hphase", NULL);
    }
    thm phase_shape = assume_rule(
        goal_lasmps(phase_branch->g)[labeled_term_list_index(
          goal_lasmps(phase_branch->g), "Hphase")].tm);
    thm coordinate_cons = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          cursors_shape, cursor_shape, phase_shape,
          cm_cursors_coordinate_def, cm_phase_child_temp_def,
          cm_phase_control_regular_def, cm_phase_code_ready_at_def,
          cm_phase_next_fid_def,
          cm_cursor_phase_def, cm_cursor_temp_def,
          cm_cursor_break_def, cm_cursor_continue_def)),
        conjunct2_rule(conjunct1_rule(task_ready)));
    thm frames_cons = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          cursors_shape, cursor_shape, phase_shape,
          cm_cursor_frames_def, cm_cursor_phase_def,
          cm_phase_frame_def)),
        conjunct2_rule(task_ready));
    thm_list shapes = THM_LIST(
        task_shape, task_ready, coordinate_cons,
        cursors_shape, cursor_shape, phase_shape, sym_rule(frames_cons));
    if (control_task) {
      term concrete_task = rhs_of(task_shape);
      term control = cm_rc_constructor_arg(concrete_task, 5, 2);
      if (i == 15) {
        term concrete_phase = rhs_of(phase_shape);
        term jump = cm_rc_constructor_arg(concrete_phase, 4, 2);
        gnode_list jump_cases = BOOL_CASES_TAC(
            phase_branch, jump, "Hblock_jump");
        for (size_t j = 0; j < vector_size(jump_cases); ++j) {
          cm_coordinate_cases_close(jump_cases[j], control,
              get_datatype_cases("cm_control"), "Hcontrol", shapes);
        }
      } else {
        cm_coordinate_cases_close(phase_branch, control,
            get_datatype_cases("cm_control"), "Hcontrol", shapes);
      }
    } else if (i == 1) {
      term concrete_task = rhs_of(task_shape);
      term value = cm_rc_constructor_arg(concrete_task, 5, 2);
      term state = cm_rc_constructor_arg(concrete_task, 5, 3);
      term concrete_phase = rhs_of(phase_shape);
      term ty = cm_rc_constructor_arg(concrete_phase, 1, 0);
      gnode_list load_cases = BOOL_CASES_TAC(phase_branch,
          `cm_load_ok ${ty:cm_type} ${value:cm_value}
             ${state:cm_src_state}`,
          "Hload_ok");
      for (size_t j = 0; j < vector_size(load_cases); ++j) {
        cm_coordinate_close(load_cases[j], shapes);
      }
    } else if (i == 3) {
      term concrete_task = rhs_of(task_shape);
      term state = cm_rc_constructor_arg(concrete_task, 5, 3);
      term concrete_phase = rhs_of(phase_shape);
      term pointer = cm_rc_constructor_arg(concrete_phase, 2, 0);
      term ty = cm_rc_constructor_arg(concrete_phase, 2, 1);
      gnode_list store_cases = BOOL_CASES_TAC(phase_branch,
          `cm_store_ok ${ty:cm_type} ${pointer:cm_value}
             ${state:cm_src_state}`,
          "Hstore_ok");
      for (size_t j = 0; j < vector_size(store_cases); ++j) {
        cm_coordinate_close(store_cases[j], shapes);
      }
    } else if (i == 4) {
      term concrete_task = rhs_of(task_shape);
      term value = cm_rc_constructor_arg(concrete_task, 5, 2);
      term state = cm_rc_constructor_arg(concrete_task, 5, 3);
      term concrete_phase = rhs_of(phase_shape);
      term op = cm_rc_constructor_arg(concrete_phase, 4, 0);
      gnode_list or_cases = BOOL_CASES_TAC(
          phase_branch, `${op:int} == 0i`, "Hor_op");
      gnode_list or_truth_cases = BOOL_CASES_TAC(or_cases[0],
          `cm_truth ${state:cm_src_state} ${value:cm_value}`,
          "Hor_truth");
      for (size_t j = 0; j < vector_size(or_truth_cases); ++j) {
        cm_coordinate_close(or_truth_cases[j], shapes);
      }
      gnode_list and_cases = BOOL_CASES_TAC(
          or_cases[1], `${op:int} == 1i`, "Hand_op");
      gnode_list and_truth_cases = BOOL_CASES_TAC(and_cases[0],
          `cm_truth ${state:cm_src_state} ${value:cm_value}`,
          "Hand_truth");
      for (size_t j = 0; j < vector_size(and_truth_cases); ++j) {
        cm_coordinate_close(and_truth_cases[j], shapes);
      }
      cm_coordinate_close(and_cases[1], shapes);
    } else if (i == 5) {
      term concrete_task = rhs_of(task_shape);
      term program = cm_rc_constructor_arg(concrete_task, 5, 0);
      term value = cm_rc_constructor_arg(concrete_task, 5, 2);
      term state = cm_rc_constructor_arg(concrete_task, 5, 3);
      term concrete_phase = rhs_of(phase_shape);
      term op = cm_rc_constructor_arg(concrete_phase, 5, 0);
      term left_value = cm_rc_constructor_arg(concrete_phase, 5, 3);
      gnode_list or_cases = BOOL_CASES_TAC(
          phase_branch, `${op:int} == 0i`, "Hor_result");
      gnode_list or_binary_cases = BOOL_CASES_TAC(or_cases[0],
          `cm_binary_ok (p:cm_program) 0i
             ${left_value:cm_value} ${value:cm_value}
             ${state:cm_src_state}`,
          "Hor_binary_ok");
      for (size_t j = 0; j < vector_size(or_binary_cases); ++j) {
        cm_coordinate_close(or_binary_cases[j], shapes);
      }
      gnode_list and_cases = BOOL_CASES_TAC(
          or_cases[1], `${op:int} == 1i`, "Hand_result");
      gnode_list and_binary_cases = BOOL_CASES_TAC(and_cases[0],
          `cm_binary_ok (p:cm_program) 1i
             ${left_value:cm_value} ${value:cm_value}
             ${state:cm_src_state}`,
          "Hand_binary_ok");
      for (size_t j = 0; j < vector_size(and_binary_cases); ++j) {
        cm_coordinate_close(and_binary_cases[j], shapes);
      }
      gnode_list other_binary_cases = BOOL_CASES_TAC(and_cases[1],
          `cm_binary_ok (p:cm_program) ${op:int}
             ${left_value:cm_value} ${value:cm_value}
             ${state:cm_src_state}`,
          "Hother_binary_ok");
      for (size_t j = 0; j < vector_size(other_binary_cases); ++j) {
        cm_coordinate_close(other_binary_cases[j], shapes);
      }
    } else if (i == 8) {
      term concrete_task = rhs_of(task_shape);
      term program = cm_rc_constructor_arg(concrete_task, 5, 0);
      term value = cm_rc_constructor_arg(concrete_task, 5, 2);
      term state = cm_rc_constructor_arg(concrete_task, 5, 3);
      term concrete_phase = rhs_of(phase_shape);
      term base = cm_rc_constructor_arg(concrete_phase, 2, 0);
      gnode_list shift_cases = BOOL_CASES_TAC(phase_branch,
          `cm_ptr_shift_ok (cm_program_structs (p:cm_program))
             ${base:cm_value}
             (cm_value_number ${state:cm_src_state} ${value:cm_value})
             ${state:cm_src_state}`,
          "Hshift_ok");
      for (size_t j = 0; j < vector_size(shift_cases); ++j) {
        cm_coordinate_close(shift_cases[j], shapes);
      }
    } else if (i == 9) {
      term concrete_task = rhs_of(task_shape);
      term program = cm_rc_constructor_arg(concrete_task, 5, 0);
      term value = cm_rc_constructor_arg(concrete_task, 5, 2);
      term state = cm_rc_constructor_arg(concrete_task, 5, 3);
      term concrete_phase = rhs_of(phase_shape);
      term mid = cm_rc_constructor_arg(concrete_phase, 2, 0);
      gnode_list member_cases = BOOL_CASES_TAC(phase_branch,
          `cm_ptr_member_ok (p:cm_program) ${value:cm_value}
             ${mid:int} ${state:cm_src_state}`,
          "Hmember_ok");
      for (size_t j = 0; j < vector_size(member_cases); ++j) {
        cm_coordinate_close(member_cases[j], shapes);
      }
    } else if (i == 21) {
      term concrete_task = rhs_of(task_shape);
      term value = cm_rc_constructor_arg(concrete_task, 5, 2);
      term state = cm_rc_constructor_arg(concrete_task, 5, 3);
      term concrete_phase = rhs_of(phase_shape);
      term callee = cm_rc_constructor_arg(concrete_phase, 8, 0);
      term rest = cm_rc_constructor_arg(concrete_phase, 8, 1);
      term values = cm_rc_constructor_arg(concrete_phase, 8, 2);
      gnode_list rest_cases = BOOL_CASES_TAC(
          phase_branch, `${rest:(cm_expr)list} == []`, "Harg_rest_nil");
      gnode_list call_cases = BOOL_CASES_TAC(rest_cases[0],
          `cm_call_ok (p:cm_program) ${callee:int}
               (REVERSE (${value:cm_value} :: ${values:(cm_value)list}))
               ${state:cm_src_state} &&
             cm_call_depth
               (cm_cursor_frames ${cursor_tail:(cm_acursor)list}) < 65536i`,
          "Harg_call_ready");
      for (size_t j = 0; j < vector_size(call_cases); ++j) {
        cm_coordinate_close(call_cases[j], shapes);
      }
      cm_coordinate_close(rest_cases[1], shapes);
    } else if (i == 14) {
      term concrete_task = rhs_of(task_shape);
      term program = cm_rc_constructor_arg(concrete_task, 5, 0);
      term fid = cm_rc_constructor_arg(concrete_task, 5, 1);
      term state = cm_rc_constructor_arg(concrete_task, 5, 3);
      term concrete_phase = rhs_of(phase_shape);
      term slot = cm_rc_constructor_arg(concrete_phase, 1, 0);
      gnode_list init_cases = BOOL_CASES_TAC(phase_branch,
          `cm_store_ok
             (cm_slot_ty
               (inth ${slot:int}
                 (cm_function_locals
                   (inth ${fid:int}
                     (cm_program_functions (p:cm_program))))))
             (cm_state_env ${state:cm_src_state} 1i ${slot:int})
             ${state:cm_src_state}`,
          "Hinit_store_ok");
      for (size_t j = 0; j < vector_size(init_cases); ++j) {
        gnode_list address_cases = BOOL_CASES_TAC(init_cases[j],
            `cm_binding_address_ok (p:cm_program) ${fid:int}
               1i ${slot:int} ${state:cm_src_state}`,
            "Hinit_address");
        for (size_t k = 0; k < vector_size(address_cases); ++k) {
          cm_coordinate_close(address_cases[k], shapes);
        }
      }
    } else if (i == 17 || i == 18) {
      term concrete_task = rhs_of(task_shape);
      term value = cm_rc_constructor_arg(concrete_task, 5, 2);
      term state = cm_rc_constructor_arg(concrete_task, 5, 3);
      gnode_list truth_cases = BOOL_CASES_TAC(phase_branch,
          `cm_truth ${state:cm_src_state} ${value:cm_value}`,
          "Hcondition_truth");
      for (size_t j = 0; j < vector_size(truth_cases); ++j) {
        cm_coordinate_close(truth_cases[j], shapes);
      }
    } else {
      cm_coordinate_close(phase_branch, shapes);
    }
  }
}

PROOF static thm cm_prove_task_coordinate_step(void) {
  term erases = `cm_annotation_erases
      (task:cm_task) (ann:cm_annotation)`;
  term current = `cm_task_coordinate_ready (p:cm_program)
      (task:cm_task) (ann:cm_annotation)`;
  term target = `cm_task_coordinate_ready (p:cm_program)
      (cm_step (task:cm_task))
      (cm_update_annotation
        (cm_annotation_step (task:cm_task) (ann:cm_annotation)))`;
  term body = mk_imp(erases, mk_imp(current, target));
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list task_cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`task:cm_task`, get_datatype_cases("cm_task")),
      "Htask");
  for (size_t i = 0; i < vector_size(task_cases); ++i) {
    gnode branch = task_cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(branch->g);
      int index = labeled_term_list_index(assumptions, "Htask");
      if (!is_exists(assumptions[index].tm)) break;
      branch = ASMP_EXISTS_TAC(branch, "Htask", NULL);
    }
    thm task_shape = assume_rule(
        goal_lasmps(branch->g)[labeled_term_list_index(
          goal_lasmps(branch->g), "Htask")].tm);
    thm ready_shape = mk_comb_rule(
        mk_comb_rule(
          refl_rule(`cm_task_coordinate_ready (p:cm_program)`),
          task_shape),
        refl_rule(`ann:cm_annotation`));
    thm task_ready = conv_rule(
        reduce_rewrite_conv(cm_coordinate_rules()),
        eq_mp_rule(ready_shape, assume_rule(current)));
    thm erases_shape = mk_comb_rule(
        mk_comb_rule(refl_rule(`cm_annotation_erases`), task_shape),
        refl_rule(`ann:cm_annotation`));
    thm task_erases = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          cm_annotation_erases_def, cm_ann_cursors_def,
          cm_cursor_frames_def)),
        eq_mp_rule(erases_shape, assume_rule(erases)));
    task_ready = conj_rule(task_ready, task_erases);
    term concrete_task = rhs_of(task_shape);
    if (i == 0) {
      term input = cm_rc_constructor_arg(concrete_task, 2, 1);
      thm depth = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_cm_call_depth_def(), get_cm_is_call_frame_def(),
            get_theorem_by_name("ILENGTH_DEF"))),
          `cm_call_depth ([CMHaltK]:(cm_frame)list) < 65536i`));
      gnode_list call_cases = BOOL_CASES_TAC(branch,
          `cm_call_ok (p:cm_program)
             (cm_program_main (p:cm_program))
             ([]:(cm_value)list)
             (cm_initial_state (p:cm_program) ${input:(int)list})`,
          "Hcall_ok");
      for (size_t j = 0; j < vector_size(call_cases); ++j) {
        cm_coordinate_close(call_cases[j],
            THM_LIST(task_shape, task_ready, depth));
      }
    } else if (i == 1 || i == 2) {
      term expression = cm_rc_constructor_arg(concrete_task, 5, 2);
      cm_coordinate_cases_close(branch, expression,
          get_cm_expr_cases(), "Hexpr",
          THM_LIST(task_shape, task_ready));
    } else if (i == 3) {
      term statement = cm_rc_constructor_arg(concrete_task, 5, 2);
      cm_coordinate_cases_close(branch, statement,
          get_cm_stmt_cases(), "Hstmt",
          THM_LIST(task_shape, task_ready));
    } else if (i == 4) {
      cm_coordinate_value_control_close(
          branch, false, task_shape, task_ready);
    } else if (i == 5) {
      cm_coordinate_value_control_close(
          branch, true, task_shape, task_ready);
    } else {
      cm_coordinate_close(
          branch, THM_LIST(task_shape, task_ready));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_task_coordinate_step =
    cm_prove_task_coordinate_step();

PROOF static int cmc_preservation_ready_coordinate_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_ready_coordinate_axioms_before,
      "cmc_preservation_ready_coordinate introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_ready_coordinate_checks =
    cmc_preservation_ready_coordinate_final_checks();
