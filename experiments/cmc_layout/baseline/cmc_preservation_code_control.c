#include "proof/proof.h"
#include "userlib/proof.h"
#include "cmc_preservation_code_value_total.h"
#include "cmc_preservation_layout.h"
#include "cmc_annotate_model.h"
#include "cmc_lang.h"
#include "cmc_codegen.h"
#include "cmc_preservation_code.h"

#require "cmc_preservation_code_value_total.c"

PROOF size_t _cmc_preservation_code_control_axioms_before =
    vector_size(get_all_axioms());

PROOF thm cm_c_regular_ready_def = new_fun_definition(
    `cm_c_regular_ready (ctl:cm_control) (ann:cm_annotation) : bool =
       (~(cm_control_kind ctl == 5i) &&
        (cm_control_kind ctl == 1i ==>
          cm_ann_break ann ==
            cm_cursor_break (HD (cm_ann_cursors ann))) &&
        (cm_control_kind ctl == 2i ==>
          cm_ann_continue ann ==
            cm_cursor_continue (HD (cm_ann_cursors ann))))`);
PROOF static int _c_cm_c_regular_ready =
    cst_add_const_to_header(`cm_c_regular_ready`);

PROOF thm cm_c_phase_ready_def = new_rec_definition(
    get_cm_aphase_recursion(),
    `(!ctl ann. cm_c_phase_ready (ctl:cm_control)
        (ann:cm_annotation) CAHaltP =
        (cm_control_kind ctl == 4i &&
         TL (cm_ann_cursors ann) == [])) &&
     (!ctl ann ty. cm_c_phase_ready ctl ann
        (CALoadP (ty:cm_type)) =
        (cm_control_kind ctl == 4i &&
         cm_c_regular_ready ctl ann)) &&
     (!ctl ann src ty. cm_c_phase_ready ctl ann
        (CAAssignLP (src:cm_expr) (ty:cm_type)) =
        (cm_control_kind ctl == 4i &&
         cm_c_regular_ready ctl ann)) &&
     (!ctl ann ptr ty. cm_c_phase_ready ctl ann
        (CAAssignRP (ptr:cm_value) (ty:cm_type)) =
        (cm_control_kind ctl == 4i &&
         cm_c_regular_ready ctl ann)) &&
     (!ctl ann op left right ty. cm_c_phase_ready ctl ann
        (CABinLP (op:int) (left:cm_expr) (right:cm_expr)
          (ty:cm_type)) =
        (cm_control_kind ctl == 4i &&
         cm_c_regular_ready ctl ann)) &&
     (!ctl ann op left right value ty. cm_c_phase_ready ctl ann
        (CABinRP (op:int) (left:cm_expr) (right:cm_expr)
          (value:cm_value) (ty:cm_type)) =
        (cm_control_kind ctl == 4i &&
         cm_c_regular_ready ctl ann)) &&
     (!ctl ann op. cm_c_phase_ready ctl ann
        (CAUnaryP (op:int)) =
        (cm_control_kind ctl == 4i &&
         cm_c_regular_ready ctl ann)) &&
     (!ctl ann index ty. cm_c_phase_ready ctl ann
        (CAIndexLP (index:cm_expr) (ty:cm_type)) =
        (cm_control_kind ctl == 4i &&
         cm_c_regular_ready ctl ann)) &&
     (!ctl ann base ty. cm_c_phase_ready ctl ann
        (CAIndexRP (base:cm_value) (ty:cm_type)) =
        (cm_control_kind ctl == 4i &&
         cm_c_regular_ready ctl ann)) &&
     (!ctl ann mid base_ty. cm_c_phase_ready ctl ann
        (CAMemberP (mid:int) (base_ty:cm_type)) =
        (cm_control_kind ctl == 4i &&
         cm_c_regular_ready ctl ann)) &&
     (!ctl ann. cm_c_phase_ready ctl ann CAPutcP =
        (cm_control_kind ctl == 4i &&
         cm_c_regular_ready ctl ann)) &&
     (!ctl ann. cm_c_phase_ready ctl ann CAPutiP =
        (cm_control_kind ctl == 4i &&
         cm_c_regular_ready ctl ann)) &&
     (!ctl ann. cm_c_phase_ready ctl ann CAExitP =
        (cm_control_kind ctl == 4i &&
         cm_c_regular_ready ctl ann)) &&
     (!ctl ann. cm_c_phase_ready ctl ann CAExprStmtP =
        (cm_control_kind ctl == 4i &&
         cm_c_regular_ready ctl ann)) &&
     (!ctl ann slot. cm_c_phase_ready ctl ann
        (CAInitP (slot:int)) =
        (cm_control_kind ctl == 4i &&
         cm_c_regular_ready ctl ann)) &&
     (!ctl ann env regions jump target. cm_c_phase_ready ctl ann
        (CABlockP (env:int->int->cm_value)
          (regions:(cm_region)list) (jump:bool) (target:int)) =
        cm_c_regular_ready ctl ann) &&
     (!ctl ann second. cm_c_phase_ready ctl ann
        (CASeqP (second:cm_stmt)) = cm_c_regular_ready ctl ann) &&
     (!ctl ann yes no. cm_c_phase_ready ctl ann
        (CAIfP (yes:cm_stmt) (no:cm_stmt)) =
        (cm_control_kind ctl == 4i &&
         cm_c_regular_ready ctl ann)) &&
     (!ctl ann guard body loop_start loop_end.
        cm_c_phase_ready ctl ann
          (CAWhileGuardP (guard:cm_expr) (body:cm_stmt)
            (loop_start:int) (loop_end:int)) =
        (cm_control_kind ctl == 4i &&
         cm_c_regular_ready ctl ann)) &&
     (!ctl ann guard body env regions loop_start loop_end.
        cm_c_phase_ready ctl ann
          (CAWhileBodyP (guard:cm_expr) (body:cm_stmt)
            (env:int->int->cm_value) (regions:(cm_region)list)
            (loop_start:int) (loop_end:int)) =
        ~(cm_control_kind ctl == 5i)) &&
     (!ctl ann. cm_c_phase_ready ctl ann CAReturnP =
        (cm_control_kind ctl == 4i &&
         cm_c_regular_ready ctl ann)) &&
     (!ctl ann callee rest values ret all_args base_slot
         current_slot scratch.
        cm_c_phase_ready ctl ann
          (CAArgP (callee:int) (rest:(cm_expr)list)
            (values:(cm_value)list) (ret:cm_type)
            (all_args:(cm_expr)list) (base_slot:int)
            (current_slot:int) (scratch:int)) =
        (cm_control_kind ctl == 4i &&
         cm_c_regular_ready ctl ann)) &&
     (!ctl ann caller env fp regions ret.
        cm_c_phase_ready ctl ann
          (CACallP (caller:int) (env:int->int->cm_value) (fp:int)
            (regions:(cm_region)list) (ret:cm_type)) =
        (cm_control_kind ctl == 0i ||
         cm_control_kind ctl == 3i ||
         cm_control_kind ctl == 4i))`);
PROOF static int _c_cm_c_phase_ready =
    cst_add_const_to_header(`cm_c_phase_ready`);
PROOF thm cm_c_code_ready_def = new_fun_definition(
    `cm_c_code_ready (p:cm_program) (fid:int)
       (ann:cm_annotation) (phase:cm_aphase) : bool =
       (!guard body env regions loop_start loop_end.
          phase ==
            CAWhileBodyP (guard:cm_expr) (body:cm_stmt)
              (env:int->int->cm_value) (regions:(cm_region)list)
              (loop_start:int) (loop_end:int) ==>
          cm_ann_break ann == loop_end &&
          cm_ann_continue ann == loop_start &&
          loop_end ==
            loop_start + cm_rvalue_code_count p fid guard + 1i +
            cm_stmt_code_count p fid body + 1i)`);
PROOF static int _c_cm_c_code_ready =
    cst_add_const_to_header(`cm_c_code_ready`);


PROOF static term cm_c_app_arg_from_right(
    term application, size_t offset) {
  for (size_t i = 0; i < offset; ++i) {
    application = dest_comb(application).tm1;
  }
  return dest_comb(application).tm2;
}
PROOF static term cm_c_application_head(term application) {
  while (is_comb(application)) {
    application = dest_comb(application).tm1;
  }
  return application;
}

PROOF static thm_list cm_c_layout_rules(void) {
  thm_list rules = cm_v_layout_rules();
  vector_add(&rules, cm_c_phase_ready_def);
  vector_add(&rules, get_cm_task_done_def());
  vector_add(&rules, cm_c_regular_ready_def);
  vector_add(&rules, cm_phase_frame_def);
  vector_add(&rules, cm_update_c_def);
  vector_add(&rules, get_cm_capply_def());
  vector_add(&rules, cm_ann_leave_call_def);
  vector_add(&rules, cm_ann_done_def);
  vector_add(&rules, cm_fallthrough_tail_code_def);
  vector_add(&rules, cm_return_tail_code_def);
  vector_add(&rules, get_cm_stmt_code_length());
  vector_add(&rules, get_cm_task_done_def());
  vector_add(&rules, get_theorem_by_name("NOT_CONS_NIL"));
  vector_add(&rules, get_theorem_by_name("COND_ID"));
  return rules;
}

PROOF static thm cm_c_normalize(
    const thm source, const thm_list rules) {
  thm result = source;
  for (size_t i = 0; i < 8; ++i) {
    result = conv_rule(reduce_rewrite_conv(rules), result);
  }
  return result;
}
PROOF static thm cm_c_normalize_term(
    const term source, const thm_list rules) {
  thm result = refl_rule(source);
  for (size_t i = 0; i < 8; ++i) {
    result = trans_rule(result, apply_conversion(
        reduce_rewrite_conv(rules), rhs_of(result)));
  }
  return result;
}

PROOF static gnode cm_c_normalize_goal(
    const gnode source, const thm_list rules) {
  gnode result = source;
  term conclusion = goal_ccl(result->g);
  if (alpha_compare(cm_c_application_head(conclusion),
        `cm_task_layout:cm_program->cm_task->cm_annotation->bool`) == 0) {
    thm task_shape = cm_c_normalize_term(
        cm_c_app_arg_from_right(conclusion, 1), rules);
    thm annotation_shape = cm_c_normalize_term(
        cm_c_app_arg_from_right(conclusion, 0), rules);
    result = CONV_TAC(result, rewrite_conv(THM_LIST(
        task_shape, annotation_shape)));
  }
  for (size_t i = 0; i < 8; ++i) {
    result = CONV_TAC(result, reduce_rewrite_conv(rules));
  }
  return result;
}

PROOF static void cm_c_add_rewrite_facts(
    const thm fact, thm_list *rules) {
  if (is_conj(concl(fact))) {
    cm_c_add_rewrite_facts(conjunct1_rule(fact), rules);
    cm_c_add_rewrite_facts(conjunct2_rule(fact), rules);
    return;
  }
  vector_add(rules, fact);
}
PROOF static bool cm_c_accept_done_layout(const gnode branch) {
  term conclusion = goal_ccl(branch->g);
  if (alpha_compare(cm_c_application_head(conclusion),
        `cm_task_layout:cm_program->cm_task->cm_annotation->bool`) != 0) {
    return false;
  }
  term next_task = cm_c_app_arg_from_right(conclusion, 1);
  if (alpha_compare(cm_c_application_head(next_task),
        `CMDoneTask:cm_src_state->cm_control->int->cm_task`) != 0) {
    return false;
  }
  term program = cm_c_app_arg_from_right(conclusion, 2);
  term next_annotation = cm_c_app_arg_from_right(conclusion, 0);
  term next_state = cm_c_app_arg_from_right(next_task, 2);
  term next_control = cm_c_app_arg_from_right(next_task, 1);
  term next_status = cm_c_app_arg_from_right(next_task, 0);
  ACCEPT_TAC(branch, specl_rule(TERM_LIST(
      program, next_state, next_control, next_status,
      next_annotation), get_cm_task_layout_done()));
  return true;
}
PROOF static void cm_c_accept_from_facts(
    const gnode branch, const thm ready,
    const thm layout, const thm_list rules) {
  thm normalized_ready = cm_c_normalize(ready, rules);
  if (is_const(concl(normalized_ready)) &&
      strcmp(dest_const(concl(normalized_ready)).s, "F") == 0) {
    CONTR_TAC(branch, normalized_ready);
    return;
  }
  thm_list strengthened = (thm_list)vector_copy(rules);
  cm_c_add_rewrite_facts(normalized_ready, &strengthened);
  thm normalized_layout =
      cm_c_normalize(layout, strengthened);
  gnode reduced = cm_c_normalize_goal(branch, strengthened);
  if (cm_c_accept_done_layout(reduced)) return;
  thm facts = conj_rule(normalized_ready, normalized_layout);
  thm implication = taut_rule(
      mk_imp(concl(facts), goal_ccl(reduced->g)));
  ACCEPT_TAC(reduced, mp_rule(implication, facts));
}

PROOF static void cm_c_add_while_ready_facts(
    const thm ready, const thm phase_shape, thm_list *rules) {
  term phase_constructor = rhs_of(phase_shape);
  term guard = cm_c_app_arg_from_right(phase_constructor, 5);
  term body = cm_c_app_arg_from_right(phase_constructor, 4);
  term env = cm_c_app_arg_from_right(phase_constructor, 3);
  term regions = cm_c_app_arg_from_right(phase_constructor, 2);
  term loop_start = cm_c_app_arg_from_right(phase_constructor, 1);
  term loop_end = cm_c_app_arg_from_right(phase_constructor, 0);
  thm code_ready = conjunct2_rule(ready);
  code_ready = conv_rule(
      rewrite_conv(THM_LIST(cm_c_code_ready_def)), code_ready);
  thm instantiated = specl_rule(
      TERM_LIST(guard, body, env, regions, loop_start, loop_end),
      code_ready);
  thm facts = conv_rule(
      reduce_rewrite_conv(THM_LIST(phase_shape)), instantiated);
  cm_c_add_rewrite_facts(facts, rules);
}

PROOF static thm cm_prove_c_phase_layout_step(void) {
  term annotation =
      `CMAnnotation (pc:int) (temp:int) (breakpc:int)
        (continuepc:int)
        (CMACursor (phase:cm_aphase) (owner:int)
          (saved_break:int) (saved_continue:int) ::
         (rest:(cm_acursor)list))
        (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`;
  term task =
      `CMCTask (p:cm_program) (fid:int) (ctl:cm_control)
        (st:cm_src_state)
        (cm_phase_frame (phase:cm_aphase) ::
         cm_cursor_frames (rest:(cm_acursor)list))`;
  term ready =
      `cm_c_phase_ready (ctl:cm_control)
         ${annotation:cm_annotation} (phase:cm_aphase) &&
       cm_c_code_ready (p:cm_program) (fid:int)
         ${annotation:cm_annotation} (phase:cm_aphase)`;
  term old_layout =
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${annotation:cm_annotation}`;
  term target =
      `cm_task_layout (p:cm_program) (cm_step ${task:cm_task})
        (cm_update_annotation
          (cm_annotation_step ${task:cm_task}
            ${annotation:cm_annotation}))`;
  term body = imp_chain(TERM_LIST(ready, old_layout), target);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list phase_cases = DISJ_CASES_TAC(
      introduced,
      ispec_rule(`phase:cm_aphase`,
        get_datatype_cases("cm_aphase")),
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
        goal_lasmps(phase_branch->g)[
          labeled_term_list_index(
            goal_lasmps(phase_branch->g), "Hphase")].tm);

    gnode_list control_cases = DISJ_CASES_TAC(
        phase_branch,
        ispec_rule(`ctl:cm_control`,
          get_datatype_cases("cm_control")),
        "Hcontrol");
    for (size_t j = 0; j < vector_size(control_cases); ++j) {
      gnode control_branch = control_cases[j];
      while (true) {
        labeled_term_list assumptions =
            goal_lasmps(control_branch->g);
        int index = labeled_term_list_index(
            assumptions, "Hcontrol");
        if (!is_exists(assumptions[index].tm)) break;
        control_branch = ASMP_EXISTS_TAC(
            control_branch, "Hcontrol", NULL);
      }
      thm control_shape = assume_rule(
          goal_lasmps(control_branch->g)[
            labeled_term_list_index(
              goal_lasmps(control_branch->g), "Hcontrol")].tm);

      if (i == 15) {
        term jump = cm_c_app_arg_from_right(
            rhs_of(phase_shape), 1);
        gnode_list jump_cases = BOOL_CASES_TAC(
            control_branch, jump, "Hjump");
        for (size_t k = 0; k < vector_size(jump_cases); ++k) {
          thm jump_shape = assume_rule(
              goal_lasmps(jump_cases[k]->g)[
                labeled_term_list_index(
                  goal_lasmps(jump_cases[k]->g), "Hjump")].tm);
          thm_list branch_rules = cm_c_layout_rules();
          vector_add(&branch_rules, phase_shape);
          vector_add(&branch_rules, control_shape);
          vector_add(&branch_rules, jump_shape);
          cm_c_accept_from_facts(jump_cases[k],
              assume_rule(ready), assume_rule(old_layout),
              branch_rules);
        }
        continue;
      }

      if (i == 22) {
        gnode_list call_cases = DISJ_CASES_TAC(
            control_branch,
            ispec_rule(`calls:(cm_call_sim_frame)list`,
              get_theorem_by_name("list_CASES")),
            "Hcalls");
        thm calls_nil = assume_rule(
            goal_lasmps(call_cases[0]->g)[
              labeled_term_list_index(
                goal_lasmps(call_cases[0]->g), "Hcalls")].tm);
        thm_list nil_rules = cm_c_layout_rules();
        vector_add(&nil_rules, phase_shape);
        vector_add(&nil_rules, control_shape);
        vector_add(&nil_rules, calls_nil);
        cm_c_accept_from_facts(call_cases[0],
            assume_rule(ready), assume_rule(old_layout),
            nil_rules);

        gnode call_cons = ASMP_EXISTS_TAC(
            call_cases[1], "Hcalls", NULL);
        call_cons = ASMP_EXISTS_TAC(call_cons, "Hcalls", NULL);
        thm calls_cons = assume_rule(
            goal_lasmps(call_cons->g)[
              labeled_term_list_index(
                goal_lasmps(call_cons->g), "Hcalls")].tm);
        thm_list cons_rules = cm_c_layout_rules();
        vector_add(&cons_rules, phase_shape);
        vector_add(&cons_rules, control_shape);
        vector_add(&cons_rules, calls_cons);
        cm_c_accept_from_facts(call_cons,
            assume_rule(ready), assume_rule(old_layout),
            cons_rules);
        continue;
      }

      thm_list branch_rules = cm_c_layout_rules();
      vector_add(&branch_rules, phase_shape);
      vector_add(&branch_rules, control_shape);
      if (i == 19) {
        cm_c_add_while_ready_facts(
            assume_rule(ready), phase_shape, &branch_rules);
      }
      if (i == 0 && j == 3) {
        thm halt_layout = cm_c_normalize(
            assume_rule(old_layout), branch_rules);
        thm return_code = conjunct1_rule(halt_layout);
        term code_at = concl(return_code);
        term code = cm_c_app_arg_from_right(code_at, 2);
        term code_pc = cm_c_app_arg_from_right(code_at, 1);
        term fragment = cm_c_app_arg_from_right(code_at, 0);
        thm empty_prefix = ispecl_rule(
            TERM_LIST(code, code_pc, `[]:(tvm_inst)list`, fragment),
            get_cm_code_at_append_left());
        empty_prefix = conv_rule(
            reduce_rewrite_conv(
              THM_LIST(get_theorem_by_name("APPEND"))),
            empty_prefix);
        vector_add(
            &branch_rules, match_mp_rule(empty_prefix, return_code));
      }
      cm_c_accept_from_facts(control_branch,
          assume_rule(ready), assume_rule(old_layout),
          branch_rules);
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_c_phase_layout_step =
    cm_prove_c_phase_layout_step();

PROOF thm cm_c_layout_ready_def = new_fun_definition(
    `cm_c_layout_ready (p:cm_program) (fid:int)
       (ctl:cm_control) (ann:cm_annotation) : bool =
       ((cm_ann_cursors ann == [] &&
         ~(cm_control_kind ctl == 1i) &&
         ~(cm_control_kind ctl == 2i) &&
         ~(cm_control_kind ctl == 3i)) ||
        (~(cm_ann_cursors ann == []) &&
         cm_c_phase_ready ctl ann
           (cm_cursor_phase (HD (cm_ann_cursors ann))) &&
         cm_c_code_ready p fid ann
           (cm_cursor_phase (HD (cm_ann_cursors ann)))))`);
PROOF static int _c_cm_c_layout_ready =
    cst_add_const_to_header(`cm_c_layout_ready`);

PROOF static thm cm_prove_c_cons_annotation_layout_step(void) {
  term task =
      `CMCTask (p:cm_program) (fid:int) (ctl:cm_control)
        (st:cm_src_state) (ks:(cm_frame)list)`;
  term annotation =
      `CMAnnotation (pc:int) (temp:int) (breakpc:int)
        (continuepc:int)
        (CMACursor (phase:cm_aphase) (owner:int)
          (saved_break:int) (saved_continue:int) ::
         (rest:(cm_acursor)list))
        (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`;
  term erases =
      `cm_annotation_erases ${task:cm_task}
        ${annotation:cm_annotation}`;
  term ready =
      `cm_c_layout_ready (p:cm_program) (fid:int)
        (ctl:cm_control) ${annotation:cm_annotation}`;
  term old_layout =
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${annotation:cm_annotation}`;
  term target =
      `cm_task_layout (p:cm_program) (cm_step ${task:cm_task})
        (cm_update_annotation
          (cm_annotation_step ${task:cm_task}
            ${annotation:cm_annotation}))`;
  term body = imp_chain(
      TERM_LIST(erases, ready, old_layout), target);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm frames_eq = conv_rule(
      reduce_rewrite_conv(THM_LIST(
        cm_annotation_erases_def,
        cm_ann_cursors_def, cm_cursor_frames_def,
        cm_cursor_phase_def)),
      assume_rule(erases));
  thm opened_ready = conv_rule(
      reduce_rewrite_conv(THM_LIST(
        cm_c_layout_ready_def, cm_ann_cursors_def,
        cm_cursor_phase_def, get_theorem_by_name("HD"),
        get_theorem_by_name("NOT_CONS_NIL"))),
      assume_rule(ready));
  thm rewritten_layout = conv_rule(
      rewrite_conv(THM_LIST(gsym_rule(frames_eq))),
      assume_rule(old_layout));
  thm result = match_mp_rule(
      cm_c_phase_layout_step, opened_ready);
  result = match_mp_rule(result, rewritten_layout);
  result = conv_rule(
      rewrite_conv(THM_LIST(frames_eq)), result);
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_c_cons_annotation_layout_step =
    cm_prove_c_cons_annotation_layout_step();

PROOF static thm cm_prove_c_nil_annotation_layout_step(void) {
  term task =
      `CMCTask (p:cm_program) (fid:int) (ctl:cm_control)
        (st:cm_src_state) (ks:(cm_frame)list)`;
  term annotation =
      `CMAnnotation (pc:int) (temp:int) (breakpc:int)
        (continuepc:int) ([]:(cm_acursor)list)
        (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`;
  term erases =
      `cm_annotation_erases ${task:cm_task}
        ${annotation:cm_annotation}`;
  term ready =
      `cm_c_layout_ready (p:cm_program) (fid:int)
        (ctl:cm_control) ${annotation:cm_annotation}`;
  term old_layout =
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${annotation:cm_annotation}`;
  term target =
      `cm_task_layout (p:cm_program) (cm_step ${task:cm_task})
        (cm_update_annotation
          (cm_annotation_step ${task:cm_task}
            ${annotation:cm_annotation}))`;
  term body = imp_chain(
      TERM_LIST(erases, ready, old_layout), target);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm frames_eq = conv_rule(
      reduce_rewrite_conv(THM_LIST(
        cm_annotation_erases_def, cm_ann_cursors_def,
        cm_cursor_frames_def)),
      assume_rule(erases));
  thm rewritten_layout = conv_rule(
      rewrite_conv(THM_LIST(gsym_rule(frames_eq))),
      assume_rule(old_layout));
  thm_list base_rules = cm_c_layout_rules();
  vector_add(&base_rules, gsym_rule(frames_eq));
  vector_add(&base_rules, cm_c_layout_ready_def);
  thm opened_ready = cm_c_normalize(
      assume_rule(ready), base_rules);
  cm_c_add_rewrite_facts(opened_ready, &base_rules);
  thm result = cm_c_normalize(rewritten_layout, base_rules);
  gnode_list exit_cases = BOOL_CASES_TAC(leaf,
      `cm_control_kind (ctl:cm_control) == 4i`, "Hnil_exit");
  {
    thm_list branch_rules = (thm_list)vector_copy(base_rules);
    vector_add(&branch_rules, assume_rule(
        `cm_control_kind (ctl:cm_control) == 4i`));
    gnode reduced = cm_c_normalize_goal(exit_cases[0], branch_rules);
    if (!cm_c_accept_done_layout(reduced)) {
      thm implication = taut_rule(
          mk_imp(concl(result), goal_ccl(reduced->g)));
      ACCEPT_TAC(reduced, mp_rule(implication, result));
    }
  }
  gnode_list error_cases = BOOL_CASES_TAC(exit_cases[1],
      `cm_control_kind (ctl:cm_control) == 5i`, "Hnil_error");
  for (size_t i = 0; i < vector_size(error_cases); ++i) {
    thm_list branch_rules = (thm_list)vector_copy(base_rules);
    vector_add(&branch_rules, assume_rule(
        `~(cm_control_kind (ctl:cm_control) == 4i)`));
    vector_add(&branch_rules, assume_rule(
        goal_lasmps(error_cases[i]->g)[labeled_term_list_index(
          goal_lasmps(error_cases[i]->g), "Hnil_error")].tm));
    gnode reduced = cm_c_normalize_goal(error_cases[i], branch_rules);
    if (!cm_c_accept_done_layout(reduced)) {
      thm implication = taut_rule(
          mk_imp(concl(result), goal_ccl(reduced->g)));
      ACCEPT_TAC(reduced, mp_rule(implication, result));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_c_nil_annotation_layout_step =
    cm_prove_c_nil_annotation_layout_step();

PROOF static thm cm_prove_c_task_layout_step(void) {
  term task =
      `CMCTask (p:cm_program) (fid:int) (ctl:cm_control)
        (st:cm_src_state) (ks:(cm_frame)list)`;
  term erases =
      `cm_annotation_erases ${task:cm_task}
        (ann:cm_annotation)`;
  term ready =
      `cm_c_layout_ready (p:cm_program) (fid:int)
        (ctl:cm_control) (ann:cm_annotation)`;
  term old_layout =
      `cm_task_layout (p:cm_program) ${task:cm_task}
        (ann:cm_annotation)`;
  term target =
      `cm_task_layout (p:cm_program) (cm_step ${task:cm_task})
        (cm_update_annotation
          (cm_annotation_step ${task:cm_task}
            (ann:cm_annotation)))`;
  term body = imp_chain(
      TERM_LIST(erases, ready, old_layout), target);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list annotation_cases = DISJ_CASES_TAC(
      introduced,
      ispec_rule(`ann:cm_annotation`,
        get_datatype_cases("cm_annotation")),
      "Hannotation");
  for (size_t i = 0; i < vector_size(annotation_cases); ++i) {
    gnode branch = annotation_cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(branch->g);
      int index =
          labeled_term_list_index(assumptions, "Hannotation");
      if (!is_exists(assumptions[index].tm)) break;
      branch = ASMP_EXISTS_TAC(branch, "Hannotation", NULL);
    }
    thm annotation_shape = assume_rule(
        goal_lasmps(branch->g)[
          labeled_term_list_index(
            goal_lasmps(branch->g), "Hannotation")].tm);
    term cursors = cm_c_app_arg_from_right(
        rhs_of(annotation_shape), 3);
    gnode_list cursor_cases = DISJ_CASES_TAC(
        branch,
        ispec_rule(cursors, get_theorem_by_name("list_CASES")),
        "Hcursors");

    thm cursors_nil = assume_rule(
        goal_lasmps(cursor_cases[0]->g)[
          labeled_term_list_index(
            goal_lasmps(cursor_cases[0]->g), "Hcursors")].tm);
    thm_list nil_shapes =
        THM_LIST(annotation_shape, cursors_nil);
    thm nil_erases = conv_rule(
        rewrite_conv(nil_shapes), assume_rule(erases));
    thm nil_ready = conv_rule(
        rewrite_conv(nil_shapes), assume_rule(ready));
    thm nil_layout = conv_rule(
        rewrite_conv(nil_shapes), assume_rule(old_layout));
    thm nil_result = match_mp_rule(
        cm_c_nil_annotation_layout_step, nil_erases);
    nil_result = match_mp_rule(nil_result, nil_ready);
    nil_result = match_mp_rule(nil_result, nil_layout);
    nil_result = conv_rule(
        rewrite_conv(nil_shapes), nil_result);
    gnode nil_goal = CONV_TAC(
        cursor_cases[0], rewrite_conv(nil_shapes));
    ACCEPT_TAC(nil_goal, nil_result);

    gnode cons = ASMP_EXISTS_TAC(
        cursor_cases[1], "Hcursors", NULL);
    cons = ASMP_EXISTS_TAC(cons, "Hcursors", NULL);
    thm cursors_cons = assume_rule(
        goal_lasmps(cons->g)[
          labeled_term_list_index(
            goal_lasmps(cons->g), "Hcursors")].tm);
    term cursor = cm_c_app_arg_from_right(
        rhs_of(cursors_cons), 1);
    gnode_list cursor_shapes = DISJ_CASES_TAC(
        cons,
        ispec_rule(cursor, get_datatype_cases("cm_acursor")),
        "Hcursor");
    for (size_t j = 0; j < vector_size(cursor_shapes); ++j) {
      gnode cursor_branch = cursor_shapes[j];
      while (true) {
        labeled_term_list cursor_assumptions =
            goal_lasmps(cursor_branch->g);
        int index = labeled_term_list_index(
            cursor_assumptions, "Hcursor");
        if (!is_exists(cursor_assumptions[index].tm)) break;
        cursor_branch =
            ASMP_EXISTS_TAC(cursor_branch, "Hcursor", NULL);
      }
      thm cursor_shape = assume_rule(
          goal_lasmps(cursor_branch->g)[
            labeled_term_list_index(
              goal_lasmps(cursor_branch->g), "Hcursor")].tm);
      thm_list cons_shapes = THM_LIST(
          annotation_shape, cursors_cons, cursor_shape);
      thm cons_erases = conv_rule(
          rewrite_conv(cons_shapes), assume_rule(erases));
      thm cons_ready = conv_rule(
          rewrite_conv(cons_shapes), assume_rule(ready));
      thm cons_layout = conv_rule(
          rewrite_conv(cons_shapes), assume_rule(old_layout));
      thm cons_result = match_mp_rule(
          cm_c_cons_annotation_layout_step, cons_erases);
      cons_result = match_mp_rule(cons_result, cons_ready);
      cons_result = match_mp_rule(cons_result, cons_layout);
      cons_result = conv_rule(
          rewrite_conv(cons_shapes), cons_result);
      gnode cons_goal = CONV_TAC(
          cursor_branch, rewrite_conv(cons_shapes));
      ACCEPT_TAC(cons_goal, cons_result);
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_c_task_layout_step =
    cm_prove_c_task_layout_step();

PROOF thm get_cm_c_task_layout_step(void) {
  return cm_c_task_layout_step;
}

PROOF static int cmc_preservation_code_control_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_code_control_axioms_before,
      "cmc_preservation_code_control introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_code_control_checks =
    cmc_preservation_code_control_final_checks();
