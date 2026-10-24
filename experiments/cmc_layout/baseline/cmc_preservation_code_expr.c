#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_code.h"
#require "cmc_preservation_code.c"
#include "cmc_preservation_code_expr.h"

PROOF static size_t _cmc_preservation_code_expr_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_layout_ilength_cond(void) {
  gnode root = gnode_new_with_ccl(
      `!(b:bool). !(xs:(A)list). !(ys:(A)list).
         ilength (if b then xs else ys) ==
         (if b then ilength xs else ilength ys)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(leaf, `b:bool`, "hcondition");
  for (size_t i = 0; i < 2; ++i) {
    CONV_WITH_ASMP_TAC(
        cases[i], reduce_rewrite_conv, THM_LIST());
  }
  return gnode_prove(root);
}
PROOF static thm cm_layout_ilength_cond =
    cm_prove_layout_ilength_cond();

PROOF static thm cm_layout_rvalue_code_length = gen_rule(
    `expr:cm_expr`,
    conjunct2_rule(spec_rule(
      `expr:cm_expr`, get_cm_expr_code_lengths())));

PROOF static thm cm_layout_rcode_length = conv_rule(
    pure_rewrite_conv(THM_LIST(get_cm_emit_rvalue_def())),
    cm_layout_rvalue_code_length);

PROOF static thm cm_prove_layout_code_length(
    const term statement, const thm_list rules) {
  gnode root = gnode_new_with_ccl(statement);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode reduced =
      CONV_TAC(leaf, reduce_rewrite_conv(rules));
  if (IS_NULL(reduced->solved)) {
    ACCEPT_TAC(reduced, int_arith_rule(goal_ccl(reduced->g)));
  }
  return gnode_prove(root);
}

PROOF static thm cm_layout_char_normalize_length =
    cm_prove_layout_code_length(
      `!(ty:cm_type).
         ilength (cm_char_normalize_code ty) ==
         cm_char_normalize_count ty`,
      THM_LIST(get_cm_char_normalize_code_def(),
        get_cm_char_normalize_count_def(), cm_layout_ilength_cond,
        get_theorem_by_name("ILENGTH_DEF"),
        get_theorem_by_name("ILENGTH_APPEND"),
        get_theorem_by_name("APPEND")));

PROOF static thm cm_layout_load_length =
    cm_prove_layout_code_length(
      `!(ty:cm_type). ilength (cm_load_code ty) == 1i`,
      THM_LIST(get_cm_load_code_def(),
        get_theorem_by_name("ILENGTH_DEF"),
        get_theorem_by_name("APPEND")));

PROOF static thm cm_layout_store_length =
    cm_prove_layout_code_length(
      `!(ty:cm_type). ilength (cm_store_code ty) == 1i`,
      THM_LIST(get_cm_store_code_def(),
        get_theorem_by_name("ILENGTH_DEF"),
        get_theorem_by_name("APPEND")));

PROOF static thm cm_layout_temp_store_length =
    cm_prove_layout_code_length(
      `!(p:cm_program) (fid:int) (temp:int).
         ilength (cm_temp_store_code p fid temp) == 5i`,
      THM_LIST(get_cm_temp_store_code_def(),
        get_cm_fp_relative_address_code_def(),
        get_theorem_by_name("ILENGTH_DEF"),
        get_theorem_by_name("ILENGTH_APPEND"),
        get_theorem_by_name("APPEND")));

PROOF static thm cm_layout_temp_load_length =
    cm_prove_layout_code_length(
      `!(p:cm_program) (fid:int) (temp:int).
         ilength (cm_temp_load_code p fid temp) == 5i`,
      THM_LIST(get_cm_temp_load_code_def(),
        get_cm_fp_relative_address_code_def(),
        get_theorem_by_name("ILENGTH_DEF"),
        get_theorem_by_name("ILENGTH_APPEND"),
        get_theorem_by_name("APPEND")));

PROOF static thm cm_layout_assign_tail_length =
    cm_prove_layout_code_length(
      `!(p:cm_program) (fid:int) (ty:cm_type) (temp:int).
         ilength (cm_assign_tail_code p fid ty temp) ==
         cm_char_normalize_count ty + 12i`,
      THM_LIST(cm_assign_tail_code_def,
        cm_layout_char_normalize_length, cm_layout_temp_load_length,
        get_cm_store_code_def(), cm_layout_load_length,
        get_theorem_by_name("ILENGTH_DEF"),
        get_theorem_by_name("ILENGTH_APPEND"),
        get_theorem_by_name("APPEND")));

PROOF static thm cm_layout_index_tail_length =
    cm_prove_layout_code_length(
      `!(p:cm_program) (fid:int) (ty:cm_type) (temp:int).
         ilength (cm_index_tail_code p fid ty temp) == 8i`,
      THM_LIST(cm_index_tail_code_def, cm_layout_temp_load_length,
        get_theorem_by_name("ILENGTH_DEF"),
        get_theorem_by_name("ILENGTH_APPEND"),
        get_theorem_by_name("APPEND")));

PROOF static thm cm_layout_member_tail_length =
    cm_prove_layout_code_length(
      `!(p:cm_program) (base_ty:cm_type) (mid:int).
         ilength (cm_member_tail_code p base_ty mid) == 2i`,
      THM_LIST(cm_member_tail_code_def,
        get_theorem_by_name("ILENGTH_DEF"),
        get_theorem_by_name("APPEND")));

PROOF static thm cm_layout_binary_finish_length =
    cm_prove_layout_code_length(
      `!(p:cm_program) (fid:int) (op:int) (left:cm_expr)
         (right:cm_expr) (temp:int).
         5i +
           ilength
             (cm_binary_finish_code p fid op left right temp) ==
         cm_binary_tail_count p op left right`,
      THM_LIST(get_cm_binary_finish_code_def(),
        get_cm_binary_tail_count_def(), cm_layout_temp_load_length,
        cm_layout_ilength_cond,
        get_theorem_by_name("ILENGTH_DEF"),
        get_theorem_by_name("ILENGTH_APPEND"),
        get_theorem_by_name("APPEND")));

PROOF static term cm_layout_binary_phase_proposition(void) {
  return
      `(prefix:int) +
        (if (op:int) == 0i || op == 1i
         then 1i + (count:int) + 4i
         else 5i + count +
           ilength
             (cm_binary_finish_code (p:cm_program) (fid:int) op
               (left:cm_expr) (right:cm_expr) (temp:int))) ==
       (if op == 0i || op == 1i
        then prefix + count + 5i
        else prefix + count +
          cm_binary_tail_count p op left right)`;
}

PROOF static thm cm_prove_layout_binary_phase_branch(
    bool short_circuit) {
  term condition = `(op:int) == 0i || op == 1i`;
  term proposition = cm_layout_binary_phase_proposition();
  term premise = short_circuit ? condition : mk_not(condition);
  gnode root =
      gnode_new_with_ccl(mk_imp(premise, proposition));
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode reduced = CONV_WITH_ASMP_TAC(
      leaf, reduce_rewrite_conv, THM_LIST());
  if (IS_NULL(reduced->solved)) {
    if (short_circuit) {
      ACCEPT_TAC(reduced, int_arith_rule(goal_ccl(reduced->g)));
    } else {
      thm finish = ispecl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `op:int`, `left:cm_expr`,
          `right:cm_expr`, `temp:int`),
          cm_layout_binary_finish_length);
      ACCEPT_TAC(reduced, mp_rule(
          int_arith_rule(mk_imp(concl(finish),
            goal_ccl(reduced->g))),
          finish));
    }
  }
  return gnode_prove(root);
}

PROOF static thm cm_prove_layout_binary_phase_length(void) {
  term proposition = cm_layout_binary_phase_proposition();
  thm positive = cm_prove_layout_binary_phase_branch(true);
  thm negative = cm_prove_layout_binary_phase_branch(false);
  thm cases = taut_rule(
      mk_imp(concl(positive), mk_imp(concl(negative), proposition)));
  thm result = mp_rule(mp_rule(cases, positive), negative);
  return genl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `op:int`, `left:cm_expr`,
      `right:cm_expr`, `temp:int`, `prefix:int`, `count:int`),
      result);
}
PROOF static thm cm_layout_binary_phase_length =
    cm_prove_layout_binary_phase_length();

PROOF static thm cm_prove_layout_append_cond_left(void) {
  gnode root = gnode_new_with_ccl(
      `!(b:bool). !(left:(A)list). !(yes:(A)list). !(no:(A)list).
         left ++ (if b then yes else no) ==
         (if b then left ++ yes else left ++ no)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(leaf, `b:bool`, "hcondition");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_WITH_ASMP_TAC(
        cases[i], reduce_rewrite_conv, THM_LIST());
  }
  return gnode_prove(root);
}
PROOF static thm cm_layout_append_cond_left =
    cm_prove_layout_append_cond_left();

PROOF static thm cm_prove_layout_append_cond_right(void) {
  gnode root = gnode_new_with_ccl(
      `!(b:bool). !(yes:(A)list). !(no:(A)list). !(right:(A)list).
         (if b then yes else no) ++ right ==
         (if b then yes ++ right else no ++ right)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(leaf, `b:bool`, "hcondition");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_WITH_ASMP_TAC(
        cases[i], reduce_rewrite_conv, THM_LIST());
  }
  return gnode_prove(root);
}
PROOF static thm cm_layout_append_cond_right =
    cm_prove_layout_append_cond_right();

PROOF static thm cm_prove_layout_add_cond(void) {
  gnode root = gnode_new_with_ccl(
      `!(b:bool). !(left:int). !(yes:int). !(no:int).
         left + (if b then yes else no) ==
         (if b then left + yes else left + no)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(leaf, `b:bool`, "hcondition");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_WITH_ASMP_TAC(
        cases[i], reduce_rewrite_conv, THM_LIST());
  }
  return gnode_prove(root);
}
PROOF static thm cm_layout_add_cond =
    cm_prove_layout_add_cond();

PROOF static thm cm_layout_binary_short_length = genl_rule(
    TERM_LIST(`prefix:int`, `count:int`),
    int_arith_rule(
      `(prefix:int) + (1i + (count:int) + 4i) ==
       prefix + count + 5i`));

PROOF static thm cm_layout_binary_short_chain = genl_rule(
    TERM_LIST(`prefix:int`, `count:int`),
    int_arith_rule(
      `(prefix:int) + 1i + (count:int) + 4i ==
       prefix + count + 5i`));

PROOF static thm cm_layout_binary_long_length = genl_rule(
    TERM_LIST(`p:cm_program`, `fid:int`, `op:int`, `left:cm_expr`,
      `right:cm_expr`, `temp:int`, `prefix:int`, `count:int`),
    mp_rule(
      int_arith_rule(mk_imp(
        concl(ispecl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `op:int`, `left:cm_expr`,
          `right:cm_expr`, `temp:int`),
          cm_layout_binary_finish_length)),
        `(prefix:int) +
           (5i + (count:int) +
             ilength
               (cm_binary_finish_code (p:cm_program) (fid:int)
                 (op:int) (left:cm_expr) (right:cm_expr) (temp:int))) ==
         prefix + count +
           cm_binary_tail_count p op left right`)),
      ispecl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `op:int`, `left:cm_expr`,
        `right:cm_expr`, `temp:int`),
        cm_layout_binary_finish_length)));




PROOF static thm cm_prove_layout_call_cons_length(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (pc:int) (slot:int) (scratch:int)
         (args:(cm_expr)list) (prefix:int).
         prefix + 5i +
           ilength
             (cm_emit_args_store p fid pc slot scratch args) +
           5i +
           ilength (cm_emit_args_reload p fid slot args) + 1i ==
         prefix + 10i +
           cm_args_code_count_of (cm_args_code_counts p fid args)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm lengths = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `pc:int`, `slot:int`,
      `scratch:int`), spec_rule(
        `args:(cm_expr)list`, get_cm_args_code_lengths()));
  ACCEPT_TAC(leaf, mp_rule(
      int_arith_rule(mk_imp(concl(lengths), goal_ccl(leaf->g))),
      lengths));
  return gnode_prove(root);
}
PROOF static thm cm_layout_call_cons_length =
    cm_prove_layout_call_cons_length();

PROOF static thm_list cm_layout_expr_rules(void) {
  return THM_LIST(
      cm_layout_rcode_length, cm_layout_rvalue_code_length,
      cm_layout_ilength_cond, cm_layout_char_normalize_length,
      cm_layout_load_length, cm_layout_store_length,
      cm_layout_temp_store_length,
      cm_layout_temp_load_length, cm_layout_assign_tail_length,
      cm_layout_index_tail_length, cm_layout_member_tail_length,
      cm_layout_binary_finish_length,
      cm_layout_binary_phase_length,
      cm_layout_binary_short_length, cm_layout_binary_short_chain,
      cm_layout_binary_long_length, cm_layout_call_cons_length,
      cm_layout_append_cond_left, cm_layout_append_cond_right,
      cm_layout_add_cond, get_cm_expr_code_lengths(),
      get_cm_args_code_lengths(),
      cm_task_layout_def, get_cm_task_done_def(),
      cm_task_code_def, cm_task_fid_def,
      cm_cont_code_def, cm_normal_cont_code_def,
      cm_status_tail_code_def, cm_cursor_code_def,
      cm_value_phase_code_def,
      cm_normal_phase_code_def, cm_phase_stops_def,
      cm_normal_phase_stops_def, cm_phase_yields_normal_def,
      cm_saved_layout_def, cm_phase_site_def, cm_phase_is_call_def,
      cm_phase_caller_def, cm_annotation_step_def,
      cm_update_annotation_def, cm_update_r_def, cm_update_l_def,
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def, cm_ann_calls_def,
      cm_cursor_phase_def, cm_cursor_temp_def, cm_cursor_break_def,
      cm_cursor_continue_def,
      cm_ann_linear_def, cm_ann_plain_def, cm_ann_push_def,
      cm_ann_replace_def, cm_ann_pop_def, get_cm_step_def(),
      get_cm_rstart_def(), get_cm_lstart_def(),
      get_cm_emit_rvalue_def(), get_cm_emit_lvalue_def(),
      get_cm_emit_expr_pair_def(), get_cm_rcode_of_def(),
      get_cm_lcode_of_def(), get_cm_emit_args_reload_def(),
      get_cm_push_code_def(), get_cm_char_normalize_count_def(),
      cm_assign_tail_code_def, cm_index_tail_code_def,
      cm_member_tail_code_def,
      get_cm_rvalue_code_count_def(), get_cm_lvalue_code_count_def(),
      get_cm_expr_code_counts_def(), get_cm_rcount_of_def(),
      get_cm_lcount_of_def(), get_cm_args_code_count_of_def(),
      get_cm_args_arity_of_def(),
      get_theorem_by_name("ILENGTH_DEF"),
      get_theorem_by_name("ILENGTH_APPEND"),
      get_theorem_by_name("NOT_CONS_NIL"),
      get_theorem_by_name("HD"), get_theorem_by_name("TL"),
      get_theorem_by_name("APPEND"),
      get_theorem_by_name("APPEND_NIL"),
      gsym_rule(get_theorem_by_name("APPEND_ASSOC")),
      int_ring_rule(
        `1i + (a:int) + 4i == a + 5i`),
      int_ring_rule(
        `((a:int) + 5i) + 1i + 6i == a + 12i`),
      int_ring_rule(
        `(a:int) + (b:int) + 5i + (c:int) + 8i ==
         a + b + c + 13i`),
      int_ring_rule(
        `((a:int) + (b:int)) + (c:int) == a + (b + c)`));
}

PROOF static thm cm_prove_r_const_layout_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (n:int) (ty:cm_type)
         (st:cm_src_state) (ks:(cm_frame)list) (ann:cm_annotation).
         cm_task_layout p (CMRTask p fid (CMConstE n ty) st ks) ann ==>
         cm_task_layout p
           (cm_step (CMRTask p fid (CMConstE n ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask p fid (CMConstE n ty) st ks) ann))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm old_layout = assume_rule(
      `cm_task_layout (p:cm_program)
         (CMRTask p (fid:int) (CMConstE (n:int) (ty:cm_type))
           (st:cm_src_state) (ks:(cm_frame)list))
         (ann:cm_annotation)`);
  thm_list rules = cm_layout_expr_rules();
  thm old_open = conv_rule(reduce_rewrite_conv(rules), old_layout);
  thm old_code = conjunct1_rule(old_open);
  thm old_sites = conjunct2_rule(old_open);
  thm suffix_rule = ispecl_rule(TERM_LIST(
      `cm_model_code (p:cm_program)`, `cm_ann_pc (ann:cm_annotation)`,
      `[TVMInst TVMPushOp (cm_const_immediate (ty:cm_type) (n:int))]:
         (tvm_inst)list`,
      `cm_cont_code (p:cm_program) (fid:int)
         (cm_ann_pc (ann:cm_annotation) + 1i)
         (cm_ann_temp ann) (cm_ann_cursors ann)`),
      cm_code_at_append_right);
  thm suffix = mp_rule(
      conv_rule(reduce_rewrite_conv(rules), suffix_rule), old_code);
  thm result = conj_rule(suffix, old_sites);
  gnode opened = CONV_TAC(leaf, reduce_rewrite_conv(rules));
  ACCEPT_TAC(opened, result);
  return gnode_prove(root);
}

PROOF static thm cm_prove_r_linear_layout_step(
    const term statement, const term expression, const term prefix,
    const thm condition) {
  gnode root = gnode_new_with_ccl(statement);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm_list rules = cm_layout_expr_rules();
  if (!IS_NULL(condition)) vector_add(&rules, condition);
  term emitted =
      `cm_emit_rvalue (p:cm_program) (fid:int)
         (cm_ann_pc (ann:cm_annotation)) (cm_ann_temp ann)
         ${expression:cm_expr}`;
  term counted =
      `cm_rvalue_code_count (p:cm_program) (fid:int)
         ${expression:cm_expr}`;
  thm emitted_length = ispecl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `cm_ann_pc (ann:cm_annotation)`,
      `cm_ann_temp (ann:cm_annotation)`),
      conjunct2_rule(
        spec_rule(expression, get_cm_expr_code_lengths())));
  thm emitted_eq =
      apply_conversion(reduce_rewrite_conv(rules), emitted);
  thm counted_eq =
      apply_conversion(reduce_rewrite_conv(rules), counted);
  thm prefix_length = trans_rule(
      gsym_rule(beta_norm(ap_term_rule(
        `\code:(tvm_inst)list. ilength code`, emitted_eq))),
      trans_rule(emitted_length, counted_eq));
  vector_add(&rules, prefix_length);
  term old_fact =
      `cm_task_layout (p:cm_program)
         (CMRTask p (fid:int) ${expression:cm_expr}
           (st:cm_src_state) (ks:(cm_frame)list))
         (ann:cm_annotation)`;
  thm old_layout = assume_rule(old_fact);
  thm old_open = conv_rule(reduce_rewrite_conv(rules), old_layout);
  thm old_code = conjunct1_rule(old_open);
  thm old_sites = conjunct2_rule(old_open);
  thm suffix_rule = ispecl_rule(TERM_LIST(
      `cm_model_code (p:cm_program)`, `cm_ann_pc (ann:cm_annotation)`,
      prefix,
      `cm_cont_code (p:cm_program) (fid:int)
         (cm_ann_pc (ann:cm_annotation) + ilength ${prefix:(tvm_inst)list})
         (cm_ann_temp ann) (cm_ann_cursors ann)`),
      cm_code_at_append_right);
  thm suffix = mp_rule(
      conv_rule(reduce_rewrite_conv(rules), suffix_rule), old_code);
  gnode opened = CONV_TAC(leaf, reduce_rewrite_conv(rules));
  ACCEPT_TAC(opened, conj_rule(suffix, old_sites));
  return gnode_prove(root);
}

PROOF thm cm_r_string_layout_step =
    cm_prove_r_linear_layout_step(
      `!(p:cm_program) (fid:int) (sid:int) (ty:cm_type)
         (st:cm_src_state) (ks:(cm_frame)list) (ann:cm_annotation).
         cm_task_layout p (CMRTask p fid (CMStringE sid ty) st ks) ann ==>
         cm_task_layout p
           (cm_step (CMRTask p fid (CMStringE sid ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask p fid (CMStringE sid ty) st ks) ann))`,
      `CMStringE (sid:int) (ty:cm_type)`,
      `cm_push_code
         (cm_string_address (p:cm_program) (sid:int))`,
      empty_theorem);

PROOF thm cm_r_sizeof_layout_step =
    cm_prove_r_linear_layout_step(
      `!(p:cm_program) (fid:int) (asked:cm_type) (ty:cm_type)
         (st:cm_src_state) (ks:(cm_frame)list) (ann:cm_annotation).
         cm_task_layout p
           (CMRTask p fid (CMSizeofE asked ty) st ks) ann ==>
         cm_task_layout p
           (cm_step (CMRTask p fid (CMSizeofE asked ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask p fid (CMSizeofE asked ty) st ks) ann))`,
      `CMSizeofE (asked:cm_type) (ty:cm_type)`,
      `cm_push_code
         (cm_type_size (cm_program_structs (p:cm_program))
           (asked:cm_type))`,
      empty_theorem);

PROOF static thm cm_r_getc_nonempty_layout_step =
    cm_prove_r_linear_layout_step(
      `!(p:cm_program) (fid:int) (ty:cm_type)
         (st:cm_src_state) (ks:(cm_frame)list) (ann:cm_annotation).
         ~(cm_state_input st == []) ==>
         tower_byte_value (HD (cm_state_input st)) ==>
         cm_task_layout p (CMRTask p fid (CMGetcE ty) st ks) ann ==>
         cm_task_layout p
           (cm_step (CMRTask p fid (CMGetcE ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask p fid (CMGetcE ty) st ks) ann))`,
      `CMGetcE (ty:cm_type)`,
      `[TVMInst TVMGetcOp 0i]:(tvm_inst)list`,
      conj_rule(
        assume_rule(`~(cm_state_input (st:cm_src_state) == [])`),
        assume_rule(`tower_byte_value
          (HD (cm_state_input (st:cm_src_state)))`)));
PROOF static thm cm_r_getc_empty_layout_step =
    cm_prove_r_linear_layout_step(
      `!(p:cm_program) (fid:int) (ty:cm_type)
         (st:cm_src_state) (ks:(cm_frame)list) (ann:cm_annotation).
         cm_state_input st == [] ==>
         cm_task_layout p (CMRTask p fid (CMGetcE ty) st ks) ann ==>
         cm_task_layout p
           (cm_step (CMRTask p fid (CMGetcE ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask p fid (CMGetcE ty) st ks) ann))`,
      `CMGetcE (ty:cm_type)`,
      `[TVMInst TVMGetcOp 0i]:(tvm_inst)list`,
      assume_rule(`cm_state_input (st:cm_src_state) == []`));

PROOF static thm cm_prove_r_getc_layout_step(void) {
  term_list variables = TERM_LIST(
      `p:cm_program`, `fid:int`, `ty:cm_type`,
      `st:cm_src_state`, `ks:(cm_frame)list`, `ann:cm_annotation`);
  thm empty = ispecl_rule(
      variables, cm_r_getc_empty_layout_step);
  thm nonempty = ispecl_rule(
      variables, cm_r_getc_nonempty_layout_step);
  term layout =
      `cm_task_layout (p:cm_program)
         (CMRTask p (fid:int) (CMGetcE (ty:cm_type))
           (st:cm_src_state) (ks:(cm_frame)list))
         (ann:cm_annotation)`;
  term input_ready =
      `cm_state_input (st:cm_src_state) == [] ||
       tower_byte_value (HD (cm_state_input st))`;
  term result =
      `cm_task_layout (p:cm_program)
         (cm_step
           (CMRTask p (fid:int) (CMGetcE (ty:cm_type))
             (st:cm_src_state) (ks:(cm_frame)list)))
         (cm_update_annotation
           (cm_annotation_step
             (CMRTask p fid (CMGetcE ty) st ks) ann))`;
  thm proof = taut_rule(
      imp_chain(TERM_LIST(concl(empty), concl(nonempty), input_ready,
        layout), result));
  return genl_rule(variables,
      mp_rule(mp_rule(proof, empty), nonempty));
}
PROOF thm cm_r_getc_layout_step =
    cm_prove_r_getc_layout_step();


PROOF thm cm_r_array_var_layout_step =
    cm_prove_r_linear_layout_step(
      `!(p:cm_program) (fid:int) (scope:int) (slot:int) (ty:cm_type)
         (st:cm_src_state) (ks:(cm_frame)list) (ann:cm_annotation).
         cm_binding_array p fid scope slot ==>
         cm_binding_address_ok p fid scope slot st ==>
         cm_task_layout p
           (CMRTask p fid (CMVarE scope slot ty) st ks) ann ==>
         cm_task_layout p
           (cm_step (CMRTask p fid (CMVarE scope slot ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask p fid (CMVarE scope slot ty) st ks) ann))`,
      `CMVarE (scope:int) (slot:int) (ty:cm_type)`,
      `cm_binding_address_code
         (p:cm_program) (fid:int) (scope:int) (slot:int)`,
      conj_rule(
        assume_rule(
          `cm_binding_array (p:cm_program) (fid:int)
            (scope:int) (slot:int)`),
        assume_rule(
          `cm_binding_address_ok (p:cm_program) (fid:int)
            (scope:int) (slot:int) (st:cm_src_state)`)));
PROOF thm cm_r_const_layout_step = cm_prove_r_const_layout_step();

PROOF static thm cm_prove_r_structural_layout_step(
    const term statement, const term expression,
    const thm_list extra_rules) {
  gnode root = gnode_new_with_ccl(statement);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm_list rules = cm_layout_expr_rules();
  for (size_t i = 0; i < vector_size(extra_rules); ++i) {
    vector_add(&rules, extra_rules[i]);
  }
  thm old_layout = assume_rule(
      `cm_task_layout (p:cm_program)
         (CMRTask p (fid:int) ${expression:cm_expr}
           (st:cm_src_state) (ks:(cm_frame)list))
         (ann:cm_annotation)`);
  thm normalized =
      conv_rule(reduce_rewrite_conv(rules), old_layout);
  gnode reduced =
      CONV_TAC(leaf, reduce_rewrite_conv(rules));
  if (vector_size(extra_rules) > 0) {
    normalized =
        conv_rule(rewrite_conv(extra_rules), normalized);
    reduced =
        CONV_TAC(reduced, rewrite_conv(extra_rules));
  }
  ACCEPT_TAC(reduced, normalized);
  return gnode_prove(root);
}

PROOF thm cm_r_scalar_var_layout_step =
    cm_prove_r_structural_layout_step(
      `!(p:cm_program) (fid:int) (scope:int) (slot:int) (ty:cm_type)
         (st:cm_src_state) (ks:(cm_frame)list) (ann:cm_annotation).
         ~cm_binding_array p fid scope slot ==>
         cm_task_layout p
           (CMRTask p fid (CMVarE scope slot ty) st ks) ann ==>
         cm_task_layout p
           (cm_step (CMRTask p fid (CMVarE scope slot ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask p fid (CMVarE scope slot ty) st ks) ann))`,
      `CMVarE (scope:int) (slot:int) (ty:cm_type)`,
      THM_LIST(assume_rule(
        `~cm_binding_array (p:cm_program) (fid:int)
           (scope:int) (slot:int)`)));
PROOF static thm cm_prove_r_var_layout_step(void) {
  term_list variables = TERM_LIST(
      `p:cm_program`, `fid:int`, `scope:int`, `slot:int`,
      `ty:cm_type`, `st:cm_src_state`, `ks:(cm_frame)list`,
      `ann:cm_annotation`);
  thm array = ispecl_rule(
      variables, cm_r_array_var_layout_step);
  thm scalar = ispecl_rule(
      variables, cm_r_scalar_var_layout_step);
  term address_ready =
      `cm_binding_array (p:cm_program) (fid:int)
         (scope:int) (slot:int) ==>
       cm_binding_address_ok p fid scope slot (st:cm_src_state)`;
  term layout =
      `cm_task_layout (p:cm_program)
         (CMRTask p (fid:int)
           (CMVarE (scope:int) (slot:int) (ty:cm_type))
           (st:cm_src_state) (ks:(cm_frame)list))
         (ann:cm_annotation)`;
  term result =
      `cm_task_layout (p:cm_program)
         (cm_step
           (CMRTask p (fid:int)
             (CMVarE (scope:int) (slot:int) (ty:cm_type))
             (st:cm_src_state) (ks:(cm_frame)list)))
         (cm_update_annotation
           (cm_annotation_step
             (CMRTask p fid (CMVarE scope slot ty) st ks) ann))`;
  thm proof = taut_rule(
      imp_chain(TERM_LIST(concl(array), concl(scalar),
        address_ready, layout), result));
  return genl_rule(variables,
      mp_rule(mp_rule(proof, array), scalar));
}
PROOF thm cm_r_var_layout_step =
    cm_prove_r_var_layout_step();
PROOF thm cm_r_assign_layout_step =
    cm_prove_r_structural_layout_step(
      `!(p:cm_program) (fid:int) (dst:cm_expr) (src:cm_expr)
         (ty:cm_type) (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         cm_task_layout p
           (CMRTask p fid (CMAssignE dst src ty) st ks) ann ==>
         cm_task_layout p
           (cm_step (CMRTask p fid (CMAssignE dst src ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask p fid (CMAssignE dst src ty) st ks) ann))`,
      `CMAssignE (dst:cm_expr) (src:cm_expr) (ty:cm_type)`,
      THM_LIST());

PROOF thm cm_r_binary_layout_step =
    cm_prove_r_structural_layout_step(
      `!(p:cm_program) (fid:int) (op:int) (left:cm_expr)
         (right:cm_expr) (ty:cm_type) (st:cm_src_state)
         (ks:(cm_frame)list) (ann:cm_annotation).
         cm_task_layout p
           (CMRTask p fid (CMBinaryE op left right ty) st ks) ann ==>
         cm_task_layout p
           (cm_step (CMRTask p fid (CMBinaryE op left right ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask p fid (CMBinaryE op left right ty) st ks) ann))`,
      `CMBinaryE (op:int) (left:cm_expr) (right:cm_expr)
         (ty:cm_type)`,
      THM_LIST(int_arith_rule(
        `cm_ann_pc (ann:cm_annotation) +
           cm_rcount_of
             (cm_expr_code_counts (p:cm_program) (fid:int)
               (left:cm_expr)) +
           1i +
           cm_rcount_of
             (cm_expr_code_counts p fid (right:cm_expr)) +
           4i ==
         cm_ann_pc ann +
           cm_rcount_of (cm_expr_code_counts p fid left) +
           cm_rcount_of (cm_expr_code_counts p fid right) +
           5i`)));

PROOF static thm cm_r_unary_two_layout_step =
    cm_prove_r_structural_layout_step(
      `!(p:cm_program) (fid:int) (op:int) (src:cm_expr)
         (ty:cm_type) (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         op == 2i ==>
         cm_task_layout p
           (CMRTask p fid (CMUnaryE op src ty) st ks) ann ==>
         cm_task_layout p
           (cm_step (CMRTask p fid (CMUnaryE op src ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask p fid (CMUnaryE op src ty) st ks) ann))`,
      `CMUnaryE (op:int) (src:cm_expr) (ty:cm_type)`,
      THM_LIST(assume_rule(`(op:int) == 2i`)));

PROOF static thm cm_r_unary_three_layout_step =
    cm_prove_r_structural_layout_step(
      `!(p:cm_program) (fid:int) (op:int) (src:cm_expr)
         (ty:cm_type) (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         ~(op == 2i) ==> op == 3i ==>
         cm_task_layout p
           (CMRTask p fid (CMUnaryE op src ty) st ks) ann ==>
         cm_task_layout p
           (cm_step (CMRTask p fid (CMUnaryE op src ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask p fid (CMUnaryE op src ty) st ks) ann))`,
      `CMUnaryE (op:int) (src:cm_expr) (ty:cm_type)`,
      THM_LIST(assume_rule(`~((op:int) == 2i)`),
        assume_rule(`(op:int) == 3i`)));

PROOF static thm cm_r_unary_other_layout_step =
    cm_prove_r_structural_layout_step(
      `!(p:cm_program) (fid:int) (op:int) (src:cm_expr)
         (ty:cm_type) (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         ~(op == 2i) ==> ~(op == 3i) ==>
         cm_task_layout p
           (CMRTask p fid (CMUnaryE op src ty) st ks) ann ==>
         cm_task_layout p
           (cm_step (CMRTask p fid (CMUnaryE op src ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask p fid (CMUnaryE op src ty) st ks) ann))`,
      `CMUnaryE (op:int) (src:cm_expr) (ty:cm_type)`,
      THM_LIST(assume_rule(`~((op:int) == 2i)`),
        assume_rule(`~((op:int) == 3i)`)));

PROOF static thm cm_prove_r_unary_layout_step(void) {
  term_list variables = TERM_LIST(
      `p:cm_program`, `fid:int`, `op:int`, `src:cm_expr`,
      `ty:cm_type`, `st:cm_src_state`, `ks:(cm_frame)list`,
      `ann:cm_annotation`);
  thm two = ispecl_rule(variables, cm_r_unary_two_layout_step);
  thm three = ispecl_rule(variables, cm_r_unary_three_layout_step);
  thm other = ispecl_rule(variables, cm_r_unary_other_layout_step);
  term layout =
      `cm_task_layout (p:cm_program)
         (CMRTask p (fid:int)
           (CMUnaryE (op:int) (src:cm_expr) (ty:cm_type))
           (st:cm_src_state) (ks:(cm_frame)list))
         (ann:cm_annotation)`;
  term result =
      `cm_task_layout (p:cm_program)
         (cm_step
           (CMRTask p (fid:int)
             (CMUnaryE (op:int) (src:cm_expr) (ty:cm_type))
             (st:cm_src_state) (ks:(cm_frame)list)))
         (cm_update_annotation
           (cm_annotation_step
             (CMRTask p fid (CMUnaryE op src ty) st ks) ann))`;
  thm cases = taut_rule(mk_imp(concl(two),
      mk_imp(concl(three),
        mk_imp(concl(other), mk_imp(layout, result)))));
  return genl_rule(variables,
      mp_rule(mp_rule(mp_rule(cases, two), three), other));
}
PROOF thm cm_r_unary_layout_step =
    cm_prove_r_unary_layout_step();

PROOF thm cm_r_index_layout_step =
    cm_prove_r_structural_layout_step(
      `!(p:cm_program) (fid:int) (base:cm_expr) (index:cm_expr)
         (ty:cm_type) (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         cm_task_layout p
           (CMRTask p fid (CMIndexE base index ty) st ks) ann ==>
         cm_task_layout p
           (cm_step (CMRTask p fid (CMIndexE base index ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask p fid (CMIndexE base index ty) st ks) ann))`,
      `CMIndexE (base:cm_expr) (index:cm_expr) (ty:cm_type)`,
      THM_LIST());

PROOF static thm cm_r_array_member_layout_step =
    cm_prove_r_structural_layout_step(
      `!(p:cm_program) (fid:int) (base:cm_expr) (mid:int)
         (ty:cm_type) (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         cm_member_array p (cm_expr_type base) mid ==>
         cm_task_layout p
           (CMRTask p fid (CMMemberE base mid ty) st ks) ann ==>
         cm_task_layout p
           (cm_step (CMRTask p fid (CMMemberE base mid ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask p fid (CMMemberE base mid ty) st ks) ann))`,
      `CMMemberE (base:cm_expr) (mid:int) (ty:cm_type)`,
      THM_LIST(assume_rule(
        `cm_member_array (p:cm_program)
          (cm_expr_type (base:cm_expr)) (mid:int)`)));

PROOF static thm cm_r_scalar_member_layout_step =
    cm_prove_r_structural_layout_step(
      `!(p:cm_program) (fid:int) (base:cm_expr) (mid:int)
         (ty:cm_type) (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         ~cm_member_array p (cm_expr_type base) mid ==>
         cm_task_layout p
           (CMRTask p fid (CMMemberE base mid ty) st ks) ann ==>
         cm_task_layout p
           (cm_step (CMRTask p fid (CMMemberE base mid ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask p fid (CMMemberE base mid ty) st ks) ann))`,
      `CMMemberE (base:cm_expr) (mid:int) (ty:cm_type)`,
      THM_LIST(assume_rule(
        `~cm_member_array (p:cm_program)
          (cm_expr_type (base:cm_expr)) (mid:int)`)));

PROOF static thm cm_prove_r_member_layout_step(void) {
  term_list variables = TERM_LIST(
      `p:cm_program`, `fid:int`, `base:cm_expr`, `mid:int`,
      `ty:cm_type`, `st:cm_src_state`, `ks:(cm_frame)list`,
      `ann:cm_annotation`);
  thm array = ispecl_rule(
      variables, cm_r_array_member_layout_step);
  thm scalar = ispecl_rule(
      variables, cm_r_scalar_member_layout_step);
  term layout =
      `cm_task_layout (p:cm_program)
         (CMRTask p (fid:int)
           (CMMemberE (base:cm_expr) (mid:int) (ty:cm_type))
           (st:cm_src_state) (ks:(cm_frame)list))
         (ann:cm_annotation)`;
  term result =
      `cm_task_layout (p:cm_program)
         (cm_step
           (CMRTask p (fid:int)
             (CMMemberE (base:cm_expr) (mid:int) (ty:cm_type))
             (st:cm_src_state) (ks:(cm_frame)list)))
         (cm_update_annotation
           (cm_annotation_step
             (CMRTask p fid (CMMemberE base mid ty) st ks) ann))`;
  thm cases = taut_rule(
      mk_imp(concl(array),
        mk_imp(concl(scalar), mk_imp(layout, result))));
  return genl_rule(variables,
      mp_rule(mp_rule(cases, array), scalar));
}
PROOF thm cm_r_member_layout_step =
    cm_prove_r_member_layout_step();

PROOF thm cm_r_putc_layout_step =
    cm_prove_r_structural_layout_step(
      `!(p:cm_program) (fid:int) (arg:cm_expr) (ty:cm_type)
         (st:cm_src_state) (ks:(cm_frame)list) (ann:cm_annotation).
         cm_task_layout p
           (CMRTask p fid (CMPutcE arg ty) st ks) ann ==>
         cm_task_layout p
           (cm_step (CMRTask p fid (CMPutcE arg ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask p fid (CMPutcE arg ty) st ks) ann))`,
      `CMPutcE (arg:cm_expr) (ty:cm_type)`,
      THM_LIST());

PROOF thm cm_r_puti_layout_step =
    cm_prove_r_structural_layout_step(
      `!(p:cm_program) (fid:int) (arg:cm_expr) (ty:cm_type)
         (st:cm_src_state) (ks:(cm_frame)list) (ann:cm_annotation).
         cm_task_layout p
           (CMRTask p fid (CMPutiE arg ty) st ks) ann ==>
         cm_task_layout p
           (cm_step (CMRTask p fid (CMPutiE arg ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask p fid (CMPutiE arg ty) st ks) ann))`,
      `CMPutiE (arg:cm_expr) (ty:cm_type)`,
      THM_LIST());


PROOF static thm cm_prove_r_exit_layout_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (arg:cm_expr) (ty:cm_type)
         (st:cm_src_state) (ks:(cm_frame)list) (ann:cm_annotation).
         cm_task_layout p
           (CMRTask p fid (CMExitE arg ty) st ks) ann ==>
         cm_task_layout p
           (cm_step (CMRTask p fid (CMExitE arg ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask p fid (CMExitE arg ty) st ks) ann))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm_list rules = cm_layout_expr_rules();
  thm old_layout = assume_rule(
      `cm_task_layout (p:cm_program)
         (CMRTask p (fid:int)
           (CMExitE (arg:cm_expr) (ty:cm_type))
           (st:cm_src_state) (ks:(cm_frame)list))
         (ann:cm_annotation)`);
  thm old_open =
      conv_rule(reduce_rewrite_conv(rules), old_layout);
  thm old_code = conjunct1_rule(old_open);
  thm old_sites = conjunct2_rule(old_open);
  thm prefix_rule = ispecl_rule(TERM_LIST(
      `cm_model_code (p:cm_program)`,
      `cm_ann_pc (ann:cm_annotation)`,
      `cm_rcode_of
         (cm_emit_expr_pair p (fid:int) (cm_ann_pc ann)
           (cm_ann_temp ann) (arg:cm_expr)) ++
       cm_char_normalize_code CMCharTy ++
       [TVMInst TVMHaltOp 0i]`,
      `cm_cont_code p fid
         (cm_ann_pc ann +
          cm_rcount_of (cm_expr_code_counts p fid arg) + 7i)
         (cm_ann_temp ann) (cm_ann_cursors ann)`),
      cm_code_at_append_left);
  thm prefix = mp_rule(
      conv_rule(reduce_rewrite_conv(rules), prefix_rule),
      old_code);
  gnode reduced =
      CONV_TAC(leaf, reduce_rewrite_conv(rules));
  ACCEPT_TAC(reduced, conj_rule(prefix, old_sites));
  return gnode_prove(root);
}
PROOF thm cm_r_exit_layout_step =
    cm_prove_r_exit_layout_step();
PROOF thm cm_r_call_cons_layout_step =
    cm_prove_r_structural_layout_step(
      `!(p:cm_program) (fid:int) (callee:int) (arg:cm_expr)
         (args:(cm_expr)list) (ty:cm_type) (st:cm_src_state)
         (ks:(cm_frame)list) (ann:cm_annotation).
         cm_task_layout p
           (CMRTask p fid (CMCallE callee (arg :: args) ty) st ks) ann ==>
         cm_task_layout p
           (cm_step
             (CMRTask p fid (CMCallE callee (arg :: args) ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask p fid (CMCallE callee (arg :: args) ty) st ks)
               ann))`,
      `CMCallE (callee:int)
         ((arg:cm_expr) :: (args:(cm_expr)list)) (ty:cm_type)`,
      THM_LIST(cm_layout_call_cons_length));

PROOF static thm cm_prove_r_call_nil_layout_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (callee:int) (ty:cm_type)
         (st:cm_src_state) (ks:(cm_frame)list) (ann:cm_annotation).
         cm_call_ok p callee [] st ==>
         cm_call_depth ks < 65536i ==>
         cm_call_depth
           (cm_cursor_frames (cm_ann_cursors ann)) < 65536i ==>
         cm_task_layout p
           (CMRTask p fid (CMCallE callee [] ty) st ks) ann ==>
         cm_task_layout p
           (cm_step (CMRTask p fid (CMCallE callee [] ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask p fid (CMCallE callee [] ty) st ks) ann))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm call_ok = assume_rule(
      `cm_call_ok (p:cm_program) (callee:int)
         ([]:(cm_value)list) (st:cm_src_state)`);
  thm source_depth = assume_rule(
      `cm_call_depth (ks:(cm_frame)list) < 65536i`);
  thm cursor_depth = assume_rule(
      `cm_call_depth
         (cm_cursor_frames
           (cm_ann_cursors (ann:cm_annotation))) < 65536i`);
  thm_list rules = cm_layout_expr_rules();
  vector_add(&rules, call_ok);
  vector_add(&rules, source_depth);
  vector_add(&rules, cursor_depth);
  vector_add(&rules, get_cm_begin_call_def());
  vector_add(&rules, cm_call_body_pc_def);
  vector_add(&rules, cm_ann_enter_call_def);
  vector_add(&rules, cm_fallthrough_tail_code_def);
  vector_add(&rules, cm_ann_spills_def);
  vector_add(&rules, cm_ann_saved_def);
  vector_add(&rules, cm_call_sim_base_def);
  vector_add(&rules, cm_call_sim_saved_def);
  vector_add(&rules, cm_call_sim_return_def);

  thm old_layout = assume_rule(
      `cm_task_layout (p:cm_program)
         (CMRTask p (fid:int)
           (CMCallE (callee:int) ([]:(cm_expr)list) (ty:cm_type))
           (st:cm_src_state) (ks:(cm_frame)list))
         (ann:cm_annotation)`);
  thm old_open =
      conv_rule(reduce_rewrite_conv(rules), old_layout);
  thm old_code = conjunct1_rule(old_open);
  thm old_sites = conjunct2_rule(old_open);
  thm return_rule = ispecl_rule(TERM_LIST(
      `cm_model_code (p:cm_program)`,
      `cm_ann_pc (ann:cm_annotation)`,
      `[TVMInst TVMCallOp
          (cm_function_pc (p:cm_program) (callee:int))]`,
      `cm_cont_code (p:cm_program) (fid:int)
         (cm_ann_pc (ann:cm_annotation) + 1i)
         (cm_ann_temp ann) (cm_ann_cursors ann)`),
      cm_code_at_append_right);
  thm return_at = mp_rule(
      conv_rule(reduce_rewrite_conv(rules), return_rule),
      old_code);

  thm opened_ok = conv_rule(
      reduce_rewrite_conv(THM_LIST(get_cm_call_ok_def())),
      call_ok);
  thm bounds = conj_rule(
      conjunct1_rule(opened_ok),
      conjunct1_rule(conjunct2_rule(opened_ok)));
  thm body_at = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `callee:int`),
      cm_model_function_body_tail_at), bounds);
  thm body_normalized =
      conv_rule(reduce_rewrite_conv(rules), body_at);

  gnode reduced =
      CONV_TAC(leaf, reduce_rewrite_conv(rules));
  thm result =
      conj_rule(body_normalized,
        conj_rule(return_at, old_sites));
  ACCEPT_TAC(reduced, result);
  return gnode_prove(root);
}
PROOF thm cm_r_call_nil_layout_step =
    cm_prove_r_call_nil_layout_step();
PROOF static thm cm_prove_r_call_nonempty_layout_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (callee:int)
         (args:(cm_expr)list) (ty:cm_type)
         (st:cm_src_state) (ks:(cm_frame)list) (ann:cm_annotation).
         ~(args == []) ==>
         cm_task_layout p
           (CMRTask p fid (CMCallE callee args ty) st ks) ann ==>
         cm_task_layout p
           (cm_step
             (CMRTask p fid (CMCallE callee args ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask p fid (CMCallE callee args ty) st ks) ann))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(leaf,
      ispec_rule(`args:(cm_expr)list`,
        get_theorem_by_name("list_CASES")), "Hshape");
  CONTR_TAC(cases[0], contra(
      assume_rule(
        `~((args:(cm_expr)list) == ([]:(cm_expr)list))`),
      assume_rule(
        `(args:(cm_expr)list) == ([]:(cm_expr)list)`)));
  gnode cons = ASMP_EXISTS_TAC(cases[1], "Hshape", "arg");
  cons = ASMP_EXISTS_TAC(cons, "Hshape", "rest");
  gnode shaped = CONV_WITH_ASMP_TAC(
      cons, reduce_rewrite_conv, THM_LIST());
  thm step = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `callee:int`, `arg:cm_expr`,
      `rest:(cm_expr)list`, `ty:cm_type`, `st:cm_src_state`,
      `ks:(cm_frame)list`, `ann:cm_annotation`),
      cm_r_call_cons_layout_step);
  thm shape = assume_rule(
      `(args:(cm_expr)list) ==
         ((arg:cm_expr) :: (rest:(cm_expr)list))`);
  thm layout = conv_rule(rewrite_conv(THM_LIST(shape)),
      assume_rule(
        `cm_task_layout (p:cm_program)
           (CMRTask p (fid:int)
             (CMCallE (callee:int) (args:(cm_expr)list)
               (ty:cm_type))
             (st:cm_src_state) (ks:(cm_frame)list))
           (ann:cm_annotation)`));
  ACCEPT_TAC(shaped, mp_rule(step, layout));
  return gnode_prove(root);
}
PROOF thm cm_r_call_nonempty_layout_step =
    cm_prove_r_call_nonempty_layout_step();

PROOF thm cm_r_layout_ready_def = new_fun_definition(
    `cm_r_layout_ready (p:cm_program) (fid:int) (expr:cm_expr)
       (st:cm_src_state) (ks:(cm_frame)list)
       (ann:cm_annotation) : bool =
       ((!callee ty.
           expr == CMCallE (callee:int) [] (ty:cm_type) ==>
           cm_call_ok p callee [] st &&
           cm_call_depth ks < 65536i &&
           cm_call_depth
             (cm_cursor_frames (cm_ann_cursors ann)) < 65536i) &&
        (!ty.
           expr == CMGetcE (ty:cm_type) ==>
           cm_state_input st == [] ||
           tower_byte_value (HD (cm_state_input st))) &&
        (!scope slot ty.
           expr == CMVarE (scope:int) (slot:int) (ty:cm_type) ==>
           cm_binding_array p fid scope slot ==>
           cm_binding_address_ok p fid scope slot st))`);
PROOF static int _e_cm_r_layout_ready =
    cst_add_const_to_header(`cm_r_layout_ready`);

PROOF static void cm_accept_r_constructor_layout(
    const gnode branch, const thm constructor_step) {
  labeled_term_list assumptions = goal_lasmps(branch->g);
  thm shape = assume_rule(
      assumptions[
        labeled_term_list_index(assumptions, "Hex")].tm);
  thm layout = conv_rule(rewrite_conv(THM_LIST(shape)),
      assume_rule(
        `cm_task_layout (p:cm_program)
           (CMRTask p (fid:int) (expr:cm_expr)
             (st:cm_src_state) (ks:(cm_frame)list))
           (ann:cm_annotation)`));
  thm result = match_mp_rule(constructor_step, layout);
  gnode shaped =
      CONV_TAC(branch, rewrite_conv(THM_LIST(shape)));
  ACCEPT_TAC(shaped, result);
}

PROOF static thm cm_prove_r_task_layout_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (expr:cm_expr)
         (st:cm_src_state) (ks:(cm_frame)list) (ann:cm_annotation).
         cm_r_layout_ready p fid expr st ks ann ==>
         cm_task_layout p
           (CMRTask p fid expr st ks) ann ==>
         cm_task_layout p
           (cm_step (CMRTask p fid expr st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask p fid expr st ks) ann))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm cases_th =
      ispec_rule(`expr:cm_expr`, get_cm_expr_cases());
  gnode_list cases =
      DISJ_CASES_TAC(introduced, cases_th, "Hex");
  thm constructor_steps[14] = {
    cm_r_const_layout_step,
    cm_r_string_layout_step,
    cm_r_var_layout_step,
    cm_r_assign_layout_step,
    cm_r_binary_layout_step,
    cm_r_unary_layout_step,
    cm_r_index_layout_step,
    cm_r_member_layout_step,
    empty_theorem,
    cm_r_sizeof_layout_step,
    cm_r_getc_layout_step,
    cm_r_putc_layout_step,
    cm_r_puti_layout_step,
    cm_r_exit_layout_step
  };
  for (size_t i = 0; i < vector_size(cases); ++i) {
    while (true) {
      labeled_term_list assumptions = goal_lasmps(cases[i]->g);
      int index =
          labeled_term_list_index(assumptions, "Hex");
      if (!is_exists(assumptions[index].tm)) break;
      cases[i] =
          ASMP_EXISTS_TAC(cases[i], "Hex", NULL);
    }
    if (i == 2 || i == 10) {
      labeled_term_list special_assumptions = goal_lasmps(cases[i]->g);
      thm expr_shape = assume_rule(
          special_assumptions[labeled_term_list_index(
            special_assumptions, "Hex")].tm);
      thm ready_open = conv_rule(
          rewrite_conv(THM_LIST(cm_r_layout_ready_def)),
          assume_rule(
            `cm_r_layout_ready (p:cm_program) (fid:int)
              (expr:cm_expr) (st:cm_src_state) (ks:(cm_frame)list)
              (ann:cm_annotation)`));
      thm condition = i == 2
          ? match_mp_rule(specl_rule(TERM_LIST(
              `a0:int`, `a1:int`, `a2:cm_type`),
              conjunct2_rule(conjunct2_rule(ready_open))), expr_shape)
          : match_mp_rule(spec_rule(`a:cm_type`,
              conjunct1_rule(conjunct2_rule(ready_open))), expr_shape);
      thm shaped_layout = conv_rule(rewrite_conv(THM_LIST(expr_shape)),
          assume_rule(
            `cm_task_layout (p:cm_program)
              (CMRTask p (fid:int) (expr:cm_expr)
                (st:cm_src_state) (ks:(cm_frame)list))
              (ann:cm_annotation)`));
      thm special_result =
          match_mp_rule(constructor_steps[i], condition);
      special_result = match_mp_rule(special_result, shaped_layout);
      gnode shaped = CONV_TAC(
          cases[i], rewrite_conv(THM_LIST(expr_shape)));
      ACCEPT_TAC(shaped, special_result);
      continue;
    }
    if (i != 8) {
      cm_accept_r_constructor_layout(
          cases[i], constructor_steps[i]);
      continue;
    }

    gnode_list args_cases = BOOL_CASES_TAC(
        cases[i],
        `(a1:(cm_expr)list) == ([]:(cm_expr)list)`,
        "Hargs");
    labeled_term_list nil_assumptions =
        goal_lasmps(args_cases[0]->g);
    thm expr_shape = assume_rule(
        nil_assumptions[
          labeled_term_list_index(
            nil_assumptions, "Hex")].tm);
    thm args_nil = assume_rule(
        nil_assumptions[
          labeled_term_list_index(
            nil_assumptions, "Hargs")].tm);
    thm call_nil_shape = conv_rule(
        rewrite_conv(THM_LIST(args_nil)), expr_shape);
    thm nil_layout = conv_rule(
        rewrite_conv(THM_LIST(call_nil_shape)),
        assume_rule(
          `cm_task_layout (p:cm_program)
             (CMRTask p (fid:int) (expr:cm_expr)
               (st:cm_src_state) (ks:(cm_frame)list))
             (ann:cm_annotation)`));
    thm ready_open = conjunct1_rule(conv_rule(
        rewrite_conv(THM_LIST(cm_r_layout_ready_def)),
        assume_rule(
          `cm_r_layout_ready (p:cm_program) (fid:int)
             (expr:cm_expr) (st:cm_src_state) (ks:(cm_frame)list)
             (ann:cm_annotation)`)));
    thm nil_conditions = mp_rule(
        specl_rule(TERM_LIST(`a0:int`, `a2:cm_type`),
          ready_open),
        call_nil_shape);
    thm nil_result = match_mp_rule(
        cm_r_call_nil_layout_step,
        conjunct1_rule(nil_conditions));
    nil_result = match_mp_rule(nil_result,
        conjunct1_rule(conjunct2_rule(nil_conditions)));
    nil_result = match_mp_rule(nil_result,
        conjunct2_rule(conjunct2_rule(nil_conditions)));
    nil_result = match_mp_rule(nil_result, nil_layout);
    gnode nil_goal = CONV_TAC(
        args_cases[0],
        rewrite_conv(THM_LIST(call_nil_shape)));
    ACCEPT_TAC(nil_goal, nil_result);

    labeled_term_list cons_assumptions =
        goal_lasmps(args_cases[1]->g);
    thm call_shape = assume_rule(
        cons_assumptions[
          labeled_term_list_index(
            cons_assumptions, "Hex")].tm);
    thm args_nonempty = assume_rule(
        cons_assumptions[
          labeled_term_list_index(
            cons_assumptions, "Hargs")].tm);
    thm call_layout = conv_rule(
        rewrite_conv(THM_LIST(call_shape)),
        assume_rule(
          `cm_task_layout (p:cm_program)
             (CMRTask p (fid:int) (expr:cm_expr)
               (st:cm_src_state) (ks:(cm_frame)list))
             (ann:cm_annotation)`));
    thm call_result = match_mp_rule(
        cm_r_call_nonempty_layout_step, args_nonempty);
    call_result =
        match_mp_rule(call_result, call_layout);
    gnode call_goal = CONV_TAC(
        args_cases[1],
        rewrite_conv(THM_LIST(call_shape)));
    ACCEPT_TAC(call_goal, call_result);
  }
  return gnode_prove(root);
}
PROOF thm cm_r_task_layout_step =
    cm_prove_r_task_layout_step();

PROOF thm get_cm_r_task_layout_step(void) {
  return cm_r_task_layout_step;
}

PROOF static thm cm_prove_l_linear_layout_step(
    const term statement, const term expression, const term prefix,
    const thm condition) {
  gnode root = gnode_new_with_ccl(statement);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm_list rules = cm_layout_expr_rules();
  if (!IS_NULL(condition)) vector_add(&rules, condition);
  term emitted =
      `cm_emit_lvalue (p:cm_program) (fid:int)
         (cm_ann_pc (ann:cm_annotation)) (cm_ann_temp ann)
         ${expression:cm_expr}`;
  term counted =
      `cm_lvalue_code_count (p:cm_program) (fid:int)
         ${expression:cm_expr}`;
  thm emitted_length = ispecl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `cm_ann_pc (ann:cm_annotation)`,
      `cm_ann_temp (ann:cm_annotation)`),
      conjunct1_rule(
        spec_rule(expression, get_cm_expr_code_lengths())));
  thm emitted_eq =
      apply_conversion(reduce_rewrite_conv(rules), emitted);
  thm counted_eq =
      apply_conversion(reduce_rewrite_conv(rules), counted);
  thm prefix_length = trans_rule(
      gsym_rule(beta_norm(ap_term_rule(
        `\code:(tvm_inst)list. ilength code`, emitted_eq))),
      trans_rule(emitted_length, counted_eq));
  vector_add(&rules, prefix_length);
  thm old_layout = assume_rule(
      `cm_task_layout (p:cm_program)
         (CMLTask p (fid:int) ${expression:cm_expr}
           (st:cm_src_state) (ks:(cm_frame)list))
         (ann:cm_annotation)`);
  thm old_open =
      conv_rule(reduce_rewrite_conv(rules), old_layout);
  thm old_code = conjunct1_rule(old_open);
  thm old_sites = conjunct2_rule(old_open);
  thm suffix_rule = ispecl_rule(TERM_LIST(
      `cm_model_code (p:cm_program)`,
      `cm_ann_pc (ann:cm_annotation)`,
      prefix,
      `cm_cont_code (p:cm_program) (fid:int)
         (cm_ann_pc (ann:cm_annotation) +
          ilength ${prefix:(tvm_inst)list})
         (cm_ann_temp ann) (cm_ann_cursors ann)`),
      cm_code_at_append_right);
  thm suffix = mp_rule(
      conv_rule(reduce_rewrite_conv(rules), suffix_rule),
      old_code);
  gnode opened =
      CONV_TAC(leaf, reduce_rewrite_conv(rules));
  ACCEPT_TAC(opened, conj_rule(suffix, old_sites));
  return gnode_prove(root);
}

PROOF static thm cm_prove_l_structural_layout_step(
    const term statement, const term expression,
    const thm_list extra_rules) {
  gnode root = gnode_new_with_ccl(statement);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm_list rules = cm_layout_expr_rules();
  for (size_t i = 0; i < vector_size(extra_rules); ++i) {
    vector_add(&rules, extra_rules[i]);
  }
  thm old_layout = assume_rule(
      `cm_task_layout (p:cm_program)
         (CMLTask p (fid:int) ${expression:cm_expr}
           (st:cm_src_state) (ks:(cm_frame)list))
         (ann:cm_annotation)`);
  thm normalized =
      conv_rule(reduce_rewrite_conv(rules), old_layout);
  gnode reduced =
      CONV_TAC(leaf, reduce_rewrite_conv(rules));
  if (vector_size(extra_rules) > 0) {
    normalized =
        conv_rule(rewrite_conv(extra_rules), normalized);
    reduced =
        CONV_TAC(reduced, rewrite_conv(extra_rules));
  }
  ACCEPT_TAC(reduced, normalized);
  return gnode_prove(root);
}

PROOF static thm cm_l_var_layout_step =
    cm_prove_l_linear_layout_step(
      `!(p:cm_program) (fid:int) (scope:int) (slot:int) (ty:cm_type)
         (st:cm_src_state) (ks:(cm_frame)list) (ann:cm_annotation).
         cm_binding_address_ok p fid scope slot st ==>
         cm_task_layout p
           (CMLTask p fid (CMVarE scope slot ty) st ks) ann ==>
         cm_task_layout p
           (cm_step (CMLTask p fid (CMVarE scope slot ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMLTask p fid (CMVarE scope slot ty) st ks) ann))`,
      `CMVarE (scope:int) (slot:int) (ty:cm_type)`,
      `cm_binding_address_code
         (p:cm_program) (fid:int) (scope:int) (slot:int)`,
      assume_rule(
        `cm_binding_address_ok (p:cm_program) (fid:int)
          (scope:int) (slot:int) (st:cm_src_state)`));

PROOF static thm cm_l_unary_layout_step =
    cm_prove_l_structural_layout_step(
      `!(p:cm_program) (fid:int) (op:int) (arg:cm_expr)
         (ty:cm_type) (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         op == 2i ==>
         cm_task_layout p
           (CMLTask p fid (CMUnaryE op arg ty) st ks) ann ==>
         cm_task_layout p
           (cm_step (CMLTask p fid (CMUnaryE op arg ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMLTask p fid (CMUnaryE op arg ty) st ks) ann))`,
      `CMUnaryE (op:int) (arg:cm_expr) (ty:cm_type)`,
      THM_LIST(assume_rule(`(op:int) == 2i`)));

PROOF static thm cm_l_index_layout_step =
    cm_prove_l_structural_layout_step(
      `!(p:cm_program) (fid:int) (base:cm_expr) (index:cm_expr)
         (ty:cm_type) (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         cm_task_layout p
           (CMLTask p fid (CMIndexE base index ty) st ks) ann ==>
         cm_task_layout p
           (cm_step (CMLTask p fid (CMIndexE base index ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMLTask p fid (CMIndexE base index ty) st ks) ann))`,
      `CMIndexE (base:cm_expr) (index:cm_expr) (ty:cm_type)`,
      THM_LIST(int_ring_rule(
        `(a:int) + (b:int) + 5i + (c:int) + 8i ==
         a + b + c + 13i`)));

PROOF static thm cm_l_member_layout_step =
    cm_prove_l_structural_layout_step(
      `!(p:cm_program) (fid:int) (base:cm_expr) (mid:int)
         (ty:cm_type) (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         cm_task_layout p
           (CMLTask p fid (CMMemberE base mid ty) st ks) ann ==>
         cm_task_layout p
           (cm_step (CMLTask p fid (CMMemberE base mid ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMLTask p fid (CMMemberE base mid ty) st ks) ann))`,
      `CMMemberE (base:cm_expr) (mid:int) (ty:cm_type)`,
      THM_LIST());

PROOF static void cm_accept_l_constructor_layout(
    const gnode branch, const thm constructor_step) {
  labeled_term_list assumptions = goal_lasmps(branch->g);
  thm shape = assume_rule(
      assumptions[
        labeled_term_list_index(assumptions, "Hex")].tm);
  thm layout = conv_rule(rewrite_conv(THM_LIST(shape)),
      assume_rule(
        `cm_task_layout (p:cm_program)
           (CMLTask p (fid:int) (expr:cm_expr)
             (st:cm_src_state) (ks:(cm_frame)list))
           (ann:cm_annotation)`));
  thm result = match_mp_rule(constructor_step, layout);
  gnode shaped =
      CONV_TAC(branch, rewrite_conv(THM_LIST(shape)));
  ACCEPT_TAC(shaped, result);
}

PROOF thm cm_l_layout_ready_def = new_fun_definition(
    `cm_l_layout_ready (p:cm_program) (fid:int) (expr:cm_expr)
       (st:cm_src_state) : bool =
       (cm_lvalue expr &&
        (!scope slot ty.
           expr == CMVarE (scope:int) (slot:int) (ty:cm_type) ==>
           cm_binding_address_ok p fid scope slot st))`);
PROOF static int _e_cm_l_layout_ready =
    cst_add_const_to_header(`cm_l_layout_ready`);

PROOF static thm cm_prove_l_task_layout_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (expr:cm_expr)
         (st:cm_src_state) (ks:(cm_frame)list) (ann:cm_annotation).
         cm_l_layout_ready p fid expr st ==>
         cm_task_layout p
           (CMLTask p fid expr st ks) ann ==>
         cm_task_layout p
           (cm_step (CMLTask p fid expr st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMLTask p fid expr st ks) ann))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(
      introduced,
      ispec_rule(`expr:cm_expr`, get_cm_expr_cases()),
      "Hex");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    while (true) {
      labeled_term_list assumptions = goal_lasmps(cases[i]->g);
      int index =
          labeled_term_list_index(assumptions, "Hex");
      if (!is_exists(assumptions[index].tm)) break;
      cases[i] =
          ASMP_EXISTS_TAC(cases[i], "Hex", NULL);
    }
    if (i == 2) {
      labeled_term_list var_assumptions = goal_lasmps(cases[i]->g);
      thm shape = assume_rule(
          var_assumptions[labeled_term_list_index(
            var_assumptions, "Hex")].tm);
      thm ready_open = conv_rule(
          rewrite_conv(THM_LIST(cm_l_layout_ready_def)),
          assume_rule(
            `cm_l_layout_ready (p:cm_program) (fid:int)
              (expr:cm_expr) (st:cm_src_state)`));
      thm address_ok = match_mp_rule(specl_rule(TERM_LIST(
          `a0:int`, `a1:int`, `a2:cm_type`),
          conjunct2_rule(ready_open)), shape);
      thm layout = conv_rule(rewrite_conv(THM_LIST(shape)),
          assume_rule(
            `cm_task_layout (p:cm_program)
              (CMLTask p (fid:int) (expr:cm_expr)
                (st:cm_src_state) (ks:(cm_frame)list))
              (ann:cm_annotation)`));
      thm result = match_mp_rule(cm_l_var_layout_step, address_ok);
      result = match_mp_rule(result, layout);
      gnode shaped =
          CONV_TAC(cases[i], rewrite_conv(THM_LIST(shape)));
      ACCEPT_TAC(shaped, result);
      continue;
    }
    if (i == 6) {
      cm_accept_l_constructor_layout(
          cases[i], cm_l_index_layout_step);
      continue;
    }
    if (i == 7) {
      cm_accept_l_constructor_layout(
          cases[i], cm_l_member_layout_step);
      continue;
    }
    labeled_term_list assumptions = goal_lasmps(cases[i]->g);
    thm shape = assume_rule(
        assumptions[
          labeled_term_list_index(assumptions, "Hex")].tm);
    thm ready_open = conv_rule(
        rewrite_conv(THM_LIST(cm_l_layout_ready_def)),
        assume_rule(
          `cm_l_layout_ready (p:cm_program) (fid:int)
            (expr:cm_expr) (st:cm_src_state)`));
    thm shaped_lvalue = conv_rule(
        rewrite_conv(THM_LIST(shape)), conjunct1_rule(ready_open));
    if (i == 5) {
      thm op_two = conv_rule(
          reduce_rewrite_conv(
            THM_LIST(get_cm_lvalue_def())),
          shaped_lvalue);
      thm layout = conv_rule(
          rewrite_conv(THM_LIST(shape)),
          assume_rule(
            `cm_task_layout (p:cm_program)
               (CMLTask p (fid:int) (expr:cm_expr)
                 (st:cm_src_state) (ks:(cm_frame)list))
               (ann:cm_annotation)`));
      thm result = match_mp_rule(
          cm_l_unary_layout_step, op_two);
      result = match_mp_rule(result, layout);
      gnode shaped =
          CONV_TAC(cases[i], rewrite_conv(THM_LIST(shape)));
      ACCEPT_TAC(shaped, result);
      continue;
    }
    thm impossible = conv_rule(
        reduce_rewrite_conv(THM_LIST(get_cm_lvalue_def())),
        shaped_lvalue);
    CONTR_TAC(cases[i], impossible);
  }
  return gnode_prove(root);
}
PROOF thm cm_l_task_layout_step =
    cm_prove_l_task_layout_step();

PROOF thm get_cm_l_task_layout_step(void) {
  return cm_l_task_layout_step;
}

PROOF thm get_cm_layout_char_normalize_length(void) {
  return cm_layout_char_normalize_length;
}
PROOF thm get_cm_layout_rcode_length(void) {
  return cm_layout_rcode_length;
}
PROOF thm get_cm_layout_load_length(void) {
  return cm_layout_load_length;
}
PROOF thm get_cm_layout_store_length(void) {
  return cm_layout_store_length;
}
PROOF thm get_cm_layout_temp_store_length(void) {
  return cm_layout_temp_store_length;
}
PROOF thm get_cm_layout_temp_load_length(void) {
  return cm_layout_temp_load_length;
}
PROOF thm get_cm_layout_assign_tail_length(void) {
  return cm_layout_assign_tail_length;
}
PROOF thm get_cm_layout_index_tail_length(void) {
  return cm_layout_index_tail_length;
}
PROOF thm get_cm_layout_member_tail_length(void) {
  return cm_layout_member_tail_length;
}
PROOF thm get_cm_layout_binary_finish_length(void) {
  return cm_layout_binary_finish_length;
}
PROOF thm get_cm_layout_binary_phase_length(void) {
  return cm_layout_binary_phase_length;
}


PROOF static int cmc_preservation_code_expr_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_code_expr_axioms_before,
      "cmc_preservation_code_expr introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_code_expr_checks =
    cmc_preservation_code_expr_final_checks();
