#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_target_value_args.h"
#include "cmc_preservation_target_spill.h"
#include "cmc_preservation_invariant_runtime.h"
#include "cmc_preservation_spill_semantic.h"
#include "cmc_preservation_code_expr.h"

#require "cmc_preservation_target_value_arg.c"
#require "cmc_preservation_spill_safety.c"
#require "cmc_preservation_spill_semantic.c"
#require "cmc_preservation_invariant_runtime.c"

PROOF static size_t _cmc_preservation_target_value_args_axioms_before =
    vector_size(get_all_axioms());

PROOF thm cm_forward_spills_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!base spills.
        cm_forward_spills (base:int) ([]:(cm_value)list)
          (spills:(cm_spill)list) = T) &&
     (!base value rest spills.
        cm_forward_spills (base:int)
          ((value:cm_value) :: (rest:(cm_value)list))
          (spills:(cm_spill)list) =
        (cm_spill_holds base value spills &&
         cm_forward_spills (base + 1i) rest spills))`);

PROOF static thm cm_prove_staged_spills_append(void) {
  gnode root = gnode_new_with_ccl(
      `!(left:(cm_value)list).
         !(base:int) (right:(cm_value)list)
           (spills:(cm_spill)list).
           cm_staged_spills base (left ++ right) spills <=>
           cm_staged_spills (base + ilength right) left spills &&
           cm_staged_spills base right spills`);
  gnode_list cases = INDUCT_TAC(
      root, `left:(cm_value)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        cm_staged_spills_def, get_theorem_by_name("APPEND"),
        get_theorem_by_name("ILENGTH_DEF"))));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm ih = specl_rule(TERM_LIST(
        `base:int`, `right:(cm_value)list`,
        `spills:(cm_spill)list`),
        assume_rule(goal_lasmps(leaf->g)[0].tm));
    thm_list rules = THM_LIST(
        cm_staged_spills_def, get_theorem_by_name("APPEND"),
        get_theorem_by_name("ILENGTH_APPEND"),
        get_theorem_by_name("ILENGTH_DEF"), ih);
    gnode reduced = CONV_WITH_ASMP_TAC(
        leaf, reduce_rewrite_conv, rules);
    thm address_order = int_ring_rule(
        `(base:int) + ilength (a1:(cm_value)list) +
           ilength (right:(cm_value)list) ==
         (base + ilength right) + ilength a1`);
    gnode ordered = CONV_WITH_ASMP_TAC(
        reduced, once_rewrite_conv, THM_LIST(address_order));
    if (IS_NULL(ordered->solved)) {
      ACCEPT_TAC(ordered, taut_rule(goal_ccl(ordered->g)));
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_staged_spills_append =
    cm_prove_staged_spills_append();

PROOF static thm cm_prove_staged_reverse_spills(void) {
  gnode root = gnode_new_with_ccl(
      `!(values:(cm_value)list).
         !(base:int) (spills:(cm_spill)list).
           cm_staged_spills base (REVERSE values) spills <=>
           cm_forward_spills base values spills`);
  gnode_list cases = INDUCT_TAC(
      root, `values:(cm_value)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        cm_staged_spills_def, cm_forward_spills_def,
        get_theorem_by_name("REVERSE"))));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm ih = specl_rule(TERM_LIST(
        `(base:int) + 1i`, `spills:(cm_spill)list`),
        assume_rule(goal_lasmps(leaf->g)[0].tm));
    thm append = specl_rule(TERM_LIST(
        `REVERSE (a1:(cm_value)list)`, `base:int`,
        `[a0:cm_value]:(cm_value)list`,
        `spills:(cm_spill)list`), cm_staged_spills_append);
    thm_list rules = THM_LIST(
        cm_forward_spills_def, get_theorem_by_name("REVERSE"),
        get_theorem_by_name("ILENGTH_DEF"),
        cm_staged_spills_def, append, ih,
        int_ring_rule(`(base:int) + 0i == base`),
        int_ring_rule(`(base:int) + 1i == base + 1i`));
    gnode reduced = CONV_WITH_ASMP_TAC(
        leaf, reduce_rewrite_conv, rules);
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_staged_reverse_spills =
    cm_prove_staged_reverse_spills();


PROOF static thm cm_value_reload_code_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p fid base.
        cm_value_reload_code (p:cm_program) (fid:int) (base:int)
          ([]:(cm_value)list) = []) &&
     (!p fid base value rest.
        cm_value_reload_code (p:cm_program) (fid:int) (base:int)
          ((value:cm_value) :: (rest:(cm_value)list)) =
        cm_temp_load_code p fid base ++
        cm_value_reload_code p fid (base + 1i) rest)`);

PROOF static thm cm_prove_code_steps_append(void) {
  gnode root = gnode_new_with_ccl(
      `!(left:(tvm_inst)list) (right:(tvm_inst)list).
         cm_code_steps (left ++ right) ==
         cm_code_steps left + cm_code_steps right`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm left_nonneg = ispec_rule(
      `left:(tvm_inst)list`, get_theorem_by_name("ILENGTH_NONNEG"));
  thm right_nonneg = ispec_rule(
      `right:(tvm_inst)list`, get_theorem_by_name("ILENGTH_NONNEG"));
  thm add = mp_rule(
      specl_rule(TERM_LIST(`ilength (left:(tvm_inst)list)`,
          `ilength (right:(tvm_inst)list)`),
          get_theorem_by_name("NUM_OF_INT_ADD")),
      conj_rule(left_nonneg, right_nonneg));
  CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      cm_code_steps_def, get_theorem_by_name("ILENGTH_APPEND"), add)));
  return gnode_prove(root);
}
PROOF static thm cm_code_steps_append =
    cm_prove_code_steps_append();

PROOF static thm cm_prove_ann_linear_append(void) {
  gnode root = gnode_new_with_ccl(
      `!(left:(tvm_inst)list) (right:(tvm_inst)list)
         (ann:cm_annotation).
         cm_ann_linear (left ++ right) ann ==
         cm_ann_linear right (cm_ann_linear left ann)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode reduced = CONV_WITH_ASMP_TAC(
      leaf, reduce_rewrite_conv, THM_LIST(
        cm_ann_linear_def, cm_ann_plain_def,
        cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
        cm_ann_continue_def, cm_ann_cursors_def,
        cm_ann_spills_def, cm_ann_saved_def, cm_ann_calls_def,
        get_theorem_by_name("ILENGTH_APPEND")));
  thm pc_order = int_ring_rule(
      `(cm_ann_pc (ann:cm_annotation) +
          (ilength (left:(tvm_inst)list) + ilength (right:(tvm_inst)list))) ==
       (cm_ann_pc ann + ilength left) + ilength right`);
  gnode ordered = CONV_WITH_ASMP_TAC(
      reduced, once_rewrite_conv, THM_LIST(pc_order));
  if (IS_NULL(ordered->solved)) {
    ACCEPT_TAC(ordered, refl_rule(dest_eq(goal_ccl(ordered->g)).tm1));
  }
  return gnode_prove(root);
}
PROOF static thm cm_ann_linear_append =
    cm_prove_ann_linear_append();

PROOF static thm cm_prove_emit_args_reload_values(void) {
  gnode root = gnode_new_with_ccl(
      `!(args:(cm_expr)list).
         !(p:cm_program) (fid:int) (base:int)
           (values:(cm_value)list).
           ilength args == ilength values ==>
           cm_emit_args_reload p fid base args ==
           cm_value_reload_code p fid base values`);
  gnode_list cases = INDUCT_TAC(root, `args:(cm_expr)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    gnode_list value_cases = BOOL_CASES_TAC(
        leaf, `(values:(cm_value)list) == []`, "Hvalues_nil");
    thm value_nil = assume_rule(`(values:(cm_value)list) == []`);
    thm emit_nil = apply_conversion(
        reduce_rewrite_conv(THM_LIST(get_cm_emit_args_reload_def())),
        `cm_emit_args_reload (p:cm_program) (fid:int) (base:int)
           ([]:(cm_expr)list)`);
    thm reload_nil = apply_conversion(
        reduce_rewrite_conv(THM_LIST(cm_value_reload_code_def)),
        `cm_value_reload_code (p:cm_program) (fid:int) (base:int)
           ([]:(cm_value)list)`);
    thm reload_shape = beta_norm(ap_term_rule(
        `\items:(cm_value)list.
           cm_value_reload_code (p:cm_program) (fid:int) (base:int) items`,
        value_nil));
    ACCEPT_TAC(value_cases[0],
        trans_rule(emit_nil,
          trans_rule(sym_rule(reload_nil), sym_rule(reload_shape))));
    {
      gnode nonnil = value_cases[1];
      thm shape = mp_rule(
          ispec_rule(`values:(cm_value)list`,
              get_theorem_by_name("CONS_HD_TL")),
          assume_rule(`~((values:(cm_value)list) == [])`));
      thm shape_len = ap_term_rule(
          `ilength:(cm_value)list->int`, shape);
      thm normalized_len = conv_rule(
          reduce_rewrite_conv(THM_LIST(
            get_theorem_by_name("ILENGTH_DEF"))),
          trans_rule(
            assume_rule(
              `ilength ([]:(cm_expr)list) ==
               ilength (values:(cm_value)list)`),
            shape_len));
      thm tail_nonneg = ispec_rule(
          `TL (values:(cm_value)list)`,
          get_theorem_by_name("ILENGTH_NONNEG"));
      thm impossible = mp_rule(mp_rule(int_arith_rule(
          `0i <= ilength (TL (values:(cm_value)list)) ==>
           0i == 1i + ilength (TL values) ==> F`),
          tail_nonneg), normalized_len);
      CONTR_TAC(nonnil, impossible);
    }
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm ih = assume_rule(goal_lasmps(leaf->g)[0].tm);
    gnode_list value_cases = BOOL_CASES_TAC(
        leaf, `(values:(cm_value)list) == []`, "Hvalues_nil");
    {
      thm nil_len = ap_term_rule(
          `ilength:(cm_value)list->int`,
          assume_rule(`(values:(cm_value)list) == []`));
      thm normalized_len = conv_rule(
          reduce_rewrite_conv(THM_LIST(
            get_theorem_by_name("ILENGTH_DEF"))),
          trans_rule(
            assume_rule(
              `ilength ((a0:cm_expr) :: (a1:(cm_expr)list)) ==
               ilength (values:(cm_value)list)`),
            nil_len));
      thm tail_nonneg = ispec_rule(
          `a1:(cm_expr)list`,
          get_theorem_by_name("ILENGTH_NONNEG"));
      thm impossible = mp_rule(mp_rule(int_arith_rule(
          `0i <= ilength (a1:(cm_expr)list) ==>
           1i + ilength a1 == 0i ==> F`),
          tail_nonneg), normalized_len);
      CONTR_TAC(value_cases[0], impossible);
    }
    {
      gnode nonnil = value_cases[1];
      thm shape = mp_rule(
          ispec_rule(`values:(cm_value)list`,
              get_theorem_by_name("CONS_HD_TL")),
          assume_rule(`~((values:(cm_value)list) == [])`));
      thm shape_len = ap_term_rule(
          `ilength:(cm_value)list->int`, shape);
      thm normalized_len = conv_rule(
          reduce_rewrite_conv(THM_LIST(
            get_theorem_by_name("ILENGTH_DEF"))),
          trans_rule(
            assume_rule(
              `ilength ((a0:cm_expr) :: (a1:(cm_expr)list)) ==
               ilength (values:(cm_value)list)`),
            shape_len));
      thm tail_len = mp_rule(int_arith_rule(
          `1i + ilength (a1:(cm_expr)list) ==
             1i + ilength (TL (values:(cm_value)list)) ==>
           ilength a1 == ilength (TL values)`),
          normalized_len);
      thm tail_code = mp_rule(
          specl_rule(TERM_LIST(`p:cm_program`, `fid:int`,
              `(base:int) + 1i`, `TL (values:(cm_value)list)`), ih),
          tail_len);
      thm emit_step = apply_conversion(
          reduce_rewrite_conv(THM_LIST(get_cm_emit_args_reload_def())),
          `cm_emit_args_reload (p:cm_program) (fid:int) (base:int)
             ((a0:cm_expr) :: (a1:(cm_expr)list))`);
      thm tail_lift = beta_norm(ap_term_rule(
          `\remaining_code:(tvm_inst)list.
             cm_temp_load_code (p:cm_program) (fid:int) (base:int) ++
             remaining_code`,
          tail_code));
      thm reload_step = apply_conversion(
          reduce_rewrite_conv(THM_LIST(cm_value_reload_code_def)),
          `cm_value_reload_code (p:cm_program) (fid:int) (base:int)
             (HD (values:(cm_value)list) :: TL values)`);
      thm reload_shape = beta_norm(ap_term_rule(
          `\items:(cm_value)list.
             cm_value_reload_code (p:cm_program) (fid:int) (base:int)
               items`,
          shape));
      ACCEPT_TAC(nonnil,
          trans_rule(emit_step,
            trans_rule(tail_lift,
              trans_rule(sym_rule(reload_step),
                sym_rule(reload_shape)))));
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_emit_args_reload_values =
    cm_prove_emit_args_reload_values();


PROOF static thm_list cm_target_args_annotation_rules(void) {
  return THM_LIST(
      cm_ann_linear_def, cm_ann_plain_def,
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def,
      cm_ann_spills_def, cm_ann_saved_def, cm_ann_calls_def,
      get_cm_temp_load_code_def(),
      get_theorem_by_name("ILENGTH_DEF"));
}


PROOF static thm cm_prove_ann_linear_nil(void) {
  gnode root = gnode_new_with_ccl(
      `!(ann:cm_annotation).
         cm_ann_linear ([]:(tvm_inst)list) ann == ann`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases =
      CASES_TAC(introduced, `ann:cm_annotation`, "Hann");
  thm ann_case = assume_rule(
      `(ann:cm_annotation) ==
       CMAnnotation (a0:int) (a1:int) (a2:int) (a3:int)
         (a4:(cm_acursor)list) (a5:(cm_spill)list)
         (a6:(cm_spill_frame)list)
         (a7:(cm_call_sim_frame)list)`);
  CONV_WITH_ASMP_TAC(cases[0], reduce_rewrite_conv, THM_LIST(
      ann_case, cm_ann_linear_def, cm_ann_plain_def,
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def,
      cm_ann_spills_def, cm_ann_saved_def, cm_ann_calls_def,
      get_theorem_by_name("ILENGTH_DEF"),
      int_ring_rule(`(pc:int) + 0i == pc`)));
  return gnode_prove(root);
}
PROOF static thm cm_ann_linear_nil =
    cm_prove_ann_linear_nil();
PROOF static thm cm_prove_target_value_reload(void) {
  gnode root = gnode_new_with_ccl(
      `!(spill_values:(cm_value)list).
         !(p:cm_program) (fid:int) (st:cm_src_state)
           (stack_values:(cm_value)list) (base:int)
           (ann:cm_annotation) (target:tvm_task)
           (rest:(tvm_inst)list).
           cm_code_at (cm_model_code p) (cm_ann_pc ann)
             (cm_value_reload_code p fid base spill_values ++ rest) ==>
           cm_running_target_sim p fid st stack_values ann target ==>
           cm_forward_spills base spill_values
             (cm_ann_spills ann) ==>
           cm_runtime_stack p (cm_state_regions st) fid
             (cm_state_fp st) (cm_state_regions st)
             (cm_ann_cursors ann) (cm_ann_spills ann)
             (cm_ann_saved ann) (cm_ann_calls ann) ==>
           0i <= fid ==>
           0i <= base ==>
           base + ilength spill_values <=
             cm_stemps
               (cm_function_body
                 (inth fid (cm_program_functions p))) ==>
           ilength spill_values + ilength stack_values < 65536i ==>
           cm_running_target_sim p fid st
             (REVERSE spill_values ++ stack_values)
             (cm_ann_linear
               (cm_value_reload_code p fid base spill_values) ann)
             (tvm_iter
               (cm_code_steps
                 (cm_value_reload_code p fid base spill_values))
               target)`);
  gnode_list cases = INDUCT_TAC(
      root, `spill_values:(cm_value)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm_list base_rules = THM_LIST(
        cm_ann_linear_nil, cm_code_steps_def, get_tvm_iter_def(),
        get_theorem_by_name("REVERSE"),
        get_theorem_by_name("APPEND"),
        get_theorem_by_name("ILENGTH_DEF"),
        get_theorem_by_name("NUM_OF_INT_OF_NUM"));
    conv base_normalize = then_conv(
        reduce_rewrite_conv(THM_LIST(cm_value_reload_code_def)),
        reduce_rewrite_conv(base_rules));
    thm base_view = apply_conversion(
        base_normalize, goal_ccl(leaf->g));
    thm base_sim = conv_rule(
        base_normalize,
        assume_rule(
          `cm_running_target_sim (p:cm_program) (fid:int)
            (st:cm_src_state) (stack_values:(cm_value)list)
            (ann:cm_annotation) (target:tvm_task)`));
    ACCEPT_TAC(leaf,
        eq_mp_rule(sym_rule(base_view), base_sim));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm ih = assume_rule(goal_lasmps(leaf->g)[0].tm);
    term tail_code =
        `cm_value_reload_code (p:cm_program) (fid:int)
          ((base:int) + 1i) (a1:(cm_value)list)`;
    term prefix =
        `cm_temp_load_code (p:cm_program) (fid:int) (base:int)`;
    term suffix =
        `${tail_code:(tvm_inst)list} ++ (rest:(tvm_inst)list)`;
    term next_ann =
        `cm_ann_linear ${prefix:(tvm_inst)list}
          (ann:cm_annotation)`;
    term next_target = `tvm_iter 5 (target:tvm_task)`;
    term address =
        `cm_state_fp (st:cm_src_state) +
         cm_temp_offset (p:cm_program) (fid:int) (base:int)`;

    thm forward = conv_rule(
        reduce_rewrite_conv(THM_LIST(cm_forward_spills_def)),
        assume_rule(
          `cm_forward_spills (base:int)
             ((a0:cm_value) :: (a1:(cm_value)list))
             (cm_ann_spills (ann:cm_annotation))`));
    thm head_holds = conjunct1_rule(forward);
    thm tail_forward = conjunct2_rule(forward);
    thm fid_nonneg = assume_rule(`0i <= (fid:int)`);
    thm base_nonneg = assume_rule(`0i <= (base:int)`);
    thm runtime = assume_rule(
        `cm_runtime_stack (p:cm_program)
          (cm_state_regions (st:cm_src_state)) (fid:int)
          (cm_state_fp st) (cm_state_regions st)
          (cm_ann_cursors (ann:cm_annotation))
          (cm_ann_spills ann) (cm_ann_saved ann)
          (cm_ann_calls ann)`);
    thm upper = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          get_theorem_by_name("ILENGTH_DEF"))),
        assume_rule(
          `(base:int) +
             ilength ((a0:cm_value) :: (a1:(cm_value)list)) <=
           cm_stemps
             (cm_function_body
               (inth (fid:int)
                 (cm_program_functions (p:cm_program))))`));
    thm tail_nonneg = ispec_rule(
        `a1:(cm_value)list`,
        get_theorem_by_name("ILENGTH_NONNEG"));
    thm slot_bound = mp_rule(mp_rule(int_arith_rule(
        `0i <= ilength (a1:(cm_value)list) ==>
         (base:int) + 1i + ilength a1 <=
           cm_stemps
             (cm_function_body
               (inth (fid:int)
                 (cm_program_functions (p:cm_program)))) ==>
         base <
           cm_stemps
             (cm_function_body
               (inth fid (cm_program_functions p)))`),
        tail_nonneg), upper);
    thm runtime_put = mp_rule(mp_rule(mp_rule(mp_rule(
        specl_rule(TERM_LIST(
          `p:cm_program`, `cm_state_regions (st:cm_src_state)`,
          `fid:int`, `cm_state_fp (st:cm_src_state)`,
          `cm_ann_cursors (ann:cm_annotation)`,
          `cm_state_regions st`, `base:int`, `a0:cm_value`,
          `cm_ann_spills ann`, `cm_ann_saved ann`,
          `cm_ann_calls ann`),
          cm_runtime_stack_spill_put),
        fid_nonneg), base_nonneg), slot_bound), runtime);
    thm address_safe = mp_rule(mp_rule(mp_rule(
        specl_rule(TERM_LIST(
          `p:cm_program`, `cm_state_regions (st:cm_src_state)`,
          `cm_ann_cursors (ann:cm_annotation)`, `fid:int`,
          `cm_state_fp (st:cm_src_state)`,
          `cm_state_regions st`, `cm_ann_spills ann`,
          `cm_ann_saved ann`, `cm_ann_calls ann`,
          `base:int`, `a0:cm_value`, address),
          get_cm_runtime_spill_address_safe()),
        runtime_put), fid_nonneg), refl_rule(address));
    thm signed_fp = conjunct1_rule(address_safe);
    thm signed_offset =
        conjunct1_rule(conjunct2_rule(address_safe));
    thm signed_address =
        conjunct1_rule(conjunct2_rule(conjunct2_rule(address_safe)));
    thm valid_address =
        conjunct2_rule(conjunct2_rule(conjunct2_rule(address_safe)));

    thm code_at = conv_rule(
        rewrite_conv(THM_LIST(
          cm_value_reload_code_def,
          gsym_rule(get_theorem_by_name("APPEND_ASSOC")))),
        assume_rule(
          `cm_code_at (cm_model_code (p:cm_program))
            (cm_ann_pc (ann:cm_annotation))
            (cm_value_reload_code p fid base
               ((a0:cm_value) :: (a1:(cm_value)list)) ++
             (rest:(tvm_inst)list))`));
    thm stack_bound = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          get_theorem_by_name("ILENGTH_DEF"))),
        assume_rule(
          `ilength ((a0:cm_value) :: (a1:(cm_value)list)) +
             ilength (stack_values:(cm_value)list) < 65536i`));
    thm current_stack_bound = mp_rule(mp_rule(int_arith_rule(
        `0i <= ilength (a1:(cm_value)list) ==>
         (1i + ilength a1) +
           ilength (stack_values:(cm_value)list) < 65536i ==>
         ilength stack_values < 65535i`),
        tail_nonneg), stack_bound);
    thm loaded = mp_rule(mp_rule(mp_rule(mp_rule(mp_rule(mp_rule(
        mp_rule(mp_rule(mp_rule(
          specl_rule(TERM_LIST(
            `p:cm_program`, `fid:int`, `st:cm_src_state`,
            `base:int`, `a0:cm_value`,
            `stack_values:(cm_value)list`, `ann:cm_annotation`,
            `target:tvm_task`, suffix, address),
            get_cm_target_temp_load()),
          code_at),
          assume_rule(
            `cm_running_target_sim (p:cm_program) (fid:int)
              (st:cm_src_state) (stack_values:(cm_value)list)
              (ann:cm_annotation) (target:tvm_task)`)),
        head_holds), current_stack_bound), signed_fp),
        signed_offset), refl_rule(address)), signed_address),
        valid_address);

    thm tail_rule = ispecl_rule(TERM_LIST(
        `cm_model_code (p:cm_program)`,
        `cm_ann_pc (ann:cm_annotation)`, prefix, suffix),
        get_cm_code_at_append_right());
    thm tail_raw = mp_rule(tail_rule, code_at);
    thm_list ann_rules = cm_target_args_annotation_rules();
    thm tail_normal =
        conv_rule(reduce_rewrite_conv(ann_rules), tail_raw);
    thm tail_view = apply_conversion(
        reduce_rewrite_conv(ann_rules),
        `cm_code_at (cm_model_code (p:cm_program))
          (cm_ann_pc ${next_ann:cm_annotation})
          ${suffix:(tvm_inst)list}`);
    thm tail_at =
        eq_mp_rule(sym_rule(tail_view), tail_normal);

    thm forward_view = apply_conversion(
        reduce_rewrite_conv(ann_rules),
        `cm_forward_spills ((base:int) + 1i)
          (a1:(cm_value)list)
          (cm_ann_spills ${next_ann:cm_annotation})`);
    thm next_forward =
        eq_mp_rule(sym_rule(forward_view), tail_forward);
    thm runtime_view = apply_conversion(
        reduce_rewrite_conv(ann_rules),
        `cm_runtime_stack (p:cm_program)
          (cm_state_regions (st:cm_src_state)) (fid:int)
          (cm_state_fp st) (cm_state_regions st)
          (cm_ann_cursors ${next_ann:cm_annotation})
          (cm_ann_spills ${next_ann:cm_annotation})
          (cm_ann_saved ${next_ann:cm_annotation})
          (cm_ann_calls ${next_ann:cm_annotation})`);
    thm next_runtime =
        eq_mp_rule(sym_rule(runtime_view), runtime);
    thm next_base_nonneg = mp_rule(int_arith_rule(
        `0i <= (base:int) ==> 0i <= base + 1i`), base_nonneg);
    thm next_upper = mp_rule(int_arith_rule(
        `(base:int) + 1i + ilength (a1:(cm_value)list) <=
           cm_stemps
             (cm_function_body
               (inth (fid:int)
                 (cm_program_functions (p:cm_program)))) ==>
         (base + 1i) + ilength a1 <=
           cm_stemps
             (cm_function_body
               (inth fid (cm_program_functions p)))`), upper);
    thm normalized_next_stack_bound = mp_rule(int_arith_rule(
        `(1i + ilength (a1:(cm_value)list)) +
           ilength (stack_values:(cm_value)list) < 65536i ==>
         ilength a1 + (1i + ilength stack_values) < 65536i`),
        stack_bound);
    thm next_stack_view = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_theorem_by_name("ILENGTH_DEF"))),
        `ilength (a1:(cm_value)list) +
           ilength ((a0:cm_value) ::
             (stack_values:(cm_value)list)) < 65536i`);
    thm next_stack_bound = eq_mp_rule(
        sym_rule(next_stack_view), normalized_next_stack_bound);

    thm tail_result = mp_rule(mp_rule(mp_rule(mp_rule(
        mp_rule(mp_rule(mp_rule(mp_rule(
          specl_rule(TERM_LIST(
            `p:cm_program`, `fid:int`, `st:cm_src_state`,
            `(a0:cm_value) :: (stack_values:(cm_value)list)`,
            `(base:int) + 1i`, next_ann, next_target,
            `rest:(tvm_inst)list`), ih),
          tail_at), loaded), next_forward), next_runtime),
        fid_nonneg), next_base_nonneg), next_upper),
        next_stack_bound);

    thm stack_assoc = sym_rule(ispecl_rule(TERM_LIST(
        `REVERSE (a1:(cm_value)list)`,
        `[a0:cm_value]:(cm_value)list`,
        `stack_values:(cm_value)list`),
        get_theorem_by_name("APPEND_ASSOC")));
    thm code_length_nonneg = ispec_rule(
        tail_code, get_theorem_by_name("ILENGTH_NONNEG"));
    thm count_add = mp_rule(
        specl_rule(TERM_LIST(`5i`,
          `ilength ${tail_code:(tvm_inst)list}`),
          get_theorem_by_name("NUM_OF_INT_ADD")),
        conj_rule(int_arith_rule(`0i <= 5i`),
          code_length_nonneg));
    count_add = conv_rule(rewrite_conv(THM_LIST(
        get_theorem_by_name("NUM_OF_INT_OF_NUM"))), count_add);
    thm_list finish_rules = THM_LIST(
        cm_value_reload_code_def,
        get_theorem_by_name("REVERSE"), stack_assoc,
        get_theorem_by_name("APPEND"),
        cm_ann_linear_append, cm_code_steps_append,
        get_cm_layout_temp_load_length(), cm_code_steps_def,
        get_theorem_by_name("ILENGTH_APPEND"),
        get_theorem_by_name("ILENGTH_DEF"),
        get_theorem_by_name("NUM_OF_INT_OF_NUM"), count_add,
        get_cm_tvm_iter_add());
    thm result_view = apply_conversion(
        reduce_rewrite_conv(finish_rules),
        goal_ccl(leaf->g));
    thm result_normal =
        conv_rule(reduce_rewrite_conv(finish_rules), tail_result);
    ACCEPT_TAC(leaf,
        eq_mp_rule(sym_rule(result_view), result_normal));
  }
  return gnode_prove(root);
}
PROOF static thm cm_target_value_reload =
    cm_prove_target_value_reload();

PROOF static thm cm_prove_target_args_reload(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (args:(cm_expr)list) (spill_values:(cm_value)list)
         (stack_values:(cm_value)list) (base:int)
         (ann:cm_annotation) (target:tvm_task)
         (rest:(tvm_inst)list).
         cm_code_at (cm_model_code p) (cm_ann_pc ann)
           (cm_emit_args_reload p fid base args ++ rest) ==>
         cm_running_target_sim p fid st stack_values ann target ==>
         cm_forward_spills base spill_values
           (cm_ann_spills ann) ==>
         ilength args == ilength spill_values ==>
         cm_runtime_stack p (cm_state_regions st) fid
           (cm_state_fp st) (cm_state_regions st)
           (cm_ann_cursors ann) (cm_ann_spills ann)
           (cm_ann_saved ann) (cm_ann_calls ann) ==>
         0i <= fid ==>
         0i <= base ==>
         base + ilength spill_values <=
           cm_stemps
             (cm_function_body
               (inth fid (cm_program_functions p))) ==>
         ilength spill_values + ilength stack_values < 65536i ==>
         cm_running_target_sim p fid st
           (REVERSE spill_values ++ stack_values)
           (cm_ann_linear
             (cm_emit_args_reload p fid base args) ann)
           (tvm_iter
             (cm_code_steps
               (cm_emit_args_reload p fid base args))
             target)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm length_equal = assume_rule(
      `ilength (args:(cm_expr)list) ==
       ilength (spill_values:(cm_value)list)`);
  thm code_equal = mp_rule(
      specl_rule(TERM_LIST(
        `args:(cm_expr)list`, `p:cm_program`, `fid:int`, `base:int`,
        `spill_values:(cm_value)list`),
        cm_emit_args_reload_values),
      length_equal);
  thm code_context = beta_norm(ap_term_rule(
      `\prefix:(tvm_inst)list.
         cm_code_at (cm_model_code (p:cm_program))
           (cm_ann_pc (ann:cm_annotation))
           (prefix ++ (rest:(tvm_inst)list))`,
      code_equal));
  thm value_code_at = eq_mp_rule(
      code_context,
      assume_rule(
        `cm_code_at (cm_model_code (p:cm_program))
          (cm_ann_pc (ann:cm_annotation))
          (cm_emit_args_reload p fid base (args:(cm_expr)list) ++
           (rest:(tvm_inst)list))`));
  thm value_result = mp_rule(mp_rule(mp_rule(mp_rule(
      mp_rule(mp_rule(mp_rule(mp_rule(
        specl_rule(TERM_LIST(
          `spill_values:(cm_value)list`, `p:cm_program`,
          `fid:int`, `st:cm_src_state`,
          `stack_values:(cm_value)list`, `base:int`,
          `ann:cm_annotation`, `target:tvm_task`,
          `rest:(tvm_inst)list`),
          cm_target_value_reload),
        value_code_at),
        assume_rule(
          `cm_running_target_sim (p:cm_program) (fid:int)
            (st:cm_src_state) (stack_values:(cm_value)list)
            (ann:cm_annotation) (target:tvm_task)`)),
      assume_rule(
        `cm_forward_spills (base:int)
          (spill_values:(cm_value)list)
          (cm_ann_spills (ann:cm_annotation))`)),
      assume_rule(
        `cm_runtime_stack (p:cm_program)
          (cm_state_regions (st:cm_src_state)) (fid:int)
          (cm_state_fp st) (cm_state_regions st)
          (cm_ann_cursors (ann:cm_annotation))
          (cm_ann_spills ann) (cm_ann_saved ann)
          (cm_ann_calls ann)`)),
      assume_rule(`0i <= (fid:int)`)),
      assume_rule(`0i <= (base:int)`)),
      assume_rule(
        `(base:int) + ilength (spill_values:(cm_value)list) <=
         cm_stemps
           (cm_function_body
             (inth (fid:int)
               (cm_program_functions (p:cm_program))))`)),
      assume_rule(
        `ilength (spill_values:(cm_value)list) +
           ilength (stack_values:(cm_value)list) < 65536i`));
  thm result_view = apply_conversion(
      rewrite_conv(THM_LIST(code_equal)), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf,
      eq_mp_rule(sym_rule(result_view), value_result));
  return gnode_prove(root);
}
PROOF thm cm_target_args_reload =
    cm_prove_target_args_reload();
PROOF thm get_cm_forward_spills_def(void) {
  return cm_forward_spills_def;
}
PROOF thm get_cm_staged_reverse_spills(void) {
  return cm_staged_reverse_spills;
}
PROOF thm get_cm_target_args_reload(void) {
  return cm_target_args_reload;
}

PROOF static int cmc_preservation_target_value_args_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_value_args_axioms_before,
      "cmc_preservation_target_value_args introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_value_args_checks =
    cmc_preservation_target_value_args_final_checks();
