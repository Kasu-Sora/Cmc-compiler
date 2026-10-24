/* Public ABI types, concrete representations, and compiler bridge lemmas. */

#include "cmc_concrete_defs.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "userlib/operational.h"
#include "cmc_rep.h"
#include "cmc_temp_algebra.h"
#include "cmc_stack_annotations.h"
#include "cmc_stack_local_core.h"
#require "userlib/operational.c"
#require "cmc_rep.c"
#require "cmc_temp_algebra.c"
#require "cmc_stack_annotations.c"
#require "cmc_stack_local_core.c"

PROOF static size_t _cmc_concrete_defs_axioms_before =
    vector_size(get_all_axioms());

/* Polymorphic list constants introduced into concrete symbolic states. */
PROOF int _e_cmc_ilength =
    cst_add_const_to_header(`ilength:(A)list->int`);
PROOF int _e_cmc_inth =
    cst_add_const_to_header(`inth:int->(A)list->A`);
PROOF int _e_cmc_append =
    cst_add_const_to_header(
      `APPEND:(A)list->(A)list->(A)list`);
PROOF int _e_cmc_param_stores_count =
    cst_add_const_to_header(
      `cm_param_stores_count:(cm_slot_d)list->int`);
PROOF int _e_cmc_functions_code_size =
    cst_add_const_to_header(
      `cm_functions_code_size:
        cm_program->(cm_function_d)list->int->int`);
PROOF int _e_cmc_function_prefix =
    cst_add_const_to_header(
      `cm_function_prefix:
        cm_program->(cm_function_d)list->int->int`);
PROOF int _e_cmc_char_normalize_code =
    cst_add_const_to_header(`cm_char_normalize_code`);
PROOF int _e_cmc_load_code =
    cst_add_const_to_header(`cm_load_code`);
PROOF int _e_cmc_store_code =
    cst_add_const_to_header(`cm_store_code`);
PROOF int _e_cmc_fp_relative_address_code =
    cst_add_const_to_header(`cm_fp_relative_address_code`);
PROOF int _e_cmc_param_offset =
    cst_add_const_to_header(`cm_param_offset`);
PROOF int _e_cmc_local_offset =
    cst_add_const_to_header(`cm_local_offset`);
PROOF int _e_cmc_temp_offset =
    cst_add_const_to_header(`cm_temp_offset`);
PROOF int _e_cmc_binding_address_code =
    cst_add_const_to_header(`cm_binding_address_code`);
PROOF int _e_cmc_temp_store_code =
    cst_add_const_to_header(`cm_temp_store_code`);
PROOF int _e_cmc_temp_load_code =
    cst_add_const_to_header(`cm_temp_load_code`);
PROOF int _e_cmc_binary_opcode =
    cst_add_const_to_header(`cm_binary_opcode`);
PROOF int _e_cmc_pointer_scale =
    cst_add_const_to_header(`cm_pointer_scale`);
PROOF int _e_cmc_binary_finish_code =
    cst_add_const_to_header(`cm_binary_finish_code`);
PROOF int _e_cmc_return_epilogue =
    cst_add_const_to_header(`cm_return_epilogue`);
PROOF int _e_cmc_emit_args_store =
    cst_add_const_to_header(`cm_emit_args_store`);
PROOF int _e_cmc_emit_args_reload =
    cst_add_const_to_header(`cm_emit_args_reload`);
PROOF int _e_cmc_emit_lvalue =
    cst_add_const_to_header(`cm_emit_lvalue`);
PROOF int _e_cmc_emit_rvalue =
    cst_add_const_to_header(`cm_emit_rvalue`);
PROOF int _e_cmc_emit_stmt =
    cst_add_const_to_header(`cm_emit_stmt`);
PROOF int _e_cmc_emit_param_stores =
    cst_add_const_to_header(`cm_emit_param_stores`);
PROOF int _e_cmc_emit_prologue =
    cst_add_const_to_header(`cm_emit_prologue`);
PROOF int _e_cmc_emit_function =
    cst_add_const_to_header(`cm_emit_function`);
PROOF int _e_cmc_emit_functions =
    cst_add_const_to_header(`cm_emit_functions`);
PROOF int _e_cmc_emit_prelude =
    cst_add_const_to_header(`cm_emit_prelude`);
PROOF int _e_cmc_model_code =
    cst_add_const_to_header(`cm_model_code`);


PROOF int _t_cm_emitter =
    (new_const("Tcm_emitter", get_struct_name_type()), 0);
PROOF int _f_cm_emitter_output =
    (new_const("Foutput", get_field_type()), 0);
PROOF int _f_cm_emitter_pc =
    (new_const("Fpc", get_field_type()), 0);


/*
 * Read-only views used by the concrete code generator.  They separate the
 * program root and current function header from the recursively owned
 * function bodies, so recursive AST traversals can retain layout metadata
 * without duplicating heap ownership.
 */
PROOF thm cm_program_context_rep_def = new_fun_definition(
    `cm_program_context_rep (root:int) (p:cm_program)
       (functions_ptr:int) : hprop =
       (exists structs_ptr globals_ptr strings_ptr.
          fact(~(root == 0i)) **
          data_at (field_addr root Tcm_program Fstructs) Tptr structs_ptr **
          data_at (field_addr root Tcm_program Fglobals) Tptr globals_ptr **
          data_at (field_addr root Tcm_program Fstrings) Tptr strings_ptr **
          data_at (field_addr root Tcm_program Ffunctions) Tptr
            functions_ptr **
          data_at (field_addr root Tcm_program Fmain_id) Tint
            (cm_program_main p) **
          cm_struct_list_rep structs_ptr (cm_program_structs p) **
          cm_global_list_rep globals_ptr (cm_program_globals p) **
          cm_string_list_rep strings_ptr (cm_program_strings p))`);

PROOF thm cm_function_context_rep_def = new_fun_definition(
    `cm_function_context_rep (function_ptr:int) (f:cm_function_d)
       (body_ptr:int) (next_ptr:int) : hprop =
       (exists params_ptr locals_ptr.
          fact(~(function_ptr == 0i)) **
          data_at (field_addr function_ptr Tcm_function Fret_ty) Tint
            (cm_type_encode (cm_function_ret f)) **
          data_at (field_addr function_ptr Tcm_function Fparams) Tptr
            params_ptr **
          data_at (field_addr function_ptr Tcm_function Flocals) Tptr
            locals_ptr **
          data_at (field_addr function_ptr Tcm_function Fbody) Tptr
            body_ptr **
          data_at (field_addr function_ptr Tcm_function Fnext) Tptr
            next_ptr **
          cm_slot_list_rep params_ptr (cm_function_params f) **
          cm_slot_list_rep locals_ptr (cm_function_locals f))`);
PROOF void cm_open_program_context_st(void) {
  thm view = apply_conversion(
      pure_rewrite_conv(THM_LIST(cm_program_context_rep_def)),
      `cm_program_context_rep (program__pre:int) (p:cm_program)
        (functions_ptr:int)`);
  cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
      rename_exists_hconv(eq2ent(view), TERM_LIST(
        `structs_ptr_:int`, `globals_ptr_:int`, `strings_ptr_:int`))));
}

PROOF void cm_close_program_context_st(void) {
  cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
      cm_program_context_fold_hconv(
        `program__pre:int`, `p:cm_program`, `functions_ptr:int`,
        `structs_ptr_:int`, `globals_ptr_:int`, `strings_ptr_:int`)));
}

PROOF void cm_open_function_context_st(void) {
  thm view = apply_conversion(
      pure_rewrite_conv(THM_LIST(cm_function_context_rep_def)),
      `cm_function_context_rep (fn__pre:int)
        (f:cm_function_d) (body:int) (next:int)`);
  cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
      rename_exists_hconv(eq2ent(view),
        TERM_LIST(`params_ptr_:int`, `locals_ptr_:int`))));
}

PROOF void cm_close_function_context_st(void) {
  cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
      cm_function_context_fold_hconv(
        `fn__pre:int`, `f:cm_function_d`, `body:int`, `next:int`,
        `params_ptr_:int`, `locals_ptr_:int`)));
}
PROOF void cm_add_opcode_facts_st(const term concrete,
                                  const term opcode) {
  add_fact_st(eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_tvm_opcode_code_def())),
      mk_eq(concrete,
        mk_comb(`tvm_opcode_code:tvm_opcode->int`, opcode)))));
  add_fact_st(eqt_elim_rule(apply_conversion(
      then_conv(
        rewrite_conv(THM_LIST(get_tvm_opcode_code_def())),
        get_conversion_by_name("INT_REDUCE_CONV")),
      mk_not(mk_eq(
        mk_comb(`tvm_opcode_code:tvm_opcode->int`, opcode),
        `22i:int`)))));
}

PROOF void cm_retarget_i64_st(const term cell, const thm result) {
  struct dest_eq_results sides = dest_eq(concl(result));
  add_fact_st(result);
  cst_set_symbolic_state(retarget_cell64_st(
      cst_get_symbolic_state(), cell, sides.tm1, sides.tm2));
}
PROOF void cm_add_count_facts(const thm theorem) {
  if (is_conj(concl(theorem))) {
    cm_add_count_facts(conjunct1_rule(theorem));
    cm_add_count_facts(conjunct2_rule(theorem));
    return;
  }
  term head = concl(theorem);
  while (is_comb(head)) {
    head = dest_comb(head).tm1;
  }
  bool encode = false;
  bool expand_i32 = false;
  bool skip = false;
  if (is_const(head)) {
    const char *name = dest_const(head).s;
    encode =
        strcmp(name, "cm_expr_counts_representable") == 0 ||
        strcmp(name, "cm_args_counts_representable") == 0 ||
        strcmp(name, "cm_stmt_counts_representable") == 0 ||
        strcmp(name, "cm_expr_wf") == 0 ||
        strcmp(name, "cm_args_wf") == 0 ||
        strcmp(name, "cm_stmt_wf") == 0 ||
        strcmp(name, "cm_type_code_wf") == 0 ||
        strcmp(name, "cm_binding_valid") == 0 ||
        strcmp(name, "cm_member_valid") == 0;
    expand_i32 = strcmp(name, "cm_i32_code_count") == 0;
    skip =
        strcmp(name, "cm_expr_convertible") == 0 ||
        strcmp(name, "cm_lvalue") == 0 ||
        strcmp(name, "cm_binary_types") == 0 ||
        strcmp(name, "cm_unary_types") == 0 ||
        strcmp(name, "cm_is_pointer") == 0 ||
        strcmp(name, "cm_scalar_type") == 0 ||
        strcmp(name, "cm_type_refs") == 0;
  }
  if (skip) {
    return;
  }
  if (expand_i32) {
    add_fact_st(eqt_intro_rule(theorem));
    add_fact_st(conv_rule(
        rewrite_conv(THM_LIST(get_cm_i32_code_count_def())), theorem));
    return;
  }
  if (encode) {
    add_fact_st(eqt_intro_rule(theorem));
  }
}

PROOF thm cm_first_expr_count_node_fact(const thm theorem) {
  if (is_conj(concl(theorem))) {
    return cm_first_expr_count_node_fact(conjunct1_rule(theorem));
  }
  return theorem;
}
PROOF static thm cm_prove_expr_counts_node(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (expr:cm_expr).
         cm_expr_counts_representable p fid expr ==>
         cm_expr_count_node_representable p fid expr`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(leaf,
      ispec_rule(`expr:cm_expr`, get_cm_expr_cases()), "Hex");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    while (true) {
      labeled_term_list assumptions = goal_lasmps(cases[i]->g);
      int index = labeled_term_list_index(assumptions, "Hex");
      if (!is_exists(assumptions[index].tm)) break;
      cases[i] = ASMP_EXISTS_TAC(cases[i], "Hex", NULL);
    }
    labeled_term_list assumptions = goal_lasmps(cases[i]->g);
    int index = labeled_term_list_index(assumptions, "Hex");
    thm shape = assume_rule(assumptions[index].tm);
    thm opened = conv_rule(rewrite_conv(THM_LIST(
        shape, get_cm_expr_counts_representable_def())),
        assume_rule(
          `cm_expr_counts_representable (p:cm_program)
            (fid:int) (expr:cm_expr)`));
    thm node = cm_first_expr_count_node_fact(opened);
    ACCEPT_TAC(cases[i], conv_rule(
        rewrite_conv(THM_LIST(sym_rule(shape))), node));
  }
  return gnode_prove(root);
}
PROOF thm cm_expr_counts_node = cm_prove_expr_counts_node();


PROOF void cm_open_expr_count_facts(const thm shape) {
  thm source = from_state_bool(
      `cm_expr_counts_representable
        (p:cm_program) (fid__pre:int) (e:cm_expr)`);
  thm shallow = conv_rule(rewrite_conv(THM_LIST(
      shape, get_cm_expr_counts_representable_def())), source);
  thm node = cm_first_expr_count_node_fact(shallow);
  thm generic_node = conv_rule(
      rewrite_conv(THM_LIST(sym_rule(shape))), node);
  thm generic_facts = conv_rule(rewrite_conv(THM_LIST(
      get_cm_expr_count_node_representable_def(),
      get_cm_code_counts_representable_def())), generic_node);
  cm_add_count_facts(generic_facts);
  thm representable = conv_rule(rewrite_conv(THM_LIST(
      shape, get_cm_expr_counts_representable_def(),
      get_cm_expr_count_node_representable_def(),
      get_cm_code_counts_representable_def(),
      get_cm_expr_type_def())), source);
  cm_add_count_facts(representable);
  thm well_formed = conv_rule(rewrite_conv(THM_LIST(
      shape, get_cm_expr_wf_def())),
      from_state_bool(
        `cm_expr_wf (p:cm_program) (f:cm_function_d) (e:cm_expr)`));
  cm_add_count_facts(well_formed);
}
PROOF void cm_open_expr_rep_st(void) {
  cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
      specl_rule(TERM_LIST(`expr__pre:int`, `e:cm_expr`),
        get_cm_expr_open())));
}

PROOF void cm_close_expr_rep_st(void) {
  apply_hconv_st(specl_rule(TERM_LIST(
      `expr__pre:int`, `e:cm_expr`, `za:int`, `zb:int`,
      `zargs:int`), get_cm_expr_close_witness()));
}
PROOF static term cm_plan_fragment_term(const term fragment,
                                        const term pattern) {
  return subst(TERM_PAIR_LIST(
      (term_pair){fragment, `fragment_:(tvm_inst)list`}), pattern);
}

PROOF void cm_plan_open(const term fragment) {
  term predicate = cm_plan_fragment_term(fragment,
      `cm_resolved_emitter_plan_rep (p:cm_program) (emitter__pre:int)
         (out:int) (capacity:int) (done:(tvm_inst)list)
         (fragment_ ++ (tail:(tvm_inst)list))`);
  thm view = apply_conversion(
      pure_rewrite_conv(THM_LIST(cm_resolved_emitter_plan_rep_def)),
      predicate);
  cst_set_symbolic_state(local_apply(
      cst_get_symbolic_state(), eq2ent(view)));

  term prefix_capacity = cm_plan_fragment_term(fragment,
      `ilength (done:(tvm_inst)list) +
         ilength (fragment_:(tvm_inst)list) <=
         (capacity:int)`);
  term final_capacity = cm_plan_fragment_term(fragment,
      `ilength ((done:(tvm_inst)list) ++
          (fragment_:(tvm_inst)list)) +
         ilength (tail:(tvm_inst)list) <= (capacity:int)`);
  thm input_capacity = conv_rule(
      rewrite_conv(THM_LIST(get_theorem_by_name("ILENGTH_APPEND"))),
      assume_rule(cm_plan_fragment_term(fragment,
        `ilength (done:(tvm_inst)list) +
           ilength ((fragment_:(tvm_inst)list) ++
             (tail:(tvm_inst)list)) <=
           (capacity:int)`)));
  thm tail_nonnegative = ispec_rule(
      `tail:(tvm_inst)list`, get_theorem_by_name("ILENGTH_NONNEG"));
  add_fact_st(by_defs_arith(prefix_capacity,
      THM_LIST(get_theorem_by_name("ILENGTH_APPEND")),
      THM_LIST(input_capacity, tail_nonnegative)));
  add_fact_st(by_defs_arith(final_capacity,
      THM_LIST(get_theorem_by_name("ILENGTH_APPEND")),
      THM_LIST(input_capacity)));
}

PROOF void cm_plan_close(const term fragment) {
  term predicate = cm_plan_fragment_term(fragment,
      `cm_resolved_emitter_plan_rep (p:cm_program) (emitter__pre:int)
         (out:int) (capacity:int)
         ((done:(tvm_inst)list) ++ fragment_)
         (tail:(tvm_inst)list)`);
  thm view = apply_conversion(
      pure_rewrite_conv(THM_LIST(cm_resolved_emitter_plan_rep_def)),
      predicate);
  cst_set_symbolic_state(local_apply(
      cst_get_symbolic_state(), eq2ent(sym_rule(view))));
}
PROOF void cm_select_code_plan_st(const thm code_shape) {
  substitute_st(code_shape);
  rewrite_st(THM_LIST(
      gsym_rule(get_theorem_by_name("APPEND_ASSOC")),
      get_theorem_by_name("APPEND_NIL")));
}

PROOF void cm_restore_code_plan_st(const thm code_shape) {
  rewrite_st(THM_LIST(
      gsym_rule(get_theorem_by_name("APPEND_ASSOC")),
      get_theorem_by_name("APPEND"),
      get_theorem_by_name("APPEND_NIL")));
  thm prefix_shape = beta_norm(ap_term_rule(
      `\code:(tvm_inst)list. (done:(tvm_inst)list) ++ code`,
      sym_rule(code_shape)));
  substitute_st(prefix_shape);
}

PROOF static term cm_code_end_fact_term(const term code) {
  return subst(TERM_PAIR_LIST(
      (term_pair){code, `code_:(tvm_inst)list`}),
      `cm_i32_code_count
         ((pc__pre:int) + ilength (code_:(tvm_inst)list)) <=> true`);
}

PROOF void cm_restore_code_plan_end_st(const thm code_shape) {
  term parent_end = cm_code_end_fact_term(
      dest_eq(concl(code_shape)).tm1);
  term selected_end = cm_code_end_fact_term(rhs_of(code_shape));
  thm restored_end = by_rewrite(parent_end,
      THM_LIST(code_shape, assume_rule(selected_end)));
  cm_restore_code_plan_st(code_shape);
  add_fact_st(restored_end);
}

PROOF void cm_empty_code_plan_end_st(const thm code_shape) {
  substitute_st(code_shape);
  rewrite_st(THM_LIST(get_theorem_by_name("APPEND"),
      get_theorem_by_name("ILENGTH_DEF")));
  substitute_st(sym_rule(ispec_rule(
      `done:(tvm_inst)list`, get_theorem_by_name("APPEND_NIL"))));
  thm prefix_shape = beta_norm(ap_term_rule(
      `\code:(tvm_inst)list. (done:(tvm_inst)list) ++ code`,
      sym_rule(code_shape)));
  substitute_st(prefix_shape);
  term parent_end = cm_code_end_fact_term(
      dest_eq(concl(code_shape)).tm1);
  thm restored_end = by_rewrite(parent_end,
      THM_LIST(code_shape, get_theorem_by_name("ILENGTH_DEF"),
        assume_rule(
          `cm_i32_code_count ((pc__pre:int) + 0i) <=> true`)));
  add_fact_st(restored_end);
}

/*
 * A filled code prefix and the undefined suffix of both parallel output
 * arrays.  The emitter fields themselves carry the local object's ownership;
 * unlike caller-owned output storage, its abstract stack base need not be
 * constrained numerically.
 */
PROOF thm cm_emitter_rep_def = new_fun_definition(
    `cm_emitter_rep (emitter:int) (out:int) (capacity:int)
       (ops_prefix:(int)list) (imms_prefix:(int)list) : hprop =
       (exists ops imms.
          fact(~(out == 0i)) **
          fact(~(ops == 0i)) ** fact(~(imms == 0i)) **
          fact(ilength ops_prefix == ilength imms_prefix) **
          fact(0i <= ilength ops_prefix) **
          fact(ilength ops_prefix <= capacity) **
          data_at (field_addr emitter Tcm_emitter Foutput) Tptr out **
          data_at (field_addr emitter Tcm_emitter Fpc) Tint
            (ilength ops_prefix) **
          data_at (field_addr out Tcm_output Fops) Tptr ops **
          data_at (field_addr out Tcm_output Fimms) Tptr imms **
          data_at (field_addr out Tcm_output Fcode_capacity) Tint capacity **
          store_int_array ops (ilength ops_prefix) ops_prefix **
          store_undef_int_array
            (ops + ilength ops_prefix * sizeof Tint)
            (capacity - ilength ops_prefix) **
          store_int64_array imms (ilength ops_prefix) imms_prefix **
          store_undef_int64_array
            (imms + ilength ops_prefix * sizeof Tint64)
            (capacity - ilength ops_prefix))`);

PROOF thm cm_emitter_plan_rep_def = new_fun_definition(
    `cm_emitter_plan_rep (emitter:int) (out:int) (capacity:int)
       (done:(tvm_inst)list) (todo:(tvm_inst)list) : hprop =
       (fact(ilength done + ilength todo <= capacity) **
        cm_emitter_rep emitter out capacity
          (cm_rep_ops done) (cm_rep_imms done))`);

/*
 * The concrete emitter records function identifiers at CALL sites and the
 * final linear pass resolves them to absolute PCs.  This logical map keeps
 * the recursive emitter specifications phrased in the resolved pure model.
 */
PROOF thm cm_patch_inst_def = new_rec_definition(
    get_tvm_inst_recursion(),
    `!p op imm.
       cm_patch_inst (p:cm_program) (TVMInst (op:tvm_opcode) (imm:int)) =
       TVMInst op
         (if tvm_opcode_code op == 22i
          then cm_function_pc p imm else imm)`);
PROOF thm cm_patch_code_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p. cm_patch_code (p:cm_program) ([]:(tvm_inst)list) = []) &&
     (!p inst rest.
        cm_patch_code (p:cm_program)
          ((inst:tvm_inst) :: (rest:(tvm_inst)list)) =
        cm_patch_inst p inst :: cm_patch_code p rest)`);

PROOF thm cm_resolved_emitter_rep_def = new_fun_definition(
    `cm_resolved_emitter_rep (p:cm_program) (emitter:int) (out:int)
       (capacity:int) (resolved_prefix:(tvm_inst)list) : hprop =
       (exists raw_prefix.
          fact(cm_patch_code p raw_prefix == resolved_prefix) **
          cm_emitter_rep emitter out capacity
            (cm_rep_ops raw_prefix) (cm_rep_imms raw_prefix))`);
PROOF void cm_open_single_child_count_payload(const thm shape) {
  thm payload_view = by_rewrite(
      `cm_expr_payload (e:cm_expr)
         (za:int) (zb:int) (zargs:int) -|-
       fact(~(za == 0i) && zb == 0i && zargs == 0i) **
       cm_expr_node za (arg_:cm_expr)
         (cm_expr_payload arg_)`,
      THM_LIST(shape, get_cm_expr_payload_def()));
  apply_hconv_st(eq2ent(payload_view));
  thm arg_view = inst_rule(TERM_PAIR_LIST(
      (term_pair){`za:int`, `p:int`},
      (term_pair){`arg_:cm_expr`, `e:cm_expr`}),
      get_cm_expr_rep_def());
  apply_hconv_st(eq2ent(sym_rule(arg_view)));
}

PROOF void cm_close_single_child_count_payload(const thm shape) {
  thm arg_view = inst_rule(TERM_PAIR_LIST(
      (term_pair){`za:int`, `p:int`},
      (term_pair){`arg_:cm_expr`, `e:cm_expr`}),
      get_cm_expr_rep_def());
  apply_hconv_st(eq2ent(arg_view));
  thm payload_view = by_rewrite(
      `cm_expr_payload (e:cm_expr)
         (za:int) (zb:int) (zargs:int) -|-
       fact(~(za == 0i) && zb == 0i && zargs == 0i) **
       cm_expr_node za (arg_:cm_expr)
         (cm_expr_payload arg_)`,
      THM_LIST(shape, get_cm_expr_payload_def()));
  thm payload_facts = conj_rule(
      assume_rule(`~((za:int) == 0i)`),
      conj_rule(assume_rule(`(zb:int) == 0i`),
        assume_rule(`(zargs:int) == 0i`)));
  thm payload_intro = frame_right_slrule(
      add_fact_hconv(payload_facts),
      `cm_expr_node (za:int) (arg_:cm_expr)
         (cm_expr_payload arg_)`);
  apply_hconv_st(trans_slrule(payload_intro,
      eq2ent(sym_rule(payload_view))));
}

PROOF void cm_open_two_child_count_payload(const thm shape) {
  thm payload_view = by_rewrite(
      `cm_expr_payload (e:cm_expr)
         (za:int) (zb:int) (zargs:int) -|-
       fact(zargs == 0i) **
       cm_expr_node za (left_:cm_expr)
         (cm_expr_payload left_) **
       cm_expr_node zb (right_:cm_expr)
         (cm_expr_payload right_)`,
      THM_LIST(shape, get_cm_expr_payload_def()));
  apply_hconv_st(eq2ent(payload_view));
  thm left_view = inst_rule(TERM_PAIR_LIST(
      (term_pair){`za:int`, `p:int`},
      (term_pair){`left_:cm_expr`, `e:cm_expr`}),
      get_cm_expr_rep_def());
  apply_hconv_st(eq2ent(sym_rule(left_view)));
  thm right_view = inst_rule(TERM_PAIR_LIST(
      (term_pair){`zb:int`, `p:int`},
      (term_pair){`right_:cm_expr`, `e:cm_expr`}),
      get_cm_expr_rep_def());
  apply_hconv_st(eq2ent(sym_rule(right_view)));
}

PROOF void cm_close_two_child_count_payload(const thm shape) {
  thm right_view = inst_rule(TERM_PAIR_LIST(
      (term_pair){`zb:int`, `p:int`},
      (term_pair){`right_:cm_expr`, `e:cm_expr`}),
      get_cm_expr_rep_def());
  apply_hconv_st(eq2ent(right_view));
  thm left_view = inst_rule(TERM_PAIR_LIST(
      (term_pair){`za:int`, `p:int`},
      (term_pair){`left_:cm_expr`, `e:cm_expr`}),
      get_cm_expr_rep_def());
  apply_hconv_st(eq2ent(left_view));
  thm payload_view = by_rewrite(
      `cm_expr_payload (e:cm_expr)
         (za:int) (zb:int) (zargs:int) -|-
       fact(zargs == 0i) **
       cm_expr_node za (left_:cm_expr)
         (cm_expr_payload left_) **
       cm_expr_node zb (right_:cm_expr)
         (cm_expr_payload right_)`,
      THM_LIST(shape, get_cm_expr_payload_def()));
  apply_hconv_st(eq2ent(sym_rule(payload_view)));
}
PROOF thm cm_resolved_emitter_plan_rep_def = new_fun_definition(
    `cm_resolved_emitter_plan_rep (p:cm_program) (emitter:int) (out:int)
       (capacity:int) (done:(tvm_inst)list)
       (todo:(tvm_inst)list) : hprop =
       (fact(ilength done + ilength todo <= capacity) **
        cm_resolved_emitter_rep p emitter out capacity done)`);
PROOF int _e_cmc_resolved_emitter_plan_rep =
    cst_add_const_to_header(`cm_resolved_emitter_plan_rep`);
PROOF thm cm_expr_code_for_def = new_fun_definition(
    `cm_expr_code_for (p:cm_program) (fid:int) (pc:int) (temp:int)
       (expr:cm_expr) (lvalue:int) : (tvm_inst)list =
       if lvalue == 0i
       then cm_emit_rvalue p fid pc temp expr
       else cm_emit_lvalue p fid pc temp expr`);
PROOF thm cm_expr_load_suffix_def = new_fun_definition(
    `cm_expr_load_suffix (ty:cm_type) (lvalue:int) :
       (tvm_inst)list =
       if lvalue == 0i then cm_load_code ty else []`);
PROOF thm cm_member_load_suffix_def = new_fun_definition(
    `cm_member_load_suffix (p:cm_program) (base:cm_type)
       (mid:int) (ty:cm_type) (lvalue:int) : (tvm_inst)list =
       if lvalue == 0i
       then if cm_member_array p base mid then [] else cm_load_code ty
       else []`);
PROOF thm cm_expr_temps_for_def = new_fun_definition(
    `cm_expr_temps_for (expr:cm_expr) (lvalue:int) : int =
       if lvalue == 0i then cm_rtemps expr else cm_ltemps expr`);
PROOF int _e_cmc_expr_code_for =
    cst_add_const_to_header(`cm_expr_code_for`);
PROOF int _e_cmc_expr_load_suffix =
    cst_add_const_to_header(`cm_expr_load_suffix`);
PROOF int _e_cmc_member_load_suffix =
    cst_add_const_to_header(`cm_member_load_suffix`);
PROOF int _e_cmc_expr_temps_for =
    cst_add_const_to_header(`cm_expr_temps_for`);
PROOF thm cm_leaf_expr_def = new_fun_definition(
    `cm_leaf_expr (expr:cm_expr) : bool =
       (cm_rep_expr_kind expr == 0i ||
        cm_rep_expr_kind expr == 1i ||
        cm_rep_expr_kind expr == 9i ||
        cm_rep_expr_kind expr == 10i)`);
PROOF int _e_cmc_leaf_expr =
    cst_add_const_to_header(`cm_leaf_expr`);
PROOF thm cm_simple_expr_def = new_fun_definition(
    `cm_simple_expr (expr:cm_expr) : bool =
       (cm_leaf_expr expr || cm_rep_expr_kind expr == 2i)`);
PROOF int _e_cmc_simple_expr =
    cst_add_const_to_header(`cm_simple_expr`);
PROOF thm cm_intrinsic_expr_def = new_fun_definition(
    `cm_intrinsic_expr (expr:cm_expr) : bool =
       (cm_rep_expr_kind expr == 11i ||
        cm_rep_expr_kind expr == 12i ||
        cm_rep_expr_kind expr == 13i)`);
PROOF int _e_cmc_intrinsic_expr =
    cst_add_const_to_header(`cm_intrinsic_expr`);
PROOF static thm cm_prove_temp_offset_mono(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (low:int) (high:int).
         low <= high ==>
         cm_temp_offset p fid low <= cm_temp_offset p fid high`);
  gnode leaf = AUTO_INTROS_TAC(root);
  ACCEPT_TAC(leaf, by_defs_arith(goal_ccl(leaf->g),
      THM_LIST(get_cm_temp_offset_def()),
      THM_LIST(assume_rule(`(low:int) <= (high:int)`))));
  return gnode_prove(root);
}
PROOF thm cm_temp_offset_mono = cm_prove_temp_offset_mono();

PROOF void cm_add_temp_offset_bound_st(const term at) {
  term at_le_limit = subst(TERM_PAIR_LIST(
      (term_pair){at, `at_:int`}),
      `(at_:int) <= (temp_limit__pre:int)`);
  thm monotone = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid__pre:int`, at, `temp_limit__pre:int`),
      cm_temp_offset_mono), assume_rule(at_le_limit));
  term ceiling =
      `cm_temp_offset (p:cm_program) (fid__pre:int)
         (temp_limit__pre:int) <= 2147483647i`;
  term target = subst(TERM_PAIR_LIST(
      (term_pair){at, `at_:int`}),
      `cm_temp_offset (p:cm_program) (fid__pre:int)
         (at_:int) <= 2147483647i`);
  thm result = mp_rule(mp_rule(
      int_arith_rule(mk_imp(concl(monotone),
        mk_imp(ceiling, target))), monotone),
      assume_rule(ceiling));
  add_fact_st(result);
}

PROOF static thm cm_prove_rep_ops_append(void) {
  gnode root = gnode_new_with_ccl(
      `!(left:(tvm_inst)list) (right:(tvm_inst)list).
         cm_rep_ops (left ++ right) ==
         cm_rep_ops left ++ cm_rep_ops right`);
  gnode_list cases = INDUCT_TAC(root, `left:(tvm_inst)list`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, THM_LIST(
        get_theorem_by_name("APPEND"), get_cm_rep_ops_def()));
  }
  return gnode_prove(root);
}
PROOF thm cm_rep_ops_append = cm_prove_rep_ops_append();

PROOF static thm cm_prove_rep_imms_append(void) {
  gnode root = gnode_new_with_ccl(
      `!(left:(tvm_inst)list) (right:(tvm_inst)list).
         cm_rep_imms (left ++ right) ==
         cm_rep_imms left ++ cm_rep_imms right`);
  gnode_list cases = INDUCT_TAC(root, `left:(tvm_inst)list`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, THM_LIST(
        get_theorem_by_name("APPEND"), get_cm_rep_imms_def()));
  }
  return gnode_prove(root);
}
PROOF thm cm_rep_imms_append = cm_prove_rep_imms_append();

PROOF static thm cm_prove_rep_ops_length(void) {
  gnode root = gnode_new_with_ccl(
      `!(code:(tvm_inst)list).
         ilength (cm_rep_ops code) == ilength code`);
  gnode_list cases = INDUCT_TAC(root, `code:(tvm_inst)list`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, THM_LIST(
        get_cm_rep_ops_def(), get_theorem_by_name("ILENGTH_DEF")));
  }
  return gnode_prove(root);
}
PROOF thm cm_rep_ops_length = cm_prove_rep_ops_length();

PROOF static thm cm_prove_rep_imms_length(void) {
  gnode root = gnode_new_with_ccl(
      `!(code:(tvm_inst)list).
         ilength (cm_rep_imms code) == ilength code`);
  gnode_list cases = INDUCT_TAC(root, `code:(tvm_inst)list`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, THM_LIST(
        get_cm_rep_imms_def(), get_theorem_by_name("ILENGTH_DEF")));
  }
  return gnode_prove(root);
}
PROOF thm cm_rep_imms_length = cm_prove_rep_imms_length();

PROOF static thm cm_prove_patch_code_append(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (left:(tvm_inst)list)
          (right:(tvm_inst)list).
         cm_patch_code p (left ++ right) ==
         cm_patch_code p left ++ cm_patch_code p right`);
  gnode_list cases = INDUCT_TAC(root, `left:(tvm_inst)list`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, THM_LIST(
        get_theorem_by_name("APPEND"), cm_patch_code_def));
  }
  return gnode_prove(root);
}
PROOF thm cm_patch_code_append = cm_prove_patch_code_append();

PROOF static thm cm_prove_patch_code_length(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (code:(tvm_inst)list).
         ilength (cm_patch_code p code) == ilength code`);
  gnode_list cases = INDUCT_TAC(root, `code:(tvm_inst)list`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, THM_LIST(
        cm_patch_code_def, get_theorem_by_name("ILENGTH_DEF")));
  }
  return gnode_prove(root);
}
PROOF thm cm_patch_code_length = cm_prove_patch_code_length();

PROOF int _e_cm_patch_inst =
    cst_add_const_to_header(`cm_patch_inst`);
PROOF int _e_cm_patch_code =
    cst_add_const_to_header(`cm_patch_code`);
PROOF int _e_cm_resolved_emitter_rep =
    cst_add_const_to_header(`cm_resolved_emitter_rep`);

PROOF int _e_cm_program_context_rep =
    cst_add_const_to_header(`cm_program_context_rep`);
PROOF int _e_cm_function_context_rep =
    cst_add_const_to_header(`cm_function_context_rep`);
PROOF int _e_cm_emitter_rep =
    cst_add_const_to_header(`cm_emitter_rep`);
PROOF int _e_cm_emitter_plan_rep =
    cst_add_const_to_header(`cm_emitter_plan_rep`);

PROOF thm cm_function_context_fold_hconv(
    const term function_ptr, const term descriptor,
    const term body_ptr, const term next_ptr,
    const term params_ptr, const term locals_ptr) {
  term subject = mk_comb(
      mk_comb(
        mk_comb(
          mk_comb(`cm_function_context_rep`, function_ptr),
          descriptor),
        body_ptr),
      next_ptr);
  thm view = apply_conversion(
      pure_rewrite_conv(THM_LIST(cm_function_context_rep_def)),
      subject);
  term existential = dest_eq(concl(view)).tm2;
  dest_binder_results outer = dest_sl_exists(existential);
  dest_binder_results inner = dest_sl_exists(outer.tm);
  term body = subst(TERM_PAIR_LIST(
      (term_pair){params_ptr, outer.v},
      (term_pair){locals_ptr, inner.v}), inner.tm);
  term inner_existential = subst(TERM_PAIR_LIST(
      (term_pair){params_ptr, outer.v}), outer.tm);
  thm introduced = refl_slrule(body);
  introduced = exists_slrule(
      inner_existential, locals_ptr, introduced);
  introduced = exists_slrule(
      existential, params_ptr, introduced);
  return trans_slrule(
      introduced, eq2ent(sym_rule(view)));
}

PROOF thm cm_program_context_fold_hconv(
    const term root, const term program,
    const term functions_ptr, const term structs_ptr,
    const term globals_ptr, const term strings_ptr) {
  term subject = mk_comb(
      mk_comb(
        mk_comb(`cm_program_context_rep`, root),
        program),
      functions_ptr);
  thm view = apply_conversion(
      pure_rewrite_conv(THM_LIST(cm_program_context_rep_def)),
      subject);
  term existential = dest_eq(concl(view)).tm2;
  dest_binder_results outer = dest_sl_exists(existential);
  dest_binder_results middle = dest_sl_exists(outer.tm);
  dest_binder_results inner = dest_sl_exists(middle.tm);
  term body = subst(TERM_PAIR_LIST(
      (term_pair){structs_ptr, outer.v},
      (term_pair){globals_ptr, middle.v},
      (term_pair){strings_ptr, inner.v}), inner.tm);
  term middle_existential = subst(TERM_PAIR_LIST(
      (term_pair){structs_ptr, outer.v},
      (term_pair){globals_ptr, middle.v}), middle.tm);
  term outer_existential = subst(TERM_PAIR_LIST(
      (term_pair){structs_ptr, outer.v}), outer.tm);
  thm introduced = refl_slrule(body);
  introduced = exists_slrule(
      middle_existential, strings_ptr, introduced);
  introduced = exists_slrule(
      outer_existential, globals_ptr, introduced);
  introduced = exists_slrule(
      existential, structs_ptr, introduced);
  return trans_slrule(
      introduced, eq2ent(sym_rule(view)));
}


PROOF static thm cm_prove_function_context_cons_open(void) {
  gnode root = gnode_new_with_ccl(
      `!(pointer:int) (fn:cm_function_d)
         (rest:(cm_function_d)list).
       cm_function_list_rep pointer (fn :: rest) |--
       exists body next.
         cm_function_context_rep pointer fn body next **
         cm_stmt_rep body (cm_function_body fn) **
         cm_function_list_rep next rest`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list initialized = AUTO_INIT_SLTAC(leaf);
  gnode converted = CONV_WITH_ASMP_SLTAC(
      initialized[0], rewrite_conv,
      THM_LIST(get_cm_function_list_rep_def(),
        get_cm_function_header_list_rep_def(),
        get_cm_function_body_list_rep_def(),
        cm_function_context_rep_def));
  gnode pulled = EXISTS_PULL_SLTAC(converted);
  gnode bodies = HANT_EXISTS_SLTAC(pulled, "H", "bodies_");
  gnode separated = HANT_SEP_SLTAC(
      bodies, "H", "Hheader", "Hbody");
  gnode zp = HANT_EXISTS_SLTAC(separated, "Hheader", "zp_");
  gnode zl = HANT_EXISTS_SLTAC(zp, "Hheader", "zl_");
  gnode zb = HANT_EXISTS_SLTAC(zl, "Hheader", "zb_");
  gnode zn = HANT_EXISTS_SLTAC(zb, "Hheader", "zn_");
  gnode body_rest = HANT_EXISTS_SLTAC(
      zn, "Hheader", "body_rest_");
  gnode zb_body = HANT_EXISTS_SLTAC(
      body_rest, "Hbody", "zb_body_");
  gnode body_rest_body = HANT_EXISTS_SLTAC(
      zb_body, "Hbody", "body_rest_body_");
  gnode header_parts = HANT_SEP_SLTAC(body_rest_body,
      "Hheader", "Hheader_fact", "Hheader_rest");
  gnode body_parts = HANT_SEP_SLTAC(header_parts,
      "Hbody", "Hbody_fact", "Hbody_rest");
  gnode facts = AUTO_INTRO_FACT_SLTAC(body_parts);
  thm header_shape = assume_rule(
      `~((pointer:int) == 0i) &&
       (bodies_:(int)list) == (zb_:int) :: (body_rest_:(int)list)`);
  thm body_shape = assume_rule(
      `(bodies_:(int)list) ==
       (zb_body_:int) :: (body_rest_body_:(int)list)`);
  thm cons_same = trans_rule(
      sym_rule(conjunct2_rule(header_shape)), body_shape);
  thm cons_parts = eq_mp_rule(ispecl_rule(TERM_LIST(
      `zb_:int`, `zb_body_:int`, `body_rest_:(int)list`,
      `body_rest_body_:(int)list`),
      get_theorem_by_name("CONS_11")), cons_same);
  gnode witnessed = LIST_EXISTS_SLTAC(facts,
      TERM_LIST(`zb_:int`, `zn_:int`, `zp_:int`, `zl_:int`,
        `body_rest_:(int)list`));
  gnode reduced = CONV_WITH_ASMP_SLTAC(
      witnessed, rewrite_conv,
      THM_LIST(sym_rule(conjunct1_rule(cons_parts)),
        sym_rule(conjunct2_rule(cons_parts))));
  gnode cleaned = CLEAN_SLTAC(reduced);
  AUTO_FRAME_SLTAC(cleaned);
  return gnode_prove(root);
}
PROOF thm cm_function_context_cons_open =
    cm_prove_function_context_cons_open();

PROOF static thm cm_prove_function_context_cons_close(void) {
  gnode root = gnode_new_with_ccl(
      `!(pointer:int) (fn:cm_function_d)
         (rest:(cm_function_d)list) (body:int) (next:int).
       cm_function_context_rep pointer fn body next **
       cm_stmt_rep body (cm_function_body fn) **
       cm_function_list_rep next rest |--
       cm_function_list_rep pointer (fn :: rest)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list initialized = AUTO_INIT_SLTAC(leaf);
  gnode converted = CONV_WITH_ASMP_SLTAC(
      initialized[0], rewrite_conv,
      THM_LIST(get_cm_function_list_rep_def(),
        get_cm_function_header_list_rep_def(),
        get_cm_function_body_list_rep_def(),
        cm_function_context_rep_def));
  gnode pulled = EXISTS_PULL_SLTAC(converted);
  gnode_list destructed = AUTO_HANT_DESTRUCT_SLTAC(pulled);
  ENSURE_COND(vector_size(destructed) == 1,
      "unexpected function context close branches");
  gnode pending = destructed[0];
  gnode facts = AUTO_INTRO_FACT_SLTAC(pending);
  gnode witnessed = LIST_EXISTS_SLTAC(facts, TERM_LIST(
      `(body:int) :: (bodies:(int)list)`, `params_ptr:int`,
      `locals_ptr:int`, `body:int`, `next:int`,
      `bodies:(int)list`, `body:int`, `bodies:(int)list`));
  gnode reduced = CONV_WITH_ASMP_SLTAC(
      witnessed, rewrite_conv, THM_LIST());
  gnode cleaned = CLEAN_SLTAC(reduced);
  AUTO_FRAME_SLTAC(cleaned);
  return gnode_prove(root);
err:
  return empty_theorem;
}
PROOF thm cm_function_context_cons_close =
    cm_prove_function_context_cons_close();


PROOF static thm cm_prove_function_list_nonnull_shape(void) {
  gnode root = gnode_new_with_ccl(
      `!(pointer:int) (functions:(cm_function_d)list).
       ~(pointer == 0i) ==>
       (cm_function_list_rep pointer functions |--
        exists fn rest.
          fact(functions == (fn:cm_function_d) :: rest) **
          cm_function_list_rep pointer functions)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list initialized = AUTO_INIT_SLTAC(leaf);
  gnode split_open = AUTO_HANT_APPLY_SLTAC(
      initialized[0], "H",
      specl_rule(TERM_LIST(`pointer:int`,
        `functions:(cm_function_d)list`),
        get_cm_function_split_open()));
  gnode bodies =
      HANT_EXISTS_SLTAC(split_open, "H", "bodies_");
  gnode separated = HANT_SEP_SLTAC(
      bodies, "H", "Hheader", "Hbody");
  thm header_open = mp_rule(specl_rule(TERM_LIST(
      `pointer:int`, `functions:(cm_function_d)list`,
      `bodies_:(int)list`), get_cm_function_header_unfold()),
      assume_rule(`~((pointer:int) == 0i)`));
  gnode opened = AUTO_HANT_APPLY_SLTAC(
      separated, "Hheader", header_open);
  gnode fn = HANT_EXISTS_SLTAC(opened, "Hheader", "fn_");
  gnode rest = HANT_EXISTS_SLTAC(fn, "Hheader", "rest_");
  gnode body = HANT_EXISTS_SLTAC(rest, "Hheader", "body_");
  gnode body_rest =
      HANT_EXISTS_SLTAC(body, "Hheader", "body_rest_");
  gnode zp = HANT_EXISTS_SLTAC(
      body_rest, "Hheader", "zp_");
  gnode zl = HANT_EXISTS_SLTAC(zp, "Hheader", "zl_");
  gnode zn = HANT_EXISTS_SLTAC(zl, "Hheader", "zn_");
  gnode header_parts = HANT_SEP_SLTAC(
      zn, "Hheader", "Hshape", "Hheader_fields");
  gnode facts = AUTO_INTRO_FACT_SLTAC(header_parts);
  thm header_fold = mp_rule(specl_rule(TERM_LIST(
      `pointer:int`, `fn_:cm_function_d`,
      `rest_:(cm_function_d)list`, `body_:int`,
      `body_rest_:(int)list`, `zp_:int`, `zl_:int`,
      `zn_:int`), get_cm_function_header_fold()),
      assume_rule(`~((pointer:int) == 0i)`));
  gnode folded_header =
      AUTO_HANT_APPLY_SLTAC(facts, NULL, header_fold);
  gnode normalized = CONV_WITH_ASMP_SLTAC(
      folded_header, rewrite_conv, THM_LIST());
  gnode pulled_shape = EXISTS_PULL_SLTAC(normalized);
  gnode witnessed_shape = LIST_EXISTS_SLTAC(
      pulled_shape, TERM_LIST(`fn_:cm_function_d`,
        `rest_:(cm_function_d)list`));
  gnode opened_target = CONV_WITH_ASMP_SLTAC(
      witnessed_shape, rewrite_conv,
      THM_LIST(get_cm_function_list_rep_def()));
  gnode pulled_bodies = EXISTS_PULL_SLTAC(opened_target);
  gnode witnessed_bodies = EXISTS_SLTAC(
      pulled_bodies, `(body_:int) :: (body_rest_:(int)list)`);
  gnode cleaned = CLEAN_SLTAC(witnessed_bodies);
  AUTO_FRAME_SLTAC(cleaned);
  return gnode_prove(root);
}
PROOF thm cm_function_list_nonnull_shape =
    cm_prove_function_list_nonnull_shape();

PROOF static thm cm_prove_function_list_null_shape(void) {
  gnode root = gnode_new_with_ccl(
      `!(pointer:int) (functions:(cm_function_d)list).
       pointer == 0i ==>
       (cm_function_list_rep pointer functions |--
        fact(functions == []) **
        cm_function_list_rep pointer functions)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list initialized = SL_MODE(leaf, "H");
  gnode_list cases = CASES_TAC(initialized[0],
      `functions:(cm_function_d)list`, "Hfunctions");
  gnode nil = CONV_WITH_ASMP_SLTAC(
      cases[0], rewrite_conv,
      THM_LIST(get_cm_function_list_rep_def(),
        get_cm_function_header_list_rep_def(),
        get_cm_function_body_list_rep_def()));
  if (IS_NULL(nil->solved)) {
    gnode_list destructed = AUTO_HANT_DESTRUCT_SLTAC(nil);
    for (size_t i = 0; i < vector_size(destructed); ++i) {
      gnode facts = AUTO_INTRO_FACT_SLTAC(destructed[i]);
      gnode pulled = EXISTS_PULL_SLTAC(facts);
      gnode witnessed = EXISTS_SLTAC(
          pulled, `[]:(int)list`);
      gnode cleaned = CLEAN_SLTAC(witnessed);
      gnode_list pure = PURE_SLTAC(cleaned);
      ACCEPT_TAC(pure[0], refl_rule(`[]:(int)list`));
      ACCEPT_TAC(pure[1], refl_rule(`[]:(int)list`));
      AUTO_FRAME_SLTAC(pure[2]);
    }
  }
  gnode cons_model = HANT_CONV_SLTAC(
      cases[1],
      rewrite_conv(THM_LIST(assume_rule(
        `(functions:(cm_function_d)list) ==
         (a0:cm_function_d) :: (a1:(cm_function_d)list)`))),
      CONST_STRING_LIST("H"));
  gnode split_open = AUTO_HANT_APPLY_SLTAC(
      cons_model, "H",
      specl_rule(TERM_LIST(`pointer:int`,
        `(a0:cm_function_d) :: (a1:(cm_function_d)list)`),
        get_cm_function_split_open()));
  gnode bodies =
      HANT_EXISTS_SLTAC(split_open, "H", "bodies_");
  gnode separated = HANT_SEP_SLTAC(
      bodies, "H", "Hheader", "Hbody");
  gnode opened = HANT_CONV_SLTAC(
      separated,
      rewrite_conv(THM_LIST(
        get_cm_function_header_list_rep_def())),
      CONST_STRING_LIST("Hheader"));
  gnode zp = HANT_EXISTS_SLTAC(opened, "Hheader", "zp_");
  gnode zl = HANT_EXISTS_SLTAC(zp, "Hheader", "zl_");
  gnode zb = HANT_EXISTS_SLTAC(zl, "Hheader", "zb_");
  gnode zn = HANT_EXISTS_SLTAC(zb, "Hheader", "zn_");
  gnode body_rest =
      HANT_EXISTS_SLTAC(zn, "Hheader", "body_rest_");
  gnode header_parts = HANT_SEP_SLTAC(
      body_rest, "Hheader", "Hfact", "Hrest");
  gnode contradiction = HANT_CONV_SLTAC(
      header_parts,
      rewrite_conv(THM_LIST(
        assume_rule(`(pointer:int) == 0i`))),
      CONST_STRING_LIST("Hfact"));
  CONTR_SLTAC(contradiction, "Hfact");
  return gnode_prove(root);
}
PROOF thm cm_function_list_null_shape =
    cm_prove_function_list_null_shape();

PROOF static thm cm_prove_function_code_count_positive(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) fid.
         1i <= cm_function_code_count p fid`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term actual =
      `inth (fid:int) (cm_program_functions (p:cm_program))`;
  term prologue =
      `cm_prologue_heights ${actual:cm_function_d}`;
  term statement =
      `cm_stmt_heights (p:cm_program) (fid:int)
         (cm_function_body ${actual:cm_function_d})`;
  thm prologue_nonnegative = ispec_rule(
      prologue, get_theorem_by_name("ILENGTH_NONNEG"));
  thm statement_nonnegative = ispec_rule(
      statement, get_theorem_by_name("ILENGTH_NONNEG"));
  thm height_shape = apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_function_heights_def, cm_return_heights_def,
        get_theorem_by_name("ILENGTH_APPEND"),
        get_theorem_by_name("ILENGTH_DEF"))),
      `ilength
         (cm_function_heights (p:cm_program) (fid:int)
           ${actual:cm_function_d})`);
  thm count_exact = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, actual),
      cm_function_height_length);
  thm facts = conj_rule(prologue_nonnegative,
      conj_rule(statement_nonnegative,
        conj_rule(height_shape, count_exact)));
  ACCEPT_TAC(leaf, mp_rule(int_arith_rule(mk_imp(
      concl(facts), goal_ccl(leaf->g))), facts));
  return gnode_prove(root);
}
PROOF thm cm_function_code_count_positive =
    cm_prove_function_code_count_positive();

PROOF static thm cm_prove_functions_length_le_code_size(void) {
  gnode root = gnode_new_with_ccl(
      `!(functions:(cm_function_d)list).
         !(p:cm_program) index.
         ilength functions <=
           cm_functions_code_size p functions index`);
  gnode_list cases =
      INDUCT_TAC(root, `functions:(cm_function_d)list`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    gnode reduced = CONV_TAC(leaf,
        reduce_rewrite_conv(THM_LIST(
          get_cm_functions_code_size_def(),
          get_theorem_by_name("ILENGTH_DEF"))));
    if (i != 0 && IS_NULL(reduced->solved)) {
      thm ih = assume_rule(
          `!(p:cm_program) index.
             ilength (a1:(cm_function_d)list) <=
               cm_functions_code_size p a1 index`);
      thm tail = specl_rule(TERM_LIST(
          `p:cm_program`, `(index:int) + 1i`), ih);
      thm head = specl_rule(TERM_LIST(
          `p:cm_program`, `index:int`),
          cm_function_code_count_positive);
      thm facts = conj_rule(head, tail);
      ACCEPT_TAC(reduced, mp_rule(int_arith_rule(mk_imp(
          concl(facts), goal_ccl(reduced->g))), facts));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_functions_length_le_code_size =
    cm_prove_functions_length_le_code_size();

PROOF static thm cm_prove_functions_code_size_nonnegative(void) {
  gnode root = gnode_new_with_ccl(
      `!(functions:(cm_function_d)list).
         !(p:cm_program) index.
         0i <= cm_functions_code_size p functions index`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm length_nonnegative = ispec_rule(
      `functions:(cm_function_d)list`,
      get_theorem_by_name("ILENGTH_NONNEG"));
  thm length_bound = specl_rule(TERM_LIST(
      `functions:(cm_function_d)list`,
      `p:cm_program`, `index:int`),
      cm_functions_length_le_code_size);
  thm facts = conj_rule(length_nonnegative, length_bound);
  ACCEPT_TAC(leaf, mp_rule(int_arith_rule(mk_imp(
      concl(facts), goal_ccl(leaf->g))), facts));
  return gnode_prove(root);
}
PROOF thm cm_functions_code_size_nonnegative =
    cm_prove_functions_code_size_nonnegative();

PROOF static thm cm_prove_encoded_leaf_size(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type).
         cm_type_code_wf ty ==>
         cm_rep_leaf_size (cm_type_encode ty) == cm_leaf_size ty`);
  gnode_list cases = INDUCT_TAC(root, `ty:cm_type`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode introduced = AUTO_INTROS_TAC(cases[i]);
    gnode_list frontier = AUTO_ASMP_DESTRUCT_TAC(introduced);
    for (size_t j = 0; j < vector_size(frontier); ++j) {
      gnode reduced = CONV_WITH_ASMP_TAC(
          frontier[j], reduce_rewrite_conv, THM_LIST(
            get_cm_rep_leaf_size_def(), get_cm_type_encode_def(),
            get_cm_type_depth_def(), get_cm_type_base_code_def(),
            get_cm_type_code_wf_def(), get_cm_leaf_size_def()));
      if (IS_NULL(reduced->solved)) {
        labeled_term_list assumptions = goal_lasmps(reduced->g);
        thm facts;
        if (i == 3) {
          thm wf = conv_rule(reduce_rewrite_conv(THM_LIST(
              get_cm_type_code_wf_def())),
              assume_rule(assumptions[
                vector_size(assumptions) - 1].tm));
          thm depth = spec_rule(`a:cm_type`,
              get_cm_type_depth_nonneg());
          thm base = mp_rule(spec_rule(`a:cm_type`,
              get_cm_type_base_range()), wf);
          facts = conj_rule(depth, base);
        } else {
          facts = conv_rule(reduce_rewrite_conv(THM_LIST(
              get_cm_type_code_wf_def())),
              assume_rule(assumptions[0].tm));
          for (size_t k = 1; k < vector_size(assumptions); ++k) {
            thm next = conv_rule(reduce_rewrite_conv(THM_LIST(
                get_cm_type_code_wf_def())),
                assume_rule(assumptions[k].tm));
            facts = conj_rule(facts, next);
          }
        }
        ACCEPT_TAC(reduced, mp_rule(int_arith_rule(mk_imp(
            concl(facts), goal_ccl(reduced->g))), facts));
      }
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_encoded_leaf_size =
    cm_prove_encoded_leaf_size();

PROOF static thm cm_prove_nonstruct_type_size(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (ty:cm_type).
         ~(cm_is_struct ty) ==>
         cm_type_size structs ty == cm_leaf_size ty`);
  gnode with_structs = GEN_TAC(root, "structs");
  gnode_list cases = INDUCT_TAC(with_structs, `ty:cm_type`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    if (i == 2) {
      thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_cm_is_struct_def())), assume_rule(
            `~(cm_is_struct (CMStructTy (a:int)))`));
      CONTR_TAC(leaf, impossible);
    } else {
      CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
          get_cm_type_size_def(), get_cm_leaf_size_def())));
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_nonstruct_type_size =
    cm_prove_nonstruct_type_size();

PROOF static thm cm_prove_rep_member_size_matches(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (slot:cm_slot_d).
         cm_slot_wf structs slot ==>
         cm_rep_member_size slot == cm_slot_size structs slot`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm opened = conv_rule(rewrite_conv(THM_LIST(
      get_cm_slot_wf_def(), get_cm_scalar_type_def())),
      assume_rule(
        `cm_slot_wf (structs:(cm_struct_d)list)
          (slot:cm_slot_d)`));
  thm code_wf = mp_rule(taut_rule(mk_imp(concl(opened),
      `cm_type_code_wf (cm_slot_ty (slot:cm_slot_d))`)), opened);
  thm not_struct = mp_rule(taut_rule(mk_imp(concl(opened),
      `~(cm_is_struct (cm_slot_ty (slot:cm_slot_d)))`)), opened);
  thm encoded = mp_rule(spec_rule(
      `cm_slot_ty (slot:cm_slot_d)`, cm_encoded_leaf_size), code_wf);
  thm semantic = mp_rule(specl_rule(TERM_LIST(
      `structs:(cm_struct_d)list`,
      `cm_slot_ty (slot:cm_slot_d)`), cm_nonstruct_type_size),
      not_struct);
  ACCEPT_TAC(leaf, by_rewrite(goal_ccl(leaf->g), THM_LIST(
      get_cm_rep_member_size_def(),
      get_cm_rep_code_slot_size_def(),
      get_cm_slot_size_def(), encoded, semantic)));
  return gnode_prove(root);
}
PROOF thm cm_rep_member_size_matches =
    cm_prove_rep_member_size_matches();
PROOF static thm cm_prove_rep_struct_member_size_matches(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (slot:cm_slot_d).
         cm_slot_wf structs slot ==>
         cm_rep_member_size slot == cm_struct_member_size slot`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm opened = conv_rule(rewrite_conv(THM_LIST(
      get_cm_slot_wf_def(), get_cm_scalar_type_def())),
      assume_rule(
        `cm_slot_wf (structs:(cm_struct_d)list)
          (slot:cm_slot_d)`));
  thm code_wf = mp_rule(taut_rule(mk_imp(concl(opened),
      `cm_type_code_wf (cm_slot_ty (slot:cm_slot_d))`)), opened);
  thm encoded = mp_rule(spec_rule(
      `cm_slot_ty (slot:cm_slot_d)`, cm_encoded_leaf_size), code_wf);
  ACCEPT_TAC(leaf, by_rewrite(goal_ccl(leaf->g), THM_LIST(
      get_cm_rep_member_size_def(),
      get_cm_rep_code_slot_size_def(),
      get_cm_struct_member_size_def(), encoded)));
  return gnode_prove(root);
}
PROOF thm cm_rep_struct_member_size_matches =
    cm_prove_rep_struct_member_size_matches();

PROOF static thm cm_prove_slots_wf_head(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (head:cm_slot_d)
          (tail:(cm_slot_d)list).
         cm_slots_wf structs (head :: tail) ==>
         cm_slot_wf structs head`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm all_wf = conv_rule(rewrite_conv(THM_LIST(
      get_cm_slots_wf_def())), assume_rule(
        `cm_slots_wf (structs:(cm_struct_d)list)
          ((head:cm_slot_d) :: (tail:(cm_slot_d)list))`));
  thm tail_nonnegative = ispec_rule(
      `tail:(cm_slot_d)list`, get_theorem_by_name("ILENGTH_NONNEG"));
  thm head_bound = by_defs_arith(
      `0i < ilength ((head:cm_slot_d) :: (tail:(cm_slot_d)list))`,
      THM_LIST(get_theorem_by_name("ILENGTH_DEF")),
      THM_LIST(tail_nonnegative));
  thm result = match_mp_rule(match_mp_rule(
      spec_rule(`0i`, all_wf), int_arith_rule(`0i <= 0i`)),
      head_bound);
  ACCEPT_TAC(leaf, conv_rule(rewrite_conv(THM_LIST(
      ispecl_rule(TERM_LIST(
        `head:cm_slot_d`, `tail:(cm_slot_d)list`),
        cm_inth_zero_cons))), result));
  return gnode_prove(root);
}
PROOF thm cm_slots_wf_head = cm_prove_slots_wf_head();

PROOF static thm cm_prove_slots_wf_tail(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (head:cm_slot_d)
          (tail:(cm_slot_d)list).
         cm_slots_wf structs (head :: tail) ==>
         cm_slots_wf structs tail`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm all_wf = conv_rule(rewrite_conv(THM_LIST(
      get_cm_slots_wf_def())), assume_rule(
        `cm_slots_wf (structs:(cm_struct_d)list)
          ((head:cm_slot_d) :: (tail:(cm_slot_d)list))`));
  gnode opened = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      get_cm_slots_wf_def())));
  gnode with_index = GEN_TAC(opened, "tail_index");
  gnode tail_leaf = AUTO_INTROS_TAC(with_index);
  thm tail_nonnegative = assume_rule(`0i <= (tail_index:int)`);
  thm tail_upper = assume_rule(
      `(tail_index:int) < ilength (tail:(cm_slot_d)list)`);
  thm full_lower = mp_rule(int_arith_rule(
      `0i <= (tail_index:int) ==> 0i <= tail_index + 1i`),
      tail_nonnegative);
  thm normalized_full_upper = mp_rule(int_arith_rule(mk_imp(
      concl(tail_upper),
      `(tail_index:int) + 1i <
       1i + ilength (tail:(cm_slot_d)list)`)), tail_upper);
  thm full_upper = eq_mp_rule(sym_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_theorem_by_name("ILENGTH_DEF"))),
      `(tail_index:int) + 1i < ilength
        ((head:cm_slot_d) :: (tail:(cm_slot_d)list))`)),
      normalized_full_upper);
  thm full_wf = match_mp_rule(match_mp_rule(
      spec_rule(`(tail_index:int) + 1i`, all_wf), full_lower),
      full_upper);
  thm one = mp_rule(int_arith_rule(
      `0i <= (tail_index:int) ==> 1i <= tail_index + 1i`),
      tail_nonnegative);
  thm at_tail = mp_rule(ispecl_rule(TERM_LIST(
      `head:cm_slot_d`, `tail:(cm_slot_d)list`,
      `(tail_index:int) + 1i`), cm_inth_cons_tail), one);
  thm index_exact = int_arith_rule(
      `((tail_index:int) + 1i) - 1i == tail_index`);
  ACCEPT_TAC(tail_leaf, conv_rule(reduce_rewrite_conv(
      THM_LIST(at_tail, index_exact)), full_wf));
  return gnode_prove(root);
}
PROOF thm cm_slots_wf_tail = cm_prove_slots_wf_tail();

PROOF static thm cm_prove_rep_members_size_matches(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (slots:(cm_slot_d)list).
         cm_slots_wf structs slots ==>
         cm_rep_members_size slots == cm_slots_size structs slots`);
  gnode with_structs = GEN_TAC(root, "structs");
  gnode_list cases = INDUCT_TAC(with_structs, `slots:(cm_slot_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_rep_members_size_def(), get_cm_slots_size_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm wf = assume_rule(
        `cm_slots_wf (structs:(cm_struct_d)list)
          ((a0:cm_slot_d) :: (a1:(cm_slot_d)list))`);
    thm head_wf = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`, `a0:cm_slot_d`,
        `a1:(cm_slot_d)list`), cm_slots_wf_head), wf);
    thm tail_wf = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`, `a0:cm_slot_d`,
        `a1:(cm_slot_d)list`), cm_slots_wf_tail), wf);
    thm head = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`, `a0:cm_slot_d`),
        cm_rep_member_size_matches), head_wf);
    thm tail = mp_rule(assume_rule(
        `cm_slots_wf (structs:(cm_struct_d)list)
           (a1:(cm_slot_d)list) ==>
         cm_rep_members_size a1 == cm_slots_size structs a1`),
        tail_wf);
    ACCEPT_TAC(leaf, by_rewrite(goal_ccl(leaf->g), THM_LIST(
        get_cm_rep_members_size_def(), get_cm_slots_size_def(),
        head, tail)));
  }
  return gnode_prove(root);
}
PROOF thm cm_rep_members_size_matches =
    cm_prove_rep_members_size_matches();
PROOF static thm cm_prove_rep_struct_members_size_matches(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (slots:(cm_slot_d)list).
         cm_slots_wf structs slots ==>
         cm_rep_members_size slots == cm_struct_slots_size slots`);
  gnode with_structs = GEN_TAC(root, "structs");
  gnode_list cases = INDUCT_TAC(with_structs, `slots:(cm_slot_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_rep_members_size_def(),
        get_cm_struct_slots_size_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm wf = assume_rule(
        `cm_slots_wf (structs:(cm_struct_d)list)
          ((a0:cm_slot_d) :: (a1:(cm_slot_d)list))`);
    thm head_wf = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`, `a0:cm_slot_d`,
        `a1:(cm_slot_d)list`), cm_slots_wf_head), wf);
    thm tail_wf = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`, `a0:cm_slot_d`,
        `a1:(cm_slot_d)list`), cm_slots_wf_tail), wf);
    thm head = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`, `a0:cm_slot_d`),
        cm_rep_struct_member_size_matches), head_wf);
    thm tail = mp_rule(assume_rule(
        `cm_slots_wf (structs:(cm_struct_d)list)
           (a1:(cm_slot_d)list) ==>
         cm_rep_members_size a1 == cm_struct_slots_size a1`),
        tail_wf);
    ACCEPT_TAC(leaf, by_rewrite(goal_ccl(leaf->g), THM_LIST(
        get_cm_rep_members_size_def(),
        get_cm_struct_slots_size_def(), head, tail)));
  }
  return gnode_prove(root);
}
PROOF thm cm_rep_struct_members_size_matches =
    cm_prove_rep_struct_members_size_matches();
PROOF static thm cm_prove_rep_struct_size_at(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (sid:int).
         0i <= sid ==> sid < ilength structs ==>
         cm_rep_struct_size structs sid ==
           cm_rep_members_size
             (cm_struct_members (inth sid structs))`);
  gnode_list cases = INDUCT_TAC(root,
      `structs:(cm_struct_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm upper = pure_rewrite_rule(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF")), assume_rule(
          `(sid:int) < ilength ([]:(cm_struct_d)list)`));
    CONTR_TAC(leaf, mp_rule(mp_rule(int_arith_rule(
        `0i <= (sid:int) ==> sid < 0i ==> F`),
        assume_rule(`0i <= (sid:int)`)), upper));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    gnode_list sid_cases =
        BOOL_CASES_TAC(leaf, `(sid:int) == 0i`, "Hsid");
    {
      CONV_WITH_ASMP_TAC(sid_cases[0], reduce_rewrite_conv,
          THM_LIST(get_cm_rep_struct_size_def(),
            get_theorem_by_name("INTH_DEF"),
            get_theorem_by_name("NUM_OF_INT_OF_NUM"),
            get_theorem_by_name("NTH_DEF")));
    }
    {
      thm lower = mp_rule(mp_rule(int_arith_rule(
          `0i <= (sid:int) ==> ~(sid == 0i) ==> 1i <= sid`),
          assume_rule(`0i <= (sid:int)`)),
          assume_rule(`~((sid:int) == 0i)`));
      thm length_step = pure_rewrite_rule(THM_LIST(
          get_theorem_by_name("ILENGTH_DEF")), assume_rule(
            `(sid:int) <
             ilength ((a0:cm_struct_d) :: (a1:(cm_struct_d)list))`));
      thm tail_bound = mp_rule(int_arith_rule(
          `(sid:int) < 1i + ilength (a1:(cm_struct_d)list) ==>
           sid - 1i < ilength a1`), length_step);
      thm tail_nonnegative = mp_rule(int_arith_rule(
          `1i <= (sid:int) ==> 0i <= sid - 1i`), lower);
      thm lookup = mp_rule(ispecl_rule(TERM_LIST(
          `a0:cm_struct_d`, `a1:(cm_struct_d)list`, `sid:int`),
          cm_inth_cons_tail), lower);
      thm result = spec_rule(`(sid:int) - 1i`, assume_rule(
          `!sid. 0i <= sid ==>
             sid < ilength (a1:(cm_struct_d)list) ==>
             cm_rep_struct_size a1 sid ==
               cm_rep_members_size
                 (cm_struct_members (inth sid a1))`));
      result = mp_rule(mp_rule(result, tail_nonnegative), tail_bound);
      gnode reduced = CONV_WITH_ASMP_TAC(
          sid_cases[1], reduce_rewrite_conv, THM_LIST(
            get_cm_rep_struct_size_def(), lookup));
      if (IS_NULL(reduced->solved)) {
        ACCEPT_TAC(reduced, result);
      }
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_rep_struct_size_at =
    cm_prove_rep_struct_size_at();

PROOF static thm cm_prove_rep_struct_size_matches(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (sid:int).
         0i <= sid ==> sid < ilength structs ==>
         cm_slots_wf structs
           (cm_struct_members (inth sid structs)) ==>
         cm_rep_struct_size structs sid ==
           cm_struct_size structs sid`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm concrete = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `structs:(cm_struct_d)list`, `sid:int`),
      cm_rep_struct_size_at),
      assume_rule(`0i <= (sid:int)`)),
      assume_rule(`(sid:int) < ilength (structs:(cm_struct_d)list)`));
  thm members = mp_rule(specl_rule(TERM_LIST(
      `structs:(cm_struct_d)list`,
      `cm_struct_members
        (inth (sid:int) (structs:(cm_struct_d)list))`),
      cm_rep_struct_members_size_matches), assume_rule(
        `cm_slots_wf (structs:(cm_struct_d)list)
          (cm_struct_members (inth (sid:int) structs))`));
  thm semantic = by_rewrite(
      `cm_struct_size (structs:(cm_struct_d)list) (sid:int) ==
       cm_struct_slots_size
         (cm_struct_members (inth sid structs))`,
      THM_LIST(get_cm_struct_size_def(),
        eqt_intro_rule(conj_rule(
          assume_rule(`0i <= (sid:int)`),
          assume_rule(
            `(sid:int) < ilength (structs:(cm_struct_d)list)`)))));
  ACCEPT_TAC(leaf, trans_rule(concrete,
      trans_rule(members, sym_rule(semantic))));
  return gnode_prove(root);
}
PROOF thm cm_rep_struct_size_matches =
    cm_prove_rep_struct_size_matches();
PROOF static thm cm_prove_rep_type_size_matches(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (ty:cm_type).
         cm_type_code_wf ty ==>
         cm_type_refs structs ty ==>
         (!(i:int). 0i <= i ==> i < ilength structs ==>
            cm_struct_wf structs (inth i structs)) ==>
         cm_rep_type_size structs (cm_type_encode ty) ==
           cm_type_size structs ty`);
  gnode with_structs = GEN_TAC(root, "structs");
  gnode_list cases = INDUCT_TAC(with_structs, `ty:cm_type`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_rep_type_size_def(), get_cm_type_encode_def(),
        get_cm_type_depth_def(), get_cm_type_base_code_def(),
        get_cm_type_size_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_rep_type_size_def(), get_cm_type_encode_def(),
        get_cm_type_depth_def(), get_cm_type_base_code_def(),
        get_cm_type_size_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[2]);
    thm code_wf = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_type_code_wf_def())), assume_rule(
          `cm_type_code_wf (CMStructTy (a:int))`));
    thm refs = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_type_refs_def())), assume_rule(
          `cm_type_refs (structs:(cm_struct_d)list)
            (CMStructTy (a:int))`));
    thm selected = mp_rule(mp_rule(spec_rule(`a:int`, assume_rule(
        `!(i:int). 0i <= i ==>
           i < ilength (structs:(cm_struct_d)list) ==>
           cm_struct_wf structs (inth i structs)`)),
        conjunct1_rule(refs)), conjunct2_rule(refs));
    thm opened = conv_rule(rewrite_conv(THM_LIST(
        get_cm_struct_wf_def())), selected);
    thm slots_wf = conjunct1_rule(conjunct2_rule(opened));
    thm matched = mp_rule(mp_rule(mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`, `a:int`),
        cm_rep_struct_size_matches),
        conjunct1_rule(refs)), conjunct2_rule(refs)), slots_wf);
    thm not_pointer = mp_rule(mp_rule(int_arith_rule(
        `0i <= (a:int) ==>
         a < 1022i ==>
         ~(1024i <= 0i + a + 2i)`),
        conjunct1_rule(code_wf)), conjunct2_rule(code_wf));
    thm not_int = mp_rule(int_arith_rule(
        `0i <= (a:int) ==> ~(0i + a + 2i == 0i)`),
        conjunct1_rule(code_wf));
    thm not_char = mp_rule(int_arith_rule(
        `0i <= (a:int) ==> ~(0i + a + 2i == 1i)`),
        conjunct1_rule(code_wf));
    gnode reduced = CONV_WITH_ASMP_TAC(leaf,
        reduce_rewrite_conv, THM_LIST(
          get_cm_rep_type_size_def(), get_cm_type_encode_def(),
          get_cm_type_depth_def(), get_cm_type_base_code_def(),
          get_cm_type_size_def(), code_wf, refs));
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, by_rewrite(goal_ccl(reduced->g), THM_LIST(
          eqf_intro_rule(not_pointer), eqf_intro_rule(not_int),
          eqf_intro_rule(not_char),
          get_theorem_by_name("COND_CLAUSES"),
          int_arith_rule(`(0i + (a:int) + 2i) - 2i == a`),
          matched)));
    }
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[3]);
    thm wf = assume_rule(
        `cm_type_code_wf (CMPtrTy (a:cm_type))`);
    thm child_wf = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_type_code_wf_def())), wf);
    thm bounds = mp_rule(spec_rule(
        `a:cm_type`, get_cm_type_base_range()), child_wf);
    thm shape = by_rewrite(
        `cm_type_encode (CMPtrTy (a:cm_type)) ==
         1024i * (1i + cm_type_depth a) +
           cm_type_base_code a`,
        THM_LIST(get_cm_type_encode_def(), get_cm_type_depth_def(),
          get_cm_type_base_code_def()));
    thm encoded_pointer = mp_rule(mp_rule(mp_rule(int_arith_rule(
        `0i <= cm_type_depth (a:cm_type) ==>
         0i <= cm_type_base_code a ==>
         cm_type_encode (CMPtrTy a) ==
           1024i * (1i + cm_type_depth a) +
             cm_type_base_code a ==>
         1024i <= cm_type_encode (CMPtrTy a)`),
        spec_rule(`a:cm_type`, get_cm_type_depth_nonneg())),
        conjunct1_rule(bounds)), shape);
    ACCEPT_TAC(leaf, by_rewrite(goal_ccl(leaf->g), THM_LIST(
        get_cm_rep_type_size_def(), get_cm_type_size_def(),
        eqt_intro_rule(encoded_pointer))));
  }
  return gnode_prove(root);
}
PROOF thm cm_rep_type_size_matches =
    cm_prove_rep_type_size_matches();
PROOF static thm cm_prove_type_encode_nonnegative(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type).
         cm_type_code_wf ty ==> 0i <= cm_type_encode ty`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm wf = assume_rule(`cm_type_code_wf (ty:cm_type)`);
  thm bounds = mp_rule(spec_rule(
      `ty:cm_type`, get_cm_type_base_range()), wf);
  thm result = mp_rule(mp_rule(mp_rule(int_arith_rule(
      `0i <= cm_type_depth (ty:cm_type) ==>
       0i <= cm_type_base_code ty ==>
       cm_type_encode ty ==
         1024i * cm_type_depth ty + cm_type_base_code ty ==>
       0i <= cm_type_encode ty`),
      spec_rule(`ty:cm_type`, get_cm_type_depth_nonneg())),
      conjunct1_rule(bounds)), get_cm_type_encode_def());
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_type_encode_nonnegative =
    cm_prove_type_encode_nonnegative();

PROOF static thm cm_prove_rep_member_prefix_matches(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (slots:(cm_slot_d)list)
          (index:int).
         cm_slots_wf structs slots ==>
         cm_rep_member_prefix slots index ==
           cm_slots_prefix structs slots index`);
  gnode with_structs = GEN_TAC(root, "structs");
  gnode_list cases = INDUCT_TAC(with_structs, `slots:(cm_slot_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_rep_member_prefix_def(), get_cm_slots_prefix_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm wf = assume_rule(
        `cm_slots_wf (structs:(cm_struct_d)list)
          ((a0:cm_slot_d) :: (a1:(cm_slot_d)list))`);
    thm head_wf = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`, `a0:cm_slot_d`,
        `a1:(cm_slot_d)list`), cm_slots_wf_head), wf);
    thm tail_wf = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`, `a0:cm_slot_d`,
        `a1:(cm_slot_d)list`), cm_slots_wf_tail), wf);
    thm head = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`, `a0:cm_slot_d`),
        cm_rep_member_size_matches), head_wf);
    thm tail = mp_rule(spec_rule(`(index:int) - 1i`,
        assume_rule(
          `!index.
             cm_slots_wf (structs:(cm_struct_d)list)
               (a1:(cm_slot_d)list) ==>
             cm_rep_member_prefix a1 index ==
               cm_slots_prefix structs a1 index`)), tail_wf);
    ACCEPT_TAC(leaf, by_rewrite(goal_ccl(leaf->g), THM_LIST(
        get_cm_rep_member_prefix_def(), get_cm_slots_prefix_def(),
        head, tail)));
  }
  return gnode_prove(root);
}
PROOF thm cm_rep_member_prefix_matches =
    cm_prove_rep_member_prefix_matches();
PROOF static thm cm_prove_rep_struct_member_prefix_slots_matches(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (slots:(cm_slot_d)list)
          (index:int).
         cm_slots_wf structs slots ==>
         cm_rep_member_prefix slots index ==
           cm_member_offset_slots slots index`);
  gnode with_structs = GEN_TAC(root, "structs");
  gnode_list cases = INDUCT_TAC(with_structs, `slots:(cm_slot_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_rep_member_prefix_def(),
        get_cm_member_offset_slots_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm wf = assume_rule(
        `cm_slots_wf (structs:(cm_struct_d)list)
          ((a0:cm_slot_d) :: (a1:(cm_slot_d)list))`);
    thm head_wf = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`, `a0:cm_slot_d`,
        `a1:(cm_slot_d)list`), cm_slots_wf_head), wf);
    thm tail_wf = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`, `a0:cm_slot_d`,
        `a1:(cm_slot_d)list`), cm_slots_wf_tail), wf);
    thm head = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`, `a0:cm_slot_d`),
        cm_rep_struct_member_size_matches), head_wf);
    thm tail = mp_rule(spec_rule(`(index:int) - 1i`,
        assume_rule(
          `!index.
             cm_slots_wf (structs:(cm_struct_d)list)
               (a1:(cm_slot_d)list) ==>
             cm_rep_member_prefix a1 index ==
               cm_member_offset_slots a1 index`)), tail_wf);
    ACCEPT_TAC(leaf, by_rewrite(goal_ccl(leaf->g), THM_LIST(
        get_cm_rep_member_prefix_def(),
        get_cm_member_offset_slots_def(), head, tail)));
  }
  return gnode_prove(root);
}
PROOF thm cm_rep_struct_member_prefix_slots_matches =
    cm_prove_rep_struct_member_prefix_slots_matches();

PROOF static thm cm_prove_rep_struct_member_prefix_at(void) {
  gnode root = gnode_new_with_ccl(
      `!(index:int) (structs:(cm_struct_d)list) (sid:int).
         0i <= sid ==> sid < ilength structs ==>
         cm_rep_struct_member_prefix structs sid index ==
           cm_rep_member_prefix
             (cm_struct_members (inth sid structs)) index`);
  gnode with_index = GEN_TAC(root, "index");
  gnode_list cases = INDUCT_TAC(with_index,
      `structs:(cm_struct_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm upper = pure_rewrite_rule(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF")), assume_rule(
          `(sid:int) < ilength ([]:(cm_struct_d)list)`));
    CONTR_TAC(leaf, mp_rule(mp_rule(int_arith_rule(
        `0i <= (sid:int) ==> sid < 0i ==> F`),
        assume_rule(`0i <= (sid:int)`)), upper));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    gnode_list sid_cases =
        BOOL_CASES_TAC(leaf, `(sid:int) == 0i`, "Hsid");
    {
      CONV_WITH_ASMP_TAC(sid_cases[0], reduce_rewrite_conv,
          THM_LIST(get_cm_rep_struct_member_prefix_def(),
            get_theorem_by_name("INTH_DEF"),
            get_theorem_by_name("NUM_OF_INT_OF_NUM"),
            get_theorem_by_name("NTH_DEF")));
    }
    {
      thm lower = mp_rule(mp_rule(int_arith_rule(
          `0i <= (sid:int) ==> ~(sid == 0i) ==> 1i <= sid`),
          assume_rule(`0i <= (sid:int)`)),
          assume_rule(`~((sid:int) == 0i)`));
      thm length_step = pure_rewrite_rule(THM_LIST(
          get_theorem_by_name("ILENGTH_DEF")), assume_rule(
            `(sid:int) <
             ilength ((a0:cm_struct_d) :: (a1:(cm_struct_d)list))`));
      thm tail_bound = mp_rule(int_arith_rule(
          `(sid:int) < 1i + ilength (a1:(cm_struct_d)list) ==>
           sid - 1i < ilength a1`), length_step);
      thm tail_nonnegative = mp_rule(int_arith_rule(
          `1i <= (sid:int) ==> 0i <= sid - 1i`), lower);
      thm lookup = mp_rule(ispecl_rule(TERM_LIST(
          `a0:cm_struct_d`, `a1:(cm_struct_d)list`, `sid:int`),
          cm_inth_cons_tail), lower);
      thm result = spec_rule(`(sid:int) - 1i`, assume_rule(
          `!sid.
             0i <= sid ==>
             sid < ilength (a1:(cm_struct_d)list) ==>
             cm_rep_struct_member_prefix a1 sid (index:int) ==
               cm_rep_member_prefix
                 (cm_struct_members (inth sid a1)) index`));
      result = mp_rule(mp_rule(result, tail_nonnegative), tail_bound);
      gnode reduced = CONV_WITH_ASMP_TAC(
          sid_cases[1], reduce_rewrite_conv, THM_LIST(
            get_cm_rep_struct_member_prefix_def(), lookup));
      if (IS_NULL(reduced->solved)) {
        ACCEPT_TAC(reduced, result);
      }
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_rep_struct_member_prefix_at =
    cm_prove_rep_struct_member_prefix_at();

PROOF static thm cm_prove_rep_struct_member_prefix_matches(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (sid:int) (index:int).
         0i <= sid ==> sid < ilength structs ==>
         cm_slots_wf structs
           (cm_struct_members (inth sid structs)) ==>
         cm_rep_struct_member_prefix structs sid index ==
           cm_member_offset structs sid index`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm concrete = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `index:int`, `structs:(cm_struct_d)list`, `sid:int`),
      cm_rep_struct_member_prefix_at),
      assume_rule(`0i <= (sid:int)`)),
      assume_rule(`(sid:int) < ilength (structs:(cm_struct_d)list)`));
  thm members = mp_rule(specl_rule(TERM_LIST(
      `structs:(cm_struct_d)list`,
      `cm_struct_members
        (inth (sid:int) (structs:(cm_struct_d)list))`,
      `index:int`),
      cm_rep_struct_member_prefix_slots_matches), assume_rule(
        `cm_slots_wf (structs:(cm_struct_d)list)
          (cm_struct_members (inth (sid:int) structs))`));
  thm semantic = by_rewrite(
      `cm_member_offset (structs:(cm_struct_d)list)
         (sid:int) (index:int) ==
       cm_member_offset_slots
         (cm_struct_members (inth sid structs)) index`,
      THM_LIST(get_cm_member_offset_def(),
        eqt_intro_rule(conj_rule(
          assume_rule(`0i <= (sid:int)`),
          assume_rule(
            `(sid:int) < ilength (structs:(cm_struct_d)list)`)))));
  ACCEPT_TAC(leaf, trans_rule(concrete,
      trans_rule(members, sym_rule(semantic))));
  return gnode_prove(root);
}
PROOF thm cm_rep_struct_member_prefix_matches =
    cm_prove_rep_struct_member_prefix_matches();


PROOF static thm cm_prove_rep_global_size_matches(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (global:cm_global_d).
         cm_global_wf structs global ==>
         cm_rep_global_size global == cm_global_size structs global`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm opened = conv_rule(rewrite_conv(THM_LIST(
      get_cm_global_wf_def(), get_cm_scalar_type_def())),
      assume_rule(
        `cm_global_wf (structs:(cm_struct_d)list)
          (global:cm_global_d)`));
  thm code_wf = mp_rule(taut_rule(mk_imp(concl(opened),
      `cm_type_code_wf (cm_global_ty (global:cm_global_d))`)),
      opened);
  thm not_struct = mp_rule(taut_rule(mk_imp(concl(opened),
      `~(cm_is_struct (cm_global_ty (global:cm_global_d)))`)),
      opened);
  thm encoded = mp_rule(spec_rule(
      `cm_global_ty (global:cm_global_d)`, cm_encoded_leaf_size),
      code_wf);
  thm semantic = mp_rule(specl_rule(TERM_LIST(
      `structs:(cm_struct_d)list`,
      `cm_global_ty (global:cm_global_d)`),
      cm_nonstruct_type_size), not_struct);
  ACCEPT_TAC(leaf, by_rewrite(goal_ccl(leaf->g), THM_LIST(
      get_cm_rep_global_size_def(),
      get_cm_rep_code_slot_size_def(),
      get_cm_global_size_def(), encoded, semantic)));
  return gnode_prove(root);
}
PROOF thm cm_rep_global_size_matches =
    cm_prove_rep_global_size_matches();

PROOF static thm cm_prove_globals_wf_head(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (head:cm_global_d)
          (tail:(cm_global_d)list).
         (!i. 0i <= i ==>
              i < ilength (head :: tail) ==>
              cm_global_wf structs (inth i (head :: tail))) ==>
         cm_global_wf structs head`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm all_wf = assume_rule(
      `!i. 0i <= i ==>
         i < ilength
           ((head:cm_global_d) :: (tail:(cm_global_d)list)) ==>
         cm_global_wf (structs:(cm_struct_d)list)
           (inth i (head :: tail))`);
  thm tail_nonnegative = ispec_rule(
      `tail:(cm_global_d)list`, get_theorem_by_name("ILENGTH_NONNEG"));
  thm head_bound = by_defs_arith(
      `0i < ilength
        ((head:cm_global_d) :: (tail:(cm_global_d)list))`,
      THM_LIST(get_theorem_by_name("ILENGTH_DEF")),
      THM_LIST(tail_nonnegative));
  thm result = match_mp_rule(match_mp_rule(
      spec_rule(`0i`, all_wf), int_arith_rule(`0i <= 0i`)),
      head_bound);
  ACCEPT_TAC(leaf, conv_rule(rewrite_conv(THM_LIST(
      ispecl_rule(TERM_LIST(
        `head:cm_global_d`, `tail:(cm_global_d)list`),
        cm_inth_zero_cons))), result));
  return gnode_prove(root);
}
PROOF thm cm_globals_wf_head = cm_prove_globals_wf_head();

PROOF static thm cm_prove_globals_wf_tail(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (head:cm_global_d)
          (tail:(cm_global_d)list).
         (!i. 0i <= i ==>
              i < ilength (head :: tail) ==>
              cm_global_wf structs (inth i (head :: tail))) ==>
         (!i. 0i <= i ==> i < ilength tail ==>
              cm_global_wf structs (inth i tail))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm all_wf = assume_rule(
      `!i. 0i <= i ==>
         i < ilength
           ((head:cm_global_d) :: (tail:(cm_global_d)list)) ==>
         cm_global_wf (structs:(cm_struct_d)list)
           (inth i (head :: tail))`);
  thm lower = assume_rule(`0i <= (i:int)`);
  thm upper = assume_rule(
      `(i:int) < ilength (tail:(cm_global_d)list)`);
  thm full_lower = mp_rule(int_arith_rule(
      `0i <= (i:int) ==> 0i <= i + 1i`), lower);
  thm normalized_upper = mp_rule(int_arith_rule(mk_imp(
      concl(upper),
      `(i:int) + 1i < 1i + ilength (tail:(cm_global_d)list)`)),
      upper);
  thm full_upper = eq_mp_rule(sym_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_theorem_by_name("ILENGTH_DEF"))),
      `(i:int) + 1i <
       ilength ((head:cm_global_d) :: (tail:(cm_global_d)list))`)),
      normalized_upper);
  thm full_wf = match_mp_rule(match_mp_rule(
      spec_rule(`(i:int) + 1i`, all_wf), full_lower), full_upper);
  thm one = mp_rule(int_arith_rule(
      `0i <= (i:int) ==> 1i <= i + 1i`), lower);
  thm at_tail = mp_rule(ispecl_rule(TERM_LIST(
      `head:cm_global_d`, `tail:(cm_global_d)list`,
      `(i:int) + 1i`), cm_inth_cons_tail), one);
  thm index_exact = int_arith_rule(`((i:int) + 1i) - 1i == i`);
  ACCEPT_TAC(leaf, conv_rule(reduce_rewrite_conv(
      THM_LIST(at_tail, index_exact)), full_wf));
  return gnode_prove(root);
}
PROOF thm cm_globals_wf_tail = cm_prove_globals_wf_tail();

PROOF static thm cm_prove_rep_globals_prefix_matches(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (globals:(cm_global_d)list)
          (index:int).
         (!i. 0i <= i ==> i < ilength globals ==>
              cm_global_wf structs (inth i globals)) ==>
         cm_rep_globals_prefix globals index ==
           cm_globals_prefix structs globals index`);
  gnode with_structs = GEN_TAC(root, "structs");
  gnode_list cases = INDUCT_TAC(with_structs,
      `globals:(cm_global_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_rep_globals_prefix_def(),
        get_cm_globals_prefix_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm all_wf = assume_rule(
        `!i. 0i <= i ==>
           i < ilength
             ((a0:cm_global_d) :: (a1:(cm_global_d)list)) ==>
           cm_global_wf (structs:(cm_struct_d)list)
             (inth i (a0 :: a1))`);
    thm head_wf = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`, `a0:cm_global_d`,
        `a1:(cm_global_d)list`), cm_globals_wf_head), all_wf);
    thm tail_wf = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`, `a0:cm_global_d`,
        `a1:(cm_global_d)list`), cm_globals_wf_tail), all_wf);
    thm head = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`, `a0:cm_global_d`),
        cm_rep_global_size_matches), head_wf);
    thm tail = mp_rule(spec_rule(`(index:int) - 1i`,
        assume_rule(
          `!index.
             (!i. 0i <= i ==>
                i < ilength (a1:(cm_global_d)list) ==>
                cm_global_wf (structs:(cm_struct_d)list)
                  (inth i a1)) ==>
             cm_rep_globals_prefix a1 index ==
               cm_globals_prefix structs a1 index`)), tail_wf);
    ACCEPT_TAC(leaf, by_rewrite(goal_ccl(leaf->g), THM_LIST(
        get_cm_rep_globals_prefix_def(), get_cm_globals_prefix_def(),
        head, tail)));
  }
  return gnode_prove(root);
}
PROOF thm cm_rep_globals_prefix_matches =
    cm_prove_rep_globals_prefix_matches();

PROOF static thm cm_prove_rep_globals_size_matches(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (globals:(cm_global_d)list).
         (!i. 0i <= i ==> i < ilength globals ==>
              cm_global_wf structs (inth i globals)) ==>
         cm_rep_globals_size globals ==
           cm_globals_size structs globals`);
  gnode with_structs = GEN_TAC(root, "structs");
  gnode_list cases = INDUCT_TAC(with_structs,
      `globals:(cm_global_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_rep_globals_size_def(), get_cm_globals_size_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm all_wf = assume_rule(
        `!i. 0i <= i ==>
           i < ilength
             ((a0:cm_global_d) :: (a1:(cm_global_d)list)) ==>
           cm_global_wf (structs:(cm_struct_d)list)
             (inth i (a0 :: a1))`);
    thm head_wf = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`, `a0:cm_global_d`,
        `a1:(cm_global_d)list`), cm_globals_wf_head), all_wf);
    thm tail_wf = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`, `a0:cm_global_d`,
        `a1:(cm_global_d)list`), cm_globals_wf_tail), all_wf);
    thm head = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`, `a0:cm_global_d`),
        cm_rep_global_size_matches), head_wf);
    thm tail = mp_rule(assume_rule(
        `(!i. 0i <= i ==>
             i < ilength (a1:(cm_global_d)list) ==>
             cm_global_wf (structs:(cm_struct_d)list)
               (inth i a1)) ==>
         cm_rep_globals_size a1 == cm_globals_size structs a1`),
        tail_wf);
    ACCEPT_TAC(leaf, by_rewrite(goal_ccl(leaf->g), THM_LIST(
        get_cm_rep_globals_size_def(), get_cm_globals_size_def(),
        head, tail)));
  }
  return gnode_prove(root);
}
PROOF thm cm_rep_globals_size_matches =
    cm_prove_rep_globals_size_matches();

PROOF static thm cm_prove_rep_strings_prefix_matches(void) {
  gnode root = gnode_new_with_ccl(
      `!(strings:(cm_string_d)list) (index:int).
         cm_rep_strings_prefix strings index ==
           cm_strings_prefix strings index`);
  gnode_list cases = INDUCT_TAC(root,
      `strings:(cm_string_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_rep_strings_prefix_def(),
        get_cm_strings_prefix_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm tail = spec_rule(`(index:int) - 1i`, assume_rule(
        `!index.
           cm_rep_strings_prefix (a1:(cm_string_d)list) index ==
             cm_strings_prefix a1 index`));
    ACCEPT_TAC(leaf, by_rewrite(goal_ccl(leaf->g), THM_LIST(
        get_cm_rep_strings_prefix_def(),
        get_cm_strings_prefix_def(),
        get_cm_rep_string_size_def(),
        get_cm_rep_string_length_def(), tail,
        int_ring_rule(
          `((a:int) + 1i) + (b:int) == a + (1i + b)`))));
  }
  return gnode_prove(root);
}
PROOF thm cm_rep_strings_prefix_matches =
    cm_prove_rep_strings_prefix_matches();
PROOF static thm cm_prove_rep_string_address_matches(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (globals:(cm_global_d)list)
          (strings:(cm_string_d)list) (index:int).
         (!i. 0i <= i ==> i < ilength globals ==>
              cm_global_wf structs (inth i globals)) ==>
         cm_rep_string_address globals strings index ==
           16i + cm_globals_size structs globals +
             cm_strings_prefix strings index`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm sizes = mp_rule(specl_rule(TERM_LIST(
      `structs:(cm_struct_d)list`, `globals:(cm_global_d)list`),
      cm_rep_globals_size_matches), assume_rule(
        `!i. 0i <= i ==> i < ilength (globals:(cm_global_d)list) ==>
           cm_global_wf (structs:(cm_struct_d)list) (inth i globals)`));
  thm prefix = specl_rule(TERM_LIST(
      `strings:(cm_string_d)list`, `index:int`),
      cm_rep_strings_prefix_matches);
  ACCEPT_TAC(leaf, by_rewrite(goal_ccl(leaf->g), THM_LIST(
      get_cm_rep_string_address_def(), sizes, prefix)));
  return gnode_prove(root);
}
PROOF thm cm_rep_string_address_matches =
    cm_prove_rep_string_address_matches();

PROOF thm cmc_pointer_code_true(void) {
  thm le = mp_rule(
      int_arith_rule(`(ty:int) >= 1024i ==> 1024i <= ty`),
      assume_rule(`(ty:int) >= 1024i`));
  thm reduced = by_rewrite(
      `cm_rep_is_pointer_code (ty:int) == 1i`,
      THM_LIST(
        get_cm_rep_is_pointer_code_def(),
        eqt_intro_rule(le),
        get_theorem_by_name("COND_CLAUSES")));
  return close_implication(
      `!(ty:int). ty >= 1024i ==> cm_rep_is_pointer_code ty == 1i`,
      reduced);
}

PROOF thm cmc_pointer_code_false(void) {
  thm nle = int_arith_rule(`(ty:int) < 1024i ==> ~(1024i <= ty)`);
  thm reduced = by_rewrite(
      `cm_rep_is_pointer_code (ty:int) == 0i`,
      THM_LIST(
        get_cm_rep_is_pointer_code_def(),
        eqf_intro_rule(mp_rule(nle, assume_rule(`(ty:int) < 1024i`))),
        get_theorem_by_name("COND_CLAUSES")));
  return close_implication(
      `!(ty:int). ty < 1024i ==> cm_rep_is_pointer_code ty == 0i`,
      reduced);
}
PROOF static thm cm_prove_pointer_depth(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type).
         cm_is_pointer ty <=> 1i <= cm_type_depth ty`);
  gnode_list cases = INDUCT_TAC(root, `ty:cm_type`);
  for (size_t i = 0; i < 3; ++i) {
    CONV_TAC(cases[i], reduce_rewrite_conv(THM_LIST(
        get_cm_is_pointer_def(), get_cm_type_depth_def())));
  }
  thm positive = eqt_intro_rule(mp_rule(int_arith_rule(
      `0i <= cm_type_depth (a:cm_type) ==>
       1i <= 1i + cm_type_depth a`),
      spec_rule(`a:cm_type`, get_cm_type_depth_nonneg())));
  CONV_TAC(cases[3], reduce_rewrite_conv(THM_LIST(
      get_cm_is_pointer_def(), get_cm_type_depth_def(), positive)));
  return gnode_prove(root);
}
PROOF thm cm_pointer_depth = cm_prove_pointer_depth();

PROOF static thm cm_prove_pointer_encode_threshold(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type).
         cm_type_code_wf ty ==>
         (1024i <= cm_type_encode ty <=> cm_is_pointer ty)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm wf = assume_rule(`cm_type_code_wf (ty:cm_type)`);
  thm bounds = mp_rule(
      spec_rule(`ty:cm_type`, get_cm_type_base_range()), wf);
  thm threshold = mp_rule(mp_rule(mp_rule(mp_rule(int_arith_rule(
      `0i <= cm_type_depth (ty:cm_type) ==>
       0i <= cm_type_base_code ty ==>
       cm_type_base_code ty < 1024i ==>
       cm_type_encode ty ==
         1024i * cm_type_depth ty + cm_type_base_code ty ==>
       ((1024i <= cm_type_encode ty) <=>
        1i <= cm_type_depth ty)`),
      spec_rule(`ty:cm_type`, get_cm_type_depth_nonneg())),
      conjunct1_rule(bounds)), conjunct2_rule(bounds)),
      get_cm_type_encode_def());
  ACCEPT_TAC(leaf, trans_rule(threshold,
      sym_rule(spec_rule(`ty:cm_type`, cm_pointer_depth))));
  return gnode_prove(root);
}
PROOF thm cm_pointer_encode_threshold =
    cm_prove_pointer_encode_threshold();

PROOF static thm cm_prove_pointer_encode_pointee(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type).
         cm_is_pointer ty ==>
         cm_type_encode (cm_pointee ty) ==
           cm_type_encode ty - 1024i`);
  gnode_list cases = INDUCT_TAC(root, `ty:cm_type`);
  for (size_t i = 0; i < 3; ++i) {
    CONV_TAC(cases[i], reduce_rewrite_conv(THM_LIST(
        get_cm_is_pointer_def())));
  }
  thm arithmetic = int_ring_rule(
      `1024i * cm_type_depth (a:cm_type) +
         cm_type_base_code a ==
       (1024i * (1i + cm_type_depth a) +
          cm_type_base_code a) - 1024i`);
  gnode pointer = AUTO_INTROS_TAC(cases[3]);
  thm left = by_rewrite(
      `cm_type_encode (cm_pointee (CMPtrTy (a:cm_type))) ==
       1024i * cm_type_depth a + cm_type_base_code a`,
      THM_LIST(get_cm_pointee_def(), get_cm_type_encode_def()));
  thm right = by_rewrite(
      `cm_type_encode (CMPtrTy (a:cm_type)) - 1024i ==
       (1024i * (1i + cm_type_depth a) +
          cm_type_base_code a) - 1024i`,
      THM_LIST(get_cm_type_encode_def(), get_cm_type_depth_def(),
               get_cm_type_base_code_def()));
  ACCEPT_TAC(pointer,
      trans_rule(left, trans_rule(arithmetic, sym_rule(right))));
  return gnode_prove(root);
}
PROOF thm cm_pointer_encode_pointee =
    cm_prove_pointer_encode_pointee();

PROOF static thm cm_prove_char_encode(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type).
         cm_type_code_wf ty ==>
         (cm_type_encode ty == 1i <=> ty == CMCharTy)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list directions = EQ_TAC(leaf);
  {
    gnode forward = AUTO_INTROS_TAC(directions[0]);
    thm wf = assume_rule(`cm_type_code_wf (ty:cm_type)`);
    thm encoded = assume_rule(`cm_type_encode (ty:cm_type) == 1i`);
    thm char_wf = eqt_elim_rule(conjunct1_rule(conjunct2_rule(
        get_cm_type_code_wf_def())));
    thm roundtrip = mp_rule(
        spec_rule(`ty:cm_type`, get_cm_type_roundtrip()), wf);
    thm char_roundtrip = mp_rule(
        spec_rule(`CMCharTy`, get_cm_type_roundtrip()), char_wf);
    thm char_encoded = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(get_cm_type_encode_def(),
          get_cm_type_depth_def(), get_cm_type_base_code_def())),
        `cm_type_encode CMCharTy == 1i`));
    thm encoded_equal = trans_rule(encoded, sym_rule(char_encoded));
    thm decoded_equal = beta_norm(ap_term_rule(
        `\z:int. cm_type_decode z`, encoded_equal));
    ACCEPT_TAC(forward, trans_rule(sym_rule(roundtrip),
        trans_rule(decoded_equal, char_roundtrip)));
  }
  {
    gnode backward = AUTO_INTROS_TAC(directions[1]);
    thm type_equal = assume_rule(`(ty:cm_type) == CMCharTy`);
    thm char_encoded = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(get_cm_type_encode_def(),
          get_cm_type_depth_def(), get_cm_type_base_code_def())),
        `cm_type_encode CMCharTy == 1i`));
    ACCEPT_TAC(backward, trans_rule(beta_norm(ap_term_rule(
        `\z:cm_type. cm_type_encode z`, type_equal)), char_encoded));
  }
  return gnode_prove(root);
}
PROOF thm cm_char_encode = cm_prove_char_encode();

PROOF thm cm_pointer_code_value_def = new_fun_definition(
    `cm_pointer_code_value (ty:cm_type) : int =
       (if cm_is_pointer ty then 1i else 0i)`);
PROOF int _e_cm_pointer_code_value =
    cst_add_const_to_header(`cm_pointer_code_value`);

PROOF static thm cm_prove_pointer_code_bridge(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type).
         cm_type_code_wf ty ==>
         cm_rep_is_pointer_code (cm_type_encode ty) ==
           cm_pointer_code_value ty`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm threshold = mp_rule(spec_rule(
      `ty:cm_type`, cm_pointer_encode_threshold),
      assume_rule(`cm_type_code_wf (ty:cm_type)`));
  gnode_list cases = BOOL_CASES_TAC(
      leaf, `cm_is_pointer (ty:cm_type)`, "Hpointer");
  CONV_TAC(cases[0], reduce_rewrite_conv(THM_LIST(
      get_cm_rep_is_pointer_code_def(), cm_pointer_code_value_def,
      threshold, eqt_intro_rule(assume_rule(
        `cm_is_pointer (ty:cm_type)`)))));
  CONV_TAC(cases[1], reduce_rewrite_conv(THM_LIST(
      get_cm_rep_is_pointer_code_def(), cm_pointer_code_value_def,
      threshold, eqf_intro_rule(assume_rule(
        `~cm_is_pointer (ty:cm_type)`)))));
  return gnode_prove(root);
}
PROOF thm cm_pointer_code_bridge =
    cm_prove_pointer_code_bridge();

PROOF static thm cm_prove_pointer_code_value_cases(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type).
         ((cm_pointer_code_value ty == 0i <=>
            ~cm_is_pointer ty) &&
          (~(cm_pointer_code_value ty == 0i) <=>
            cm_is_pointer ty))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      leaf, `cm_is_pointer (ty:cm_type)`, "Hpointer");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_WITH_ASMP_TAC(cases[i], reduce_rewrite_conv,
        THM_LIST(cm_pointer_code_value_def));
  }
  return gnode_prove(root);
}
PROOF thm cm_pointer_code_value_cases =
    cm_prove_pointer_code_value_cases();

PROOF thm cm_normalize_code_value_def = new_fun_definition(
    `cm_normalize_code_value (code:int) : int =
       (if code == 1i then 6i else 0i)`);
PROOF int _e_cm_normalize_code_value =
    cst_add_const_to_header(`cm_normalize_code_value`);

PROOF static thm cm_prove_char_normalize_bridge(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type).
         cm_type_code_wf ty ==>
         cm_normalize_code_value (cm_type_encode ty) ==
           cm_char_normalize_count ty`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm encoded = mp_rule(spec_rule(`ty:cm_type`, cm_char_encode),
      assume_rule(`cm_type_code_wf (ty:cm_type)`));
  CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      encoded, cm_normalize_code_value_def,
      get_cm_char_normalize_count_def())));
  return gnode_prove(root);
}
PROOF thm cm_char_normalize_bridge =
    cm_prove_char_normalize_bridge();

PROOF static thm cm_prove_char_normalize_nonnegative(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type). 0i <= cm_char_normalize_count ty`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      leaf, `(ty:cm_type) == CMCharTy`, "Hchar");
  CONV_TAC(cases[0], reduce_rewrite_conv(THM_LIST(
      get_cm_char_normalize_count_def(),
      eqt_intro_rule(assume_rule(`(ty:cm_type) == CMCharTy`)))));
  CONV_TAC(cases[1], reduce_rewrite_conv(THM_LIST(
      get_cm_char_normalize_count_def(),
      eqf_intro_rule(assume_rule(`~((ty:cm_type) == CMCharTy)`)))));
  return gnode_prove(root);
}
PROOF thm cm_char_normalize_nonnegative =
    cm_prove_char_normalize_nonnegative();

PROOF thm cmc_leaf_pointer_case(void) {
  thm le = mp_rule(
      int_arith_rule(`(ty:int) >= 1024i ==> 1024i <= ty`),
      assume_rule(`(ty:int) >= 1024i`));
  thm reduced = by_rewrite(
      `cm_rep_leaf_size (ty:int) == 8i`,
      THM_LIST(get_cm_rep_leaf_size_def(), eqt_intro_rule(le),
        get_theorem_by_name("COND_CLAUSES")));
  return close_implication(
      `!(ty:int). ty >= 1024i ==> cm_rep_leaf_size ty == 8i`,
      reduced);
}

PROOF thm cmc_leaf_int_case(void) {
  thm nle = mp_rule(
      int_arith_rule(`(ty:int) < 1024i ==> ~(1024i <= ty)`),
      assume_rule(`(ty:int) < 1024i`));
  thm reduced = by_rewrite(
      `cm_rep_leaf_size (ty:int) == 8i`,
      THM_LIST(get_cm_rep_leaf_size_def(), eqf_intro_rule(nle),
        eqt_intro_rule(assume_rule(`(ty:int) == 0i`)),
        get_theorem_by_name("COND_CLAUSES")));
  return close_implication(
      `!(ty:int). ty < 1024i ==> ty == 0i ==>
         cm_rep_leaf_size ty == 8i`,
      reduced);
}

PROOF thm cmc_leaf_char_case(void) {
  thm nle = mp_rule(
      int_arith_rule(`(ty:int) < 1024i ==> ~(1024i <= ty)`),
      assume_rule(`(ty:int) < 1024i`));
  thm reduced = by_rewrite(
      `cm_rep_leaf_size (ty:int) == 1i`,
      THM_LIST(get_cm_rep_leaf_size_def(), eqf_intro_rule(nle),
        eqf_intro_rule(assume_rule(`~((ty:int) == 0i)`)),
        eqt_intro_rule(assume_rule(`(ty:int) == 1i`)),
        get_theorem_by_name("COND_CLAUSES")));
  return close_implication(
      `!(ty:int). ty < 1024i ==> ~(ty == 0i) ==> ty == 1i ==>
         cm_rep_leaf_size ty == 1i`,
      reduced);
}

PROOF thm cmc_leaf_other_case(void) {
  thm nle = mp_rule(
      int_arith_rule(`(ty:int) < 1024i ==> ~(1024i <= ty)`),
      assume_rule(`(ty:int) < 1024i`));
  thm reduced = by_rewrite(
      `cm_rep_leaf_size (ty:int) == 0i`,
      THM_LIST(get_cm_rep_leaf_size_def(), eqf_intro_rule(nle),
        eqf_intro_rule(assume_rule(`~((ty:int) == 0i)`)),
        eqf_intro_rule(assume_rule(`~((ty:int) == 1i)`)),
        get_theorem_by_name("COND_CLAUSES")));
  return close_implication(
      `!(ty:int). ty < 1024i ==> ~(ty == 0i) ==> ~(ty == 1i) ==>
         cm_rep_leaf_size ty == 0i`,
      reduced);
}

PROOF thm cmc_leaf_cases(void) {
  gnode root = gnode_new_with_ccl(
      `!(code:int).
         cm_rep_leaf_size code == 0i ||
         cm_rep_leaf_size code == 1i ||
         cm_rep_leaf_size code == 8i`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list pointer_cases = BOOL_CASES_TAC(
      leaf, `1024i <= (code:int)`, "Hpointer");
  CONV_WITH_ASMP_TAC(pointer_cases[0], reduce_rewrite_conv,
      THM_LIST(get_cm_rep_leaf_size_def()));
  gnode_list int_cases = BOOL_CASES_TAC(
      pointer_cases[1], `(code:int) == 0i`, "Hint");
  CONV_WITH_ASMP_TAC(int_cases[0], reduce_rewrite_conv,
      THM_LIST(get_cm_rep_leaf_size_def()));
  gnode_list char_cases = BOOL_CASES_TAC(
      int_cases[1], `(code:int) == 1i`, "Hchar");
  CONV_WITH_ASMP_TAC(char_cases[0], reduce_rewrite_conv,
      THM_LIST(get_cm_rep_leaf_size_def()));
  CONV_WITH_ASMP_TAC(char_cases[1], reduce_rewrite_conv,
      THM_LIST(get_cm_rep_leaf_size_def()));
  return gnode_prove(root);
}

PROOF thm cmc_code_slot_zero_case(void) {
  thm reduced = by_rewrite(
      `cm_rep_code_slot_size (code:int) (count:int) ==
         cm_rep_leaf_size code`,
      THM_LIST(get_cm_rep_code_slot_size_def(),
        eqt_intro_rule(assume_rule(`(count:int) == 0i`)),
        get_theorem_by_name("COND_CLAUSES")));
  return close_implication(
      `!(code:int) (count:int). count == 0i ==>
         cm_rep_code_slot_size code count == cm_rep_leaf_size code`,
      reduced);
}

PROOF thm cmc_code_slot_nonzero_case(void) {
  thm reduced = by_rewrite(
      `cm_rep_code_slot_size (code:int) (count:int) ==
         count * cm_rep_leaf_size code`,
      THM_LIST(get_cm_rep_code_slot_size_def(),
        eqf_intro_rule(assume_rule(`~((count:int) == 0i)`)),
        get_theorem_by_name("COND_CLAUSES")));
  return close_implication(
      `!(code:int) (count:int). ~(count == 0i) ==>
         cm_rep_code_slot_size code count ==
           count * cm_rep_leaf_size code`,
      reduced);
}

PROOF static thm cm_prove_slot_expr_type_refs(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (slot:cm_slot_d).
         cm_slot_wf structs slot ==>
         cm_type_refs structs (cm_slot_expr_type slot)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm wf = conv_rule(rewrite_conv(THM_LIST(
      get_cm_slot_wf_def())), assume_rule(
        `cm_slot_wf (structs:(cm_struct_d)list) (slot:cm_slot_d)`));
  thm scalar = conjunct1_rule(conjunct2_rule(wf));
  thm opened_scalar = conv_rule(rewrite_conv(THM_LIST(
      get_cm_scalar_type_def())), scalar);
  thm refs = conjunct1_rule(conjunct2_rule(opened_scalar));
  gnode_list cases = BOOL_CASES_TAC(
      leaf, `cm_slot_count (slot:cm_slot_d) == 0i`, "Harray");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_WITH_ASMP_TAC(cases[i], reduce_rewrite_conv, THM_LIST(
        get_cm_slot_expr_type_def(), get_cm_type_refs_def(), refs));
  }
  return gnode_prove(root);
}
PROOF static thm cm_slot_expr_type_refs =
    cm_prove_slot_expr_type_refs();

PROOF static thm cm_prove_global_expr_type_refs(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (global:cm_global_d).
         cm_global_wf structs global ==>
         cm_type_refs structs (cm_global_expr_type global)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm wf = conv_rule(rewrite_conv(THM_LIST(
      get_cm_global_wf_def())), assume_rule(
        `cm_global_wf (structs:(cm_struct_d)list)
          (global:cm_global_d)`));
  thm scalar = conjunct1_rule(conjunct2_rule(wf));
  thm opened_scalar = conv_rule(rewrite_conv(THM_LIST(
      get_cm_scalar_type_def())), scalar);
  thm refs = conjunct1_rule(conjunct2_rule(opened_scalar));
  gnode_list cases = BOOL_CASES_TAC(
      leaf, `cm_global_count (global:cm_global_d) == 0i`, "Harray");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_WITH_ASMP_TAC(cases[i], reduce_rewrite_conv, THM_LIST(
        get_cm_global_expr_type_def(), get_cm_type_refs_def(), refs));
  }
  return gnode_prove(root);
}
PROOF static thm cm_global_expr_type_refs =
    cm_prove_global_expr_type_refs();
PROOF static thm cm_prove_binding_type_refs(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (f:cm_function_d) (scope:int) (slot:int).
         cm_typed_program p ==>
         cm_slots_wf (cm_program_structs p) (cm_function_params f) ==>
         cm_slots_wf (cm_program_structs p) (cm_function_locals f) ==>
         cm_binding_valid p f scope slot ==>
         cm_type_refs (cm_program_structs p)
           (cm_binding_type p f scope slot)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm valid = conv_rule(rewrite_conv(THM_LIST(
      get_cm_binding_valid_def())), assume_rule(
        `cm_binding_valid (p:cm_program) (f:cm_function_d)
          (scope:int) (slot:int)`));
  thm typed = conv_rule(rewrite_conv(THM_LIST(
      get_cm_typed_program_def())), assume_rule(
        `cm_typed_program (p:cm_program)`));
  gnode_list global_cases = BOOL_CASES_TAC(
      leaf, `(scope:int) == 0i`, "Hglobal");
  {
    thm scope_zero = assume_rule(`(scope:int) == 0i`);
    thm branch_facts = conj_rule(valid, scope_zero);
    thm lower = mp_rule(int_arith_rule(mk_imp(concl(branch_facts),
        `0i <= (slot:int)`)), branch_facts);
    thm upper = mp_rule(int_arith_rule(mk_imp(concl(branch_facts),
        `(slot:int) < ilength (cm_program_globals (p:cm_program))`)),
        branch_facts);
    thm globals_wf = conjunct1_rule(conjunct2_rule(typed));
    thm selected = mp_rule(mp_rule(spec_rule(
        `slot:int`, globals_wf), lower), upper);
    thm refs = mp_rule(specl_rule(TERM_LIST(
        `cm_program_structs (p:cm_program)`,
        `inth (slot:int) (cm_program_globals p)`),
        cm_global_expr_type_refs), selected);
    CONV_WITH_ASMP_TAC(global_cases[0], reduce_rewrite_conv,
        THM_LIST(get_cm_binding_type_def(), refs));
  }
  {
    gnode_list local_cases = BOOL_CASES_TAC(
        global_cases[1], `(scope:int) == 1i`, "Hlocal");
    {
      thm not_global = assume_rule(`~((scope:int) == 0i)`);
      thm scope_one = assume_rule(`(scope:int) == 1i`);
      thm branch_facts =
          conj_rule(valid, conj_rule(not_global, scope_one));
      thm lower = mp_rule(int_arith_rule(mk_imp(concl(branch_facts),
          `0i <= (slot:int)`)), branch_facts);
      thm upper = mp_rule(int_arith_rule(mk_imp(concl(branch_facts),
          `(slot:int) < ilength
            (cm_function_locals (f:cm_function_d))`)), branch_facts);
      thm slots = conv_rule(rewrite_conv(THM_LIST(
          get_cm_slots_wf_def())), assume_rule(
            `cm_slots_wf (cm_program_structs (p:cm_program))
              (cm_function_locals (f:cm_function_d))`));
      thm selected = mp_rule(mp_rule(spec_rule(
          `slot:int`, slots), lower), upper);
      thm refs = mp_rule(specl_rule(TERM_LIST(
          `cm_program_structs (p:cm_program)`,
          `inth (slot:int) (cm_function_locals (f:cm_function_d))`),
          cm_slot_expr_type_refs), selected);
      CONV_WITH_ASMP_TAC(local_cases[0], reduce_rewrite_conv,
          THM_LIST(get_cm_binding_type_def(), refs));
    }
    {
      thm not_global = assume_rule(`~((scope:int) == 0i)`);
      thm not_local = assume_rule(`~((scope:int) == 1i)`);
      thm branch_facts =
          conj_rule(valid, conj_rule(not_global, not_local));
      thm scope_two = mp_rule(int_arith_rule(mk_imp(concl(branch_facts),
          `(scope:int) == 2i`)), branch_facts);
      thm lower = mp_rule(int_arith_rule(mk_imp(concl(branch_facts),
          `0i <= (slot:int)`)), branch_facts);
      thm upper = mp_rule(int_arith_rule(mk_imp(concl(branch_facts),
          `(slot:int) < ilength
            (cm_function_params (f:cm_function_d))`)), branch_facts);
      thm slots = conv_rule(rewrite_conv(THM_LIST(
          get_cm_slots_wf_def())), assume_rule(
            `cm_slots_wf (cm_program_structs (p:cm_program))
              (cm_function_params (f:cm_function_d))`));
      thm selected = mp_rule(mp_rule(spec_rule(
          `slot:int`, slots), lower), upper);
      thm refs = mp_rule(specl_rule(TERM_LIST(
          `cm_program_structs (p:cm_program)`,
          `inth (slot:int) (cm_function_params (f:cm_function_d))`),
          cm_slot_expr_type_refs), selected);
      CONV_WITH_ASMP_TAC(local_cases[1], reduce_rewrite_conv,
          THM_LIST(get_cm_binding_type_def(), scope_two, refs));
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_binding_type_refs =
    cm_prove_binding_type_refs();

PROOF static thm cm_prove_member_type_refs(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (base:cm_type) (mid:int).
         cm_typed_program p ==>
         cm_member_valid p base mid ==>
         cm_type_refs (cm_program_structs p)
           (cm_member_type p base mid)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm valid = conv_rule(rewrite_conv(THM_LIST(
      get_cm_member_valid_def())), assume_rule(
        `cm_member_valid (p:cm_program) (base:cm_type) (mid:int)`));
  thm rest = conjunct2_rule(valid);
  rest = conjunct2_rule(rest);
  thm sid_nonnegative = conjunct1_rule(rest);
  rest = conjunct2_rule(rest);
  thm sid_upper = conjunct1_rule(rest);
  rest = conjunct2_rule(rest);
  thm mid_nonnegative = conjunct1_rule(rest);
  thm mid_upper = conjunct2_rule(rest);
  thm typed = conv_rule(rewrite_conv(THM_LIST(
      get_cm_typed_program_def())), assume_rule(
        `cm_typed_program (p:cm_program)`));
  thm structs_wf = conjunct1_rule(typed);
  thm selected_struct = mp_rule(mp_rule(spec_rule(
      `cm_struct_id (cm_pointee (base:cm_type))`, structs_wf),
      sid_nonnegative), sid_upper);
  thm opened_struct = conv_rule(rewrite_conv(THM_LIST(
      get_cm_struct_wf_def())), selected_struct);
  thm slots_wf = conjunct1_rule(conjunct2_rule(opened_struct));
  thm opened_slots = conv_rule(rewrite_conv(THM_LIST(
      get_cm_slots_wf_def())), slots_wf);
  thm selected_slot = mp_rule(mp_rule(spec_rule(
      `mid:int`, opened_slots), mid_nonnegative), mid_upper);
  thm refs = mp_rule(specl_rule(TERM_LIST(
      `cm_program_structs (p:cm_program)`,
      `inth (mid:int)
        (cm_struct_members
          (inth (cm_struct_id (cm_pointee (base:cm_type)))
            (cm_program_structs p)))`),
      cm_slot_expr_type_refs), selected_slot);
  CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv,
      THM_LIST(get_cm_member_type_def(), refs));
  return gnode_prove(root);
}
PROOF static thm cm_member_type_refs =
    cm_prove_member_type_refs();

PROOF static thm cm_prove_function_ret_refs(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int).
         cm_typed_program p ==>
         0i <= fid ==>
         fid < ilength (cm_program_functions p) ==>
         cm_type_refs (cm_program_structs p)
           (cm_function_ret
             (inth fid (cm_program_functions p)))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm typed = conv_rule(rewrite_conv(THM_LIST(
      get_cm_typed_program_def())), assume_rule(
        `cm_typed_program (p:cm_program)`));
  thm rest = conjunct2_rule(typed);
  rest = conjunct2_rule(rest);
  rest = conjunct2_rule(rest);
  thm functions_wf = conjunct1_rule(rest);
  thm selected = mp_rule(mp_rule(spec_rule(
      `fid:int`, functions_wf), assume_rule(`0i <= (fid:int)`)),
      assume_rule(
        `(fid:int) < ilength (cm_program_functions (p:cm_program))`));
  thm opened_function = conv_rule(rewrite_conv(THM_LIST(
      get_cm_function_wf_def())), selected);
  thm scalar = conjunct1_rule(opened_function);
  thm opened_scalar = conv_rule(rewrite_conv(THM_LIST(
      get_cm_scalar_type_def())), scalar);
  ACCEPT_TAC(leaf, conjunct1_rule(conjunct2_rule(opened_scalar)));
  return gnode_prove(root);
}
PROOF static thm cm_function_ret_refs =
    cm_prove_function_ret_refs();


PROOF static thm cm_prove_type_refs_pointee(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (ty:cm_type).
         cm_type_refs structs ty ==>
         cm_is_pointer ty ==>
         cm_type_refs structs (cm_pointee ty)`);
  gnode with_structs = GEN_TAC(root, "structs");
  gnode_list cases = INDUCT_TAC(with_structs, `ty:cm_type`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_TAC(cases[i], reduce_rewrite_conv(THM_LIST(
        get_cm_type_refs_def(), get_cm_is_pointer_def(),
        get_cm_pointee_def())));
  }
  return gnode_prove(root);
}
PROOF thm cm_type_refs_pointee =
    cm_prove_type_refs_pointee();

PROOF static thm cm_prove_type_code_wf_pointee(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type).
         cm_type_code_wf ty ==>
         cm_is_pointer ty ==>
         cm_type_code_wf (cm_pointee ty)`);
  gnode_list cases = INDUCT_TAC(root, `ty:cm_type`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_TAC(cases[i], reduce_rewrite_conv(THM_LIST(
        get_cm_type_code_wf_def(), get_cm_is_pointer_def(),
        get_cm_pointee_def())));
  }
  return gnode_prove(root);
}
PROOF thm cm_type_code_wf_pointee =
    cm_prove_type_code_wf_pointee();

PROOF static void cm_finish_type_refs_branch(const gnode branch) {
  if (!IS_NULL(branch->solved)) {
    return;
  }
  gnode leaf = AUTO_INTROS_TAC(branch);
  gnode_list frontier = AUTO_ASMP_DESTRUCT_TAC(leaf);
  for (size_t i = 0; i < vector_size(frontier); ++i) {
    gnode closed = CONV_WITH_ASMP_TAC(
        frontier[i], reduce_rewrite_conv, THM_LIST(
          get_cm_type_refs_def(), cm_type_refs_pointee));
    if (IS_NULL(closed->solved) &&
        alpha_compare(goal_ccl(closed->g),
          `cm_type_refs (structs:(cm_struct_d)list)
            (cm_pointee (arg:cm_type))`) == 0) {
      thm result = specl_rule(TERM_LIST(
          `structs:(cm_struct_d)list`, `arg:cm_type`),
          cm_type_refs_pointee);
      result = mp_rule(result, assume_rule(
          `cm_type_refs (structs:(cm_struct_d)list) (arg:cm_type)`));
      result = mp_rule(result,
          assume_rule(`cm_is_pointer (arg:cm_type)`));
      ACCEPT_TAC(closed, result);
    }
    ENSURE_COND(!IS_NULL(closed->solved),
        "type reference result branch remains open: %s",
        cstr_gnode(closed));
  }
  return;
err:
  return;
}

PROOF static void cm_reduce_binary_refs_branch(const gnode branch) {
  gnode reduced = CONV_WITH_ASMP_TAC(
      branch, reduce_rewrite_conv, THM_LIST(
        get_cm_binary_types_def(), get_cm_type_refs_def()));
  cm_finish_type_refs_branch(reduced);
}

PROOF static void cm_binary_refs_after_compare(const gnode branch) {
  gnode_list add_cases = BOOL_CASES_TAC(
      branch, `(op:int) == 8i`, "Hadd");
  cm_reduce_binary_refs_branch(add_cases[0]);
  gnode_list sub_cases = BOOL_CASES_TAC(
      add_cases[1], `(op:int) == 9i`, "Hsub");
  cm_reduce_binary_refs_branch(sub_cases[0]);
  cm_reduce_binary_refs_branch(sub_cases[1]);
}

PROOF static thm cm_prove_binary_result_refs(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (op:int)
          (left:cm_type) (right:cm_type) (result:cm_type).
         cm_type_refs structs left ==>
         cm_type_refs structs right ==>
         cm_binary_types op left right result ==>
         cm_type_refs structs result`);
  gnode quantified = GEN_TAC(root, "structs");
  quantified = GEN_TAC(quantified, "op");
  quantified = GEN_TAC(quantified, "left");
  quantified = GEN_TAC(quantified, "right");
  quantified = GEN_TAC(quantified, "result");
  gnode_list zero_cases = BOOL_CASES_TAC(
      quantified, `(op:int) == 0i`, "Hzero");
  cm_reduce_binary_refs_branch(zero_cases[0]);
  gnode_list one_cases = BOOL_CASES_TAC(
      zero_cases[1], `(op:int) == 1i`, "Hone");
  cm_reduce_binary_refs_branch(one_cases[0]);
  gnode_list lower_cases = BOOL_CASES_TAC(
      one_cases[1], `2i <= (op:int)`, "Hcompare_lower");
  cm_binary_refs_after_compare(lower_cases[1]);
  gnode_list upper_cases = BOOL_CASES_TAC(
      lower_cases[0], `(op:int) <= 7i`, "Hcompare_upper");
  cm_reduce_binary_refs_branch(upper_cases[0]);
  cm_binary_refs_after_compare(upper_cases[1]);
  return gnode_prove(root);
}
PROOF static thm cm_binary_result_refs =
    cm_prove_binary_result_refs();

PROOF static void cm_reduce_unary_refs_branch(const gnode branch) {
  gnode reduced = CONV_WITH_ASMP_TAC(
      branch, reduce_rewrite_conv, THM_LIST(
        get_cm_unary_types_def(), get_cm_type_refs_def(),
        cm_type_refs_pointee));
  cm_finish_type_refs_branch(reduced);
}

PROOF static thm cm_prove_unary_result_refs(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (op:int)
          (arg:cm_type) (result:cm_type).
         cm_type_refs structs arg ==>
         cm_unary_types op arg result ==>
         cm_type_refs structs result`);
  gnode quantified = GEN_TAC(root, "structs");
  quantified = GEN_TAC(quantified, "op");
  quantified = GEN_TAC(quantified, "arg");
  quantified = GEN_TAC(quantified, "result");
  gnode_list zero_cases = BOOL_CASES_TAC(
      quantified, `(op:int) == 0i`, "Hzero");
  cm_reduce_unary_refs_branch(zero_cases[0]);
  gnode_list one_cases = BOOL_CASES_TAC(
      zero_cases[1], `(op:int) == 1i`, "Hone");
  cm_reduce_unary_refs_branch(one_cases[0]);
  gnode_list deref_cases = BOOL_CASES_TAC(
      one_cases[1], `(op:int) == 2i`, "Hderef");
  cm_reduce_unary_refs_branch(deref_cases[0]);
  cm_reduce_unary_refs_branch(deref_cases[1]);
  return gnode_prove(root);
}
PROOF static thm cm_unary_result_refs =
    cm_prove_unary_result_refs();

PROOF static thm cm_prove_cond_nonnegative(void) {
  gnode root = gnode_new_with_ccl(
      `!(choice:bool) (x:int) (y:int).
         0i <= x && 0i <= y ==>
         0i <= (if choice then x else y)`);
  gnode quantified = GEN_TAC(root, "choice");
  quantified = GEN_TAC(quantified, "x");
  quantified = GEN_TAC(quantified, "y");
  gnode_list cases = BOOL_CASES_TAC(
      quantified, `choice:bool`, "Hchoice");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode reduced = CONV_WITH_ASMP_TAC(
        cases[i], reduce_rewrite_conv, THM_LIST());
    gnode leaf = AUTO_INTROS_TAC(reduced);
    gnode_list frontier = AUTO_ASMP_DESTRUCT_TAC(leaf);
    CONV_WITH_ASMP_TAC(
        frontier[0], reduce_rewrite_conv, THM_LIST());
  }
  return gnode_prove(root);
}
PROOF static thm cm_cond_nonnegative =
    cm_prove_cond_nonnegative();

PROOF static void cm_close_nonnegative_expression(const gnode node) {
  if (!IS_NULL(node->solved)) {
    return;
  }
  if (is_conj(goal_ccl(node->g))) {
    gnode_list parts = CONJ_TAC(node);
    cm_close_nonnegative_expression(parts[0]);
    cm_close_nonnegative_expression(parts[1]);
    return;
  }
  term proposition_head = goal_ccl(node->g);
  while (is_comb(proposition_head)) {
    proposition_head = dest_comb(proposition_head).tm1;
  }
  if (alpha_compare(
        proposition_head, `COND:bool->bool->bool->bool`) == 0) {
    dest_comb_results outer = dest_comb(goal_ccl(node->g));
    dest_comb_results middle = dest_comb(outer.tm1);
    term choice = dest_comb(middle.tm1).tm2;
    gnode_list cases = BOOL_CASES_TAC(
        node, choice, "Htemp_choice");
    for (size_t i = 0; i < vector_size(cases); ++i) {
      gnode reduced = CONV_WITH_ASMP_TAC(
          cases[i], reduce_rewrite_conv, THM_LIST());
      cm_close_nonnegative_expression(reduced);
    }
    return;
  }
  dest_binop_results comparison = dest_binop(
      `(<=):int->int->bool`, goal_ccl(node->g));
  term head = comparison.tm2;
  while (is_comb(head)) {
    head = dest_comb(head).tm1;
  }
  if (alpha_compare(head, `cm_imax:int->int->int`) == 0 ||
      alpha_compare(head, `COND:bool->int->int->int`) == 0) {
    thm rule = alpha_compare(
        head, `cm_imax:int->int->int`) == 0
        ? cm_imax_nonnegative : cm_cond_nonnegative;
    gnode premise = MATCH_MP_TAC(node, rule);
    gnode_list parts = CONJ_TAC(premise);
    cm_close_nonnegative_expression(parts[0]);
    cm_close_nonnegative_expression(parts[1]);
    return;
  }
  labeled_term_list context = goal_lasmps(node->g);
  thm facts = assume_rule(context[0].tm);
  for (size_t i = 1; i < vector_size(context); ++i) {
    facts = conj_rule(facts, assume_rule(context[i].tm));
  }
  ACCEPT_TAC(node, mp_rule(int_arith_rule(
      mk_imp(concl(facts), goal_ccl(node->g))), facts));
}



PROOF static thm cm_prove_integer_type_refs(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (ty:cm_type).
         cm_integer_type ty ==> cm_type_refs structs ty`);
  gnode_list cases = INDUCT_TAC(root, `ty:cm_type`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    thm view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        get_cm_integer_type_def(), get_cm_type_refs_def(),
        get_datatype_distinctness("cm_type"))),
        goal_ccl(cases[i]->g));
    ACCEPT_TAC(cases[i], eqt_elim_rule(view));
  }
  return gnode_prove(root);
}
PROOF static thm cm_integer_type_refs =
    cm_prove_integer_type_refs();

PROOF static thm cm_apply_expr_result_refs_ih(
    const thm ih, const thm expr_wf) {
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `f:cm_function_d`), ih);
  result = mp_rule(result,
      assume_rule(`cm_typed_program (p:cm_program)`));
  result = mp_rule(result, assume_rule(
      `cm_slots_wf (cm_program_structs (p:cm_program))
        (cm_function_params (f:cm_function_d))`));
  result = mp_rule(result, assume_rule(
      `cm_slots_wf (cm_program_structs (p:cm_program))
        (cm_function_locals (f:cm_function_d))`));
  return mp_rule(result, expr_wf);
}

PROOF static thm cm_prove_expr_result_refs(void) {
  gnode root = gnode_new_with_ccl(
      `((!(e:cm_expr) (p:cm_program) (f:cm_function_d).
           cm_typed_program p ==>
           cm_slots_wf (cm_program_structs p) (cm_function_params f) ==>
           cm_slots_wf (cm_program_structs p) (cm_function_locals f) ==>
           cm_expr_wf p f e ==>
           cm_type_refs (cm_program_structs p) (cm_expr_type e)) &&
        (!(args:(cm_expr)list). T))`);
  gnode matched = MATCH_MP_TAC(root, get_cm_expr_induction());
  gnode cursor = CONV_TAC(
      matched, reduce_rewrite_conv(THM_LIST()));
  gnode cases[14];
  for (size_t i = 0; i < 13; ++i) {
    gnode_list split = CONJ_TAC(cursor);
    cases[i] = split[0];
    cursor = split[1];
  }
  cases[13] = cursor;
  for (size_t i = 0; i < 14; ++i) {
    gnode expanded = CONV_TAC(cases[i], rewrite_conv(THM_LIST(
        get_cm_expr_wf_def(), get_cm_expr_type_def(),
        get_cm_scalar_type_def(), get_cm_is_pointer_def(),
        get_cm_pointee_def())));
    gnode constructor = AUTO_INTROS_TAC(expanded);
    gnode_list frontier = AUTO_ASMP_DESTRUCT_TAC(constructor);
    for (size_t j = 0; j < vector_size(frontier); ++j) {
      if (i == 0) {
        thm result = specl_rule(TERM_LIST(
            `cm_program_structs (p:cm_program)`, `a1:cm_type`),
            cm_integer_type_refs);
        result = mp_rule(result,
            assume_rule(`cm_integer_type (a1:cm_type)`));
        ACCEPT_TAC(frontier[j], result);
        continue;
      }
      if (i == 2) {
        thm result = specl_rule(TERM_LIST(
            `p:cm_program`, `f:cm_function_d`,
            `a0:int`, `a1:int`), cm_binding_type_refs);
        result = mp_rule(result,
            assume_rule(`cm_typed_program (p:cm_program)`));
        result = mp_rule(result, assume_rule(
            `cm_slots_wf (cm_program_structs (p:cm_program))
              (cm_function_params (f:cm_function_d))`));
        result = mp_rule(result, assume_rule(
            `cm_slots_wf (cm_program_structs (p:cm_program))
              (cm_function_locals (f:cm_function_d))`));
        result = mp_rule(result, assume_rule(
            `cm_binding_valid (p:cm_program) (f:cm_function_d)
              (a0:int) (a1:int)`));
        gnode closed = CONV_WITH_ASMP_TAC(
            frontier[j], reduce_rewrite_conv, THM_LIST(result));
        ENSURE_COND(!IS_NULL(closed->solved),
            "expression refs special case %zu branch %zu: %s",
            i, j, cstr_gnode(closed));
        continue;
      }
      if (i == 3) {
        thm result = cm_apply_expr_result_refs_ih(assume_rule(
            `!(p:cm_program) (f:cm_function_d).
               cm_typed_program p ==>
               cm_slots_wf (cm_program_structs p)
                 (cm_function_params f) ==>
               cm_slots_wf (cm_program_structs p)
                 (cm_function_locals f) ==>
               cm_expr_wf p f (a0:cm_expr) ==>
               cm_type_refs (cm_program_structs p)
                 (cm_expr_type a0)`), assume_rule(
            `cm_expr_wf (p:cm_program) (f:cm_function_d)
              (a0:cm_expr)`));
        gnode closed = CONV_WITH_ASMP_TAC(
            frontier[j], reduce_rewrite_conv,
            THM_LIST(get_cm_type_refs_def(), result));
        ENSURE_COND(!IS_NULL(closed->solved),
            "expression refs special case %zu branch %zu: %s",
            i, j, cstr_gnode(closed));
        continue;
      }
      if (i == 4) {
        thm left_refs = cm_apply_expr_result_refs_ih(assume_rule(
            `!(p:cm_program) (f:cm_function_d).
               cm_typed_program p ==>
               cm_slots_wf (cm_program_structs p)
                 (cm_function_params f) ==>
               cm_slots_wf (cm_program_structs p)
                 (cm_function_locals f) ==>
               cm_expr_wf p f (a1:cm_expr) ==>
               cm_type_refs (cm_program_structs p)
                 (cm_expr_type a1)`), assume_rule(
            `cm_expr_wf (p:cm_program) (f:cm_function_d)
              (a1:cm_expr)`));
        thm right_refs = cm_apply_expr_result_refs_ih(assume_rule(
            `!(p:cm_program) (f:cm_function_d).
               cm_typed_program p ==>
               cm_slots_wf (cm_program_structs p)
                 (cm_function_params f) ==>
               cm_slots_wf (cm_program_structs p)
                 (cm_function_locals f) ==>
               cm_expr_wf p f (a2:cm_expr) ==>
               cm_type_refs (cm_program_structs p)
                 (cm_expr_type a2)`), assume_rule(
            `cm_expr_wf (p:cm_program) (f:cm_function_d)
              (a2:cm_expr)`));
        thm result = specl_rule(TERM_LIST(
            `cm_program_structs (p:cm_program)`,
            `a0:int`, `cm_expr_type (a1:cm_expr)`,
            `cm_expr_type (a2:cm_expr)`, `a3:cm_type`),
            cm_binary_result_refs);
        result = mp_rule(result, left_refs);
        result = mp_rule(result, right_refs);
        result = mp_rule(result, assume_rule(
            `cm_binary_types (a0:int) (cm_expr_type (a1:cm_expr))
              (cm_expr_type (a2:cm_expr)) (a3:cm_type)`));
        gnode closed = CONV_WITH_ASMP_TAC(
            frontier[j], reduce_rewrite_conv, THM_LIST(result));
        ENSURE_COND(!IS_NULL(closed->solved),
            "expression refs special case %zu branch %zu: %s",
            i, j, cstr_gnode(closed));
        continue;
      }
      if (i == 5) {
        thm arg_refs = cm_apply_expr_result_refs_ih(assume_rule(
            `!(p:cm_program) (f:cm_function_d).
               cm_typed_program p ==>
               cm_slots_wf (cm_program_structs p)
                 (cm_function_params f) ==>
               cm_slots_wf (cm_program_structs p)
                 (cm_function_locals f) ==>
               cm_expr_wf p f (a1:cm_expr) ==>
               cm_type_refs (cm_program_structs p)
                 (cm_expr_type a1)`), assume_rule(
            `cm_expr_wf (p:cm_program) (f:cm_function_d)
              (a1:cm_expr)`));
        thm result = specl_rule(TERM_LIST(
            `cm_program_structs (p:cm_program)`,
            `a0:int`, `cm_expr_type (a1:cm_expr)`, `a2:cm_type`),
            cm_unary_result_refs);
        result = mp_rule(result, arg_refs);
        result = mp_rule(result, assume_rule(
            `cm_unary_types (a0:int) (cm_expr_type (a1:cm_expr))
              (a2:cm_type)`));
        gnode closed = CONV_WITH_ASMP_TAC(
            frontier[j], reduce_rewrite_conv, THM_LIST(result));
        ENSURE_COND(!IS_NULL(closed->solved),
            "expression refs special case %zu branch %zu: %s",
            i, j, cstr_gnode(closed));
        continue;
      }
      if (i == 6) {
        thm base_refs = cm_apply_expr_result_refs_ih(assume_rule(
            `!(p:cm_program) (f:cm_function_d).
               cm_typed_program p ==>
               cm_slots_wf (cm_program_structs p)
                 (cm_function_params f) ==>
               cm_slots_wf (cm_program_structs p)
                 (cm_function_locals f) ==>
               cm_expr_wf p f (a0:cm_expr) ==>
               cm_type_refs (cm_program_structs p)
                 (cm_expr_type a0)`), assume_rule(
            `cm_expr_wf (p:cm_program) (f:cm_function_d)
              (a0:cm_expr)`));
        thm result = specl_rule(TERM_LIST(
            `cm_program_structs (p:cm_program)`,
            `cm_expr_type (a0:cm_expr)`), cm_type_refs_pointee);
        result = mp_rule(result, base_refs);
        result = mp_rule(result, assume_rule(
            `cm_is_pointer (cm_expr_type (a0:cm_expr))`));
        gnode closed = CONV_WITH_ASMP_TAC(
            frontier[j], reduce_rewrite_conv, THM_LIST(result));
        ENSURE_COND(!IS_NULL(closed->solved),
            "expression refs special case %zu branch %zu: %s",
            i, j, cstr_gnode(closed));
        continue;
      }
      if (i == 7) {
        thm result = specl_rule(TERM_LIST(
            `p:cm_program`, `cm_expr_type (a0:cm_expr)`,
            `a1:int`), cm_member_type_refs);
        result = mp_rule(result,
            assume_rule(`cm_typed_program (p:cm_program)`));
        result = mp_rule(result, assume_rule(
            `cm_member_valid (p:cm_program)
              (cm_expr_type (a0:cm_expr)) (a1:int)`));
        gnode closed = CONV_WITH_ASMP_TAC(
            frontier[j], reduce_rewrite_conv, THM_LIST(result));
        ENSURE_COND(!IS_NULL(closed->solved),
            "expression refs special case %zu branch %zu: %s",
            i, j, cstr_gnode(closed));
        continue;
      }
      if (i == 8) {
        thm result = specl_rule(TERM_LIST(
            `p:cm_program`, `a0:int`), cm_function_ret_refs);
        result = mp_rule(result,
            assume_rule(`cm_typed_program (p:cm_program)`));
        result = mp_rule(result, assume_rule(`0i <= (a0:int)`));
        result = mp_rule(result, assume_rule(
            `(a0:int) < ilength
              (cm_program_functions (p:cm_program))`));
        gnode closed = CONV_WITH_ASMP_TAC(
            frontier[j], reduce_rewrite_conv, THM_LIST(result));
        ENSURE_COND(!IS_NULL(closed->solved),
            "expression refs special case %zu branch %zu: %s",
            i, j, cstr_gnode(closed));
        continue;
      }
      gnode reduced = CONV_WITH_ASMP_TAC(
          frontier[j], reduce_rewrite_conv, THM_LIST(
            get_cm_expr_wf_def(), get_cm_expr_type_def(),
            get_cm_scalar_type_def(), get_cm_type_refs_def(),
            get_cm_binary_types_def(), get_cm_unary_types_def(),
            get_cm_is_pointer_def(), get_cm_pointee_def(),
            cm_binding_type_refs, cm_member_type_refs,
            cm_function_ret_refs));
      ENSURE_COND(!IS_NULL(reduced->solved),
          "expression result refs case %zu branch %zu remains open: %s",
          i, j, cstr_gnode(reduced));
    }
  }
  return conjunct1_rule(gnode_prove(root));
err:
  return empty_theorem;
}
PROOF thm cm_expr_result_refs = cm_prove_expr_result_refs();


PROOF thm cm_binding_array_code_def = new_fun_definition(
    `cm_binding_array_code (p:cm_program) (fid:int)
       (scope:int) (slot:int) : int =
       (if cm_binding_array p fid scope slot then 1i else 0i)`);
PROOF int _e_cm_binding_array_code =
    cst_add_const_to_header(`cm_binding_array_code`);
PROOF static thm cm_prove_binding_array_code_zero(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (scope:int) (slot:int).
         (cm_binding_array_code p fid scope slot == 0i <=>
          ~(cm_binding_array p fid scope slot))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(leaf,
      `cm_binding_array (p:cm_program) (fid:int)
        (scope:int) (slot:int)`, "Harray");
  CONV_WITH_ASMP_TAC(cases[0], reduce_rewrite_conv,
      THM_LIST(cm_binding_array_code_def));
  CONV_WITH_ASMP_TAC(cases[1], reduce_rewrite_conv,
      THM_LIST(cm_binding_array_code_def));
  return gnode_prove(root);
}
PROOF thm cm_binding_array_code_zero =
    cm_prove_binding_array_code_zero();

PROOF static thm cm_prove_binding_array_code_nonzero(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (scope:int) (slot:int).
         (~(cm_binding_array_code p fid scope slot == 0i) <=>
          cm_binding_array p fid scope slot)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(leaf,
      `cm_binding_array (p:cm_program) (fid:int)
        (scope:int) (slot:int)`, "Harray");
  CONV_WITH_ASMP_TAC(cases[0], reduce_rewrite_conv,
      THM_LIST(cm_binding_array_code_def));
  CONV_WITH_ASMP_TAC(cases[1], reduce_rewrite_conv,
      THM_LIST(cm_binding_array_code_def));
  return gnode_prove(root);
}
PROOF thm cm_binding_array_code_nonzero =
    cm_prove_binding_array_code_nonzero();
PROOF thm cm_member_array_code_def = new_fun_definition(
    `cm_member_array_code (p:cm_program) (base:cm_type)
       (mid:int) : int =
       (if cm_member_array p base mid then 1i else 0i)`);
PROOF int _e_cm_member_array_code =
    cst_add_const_to_header(`cm_member_array_code`);
PROOF static int cmc_concrete_defs_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_concrete_defs_axioms_before,
      "cmc_concrete_defs introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_concrete_defs_checks =
    cmc_concrete_defs_final_checks();
