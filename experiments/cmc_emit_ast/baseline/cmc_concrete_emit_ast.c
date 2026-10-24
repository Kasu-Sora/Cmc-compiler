#include "cmc_concrete_emit_ast.h"



PROOF static void cm_ast_open_fragment(const thm code_shape) {
  thm capacity_shape = beta_norm(ap_term_rule(
      `\code:(tvm_inst)list.
         ilength (done:(tvm_inst)list) + ilength code <= (capacity:int)`,
      code_shape));
  substitute_st(capacity_shape);
}

PROOF static void cm_ast_close_fragment(const thm code_shape) {
  thm done_shape = beta_norm(ap_term_rule(
      `\code:(tvm_inst)list.
         (done:(tvm_inst)list) ++ code`,
      sym_rule(code_shape)));
  substitute_st(done_shape);
}

PROOF static thm cm_ast_typed_program(void) {
  thm wf = eqt_elim_rule(assume_rule(
      `cm_wf_program (p:cm_program) <=> true`));
  thm admissible = conv_rule(rewrite_conv(THM_LIST(
      get_cm_wf_program_def())), wf);
  thm opened = conv_rule(rewrite_conv(THM_LIST(
      get_cm_codegen_admissible_def())), admissible);
  return conjunct1_rule(opened);
}

PROOF static thm cm_ast_globals_wf(void) {
  thm typed = cm_ast_typed_program();
  thm opened = conv_rule(rewrite_conv(THM_LIST(
      get_cm_typed_program_def())), typed);
  return conjunct1_rule(conjunct2_rule(opened));
}

PROOF static thm cm_ast_global_address_bridge(void) {
  thm prefix = mp_rule(specl_rule(TERM_LIST(
      `cm_program_structs (p:cm_program)`,
      `cm_program_globals (p:cm_program)`, `slot__pre:int`),
      cm_rep_globals_prefix_matches), cm_ast_globals_wf());
  return by_rewrite(
      `cm_rep_global_address (cm_program_globals (p:cm_program))
         (slot__pre:int) ==
       cm_global_address p slot__pre`,
      THM_LIST(get_cm_rep_global_address_def(),
        get_cm_global_address_def(), prefix));
}

PROOF static thm cm_ast_local_offset_bridge(void) {
  thm params = mp_rule(specl_rule(TERM_LIST(
      `structs:(cm_struct_d)list`,
      `cm_function_params (f:cm_function_d)`),
      cm_rep_members_size_matches), eqt_elim_rule(assume_rule(
        `cm_slots_wf (structs:(cm_struct_d)list)
           (cm_function_params (f:cm_function_d)) <=> true`)));
  thm locals = mp_rule(specl_rule(TERM_LIST(
      `structs:(cm_struct_d)list`,
      `cm_function_locals (f:cm_function_d)`, `slot__pre:int`),
      cm_rep_member_prefix_matches), eqt_elim_rule(assume_rule(
        `cm_slots_wf (structs:(cm_struct_d)list)
           (cm_function_locals (f:cm_function_d)) <=> true`)));
  return by_rewrite(
      `8i + cm_rep_members_size (cm_function_params (f:cm_function_d)) +
         cm_rep_member_prefix (cm_function_locals f) (slot__pre:int) ==
       cm_local_offset (p:cm_program) (fid:int) slot__pre`,
      THM_LIST(get_cm_local_offset_def(), params, locals,
        assume_rule(
          `structs == cm_program_structs (p:cm_program)`),
        assume_rule(
          `(f:cm_function_d) ==
           inth (fid:int) (cm_program_functions p)`)));
}

PROOF static thm cm_ast_param_offset_bridge(void) {
  thm params = mp_rule(specl_rule(TERM_LIST(
      `structs:(cm_struct_d)list`,
      `cm_function_params (f:cm_function_d)`, `slot__pre:int`),
      cm_rep_member_prefix_matches), eqt_elim_rule(assume_rule(
        `cm_slots_wf (structs:(cm_struct_d)list)
           (cm_function_params (f:cm_function_d)) <=> true`)));
  return by_rewrite(
      `8i + cm_rep_member_prefix
         (cm_function_params (f:cm_function_d)) (slot__pre:int) ==
       cm_param_offset (p:cm_program) (fid:int) slot__pre`,
      THM_LIST(get_cm_param_offset_def(), params,
        assume_rule(
          `structs == cm_program_structs (p:cm_program)`),
        assume_rule(
          `(f:cm_function_d) ==
           inth (fid:int) (cm_program_functions p)`)));
}

void cm_emit_binding_address(struct cm_program *program,
                             struct cm_function *fn,
                             int scope, int slot,
                             struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `fid:int`,
                 `structs:(cm_struct_d)list`,
                 `globals:(cm_global_d)list`,
                 `functions_ptr:int`, `body:int`, `next:int`,
                 `done:(tvm_inst)list`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(structs == cm_program_structs p) **
       fact(globals == cm_program_globals p) **
       fact(cm_binding_valid p f scope slot <=> true) **
       fact(cm_slots_wf structs (cm_function_params f) <=> true) **
       fact(cm_slots_wf structs (cm_function_locals f) <=> true) **
       fact(cm_rep_globals_safe globals <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(ilength done +
              ilength (cm_binding_address_code p fid scope slot) <=
              capacity) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_resolved_emitter_rep p emitter out capacity done`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(structs == cm_program_structs p) **
       fact(globals == cm_program_globals p) **
       fact(cm_binding_valid p f scope slot <=> true) **
       fact(cm_slots_wf structs (cm_function_params f) <=> true) **
       fact(cm_slots_wf structs (cm_function_locals f) <=> true) **
       fact(cm_rep_globals_safe globals <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_resolved_emitter_rep p emitter out capacity
         (done ++ cm_binding_address_code p fid scope slot)`)]]
{
  [[cst::proof]] {
    cm_open_program_context_st();
    cm_open_function_context_st();
    thm nonnegative = mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `f:cm_function_d`, `scope__pre:int`,
        `slot__pre:int`), cm_binding_valid_slot_nonnegative),
        eqt_elim_rule(assume_rule(
          `cm_binding_valid (p:cm_program) (f:cm_function_d)
             (scope__pre:int) (slot__pre:int) <=> true`)));
    add_fact_st(nonnegative);
  }
  if (scope == CMC_BIND_GLOBAL) {
    [[cst::proof]] {
      substitute_st(assume_rule(
          `globals == cm_program_globals (p:cm_program)`));
    }
    [[cst::where(`items`, `cm_program_globals (p:cm_program)`)]]
    long long address = cmc_global_address(program->globals, slot);
    [[cst::proof]] {
      thm returned = assume_rule(
          `(retval:int) ==
           cm_rep_global_address (cm_program_globals (p:cm_program))
             (slot__pre:int)`);
      cm_retarget_i64_st(`address__addr:addr`,
          trans_rule(returned, cm_ast_global_address_bridge()));
      thm code_shape = apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_cm_binding_address_code_def(), get_cm_push_code_def(),
            eqt_intro_rule(assume_rule(`scope__pre == 0i`)))),
          `cm_binding_address_code (p:cm_program) (fid:int)
             (scope__pre:int) (slot__pre:int)`);
      cm_ast_open_fragment(code_shape);
      rewrite_st(THM_LIST(get_theorem_by_name("ILENGTH_DEF")));
      cm_add_opcode_facts_st(`0i`, `TVMPushOp`);
    }
    [[cst::where(`p`, `(p:cm_program)`)]][[cst::where(`opcode`, `TVMPushOp`)]]
    cm_emit_resolved(emitter, CMC_OP_PUSH, address);
    [[cst::proof]] {
      thm code_shape = apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_cm_binding_address_code_def(), get_cm_push_code_def(),
            eqt_intro_rule(assume_rule(`scope__pre == 0i`)))),
          `cm_binding_address_code (p:cm_program) (fid:int)
             (scope__pre:int) (slot__pre:int)`);
      cm_ast_close_fragment(code_shape);
      cm_close_function_context_st();
      cm_close_program_context_st();
      substitute_st(sym_rule(assume_rule(
          `globals == cm_program_globals (p:cm_program)`)));
    }
  } else if (scope == CMC_BIND_LOCAL) {
    [[cst::where(`params`, `cm_function_params (f:cm_function_d)`)]]
    [[cst::where(`locals`, `cm_function_locals (f:cm_function_d)`)]]
    long long offset = cmc_local_offset(fn, slot);
    [[cst::proof]] {
      thm returned = assume_rule(
          `(retval:int) ==
           8i + cm_rep_members_size
             (cm_function_params (f:cm_function_d)) +
             cm_rep_member_prefix (cm_function_locals f)
               (slot__pre:int)`);
      cm_retarget_i64_st(`offset__addr:addr`,
          trans_rule(returned, cm_ast_local_offset_bridge()));
      thm code_shape = apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_cm_binding_address_code_def(),
            eqf_intro_rule(assume_rule(`~(scope__pre == 0i)`)),
            eqt_intro_rule(assume_rule(`scope__pre == 1i`)))),
          `cm_binding_address_code (p:cm_program) (fid:int)
             (scope__pre:int) (slot__pre:int)`);
      cm_ast_open_fragment(code_shape);
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    cm_emit_resolved_fp_address(emitter, offset);
    [[cst::proof]] {
      thm code_shape = apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_cm_binding_address_code_def(),
            eqf_intro_rule(assume_rule(`~(scope__pre == 0i)`)),
            eqt_intro_rule(assume_rule(`scope__pre == 1i`)))),
          `cm_binding_address_code (p:cm_program) (fid:int)
             (scope__pre:int) (slot__pre:int)`);
      cm_ast_close_fragment(code_shape);
      cm_close_function_context_st();
      cm_close_program_context_st();
    }
  } else {
    [[cst::where(`params`, `cm_function_params (f:cm_function_d)`)]]
    long long offset = cmc_param_offset(fn, slot);
    [[cst::proof]] {
      thm returned = assume_rule(
          `(retval:int) == 8i +
           cm_rep_member_prefix
             (cm_function_params (f:cm_function_d)) (slot__pre:int)`);
      cm_retarget_i64_st(`offset__addr:addr`,
          trans_rule(returned, cm_ast_param_offset_bridge()));
      thm code_shape = apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_cm_binding_address_code_def(),
            eqf_intro_rule(assume_rule(`~(scope__pre == 0i)`)),
            eqf_intro_rule(assume_rule(`~(scope__pre == 1i)`)))),
          `cm_binding_address_code (p:cm_program) (fid:int)
             (scope__pre:int) (slot__pre:int)`);
      cm_ast_open_fragment(code_shape);
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    cm_emit_resolved_fp_address(emitter, offset);
    [[cst::proof]] {
      thm code_shape = apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_cm_binding_address_code_def(),
            eqf_intro_rule(assume_rule(`~(scope__pre == 0i)`)),
            eqf_intro_rule(assume_rule(`~(scope__pre == 1i)`)))),
          `cm_binding_address_code (p:cm_program) (fid:int)
             (scope__pre:int) (slot__pre:int)`);
      cm_ast_close_fragment(code_shape);
      cm_close_function_context_st();
      cm_close_program_context_st();
    }
  }
}

void cm_emit_binding_address_plan(struct cm_program *program,
                                  struct cm_function *fn,
                                  int scope, int slot,
                                  struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `fid:int`,
                 `structs:(cm_struct_d)list`,
                 `globals:(cm_global_d)list`,
                 `functions_ptr:int`, `body:int`, `next:int`,
                 `done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(structs == cm_program_structs p) **
       fact(globals == cm_program_globals p) **
       fact(cm_binding_valid p f scope slot <=> true) **
       fact(cm_slots_wf structs (cm_function_params f) <=> true) **
       fact(cm_slots_wf structs (cm_function_locals f) <=> true) **
       fact(cm_rep_globals_safe globals <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_binding_address_code p fid scope slot ++ tail)`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(structs == cm_program_structs p) **
       fact(globals == cm_program_globals p) **
       fact(cm_binding_valid p f scope slot <=> true) **
       fact(cm_slots_wf structs (cm_function_params f) <=> true) **
       fact(cm_slots_wf structs (cm_function_locals f) <=> true) **
       fact(cm_rep_globals_safe globals <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_binding_address_code p fid scope slot) tail`)]]
{
  [[cst::proof]] {
    cm_plan_open(
        `cm_binding_address_code (p:cm_program) (fid:int)
          (scope__pre:int) (slot__pre:int)`);
  }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`f`, `(f:cm_function_d)`)]]
  [[cst::where(`fid`, `(fid:int)`)]]
  [[cst::where(`structs`, `(structs:(cm_struct_d)list)`)]]
  [[cst::where(`globals`, `(globals:(cm_global_d)list)`)]]
  cm_emit_binding_address(program, fn, scope, slot, emitter);
  [[cst::proof]] {
    cm_plan_close(
        `cm_binding_address_code (p:cm_program) (fid:int)
          (scope__pre:int) (slot__pre:int)`);
  }
}
