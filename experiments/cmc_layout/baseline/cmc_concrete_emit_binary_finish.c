#include "cmc_concrete_emit_binary_finish.h"
#include "cmc_concrete_count_context.h"
#include "cmc_concrete_layout.h"
#include "userlib/proof.h"
#require "cmc_concrete_count_context.c"
#require "cmc_concrete_layout.c"

PROOF static thm cm_pointer_value_true(const term ty) {
  return eq_mp_rule(conjunct2_rule(spec_rule(
      ty, cm_pointer_code_value_cases)), assume_rule(
        mk_not(mk_eq(mk_comb(`cm_pointer_code_value`, ty), `0i`))));
}

PROOF static thm cm_pointer_value_false(const term ty) {
  return eq_mp_rule(conjunct1_rule(spec_rule(
      ty, cm_pointer_code_value_cases)), assume_rule(
        mk_eq(mk_comb(`cm_pointer_code_value`, ty), `0i`)));
}

PROOF static thm cm_binary_finish_shape2(
    const term selected, const thm branch1, const thm branch2) {
  return eqt_elim_rule(apply_conversion(rewrite_conv(THM_LIST(
      get_cm_binary_finish_code_def(), branch1, branch2,
      get_theorem_by_name("APPEND"))),
      mk_eq(
        `cm_binary_finish_code (p:cm_program) (fid__pre:int)
           (op__pre:int) (left_e:cm_expr) (right_e:cm_expr)
           (temp__pre:int)`,
        selected)));
}

PROOF static thm cm_binary_finish_shape3(
    const term selected, const thm branch1, const thm branch2,
    const thm branch3) {
  return eqt_elim_rule(apply_conversion(rewrite_conv(THM_LIST(
      get_cm_binary_finish_code_def(), branch1, branch2, branch3,
      get_theorem_by_name("APPEND"))),
      mk_eq(
        `cm_binary_finish_code (p:cm_program) (fid__pre:int)
           (op__pre:int) (left_e:cm_expr) (right_e:cm_expr)
           (temp__pre:int)`,
        selected)));
}

PROOF static thm cm_binary_finish_shape4(
    const term selected, const thm branch1, const thm branch2,
    const thm branch3, const thm branch4) {
  return eqt_elim_rule(apply_conversion(rewrite_conv(THM_LIST(
      get_cm_binary_finish_code_def(), branch1, branch2, branch3,
      branch4, get_theorem_by_name("APPEND"))),
      mk_eq(
        `cm_binary_finish_code (p:cm_program) (fid__pre:int)
           (op__pre:int) (left_e:cm_expr) (right_e:cm_expr)
           (temp__pre:int)`,
        selected)));
}

PROOF static void cm_finish_selected_binary_st(const thm code_shape) {
  thm normalized = conv_rule(rewrite_conv(THM_LIST(
      gsym_rule(get_theorem_by_name("APPEND_ASSOC")),
      get_theorem_by_name("APPEND"),
      get_theorem_by_name("APPEND_NIL"))), code_shape);
  cm_restore_code_plan_st(normalized);
}

static long long cm_pointer_scale_value(struct cm_program *program,
                                        struct cm_expr *expr)
    [[cst::param(`p:cm_program`, `e:cm_expr`, `functions_ptr:int`)]]
    [[cst::require(
      `fact(cm_typed_program p <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       fact(cm_type_code_wf (cm_expr_type e) <=> true) **
       fact(cm_type_refs (cm_program_structs p)
              (cm_expr_type e) <=> true) **
       fact(cm_i32_code_count
              (cm_type_encode (cm_expr_type e)) <=> true) **
       fact(cm_is_pointer (cm_expr_type e) <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_expr_rep expr e`)]]
    [[cst::ensure(
      `fact(cm_typed_program p <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       fact(cm_type_code_wf (cm_expr_type e) <=> true) **
       fact(cm_type_refs (cm_program_structs p)
              (cm_expr_type e) <=> true) **
       fact(cm_i32_code_count
              (cm_type_encode (cm_expr_type e)) <=> true) **
       fact(cm_is_pointer (cm_expr_type e) <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_expr_rep expr e **
       fact((__return:int) == cm_pointer_scale p e)`)]]
{
  int type_code;
  cm_expr_type_code_context(expr, &type_code);
  [[cst::proof]] {
    thm type_wf = from_state_bool(
        `cm_type_code_wf (cm_expr_type (e:cm_expr))`);
    thm pointer = from_state_bool(
        `cm_is_pointer (cm_expr_type (e:cm_expr))`);
    thm threshold = mp_rule(spec_rule(
        `cm_expr_type (e:cm_expr)`, cm_pointer_encode_threshold),
        type_wf);
    add_fact_st(eq_mp_rule(sym_rule(threshold), pointer));
    thm encoded_bounds = conv_rule(rewrite_conv(THM_LIST(
        get_cm_i32_code_count_def())), from_state_bool(
          `cm_i32_code_count
             (cm_type_encode (cm_expr_type (e:cm_expr)))`));
    add_fact_st(conjunct2_rule(encoded_bounds));
  }
  int pointee_code = cmc_pointee(type_code);
  [[cst::proof]] {
    thm pointer = from_state_bool(
        `cm_is_pointer (cm_expr_type (e:cm_expr))`);
    thm pointee_encoding = mp_rule(spec_rule(
        `cm_expr_type (e:cm_expr)`, cm_pointer_encode_pointee),
        pointer);
    thm returned = assume_rule(
        `(retval:int) ==
         cm_type_encode (cm_expr_type (e:cm_expr)) - 1024i`);
    thm code_model = trans_rule(returned, sym_rule(pointee_encoding));
    add_fact_st(code_model);
    cst_set_symbolic_state(retarget_cell_st(
        cst_get_symbolic_state(), `pointee_code__addr:addr`,
        `retval:int`,
        `cm_type_encode (cm_pointee (cm_expr_type (e:cm_expr)))`));
    add_fact_st(eqt_intro_rule(mp_rule(mp_rule(spec_rule(
        `cm_expr_type (e:cm_expr)`, cm_type_code_wf_pointee),
        from_state_bool(
          `cm_type_code_wf (cm_expr_type (e:cm_expr))`)),
        pointer)));
    add_fact_st(eqt_intro_rule(mp_rule(mp_rule(specl_rule(TERM_LIST(
        `cm_program_structs (p:cm_program)`,
        `cm_expr_type (e:cm_expr)`), cm_type_refs_pointee),
        from_state_bool(
          `cm_type_refs (cm_program_structs (p:cm_program))
             (cm_expr_type (e:cm_expr))`)),
        pointer)));
  }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`asked`,
      `cm_pointee (cm_expr_type (e:cm_expr))`)]]
  [[cst::where(`functions_ptr`, `(functions_ptr:int)`)]]
  long long result = cm_type_size_value(program, pointee_code);
  [[cst::proof]] {
    thm scale_definition = by_rewrite(
        `cm_pointer_scale (p:cm_program) (e:cm_expr) ==
         cm_type_size (cm_program_structs p)
           (cm_pointee (cm_expr_type e))`,
        THM_LIST(get_cm_pointer_scale_def()));
    thm model = trans_rule(assume_rule(
        `(retval_1:int) ==
         cm_type_size (cm_program_structs (p:cm_program))
           (cm_pointee (cm_expr_type (e:cm_expr)))`),
        sym_rule(scale_definition));
    add_fact_st(model);
    cst_set_symbolic_state(retarget_cell64_st(
        cst_get_symbolic_state(), `result__addr:addr`,
        `retval_1:int`, `cm_pointer_scale (p:cm_program) (e:cm_expr)`));
  }
  return result;
}

static void cm_emit_binary_generic_fragment(struct cm_function *fn,
                                            int temp, int op,
                                            struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `fid:int`,
                 `body:int`, `next:int`,
                 `done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(f == inth fid (cm_program_functions p)) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_locals f) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(0i <= temp) **
       fact(cm_temp_offset p fid temp <= 2147483647i) **
       cm_function_context_rep fn f body next **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_temp_load_code p fid temp ++
          ([TVMInst TVMSwapOp 0i;
            TVMInst (cm_binary_opcode op) 0i] ++ tail))`)]]
    [[cst::ensure(
      `fact(f == inth fid (cm_program_functions p)) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_locals f) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(0i <= temp) **
       fact(cm_temp_offset p fid temp <= 2147483647i) **
       cm_function_context_rep fn f body next **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++
          (cm_temp_load_code p fid temp ++
           [TVMInst TVMSwapOp 0i;
            TVMInst (cm_binary_opcode op) 0i]))
         tail`)]]
{
  [[cst::proof]] {
    rewrite_st(THM_LIST(gsym_rule(get_theorem_by_name("APPEND_ASSOC"))));
  }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`f`, `(f:cm_function_d)`)]]
  [[cst::where(`fid`, `(fid:int)`)]]
  [[cst::where(`structs`, `cm_program_structs (p:cm_program)`)]]
  [[cst::where(`body`, `(body:int)`)]]
  [[cst::where(`next`, `(next:int)`)]]
  cm_emit_temp_load_plan(fn, temp, emitter);
  [[cst::proof]] {
    rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
    cm_add_opcode_facts_st(`3i`, `TVMSwapOp`);
  }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`opcode`, `TVMSwapOp`)]]
  cm_emit_plan(emitter, CMC_OP_SWAP, 0);
  int opcode = cmc_binary_opcode(op);
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`opcode`, `cm_binary_opcode (op__pre:int)`)]]
  cm_emit_plan(emitter, opcode, 0);
  [[cst::proof]] {
    rewrite_st(THM_LIST(
        gsym_rule(get_theorem_by_name("APPEND_ASSOC")),
        get_theorem_by_name("APPEND")));
  }
}

void cm_emit_binary_finish_plan(struct cm_program *program, int fid,
                                struct cm_function *fn, int temp, int op,
                                struct cm_expr *left,
                                struct cm_expr *right,
                                struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`,
                 `left_e:cm_expr`, `right_e:cm_expr`,
                 `body:int`, `next:int`, `functions_ptr:int`,
                 `done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(cm_typed_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_locals f) <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_type_code_wf (cm_expr_type left_e) <=> true) **
       fact(cm_type_code_wf (cm_expr_type right_e) <=> true) **
       fact(cm_type_refs (cm_program_structs p)
              (cm_expr_type left_e) <=> true) **
       fact(cm_type_refs (cm_program_structs p)
              (cm_expr_type right_e) <=> true) **
       fact(cm_i32_code_count
              (cm_type_encode (cm_expr_type left_e)) <=> true) **
       fact(cm_i32_code_count
              (cm_type_encode (cm_expr_type right_e)) <=> true) **
       fact(0i <= temp) **
       fact(cm_temp_offset p fid temp <= 2147483647i) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep left left_e **
       cm_expr_rep right right_e **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_binary_finish_code p fid op left_e right_e temp ++ tail)`)]]
    [[cst::ensure(
      `fact(cm_typed_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_locals f) <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_type_code_wf (cm_expr_type left_e) <=> true) **
       fact(cm_type_code_wf (cm_expr_type right_e) <=> true) **
       fact(cm_type_refs (cm_program_structs p)
              (cm_expr_type left_e) <=> true) **
       fact(cm_type_refs (cm_program_structs p)
              (cm_expr_type right_e) <=> true) **
       fact(cm_i32_code_count
              (cm_type_encode (cm_expr_type left_e)) <=> true) **
       fact(cm_i32_code_count
              (cm_type_encode (cm_expr_type right_e)) <=> true) **
       fact(0i <= temp) **
       fact(cm_temp_offset p fid temp <= 2147483647i) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep left left_e **
       cm_expr_rep right right_e **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_binary_finish_code p fid op left_e right_e temp)
         tail`)]]
{
  int left_type;
  int right_type;
  cm_expr_type_code_context(left, &left_type);
  cm_expr_type_code_context(right, &right_type);
  int left_pointer;
  int right_pointer;
  cmc_is_pointer_value(left_type, &left_pointer);
  [[cst::proof]] {
    thm bridge = mp_rule(spec_rule(
        `cm_expr_type (left_e:cm_expr)`, cm_pointer_code_bridge),
        from_state_bool(
          `cm_type_code_wf (cm_expr_type (left_e:cm_expr))`));
    substitute_st(bridge);
  }
  cmc_is_pointer_value(right_type, &right_pointer);
  [[cst::proof]] {
    thm bridge = mp_rule(spec_rule(
        `cm_expr_type (right_e:cm_expr)`, cm_pointer_code_bridge),
        from_state_bool(
          `cm_type_code_wf (cm_expr_type (right_e:cm_expr))`));
    substitute_st(bridge);
  }

  if (op == CMC_BIN_ADD && right_pointer) {
    [[cst::proof]] {
      thm pointer = cm_pointer_value_true(
          `cm_expr_type (right_e:cm_expr)`);
      add_fact_st(eqt_intro_rule(pointer));
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`e`, `(right_e:cm_expr)`)]]
    [[cst::where(`functions_ptr`, `(functions_ptr:int)`)]]
    long long scale = cm_pointer_scale_value(program, right);
    [[cst::proof]] {
      cst_set_symbolic_state(retarget_cell64_st(
          cst_get_symbolic_state(), `scale__addr:addr`, `retval:int`,
          `cm_pointer_scale (p:cm_program) (right_e:cm_expr)`));
    }
    [[cst::proof]] {
      thm op_case = eqt_intro_rule(assume_rule(`op__pre == 8i`));
      thm pointer_case = eqt_intro_rule(from_state_bool(
          `cm_is_pointer (cm_expr_type (right_e:cm_expr))`));
      thm code_shape = cm_binary_finish_shape2(
          `cm_temp_load_code (p:cm_program) (fid__pre:int)
             (temp__pre:int) ++
           [TVMInst TVMPushOp (cm_pointer_scale p (right_e:cm_expr));
            TVMInst TVMMulOp 0i; TVMInst TVMSwapOp 0i;
            TVMInst TVMAddOp 0i]`,
          op_case, pointer_case);
      cm_select_code_plan_st(code_shape);
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`fid`, `(fid__pre:int)`)]]
    [[cst::where(`structs`, `cm_program_structs (p:cm_program)`)]]
    cm_emit_temp_load_plan(fn, temp, emitter);
    [[cst::proof]] {
      rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
      cm_add_opcode_facts_st(`0i`, `TVMPushOp`);
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`opcode`, `TVMPushOp`)]]
    cm_emit_plan(emitter, CMC_OP_PUSH, scale);
    [[cst::proof]] { cm_add_opcode_facts_st(`10i`, `TVMMulOp`); }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`opcode`, `TVMMulOp`)]]
    cm_emit_plan(emitter, CMC_OP_MUL, 0);
    [[cst::proof]] { cm_add_opcode_facts_st(`3i`, `TVMSwapOp`); }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`opcode`, `TVMSwapOp`)]]
    cm_emit_plan(emitter, CMC_OP_SWAP, 0);
    [[cst::proof]] { cm_add_opcode_facts_st(`8i`, `TVMAddOp`); }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`opcode`, `TVMAddOp`)]]
    cm_emit_plan(emitter, CMC_OP_ADD, 0);
    [[cst::proof]] {
      thm code_shape = cm_binary_finish_shape2(
          `cm_temp_load_code (p:cm_program) (fid__pre:int)
             (temp__pre:int) ++
           [TVMInst TVMPushOp (cm_pointer_scale p (right_e:cm_expr));
            TVMInst TVMMulOp 0i; TVMInst TVMSwapOp 0i;
            TVMInst TVMAddOp 0i]`,
          eqt_intro_rule(assume_rule(`op__pre == 8i`)),
          eqt_intro_rule(from_state_bool(
            `cm_is_pointer (cm_expr_type (right_e:cm_expr))`)));
      cm_finish_selected_binary_st(code_shape);
    }
  } else {
    [[cst::proof]] {
      cm_add_opcode_facts_st(`3i`, `TVMSwapOp`);
    }
    if (op == CMC_BIN_ADD && left_pointer) {
      [[cst::proof]] {
        thm left_pointer_case = cm_pointer_value_true(
            `cm_expr_type (left_e:cm_expr)`);
        add_fact_st(eqt_intro_rule(left_pointer_case));
      }
      [[cst::where(`p`, `(p:cm_program)`)]]
      [[cst::where(`e`, `(left_e:cm_expr)`)]]
      [[cst::where(`functions_ptr`, `(functions_ptr:int)`)]]
      long long scale = cm_pointer_scale_value(program, left);
      [[cst::proof]] {
        cst_set_symbolic_state(retarget_cell64_st(
            cst_get_symbolic_state(), `scale__addr:addr`, `retval:int`,
            `cm_pointer_scale (p:cm_program) (left_e:cm_expr)`));
      }
      [[cst::proof]] {
        thm code_shape = cm_binary_finish_shape3(
            `cm_temp_load_code (p:cm_program) (fid__pre:int)
               (temp__pre:int) ++
             [TVMInst TVMSwapOp 0i;
              TVMInst TVMPushOp (cm_pointer_scale p (left_e:cm_expr));
              TVMInst TVMMulOp 0i; TVMInst TVMAddOp 0i]`,
            eqt_intro_rule(assume_rule(`op__pre == 8i`)),
            eqf_intro_rule(cm_pointer_value_false(
              `cm_expr_type (right_e:cm_expr)`)),
            eqt_intro_rule(from_state_bool(
              `cm_is_pointer (cm_expr_type (left_e:cm_expr))`)));
        cm_select_code_plan_st(code_shape);
      }
      [[cst::where(`p`, `(p:cm_program)`)]]
      [[cst::where(`f`, `(f:cm_function_d)`)]]
      [[cst::where(`fid`, `(fid__pre:int)`)]]
      [[cst::where(`structs`, `cm_program_structs (p:cm_program)`)]]
      cm_emit_temp_load_plan(fn, temp, emitter);
      [[cst::proof]] { rewrite_st(THM_LIST(get_theorem_by_name("APPEND"))); }
      [[cst::where(`p`, `(p:cm_program)`)]]
      [[cst::where(`opcode`, `TVMSwapOp`)]]
      cm_emit_plan(emitter, CMC_OP_SWAP, 0);
      [[cst::proof]] { cm_add_opcode_facts_st(`0i`, `TVMPushOp`); }
      [[cst::where(`p`, `(p:cm_program)`)]]
      [[cst::where(`opcode`, `TVMPushOp`)]]
      cm_emit_plan(emitter, CMC_OP_PUSH, scale);
      [[cst::proof]] { cm_add_opcode_facts_st(`10i`, `TVMMulOp`); }
      [[cst::where(`p`, `(p:cm_program)`)]]
      [[cst::where(`opcode`, `TVMMulOp`)]]
      cm_emit_plan(emitter, CMC_OP_MUL, 0);
      [[cst::proof]] { cm_add_opcode_facts_st(`8i`, `TVMAddOp`); }
      [[cst::where(`p`, `(p:cm_program)`)]]
      [[cst::where(`opcode`, `TVMAddOp`)]]
      cm_emit_plan(emitter, CMC_OP_ADD, 0);
      [[cst::proof]] {
        thm code_shape = cm_binary_finish_shape3(
            `cm_temp_load_code (p:cm_program) (fid__pre:int)
               (temp__pre:int) ++
             [TVMInst TVMSwapOp 0i;
              TVMInst TVMPushOp (cm_pointer_scale p (left_e:cm_expr));
              TVMInst TVMMulOp 0i; TVMInst TVMAddOp 0i]`,
            eqt_intro_rule(assume_rule(`op__pre == 8i`)),
            eqf_intro_rule(cm_pointer_value_false(
              `cm_expr_type (right_e:cm_expr)`)),
            eqt_intro_rule(from_state_bool(
              `cm_is_pointer (cm_expr_type (left_e:cm_expr))`)));
        cm_finish_selected_binary_st(code_shape);
      }
    } else if (op == CMC_BIN_SUB && left_pointer && right_pointer) {
      [[cst::proof]] {
        thm left_pointer_case = cm_pointer_value_true(
            `cm_expr_type (left_e:cm_expr)`);
        thm right_pointer_case = cm_pointer_value_true(
            `cm_expr_type (right_e:cm_expr)`);
        add_fact_st(eqt_intro_rule(left_pointer_case));
        add_fact_st(eqt_intro_rule(right_pointer_case));
      }
      [[cst::where(`p`, `(p:cm_program)`)]]
      [[cst::where(`e`, `(left_e:cm_expr)`)]]
      [[cst::where(`functions_ptr`, `(functions_ptr:int)`)]]
      long long scale = cm_pointer_scale_value(program, left);
      [[cst::proof]] {
        cst_set_symbolic_state(retarget_cell64_st(
            cst_get_symbolic_state(), `scale__addr:addr`, `retval:int`,
            `cm_pointer_scale (p:cm_program) (left_e:cm_expr)`));
      }
      [[cst::proof]] {
        thm code_shape = cm_binary_finish_shape4(
            `cm_temp_load_code (p:cm_program) (fid__pre:int)
               (temp__pre:int) ++
             [TVMInst TVMSwapOp 0i; TVMInst TVMSubOp 0i;
              TVMInst TVMPushOp (cm_pointer_scale p (left_e:cm_expr));
              TVMInst TVMDivOp 0i]`,
            eqf_intro_rule(assume_rule(`~(op__pre == 8i)`)),
            eqt_intro_rule(assume_rule(`op__pre == 9i`)),
            eqt_intro_rule(from_state_bool(
              `cm_is_pointer (cm_expr_type (left_e:cm_expr))`)),
            eqt_intro_rule(from_state_bool(
              `cm_is_pointer (cm_expr_type (right_e:cm_expr))`)));
        cm_select_code_plan_st(code_shape);
      }
      [[cst::where(`p`, `(p:cm_program)`)]]
      [[cst::where(`f`, `(f:cm_function_d)`)]]
      [[cst::where(`fid`, `(fid__pre:int)`)]]
      [[cst::where(`structs`, `cm_program_structs (p:cm_program)`)]]
      cm_emit_temp_load_plan(fn, temp, emitter);
      [[cst::proof]] { rewrite_st(THM_LIST(get_theorem_by_name("APPEND"))); }
      [[cst::where(`p`, `(p:cm_program)`)]]
      [[cst::where(`opcode`, `TVMSwapOp`)]]
      cm_emit_plan(emitter, CMC_OP_SWAP, 0);
      [[cst::proof]] { cm_add_opcode_facts_st(`9i`, `TVMSubOp`); }
      [[cst::where(`p`, `(p:cm_program)`)]]
      [[cst::where(`opcode`, `TVMSubOp`)]]
      cm_emit_plan(emitter, CMC_OP_SUB, 0);
      [[cst::proof]] { cm_add_opcode_facts_st(`0i`, `TVMPushOp`); }
      [[cst::where(`p`, `(p:cm_program)`)]]
      [[cst::where(`opcode`, `TVMPushOp`)]]
      cm_emit_plan(emitter, CMC_OP_PUSH, scale);
      [[cst::proof]] { cm_add_opcode_facts_st(`11i`, `TVMDivOp`); }
      [[cst::where(`p`, `(p:cm_program)`)]]
      [[cst::where(`opcode`, `TVMDivOp`)]]
      cm_emit_plan(emitter, CMC_OP_DIV, 0);
      [[cst::proof]] {
        thm code_shape = cm_binary_finish_shape4(
            `cm_temp_load_code (p:cm_program) (fid__pre:int)
               (temp__pre:int) ++
             [TVMInst TVMSwapOp 0i; TVMInst TVMSubOp 0i;
              TVMInst TVMPushOp (cm_pointer_scale p (left_e:cm_expr));
              TVMInst TVMDivOp 0i]`,
            eqf_intro_rule(assume_rule(`~(op__pre == 8i)`)),
            eqt_intro_rule(assume_rule(`op__pre == 9i`)),
            eqt_intro_rule(from_state_bool(
              `cm_is_pointer (cm_expr_type (left_e:cm_expr))`)),
            eqt_intro_rule(from_state_bool(
              `cm_is_pointer (cm_expr_type (right_e:cm_expr))`)));
        cm_finish_selected_binary_st(code_shape);
      }
    } else if (op == CMC_BIN_SUB && left_pointer) {
      [[cst::proof]] {
        thm left_pointer_case = cm_pointer_value_true(
            `cm_expr_type (left_e:cm_expr)`);
        add_fact_st(eqt_intro_rule(left_pointer_case));
      }
      [[cst::where(`p`, `(p:cm_program)`)]]
      [[cst::where(`e`, `(left_e:cm_expr)`)]]
      [[cst::where(`functions_ptr`, `(functions_ptr:int)`)]]
      long long scale = cm_pointer_scale_value(program, left);
      [[cst::proof]] {
        cst_set_symbolic_state(retarget_cell64_st(
            cst_get_symbolic_state(), `scale__addr:addr`, `retval:int`,
            `cm_pointer_scale (p:cm_program) (left_e:cm_expr)`));
      }
      [[cst::proof]] {
        thm code_shape = cm_binary_finish_shape4(
            `cm_temp_load_code (p:cm_program) (fid__pre:int)
               (temp__pre:int) ++
             [TVMInst TVMSwapOp 0i;
              TVMInst TVMPushOp (cm_pointer_scale p (left_e:cm_expr));
              TVMInst TVMMulOp 0i; TVMInst TVMSubOp 0i]`,
            eqf_intro_rule(assume_rule(`~(op__pre == 8i)`)),
            eqt_intro_rule(assume_rule(`op__pre == 9i`)),
            eqt_intro_rule(from_state_bool(
              `cm_is_pointer (cm_expr_type (left_e:cm_expr))`)),
            eqf_intro_rule(cm_pointer_value_false(
              `cm_expr_type (right_e:cm_expr)`)));
        cm_select_code_plan_st(code_shape);
      }
      [[cst::where(`p`, `(p:cm_program)`)]]
      [[cst::where(`f`, `(f:cm_function_d)`)]]
      [[cst::where(`fid`, `(fid__pre:int)`)]]
      [[cst::where(`structs`, `cm_program_structs (p:cm_program)`)]]
      cm_emit_temp_load_plan(fn, temp, emitter);
      [[cst::proof]] { rewrite_st(THM_LIST(get_theorem_by_name("APPEND"))); }
      [[cst::where(`p`, `(p:cm_program)`)]]
      [[cst::where(`opcode`, `TVMSwapOp`)]]
      cm_emit_plan(emitter, CMC_OP_SWAP, 0);
      [[cst::proof]] { cm_add_opcode_facts_st(`0i`, `TVMPushOp`); }
      [[cst::where(`p`, `(p:cm_program)`)]]
      [[cst::where(`opcode`, `TVMPushOp`)]]
      cm_emit_plan(emitter, CMC_OP_PUSH, scale);
      [[cst::proof]] { cm_add_opcode_facts_st(`10i`, `TVMMulOp`); }
      [[cst::where(`p`, `(p:cm_program)`)]]
      [[cst::where(`opcode`, `TVMMulOp`)]]
      cm_emit_plan(emitter, CMC_OP_MUL, 0);
      [[cst::proof]] { cm_add_opcode_facts_st(`9i`, `TVMSubOp`); }
      [[cst::where(`p`, `(p:cm_program)`)]]
      [[cst::where(`opcode`, `TVMSubOp`)]]
      cm_emit_plan(emitter, CMC_OP_SUB, 0);
      [[cst::proof]] {
        thm code_shape = cm_binary_finish_shape4(
            `cm_temp_load_code (p:cm_program) (fid__pre:int)
               (temp__pre:int) ++
             [TVMInst TVMSwapOp 0i;
              TVMInst TVMPushOp (cm_pointer_scale p (left_e:cm_expr));
              TVMInst TVMMulOp 0i; TVMInst TVMSubOp 0i]`,
            eqf_intro_rule(assume_rule(`~(op__pre == 8i)`)),
            eqt_intro_rule(assume_rule(`op__pre == 9i`)),
            eqt_intro_rule(from_state_bool(
              `cm_is_pointer (cm_expr_type (left_e:cm_expr))`)),
            eqf_intro_rule(cm_pointer_value_false(
              `cm_expr_type (right_e:cm_expr)`)));
        cm_finish_selected_binary_st(code_shape);
      }
    } else {
      if (op == CMC_BIN_ADD) {
        [[cst::proof]] {
          thm right_nonpointer = cm_pointer_value_false(
              `cm_expr_type (right_e:cm_expr)`);
          thm left_nonpointer = cm_pointer_value_false(
              `cm_expr_type (left_e:cm_expr)`);
          thm code_shape = cm_binary_finish_shape3(
              `cm_temp_load_code (p:cm_program) (fid__pre:int)
                 (temp__pre:int) ++
               [TVMInst TVMSwapOp 0i;
                TVMInst (cm_binary_opcode (op__pre:int)) 0i]`,
              eqt_intro_rule(assume_rule(`op__pre == 8i`)),
              eqf_intro_rule(right_nonpointer),
              eqf_intro_rule(left_nonpointer));
          cm_select_code_plan_st(code_shape);
        }
        [[cst::where(`p`, `(p:cm_program)`)]]
        [[cst::where(`f`, `(f:cm_function_d)`)]]
        [[cst::where(`fid`, `(fid__pre:int)`)]]
        [[cst::where(`body`, `(body:int)`)]]
        [[cst::where(`next`, `(next:int)`)]]
        cm_emit_binary_generic_fragment(fn, temp, op, emitter);
        [[cst::proof]] {
          thm code_shape = cm_binary_finish_shape3(
              `cm_temp_load_code (p:cm_program) (fid__pre:int)
                 (temp__pre:int) ++
               [TVMInst TVMSwapOp 0i;
                TVMInst (cm_binary_opcode (op__pre:int)) 0i]`,
              eqt_intro_rule(assume_rule(`op__pre == 8i`)),
              eqf_intro_rule(cm_pointer_value_false(
                `cm_expr_type (right_e:cm_expr)`)),
              eqf_intro_rule(cm_pointer_value_false(
                `cm_expr_type (left_e:cm_expr)`)));
          cm_finish_selected_binary_st(code_shape);
        }
      } else if (op == CMC_BIN_SUB) {
        [[cst::proof]] {
          thm left_nonpointer = cm_pointer_value_false(
              `cm_expr_type (left_e:cm_expr)`);
          thm code_shape = cm_binary_finish_shape3(
              `cm_temp_load_code (p:cm_program) (fid__pre:int)
                 (temp__pre:int) ++
               [TVMInst TVMSwapOp 0i;
                TVMInst (cm_binary_opcode (op__pre:int)) 0i]`,
              eqf_intro_rule(assume_rule(`~(op__pre == 8i)`)),
              eqt_intro_rule(assume_rule(`op__pre == 9i`)),
              eqf_intro_rule(left_nonpointer));
          cm_select_code_plan_st(code_shape);
        }
        [[cst::where(`p`, `(p:cm_program)`)]]
        [[cst::where(`f`, `(f:cm_function_d)`)]]
        [[cst::where(`fid`, `(fid__pre:int)`)]]
        [[cst::where(`body`, `(body:int)`)]]
        [[cst::where(`next`, `(next:int)`)]]
        cm_emit_binary_generic_fragment(fn, temp, op, emitter);
        [[cst::proof]] {
          thm code_shape = cm_binary_finish_shape3(
              `cm_temp_load_code (p:cm_program) (fid__pre:int)
                 (temp__pre:int) ++
               [TVMInst TVMSwapOp 0i;
                TVMInst (cm_binary_opcode (op__pre:int)) 0i]`,
              eqf_intro_rule(assume_rule(`~(op__pre == 8i)`)),
              eqt_intro_rule(assume_rule(`op__pre == 9i`)),
              eqf_intro_rule(cm_pointer_value_false(
                `cm_expr_type (left_e:cm_expr)`)));
          cm_finish_selected_binary_st(code_shape);
        }
      } else {
        [[cst::proof]] {
          thm code_shape = cm_binary_finish_shape2(
              `cm_temp_load_code (p:cm_program) (fid__pre:int)
                 (temp__pre:int) ++
               [TVMInst TVMSwapOp 0i;
                TVMInst (cm_binary_opcode (op__pre:int)) 0i]`,
              eqf_intro_rule(assume_rule(`~(op__pre == 8i)`)),
              eqf_intro_rule(assume_rule(`~(op__pre == 9i)`)));
          cm_select_code_plan_st(code_shape);
        }
        [[cst::where(`p`, `(p:cm_program)`)]]
        [[cst::where(`f`, `(f:cm_function_d)`)]]
        [[cst::where(`fid`, `(fid__pre:int)`)]]
        [[cst::where(`body`, `(body:int)`)]]
        [[cst::where(`next`, `(next:int)`)]]
        cm_emit_binary_generic_fragment(fn, temp, op, emitter);
        [[cst::proof]] {
          thm code_shape = cm_binary_finish_shape2(
              `cm_temp_load_code (p:cm_program) (fid__pre:int)
                 (temp__pre:int) ++
               [TVMInst TVMSwapOp 0i;
                TVMInst (cm_binary_opcode (op__pre:int)) 0i]`,
              eqf_intro_rule(assume_rule(`~(op__pre == 8i)`)),
              eqf_intro_rule(assume_rule(`~(op__pre == 9i)`)));
          cm_finish_selected_binary_st(code_shape);
        }
      }
    }
  }
}
