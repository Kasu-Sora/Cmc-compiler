#include "cmc_concrete_emit_plan.h"
#include "userlib/proof.h"
#include "userlib/operational.h"
#require "cmc_concrete_emit_resolved.c"


PROOF static void cm_plan_add_singleton_capacity(void) {
  thm input_capacity = conv_rule(rewrite_conv(THM_LIST(
      get_theorem_by_name("APPEND"),
      get_theorem_by_name("ILENGTH_DEF"))), assume_rule(
      `ilength (done:(tvm_inst)list) +
         ilength ([TVMInst (opcode:tvm_opcode)
                    (immediate__pre:int)] ++
                   (tail:(tvm_inst)list)) <= (capacity:int)`));
  thm tail_nonnegative = ispec_rule(
      `tail:(tvm_inst)list`, get_theorem_by_name("ILENGTH_NONNEG"));
  add_fact_st(by_defs_arith(
      `ilength (done:(tvm_inst)list) + 1i <= (capacity:int)`,
      THM_LIST(get_theorem_by_name("ILENGTH_APPEND"),
               get_theorem_by_name("ILENGTH_DEF")),
      THM_LIST(input_capacity, tail_nonnegative)));
}

PROOF static void cm_plan_add_call_capacity(void) {
  thm input_capacity = conv_rule(rewrite_conv(THM_LIST(
      get_theorem_by_name("APPEND"),
      get_theorem_by_name("ILENGTH_DEF"))), assume_rule(
      `ilength (done:(tvm_inst)list) +
         ilength ([TVMInst TVMCallOp
                    (cm_function_pc (p:cm_program)
                      (function_id__pre:int))] ++
                   (tail:(tvm_inst)list)) <= (capacity:int)`));
  thm tail_nonnegative = ispec_rule(
      `tail:(tvm_inst)list`, get_theorem_by_name("ILENGTH_NONNEG"));
  add_fact_st(by_defs_arith(
      `ilength (done:(tvm_inst)list) + 1i <= (capacity:int)`,
      THM_LIST(get_theorem_by_name("ILENGTH_APPEND"),
               get_theorem_by_name("ILENGTH_DEF")),
      THM_LIST(input_capacity, tail_nonnegative)));
}


void cm_emit_plan(struct cm_emitter *emitter, int op,
                  long long immediate)
    [[cst::param(`p:cm_program`, `done:(tvm_inst)list`,
                 `tail:(tvm_inst)list`, `opcode:tvm_opcode`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(op == tvm_opcode_code opcode) **
       fact(~(tvm_opcode_code opcode == 22i)) **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (TVMInst opcode immediate :: tail)`)]]
    [[cst::ensure(
      `cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ [TVMInst opcode immediate]) tail`)]]
{
  [[cst::proof]] {
    term fragment =
        `[TVMInst (opcode:tvm_opcode) (immediate__pre:int)]`;
    substitute_st(by_rewrite(
        `(TVMInst (opcode:tvm_opcode) (immediate__pre:int) ::
            (tail:(tvm_inst)list)) ==
         [TVMInst opcode immediate__pre] ++ tail`,
        THM_LIST(get_theorem_by_name("APPEND"))));
    cm_plan_open(fragment);
    cm_plan_add_singleton_capacity();
  }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`opcode`, `(opcode:tvm_opcode)`)]]
  cm_emit_resolved(emitter, op, immediate);
  [[cst::proof]] {
    cm_plan_close(
        `[TVMInst (opcode:tvm_opcode) (immediate__pre:int)]`);
  }
}

void cm_emit_call_plan(struct cm_emitter *emitter, int function_id)
    [[cst::param(`p:cm_program`, `done:(tvm_inst)list`,
                 `tail:(tvm_inst)list`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `cm_resolved_emitter_plan_rep p emitter out capacity done
         (TVMInst TVMCallOp (cm_function_pc p function_id) :: tail)`)]]
    [[cst::ensure(
      `cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ [TVMInst TVMCallOp
                    (cm_function_pc p function_id)]) tail`)]]
{
  [[cst::proof]] {
    term fragment =
        `[TVMInst TVMCallOp
           (cm_function_pc (p:cm_program) (function_id__pre:int))]`;
    substitute_st(by_rewrite(
        `(TVMInst TVMCallOp
            (cm_function_pc (p:cm_program) (function_id__pre:int)) ::
            (tail:(tvm_inst)list)) ==
         [TVMInst TVMCallOp (cm_function_pc p function_id__pre)] ++ tail`,
        THM_LIST(get_theorem_by_name("APPEND"))));
    cm_plan_open(fragment);
    cm_plan_add_call_capacity();
  }
  [[cst::where(`p`, `(p:cm_program)`)]]
  cm_emit_resolved_call(emitter, function_id);
  [[cst::proof]] {
    cm_plan_close(
        `[TVMInst TVMCallOp
           (cm_function_pc (p:cm_program) (function_id__pre:int))]`);
  }
}

void cm_emit_normalize_plan(struct cm_emitter *emitter, int ty)
    [[cst::param(`p:cm_program`, `model_ty:cm_type`,
                 `done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(ty == cm_type_encode model_ty) **
       fact(cm_type_code_wf model_ty <=> true) **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_char_normalize_code model_ty ++ tail)`)]]
    [[cst::ensure(
      `cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_char_normalize_code model_ty) tail`)]]
{
  [[cst::proof]] {
    cm_plan_open(`cm_char_normalize_code (model_ty:cm_type)`);
  }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`model_ty`, `(model_ty:cm_type)`)]]
  cm_emit_resolved_normalize(emitter, ty);
  [[cst::proof]] {
    cm_plan_close(`cm_char_normalize_code (model_ty:cm_type)`);
  }
}

void cm_emit_load_plan(struct cm_emitter *emitter, int ty)
    [[cst::param(`p:cm_program`, `model_ty:cm_type`,
                 `done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(ty == cm_type_encode model_ty) **
       fact(cm_type_code_wf model_ty <=> true) **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_load_code model_ty ++ tail)`)]]
    [[cst::ensure(
      `cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_load_code model_ty) tail`)]]
{
  [[cst::proof]] { cm_plan_open(`cm_load_code (model_ty:cm_type)`); }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`model_ty`, `(model_ty:cm_type)`)]]
  cm_emit_resolved_load(emitter, ty);
  [[cst::proof]] { cm_plan_close(`cm_load_code (model_ty:cm_type)`); }
}

void cm_emit_store_plan(struct cm_emitter *emitter, int ty)
    [[cst::param(`p:cm_program`, `model_ty:cm_type`,
                 `done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(ty == cm_type_encode model_ty) **
       fact(cm_type_code_wf model_ty <=> true) **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_store_code model_ty ++ tail)`)]]
    [[cst::ensure(
      `cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_store_code model_ty) tail`)]]
{
  [[cst::proof]] { cm_plan_open(`cm_store_code (model_ty:cm_type)`); }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`model_ty`, `(model_ty:cm_type)`)]]
  cm_emit_resolved_store(emitter, ty);
  [[cst::proof]] { cm_plan_close(`cm_store_code (model_ty:cm_type)`); }
}

void cm_emit_fp_address_plan(struct cm_emitter *emitter,
                             long long offset)
    [[cst::param(`p:cm_program`, `done:(tvm_inst)list`,
                 `tail:(tvm_inst)list`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_fp_relative_address_code offset ++ tail)`)]]
    [[cst::ensure(
      `cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_fp_relative_address_code offset) tail`)]]
{
  [[cst::proof]] {
    cm_plan_open(
        `cm_fp_relative_address_code (offset__pre:int)`);
  }
  [[cst::where(`p`, `(p:cm_program)`)]]
  cm_emit_resolved_fp_address(emitter, offset);
  [[cst::proof]] {
    cm_plan_close(
        `cm_fp_relative_address_code (offset__pre:int)`);
  }
}

void cm_emit_temp_store_plan(struct cm_function *fn, int temp,
                             struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `fid:int`,
                 `structs:(cm_struct_d)list`, `body:int`, `next:int`,
                 `done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(0i <= temp) **
       fact(structs == cm_program_structs p) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_slots_wf structs (cm_function_params f) <=> true) **
       fact(cm_slots_wf structs (cm_function_locals f) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_temp_offset p fid temp <= 2147483647i) **
       cm_function_context_rep fn f body next **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_temp_store_code p fid temp ++ tail)`)]]
    [[cst::ensure(
      `fact(0i <= temp) **
       fact(structs == cm_program_structs p) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_slots_wf structs (cm_function_params f) <=> true) **
       fact(cm_slots_wf structs (cm_function_locals f) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_temp_offset p fid temp <= 2147483647i) **
       cm_function_context_rep fn f body next **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_temp_store_code p fid temp) tail`)]]
{
  [[cst::proof]] {
    cm_plan_open(
        `cm_temp_store_code (p:cm_program) (fid:int) (temp__pre:int)`);
  }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`f`, `(f:cm_function_d)`)]]
  [[cst::where(`fid`, `(fid:int)`)]]
  [[cst::where(`structs`, `structs:(cm_struct_d)list`)]]
  [[cst::where(`body`, `(body:int)`)]]
  [[cst::where(`next`, `(next:int)`)]]
  cm_emit_resolved_temp_store(fn, temp, emitter);
  [[cst::proof]] {
    cm_plan_close(
        `cm_temp_store_code (p:cm_program) (fid:int) (temp__pre:int)`);
  }
}

void cm_emit_temp_load_plan(struct cm_function *fn, int temp,
                            struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `fid:int`,
                 `structs:(cm_struct_d)list`, `body:int`, `next:int`,
                 `done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(0i <= temp) **
       fact(structs == cm_program_structs p) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_slots_wf structs (cm_function_params f) <=> true) **
       fact(cm_slots_wf structs (cm_function_locals f) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_temp_offset p fid temp <= 2147483647i) **
       cm_function_context_rep fn f body next **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_temp_load_code p fid temp ++ tail)`)]]
    [[cst::ensure(
      `fact(0i <= temp) **
       fact(structs == cm_program_structs p) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_slots_wf structs (cm_function_params f) <=> true) **
       fact(cm_slots_wf structs (cm_function_locals f) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_temp_offset p fid temp <= 2147483647i) **
       cm_function_context_rep fn f body next **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_temp_load_code p fid temp) tail`)]]
{
  [[cst::proof]] {
    cm_plan_open(
        `cm_temp_load_code (p:cm_program) (fid:int) (temp__pre:int)`);
  }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`f`, `(f:cm_function_d)`)]]
  [[cst::where(`fid`, `(fid:int)`)]]
  [[cst::where(`structs`, `structs:(cm_struct_d)list`)]]
  [[cst::where(`body`, `(body:int)`)]]
  [[cst::where(`next`, `(next:int)`)]]
  cm_emit_resolved_temp_load(fn, temp, emitter);
  [[cst::proof]] {
    cm_plan_close(
        `cm_temp_load_code (p:cm_program) (fid:int) (temp__pre:int)`);
  }
}
