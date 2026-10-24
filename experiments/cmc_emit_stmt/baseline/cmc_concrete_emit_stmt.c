#include "cmc_concrete_emit_stmt.h"
#include "cmc_concrete_emit_stmt_proof.h"
#include "cmc_concrete_emit_return.h"
#include "cmc_concrete_emit_stmt_if.h"
#include "cmc_concrete_emit_ast.h"
#include "userlib/proof.h"
#include "userlib/operational.h"
#require "cmc_concrete_emit_expr.c"
#require "cmc_concrete_emit_return.c"
#require "cmc_concrete_emit_ast.c"
#require "cmc_concrete_emit_stmt_proof.c"
#require "cmc_concrete_count_context.c"

PROOF static void cm_add_stmt_count_bounds_st(const thm shape) {
  cm_add_i32_term_st(from_state_bool(
      `cm_i32_code_count (pc__pre:int)`));
  thm length = cm_stmt_code_length_at(`s:cm_stmt`, `pc__pre:int`,
      `temp__pre:int`, `break_pc__pre:int`, `continue_pc__pre:int`);
  thm end = conv_rule(rewrite_conv(THM_LIST(length)), from_state_bool(
      `cm_i32_code_count
        ((pc__pre:int) + ilength
          (cm_emit_stmt (p:cm_program) (fid__pre:int) pc__pre
            (temp__pre:int) (break_pc__pre:int)
            (continue_pc__pre:int) (s:cm_stmt)))`));
  end = conv_rule(rewrite_conv(THM_LIST(shape)), end);
  cm_add_i32_term_st(end);
  cm_add_i32_term_st(conv_rule(rewrite_conv(THM_LIST(
      get_cm_stmt_code_count_def())), end));
}

void cmc_emit_if_stmt(struct cm_program *program, int fid,
                      struct cm_function *fn, int pc, int temp,
                      int temp_limit, int break_pc, int continue_pc,
                      struct cm_stmt *stmt, struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `s:cm_stmt`,
                 `guard_:cm_expr`, `yes_:cm_stmt`, `no_:cm_stmt`,
                 `loop_:bool`, `body:int`, `next:int`,
                 `functions_ptr:int`, `done:(tvm_inst)list`,
                 `tail:(tvm_inst)list`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(s == CMIfS guard_ yes_ no_) **
       fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_stmt_wf p f loop_ s <=> true) **
       fact(cm_stmt_counts_representable p fid s <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_locals f) <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       fact(cm_rep_globals_safe (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe (cm_program_strings p) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_rep_globals_size (cm_program_globals p) +
              cm_rep_strings_size (cm_program_strings p) <= 1048560i) **
       fact(0i <= temp) ** fact(temp <= temp_limit) **
       fact(temp + cm_stemps s <= temp_limit) **
       fact(cm_temp_offset p fid temp_limit <= 2147483647i) **
       fact(cm_i32_code_count pc <=> true) **
       fact(cm_i32_code_count break_pc <=> true) **
       fact(cm_i32_code_count continue_pc <=> true) **
       fact(cm_i32_code_count
              (pc + ilength
                (cm_emit_stmt p fid pc temp break_pc continue_pc s))
              <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_stmt_rep stmt s **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_emit_stmt p fid pc temp break_pc continue_pc s ++ tail)`)]]
    [[cst::ensure(
      `fact(s == CMIfS guard_ yes_ no_) **
       fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_stmt_wf p f loop_ s <=> true) **
       fact(cm_stmt_counts_representable p fid s <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_locals f) <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       fact(cm_rep_globals_safe (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe (cm_program_strings p) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_rep_globals_size (cm_program_globals p) +
              cm_rep_strings_size (cm_program_strings p) <= 1048560i) **
       fact(0i <= temp) ** fact(temp <= temp_limit) **
       fact(temp + cm_stemps s <= temp_limit) **
       fact(cm_temp_offset p fid temp_limit <= 2147483647i) **
       fact(cm_i32_code_count pc <=> true) **
       fact(cm_i32_code_count break_pc <=> true) **
       fact(cm_i32_code_count continue_pc <=> true) **
       fact(cm_i32_code_count
              (pc + ilength
                (cm_emit_stmt p fid pc temp break_pc continue_pc s))
              <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_stmt_rep stmt s **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_emit_stmt p fid pc temp break_pc continue_pc s)
         tail`)]]
{
    [[cst::proof]] {
      cm_open_stmt_rep_st();
      thm shape = assume_rule(
          `s == CMIfS (guard_:cm_expr) (yes_:cm_stmt) (no_:cm_stmt)`);
      cm_open_stmt_case_st(shape, CMC_STMT_IF);
      thm wf = cm_stmt_case_wf(shape);
      add_fact_st(eqt_intro_rule(cm_find_stmt_conjunct_rule(wf,
          `cm_expr_wf (p:cm_program) (f:cm_function_d)
             (guard_:cm_expr)`)));
      add_fact_st(eqt_intro_rule(cm_find_stmt_conjunct_rule(wf,
          `cm_stmt_wf (p:cm_program) (f:cm_function_d)
             (loop_:bool) (yes_:cm_stmt)`)));
      add_fact_st(eqt_intro_rule(cm_find_stmt_conjunct_rule(wf,
          `cm_stmt_wf (p:cm_program) (f:cm_function_d)
             (loop_:bool) (no_:cm_stmt)`)));
      thm parent_temp = conv_rule(rewrite_conv(THM_LIST(
          shape, get_cm_stemps_def())), assume_rule(
          `(temp__pre:int) + cm_stemps (s:cm_stmt) <=
           (temp_limit__pre:int)`));
      thm guard_bound = ispecl_rule(TERM_LIST(
          `cm_rtemps (guard_:cm_expr)`,
          `cm_imax (cm_stemps (yes_:cm_stmt))
             (cm_stemps (no_:cm_stmt))`), cm_imax_left_bound);
      thm branches_bound = ispecl_rule(TERM_LIST(
          `cm_rtemps (guard_:cm_expr)`,
          `cm_imax (cm_stemps (yes_:cm_stmt))
             (cm_stemps (no_:cm_stmt))`), cm_imax_right_bound);
      thm yes_bound = ispecl_rule(TERM_LIST(
          `cm_stemps (yes_:cm_stmt)`, `cm_stemps (no_:cm_stmt)`),
          cm_imax_left_bound);
      thm no_bound = ispecl_rule(TERM_LIST(
          `cm_stemps (yes_:cm_stmt)`, `cm_stemps (no_:cm_stmt)`),
          cm_imax_right_bound);
      thm guard_temp = by_defs_arith(
          `(temp__pre:int) +
             cm_expr_temps_for (guard_:cm_expr) 0i <=
           (temp_limit__pre:int)`,
          THM_LIST(cm_expr_temps_for_def,
            eqt_intro_rule(int_arith_rule(`0i == 0i`))),
          THM_LIST(parent_temp, guard_bound));
      add_fact_st(guard_temp);
      add_fact_st(by_defs_arith(
          `(temp__pre:int) + cm_stemps (yes_:cm_stmt) <=
           (temp_limit__pre:int)`, THM_LIST(),
          THM_LIST(parent_temp, branches_bound, yes_bound)));
      add_fact_st(by_defs_arith(
          `(temp__pre:int) + cm_stemps (no_:cm_stmt) <=
           (temp_limit__pre:int)`, THM_LIST(),
          THM_LIST(parent_temp, branches_bound, no_bound)));
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    int guard_count = cm_expr_rvalue_count_context(
        program, fid, fn, stmt->expr);
    [[cst::proof]] {
      thm returned = assume_rule(
          `(retval:int) ==
           cm_rcount_of
             (cm_expr_code_counts (p:cm_program)
               (fid__pre:int) (guard_:cm_expr))`);
      thm model = conv_rule(rewrite_conv(THM_LIST(
          gsym_rule(get_cm_rvalue_code_count_def()))), returned);
      add_fact_st(model);
      thm count_i32 = conv_rule(rewrite_conv(THM_LIST(model)),
          from_state_bool(`cm_i32_code_count (retval:int)`));
      cm_add_i32_term_st(count_i32);
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `guard_count__addr:addr`,
          `retval:int`,
          `cm_rvalue_code_count (p:cm_program)
            (fid__pre:int) (guard_:cm_expr)`));
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`loop_`, `(loop_:bool)`)]]
    int yes_count = cm_stmt_code_count_context(
        program, fid, fn, stmt->a);
    [[cst::proof]] {
      thm returned = assume_rule(
          `(retval_1:int) ==
           cm_stmt_code_count (p:cm_program)
             (fid__pre:int) (yes_:cm_stmt)`);
      thm count_i32 = conv_rule(rewrite_conv(THM_LIST(returned)),
          from_state_bool(`cm_i32_code_count (retval_1:int)`));
      cm_add_i32_term_st(count_i32);
      cm_retarget_stmt_call_result_st(`yes_count__addr:addr`, returned);
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`loop_`, `(loop_:bool)`)]]
    int no_count = cm_stmt_code_count_context(
        program, fid, fn, stmt->b);
    [[cst::proof]] {
      thm returned = assume_rule(
          `(retval_1:int) ==
           cm_stmt_code_count (p:cm_program)
             (fid__pre:int) (no_:cm_stmt)`);
      thm count_i32 = conv_rule(rewrite_conv(THM_LIST(returned)),
          from_state_bool(`cm_i32_code_count (retval_1:int)`));
      cm_add_i32_term_st(count_i32);
      cm_retarget_stmt_call_result_st(`no_count__addr:addr`, returned);
    }
    [[cst::proof]] {
      cm_add_i32_term_st(from_state_bool(
          `cm_i32_code_count (pc__pre:int)`));
    }
    long long no_target =
        (long long)pc +
        ((long long)guard_count + ((long long)yes_count + 2LL));
    long long end_target =
        (long long)pc +
        ((long long)guard_count +
         ((long long)yes_count + ((long long)no_count + 2LL)));
    [[cst::proof]] {
      thm no_model = int_arith_rule(
          `(pc__pre:int) +
             cm_rvalue_code_count (p:cm_program) (fid__pre:int)
               (guard_:cm_expr) +
             cm_stmt_code_count p fid__pre (yes_:cm_stmt) + 2i ==
           pc__pre + cm_rvalue_code_count p fid__pre guard_ + 1i +
             cm_stmt_code_count p fid__pre yes_ + 1i`);
      add_fact_st(no_model);
      cst_set_symbolic_state(retarget_cell64_st(
          cst_get_symbolic_state(), `no_target__addr:addr`,
          `(pc__pre:int) +
             cm_rvalue_code_count (p:cm_program) (fid__pre:int)
               (guard_:cm_expr) +
             cm_stmt_code_count p fid__pre (yes_:cm_stmt) + 2i`,
          `pc__pre + cm_rvalue_code_count p fid__pre guard_ + 1i +
             cm_stmt_code_count p fid__pre yes_ + 1i`));
      thm end_model = by_defs_arith(
          `(pc__pre:int) +
             cm_rvalue_code_count (p:cm_program) (fid__pre:int)
               (guard_:cm_expr) +
             cm_stmt_code_count p fid__pre (yes_:cm_stmt) +
             cm_stmt_code_count p fid__pre (no_:cm_stmt) + 2i ==
           pc__pre + cm_stmt_code_count p fid__pre
             (CMIfS guard_ yes_ no_)`,
          THM_LIST(get_cm_stmt_code_count_def()), THM_LIST());
      add_fact_st(end_model);
      cst_set_symbolic_state(retarget_cell64_st(
          cst_get_symbolic_state(), `end_target__addr:addr`,
          `(pc__pre:int) +
             cm_rvalue_code_count (p:cm_program) (fid__pre:int)
               (guard_:cm_expr) +
             cm_stmt_code_count p fid__pre (yes_:cm_stmt) +
             cm_stmt_code_count p fid__pre (no_:cm_stmt) + 2i`,
          `pc__pre + cm_stmt_code_count p fid__pre
             (CMIfS guard_ yes_ no_)`));
      cm_add_stmt_count_bounds_st(assume_rule(
          `s == CMIfS (guard_:cm_expr) (yes_:cm_stmt) (no_:cm_stmt)`));
    }
    int yes_pc = pc + (guard_count + 1);
    int no_pc = pc + (guard_count + (1 + (yes_count + 1)));
    int end_pc =
        pc + (guard_count + (1 + (yes_count + (1 + no_count))));
    [[cst::proof]] {
      thm shape = assume_rule(
          `s == CMIfS (guard_:cm_expr) (yes_:cm_stmt) (no_:cm_stmt)`);
      term guard_code =
          `cm_expr_code_for (p:cm_program) (fid__pre:int)
             (pc__pre:int) (temp__pre:int) (guard_:cm_expr) 0i`;
      term yes_code =
          `cm_emit_stmt (p:cm_program) (fid__pre:int)
             (pc__pre + cm_rvalue_code_count p fid__pre guard_ + 1i)
             (temp__pre:int) (break_pc__pre:int)
             (continue_pc__pre:int) (yes_:cm_stmt)`;
      term no_code =
          `cm_emit_stmt (p:cm_program) (fid__pre:int)
             (pc__pre + cm_rvalue_code_count p fid__pre guard_ + 1i +
               cm_stmt_code_count p fid__pre yes_ + 1i)
             (temp__pre:int) (break_pc__pre:int)
             (continue_pc__pre:int) (no_:cm_stmt)`;
      term jz_code =
          `[TVMInst TVMJzOp
             ((pc__pre:int) +
               cm_rvalue_code_count (p:cm_program) (fid__pre:int) guard_ +
               1i + cm_stmt_code_count p fid__pre yes_ + 1i)]`;
      term jmp_code =
          `[TVMInst TVMJmpOp
             ((pc__pre:int) +
               cm_stmt_code_count (p:cm_program) (fid__pre:int)
                 (CMIfS (guard_:cm_expr) (yes_:cm_stmt) (no_:cm_stmt)))]`;
      term code =
          `${guard_code:(tvm_inst)list} ++ ${jz_code:(tvm_inst)list} ++
           ${yes_code:(tvm_inst)list} ++ ${jmp_code:(tvm_inst)list} ++
           ${no_code:(tvm_inst)list}`;
      thm code_shape = cm_stmt_code_shape(shape, code);
      cm_add_stmt_fragment_i32_st(code_shape,
          `[]:(tvm_inst)list`, guard_code,
          `${jz_code:(tvm_inst)list} ++ ${yes_code:(tvm_inst)list} ++
           ${jmp_code:(tvm_inst)list} ++ ${no_code:(tvm_inst)list}`);
      cm_add_stmt_fragment_i32_st(code_shape,
          `${guard_code:(tvm_inst)list} ++ ${jz_code:(tvm_inst)list}`,
          yes_code,
          `${jmp_code:(tvm_inst)list} ++ ${no_code:(tvm_inst)list}`);
      cm_add_stmt_fragment_i32_st(code_shape,
          `${guard_code:(tvm_inst)list} ++ ${jz_code:(tvm_inst)list} ++
           ${yes_code:(tvm_inst)list} ++ ${jmp_code:(tvm_inst)list}`,
          no_code, `[]:(tvm_inst)list`);
      thm guard_length = cm_rvalue_code_length_at(`guard_:cm_expr`,
          `pc__pre:int`, `temp__pre:int`);
      thm yes_length = cm_stmt_code_length_at(`yes_:cm_stmt`,
          `(pc__pre:int) +
             cm_rvalue_code_count (p:cm_program) (fid__pre:int) guard_ + 1i`,
          `temp__pre:int`, `break_pc__pre:int`, `continue_pc__pre:int`);
      thm no_length = cm_stmt_code_length_at(`no_:cm_stmt`,
          `(pc__pre:int) +
             cm_rvalue_code_count (p:cm_program) (fid__pre:int) guard_ + 1i +
             cm_stmt_code_count p fid__pre yes_ + 1i`,
          `temp__pre:int`, `break_pc__pre:int`, `continue_pc__pre:int`);
      add_fact_st(guard_length);
      add_fact_st(yes_length);
      add_fact_st(no_length);
      thm yes_prefix = conv_rule(rewrite_conv(THM_LIST(
          get_cm_i32_code_count_def(), guard_length,
          get_theorem_by_name("ILENGTH_APPEND"),
          get_theorem_by_name("ILENGTH_DEF"))), from_state_bool(
            `cm_i32_code_count
              ((pc__pre:int) + ilength
                (${guard_code:(tvm_inst)list} ++
                 ${jz_code:(tvm_inst)list}))`));
      thm yes_target = by_defs_arith(
          `cm_i32_code_count
            ((pc__pre:int) +
             cm_rvalue_code_count (p:cm_program) (fid__pre:int)
               (guard_:cm_expr) + 1i)`,
          THM_LIST(get_cm_i32_code_count_def()),
          THM_LIST(yes_prefix));
      cm_add_i32_term_st(yes_target);
      thm yes_end_prefix = conv_rule(rewrite_conv(THM_LIST(
          get_cm_i32_code_count_def(), guard_length,
          get_theorem_by_name("ILENGTH_APPEND"),
          get_theorem_by_name("ILENGTH_DEF"))), from_state_bool(
            `cm_i32_code_count
              ((pc__pre:int) + ilength
                (${guard_code:(tvm_inst)list} ++
                 ${jz_code:(tvm_inst)list}) +
               ilength ${yes_code:(tvm_inst)list})`));
      thm yes_end = by_defs_arith(
          `cm_i32_code_count
            (((pc__pre:int) +
              cm_rvalue_code_count (p:cm_program) (fid__pre:int)
                (guard_:cm_expr) + 1i) +
             ilength ${yes_code:(tvm_inst)list})`,
          THM_LIST(get_cm_i32_code_count_def()),
          THM_LIST(yes_end_prefix));
      cm_add_i32_term_st(yes_end);
      thm no_prefix = conv_rule(rewrite_conv(THM_LIST(
          get_cm_i32_code_count_def(), guard_length, yes_length,
          get_theorem_by_name("ILENGTH_APPEND"),
          get_theorem_by_name("ILENGTH_DEF"))), from_state_bool(
            `cm_i32_code_count
              ((pc__pre:int) + ilength
                (${guard_code:(tvm_inst)list} ++
                 ${jz_code:(tvm_inst)list} ++
                 ${yes_code:(tvm_inst)list} ++
                 ${jmp_code:(tvm_inst)list}))`));
      thm no_target = by_defs_arith(
          `cm_i32_code_count
            ((pc__pre:int) +
             cm_rvalue_code_count (p:cm_program) (fid__pre:int)
               (guard_:cm_expr) +
             1i + cm_stmt_code_count p fid__pre (yes_:cm_stmt) + 1i)`,
          THM_LIST(get_cm_i32_code_count_def()),
          THM_LIST(no_prefix));
      thm no_end_prefix = conv_rule(rewrite_conv(THM_LIST(
          get_cm_i32_code_count_def(), guard_length, yes_length,
          get_theorem_by_name("ILENGTH_APPEND"),
          get_theorem_by_name("ILENGTH_DEF"))), from_state_bool(
            `cm_i32_code_count
              ((pc__pre:int) + ilength
                (${guard_code:(tvm_inst)list} ++
                 ${jz_code:(tvm_inst)list} ++
                 ${yes_code:(tvm_inst)list} ++
                 ${jmp_code:(tvm_inst)list}) +
               ilength ${no_code:(tvm_inst)list})`));
      thm no_end = by_defs_arith(
          `cm_i32_code_count
            (((pc__pre:int) +
              cm_rvalue_code_count (p:cm_program) (fid__pre:int)
                (guard_:cm_expr) +
              1i + cm_stmt_code_count p fid__pre (yes_:cm_stmt) + 1i) +
             ilength ${no_code:(tvm_inst)list})`,
          THM_LIST(get_cm_i32_code_count_def()),
          THM_LIST(no_end_prefix));
      cm_add_i32_term_st(no_end);
      cm_add_i32_term_st(no_target);
      thm total_count = from_state_bool(
          `cm_i32_code_count
            ((pc__pre:int) +
             ilength (cm_emit_stmt (p:cm_program) (fid__pre:int)
               pc__pre (temp__pre:int) (break_pc__pre:int)
               (continue_pc__pre:int) (s:cm_stmt)))`);
      cm_add_i32_term_st(conv_rule(rewrite_conv(THM_LIST(
          code_shape, guard_length, yes_length, no_length,
          get_theorem_by_name("ILENGTH_APPEND"),
          get_theorem_by_name("ILENGTH_DEF"),
          get_cm_stmt_code_count_def())), total_count));
      cm_select_code_plan_st(code_shape);
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`fid`, `(fid__pre:int)`)]]
    cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                 stmt->expr, 0, emitter);
    [[cst::proof]] {
      rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
      cm_add_opcode_facts_st(`20i`, `TVMJzOp`);
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`opcode`, `TVMJzOp`)]]
    cm_emit_plan(emitter, CMC_OP_JZ, no_target);
    [[cst::proof]] { rewrite_st(THM_LIST(get_theorem_by_name("APPEND"))); }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`fid`, `(fid__pre:int)`)]]
    [[cst::where(`loop_`, `(loop_:bool)`)]]
    [[cst::where(`body`, `(body:int)`)]]
    [[cst::where(`next`, `(next:int)`)]]
    [[cst::where(`functions_ptr`, `(functions_ptr:int)`)]]
    [[cst::where(`out`, `(out:int)`)]]
    [[cst::where(`capacity`, `(capacity:int)`)]]
    [[cst::where(`s`, `(yes_:cm_stmt)`)]]
    [[cst::where(`done`,
        `((done:(tvm_inst)list) ++
           cm_expr_code_for (p:cm_program) (fid__pre:int)
             (pc__pre:int) (temp__pre:int) (guard_:cm_expr) 0i) ++
         [TVMInst TVMJzOp
           (pc__pre + cm_rvalue_code_count p fid__pre guard_ + 1i +
            cm_stmt_code_count p fid__pre yes_ + 1i)]`)]]
    [[cst::where(`tail`,
        `TVMInst TVMJmpOp
           ((pc__pre:int) + cm_stmt_code_count (p:cm_program)
             (fid__pre:int) (CMIfS (guard_:cm_expr)
               (yes_:cm_stmt) (no_:cm_stmt))) ::
         (cm_emit_stmt p fid__pre
            (pc__pre + cm_rvalue_code_count p fid__pre guard_ + 1i +
             cm_stmt_code_count p fid__pre yes_ + 1i)
            (temp__pre:int) (break_pc__pre:int) (continue_pc__pre:int)
            no_ ++ (tail:(tvm_inst)list))`)]]
    cmc_emit_stmt(program, fid, fn, yes_pc, temp, temp_limit,
                 break_pc, continue_pc, stmt->a, emitter);
    [[cst::proof]] {
      rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
      cm_add_opcode_facts_st(`19i`, `TVMJmpOp`);
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`opcode`, `TVMJmpOp`)]]
    cm_emit_plan(emitter, CMC_OP_JMP, end_target);
    [[cst::proof]] { rewrite_st(THM_LIST(get_theorem_by_name("APPEND"))); }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`fid`, `(fid__pre:int)`)]]
    [[cst::where(`loop_`, `(loop_:bool)`)]]
    [[cst::where(`body`, `(body:int)`)]]
    [[cst::where(`next`, `(next:int)`)]]
    [[cst::where(`functions_ptr`, `(functions_ptr:int)`)]]
    [[cst::where(`out`, `(out:int)`)]]
    [[cst::where(`capacity`, `(capacity:int)`)]]
    [[cst::where(`s`, `(no_:cm_stmt)`)]]
    cmc_emit_stmt(program, fid, fn, no_pc, temp, temp_limit,
                 break_pc, continue_pc, stmt->b, emitter);
    [[cst::proof]] {
      thm shape = assume_rule(
          `s == CMIfS (guard_:cm_expr) (yes_:cm_stmt) (no_:cm_stmt)`);
      term code =
          `cm_expr_code_for (p:cm_program) (fid__pre:int)
             (pc__pre:int) (temp__pre:int) (guard_:cm_expr) 0i ++
           [TVMInst TVMJzOp
             (pc__pre + cm_rvalue_code_count p fid__pre guard_ + 1i +
              cm_stmt_code_count p fid__pre yes_ + 1i)] ++
           cm_emit_stmt p fid__pre
             (pc__pre + cm_rvalue_code_count p fid__pre guard_ + 1i)
             temp__pre break_pc__pre continue_pc__pre yes_ ++
           [TVMInst TVMJmpOp
             (pc__pre + cm_stmt_code_count p fid__pre
               (CMIfS guard_ yes_ no_))] ++
           cm_emit_stmt p fid__pre
             (pc__pre + cm_rvalue_code_count p fid__pre guard_ + 1i +
              cm_stmt_code_count p fid__pre yes_ + 1i)
             temp__pre break_pc__pre continue_pc__pre no_`;
      thm expanded_shape = cm_stmt_code_shape(shape, code);
      thm canonical_shape = conv_rule(rewrite_conv(THM_LIST(
          get_theorem_by_name("APPEND"))), expanded_shape);
      cm_restore_code_plan_end_st(canonical_shape);
      cm_close_stmt_case_st(shape, CMC_STMT_IF);
      cm_close_stmt_rep_st();
    }
}
void cmc_emit_stmt(struct cm_program *program, int fid,
                  struct cm_function *fn, int pc, int temp,
                  int temp_limit, int break_pc, int continue_pc,
                  struct cm_stmt *stmt, struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `s:cm_stmt`,
                 `loop_:bool`, `body:int`, `next:int`,
                 `functions_ptr:int`, `done:(tvm_inst)list`,
                 `tail:(tvm_inst)list`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_stmt_wf p f loop_ s <=> true) **
       fact(cm_stmt_counts_representable p fid s <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_locals f) <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       fact(cm_rep_globals_safe (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe (cm_program_strings p) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_rep_globals_size (cm_program_globals p) +
              cm_rep_strings_size (cm_program_strings p) <= 1048560i) **
       fact(0i <= temp) ** fact(temp <= temp_limit) **
       fact(temp + cm_stemps s <= temp_limit) **
       fact(cm_temp_offset p fid temp_limit <= 2147483647i) **
       fact(cm_i32_code_count pc <=> true) **
       fact(cm_i32_code_count break_pc <=> true) **
       fact(cm_i32_code_count continue_pc <=> true) **
       fact(cm_i32_code_count
              (pc + ilength
                (cm_emit_stmt p fid pc temp break_pc continue_pc s))
              <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_stmt_rep stmt s **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_emit_stmt p fid pc temp break_pc continue_pc s ++ tail)`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_stmt_wf p f loop_ s <=> true) **
       fact(cm_stmt_counts_representable p fid s <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_locals f) <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       fact(cm_rep_globals_safe (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe (cm_program_strings p) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_rep_globals_size (cm_program_globals p) +
              cm_rep_strings_size (cm_program_strings p) <= 1048560i) **
       fact(0i <= temp) ** fact(temp <= temp_limit) **
       fact(temp + cm_stemps s <= temp_limit) **
       fact(cm_temp_offset p fid temp_limit <= 2147483647i) **
       fact(cm_i32_code_count pc <=> true) **
       fact(cm_i32_code_count break_pc <=> true) **
       fact(cm_i32_code_count continue_pc <=> true) **
       fact(cm_i32_code_count
              (pc + ilength
                (cm_emit_stmt p fid pc temp break_pc continue_pc s))
              <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_stmt_rep stmt s **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_emit_stmt p fid pc temp break_pc continue_pc s)
         tail`)]]
{
  [[cst::proof]] { cm_open_stmt_rep_st(); }
  if (stmt->kind == CMC_STMT_SKIP) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`s:cm_stmt`,
          get_cm_stmt_skip_shape_ent()),
          assume_rule(`cm_rep_stmt_kind (s:cm_stmt) == 0i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(), shape_ent));
      thm shape = assume_rule(`s == CMSkipS`);
      cm_open_stmt_case_st(shape, CMC_STMT_SKIP);
      thm code_shape = cm_stmt_code_shape(shape, `[]:(tvm_inst)list`);
      cm_empty_code_plan_end_st(code_shape);
      cm_close_stmt_case_st(shape, CMC_STMT_SKIP);
      cm_close_stmt_rep_st();
    }
  } else if (stmt->kind == CMC_STMT_EXPR) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`s:cm_stmt`,
          get_cm_stmt_expr_shape_ent()),
          assume_rule(`cm_rep_stmt_kind (s:cm_stmt) == 1i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent, TERM_LIST(`expr_:cm_expr`))));
      thm shape = assume_rule(`s == CMExprS (expr_:cm_expr)`);
      cm_open_stmt_case_st(shape, CMC_STMT_EXPR);
      thm wf = cm_stmt_case_wf(shape);
      add_fact_st(eqt_intro_rule(cm_find_stmt_conjunct_rule(wf,
          `cm_expr_wf (p:cm_program) (f:cm_function_d)
            (expr_:cm_expr)`)));
      add_fact_st(by_defs_arith(
          `(temp__pre:int) + cm_expr_temps_for (expr_:cm_expr) 0i <=
           (temp_limit__pre:int)`,
          THM_LIST(cm_expr_temps_for_def),
          THM_LIST(conv_rule(rewrite_conv(THM_LIST(
            shape, get_cm_stemps_def())), assume_rule(
              `(temp__pre:int) + cm_stemps (s:cm_stmt) <=
               (temp_limit__pre:int)`)))));
      term expr_code =
          `cm_expr_code_for (p:cm_program) (fid__pre:int)
             (pc__pre:int) (temp__pre:int) (expr_:cm_expr) 0i`;
      term code =
          `cm_expr_code_for (p:cm_program) (fid__pre:int)
             (pc__pre:int) (temp__pre:int) (expr_:cm_expr) 0i ++
           [TVMInst TVMPopOp 0i]`;
      thm code_shape = cm_stmt_code_shape(shape, code);
      cm_add_stmt_fragment_i32_st(code_shape,
          `[]:(tvm_inst)list`, expr_code,
          `[TVMInst TVMPopOp 0i]`);
      cm_select_code_plan_st(code_shape);
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`fid`, `(fid__pre:int)`)]]
    cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                 stmt->expr, 0, emitter);
    [[cst::proof]] {
      rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
      cm_add_opcode_facts_st(`1i`, `TVMPopOp`);
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`opcode`, `TVMPopOp`)]]
    cm_emit_plan(emitter, CMC_OP_POP, 0);
    [[cst::proof]] {
      thm shape = assume_rule(`s == CMExprS (expr_:cm_expr)`);
      term code =
          `cm_expr_code_for (p:cm_program) (fid__pre:int)
             (pc__pre:int) (temp__pre:int) (expr_:cm_expr) 0i ++
           [TVMInst TVMPopOp 0i]`;
      cm_restore_code_plan_end_st(cm_stmt_code_shape(shape, code));
      cm_close_stmt_case_st(shape, CMC_STMT_EXPR);
      cm_close_stmt_rep_st();
    }
  } else if (stmt->kind == CMC_STMT_DECL) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`s:cm_stmt`,
          get_cm_stmt_decl_shape_ent()),
          assume_rule(`cm_rep_stmt_kind (s:cm_stmt) == 2i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent, TERM_LIST(`slot_:int`))));
      thm shape = assume_rule(`s == CMDeclS (slot_:int)`);
      cm_open_stmt_case_st(shape, CMC_STMT_DECL);
      thm code_shape = cm_stmt_code_shape(shape, `[]:(tvm_inst)list`);
      cm_empty_code_plan_end_st(code_shape);
      cm_close_stmt_case_st(shape, CMC_STMT_DECL);
      cm_close_stmt_rep_st();
    }
  } else if (stmt->kind == CMC_STMT_INIT) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`s:cm_stmt`,
          get_cm_stmt_init_shape_ent()),
          assume_rule(`cm_rep_stmt_kind (s:cm_stmt) == 3i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`slot_:int`, `expr_:cm_expr`))));
      thm shape = assume_rule(
          `s == CMInitS (slot_:int) (expr_:cm_expr)`);
      cm_open_stmt_case_st(shape, CMC_STMT_INIT);
      thm wf = cm_stmt_case_wf(shape);
      thm lower = cm_find_stmt_conjunct_rule(
          wf, `0i <= (slot_:int)`);
      thm upper = cm_find_stmt_conjunct_rule(wf,
          `(slot_:int) < ilength (cm_function_locals (f:cm_function_d))`);
      add_fact_st(lower);
      add_fact_st(upper);
      add_fact_st(eqt_intro_rule(cm_find_stmt_conjunct_rule(wf,
          `cm_expr_wf (p:cm_program) (f:cm_function_d)
            (expr_:cm_expr)`)));
      thm slot_model = by_rewrite(
          `cm_rep_stmt_slot (s:cm_stmt) == (slot_:int)`,
          THM_LIST(shape, get_cm_rep_stmt_slot_def()));
      substitute_st(slot_model);
      add_fact_st(by_defs_arith(
          `(temp__pre:int) + cm_expr_temps_for (expr_:cm_expr) 0i <=
           (temp_limit__pre:int)`,
          THM_LIST(cm_expr_temps_for_def),
          THM_LIST(conv_rule(rewrite_conv(THM_LIST(
            shape, get_cm_stemps_def())), assume_rule(
              `(temp__pre:int) + cm_stemps (s:cm_stmt) <=
               (temp_limit__pre:int)`)))));
      term model_ty =
          `cm_slot_ty
            (inth (slot_:int)
              (cm_function_locals
                (inth (fid__pre:int)
                  (cm_program_functions (p:cm_program)))))`;
      term expr_code =
          `cm_expr_code_for (p:cm_program) (fid__pre:int)
             (pc__pre:int) (temp__pre:int) (expr_:cm_expr) 0i`;
      term code =
          `cm_expr_code_for (p:cm_program) (fid__pre:int)
             (pc__pre:int) (temp__pre:int) (expr_:cm_expr) 0i ++
           cm_char_normalize_code ${model_ty:cm_type} ++
           cm_fp_relative_address_code
             (cm_local_offset p fid__pre (slot_:int)) ++
           cm_store_code ${model_ty:cm_type}`;
      thm code_shape = cm_stmt_code_shape(shape, code);
      cm_add_stmt_fragment_i32_st(code_shape,
          `[]:(tvm_inst)list`, expr_code,
          `cm_char_normalize_code ${model_ty:cm_type} ++
           cm_fp_relative_address_code
             (cm_local_offset (p:cm_program) (fid__pre:int)
               (slot_:int)) ++
           cm_store_code ${model_ty:cm_type}`);
      cm_select_code_plan_st(code_shape);
      cm_open_function_context_st();
    }
    [[cst::where(`slots`, `cm_function_locals (f:cm_function_d)`)]]
    int local_ty = cmc_slot_type_at(fn->locals, stmt->slot);
    [[cst::proof]] {
      thm lower = assume_rule(`0i <= (slot_:int)`);
      thm upper = assume_rule(
          `(slot_:int) <
           ilength (cm_function_locals (f:cm_function_d))`);
      thm bridge = cm_rep_slot_type_model(
          `cm_function_locals (f:cm_function_d)`, `slot_:int`);
      bridge = mp_rule(mp_rule(bridge, lower), upper);
      thm returned = assume_rule(
          `(retval:int) ==
           cm_rep_slot_type (cm_function_locals (f:cm_function_d))
             (slot_:int)`);
      thm encoded = trans_rule(returned, bridge);
      encoded = conv_rule(rewrite_conv(THM_LIST(assume_rule(
          `f == inth (fid__pre:int)
            (cm_program_functions (p:cm_program))`))), encoded);
      cm_retarget_stmt_call_result_st(
          `local_ty__addr:addr`, encoded);
      cm_close_function_context_st();
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`fid`, `(fid__pre:int)`)]]
    cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                 stmt->expr, 0, emitter);
    [[cst::proof]] {
      rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    cm_emit_normalize_plan(emitter, local_ty);
    [[cst::proof]] {
      thm valid = by_rewrite(
          `cm_binding_valid (p:cm_program) (f:cm_function_d)
             1i (slot_:int)`,
          THM_LIST(get_cm_binding_valid_def(),
            eqt_intro_rule(int_arith_rule(`1i == 1i`)),
            assume_rule(`0i <= (slot_:int)`),
            assume_rule(
              `(slot_:int) < ilength
                (cm_function_locals (f:cm_function_d))`)));
      add_fact_st(eqt_intro_rule(valid));
      thm address_shape = by_rewrite(
          `cm_binding_address_code (p:cm_program) (fid__pre:int)
             1i (slot_:int) ==
           cm_fp_relative_address_code
             (cm_local_offset p fid__pre slot_)`,
          THM_LIST(get_cm_binding_address_code_def(),
            eqt_intro_rule(int_arith_rule(`1i == 1i`)),
            eqf_intro_rule(int_arith_rule(`~(1i == 0i)`))));
      rewrite_st(THM_LIST(gsym_rule(address_shape),
          get_theorem_by_name("APPEND")));
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`fid`, `(fid__pre:int)`)]]
    [[cst::where(`structs`, `cm_program_structs (p:cm_program)`)]]
    [[cst::where(`globals`, `cm_program_globals (p:cm_program)`)]]
    cm_emit_binding_address_plan(program, fn, CMC_BIND_LOCAL,
                                 stmt->slot, emitter);
    [[cst::proof]] {
      rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    cm_emit_store_plan(emitter, local_ty);
    [[cst::proof]] {
      thm shape = assume_rule(
          `s == CMInitS (slot_:int) (expr_:cm_expr)`);
      thm address_shape = by_rewrite(
          `cm_binding_address_code (p:cm_program) (fid__pre:int)
             1i (slot_:int) ==
           cm_fp_relative_address_code
             (cm_local_offset p fid__pre slot_)`,
          THM_LIST(get_cm_binding_address_code_def(),
            eqt_intro_rule(int_arith_rule(`1i == 1i`)),
            eqf_intro_rule(int_arith_rule(`~(1i == 0i)`))));
      rewrite_st(THM_LIST(address_shape));
      term model_ty =
          `cm_slot_ty
            (inth (slot_:int)
              (cm_function_locals
                (inth (fid__pre:int)
                  (cm_program_functions (p:cm_program)))))`;
      term code =
          `cm_expr_code_for (p:cm_program) (fid__pre:int)
             (pc__pre:int) (temp__pre:int) (expr_:cm_expr) 0i ++
           cm_char_normalize_code ${model_ty:cm_type} ++
           cm_fp_relative_address_code
             (cm_local_offset p fid__pre (slot_:int)) ++
           cm_store_code ${model_ty:cm_type}`;
      cm_restore_code_plan_end_st(cm_stmt_code_shape(shape, code));
      cm_close_stmt_case_st(shape, CMC_STMT_INIT);
      thm slot_model = by_rewrite(
          `cm_rep_stmt_slot (s:cm_stmt) == (slot_:int)`,
          THM_LIST(shape, get_cm_rep_stmt_slot_def()));
      substitute_st(sym_rule(slot_model));
      cm_close_stmt_rep_st();
    }
  } else if (stmt->kind == CMC_STMT_SEQ) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`s:cm_stmt`,
          get_cm_stmt_seq_shape_ent()),
          assume_rule(`cm_rep_stmt_kind (s:cm_stmt) == 4i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`first_:cm_stmt`, `second_:cm_stmt`))));
      thm shape = assume_rule(
          `s == CMSeqS (first_:cm_stmt) (second_:cm_stmt)`);
      cm_open_stmt_case_st(shape, CMC_STMT_SEQ);
      thm wf = cm_stmt_case_wf(shape);
      add_fact_st(eqt_intro_rule(cm_find_stmt_conjunct_rule(wf,
          `cm_stmt_wf (p:cm_program) (f:cm_function_d)
             (loop_:bool) (first_:cm_stmt)`)));
      add_fact_st(eqt_intro_rule(cm_find_stmt_conjunct_rule(wf,
          `cm_stmt_wf (p:cm_program) (f:cm_function_d)
             (loop_:bool) (second_:cm_stmt)`)));
      thm parent_temp = conv_rule(rewrite_conv(THM_LIST(
          shape, get_cm_stemps_def())), assume_rule(
          `(temp__pre:int) + cm_stemps (s:cm_stmt) <=
           (temp_limit__pre:int)`));
      thm left_bound = ispecl_rule(TERM_LIST(
          `cm_stemps (first_:cm_stmt)`,
          `cm_stemps (second_:cm_stmt)`), cm_imax_left_bound);
      thm right_bound = ispecl_rule(TERM_LIST(
          `cm_stemps (first_:cm_stmt)`,
          `cm_stemps (second_:cm_stmt)`), cm_imax_right_bound);
      add_fact_st(mp_rule(int_arith_rule(
          `(cm_stemps (first_:cm_stmt) <=
              cm_imax (cm_stemps first_) (cm_stemps (second_:cm_stmt)) &&
            (temp__pre:int) +
              cm_imax (cm_stemps first_) (cm_stemps second_) <=
              (temp_limit__pre:int)) ==>
           temp__pre + cm_stemps first_ <= temp_limit__pre`),
          conj_rule(left_bound, parent_temp)));
      add_fact_st(mp_rule(int_arith_rule(
          `(cm_stemps (second_:cm_stmt) <=
              cm_imax (cm_stemps (first_:cm_stmt)) (cm_stemps second_) &&
            (temp__pre:int) +
              cm_imax (cm_stemps first_) (cm_stemps second_) <=
              (temp_limit__pre:int)) ==>
           temp__pre + cm_stemps second_ <= temp_limit__pre`),
          conj_rule(right_bound, parent_temp)));
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`loop_`, `(loop_:bool)`)]]
    int first_count = cm_stmt_code_count_context(
        program, fid, fn, stmt->a);
    [[cst::proof]] {
      thm returned = assume_rule(
          `(retval:int) == cm_stmt_code_count
            (p:cm_program) (fid__pre:int) (first_:cm_stmt)`);
      cm_retarget_stmt_call_result_st(`first_count__addr:addr`, returned);
      thm shape = assume_rule(
          `s == CMSeqS (first_:cm_stmt) (second_:cm_stmt)`);
      term first_code =
          `cm_emit_stmt (p:cm_program) (fid__pre:int) (pc__pre:int)
             (temp__pre:int) (break_pc__pre:int)
             (continue_pc__pre:int) (first_:cm_stmt)`;
      term second_code =
          `cm_emit_stmt (p:cm_program) (fid__pre:int)
             (pc__pre + cm_stmt_code_count p fid__pre first_)
             (temp__pre:int) (break_pc__pre:int)
             (continue_pc__pre:int) (second_:cm_stmt)`;
      term code =
          `cm_emit_stmt (p:cm_program) (fid__pre:int) (pc__pre:int)
             (temp__pre:int) (break_pc__pre:int)
             (continue_pc__pre:int) (first_:cm_stmt) ++
           cm_emit_stmt p fid__pre
             (pc__pre + cm_stmt_code_count p fid__pre first_)
             temp__pre break_pc__pre continue_pc__pre second_`;
      thm code_shape = cm_stmt_code_shape(shape, code);
      cm_add_stmt_fragment_i32_st(code_shape,
          `[]:(tvm_inst)list`, first_code, second_code);
      cm_add_stmt_fragment_i32_st(code_shape,
          first_code, second_code, `[]:(tvm_inst)list`);
      thm first_length = cm_stmt_code_length_at(`first_:cm_stmt`,
          `pc__pre:int`, `temp__pre:int`, `break_pc__pre:int`,
          `continue_pc__pre:int`);
      add_fact_st(first_length);
      thm second_start = conv_rule(rewrite_conv(THM_LIST(first_length)),
          from_state_bool(
            `cm_i32_code_count
              ((pc__pre:int) + ilength ${first_code:(tvm_inst)list})`));
      cm_add_i32_term_st(second_start);
      thm second_end_bounds = conv_rule(rewrite_conv(THM_LIST(
          get_cm_i32_code_count_def())),
          conv_rule(subs_conv(THM_LIST(first_length)), from_state_bool(
            `cm_i32_code_count
              ((pc__pre:int) + ilength ${first_code:(tvm_inst)list} +
               ilength ${second_code:(tvm_inst)list})`)));
      cm_add_i32_term_st(by_defs_arith(
          `cm_i32_code_count
            (((pc__pre:int) +
              cm_stmt_code_count (p:cm_program) (fid__pre:int)
                (first_:cm_stmt)) +
             ilength ${second_code:(tvm_inst)list})`,
          THM_LIST(get_cm_i32_code_count_def()), THM_LIST(second_end_bounds)));
      cm_select_code_plan_st(code_shape);
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`fid`, `(fid__pre:int)`)]]
    [[cst::where(`loop_`, `(loop_:bool)`)]]
    cmc_emit_stmt(program, fid, fn, pc, temp, temp_limit,
                 break_pc, continue_pc, stmt->a, emitter);
    int second_pc = pc + first_count;
    [[cst::proof]] {
      rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`fid`, `(fid__pre:int)`)]]
    [[cst::where(`loop_`, `(loop_:bool)`)]]
    cmc_emit_stmt(program, fid, fn, second_pc, temp, temp_limit,
                 break_pc, continue_pc, stmt->b, emitter);
    [[cst::proof]] {
      thm shape = assume_rule(
          `s == CMSeqS (first_:cm_stmt) (second_:cm_stmt)`);
      term code =
          `cm_emit_stmt (p:cm_program) (fid__pre:int) (pc__pre:int)
             (temp__pre:int) (break_pc__pre:int)
             (continue_pc__pre:int) (first_:cm_stmt) ++
           cm_emit_stmt p fid__pre
             (pc__pre + cm_stmt_code_count p fid__pre first_)
             temp__pre break_pc__pre continue_pc__pre second_`;
      cm_restore_code_plan_end_st(cm_stmt_code_shape(shape, code));
      cm_close_stmt_case_st(shape, CMC_STMT_SEQ);
      cm_close_stmt_rep_st();
    }
  } else if (stmt->kind == CMC_STMT_BLOCK) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`s:cm_stmt`,
          get_cm_stmt_block_shape_ent()),
          assume_rule(`cm_rep_stmt_kind (s:cm_stmt) == 5i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent, TERM_LIST(`first_:cm_stmt`))));
      thm shape = assume_rule(`s == CMBlockS (first_:cm_stmt)`);
      cm_open_stmt_case_st(shape, CMC_STMT_BLOCK);
      thm wf = cm_stmt_case_wf(shape);
      add_fact_st(eqt_intro_rule(cm_find_stmt_conjunct_rule(wf,
          `cm_stmt_wf (p:cm_program) (f:cm_function_d)
             (loop_:bool) (first_:cm_stmt)`)));
      thm child_temp = conv_rule(rewrite_conv(THM_LIST(
          shape, get_cm_stemps_def())), assume_rule(
          `(temp__pre:int) + cm_stemps (s:cm_stmt) <=
           (temp_limit__pre:int)`));
      add_fact_st(child_temp);
      term child_code =
          `cm_emit_stmt (p:cm_program) (fid__pre:int) (pc__pre:int)
             (temp__pre:int) (break_pc__pre:int)
             (continue_pc__pre:int) (first_:cm_stmt)`;
      thm code_shape = cm_stmt_code_shape(shape, child_code);
      cm_add_stmt_fragment_i32_st(code_shape,
          `[]:(tvm_inst)list`, child_code, `[]:(tvm_inst)list`);
      cm_select_code_plan_st(code_shape);
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`fid`, `(fid__pre:int)`)]]
    [[cst::where(`loop_`, `(loop_:bool)`)]]
    cmc_emit_stmt(program, fid, fn, pc, temp, temp_limit,
                 break_pc, continue_pc, stmt->a, emitter);
    [[cst::proof]] {
      thm shape = assume_rule(`s == CMBlockS (first_:cm_stmt)`);
      term child_code =
          `cm_emit_stmt (p:cm_program) (fid__pre:int) (pc__pre:int)
             (temp__pre:int) (break_pc__pre:int)
             (continue_pc__pre:int) (first_:cm_stmt)`;
      cm_restore_code_plan_end_st(cm_stmt_code_shape(shape, child_code));
      cm_close_stmt_case_st(shape, CMC_STMT_BLOCK);
      cm_close_stmt_rep_st();
    }
  } else if (stmt->kind == CMC_STMT_IF) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`s:cm_stmt`,
          get_cm_stmt_if_shape_ent()),
          assume_rule(`cm_rep_stmt_kind (s:cm_stmt) == 6i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`guard_:cm_expr`, `yes_:cm_stmt`, `no_:cm_stmt`))));
      thm shape = assume_rule(
          `s == CMIfS (guard_:cm_expr) (yes_:cm_stmt) (no_:cm_stmt)`);
      cm_open_stmt_case_st(shape, CMC_STMT_IF);
      cm_close_stmt_case_st(shape, CMC_STMT_IF);
      cm_close_stmt_rep_st();
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`s`, `(s:cm_stmt)`)]]
    [[cst::where(`loop_`, `(loop_:bool)`)]]
    [[cst::where(`body`, `(body:int)`)]]
    [[cst::where(`next`, `(next:int)`)]]
    [[cst::where(`functions_ptr`, `(functions_ptr:int)`)]]
    [[cst::where(`done`, `(done:(tvm_inst)list)`)]]
    [[cst::where(`tail`, `(tail:(tvm_inst)list)`)]]
    [[cst::where(`out`, `(out:int)`)]]
    [[cst::where(`capacity`, `(capacity:int)`)]]
    cmc_emit_if_stmt(program, fid, fn, pc, temp, temp_limit,
                     break_pc, continue_pc, stmt, emitter);
  } else if (stmt->kind == CMC_STMT_WHILE) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`s:cm_stmt`,
          get_cm_stmt_while_shape_ent()),
          assume_rule(`cm_rep_stmt_kind (s:cm_stmt) == 7i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`guard_:cm_expr`, `body_:cm_stmt`))));
      thm shape = assume_rule(
          `s == CMWhileS (guard_:cm_expr) (body_:cm_stmt)`);
      cm_open_stmt_case_st(shape, CMC_STMT_WHILE);
      thm wf = cm_stmt_case_wf(shape);
      add_fact_st(eqt_intro_rule(cm_find_stmt_conjunct_rule(wf,
          `cm_expr_wf (p:cm_program) (f:cm_function_d)
             (guard_:cm_expr)`)));
      add_fact_st(eqt_intro_rule(cm_find_stmt_conjunct_rule(wf,
          `cm_stmt_wf (p:cm_program) (f:cm_function_d)
             T (body_:cm_stmt)`)));
      thm parent_temp = conv_rule(rewrite_conv(THM_LIST(
          shape, get_cm_stemps_def())), assume_rule(
          `(temp__pre:int) + cm_stemps (s:cm_stmt) <=
           (temp_limit__pre:int)`));
      thm guard_bound = ispecl_rule(TERM_LIST(
          `cm_rtemps (guard_:cm_expr)`, `cm_stemps (body_:cm_stmt)`),
          cm_imax_left_bound);
      thm body_bound = ispecl_rule(TERM_LIST(
          `cm_rtemps (guard_:cm_expr)`, `cm_stemps (body_:cm_stmt)`),
          cm_imax_right_bound);
      add_fact_st(by_defs_arith(
          `(temp__pre:int) +
             cm_expr_temps_for (guard_:cm_expr) 0i <=
           (temp_limit__pre:int)`,
          THM_LIST(cm_expr_temps_for_def,
            eqt_intro_rule(int_arith_rule(`0i == 0i`))),
          THM_LIST(parent_temp, guard_bound)));
      add_fact_st(by_defs_arith(
          `(temp__pre:int) + cm_stemps (body_:cm_stmt) <=
           (temp_limit__pre:int)`, THM_LIST(),
          THM_LIST(parent_temp, body_bound)));
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    int guard_count = cm_expr_rvalue_count_context(
        program, fid, fn, stmt->expr);
    [[cst::proof]] {
      thm returned = assume_rule(
          `(retval:int) ==
           cm_rcount_of
             (cm_expr_code_counts (p:cm_program)
               (fid__pre:int) (guard_:cm_expr))`);
      thm model = conv_rule(rewrite_conv(THM_LIST(
          gsym_rule(get_cm_rvalue_code_count_def()))), returned);
      add_fact_st(model);
      thm count_i32 = conv_rule(rewrite_conv(THM_LIST(model)),
          from_state_bool(`cm_i32_code_count (retval:int)`));
      cm_add_i32_term_st(count_i32);
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `guard_count__addr:addr`,
          `retval:int`,
          `cm_rvalue_code_count (p:cm_program)
            (fid__pre:int) (guard_:cm_expr)`));
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`loop_`, `T`)]]
    int body_count = cm_stmt_code_count_context(
        program, fid, fn, stmt->a);
    [[cst::proof]] {
      thm returned = assume_rule(
          `(retval_1:int) ==
           cm_stmt_code_count (p:cm_program)
             (fid__pre:int) (body_:cm_stmt)`);
      thm count_i32 = conv_rule(rewrite_conv(THM_LIST(returned)),
          from_state_bool(`cm_i32_code_count (retval_1:int)`));
      cm_add_i32_term_st(count_i32);
      cm_retarget_stmt_call_result_st(`body_count__addr:addr`, returned);
      cm_add_stmt_count_bounds_st(assume_rule(
          `s == CMWhileS (guard_:cm_expr) (body_:cm_stmt)`));
    }
    int body_pc = pc + (guard_count + 1);
    int loop_end = pc + (guard_count + (1 + (body_count + 1)));
    [[cst::proof]] {
      thm loop_end_model = by_defs_arith(
          `(pc__pre:int) +
             (cm_rvalue_code_count (p:cm_program) (fid__pre:int)
                (guard_:cm_expr) +
              (1i + (cm_stmt_code_count p fid__pre (body_:cm_stmt) + 1i))) ==
           pc__pre + cm_stmt_code_count p fid__pre
             (CMWhileS guard_ body_)`,
          THM_LIST(get_cm_stmt_code_count_def()), THM_LIST());
      add_fact_st(loop_end_model);
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `loop_end__addr:addr`,
          `(pc__pre:int) +
             (cm_rvalue_code_count (p:cm_program) (fid__pre:int)
                (guard_:cm_expr) +
              (1i + (cm_stmt_code_count p fid__pre (body_:cm_stmt) + 1i)))`,
          `pc__pre + cm_stmt_code_count p fid__pre
             (CMWhileS guard_ body_)`));
    }
    [[cst::proof]] {
      thm shape = assume_rule(
          `s == CMWhileS (guard_:cm_expr) (body_:cm_stmt)`);
      term guard_code =
          `cm_expr_code_for (p:cm_program) (fid__pre:int)
             (pc__pre:int) (temp__pre:int) (guard_:cm_expr) 0i`;
      term body_code =
          `cm_emit_stmt (p:cm_program) (fid__pre:int)
             (pc__pre + cm_rvalue_code_count p fid__pre guard_ + 1i)
             (temp__pre:int)
             (pc__pre + cm_stmt_code_count p fid__pre
               (CMWhileS (guard_:cm_expr) (body_:cm_stmt)))
             (pc__pre:int) (body_:cm_stmt)`;
      term jz_code =
          `[TVMInst TVMJzOp
             ((pc__pre:int) +
               cm_stmt_code_count (p:cm_program) (fid__pre:int)
                 (CMWhileS (guard_:cm_expr) (body_:cm_stmt)))]`;
      term back_code = `[TVMInst TVMJmpOp (pc__pre:int)]`;
      term code =
          `${guard_code:(tvm_inst)list} ++ ${jz_code:(tvm_inst)list} ++
           ${body_code:(tvm_inst)list} ++ ${back_code:(tvm_inst)list}`;
      thm code_shape = cm_stmt_code_shape(shape, code);
      cm_add_stmt_fragment_i32_st(code_shape,
          `[]:(tvm_inst)list`, guard_code,
          `${jz_code:(tvm_inst)list} ++ ${body_code:(tvm_inst)list} ++
           ${back_code:(tvm_inst)list}`);
      cm_add_stmt_fragment_i32_st(code_shape,
          `${guard_code:(tvm_inst)list} ++ ${jz_code:(tvm_inst)list}`,
          body_code, back_code);
      thm guard_length = cm_rvalue_code_length_at(`guard_:cm_expr`,
          `pc__pre:int`, `temp__pre:int`);
      thm body_length = cm_stmt_code_length_at(`body_:cm_stmt`,
          `(pc__pre:int) +
             cm_rvalue_code_count (p:cm_program) (fid__pre:int) guard_ + 1i`,
          `temp__pre:int`,
          `(pc__pre:int) +
             cm_stmt_code_count (p:cm_program) (fid__pre:int)
               (CMWhileS (guard_:cm_expr) (body_:cm_stmt))`,
          `pc__pre:int`);
      add_fact_st(guard_length);
      add_fact_st(body_length);
      thm body_prefix = conv_rule(rewrite_conv(THM_LIST(
          get_cm_i32_code_count_def(), guard_length,
          get_theorem_by_name("ILENGTH_APPEND"),
          get_theorem_by_name("ILENGTH_DEF"))), from_state_bool(
            `cm_i32_code_count
              ((pc__pre:int) + ilength
                (${guard_code:(tvm_inst)list} ++
                 ${jz_code:(tvm_inst)list}))`));
      cm_add_i32_term_st(by_defs_arith(
          `cm_i32_code_count
            ((pc__pre:int) +
             cm_rvalue_code_count (p:cm_program) (fid__pre:int)
               (guard_:cm_expr) + 1i)`,
          THM_LIST(get_cm_i32_code_count_def()), THM_LIST(body_prefix)));
      thm body_end_prefix = conv_rule(rewrite_conv(THM_LIST(
          get_cm_i32_code_count_def(), guard_length,
          get_theorem_by_name("ILENGTH_APPEND"),
          get_theorem_by_name("ILENGTH_DEF"))), from_state_bool(
            `cm_i32_code_count
              ((pc__pre:int) + ilength
                (${guard_code:(tvm_inst)list} ++
                 ${jz_code:(tvm_inst)list}) +
               ilength ${body_code:(tvm_inst)list})`));
      cm_add_i32_term_st(by_defs_arith(
          `cm_i32_code_count
            (((pc__pre:int) +
              cm_rvalue_code_count (p:cm_program) (fid__pre:int)
                (guard_:cm_expr) + 1i) +
             ilength ${body_code:(tvm_inst)list})`,
          THM_LIST(get_cm_i32_code_count_def()), THM_LIST(body_end_prefix)));
      cm_select_code_plan_st(code_shape);
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`fid`, `(fid__pre:int)`)]]
    cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                 stmt->expr, 0, emitter);
    [[cst::proof]] {
      rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
      cm_add_opcode_facts_st(`20i`, `TVMJzOp`);
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`opcode`, `TVMJzOp`)]]
    cm_emit_plan(emitter, CMC_OP_JZ, (long long)loop_end);
    [[cst::proof]] { rewrite_st(THM_LIST(get_theorem_by_name("APPEND"))); }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`fid`, `(fid__pre:int)`)]]
    [[cst::where(`loop_`, `T`)]]
    cmc_emit_stmt(program, fid, fn, body_pc, temp, temp_limit,
                 loop_end, pc, stmt->a, emitter);
    [[cst::proof]] {
      rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
      cm_add_opcode_facts_st(`19i`, `TVMJmpOp`);
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`opcode`, `TVMJmpOp`)]]
    cm_emit_plan(emitter, CMC_OP_JMP, (long long)pc);
    [[cst::proof]] {
      thm shape = assume_rule(
          `s == CMWhileS (guard_:cm_expr) (body_:cm_stmt)`);
      term code =
          `cm_expr_code_for (p:cm_program) (fid__pre:int)
             (pc__pre:int) (temp__pre:int) (guard_:cm_expr) 0i ++
           [TVMInst TVMJzOp
             (pc__pre + cm_stmt_code_count p fid__pre
               (CMWhileS guard_ body_))] ++
           cm_emit_stmt p fid__pre
             (pc__pre + cm_rvalue_code_count p fid__pre guard_ + 1i)
             temp__pre
             (pc__pre + cm_stmt_code_count p fid__pre
               (CMWhileS guard_ body_))
             pc__pre body_ ++
           [TVMInst TVMJmpOp pc__pre]`;
      thm expanded_shape = cm_stmt_code_shape(shape, code);
      thm canonical_shape = conv_rule(rewrite_conv(THM_LIST(
          get_theorem_by_name("APPEND"))), expanded_shape);
      cm_restore_code_plan_end_st(canonical_shape);
      cm_close_stmt_case_st(shape, CMC_STMT_WHILE);
      cm_close_stmt_rep_st();
    }
  } else if (stmt->kind == CMC_STMT_BREAK) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`s:cm_stmt`,
          get_cm_stmt_break_shape_ent()),
          assume_rule(`cm_rep_stmt_kind (s:cm_stmt) == 8i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(), shape_ent));
      thm shape = assume_rule(`s == CMBreakS`);
      cm_open_stmt_case_st(shape, CMC_STMT_BREAK);
      term code = `[TVMInst TVMJmpOp (break_pc__pre:int)]`;
      thm code_shape = cm_stmt_code_shape(shape, code);
      cm_select_code_plan_st(code_shape);
      rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
      cm_add_opcode_facts_st(`19i`, `TVMJmpOp`);
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`opcode`, `TVMJmpOp`)]]
    cm_emit_plan(emitter, CMC_OP_JMP, (long long)break_pc);
    [[cst::proof]] {
      thm shape = assume_rule(`s == CMBreakS`);
      cm_restore_code_plan_end_st(cm_stmt_code_shape(shape,
          `[TVMInst TVMJmpOp (break_pc__pre:int)]`));
      cm_close_stmt_case_st(shape, CMC_STMT_BREAK);
      cm_close_stmt_rep_st();
    }
  } else if (stmt->kind == CMC_STMT_CONTINUE) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`s:cm_stmt`,
          get_cm_stmt_continue_shape_ent()),
          assume_rule(`cm_rep_stmt_kind (s:cm_stmt) == 9i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(), shape_ent));
      thm shape = assume_rule(`s == CMContinueS`);
      cm_open_stmt_case_st(shape, CMC_STMT_CONTINUE);
      term code = `[TVMInst TVMJmpOp (continue_pc__pre:int)]`;
      thm code_shape = cm_stmt_code_shape(shape, code);
      cm_select_code_plan_st(code_shape);
      rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
      cm_add_opcode_facts_st(`19i`, `TVMJmpOp`);
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`opcode`, `TVMJmpOp`)]]
    cm_emit_plan(emitter, CMC_OP_JMP, (long long)continue_pc);
    [[cst::proof]] {
      thm shape = assume_rule(`s == CMContinueS`);
      cm_restore_code_plan_end_st(cm_stmt_code_shape(shape,
          `[TVMInst TVMJmpOp (continue_pc__pre:int)]`));
      cm_close_stmt_case_st(shape, CMC_STMT_CONTINUE);
      cm_close_stmt_rep_st();
    }
  } else {
    [[cst::proof]] {
      thm kind = mp_rule(int_arith_rule(
          `(0i <= cm_rep_stmt_kind (s:cm_stmt) &&
            cm_rep_stmt_kind s <= 10i) ==>
           ~(cm_rep_stmt_kind s == 0i) ==>
           ~(cm_rep_stmt_kind s == 1i) ==>
           ~(cm_rep_stmt_kind s == 2i) ==>
           ~(cm_rep_stmt_kind s == 3i) ==>
           ~(cm_rep_stmt_kind s == 4i) ==>
           ~(cm_rep_stmt_kind s == 5i) ==>
           ~(cm_rep_stmt_kind s == 6i) ==>
           ~(cm_rep_stmt_kind s == 7i) ==>
           ~(cm_rep_stmt_kind s == 8i) ==>
           ~(cm_rep_stmt_kind s == 9i) ==>
           cm_rep_stmt_kind s == 10i`),
          spec_rule(`s:cm_stmt`, get_cm_rep_stmt_kind_bounds()));
      kind = mp_rule(kind, assume_rule(
          `~(cm_rep_stmt_kind (s:cm_stmt) == 0i)`));
      kind = mp_rule(kind, assume_rule(
          `~(cm_rep_stmt_kind (s:cm_stmt) == 1i)`));
      kind = mp_rule(kind, assume_rule(
          `~(cm_rep_stmt_kind (s:cm_stmt) == 2i)`));
      kind = mp_rule(kind, assume_rule(
          `~(cm_rep_stmt_kind (s:cm_stmt) == 3i)`));
      kind = mp_rule(kind, assume_rule(
          `~(cm_rep_stmt_kind (s:cm_stmt) == 4i)`));
      kind = mp_rule(kind, assume_rule(
          `~(cm_rep_stmt_kind (s:cm_stmt) == 5i)`));
      kind = mp_rule(kind, assume_rule(
          `~(cm_rep_stmt_kind (s:cm_stmt) == 6i)`));
      kind = mp_rule(kind, assume_rule(
          `~(cm_rep_stmt_kind (s:cm_stmt) == 7i)`));
      kind = mp_rule(kind, assume_rule(
          `~(cm_rep_stmt_kind (s:cm_stmt) == 8i)`));
      kind = mp_rule(kind, assume_rule(
          `~(cm_rep_stmt_kind (s:cm_stmt) == 9i)`));
      add_fact_st(kind);
      thm shape_ent = mp_rule(spec_rule(`s:cm_stmt`,
          get_cm_stmt_return_shape_ent()), kind);
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent, TERM_LIST(`expr_:cm_expr`))));
      thm shape = assume_rule(`s == CMReturnS (expr_:cm_expr)`);
      cm_open_stmt_case_st(shape, CMC_STMT_RETURN);
      thm wf = cm_stmt_case_wf(shape);
      add_fact_st(eqt_intro_rule(cm_find_stmt_conjunct_rule(wf,
          `cm_expr_wf (p:cm_program) (f:cm_function_d)
             (expr_:cm_expr)`)));
      add_fact_st(by_defs_arith(
          `(temp__pre:int) + cm_expr_temps_for (expr_:cm_expr) 0i <=
           (temp_limit__pre:int)`,
          THM_LIST(cm_expr_temps_for_def),
          THM_LIST(conv_rule(rewrite_conv(THM_LIST(
            shape, get_cm_stemps_def())), assume_rule(
              `(temp__pre:int) + cm_stemps (s:cm_stmt) <=
               (temp_limit__pre:int)`)))));
      term model_ty =
          `cm_function_ret
            (inth (fid__pre:int)
              (cm_program_functions (p:cm_program)))`;
      term expr_code =
          `cm_expr_code_for (p:cm_program) (fid__pre:int)
             (pc__pre:int) (temp__pre:int) (expr_:cm_expr) 0i`;
      term code =
          `cm_expr_code_for (p:cm_program) (fid__pre:int)
             (pc__pre:int) (temp__pre:int) (expr_:cm_expr) 0i ++
           cm_char_normalize_code ${model_ty:cm_type} ++
           cm_return_epilogue`;
      thm code_shape = cm_stmt_code_shape(shape, code);
      cm_add_stmt_fragment_i32_st(code_shape,
          `[]:(tvm_inst)list`, expr_code,
          `cm_char_normalize_code ${model_ty:cm_type} ++
           cm_return_epilogue`);
      cm_select_code_plan_st(code_shape);
      cm_open_function_context_st();
    }
    int return_ty = fn->ret_ty;
    [[cst::proof]] {
      thm function_model = assume_rule(
          `f == inth (fid__pre:int)
            (cm_program_functions (p:cm_program))`);
      thm return_model = ap_term_rule(
          `cm_function_ret:cm_function_d->cm_type`, function_model);
      thm model = ap_term_rule(
          `cm_type_encode:cm_type->int`, return_model);
      add_fact_st(model);
      cst_set_symbolic_state(retarget_cell_st(cst_get_symbolic_state(),
          `return_ty__addr:addr`,
          `cm_type_encode (cm_function_ret (f:cm_function_d))`,
          `cm_type_encode
            (cm_function_ret
              (inth (fid__pre:int)
                (cm_program_functions (p:cm_program))))`));
      cm_close_function_context_st();
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`fid`, `(fid__pre:int)`)]]
    cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                 stmt->expr, 0, emitter);
    [[cst::proof]] { rewrite_st(THM_LIST(get_theorem_by_name("APPEND"))); }
    [[cst::where(`p`, `(p:cm_program)`)]]
    cm_emit_normalize_plan(emitter, return_ty);
    [[cst::proof]] { rewrite_st(THM_LIST(get_theorem_by_name("APPEND"))); }
    [[cst::where(`p`, `(p:cm_program)`)]]
    cm_emit_return_epilogue_plan(emitter);
    [[cst::proof]] {
      thm shape = assume_rule(`s == CMReturnS (expr_:cm_expr)`);
      term model_ty =
          `cm_function_ret
            (inth (fid__pre:int)
              (cm_program_functions (p:cm_program)))`;
      term code =
          `cm_expr_code_for (p:cm_program) (fid__pre:int)
             (pc__pre:int) (temp__pre:int) (expr_:cm_expr) 0i ++
           cm_char_normalize_code ${model_ty:cm_type} ++
           cm_return_epilogue`;
      cm_restore_code_plan_end_st(cm_stmt_code_shape(shape, code));
      cm_close_stmt_case_st(shape, CMC_STMT_RETURN);
      cm_close_stmt_rep_st();
    }
  }
}
