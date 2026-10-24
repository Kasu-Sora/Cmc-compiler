void cmc_emit_if_stmt(struct cm_program *program, int fid,
                      struct cm_function *fn, int pc, int temp,
                      int temp_limit, int break_pc, int continue_pc,
                      struct cm_stmt *stmt, struct cm_emitter *emitter)
{
    int guard_count = cm_expr_rvalue_count_context(
        program, fid, fn, stmt->expr);
    int yes_count = cm_stmt_code_count_context(
        program, fid, fn, stmt->a);
    int no_count = cm_stmt_code_count_context(
        program, fid, fn, stmt->b);
    long long no_target =
        (long long)pc +
        ((long long)guard_count + ((long long)yes_count + 2LL));
    long long end_target =
        (long long)pc +
        ((long long)guard_count +
         ((long long)yes_count + ((long long)no_count + 2LL)));
    int yes_pc = pc + (guard_count + 1);
    int no_pc = pc + (guard_count + (1 + (yes_count + 1)));
    int end_pc =
        pc + (guard_count + (1 + (yes_count + (1 + no_count))));
    cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                 stmt->expr, 0, emitter);
    cm_emit_plan(emitter, CMC_OP_JZ, no_target);
    cmc_emit_stmt(program, fid, fn, yes_pc, temp, temp_limit,
                 break_pc, continue_pc, stmt->a, emitter);
    cm_emit_plan(emitter, CMC_OP_JMP, end_target);
    cmc_emit_stmt(program, fid, fn, no_pc, temp, temp_limit,
                 break_pc, continue_pc, stmt->b, emitter);
}

void cmc_emit_stmt(struct cm_program *program, int fid,
                  struct cm_function *fn, int pc, int temp,
                  int temp_limit, int break_pc, int continue_pc,
                  struct cm_stmt *stmt, struct cm_emitter *emitter)
{
  if (stmt->kind == CMC_STMT_SKIP) {
  } else if (stmt->kind == CMC_STMT_EXPR) {
    cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                 stmt->expr, 0, emitter);
    cm_emit_plan(emitter, CMC_OP_POP, 0);
  } else if (stmt->kind == CMC_STMT_DECL) {
  } else if (stmt->kind == CMC_STMT_INIT) {
    int local_ty = cmc_slot_type_at(fn->locals, stmt->slot);
    cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                 stmt->expr, 0, emitter);
    cm_emit_normalize_plan(emitter, local_ty);
    cm_emit_binding_address_plan(program, fn, CMC_BIND_LOCAL,
                                 stmt->slot, emitter);
    cm_emit_store_plan(emitter, local_ty);
  } else if (stmt->kind == CMC_STMT_SEQ) {
    int first_count = cm_stmt_code_count_context(
        program, fid, fn, stmt->a);
    cmc_emit_stmt(program, fid, fn, pc, temp, temp_limit,
                 break_pc, continue_pc, stmt->a, emitter);
    int second_pc = pc + first_count;
    cmc_emit_stmt(program, fid, fn, second_pc, temp, temp_limit,
                 break_pc, continue_pc, stmt->b, emitter);
  } else if (stmt->kind == CMC_STMT_BLOCK) {
    cmc_emit_stmt(program, fid, fn, pc, temp, temp_limit,
                 break_pc, continue_pc, stmt->a, emitter);
  } else if (stmt->kind == CMC_STMT_IF) {
    cmc_emit_if_stmt(program, fid, fn, pc, temp, temp_limit,
                     break_pc, continue_pc, stmt, emitter);
  } else if (stmt->kind == CMC_STMT_WHILE) {
    int guard_count = cm_expr_rvalue_count_context(
        program, fid, fn, stmt->expr);
    int body_count = cm_stmt_code_count_context(
        program, fid, fn, stmt->a);
    int body_pc = pc + (guard_count + 1);
    int loop_end = pc + (guard_count + (1 + (body_count + 1)));
    cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                 stmt->expr, 0, emitter);
    cm_emit_plan(emitter, CMC_OP_JZ, (long long)loop_end);
    cmc_emit_stmt(program, fid, fn, body_pc, temp, temp_limit,
                 loop_end, pc, stmt->a, emitter);
    cm_emit_plan(emitter, CMC_OP_JMP, (long long)pc);
  } else if (stmt->kind == CMC_STMT_BREAK) {
    cm_emit_plan(emitter, CMC_OP_JMP, (long long)break_pc);
  } else if (stmt->kind == CMC_STMT_CONTINUE) {
    cm_emit_plan(emitter, CMC_OP_JMP, (long long)continue_pc);
  } else {
    int return_ty = fn->ret_ty;
    cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                 stmt->expr, 0, emitter);
    cm_emit_normalize_plan(emitter, return_ty);
    cm_emit_return_epilogue_plan(emitter);
  }
}
