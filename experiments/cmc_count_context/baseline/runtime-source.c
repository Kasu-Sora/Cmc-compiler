void cm_expr_type_code_context(struct cm_expr *expr, int *code)
{
  *code = expr->ty;
}

int cm_expr_lvalue_count_context(struct cm_program *program, int fid,
                                 struct cm_function *fn,
                                 struct cm_expr *expr)
{
  int result = cm_expr_lvalue_count(program, fid, fn, expr);
  return result;
}

int cm_expr_rvalue_count_context(struct cm_program *program, int fid,
                                 struct cm_function *fn,
                                 struct cm_expr *expr)
{
  int result = cm_expr_rvalue_count(program, fid, fn, expr);
  return result;
}

int cm_stmt_code_count_context(struct cm_program *program, int fid,
                               struct cm_function *fn,
                               struct cm_stmt *stmt)
{
  int result = cmc_stmt_code_count(program, fid, fn, stmt);
  return result;
}
