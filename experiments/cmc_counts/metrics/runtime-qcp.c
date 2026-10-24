






















static void cmc_expr_type_code_value(struct cm_expr *expr, int *code)

{
  
  *code = expr->ty;
}

static void cm_expr_counts(struct cm_program *program, int fid,
                           struct cm_function *fn,
                           struct cm_expr *expr, int *lvalue, int *rvalue)

;

int cm_expr_lvalue_count(struct cm_program *program, int fid,
                                struct cm_function *fn,
                                struct cm_expr *expr)

{
  int lvalue;
  int rvalue;
  cm_expr_counts(program, fid, fn, expr, &lvalue, &rvalue) ;
  return lvalue;
}

int cm_expr_rvalue_count(struct cm_program *program, int fid,
                                struct cm_function *fn,
                                struct cm_expr *expr)

{
  int lvalue;
  int rvalue;
  cm_expr_counts(program, fid, fn, expr, &lvalue, &rvalue) ;
  return rvalue;
}

static void cmc_args_code_count(struct cm_program *program, int fid,
                                struct cm_function *fn,
                                struct cm_arg *arg, int *count)

{
  if (arg == 0) {
    *count = 1;
    return;
  } else {
  
  int head_lvalue;
  int head_count;
  cm_expr_counts(program, fid, fn, arg->expr,
                 &head_lvalue, &head_count) ;
  int tail_count;
  cmc_args_code_count(program, fid, fn, arg->next, &tail_count) ;
  *count = head_count + 10 + tail_count;
  }
}

static void cm_binding_address_count_value(int scope, int *count)

{
  if (scope == CMC_BIND_GLOBAL) {
    *count = 1;
  } else {
    *count = 4;
  }
}

static void cm_expr_counts(struct cm_program *program, int fid,
                           struct cm_function *fn,
                           struct cm_expr *expr, int *lvalue, int *rvalue)

{
  
  int out_lvalue = 0;
  int out_rvalue = 0;
  if (expr->kind == CMC_EXPR_CONST) {
    out_rvalue = 1;
  } else if (expr->kind == CMC_EXPR_STRING) {
    out_rvalue = 1;
  } else if (expr->kind == CMC_EXPR_SIZEOF) {
    out_rvalue = 1;
  } else if (expr->kind == CMC_EXPR_GETC) {
    out_rvalue = 1;
  } else if (expr->kind == CMC_EXPR_VAR) {
  
    int address_count;
    cm_binding_address_count_value(expr->op, &address_count);
    out_lvalue = address_count;
    out_rvalue = address_count;
    int array;
    cmc_binding_array_value(program, fid, fn, expr->op,
                            (int)expr->value, &array) ;
    if (!array) {
      out_rvalue = out_rvalue + 1;
    } else {
    }
  } else if (expr->kind == CMC_EXPR_ASSIGN) {
  
    int dst_lvalue;
    int dst_rvalue;
    int src_lvalue;
    int src_rvalue;
    cm_expr_counts(program, fid, fn, expr->a,
                   &dst_lvalue, &dst_rvalue) ;
    cm_expr_counts(program, fid, fn, expr->b,
                   &src_lvalue, &src_rvalue) ;
    int normalize_count = cm_normalize_count(expr->ty);
    out_rvalue = dst_lvalue +
                 (5 + (src_rvalue + (normalize_count + 12)));
  } else if (expr->kind == CMC_EXPR_BINARY) {
  
    int left_lvalue;
    int left_rvalue;
    int right_lvalue;
    int right_rvalue;
    cm_expr_counts(program, fid, fn, expr->a,
                   &left_lvalue, &left_rvalue) ;
    cm_expr_counts(program, fid, fn, expr->b,
                   &right_lvalue, &right_rvalue) ;
    if (expr->op == CMC_BIN_OR) {
      out_rvalue = left_rvalue + (right_rvalue + 5);
    } else if (expr->op == CMC_BIN_AND) {
      out_rvalue = left_rvalue + (right_rvalue + 5);
    } else {
      if (expr->op == CMC_BIN_ADD) {
        int right_type;
        cmc_expr_type_code_value(expr->b, &right_type);
        int right_pointer;
        cmc_is_pointer_value(right_type, &right_pointer);
        if (right_pointer) {
          out_rvalue = left_rvalue + (right_rvalue + 14);
        } else {
          int left_type;
          cmc_expr_type_code_value(expr->a, &left_type);
          int left_pointer;
          cmc_is_pointer_value(left_type, &left_pointer);
          if (left_pointer) {
            out_rvalue = left_rvalue + (right_rvalue + 14);
          } else {
            out_rvalue = left_rvalue + (right_rvalue + 12);
          }
        }
      } else if (expr->op == CMC_BIN_SUB) {
        int left_type;
        cmc_expr_type_code_value(expr->a, &left_type);
        int left_pointer;
        cmc_is_pointer_value(left_type, &left_pointer);
        if (left_pointer) {
          out_rvalue = left_rvalue + (right_rvalue + 14);
        } else {
          out_rvalue = left_rvalue + (right_rvalue + 12);
        }
      } else {
        out_rvalue = left_rvalue + (right_rvalue + 12);
      }
    }
  } else if (expr->kind == CMC_EXPR_UNARY) {
  
    int child_lvalue;
    int child_rvalue;
    cm_expr_counts(program, fid, fn, expr->a,
                   &child_lvalue, &child_rvalue) ;
    if (expr->op == CMC_UN_DEREF) {
      out_lvalue = child_rvalue;
      out_rvalue = child_rvalue + 1;
    } else if (expr->op == CMC_UN_ADDR) {
      out_rvalue = child_lvalue;
    } else {
      out_rvalue = child_rvalue + 2;
    }
  } else if (expr->kind == CMC_EXPR_INDEX) {
  
    int base_lvalue;
    int base_rvalue;
    int index_lvalue;
    int index_rvalue;
    cm_expr_counts(program, fid, fn, expr->a,
                   &base_lvalue, &base_rvalue) ;
    cm_expr_counts(program, fid, fn, expr->b,
                   &index_lvalue, &index_rvalue) ;
    out_lvalue = base_rvalue + (index_rvalue + 13);
    out_rvalue = out_lvalue + 1;
  } else if (expr->kind == CMC_EXPR_MEMBER) {
  
    int base_lvalue;
    int base_rvalue;
    cm_expr_counts(program, fid, fn, expr->a,
                   &base_lvalue, &base_rvalue) ;
    out_lvalue = base_rvalue + 2;
    out_rvalue = out_lvalue;
    int base_type;
    cmc_expr_type_code_value(expr->a, &base_type);
    int member_id = (int)expr->value;
    int array;
    cmc_member_array_value(
        program, base_type, member_id, &array) ;
    if (!array) {
      out_rvalue = out_rvalue + 1;
    } else {
    }
  } else if (expr->kind == CMC_EXPR_CALL) {
  
    int args_count;
    cmc_args_code_count(
        program, fid, fn, expr->args, &args_count) ;
    out_rvalue = args_count;
  } else if (expr->kind == CMC_EXPR_PUTC) {
  
    int child_lvalue;
    int child_rvalue;
    cm_expr_counts(program, fid, fn, expr->a,
                   &child_lvalue, &child_rvalue) ;
    out_rvalue = child_rvalue + 2;
  } else if (expr->kind == CMC_EXPR_PUTI) {
  
    int child_lvalue;
    int child_rvalue;
    cm_expr_counts(program, fid, fn, expr->a,
                   &child_lvalue, &child_rvalue) ;
    out_rvalue = child_rvalue + 2;
  } else {
  
    int child_lvalue;
    int child_rvalue;
    cm_expr_counts(program, fid, fn, expr->a,
                   &child_lvalue, &child_rvalue) ;
    out_rvalue = child_rvalue + 7;
  }
  *lvalue = out_lvalue;
  *rvalue = out_rvalue;
}

int cmc_stmt_code_count(struct cm_program *program, int fid,
                               struct cm_function *fn,
                               struct cm_stmt *stmt)

{
  
  int result = 0;
  if (stmt->kind == CMC_STMT_SKIP) {
  } else if (stmt->kind == CMC_STMT_DECL) {
  } else if (stmt->kind == CMC_STMT_EXPR) {
  
    int expr_count =
        cm_expr_rvalue_count(program, fid, fn, stmt->expr) ;
    result = expr_count + 1;
  } else if (stmt->kind == CMC_STMT_INIT) {
  
    int ty_code = cmc_slot_type_at(fn->locals, stmt->slot);
    int expr_count =
        cm_expr_rvalue_count(program, fid, fn, stmt->expr) ;
    int normalize = cm_normalize_count(ty_code);
    result = expr_count + normalize + 5;
  } else if (stmt->kind == CMC_STMT_SEQ) {
  
    int first_count =
        cmc_stmt_code_count(program, fid, fn, stmt->a) ;
    int second_count =
        cmc_stmt_code_count(program, fid, fn, stmt->b) ;
    result = first_count + second_count;
  } else if (stmt->kind == CMC_STMT_BLOCK) {
  
    int first_count =
        cmc_stmt_code_count(program, fid, fn, stmt->a) ;
    result = first_count;
  } else if (stmt->kind == CMC_STMT_IF) {
  
    int expr_count =
        cm_expr_rvalue_count(program, fid, fn, stmt->expr) ;
    int first_count =
        cmc_stmt_code_count(program, fid, fn, stmt->a) ;
    int second_count =
        cmc_stmt_code_count(program, fid, fn, stmt->b) ;
    result = expr_count + 1 + first_count + 1 + second_count;
  } else if (stmt->kind == CMC_STMT_WHILE) {
  
    int expr_count =
        cm_expr_rvalue_count(program, fid, fn, stmt->expr) ;
    int first_count =
        cmc_stmt_code_count(program, fid, fn, stmt->a) ;
    result = expr_count + 1 + first_count + 1;
  } else if (stmt->kind == CMC_STMT_BREAK) {
    result = 1;
  } else if (stmt->kind == CMC_STMT_CONTINUE) {
    result = 1;
  } else {
  
    int expr_count =
        cm_expr_rvalue_count(program, fid, fn, stmt->expr) ;
    int normalize = cm_normalize_count(fn->ret_ty);
    result = expr_count + normalize + 6;
  }
  return result;
}

static int cmc_param_stores_count(struct cm_slot *param)

{
  int result;
  if (param == 0) {
    result = 0;
  } else {
  
    int normalize = cm_normalize_count(param->ty);
    struct cm_slot *next = param->next;
    int rest = cmc_param_stores_count(next);
    result = rest + normalize + 5;
  }
  return result;
}

int cmc_function_prologue_count(struct cm_function *fn)

{
  
  int params_count = cmc_param_stores_count(fn->params);
  int result = 14 + params_count;
  return result;
}

int cmc_function_code_count(struct cm_program *program, int fid,
                                   struct cm_function *fn)

{
  int prologue_count = cmc_function_prologue_count(fn) ;
  
  int body_count =
      cmc_stmt_code_count(program, fid, fn, fn->body) ;
  int result = prologue_count + body_count + 7;
  return result;
}

static int cmc_function_prefix_count(
    struct cm_program *program, struct cm_function *fn,
    int index, int remaining)

{
  if (remaining == 0) {
    return 0;
  };
  if (fn == 0) {
    return 0;
  };
  
  int head_count =
      cmc_function_code_count(program, index, fn) ;
  
  struct cm_function *next = fn->next;
  int tail_count = cmc_function_prefix_count(
      program, next, index + 1, remaining - 1) ;
  int result = head_count + tail_count;
  return result;
}

int cmc_function_pc(struct cm_program *program, int fid)

{
  
  struct cm_function *fn = program->functions;
  
  int prefix =
      cmc_function_prefix_count(program, fn, 0, fid) ;
  int result = 11 + prefix;
  return result;
}

static int cmc_functions_code_size_count(
    struct cm_program *program, struct cm_function *fn, int index)

{
  if (fn == 0) {
    return 0;
  };
  
  int head_count =
      cmc_function_code_count(program, index, fn) ;
  
  struct cm_function *next = fn->next;
  int tail_count =
      cmc_functions_code_size_count(program, next, index + 1) ;
  int result = head_count + tail_count;
  return result;
}

int cmc_model_code_length(struct cm_program *program)

{
  
  struct cm_function *functions = program->functions;
  
  int functions_size =
      cmc_functions_code_size_count(program, functions, 0) ;
  int result = 11 + functions_size;
  return result;
}

int cmc_model_data_length(struct cm_program *program)

{
  
  struct cm_global *globals = program->globals;
  struct cm_string *strings = program->strings;
  long long global_size = cmc_globals_size(globals);
  long long string_size = cmc_strings_size(strings);
  long long total = 8LL + global_size;
  total = total + string_size;
  int result = (int)total;
  return result;
}
