static int cm_max(int a, int b)
{
  int result;
  if (a <= b) {
    result = b;
  } else {
    result = a;
  }
  return result;
}

int cmc_is_pointer(int ty)
{
  int result;
  if (ty >= 1024) {
    result = 1;
  } else {
    result = 0;
  }
  return result;
}

void cmc_is_pointer_value(int ty, int *pointer)
{
  int result = cmc_is_pointer(ty);
  *pointer = result;
}

int cmc_pointee(int ty)
{
  return ty - 1024;
}

static int cmc_leaf_size(int ty)
{
  int result;
  if (ty >= 1024) {
    result = 8;
  } else if (ty == CMC_TYPE_INT) {
    result = 8;
  } else if (ty == CMC_TYPE_CHAR) {
    result = 1;
  } else {
    result = 0;
  }
  return result;
}

long long cmc_code_slot_size(int code, int count)
{
  int leaf = cmc_leaf_size(code);
  long long result;
  if (count == 0) {
    result = leaf;
  } else {
    result = (long long)count * leaf;
  }
  return result;
}

static long long cmc_members_size(struct cm_member *member)
{
  long long total;
  if (member == 0) {
    total = 0;
  } else {
    long long size = cmc_code_slot_size(member->ty, member->count);
    struct cm_member *next = member->next;
    long long rest_size = cmc_members_size(next);
    total = size + rest_size;
  }
  return total;
}

static long long cmc_struct_size_at(struct cm_struct *item, int sid)
{
  long long total;
  if (item == 0) {
    total = 0;
  } else {
    if (sid == 0) {
      total = cmc_members_size(item->members);
    } else {
      struct cm_struct *next = item->next;
      total = cmc_struct_size_at(next, sid - 1);
    }
  }
  return total;
}

static int cmc_nonzero(int n)
{
  int result;
  if (n == 0) {
    result = 0;
  } else {
    result = 1;
  }
  return result;
}

static int cmc_global_array_at(struct cm_global *item, int index)
{
  int result;
  if (item == 0) {
    result = 0;
  } else {
    if (index == 0) {
      result = cmc_nonzero(item->count);
    } else {
      struct cm_global *next = item->next;
      result = cmc_global_array_at(next, index - 1);
    }
  }
  return result;
}

static int cmc_slot_array_at(struct cm_slot *item, int index)
{
  int result;
  if (item == 0) {
    result = 0;
  } else {
    if (index == 0) {
      result = cmc_nonzero(item->count);
    } else {
      struct cm_slot *next = item->next;
      result = cmc_slot_array_at(next, index - 1);
    }
  }
  return result;
}

int cmc_slot_type_at(struct cm_slot *item, int index)
{
  int result;
  if (item == 0) {
    result = 0;
  } else {
    if (index == 0) {
      result = item->ty;
    } else {
      struct cm_slot *next = item->next;
      result = cmc_slot_type_at(next, index - 1);
    }
  }
  return result;
}

static int cmc_member_array_at(struct cm_member *item, int index)
{
  int result;
  if (item == 0) {
    result = 0;
  } else {
    if (index == 0) {
      result = cmc_nonzero(item->count);
    } else {
      struct cm_member *next = item->next;
      result = cmc_member_array_at(next, index - 1);
    }
  }
  return result;
}

long long cmc_type_size_at(struct cm_struct *items, int ty)
{
  long long result;
  if (ty >= 1024) {
    result = 8;
  } else if (ty == CMC_TYPE_INT) {
    result = 8;
  } else if (ty == CMC_TYPE_CHAR) {
    result = 1;
  } else {
    result = cmc_struct_size_at(items, ty - 2);
  }
  return result;
}

static long long cmc_slots_size(struct cm_slot *slot)
{
  long long total;
  if (slot == 0) {
    total = 0;
  } else {
    long long size = cmc_code_slot_size(slot->ty, slot->count);
    struct cm_slot *next = slot->next;
    long long rest_size = cmc_slots_size(next);
    total = size + rest_size;
  }
  return total;
}

static long long cmc_slots_prefix(struct cm_slot *slot, int index)
{
  long long total;
  if (slot == 0) {
    total = 0;
  } else {
    if (index == 0) {
      total = 0;
    } else {
      long long size = cmc_code_slot_size(slot->ty, slot->count);
      struct cm_slot *next = slot->next;
      long long rest_size = cmc_slots_prefix(next, index - 1);
      total = size + rest_size;
    }
  }
  return total;
}

static long long cmc_members_prefix(struct cm_member *node, int index)
{
  long long total;
  if (node == 0) {
    total = 0;
  } else {
    if (index == 0) {
      total = 0;
    } else {
      long long size = cmc_code_slot_size(node->ty, node->count);
      struct cm_member *next = node->next;
      long long rest_size = cmc_members_prefix(next, index - 1);
      total = size + rest_size;
    }
  }
  return total;
}

long long cmc_member_offset_at(struct cm_struct *item,
                                      int sid, int index)
{
  long long total;
  if (item == 0) {
    total = 0;
  } else {
    if (sid == 0) {
      total = cmc_members_prefix(item->members, index);
    } else {
      struct cm_struct *next = item->next;
      total = cmc_member_offset_at(next, sid - 1, index);
    }
  }
  return total;
}

static int cmc_struct_member_array_at(struct cm_struct *item,
                                      int sid, int index)
{
  int result;
  if (item == 0) {
    result = 0;
  } else {
    if (sid == 0) {
      result = cmc_member_array_at(item->members, index);
    } else {
      struct cm_struct *next = item->next;
      result = cmc_struct_member_array_at(next, sid - 1, index);
    }
  }
  return result;
}

long long cmc_globals_size(struct cm_global *node)
{
  long long total;
  if (node == 0) {
    total = 0;
  } else {
    long long size = cmc_code_slot_size(node->ty, node->count);
    struct cm_global *next = node->next;
    long long rest_size = cmc_globals_size(next);
    total = size + rest_size;
  }
  return total;
}

static long long cmc_globals_prefix(struct cm_global *node, int index)
{
  long long total;
  if (node == 0) {
    total = 0;
  } else {
    if (index == 0) {
      total = 0;
    } else {
      long long size = cmc_code_slot_size(node->ty, node->count);
      struct cm_global *next = node->next;
      long long rest_size = cmc_globals_prefix(next, index - 1);
      total = size + rest_size;
    }
  }
  return total;
}

long long cmc_strings_size(struct cm_string *node)
{
  long long total;
  if (node == 0) {
    total = 0;
  } else {
    long long size = node->length;
    size = size + 1;
    struct cm_string *next = node->next;
    long long rest_size = cmc_strings_size(next);
    total = size + rest_size;
  }
  return total;
}

static long long cmc_strings_prefix(struct cm_string *node, int index)
{
  long long total;
  if (node == 0) {
    total = 0;
  } else {
    if (index == 0) {
      total = 0;
    } else {
      long long size = node->length;
      size = size + 1;
      struct cm_string *next = node->next;
      long long rest_size = cmc_strings_prefix(next, index - 1);
      total = size + rest_size;
    }
  }
  return total;
}

long long cmc_global_address(struct cm_global *globals, int index)
{
  long long prefix = cmc_globals_prefix(globals, index);
  long long address = 16LL + prefix;
  return address;
}

long long cmc_string_address(struct cm_global *globals,
                                    struct cm_string *strings, int index)
{
  long long global_size = cmc_globals_size(globals);
  long long prefix = cmc_strings_prefix(strings, index);
  long long address = 16LL + global_size;
  address = address + prefix;
  return address;
}

void cmc_binding_array_value(struct cm_program *program, int fid,
                                    struct cm_function *fn,
                                    int scope, int slot, int *array)
{
  int result;
  if (scope == CMC_BIND_GLOBAL) {
    result = cmc_global_array_at(program->globals, slot);
  } else if (scope == CMC_BIND_LOCAL) {
    result = cmc_slot_array_at(fn->locals, slot);
  } else {
    result = 0;
  }
  *array = result;
}

int cmc_binding_array(struct cm_program *program, int fid,
                             struct cm_function *fn,
                             int scope, int slot)
{
  int result;
  cmc_binding_array_value(program, fid, fn, scope, slot, &result);
  return result;
}

int cmc_member_array(struct cm_program *program, int base_ty, int mid)
{
  int pointee = cmc_pointee(base_ty);
  int sid = (pointee % 1024) - 2;
  int result = cmc_struct_member_array_at(program->structs, sid, mid);
  return result;
}

void cmc_member_array_value(struct cm_program *program,
                                   int base_ty, int mid, int *array)
{
  int result;
  result = cmc_member_array(program, base_ty, mid);
  *array = result;
}

static void cm_expr_temps(struct cm_expr *expr,
                          int *lvalue, int *rvalue)
    ;

int cm_args_length(struct cm_arg *arg)
{
  int count;
  if (arg == 0) {
    count = 0;
  } else {
    count = cm_args_length(arg->next);
    count = count + 1;
  }
  return count;
}

static void cmc_args_tpair(struct cm_arg *arg, int *count, int *depth)
{
  if (arg == 0) {
    *count = 0;
    *depth = 0;
  } else {
    struct cm_expr *child = arg->expr;
    int child_lvalue;
    int child_rvalue;
    cm_expr_temps(child, &child_lvalue, &child_rvalue);
    int rest_count;
    int rest_depth;
    cmc_args_tpair(arg->next, &rest_count, &rest_depth);
    int new_count = rest_count + 1;
    int new_depth = cm_max(child_rvalue, rest_depth);
    *count = new_count;
    *depth = new_depth;
  }
}

static void cm_expr_temps(struct cm_expr *expr,
                          int *lvalue, int *rvalue)
{
  int out_lvalue = 0;
  int out_rvalue = 0;
  if (expr->kind == CMC_EXPR_ASSIGN) {
    int left_lvalue;
    int left_rvalue;
    int right_lvalue;
    int right_rvalue;
    cm_expr_temps(expr->a, &left_lvalue, &left_rvalue);
    cm_expr_temps(expr->b, &right_lvalue, &right_rvalue);
    out_rvalue = cm_max(left_lvalue, 1 + right_rvalue);
  } else if (expr->kind == CMC_EXPR_BINARY) {
    int left_lvalue;
    int left_rvalue;
    int right_lvalue;
    int right_rvalue;
    cm_expr_temps(expr->a, &left_lvalue, &left_rvalue);
    cm_expr_temps(expr->b, &right_lvalue, &right_rvalue);
    if (expr->op == CMC_BIN_OR) {
      out_rvalue = cm_max(left_rvalue, right_rvalue);
    } else if (expr->op == CMC_BIN_AND) {
      out_rvalue = cm_max(left_rvalue, right_rvalue);
    } else {
      out_rvalue = cm_max(left_rvalue, 1 + right_rvalue);
    }
  } else if (expr->kind == CMC_EXPR_UNARY) {
    int child_lvalue;
    int child_rvalue;
    cm_expr_temps(expr->a, &child_lvalue, &child_rvalue);
    if (expr->op == CMC_UN_DEREF) {
      out_lvalue = child_rvalue;
      out_rvalue = child_rvalue;
    } else if (expr->op == CMC_UN_ADDR) {
      out_rvalue = child_lvalue;
    } else {
      out_rvalue = child_rvalue;
    }
  } else if (expr->kind == CMC_EXPR_INDEX) {
    int base_lvalue;
    int base_rvalue;
    int index_lvalue;
    int index_rvalue;
    cm_expr_temps(expr->a, &base_lvalue, &base_rvalue);
    cm_expr_temps(expr->b, &index_lvalue, &index_rvalue);
    out_lvalue = cm_max(base_rvalue, 1 + index_rvalue);
    out_rvalue = out_lvalue;
  } else if (expr->kind == CMC_EXPR_MEMBER) {
    int base_lvalue;
    int base_rvalue;
    cm_expr_temps(expr->a, &base_lvalue, &base_rvalue);
    out_lvalue = base_rvalue;
    out_rvalue = base_rvalue;
  } else if (expr->kind == CMC_EXPR_CALL) {
    int count;
    int depth;
    cmc_args_tpair(expr->args, &count, &depth);
    out_rvalue = count + depth;
  } else if (expr->kind == CMC_EXPR_PUTC) {
    int child_lvalue;
    int child_rvalue;
    cm_expr_temps(expr->a, &child_lvalue, &child_rvalue);
    out_rvalue = child_rvalue;
  } else if (expr->kind == CMC_EXPR_PUTI) {
    int child_lvalue;
    int child_rvalue;
    cm_expr_temps(expr->a, &child_lvalue, &child_rvalue);
    out_rvalue = child_rvalue;
  } else if (expr->kind == CMC_EXPR_EXIT) {
    int child_lvalue;
    int child_rvalue;
    cm_expr_temps(expr->a, &child_lvalue, &child_rvalue);
    out_rvalue = child_rvalue;
  } else if (expr->kind == CMC_EXPR_CONST) {
  } else if (expr->kind == CMC_EXPR_STRING) {
  } else if (expr->kind == CMC_EXPR_VAR) {
  } else if (expr->kind == CMC_EXPR_SIZEOF) {
  } else if (expr->kind == CMC_EXPR_GETC) {
  } else {
  }
  *lvalue = out_lvalue;
  *rvalue = out_rvalue;
}

static int cm_expr_rtemps(struct cm_expr *expr)
{
  int lvalue;
  int rvalue;
  cm_expr_temps(expr, &lvalue, &rvalue);
  return rvalue;
}

int cmc_stmt_temps(struct cm_stmt *stmt)
{
  int result = 0;
  if (stmt->kind == CMC_STMT_EXPR) {
    result = cm_expr_rtemps(stmt->expr);
  } else if (stmt->kind == CMC_STMT_INIT) {
    result = cm_expr_rtemps(stmt->expr);
  } else if (stmt->kind == CMC_STMT_RETURN) {
    result = cm_expr_rtemps(stmt->expr);
  } else if (stmt->kind == CMC_STMT_SEQ) {
    int first_temps = cmc_stmt_temps(stmt->a);
    int second_temps = cmc_stmt_temps(stmt->b);
    result = cm_max(first_temps, second_temps);
  } else if (stmt->kind == CMC_STMT_BLOCK) {
    result = cmc_stmt_temps(stmt->a);
  } else if (stmt->kind == CMC_STMT_IF) {
    int guard_temps = cm_expr_rtemps(stmt->expr);
    int yes_temps = cmc_stmt_temps(stmt->a);
    int no_temps = cmc_stmt_temps(stmt->b);
    int branch_temps = cm_max(yes_temps, no_temps);
    result = cm_max(guard_temps, branch_temps);
  } else if (stmt->kind == CMC_STMT_WHILE) {
    int guard_temps = cm_expr_rtemps(stmt->expr);
    int body_temps = cmc_stmt_temps(stmt->a);
    result = cm_max(guard_temps, body_temps);
  } else if (stmt->kind == CMC_STMT_SKIP) {
    result = 0;
  } else if (stmt->kind == CMC_STMT_DECL) {
    result = 0;
  } else if (stmt->kind == CMC_STMT_BREAK) {
    result = 0;
  } else if (stmt->kind == CMC_STMT_CONTINUE) {
    result = 0;
  } else {
    result = 0;
  }
  return result;
}

long long cmc_frame_size(struct cm_function *fn)
{
  long long params_size = cmc_slots_size(fn->params);
  long long locals_size = cmc_slots_size(fn->locals);
  int temps = cmc_stmt_temps(fn->body);
  return 8 + params_size + locals_size + 8LL * temps;
}

long long cmc_param_offset(struct cm_function *fn, int slot)
{
  long long prefix = cmc_slots_prefix(fn->params, slot);
  return 8 + prefix;
}

long long cmc_local_offset(struct cm_function *fn, int slot)
{
  long long params_size = cmc_slots_size(fn->params);
  long long prefix = cmc_slots_prefix(fn->locals, slot);
  return 8 + params_size + prefix;
}

long long cmc_temp_offset(struct cm_function *fn, int temp)
{
  long long params_size = cmc_slots_size(fn->params);
  long long locals_size = cmc_slots_size(fn->locals);
  return 8 + params_size + locals_size + 8LL * temp;
}

int cm_normalize_count(int ty)
{
  int result;
  if (ty == CMC_TYPE_CHAR) {
    result = 6;
  } else {
    result = 0;
  }
  return result;
}
