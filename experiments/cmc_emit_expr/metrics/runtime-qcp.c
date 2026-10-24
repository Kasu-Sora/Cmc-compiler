
struct cm_emitter { struct cm_output *output; int pc; };



































void cm_emit_expr(struct cm_program *program, int fid,
                  struct cm_function *fn, int pc, int temp,
                  int temp_limit, struct cm_expr *expr, int lvalue,
                  struct cm_emitter *emitter)
;

static void cm_emit_intrinsic_expr(struct cm_program *program, int fid,
                            struct cm_function *fn, int pc, int temp,
                            int temp_limit, struct cm_expr *expr,
                            int lvalue, struct cm_emitter *emitter)

{
  
  
  
  

  if (expr->kind == CMC_EXPR_PUTC) {
    if (!lvalue) {
      
  
  
  
  
  
  cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                   expr->a, 0, emitter) ;
      cm_emit_plan(emitter, CMC_OP_DUP, 0) ;
      cm_emit_plan(emitter, CMC_OP_PUTC, 0) ;
    } else {
    }
  } else if (expr->kind == CMC_EXPR_PUTI) {
    if (!lvalue) {
      
  
  
  
  
  
  cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                   expr->a, 0, emitter) ;
      cm_emit_plan(emitter, CMC_OP_DUP, 0) ;
      cm_emit_plan(emitter, CMC_OP_PUTI, 0) ;
    } else {
    }
  } else {
    if (!lvalue) {
      
  
  
  
  
  
  cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                   expr->a, 0, emitter) ;
      cm_emit_normalize_plan(emitter, CMC_TYPE_CHAR) ;
      cm_emit_plan(emitter, CMC_OP_HALT, 0) ;
    } else {
    }
  }

  
  
}



static void cm_emit_unary_expr(struct cm_program *program, int fid,
                               struct cm_function *fn, int pc, int temp,
                               int temp_limit, struct cm_expr *expr,
                               int lvalue, struct cm_emitter *emitter)

{
  
  
  
  

  if (expr->op == CMC_UN_DEREF) {
    if (!lvalue) {
      
  
  
  
  cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                   expr->a, 0, emitter) ;
      cm_emit_load_plan(emitter, expr->ty) ;
    } else {
      
  
  
  
  cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                   expr->a, 0, emitter) ;
    }
  } else if (expr->op == CMC_UN_ADDR) {
    if (!lvalue) {
      
  
  
  
  cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                   expr->a, 1, emitter) ;
    } else {
    }
  } else {
    if (!lvalue) {
      if (expr->op == CMC_UN_NEG) {
        
  
  
  
  cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                     expr->a, 0, emitter) ;
        cm_emit_plan(emitter, CMC_OP_PUSH, -1) ;
        cm_emit_plan(emitter, CMC_OP_MUL, 0) ;
      } else {
        
  
  
  
  cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                     expr->a, 0, emitter) ;
        cm_emit_plan(emitter, CMC_OP_PUSH, 0) ;
        cm_emit_plan(emitter, CMC_OP_EQ, 0) ;
      }
    } else {
    }
  }

  
  
}



static void cm_emit_index_expr(struct cm_program *program, int fid,
                               struct cm_function *fn, int pc, int temp,
                               int temp_limit, struct cm_expr *expr,
                               int lvalue, struct cm_emitter *emitter)

{
  
  
  
  

  int base_count = cm_expr_rvalue_count_context(
      program, fid, fn, expr->a) ;
  long long element_size = cm_type_size_value(program, expr->ty) ;
  
  
  
  
  cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
               expr->a, 0, emitter) ;
  cm_emit_temp_store_plan(fn, temp, emitter) ;
  int right_pc = pc + (base_count + 5);
  int right_temp = temp + 1;
  struct cm_expr *right_expr = expr->b;
  
  
  cm_emit_expr(program, fid, fn, right_pc, right_temp, temp_limit,
               right_expr, 0, emitter) ;
  cm_emit_plan(emitter, CMC_OP_PUSH, element_size) ;
  cm_emit_plan(emitter, CMC_OP_MUL, 0) ;
  cm_emit_temp_load_plan(fn, temp, emitter) ;
  cm_emit_plan(emitter, CMC_OP_ADD, 0) ;
  if (!lvalue) {
    
  
  cm_emit_load_plan(emitter, expr->ty) ;
  } else {
  }

  
  
}



static void cm_emit_assignment_expr(struct cm_program *program, int fid,
                                    struct cm_function *fn, int pc, int temp,
                                    int temp_limit, struct cm_expr *expr,
                                    int lvalue, struct cm_emitter *emitter)

{
  
  
  
  

  if (!lvalue) {
    int left_count = cm_expr_lvalue_count_context(
        program, fid, fn, expr->a) ;
    
  
  
  
  cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                 expr->a, 1, emitter) ;
    cm_emit_temp_store_plan(fn, temp, emitter) ;
    int right_pc = pc + (left_count + 5);
    int right_temp = temp + 1;
    struct cm_expr *right_expr = expr->b;
    
  
  cm_emit_expr(program, fid, fn, right_pc, right_temp, temp_limit,
                 right_expr, 0, emitter) ;
    cm_emit_normalize_plan(emitter, expr->ty) ;
    cm_emit_temp_load_plan(fn, temp, emitter) ;
    cm_emit_store_plan(emitter, expr->ty) ;
    cm_emit_temp_load_plan(fn, temp, emitter) ;
    cm_emit_load_plan(emitter, expr->ty) ;
  } else {
  }

  
  
}



static void cm_emit_binary_expr(struct cm_program *program, int fid,
                                struct cm_function *fn, int pc, int temp,
                                int temp_limit, struct cm_expr *expr,
                                int lvalue, struct cm_emitter *emitter)

{
  
  
  
  

  if (!lvalue) {
    int left_count = cm_expr_rvalue_count_context(
        program, fid, fn, expr->a) ;
    int right_count = cm_expr_rvalue_count_context(
        program, fid, fn, expr->b) ;
    if (expr->op == CMC_BIN_OR || expr->op == CMC_BIN_AND) {
      if (expr->op == CMC_BIN_OR) {
      } else {
      }
      
  
  
  
  cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                   expr->a, 0, emitter) ;
      long long first_target =
          (long long)pc +
          ((long long)left_count + ((long long)right_count + 4LL));
      if (expr->op == CMC_BIN_OR) {
        cm_emit_plan(emitter, CMC_OP_JNZ, first_target) ;
      } else {
        cm_emit_plan(emitter, CMC_OP_JZ, first_target) ;
      }
      int right_pc = pc + (left_count + 1);
      struct cm_expr *right_expr = expr->b;
      if (expr->op == CMC_BIN_OR) {
        
  
  cm_emit_expr(program, fid, fn, right_pc, temp,
                     temp_limit, right_expr, 0, emitter) ;
      } else {
        
  
  cm_emit_expr(program, fid, fn, right_pc, temp,
                     temp_limit, right_expr, 0, emitter) ;
      }
      cm_emit_plan(emitter, CMC_OP_PUSH, 0) ;
      cm_emit_plan(emitter, CMC_OP_NE, 0) ;
      long long final_target =
          (long long)pc +
          ((long long)left_count + ((long long)right_count + 5LL));
      cm_emit_plan(emitter, CMC_OP_JMP, final_target) ;
      long long short_value =
          expr->op == CMC_BIN_OR ? 1LL : 0LL;
      
      cm_emit_plan(emitter, CMC_OP_PUSH, short_value) ;
      if (expr->op == CMC_BIN_OR) {
      } else {
      }
    } else {
      
  
  
  
  cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                   expr->a, 0, emitter) ;
      cm_emit_temp_store_plan(fn, temp, emitter) ;
      int right_pc = pc + (left_count + 5);
      int right_temp = temp + 1;
      struct cm_expr *right_expr = expr->b;
      
  
  cm_emit_expr(program, fid, fn, right_pc, right_temp,
                   temp_limit, right_expr, 0, emitter) ;
      cm_emit_binary_finish_plan(program, fid, fn, temp, expr->op,
                                 expr->a, expr->b, emitter) ;
    }
  } else {
  }

  
  
}



static void cm_emit_member_expr(struct cm_program *program, int fid,
                                struct cm_function *fn, int pc, int temp,
                                int temp_limit, struct cm_expr *expr,
                                int lvalue, struct cm_emitter *emitter)

{
  
  
  
  

  int member_id = (int)expr->value;
  int base_type;
  cm_expr_type_code_context(expr->a, &base_type) ;
  int array_value = cm_member_array_value_context(
      program, base_type, member_id) ;
  long long offset = cm_member_offset_value_context(
      program, base_type, member_id) ;
  
  
  
  
  cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
               expr->a, 0, emitter) ;
  cm_emit_plan(emitter, CMC_OP_PUSH, offset) ;
  cm_emit_plan(emitter, CMC_OP_ADD, 0) ;
  if (!lvalue) {
    if (!array_value) {
      
  
  cm_emit_load_plan(emitter, expr->ty) ;
    } else {
    }
  } else {
  }

  
  
}



void cm_emit_expr(struct cm_program *program, int fid,
                  struct cm_function *fn, int pc, int temp,
                  int temp_limit, struct cm_expr *expr, int lvalue,
                  struct cm_emitter *emitter)

{
  

  if (expr->kind == CMC_EXPR_CONST) {
    
  
  
  
  cm_emit_simple_expr(program, fid, fn, pc, temp,
        expr, lvalue, emitter) ;
  } else if (expr->kind == CMC_EXPR_STRING) {
    
  
  
  
  cm_emit_simple_expr(program, fid, fn, pc, temp,
        expr, lvalue, emitter) ;
  } else if (expr->kind == CMC_EXPR_VAR) {
    
  
  
  
  cm_emit_simple_expr(program, fid, fn, pc, temp,
        expr, lvalue, emitter) ;
  } else if (expr->kind == CMC_EXPR_ASSIGN) {
    
  
  
  
  cm_emit_assignment_expr(program, fid, fn, pc, temp,
        temp_limit, expr, lvalue, emitter) ;
  } else if (expr->kind == CMC_EXPR_BINARY) {
    
  
  
  
  cm_emit_binary_expr(program, fid, fn, pc, temp,
        temp_limit, expr, lvalue, emitter) ;
  } else if (expr->kind == CMC_EXPR_UNARY) {
    
  
  
  
  cm_emit_unary_expr(program, fid, fn, pc, temp,
        temp_limit, expr, lvalue, emitter) ;
  } else if (expr->kind == CMC_EXPR_INDEX) {
    
  
  
  
  cm_emit_index_expr(program, fid, fn, pc, temp,
        temp_limit, expr, lvalue, emitter) ;
  } else if (expr->kind == CMC_EXPR_MEMBER) {
    
  
  
  
  cm_emit_member_expr(program, fid, fn, pc, temp,
        temp_limit, expr, lvalue, emitter) ;
  } else if (expr->kind == CMC_EXPR_CALL) {
    
  
  cm_emit_call_expr(program, fid, fn, pc, temp,
        temp_limit, expr, lvalue, emitter) ;
  } else if (expr->kind == CMC_EXPR_SIZEOF) {
    
  
  
  
  cm_emit_simple_expr(program, fid, fn, pc, temp,
        expr, lvalue, emitter) ;
  } else if (expr->kind == CMC_EXPR_GETC) {
    
  
  
  
  cm_emit_simple_expr(program, fid, fn, pc, temp,
        expr, lvalue, emitter) ;
  } else if (expr->kind == CMC_EXPR_PUTC) {
    
  
  
  
  cm_emit_intrinsic_expr(program, fid, fn, pc, temp,
        temp_limit, expr, lvalue, emitter) ;
  } else if (expr->kind == CMC_EXPR_PUTI) {
    
  
  
  
  cm_emit_intrinsic_expr(program, fid, fn, pc, temp,
        temp_limit, expr, lvalue, emitter) ;
  } else {
    
  
  
  
  cm_emit_intrinsic_expr(program, fid, fn, pc, temp,
        temp_limit, expr, lvalue, emitter) ;
  }
}

