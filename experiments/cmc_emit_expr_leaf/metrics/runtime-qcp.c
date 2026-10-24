

struct cm_emitter {
  struct cm_output *output;
  int pc;
};

















static long long cmc_const_immediate(long long value, int ty)

{
  if (ty == CMC_TYPE_CHAR) {
    unsigned long long bits = (unsigned long long)value;
    unsigned char byte = (unsigned char)(bits % 256ULL);
    return (long long)byte;
  } else {
    return value;
  }
}

void cm_emit_const_expr(struct cm_program *program, int fid,
                        struct cm_function *fn, int pc, int temp,
                        struct cm_expr *expr, int lvalue,
                        struct cm_emitter *emitter)

{
 

  if (!lvalue) {
    long long immediate =
        cmc_const_immediate(expr->value, expr->ty) ;
    
    cm_emit_plan(emitter, CMC_OP_PUSH, immediate) ;
  } else {
  }
}

void cm_emit_string_expr(struct cm_program *program, int fid,
                         struct cm_function *fn, int pc, int temp,
                         struct cm_expr *expr, int lvalue,
                         struct cm_emitter *emitter)

{
 

  int string_id = (int)expr->value;
  if (!lvalue) {
    
    long long address = cmc_string_address(
        program->globals, program->strings, string_id) ;
    
    cm_emit_plan(emitter, CMC_OP_PUSH, address) ;
  } else {
  }
}

void cm_emit_getc_expr(struct cm_program *program, int fid,
                       struct cm_function *fn, int pc, int temp,
                       struct cm_expr *expr, int lvalue,
                       struct cm_emitter *emitter)

{
  if (!lvalue) {
    
    cm_emit_plan(emitter, CMC_OP_GETC, 0) ;
  } else {
  }
}

static long long cm_sizeof_value(struct cm_program *program,
                                 long long code)

{
  long long result;
  if (code >= 1024) {
    result = 8;
  } else {
    
    int narrowed = (int)code;
    
    result = cmc_type_size_at(program->structs, narrowed) ;
  }
  return result;
}

long long cm_type_size_value(struct cm_program *program,
                             long long code)

{
  return cm_sizeof_value(program, code) ;
}

void cm_emit_sizeof_expr(struct cm_program *program, int fid,
                         struct cm_function *fn, int pc, int temp,
                         struct cm_expr *expr, int lvalue,
                         struct cm_emitter *emitter)

{
 

  if (!lvalue) {
    long long size = cm_sizeof_value(program, expr->value) ;
    
    cm_emit_plan(emitter, CMC_OP_PUSH, size) ;
  } else {
  }
}

int cm_member_array_value_context(struct cm_program *program,
                                  int base_ty, int mid)

{
 

  int result = cmc_member_array(program, base_ty, mid) ;
  return result;
}

long long cm_member_offset_value_context(struct cm_program *program,
                                         int base_ty, int mid)

{
 

  int pointee = cmc_pointee(base_ty);
  int sid = (pointee % 1024) - 2;
  long long result = cmc_member_offset_at(program->structs, sid, mid) ;
  return result;
}
