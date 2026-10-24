
struct cm_emitter { struct cm_output *output; int pc; };



















static long long cm_pointer_scale_value(struct cm_program *program,
                                        struct cm_expr *expr)

{
  int type_code;
  cm_expr_type_code_context(expr, &type_code) ;
  int pointee_code = cmc_pointee(type_code);
  long long result = cm_type_size_value(program, pointee_code) ;
  return result;
}

static void cm_emit_binary_generic_fragment(struct cm_function *fn,
                                            int temp, int op,
                                            struct cm_emitter *emitter)

{
  
  cm_emit_temp_load_plan(fn, temp, emitter) ;
  cm_emit_plan(emitter, CMC_OP_SWAP, 0) ;
  int opcode = cmc_binary_opcode(op);
  cm_emit_plan(emitter, opcode, 0) ;
}

void cm_emit_binary_finish_plan(struct cm_program *program, int fid,
                                struct cm_function *fn, int temp, int op,
                                struct cm_expr *left,
                                struct cm_expr *right,
                                struct cm_emitter *emitter)

{
  int left_type;
  int right_type;
  cm_expr_type_code_context(left, &left_type) ;
  cm_expr_type_code_context(right, &right_type) ;
  int left_pointer;
  int right_pointer;
  cmc_is_pointer_value(left_type, &left_pointer);
  cmc_is_pointer_value(right_type, &right_pointer);
  if (op == CMC_BIN_ADD && right_pointer) {
    long long scale = cm_pointer_scale_value(program, right) ;
  
    cm_emit_temp_load_plan(fn, temp, emitter) ;
    cm_emit_plan(emitter, CMC_OP_PUSH, scale) ;
    cm_emit_plan(emitter, CMC_OP_MUL, 0) ;
    cm_emit_plan(emitter, CMC_OP_SWAP, 0) ;
    cm_emit_plan(emitter, CMC_OP_ADD, 0) ;
  } else {
    if (op == CMC_BIN_ADD && left_pointer) {
      long long scale = cm_pointer_scale_value(program, left) ;
  
      cm_emit_temp_load_plan(fn, temp, emitter) ;
      cm_emit_plan(emitter, CMC_OP_SWAP, 0) ;
      cm_emit_plan(emitter, CMC_OP_PUSH, scale) ;
      cm_emit_plan(emitter, CMC_OP_MUL, 0) ;
      cm_emit_plan(emitter, CMC_OP_ADD, 0) ;
    } else if (op == CMC_BIN_SUB && left_pointer && right_pointer) {
      long long scale = cm_pointer_scale_value(program, left) ;
  
      cm_emit_temp_load_plan(fn, temp, emitter) ;
      cm_emit_plan(emitter, CMC_OP_SWAP, 0) ;
      cm_emit_plan(emitter, CMC_OP_SUB, 0) ;
      cm_emit_plan(emitter, CMC_OP_PUSH, scale) ;
      cm_emit_plan(emitter, CMC_OP_DIV, 0) ;
    } else if (op == CMC_BIN_SUB && left_pointer) {
      long long scale = cm_pointer_scale_value(program, left) ;
  
      cm_emit_temp_load_plan(fn, temp, emitter) ;
      cm_emit_plan(emitter, CMC_OP_SWAP, 0) ;
      cm_emit_plan(emitter, CMC_OP_PUSH, scale) ;
      cm_emit_plan(emitter, CMC_OP_MUL, 0) ;
      cm_emit_plan(emitter, CMC_OP_SUB, 0) ;
    } else {
      if (op == CMC_BIN_ADD) {
        
        cm_emit_binary_generic_fragment(fn, temp, op, emitter) ;
      } else if (op == CMC_BIN_SUB) {
        
        cm_emit_binary_generic_fragment(fn, temp, op, emitter) ;
      } else {
        
        cm_emit_binary_generic_fragment(fn, temp, op, emitter) ;
      }
    }
  }
}
