
struct cm_emitter {
  struct cm_output *output;
  int pc;
};














void cm_emit_leaf_expr(struct cm_program *program, int fid,
                       struct cm_function *fn, int pc, int temp,
                       struct cm_expr *expr, int lvalue,
                       struct cm_emitter *emitter)

{
 
  if (expr->kind == CMC_EXPR_CONST) {
 
 
    cm_emit_const_expr(program, fid, fn, pc, temp, expr, lvalue, emitter) ;
  } else if (expr->kind == CMC_EXPR_STRING) {
 
 
    cm_emit_string_expr(program, fid, fn, pc, temp, expr, lvalue, emitter) ;
  } else if (expr->kind == CMC_EXPR_SIZEOF) {
 
 
    cm_emit_sizeof_expr(program, fid, fn, pc, temp, expr, lvalue, emitter) ;
  } else {
 
 
    cm_emit_getc_expr(program, fid, fn, pc, temp, expr, lvalue, emitter) ;
  }
}
