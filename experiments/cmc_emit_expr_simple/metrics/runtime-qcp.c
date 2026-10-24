
struct cm_emitter {
  struct cm_output *output;
  int pc;
};









void cm_emit_simple_expr(struct cm_program *program, int fid,
                         struct cm_function *fn, int pc, int temp,
                         struct cm_expr *expr, int lvalue,
                         struct cm_emitter *emitter)

{
 
  if (expr->kind == CMC_EXPR_VAR) {
 
 
    cm_emit_var_expr(program, fid, fn, pc, temp, expr, lvalue, emitter) ;
  } else {
 
 
    cm_emit_leaf_expr(program, fid, fn, pc, temp, expr, lvalue, emitter) ;
  }
}
