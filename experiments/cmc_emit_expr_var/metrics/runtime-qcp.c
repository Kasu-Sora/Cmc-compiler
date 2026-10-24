

struct cm_emitter {
  struct cm_output *output;
  int pc;
};












void cm_emit_var_expr(struct cm_program *program, int fid,
                      struct cm_function *fn, int pc, int temp,
                      struct cm_expr *expr, int lvalue,
                      struct cm_emitter *emitter)

{
  
  
  int array = cmc_binding_array(program, fid, fn,
                                expr->op, (int)expr->value) ;
  
  if (!lvalue) {
    if (array == 0) {
      
      cm_emit_binding_address_plan(program, fn, expr->op,
                                   (int)expr->value, emitter) ;
      cm_emit_load_plan(emitter, expr->ty) ;
    } else {
      
      cm_emit_binding_address_plan(program, fn, expr->op,
                                   (int)expr->value, emitter) ;
    }
  } else {
      
    cm_emit_binding_address_plan(program, fn, expr->op,
                                 (int)expr->value, emitter) ;
  }
}
