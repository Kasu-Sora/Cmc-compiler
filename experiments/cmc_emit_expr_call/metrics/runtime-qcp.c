
struct cm_emitter { struct cm_output *output; int pc; };


















static void cm_emit_args_reload_plan(struct cm_function *fn, int slot,
                                     int temp_limit, struct cm_arg *arg,
                                     struct cm_emitter *emitter)

{
  if (arg == 0) {

 
    return;
  } else {
  }

 

 

 
  cm_emit_temp_load_plan(fn, slot, emitter) ;
  cm_emit_args_reload_plan(fn, slot + 1, temp_limit,
                           arg->next, emitter) ;
 

}

static void cm_emit_args_store_plan(struct cm_program *program, int fid,
                                    struct cm_function *fn, int pc,
                                    int slot, int scratch, int temp_limit,
                                    struct cm_arg *arg,
                                    struct cm_emitter *emitter)

{
  if (arg == 0) {

 
    return;
  } else {
  }

 

 
  int head_count =
      cm_expr_rvalue_count_context(program, fid, fn, arg->expr) ;

 

 
  cm_emit_expr(program, fid, fn, pc, scratch, temp_limit,
               arg->expr, 0, emitter) ;
  cm_emit_temp_store_plan(fn, slot, emitter) ;
  cm_emit_args_store_plan(program, fid, fn,
      pc + head_count + 5, slot + 1, scratch, temp_limit,
      arg->next, emitter) ;
 

}

void cm_emit_call_expr(struct cm_program *program, int fid,
                       struct cm_function *fn, int pc, int temp,
                       int temp_limit, struct cm_expr *expr,
                       int lvalue, struct cm_emitter *emitter)

{

 

 

 
  if (!lvalue) {

 

 

 

 
    int count = cm_args_length(expr->args) ;

 

 
    cm_emit_args_store_plan(program, fid, fn, pc, temp,
        temp + count, temp_limit, expr->args, emitter) ;
    cm_emit_args_reload_plan(fn, temp, temp_limit,
        expr->args, emitter) ;
    cm_emit_call_plan(emitter, expr->value) ;
 

 

  } else {
  }

 
}
