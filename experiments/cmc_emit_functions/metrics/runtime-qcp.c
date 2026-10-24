
struct cm_emitter { struct cm_output *output; int pc; };









void cmc_emit_functions(
    struct cm_program *program, struct cm_function *fn,
    int fid, int function_pc, struct cm_emitter *emitter)

{
  if (fn == 0) {
    return;
  };
  
  
  int head_count = cmc_function_code_count(program, fid, fn) ;
  
  
  cmc_emit_function(program, fn, fid, function_pc, emitter) ;
  struct cm_function *next_fn;
  
  next_fn = fn->next;
  
  int next_pc = function_pc + head_count;
  cmc_emit_functions(program, next_fn, fid + 1, next_pc, emitter) ;
  
}
