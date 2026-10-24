

struct cm_emitter {
  struct cm_output *output;
  int pc;
};















void cm_emit_binding_address(struct cm_program *program,
                             struct cm_function *fn,
                             int scope, int slot,
                             struct cm_emitter *emitter)

{
  
  if (scope == CMC_BIND_GLOBAL) {
    long long address = cmc_global_address(program->globals, slot) ;
    cm_emit_resolved(emitter, CMC_OP_PUSH, address) ;
  } else if (scope == CMC_BIND_LOCAL) {
    long long offset = cmc_local_offset(fn, slot) ;
    cm_emit_resolved_fp_address(emitter, offset) ;
  } else {
    long long offset = cmc_param_offset(fn, slot) ;
    cm_emit_resolved_fp_address(emitter, offset) ;
  }
}

void cm_emit_binding_address_plan(struct cm_program *program,
                             struct cm_function *fn,
                             int scope, int slot,
                             struct cm_emitter *emitter)

{
  
  cm_emit_binding_address(program, fn, scope, slot, emitter) ;
}
