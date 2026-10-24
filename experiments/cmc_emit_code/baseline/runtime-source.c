void cmc_emit_code(struct cm_program *program,
                   struct cm_emitter *emitter)
{
  struct cm_function *functions;
  functions = program->functions;
  cmc_emit_prelude(program, emitter);
  cmc_emit_functions(program, functions, 0, 11, emitter);
}
