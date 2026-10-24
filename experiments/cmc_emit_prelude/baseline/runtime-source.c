void cmc_emit_prelude(struct cm_program *program,
                      struct cm_emitter *emitter)
{
  int main_id;
  main_id = program->main_id;
  cm_emit_plan(emitter, CMC_OP_PUSH, 1048576);
  cm_emit_plan(emitter, CMC_OP_PUSH, 8);
  cm_emit_plan(emitter, CMC_OP_STORE, 0);
  cm_emit_call_plan(emitter, main_id);
  cm_emit_plan(emitter, CMC_OP_PUSH, 256);
  cm_emit_plan(emitter, CMC_OP_MOD, 0);
  cm_emit_plan(emitter, CMC_OP_PUSH, 256);
  cm_emit_plan(emitter, CMC_OP_ADD, 0);
  cm_emit_plan(emitter, CMC_OP_PUSH, 256);
  cm_emit_plan(emitter, CMC_OP_MOD, 0);
  cm_emit_plan(emitter, CMC_OP_HALT, 0);
}
