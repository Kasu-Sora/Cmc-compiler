void cm_emit_return_epilogue_plan(struct cm_emitter *emitter)
{
  cm_emit_plan(emitter, CMC_OP_PUSH, 8);
  cm_emit_plan(emitter, CMC_OP_LOAD, 0);
  cm_emit_plan(emitter, CMC_OP_LOAD, 0);
  cm_emit_plan(emitter, CMC_OP_PUSH, 8);
  cm_emit_plan(emitter, CMC_OP_STORE, 0);
  cm_emit_plan(emitter, CMC_OP_RET, 0);
}
