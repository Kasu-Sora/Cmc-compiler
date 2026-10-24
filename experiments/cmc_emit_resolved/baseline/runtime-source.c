void cm_emit_resolved(struct cm_emitter *emitter, int op,
                      long long immediate)
{
  cm_emit(emitter, op, immediate);
}

void cm_emit_resolved_call(struct cm_emitter *emitter, int function_id)
{
  cm_emit(emitter, CMC_OP_CALL, function_id);
}

void cm_emit_resolved_normalize(struct cm_emitter *emitter, int ty)
{
  cm_emit_normalize(emitter, ty);
}

void cm_emit_resolved_load(struct cm_emitter *emitter, int ty)
{
  cm_emit_load(emitter, ty);
}

void cm_emit_resolved_store(struct cm_emitter *emitter, int ty)
{
  cm_emit_store(emitter, ty);
}

void cm_emit_resolved_fp_address(struct cm_emitter *emitter,
                                 long long offset)
{
  cm_emit_fp_address(emitter, offset);
}

void cm_emit_resolved_temp_store(struct cm_function *fn, int temp,
                                 struct cm_emitter *emitter)
{
  cm_emit_temp_store(fn, temp, emitter);
}

void cm_emit_resolved_temp_load(struct cm_function *fn, int temp,
                                struct cm_emitter *emitter)
{
  cm_emit_temp_load(fn, temp, emitter);
}
