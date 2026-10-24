void cm_emit_plan(struct cm_emitter *emitter, int op,
                  long long immediate)
{
  cm_emit_resolved(emitter, op, immediate);
}

void cm_emit_call_plan(struct cm_emitter *emitter, int function_id)
{
  cm_emit_resolved_call(emitter, function_id);
}

void cm_emit_normalize_plan(struct cm_emitter *emitter, int ty)
{
  cm_emit_resolved_normalize(emitter, ty);
}

void cm_emit_load_plan(struct cm_emitter *emitter, int ty)
{
  cm_emit_resolved_load(emitter, ty);
}

void cm_emit_store_plan(struct cm_emitter *emitter, int ty)
{
  cm_emit_resolved_store(emitter, ty);
}

void cm_emit_fp_address_plan(struct cm_emitter *emitter,
                             long long offset)
{
  cm_emit_resolved_fp_address(emitter, offset);
}

void cm_emit_temp_store_plan(struct cm_function *fn, int temp,
                             struct cm_emitter *emitter)
{
  cm_emit_resolved_temp_store(fn, temp, emitter);
}

void cm_emit_temp_load_plan(struct cm_function *fn, int temp,
                            struct cm_emitter *emitter)
{
  cm_emit_resolved_temp_load(fn, temp, emitter);
}
