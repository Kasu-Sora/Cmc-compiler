static void cm_emit_raw(struct cm_emitter *emitter, int op,
                        long long immediate)
{
  emitter->output->ops[emitter->pc] = op;
  emitter->output->imms[emitter->pc] = immediate;
  emitter->pc = emitter->pc + 1;
}

void cm_emit(struct cm_emitter *emitter, int op, long long immediate)
{
  cm_emit_raw(emitter, op, immediate);
}

void cm_emit_normalize(struct cm_emitter *emitter, int ty)
{
  if (ty == CMC_TYPE_CHAR) {
    cm_emit(emitter, CMC_OP_PUSH, 256);
    cm_emit(emitter, CMC_OP_MOD, 0);
    cm_emit(emitter, CMC_OP_PUSH, 256);
    cm_emit(emitter, CMC_OP_ADD, 0);
    cm_emit(emitter, CMC_OP_PUSH, 256);
    cm_emit(emitter, CMC_OP_MOD, 0);
  } else {
  }
}

void cm_emit_load(struct cm_emitter *emitter, int ty)
{
  if (ty == CMC_TYPE_CHAR) {
    cm_emit(emitter, CMC_OP_LOADB, 0);
  } else {
    cm_emit(emitter, CMC_OP_LOAD, 0);
  }
}

void cm_emit_store(struct cm_emitter *emitter, int ty)
{
  if (ty == CMC_TYPE_CHAR) {
    cm_emit(emitter, CMC_OP_STOREB, 0);
  } else {
    cm_emit(emitter, CMC_OP_STORE, 0);
  }
}

void cm_emit_fp_address(struct cm_emitter *emitter, long long offset)
{
  cm_emit(emitter, CMC_OP_PUSH, 8);
  cm_emit(emitter, CMC_OP_LOAD, 0);
  cm_emit(emitter, CMC_OP_PUSH, offset);
  cm_emit(emitter, CMC_OP_ADD, 0);
}

void cm_emit_temp_store(struct cm_function *fn, int temp,
                               struct cm_emitter *emitter)
{
  long long offset = cmc_temp_offset(fn, temp);
  cm_emit_fp_address(emitter, offset);
  cm_emit(emitter, CMC_OP_STORE, 0);
}

void cm_emit_temp_load(struct cm_function *fn, int temp,
                              struct cm_emitter *emitter)
{
  long long offset = cmc_temp_offset(fn, temp);
  cm_emit_fp_address(emitter, offset);
  cm_emit(emitter, CMC_OP_LOAD, 0);
}

int cmc_binary_opcode(int op)
{
  int result;
  if (op == CMC_BIN_EQ) {
    result = CMC_OP_EQ;
  } else if (op == CMC_BIN_NE) {
    result = CMC_OP_NE;
  } else if (op == CMC_BIN_LT) {
    result = CMC_OP_LT;
  } else if (op == CMC_BIN_LE) {
    result = CMC_OP_LE;
  } else if (op == CMC_BIN_GT) {
    result = CMC_OP_GT;
  } else if (op == CMC_BIN_GE) {
    result = CMC_OP_GE;
  } else if (op == CMC_BIN_ADD) {
    result = CMC_OP_ADD;
  } else if (op == CMC_BIN_SUB) {
    result = CMC_OP_SUB;
  } else if (op == CMC_BIN_MUL) {
    result = CMC_OP_MUL;
  } else if (op == CMC_BIN_DIV) {
    result = CMC_OP_DIV;
  } else {
    result = CMC_OP_MOD;
  }
  return result;
}
