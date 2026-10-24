static void cmc_patch_code_arrays(
    struct cm_program *program, int *ops, long long *imms, int length)
{
  if (length == 0) {
    return;
  };
  int op = *ops;
  long long immediate = *imms;
  int *remaining_ops = ops + 1;
  long long *remaining_imms = imms + 1;
  int remaining_length = length - 1;
  if (op == CMC_OP_CALL) {
    int pc = cmc_function_pc_total(program, immediate);
    *imms = pc;
    cmc_patch_code_arrays(
        program, remaining_ops, remaining_imms, remaining_length);
  } else {
    cmc_patch_code_arrays(
        program, remaining_ops, remaining_imms, remaining_length);
  };
}

void cmc_patch_resolved_calls(struct cm_program *program,
                              struct cm_emitter *emitter)
{
  struct cm_output *output = emitter->output;
  int length = emitter->pc;
  int *ops = output->ops;
  long long *imms = output->imms;
  cmc_patch_code_arrays(program, ops, imms, length);
}
