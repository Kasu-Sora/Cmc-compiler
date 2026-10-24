int cmc_compile(struct cm_program *program, struct cm_output *output)
{
  int code_length = cmc_model_code_length(program);
  int data_length = cmc_model_data_length(program);
  output->code_length = code_length;
  output->data_length = data_length;
  output->entry = -1;
  if (code_length > output->code_capacity) {
    return CMC_CAPACITY;
  }
  if (data_length > output->data_capacity) {
    return CMC_CAPACITY;
  }
  struct cm_emitter emitter;
  emitter.output = output;
  emitter.pc = 0;
  cmc_emit_code(program, &emitter);
  cmc_patch_resolved_calls(program, &emitter);
  struct cm_global *globals = program->globals;
  struct cm_string *strings = program->strings;
  unsigned char *data = output->data;
  int output_data_capacity = output->data_capacity;
  int emitted_data = cmc_emit_data(
      globals, strings, data, output_data_capacity);
  output->entry = 0;
  return CMC_OK;
}
