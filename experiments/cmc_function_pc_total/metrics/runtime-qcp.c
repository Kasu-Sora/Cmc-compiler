







static int cmc_function_prefix_total(
    struct cm_program *program, struct cm_function *fn,
    int index, long long target)

{
  if (fn == 0) {
    return 0;
  };
  if (index == target) {
    return 0;
  };
  
  int head_count = cmc_function_code_count(program, index, fn) ;
  
  struct cm_function *next_fn;
  next_fn = fn->next;
  int tail_count = cmc_function_prefix_total(
      program, next_fn, index + 1, target) ;
  int result = head_count + tail_count;
  return result;
}

int cmc_function_pc_total(struct cm_program *program, long long target)

{
  
  struct cm_function *fn = program->functions;
  
  int prefix = cmc_function_prefix_total(program, fn, 0, target) ;
  int result = 11 + prefix;
  return result;
}
