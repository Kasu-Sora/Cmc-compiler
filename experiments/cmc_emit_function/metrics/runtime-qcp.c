
struct cm_emitter { struct cm_output *output; int pc; };



























static void cmc_emit_param_stores_from(
    struct cm_slot *param, int slot, long long offset,
    struct cm_emitter *emitter)

{
  if (param == 0) {
    return;
  } else {
  
  }
  long long member_size = cmc_code_slot_size(param->ty, param->count);
  
  struct cm_slot *next = param->next;
  
  
  cmc_emit_param_stores_from(next, slot + 1,
                             offset + member_size, emitter) ;
  cm_emit_normalize_plan(emitter, param->ty) ;
  cm_emit_fp_address_plan(emitter, offset) ;
  cm_emit_store_plan(emitter, param->ty) ;
  
  
}

static void cmc_emit_prologue(
    struct cm_function *fn, int fid, struct cm_emitter *emitter)

{
  
  long long frame_size = cmc_frame_size(fn) ;
  
  
  cm_emit_plan(emitter, CMC_OP_PUSH, 8) ;
  cm_emit_plan(emitter, CMC_OP_LOAD, 0) ;
  cm_emit_plan(emitter, CMC_OP_DUP, 0) ;
  cm_emit_plan(emitter, CMC_OP_PUSH, frame_size) ;
  cm_emit_plan(emitter, CMC_OP_SUB, 0) ;
  cm_emit_plan(emitter, CMC_OP_STORE, 0) ;
  cm_emit_plan(emitter, CMC_OP_PUSH, 8) ;
  cm_emit_plan(emitter, CMC_OP_LOAD, 0) ;
  cm_emit_plan(emitter, CMC_OP_PUSH, frame_size) ;
  cm_emit_plan(emitter, CMC_OP_SUB, 0) ;
  cm_emit_plan(emitter, CMC_OP_DUP, 0) ;
  cm_emit_plan(emitter, CMC_OP_PUSH, 8) ;
  cm_emit_plan(emitter, CMC_OP_STORE, 0) ;
  cm_emit_plan(emitter, CMC_OP_POP, 0) ;
  
  cmc_emit_param_stores_from(fn->params, 0, 8, emitter) ;
  
  
}

void cmc_emit_function(
    struct cm_program *program, struct cm_function *fn,
    int fid, int function_pc, struct cm_emitter *emitter)

{
  int prologue_count = cmc_function_prologue_count(fn) ;
  
  int body_pc = function_pc + prologue_count;
  struct cm_stmt *body_stmt;
  
  body_stmt = fn->body;
  
  int temp_limit = cmc_stmt_temps(body_stmt) ;
  
  
  cmc_emit_prologue(fn, fid, emitter) ;
  cmc_emit_stmt(program, fid, fn, body_pc, 0, temp_limit,
                0, 0, body_stmt, emitter) ;
  
  cm_emit_plan(emitter, CMC_OP_PUSH, 0) ;
  cm_emit_return_epilogue_plan(emitter) ;
  
}
