/* Tower C- source represented below:
 * int main() { int x = 2; return x + 3; }
 * This driver constructs the resolved, typed AST directly; it is not a parser.
 */
#include <stdio.h>
#include "cmc_layout_migration_abi.h"

int cmc_compile(struct cm_program *, struct cm_output *);
long long cmc_frame_size(struct cm_function *);
int cmc_stmt_temps(struct cm_stmt *);

int main(void) {
  struct cm_expr two = {.kind=CMC_EXPR_CONST, .ty=CMC_TYPE_INT, .value=2};
  struct cm_expr x = {.kind=CMC_EXPR_VAR, .op=CMC_BIND_LOCAL,
                     .ty=CMC_TYPE_INT, .value=0};
  struct cm_expr three = {.kind=CMC_EXPR_CONST, .ty=CMC_TYPE_INT, .value=3};
  struct cm_expr sum = {.kind=CMC_EXPR_BINARY, .op=CMC_BIN_ADD,
                       .ty=CMC_TYPE_INT, .a=&x, .b=&three};
  struct cm_stmt init = {.kind=CMC_STMT_INIT, .slot=0, .expr=&two};
  struct cm_stmt ret = {.kind=CMC_STMT_RETURN, .expr=&sum};
  struct cm_stmt seq = {.kind=CMC_STMT_SEQ, .a=&init, .b=&ret};
  struct cm_stmt block = {.kind=CMC_STMT_BLOCK, .a=&seq};
  struct cm_slot local = {.ty=CMC_TYPE_INT, .count=0};
  struct cm_function main_fn = {.ret_ty=CMC_TYPE_INT, .locals=&local,
                               .body=&block};
  struct cm_program program = {.functions=&main_fn, .main_id=0};
  int ops[256] = {0};
  long long imms[256] = {0};
  unsigned char data[64] = {0};
  struct cm_output output = {.ops=ops, .imms=imms, .data=data,
                            .code_capacity=256, .data_capacity=64};
  const char *names[] = {"PUSH","POP","DUP","SWAP","LOAD","STORE",
    "LOADB","STOREB","ADD","SUB","MUL","DIV","MOD","EQ","NE",
    "LT","LE","GT","GE","JMP","JZ","JNZ","CALL","RET","GETC",
    "PUTC","PUTI","HALT"};
  int rc = cmc_compile(&program, &output);
  printf("return=%d entry=%d code_length=%d data_length=%d\n", rc,
         output.entry, output.code_length, output.data_length);
  printf("frame_size=%lld temp_slots=%d\n", cmc_frame_size(&main_fn),
         cmc_stmt_temps(&block));
  if (rc != CMC_OK) return 1;
  printf("PC  instruction  opcode immediate\n");
  for (int i=0; i<output.code_length; ++i)
    printf("%02d  %-11s %2d %lld\n", i, names[ops[i]], ops[i], imms[i]);
  printf("data:");
  for (int i=0; i<output.data_length; ++i) printf(" %02x", data[i]);
  printf("\n");
  return 0;
}
