#pragma once

#define CMC_EXPR_CONST 0
#define CMC_EXPR_STRING 1
#define CMC_EXPR_VAR 2
#define CMC_EXPR_ASSIGN 3
#define CMC_EXPR_BINARY 4
#define CMC_EXPR_UNARY 5
#define CMC_EXPR_INDEX 6
#define CMC_EXPR_MEMBER 7
#define CMC_EXPR_CALL 8
#define CMC_EXPR_SIZEOF 9
#define CMC_EXPR_GETC 10
#define CMC_EXPR_PUTC 11
#define CMC_EXPR_PUTI 12
#define CMC_EXPR_EXIT 13

#define CMC_STMT_SKIP 0
#define CMC_STMT_EXPR 1
#define CMC_STMT_DECL 2
#define CMC_STMT_INIT 3
#define CMC_STMT_SEQ 4
#define CMC_STMT_BLOCK 5
#define CMC_STMT_IF 6
#define CMC_STMT_WHILE 7
#define CMC_STMT_BREAK 8
#define CMC_STMT_CONTINUE 9
#define CMC_STMT_RETURN 10

#define CMC_BIND_GLOBAL 0
#define CMC_BIND_LOCAL 1
#define CMC_BIND_PARAM 2

#define CMC_BIN_OR 0
#define CMC_BIN_AND 1
#define CMC_BIN_EQ 2
#define CMC_BIN_NE 3
#define CMC_BIN_LT 4
#define CMC_BIN_LE 5
#define CMC_BIN_GT 6
#define CMC_BIN_GE 7
#define CMC_BIN_ADD 8
#define CMC_BIN_SUB 9
#define CMC_BIN_MUL 10
#define CMC_BIN_DIV 11
#define CMC_BIN_MOD 12

#define CMC_UN_NEG 0
#define CMC_UN_NOT 1
#define CMC_UN_DEREF 2
#define CMC_UN_ADDR 3

#define CMC_OP_PUSH 0
#define CMC_OP_POP 1
#define CMC_OP_DUP 2
#define CMC_OP_SWAP 3
#define CMC_OP_LOAD 4
#define CMC_OP_STORE 5
#define CMC_OP_LOADB 6
#define CMC_OP_STOREB 7
#define CMC_OP_ADD 8
#define CMC_OP_SUB 9
#define CMC_OP_MUL 10
#define CMC_OP_DIV 11
#define CMC_OP_MOD 12
#define CMC_OP_EQ 13
#define CMC_OP_NE 14
#define CMC_OP_LT 15
#define CMC_OP_LE 16
#define CMC_OP_GT 17
#define CMC_OP_GE 18
#define CMC_OP_JMP 19
#define CMC_OP_JZ 20
#define CMC_OP_JNZ 21
#define CMC_OP_CALL 22
#define CMC_OP_RET 23
#define CMC_OP_GETC 24
#define CMC_OP_PUTC 25
#define CMC_OP_PUTI 26
#define CMC_OP_HALT 27

#define CMC_TYPE_INT 0
#define CMC_TYPE_CHAR 1
#define CMC_TYPE_STRUCT(id) (2 + (id))
#define CMC_TYPE_POINTER(ty) ((ty) + 1024)

#define CMC_OK 0
#define CMC_CAPACITY 1

struct cm_arg;

struct cm_expr {
  int kind;
  int op;
  int ty;
  long long value;
  struct cm_expr *a;
  struct cm_expr *b;
#ifdef CSTAR_VERIFY
  void *args;
#else
  struct cm_arg *args;
#endif
};

struct cm_arg {
  struct cm_expr *expr;
  struct cm_arg *next;
};

struct cm_stmt {
  int kind;
  int slot;
  struct cm_expr *expr;
  struct cm_stmt *a;
  struct cm_stmt *b;
};

struct cm_slot {
  int ty;
  int count;
  struct cm_slot *next;
};

struct cm_member {
  int ty;
  int count;
  struct cm_member *next;
};

struct cm_struct {
  struct cm_member *members;
  struct cm_struct *next;
};

struct cm_global {
  int ty;
  int count;
  int has_init;
  long long init;
  struct cm_global *next;
};

struct cm_string {
  unsigned char *bytes;
  int length;
  struct cm_string *next;
};

struct cm_function {
  int ret_ty;
  struct cm_slot *params;
  struct cm_slot *locals;
  struct cm_stmt *body;
  struct cm_function *next;
};

struct cm_program {
  struct cm_struct *structs;
  struct cm_global *globals;
  struct cm_string *strings;
  struct cm_function *functions;
  int main_id;
};

struct cm_output {
  int *ops;
  long long *imms;
  unsigned char *data;
  int code_capacity;
  int data_capacity;
  int code_length;
  int data_length;
  int entry;
};
