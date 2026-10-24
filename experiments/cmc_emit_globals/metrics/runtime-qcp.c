













int cmc_emit_globals(struct cm_global *node,
                      unsigned char *data, int capacity, int cursor)

{
  if (node == 0) {
    return cursor;
  };
  
  int type_code = node->ty;
  int count = node->count;
  int has_init = node->has_init;
  long long init_value = node->init;
  struct cm_global *next = node->next;
  long long size64 = cmc_code_slot_size(type_code, count);
  int size = (int)size64;
  if (has_init) {
    if (type_code == CMC_TYPE_CHAR) {
      cmc_write_char(data, capacity, cursor, init_value)
        ;
    } else {
      cmc_write_word(data, capacity, cursor, init_value)
        ;
    }
  } else {
    cmc_write_zeroes(data, capacity, cursor, size)
      ;
  }
  
  int final_cursor =
      cmc_emit_globals(next, data, capacity, cursor + size)
        ;
  return final_cursor;
}
