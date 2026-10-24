









int cmc_emit_strings(struct cm_string *node,
                      unsigned char *data, int capacity, int cursor)

{
  if (node == 0) {
    return cursor;
  };
  
  unsigned char *source = node->bytes;
  int length = node->length;
  struct cm_string *next = node->next;
  cmc_copy_bytes(source, length, data, capacity, cursor)
    ;
  cmc_write_byte(data, capacity,
      cursor + length, (unsigned char)0)
    ;
  int final_cursor = cmc_emit_strings(next, data, capacity,
      cursor + length + 1);
  return final_cursor;
}
