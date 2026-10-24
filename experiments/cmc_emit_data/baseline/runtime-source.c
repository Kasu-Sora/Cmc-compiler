int cmc_emit_data(struct cm_global *global_node,
                  struct cm_string *string_node,
                  unsigned char *data, int capacity)
{
  cmc_write_zeroes(data, capacity, 0, 8);
  int globals_cursor =
      cmc_emit_globals(global_node, data, capacity, 8);
  int final_cursor =
      cmc_emit_strings(string_node, data, capacity, globals_cursor);
  return final_cursor;
}
