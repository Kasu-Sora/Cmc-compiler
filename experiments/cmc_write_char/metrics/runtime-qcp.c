void cmc_write_char(unsigned char *data, int capacity,
                    int cursor, long long char_value)

{
  unsigned long long bits = (unsigned long long)char_value;
  unsigned char byte = (unsigned char)(bits % 256ULL);
  cmc_write_byte(data, capacity, cursor, byte)
    ;
}

