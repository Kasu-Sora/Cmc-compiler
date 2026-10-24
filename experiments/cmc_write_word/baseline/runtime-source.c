void cmc_write_word(unsigned char *data, int capacity,
                    int cursor, long long word_value)
{
  unsigned long long bits = (unsigned long long)word_value;
  unsigned char b0 = (unsigned char)(bits % 256ULL);
  unsigned char b1 = (unsigned char)((bits / 256ULL) % 256ULL);
  unsigned char b2 = (unsigned char)((bits / 65536ULL) % 256ULL);
  unsigned char b3 = (unsigned char)((bits / 16777216ULL) % 256ULL);
  unsigned char b4 = (unsigned char)((bits / 4294967296ULL) % 256ULL);
  unsigned char b5 = (unsigned char)((bits / 1099511627776ULL) % 256ULL);
  unsigned char b6 = (unsigned char)((bits / 281474976710656ULL) % 256ULL);
  unsigned char b7 = (unsigned char)((bits / 72057594037927936ULL) % 256ULL);
  cmc_write_byte(data, capacity, cursor, b0);
  cmc_write_byte(data, capacity, cursor + 1, b1);
  cmc_write_byte(data, capacity, cursor + 2, b2);
  cmc_write_byte(data, capacity, cursor + 3, b3);
  cmc_write_byte(data, capacity, cursor + 4, b4);
  cmc_write_byte(data, capacity, cursor + 5, b5);
  cmc_write_byte(data, capacity, cursor + 6, b6);
  cmc_write_byte(data, capacity, cursor + 7, b7);
}
