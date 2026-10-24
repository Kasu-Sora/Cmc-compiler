

void cmc_write_zeroes(unsigned char *data, int capacity,
                      int cursor, int count)

{
  int index = 0;
  
  while (index != count)
  {
    data[cursor + index] = 0;
    index = index + 1;
  }
}

