void cmc_copy_bytes(unsigned char *source, int length,
                    unsigned char *data, int capacity, int cursor)
    
    
    
{
  if (length == 0) {
    
    return;
  };

  int index = 0;
  

  while (index < length)
      
  {
    
    unsigned char byte = source[index];
    
    data[cursor + index] = byte;
    index = index + 1;
    
  }

  
}
