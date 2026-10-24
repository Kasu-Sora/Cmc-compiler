/*@ Extern Coq
      (UCharArray::seg : Z -> Z -> Z -> list Z -> Assertion)
      (UCharArray::undef_seg : Z -> Z -> Z -> Assertion)
      (zeros : Z -> list Z)
*/

void cmc_write_zeroes(unsigned char *data, int capacity,
                      int cursor, int count)
/*@ With (prefix : list Z)
    Require 0 <= cursor && 0 <= count &&
            cursor + count <= capacity && capacity <= 2147483647 &&
            UCharArray::seg(data, 0, cursor, prefix) *
            UCharArray::undef_seg(data, cursor, capacity)
    Ensure UCharArray::seg(data, 0, cursor + count,
                          app(prefix, zeros(count))) *
           UCharArray::undef_seg(data, cursor + count, capacity)
*/
{
  int index = 0;
  /*@ Inv Assert
        data == data@pre && capacity == capacity@pre &&
        cursor == cursor@pre && count == count@pre &&
        0 <= index && index <= count &&
        0 <= cursor && 0 <= count &&
        cursor + count <= capacity && capacity <= 2147483647 &&
        UCharArray::seg(data, 0, cursor + index,
                       app(prefix, zeros(index))) *
        UCharArray::undef_seg(data, cursor + index, capacity)
  */
  while (index != count)
  {
    data[cursor + index] = 0;
    index = index + 1;
  }
}
