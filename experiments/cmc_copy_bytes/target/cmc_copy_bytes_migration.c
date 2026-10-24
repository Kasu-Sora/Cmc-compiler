/*@ Extern Coq
      (UCharArray::full : Z -> Z -> list Z -> Assertion)
      (UCharArray::seg : Z -> Z -> Z -> list Z -> Assertion)
      (UCharArray::undef_seg : Z -> Z -> Z -> Assertion)
      (cmc_uint8_buffer_nonnull : Z -> list Z -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_human.cmc_copy_bytes_migration_lib */

void cmc_copy_bytes(unsigned char *source, int length,
                    unsigned char *data, int capacity, int cursor)
/*@ With (prefix : list Z) (bytes : list Z)
    Require 0 <= length && Zlength(bytes) == length &&
            0 <= cursor && cursor + length <= capacity &&
            capacity <= 2147483647 &&
            cmc_uint8_buffer_nonnull(source, bytes) &&
            UCharArray::full(source, length, bytes) *
            UCharArray::seg(data, 0, cursor, prefix) *
            UCharArray::undef_seg(data, cursor, capacity)
    Ensure cmc_uint8_buffer_nonnull(source, bytes) &&
           UCharArray::full(source, length, bytes) *
           UCharArray::seg(data, 0, cursor + length, app(prefix, bytes)) *
           UCharArray::undef_seg(data, cursor + length, capacity)
*/
{
  if (length == 0) {
    return;
  };

  int index = 0;
  /*@ Inv Assert
        source == source@pre && length == length@pre &&
        data == data@pre && capacity == capacity@pre &&
        cursor == cursor@pre &&
        0 < length && Zlength(bytes) == length && source != 0 &&
        0 <= index && index <= length &&
        0 <= cursor && cursor + length <= capacity &&
        capacity <= 2147483647 &&
        UCharArray::full(source, length, bytes) *
        UCharArray::seg(data, 0, cursor + index,
                       app(prefix, sublist(0, index, bytes))) *
        UCharArray::undef_seg(data, cursor + index, capacity)
  */
  while (index < length)
  {
    unsigned char byte = source[index];
    data[cursor + index] = byte;
    index = index + 1;
  }
}
