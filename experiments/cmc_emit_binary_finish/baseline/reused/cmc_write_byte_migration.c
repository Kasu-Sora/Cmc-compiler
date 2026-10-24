/*@ Extern Coq
      (UCharArray::seg : Z -> Z -> Z -> list Z -> Assertion)
      (UCharArray::undef_seg : Z -> Z -> Z -> Assertion)
*/

void cmc_write_byte(unsigned char *data, int capacity, int cursor,
                    unsigned char byte)
/*@ With (prefix : list Z) (model_byte : Z)
    Require 0 <= cursor && cursor < capacity &&
            byte == model_byte && 0 <= model_byte && model_byte < 256 &&
            UCharArray::seg(data, 0, cursor, prefix) *
            UCharArray::undef_seg(data, cursor, capacity)
    Ensure UCharArray::seg(data, 0, cursor + 1,
                          app(prefix, cons(model_byte, nil))) *
           UCharArray::undef_seg(data, cursor + 1, capacity)
*/
{
  data[cursor] = byte;
}
