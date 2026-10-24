/*@ Extern Coq
      (UCharArray::seg : Z -> Z -> Z -> list Z -> Assertion)
      (UCharArray::undef_seg : Z -> Z -> Z -> Assertion)
      (tower_u8 : Z -> Z)
*/
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_human.cmc_write_word_migration_lib */

void cmc_write_byte(unsigned char *data, int capacity, int cursor, unsigned char byte)
/*@ With (prefix : list Z) (model_byte : Z)
    Require 0 <= cursor && cursor < capacity &&
            byte == model_byte && 0 <= model_byte && model_byte < 256 &&
            UCharArray::seg(data, 0, cursor, prefix) *
            UCharArray::undef_seg(data, cursor, capacity)
    Ensure UCharArray::seg(data, 0, cursor + 1,
                          app(prefix, cons(model_byte, nil))) *
           UCharArray::undef_seg(data, cursor + 1, capacity)
*/;

void cmc_write_char(unsigned char *data, int capacity,
                    int cursor, long long char_value)
/*@ With (prefix : list Z)
    Require 0 <= cursor && cursor + 1 <= capacity &&
            capacity <= 2147483647 &&
            UCharArray::seg(data, 0, cursor, prefix) *
            UCharArray::undef_seg(data, cursor, capacity)
    Ensure UCharArray::seg(data, 0, cursor + 1,
                          app(prefix, cons(tower_u8(char_value), nil))) *
           UCharArray::undef_seg(data, cursor + 1, capacity)
*/
{
  unsigned long long bits = (unsigned long long)char_value;
  unsigned char byte = (unsigned char)(bits % 256ULL);
  cmc_write_byte(data, capacity, cursor, byte)
    /*@ where prefix = prefix, model_byte = tower_u8(char_value) */;
}
