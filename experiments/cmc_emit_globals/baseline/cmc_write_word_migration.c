/*@ Extern Coq
      (UCharArray::seg : Z -> Z -> Z -> list Z -> Assertion)
      (UCharArray::undef_seg : Z -> Z -> Z -> Assertion)
      (tower_encode_byte : Z -> Z -> Z)
      (tower_word_bytes : Z -> list Z)
*/
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_human.cmc_write_word_migration_lib */

/* Modular dependency: the exact contract verified in cmc_write_byte_migration.c. */
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

void cmc_write_word(unsigned char *data, int capacity,
                    int cursor, long long word_value)
/*@ With (prefix : list Z)
    Require 0 <= cursor && cursor + 8 <= capacity &&
            capacity <= 2147483647 &&
            UCharArray::seg(data, 0, cursor, prefix) *
            UCharArray::undef_seg(data, cursor, capacity)
    Ensure UCharArray::seg(data, 0, cursor + 8,
                          app(prefix, tower_word_bytes(word_value))) *
           UCharArray::undef_seg(data, cursor + 8, capacity)
*/
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
  cmc_write_byte(data, capacity, cursor, b0)
    /*@ where prefix = prefix,
              model_byte = tower_encode_byte(word_value, 0) */;
  cmc_write_byte(data, capacity, cursor + 1, b1)
    /*@ where prefix = app(prefix, cons(tower_encode_byte(word_value, 0), nil)),
              model_byte = tower_encode_byte(word_value, 1) */;
  /*@ Assert exists bits_value, bits == bits_value &&
             b0 == tower_encode_byte(word_value, 0) &&
             b1 == tower_encode_byte(word_value, 1) &&
             b2 == tower_encode_byte(word_value, 2) &&
             b3 == tower_encode_byte(word_value, 3) &&
             b4 == tower_encode_byte(word_value, 4) &&
             b5 == tower_encode_byte(word_value, 5) &&
             b6 == tower_encode_byte(word_value, 6) &&
             b7 == tower_encode_byte(word_value, 7) &&
             data == data@pre && capacity == capacity@pre &&
             cursor == cursor@pre && word_value == word_value@pre &&
             0 <= cursor && cursor + 8 <= capacity && capacity <= 2147483647 &&
             UCharArray::seg(data, 0, cursor + 2, app(app(prefix, cons(tower_encode_byte(word_value, 0), nil)), cons(tower_encode_byte(word_value, 1), nil))) *
             UCharArray::undef_seg(data, cursor + 2, capacity)
  */
  cmc_write_byte(data, capacity, cursor + 2, b2)
    /*@ where prefix = app(app(prefix, cons(tower_encode_byte(word_value, 0), nil)), cons(tower_encode_byte(word_value, 1), nil)),
              model_byte = tower_encode_byte(word_value, 2) */;
  /*@ Assert exists bits_value, bits == bits_value &&
             b0 == tower_encode_byte(word_value, 0) &&
             b1 == tower_encode_byte(word_value, 1) &&
             b2 == tower_encode_byte(word_value, 2) &&
             b3 == tower_encode_byte(word_value, 3) &&
             b4 == tower_encode_byte(word_value, 4) &&
             b5 == tower_encode_byte(word_value, 5) &&
             b6 == tower_encode_byte(word_value, 6) &&
             b7 == tower_encode_byte(word_value, 7) &&
             data == data@pre && capacity == capacity@pre &&
             cursor == cursor@pre && word_value == word_value@pre &&
             0 <= cursor && cursor + 8 <= capacity && capacity <= 2147483647 &&
             UCharArray::seg(data, 0, cursor + 3, app(app(app(prefix, cons(tower_encode_byte(word_value, 0), nil)), cons(tower_encode_byte(word_value, 1), nil)), cons(tower_encode_byte(word_value, 2), nil))) *
             UCharArray::undef_seg(data, cursor + 3, capacity)
  */
  cmc_write_byte(data, capacity, cursor + 3, b3)
    /*@ where prefix = app(app(app(prefix, cons(tower_encode_byte(word_value, 0), nil)), cons(tower_encode_byte(word_value, 1), nil)), cons(tower_encode_byte(word_value, 2), nil)),
              model_byte = tower_encode_byte(word_value, 3) */;
  /*@ Assert exists bits_value, bits == bits_value &&
             b0 == tower_encode_byte(word_value, 0) &&
             b1 == tower_encode_byte(word_value, 1) &&
             b2 == tower_encode_byte(word_value, 2) &&
             b3 == tower_encode_byte(word_value, 3) &&
             b4 == tower_encode_byte(word_value, 4) &&
             b5 == tower_encode_byte(word_value, 5) &&
             b6 == tower_encode_byte(word_value, 6) &&
             b7 == tower_encode_byte(word_value, 7) &&
             data == data@pre && capacity == capacity@pre &&
             cursor == cursor@pre && word_value == word_value@pre &&
             0 <= cursor && cursor + 8 <= capacity && capacity <= 2147483647 &&
             UCharArray::seg(data, 0, cursor + 4, app(app(app(app(prefix, cons(tower_encode_byte(word_value, 0), nil)), cons(tower_encode_byte(word_value, 1), nil)), cons(tower_encode_byte(word_value, 2), nil)), cons(tower_encode_byte(word_value, 3), nil))) *
             UCharArray::undef_seg(data, cursor + 4, capacity)
  */
  cmc_write_byte(data, capacity, cursor + 4, b4)
    /*@ where prefix = app(app(app(app(prefix, cons(tower_encode_byte(word_value, 0), nil)), cons(tower_encode_byte(word_value, 1), nil)), cons(tower_encode_byte(word_value, 2), nil)), cons(tower_encode_byte(word_value, 3), nil)),
              model_byte = tower_encode_byte(word_value, 4) */;
  /*@ Assert exists bits_value, bits == bits_value &&
             b0 == tower_encode_byte(word_value, 0) &&
             b1 == tower_encode_byte(word_value, 1) &&
             b2 == tower_encode_byte(word_value, 2) &&
             b3 == tower_encode_byte(word_value, 3) &&
             b4 == tower_encode_byte(word_value, 4) &&
             b5 == tower_encode_byte(word_value, 5) &&
             b6 == tower_encode_byte(word_value, 6) &&
             b7 == tower_encode_byte(word_value, 7) &&
             data == data@pre && capacity == capacity@pre &&
             cursor == cursor@pre && word_value == word_value@pre &&
             0 <= cursor && cursor + 8 <= capacity && capacity <= 2147483647 &&
             UCharArray::seg(data, 0, cursor + 5, app(app(app(app(app(prefix, cons(tower_encode_byte(word_value, 0), nil)), cons(tower_encode_byte(word_value, 1), nil)), cons(tower_encode_byte(word_value, 2), nil)), cons(tower_encode_byte(word_value, 3), nil)), cons(tower_encode_byte(word_value, 4), nil))) *
             UCharArray::undef_seg(data, cursor + 5, capacity)
  */
  cmc_write_byte(data, capacity, cursor + 5, b5)
    /*@ where prefix = app(app(app(app(app(prefix, cons(tower_encode_byte(word_value, 0), nil)), cons(tower_encode_byte(word_value, 1), nil)), cons(tower_encode_byte(word_value, 2), nil)), cons(tower_encode_byte(word_value, 3), nil)), cons(tower_encode_byte(word_value, 4), nil)),
              model_byte = tower_encode_byte(word_value, 5) */;
  /*@ Assert exists bits_value, bits == bits_value &&
             b0 == tower_encode_byte(word_value, 0) &&
             b1 == tower_encode_byte(word_value, 1) &&
             b2 == tower_encode_byte(word_value, 2) &&
             b3 == tower_encode_byte(word_value, 3) &&
             b4 == tower_encode_byte(word_value, 4) &&
             b5 == tower_encode_byte(word_value, 5) &&
             b6 == tower_encode_byte(word_value, 6) &&
             b7 == tower_encode_byte(word_value, 7) &&
             data == data@pre && capacity == capacity@pre &&
             cursor == cursor@pre && word_value == word_value@pre &&
             0 <= cursor && cursor + 8 <= capacity && capacity <= 2147483647 &&
             UCharArray::seg(data, 0, cursor + 6, app(app(app(app(app(app(prefix, cons(tower_encode_byte(word_value, 0), nil)), cons(tower_encode_byte(word_value, 1), nil)), cons(tower_encode_byte(word_value, 2), nil)), cons(tower_encode_byte(word_value, 3), nil)), cons(tower_encode_byte(word_value, 4), nil)), cons(tower_encode_byte(word_value, 5), nil))) *
             UCharArray::undef_seg(data, cursor + 6, capacity)
  */
  cmc_write_byte(data, capacity, cursor + 6, b6)
    /*@ where prefix = app(app(app(app(app(app(prefix, cons(tower_encode_byte(word_value, 0), nil)), cons(tower_encode_byte(word_value, 1), nil)), cons(tower_encode_byte(word_value, 2), nil)), cons(tower_encode_byte(word_value, 3), nil)), cons(tower_encode_byte(word_value, 4), nil)), cons(tower_encode_byte(word_value, 5), nil)),
              model_byte = tower_encode_byte(word_value, 6) */;
  /*@ Assert exists bits_value, bits == bits_value &&
             b0 == tower_encode_byte(word_value, 0) &&
             b1 == tower_encode_byte(word_value, 1) &&
             b2 == tower_encode_byte(word_value, 2) &&
             b3 == tower_encode_byte(word_value, 3) &&
             b4 == tower_encode_byte(word_value, 4) &&
             b5 == tower_encode_byte(word_value, 5) &&
             b6 == tower_encode_byte(word_value, 6) &&
             b7 == tower_encode_byte(word_value, 7) &&
             data == data@pre && capacity == capacity@pre &&
             cursor == cursor@pre && word_value == word_value@pre &&
             0 <= cursor && cursor + 8 <= capacity && capacity <= 2147483647 &&
             UCharArray::seg(data, 0, cursor + 7, app(app(app(app(app(app(app(prefix, cons(tower_encode_byte(word_value, 0), nil)), cons(tower_encode_byte(word_value, 1), nil)), cons(tower_encode_byte(word_value, 2), nil)), cons(tower_encode_byte(word_value, 3), nil)), cons(tower_encode_byte(word_value, 4), nil)), cons(tower_encode_byte(word_value, 5), nil)), cons(tower_encode_byte(word_value, 6), nil))) *
             UCharArray::undef_seg(data, cursor + 7, capacity)
  */
  cmc_write_byte(data, capacity, cursor + 7, b7)
    /*@ where prefix = app(app(app(app(app(app(app(prefix, cons(tower_encode_byte(word_value, 0), nil)), cons(tower_encode_byte(word_value, 1), nil)), cons(tower_encode_byte(word_value, 2), nil)), cons(tower_encode_byte(word_value, 3), nil)), cons(tower_encode_byte(word_value, 4), nil)), cons(tower_encode_byte(word_value, 5), nil)), cons(tower_encode_byte(word_value, 6), nil)),
              model_byte = tower_encode_byte(word_value, 7) */;
}
