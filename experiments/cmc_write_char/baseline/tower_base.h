#pragma once

#include "proof/proof.h"

PROOF thm get_tower_signed64_def(void);
PROOF thm get_tower_byte_value_def(void);
PROOF thm get_tower_wrap64_def(void);
PROOF thm get_tower_u8_def(void);
PROOF thm get_tower_status_def(void);
PROOF thm get_tower_bool_def(void);
PROOF thm get_tower_add_def(void);
PROOF thm get_tower_sub_def(void);
PROOF thm get_tower_mul_def(void);
PROOF thm get_tower_neg_def(void);
PROOF thm get_tower_tquot_def(void);
PROOF thm get_tower_trem_def(void);
PROOF thm get_tower_div_def(void);
PROOF thm get_tower_mod_def(void);

PROOF thm get_tower_wrap64_range(void);
PROOF thm get_tower_wrap64_idempotent(void);
PROOF thm get_tower_wrap64_fixed(void);
PROOF thm get_tower_wrap64_u8(void);
PROOF thm get_tower_u8_wrap64(void);
PROOF thm get_tower_u8_range(void);
PROOF thm get_tower_u8_idempotent(void);
PROOF thm get_tower_u8_fixed(void);
PROOF thm get_tower_status_range(void);
PROOF thm get_tower_div_min_neg1(void);
PROOF thm get_tower_mod_min_neg1(void);
PROOF thm get_tower_bool_cases(void);

PROOF thm get_tower_encode_byte_def(void);
PROOF thm get_tower_decode8_def(void);
PROOF thm get_tower_word_bytes_def(void);
PROOF thm get_tower_decode_encode(void);

PROOF thm get_tower_addr_valid_def(void);
PROOF thm get_tower_word_valid_def(void);
PROOF thm get_tower_zero_mem_def(void);
PROOF thm get_tower_getb_def(void);
PROOF thm get_tower_setb_def(void);
PROOF thm get_tower_getw_def(void);
PROOF thm get_tower_setw_def(void);
PROOF thm get_tower_getb_setb_same(void);
PROOF thm get_tower_getb_setb_other(void);
PROOF thm get_tower_getw_setw(void);

PROOF thm get_tower_digit_def(void);
PROOF thm get_tower_digits_def(void);
PROOF thm get_tower_decimal_def(void);
PROOF thm get_tower_decimal_zero(void);
PROOF thm get_tower_decimal_neg1(void);
PROOF thm get_tower_decimal_255(void);
