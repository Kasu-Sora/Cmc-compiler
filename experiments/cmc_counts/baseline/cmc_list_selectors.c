#include "cmc_list_selectors.h"

PROOF static int _e_cmc_hd =
    cst_add_const_to_header(`HD:(A)list->A`);
PROOF static int _e_cmc_tl =
    cst_add_const_to_header(`TL:(A)list->(A)list`);
