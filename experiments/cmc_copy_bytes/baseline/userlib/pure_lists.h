/**
 * pure_lists — the pure foundation of the array library (task s2-3a).
 *
 * Closed `:bool` list lemmas over `:(int)list` for the spatial layer
 * (s2-3b) and memcpy (s2-4): the ireplicate family, the sublist/prefix
 * family, and the ilength/num_of_int bridges. See pure_lists.c for the
 * statements and the design notes.
 */

#pragma once

#include "proof/proof.h"

/*--- num-level helpers (hidden) ---*/
PROOF thm mk_firstn_snoc_num(void);
PROOF thm mk_length_firstn_num(void);
PROOF thm mk_firstn_full_num(void);
PROOF thm mk_replicate_append_num(void);
PROOF thm mk_length_skipn_num(void);
PROOF thm mk_skipn_firstn_nth_num(void);
PROOF thm mk_replace_nth_split_num(void);

/*--- int/num bridges ---*/
PROOF thm mk_int_lt_num_of_num(void);
PROOF thm mk_int_le_num_of_num(void);
PROOF thm mk_num_of_int_suc(void);

/*--- sublist/ilength unfolds (shared) ---*/
PROOF thm mk_sublist_0_firstn(void);
PROOF thm mk_inth_nth(void);

/*--- the exported theorems ---*/
PROOF thm mk_ilength_of_num_length(void);
PROOF thm mk_ilength_ireplicate(void);
PROOF thm mk_ireplicate_empty(void);
PROOF thm mk_ireplicate_snoc(void);
PROOF thm mk_ireplicate_append2(void);
PROOF thm mk_sublist_empty(void);
PROOF thm mk_sublist_snoc(void);
PROOF thm mk_sublist_full(void);
PROOF thm mk_sublist_self_empty(void);
PROOF thm mk_sublist_cons(void);
PROOF thm mk_sublist_length(void);
PROOF thm mk_ilength_sublist(void);
PROOF thm mk_replace_inth_split(void);
