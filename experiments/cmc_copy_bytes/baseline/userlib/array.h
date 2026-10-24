/**
 * array — the SPATIAL half of the array library (task s2-3b).
 *
 * Type-generic entailment lemmas over the built-in array predicates,
 * consuming the pure list layer (pure_lists.c) unchanged. Clients
 * instantiate the element type (`Tchar`, `Tint`, `Tptr`, ...) at the
 * call site. See array.c for the statements and the design notes.
 *
 * Two families:
 *
 *   Random access (read/modify at an index):
 *     mk_open_cell  : array_at p ty n vs |--
 *                     left flank ** cell at i ** right flank
 *     mk_close_cell : the three pieces back (cell rewritten) |--
 *                     array_at p ty n (replace_inth i v vs)
 *
 *   Left-to-right fill cursor (initialization loops):
 *     mk_begin_fill    : undef array |-- empty prefix ** undef suffix
 *     mk_open_fill_cell: peel the first undef cell at the cursor
 *     mk_close_fill_cell: append the just-written value to the prefix
 *     mk_finish_fill   : cursor at n collapses to the plain array
 *
 * Every export is a closed file-scope proof; the library contains no
 * inline [[cst::proof]] blocks tied to any client.
 */

#pragma once

#include "proof/proof.h"

/*--- random access ---*/
PROOF thm mk_open_cell(void);
PROOF thm mk_close_cell(void);

/*--- left-to-right fill cursor ---*/
PROOF thm mk_begin_fill(void);
PROOF thm mk_open_fill_cell(void);
PROOF thm mk_close_fill_cell(void);
PROOF thm mk_finish_fill(void);
