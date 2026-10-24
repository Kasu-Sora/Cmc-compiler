/* s2-3b — array: the SPATIAL half of the array library.
 *
 * Spec (task s2-3b): a type-generic family of closed entailment lemmas
 * over the built-in array predicates (array_at / undef_array_at /
 * data_at / undef_data_at), consuming the s2-3a pure layer
 * (pure_lists.c) unchanged. Clients instantiate the element type; every
 * export is a closed file-scope proof — no inline [[cst::proof]] blocks
 * tied to any client.
 *
 * The two families (all lemmas are `!p ty ... .` — generic in the cell
 * type, which the annotation layer cannot spell but HOL handles fine):
 *
 * RANDOM ACCESS (read/modify at an index):
 *   open_cell : array_at p ty n vs |--
 *       array_at p ty i (sublist 0i i vs) **
 *       data_at (p + i * sizeof ty) ty (inth i vs) **
 *       array_at (p + (i + 1i) * sizeof ty) ty (n - (i + 1i))
 *                (sublist (i + 1i) n vs)
 *     (0i <= i, i < n, ilength vs == n)
 *   close_cell : the same three pieces with the cell rewritten to v |--
 *       array_at p ty n (replace_inth i v vs)
 *     (same side conditions)
 *
 *   The flank shapes are the array_at_divide convention: the left flank
 *   stays on the base address, the right flank is REBASED to
 *   p + (i + 1i) * sizeof ty and its list is the window sublist
 *   (i + 1i) n vs. open_cell's right side IS close_cell's left side.
 *
 * FILL CURSOR (initialization loops; generalizes the s2-2 invariant
 *   zeroed arr iv ** undef_char_array (arr + iv * sizeof Tchar) (n - iv)):
 *   begin_fill : undef_array_at p ty n |--
 *       array_at p ty 0i [] ** undef_array_at (p + 0i * sizeof ty) ty (n - 0i)
 *   open_fill_cell : undef_array_at (p + iv * sizeof ty) ty (n - iv) |--
 *       undef_data_at (p + iv * sizeof ty) ty **
 *       undef_array_at (p + (iv + 1i) * sizeof ty) ty (n - (iv + 1i))
 *     (n - iv >= 1i)
 *   close_fill_cell : array_at p ty iv pl ** data_at (p + iv * sizeof ty) ty v |--
 *       array_at p ty (iv + 1i) (pl ++ [v])
 *   finish_fill : iv == n ==>
 *       array_at p ty iv pl ** undef_array_at (p + iv * sizeof ty) ty (n - iv) |--
 *       array_at p ty n pl
 *
 * Design notes:
 *   - open_cell peels the MIDDLE cell by array_at_divide at i (the left
 *     flank plus the rest), then array_at_split_first on the rest — the
 *     rest's list is put in `v :: l` form by the pure windowed-head split
 *     mk_sublist_cons. The address/length leftovers are ring identities
 *     over the opaque atom `sizeof ty`, spelled with explicit parens
 *     (`(p + i * sizeof ty) + sizeof ty` is the left-nested form the
 *     stdlib instantiation produces).
 *   - close_cell merges via array_at_merge_last (no side condition),
 *     frames the right flank with hsep_cancel_right, and reassembles with
 *     array_at_divide2's reverse — its two length premises come from
 *     mk_ilength_sublist and the new pure mk_sublist_length. The final
 *     list rewrite (concat of the three pieces == replace_inth i v vs) is
 *     built as ONE targeted rewrite on the exact RHS term
 *     (apply_conversion), never as a whole-theorem conv: the flank window
 *     `sublist (i + 1i) n vs` occurs on BOTH sides, so an unfettered
 *     rewrite would corrupt the LHS and break the ccl match.
 *   - The fill family is the s2-2 clear family generalized from Tchar to
 *     a type variable: begin_fill is array_at_zero + ring + the sep unit
 *     (hsep_hemp_left), open_fill_cell is undef_array_at_split_first +
 *     rings (the old mk_undef_suffix_split_first), close_fill_cell is
 *     array_at_merge_last verbatim, finish_fill rewrites the cursor to n
 *     (iv == n), zeroes the suffix (undef_array_at_zero), and collapses
 *     with hsep_hemp_right.
 *   - No new HOL constants, so no cst_add_const_to_header calls.
 *   - The six exports are ALSO bound as top-level `PROOF thm` variables
 *     (open_cell, close_cell, begin_fill, ...). File-scope function
 *     bodies execute LAZILY — only when a caller invokes them — so the
 *     named bindings are what make this file's own verification actually
 *     run and check every proof (a broken lemma fails the standalone
 *     audit at load, not just at its first client). The bindings are NOT
 *     declared in array.h: declaring a `PROOF thm` in a header makes
 *     clients emit a duplicate symbol at link time.
 *   - Audit: file's last line shows verification_conditions [] and
 *     axioms []; every export's concl is rendered in this file's own
 *     gl scope (the intended lhs |-- rhs, with genuinely different
 *     sides); open_cell/close_cell were mutation-checked (flipping the
 *     entailment / corrupting the RHS makes the load-time binding throw
 *     `Theorem conclusion does not match the goal`).
 */

#include "proof/proof.h"

#include "userlib/renderers.h"

#include "userlib/proof.h"
#require "userlib/proof.c"

#include "userlib/pure_lists.h"
#require "userlib/pure_lists.c"

#include "userlib/array.h"

/*============================== random access ==============================*/

/* !p ty n vs i. 0i <= i ==> i < n ==> ilength vs == n ==>
 *   (array_at p ty n vs |--
 *      array_at p ty i (sublist 0i i vs) **
 *      data_at (p + i * sizeof ty) ty (inth i vs) **
 *      array_at (p + (i + 1i) * sizeof ty) ty (n - (i + 1i))
 *               (sublist (i + 1i) n vs)) */
PROOF thm mk_open_cell(void) {
  thm h1 = assume_rule(`0i <= (i:int)`);
  thm h2 = assume_rule(`(i:int) < n`);
  thm h3 = assume_rule(`ilength (vs:(int)list) == n`);
  thm i_le_n = match_mp_rule(int_arith_rule(`(i:int) < n ==> i <= n`), h2);
  thm n_le_il = match_mp_rule(int_arith_rule(`(n:int) == ilength (vs:(int)list) ==> n <= ilength vs`), sym_rule(h3));
  thm i_lt_il = mp_rule(match_mp_rule(int_arith_rule(`(i:int) < n ==> n <= ilength (vs:(int)list) ==> i < ilength vs`), h2), n_le_il);
  thm div_ent = eq2ent(mp_rule(mp_rule(mp_rule(spec_rule(`(i:int)`, spec_rule(`(vs:(int)list)`, spec_rule(`(n:int)`, spec_rule(`(ty:ctype)`, spec_rule(`(p:int)`, get_theorem_by_name("array_at_divide")))))), h1), i_le_n), h3));
  thm sc1 = mp_rule(mp_rule(mp_rule(spec_rule(`vs:(int)list`, spec_rule(`(n:int)`, spec_rule(`(i:int)`, mk_sublist_cons()))), h1), h2), n_le_il);
  thm div2 = conv_rule(rewrite_conv(THM_LIST(sc1)), div_ent);
  thm sf = mp_rule(spec_rule(`sublist (i + 1i) (n:int) (vs:(int)list)`, spec_rule(`inth (i:int) (vs:(int)list)`, spec_rule(`(n:int) - i`, spec_rule(`(ty:ctype)`, spec_rule(`(p:int) + i * sizeof ty`, get_theorem_by_name("array_at_split_first")))))), match_mp_rule(int_arith_rule(`(i:int) < n ==> n - i >= 1i`), h2));
  thm frame = mp_rule(spec_rule(`array_at p ty i (sublist 0i (i:int) (vs:(int)list))`, spec_rule(`data_at (p + i * sizeof ty) ty (inth (i:int) (vs:(int)list)) ** array_at ((p + i * sizeof ty) + sizeof ty) ty ((n - i) - 1i) (sublist (i + 1i) (n:int) (vs:(int)list))`, spec_rule(`array_at (p + i * sizeof ty) ty (n - i) (inth (i:int) (vs:(int)list) :: sublist (i + 1i) (n:int) (vs:(int)list))`, get_theorem_by_name("hsep_cancel_left")))), sf);
  thm fin = mp_rule(mp_rule(spec_rule(`array_at p ty i (sublist 0i (i:int) (vs:(int)list)) ** (data_at (p + i * sizeof ty) ty (inth (i:int) (vs:(int)list)) ** array_at ((p + i * sizeof ty) + sizeof ty) ty ((n - i) - 1i) (sublist (i + 1i) (n:int) (vs:(int)list)))`, spec_rule(`array_at p ty i (sublist 0i (i:int) (vs:(int)list)) ** array_at (p + i * sizeof ty) ty (n - i) (inth (i:int) (vs:(int)list) :: sublist (i + 1i) (n:int) (vs:(int)list))`, spec_rule(`array_at p ty n vs`, get_theorem_by_name("hentail_trans")))), div2), frame);
  thm eq1 = spec_rule(`(ty:ctype)`, spec_rule(`(i:int)`, spec_rule(`(p:int)`, mk_addr_step())));
  thm eq2 = spec_rule(`(i:int)`, spec_rule(`(n:int)`, mk_len_step()));
  thm fin2 = conv_rule(rewrite_conv(THM_LIST(eq1, eq2)), fin);
  return close_implication(`!p ty n (vs:(int)list) i. 0i <= i ==> i < n ==> ilength vs == n ==> (array_at p ty n vs |-- array_at p ty i (sublist 0i i vs) ** data_at (p + i * sizeof ty) ty (inth i vs) ** array_at (p + (i + 1i) * sizeof ty) ty (n - (i + 1i)) (sublist (i + 1i) n vs))`, fin2);
}

/* The named closed theorems — binding them at top level executes each
 * mk_ function during this file's own verification, so a broken proof
 * fails the standalone audit (not just its first client). */
PROOF thm open_cell = mk_open_cell();
PROOF thm close_cell = mk_close_cell();
PROOF thm begin_fill = mk_begin_fill();
PROOF thm open_fill_cell = mk_open_fill_cell();
PROOF thm close_fill_cell = mk_close_fill_cell();
PROOF thm finish_fill = mk_finish_fill();

/* !p ty n vs i v. 0i <= i ==> i < n ==> ilength vs == n ==>
 *   (array_at p ty i (sublist 0i i vs) **
 *    data_at (p + i * sizeof ty) ty v **
 *    array_at (p + (i + 1i) * sizeof ty) ty (n - (i + 1i))
 *             (sublist (i + 1i) n vs) |--
 *    array_at p ty n (replace_inth i v vs)) */
PROOF thm mk_close_cell(void) {
  thm h1 = assume_rule(`0i <= (i:int)`);
  thm h2 = assume_rule(`(i:int) < n`);
  thm h3 = assume_rule(`ilength (vs:(int)list) == n`);
  thm n_le_il = match_mp_rule(int_arith_rule(`(n:int) == ilength (vs:(int)list) ==> n <= ilength vs`), sym_rule(h3));
  thm i_le_il = mp_rule(match_mp_rule(int_arith_rule(`(i:int) < n ==> n <= ilength (vs:(int)list) ==> i <= ilength vs`), h2), n_le_il);
  thm i_lt_il = mp_rule(match_mp_rule(int_arith_rule(`(i:int) < n ==> n <= ilength (vs:(int)list) ==> i < ilength vs`), h2), n_le_il);
  thm ip1_nonneg = match_mp_rule(int_arith_rule(`0i <= (i:int) ==> 0i <= i + 1i`), h1);
  thm ip1_le_n = match_mp_rule(int_arith_rule(`(i:int) < n ==> i + 1i <= n`), h2);
  thm m = spec_rule(`sublist 0i (i:int) (vs:(int)list)`, spec_rule(`(v:int)`, spec_rule(`(i:int)`, spec_rule(`(ty:ctype)`, spec_rule(`(p:int)`, get_theorem_by_name("array_at_merge_last"))))));
  thm frame = mp_rule(spec_rule(`array_at (p + (i + 1i) * sizeof ty) ty (n - (i + 1i)) (sublist (i + 1i) (n:int) (vs:(int)list))`, spec_rule(`array_at p ty (i + 1i) (sublist 0i (i:int) (vs:(int)list) ++ [(v:int)])`, spec_rule(`array_at p ty i (sublist 0i (i:int) (vs:(int)list)) ** data_at (p + i * sizeof ty) ty v`, get_theorem_by_name("hsep_cancel_right")))), m);
  thm l1 = mp_rule(mp_rule(spec_rule(`vs:(int)list`, spec_rule(`i:int`, mk_ilength_sublist())), h1), i_le_il);
  thm l2 = apply_conversion(rewrite_conv(THM_LIST(get_theorem_by_name("ILENGTH_DEF"), int_arith_rule(`1i + 0i == 1i`))), `ilength [(v:int)]`);
  thm l3 = conv_rule(rewrite_conv(THM_LIST(l1, l2)), apply_conversion(rewrite_conv(THM_LIST(get_theorem_by_name("ILENGTH_APPEND"))), `ilength (sublist 0i (i:int) (vs:(int)list) ++ [(v:int)])`));
  thm l4 = mp_rule(mp_rule(mp_rule(spec_rule(`vs:(int)list`, spec_rule(`(n:int)`, spec_rule(`(i:int) + 1i`, mk_sublist_length()))), ip1_nonneg), ip1_le_n), n_le_il);
  thm d2 = spec_rule(`sublist (i + 1i) (n:int) (vs:(int)list)`, spec_rule(`sublist 0i (i:int) (vs:(int)list) ++ [(v:int)]`, spec_rule(`(n:int) - (i + 1i)`, spec_rule(`(i:int) + 1i`, spec_rule(`(ty:ctype)`, spec_rule(`(p:int)`, get_theorem_by_name("array_at_divide2")))))));
  thm d2mp = mp_rule(mp_rule(d2, l3), l4);
  thm d2b = eq2ent(sym_rule(d2mp));
  thm fin = mp_rule(mp_rule(spec_rule(`array_at p ty ((i + 1i) + (n - (i + 1i))) ((sublist 0i (i:int) (vs:(int)list) ++ [(v:int)]) ++ sublist (i + 1i) (n:int) (vs:(int)list))`, spec_rule(`array_at p ty (i + 1i) (sublist 0i (i:int) (vs:(int)list) ++ [(v:int)]) ** array_at (p + (i + 1i) * sizeof ty) ty (n - (i + 1i)) (sublist (i + 1i) (n:int) (vs:(int)list))`, spec_rule(`(array_at p ty i (sublist 0i (i:int) (vs:(int)list)) ** data_at (p + i * sizeof ty) ty v) ** array_at (p + (i + 1i) * sizeof ty) ty (n - (i + 1i)) (sublist (i + 1i) (n:int) (vs:(int)list))`, get_theorem_by_name("hentail_trans")))), frame), d2b);
  thm assoc = spec_rule(`array_at (p + (i + 1i) * sizeof ty) ty (n - (i + 1i)) (sublist (i + 1i) (n:int) (vs:(int)list))`, spec_rule(`data_at (p + i * sizeof ty) ty v`, spec_rule(`array_at p ty i (sublist 0i (i:int) (vs:(int)list))`, get_theorem_by_name("hsep_assoc"))));
  thm eq_total = int_arith_rule(`((i:int) + 1i) + (n - (i + 1i)) == n`);
  thm rp = mp_rule(mp_rule(spec_rule(`vs:(int)list`, spec_rule(`(v:int)`, spec_rule(`(i:int)`, mk_replace_inth_split()))), h1), i_lt_il);
  thm sublist_n = apply_conversion(rewrite_conv(THM_LIST(sym_rule(h3))), `sublist (i + 1i) (n:int) (vs:(int)list)`);
  thm rlist = apply_conversion(rewrite_conv(THM_LIST(sym_rule(ispec_rule(`sublist (i + 1i) (n:int) (vs:(int)list)`, ispec_rule(`[(v:int)]`, ispec_rule(`sublist 0i (i:int) (vs:(int)list)`, get_theorem_by_name("APPEND_ASSOC"))))), sublist_n, rp)), `(sublist 0i (i:int) (vs:(int)list) ++ [(v:int)]) ++ sublist (i + 1i) (n:int) (vs:(int)list)`);
  thm fin2 = conv_rule(rewrite_conv(THM_LIST(assoc, eq_total, rlist)), fin);
  return close_implication(`!p ty n (vs:(int)list) i v. 0i <= i ==> i < n ==> ilength vs == n ==> (array_at p ty i (sublist 0i i vs) ** data_at (p + i * sizeof ty) ty v ** array_at (p + (i + 1i) * sizeof ty) ty (n - (i + 1i)) (sublist (i + 1i) n vs) |-- array_at p ty n (replace_inth i v vs))`, fin2);
}

/*=============================== fill cursor ===============================*/

/* !p ty n. undef_array_at p ty n |--
 *            array_at p ty 0i [] ** undef_array_at (p + 0i * sizeof ty) ty (n - 0i) */
PROOF thm mk_begin_fill(void) {
  thm eq1 = int_arith_rule(`(p:int) + 0i * sizeof ty == p`);
  thm eq2 = int_arith_rule(`(n:int) - 0i == n`);
  thm aeq = sym_rule(apply_conversion(rewrite_conv(THM_LIST(eq1, eq2)), `undef_array_at (p + 0i * sizeof ty) ty (n - 0i)`));
  thm z1 = mp_rule(mp_rule(spec_rule(`[]:(int)list`, spec_rule(`0i:int`, spec_rule(`(ty:ctype)`, spec_rule(`(p:int)`, get_theorem_by_name("array_at_zero"))))), refl_rule(`0i:int`)), refl_rule(`[]:(int)list`));
  thm emp_eq = sym_rule(z1);
  term X = parse_term("undef_array_at (p + 0i * sizeof ty) ty (n - 0i)");
  thm unit_eq = sym_rule(spec_rule(X, get_theorem_by_name("hsep_hemp_left")));
  thm bin = mk_binop_rule(get_hconj(), emp_eq, refl_rule(X));
  return close_implication(`!p ty n. undef_array_at p ty n |-- array_at p ty 0i [] ** undef_array_at (p + 0i * sizeof ty) ty (n - 0i)`, eq2ent(trans_rule(aeq, trans_rule(unit_eq, bin))));
}

/* !p ty n iv. n - iv >= 1i ==>
 *   (undef_array_at (p + iv * sizeof ty) ty (n - iv) |--
 *    undef_data_at (p + iv * sizeof ty) ty **
 *    undef_array_at (p + (iv + 1i) * sizeof ty) ty (n - (iv + 1i))) */
PROOF thm mk_open_fill_cell(void) {
  thm raw = spec_rule(`(n:int) - iv`, spec_rule(`(ty:ctype)`, spec_rule(`(p:int) + iv * sizeof ty`, get_theorem_by_name("undef_array_at_split_first"))));
  thm eq1 = spec_rule(`(ty:ctype)`, spec_rule(`(iv:int)`, spec_rule(`(p:int)`, mk_addr_step())));
  thm eq2 = spec_rule(`(iv:int)`, spec_rule(`(n:int)`, mk_len_step()));
  thm raw2 = conv_rule(rewrite_conv(THM_LIST(eq1, eq2)), raw);
  return close_implication(`!p ty n iv. (n:int) - iv >= 1i ==> (undef_array_at (p + iv * sizeof ty) ty (n - iv) |-- undef_data_at (p + iv * sizeof ty) ty ** undef_array_at (p + (iv + 1i) * sizeof ty) ty (n - (iv + 1i)))`, undisch_rule(raw2));
}

/* !p ty iv pl v. array_at p ty iv pl ** data_at (p + iv * sizeof ty) ty v |--
 *                 array_at p ty (iv + 1i) (pl ++ [v]) */
PROOF thm mk_close_fill_cell(void) {
  thm m = spec_rule(`pl:(int)list`, spec_rule(`(v:int)`, spec_rule(`(iv:int)`, spec_rule(`(ty:ctype)`, spec_rule(`(p:int)`, get_theorem_by_name("array_at_merge_last"))))));
  return close_implication(`!p ty iv (pl:(int)list) v. array_at p ty iv pl ** data_at (p + iv * sizeof ty) ty v |-- array_at p ty (iv + 1i) (pl ++ [v])`, m);
}

/* !p ty n iv pl. iv == n ==>
 *   (array_at p ty iv pl ** undef_array_at (p + iv * sizeof ty) ty (n - iv) |--
 *    array_at p ty n pl) */
PROOF thm mk_finish_fill(void) {
  thm h_eq = assume_rule(`(iv:int) == n`);
  thm a_eq = apply_conversion(rewrite_conv(THM_LIST(h_eq)), `array_at p ty iv pl`);
  thm b_eq2 = trans_rule(apply_conversion(rewrite_conv(THM_LIST(h_eq)), `undef_array_at (p + iv * sizeof ty) ty (n - iv)`), mp_rule(spec_rule(`(n:int) - n`, spec_rule(`(ty:ctype)`, spec_rule(`(p:int) + n * sizeof ty`, get_theorem_by_name("undef_array_at_zero")))), int_arith_rule(`(n:int) - n == 0i`)));
  thm bin = mk_binop_rule(get_hconj(), a_eq, b_eq2);
  thm unit = spec_rule(`array_at p ty n pl`, get_theorem_by_name("hsep_hemp_right"));
  return close_implication(`!p ty n iv (pl:(int)list). (iv:int) == n ==> (array_at p ty iv pl ** undef_array_at (p + iv * sizeof ty) ty (n - iv) |-- array_at p ty n pl)`, eq2ent(trans_rule(bin, unit)));
}
