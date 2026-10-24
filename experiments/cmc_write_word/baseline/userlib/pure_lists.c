/* s2-3a — pure_lists: the PURE foundation of the array library.
 *
 * Spec (task s2-3a): a family of closed `:bool` list lemmas — no heap, no
 * data_at, no clients — that the spatial layer (s2-3b) and the memcpy
 * layer (s2-4) build on.
 *
 * The families:
 *   ireplicate (all-zero value lists for zeroed arrays):
 *     ireplicate_empty   : ireplicate 0 v == []
 *     ireplicate_snoc    : 0 <= n ==>
 *                          ireplicate (n + 1i) v == ireplicate n v ++ [v]
 *     ireplicate_append2 : two replications of one value merge:
 *                          0 <= n ==> 0 <= m ==>
 *                          ireplicate n v ++ ireplicate m v
 *                            == ireplicate (n + m) v
 *   sublist / prefix (memcpy's view of a list as a walkable array):
 *     sublist_empty      : sublist 0 0 l == []
 *     sublist_snoc       : 0 <= n ==> n < ilength l ==>
 *                          sublist 0 n l ++ [inth n l] == sublist 0 (n+1) l
 *     sublist_full       : sublist 0 (ilength l) l == l
 *   ilength / num_of_int bridges (the loop arithmetic's fuel):
 *     ilength_ireplicate : 0 <= n ==> ilength (ireplicate n v) == n
 *     ilength_sublist    : 0 <= n ==> n <= ilength l ==>
 *                          ilength (sublist 0 n l) == n
 *     ilength_of_num_length : ilength l == &(LENGTH l)   (the central one)
 *     int_lt_num_of_num  : 0 <= n ==> n < &m ==> num_of_int n < m
 *     int_le_num_of_num  : 0 <= n ==> n <= &m ==> num_of_int n <= m
 *     num_of_int_suc     : 0 <= n ==> num_of_int (n + 1i) == SUC (num_of_int n)
 *
 * Design notes (why the statements are what they are):
 *   - The num-level machinery (FIRSTN/NTH/REPLICATE over :num) is proved
 *     once and hidden: mk_firstn_snoc_num, mk_length_firstn_num,
 *     mk_firstn_full_num, mk_replicate_append_num. The exported int-level
 *     theorems are one rewrite-chain away from them via num_of_int.
 *   - `sublist 0i n l` is the canonical prefix of length n
 *     (sublist lo hi l = SKIPN lo (FIRSTN hi l), so sublist 0i n l =
 *     FIRSTN (num_of_int n) l — mk_sublist_0_firstn).
 *   - Every list binder is pinned `(l:(int)list)` and every value binder
 *     `(v:int)`: unpinned binders get fresh TYPE variables that never
 *     alpha-match a monomorphic forward theorem (a TRANS/ACCEPT failure
 *     whose rendered term shows `?NNNNNN`).
 *
 * Proof-method notes (all developed in pure_probe.c first):
 *   - Engine-generated leaf variables (a0/a1/n) break mp_rule/spec_rule
 *     chains built on backtick re-parses: read the leaf's own assumption
 *     terms via goal_lasmps and apply the IH with match_mp_rule.
 *   - rewrite_conv loop-guards rewrites whose LHS is a bare variable that
 *     also occurs free in the RHS (`n == &(num_of_int n)` is refused);
 *     travel in the safe direction (`&(num_of_int n) == n` fires).
 *   - num_lt_suc / num_le_suc (userlib) strip the SUC off both sides of a
 *     nat inequality as rewrite rules.
 */

#include "proof/proof.h"

#include "userlib/renderers.h"

#include "userlib/proof.h"
#require "userlib/proof.c"

#include "userlib/pure_lists.h"

/*--- nat SUC-monotonicity bridges. NOTE: file-scope PROOF variable
 *    bindings do NOT cross #require boundaries (the generated C only sees
 *    them inside their own file) — shared facts like these live in the
 *    file that uses them, or are wrapped in mk_ functions. ---*/

PROOF thm num_lt_suc = arith_rule(`!m n. SUC m < SUC n <=> m < n`);
PROOF thm num_le_suc = arith_rule(`!m n. SUC m <= SUC n <=> m <= n`);

/*==========================================================================
  The num-level helpers (internal — the int-level exports sit on these)
==========================================================================*/

/* !l m. m < LENGTH l ==> FIRSTN m l ++ [NTH m l] == FIRSTN (SUC m) l
 * Induction on l; base: m < LENGTH [] is absurd (CONTR), step: split m. */
PROOF thm mk_firstn_snoc_num(void) {
  gnode root = gnode_new_with_ccl(`!l m. (m:num) < LENGTH (l:(int)list) ==> FIRSTN m l ++ [NTH m l] == FIRSTN (SUC m) l`);
  gnode_list cases = INDUCT_TAC(root, `l:(int)list`);
  gnode b0 = AUTO_INTROS_TAC(cases[0]);
  thm h0 = assume_rule(goal_lasmps(b0->g)[0].tm);
  thm h0b = conv_rule(rewrite_conv(THM_LIST(conjunct1_rule(get_theorem_by_name("LENGTH")))), h0);
  CONTR_TAC(b0, match_mp_rule(arith_rule(`(m:num) < 0 ==> F`), h0b));
  gnode s0 = AUTO_INTROS_TAC(cases[1]);
  gnode_list mc = CASES_TAC(s0, `(m:num)`, "M");
  CONV_WITH_ASMP_TAC(mc[0], rewrite_conv, THM_LIST(get_theorem_by_name("FIRSTN_DEF"), get_theorem_by_name("NTH_DEF"), get_theorem_by_name("APPEND")));
  gnode b2 = mc[1];
  labeled_term_list asmps = goal_lasmps(b2->g);
  thm ih = assume_rule(asmps[0].tm);
  thm hcons = assume_rule(asmps[2].tm);
  thm hlt = assume_rule(asmps[1].tm);
  thm hlt2 = conv_rule(rewrite_conv(THM_LIST(hcons, conjunct2_rule(get_theorem_by_name("LENGTH")))), hlt);
  thm hlt3 = conv_rule(rewrite_conv(THM_LIST(num_lt_suc)), hlt2);
  thm ih_eq = match_mp_rule(ih, hlt3);
  CONV_TAC(b2, rewrite_conv(THM_LIST(hcons, ih_eq, get_theorem_by_name("FIRSTN_DEF"), get_theorem_by_name("NTH_DEF"), get_theorem_by_name("APPEND"))));
  return gnode_prove(root);
}

/* !m l. m <= LENGTH l ==> LENGTH (FIRSTN m l) == m
 * Induction on m; base closes on the defs, step: split l. */
PROOF thm mk_length_firstn_num(void) {
  gnode root = gnode_new_with_ccl(`!m l. (m:num) <= LENGTH (l:(int)list) ==> LENGTH (FIRSTN m l) == m`);
  gnode_list cases = INDUCT_TAC(root, `m:num`);
  gnode b0 = AUTO_INTROS_TAC(cases[0]);
  CONV_TAC(b0, rewrite_conv(THM_LIST(get_theorem_by_name("FIRSTN_DEF"), get_theorem_by_name("LENGTH"))));
  gnode s0 = AUTO_INTROS_TAC(cases[1]);
  gnode_list lc = CASES_TAC(s0, `(l:(int)list)`, "L");
  gnode z0 = lc[0];
  labeled_term_list zasmps = goal_lasmps(z0->g);
  thm h_eq = assume_rule(zasmps[2].tm);
  thm h_le = assume_rule(zasmps[1].tm);
  thm h_le2 = conv_rule(rewrite_conv(THM_LIST(h_eq, conjunct1_rule(get_theorem_by_name("LENGTH")))), h_le);
  CONTR_TAC(z0, match_mp_rule(arith_rule(`SUC (m:num) <= 0 ==> F`), h_le2));
  gnode z1 = lc[1];
  labeled_term_list casmps = goal_lasmps(z1->g);
  thm cih = assume_rule(casmps[0].tm);
  thm ccons = assume_rule(casmps[2].tm);
  thm cle = assume_rule(casmps[1].tm);
  thm cle2 = conv_rule(rewrite_conv(THM_LIST(ccons, conjunct2_rule(get_theorem_by_name("LENGTH")))), cle);
  thm cle3 = conv_rule(rewrite_conv(THM_LIST(num_le_suc)), cle2);
  thm cih_eq = match_mp_rule(cih, cle3);
  CONV_TAC(z1, rewrite_conv(THM_LIST(ccons, cih_eq, get_theorem_by_name("FIRSTN_DEF"), get_theorem_by_name("LENGTH"))));
  return gnode_prove(root);
}

/* !l. FIRSTN (LENGTH l) l == l — induction on l. */
PROOF thm mk_firstn_full_num(void) {
  return induct_rewrite_close(`!l. FIRSTN (LENGTH l) (l:(int)list) == l`,
      `l:(int)list`,
      THM_LIST(get_theorem_by_name("LENGTH"), get_theorem_by_name("FIRSTN_DEF")),
      THM_LIST(get_theorem_by_name("LENGTH"), get_theorem_by_name("FIRSTN_DEF")));
}

/* !n m x. REPLICATE n x ++ REPLICATE m x == REPLICATE (n + m) x
 * Induction on n; base/step close on REPLICATE + APPEND + ADD_CLAUSES. */
PROOF thm mk_replicate_append_num(void) {
  return induct_rewrite_close(`!n m (x:int). REPLICATE n x ++ REPLICATE m x == REPLICATE (n + m) x`,
      `n:num`,
      THM_LIST(get_theorem_by_name("REPLICATE"), get_theorem_by_name("APPEND"), get_theorem_by_name("ADD_CLAUSES")),
      THM_LIST(get_theorem_by_name("REPLICATE"), get_theorem_by_name("APPEND"), get_theorem_by_name("ADD_CLAUSES")));
}

/* !n l. LENGTH (SKIPN n l) == LENGTH l - n — the tail-length bridge
 * (sublist_length's engine). SKIPN saturates to [], and num subtraction
 * saturates the same way, so there is no side condition. */
PROOF thm mk_length_skipn_num(void) {
  gnode root = gnode_new_with_ccl(`!n l. LENGTH (SKIPN n (l:(int)list)) == LENGTH l - n`);
  gnode_list cases = INDUCT_TAC(root, `l:(int)list`);
  gnode b0 = AUTO_INTROS_TAC(cases[0]);
  gnode_list bcases = CASES_TAC(b0, `(n:num)`, "N");
  CONV_WITH_ASMP_TAC(bcases[0], rewrite_conv, THM_LIST(get_theorem_by_name("LENGTH"), get_theorem_by_name("SKIPN_DEF"), arith_rule(`(0:num) - 0 == 0`)));
  CONV_WITH_ASMP_TAC(bcases[1], rewrite_conv, THM_LIST(get_theorem_by_name("LENGTH"), get_theorem_by_name("SKIPN_DEF"), arith_rule(`!n. (0:num) - SUC n == 0`)));
  gnode s0 = AUTO_INTROS_TAC(cases[1]);
  gnode_list scases = CASES_TAC(s0, `(n:num)`, "N");
  CONV_WITH_ASMP_TAC(scases[0], rewrite_conv, THM_LIST(get_theorem_by_name("LENGTH"), get_theorem_by_name("SKIPN_DEF"), arith_rule(`!m. (m:num) - 0 == m`)));
  gnode s1 = scases[1];
  thm ih = assume_rule(goal_lasmps(s1->g)[0].tm);
  CONV_WITH_ASMP_TAC(s1, rewrite_conv, THM_LIST(get_theorem_by_name("LENGTH"), get_theorem_by_name("SKIPN_DEF"), ih, arith_rule(`!m n. (SUC m) - (SUC n) == m - n`)));
  return gnode_prove(root);
}

/* !l a b. a < b ==> b <= LENGTH l ==>
 *         SKIPN a (FIRSTN b l) == NTH a l :: SKIPN (SUC a) (FIRSTN b l)
 * The windowed-head split (sublist_cons's engine): the head of the
 * [a,b) window is the element at a. Induction on l; the step splits b
 * then a, and the a = SUC a_ branch walks SKIPN/FIRSTN/NTH down with the
 * IH at (a_, b_). */
PROOF thm mk_skipn_firstn_nth_num(void) {
  gnode root = gnode_new_with_ccl(`!l a b. (a:num) < b ==> b <= LENGTH (l:(int)list) ==> SKIPN a (FIRSTN b l) == NTH a l :: SKIPN (SUC a) (FIRSTN b l)`);
  gnode_list cases = INDUCT_TAC(root, `l:(int)list`);
  gnode b0 = AUTO_INTROS_TAC(cases[0]);
  labeled_term_list b0as = goal_lasmps(b0->g);
  thm b0_lt = assume_rule(b0as[0].tm);
  thm b0_le = conv_rule(rewrite_conv(THM_LIST(conjunct1_rule(get_theorem_by_name("LENGTH")))), assume_rule(b0as[1].tm));
  CONTR_TAC(b0, match_mp_rule(match_mp_rule(arith_rule(`(a:num) < b ==> b <= 0 ==> F`), b0_lt), b0_le));
  gnode s0 = AUTO_INTROS_TAC(cases[1]);
  gnode_list bcases = CASES_TAC(s0, `(b:num)`, "B");
  gnode bz = bcases[0];
  labeled_term_list bzas = goal_lasmps(bz->g);
  thm bz_eq = assume_rule(bzas[3].tm);
  thm bz_lt = conv_rule(rewrite_conv(THM_LIST(bz_eq)), assume_rule(bzas[1].tm));
  CONTR_TAC(bz, match_mp_rule(arith_rule(`(a:num) < 0 ==> F`), bz_lt));
  gnode bs = bcases[1];
  gnode_list acases = CASES_TAC(bs, `(a:num)`, "A");
  CONV_WITH_ASMP_TAC(acases[0], rewrite_conv, THM_LIST(get_theorem_by_name("SKIPN_DEF"), get_theorem_by_name("NTH_DEF"), get_theorem_by_name("FIRSTN_DEF")));
  gnode as1 = acases[1];
  labeled_term_list asas = goal_lasmps(as1->g);
  thm a_eq = assume_rule(asas[4].tm);
  thm b_eq = assume_rule(asas[3].tm);
  thm ih = assume_rule(asas[0].tm);
  thm lt2 = conv_rule(rewrite_conv(THM_LIST(a_eq, b_eq)), assume_rule(asas[1].tm));
  thm lt3 = conv_rule(rewrite_conv(THM_LIST(num_lt_suc)), lt2);
  thm le2 = conv_rule(rewrite_conv(THM_LIST(b_eq, conjunct2_rule(get_theorem_by_name("LENGTH")))), assume_rule(asas[2].tm));
  thm le3 = conv_rule(rewrite_conv(THM_LIST(num_le_suc)), le2);
  thm ih_eq = match_mp_rule(match_mp_rule(ih, lt3), le3);
  CONV_TAC(as1, rewrite_conv(THM_LIST(a_eq, b_eq, ih_eq, get_theorem_by_name("SKIPN_DEF"), get_theorem_by_name("NTH_DEF"), get_theorem_by_name("FIRSTN_DEF"))));
  return gnode_prove(root);
}

/* !n a l. n < LENGTH l ==>
 *         REPLACE_NTH n a l == FIRSTN n l ++ [a] ++ SKIPN (SUC n) l
 * The replace-at-index split (replace_inth_split's engine). Induction on
 * l; the step splits n, and the SUC branch walks the recursion with the
 * IH at n_. */
PROOF thm mk_replace_nth_split_num(void) {
  gnode root = gnode_new_with_ccl(`!n a l. (n:num) < LENGTH (l:(int)list) ==> REPLACE_NTH n a l == FIRSTN n l ++ [a] ++ SKIPN (SUC n) l`);
  gnode_list cases = INDUCT_TAC(root, `l:(int)list`);
  gnode b0 = AUTO_INTROS_TAC(cases[0]);
  thm b0_lt = conv_rule(rewrite_conv(THM_LIST(conjunct1_rule(get_theorem_by_name("LENGTH")))), assume_rule(goal_lasmps(b0->g)[0].tm));
  CONTR_TAC(b0, match_mp_rule(arith_rule(`(n:num) < 0 ==> F`), b0_lt));
  gnode s0 = AUTO_INTROS_TAC(cases[1]);
  gnode_list nc = CASES_TAC(s0, `(n:num)`, "N");
  CONV_WITH_ASMP_TAC(nc[0], rewrite_conv, THM_LIST(get_theorem_by_name("REPLACE_NTH_DEF"), get_theorem_by_name("FIRSTN_DEF"), get_theorem_by_name("SKIPN_DEF"), get_theorem_by_name("APPEND"), get_theorem_by_name("APPEND_SING")));
  gnode s1 = nc[1];
  labeled_term_list sas = goal_lasmps(s1->g);
  thm n_eq = assume_rule(sas[2].tm);
  thm ih = assume_rule(sas[0].tm);
  thm lt2 = conv_rule(rewrite_conv(THM_LIST(n_eq, conjunct2_rule(get_theorem_by_name("LENGTH")))), assume_rule(sas[1].tm));
  thm lt3 = conv_rule(rewrite_conv(THM_LIST(num_lt_suc)), lt2);
  thm ih_eq = match_mp_rule(ih, lt3);
  CONV_TAC(s1, rewrite_conv(THM_LIST(n_eq, ih_eq, get_theorem_by_name("REPLACE_NTH_DEF"), get_theorem_by_name("FIRSTN_DEF"), get_theorem_by_name("SKIPN_DEF"), get_theorem_by_name("APPEND"), get_theorem_by_name("APPEND_SING"))));
  return gnode_prove(root);
}

/*==========================================================================
  The int/num bridges
==========================================================================*/

/* !n m. 0i <= n ==> n < &m ==> num_of_int n < m */
PROOF thm mk_int_lt_num_of_num(void) {
  thm h1 = assume_rule(`0i <= (n:int)`);
  thm h2 = assume_rule(`(n:int) < &(m:num)`);
  thm eq = mp_rule(spec_rule(`n:int`, get_theorem_by_name("INT_OF_NUM_OF_INT")), h1);
  thm raw = apply_conversion(rewrite_conv(THM_LIST(eq)), `&(num_of_int (n:int)) < &(m:num)`);
  thm h2b = eq_mp_rule(sym_rule(raw), h2);
  thm iff = spec_rule(`m:num`, spec_rule(`num_of_int (n:int)`, get_theorem_by_name("INT_OF_NUM_LT")));
  return close_implication(`!n m. 0i <= n ==> n < &m ==> num_of_int n < m`, eq_mp_rule(iff, h2b));
}

/* !n m. 0i <= n ==> n <= &m ==> num_of_int n <= m */
PROOF thm mk_int_le_num_of_num(void) {
  thm h1 = assume_rule(`0i <= (n:int)`);
  thm h2 = assume_rule(`(n:int) <= &(m:num)`);
  thm eq = mp_rule(spec_rule(`n:int`, get_theorem_by_name("INT_OF_NUM_OF_INT")), h1);
  thm raw = apply_conversion(rewrite_conv(THM_LIST(eq)), `&(num_of_int (n:int)) <= &(m:num)`);
  thm h2b = eq_mp_rule(sym_rule(raw), h2);
  thm iff = spec_rule(`m:num`, spec_rule(`num_of_int (n:int)`, get_theorem_by_name("INT_OF_NUM_LE")));
  return close_implication(`!n m. 0i <= n ==> n <= &m ==> num_of_int n <= m`, eq_mp_rule(iff, h2b));
}

/* !n. 0i <= n ==> num_of_int (n + 1i) == SUC (num_of_int n) */
PROOF thm mk_num_of_int_suc(void) {
  thm h1 = assume_rule(`0i <= (n:int)`);
  thm noa = spec_rule(`1i:int`, spec_rule(`n:int`, get_theorem_by_name("NUM_OF_INT_ADD")));
  thm noa2 = conv_rule(rewrite_conv(THM_LIST(get_theorem_by_name("NUM_OF_INT_OF_NUM"))), noa);
  thm add_eq = mp_rule(noa2, conj_rule(h1, int_arith_rule(`0i <= 1i`)));
  thm add1 = spec_rule(`num_of_int (n:int)`, get_theorem_by_name("ADD1"));
  return close_implication(`!n. 0i <= n ==> num_of_int (n + 1i) == SUC (num_of_int n)`, trans_rule(add_eq, sym_rule(add1)));
}

/*==========================================================================
  sublist / ilength unfold helpers (shared by the exports below)
==========================================================================*/

/* !n l. sublist 0i n l == FIRSTN (num_of_int n) l — the prefix of length n
 * is the first n elements. (SKIPN 0 x == x; num_of_int 0i == 0.) */
PROOF thm mk_sublist_0_firstn(void) {
  gnode root = gnode_new_with_ccl(`!n l. sublist 0i (n:int) (l:(int)list) == FIRSTN (num_of_int n) l`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_TAC(leaf, rewrite_conv(THM_LIST(get_theorem_by_name("SUBLIST_DEF"), get_theorem_by_name("NUM_OF_INT_OF_NUM"), conjunct1_rule(get_theorem_by_name("SKIPN_DEF")))));
  return gnode_prove(root);
}

/* !n l. inth n l == NTH (num_of_int n) l */
PROOF thm mk_inth_nth(void) {
  gnode root = gnode_new_with_ccl(`!n l. inth n l == NTH (num_of_int n) (l:(int)list)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_TAC(leaf, rewrite_conv(THM_LIST(get_theorem_by_name("INTH_DEF"))));
  return gnode_prove(root);
}

/*==========================================================================
  The spatial layer's window lemmas (s2-3b): the sublist window [i, n)
  splits at its head, has length n - lo, and replace_inth is the
  three-piece reassembly. All three are consumed by array.c.
==========================================================================*/

/* !i n vs. 0i <= i ==> i < n ==> n <= ilength vs ==>
 *         sublist i n vs == inth i vs :: sublist (i + 1i) n vs
 * The windowed-head split (open_cell's engine): the first element of the
 * [i, n) window is the element at index i. Chain: sublist = SKIPN o
 * FIRSTN; the num-level head split (mk_skipn_firstn_nth_num) applied at
 * (num_of_int i, num_of_int n); NTH/SUC bridges back to inth / the
 * (i + 1i) window. */
PROOF thm mk_sublist_cons(void) {
  thm h1 = assume_rule(`0i <= (i:int)`);
  thm h2 = assume_rule(`(i:int) < n`);
  thm h3 = assume_rule(`(n:int) <= ilength (vs:(int)list)`);
  thm h_n = mp_rule(match_mp_rule(int_arith_rule(`0i <= (i:int) ==> i < n ==> 0i <= n`), h1), h2);
  thm i_eq = mp_rule(spec_rule(`i:int`, get_theorem_by_name("INT_OF_NUM_OF_INT")), h1);
  thm n_eq = mp_rule(spec_rule(`n:int`, get_theorem_by_name("INT_OF_NUM_OF_INT")), h_n);
  thm lt_int = eq_mp_rule(mk_binop_rule(`(<):int->int->bool`, sym_rule(i_eq), sym_rule(n_eq)), h2);
  thm i_lt_n_num = conv_rule(rewrite_conv(THM_LIST(get_theorem_by_name("INT_OF_NUM_LT"))), lt_int);
  thm h3_len = conv_rule(rewrite_conv(THM_LIST(mk_ilength_of_num_length())), h3);
  thm n_le_len_num = mp_rule(mp_rule(spec_rule(`LENGTH (vs:(int)list)`, spec_rule(`n:int`, mk_int_le_num_of_num())), h_n), h3_len);
  thm nl2 = mp_rule(mp_rule(spec_rule(`num_of_int (n:int)`, spec_rule(`num_of_int (i:int)`, spec_rule(`vs:(int)list`, mk_skipn_firstn_nth_num()))), i_lt_n_num), n_le_len_num);
  thm lhs_eq = apply_conversion(rewrite_conv(THM_LIST(get_theorem_by_name("SUBLIST_DEF"))), `sublist (i:int) (n:int) (vs:(int)list)`);
  thm suc_eq = sym_rule(mp_rule(spec_rule(`i:int`, mk_num_of_int_suc()), h1));
  thm inth_inst = sym_rule(spec_rule(`vs:(int)list`, spec_rule(`i:int`, mk_inth_nth())));
  thm sub_inst = sym_rule(apply_conversion(rewrite_conv(THM_LIST(get_theorem_by_name("SUBLIST_DEF"))), `sublist ((i:int) + 1i) (n:int) (vs:(int)list)`));
  thm nl3 = conv_rule(rewrite_conv(THM_LIST(inth_inst, suc_eq, sub_inst)), nl2);
  return close_implication(`!i n (vs:(int)list). 0i <= i ==> i < n ==> n <= ilength vs ==> sublist i n vs == inth i vs :: sublist (i + 1i) n vs`, trans_rule(lhs_eq, nl3));
}

/* !lo hi l. 0i <= lo ==> lo <= hi ==> hi <= ilength l ==>
 *         ilength (sublist lo hi l) == hi - lo
 * The window length (close_cell's right-flank length fact). Chain:
 * sublist = SKIPN o FIRSTN -> LENGTH (SKIPN k X) = LENGTH X - k
 * (mk_length_skipn_num) -> LENGTH (FIRSTN hi l) = num_of_int hi
 * (mk_length_firstn_num) -> &(num sub) -> INT_OF_NUM_SUB -> &-bridges. */
PROOF thm mk_sublist_length(void) {
  thm h1 = assume_rule(`0i <= (lo:int)`);
  thm h2 = assume_rule(`(lo:int) <= hi`);
  thm h3 = assume_rule(`(hi:int) <= ilength (l:(int)list)`);
  thm h_hi = mp_rule(match_mp_rule(int_arith_rule(`0i <= (lo:int) ==> lo <= hi ==> 0i <= hi`), h1), h2);
  thm lo_eq = mp_rule(spec_rule(`lo:int`, get_theorem_by_name("INT_OF_NUM_OF_INT")), h1);
  thm hi_eq = mp_rule(spec_rule(`hi:int`, get_theorem_by_name("INT_OF_NUM_OF_INT")), h_hi);
  thm lo_le_hi_int = eq_mp_rule(mk_binop_rule(`(<=):int->int->bool`, sym_rule(lo_eq), sym_rule(hi_eq)), h2);
  thm lo_le_hi_num = conv_rule(rewrite_conv(THM_LIST(get_theorem_by_name("INT_OF_NUM_LE"))), lo_le_hi_int);
  thm hi_le_len = conv_rule(rewrite_conv(THM_LIST(mk_ilength_of_num_length())), h3);
  thm hi_num_le = mp_rule(mp_rule(spec_rule(`LENGTH (l:(int)list)`, spec_rule(`hi:int`, mk_int_le_num_of_num())), h_hi), hi_le_len);
  thm lf = mp_rule(spec_rule(`(l:(int)list)`, spec_rule(`num_of_int (hi:int)`, mk_length_firstn_num())), hi_num_le);
  thm ios = sym_rule(mp_rule(spec_rule(`num_of_int (hi:int)`, spec_rule(`num_of_int (lo:int)`, get_theorem_by_name("INT_OF_NUM_SUB"))), lo_le_hi_num));
  thm u = apply_conversion(rewrite_conv(THM_LIST(mk_ilength_of_num_length(), get_theorem_by_name("SUBLIST_DEF"))), `ilength (sublist (lo:int) (hi:int) (l:(int)list))`);
  thm ls = spec_rule(`FIRSTN (num_of_int (hi:int)) (l:(int)list)`, spec_rule(`num_of_int (lo:int)`, mk_length_skipn_num()));
  thm w = conv_rule(rewrite_conv(THM_LIST(ls)), u);
  thm w2 = conv_rule(rewrite_conv(THM_LIST(lf)), w);
  thm w3 = conv_rule(rewrite_conv(THM_LIST(ios)), w2);
  thm w4 = conv_rule(rewrite_conv(THM_LIST(hi_eq, lo_eq)), w3);
  return close_implication(`!lo hi (l:(int)list). 0i <= lo ==> lo <= hi ==> hi <= ilength l ==> ilength (sublist lo hi l) == hi - lo`, w4);
}

/* !i v vs. 0i <= i ==> i < ilength vs ==>
 *         sublist 0i i vs ++ [v] ++ sublist (i + 1i) (ilength vs) vs
 *           == replace_inth i v vs
 * The write-back split (close_cell's final list step): replacing index i
 * is the prefix, the new element, and the tail window. Chain:
 * REPLACE_INTH_DEF -> mk_replace_nth_split_num at num_of_int i ->
 * FIRSTN/SUC/SKIPN bridges to the sublist spellings (FIRSTN n vs = sublist
 * 0i n vs; SUC (num_of_int i) = num_of_int (i + 1i); the tail window is
 * the full-length suffix). */
PROOF thm mk_replace_inth_split(void) {
  thm h1 = assume_rule(`0i <= (i:int)`);
  thm h2 = assume_rule(`(i:int) < ilength (vs:(int)list)`);
  thm h2_len = conv_rule(rewrite_conv(THM_LIST(mk_ilength_of_num_length())), h2);
  thm i_lt_len = mp_rule(mp_rule(spec_rule(`LENGTH (vs:(int)list)`, spec_rule(`i:int`, mk_int_lt_num_of_num())), h1), h2_len);
  thm rn2 = mp_rule(spec_rule(`vs:(int)list`, spec_rule(`(v:int)`, spec_rule(`num_of_int (i:int)`, mk_replace_nth_split_num()))), i_lt_len);
  thm rid = apply_conversion(rewrite_conv(THM_LIST(get_theorem_by_name("REPLACE_INTH_DEF"))), `replace_inth (i:int) (v:int) (vs:(int)list)`);
  thm firstn_inst = sym_rule(spec_rule(`vs:(int)list`, spec_rule(`i:int`, mk_sublist_0_firstn())));
  thm suc_eq = sym_rule(mp_rule(spec_rule(`i:int`, mk_num_of_int_suc()), h1));
  thm il_len = conv_rule(rewrite_conv(THM_LIST(get_theorem_by_name("NUM_OF_INT_OF_NUM"))), apply_conversion(rewrite_conv(THM_LIST(mk_ilength_of_num_length())), `num_of_int (ilength (vs:(int)list))`));
  thm firstn_full = spec_rule(`vs:(int)list`, mk_firstn_full_num());
  thm sl3 = conv_rule(rewrite_conv(THM_LIST(il_len, firstn_full)), apply_conversion(rewrite_conv(THM_LIST(get_theorem_by_name("SUBLIST_DEF"))), `sublist ((i:int) + 1i) (ilength (vs:(int)list)) vs`));
  thm sl4 = conv_rule(rewrite_conv(THM_LIST(sym_rule(suc_eq))), sl3);
  thm rn3 = conv_rule(rewrite_conv(THM_LIST(firstn_inst, sym_rule(sl4))), rn2);
  return close_implication(`!i (v:int) (vs:(int)list). 0i <= i ==> i < ilength vs ==> sublist 0i i vs ++ [v] ++ sublist (i + 1i) (ilength vs) vs == replace_inth i v vs`, sym_rule(trans_rule(rid, rn3)));
}

/*==========================================================================
  The exported theorems
==========================================================================*/

/* !l. ilength l == &(LENGTH l) — induction on l; the step needs the
 * commuted INT_OF_NUM_SUC (INT_ADD_SYM), built forward and used as a
 * rewrite so the engine-named tail variable does not matter. */
PROOF thm mk_ilength_of_num_length(void) {
  gnode root = gnode_new_with_ccl(`!l. ilength (l:(int)list) == &(LENGTH l)`);
  gnode_list cases = INDUCT_TAC(root, `l:(int)list`);
  CONV_TAC(cases[0], rewrite_conv(THM_LIST(get_theorem_by_name("ILENGTH_DEF"), get_theorem_by_name("LENGTH"))));
  thm suc1 = spec_rule(`LENGTH (t:(int)list)`, get_theorem_by_name("INT_OF_NUM_SUC"));
  thm comm = spec_rule(`&(LENGTH (t:(int)list))`, spec_rule(`1i:int`, get_theorem_by_name("INT_ADD_SYM")));
  thm step_eq = trans_rule(comm, suc1);
  CONV_WITH_ASMP_TAC(cases[1], rewrite_conv, THM_LIST(get_theorem_by_name("ILENGTH_DEF"), get_theorem_by_name("LENGTH"), step_eq));
  return gnode_prove(root);
}

/* !n v. 0i <= n ==> ilength (ireplicate n v) == n — closed stock. */
PROOF thm mk_ilength_ireplicate(void) {
  thm stock = ispec_rule(`(v:int)`, spec_rule(`(n:int)`, get_theorem_by_name("ILENGTH_IREPLICATE")));
  return close_implication(`!n (v:int). 0i <= n ==> ilength (ireplicate n v) == n`, undisch_rule(stock));
}

/* !v. ireplicate 0i v == [] */
PROOF thm mk_ireplicate_empty(void) {
  gnode root = gnode_new_with_ccl(`!v. ireplicate 0i v == []`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_TAC(leaf, rewrite_conv(THM_LIST(get_theorem_by_name("IREPLICATE_DEF"), get_theorem_by_name("NUM_OF_INT_OF_NUM"), get_theorem_by_name("REPLICATE"))));
  return gnode_prove(root);
}

/* !n v. 0i <= n ==>
 *          ireplicate (n + 1i) v == ireplicate n v ++ [v]
 * The snoc law is IREPLICATE_APPEND reoriented after discharging its
 * nonnegative-length premise. */
PROOF thm mk_ireplicate_snoc(void) {
  thm step = undisch_rule(ispec_rule(
      `(v:A)`,
      spec_rule(`n:int`, get_theorem_by_name("IREPLICATE_APPEND"))));
  return close_implication(
      `!(n:int) (v:A). 0i <= n ==>
         ireplicate (n + 1i) v == ireplicate n v ++ [v]`,
      sym_rule(step));
}

/* !n m v. 0i <= n ==> 0i <= m ==>
 *         ireplicate n v ++ ireplicate m v == ireplicate (n + m) v
 * Unfold both sides to REPLICATE, merge at the num level
 * (mk_replicate_append_num), bridge the lengths with NUM_OF_INT_ADD. */
PROOF thm mk_ireplicate_append2(void) {
  thm j1 = assume_rule(`0i <= (n:int)`);
  thm j2 = assume_rule(`0i <= (m:int)`);
  thm noa = spec_rule(`m:int`, spec_rule(`n:int`, get_theorem_by_name("NUM_OF_INT_ADD")));
  thm jadd = mp_rule(noa, conj_rule(j1, j2));
  thm ra = spec_rule(`(v:int)`, spec_rule(`num_of_int (m:int)`, spec_rule(`num_of_int (n:int)`, mk_replicate_append_num())));
  thm ra2 = conv_rule(rewrite_conv(THM_LIST(sym_rule(jadd))), ra);
  thm jl = apply_conversion(rewrite_conv(THM_LIST(get_theorem_by_name("IREPLICATE_DEF"))), `ireplicate (n:int) (v:int) ++ ireplicate (m:int) (v:int)`);
  thm jr = apply_conversion(rewrite_conv(THM_LIST(get_theorem_by_name("IREPLICATE_DEF"))), `ireplicate ((n:int) + m) (v:int)`);
  thm jfull = trans_rule(jl, trans_rule(ra2, sym_rule(jr)));
  return close_implication(`!n m (v:int). 0i <= n ==> 0i <= m ==> ireplicate n v ++ ireplicate m v == ireplicate (n + m) v`, jfull);
}

/* !l. sublist 0i 0i l == [] */
PROOF thm mk_sublist_empty(void) {
  gnode root = gnode_new_with_ccl(`!l. sublist 0i 0i (l:(int)list) == []`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_TAC(leaf, rewrite_conv(THM_LIST(get_theorem_by_name("SUBLIST_DEF"), get_theorem_by_name("NUM_OF_INT_OF_NUM"), get_theorem_by_name("FIRSTN_DEF"), get_theorem_by_name("SKIPN_DEF"))));
  return gnode_prove(root);
}

/* !n l. 0i <= n ==> n < ilength l ==>
 *        sublist 0i n l ++ [inth n l] == sublist 0i (n + 1i) l
 * The memcpy-invariant workhorse: extending a prefix by the next element.
 * Chain: n < ilength l -> n < &(LENGTH l) (ilength bridge) ->
 * num_of_int n < LENGTH l (int_lt bridge) -> FIRSTN-level snoc
 * (mk_firstn_snoc_num) -> SUC (num_of_int n) == num_of_int (n + 1i)
 * (mk_num_of_int_suc) -> unfold sublist/inth on both sides. */
PROOF thm mk_sublist_snoc(void) {
  thm h1 = assume_rule(`0i <= (n:int)`);
  thm h2 = assume_rule(`(n:int) < ilength (l:(int)list)`);
  thm h2_len = conv_rule(rewrite_conv(THM_LIST(mk_ilength_of_num_length())), h2);
  thm lt_inst = spec_rule(`LENGTH (l:(int)list)`, spec_rule(`n:int`, mk_int_lt_num_of_num()));
  thm lt_num = mp_rule(mp_rule(lt_inst, h1), h2_len);
  thm fs = spec_rule(`num_of_int (n:int)`, spec_rule(`(l:(int)list)`, mk_firstn_snoc_num()));
  thm fs_eq = mp_rule(fs, lt_num);
  thm suc_inst = mp_rule(spec_rule(`n:int`, mk_num_of_int_suc()), h1);
  thm fs_eq2 = conv_rule(rewrite_conv(THM_LIST(sym_rule(suc_inst))), fs_eq);
  thm side_l = apply_conversion(rewrite_conv(THM_LIST(mk_sublist_0_firstn(), mk_inth_nth())), `sublist 0i (n:int) (l:(int)list) ++ [inth n (l:(int)list)]`);
  thm side_r = apply_conversion(rewrite_conv(THM_LIST(mk_sublist_0_firstn())), `sublist 0i ((n:int) + 1i) (l:(int)list)`);
  thm eq_full = trans_rule(side_l, trans_rule(fs_eq2, sym_rule(side_r)));
  return close_implication(`!n (l:(int)list). 0i <= n ==> n < ilength l ==> sublist 0i n l ++ [inth n l] == sublist 0i (n + 1i) l`, eq_full);
}

/* !l. sublist 0i (ilength l) l == l — the full-length prefix is the list. */
PROOF thm mk_sublist_full(void) {
  gnode root = gnode_new_with_ccl(`!l. sublist 0i (ilength l) (l:(int)list) == l`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_TAC(leaf, rewrite_conv(THM_LIST(get_theorem_by_name("SUBLIST_DEF"), get_theorem_by_name("NUM_OF_INT_OF_NUM"), conjunct1_rule(get_theorem_by_name("SKIPN_DEF")), mk_ilength_of_num_length(), mk_firstn_full_num())));
  return gnode_prove(root);
}

/* !n l. 0i <= n ==> n <= ilength l ==> ilength (sublist 0i n l) == n
 * The prefix has exactly its index's length. Chain: n <= ilength l ->
 * num_of_int n <= LENGTH l -> LENGTH (FIRSTN (num_of_int n) l) ==
 * num_of_int n (mk_length_firstn_num) -> ilength == &(LENGTH) ->
 * &(num_of_int n) == n. */
PROOF thm mk_ilength_sublist(void) {
  thm g1 = assume_rule(`0i <= (n:int)`);
  thm g2 = assume_rule(`(n:int) <= ilength (l:(int)list)`);
  thm g2_len = conv_rule(rewrite_conv(THM_LIST(mk_ilength_of_num_length())), g2);
  thm le_inst = spec_rule(`LENGTH (l:(int)list)`, spec_rule(`n:int`, mk_int_le_num_of_num()));
  thm le_num = mp_rule(mp_rule(le_inst, g1), g2_len);
  thm lf = spec_rule(`(l:(int)list)`, spec_rule(`num_of_int (n:int)`, mk_length_firstn_num()));
  thm lf_eq = mp_rule(lf, le_num);
  thm u = apply_conversion(rewrite_conv(THM_LIST(mk_sublist_0_firstn(), mk_ilength_of_num_length())), `ilength (sublist 0i (n:int) (l:(int)list))`);
  thm w = conv_rule(rewrite_conv(THM_LIST(lf_eq)), u);
  thm ofn = mp_rule(spec_rule(`n:int`, get_theorem_by_name("INT_OF_NUM_OF_INT")), g1);
  thm len_full = trans_rule(w, ofn);
  return close_implication(`!n (l:(int)list). 0i <= n ==> n <= ilength l ==> ilength (sublist 0i n l) == n`, len_full);
}

/* !l. sublist (ilength l) (ilength l) l == [] — an empty window at the
 * list's own length (added for the memcpy exit, s2-4: the src tail's
 * window at iv == n must collapse to [] before the chunk vanishes via
 * array_at_zero). Closed, no side conditions. Chain: SUBLIST_DEF ->
 * num_of_int (ilength l) == LENGTH l (ilength bridge + NUM_OF_INT_OF_NUM)
 * -> FIRSTN (LENGTH l) l == l (mk_firstn_full_num) ->
 * SKIPN (LENGTH l) l == [] (ISKIPN_ILENGTH over ISKIPN_DEF). */
PROOF thm mk_sublist_self_empty(void) {
  thm iil = ispec_rule(`(l:(int)list)`, get_theorem_by_name("ISKIPN_ILENGTH"));
  thm idef = ispec_rule(`(l:(int)list)`, spec_rule(`ilength (l:(int)list)`, get_theorem_by_name("ISKIPN_DEF")));
  thm len_eq = apply_conversion(rewrite_conv(THM_LIST(mk_ilength_of_num_length(), get_theorem_by_name("NUM_OF_INT_OF_NUM"))), `num_of_int (ilength (l:(int)list))`);
  thm skip_eq = conv_rule(rewrite_conv(THM_LIST(len_eq)), idef);
  thm skipp = trans_rule(sym_rule(skip_eq), iil);
  gnode root = gnode_new_with_ccl(`!l. sublist (ilength l) (ilength l) (l:(int)list) == []`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode closed = CONV_TAC(leaf, rewrite_conv(THM_LIST(get_theorem_by_name("SUBLIST_DEF"), mk_ilength_of_num_length(), get_theorem_by_name("NUM_OF_INT_OF_NUM"), mk_firstn_full_num(), skipp)));
  return gnode_prove(root);
}

/*==========================================================================
  The named closed theorems (the library surface)
==========================================================================*/

PROOF thm ireplicate_empty = mk_ireplicate_empty();
PROOF thm ireplicate_snoc = mk_ireplicate_snoc();
PROOF thm ireplicate_append2 = mk_ireplicate_append2();
PROOF thm sublist_empty = mk_sublist_empty();
PROOF thm sublist_snoc = mk_sublist_snoc();
PROOF thm sublist_full = mk_sublist_full();
PROOF thm sublist_self_empty = mk_sublist_self_empty();
PROOF thm ilength_ireplicate = mk_ilength_ireplicate();
PROOF thm ilength_sublist = mk_ilength_sublist();
PROOF thm ilength_of_num_length = mk_ilength_of_num_length();
PROOF thm int_lt_num_of_num = mk_int_lt_num_of_num();
PROOF thm int_le_num_of_num = mk_int_le_num_of_num();
PROOF thm num_of_int_suc = mk_num_of_int_suc();
PROOF thm sublist_cons = mk_sublist_cons();
PROOF thm sublist_length = mk_sublist_length();
PROOF thm replace_inth_split = mk_replace_inth_split();
