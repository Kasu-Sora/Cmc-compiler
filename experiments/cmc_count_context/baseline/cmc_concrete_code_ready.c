#include "cmc_concrete_code_ready.h"
#require "cmc_concrete_program_ready.c"
#require "cmc_concrete_counts.c"

PROOF static size_t _cmc_code_ready_axioms_before =
    vector_size(get_all_axioms());

PROOF thm cm_concrete_structs_ready_def = new_fun_definition(
    `cm_concrete_structs_ready (p:cm_program) : bool =
       cm_rep_structs_safe (cm_program_structs p)`);
PROOF static int _e_cm_concrete_structs_ready =
    cst_add_const_to_header(`cm_concrete_structs_ready`);

PROOF static thm cm_slot_rep_positive(
    const term structs, const term slot, const thm slot_wf) {
  thm opened = conv_rule(rewrite_conv(THM_LIST(
      get_cm_slot_wf_def())), slot_wf);
  thm semantic_positive = conjunct1_rule(conjunct2_rule(
      conjunct2_rule(opened)));
  thm bridge = mp_rule(specl_rule(TERM_LIST(structs, slot),
      cm_rep_member_size_matches), slot_wf);
  return conv_rule(rewrite_conv(THM_LIST(sym_rule(bridge))),
      semantic_positive);
}

PROOF static thm cm_prove_slots_nonnegative(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (slots:(cm_slot_d)list).
         cm_slots_wf structs slots ==>
         0i <= cm_rep_members_size slots`);
  gnode with_structs = GEN_TAC(root, "structs");
  gnode_list cases = INDUCT_TAC(with_structs,
      `slots:(cm_slot_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_rep_members_size_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm slots_wf = assume_rule(
        `cm_slots_wf (structs:(cm_struct_d)list)
          ((a0:cm_slot_d) :: (a1:(cm_slot_d)list))`);
    thm head_wf = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`, `a0:cm_slot_d`,
        `a1:(cm_slot_d)list`), cm_slots_wf_head), slots_wf);
    thm tail_wf = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`, `a0:cm_slot_d`,
        `a1:(cm_slot_d)list`), cm_slots_wf_tail), slots_wf);
    thm head_positive = cm_slot_rep_positive(
        `structs:(cm_struct_d)list`, `a0:cm_slot_d`, head_wf);
    thm tail_nonnegative = mp_rule(assume_rule(
        `cm_slots_wf (structs:(cm_struct_d)list)
           (a1:(cm_slot_d)list) ==>
         0i <= cm_rep_members_size a1`), tail_wf);
    thm sum = mp_rule(mp_rule(int_arith_rule(
        `0i < cm_rep_member_size (a0:cm_slot_d) ==>
         0i <= cm_rep_members_size (a1:(cm_slot_d)list) ==>
         0i <= cm_rep_member_size a0 + cm_rep_members_size a1`),
        head_positive), tail_nonnegative);
    thm view = apply_conversion(rewrite_conv(THM_LIST(
        get_cm_rep_members_size_def())),
        `0i <= cm_rep_members_size
          ((a0:cm_slot_d) :: (a1:(cm_slot_d)list))`);
    ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(view), sum));
  }
  return gnode_prove(root);
}
PROOF static thm cm_slots_nonnegative =
    cm_prove_slots_nonnegative();

PROOF static thm cm_prove_slots_safe(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (slots:(cm_slot_d)list).
         cm_slots_wf structs slots ==>
         cm_rep_members_size slots <= 1048576i ==>
         cm_rep_members_safe slots`);
  gnode with_structs = GEN_TAC(root, "structs");
  gnode_list cases = INDUCT_TAC(with_structs,
      `slots:(cm_slot_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_rep_members_safe_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm slots_wf = assume_rule(
        `cm_slots_wf (structs:(cm_struct_d)list)
          ((a0:cm_slot_d) :: (a1:(cm_slot_d)list))`);
    thm full_bound = assume_rule(
        `cm_rep_members_size
          ((a0:cm_slot_d) :: (a1:(cm_slot_d)list)) <= 1048576i`);
    thm head_wf = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`, `a0:cm_slot_d`,
        `a1:(cm_slot_d)list`), cm_slots_wf_head), slots_wf);
    thm tail_wf = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`, `a0:cm_slot_d`,
        `a1:(cm_slot_d)list`), cm_slots_wf_tail), slots_wf);
    thm head_positive = cm_slot_rep_positive(
        `structs:(cm_struct_d)list`, `a0:cm_slot_d`, head_wf);
    thm head_nonnegative = mp_rule(int_arith_rule(
        `0i < cm_rep_member_size (a0:cm_slot_d) ==>
         0i <= cm_rep_member_size a0`), head_positive);
    thm tail_nonnegative = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`, `a1:(cm_slot_d)list`),
        cm_slots_nonnegative), tail_wf);
    thm unfolded_bound = conv_rule(rewrite_conv(THM_LIST(
        get_cm_rep_members_size_def())), full_bound);
    thm tail_bound = mp_rule(mp_rule(int_arith_rule(
        `0i <= cm_rep_member_size (a0:cm_slot_d) ==>
         cm_rep_member_size a0 +
           cm_rep_members_size (a1:(cm_slot_d)list) <= 1048576i ==>
         cm_rep_members_size a1 <= 1048576i`),
        head_nonnegative), unfolded_bound);
    thm tail_safe = mp_rule(mp_rule(assume_rule(
        `cm_slots_wf (structs:(cm_struct_d)list)
           (a1:(cm_slot_d)list) ==>
         cm_rep_members_size a1 <= 1048576i ==>
         cm_rep_members_safe a1`), tail_wf), tail_bound);
    thm parts = conj_rule(head_nonnegative,
        conj_rule(tail_nonnegative,
          conj_rule(full_bound, tail_safe)));
    thm view = apply_conversion(rewrite_conv(THM_LIST(
        get_cm_rep_members_safe_def())),
        `cm_rep_members_safe
          ((a0:cm_slot_d) :: (a1:(cm_slot_d)list))`);
    ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(view), parts));
  }
  return gnode_prove(root);
}
PROOF static thm cm_slots_safe = cm_prove_slots_safe();
PROOF thm get_cm_slots_nonnegative(void) {
  return cm_slots_nonnegative;
}
PROOF thm get_cm_slots_safe(void) {
  return cm_slots_safe;
}


PROOF static thm cm_prove_structs_wf_head(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (head:cm_struct_d)
          (tail:(cm_struct_d)list).
         (!i. 0i <= i ==> i < ilength (head :: tail) ==>
              cm_struct_wf structs (inth i (head :: tail))) ==>
         cm_struct_wf structs head`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm all_wf = assume_rule(
      `!i. 0i <= i ==>
         i < ilength ((head:cm_struct_d) ::
           (tail:(cm_struct_d)list)) ==>
         cm_struct_wf (structs:(cm_struct_d)list)
           (inth i (head :: tail))`);
  thm tail_nonnegative = ispec_rule(
      `tail:(cm_struct_d)list`, get_theorem_by_name("ILENGTH_NONNEG"));
  thm head_bound = by_defs_arith(
      `0i < ilength
        ((head:cm_struct_d) :: (tail:(cm_struct_d)list))`,
      THM_LIST(get_theorem_by_name("ILENGTH_DEF")),
      THM_LIST(tail_nonnegative));
  thm result = match_mp_rule(match_mp_rule(
      spec_rule(`0i`, all_wf), int_arith_rule(`0i <= 0i`)),
      head_bound);
  ACCEPT_TAC(leaf, conv_rule(rewrite_conv(THM_LIST(
      ispecl_rule(TERM_LIST(`head:cm_struct_d`,
        `tail:(cm_struct_d)list`), cm_inth_zero_cons))), result));
  return gnode_prove(root);
}
PROOF static thm cm_structs_wf_head = cm_prove_structs_wf_head();

PROOF static thm cm_prove_structs_wf_tail(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (head:cm_struct_d)
          (tail:(cm_struct_d)list).
         (!i. 0i <= i ==> i < ilength (head :: tail) ==>
              cm_struct_wf structs (inth i (head :: tail))) ==>
         (!i. 0i <= i ==> i < ilength tail ==>
              cm_struct_wf structs (inth i tail))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm all_wf = assume_rule(
      `!i. 0i <= i ==>
         i < ilength ((head:cm_struct_d) ::
           (tail:(cm_struct_d)list)) ==>
         cm_struct_wf (structs:(cm_struct_d)list)
           (inth i (head :: tail))`);
  thm lower = assume_rule(`0i <= (i:int)`);
  thm upper = assume_rule(
      `(i:int) < ilength (tail:(cm_struct_d)list)`);
  thm full_lower = mp_rule(int_arith_rule(
      `0i <= (i:int) ==> 0i <= i + 1i`), lower);
  thm normalized_upper = mp_rule(int_arith_rule(mk_imp(
      concl(upper),
      `(i:int) + 1i < 1i + ilength (tail:(cm_struct_d)list)`)),
      upper);
  thm full_upper = eq_mp_rule(sym_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_theorem_by_name("ILENGTH_DEF"))),
      `(i:int) + 1i < ilength
        ((head:cm_struct_d) :: (tail:(cm_struct_d)list))`)),
      normalized_upper);
  thm full_wf = match_mp_rule(match_mp_rule(
      spec_rule(`(i:int) + 1i`, all_wf), full_lower), full_upper);
  thm one = mp_rule(int_arith_rule(
      `0i <= (i:int) ==> 1i <= i + 1i`), lower);
  thm at_tail = mp_rule(ispecl_rule(TERM_LIST(
      `head:cm_struct_d`, `tail:(cm_struct_d)list`,
      `(i:int) + 1i`), cm_inth_cons_tail), one);
  thm index_exact = int_arith_rule(`((i:int) + 1i) - 1i == i`);
  ACCEPT_TAC(leaf, conv_rule(reduce_rewrite_conv(
      THM_LIST(at_tail, index_exact)), full_wf));
  return gnode_prove(root);
}
PROOF static thm cm_structs_wf_tail = cm_prove_structs_wf_tail();

PROOF static thm cm_prove_structs_safe(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (items:(cm_struct_d)list).
         (!i. 0i <= i ==> i < ilength items ==>
              cm_struct_wf structs (inth i items)) ==>
         cm_rep_structs_safe items`);
  gnode with_structs = GEN_TAC(root, "structs");
  gnode_list cases = INDUCT_TAC(with_structs,
      `items:(cm_struct_d)list`);
  {
    gnode base = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(base, reduce_rewrite_conv(THM_LIST(
        get_cm_rep_structs_safe_def())));
  }
  {
    gnode step = AUTO_INTROS_TAC(cases[1]);
    thm all_wf = assume_rule(
        `!i. 0i <= i ==>
           i < ilength ((a0:cm_struct_d) ::
             (a1:(cm_struct_d)list)) ==>
           cm_struct_wf (structs:(cm_struct_d)list)
             (inth i (a0 :: a1))`);
    thm head_wf = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`,
        `a0:cm_struct_d`, `a1:(cm_struct_d)list`),
        cm_structs_wf_head), all_wf);
    thm tail_wf = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`,
        `a0:cm_struct_d`, `a1:(cm_struct_d)list`),
        cm_structs_wf_tail), all_wf);
    thm opened_head = conv_rule(rewrite_conv(THM_LIST(
        get_cm_struct_wf_def())), head_wf);
    thm members_wf = conjunct1_rule(conjunct2_rule(opened_head));
    thm members_upper = conjunct2_rule(conjunct2_rule(
        conjunct2_rule(opened_head)));
    thm members_bridge = mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`,
        `cm_struct_members (a0:cm_struct_d)`),
        cm_rep_struct_members_size_matches), members_wf);
    thm concrete_upper = conv_rule(rewrite_conv(THM_LIST(
        sym_rule(members_bridge))), members_upper);
    thm members_safe = mp_rule(mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`,
        `cm_struct_members (a0:cm_struct_d)`), cm_slots_safe),
        members_wf), concrete_upper);
    thm tail_safe = mp_rule(assume_rule(
        `(!i. 0i <= i ==>
             i < ilength (a1:(cm_struct_d)list) ==>
             cm_struct_wf (structs:(cm_struct_d)list)
               (inth i a1)) ==>
         cm_rep_structs_safe a1`), tail_wf);
    thm parts = conj_rule(members_safe, tail_safe);
    thm view = apply_conversion(rewrite_conv(THM_LIST(
        get_cm_rep_structs_safe_def())),
        `cm_rep_structs_safe
          ((a0:cm_struct_d) :: (a1:(cm_struct_d)list))`);
    ACCEPT_TAC(step, eq_mp_rule(sym_rule(view), parts));
  }
  return gnode_prove(root);
}
PROOF static thm cm_structs_safe = cm_prove_structs_safe();

PROOF static thm cm_prove_structs_ready_from_typed(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program).
         cm_typed_program p ==> cm_concrete_structs_ready p`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm typed = assume_rule(`cm_typed_program (p:cm_program)`);
  thm opened = conv_rule(rewrite_conv(THM_LIST(
      get_cm_typed_program_def())), typed);
  thm all_wf = mp_rule(taut_rule(mk_imp(concl(opened),
      `!i. 0i <= i ==>
         i < ilength (cm_program_structs (p:cm_program)) ==>
         cm_struct_wf (cm_program_structs p)
           (inth i (cm_program_structs p))`)), opened);
  thm safe = mp_rule(specl_rule(TERM_LIST(
      `cm_program_structs (p:cm_program)`,
      `cm_program_structs (p:cm_program)`), cm_structs_safe), all_wf);
  thm view = apply_conversion(rewrite_conv(THM_LIST(
      cm_concrete_structs_ready_def)),
      `cm_concrete_structs_ready (p:cm_program)`);
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(view), safe));
  return gnode_prove(root);
}
PROOF thm cmc_structs_ready_from_typed =
    cm_prove_structs_ready_from_typed();

PROOF thm get_cm_concrete_structs_ready_def(void) {
  return cm_concrete_structs_ready_def;
}
PROOF thm get_cmc_structs_ready_from_typed(void) {
  return cmc_structs_ready_from_typed;
}

PROOF static int _cmc_code_ready_no_axioms =
    vector_size(get_all_axioms()) == _cmc_code_ready_axioms_before
        ? 1 : (abort(), 0);
