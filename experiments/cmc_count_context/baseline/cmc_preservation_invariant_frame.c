#include "proof/proof.h"
#include "userlib/proof.h"
#include "cmc_preservation_invariant_frame.h"
#include "cmc_stack.h"

#require "cmc_preservation_invariant_step.c"

PROOF static size_t _cmc_preservation_invariant_frame_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_frame_assumption(gnode node, term wanted) {
  labeled_term_list assumptions = goal_lasmps(node->g);
  for (size_t index = 0; index < vector_size(assumptions); ++index) {
    if (alpha_compare(assumptions[index].tm, wanted) == 0) {
      return assume_rule(assumptions[index].tm);
    }
  }
  ENSURE_COND(false, "missing frame proof assumption: %s in %s",
      cstr_term(wanted), cstr_gnode(node));
err:
  return empty_theorem;
}

PROOF thm cm_slot_sizes_positive_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!structs.
        cm_slot_sizes_positive (structs:(cm_struct_d)list)
          ([]:(cm_slot_d)list) <=> T) &&
     (!structs slot rest.
        cm_slot_sizes_positive structs
          ((slot:cm_slot_d) :: (rest:(cm_slot_d)list)) <=>
        0i < cm_slot_size structs slot &&
        cm_slot_sizes_positive structs rest)`);

PROOF static thm cm_prove_slot_sizes_positive_total(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (slots:(cm_slot_d)list).
         cm_slot_sizes_positive structs slots ==>
         0i <= cm_slots_size structs slots`);
  gnode with_structs = GEN_TAC(root, "structs");
  gnode_list cases = INDUCT_TAC(with_structs, `slots:(cm_slot_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_slots_size_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm positive = conv_rule(rewrite_conv(THM_LIST(
        cm_slot_sizes_positive_def)), assume_rule(
          `cm_slot_sizes_positive
            (structs:(cm_struct_d)list)
            ((a0:cm_slot_d) :: (a1:(cm_slot_d)list))`));
    thm tail_nonnegative = match_mp_rule(
        cm_frame_assumption(leaf,
          `cm_slot_sizes_positive
             (structs:(cm_struct_d)list)
             (a1:(cm_slot_d)list) ==>
           0i <= cm_slots_size structs a1`),
        conjunct2_rule(positive));
    gnode reduced = CONV_TAC(leaf, rewrite_conv(THM_LIST(
        get_cm_slots_size_def())));
    thm inputs = conj_rule(conjunct1_rule(positive), tail_nonnegative);
    ACCEPT_TAC(reduced, mp_rule(int_arith_rule(mk_imp(
        concl(inputs), goal_ccl(reduced->g))), inputs));
  }
  return gnode_prove(root);
}
PROOF thm cm_slot_sizes_positive_total =
    cm_prove_slot_sizes_positive_total();

PROOF static thm cm_prove_slots_prefix_cell_bounds(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (slots:(cm_slot_d)list).
         cm_slot_sizes_positive structs slots ==>
         !index. 0i <= index ==> index < ilength slots ==>
           0i <= cm_slots_prefix structs slots index &&
           cm_slots_prefix structs slots index +
             cm_slot_size structs (inth index slots) <=
           cm_slots_size structs slots`);
  gnode with_structs = GEN_TAC(root, "structs");
  gnode_list cases = INDUCT_TAC(with_structs, `slots:(cm_slot_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(
        THM_LIST(get_theorem_by_name("ILENGTH_DEF"))),
        assume_rule(`(index:int) < ilength ([]:(cm_slot_d)list)`));
    CONTR_TAC(leaf, mp_rule(mp_rule(
        int_arith_rule(`0i <= (index:int) ==> index < 0i ==> F`),
        assume_rule(`0i <= (index:int)`)), impossible));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm positive = conv_rule(rewrite_conv(THM_LIST(
        cm_slot_sizes_positive_def)), assume_rule(
          `cm_slot_sizes_positive
            (structs:(cm_struct_d)list)
            ((a0:cm_slot_d) :: (a1:(cm_slot_d)list))`));
    thm tail_total = match_mp_rule(specl_rule(TERM_LIST(
        `structs:(cm_struct_d)list`, `a1:(cm_slot_d)list`),
        cm_slot_sizes_positive_total), conjunct2_rule(positive));
    gnode_list zero_cases = BOOL_CASES_TAC(
        leaf, `(index:int) == 0i`, "Hslot_index_zero");
    {
      thm zero = assume_rule(`(index:int) == 0i`);
      thm at_zero = ispecl_rule(TERM_LIST(
          `a0:cm_slot_d`, `a1:(cm_slot_d)list`), cm_inth_zero_cons);
      gnode reduced = CONV_WITH_ASMP_TAC(
          zero_cases[0], reduce_rewrite_conv,
          THM_LIST(get_cm_slots_prefix_def(), get_cm_slots_size_def(),
            zero, at_zero));
      thm inputs = conj_rule(conjunct1_rule(positive), tail_total);
      ACCEPT_TAC(reduced, mp_rule(int_arith_rule(mk_imp(
          concl(inputs), goal_ccl(reduced->g))), inputs));
    }
    {
      thm not_zero = assume_rule(`~((index:int) == 0i)`);
      thm index_nonnegative = assume_rule(`0i <= (index:int)`);
      thm one_le = mp_rule(mp_rule(int_arith_rule(
          `0i <= (index:int) ==> ~((index:int) == 0i) ==>
           1i <= index`), index_nonnegative), not_zero);
      thm normalized_bound = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_theorem_by_name("ILENGTH_DEF"))), assume_rule(
            `(index:int) < ilength
              ((a0:cm_slot_d) :: (a1:(cm_slot_d)list))`));
      thm bound_inputs = conj_rule(one_le, normalized_bound);
      thm tail_bounds = mp_rule(int_arith_rule(mk_imp(
          concl(bound_inputs),
          `0i <= (index:int) - 1i &&
           index - 1i < ilength (a1:(cm_slot_d)list)`)),
          bound_inputs);
      thm ih = spec_rule(`(index:int) - 1i`, match_mp_rule(
          cm_frame_assumption(zero_cases[1],
            `cm_slot_sizes_positive
               (structs:(cm_struct_d)list) (a1:(cm_slot_d)list) ==>
             !tail_index.
               0i <= tail_index ==>
               tail_index < ilength a1 ==>
               0i <= cm_slots_prefix structs a1 tail_index &&
               cm_slots_prefix structs a1 tail_index +
                 cm_slot_size structs (inth tail_index a1) <=
               cm_slots_size structs a1`),
          conjunct2_rule(positive)));
      thm tail_result = match_mp_rule(match_mp_rule(
          ih, conjunct1_rule(tail_bounds)), conjunct2_rule(tail_bounds));
      thm at_tail = mp_rule(ispecl_rule(TERM_LIST(
          `a0:cm_slot_d`, `a1:(cm_slot_d)list`, `index:int`),
          cm_inth_cons_tail), one_le);
      gnode reduced = CONV_WITH_ASMP_TAC(
          zero_cases[1], reduce_rewrite_conv,
          THM_LIST(get_cm_slots_prefix_def(), get_cm_slots_size_def(),
            not_zero, at_tail));
      thm inputs = conj_rule(conjunct1_rule(positive), tail_result);
      ACCEPT_TAC(reduced, mp_rule(int_arith_rule(mk_imp(
          concl(inputs), goal_ccl(reduced->g))), inputs));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_slots_prefix_cell_bounds =
    cm_prove_slots_prefix_cell_bounds();

PROOF static thm cm_prove_slots_wf_sizes_positive(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (slots:(cm_slot_d)list).
         cm_slots_wf structs slots ==>
         cm_slot_sizes_positive structs slots`);
  gnode with_structs = GEN_TAC(root, "structs");
  gnode_list cases = INDUCT_TAC(with_structs, `slots:(cm_slot_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, rewrite_conv(THM_LIST(cm_slot_sizes_positive_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm all_wf = conv_rule(rewrite_conv(THM_LIST(
        get_cm_slots_wf_def())), assume_rule(
          `cm_slots_wf (structs:(cm_struct_d)list)
            ((a0:cm_slot_d) :: (a1:(cm_slot_d)list))`));
    thm tail_length_nonnegative = ispec_rule(
        `a1:(cm_slot_d)list`, get_theorem_by_name("ILENGTH_NONNEG"));
    thm head_bound = by_defs_arith(
        `0i < ilength ((a0:cm_slot_d) :: (a1:(cm_slot_d)list))`,
        THM_LIST(get_theorem_by_name("ILENGTH_DEF")),
        THM_LIST(tail_length_nonnegative));
    thm head_wf = match_mp_rule(match_mp_rule(
        spec_rule(`0i`, all_wf), int_arith_rule(`0i <= 0i`)),
        head_bound);
    head_wf = conv_rule(rewrite_conv(THM_LIST(ispecl_rule(TERM_LIST(
        `a0:cm_slot_d`, `a1:(cm_slot_d)list`), cm_inth_zero_cons))),
        head_wf);
    thm head_open = conv_rule(rewrite_conv(THM_LIST(
        get_cm_slot_wf_def())), head_wf);
    thm head_positive = mp_rule(taut_rule(mk_imp(concl(head_open),
        `0i < cm_slot_size (structs:(cm_struct_d)list)
          (a0:cm_slot_d)`)), head_open);
    gnode reduced = CONV_TAC(leaf, rewrite_conv(THM_LIST(
        cm_slot_sizes_positive_def)));
    gnode_list parts = CONJ_TAC(reduced);
    ACCEPT_TAC(parts[0], head_positive);
    thm ih = cm_frame_assumption(parts[1],
        `cm_slots_wf (structs:(cm_struct_d)list)
           (a1:(cm_slot_d)list) ==>
         cm_slot_sizes_positive structs a1`);
    gnode tail_wf_goal = MATCH_MP_TAC(parts[1], ih);
    gnode opened_tail = CONV_TAC(tail_wf_goal, rewrite_conv(THM_LIST(
        get_cm_slots_wf_def())));
    gnode with_index = GEN_TAC(opened_tail, "tail_index");
    gnode tail_leaf = AUTO_INTROS_TAC(with_index);
    thm tail_nonnegative = assume_rule(`0i <= (tail_index:int)`);
    thm tail_upper = assume_rule(
        `(tail_index:int) < ilength (a1:(cm_slot_d)list)`);
    thm full_lower = mp_rule(int_arith_rule(
        `0i <= (tail_index:int) ==> 0i <= tail_index + 1i`),
        tail_nonnegative);
    thm normalized_full_upper = mp_rule(int_arith_rule(mk_imp(
        concl(tail_upper),
        `(tail_index:int) + 1i <
         1i + ilength (a1:(cm_slot_d)list)`)), tail_upper);
    thm full_upper = eq_mp_rule(sym_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(get_theorem_by_name("ILENGTH_DEF"))),
        `(tail_index:int) + 1i < ilength
          ((a0:cm_slot_d) :: (a1:(cm_slot_d)list))`)),
        normalized_full_upper);
    thm full_wf = match_mp_rule(match_mp_rule(
        spec_rule(`(tail_index:int) + 1i`, all_wf), full_lower),
        full_upper);
    thm one = mp_rule(int_arith_rule(
        `0i <= (tail_index:int) ==> 1i <= tail_index + 1i`),
        tail_nonnegative);
    thm at_tail = mp_rule(ispecl_rule(TERM_LIST(
        `a0:cm_slot_d`, `a1:(cm_slot_d)list`,
        `(tail_index:int) + 1i`), cm_inth_cons_tail), one);
    thm index_exact = int_arith_rule(
        `((tail_index:int) + 1i) - 1i == tail_index`);
    ACCEPT_TAC(tail_leaf, conv_rule(reduce_rewrite_conv(
        THM_LIST(at_tail, index_exact)), full_wf));
  }
  return gnode_prove(root);
}
PROOF thm cm_slots_wf_sizes_positive =
    cm_prove_slots_wf_sizes_positive();


PROOF static thm cm_prove_slot_region_member_index(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (slots:(cm_slot_d)list).
         !gen base region.
           MEM region (cm_regions_for_slots structs slots gen base) ==>
           ?offset.
             0i <= offset &&
             offset < ilength slots &&
             region ==
               CMRegion
                 (gen + offset)
                 (base + cm_slots_prefix structs slots offset)
                 0i (cm_slot_size structs (inth offset slots)) T T`);
  gnode with_structs = GEN_TAC(root, "structs");
  gnode_list cases = INDUCT_TAC(
      with_structs, `slots:(cm_slot_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_regions_for_slots_def(),
        get_theorem_by_name("MEM"))), assume_rule(
          `MEM (region:cm_region)
            (cm_regions_for_slots
              (structs:(cm_struct_d)list)
              ([]:(cm_slot_d)list) (gen:int) (base:int))`));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm member = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_regions_for_slots_def(),
        get_theorem_by_name("MEM"))), assume_rule(
          `MEM (region:cm_region)
            (cm_regions_for_slots
              (structs:(cm_struct_d)list)
              ((a0:cm_slot_d) :: (a1:(cm_slot_d)list))
              (gen:int) (base:int))`));
    dest_disj_results parts = dest_disj(concl(member));
    thm head_equal = assume_rule(parts.tm1);
    thm tail_length_nonnegative = ispec_rule(
        `a1:(cm_slot_d)list`, get_theorem_by_name("ILENGTH_NONNEG"));
    thm head_at = ispecl_rule(TERM_LIST(
        `a0:cm_slot_d`, `a1:(cm_slot_d)list`), cm_inth_zero_cons);
    thm gen_zero = int_arith_rule(
        `(gen:int) + 0i == gen`);
    thm base_zero = int_arith_rule(
        `(base:int) + 0i == base`);
    term wanted =
        `?offset.
           0i <= offset &&
           offset <
             ilength ((a0:cm_slot_d) :: (a1:(cm_slot_d)list)) &&
           (region:cm_region) ==
             CMRegion
               ((gen:int) + offset)
               ((base:int) +
                 cm_slots_prefix (structs:(cm_struct_d)list)
                   (a0 :: a1) offset)
               0i (cm_slot_size structs (inth offset (a0 :: a1)))
               T T`;
    thm head_body = by_defs_arith(
        `0i <= 0i &&
         0i <
           ilength ((a0:cm_slot_d) :: (a1:(cm_slot_d)list)) &&
         (region:cm_region) ==
           CMRegion
             ((gen:int) + 0i)
             ((base:int) +
               cm_slots_prefix (structs:(cm_struct_d)list)
                 (a0 :: a1) 0i)
             0i (cm_slot_size structs (inth 0i (a0 :: a1))) T T`,
        THM_LIST(get_theorem_by_name("ILENGTH_DEF"),
          get_cm_slots_prefix_def(), head_at,
          gen_zero, base_zero, head_equal),
        THM_LIST(tail_length_nonnegative));
    thm head_result = exists_rule(wanted, `0i`, head_body);

    thm ih = specl_rule(TERM_LIST(
        `(gen:int) + 1i`,
        `(base:int) + cm_slot_size
          (structs:(cm_struct_d)list) (a0:cm_slot_d)`,
        `region:cm_region`), cm_frame_assumption(leaf,
          `!next_gen next_base candidate.
             MEM candidate
               (cm_regions_for_slots
                 (structs:(cm_struct_d)list)
                 (a1:(cm_slot_d)list) next_gen next_base) ==>
             ?offset.
               0i <= offset &&
               offset < ilength a1 &&
               candidate ==
                 CMRegion
                   (next_gen + offset)
                   (next_base +
                     cm_slots_prefix structs a1 offset)
                   0i
                   (cm_slot_size structs (inth offset a1)) T T`));
    thm tail_exists = match_mp_rule(
        ih, assume_rule(parts.tm2));
    term tail_body_term =
        `0i <= (offset:int) &&
         offset < ilength (a1:(cm_slot_d)list) &&
         (region:cm_region) ==
           CMRegion
             (((gen:int) + 1i) + offset)
             (((base:int) + cm_slot_size
                 (structs:(cm_struct_d)list) (a0:cm_slot_d)) +
               cm_slots_prefix structs a1 offset)
             0i (cm_slot_size structs (inth offset a1)) T T`;
    thm tail_body = assume_rule(tail_body_term);
    thm offset_lower = mp_rule(taut_rule(mk_imp(
        concl(tail_body), `0i <= (offset:int)`)), tail_body);
    thm offset_upper = mp_rule(taut_rule(mk_imp(
        concl(tail_body),
        `(offset:int) < ilength (a1:(cm_slot_d)list)`)), tail_body);
    thm region_equal = mp_rule(taut_rule(mk_imp(
        concl(tail_body),
        `(region:cm_region) ==
          CMRegion
            (((gen:int) + 1i) + offset)
            (((base:int) + cm_slot_size
                (structs:(cm_struct_d)list) (a0:cm_slot_d)) +
              cm_slots_prefix structs a1 offset)
            0i (cm_slot_size structs (inth offset a1)) T T`)),
        tail_body);
    thm new_lower = mp_rule(int_arith_rule(
        `0i <= (offset:int) ==> 0i <= offset + 1i`), offset_lower);
    thm new_upper = by_defs_arith(
        `(offset:int) + 1i <
          ilength ((a0:cm_slot_d) :: (a1:(cm_slot_d)list))`,
        THM_LIST(get_theorem_by_name("ILENGTH_DEF")),
        THM_LIST(offset_upper));
    thm one = mp_rule(int_arith_rule(
        `0i <= (offset:int) ==> 1i <= offset + 1i`), offset_lower);
    thm at_tail = mp_rule(ispecl_rule(TERM_LIST(
        `a0:cm_slot_d`, `a1:(cm_slot_d)list`,
        `(offset:int) + 1i`), cm_inth_cons_tail), one);
    thm offset_exact = int_arith_rule(
        `((offset:int) + 1i) - 1i == offset`);
    at_tail = conv_rule(reduce_rewrite_conv(
        THM_LIST(offset_exact)), at_tail);
    thm not_zero = mp_rule(int_arith_rule(
        `0i <= (offset:int) ==>
         ~((offset + 1i) == 0i)`), offset_lower);
    thm prefix_at = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_slots_prefix_def(), not_zero, offset_exact)),
        `cm_slots_prefix (structs:(cm_struct_d)list)
          ((a0:cm_slot_d) :: (a1:(cm_slot_d)list))
          ((offset:int) + 1i)`);
    thm base_assoc = int_ring_rule(
        `((base:int) + cm_slot_size
            (structs:(cm_struct_d)list) (a0:cm_slot_d)) +
           cm_slots_prefix structs (a1:(cm_slot_d)list) (offset:int) ==
         base +
           (cm_slot_size structs a0 +
             cm_slots_prefix structs a1 offset)`);
    thm base_cong = beta_norm(ap_term_rule(
        `\amount:int. (base:int) + amount`,
        sym_rule(prefix_at)));
    thm base_exact = trans_rule(base_assoc, base_cong);
    thm index_exact = int_ring_rule(
        `((gen:int) + 1i) + (offset:int) ==
         gen + (offset + 1i)`);
    thm new_equal = conv_rule(rewrite_conv(THM_LIST(
        index_exact, base_exact, sym_rule(at_tail))), region_equal);
    thm new_body = conj_rule(new_lower,
        conj_rule(new_upper, new_equal));
    thm tail_witness = exists_rule(
        wanted, `(offset:int) + 1i`, new_body);
    thm tail_result = choose_rule(
        `offset:int`, tail_exists, tail_witness);
    ACCEPT_TAC(leaf,
        disj_cases_rule(member, head_result, tail_result));
  }
  return gnode_prove(root);
}
PROOF thm cm_slot_region_member_index =
    cm_prove_slot_region_member_index();

PROOF static thm cm_prove_slot_region_base_lookup(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (slots:(cm_slot_d)list).
         !gen base old region.
           cm_regions_before old gen ==>
           MEM region (cm_regions_for_slots structs slots gen base) ==>
           cm_region_base
             (cm_regions_for_slots structs slots gen base ++ old)
             (cm_region_gen region) ==
           cm_region_base_field region`);
  gnode with_structs = GEN_TAC(root, "structs");
  gnode_list cases = INDUCT_TAC(
      with_structs, `slots:(cm_slot_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_regions_for_slots_def(),
        get_theorem_by_name("MEM"))), assume_rule(
          `MEM (region:cm_region)
            (cm_regions_for_slots
              (structs:(cm_struct_d)list)
              ([]:(cm_slot_d)list) (gen:int) (base:int))`));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm before = assume_rule(
        `cm_regions_before (old:(cm_region)list) (gen:int)`);
    thm member = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_regions_for_slots_def(),
        get_theorem_by_name("MEM"))), assume_rule(
          `MEM (region:cm_region)
            (cm_regions_for_slots
              (structs:(cm_struct_d)list)
              ((a0:cm_slot_d) :: (a1:(cm_slot_d)list))
              (gen:int) (base:int))`));
    dest_disj_results parts = dest_disj(concl(member));
    thm head_equal = assume_rule(parts.tm1);
    term head_region =
        `CMRegion (gen:int) (base:int) 0i
          (cm_slot_size (structs:(cm_struct_d)list)
            (a0:cm_slot_d)) T T`;
    thm head_lookup = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_regions_for_slots_def(),
          get_cm_region_base_def(),
          get_theorem_by_name("APPEND"))),
        `cm_region_base
           (cm_regions_for_slots
              (structs:(cm_struct_d)list)
              ((a0:cm_slot_d) :: (a1:(cm_slot_d)list))
              (gen:int) (base:int) ++ (old:(cm_region)list))
           (cm_region_gen ${head_region:cm_region}) ==
         cm_region_base_field ${head_region:cm_region}`));
    thm head_transport = beta_norm(ap_term_rule(
        `\candidate:cm_region.
           cm_region_base
             (cm_regions_for_slots
                (structs:(cm_struct_d)list)
                ((a0:cm_slot_d) :: (a1:(cm_slot_d)list))
                (gen:int) (base:int) ++ (old:(cm_region)list))
             (cm_region_gen candidate) ==
           cm_region_base_field candidate`,
        sym_rule(head_equal)));
    thm head_result = eq_mp_rule(
        head_transport, head_lookup);

    thm next_before = match_mp_rule(match_mp_rule(
        specl_rule(TERM_LIST(
          `old:(cm_region)list`, `gen:int`, `(gen:int) + 1i`),
          cm_regions_before_mono), before),
        int_arith_rule(`(gen:int) <= gen + 1i`));
    thm tail_member = assume_rule(parts.tm2);
    thm ih = specl_rule(TERM_LIST(
        `(gen:int) + 1i`,
        `(base:int) + cm_slot_size
          (structs:(cm_struct_d)list) (a0:cm_slot_d)`,
        `old:(cm_region)list`, `region:cm_region`),
        cm_frame_assumption(leaf,
          `!next_gen next_base remaining candidate.
             cm_regions_before remaining next_gen ==>
             MEM candidate
               (cm_regions_for_slots
                 (structs:(cm_struct_d)list)
                 (a1:(cm_slot_d)list) next_gen next_base) ==>
             cm_region_base
               (cm_regions_for_slots structs a1
                  next_gen next_base ++ remaining)
               (cm_region_gen candidate) ==
             cm_region_base_field candidate`));
    thm tail_lookup = match_mp_rule(match_mp_rule(
        ih, next_before), tail_member);
    thm tail_gen_lower = match_mp_rule(
        specl_rule(TERM_LIST(
          `structs:(cm_struct_d)list`, `a1:(cm_slot_d)list`,
          `(gen:int) + 1i`,
          `(base:int) + cm_slot_size structs (a0:cm_slot_d)`,
          `region:cm_region`),
          cm_regions_for_slots_gen_lower), tail_member);
    thm head_distinct = mp_rule(int_arith_rule(
        `(gen:int) + 1i <= cm_region_gen (region:cm_region) ==>
         ~((gen:int) == cm_region_gen region)`), tail_gen_lower);
    thm lookup_step = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_regions_for_slots_def(),
          get_cm_region_base_def(),
          get_theorem_by_name("APPEND"),
          get_cm_region_gen_def(),
          get_cm_region_base_field_def(),
          head_distinct)),
        `cm_region_base
           (cm_regions_for_slots
              (structs:(cm_struct_d)list)
              ((a0:cm_slot_d) :: (a1:(cm_slot_d)list))
              (gen:int) (base:int) ++ (old:(cm_region)list))
           (cm_region_gen (region:cm_region))`);
    thm tail_result = trans_rule(
        lookup_step, tail_lookup);
    ACCEPT_TAC(leaf, disj_cases_rule(
        member, head_result, tail_result));
  }
  return gnode_prove(root);
}
PROOF thm cm_slot_region_base_lookup =
    cm_prove_slot_region_base_lookup();
PROOF static thm cm_prove_parameter_region_frame_safe(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) fid fp gen old region.
         cm_function_wf p
           (inth fid (cm_program_functions p)) ==>
         cm_regions_before old gen ==>
         MEM region
           (cm_regions_for_slots
             (cm_program_structs p)
             (cm_function_params
               (inth fid (cm_program_functions p)))
             gen (fp + 8i)) ==>
         cm_region_frame_safe p
           (cm_regions_for_slots
              (cm_program_structs p)
              (cm_function_params
                (inth fid (cm_program_functions p)))
              gen (fp + 8i) ++ old)
           fid fp region`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term parameters =
      `cm_function_params
        (inth (fid:int)
          (cm_program_functions (p:cm_program)))`;
  term locals =
      `cm_function_locals
        (inth (fid:int)
          (cm_program_functions (p:cm_program)))`;
  thm function_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_function_wf_def())), assume_rule(
        `cm_function_wf (p:cm_program)
          (inth (fid:int) (cm_program_functions p))`));
  thm params_wf = mp_rule(taut_rule(mk_imp(
      concl(function_open),
      `cm_params_wf (cm_program_structs (p:cm_program))
        ${parameters:(cm_slot_d)list}`)), function_open);
  thm params_slots_wf = conv_rule(rewrite_conv(THM_LIST(
      get_cm_params_wf_def())), params_wf);
  params_slots_wf = conjunct1_rule(params_slots_wf);
  thm locals_wf = mp_rule(taut_rule(mk_imp(
      concl(function_open),
      `cm_slots_wf (cm_program_structs (p:cm_program))
        ${locals:(cm_slot_d)list}`)), function_open);
  thm params_positive = match_mp_rule(
      specl_rule(TERM_LIST(
        `cm_program_structs (p:cm_program)`,
        parameters), cm_slots_wf_sizes_positive),
      params_slots_wf);
  thm locals_positive = match_mp_rule(
      specl_rule(TERM_LIST(
        `cm_program_structs (p:cm_program)`,
        locals), cm_slots_wf_sizes_positive),
      locals_wf);
  thm locals_total = match_mp_rule(
      specl_rule(TERM_LIST(
        `cm_program_structs (p:cm_program)`,
        locals), cm_slot_sizes_positive_total),
      locals_positive);
  thm indexed = match_mp_rule(specl_rule(TERM_LIST(
      `cm_program_structs (p:cm_program)`,
      parameters, `gen:int`, `(fp:int) + 8i`,
      `region:cm_region`), cm_slot_region_member_index),
      assume_rule(
        `MEM (region:cm_region)
          (cm_regions_for_slots
            (cm_program_structs (p:cm_program))
            ${parameters:(cm_slot_d)list}
            (gen:int) ((fp:int) + 8i))`));
  term indexed_body_term =
      `0i <= (offset:int) &&
       offset < ilength ${parameters:(cm_slot_d)list} &&
       (region:cm_region) ==
         CMRegion
           ((gen:int) + offset)
           (((fp:int) + 8i) +
             cm_slots_prefix (cm_program_structs (p:cm_program))
               ${parameters:(cm_slot_d)list} offset)
           0i
           (cm_slot_size (cm_program_structs p)
             (inth offset ${parameters:(cm_slot_d)list})) T T`;
  thm indexed_body = assume_rule(indexed_body_term);
  thm offset_lower = mp_rule(taut_rule(mk_imp(
      concl(indexed_body), `0i <= (offset:int)`)), indexed_body);
  thm offset_upper = mp_rule(taut_rule(mk_imp(
      concl(indexed_body),
      `(offset:int) <
        ilength ${parameters:(cm_slot_d)list}`)), indexed_body);
  thm region_equal = mp_rule(taut_rule(mk_imp(
      concl(indexed_body),
      `(region:cm_region) ==
        CMRegion
          ((gen:int) + offset)
          (((fp:int) + 8i) +
            cm_slots_prefix (cm_program_structs (p:cm_program))
              ${parameters:(cm_slot_d)list} offset)
          0i
          (cm_slot_size (cm_program_structs p)
            (inth offset ${parameters:(cm_slot_d)list})) T T`)),
      indexed_body);
  thm prefix_bounds = match_mp_rule(match_mp_rule(
      spec_rule(`offset:int`, match_mp_rule(
        specl_rule(TERM_LIST(
          `cm_program_structs (p:cm_program)`,
          parameters), cm_slots_prefix_cell_bounds),
        params_positive)), offset_lower), offset_upper);
  thm slots_wf_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_slots_wf_def())), params_slots_wf);
  thm slot_wf = match_mp_rule(match_mp_rule(
      spec_rule(`offset:int`, slots_wf_open),
      offset_lower), offset_upper);
  thm slot_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_slot_wf_def())), slot_wf);
  thm size_positive = mp_rule(taut_rule(mk_imp(
      concl(slot_open),
      `0i < cm_slot_size
        (cm_program_structs (p:cm_program))
        (inth (offset:int) ${parameters:(cm_slot_d)list})`)),
      slot_open);
  term descriptor =
      `CMRegion
         ((gen:int) + (offset:int))
         (((fp:int) + 8i) +
           cm_slots_prefix (cm_program_structs (p:cm_program))
             ${parameters:(cm_slot_d)list} offset)
         0i
         (cm_slot_size (cm_program_structs p)
           (inth offset ${parameters:(cm_slot_d)list})) T T`;
  thm source_member = assume_rule(
      `MEM (region:cm_region)
        (cm_regions_for_slots
          (cm_program_structs (p:cm_program))
          ${parameters:(cm_slot_d)list}
          (gen:int) ((fp:int) + 8i))`);
  thm descriptor_member = conv_rule(
      rewrite_conv(THM_LIST(region_equal)), source_member);
  thm base_lookup = match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `cm_program_structs (p:cm_program)`,
        parameters, `gen:int`, `(fp:int) + 8i`,
        `old:(cm_region)list`, descriptor),
        cm_slot_region_base_lookup),
      assume_rule(
        `cm_regions_before (old:(cm_region)list) (gen:int)`)),
      descriptor_member);
  term property =
      `cm_region_frame_safe (p:cm_program)
        (cm_regions_for_slots
           (cm_program_structs p) ${parameters:(cm_slot_d)list}
           (gen:int) ((fp:int) + 8i) ++ (old:(cm_region)list))
        (fid:int) (fp:int) ${descriptor:cm_region}`;
  thm numeric = conj_rule(size_positive,
      conj_rule(prefix_bounds, locals_total));
  thm normalized = apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_region_frame_safe_def,
        get_cm_region_gen_def(),
        get_cm_region_base_field_def(),
        get_cm_region_lo_def(),
        get_cm_region_hi_def(),
        get_cm_region_live_def(),
        get_cm_temp_offset_def(),
        base_lookup)), property);
  struct dest_eq_results normalized_parts =
      dest_eq(concl(normalized));
  thm normalized_result = mp_rule(int_arith_rule(mk_imp(
      concl(numeric), normalized_parts.tm2)), numeric);
  thm descriptor_result = eq_mp_rule(
      sym_rule(normalized), normalized_result);
  thm transported = eq_mp_rule(sym_rule(beta_norm(ap_term_rule(
      `\candidate:cm_region.
         cm_region_frame_safe (p:cm_program)
           (cm_regions_for_slots
              (cm_program_structs p)
              ${parameters:(cm_slot_d)list}
              (gen:int) ((fp:int) + 8i) ++ (old:(cm_region)list))
           (fid:int) (fp:int) candidate`,
      region_equal))), descriptor_result);
  thm result = choose_rule(
      `offset:int`, indexed, transported);
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_parameter_region_frame_safe =
    cm_prove_parameter_region_frame_safe();


PROOF static thm cm_prove_region_prefix_safe_refl(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (all_regions:(cm_region)list)
         (fid:int) (fp:int) (regions:(cm_region)list).
         cm_region_prefix_safe p all_regions fid fp regions regions`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_all = GEN_TAC(with_program, "all_regions");
  gnode with_fid = GEN_TAC(with_all, "fid");
  gnode with_fp = GEN_TAC(with_fid, "fp");
  gnode_list cases =
      INDUCT_TAC(with_fp, `regions:(cm_region)list`);
  for (size_t index = 0; index < vector_size(cases); ++index) {
    gnode leaf = AUTO_INTROS_TAC(cases[index]);
    gnode reduced = CONV_TAC(leaf,
        reduce_rewrite_conv(THM_LIST(
          cm_region_prefix_safe_def)));
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_region_prefix_safe_refl =
    cm_prove_region_prefix_safe_refl();
PROOF static thm cm_prove_region_prefix_safe_append(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (all_regions:(cm_region)list)
         (fid:int) (fp:int) (fresh:(cm_region)list)
         (old:(cm_region)list).
         (!region. MEM region fresh ==>
            cm_region_frame_safe p all_regions fid fp region) ==>
         cm_region_prefix_safe p all_regions fid fp
           (fresh ++ old) old`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_all = GEN_TAC(with_program, "all_regions");
  gnode with_fid = GEN_TAC(with_all, "fid");
  gnode with_fp = GEN_TAC(with_fid, "fp");
  gnode_list cases =
      INDUCT_TAC(with_fp, `fresh:(cm_region)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    gnode reduced = CONV_TAC(leaf,
        reduce_rewrite_conv(THM_LIST(
          get_theorem_by_name("APPEND"))));
    ACCEPT_TAC(reduced, specl_rule(TERM_LIST(
        `p:cm_program`, `all_regions:(cm_region)list`,
        `fid:int`, `fp:int`, `old:(cm_region)list`),
        cm_region_prefix_safe_refl));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm all_safe = assume_rule(
        `!region.
           MEM region
             ((a0:cm_region) :: (a1:(cm_region)list)) ==>
           cm_region_frame_safe
             (p:cm_program) (all_regions:(cm_region)list)
             (fid:int) (fp:int) region`);
    thm head_member = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_theorem_by_name("MEM"))),
        `MEM (a0:cm_region)
          ((a0:cm_region) :: (a1:(cm_region)list))`));
    thm head_safe = match_mp_rule(
        spec_rule(`a0:cm_region`, all_safe), head_member);
    thm tail_member = assume_rule(
        `MEM (region:cm_region) (a1:(cm_region)list)`);
    thm tail_disj = disj2_rule(
        `(region:cm_region) == (a0:cm_region)`, tail_member);
    thm tail_cons_member = eq_mp_rule(sym_rule(
        apply_conversion(rewrite_conv(THM_LIST(
          get_theorem_by_name("MEM"))),
          `MEM (region:cm_region)
            ((a0:cm_region) :: (a1:(cm_region)list))`)),
        tail_disj);
    thm tail_safe_one = match_mp_rule(
        spec_rule(`region:cm_region`, all_safe), tail_cons_member);
    thm tail_all = gen_rule(`region:cm_region`,
        disch_rule(
          `MEM (region:cm_region) (a1:(cm_region)list)`,
          tail_safe_one));
    thm ih = spec_rule(`old:(cm_region)list`,
        cm_frame_assumption(leaf,
          `!remaining:(cm_region)list.
             (!region.
                MEM region (a1:(cm_region)list) ==>
                cm_region_frame_safe
                  (p:cm_program) (all_regions:(cm_region)list)
                  (fid:int) (fp:int) region) ==>
             cm_region_prefix_safe p all_regions fid fp
               (a1 ++ remaining) remaining`));
    thm tail_safe = match_mp_rule(ih, tail_all);
    term active =
        `(a0:cm_region) ::
          ((a1:(cm_region)list) ++ (old:(cm_region)list))`;
    thm rest_length = ispec_rule(
        `a1:(cm_region)list`,
        get_theorem_by_name("ILENGTH_NONNEG"));
    thm length_if_equal = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          get_theorem_by_name("ILENGTH_DEF"),
          get_theorem_by_name("ILENGTH_APPEND"))),
        ap_term_rule(`ilength:(cm_region)list->int`,
          assume_rule(
            `${active:(cm_region)list} ==
             (old:(cm_region)list)`)));
    thm impossible = mp_rule(
        int_arith_rule(mk_imp(
          mk_conj(concl(rest_length),
            concl(length_if_equal)), `F`)),
        conj_rule(rest_length, length_if_equal));
    thm distinct = not_intro(
        `${active:(cm_region)list} ==
         (old:(cm_region)list)`, impossible);
    gnode reduced = CONV_TAC(leaf,
        reduce_rewrite_conv(THM_LIST(
          cm_region_prefix_safe_def,
          get_theorem_by_name("APPEND"), distinct)));
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, conj_rule(head_safe, tail_safe));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_region_prefix_safe_append =
    cm_prove_region_prefix_safe_append();

PROOF static thm cm_prove_parameter_region_prefix_safe(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) fid fp gen old.
         cm_function_wf p
           (inth fid (cm_program_functions p)) ==>
         cm_regions_before old gen ==>
         cm_region_prefix_safe p
           (cm_regions_for_slots
              (cm_program_structs p)
              (cm_function_params
                (inth fid (cm_program_functions p)))
              gen (fp + 8i) ++ old)
           fid fp
           (cm_regions_for_slots
              (cm_program_structs p)
              (cm_function_params
                (inth fid (cm_program_functions p)))
              gen (fp + 8i) ++ old)
           old`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term fresh =
      `cm_regions_for_slots
        (cm_program_structs (p:cm_program))
        (cm_function_params
          (inth (fid:int) (cm_program_functions p)))
        (gen:int) ((fp:int) + 8i)`;
  thm each_safe = gen_rule(`region:cm_region`,
      disch_rule(`MEM (region:cm_region) ${fresh:(cm_region)list}`,
        match_mp_rule(match_mp_rule(match_mp_rule(
          specl_rule(TERM_LIST(
            `p:cm_program`, `fid:int`, `fp:int`, `gen:int`,
            `old:(cm_region)list`, `region:cm_region`),
            cm_parameter_region_frame_safe),
          assume_rule(
            `cm_function_wf (p:cm_program)
              (inth (fid:int) (cm_program_functions p))`)),
          assume_rule(
            `cm_regions_before (old:(cm_region)list) (gen:int)`)),
          assume_rule(
            `MEM (region:cm_region) ${fresh:(cm_region)list}`))));
  ACCEPT_TAC(leaf, match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `${fresh:(cm_region)list} ++
          (old:(cm_region)list)`,
        `fid:int`, `fp:int`, fresh, `old:(cm_region)list`),
        cm_region_prefix_safe_append), each_safe));
  return gnode_prove(root);
}
PROOF thm cm_parameter_region_prefix_safe =
    cm_prove_parameter_region_prefix_safe();
PROOF static thm cm_prove_call_frame_segment(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) fid values st.
         cm_typed_program p ==>
         cm_call_ok p fid values st ==>
         cm_frame_segment p fid
           (cm_state_fp st -
             cm_frame_size (cm_program_structs p)
               (inth fid (cm_program_functions p)))
           (cm_state_fp st)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm typed_assumption =
      assume_rule(`cm_typed_program (p:cm_program)`);
  thm typed = conv_rule(rewrite_conv(THM_LIST(
      get_cm_typed_program_def())), typed_assumption);
  thm call_ok = conv_rule(rewrite_conv(THM_LIST(
      get_cm_call_ok_def())), assume_rule(
        `cm_call_ok (p:cm_program) (fid:int)
          (values:(cm_value)list) (st:cm_src_state)`));
  thm fid_lower = mp_rule(taut_rule(mk_imp(
      concl(call_ok), `0i <= (fid:int)`)), call_ok);
  thm fid_upper = mp_rule(taut_rule(mk_imp(
      concl(call_ok),
      `(fid:int) < ilength (cm_program_functions (p:cm_program))`)),
      call_ok);
  thm function_all = mp_rule(taut_rule(mk_imp(
      concl(typed),
      `!index.
         0i <= index ==>
         index < ilength (cm_program_functions (p:cm_program)) ==>
         cm_function_wf p
           (inth index (cm_program_functions p))`)), typed);
  thm function_wf = match_mp_rule(match_mp_rule(
      spec_rule(`fid:int`, function_all), fid_lower), fid_upper);
  thm function_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_function_wf_def())), function_wf);
  term parameters =
      `cm_function_params
        (inth (fid:int)
          (cm_program_functions (p:cm_program)))`;
  term locals =
      `cm_function_locals
        (inth (fid:int)
          (cm_program_functions (p:cm_program)))`;
  thm params_wf = mp_rule(taut_rule(mk_imp(
      concl(function_open),
      `cm_params_wf (cm_program_structs (p:cm_program))
        ${parameters:(cm_slot_d)list}`)), function_open);
  thm params_slots_wf = conjunct1_rule(conv_rule(
      rewrite_conv(THM_LIST(get_cm_params_wf_def())), params_wf));
  thm locals_wf = mp_rule(taut_rule(mk_imp(
      concl(function_open),
      `cm_slots_wf (cm_program_structs (p:cm_program))
        ${locals:(cm_slot_d)list}`)), function_open);
  thm temp_nonnegative = mp_rule(taut_rule(mk_imp(
      concl(function_open),
      `0i <= cm_temp_slots
        (inth (fid:int) (cm_program_functions (p:cm_program)))`)),
      function_open);
  thm params_total = match_mp_rule(
      specl_rule(TERM_LIST(
        `cm_program_structs (p:cm_program)`,
        parameters), cm_slot_sizes_positive_total),
      match_mp_rule(specl_rule(TERM_LIST(
        `cm_program_structs (p:cm_program)`,
        parameters), cm_slots_wf_sizes_positive),
        params_slots_wf));
  thm locals_total = match_mp_rule(
      specl_rule(TERM_LIST(
        `cm_program_structs (p:cm_program)`,
        locals), cm_slot_sizes_positive_total),
      match_mp_rule(specl_rule(TERM_LIST(
        `cm_program_structs (p:cm_program)`,
        locals), cm_slots_wf_sizes_positive),
        locals_wf));
  thm static_lower = mp_rule(taut_rule(mk_imp(
      concl(typed), `16i <= cm_static_size (p:cm_program)`)), typed);
  thm call_numeric = mp_rule(taut_rule(mk_imp(
      concl(call_ok),
      `0i <= (fid:int) &&
       fid < ilength (cm_program_functions (p:cm_program)) &&
       cm_static_size p <=
         cm_state_fp (st:cm_src_state) -
           cm_frame_size (cm_program_structs p)
             (inth fid (cm_program_functions p)) &&
       cm_state_fp st <= 1048576i`)), call_ok);
  thm frame_size_exact = apply_conversion(
      rewrite_conv(THM_LIST(get_cm_frame_size_def())),
      `cm_frame_size (cm_program_structs (p:cm_program))
        (inth (fid:int) (cm_program_functions p))`);
  thm numeric = conj_rule(static_lower,
      conj_rule(call_numeric,
        conj_rule(frame_size_exact,
          conj_rule(params_total,
            conj_rule(locals_total, temp_nonnegative)))));
  gnode reduced = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(
        cm_frame_segment_def,
        get_cm_frame_size_def(),
        get_cm_temp_offset_def())));
  ACCEPT_TAC(reduced, mp_rule(int_arith_rule(mk_imp(
      concl(numeric), goal_ccl(reduced->g))), numeric));
  return gnode_prove(root);
}
PROOF thm cm_call_frame_segment =
    cm_prove_call_frame_segment();

PROOF static thm cm_prove_local_region_frame_safe(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) fid fp gen old slot.
         cm_function_wf p
           (inth fid (cm_program_functions p)) ==>
         0i <= slot ==>
         slot < ilength
           (cm_function_locals
             (inth fid (cm_program_functions p))) ==>
         cm_region_frame_safe p
           (CMRegion gen (cm_local_base p fid slot fp) 0i
              (cm_slot_size (cm_program_structs p)
                (inth slot (cm_function_locals
                  (inth fid (cm_program_functions p))))) T T ::
            old)
           fid fp
           (CMRegion gen (cm_local_base p fid slot fp) 0i
              (cm_slot_size (cm_program_structs p)
                (inth slot (cm_function_locals
                  (inth fid (cm_program_functions p))))) T T)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term parameters =
      `cm_function_params
        (inth (fid:int)
          (cm_program_functions (p:cm_program)))`;
  term locals =
      `cm_function_locals
        (inth (fid:int)
          (cm_program_functions (p:cm_program)))`;
  thm function_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_function_wf_def())), assume_rule(
        `cm_function_wf (p:cm_program)
          (inth (fid:int) (cm_program_functions p))`));
  thm params_wf = mp_rule(taut_rule(mk_imp(
      concl(function_open),
      `cm_params_wf (cm_program_structs (p:cm_program))
        ${parameters:(cm_slot_d)list}`)), function_open);
  thm params_slots_wf = conjunct1_rule(conv_rule(
      rewrite_conv(THM_LIST(get_cm_params_wf_def())), params_wf));
  thm locals_wf = mp_rule(taut_rule(mk_imp(
      concl(function_open),
      `cm_slots_wf (cm_program_structs (p:cm_program))
        ${locals:(cm_slot_d)list}`)), function_open);
  thm params_total = match_mp_rule(
      specl_rule(TERM_LIST(
        `cm_program_structs (p:cm_program)`,
        parameters), cm_slot_sizes_positive_total),
      match_mp_rule(specl_rule(TERM_LIST(
        `cm_program_structs (p:cm_program)`,
        parameters), cm_slots_wf_sizes_positive),
        params_slots_wf));
  thm locals_positive = match_mp_rule(
      specl_rule(TERM_LIST(
        `cm_program_structs (p:cm_program)`,
        locals), cm_slots_wf_sizes_positive),
      locals_wf);
  thm slot_lower = assume_rule(`0i <= (slot:int)`);
  thm slot_upper = assume_rule(
      `(slot:int) < ilength ${locals:(cm_slot_d)list}`);
  thm prefix_bounds = match_mp_rule(match_mp_rule(
      spec_rule(`slot:int`, match_mp_rule(
        specl_rule(TERM_LIST(
          `cm_program_structs (p:cm_program)`,
          locals), cm_slots_prefix_cell_bounds),
        locals_positive)), slot_lower), slot_upper);
  thm locals_wf_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_slots_wf_def())), locals_wf);
  thm slot_wf = match_mp_rule(match_mp_rule(
      spec_rule(`slot:int`, locals_wf_open),
      slot_lower), slot_upper);
  thm slot_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_slot_wf_def())), slot_wf);
  thm size_positive = mp_rule(taut_rule(mk_imp(
      concl(slot_open),
      `0i < cm_slot_size
        (cm_program_structs (p:cm_program))
        (inth (slot:int) ${locals:(cm_slot_d)list})`)),
      slot_open);
  thm numeric = conj_rule(params_total,
      conj_rule(prefix_bounds, size_positive));
  gnode reduced = CONV_TAC(leaf,
      reduce_rewrite_conv(THM_LIST(
        cm_region_frame_safe_def,
        get_cm_region_gen_def(),
        get_cm_region_base_field_def(),
        get_cm_region_lo_def(),
        get_cm_region_hi_def(),
        get_cm_region_live_def(),
        get_cm_region_base_def(),
        get_cm_local_base_def(),
        get_cm_temp_offset_def())));
  ACCEPT_TAC(reduced, mp_rule(int_arith_rule(mk_imp(
      concl(numeric), goal_ccl(reduced->g))), numeric));
  return gnode_prove(root);
}
PROOF thm cm_local_region_frame_safe =
    cm_prove_local_region_frame_safe();
PROOF static int cmc_preservation_invariant_frame_final_checks(void) {


  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_invariant_frame_axioms_before,
      "cmc_preservation_invariant_frame introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_invariant_frame_checks =
    cmc_preservation_invariant_frame_final_checks();
