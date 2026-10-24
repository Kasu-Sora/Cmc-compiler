#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_sim.h"
#require "cmc_sim.c"
#include "cmc_sim_ops.h"

PROOF static size_t _cmc_sim_ops_axioms_before =
    vector_size(get_all_axioms());

PROOF static bool cm_sim_has_conjunct(
    const term tree, const term wanted) {
  if (alpha_compare(tree, wanted) == 0) {
    return true;
  }
  if (!is_conj(tree)) {
    return false;
  }
  dest_conj_results parts = dest_conj(tree);
  return cm_sim_has_conjunct(parts.tm1, wanted) ||
         cm_sim_has_conjunct(parts.tm2, wanted);
}

PROOF static thm cm_sim_pick_conjunct(
    const thm fact, const term wanted) {
  if (alpha_compare(concl(fact), wanted) == 0) {
    return fact;
  }
  dest_conj_results parts = dest_conj(concl(fact));
  return cm_sim_has_conjunct(parts.tm1, wanted)
      ? cm_sim_pick_conjunct(conjunct1_rule(fact), wanted)
      : cm_sim_pick_conjunct(conjunct2_rule(fact), wanted);
}

PROOF static thm cm_prove_truth_number_bridge(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (v:cm_value).
         cm_truth st v = ~(cm_value_number st v == 0i)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_TAC(leaf, rewrite_conv(THM_LIST(get_cm_truth_def())));
  return gnode_prove(root);
}
PROOF thm cm_truth_number_bridge = cm_prove_truth_number_bridge();
PROOF static thm cm_prove_const_immediate_number_bridge(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (ty:cm_type) (n:int).
         tower_wrap64 (cm_const_immediate ty n) ==
         cm_value_number st
           (cm_convert_value st ty (CMIntV n))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list char_cases = BOOL_CASES_TAC(
      leaf, `(ty:cm_type) == CMCharTy`, "Hchar");
  for (size_t i = 0; i < 2; ++i) {
    CONV_WITH_ASMP_TAC(char_cases[i], reduce_rewrite_conv, THM_LIST(
        get_cm_const_immediate_def(),
        get_cm_convert_value_number_bridge(),
        get_cm_value_number_def(), get_tower_wrap64_u8(),
        get_tower_u8_wrap64()));
  }
  return gnode_prove(root);
}
PROOF thm cm_const_immediate_number_bridge =
    cm_prove_const_immediate_number_bridge();


PROOF static thm cm_prove_wrap_bool(void) {
  gnode root = gnode_new_with_ccl(
      `!(b:bool). tower_wrap64 (tower_bool b) == tower_bool b`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(leaf, `b:bool`, "hb");
  for (size_t i = 0; i < 2; ++i) {
    CONV_WITH_ASMP_TAC(cases[i], reduce_rewrite_conv, THM_LIST(
        get_tower_bool_def(), get_tower_wrap64_def()));
  }
  return gnode_prove(root);
}
PROOF static thm cm_wrap_bool = cm_prove_wrap_bool();

PROOF static thm cm_prove_add_wrapped(void) {
  gnode root = gnode_new_with_ccl(
      `!(a:int) (b:int).
         tower_add (tower_wrap64 a) (tower_wrap64 b) ==
         tower_wrap64 (a + b)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode reduced = CONV_TAC(leaf, then_conv(
      rewrite_conv(THM_LIST(
        get_tower_add_def(), get_tower_wrap64_def())),
      get_conversion_by_name("INT_REM_DOWN_CONV")));
  if (IS_NULL(reduced->solved)) {
    thm args = int_ring_rule(
        `((((a:int) + 9223372036854775808i) -
             9223372036854775808i +
           ((b:int) + 9223372036854775808i) -
             9223372036854775808i) +
          9223372036854775808i) ==
         ((a:int) + b) + 9223372036854775808i`);
    thm rems = beta_norm(ap_term_rule(
        `\z:int. z % 18446744073709551616i`, args));
    thm result = beta_norm(ap_term_rule(
        `\z:int. z - 9223372036854775808i`, rems));
    ACCEPT_TAC(reduced, result);
  }
  return gnode_prove(root);
}
PROOF static thm cm_add_wrapped = cm_prove_add_wrapped();

PROOF static thm cm_prove_add_left_wrapped(void) {
  gnode root = gnode_new_with_ccl(
      `!(a:int) (b:int).
         tower_add (tower_wrap64 a) b == tower_wrap64 (a + b)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode reduced = CONV_TAC(leaf, then_conv(
      rewrite_conv(THM_LIST(
        get_tower_add_def(), get_tower_wrap64_def())),
      get_conversion_by_name("INT_REM_DOWN_CONV")));
  if (IS_NULL(reduced->solved)) {
    thm args = int_ring_rule(
        `((((a:int) + 9223372036854775808i) -
             9223372036854775808i +
           (b:int)) +
          9223372036854775808i) ==
         ((a:int) + b) + 9223372036854775808i`);
    thm rems = beta_norm(ap_term_rule(
        `\z:int. z % 18446744073709551616i`, args));
    thm result = beta_norm(ap_term_rule(
        `\z:int. z - 9223372036854775808i`, rems));
    ACCEPT_TAC(reduced, result);
  }
  return gnode_prove(root);
}
PROOF static thm cm_add_left_wrapped =
    cm_prove_add_left_wrapped();

PROOF static thm cm_prove_sub_wrapped(void) {
  gnode root = gnode_new_with_ccl(
      `!(a:int) (b:int).
         tower_sub (tower_wrap64 a) (tower_wrap64 b) ==
         tower_wrap64 (a - b)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode reduced = CONV_TAC(leaf, then_conv(
      rewrite_conv(THM_LIST(
        get_tower_sub_def(), get_tower_wrap64_def())),
      get_conversion_by_name("INT_REM_DOWN_CONV")));
  if (IS_NULL(reduced->solved)) {
    thm args = int_ring_rule(
        `((((a:int) + 9223372036854775808i) -
             9223372036854775808i -
           (((b:int) + 9223372036854775808i) -
             9223372036854775808i)) +
          9223372036854775808i) ==
         ((a:int) - b) + 9223372036854775808i`);
    thm rems = beta_norm(ap_term_rule(
        `\z:int. z % 18446744073709551616i`, args));
    thm result = beta_norm(ap_term_rule(
        `\z:int. z - 9223372036854775808i`, rems));
    ACCEPT_TAC(reduced, result);
  }
  return gnode_prove(root);
}
PROOF static thm cm_sub_wrapped = cm_prove_sub_wrapped();

PROOF static thm cm_prove_add_neg_mul(void) {
  gnode root = gnode_new_with_ccl(
      `!(x:int) (y:int) (z:int).
         tower_add x (tower_mul (tower_neg y) z) ==
         tower_sub x (tower_mul y z)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode reduced = CONV_TAC(leaf, then_conv(
      rewrite_conv(THM_LIST(
        get_tower_add_def(), get_tower_sub_def(),
        get_tower_mul_def(), get_tower_neg_def(),
        get_tower_wrap64_def())),
      get_conversion_by_name("INT_REM_DOWN_CONV")));
  if (IS_NULL(reduced->solved)) {
    thm args = int_ring_rule(
        `(((x:int) +
           ((((--(y:int)) + 9223372036854775808i) -
               9223372036854775808i) * (z:int) +
             9223372036854775808i) -
             9223372036854775808i) +
          9223372036854775808i) ==
         ((x:int) -
           (((y:int) * (z:int) + 9223372036854775808i) -
             9223372036854775808i) +
          9223372036854775808i)`);
    thm rems = beta_norm(ap_term_rule(
        `\q:int. q % 18446744073709551616i`, args));
    thm result = beta_norm(ap_term_rule(
        `\q:int. q - 9223372036854775808i`, rems));
    ACCEPT_TAC(reduced, result);
  }
  return gnode_prove(root);
}
PROOF static thm cm_add_neg_mul =
    cm_prove_add_neg_mul();

PROOF static thm cm_prove_ptr_add_number_bridge(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (ptr:cm_value) (index:int)
         (st:cm_src_state).
         cm_pointer_live st ptr ==>
         cm_value_number st (cm_ptr_add structs ptr index) ==
         tower_add (cm_value_number st ptr)
           (tower_mul index (cm_type_size structs (cm_ptr_view ptr)))`);
  gnode with_structs = GEN_TAC(root, "structs");
  gnode_list cases = INDUCT_TAC(with_structs, `ptr:cm_value`);
  for (size_t i = 0; i < 3; ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    thm live = assume_rule(goal_lasmps(leaf->g)[0].tm);
    thm impossible = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          get_cm_pointer_live_def(), get_cm_ptr_gen_def())),
        live);
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[3]);
    gnode reduced = CONV_WITH_ASMP_TAC(
        leaf, reduce_rewrite_conv, THM_LIST(
          get_cm_ptr_add_def(), get_cm_value_number_def(),
          get_cm_ptr_gen_def(), get_cm_ptr_lo_def(),
          get_cm_ptr_hi_def(), get_cm_ptr_offset_def(),
          get_cm_ptr_view_def(), get_tower_mul_def(),
          cm_add_wrapped));
    if (IS_NULL(reduced->solved)) {
      struct dest_eq_results sides = dest_eq(goal_ccl(reduced->g));
      thm args = int_ring_rule(mk_eq(
          dest_comb(sides.tm1).tm2,
          dest_comb(sides.tm2).tm2));
      ACCEPT_TAC(reduced,
          mk_comb_rule(refl_rule(`tower_wrap64:int->int`), args));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_ptr_add_number_bridge =
    cm_prove_ptr_add_number_bridge();

PROOF static thm cm_prove_ptr_member_number_bridge(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (ptr:cm_value) (mid:int)
         (st:cm_src_state).
         cm_pointer_live st ptr ==>
         cm_value_number st (cm_ptr_member p ptr mid) ==
         tower_add (cm_value_number st ptr)
           (cm_member_offset (cm_program_structs p)
             (cm_struct_id (cm_ptr_view ptr)) mid)`);
  gnode with_program = GEN_TAC(root, "p");
  gnode_list cases = INDUCT_TAC(with_program, `ptr:cm_value`);
  for (size_t i = 0; i < 3; ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    thm live = assume_rule(goal_lasmps(leaf->g)[0].tm);
    thm impossible = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          get_cm_pointer_live_def(), get_cm_ptr_gen_def())),
        live);
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[3]);
    gnode reduced = CONV_WITH_ASMP_TAC(
        leaf, reduce_rewrite_conv, THM_LIST(
          get_cm_ptr_member_def(), get_cm_value_number_def(),
          get_cm_ptr_gen_def(), get_cm_ptr_lo_def(),
          get_cm_ptr_hi_def(), get_cm_ptr_offset_def(),
          get_cm_ptr_view_def(), cm_add_left_wrapped));
    if (IS_NULL(reduced->solved)) {
      struct dest_eq_results sides = dest_eq(goal_ccl(reduced->g));
      thm args = int_ring_rule(mk_eq(
          dest_comb(sides.tm1).tm2,
          dest_comb(sides.tm2).tm2));
      ACCEPT_TAC(reduced,
          mk_comb_rule(refl_rule(`tower_wrap64:int->int`), args));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_ptr_member_number_bridge =
    cm_prove_ptr_member_number_bridge();

PROOF thm cm_binary_machine_number_def = new_fun_definition(
    `cm_binary_machine_number (p:cm_program) (op:int)
       (left:cm_value) (right:cm_value)
       (st:cm_src_state) : int =
       (if op == 0i
        then tower_bool (cm_truth st left || cm_truth st right)
        else if op == 1i
        then tower_bool (cm_truth st left && cm_truth st right)
        else if op == 2i
        then tower_bool
          (cm_value_number st left == cm_value_number st right)
        else if op == 3i
        then tower_bool
          (~(cm_value_number st left == cm_value_number st right))
        else if op == 4i
        then tower_bool
          (cm_value_number st left < cm_value_number st right)
        else if op == 5i
        then tower_bool
          (cm_value_number st left <= cm_value_number st right)
        else if op == 6i
        then tower_bool
          (cm_value_number st left > cm_value_number st right)
        else if op == 7i
        then tower_bool
          (cm_value_number st left >= cm_value_number st right)
        else if op == 8i &&
                cm_is_pointer (cm_value_type right)
        then tower_add (cm_value_number st right)
          (tower_mul (cm_value_number st left)
            (cm_type_size (cm_program_structs p)

              (cm_pointee (cm_value_type right))))
        else if op == 8i &&
                cm_is_pointer (cm_value_type left)
        then tower_add (cm_value_number st left)
          (tower_mul (cm_value_number st right)
            (cm_type_size (cm_program_structs p)
              (cm_pointee (cm_value_type left))))
        else if op == 8i
        then tower_add
          (cm_value_number st left) (cm_value_number st right)
        else if op == 9i &&
                cm_is_pointer (cm_value_type left) &&
                cm_is_pointer (cm_value_type right)
        then tower_div
          (tower_sub
            (cm_value_number st left)
            (cm_value_number st right))
          (cm_type_size (cm_program_structs p)
            (cm_pointee (cm_value_type left)))
        else if op == 9i &&
                cm_is_pointer (cm_value_type left)
        then tower_sub (cm_value_number st left)
          (tower_mul (cm_value_number st right)
            (cm_type_size (cm_program_structs p)
              (cm_pointee (cm_value_type left))))
        else if op == 9i
        then tower_sub
          (cm_value_number st left) (cm_value_number st right)
        else if op == 10i
        then tower_mul
          (cm_value_number st left) (cm_value_number st right)
        else if op == 11i
        then tower_div
          (cm_value_number st left) (cm_value_number st right)
        else tower_mod
          (cm_value_number st left) (cm_value_number st right))`);
PROOF static thm cm_prove_pointer_type_view(void) {
  gnode root = gnode_new_with_ccl(
      `!(v:cm_value).
         cm_pointee (cm_value_type v) == cm_ptr_view v`);
  gnode_list cases = INDUCT_TAC(root, `v:cm_value`);
  for (size_t i = 0; i < 4; ++i) {
    CONV_TAC(cases[i], reduce_rewrite_conv(THM_LIST(
        get_cm_value_type_def(), get_cm_pointee_def(),
        get_cm_ptr_view_def())));
  }
  return gnode_prove(root);
}
PROOF static thm cm_pointer_type_view =
    cm_prove_pointer_type_view();

PROOF static thm cm_prove_pointer_difference_number(void) {
  gnode root = gnode_new_with_ccl(
      `!(left:cm_value) (right:cm_value) (st:cm_src_state).
         cm_pointer_compatible st left right ==>
         tower_sub
           (cm_value_number st left)
           (cm_value_number st right) ==
         tower_sub (cm_ptr_offset left) (cm_ptr_offset right)`);
  gnode_list left_cases = INDUCT_TAC(root, `left:cm_value`);
  for (size_t i = 0; i < 3; ++i) {
    gnode leaf = AUTO_INTROS_TAC(left_cases[i]);
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_pointer_compatible_def(),
        get_cm_is_null_value_def(), get_cm_pointer_live_def(),
        get_cm_ptr_gen_def())),
        assume_rule(goal_lasmps(leaf->g)[0].tm));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode_list right_cases =
        INDUCT_TAC(left_cases[3], `right:cm_value`);
    for (size_t i = 0; i < 3; ++i) {
      gnode leaf = AUTO_INTROS_TAC(right_cases[i]);
      thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_cm_pointer_compatible_def(),
          get_cm_is_null_value_def(), get_cm_pointer_live_def(),
          get_cm_ptr_gen_def())),
          assume_rule(goal_lasmps(leaf->g)[0].tm));
      CONTR_TAC(leaf, impossible);
    }
    {
      gnode leaf = AUTO_INTROS_TAC(right_cases[3]);
      thm compatible = assume_rule(
          `cm_pointer_compatible (st:cm_src_state)
             (CMPtrV (a0:int) (a1:int) (a2:int) (a3:int)
               (a4:cm_type))
             (CMPtrV (a0_:int) (a1_:int) (a2_:int) (a3_:int)
               (a4_:cm_type))`);
      thm expanded = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_cm_pointer_compatible_def(), get_cm_ptr_gen_def())),
          compatible);
      thm same_generation = cm_sim_pick_conjunct(
          expanded, `(a0:int) == (a0_:int)`);
      gnode reduced = CONV_WITH_ASMP_TAC(
          leaf, reduce_rewrite_conv, THM_LIST(
            get_cm_value_number_def(), get_cm_ptr_offset_def(),
            same_generation, cm_sub_wrapped));
      if (IS_NULL(reduced->solved)) {
        gnode unfolded = CONV_TAC(reduced,
            rewrite_conv(THM_LIST(get_tower_sub_def())));
        if (IS_NULL(unfolded->solved)) {
          struct dest_eq_results sides = dest_eq(goal_ccl(unfolded->g));
          thm args = int_ring_rule(mk_eq(
              dest_comb(sides.tm1).tm2,
              dest_comb(sides.tm2).tm2));
          ACCEPT_TAC(unfolded,
              mk_comb_rule(refl_rule(`tower_wrap64:int->int`), args));
        }
      }
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_pointer_difference_number =
    cm_prove_pointer_difference_number();

PROOF static thm cm_prove_pointer_subtract_number(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (ptr:cm_value)
         (number:int) (st:cm_src_state).
         cm_pointer_live st ptr ==>
         cm_value_number st
           (cm_ptr_add structs ptr
             (tower_neg number)) ==
         tower_sub (cm_value_number st ptr)
           (tower_mul number
             (cm_type_size structs
               (cm_pointee (cm_value_type ptr))))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm live = assume_rule(
      `cm_pointer_live (st:cm_src_state) (ptr:cm_value)`);
  thm view = spec_rule(
      `ptr:cm_value`, cm_pointer_type_view);
  thm added = mp_rule(specl_rule(TERM_LIST(
      `structs:(cm_struct_d)list`, `ptr:cm_value`,
      `tower_neg (number:int)`, `st:cm_src_state`),
      cm_ptr_add_number_bridge), live);
  thm normalized = conv_rule(rewrite_conv(THM_LIST(
      view, cm_add_neg_mul)), added);
  gnode reduced = CONV_TAC(leaf, rewrite_conv(THM_LIST(view)));
  ACCEPT_TAC(reduced, normalized);
  return gnode_prove(root);
}
PROOF static thm cm_pointer_subtract_number =
    cm_prove_pointer_subtract_number();
PROOF static thm cm_prove_binary_add_number(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (left:cm_value) (right:cm_value)
         (ty:cm_type) (st:cm_src_state).
         cm_binary_ok p 8i left right st ==>
         ~(cm_is_pointer (cm_value_type left) &&
           cm_is_pointer (cm_value_type right)) ==>
         cm_value_number st
           (cm_binary_value p 8i left right ty st) ==
         cm_binary_machine_number p 8i left right st`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm ok = assume_rule(
      `cm_binary_ok (p:cm_program) 8i
         (left:cm_value) (right:cm_value) (st:cm_src_state)`);
  thm not_both = assume_rule(
      `~(cm_is_pointer (cm_value_type (left:cm_value)) &&
         cm_is_pointer (cm_value_type (right:cm_value)))`);
  gnode_list right_cases = BOOL_CASES_TAC(leaf,
      `cm_is_pointer (cm_value_type (right:cm_value))`,
      "right_pointer");
  {
    thm right_pointer = assume_rule(
        `cm_is_pointer (cm_value_type (right:cm_value))`);
    gnode_list left_cases = BOOL_CASES_TAC(right_cases[0],
        `cm_is_pointer (cm_value_type (left:cm_value))`,
        "left_pointer");
    {
      thm left_pointer = assume_rule(
          `cm_is_pointer (cm_value_type (left:cm_value))`);
      thm impossible = contra(not_both,
          conj_rule(left_pointer, right_pointer));
      CONTR_TAC(left_cases[0], impossible);
    }
    {
      thm not_left = assume_rule(
          `~cm_is_pointer (cm_value_type (left:cm_value))`);
      thm shift = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_cm_binary_ok_def(), not_left, right_pointer)), ok);
      thm shift_parts = conv_rule(rewrite_conv(THM_LIST(
          get_cm_ptr_shift_ok_def())), shift);
      thm live = cm_sim_pick_conjunct(shift_parts,
          `cm_pointer_live (st:cm_src_state) (right:cm_value)`);
      thm bridge = mp_rule(specl_rule(TERM_LIST(
          `cm_program_structs (p:cm_program)`, `right:cm_value`,
          `cm_value_number (st:cm_src_state) (left:cm_value)`,
          `st:cm_src_state`), cm_ptr_add_number_bridge), live);
      thm view = spec_rule(
          `right:cm_value`, cm_pointer_type_view);
      gnode reduced = CONV_WITH_ASMP_TAC(left_cases[1],
          reduce_rewrite_conv, THM_LIST(
            get_cm_binary_value_def(),
            cm_binary_machine_number_def,
            not_left, right_pointer, bridge, view));
      if (IS_NULL(reduced->solved)) {
        ACCEPT_TAC(reduced, bridge);
      }
    }
  }
  {
    thm not_right = assume_rule(
        `~cm_is_pointer (cm_value_type (right:cm_value))`);
    gnode_list left_cases = BOOL_CASES_TAC(right_cases[1],
        `cm_is_pointer (cm_value_type (left:cm_value))`,
        "left_pointer");
    {
      thm left_pointer = assume_rule(
          `cm_is_pointer (cm_value_type (left:cm_value))`);
      thm shift = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_cm_binary_ok_def(), left_pointer, not_right)), ok);
      thm shift_parts = conv_rule(rewrite_conv(THM_LIST(
          get_cm_ptr_shift_ok_def())), shift);
      thm live = cm_sim_pick_conjunct(shift_parts,
          `cm_pointer_live (st:cm_src_state) (left:cm_value)`);
      thm bridge = mp_rule(specl_rule(TERM_LIST(
          `cm_program_structs (p:cm_program)`, `left:cm_value`,
          `cm_value_number (st:cm_src_state) (right:cm_value)`,
          `st:cm_src_state`), cm_ptr_add_number_bridge), live);
      thm view = spec_rule(
          `left:cm_value`, cm_pointer_type_view);
      gnode reduced = CONV_WITH_ASMP_TAC(left_cases[0],
          reduce_rewrite_conv, THM_LIST(
            get_cm_binary_value_def(),
            cm_binary_machine_number_def,
            left_pointer, not_right, bridge, view));
      if (IS_NULL(reduced->solved)) {
        ACCEPT_TAC(reduced, bridge);
      }
    }
    {
      thm not_left = assume_rule(
          `~cm_is_pointer (cm_value_type (left:cm_value))`);
      gnode reduced = CONV_WITH_ASMP_TAC(left_cases[1],
          reduce_rewrite_conv, THM_LIST(
            get_cm_binary_value_def(),
            cm_binary_machine_number_def,
            get_cm_value_number_def(),
            get_tower_add_def(),
            get_tower_wrap64_idempotent(),
            not_left, not_right));
      if (IS_NULL(reduced->solved)) {
        CONV_TAC(reduced, reduce_rewrite_conv(THM_LIST(
            get_cm_value_number_def(),
            get_tower_wrap64_idempotent())));
      }
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_binary_add_number =
    cm_prove_binary_add_number();

PROOF static thm cm_prove_binary_subtract_number(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (left:cm_value) (right:cm_value)
         (ty:cm_type) (st:cm_src_state).
         cm_binary_ok p 9i left right st ==>
         cm_value_number st
           (cm_binary_value p 9i left right ty st) ==
         cm_binary_machine_number p 9i left right st`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm ok = assume_rule(
      `cm_binary_ok (p:cm_program) 9i
         (left:cm_value) (right:cm_value) (st:cm_src_state)`);
  gnode_list left_cases = BOOL_CASES_TAC(leaf,
      `cm_is_pointer (cm_value_type (left:cm_value))`,
      "left_pointer");
  {
    thm left_pointer = assume_rule(
        `cm_is_pointer (cm_value_type (left:cm_value))`);
    gnode_list right_cases = BOOL_CASES_TAC(left_cases[0],
        `cm_is_pointer (cm_value_type (right:cm_value))`,
        "right_pointer");
    {
      thm right_pointer = assume_rule(
          `cm_is_pointer (cm_value_type (right:cm_value))`);
      thm diff = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_cm_binary_ok_def(), left_pointer, right_pointer)), ok);
      thm diff_parts = conv_rule(rewrite_conv(THM_LIST(
          get_cm_ptr_diff_ok_def())), diff);
      thm compatible = cm_sim_pick_conjunct(diff_parts,
          `cm_pointer_compatible (st:cm_src_state)
             (left:cm_value) (right:cm_value)`);
      thm difference = mp_rule(specl_rule(TERM_LIST(
          `left:cm_value`, `right:cm_value`, `st:cm_src_state`),
          cm_pointer_difference_number), compatible);
      thm view = spec_rule(
          `left:cm_value`, cm_pointer_type_view);
      gnode reduced = CONV_WITH_ASMP_TAC(right_cases[0],
          reduce_rewrite_conv, THM_LIST(
            get_cm_binary_value_def(),
            cm_binary_machine_number_def,
            left_pointer, right_pointer,
            difference, view));
      if (IS_NULL(reduced->solved)) {
        reduced = CONV_TAC(reduced,
            reduce_rewrite_conv(THM_LIST(
              get_cm_value_number_def(), get_tower_div_def(),
              get_tower_wrap64_idempotent(),
              difference, view)));
      }
    }
    {
      thm not_right = assume_rule(
          `~cm_is_pointer (cm_value_type (right:cm_value))`);
      thm shift = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_cm_binary_ok_def(), left_pointer, not_right)), ok);
      thm shift_parts = conv_rule(rewrite_conv(THM_LIST(
          get_cm_ptr_shift_ok_def())), shift);
      thm live = cm_sim_pick_conjunct(shift_parts,
          `cm_pointer_live (st:cm_src_state) (left:cm_value)`);
      thm bridge = mp_rule(specl_rule(TERM_LIST(
          `cm_program_structs (p:cm_program)`, `left:cm_value`,
          `cm_value_number (st:cm_src_state) (right:cm_value)`,
          `st:cm_src_state`), cm_pointer_subtract_number), live);
      gnode reduced = CONV_WITH_ASMP_TAC(right_cases[1],
          reduce_rewrite_conv, THM_LIST(
            get_cm_binary_value_def(),
            cm_binary_machine_number_def,
            left_pointer, not_right, bridge));
      if (IS_NULL(reduced->solved)) {
        ACCEPT_TAC(reduced, bridge);
      }
    }
  }
  {
    thm not_left = assume_rule(
        `~cm_is_pointer (cm_value_type (left:cm_value))`);
    gnode reduced = CONV_WITH_ASMP_TAC(left_cases[1],
        reduce_rewrite_conv, THM_LIST(
          get_cm_binary_value_def(),
          cm_binary_machine_number_def,
          get_tower_sub_def(),
          not_left));
    if (IS_NULL(reduced->solved)) {
      CONV_TAC(reduced, reduce_rewrite_conv(THM_LIST(
          get_cm_value_number_def(),
          get_tower_wrap64_idempotent())));
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_binary_subtract_number =
    cm_prove_binary_subtract_number();
PROOF static thm cm_prove_binary_value_number_bridge(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (op:int) (left:cm_value)
         (right:cm_value) (ty:cm_type) (st:cm_src_state).
         cm_binary_ok p op left right st ==>
         ~(op == 8i &&
           cm_is_pointer (cm_value_type left) &&
           cm_is_pointer (cm_value_type right)) ==>
         cm_value_number st
           (cm_binary_value p op left right ty st) ==
         cm_binary_machine_number p op left right st`);
  gnode frontier = AUTO_INTROS_TAC(root);
  thm ok = assume_rule(
      `cm_binary_ok (p:cm_program) (op:int)
         (left:cm_value) (right:cm_value) (st:cm_src_state)`);
  thm restriction = assume_rule(
      `~((op:int) == 8i &&
         cm_is_pointer (cm_value_type (left:cm_value)) &&
         cm_is_pointer (cm_value_type (right:cm_value)))`);
  term_list tests = TERM_LIST(
      `(op:int) == 0i`, `(op:int) == 1i`,
      `(op:int) == 2i`, `(op:int) == 3i`,
      `(op:int) == 4i`, `(op:int) == 5i`,
      `(op:int) == 6i`, `(op:int) == 7i`,
      `(op:int) == 8i`, `(op:int) == 9i`,
      `(op:int) == 10i`, `(op:int) == 11i`);
  for (size_t index = 0; index < vector_size(tests); ++index) {
    term test = tests[index];
    gnode_list cases = BOOL_CASES_TAC(
        frontier, test, gc_sprintf("binary_op_%zu", index));
    thm selected = assume_rule(test);
    if (index == 8) {
      thm ok8 = conv_rule(reduce_rewrite_conv(
          THM_LIST(selected)), ok);
      thm not_both = conv_rule(reduce_rewrite_conv(
          THM_LIST(selected)), restriction);
      thm bridge = mp_rule(mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `left:cm_value`, `right:cm_value`,
          `ty:cm_type`, `st:cm_src_state`),
          cm_binary_add_number), ok8), not_both);
      gnode reduced = CONV_WITH_ASMP_TAC(cases[0],
          reduce_rewrite_conv, THM_LIST(selected, bridge));
      if (IS_NULL(reduced->solved)) {
        ACCEPT_TAC(reduced, bridge);
      }
    } else if (index == 9) {
      thm ok9 = conv_rule(reduce_rewrite_conv(
          THM_LIST(selected)), ok);
      thm bridge = mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `left:cm_value`, `right:cm_value`,
          `ty:cm_type`, `st:cm_src_state`),
          cm_binary_subtract_number), ok9);
      gnode reduced = CONV_WITH_ASMP_TAC(cases[0],
          reduce_rewrite_conv, THM_LIST(selected, bridge));
      if (IS_NULL(reduced->solved)) {
        ACCEPT_TAC(reduced, bridge);
      }
    } else {
      gnode reduced = CONV_WITH_ASMP_TAC(cases[0],
          reduce_rewrite_conv, THM_LIST(
            selected, get_cm_binary_value_def(),
            cm_binary_machine_number_def,
            get_cm_value_number_def(), cm_wrap_bool,
            get_tower_add_def(), get_tower_sub_def(),
            get_tower_mul_def(), get_tower_div_def(),
            get_tower_mod_def(),
            get_tower_wrap64_idempotent()));
      if (IS_NULL(reduced->solved)) {
        CONV_TAC(reduced, reduce_rewrite_conv(THM_LIST(
            get_cm_value_number_def(), cm_wrap_bool,
            get_tower_add_def(), get_tower_sub_def(),
            get_tower_mul_def(), get_tower_div_def(),
            get_tower_mod_def(),
            get_tower_wrap64_idempotent())));
      }
    }
    frontier = cases[1];
  }
  {
    gnode reduced = CONV_WITH_ASMP_TAC(frontier,
        reduce_rewrite_conv, THM_LIST(
          get_cm_binary_value_def(),
          cm_binary_machine_number_def,
          get_cm_value_number_def(),
          get_tower_mod_def(),
          get_tower_wrap64_idempotent()));
    if (IS_NULL(reduced->solved)) {
      CONV_TAC(reduced, reduce_rewrite_conv(THM_LIST(
          get_cm_value_number_def(),
          get_tower_mod_def(),
          get_tower_wrap64_idempotent())));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_binary_value_number_bridge =
    cm_prove_binary_value_number_bridge();


PROOF int _e_cm_binary_machine_number =
    cst_add_const_to_header(`cm_binary_machine_number`);

PROOF static thm cm_prove_unary_value_number_bridge(void) {
  gnode root = gnode_new_with_ccl(
      `!(op:int) (v:cm_value) (st:cm_src_state).
         cm_value_number st (cm_unary_value op v st) ==
         (if op == 0i
          then tower_neg (cm_value_number st v)
          else tower_bool (~cm_truth st v))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(leaf, `(op:int) == 0i`, "hop");
  for (size_t i = 0; i < 2; ++i) {
    gnode reduced = CONV_WITH_ASMP_TAC(
        cases[i], reduce_rewrite_conv, THM_LIST(
          get_cm_unary_value_def(), get_cm_value_number_def(),
          get_tower_neg_def(), get_tower_wrap64_idempotent(),
          cm_wrap_bool));
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_unary_value_number_bridge =
    cm_prove_unary_value_number_bridge();

PROOF static thm cm_prove_initialized_byte_bridge(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (vmem:int->int) (addr:int).
         cm_initialized_bytes_sim st vmem ==>
         cm_state_init st addr ==>
         cm_live_address st addr ==>
         tower_getb vmem addr ==
           tower_getb (cm_state_mem st) addr`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm simulation = eq_mp_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_initialized_bytes_sim_def)),
      `cm_initialized_bytes_sim
         (st:cm_src_state) (vmem:int->int)`),
      assume_rule(
        `cm_initialized_bytes_sim
           (st:cm_src_state) (vmem:int->int)`));
  ACCEPT_TAC(leaf, mp_rule(spec_rule(`addr:int`, simulation),
      conj_rule(
        assume_rule(`cm_state_init (st:cm_src_state) (addr:int)`),
        assume_rule(`cm_live_address (st:cm_src_state) (addr:int)`))));
  return gnode_prove(root);
}
PROOF static thm cm_initialized_byte_bridge =
    cm_prove_initialized_byte_bridge();

PROOF static thm cm_prove_initialized_word_bridge(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (vmem:int->int) (addr:int).
         cm_initialized_bytes_sim st vmem ==>
         cm_bytes_initialized (cm_state_init st) addr 8i ==>
         cm_live_span st addr 8i ==>
         tower_getw vmem addr ==
           tower_getw (cm_state_mem st) addr`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm initialized = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_bytes_initialized_def())),
      assume_rule(
        `cm_bytes_initialized
           (cm_state_init (st:cm_src_state)) (addr:int) 8i`));
  thm live_span = conv_rule(rewrite_conv(THM_LIST(
      cm_live_span_def)), assume_rule(
        `cm_live_span (st:cm_src_state) (addr:int) 8i`));
  thm_list equalities = THM_LIST();
  term_list addresses = TERM_LIST(
      `addr:int`, `(addr:int) + 1i`, `(addr:int) + 2i`,
      `(addr:int) + 3i`, `(addr:int) + 4i`,
      `(addr:int) + 5i`, `(addr:int) + 6i`,
      `(addr:int) + 7i`);
  for (int offset = 0; offset < 8; ++offset) {
    term address = addresses[offset];
    thm init = cm_sim_pick_conjunct(initialized,
        mk_comb(`cm_state_init (st:cm_src_state)`,
          address));
    thm live = mp_rule(spec_rule(address, live_span),
        int_arith_rule(
          `(addr:int) <= ${address:int} &&
           ${address:int} < addr + 8i`));
    thm byte = mp_rule(mp_rule(mp_rule(specl_rule(TERM_LIST(
        `st:cm_src_state`, `vmem:int->int`, address),
        cm_initialized_byte_bridge),
        assume_rule(
          `cm_initialized_bytes_sim
             (st:cm_src_state) (vmem:int->int)`)),
        init), live);
    vector_add(&equalities, byte);
  }
  vector_add(&equalities,
      int_arith_rule(`(addr:int) + 0i == addr`));
  vector_add(&equalities, get_tower_getw_def());
  ACCEPT_TAC(leaf, eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(equalities), goal_ccl(leaf->g))));
  return gnode_prove(root);
}
PROOF static thm cm_initialized_word_bridge =
    cm_prove_initialized_word_bridge();

PROOF static thm cm_prove_load_value_number_bridge(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type) (ptr:cm_value) (st:cm_src_state)
         (vmem:int->int).
         cm_load_ok ty ptr st ==>
         (ty == CMCharTy || ty == CMIntTy || cm_is_pointer ty) ==>
         cm_initialized_bytes_sim st vmem ==>
         cm_stored_provenance_sim st vmem ==>
         cm_live_span st (cm_value_number st ptr)
           (cm_store_width ty) ==>
         cm_value_number st (cm_load_value ty ptr st) ==
           (if ty == CMCharTy
            then tower_getb vmem (cm_value_number st ptr)
            else tower_getw vmem (cm_value_number st ptr))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm load_ok = assume_rule(
      `cm_load_ok (ty:cm_type) (ptr:cm_value) (st:cm_src_state)`);
  thm kinds = assume_rule(
      `(ty:cm_type) == CMCharTy ||
       ty == CMIntTy || cm_is_pointer ty`);
  thm initialized_sim = assume_rule(
      `cm_initialized_bytes_sim
         (st:cm_src_state) (vmem:int->int)`);
  thm provenance_sim = assume_rule(
      `cm_stored_provenance_sim
         (st:cm_src_state) (vmem:int->int)`);
  thm live_span = assume_rule(
      `cm_live_span (st:cm_src_state)
         (cm_value_number st (ptr:cm_value))
         (cm_store_width (ty:cm_type))`);
  term address =
      `cm_value_number (st:cm_src_state) (ptr:cm_value)`;
  gnode_list char_cases = BOOL_CASES_TAC(
      leaf, `(ty:cm_type) == CMCharTy`, "hchar");
  {
    thm is_char = assume_rule(`(ty:cm_type) == CMCharTy`);
    thm expanded_load = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_load_ok_def(), get_cm_store_width_def(),
        get_cm_bytes_initialized_def(), is_char)), load_ok);
    thm init = cm_sim_pick_conjunct(expanded_load,
        mk_comb(`cm_state_init (st:cm_src_state)`, address));
    thm char_live_span = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          get_cm_store_width_def(), is_char)), live_span);
    thm live = mp_rule(spec_rule(address,
        conv_rule(rewrite_conv(THM_LIST(cm_live_span_def)),
          char_live_span)),
        int_arith_rule(
          `${address:int} <= ${address:int} &&
           ${address:int} < ${address:int} + 1i`));
    thm byte = mp_rule(mp_rule(mp_rule(specl_rule(TERM_LIST(
        `st:cm_src_state`, `vmem:int->int`, address),
        cm_initialized_byte_bridge), initialized_sim), init), live);
    CONV_WITH_ASMP_TAC(char_cases[0], reduce_rewrite_conv, THM_LIST(
        get_cm_load_value_def(), get_cm_value_number_def(),
        get_tower_getb_def(), get_tower_u8_idempotent(),
        is_char, byte));
  }
  gnode_list int_cases = BOOL_CASES_TAC(
      char_cases[1], `(ty:cm_type) == CMIntTy`, "hint");
  {
    thm not_char = assume_rule(`~((ty:cm_type) == CMCharTy)`);
    thm is_int = assume_rule(`(ty:cm_type) == CMIntTy`);
    thm expanded_load = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_load_ok_def(), get_cm_store_width_def(),
        not_char, is_int)), load_ok);
    thm bytes = cm_sim_pick_conjunct(expanded_load,
        `cm_bytes_initialized
           (cm_state_init (st:cm_src_state))
           (cm_value_number st (ptr:cm_value)) 8i`);
    thm word_live = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_store_width_def(), not_char)), live_span);
    thm word = mp_rule(mp_rule(mp_rule(specl_rule(TERM_LIST(
        `st:cm_src_state`, `vmem:int->int`, address),
        cm_initialized_word_bridge), initialized_sim), bytes),
        word_live);
    CONV_WITH_ASMP_TAC(int_cases[0], reduce_rewrite_conv, THM_LIST(
        get_cm_load_value_def(), get_cm_value_number_def(),
        get_tower_getw_def(), get_tower_decode8_def(),
        get_tower_wrap64_idempotent(),
        not_char, is_int, word));
  }
  {
    thm not_char = assume_rule(`~((ty:cm_type) == CMCharTy)`);
    thm not_int = assume_rule(`~((ty:cm_type) == CMIntTy)`);
    thm pointer_kind = conv_rule(reduce_rewrite_conv(THM_LIST(
        not_char, not_int)), kinds);
    thm expanded_load = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_load_ok_def(), get_cm_store_width_def(),
        not_char)), load_ok);
    thm bytes = cm_sim_pick_conjunct(expanded_load,
        `cm_bytes_initialized
           (cm_state_init (st:cm_src_state))
           (cm_value_number st (ptr:cm_value)) 8i`);
    thm word_live = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_store_width_def(), not_char)), live_span);
    thm word = mp_rule(mp_rule(mp_rule(specl_rule(TERM_LIST(
        `st:cm_src_state`, `vmem:int->int`, address),
        cm_initialized_word_bridge), initialized_sim), bytes),
        word_live);
    gnode_list zero_cases = BOOL_CASES_TAC(
        int_cases[1],
        `tower_getw (cm_state_mem (st:cm_src_state))
           (cm_value_number st (ptr:cm_value)) == 0i`,
        "hword_zero");
    {
      thm source_zero = assume_rule(
          `tower_getw (cm_state_mem (st:cm_src_state))
             (cm_value_number st (ptr:cm_value)) == 0i`);
      CONV_WITH_ASMP_TAC(zero_cases[0], reduce_rewrite_conv, THM_LIST(
          get_cm_load_value_def(), get_cm_value_number_def(),
          not_char, not_int, source_zero, word));
    }
    {
      thm source_nonzero = assume_rule(
          `~(tower_getw (cm_state_mem (st:cm_src_state))
               (cm_value_number st (ptr:cm_value)) == 0i)`);
      thm tagged_implication = cm_sim_pick_conjunct(expanded_load,
          `cm_is_pointer (ty:cm_type) ==>
           tower_getw (cm_state_mem (st:cm_src_state))
             (cm_value_number st (ptr:cm_value)) == 0i ||
           cm_state_tagged st (cm_value_number st ptr) &&
           cm_is_pointer
             (cm_value_type
               (cm_state_tags st (cm_value_number st ptr)))`);
      thm tagged_disjunction = mp_rule(
          tagged_implication, pointer_kind);
      thm tagged = mp_rule(taut_rule(mk_imp(
          list_mk_conj(TERM_LIST(
            concl(tagged_disjunction), concl(source_nonzero))),
          `cm_state_tagged (st:cm_src_state)
             (cm_value_number st (ptr:cm_value))`)),
          conj_rule(tagged_disjunction, source_nonzero));
      thm provenance = eq_mp_rule(apply_conversion(
          rewrite_conv(THM_LIST(cm_stored_provenance_sim_def)),
          concl(provenance_sim)), provenance_sim);
      thm live = mp_rule(spec_rule(address,
          conv_rule(rewrite_conv(THM_LIST(cm_live_span_def)),
            word_live)),
          int_arith_rule(
            `${address:int} <= ${address:int} &&
             ${address:int} < ${address:int} + 8i`));
      thm stored = mp_rule(spec_rule(address, provenance),
          conj_rule(tagged, live));
      thm encoded = specl_rule(TERM_LIST(
          `st:cm_src_state`, `ty:cm_type`,
          `cm_state_tags (st:cm_src_state)
             (cm_value_number st (ptr:cm_value))`),
          get_cm_pointer_retype_number_bridge());
      CONV_WITH_ASMP_TAC(zero_cases[1],
          reduce_rewrite_conv, THM_LIST(
            get_cm_load_value_def(), not_char, not_int,
            source_nonzero, encoded,
            conjunct2_rule(stored)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_load_value_number_bridge =
    cm_prove_load_value_number_bridge();


PROOF thm get_cm_truth_number_bridge(void) {
  return cm_truth_number_bridge;
}
PROOF thm get_cm_const_immediate_number_bridge(void) {
  return cm_const_immediate_number_bridge;
}
PROOF thm get_cm_ptr_add_number_bridge(void) {
  return cm_ptr_add_number_bridge;
}
PROOF thm get_cm_ptr_member_number_bridge(void) {
  return cm_ptr_member_number_bridge;
}
PROOF thm get_cm_binary_machine_number_def(void) {
  return cm_binary_machine_number_def;
}
PROOF thm get_cm_binary_value_number_bridge(void) {
  return cm_binary_value_number_bridge;
}
PROOF thm get_cm_pointer_type_view(void) {
  return cm_pointer_type_view;
}
PROOF thm get_cm_unary_value_number_bridge(void) {
  return cm_unary_value_number_bridge;
}
PROOF thm get_cm_load_value_number_bridge(void) {
  return cm_load_value_number_bridge;
}

PROOF static int cmc_sim_ops_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_sim_ops_axioms_before,
      "cmc_sim_ops introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_sim_ops_checks = cmc_sim_ops_final_checks();
