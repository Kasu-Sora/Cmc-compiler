#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_static_bases.h"
#include "cmc_preservation_generation_task.h"
#include "cmc_preservation_invariant_step.h"

#require "cmc_preservation_generation_static_task.c"
#require "cmc_preservation_invariant_step.c"

PROOF static size_t _cmc_preservation_static_bases_axioms_before =
    vector_size(get_all_axioms());

PROOF thm cm_task_static_bases_def = new_rec_definition(
    get_cm_task_recursion(),
    `(!q input p.
        cm_task_static_bases (p:cm_program)
          (CMStartTask (q:cm_program) (input:(int)list)) = (q == p)) &&
     (!q fid expr st ks p.
        cm_task_static_bases (p:cm_program)
          (CMRTask (q:cm_program) (fid:int) (expr:cm_expr)
            (st:cm_src_state) (ks:(cm_frame)list)) =
        (q == p &&
         cm_region_bases_below_equal
           (cm_state_regions st) (cm_static_regions p)
           (cm_first_dynamic_generation p))) &&
     (!q fid expr st ks p.
        cm_task_static_bases (p:cm_program)
          (CMLTask (q:cm_program) (fid:int) (expr:cm_expr)
            (st:cm_src_state) (ks:(cm_frame)list)) =
        (q == p &&
         cm_region_bases_below_equal
           (cm_state_regions st) (cm_static_regions p)
           (cm_first_dynamic_generation p))) &&
     (!q fid stmt st ks p.
        cm_task_static_bases (p:cm_program)
          (CMSTask (q:cm_program) (fid:int) (stmt:cm_stmt)
            (st:cm_src_state) (ks:(cm_frame)list)) =
        (q == p &&
         cm_region_bases_below_equal
           (cm_state_regions st) (cm_static_regions p)
           (cm_first_dynamic_generation p))) &&
     (!q fid value st ks p.
        cm_task_static_bases (p:cm_program)
          (CMVTask (q:cm_program) (fid:int) (value:cm_value)
            (st:cm_src_state) (ks:(cm_frame)list)) =
        (q == p &&
         cm_region_bases_below_equal
           (cm_state_regions st) (cm_static_regions p)
           (cm_first_dynamic_generation p))) &&
     (!q fid control st ks p.
        cm_task_static_bases (p:cm_program)
          (CMCTask (q:cm_program) (fid:int) (control:cm_control)
            (st:cm_src_state) (ks:(cm_frame)list)) =
        (q == p &&
         cm_region_bases_below_equal
           (cm_state_regions st) (cm_static_regions p)
           (cm_first_dynamic_generation p))) &&
     (!st control status p.
        cm_task_static_bases (p:cm_program)
          (CMDoneTask (st:cm_src_state) (control:cm_control)
            (status:int)) =
        cm_region_bases_below_equal
          (cm_state_regions st) (cm_static_regions p)
          (cm_first_dynamic_generation p))`);
PROOF static int _e_cm_task_static_bases =
    cst_add_const_to_header(`cm_task_static_bases`);

PROOF static thm cm_prove_task_static_bases_initial(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (input:(int)list).
         cm_task_static_bases p (CMStartTask p input)`);
  CONV_TAC(AUTO_INTROS_TAC(root),
      reduce_rewrite_conv(THM_LIST(cm_task_static_bases_def)));
  return gnode_prove(root);
}
PROOF thm cm_task_static_bases_initial =
    cm_prove_task_static_bases_initial();

PROOF static thm cm_prove_string_region_at_member(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (strings:(cm_string_d)list).
         !start sid.
           0i <= sid ==>
           sid < ilength strings ==>
           MEM
             (CMRegion
               (cm_string_generation p (start + sid))
               (cm_string_address p (start + sid)) 0i
               (ilength (cm_string_bytes (inth sid strings)) + 1i)
               F T)
             (cm_string_regions p strings start)`);
  gnode with_program = GEN_TAC(root, "p");
  gnode_list cases = INDUCT_TAC(with_program,
      `strings:(cm_string_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm upper_negative = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          get_theorem_by_name("ILENGTH_DEF"))),
        assume_rule(
          `(sid:int) < ilength ([]:(cm_string_d)list)`));
    thm impossible = mp_rule(mp_rule(int_arith_rule(
        `0i <= (sid:int) ==> sid < 0i ==> F`),
        assume_rule(`0i <= (sid:int)`)), upper_negative);
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    gnode_list sid_cases = BOOL_CASES_TAC(
        leaf, `(sid:int) == 0i`, "Hsid");
    {
      thm head_member = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            assume_rule(`(sid:int) == 0i`),
            int_arith_rule(`(start:int) + 0i == start`),
            get_cm_string_regions_def(),
            get_theorem_by_name("MEM"), cm_inth_zero_cons,
            get_theorem_by_name("ILENGTH_DEF"))),
          goal_ccl(sid_cases[0]->g)));
      ACCEPT_TAC(sid_cases[0], head_member);
    }
    {
      thm lower = assume_rule(`0i <= (sid:int)`);
      thm upper = assume_rule(
          `(sid:int) < ilength
            ((a0:cm_string_d) :: (a1:(cm_string_d)list))`);
      thm nonzero = assume_rule(`~((sid:int) == 0i)`);
      thm one = mp_rule(mp_rule(int_arith_rule(
          `0i <= (sid:int) ==> ~(sid == 0i) ==> 1i <= sid`),
          lower), nonzero);
      thm tail_lower = mp_rule(int_arith_rule(
          `1i <= (sid:int) ==> 0i <= sid - 1i`), one);
      thm tail_upper = mp_rule(mp_rule(int_arith_rule(
          `(sid:int) < 1i + ilength (a1:(cm_string_d)list) ==>
           1i <= sid ==>
           sid - 1i < ilength a1`),
          conv_rule(reduce_rewrite_conv(THM_LIST(
            get_theorem_by_name("ILENGTH_DEF"))), upper)), one);
      thm ih = specl_rule(TERM_LIST(
          `(start:int) + 1i`, `(sid:int) - 1i`),
          assume_rule(goal_lasmps(sid_cases[1]->g)[0].tm));
      thm tail_member = mp_rule(mp_rule(ih, tail_lower), tail_upper);
      thm at_tail = mp_rule(ispecl_rule(TERM_LIST(
          `a0:cm_string_d`, `a1:(cm_string_d)list`, `sid:int`),
          cm_inth_cons_tail), one);
      thm index_exact = int_ring_rule(
          `((start:int) + 1i) + ((sid:int) - 1i) == start + sid`);
      tail_member = conv_rule(rewrite_conv(THM_LIST(
          index_exact, sym_rule(at_tail))), tail_member);
      thm target_view = apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_cm_string_regions_def(),
            get_theorem_by_name("MEM"))),
          goal_ccl(sid_cases[1]->g));
      ACCEPT_TAC(sid_cases[1], eq_mp_rule(
          sym_rule(target_view),
          disj2_rule(
            `CMRegion
               (cm_string_generation (p:cm_program)
                 ((start:int) + (sid:int)))
               (cm_string_address p (start + sid)) 0i
               (ilength
                 (cm_string_bytes
                   (inth sid
                     ((a0:cm_string_d) :: (a1:(cm_string_d)list)))) + 1i)
               F T ==
             CMRegion
               (cm_string_generation p start)
               (cm_string_address p start) 0i
               (ilength (cm_string_bytes a0) + 1i) F T`,
            tail_member)));
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_string_region_at_member =
    cm_prove_string_region_at_member();

PROOF static thm cm_prove_task_static_bases_string_number(void) {
  term task =
      `CMRTask (p:cm_program) (fid:int)
        (CMStringE (sid:int) (ty:cm_type))
        (st:cm_src_state) (ks:(cm_frame)list)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (sid:int) (ty:cm_type)
         (st:cm_src_state) (ks:(cm_frame)list).
         cm_task_static_valid
           (CMRTask p fid (CMStringE sid ty) st ks) ==>
         cm_task_static_bases p
           (CMRTask p fid (CMStringE sid ty) st ks) ==>
         tower_wrap64 (cm_string_address p sid) ==
           cm_value_number st (cm_string_pointer p sid)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm static_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_static_valid_def, cm_expr_static_valid_def)),
      assume_rule(mk_comb(`cm_task_static_valid`, task)));
  thm sid_bounds = conjunct1_rule(static_open);
  thm member_strings = match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `cm_program_strings (p:cm_program)`,
        `0i`, `sid:int`), cm_string_region_at_member),
      conjunct1_rule(sid_bounds)), conjunct2_rule(sid_bounds));
  thm zero_index = int_arith_rule(`0i + (sid:int) == sid`);
  member_strings = conv_rule(rewrite_conv(THM_LIST(zero_index)),
      member_strings);
  term descriptor =
      `CMRegion
        (cm_string_generation (p:cm_program) (sid:int))
        (cm_string_address p sid) 0i
        (ilength
          (cm_string_bytes
            (inth sid (cm_program_strings p))) + 1i)
        F T`;
  thm member_static = eq_mp_rule(
      sym_rule(apply_conversion(rewrite_conv(THM_LIST(
        cm_static_regions_def,
        get_theorem_by_name("MEM_APPEND"))),
        `MEM ${descriptor:cm_region}
          (cm_static_regions (p:cm_program))`)),
      disj2_rule(
        `MEM ${descriptor:cm_region}
          (cm_global_regions (p:cm_program)
            (cm_program_globals p) 0i)`, member_strings));
  thm static_lookup = match_mp_rule(
      specl_rule(TERM_LIST(`p:cm_program`, descriptor),
        cm_static_region_base_member), member_static);
  static_lookup = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_region_gen_def(), get_cm_region_base_field_def())),
      static_lookup);
  thm generation_bound = mp_rule(int_arith_rule(
      `(sid:int) < ilength (cm_program_strings (p:cm_program)) ==>
       1i + ilength (cm_program_globals p) + sid <
         1i + ilength (cm_program_globals p) +
           ilength (cm_program_strings p)`),
      conjunct2_rule(sid_bounds));
  thm generation_view = apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_string_generation_def(),
        get_cm_first_dynamic_generation_def())),
      `cm_string_generation (p:cm_program) (sid:int) <
       cm_first_dynamic_generation p`);
  generation_bound =
      eq_mp_rule(sym_rule(generation_view), generation_bound);
  thm bases_open = conv_rule(rewrite_conv(THM_LIST(
      cm_task_static_bases_def,
      cm_region_bases_below_equal_def)),
      assume_rule(mk_comb(`cm_task_static_bases (p:cm_program)`, task)));
  thm current_static = match_mp_rule(
      spec_rule(`cm_string_generation (p:cm_program) (sid:int)`,
        bases_open), generation_bound);
  thm current_address = trans_rule(current_static, static_lookup);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_string_pointer_def(), get_cm_value_number_def(),
      get_cm_ptr_offset_def(),
      int_arith_rule(`!(x:int). x + 0i == x`))),
      goal_ccl(leaf->g));
  thm wrapped = ap_term_rule(`tower_wrap64`,
      sym_rule(current_address));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), wrapped));
  return gnode_prove(root);
}
PROOF thm cm_task_static_bases_string_number =
    cm_prove_task_static_bases_string_number();

PROOF thm get_cm_task_static_bases_def(void) {
  return cm_task_static_bases_def;
}
PROOF thm get_cm_task_static_bases_initial(void) {
  return cm_task_static_bases_initial;
}
PROOF thm get_cm_task_static_bases_string_number(void) {
  return cm_task_static_bases_string_number;
}

PROOF static int cmc_preservation_static_bases_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_static_bases_axioms_before,
      "cmc_preservation_static_bases introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_task_static_bases_initial)) == 0 &&
      vector_size(hyp(cm_task_static_bases_string_number)) == 0,
      "static-base theorem is not closed");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_static_bases_checks =
    cmc_preservation_static_bases_final_checks();
