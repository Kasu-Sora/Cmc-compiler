#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_machine_store.h"
#require "cmc_preservation_machine_store.c"
#include "cmc_preservation_runtime.h"

PROOF static size_t _cmc_preservation_runtime_axioms_before =
    vector_size(get_all_axioms());

PROOF thm cm_call_frames_range_safe_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_call_frames_range_safe (base:int) (width:int)
         ([]:(cm_call_sim_frame)list) <=> T) &&
     (!frame rest.
        cm_call_frames_range_safe base width
          ((frame:cm_call_sim_frame) :: rest) <=>
        cm_range_disjoint base width (cm_call_sim_base frame) 8i &&
        cm_call_frames_range_safe base width rest)`);

PROOF thm cm_spill_list_range_safe_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_spill_list_range_safe (p:cm_program) (fid:int) (fp:int)
         (base:int) (width:int) ([]:(cm_spill)list) <=> T) &&
     (!spill rest.
        cm_spill_list_range_safe p fid fp base width
          ((spill:cm_spill) :: rest) <=>
        cm_range_disjoint base width
          (fp + cm_temp_offset p fid (cm_spill_slot spill)) 8i &&
        cm_spill_list_range_safe p fid fp base width rest)`);

PROOF thm cm_spill_frames_range_safe_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_spill_frames_range_safe (p:cm_program) (base:int)
         (width:int) ([]:(cm_spill_frame)list) <=> T) &&
     (!frame rest.
        cm_spill_frames_range_safe p base width
          ((frame:cm_spill_frame) :: rest) <=>
        cm_spill_list_range_safe p (cm_spill_frame_fid frame)
          (cm_spill_frame_fp frame) base width
          (cm_spill_frame_spills frame) &&
        cm_spill_frames_range_safe p base width rest)`);

PROOF thm cm_machine_range_safe_def = new_fun_definition(
    `cm_machine_range_safe (p:cm_program) (base:int) (width:int)
       (calls:(cm_call_sim_frame)list)
       (spill_frames:(cm_spill_frame)list) : bool =
       (cm_range_disjoint base width 8i 8i &&
        cm_call_frames_range_safe base width calls &&
        cm_spill_frames_range_safe p base width spill_frames)`);

PROOF thm cm_region_runtime_safe_def = new_fun_definition(
    `cm_region_runtime_safe (p:cm_program)
       (calls:(cm_call_sim_frame)list)
       (spill_frames:(cm_spill_frame)list)
       (regions:(cm_region)list) (region:cm_region) : bool =
       (~cm_region_live region ||
        (0i <= cm_region_lo region &&
         cm_region_lo region <= cm_region_hi region &&
         0i <= cm_region_base regions (cm_region_gen region) +
                 cm_region_lo region &&
         cm_region_base regions (cm_region_gen region) +
                 cm_region_hi region <= 1048576i &&
         cm_machine_range_safe p
           (cm_region_base regions (cm_region_gen region) +
             cm_region_lo region)
           (cm_region_hi region - cm_region_lo region)
           calls spill_frames))`);

PROOF thm cm_regions_runtime_safe_def = new_fun_definition(
    `cm_regions_runtime_safe (p:cm_program)
       (calls:(cm_call_sim_frame)list)
       (spill_frames:(cm_spill_frame)list)
       (regions:(cm_region)list) : bool =
       (!(region:cm_region).
          MEM region regions ==>
          cm_region_runtime_safe p calls spill_frames regions region)`);

PROOF thm cm_runtime_memory_layout_def = new_fun_definition(
    `cm_runtime_memory_layout (p:cm_program) (st:cm_src_state)
       (calls:(cm_call_sim_frame)list)
       (spill_frames:(cm_spill_frame)list) : bool =
       cm_regions_runtime_safe p calls spill_frames
         (cm_state_regions st)`);

PROOF static int _e_cm_call_frames_range_safe =
    cst_add_const_to_header(`cm_call_frames_range_safe`);
PROOF static int _e_cm_spill_list_range_safe =
    cst_add_const_to_header(`cm_spill_list_range_safe`);
PROOF static int _e_cm_spill_frames_range_safe =
    cst_add_const_to_header(`cm_spill_frames_range_safe`);
PROOF static int _e_cm_machine_range_safe =
    cst_add_const_to_header(`cm_machine_range_safe`);
PROOF static int _e_cm_region_runtime_safe =
    cst_add_const_to_header(`cm_region_runtime_safe`);
PROOF static int _e_cm_regions_runtime_safe =
    cst_add_const_to_header(`cm_regions_runtime_safe`);
PROOF static int _e_cm_runtime_memory_layout =
    cst_add_const_to_header(`cm_runtime_memory_layout`);

PROOF static thm cm_prove_range_disjoint_subrange(void) {
  gnode root = gnode_new_with_ccl(
      `!(outer:int) (outer_width:int) (inner:int) (inner_width:int)
         (other:int) (other_width:int).
         outer <= inner ==>
         inner + inner_width <= outer + outer_width ==>
         cm_range_disjoint outer outer_width other other_width ==>
         cm_range_disjoint inner inner_width other other_width`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm disjoint = conv_rule(rewrite_conv(
      THM_LIST(cm_range_disjoint_def)),
      assume_rule(
        `cm_range_disjoint (outer:int) (outer_width:int)
           (other:int) (other_width:int)`));
  thm result = int_arith_rule(
      `(outer:int) <= (inner:int) ==>
       inner + (inner_width:int) <= outer + (outer_width:int) ==>
       (outer + outer_width <= (other:int) ||
        other + (other_width:int) <= outer) ==>
       (inner + inner_width <= other ||
        other + other_width <= inner)`);
  result = mp_rule(result, assume_rule(`(outer:int) <= (inner:int)`));
  result = mp_rule(result, assume_rule(
      `(inner:int) + (inner_width:int) <=
       (outer:int) + (outer_width:int)`));
  result = mp_rule(result, disjoint);
  gnode opened = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(cm_range_disjoint_def)));
  ACCEPT_TAC(opened, result);
  return gnode_prove(root);
}
PROOF thm cm_range_disjoint_subrange =
    cm_prove_range_disjoint_subrange();

PROOF static thm cm_prove_pointer_region_witness(void) {
  gnode root = gnode_new_with_ccl(
      `!(regions:(cm_region)list) (ptr:cm_value).
         cm_pointer_region_ok regions ptr T ==>
         ?region.
           MEM region regions &&
           cm_region_gen region == cm_ptr_gen ptr &&
           cm_region_live region &&
           cm_region_writable region &&
           cm_region_lo region <= cm_ptr_lo ptr &&
           cm_ptr_hi ptr <= cm_region_hi region`);
  gnode with_regions = GEN_TAC(root, "regions");
  gnode_list cases =
      INDUCT_TAC(with_regions, `regions:(cm_region)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(
        THM_LIST(get_cm_pointer_region_ok_def())),
        assume_rule(goal_lasmps(leaf->g)[0].tm));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm opened = conv_rule(rewrite_conv(THM_LIST(
        get_cm_pointer_region_ok_def())),
        assume_rule(
          `cm_pointer_region_ok
             ((a0:cm_region) :: (a1:(cm_region)list))
             (ptr:cm_value) T`));
    thm left = assume_rule(
        `cm_region_gen (a0:cm_region) == cm_ptr_gen (ptr:cm_value) &&
         cm_region_live a0 && cm_region_lo a0 <= cm_ptr_lo ptr &&
         cm_ptr_hi ptr <= cm_region_hi a0 && cm_region_writable a0`);
    term left_rest_term =
        `cm_region_gen (a0:cm_region) == cm_ptr_gen (ptr:cm_value) &&
         cm_region_live a0 && cm_region_writable a0 &&
         cm_region_lo a0 <= cm_ptr_lo ptr &&
         cm_ptr_hi ptr <= cm_region_hi a0`;
    thm left_rest = mp_rule(
        taut_rule(mk_imp(concl(left), left_rest_term)), left);
    thm left_body_expanded = conj_rule(
        disj1_rule(refl_rule(`a0:cm_region`),
          `MEM (a0:cm_region) (a1:(cm_region)list)`),
        left_rest);
    term expanded_witness =
        `?region.
           (region == (a0:cm_region) ||
            MEM region (a1:(cm_region)list)) &&
           cm_region_gen region == cm_ptr_gen (ptr:cm_value) &&
           cm_region_live region && cm_region_writable region &&
           cm_region_lo region <= cm_ptr_lo ptr &&
           cm_ptr_hi ptr <= cm_region_hi region`;
    thm left_exists = exists_rule(expanded_witness,
        `a0:cm_region`, left_body_expanded);
    thm tail_exists = match_mp_rule(
        spec_rule(`ptr:cm_value`,
          assume_rule(goal_lasmps(leaf->g)[0].tm)),
        assume_rule(
          `cm_pointer_region_ok (a1:(cm_region)list)
             (ptr:cm_value) T`));
    thm tail_body = assume_rule(
        `MEM (region:cm_region) (a1:(cm_region)list) &&
         cm_region_gen region == cm_ptr_gen (ptr:cm_value) &&
         cm_region_live region && cm_region_writable region &&
         cm_region_lo region <= cm_ptr_lo ptr &&
         cm_ptr_hi ptr <= cm_region_hi region`);
    thm tail_mem = disj2_rule(
        `(region:cm_region) == (a0:cm_region)`,
        conjunct1_rule(tail_body));
    thm tail_cons =
        conj_rule(tail_mem, conjunct2_rule(tail_body));
    thm tail_witness = exists_rule(expanded_witness,
        `region:cm_region`, tail_cons);
    thm tail_case = choose_rule(`region:cm_region`,
        tail_exists, tail_witness);
    thm result =
        disj_cases_rule(opened, left_exists, tail_case);
    gnode reduced = CONV_TAC(leaf, rewrite_conv(
        THM_LIST(get_theorem_by_name("MEM"))));
    ACCEPT_TAC(reduced, result);
  }
  return gnode_prove(root);
}
PROOF thm cm_pointer_region_witness =
    cm_prove_pointer_region_witness();

PROOF static thm cm_prove_call_frames_range_subrange(void) {
  gnode root = gnode_new_with_ccl(
      `!(outer:int) (outer_width:int) (inner:int) (ty:cm_type)
         (frames:(cm_call_sim_frame)list).
         outer <= inner ==>
         inner + cm_store_width ty <= outer + outer_width ==>
         cm_call_frames_range_safe outer outer_width frames ==>
         cm_call_frames_store_safe ty inner frames`);
  gnode with_outer = GEN_TAC(root, "outer");
  gnode with_width = GEN_TAC(with_outer, "outer_width");
  gnode with_inner = GEN_TAC(with_width, "inner");
  gnode with_type = GEN_TAC(with_inner, "ty");
  gnode_list cases =
      INDUCT_TAC(with_type, `frames:(cm_call_sim_frame)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        cm_call_frames_range_safe_def,
        cm_call_frames_store_safe_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm safe = conv_rule(rewrite_conv(THM_LIST(
        cm_call_frames_range_safe_def)), assume_rule(
          `cm_call_frames_range_safe (outer:int) (outer_width:int)
             ((a0:cm_call_sim_frame) ::
              (a1:(cm_call_sim_frame)list))`));
    thm head = match_mp_rule(
        match_mp_rule(
          match_mp_rule(specl_rule(TERM_LIST(
            `outer:int`, `outer_width:int`, `inner:int`,
            `cm_store_width (ty:cm_type)`,
            `cm_call_sim_base (a0:cm_call_sim_frame)`, `8i:int`),
            cm_range_disjoint_subrange),
            assume_rule(`(outer:int) <= (inner:int)`)),
          assume_rule(
            `(inner:int) + cm_store_width (ty:cm_type) <=
             outer + (outer_width:int)`)),
        conjunct1_rule(safe));
    thm tail = match_mp_rule(
        match_mp_rule(
          match_mp_rule(
            assume_rule(goal_lasmps(leaf->g)[0].tm),
            assume_rule(`(outer:int) <= (inner:int)`)),
          assume_rule(
            `(inner:int) + cm_store_width (ty:cm_type) <=
             outer + (outer_width:int)`)),
        conjunct2_rule(safe));
    gnode opened = CONV_TAC(leaf, rewrite_conv(THM_LIST(
        cm_call_frames_store_safe_def)));
    ACCEPT_TAC(opened, conj_rule(head, tail));
  }
  return gnode_prove(root);
}
PROOF thm cm_call_frames_range_subrange =
    cm_prove_call_frames_range_subrange();

PROOF static thm cm_prove_spill_list_range_subrange(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (fp:int)
         (outer:int) (outer_width:int) (inner:int) (ty:cm_type)
         (spills:(cm_spill)list).
         outer <= inner ==>
         inner + cm_store_width ty <= outer + outer_width ==>
         cm_spill_list_range_safe p fid fp outer outer_width spills ==>
         cm_spill_list_store_safe p fid fp ty inner spills`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_fid = GEN_TAC(with_program, "fid");
  gnode with_fp = GEN_TAC(with_fid, "fp");
  gnode with_outer = GEN_TAC(with_fp, "outer");
  gnode with_width = GEN_TAC(with_outer, "outer_width");
  gnode with_inner = GEN_TAC(with_width, "inner");
  gnode with_type = GEN_TAC(with_inner, "ty");
  gnode_list cases =
      INDUCT_TAC(with_type, `spills:(cm_spill)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        cm_spill_list_range_safe_def,
        cm_spill_list_store_safe_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm safe = conv_rule(rewrite_conv(THM_LIST(
        cm_spill_list_range_safe_def)), assume_rule(
          `cm_spill_list_range_safe (p:cm_program) (fid:int) (fp:int)
             (outer:int) (outer_width:int)
             ((a0:cm_spill) :: (a1:(cm_spill)list))`));
    term cell =
        `(fp:int) + cm_temp_offset (p:cm_program) (fid:int)
           (cm_spill_slot (a0:cm_spill))`;
    thm head = match_mp_rule(
        match_mp_rule(
          match_mp_rule(specl_rule(TERM_LIST(
            `outer:int`, `outer_width:int`, `inner:int`,
            `cm_store_width (ty:cm_type)`, cell, `8i:int`),
            cm_range_disjoint_subrange),
            assume_rule(`(outer:int) <= (inner:int)`)),
          assume_rule(
            `(inner:int) + cm_store_width (ty:cm_type) <=
             outer + (outer_width:int)`)),
        conjunct1_rule(safe));
    thm tail = match_mp_rule(
        match_mp_rule(
          match_mp_rule(
            assume_rule(goal_lasmps(leaf->g)[0].tm),
            assume_rule(`(outer:int) <= (inner:int)`)),
          assume_rule(
            `(inner:int) + cm_store_width (ty:cm_type) <=
             outer + (outer_width:int)`)),
        conjunct2_rule(safe));
    gnode opened = CONV_TAC(leaf, rewrite_conv(THM_LIST(
        cm_spill_list_store_safe_def)));
    ACCEPT_TAC(opened, conj_rule(head, tail));
  }
  return gnode_prove(root);
}
PROOF thm cm_spill_list_range_subrange =
    cm_prove_spill_list_range_subrange();

PROOF static thm cm_prove_spill_frames_range_subrange(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (outer:int) (outer_width:int)
         (inner:int) (ty:cm_type)
         (frames:(cm_spill_frame)list).
         outer <= inner ==>
         inner + cm_store_width ty <= outer + outer_width ==>
         cm_spill_frames_range_safe p outer outer_width frames ==>
         cm_spill_frames_store_safe p ty inner frames`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_outer = GEN_TAC(with_program, "outer");
  gnode with_width = GEN_TAC(with_outer, "outer_width");
  gnode with_inner = GEN_TAC(with_width, "inner");
  gnode with_type = GEN_TAC(with_inner, "ty");
  gnode_list cases =
      INDUCT_TAC(with_type, `frames:(cm_spill_frame)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        cm_spill_frames_range_safe_def,
        cm_spill_frames_store_safe_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm safe = conv_rule(rewrite_conv(THM_LIST(
        cm_spill_frames_range_safe_def)), assume_rule(
          `cm_spill_frames_range_safe (p:cm_program)
             (outer:int) (outer_width:int)
             ((a0:cm_spill_frame) ::
              (a1:(cm_spill_frame)list))`));
    thm head = match_mp_rule(
        match_mp_rule(
          match_mp_rule(specl_rule(TERM_LIST(
            `p:cm_program`, `cm_spill_frame_fid (a0:cm_spill_frame)`,
            `cm_spill_frame_fp (a0:cm_spill_frame)`,
            `outer:int`, `outer_width:int`, `inner:int`,
            `ty:cm_type`,
            `cm_spill_frame_spills (a0:cm_spill_frame)`),
            cm_spill_list_range_subrange),
            assume_rule(`(outer:int) <= (inner:int)`)),
          assume_rule(
            `(inner:int) + cm_store_width (ty:cm_type) <=
             outer + (outer_width:int)`)),
        conjunct1_rule(safe));
    thm tail = match_mp_rule(
        match_mp_rule(
          match_mp_rule(
            assume_rule(goal_lasmps(leaf->g)[0].tm),
            assume_rule(`(outer:int) <= (inner:int)`)),
          assume_rule(
            `(inner:int) + cm_store_width (ty:cm_type) <=
             outer + (outer_width:int)`)),
        conjunct2_rule(safe));
    gnode opened = CONV_TAC(leaf, rewrite_conv(THM_LIST(
        cm_spill_frames_store_safe_def)));
    ACCEPT_TAC(opened, conj_rule(head, tail));
  }
  return gnode_prove(root);
}
PROOF thm cm_spill_frames_range_subrange =
    cm_prove_spill_frames_range_subrange();

PROOF static thm cm_prove_machine_range_subrange(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (outer:int) (outer_width:int)
         (inner:int) (ty:cm_type)
         (calls:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list).
         outer <= inner ==>
         inner + cm_store_width ty <= outer + outer_width ==>
         cm_machine_range_safe p outer outer_width calls spill_frames ==>
         cm_machine_store_safe p ty inner calls spill_frames`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm safe = conv_rule(rewrite_conv(THM_LIST(
      cm_machine_range_safe_def)), assume_rule(
        `cm_machine_range_safe (p:cm_program)
           (outer:int) (outer_width:int)
           (calls:(cm_call_sim_frame)list)
           (spill_frames:(cm_spill_frame)list)`));
  thm lower = assume_rule(`(outer:int) <= (inner:int)`);
  thm upper = assume_rule(
      `(inner:int) + cm_store_width (ty:cm_type) <=
       outer + (outer_width:int)`);
  thm fp_safe = match_mp_rule(
      match_mp_rule(
        match_mp_rule(specl_rule(TERM_LIST(
          `outer:int`, `outer_width:int`, `inner:int`,
          `cm_store_width (ty:cm_type)`, `8i:int`, `8i:int`),
          cm_range_disjoint_subrange), lower), upper),
      conjunct1_rule(safe));
  thm call_safe = match_mp_rule(
      match_mp_rule(
        match_mp_rule(specl_rule(TERM_LIST(
          `outer:int`, `outer_width:int`, `inner:int`,
          `ty:cm_type`, `calls:(cm_call_sim_frame)list`),
          cm_call_frames_range_subrange), lower), upper),
      conjunct1_rule(conjunct2_rule(safe)));
  thm spill_safe = match_mp_rule(
      match_mp_rule(
        match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `outer:int`, `outer_width:int`,
          `inner:int`, `ty:cm_type`,
          `spill_frames:(cm_spill_frame)list`),
          cm_spill_frames_range_subrange), lower), upper),
      conjunct2_rule(conjunct2_rule(safe)));
  gnode opened = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      cm_machine_store_safe_def)));
  ACCEPT_TAC(opened, conj_rule(
      fp_safe, conj_rule(call_safe, spill_safe)));
  return gnode_prove(root);
}
PROOF thm cm_machine_range_subrange =
    cm_prove_machine_range_subrange();

PROOF static thm cm_prove_pointer_writable_number(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (ptr:cm_value).
         cm_pointer_writable st ptr ==>
         cm_value_number st ptr ==
           tower_wrap64
             (cm_region_base (cm_state_regions st)
                (cm_ptr_gen ptr) + cm_ptr_offset ptr)`);
  gnode with_state = GEN_TAC(root, "st");
  gnode_list cases = INDUCT_TAC(with_state, `ptr:cm_value`);
  for (size_t i = 0; i < 3; ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_pointer_writable_def(), get_cm_pointer_live_def(),
        get_cm_ptr_gen_def())),
        assume_rule(goal_lasmps(leaf->g)[0].tm));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[3]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_value_number_def(), get_cm_ptr_gen_def(),
        get_cm_ptr_offset_def())));
  }
  return gnode_prove(root);
}
PROOF thm cm_pointer_writable_number =
    cm_prove_pointer_writable_number();

PROOF static thm cm_prove_store_width_positive(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type). 1i <= cm_store_width ty`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      leaf, `(ty:cm_type) == CMCharTy`, "hchar");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_WITH_ASMP_TAC(cases[i], reduce_rewrite_conv,
        THM_LIST(get_cm_store_width_def()));
  }
  return gnode_prove(root);
}
PROOF thm cm_store_width_positive =
    cm_prove_store_width_positive();

PROOF static thm cm_prove_runtime_live_span_bounds(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state)
         (calls:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         (base:int) (width:int).
         cm_runtime_memory_layout p st calls spill_frames ==>
         cm_live_span st base width ==>
         1i <= width ==>
         0i <= base && base + width <= 1048576i`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm layout = conv_rule(rewrite_conv(THM_LIST(
      cm_runtime_memory_layout_def,
      cm_regions_runtime_safe_def)), assume_rule(
        `cm_runtime_memory_layout (p:cm_program) (st:cm_src_state)
          (calls:(cm_call_sim_frame)list)
          (spill_frames:(cm_spill_frame)list)`));
  thm live_span = conv_rule(rewrite_conv(THM_LIST(
      cm_live_span_def)), assume_rule(
        `cm_live_span (st:cm_src_state) (base:int) (width:int)`));
  thm width_positive = assume_rule(`1i <= (width:int)`);
  thm lower_live = match_mp_rule(
      spec_rule(`base:int`, live_span),
      mp_rule(int_arith_rule(
        `1i <= (width:int) ==>
         (base:int) <= base && base < base + width`),
        width_positive));
  term last = `(base:int) + (width:int) - 1i`;
  thm upper_live = match_mp_rule(
      spec_rule(last, live_span),
      mp_rule(int_arith_rule(
        `1i <= (width:int) ==>
         (base:int) <= base + width - 1i &&
         base + width - 1i < base + width`),
        width_positive));
  thm lower_exists = conv_rule(rewrite_conv(THM_LIST(
      cm_live_address_def)), lower_live);
  thm upper_exists = conv_rule(rewrite_conv(THM_LIST(
      cm_live_address_def)), upper_live);

  thm lower_body = assume_rule(
      `MEM (lower_region:cm_region)
         (cm_state_regions (st:cm_src_state)) &&
       cm_region_live lower_region &&
       cm_region_base (cm_state_regions st)
           (cm_region_gen lower_region) +
         cm_region_lo lower_region <= (base:int) &&
       base <
         cm_region_base (cm_state_regions st)
           (cm_region_gen lower_region) +
         cm_region_hi lower_region`);
  thm lower_safe = match_mp_rule(
      spec_rule(`lower_region:cm_region`, layout),
      conjunct1_rule(lower_body));
  lower_safe = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_region_runtime_safe_def,
      conjunct1_rule(conjunct2_rule(lower_body)))),
      lower_safe);
  thm lower_bound = int_arith_rule(
      `0i <=
         cm_region_base (cm_state_regions (st:cm_src_state))
           (cm_region_gen (lower_region:cm_region)) +
         cm_region_lo lower_region ==>
       cm_region_base (cm_state_regions st)
           (cm_region_gen lower_region) +
         cm_region_lo lower_region <= (base:int) ==>
       0i <= base`);
  lower_bound = mp_rule(lower_bound,
      conjunct1_rule(conjunct2_rule(conjunct2_rule(lower_safe))));
  lower_bound = mp_rule(lower_bound,
      conjunct1_rule(conjunct2_rule(conjunct2_rule(lower_body))));
  thm lower_result =
      choose_rule(`lower_region:cm_region`, lower_exists, lower_bound);

  thm upper_body = assume_rule(
      `MEM (upper_region:cm_region)
         (cm_state_regions (st:cm_src_state)) &&
       cm_region_live upper_region &&
       cm_region_base (cm_state_regions st)
           (cm_region_gen upper_region) +
         cm_region_lo upper_region <= ${last:int} &&
       ${last:int} <
         cm_region_base (cm_state_regions st)
           (cm_region_gen upper_region) +
         cm_region_hi upper_region`);
  thm upper_safe = match_mp_rule(
      spec_rule(`upper_region:cm_region`, layout),
      conjunct1_rule(upper_body));
  upper_safe = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_region_runtime_safe_def,
      conjunct1_rule(conjunct2_rule(upper_body)))),
      upper_safe);
  thm upper_bound = int_arith_rule(
      `${last:int} <
         cm_region_base (cm_state_regions (st:cm_src_state))
           (cm_region_gen (upper_region:cm_region)) +
         cm_region_hi upper_region ==>
       cm_region_base (cm_state_regions st)
           (cm_region_gen upper_region) +
         cm_region_hi upper_region <= 1048576i ==>
       (base:int) + (width:int) <= 1048576i`);
  upper_bound = mp_rule(upper_bound,
      conjunct2_rule(conjunct2_rule(conjunct2_rule(upper_body))));
  upper_bound = mp_rule(upper_bound,
      conjunct1_rule(conjunct2_rule(conjunct2_rule(
        conjunct2_rule(upper_safe)))));
  thm upper_result =
      choose_rule(`upper_region:cm_region`, upper_exists, upper_bound);
  ACCEPT_TAC(leaf, conj_rule(lower_result, upper_result));
  return gnode_prove(root);
}
PROOF thm cm_runtime_live_span_bounds =
    cm_prove_runtime_live_span_bounds();

PROOF static thm cm_runtime_consequence(
    const thm premise, const term conclusion) {
  return mp_rule(taut_rule(mk_imp(concl(premise), conclusion)),
      premise);
}

PROOF static thm cm_prove_runtime_store_safe(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state)
         (calls:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         (ty:cm_type) (ptr:cm_value).
         cm_runtime_memory_layout p st calls spill_frames ==>
         cm_store_ok ty ptr st ==>
         cm_machine_store_safe p ty (cm_value_number st ptr)
           calls spill_frames`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm layout = conv_rule(rewrite_conv(THM_LIST(
      cm_runtime_memory_layout_def,
      cm_regions_runtime_safe_def)), assume_rule(
        `cm_runtime_memory_layout (p:cm_program) (st:cm_src_state)
           (calls:(cm_call_sim_frame)list)
           (spill_frames:(cm_spill_frame)list)`));
  thm store = conv_rule(rewrite_conv(THM_LIST(
      get_cm_store_ok_def())), assume_rule(
        `cm_store_ok (ty:cm_type) (ptr:cm_value)
           (st:cm_src_state)`));
  thm writable = conjunct1_rule(store);
  thm writable_parts = conv_rule(rewrite_conv(THM_LIST(
      get_cm_pointer_writable_def())), writable);
  thm region_exists = match_mp_rule(
      specl_rule(TERM_LIST(
        `cm_state_regions (st:cm_src_state)`, `ptr:cm_value`),
        cm_pointer_region_witness),
      conjunct2_rule(writable_parts));

  thm witness = assume_rule(
      `MEM (region:cm_region) (cm_state_regions (st:cm_src_state)) &&
       cm_region_gen region == cm_ptr_gen (ptr:cm_value) &&
       cm_region_live region && cm_region_writable region &&
       cm_region_lo region <= cm_ptr_lo ptr &&
       cm_ptr_hi ptr <= cm_region_hi region`);
  thm member = conjunct1_rule(witness);
  thm live = cm_runtime_consequence(
      witness, `cm_region_live (region:cm_region)`);
  thm can_write = cm_runtime_consequence(
      witness, `cm_region_writable (region:cm_region)`);
  thm region_safe = mp_rule(
      spec_rule(`region:cm_region`, layout), member);
  thm region_parts = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_region_runtime_safe_def, live, can_write)), region_safe);

  term base =
      `cm_region_base (cm_state_regions (st:cm_src_state))
         (cm_region_gen (region:cm_region))`;
  term outer =
      `${base:int} + cm_region_lo (region:cm_region)`;
  term outer_width =
      `cm_region_hi (region:cm_region) -
         cm_region_lo region`;
  term inner =
      `${base:int} + cm_ptr_offset (ptr:cm_value)`;
  thm outer_nonnegative =
      conjunct1_rule(conjunct2_rule(conjunct2_rule(region_parts)));
  thm region_upper = conjunct1_rule(conjunct2_rule(
      conjunct2_rule(conjunct2_rule(region_parts))));
  thm full_range = conjunct2_rule(conjunct2_rule(
      conjunct2_rule(conjunct2_rule(region_parts))));
  thm region_lo_ptr = cm_runtime_consequence(witness,
      `cm_region_lo (region:cm_region) <=
       cm_ptr_lo (ptr:cm_value)`);
  thm ptr_region_hi = cm_runtime_consequence(witness,
      `cm_ptr_hi (ptr:cm_value) <=
       cm_region_hi (region:cm_region)`);
  thm ptr_lo_offset =
      conjunct1_rule(conjunct2_rule(store));
  thm offset_width = conjunct1_rule(
      conjunct2_rule(conjunct2_rule(store)));
  thm lower = int_arith_rule(
      `cm_region_lo (region:cm_region) <=
         cm_ptr_lo (ptr:cm_value) ==>
       cm_ptr_lo ptr <= cm_ptr_offset ptr ==>
       (${outer:int}) <= (${inner:int})`);
  lower = mp_rule(lower, region_lo_ptr);
  lower = mp_rule(lower, ptr_lo_offset);
  thm upper = int_arith_rule(
      `cm_ptr_offset (ptr:cm_value) + cm_store_width (ty:cm_type) <=
         cm_ptr_hi ptr ==>
       cm_ptr_hi ptr <= cm_region_hi (region:cm_region) ==>
       (${inner:int}) + cm_store_width ty <=
         (${outer:int}) + (${outer_width:int})`);
  upper = mp_rule(upper, offset_width);
  upper = mp_rule(upper, ptr_region_hi);
  thm raw_safe = match_mp_rule(
      match_mp_rule(
        match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, outer, outer_width, inner,
          `ty:cm_type`, `calls:(cm_call_sim_frame)list`,
          `spill_frames:(cm_spill_frame)list`),
          cm_machine_range_subrange), lower), upper),
      full_range);

  thm width_positive =
      spec_rule(`ty:cm_type`, cm_store_width_positive);
  thm raw_signed_bounds = int_arith_rule(
      `0i <= (${outer:int}) ==>
       (${outer:int}) <= (${inner:int}) ==>
       (${inner:int}) + cm_store_width (ty:cm_type) <=
         (${outer:int}) + (${outer_width:int}) ==>
       (${base:int}) + cm_region_hi (region:cm_region) <=
         1048576i ==>
       1i <= cm_store_width ty ==>
       --9223372036854775808i <= (${inner:int}) &&
       (${inner:int}) <= 9223372036854775807i`);
  raw_signed_bounds =
      mp_rule(raw_signed_bounds, outer_nonnegative);
  raw_signed_bounds = mp_rule(raw_signed_bounds, lower);
  raw_signed_bounds = mp_rule(raw_signed_bounds, upper);
  raw_signed_bounds = mp_rule(raw_signed_bounds, region_upper);
  raw_signed_bounds = mp_rule(raw_signed_bounds, width_positive);
  thm signed_value = eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(get_tower_signed64_def())),
      `tower_signed64 (${inner:int})`)), raw_signed_bounds);
  thm wrap_fixed = mp_rule(
      spec_rule(inner, get_tower_wrap64_fixed()), signed_value);
  thm pointer_number = match_mp_rule(
      specl_rule(TERM_LIST(`st:cm_src_state`, `ptr:cm_value`),
        cm_pointer_writable_number), writable);
  thm generation = cm_runtime_consequence(witness,
      `cm_region_gen (region:cm_region) ==
       cm_ptr_gen (ptr:cm_value)`);
  pointer_number = conv_rule(rewrite_conv(
      THM_LIST(sym_rule(generation))), pointer_number);
  thm number_raw = trans_rule(pointer_number, wrap_fixed);
  thm numbered_safe = conv_rule(rewrite_conv(
      THM_LIST(sym_rule(number_raw))), raw_safe);
  thm result = choose_rule(
      `region:cm_region`, region_exists, numbered_safe);
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_runtime_store_safe =
    cm_prove_runtime_store_safe();

PROOF thm get_cm_runtime_memory_layout_def(void) {
  return cm_runtime_memory_layout_def;
}
PROOF thm get_cm_runtime_store_safe(void) {
  return cm_runtime_store_safe;
}
PROOF thm get_cm_runtime_live_span_bounds(void) {
  return cm_runtime_live_span_bounds;
}
PROOF thm get_cm_store_width_positive(void) {
  return cm_store_width_positive;
}

PROOF static int cmc_preservation_runtime_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_runtime_axioms_before,
      "cmc_preservation_runtime introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_runtime_final_checks =
    cmc_preservation_runtime_final_checks();
