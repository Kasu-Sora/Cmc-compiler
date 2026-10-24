#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_call_param.h"

#require "cmc_preservation_call_pending.c"
#require "cmc_preservation_store_semantic.c"

PROOF static size_t _cmc_preservation_call_param_axioms_before =
    vector_size(get_all_axioms());
PROOF static thm cm_call_param_assumption(
    const gnode node, const term wanted) {
  labeled_term_list assumptions = goal_lasmps(node->g);
  for (size_t index = 0; index < vector_size(assumptions); ++index) {
    if (alpha_compare(assumptions[index].tm, wanted) == 0) {
      return assume_rule(assumptions[index].tm);
    }
  }
  return empty_theorem;
}
PROOF static thm cm_call_param_consequence(
    const thm premise, const term conclusion) {
  return mp_rule(taut_rule(mk_imp(concl(premise), conclusion)), premise);
}



PROOF static thm cm_prove_scalar_store_shape(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type) (structs:(cm_struct_d)list).
         cm_scalar_type structs ty ==>
         ((ty == CMCharTy || ty == CMIntTy || cm_is_pointer ty) &&
          cm_type_size structs ty == cm_store_width ty)`);
  gnode_list cases = INDUCT_TAC(root, `ty:cm_type`);
  thm distinct = get_datatype_distinctness("cm_type");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    gnode reduced = CONV_WITH_ASMP_TAC(
        leaf, reduce_rewrite_conv, THM_LIST(
          get_cm_scalar_type_def(), get_cm_type_size_def(),
          get_cm_store_width_def(), get_cm_is_pointer_def(),
          get_cm_is_struct_def(), distinct));
    if (IS_NULL(reduced->solved)) {
      thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_cm_scalar_type_def(), get_cm_is_struct_def())),
          assume_rule(
            `cm_scalar_type (structs:(cm_struct_d)list)
              (CMStructTy (a:int))`));
      CONTR_TAC(reduced, impossible);
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_scalar_store_shape = cm_prove_scalar_store_shape();

PROOF static thm cm_prove_slot_region_index_member(void) {
  gnode root = gnode_new_with_ccl(
      `!(slots:(cm_slot_d)list). !(structs:(cm_struct_d)list)
         (gen:int) (base:int) (index:int).
         0i <= index ==> index < ilength slots ==>
         MEM
           (CMRegion (gen + index)
             (base + cm_slots_prefix structs slots index)
             0i (cm_slot_size structs (inth index slots)) T T)
           (cm_regions_for_slots structs slots gen base)`);
  gnode_list cases = INDUCT_TAC(root, `slots:(cm_slot_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = mp_rule(int_arith_rule(
        `0i <= (index:int) ==> index < 0i ==> F`),
        assume_rule(`0i <= (index:int)`));
    impossible = mp_rule(impossible, conv_rule(
        rewrite_conv(THM_LIST(get_theorem_by_name("ILENGTH_DEF"))),
        assume_rule(`(index:int) < ilength ([]:(cm_slot_d)list)`)));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    gnode_list zero_cases = BOOL_CASES_TAC(
        leaf, `(index:int) == 0i`, "Hindex_zero");
    {
      CONV_WITH_ASMP_TAC(
          zero_cases[0], reduce_rewrite_conv, THM_LIST(
            get_cm_regions_for_slots_def(), get_cm_slots_prefix_def(),
            get_theorem_by_name("MEM"), cm_inth_zero_cons,
            get_theorem_by_name("ILENGTH_DEF"),
            int_arith_rule(`!(x:int). x + 0i == x`)));
    }
    {
      thm lower = assume_rule(`0i <= (index:int)`);
      thm not_zero = assume_rule(`~((index:int) == 0i)`);
      thm upper = conv_rule(
          rewrite_conv(THM_LIST(get_theorem_by_name("ILENGTH_DEF"))),
          assume_rule(
            `(index:int) <
             ilength ((a0:cm_slot_d) :: (a1:(cm_slot_d)list))`));
      thm tail_lower = mp_rule(int_arith_rule(
          `0i <= (index:int) ==> ~(index == 0i) ==>
           0i <= index - 1i`), lower);
      tail_lower = mp_rule(tail_lower, not_zero);
      thm tail_upper = mp_rule(int_arith_rule(
          `(index:int) < 1i + ilength (a1:(cm_slot_d)list) ==>
           index - 1i < ilength a1`), upper);
      thm ih = specl_rule(TERM_LIST(
          `structs:(cm_struct_d)list`,
          `(gen:int) + 1i`,
          `(base:int) + cm_slot_size
            (structs:(cm_struct_d)list) (a0:cm_slot_d)`,
          `(index:int) - 1i`),
          cm_call_param_assumption(leaf,
            `!(structs:(cm_struct_d)list) (gen:int) (base:int)
               (index:int).
               0i <= index ==> index < ilength (a1:(cm_slot_d)list) ==>
               MEM
                 (CMRegion (gen + index)
                   (base + cm_slots_prefix structs a1 index)
                   0i (cm_slot_size structs (inth index a1)) T T)
                 (cm_regions_for_slots structs a1 gen base)`));
      thm tail_member = mp_rule(mp_rule(ih, tail_lower), tail_upper);
      thm one = mp_rule(int_arith_rule(
          `0i <= (index:int) ==> ~(index == 0i) ==> 1i <= index`),
          lower);
      one = mp_rule(one, not_zero);
      thm at_tail = mp_rule(ispecl_rule(TERM_LIST(
          `a0:cm_slot_d`, `a1:(cm_slot_d)list`, `index:int`),
          cm_inth_cons_tail), one);
      thm offset_exact = mp_rule(int_arith_rule(
          `1i <= (index:int) ==> index - 1i + 1i == index`), one);
      thm gen_exact = mp_rule(int_arith_rule(
          `1i <= (index:int) ==>
           ((gen:int) + 1i) + (index - 1i) == gen + index`), one);
      thm prefix = apply_conversion(reduce_rewrite_conv(THM_LIST(
          get_cm_slots_prefix_def(), not_zero)),
          `cm_slots_prefix (structs:(cm_struct_d)list)
             ((a0:cm_slot_d) :: (a1:(cm_slot_d)list)) (index:int)`);
      thm base_exact = trans_rule(
          int_ring_rule(
            `((base:int) + cm_slot_size
                (structs:(cm_struct_d)list) (a0:cm_slot_d)) +
               cm_slots_prefix structs (a1:(cm_slot_d)list)
                 ((index:int) - 1i) ==
             base +
               (cm_slot_size structs a0 +
                cm_slots_prefix structs a1 (index - 1i))`),
          beta_norm(ap_term_rule(`\amount:int. (base:int) + amount`,
              sym_rule(prefix))));
      thm normalized = conv_rule(rewrite_conv(THM_LIST(
          gen_exact, base_exact, sym_rule(at_tail))), tail_member);
      CONV_TAC(zero_cases[1], reduce_rewrite_conv(THM_LIST(
          get_cm_regions_for_slots_def(), get_theorem_by_name("MEM"),
          normalized)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_slot_region_index_member =
    cm_prove_slot_region_index_member();

PROOF static thm cm_prove_region_pointer_writable(void) {
  gnode root = gnode_new_with_ccl(
      `!(regions:(cm_region)list). !gen base hi (ty:cm_type)
         (write:bool).
         MEM (CMRegion gen base 0i hi T T) regions ==>
         cm_pointer_region_ok regions
           (CMPtrV gen 0i hi 0i ty) write`);
  gnode_list cases = INDUCT_TAC(root, `regions:(cm_region)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("MEM"))), assume_rule(
          `MEM (CMRegion (gen:int) (base:int) 0i (hi:int) T T)
            ([]:(cm_region)list)`));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    term region =
        `CMRegion (gen:int) (base:int) 0i (hi:int) T T`;
    term pointer =
        `CMPtrV (gen:int) 0i (hi:int) 0i (ty:cm_type)`;
    thm member = conv_rule(rewrite_conv(THM_LIST(
        get_theorem_by_name("MEM"))), assume_rule(
          `MEM ${region:cm_region}
            ((a0:cm_region) :: (a1:(cm_region)list))`));
    dest_disj_results parts = dest_disj(concl(member));
    term wanted =
        `cm_pointer_region_ok
          ((a0:cm_region) :: (a1:(cm_region)list))
          ${pointer:cm_value} (write:bool)`;
    thm_list head_rules = get_cm_runtime_defs();
    vector_add(&head_rules,
        int_arith_rule(`!(x:int). x <= x`));
    thm head = eqt_elim_rule(apply_conversion(
        then_conv(rewrite_conv(THM_LIST(
            get_cm_pointer_region_ok_def(),
            sym_rule(assume_rule(parts.tm1)))),
          reduce_rewrite_conv(head_rules)),
        wanted));
    thm ih = specl_rule(TERM_LIST(
        `gen:int`, `base:int`, `hi:int`, `ty:cm_type`,
        `write:bool`),
        cm_call_param_assumption(leaf,
          `!gen base hi (ty:cm_type) (write:bool).
             MEM (CMRegion gen base 0i hi T T)
               (a1:(cm_region)list) ==>
             cm_pointer_region_ok a1
               (CMPtrV gen 0i hi 0i ty) write`));
    thm tail_ok = mp_rule(ih, assume_rule(parts.tm2));
    thm tail = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_pointer_region_ok_def(), tail_ok)), wanted));
    ACCEPT_TAC(leaf, disj_cases_rule(member, head, tail));
  }
  return gnode_prove(root);
}
PROOF thm cm_region_pointer_writable =
    cm_prove_region_pointer_writable();

PROOF static thm cm_prove_exact_region_live_span(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (regions:(cm_region)list)
         (gen:int) (base:int) (width:int).
         cm_state_regions st == regions ==>
         MEM (CMRegion gen base 0i width T T) regions ==>
         cm_region_base regions gen == base ==>
         cm_live_span st base width`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode opened = CONV_TAC(
      leaf, rewrite_conv(THM_LIST(cm_live_span_def)));
  gnode at_address = AUTO_INTROS_TAC(opened);
  thm interval = assume_rule(
      `(base:int) <= (addr:int) && addr < base + (width:int)`);
  thm member = assume_rule(
      `MEM (CMRegion (gen:int) (base:int) 0i (width:int) T T)
        (regions:(cm_region)list)`);
  thm lookup = assume_rule(
      `cm_region_base (regions:(cm_region)list) (gen:int) ==
       (base:int)`);
  term body =
      `MEM (CMRegion (gen:int) (base:int) 0i (width:int) T T)
          (regions:(cm_region)list) &&
       cm_region_live (CMRegion gen base 0i width T T) &&
       cm_region_base regions
           (cm_region_gen (CMRegion gen base 0i width T T)) +
         cm_region_lo (CMRegion gen base 0i width T T) <=
           (addr:int) &&
       addr <
         cm_region_base regions
           (cm_region_gen (CMRegion gen base 0i width T T)) +
         cm_region_hi (CMRegion gen base 0i width T T)`;
  thm live = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_cm_region_live_def())),
      `cm_region_live
        (CMRegion (gen:int) (base:int) 0i (width:int) T T)`));
  thm bounds = by_defs_arith(
      `cm_region_base (regions:(cm_region)list)
           (cm_region_gen
             (CMRegion (gen:int) (base:int) 0i (width:int) T T)) +
         cm_region_lo (CMRegion gen base 0i width T T) <= (addr:int) &&
       addr <
         cm_region_base regions
           (cm_region_gen (CMRegion gen base 0i width T T)) +
         cm_region_hi (CMRegion gen base 0i width T T)`,
      THM_LIST(get_cm_region_gen_def(), get_cm_region_lo_def(),
        get_cm_region_hi_def(), lookup),
      THM_LIST(conjunct1_rule(interval), conjunct2_rule(interval)));
  thm body_proof = conj_rule(member, conj_rule(live, bounds));
  thm exists = exists_rule(
      `?region.
         MEM region (regions:(cm_region)list) &&
         cm_region_live region &&
         cm_region_base regions (cm_region_gen region) +
           cm_region_lo region <= (addr:int) &&
         addr <
           cm_region_base regions (cm_region_gen region) +
             cm_region_hi region`,
      `CMRegion (gen:int) (base:int) 0i (width:int) T T`,
      body_proof);
  thm state_regions = assume_rule(
      `cm_state_regions (st:cm_src_state) ==
       (regions:(cm_region)list)`);
  thm exists_state = conv_rule(
      rewrite_conv(THM_LIST(sym_rule(state_regions))), exists);
  thm folded = eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_live_address_def)),
      goal_ccl(at_address->g))), exists_state);
  ACCEPT_TAC(at_address, folded);
  return gnode_prove(root);
}
PROOF thm cm_exact_region_live_span =
    cm_prove_exact_region_live_span();

PROOF static thm cm_prove_parameter_store_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (old:(cm_region)list) (gen:int) (fp:int) (index:int).
         cm_function_wf p
           (inth fid (cm_program_functions p)) ==>
         cm_regions_before old gen ==>
         0i <= gen ==>
         cm_state_fp st == fp ==>
         cm_state_regions st ==
           (cm_regions_for_slots (cm_program_structs p)
             (cm_function_params
               (inth fid (cm_program_functions p)))
             gen (fp + 8i) ++ old) ==>
         0i <= index ==>
         index <
           ilength (cm_function_params
             (inth fid (cm_program_functions p))) ==>
         tower_signed64 (cm_param_offset p fid index) ==>
         tower_signed64
           (fp + cm_param_offset p fid index) ==>
         (if cm_slot_ty
               (inth index (cm_function_params
                 (inth fid (cm_program_functions p)))) == CMCharTy
          then tower_addr_valid
                 (fp + cm_param_offset p fid index)
          else tower_word_valid
                 (fp + cm_param_offset p fid index)) ==>
         (tower_signed64 (cm_param_offset p fid index) &&
          fp + cm_param_offset p fid index ==
            cm_state_fp st + cm_param_offset p fid index &&
          tower_signed64
            (fp + cm_param_offset p fid index) &&
          tower_wrap64
            (fp + cm_param_offset p fid index) ==
            cm_value_number st
              (CMPtrV (gen + index) 0i
                (cm_slot_size (cm_program_structs p)
                  (inth index (cm_function_params
                    (inth fid (cm_program_functions p)))))
                0i
                (cm_slot_ty
                  (inth index (cm_function_params
                    (inth fid (cm_program_functions p)))))) &&
          cm_store_ok
            (cm_slot_ty
              (inth index (cm_function_params
                (inth fid (cm_program_functions p)))))
            (CMPtrV (gen + index) 0i
              (cm_slot_size (cm_program_structs p)
                (inth index (cm_function_params
                  (inth fid (cm_program_functions p)))))
              0i
              (cm_slot_ty
                (inth index (cm_function_params
                  (inth fid (cm_program_functions p))))))
            st &&
          (cm_slot_ty
              (inth index (cm_function_params
                (inth fid (cm_program_functions p)))) == CMCharTy ||
           cm_slot_ty
              (inth index (cm_function_params
                (inth fid (cm_program_functions p)))) == CMIntTy ||
           cm_is_pointer
             (cm_slot_ty
               (inth index (cm_function_params
                 (inth fid (cm_program_functions p)))))) &&
          cm_live_span st
            (fp + cm_param_offset p fid index)
            (cm_store_width
              (cm_slot_ty
                (inth index (cm_function_params
                  (inth fid (cm_program_functions p)))))))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term function =
      `inth (fid:int) (cm_program_functions (p:cm_program))`;
  term structs = `cm_program_structs (p:cm_program)`;
  term params = `cm_function_params ${function:cm_function_d}`;
  term slot = `inth (index:int) ${params:(cm_slot_d)list}`;
  term ty = `cm_slot_ty ${slot:cm_slot_d}`;
  term width = `cm_store_width ${ty:cm_type}`;
  term slot_size = `cm_slot_size ${structs:(cm_struct_d)list}
      ${slot:cm_slot_d}`;
  term offset = `cm_param_offset (p:cm_program) (fid:int) (index:int)`;
  term address = `(fp:int) + ${offset:int}`;
  term pointer =
      `CMPtrV ((gen:int) + (index:int)) 0i ${slot_size:int}
        0i ${ty:cm_type}`;
  term fresh =
      `cm_regions_for_slots ${structs:(cm_struct_d)list}
        ${params:(cm_slot_d)list} (gen:int) ((fp:int) + 8i)`;
  term all_regions =
      `${fresh:(cm_region)list} ++ (old:(cm_region)list)`;
  term region =
      `CMRegion ((gen:int) + (index:int))
        (((fp:int) + 8i) +
          cm_slots_prefix ${structs:(cm_struct_d)list}
            ${params:(cm_slot_d)list} (index:int))
        0i ${slot_size:int} T T`;

  thm function_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_function_wf_def())), assume_rule(
        `cm_function_wf (p:cm_program) ${function:cm_function_d}`));
  thm params_wf = cm_call_param_consequence(function_open,
      `cm_params_wf ${structs:(cm_struct_d)list}
        ${params:(cm_slot_d)list}`);
  thm params_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_params_wf_def())), params_wf);
  thm slots_wf = conjunct1_rule(params_open);
  thm slots_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_slots_wf_def())), slots_wf);
  thm index_lower = assume_rule(`0i <= (index:int)`);
  thm index_upper = assume_rule(
      `(index:int) < ilength ${params:(cm_slot_d)list}`);
  thm slot_wf = match_mp_rule(match_mp_rule(
      spec_rule(`index:int`, slots_open), index_lower), index_upper);
  thm slot_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_slot_wf_def())), slot_wf);
  thm scalar = cm_call_param_consequence(slot_open,
      `cm_scalar_type ${structs:(cm_struct_d)list} ${ty:cm_type}`);
  thm positive = cm_call_param_consequence(slot_open,
      `0i < ${slot_size:int}`);
  thm counts = conjunct2_rule(params_open);
  thm count_zero = match_mp_rule(match_mp_rule(
      spec_rule(`index:int`, counts), index_lower), index_upper);
  thm shape = mp_rule(specl_rule(TERM_LIST(
      ty, structs), cm_scalar_store_shape), scalar);
  thm kinds = conjunct1_rule(shape);
  thm size_width = by_rewrite(
      `${slot_size:int} == ${width:int}`,
      THM_LIST(get_cm_slot_size_def(), count_zero,
        conjunct2_rule(shape)));

  thm fresh_member = mp_rule(mp_rule(specl_rule(TERM_LIST(
      params, structs, `gen:int`, `(fp:int) + 8i`, `index:int`),
      cm_slot_region_index_member), index_lower), index_upper);
  thm member_disj = disj1_rule(fresh_member,
      `MEM ${region:cm_region} (old:(cm_region)list)`);
  thm all_member = eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(get_theorem_by_name("MEM_APPEND"))),
      `MEM ${region:cm_region} ${all_regions:(cm_region)list}`)),
      member_disj);
  thm lookup_raw = mp_rule(mp_rule(specl_rule(TERM_LIST(
      structs, params, `gen:int`, `(fp:int) + 8i`,
      `old:(cm_region)list`, region), cm_slot_region_base_lookup),
      assume_rule(`cm_regions_before (old:(cm_region)list) (gen:int)`)),
      fresh_member);
  thm lookup = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_region_gen_def(), get_cm_region_base_field_def())),
      lookup_raw);

  thm read_region = mp_rule(specl_rule(TERM_LIST(
      all_regions, `(gen:int) + index`,
      `((fp:int) + 8i) +
        cm_slots_prefix ${structs:(cm_struct_d)list}
          ${params:(cm_slot_d)list} (index:int)`,
      slot_size, ty, `F`), cm_region_pointer_writable), all_member);
  thm write_region = mp_rule(specl_rule(TERM_LIST(
      all_regions, `(gen:int) + index`,
      `((fp:int) + 8i) +
        cm_slots_prefix ${structs:(cm_struct_d)list}
          ${params:(cm_slot_d)list} (index:int)`,
      slot_size, ty, `T`), cm_region_pointer_writable), all_member);
  thm generation_nonnegative = mp_rule(mp_rule(int_arith_rule(
      `0i <= (gen:int) ==> 0i <= (index:int) ==>
       0i <= gen + index`),
      assume_rule(`0i <= (gen:int)`)), index_lower);
  thm size_nonnegative = mp_rule(int_arith_rule(
      `0i < ${slot_size:int} ==> 0i <= ${slot_size:int}`),
      positive);
  thm state_regions = assume_rule(
      `cm_state_regions (st:cm_src_state) ==
       ${all_regions:(cm_region)list}`);
  thm pointer_live = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_pointer_live_def(), get_cm_ptr_gen_def(),
        get_cm_ptr_lo_def(), get_cm_ptr_hi_def(), state_regions,
        read_region, generation_nonnegative, size_nonnegative)),
      `cm_pointer_live (st:cm_src_state) ${pointer:cm_value}`));
  thm pointer_writable = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_pointer_writable_def(), pointer_live, state_regions,
        write_region)),
      `cm_pointer_writable (st:cm_src_state) ${pointer:cm_value}`));

  thm base_address = by_rewrite(
      `((fp:int) + 8i) +
         cm_slots_prefix ${structs:(cm_struct_d)list}
           ${params:(cm_slot_d)list} (index:int) ==
       ${address:int}`,
      THM_LIST(get_cm_param_offset_def(),
        int_ring_rule(`!(x:int) y z. (x + y) + z == x + (y + z)`)));
  thm number_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_value_number_def(), state_regions, lookup,
      get_cm_ptr_offset_def(), base_address,
      int_arith_rule(`!(x:int). x + 0i == x`))),
      `cm_value_number (st:cm_src_state) ${pointer:cm_value}`);
  thm number = sym_rule(number_view);

  thm live_slot = mp_rule(mp_rule(mp_rule(specl_rule(TERM_LIST(
      `st:cm_src_state`, all_regions, `(gen:int) + index`,
      `((fp:int) + 8i) +
        cm_slots_prefix ${structs:(cm_struct_d)list}
          ${params:(cm_slot_d)list} (index:int)`,
      slot_size), cm_exact_region_live_span),
      state_regions), all_member), lookup);
  thm live = conv_rule(rewrite_conv(THM_LIST(
      base_address, size_width)), live_slot);

  thm validity = assume_rule(
      `if ${ty:cm_type} == CMCharTy
       then tower_addr_valid ${address:int}
       else tower_word_valid ${address:int}`);
  thm wrap_fixed = mp_rule(
      spec_rule(address, get_tower_wrap64_fixed()),
      assume_rule(`tower_signed64 ${address:int}`));
  thm number_address = trans_rule(sym_rule(number), wrap_fixed);
  thm width_bound = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(size_width,
        int_arith_rule(`!(x:int). x <= x`))),
      `${width:int} <= ${slot_size:int}`));
  thm store_ok = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_store_ok_def(), pointer_writable,
        get_cm_ptr_lo_def(), get_cm_ptr_offset_def(),
        get_cm_ptr_hi_def(), width_bound, number_address, validity,
        int_arith_rule(`!(x:int). 0i + x == x`),
        int_arith_rule(`!(x:int). x <= x`))),
      `cm_store_ok ${ty:cm_type} ${pointer:cm_value}
        (st:cm_src_state)`));
  thm fp_equal = assume_rule(
      `cm_state_fp (st:cm_src_state) == (fp:int)`);
  thm address_fp = beta_norm(ap_term_rule(
      `\base:int. base + ${offset:int}`, sym_rule(fp_equal)));
  thm result = conj_rule(
      assume_rule(`tower_signed64 ${offset:int}`),
      conj_rule(address_fp,
        conj_rule(
          assume_rule(`tower_signed64 ${address:int}`),
          conj_rule(number,
            conj_rule(store_ok, conj_rule(kinds, live))))));
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_parameter_store_ready =
    cm_prove_parameter_store_ready();
PROOF static thm cm_prove_parameter_address_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (fp:int) (oldfp:int) (index:int).
         cm_function_wf p
           (inth fid (cm_program_functions p)) ==>
         cm_frame_segment p fid fp oldfp ==>
         0i <= index ==>
         index <
           ilength (cm_function_params
             (inth fid (cm_program_functions p))) ==>
         (tower_signed64 fp &&
          tower_signed64 (cm_param_offset p fid index) &&
          tower_signed64 (fp + cm_param_offset p fid index) &&
          (if cm_slot_ty
                (inth index (cm_function_params
                  (inth fid (cm_program_functions p)))) == CMCharTy
           then tower_addr_valid
                  (fp + cm_param_offset p fid index)
           else tower_word_valid
                  (fp + cm_param_offset p fid index)))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term function =
      `inth (fid:int) (cm_program_functions (p:cm_program))`;
  term structs = `cm_program_structs (p:cm_program)`;
  term params = `cm_function_params ${function:cm_function_d}`;
  term locals = `cm_function_locals ${function:cm_function_d}`;
  term slot = `inth (index:int) ${params:(cm_slot_d)list}`;
  term ty = `cm_slot_ty ${slot:cm_slot_d}`;
  term slot_size = `cm_slot_size ${structs:(cm_struct_d)list}
      ${slot:cm_slot_d}`;
  term width = `cm_store_width ${ty:cm_type}`;
  term prefix = `cm_slots_prefix ${structs:(cm_struct_d)list}
      ${params:(cm_slot_d)list} (index:int)`;
  term params_size =
      `cm_slots_size ${structs:(cm_struct_d)list}
        ${params:(cm_slot_d)list}`;
  term locals_size =
      `cm_slots_size ${structs:(cm_struct_d)list}
        ${locals:(cm_slot_d)list}`;
  term frame_size =
      `cm_frame_size ${structs:(cm_struct_d)list}
        ${function:cm_function_d}`;
  term offset = `cm_param_offset (p:cm_program) (fid:int) (index:int)`;
  term address = `(fp:int) + ${offset:int}`;

  thm function_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_function_wf_def())), assume_rule(
        `cm_function_wf (p:cm_program) ${function:cm_function_d}`));
  thm params_wf = cm_call_param_consequence(function_open,
      `cm_params_wf ${structs:(cm_struct_d)list}
        ${params:(cm_slot_d)list}`);
  thm params_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_params_wf_def())), params_wf);
  thm params_slots_wf = conjunct1_rule(params_open);
  thm locals_slots_wf = cm_call_param_consequence(function_open,
      `cm_slots_wf ${structs:(cm_struct_d)list}
        ${locals:(cm_slot_d)list}`);
  thm temp_nonnegative = cm_call_param_consequence(function_open,
      `0i <= cm_temp_slots ${function:cm_function_d}`);
  thm frame_upper = cm_call_param_consequence(function_open,
      `${frame_size:int} <= 1048560i`);
  thm params_positive = mp_rule(specl_rule(TERM_LIST(
      structs, params), cm_slots_wf_sizes_positive), params_slots_wf);
  thm locals_positive = mp_rule(specl_rule(TERM_LIST(
      structs, locals), cm_slots_wf_sizes_positive), locals_slots_wf);
  thm locals_nonnegative = mp_rule(specl_rule(TERM_LIST(
      structs, locals), cm_slot_sizes_positive_total), locals_positive);
  thm frame_lower = cm_call_param_consequence(function_open,
      `8i <= ${frame_size:int}`);
  thm index_lower = assume_rule(`0i <= (index:int)`);
  thm index_upper = assume_rule(
      `(index:int) < ilength ${params:(cm_slot_d)list}`);
  thm prefix_bounds = mp_rule(mp_rule(spec_rule(
      `index:int`, mp_rule(specl_rule(TERM_LIST(
        structs, params), cm_slots_prefix_cell_bounds),
        params_positive)), index_lower), index_upper);
  thm prefix_nonnegative = conjunct1_rule(prefix_bounds);
  thm prefix_cell_upper = conjunct2_rule(prefix_bounds);

  thm slots_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_slots_wf_def())), params_slots_wf);
  thm slot_wf = match_mp_rule(match_mp_rule(
      spec_rule(`index:int`, slots_open), index_lower), index_upper);
  thm slot_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_slot_wf_def())), slot_wf);
  thm scalar = cm_call_param_consequence(slot_open,
      `cm_scalar_type ${structs:(cm_struct_d)list} ${ty:cm_type}`);
  thm slot_positive = cm_call_param_consequence(slot_open,
      `0i < ${slot_size:int}`);
  thm counts = conjunct2_rule(params_open);
  thm count_zero = match_mp_rule(match_mp_rule(
      spec_rule(`index:int`, counts), index_lower), index_upper);
  thm shape = mp_rule(specl_rule(TERM_LIST(
      ty, structs), cm_scalar_store_shape), scalar);
  thm size_width = by_rewrite(
      `${slot_size:int} == ${width:int}`,
      THM_LIST(get_cm_slot_size_def(), count_zero,
        conjunct2_rule(shape)));
  thm width_positive = conv_rule(rewrite_conv(THM_LIST(
      size_width)), slot_positive);

  thm frame_open = conv_rule(rewrite_conv(THM_LIST(
      cm_frame_segment_def)), assume_rule(
        `cm_frame_segment (p:cm_program) (fid:int)
          (fp:int) (oldfp:int)`));
  thm static_lower = cm_call_param_consequence(frame_open,
      `16i <= cm_static_size (p:cm_program)`);
  thm fp_above_static = cm_call_param_consequence(frame_open,
      `cm_static_size (p:cm_program) <= (fp:int)`);
  thm frame_end = cm_call_param_consequence(frame_open,
      `(fp:int) + ${frame_size:int} == (oldfp:int)`);
  thm oldfp_upper = cm_call_param_consequence(frame_open,
      `(oldfp:int) <= 1048576i`);
  thm fp_nonnegative = mp_rule(mp_rule(int_arith_rule(
      `16i <= cm_static_size (p:cm_program) ==>
       cm_static_size p <= (fp:int) ==> 0i <= fp`),
      static_lower), fp_above_static);

  thm fp_upper = mp_rule(mp_rule(mp_rule(int_arith_rule(
      `8i <= ${frame_size:int} ==>
       (fp:int) + ${frame_size:int} == (oldfp:int) ==>
       oldfp <= 1048576i ==> fp <= 1048576i`),
      frame_lower), frame_end), oldfp_upper);
  thm fp_bounds = mp_rule(mp_rule(int_arith_rule(
      `0i <= (fp:int) ==> fp <= 1048576i ==>
       --9223372036854775808i <= fp &&
       fp <= 9223372036854775807i`),
      fp_nonnegative), fp_upper);
  thm fp_signed_view = apply_conversion(rewrite_conv(THM_LIST(
      get_tower_signed64_def())), `tower_signed64 (fp:int)`);
  thm fp_signed = eq_mp_rule(sym_rule(fp_signed_view), fp_bounds);

  thm frame_param_raw = mp_rule(mp_rule(int_arith_rule(
      `0i <= ${locals_size:int} ==>
       0i <= cm_temp_slots ${function:cm_function_d} ==>
       8i + ${params_size:int} <=
         8i + ${params_size:int} + ${locals_size:int} +
           8i * cm_temp_slots ${function:cm_function_d}`),
      locals_nonnegative), temp_nonnegative);
  thm frame_param_bound = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(get_cm_frame_size_def()))), frame_param_raw);

  thm offset_lower_raw = mp_rule(int_arith_rule(
      `0i <= ${prefix:int} ==> 0i <= 8i + ${prefix:int}`),
      prefix_nonnegative);
  thm offset_lower_view = apply_conversion(rewrite_conv(THM_LIST(
      get_cm_param_offset_def())), `0i <= ${offset:int}`);
  thm offset_lower =
      eq_mp_rule(sym_rule(offset_lower_view), offset_lower_raw);
  thm offset_upper_raw = mp_rule(mp_rule(mp_rule(
      int_arith_rule(
        `${prefix:int} + ${slot_size:int} <= ${params_size:int} ==>
         0i < ${slot_size:int} ==>
         8i + ${params_size:int} <= ${frame_size:int} ==>
         8i + ${prefix:int} <= ${frame_size:int}`),
      prefix_cell_upper), slot_positive), frame_param_bound);
  thm offset_upper_view = apply_conversion(rewrite_conv(THM_LIST(
      get_cm_param_offset_def())),
      `${offset:int} <= ${frame_size:int}`);
  thm offset_upper =
      eq_mp_rule(sym_rule(offset_upper_view), offset_upper_raw);
  thm offset_bounds = mp_rule(mp_rule(mp_rule(int_arith_rule(
      `0i <= ${offset:int} ==>
       ${offset:int} <= ${frame_size:int} ==>
       ${frame_size:int} <= 1048560i ==>
       --9223372036854775808i <= ${offset:int} &&
       ${offset:int} <= 9223372036854775807i`),
      offset_lower), offset_upper), frame_upper);
  thm offset_signed_view = apply_conversion(rewrite_conv(THM_LIST(
      get_tower_signed64_def())), `tower_signed64 ${offset:int}`);
  thm offset_signed =
      eq_mp_rule(sym_rule(offset_signed_view), offset_bounds);

  thm address_lower = mp_rule(mp_rule(int_arith_rule(
      `0i <= (fp:int) ==> 0i <= ${offset:int} ==>
       0i <= fp + ${offset:int}`),
      fp_nonnegative), offset_lower);
  thm address_end_raw = mp_rule(mp_rule(mp_rule(mp_rule(
      mp_rule(int_arith_rule(
        `${prefix:int} + ${slot_size:int} <= ${params_size:int} ==>
         ${slot_size:int} == ${width:int} ==>
         8i + ${params_size:int} <= ${frame_size:int} ==>
         (fp:int) + ${frame_size:int} == (oldfp:int) ==>
         oldfp <= 1048576i ==>
         (fp + 8i + ${prefix:int}) + ${width:int} <= 1048576i`),
        prefix_cell_upper), size_width), frame_param_bound),
      frame_end), oldfp_upper);
  thm address_end_view = apply_conversion(rewrite_conv(THM_LIST(
      get_cm_param_offset_def())),
      `${address:int} + ${width:int} <= 1048576i`);
  thm address_end =
      eq_mp_rule(sym_rule(address_end_view), address_end_raw);
  thm address_bounds = mp_rule(mp_rule(mp_rule(int_arith_rule(
      `0i <= ${address:int} ==>
       ${address:int} + ${width:int} <= 1048576i ==>
       0i < ${width:int} ==>
       --9223372036854775808i <= ${address:int} &&
       ${address:int} <= 9223372036854775807i`),
      address_lower), address_end), width_positive);
  thm address_signed_view = apply_conversion(rewrite_conv(THM_LIST(
      get_tower_signed64_def())), `tower_signed64 ${address:int}`);
  thm address_signed =
      eq_mp_rule(sym_rule(address_signed_view), address_bounds);

  gnode_list cases = BOOL_CASES_TAC(
      leaf, `${ty:cm_type} == CMCharTy`, "Hchar");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    bool is_char = i == 0;
    thm char_case = assume_rule(is_char
        ? `${ty:cm_type} == CMCharTy`
        : `~(${ty:cm_type} == CMCharTy)`);
    term concrete_width_value = is_char ? `1i:int` : `8i:int`;
    thm concrete_width = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_store_width_def(), char_case)),
        `${width:int} == ${concrete_width_value:int}`));
    thm raw_valid = mp_rule(mp_rule(mp_rule(
        is_char
          ? int_arith_rule(
              `0i <= ${address:int} ==>
               ${address:int} + ${width:int} <= 1048576i ==>
               ${width:int} == 1i ==>
               0i <= ${address:int} &&
               ${address:int} < 1048576i`)
          : int_arith_rule(
              `0i <= ${address:int} ==>
               ${address:int} + ${width:int} <= 1048576i ==>
               ${width:int} == 8i ==>
               0i <= ${address:int} &&
               ${address:int} + 7i < 1048576i`),
        address_lower), address_end), concrete_width);
    term valid_term = is_char
        ? `tower_addr_valid ${address:int}`
        : `tower_word_valid ${address:int}`;
    thm valid_view = apply_conversion(rewrite_conv(THM_LIST(
        is_char
          ? get_tower_addr_valid_def()
          : get_tower_word_valid_def())), valid_term);
    thm valid = eq_mp_rule(sym_rule(valid_view), raw_valid);
    thm conditional_valid = eq_mp_rule(sym_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(char_case)),
        `if ${ty:cm_type} == CMCharTy
         then tower_addr_valid ${address:int}
         else tower_word_valid ${address:int}`)), valid);
    ACCEPT_TAC(cases[i], conj_rule(fp_signed,
        conj_rule(offset_signed,
          conj_rule(address_signed, conditional_valid))));
  }
  return gnode_prove(root);
}
PROOF thm cm_parameter_address_ready =
    cm_prove_parameter_address_ready();


PROOF thm get_cm_scalar_store_shape(void) {
  return cm_scalar_store_shape;
}
PROOF thm get_cm_slot_region_index_member(void) {
  return cm_slot_region_index_member;
}

PROOF thm get_cm_region_pointer_writable(void) {
  return cm_region_pointer_writable;
}
PROOF thm get_cm_exact_region_live_span(void) {
  return cm_exact_region_live_span;
}
PROOF thm get_cm_parameter_store_ready(void) {
  return cm_parameter_store_ready;
}
PROOF thm get_cm_parameter_address_ready(void) {
  return cm_parameter_address_ready;
}
PROOF static int cmc_preservation_call_param_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_call_param_axioms_before,
      "cmc_preservation_call_param introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_call_param_checks =
    cmc_preservation_call_param_final_checks();
