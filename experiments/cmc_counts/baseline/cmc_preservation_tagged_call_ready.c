#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_tagged_call_ready.h"

#require "cmc_preservation_tagged_call.c"
#require "cmc_preservation_target_call_params.c"

PROOF static size_t _cmc_preservation_tagged_call_ready_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_tagged_call_ready_consequence(
    const thm premise, const term conclusion) {
  return mp_rule(taut_rule(mk_imp(concl(premise), conclusion)), premise);
}

PROOF static thm cm_prove_param_stores_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(values:(cm_value)list).
         !(p:cm_program) (fid:int) (st:cm_src_state)
           (old:(cm_region)list) (gen:int) (fp:int) (oldfp:int)
           (index:int).
         cm_function_wf p
           (inth fid (cm_program_functions p)) ==>
         cm_frame_segment p fid fp oldfp ==>
         cm_regions_before old gen ==>
         0i <= gen ==>
         cm_state_fp st == fp ==>
         cm_state_regions st ==
           (cm_regions_for_slots (cm_program_structs p)
             (cm_function_params
               (inth fid (cm_program_functions p)))
             gen (fp + 8i) ++ old) ==>
         (!j. 0i <= j ==>
              j < ilength (cm_function_params
                (inth fid (cm_program_functions p))) ==>
              cm_state_env st 2i j ==
                CMPtrV (gen + j) 0i
                  (cm_slot_size (cm_program_structs p)
                    (inth j (cm_function_params
                      (inth fid (cm_program_functions p)))))
                  0i
                  (cm_slot_ty (inth j (cm_function_params
                    (inth fid (cm_program_functions p)))))) ==>
         0i <= index ==>
         index + ilength values <=
           ilength (cm_function_params
             (inth fid (cm_program_functions p))) ==>
         cm_param_stores_ok p fid values index st`);
  gnode_list cases = INDUCT_TAC(root, `values:(cm_value)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        cm_param_stores_ok_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    term full =
        `cm_function_params
          (inth (fid:int) (cm_program_functions (p:cm_program)))`;
    term tail_state =
        `cm_store_params_reverse (p:cm_program) (fid:int)
          (a1:(cm_value)list) ((index:int) + 1i)
          (st:cm_src_state)`;
    term ty = `cm_slot_ty (inth (index:int)
        ${full:(cm_slot_d)list})`;
    term pointer =
        `CMPtrV ((gen:int) + (index:int)) 0i
          (cm_slot_size (cm_program_structs (p:cm_program))
            (inth (index:int) ${full:(cm_slot_d)list}))
          0i ${ty:cm_type}`;
    term offset = `cm_param_offset (p:cm_program) (fid:int) (index:int)`;
    term address = `(fp:int) + ${offset:int}`;

    thm total_raw = conv_rule(rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))), assume_rule(
          `(index:int) + ilength
             ((a0:cm_value) :: (a1:(cm_value)list)) <=
           ilength ${full:(cm_slot_d)list}`));
    thm rest_nonnegative = ispec_rule(
        `a1:(cm_value)list`, get_theorem_by_name("ILENGTH_NONNEG"));
    thm index_lower = assume_rule(`0i <= (index:int)`);
    thm tail_index_lower = mp_rule(int_arith_rule(
        `0i <= (index:int) ==> 0i <= index + 1i`), index_lower);
    thm index_upper = mp_rule(mp_rule(int_arith_rule(
        `(index:int) + (1i + ilength (a1:(cm_value)list)) <=
             ilength ${full:(cm_slot_d)list} ==>
         0i <= ilength a1 ==>
         index < ilength ${full:(cm_slot_d)list}`),
        total_raw), rest_nonnegative);
    thm tail_total = mp_rule(int_arith_rule(
        `(index:int) + (1i + ilength (a1:(cm_value)list)) <=
             ilength ${full:(cm_slot_d)list} ==>
         (index + 1i) + ilength a1 <=
           ilength ${full:(cm_slot_d)list}`), total_raw);

    thm tail_ok = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`,
        `old:(cm_region)list`, `gen:int`, `fp:int`, `oldfp:int`,
        `(index:int) + 1i`), assume_rule(goal_lasmps(leaf->g)[0].tm));
    tail_ok = match_mp_rule(tail_ok, assume_rule(
        `cm_function_wf (p:cm_program)
          (inth (fid:int) (cm_program_functions p))`));
    tail_ok = match_mp_rule(tail_ok, assume_rule(
        `cm_frame_segment (p:cm_program) (fid:int)
          (fp:int) (oldfp:int)`));
    tail_ok = match_mp_rule(tail_ok, assume_rule(
        `cm_regions_before (old:(cm_region)list) (gen:int)`));
    tail_ok = match_mp_rule(tail_ok, assume_rule(`0i <= (gen:int)`));
    tail_ok = match_mp_rule(tail_ok, assume_rule(
        `cm_state_fp (st:cm_src_state) == (fp:int)`));
    tail_ok = match_mp_rule(tail_ok, assume_rule(
        `cm_state_regions (st:cm_src_state) ==
         (cm_regions_for_slots (cm_program_structs p)
           ${full:(cm_slot_d)list} (gen:int) ((fp:int) + 8i) ++
          (old:(cm_region)list))`));
    tail_ok = match_mp_rule(tail_ok, assume_rule(
        `!j. 0i <= j ==> j < ilength ${full:(cm_slot_d)list} ==>
             cm_state_env (st:cm_src_state) 2i j ==
               CMPtrV ((gen:int) + j) 0i
                 (cm_slot_size (cm_program_structs p)
                   (inth j ${full:(cm_slot_d)list}))
                 0i (cm_slot_ty
                   (inth j ${full:(cm_slot_d)list}))`));
    tail_ok = match_mp_rule(tail_ok, tail_index_lower);
    tail_ok = match_mp_rule(tail_ok, tail_total);

    thm tail_structure = specl_rule(TERM_LIST(
        `a1:(cm_value)list`, `p:cm_program`, `fid:int`,
        `(index:int) + 1i`, `st:cm_src_state`),
        cm_store_params_reverse_structure);
    thm tail_fp = trans_rule(cm_tagged_call_ready_consequence(
        tail_structure,
        `cm_state_fp ${tail_state:cm_src_state} ==
         cm_state_fp (st:cm_src_state)`), assume_rule(
          `cm_state_fp (st:cm_src_state) == (fp:int)`));
    thm tail_regions = trans_rule(cm_tagged_call_ready_consequence(
        tail_structure,
        `cm_state_regions ${tail_state:cm_src_state} ==
         cm_state_regions (st:cm_src_state)`), assume_rule(
          `cm_state_regions (st:cm_src_state) ==
           (cm_regions_for_slots (cm_program_structs p)
             ${full:(cm_slot_d)list} (gen:int) ((fp:int) + 8i) ++
            (old:(cm_region)list))`));

    thm numeric = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `fp:int`, `oldfp:int`,
        `index:int`), cm_parameter_address_ready);
    numeric = match_mp_rule(numeric, assume_rule(
        `cm_function_wf (p:cm_program)
          (inth (fid:int) (cm_program_functions p))`));
    numeric = match_mp_rule(numeric, assume_rule(
        `cm_frame_segment (p:cm_program) (fid:int)
          (fp:int) (oldfp:int)`));
    numeric = match_mp_rule(numeric, index_lower);
    numeric = match_mp_rule(numeric, index_upper);
    thm offset_signed = cm_tagged_call_ready_consequence(
        numeric, `tower_signed64 ${offset:int}`);
    thm address_signed = cm_tagged_call_ready_consequence(
        numeric, `tower_signed64 ${address:int}`);
    thm validity = cm_tagged_call_ready_consequence(numeric,
        `if ${ty:cm_type} == CMCharTy
         then tower_addr_valid ${address:int}
         else tower_word_valid ${address:int}`);

    thm ready = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, tail_state,
        `old:(cm_region)list`, `gen:int`, `fp:int`, `index:int`),
        cm_parameter_store_ready);
    ready = match_mp_rule(ready, assume_rule(
        `cm_function_wf (p:cm_program)
          (inth (fid:int) (cm_program_functions p))`));
    ready = match_mp_rule(ready, assume_rule(
        `cm_regions_before (old:(cm_region)list) (gen:int)`));
    ready = match_mp_rule(ready, assume_rule(`0i <= (gen:int)`));
    ready = match_mp_rule(ready, tail_fp);
    ready = match_mp_rule(ready, tail_regions);
    ready = match_mp_rule(ready, index_lower);
    ready = match_mp_rule(ready, index_upper);
    ready = match_mp_rule(ready, offset_signed);
    ready = match_mp_rule(ready, address_signed);
    ready = match_mp_rule(ready, validity);
    thm canonical_store_ok = cm_tagged_call_ready_consequence(ready,
        `cm_store_ok ${ty:cm_type} ${pointer:cm_value}
          ${tail_state:cm_src_state}`);

    thm env_cell = match_mp_rule(match_mp_rule(
        spec_rule(`index:int`, assume_rule(
          `!j. 0i <= j ==> j < ilength ${full:(cm_slot_d)list} ==>
               cm_state_env (st:cm_src_state) 2i j ==
                 CMPtrV ((gen:int) + j) 0i
                   (cm_slot_size (cm_program_structs p)
                     (inth j ${full:(cm_slot_d)list}))
                   0i (cm_slot_ty
                     (inth j ${full:(cm_slot_d)list}))`)),
        index_lower), index_upper);
    thm tail_env = specl_rule(TERM_LIST(
        `a1:(cm_value)list`, `p:cm_program`, `fid:int`,
        `(index:int) + 1i`, `st:cm_src_state`),
        cm_store_params_reverse_env);
    thm tail_env_cell = beta_norm(ap_term_rule(
        `\env:int->int->cm_value. env 2i (index:int)`, tail_env));
    thm env_pointer = trans_rule(tail_env_cell, env_cell);
    thm actual_store_ok = conv_rule(rewrite_conv(THM_LIST(
        sym_rule(env_pointer))), canonical_store_ok);
    thm body = conj_rule(tail_ok, actual_store_ok);
    thm view = apply_conversion(rewrite_conv(THM_LIST(
        cm_param_stores_ok_def)), goal_ccl(leaf->g));
    ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(view), body));
  }
  return gnode_prove(root);
}
PROOF thm cm_param_stores_ready = cm_prove_param_stores_ready();

PROOF static int cmc_preservation_tagged_call_ready_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_tagged_call_ready_axioms_before,
      "cmc_preservation_tagged_call_ready introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_param_stores_ready)) == 0,
      "parameter stores readiness theorem is not closed");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_tagged_call_ready_checks =
    cmc_preservation_tagged_call_ready_final_checks();
