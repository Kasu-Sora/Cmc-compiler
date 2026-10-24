#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_annotate_model.h"
#include "cmc_preservation_store_metadata.h"
#require "cmc_preservation_store_metadata.c"
#require "cmc_annotate_model.c"
#include "cmc_preservation_machine_store.h"

PROOF static size_t _cmc_preservation_machine_store_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_machine_store(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state) (target:tvm_state)
         (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         (ptr:cm_value) (v:cm_value) (values:(cm_value)list)
         (suffix:(int)list) (ty:cm_type).
         cm_machine_state_sim p st target frames spill_frames
           (ptr :: v :: values) suffix ==>
         cm_machine_store_safe p ty (cm_value_number st ptr)
           frames spill_frames ==>
         cm_machine_state_sim p (cm_state_store ty ptr v st)
           (tvm_next_state target
             (TL (TL (tvm_stack target)))
             (tvm_calls target)
             (if ty == CMCharTy
              then tower_setb (tvm_mem target)
                     (cm_value_number st ptr)
                     (cm_value_number st v)
              else tower_setw (tvm_mem target)
                     (cm_value_number st ptr)
                     (cm_value_number st v))
             (tvm_input target) (tvm_output target))
           frames spill_frames values suffix`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm simulation = assume_rule(
      `cm_machine_state_sim (p:cm_program) (st:cm_src_state)
         (target:tvm_state) (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         ((ptr:cm_value) :: (v:cm_value) ::
          (values:(cm_value)list)) (suffix:(int)list)`);
  thm parts = conv_rule(rewrite_conv(THM_LIST(cm_machine_sim_parts)),
      simulation);
  thm initialized = conjunct1_rule(parts);
  thm after_initialized = conjunct2_rule(parts);
  thm provenance = conjunct1_rule(after_initialized);
  thm after_provenance = conjunct2_rule(after_initialized);
  thm fp = conjunct1_rule(after_provenance);
  thm after_fp = conjunct2_rule(after_provenance);
  thm calls = conjunct1_rule(after_fp);
  thm after_calls = conjunct2_rule(after_fp);
  thm spills = conjunct1_rule(after_calls);
  thm after_spills = conjunct2_rule(after_calls);
  thm input_equal = conjunct1_rule(after_spills);
  thm after_input = conjunct2_rule(after_spills);
  thm output_equal = conjunct1_rule(after_input);
  thm operand = conjunct2_rule(after_input);
  thm safety = conv_rule(rewrite_conv(THM_LIST(
      cm_machine_store_safe_def)), assume_rule(
        `cm_machine_store_safe (p:cm_program) (ty:cm_type)
           (cm_value_number (st:cm_src_state) (ptr:cm_value))
           (frames:(cm_call_sim_frame)list)
           (spill_frames:(cm_spill_frame)list)`));
  thm after_fp_safe = conjunct2_rule(safety);
  thm normalized_memory = specl_rule(TERM_LIST(
      `ty:cm_type`, `ptr:cm_value`, `v:cm_value`,
      `st:cm_src_state`, `tvm_mem (target:tvm_state)`),
      cm_store_mem_target);
  term number =
      `cm_value_number (st:cm_src_state)
        (cm_convert_value st (ty:cm_type) (v:cm_value))`;
  thm new_initialized = mp_rule(specl_rule(TERM_LIST(
      `ty:cm_type`, `ptr:cm_value`, `v:cm_value`,
      `st:cm_src_state`, `tvm_mem (target:tvm_state)`),
      cm_initialized_store_sim), initialized);
  thm new_provenance = mp_rule(specl_rule(TERM_LIST(
      `ty:cm_type`, `ptr:cm_value`, `v:cm_value`,
      `st:cm_src_state`, `tvm_mem (target:tvm_state)`),
      cm_stored_provenance_store_sim), provenance);
  thm fp_unchanged = mp_rule(specl_rule(TERM_LIST(
      `ty:cm_type`,
      `cm_value_number (st:cm_src_state) (ptr:cm_value)`,
      number, `tvm_mem (target:tvm_state)`, `8i`),
      cm_store_mem_word_other), conjunct1_rule(safety));
  thm new_fp = trans_rule(fp_unchanged, fp);
  thm new_calls = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `ty:cm_type`,
      `cm_value_number (st:cm_src_state) (ptr:cm_value)`,
      number, `tvm_mem (target:tvm_state)`,
      `frames:(cm_call_sim_frame)list`,
      `tvm_calls (target:tvm_state)`),
      cm_call_frames_store_sim), calls),
      conjunct1_rule(after_fp_safe));
  thm new_spills = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `ty:cm_type`, `ptr:cm_value`, `v:cm_value`,
      `st:cm_src_state`, number, `tvm_mem (target:tvm_state)`,
      `spill_frames:(cm_spill_frame)list`),
      cm_spill_frames_store_sim), spills),
      conjunct2_rule(after_fp_safe));
  thm old_stack = conv_rule(rewrite_conv(THM_LIST(
      cm_operand_suffix_sim_def)), operand);
  term stack_equality =
      `TL (TL (tvm_stack (target:tvm_state))) ==
       cm_encode_values
         (cm_state_store (ty:cm_type) (ptr:cm_value)
           (v:cm_value) (st:cm_src_state))
         (values:(cm_value)list) ++ (suffix:(int)list)`;
  thm new_stack = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        old_stack, cm_encode_values_def,
        cm_encode_values_state_store,
        get_theorem_by_name("APPEND"),
        get_theorem_by_name("TL"))), stack_equality));
  term operand_term =
      `cm_operand_suffix_sim
         (cm_state_store (ty:cm_type) (ptr:cm_value)
           (v:cm_value) (st:cm_src_state))
         (values:(cm_value)list) (suffix:(int)list)
         (TL (TL (tvm_stack (target:tvm_state))))`;
  thm new_operand = eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_operand_suffix_sim_def)),
      operand_term)), new_stack);
  thm result = conj_rule(new_initialized,
      conj_rule(new_provenance,
      conj_rule(new_fp,
      conj_rule(new_calls,
      conj_rule(new_spills,
      conj_rule(input_equal,
      conj_rule(output_equal, new_operand)))))));
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, get_cm_state_store_def());
  vector_add(&rules, cm_machine_sim_parts);
  vector_add(&rules, get_tvm_next_state_def());
  vector_add(&rules, get_tvm_state_selectors_def());
  vector_add(&rules, sym_rule(normalized_memory));
  gnode opened = CONV_TAC(leaf, reduce_rewrite_conv(rules));
  ACCEPT_TAC(opened, conv_rule(reduce_rewrite_conv(rules), result));
  return gnode_prove(root);
}
PROOF thm cm_machine_store = cm_prove_machine_store();

PROOF static thm cm_prove_temp_cells_disjoint(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (fp:int) (left:int) (right:int).
         ~(left == right) ==>
         cm_range_disjoint
           (fp + cm_temp_offset p fid left) 8i
           (fp + cm_temp_offset p fid right) 8i`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm unequal = assume_rule(`~((left:int) == (right:int))`);
  gnode opened = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      cm_range_disjoint_def, get_cm_temp_offset_def())));
  thm result = mp_rule(
      int_arith_rule(mk_imp(concl(unequal), goal_ccl(opened->g))),
      unequal);
  ACCEPT_TAC(opened, result);
  return gnode_prove(root);
}
PROOF static thm cm_temp_cells_disjoint =
    cm_prove_temp_cells_disjoint();

PROOF static thm cm_prove_initialized_scratch_store_sim(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (mem:int->int) (base:int) (number:int).
         cm_initialized_bytes_sim st mem ==>
         tower_signed64 number ==>
         (!addr.
            cm_live_address st addr ==>
            ~(base <= addr && addr < base + 8i)) ==>
         cm_initialized_bytes_sim st
           (tower_setw mem base number)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm old_sim = conv_rule(rewrite_conv(THM_LIST(
      cm_initialized_bytes_sim_def)), assume_rule(
        `cm_initialized_bytes_sim
          (st:cm_src_state) (mem:int->int)`));
  thm fixed = mp_rule(spec_rule(
      `number:int`, get_tower_wrap64_fixed()), assume_rule(
        `tower_signed64 (number:int)`));
  gnode opened = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      cm_initialized_bytes_sim_def)));
  gnode at_address = AUTO_INTROS_TAC(opened);
  thm initialized_live = assume_rule(
      `cm_state_init (st:cm_src_state) (addr:int) &&
       cm_live_address st addr`);
  thm initialized = conjunct1_rule(initialized_live);
  thm live = conjunct2_rule(initialized_live);
  thm outside = match_mp_rule(spec_rule(
      `addr:int`, assume_rule(
        `!addr.
           cm_live_address (st:cm_src_state) addr ==>
           ~((base:int) <= addr && addr < base + 8i)`)),
      live);
  thm unchanged = specl_rule(TERM_LIST(
      `CMIntTy:cm_type`, `base:int`, `number:int`,
      `mem:int->int`, `addr:int`), cm_store_mem_byte_other);
  unchanged = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_store_width_def(), get_cm_store_mem_def(),
      get_cm_type_int_char_distinct(), fixed)), unchanged);
  unchanged = match_mp_rule(unchanged, outside);
  thm old_byte = match_mp_rule(
      spec_rule(`addr:int`, old_sim), conj_rule(initialized, live));
  ACCEPT_TAC(at_address, trans_rule(unchanged, old_byte));
  return gnode_prove(root);
}
PROOF static thm cm_initialized_scratch_store_sim =
    cm_prove_initialized_scratch_store_sim();

PROOF static thm cm_prove_provenance_scratch_store_sim(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (mem:int->int) (base:int) (number:int).
         cm_stored_provenance_sim st mem ==>
         tower_signed64 number ==>
         cm_tagged_span_valid st ==>
         (!addr.
            cm_live_address st addr ==>
            ~(base <= addr && addr < base + 8i)) ==>
         cm_stored_provenance_sim st
           (tower_setw mem base number)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm old_sim = conv_rule(rewrite_conv(THM_LIST(
      cm_stored_provenance_sim_def)), assume_rule(
        `cm_stored_provenance_sim
          (st:cm_src_state) (mem:int->int)`));
  thm span_valid = conv_rule(rewrite_conv(THM_LIST(
      cm_tagged_span_valid_def)), assume_rule(
        `cm_tagged_span_valid (st:cm_src_state)`));
  thm fixed = mp_rule(spec_rule(
      `number:int`, get_tower_wrap64_fixed()), assume_rule(
        `tower_signed64 (number:int)`));
  thm outside_all = assume_rule(
      `!addr.
         cm_live_address (st:cm_src_state) addr ==>
         ~((base:int) <= addr && addr < base + 8i)`);
  gnode opened = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      cm_stored_provenance_sim_def)));
  gnode at_address = AUTO_INTROS_TAC(opened);
  thm tagged_live = assume_rule(
      `cm_state_tagged (st:cm_src_state) (addr:int) &&
       cm_live_address st addr`);
  thm tagged = conjunct1_rule(tagged_live);
  thm live = conjunct2_rule(tagged_live);
  thm old_point = match_mp_rule(spec_rule(
      `addr:int`, old_sim), conj_rule(tagged, live));
  thm span = match_mp_rule(spec_rule(
      `addr:int`, span_valid), conj_rule(tagged, live));
  span = conv_rule(rewrite_conv(THM_LIST(cm_live_span_def)), span);
  thm live_last = match_mp_rule(spec_rule(
      `(addr:int) + 7i`, span), int_arith_rule(
        `(addr:int) <= addr + 7i &&
         addr + 7i < addr + 8i`));
  thm outside_first = match_mp_rule(
      spec_rule(`addr:int`, outside_all), live);
  thm outside_last = match_mp_rule(
      spec_rule(`(addr:int) + 7i`, outside_all), live_last);
  thm disjoint_raw = mp_rule(mp_rule(int_arith_rule(
      `~((base:int) <= (addr:int) && addr < base + 8i) ==>
       ~(base <= addr + 7i && addr + 7i < base + 8i) ==>
       base + 8i <= addr || addr + 8i <= base`),
      outside_first), outside_last);
  thm disjoint = eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_range_disjoint_def)),
      `cm_range_disjoint (base:int) 8i (addr:int) 8i`)),
      disjoint_raw);
  thm unchanged = specl_rule(TERM_LIST(
      `CMIntTy:cm_type`, `base:int`, `number:int`,
      `mem:int->int`, `addr:int`), cm_store_mem_word_other);
  unchanged = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_store_width_def(),
      get_cm_type_int_char_distinct())), unchanged);
  unchanged = match_mp_rule(unchanged, disjoint);
  unchanged = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_store_mem_def(),
      get_cm_type_int_char_distinct(), fixed)), unchanged);
  thm result = conj_rule(conjunct1_rule(old_point),
      trans_rule(unchanged, conjunct2_rule(old_point)));
  ACCEPT_TAC(at_address, result);
  return gnode_prove(root);
}

PROOF static thm cm_prove_spill_list_scratch_store_sim(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state) (mem:int->int)
         (fid:int) (fp:int) (base:int) (number:int)
         (spills:(cm_spill)list).
         cm_spill_list_sim p st mem fid fp spills ==>
         cm_spill_list_store_safe p fid fp CMIntTy base spills ==>
         tower_signed64 number ==>
         cm_spill_list_sim p st
           (tower_setw mem base number) fid fp spills`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_state = GEN_TAC(with_program, "st");
  gnode with_mem = GEN_TAC(with_state, "mem");
  gnode with_fid = GEN_TAC(with_mem, "fid");
  gnode with_fp = GEN_TAC(with_fid, "fp");
  gnode with_base = GEN_TAC(with_fp, "base");
  gnode with_number = GEN_TAC(with_base, "number");
  gnode_list cases = INDUCT_TAC(
      with_number, `spills:(cm_spill)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        cm_spill_list_sim_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm old_sim = conv_rule(rewrite_conv(THM_LIST(
        cm_spill_list_sim_def)), assume_rule(
          `cm_spill_list_sim (p:cm_program) (st:cm_src_state)
             (mem:int->int) (fid:int) (fp:int)
             ((a0:cm_spill) :: (a1:(cm_spill)list))`));
    thm safety = conv_rule(rewrite_conv(THM_LIST(
        cm_spill_list_store_safe_def)), assume_rule(
          `cm_spill_list_store_safe (p:cm_program) (fid:int)
             (fp:int) CMIntTy (base:int)
             ((a0:cm_spill) :: (a1:(cm_spill)list))`));
    thm fixed = mp_rule(spec_rule(
        `number:int`, get_tower_wrap64_fixed()), assume_rule(
          `tower_signed64 (number:int)`));
    term cell =
        `(fp:int) + cm_temp_offset (p:cm_program) (fid:int)
          (cm_spill_slot (a0:cm_spill))`;
    thm unchanged = match_mp_rule(specl_rule(TERM_LIST(
        `CMIntTy:cm_type`, `base:int`, `number:int`,
        `mem:int->int`, cell), cm_store_mem_word_other),
        conjunct1_rule(safety));
    unchanged = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_store_width_def(), get_cm_store_mem_def(),
        get_cm_type_int_char_distinct(), fixed)), unchanged);
    thm new_word =
        trans_rule(unchanged, conjunct1_rule(old_sim));
    thm induction = assume_rule(
        `cm_spill_list_sim (p:cm_program) (st:cm_src_state)
           (mem:int->int) (fid:int) (fp:int)
           (a1:(cm_spill)list) ==>
         cm_spill_list_store_safe p fid fp CMIntTy
           (base:int) a1 ==>
         tower_signed64 (number:int) ==>
         cm_spill_list_sim p st
           (tower_setw mem base number) fid fp a1`);
    thm new_tail = mp_rule(mp_rule(mp_rule(
        induction, conjunct2_rule(old_sim)),
        conjunct2_rule(safety)),
        assume_rule(`tower_signed64 (number:int)`));
    thm result = conj_rule(new_word, new_tail);
    gnode reduced = CONV_TAC(leaf,
        rewrite_conv(THM_LIST(cm_spill_list_sim_def)));
    ACCEPT_TAC(reduced, result);
  }
  return gnode_prove(root);
}
PROOF static thm cm_spill_list_scratch_store_sim =
    cm_prove_spill_list_scratch_store_sim();

PROOF static thm cm_prove_spill_frames_scratch_store_sim(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state) (mem:int->int)
         (base:int) (number:int)
         (frames:(cm_spill_frame)list).
         cm_spill_frames_sim p st mem frames ==>
         cm_spill_frames_store_safe p CMIntTy base frames ==>
         tower_signed64 number ==>
         cm_spill_frames_sim p st
           (tower_setw mem base number) frames`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_state = GEN_TAC(with_program, "st");
  gnode with_mem = GEN_TAC(with_state, "mem");
  gnode with_base = GEN_TAC(with_mem, "base");
  gnode with_number = GEN_TAC(with_base, "number");
  gnode_list cases = INDUCT_TAC(
      with_number, `frames:(cm_spill_frame)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        cm_spill_frames_sim_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm old_sim = conv_rule(rewrite_conv(THM_LIST(
        cm_spill_frames_sim_def)), assume_rule(
          `cm_spill_frames_sim (p:cm_program) (st:cm_src_state)
             (mem:int->int)
             ((a0:cm_spill_frame) ::
              (a1:(cm_spill_frame)list))`));
    thm safety = conv_rule(rewrite_conv(THM_LIST(
        cm_spill_frames_store_safe_def)), assume_rule(
          `cm_spill_frames_store_safe (p:cm_program) CMIntTy
             (base:int)
             ((a0:cm_spill_frame) ::
              (a1:(cm_spill_frame)list))`));
    thm induction = assume_rule(
        `cm_spill_frames_sim (p:cm_program) (st:cm_src_state)
           (mem:int->int) (a1:(cm_spill_frame)list) ==>
         cm_spill_frames_store_safe p CMIntTy
           (base:int) a1 ==>
         tower_signed64 (number:int) ==>
         cm_spill_frames_sim p st
           (tower_setw mem base number) a1`);
    thm new_head = mp_rule(mp_rule(mp_rule(specl_rule(
        TERM_LIST(`p:cm_program`, `st:cm_src_state`,
          `mem:int->int`,
          `cm_spill_frame_fid (a0:cm_spill_frame)`,
          `cm_spill_frame_fp (a0:cm_spill_frame)`,
          `base:int`, `number:int`,
          `cm_spill_frame_spills (a0:cm_spill_frame)`),
        cm_spill_list_scratch_store_sim),
        conjunct1_rule(old_sim)), conjunct1_rule(safety)),
        assume_rule(`tower_signed64 (number:int)`));
    thm new_tail = mp_rule(mp_rule(mp_rule(
        induction, conjunct2_rule(old_sim)),
        conjunct2_rule(safety)),
        assume_rule(`tower_signed64 (number:int)`));
    gnode reduced = CONV_TAC(leaf,
        rewrite_conv(THM_LIST(cm_spill_frames_sim_def)));
    ACCEPT_TAC(reduced, conj_rule(new_head, new_tail));
  }
  return gnode_prove(root);
}
PROOF static thm cm_spill_frames_scratch_store_sim =
    cm_prove_spill_frames_scratch_store_sim();

PROOF static thm cm_prove_spill_remove_scratch_store_sim(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state) (mem:int->int)
         (fid:int) (fp:int) (spills:(cm_spill)list)
         (slot:int) (number:int).
         tower_signed64 number ==>
         cm_spill_list_sim p st mem fid fp spills ==>
         cm_spill_list_sim p st
           (tower_setw mem
             (fp + cm_temp_offset p fid slot) number)
           fid fp (cm_spill_remove slot spills)`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_state = GEN_TAC(with_program, "st");
  gnode with_mem = GEN_TAC(with_state, "mem");
  gnode with_fid = GEN_TAC(with_mem, "fid");
  gnode with_fp = GEN_TAC(with_fid, "fp");
  gnode_list cases = INDUCT_TAC(
      with_fp, `spills:(cm_spill)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        cm_spill_remove_def, cm_spill_list_sim_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm old_sim = conv_rule(rewrite_conv(THM_LIST(
        cm_spill_list_sim_def)), assume_rule(
          `cm_spill_list_sim (p:cm_program) (st:cm_src_state)
             (mem:int->int) (fid:int) (fp:int)
             ((a0:cm_spill) :: (a1:(cm_spill)list))`));
    thm signed_number =
        assume_rule(`tower_signed64 (number:int)`);
    thm induction = assume_rule(
        `!slot number.
           tower_signed64 (number:int) ==>
           cm_spill_list_sim (p:cm_program) (st:cm_src_state)
             (mem:int->int) (fid:int) (fp:int)
             (a1:(cm_spill)list) ==>
           cm_spill_list_sim p st
             (tower_setw mem
               (fp + cm_temp_offset p fid (slot:int)) number)
             fid fp (cm_spill_remove slot a1)`);
    gnode_list slot_cases = BOOL_CASES_TAC(
        leaf, `cm_spill_slot (a0:cm_spill) == (slot:int)`,
        "Hsame");
    {
      thm same = assume_rule(
          `cm_spill_slot (a0:cm_spill) == (slot:int)`);
      thm new_tail = mp_rule(mp_rule(specl_rule(TERM_LIST(
          `slot:int`, `number:int`), induction),
          signed_number), conjunct2_rule(old_sim));
      gnode reduced = CONV_TAC(slot_cases[0],
          reduce_rewrite_conv(THM_LIST(
            cm_spill_remove_def, same)));
      ACCEPT_TAC(reduced, new_tail);
    }
    {
      thm different = assume_rule(
          `~(cm_spill_slot (a0:cm_spill) == (slot:int))`);
      thm new_tail = mp_rule(mp_rule(specl_rule(TERM_LIST(
          `slot:int`, `number:int`), induction),
          signed_number), conjunct2_rule(old_sim));
      thm slot_unequal = conv_rule(rewrite_conv(THM_LIST(
          ispecl_rule(TERM_LIST(
            `cm_spill_slot (a0:cm_spill)`, `slot:int`),
            get_theorem_by_name("EQ_SYM_EQ")))), different);
      thm disjoint = match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `fp:int`, `slot:int`,
          `cm_spill_slot (a0:cm_spill)`),
          cm_temp_cells_disjoint), slot_unequal);
      term base =
          `(fp:int) + cm_temp_offset (p:cm_program) (fid:int)
            (slot:int)`;
      term cell =
          `(fp:int) + cm_temp_offset (p:cm_program) (fid:int)
            (cm_spill_slot (a0:cm_spill))`;
      thm fixed = mp_rule(spec_rule(
          `number:int`, get_tower_wrap64_fixed()),
          signed_number);
      thm unchanged = specl_rule(TERM_LIST(
          `CMIntTy:cm_type`, base, `number:int`,
          `mem:int->int`, cell), cm_store_mem_word_other);
      unchanged = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_cm_store_width_def(),
          get_cm_type_int_char_distinct())), unchanged);
      unchanged = match_mp_rule(unchanged, disjoint);
      unchanged = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_cm_store_mem_def(),
          get_cm_type_int_char_distinct(), fixed)), unchanged);
      thm new_word =
          trans_rule(unchanged, conjunct1_rule(old_sim));
      gnode reduced = CONV_TAC(slot_cases[1],
          reduce_rewrite_conv(THM_LIST(
            cm_spill_remove_def, different,
            cm_spill_list_sim_def)));
      ACCEPT_TAC(reduced, conj_rule(new_word, new_tail));
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_spill_remove_scratch_store_sim =
    cm_prove_spill_remove_scratch_store_sim();
PROOF static thm cm_provenance_scratch_store_sim =
    cm_prove_provenance_scratch_store_sim();

PROOF static thm cm_prove_machine_spill_store(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state) (target:tvm_state)
         (frames:(cm_call_sim_frame)list)
         (fid:int) (fp:int) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (slot:int) (base:int) (v:cm_value)
         (values:(cm_value)list) (suffix:(int)list).
         cm_machine_state_sim p st target frames
           (CMSpillFrame fid fp spills :: saved)
           (CMIntV base :: v :: values) suffix ==>
         cm_tagged_span_valid st ==>
         (!addr.
            cm_live_address st addr ==>
            ~(base <= addr && addr < base + 8i)) ==>
         cm_range_disjoint base 8i 8i 8i ==>
         cm_call_frames_store_safe CMIntTy base frames ==>
         cm_spill_frames_store_safe p CMIntTy base saved ==>
         base == fp + cm_temp_offset p fid slot ==>
         cm_machine_state_sim p st
           (tvm_next_state target
             (TL (TL (tvm_stack target)))
             (tvm_calls target)
             (tower_setw (tvm_mem target) base
               (cm_value_number st v))
             (tvm_input target) (tvm_output target))
           frames
           (CMSpillFrame fid fp
              (cm_spill_put slot v spills) :: saved)
           values suffix`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm simulation = assume_rule(
      `cm_machine_state_sim (p:cm_program) (st:cm_src_state)
         (target:tvm_state) (frames:(cm_call_sim_frame)list)
         (CMSpillFrame (fid:int) (fp:int)
            (spills:(cm_spill)list) ::
          (saved:(cm_spill_frame)list))
         (CMIntV (base:int) :: (v:cm_value) ::
          (values:(cm_value)list)) (suffix:(int)list)`);
  thm parts = conv_rule(rewrite_conv(THM_LIST(
      cm_machine_sim_parts)), simulation);
  thm initialized = conjunct1_rule(parts);
  thm after_initialized = conjunct2_rule(parts);
  thm provenance = conjunct1_rule(after_initialized);
  thm after_provenance = conjunct2_rule(after_initialized);
  thm fp_word = conjunct1_rule(after_provenance);
  thm after_fp = conjunct2_rule(after_provenance);
  thm calls = conjunct1_rule(after_fp);
  thm after_calls = conjunct2_rule(after_fp);
  thm all_spills = conjunct1_rule(after_calls);
  thm after_spills = conjunct2_rule(after_calls);
  thm input_equal = conjunct1_rule(after_spills);
  thm after_input = conjunct2_rule(after_spills);
  thm output_equal = conjunct1_rule(after_input);
  thm operand = conjunct2_rule(after_input);
  thm number_signed = specl_rule(TERM_LIST(
      `st:cm_src_state`, `v:cm_value`),
      get_cm_value_number_signed_bridge());
  thm fixed = mp_rule(spec_rule(
      `cm_value_number (st:cm_src_state) (v:cm_value)`,
      get_tower_wrap64_fixed()), number_signed);
  thm outside = assume_rule(
      `!addr.
         cm_live_address (st:cm_src_state) addr ==>
         ~((base:int) <= addr && addr < base + 8i)`);
  thm new_initialized = mp_rule(mp_rule(mp_rule(
      specl_rule(TERM_LIST(
        `st:cm_src_state`, `tvm_mem (target:tvm_state)`,
        `base:int`,
        `cm_value_number (st:cm_src_state) (v:cm_value)`),
        cm_initialized_scratch_store_sim),
      initialized), number_signed), outside);
  thm new_provenance = mp_rule(mp_rule(mp_rule(mp_rule(
      specl_rule(TERM_LIST(
        `st:cm_src_state`, `tvm_mem (target:tvm_state)`,
        `base:int`,
        `cm_value_number (st:cm_src_state) (v:cm_value)`),
        cm_provenance_scratch_store_sim),
      provenance), number_signed), assume_rule(
        `cm_tagged_span_valid (st:cm_src_state)`)), outside);
  thm fp_unchanged = specl_rule(TERM_LIST(
      `CMIntTy:cm_type`, `base:int`,
      `cm_value_number (st:cm_src_state) (v:cm_value)`,
      `tvm_mem (target:tvm_state)`, `8i`),
      cm_store_mem_word_other);
  fp_unchanged = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_store_width_def(),
      get_cm_type_int_char_distinct())), fp_unchanged);
  fp_unchanged = match_mp_rule(fp_unchanged, assume_rule(
      `cm_range_disjoint (base:int) 8i 8i 8i`));
  fp_unchanged = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_store_mem_def(),
      get_cm_type_int_char_distinct(), fixed)), fp_unchanged);
  thm new_fp = trans_rule(fp_unchanged, fp_word);
  thm new_calls = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `CMIntTy:cm_type`, `base:int`,
      `cm_value_number (st:cm_src_state) (v:cm_value)`,
      `tvm_mem (target:tvm_state)`,
      `frames:(cm_call_sim_frame)list`,
      `tvm_calls (target:tvm_state)`),
      cm_call_frames_store_sim), calls), assume_rule(
        `cm_call_frames_store_safe CMIntTy (base:int)
           (frames:(cm_call_sim_frame)list)`));
  new_calls = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_store_mem_def(),
      get_cm_type_int_char_distinct(), fixed)), new_calls);
  thm spill_parts = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_spill_frames_sim_def, cm_spill_frame_fid_def,
      cm_spill_frame_fp_def, cm_spill_frame_spills_def)),
      all_spills);
  thm old_current = conjunct1_rule(spill_parts);
  thm old_saved = conjunct2_rule(spill_parts);
  thm removed = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`,
      `tvm_mem (target:tvm_state)`, `fid:int`, `fp:int`,
      `spills:(cm_spill)list`, `slot:int`,
      `cm_value_number (st:cm_src_state) (v:cm_value)`),
      cm_spill_remove_scratch_store_sim),
      number_signed), old_current);
  term cell =
      `(fp:int) + cm_temp_offset (p:cm_program) (fid:int)
        (slot:int)`;
  thm new_head = specl_rule(TERM_LIST(
      `tvm_mem (target:tvm_state)`, cell,
      `cm_value_number (st:cm_src_state) (v:cm_value)`),
      get_tower_getw_setw());
  new_head = conv_rule(rewrite_conv(THM_LIST(fixed)), new_head);
  term current_term =
      `cm_spill_list_sim (p:cm_program) (st:cm_src_state)
         (tower_setw (tvm_mem (target:tvm_state)) ${cell:int}
           (cm_value_number st (v:cm_value)))
         (fid:int) (fp:int)
         (cm_spill_put (slot:int) v (spills:(cm_spill)list))`;
  thm new_current = eq_mp_rule(sym_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_spill_put_def, cm_spill_list_sim_def,
        cm_spill_slot_def, cm_spill_value_def)),
      current_term)), conj_rule(new_head, removed));
  thm address_equal = assume_rule(
      `(base:int) ==
       (fp:int) + cm_temp_offset (p:cm_program) (fid:int)
         (slot:int)`);
  new_current = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(address_equal))), new_current);
  thm new_saved = mp_rule(mp_rule(mp_rule(specl_rule(
      TERM_LIST(`p:cm_program`, `st:cm_src_state`,
        `tvm_mem (target:tvm_state)`, `base:int`,
        `cm_value_number (st:cm_src_state) (v:cm_value)`,
        `saved:(cm_spill_frame)list`),
      cm_spill_frames_scratch_store_sim),
      old_saved), assume_rule(
        `cm_spill_frames_store_safe (p:cm_program) CMIntTy
           (base:int) (saved:(cm_spill_frame)list)`)),
      number_signed);
  thm new_spills = eq_mp_rule(sym_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_spill_frames_sim_def, cm_spill_frame_fid_def,
        cm_spill_frame_fp_def, cm_spill_frame_spills_def)),
      `cm_spill_frames_sim (p:cm_program) (st:cm_src_state)
         (tower_setw (tvm_mem (target:tvm_state)) (base:int)
           (cm_value_number st (v:cm_value)))
         (CMSpillFrame (fid:int) (fp:int)
            (cm_spill_put (slot:int) v
              (spills:(cm_spill)list)) ::
          (saved:(cm_spill_frame)list))`)),
      conj_rule(new_current, new_saved));
  thm old_stack = conv_rule(rewrite_conv(THM_LIST(
      cm_operand_suffix_sim_def)), operand);
  term stack_equality =
      `TL (TL (tvm_stack (target:tvm_state))) ==
       cm_encode_values (st:cm_src_state)
         (values:(cm_value)list) ++ (suffix:(int)list)`;
  thm new_stack = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        old_stack, cm_encode_values_def,
        get_theorem_by_name("APPEND"),
        get_theorem_by_name("TL"))), stack_equality));
  thm new_operand = eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_operand_suffix_sim_def)),
      `cm_operand_suffix_sim (st:cm_src_state)
         (values:(cm_value)list) (suffix:(int)list)
         (TL (TL (tvm_stack (target:tvm_state))))`)),
      new_stack);
  thm result = conj_rule(new_initialized,
      conj_rule(new_provenance,
      conj_rule(new_fp,
      conj_rule(new_calls,
      conj_rule(new_spills,
      conj_rule(input_equal,
      conj_rule(output_equal, new_operand)))))));
  thm_list rules = THM_LIST(
      cm_machine_sim_parts, get_tvm_next_state_def(),
      get_tvm_state_selectors_def());
  gnode opened = CONV_TAC(leaf, reduce_rewrite_conv(rules));
  ACCEPT_TAC(opened, conv_rule(reduce_rewrite_conv(rules), result));
  return gnode_prove(root);
}
PROOF thm cm_machine_spill_store =
    cm_prove_machine_spill_store();

PROOF thm get_cm_machine_store(void) {
  return cm_machine_store;
}
PROOF thm get_cm_machine_spill_store(void) {
  return cm_machine_spill_store;
}
PROOF thm get_cm_initialized_scratch_store_sim(void) {
  return cm_initialized_scratch_store_sim;
}
PROOF thm get_cm_provenance_scratch_store_sim(void) {
  return cm_provenance_scratch_store_sim;
}
PROOF thm get_cm_spill_frames_scratch_store_sim(void) {
  return cm_spill_frames_scratch_store_sim;
}


PROOF static int cmc_preservation_machine_store_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_machine_store_axioms_before,
      "cmc_preservation_machine_store introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_machine_store_final_checks =
    cmc_preservation_machine_store_final_checks();
