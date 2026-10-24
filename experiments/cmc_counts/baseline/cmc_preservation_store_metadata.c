#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_store_provenance.h"
#require "cmc_preservation_store_provenance.c"
#include "cmc_preservation_store_metadata.h"

PROOF static size_t _cmc_preservation_store_metadata_axioms_before =
    vector_size(get_all_axioms());

PROOF thm cm_call_frames_store_safe_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_call_frames_store_safe (ty:cm_type) (base:int)
         ([]:(cm_call_sim_frame)list) <=> T) &&
     (!frame rest.
        cm_call_frames_store_safe ty base
          ((frame:cm_call_sim_frame) :: rest) <=>
        cm_range_disjoint base (cm_store_width ty)
          (cm_call_sim_base frame) 8i &&
        cm_call_frames_store_safe ty base rest)`);
PROOF static int _e_cm_call_frames_store_safe =
    cst_add_const_to_header(`cm_call_frames_store_safe`);

PROOF thm cm_spill_list_store_safe_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_spill_list_store_safe (p:cm_program) (fid:int) (fp:int)
         (ty:cm_type) (base:int) ([]:(cm_spill)list) <=> T) &&
     (!spill rest.
        cm_spill_list_store_safe p fid fp ty base
          ((spill:cm_spill) :: rest) <=>
        cm_range_disjoint base (cm_store_width ty)
          (fp + cm_temp_offset p fid (cm_spill_slot spill)) 8i &&
        cm_spill_list_store_safe p fid fp ty base rest)`);
PROOF static int _e_cm_spill_list_store_safe =
    cst_add_const_to_header(`cm_spill_list_store_safe`);

PROOF thm cm_spill_frames_store_safe_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_spill_frames_store_safe (p:cm_program) (ty:cm_type)
         (base:int) ([]:(cm_spill_frame)list) <=> T) &&
     (!frame rest.
        cm_spill_frames_store_safe p ty base
          ((frame:cm_spill_frame) :: rest) <=>
        cm_spill_list_store_safe p (cm_spill_frame_fid frame)
          (cm_spill_frame_fp frame) ty base
          (cm_spill_frame_spills frame) &&
        cm_spill_frames_store_safe p ty base rest)`);
PROOF static int _e_cm_spill_frames_store_safe =
    cst_add_const_to_header(`cm_spill_frames_store_safe`);

PROOF thm cm_machine_store_safe_def = new_fun_definition(
    `cm_machine_store_safe (p:cm_program) (ty:cm_type) (base:int)
       (frames:(cm_call_sim_frame)list)
       (spill_frames:(cm_spill_frame)list) : bool =
       (cm_range_disjoint base (cm_store_width ty) 8i 8i &&
        cm_call_frames_store_safe ty base frames &&
        cm_spill_frames_store_safe p ty base spill_frames)`);
PROOF static int _e_cm_machine_store_safe =
    cst_add_const_to_header(`cm_machine_store_safe`);

PROOF static thm cm_prove_encode_values_state_store(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type) (ptr:cm_value) (stored:cm_value)
         (st:cm_src_state) (values:(cm_value)list).
         cm_encode_values (cm_state_store ty ptr stored st) values ==
         cm_encode_values st values`);
  gnode with_type = GEN_TAC(root, "ty");
  gnode with_ptr = GEN_TAC(with_type, "ptr");
  gnode with_stored = GEN_TAC(with_ptr, "stored");
  gnode with_state = GEN_TAC(with_stored, "st");
  gnode_list cases =
      INDUCT_TAC(with_state, `values:(cm_value)list`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, THM_LIST(
        cm_encode_values_def, cm_value_number_state_store));
  }
  return gnode_prove(root);
}
PROOF thm cm_encode_values_state_store =
    cm_prove_encode_values_state_store();

PROOF static thm cm_prove_call_frames_store_sim(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type) (base:int) (number:int) (mem:int->int)
         (frames:(cm_call_sim_frame)list) (calls:(int)list).
         cm_call_frames_sim mem frames calls ==>
         cm_call_frames_store_safe ty base frames ==>
         cm_call_frames_sim (cm_store_mem ty base number mem)
           frames calls`);
  gnode with_type = GEN_TAC(root, "ty");
  gnode with_base = GEN_TAC(with_type, "base");
  gnode with_number = GEN_TAC(with_base, "number");
  gnode with_mem = GEN_TAC(with_number, "mem");
  gnode_list cases = INDUCT_TAC(
      with_mem, `frames:(cm_call_sim_frame)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm old_sim = conv_rule(rewrite_conv(THM_LIST(
        cm_call_frames_sim_def)), assume_rule(
          `cm_call_frames_sim (mem:int->int)
             ([]:(cm_call_sim_frame)list) (calls:(int)list)`));
    gnode reduced = CONV_TAC(leaf,
        rewrite_conv(THM_LIST(cm_call_frames_sim_def)));
    ACCEPT_TAC(reduced, old_sim);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm old_sim = conv_rule(rewrite_conv(THM_LIST(
        cm_call_frames_sim_def)), assume_rule(
          `cm_call_frames_sim (mem:int->int)
             ((a0:cm_call_sim_frame) ::
              (a1:(cm_call_sim_frame)list))
             (calls:(int)list)`));
    thm safety = conv_rule(rewrite_conv(THM_LIST(
        cm_call_frames_store_safe_def)), assume_rule(
          `cm_call_frames_store_safe (ty:cm_type) (base:int)
             ((a0:cm_call_sim_frame) ::
              (a1:(cm_call_sim_frame)list))`));
    thm after_nonempty = conjunct2_rule(old_sim);
    thm after_head = conjunct2_rule(after_nonempty);
    thm unchanged = mp_rule(specl_rule(TERM_LIST(
        `ty:cm_type`, `base:int`, `number:int`, `mem:int->int`,
        `cm_call_sim_base (a0:cm_call_sim_frame)`),
        cm_store_mem_word_other), conjunct1_rule(safety));
    thm new_word =
        trans_rule(unchanged, conjunct1_rule(after_head));
    thm induction = assume_rule(
        `!(calls:(int)list).
           cm_call_frames_sim (mem:int->int)
             (a1:(cm_call_sim_frame)list) calls ==>
           cm_call_frames_store_safe (ty:cm_type) (base:int) a1 ==>
           cm_call_frames_sim
             (cm_store_mem ty base (number:int) mem) a1 calls`);
    thm new_tail = mp_rule(mp_rule(spec_rule(
        `TL (calls:(int)list)`, induction),
        conjunct2_rule(after_head)), conjunct2_rule(safety));
    thm result = conj_rule(conjunct1_rule(old_sim),
        conj_rule(conjunct1_rule(after_nonempty),
          conj_rule(new_word, new_tail)));
    gnode reduced = CONV_TAC(leaf,
        rewrite_conv(THM_LIST(cm_call_frames_sim_def)));
    ACCEPT_TAC(reduced, result);
  }
  return gnode_prove(root);
}
PROOF thm cm_call_frames_store_sim =
    cm_prove_call_frames_store_sim();

PROOF static thm cm_prove_spill_list_store_sim(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (ty:cm_type) (ptr:cm_value)
         (stored:cm_value) (st:cm_src_state) (number:int)
         (mem:int->int) (fid:int) (fp:int)
         (spills:(cm_spill)list).
         cm_spill_list_sim p st mem fid fp spills ==>
         cm_spill_list_store_safe p fid fp ty
           (cm_value_number st ptr) spills ==>
         cm_spill_list_sim p (cm_state_store ty ptr stored st)
           (cm_store_mem ty (cm_value_number st ptr) number mem)
           fid fp spills`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_type = GEN_TAC(with_program, "ty");
  gnode with_ptr = GEN_TAC(with_type, "ptr");
  gnode with_stored = GEN_TAC(with_ptr, "stored");
  gnode with_state = GEN_TAC(with_stored, "st");
  gnode with_number = GEN_TAC(with_state, "number");
  gnode with_mem = GEN_TAC(with_number, "mem");
  gnode with_fid = GEN_TAC(with_mem, "fid");
  gnode with_fp = GEN_TAC(with_fid, "fp");
  gnode_list cases = INDUCT_TAC(
      with_fp, `spills:(cm_spill)list`);
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
             (fp:int) (ty:cm_type)
             (cm_value_number (st:cm_src_state) (ptr:cm_value))
             ((a0:cm_spill) :: (a1:(cm_spill)list))`));
    term slot_address =
        `(fp:int) + cm_temp_offset (p:cm_program) (fid:int)
          (cm_spill_slot (a0:cm_spill))`;
    thm unchanged = mp_rule(specl_rule(TERM_LIST(
        `ty:cm_type`,
        `cm_value_number (st:cm_src_state) (ptr:cm_value)`,
        `number:int`, `mem:int->int`, slot_address),
        cm_store_mem_word_other), conjunct1_rule(safety));
    thm old_word = conjunct1_rule(old_sim);
    thm new_number = specl_rule(TERM_LIST(
        `ty:cm_type`, `ptr:cm_value`, `stored:cm_value`,
        `st:cm_src_state`, `cm_spill_value (a0:cm_spill)`),
        cm_value_number_state_store);
    thm new_word = trans_rule(trans_rule(unchanged, old_word),
        sym_rule(new_number));
    thm induction = assume_rule(
        `cm_spill_list_sim (p:cm_program) (st:cm_src_state)
           (mem:int->int) (fid:int) (fp:int)
           (a1:(cm_spill)list) ==>
         cm_spill_list_store_safe p fid fp (ty:cm_type)
           (cm_value_number st (ptr:cm_value)) a1 ==>
         cm_spill_list_sim p
           (cm_state_store ty ptr (stored:cm_value) st)
           (cm_store_mem ty (cm_value_number st ptr)
             (number:int) mem)
           fid fp a1`);
    thm new_tail = mp_rule(mp_rule(induction,
        conjunct2_rule(old_sim)), conjunct2_rule(safety));
    thm result = conj_rule(new_word, new_tail);
    gnode reduced = CONV_TAC(leaf,
        rewrite_conv(THM_LIST(cm_spill_list_sim_def)));
    ACCEPT_TAC(reduced, result);
  }
  return gnode_prove(root);
}
PROOF thm cm_spill_list_store_sim =
    cm_prove_spill_list_store_sim();

PROOF static thm cm_prove_spill_frames_store_sim(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (ty:cm_type) (ptr:cm_value)
         (stored:cm_value) (st:cm_src_state) (number:int)
         (mem:int->int) (frames:(cm_spill_frame)list).
         cm_spill_frames_sim p st mem frames ==>
         cm_spill_frames_store_safe p ty
           (cm_value_number st ptr) frames ==>
         cm_spill_frames_sim p (cm_state_store ty ptr stored st)
           (cm_store_mem ty (cm_value_number st ptr) number mem)
           frames`);
  gnode with_program = GEN_TAC(root, "p");
  gnode with_type = GEN_TAC(with_program, "ty");
  gnode with_ptr = GEN_TAC(with_type, "ptr");
  gnode with_stored = GEN_TAC(with_ptr, "stored");
  gnode with_state = GEN_TAC(with_stored, "st");
  gnode with_number = GEN_TAC(with_state, "number");
  gnode with_mem = GEN_TAC(with_number, "mem");
  gnode_list cases = INDUCT_TAC(
      with_mem, `frames:(cm_spill_frame)list`);
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
          `cm_spill_frames_store_safe (p:cm_program) (ty:cm_type)
             (cm_value_number (st:cm_src_state) (ptr:cm_value))
             ((a0:cm_spill_frame) ::
              (a1:(cm_spill_frame)list))`));
    thm new_head = mp_rule(mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `ty:cm_type`, `ptr:cm_value`,
        `stored:cm_value`, `st:cm_src_state`, `number:int`,
        `mem:int->int`, `cm_spill_frame_fid (a0:cm_spill_frame)`,
        `cm_spill_frame_fp (a0:cm_spill_frame)`,
        `cm_spill_frame_spills (a0:cm_spill_frame)`),
        cm_spill_list_store_sim), conjunct1_rule(old_sim)),
        conjunct1_rule(safety));
    thm induction = assume_rule(
        `cm_spill_frames_sim (p:cm_program) (st:cm_src_state)
           (mem:int->int) (a1:(cm_spill_frame)list) ==>
         cm_spill_frames_store_safe p (ty:cm_type)
           (cm_value_number st (ptr:cm_value)) a1 ==>
         cm_spill_frames_sim p
           (cm_state_store ty ptr (stored:cm_value) st)
           (cm_store_mem ty (cm_value_number st ptr)
             (number:int) mem)
           a1`);
    thm new_tail = mp_rule(mp_rule(induction,
        conjunct2_rule(old_sim)), conjunct2_rule(safety));
    thm result = conj_rule(new_head, new_tail);
    gnode reduced = CONV_TAC(leaf,
        rewrite_conv(THM_LIST(cm_spill_frames_sim_def)));
    ACCEPT_TAC(reduced, result);
  }
  return gnode_prove(root);
}
PROOF thm cm_spill_frames_store_sim =
    cm_prove_spill_frames_store_sim();

PROOF thm get_cm_call_frames_store_safe_def(void) {
  return cm_call_frames_store_safe_def;
}
PROOF thm get_cm_spill_list_store_safe_def(void) {
  return cm_spill_list_store_safe_def;
}
PROOF thm get_cm_spill_frames_store_safe_def(void) {
  return cm_spill_frames_store_safe_def;
}
PROOF thm get_cm_machine_store_safe_def(void) {
  return cm_machine_store_safe_def;
}
PROOF thm get_cm_encode_values_state_store(void) {
  return cm_encode_values_state_store;
}
PROOF thm get_cm_call_frames_store_sim(void) {
  return cm_call_frames_store_sim;
}
PROOF thm get_cm_spill_list_store_sim(void) {
  return cm_spill_list_store_sim;
}
PROOF thm get_cm_spill_frames_store_sim(void) {
  return cm_spill_frames_store_sim;
}

PROOF static int cmc_preservation_store_metadata_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_store_metadata_axioms_before,
      "cmc_preservation_store_metadata introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_store_metadata_final_checks =
    cmc_preservation_store_metadata_final_checks();
