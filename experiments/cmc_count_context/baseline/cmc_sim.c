#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_codegen.h"
#require "cmc_codegen.c"
#include "cmc_sim.h"

PROOF static size_t _cmc_sim_axioms_before = vector_size(get_all_axioms());

/* The simulation keeps source provenance in the source state while exposing
 * only the signed-64 numerical encoding stored by TVM.  Spill witnesses are
 * indexed by the source function and temporary slot that owns the cell. */
PROOF indtype cm_spill_ty = new_datatype_definition(
    "cm_spill = CMSpill int cm_value");
PROOF indtype cm_spill_frame_ty = new_datatype_definition(
    "cm_spill_frame = CMSpillFrame int int (cm_spill)list");
PROOF indtype cm_call_sim_frame_ty = new_datatype_definition(
    "cm_call_sim_frame = CMCallSimFrame int int int");
PROOF static int _t_cm_spill = cst_add_type_to_header("cm_spill", 0);
PROOF static int _t_cm_spill_frame =
    cst_add_type_to_header("cm_spill_frame", 0);
PROOF static int _t_cm_call_sim_frame =
    cst_add_type_to_header("cm_call_sim_frame", 0);
PROOF static int _c_CMSpill =
    cst_add_const_to_header(`CMSpill:int->cm_value->cm_spill`);
PROOF static int _c_CMSpillFrame = cst_add_const_to_header(
    `CMSpillFrame:int->int->(cm_spill)list->cm_spill_frame`);
PROOF static int _c_CMCallSimFrame = cst_add_const_to_header(
    `CMCallSimFrame:int->int->int->cm_call_sim_frame`);

PROOF thm cm_spill_slot_def = new_rec_definition(
    cm_spill_ty.rec,
    `cm_spill_slot (CMSpill (slot:int) (v:cm_value)) = slot`);
PROOF thm cm_spill_value_def = new_rec_definition(
    cm_spill_ty.rec,
    `cm_spill_value (CMSpill (slot:int) (v:cm_value)) = v`);
PROOF thm cm_spill_holds_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!slot value.
        cm_spill_holds (slot:int) (value:cm_value)
          ([]:(cm_spill)list) = F) &&
     (!slot value spill rest.
        cm_spill_holds slot value
          ((spill:cm_spill) :: (rest:(cm_spill)list)) =
        (if cm_spill_slot spill == slot
         then cm_spill_value spill == value
         else cm_spill_holds slot value rest))`);
PROOF thm cm_spill_frame_fid_def = new_rec_definition(
    cm_spill_frame_ty.rec,
    `cm_spill_frame_fid
       (CMSpillFrame (fid:int) (fp:int) (spills:(cm_spill)list)) =
       fid`);
PROOF thm cm_spill_frame_fp_def = new_rec_definition(
    cm_spill_frame_ty.rec,
    `cm_spill_frame_fp
       (CMSpillFrame (fid:int) (fp:int) (spills:(cm_spill)list)) =
       fp`);
PROOF thm cm_spill_frame_spills_def = new_rec_definition(
    cm_spill_frame_ty.rec,
    `cm_spill_frame_spills
       (CMSpillFrame (fid:int) (fp:int) (spills:(cm_spill)list)) =
       spills`);
PROOF thm cm_call_sim_base_def = new_rec_definition(
    cm_call_sim_frame_ty.rec,
    `cm_call_sim_base
       (CMCallSimFrame (base:int) (saved:int) (returnpc:int)) = base`);
PROOF thm cm_call_sim_saved_def = new_rec_definition(
    cm_call_sim_frame_ty.rec,
    `cm_call_sim_saved
       (CMCallSimFrame (base:int) (saved:int) (returnpc:int)) = saved`);
PROOF thm cm_call_sim_return_def = new_rec_definition(
    cm_call_sim_frame_ty.rec,
    `cm_call_sim_return
       (CMCallSimFrame (base:int) (saved:int) (returnpc:int)) =
       returnpc`);

PROOF thm cm_value_encoding_def = new_fun_definition(
    `cm_value_encoding (st:cm_src_state) (v:cm_value)
       (encoded:int) : bool =
       (encoded == cm_value_number st v)`);
PROOF thm cm_encode_values_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_encode_values (st:cm_src_state) ([]:(cm_value)list) =
        ([]:(int)list)) &&
     (!v rest.
       cm_encode_values st
         ((v:cm_value) :: (rest:(cm_value)list)) =
       cm_value_number st v :: cm_encode_values st rest)`);
PROOF thm cm_live_address_def = new_fun_definition(
    `cm_live_address (st:cm_src_state) (addr:int) : bool =
       (?region.
          MEM region (cm_state_regions st) &&
          cm_region_live region &&
          cm_region_base (cm_state_regions st)
              (cm_region_gen region) + cm_region_lo region <= addr &&
          addr < cm_region_base (cm_state_regions st)
              (cm_region_gen region) + cm_region_hi region)`);
PROOF thm cm_live_span_def = new_fun_definition(
    `cm_live_span (st:cm_src_state) (base:int) (width:int) : bool =
       (!(addr:int).
          base <= addr && addr < base + width ==>
          cm_live_address st addr)`);
PROOF thm cm_tagged_span_valid_def = new_fun_definition(
    `cm_tagged_span_valid (st:cm_src_state) : bool =
       (!(addr:int).
          cm_state_tagged st addr && cm_live_address st addr ==>
          cm_live_span st addr 8i)`);
PROOF thm cm_initialized_bytes_sim_def = new_fun_definition(
    `cm_initialized_bytes_sim (st:cm_src_state)
       (vmem:int->int) : bool =
       (!(addr:int).
          cm_state_init st addr && cm_live_address st addr ==>
          tower_getb vmem addr == tower_getb (cm_state_mem st) addr)`);
PROOF thm cm_stored_provenance_sim_def = new_fun_definition(
    `cm_stored_provenance_sim (st:cm_src_state)
       (vmem:int->int) : bool =
       (!(addr:int).
          cm_state_tagged st addr && cm_live_address st addr ==>
          cm_state_init st addr &&
          tower_getw vmem addr ==
            cm_value_number st (cm_state_tags st addr))`);
PROOF thm cm_spill_list_sim_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_spill_list_sim (p:cm_program) (st:cm_src_state)
        (vmem:int->int) (fid:int) (fp:int)
        ([]:(cm_spill)list) = T) &&
     (!spill rest.
       cm_spill_list_sim p st vmem fid fp
         ((spill:cm_spill) :: (rest:(cm_spill)list)) =
       (tower_getw vmem
          (fp + cm_temp_offset p fid (cm_spill_slot spill)) ==
          cm_value_number st (cm_spill_value spill) &&
        cm_spill_list_sim p st vmem fid fp rest))`);
PROOF thm cm_spill_frames_sim_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_spill_frames_sim (p:cm_program) (st:cm_src_state)
        (vmem:int->int) ([]:(cm_spill_frame)list) = T) &&
     (!frame rest.
       cm_spill_frames_sim p st vmem
         ((frame:cm_spill_frame) :: (rest:(cm_spill_frame)list)) =
       (cm_spill_list_sim p st vmem
          (cm_spill_frame_fid frame) (cm_spill_frame_fp frame)
          (cm_spill_frame_spills frame) &&
        cm_spill_frames_sim p st vmem rest))`);
PROOF thm cm_call_frames_sim_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_call_frames_sim (vmem:int->int)
        ([]:(cm_call_sim_frame)list) (calls:(int)list) =
        (calls == [])) &&
     (!frame rest.
       cm_call_frames_sim vmem
         ((frame:cm_call_sim_frame) :: (rest:(cm_call_sim_frame)list))
         calls =
       (~(calls == []) &&
        HD calls == cm_call_sim_return frame &&
        tower_getw vmem (cm_call_sim_base frame) ==
          cm_call_sim_saved frame &&
        cm_call_frames_sim vmem rest (TL calls)))`);
PROOF thm cm_operand_suffix_sim_def = new_fun_definition(
    `cm_operand_suffix_sim (st:cm_src_state)
       (values:(cm_value)list) (suffix:(int)list)
       (stack:(int)list) : bool =
       (stack == cm_encode_values st values ++ suffix)`);
PROOF thm cm_machine_state_sim_def = new_fun_definition(
    `cm_machine_state_sim (p:cm_program) (st:cm_src_state)
       (target:tvm_state) (frames:(cm_call_sim_frame)list)
       (spill_frames:(cm_spill_frame)list)
       (values:(cm_value)list) (suffix:(int)list) : bool =
       (cm_initialized_bytes_sim st (tvm_mem target) &&
        cm_stored_provenance_sim st (tvm_mem target) &&
        tower_getw (tvm_mem target) 8i == cm_state_fp st &&
        cm_call_frames_sim (tvm_mem target) frames (tvm_calls target) &&
        cm_spill_frames_sim p st (tvm_mem target) spill_frames &&
        tvm_input target == cm_state_input st &&
        tvm_output target == cm_state_output st &&
        cm_operand_suffix_sim st values suffix (tvm_stack target))`);
PROOF thm cm_continuation_sim_def = new_fun_definition(
    `cm_continuation_sim (p:cm_program) (st:cm_src_state)
       (ks:(cm_frame)list) (target:tvm_state)
       (frames:(cm_call_sim_frame)list)
       (spill_frames:(cm_spill_frame)list)
       (values:(cm_value)list) (suffix:(int)list) : bool =
       (cm_machine_state_sim p st target frames spill_frames
          values suffix &&
        ilength frames <= ilength ks)`);

PROOF int _e_cm_value_encoding =
    cst_add_const_to_header(`cm_value_encoding`);
PROOF int _e_cm_live_address =
    cst_add_const_to_header(`cm_live_address`);
PROOF int _e_cm_live_span =
    cst_add_const_to_header(`cm_live_span`);
PROOF int _e_cm_initialized_bytes_sim =
    cst_add_const_to_header(`cm_initialized_bytes_sim`);
PROOF int _e_cm_stored_provenance_sim =
    cst_add_const_to_header(`cm_stored_provenance_sim`);
PROOF int _e_cm_machine_state_sim =
    cst_add_const_to_header(`cm_machine_state_sim`);
PROOF int _e_cm_continuation_sim =
    cst_add_const_to_header(`cm_continuation_sim`);

PROOF static thm cm_prove_value_encoding_refl(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (v:cm_value).
         cm_value_encoding st v (cm_value_number st v)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_TAC(leaf, rewrite_conv(THM_LIST(cm_value_encoding_def)));
  return gnode_prove(root);
}
PROOF thm cm_value_encoding_refl =
    cm_prove_value_encoding_refl();

PROOF static thm cm_prove_machine_sim_io(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) st target frames spill_frames values suffix.
         cm_machine_state_sim p (st:cm_src_state) (target:tvm_state)
           (frames:(cm_call_sim_frame)list)
           (spill_frames:(cm_spill_frame)list)
           (values:(cm_value)list) (suffix:(int)list) ==>
         tvm_input target == cm_state_input st &&
         tvm_output target == cm_state_output st`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm sim = assume_rule(
      `cm_machine_state_sim (p:cm_program) (st:cm_src_state)
         (target:tvm_state) (frames:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         (values:(cm_value)list) (suffix:(int)list)`);
  thm parts = eq_mp_rule(
      apply_conversion(rewrite_conv(THM_LIST(
        cm_machine_state_sim_def)), concl(sim)), sim);
  for (size_t i = 0; i < 5; ++i) {
    parts = conjunct2_rule(parts);
  }
  ACCEPT_TAC(leaf, conj_rule(
      conjunct1_rule(parts),
      conjunct1_rule(conjunct2_rule(parts))));
  return gnode_prove(root);
}
PROOF thm cm_machine_sim_io = cm_prove_machine_sim_io();

PROOF static thm cm_prove_value_number_signed(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (v:cm_value).
         tower_signed64 (cm_value_number st v)`);
  gnode quantified = GEN_TAC(root, "st");
  gnode_list cases = INDUCT_TAC(quantified, `v:cm_value`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, rewrite_conv(THM_LIST(
        get_cm_value_number_def(), get_tower_wrap64_range())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    gnode unfolded = CONV_TAC(leaf, rewrite_conv(THM_LIST(
        get_cm_value_number_def(), get_tower_signed64_def())));
    dest_conj_results goal_parts = dest_conj(goal_ccl(unfolded->g));
    term value_number = dest_comb(goal_parts.tm1).tm2;
    term original = dest_comb(value_number).tm2;
    thm byte = conv_rule(rewrite_conv(THM_LIST(
        get_tower_byte_value_def())),
        spec_rule(original, get_tower_u8_range()));
    thm transfer = inst_rule(TERM_PAIR_LIST(
        (term_pair){value_number, `x:int`}), int_arith_rule(
          `0i <= (x:int) && x < 256i ==>
           --9223372036854775808i <= x &&
           x <= 9223372036854775807i`));
    ACCEPT_TAC(unfolded, mp_rule(transfer, byte));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[2]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_value_number_def(), get_tower_signed64_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[3]);
    CONV_TAC(leaf, rewrite_conv(THM_LIST(
        get_cm_value_number_def(), get_tower_wrap64_range())));
  }
  return gnode_prove(root);
}
PROOF thm cm_value_number_signed = cm_prove_value_number_signed();

PROOF static thm cm_prove_pointer_retype_number(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (ty:cm_type) (v:cm_value).
         cm_value_number st (cm_pointer_retype ty v) ==
         cm_value_number st v`);
  gnode with_state = GEN_TAC(root, "st");
  gnode with_type = GEN_TAC(with_state, "ty");
  gnode_list cases = INDUCT_TAC(with_type, `v:cm_value`);
  for (size_t index = 0; index < 2; ++index) {
    gnode leaf = AUTO_INTROS_TAC(cases[index]);
    gnode opened = CONV_TAC(leaf, once_rewrite_conv(THM_LIST(
        get_cm_pointer_retype_def())));
    struct dest_eq_results sides = dest_eq(goal_ccl(opened->g));
    term source_value = dest_comb(sides.tm2).tm2;
    term number = dest_comb(source_value).tm2;
    term normalize = index == 0
        ? `tower_wrap64:int->int`
        : `tower_u8:int->int`;
    term condition = mk_eq(mk_comb(normalize, number), `0i`);
    gnode_list branches = BOOL_CASES_TAC(
        opened, condition, index == 0 ? "hwrapzero" : "hu8zero");
    for (size_t branch = 0; branch < 2; ++branch) {
      CONV_WITH_ASMP_TAC(branches[branch], reduce_rewrite_conv,
          THM_LIST(get_cm_value_number_def(),
            get_tower_wrap64_idempotent(),
            get_tower_u8_idempotent()));
    }
  }
  for (size_t index = 2; index < 4; ++index) {
    gnode leaf = AUTO_INTROS_TAC(cases[index]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_pointer_retype_def(), get_cm_value_number_def())));
  }
  return gnode_prove(root);
}
PROOF thm cm_pointer_retype_number =
    cm_prove_pointer_retype_number();

PROOF static thm cm_prove_type_int_char_distinct(void) {
  gnode root = gnode_new_with_ccl(`~(CMIntTy == CMCharTy)`);
  gnode leaf = DISCH_TAC(root, "hequal");
  thm tagged = ap_term_rule(`cm_type_base_code`,
      assume_rule(`CMIntTy == CMCharTy`));
  thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_type_base_code_def())), tagged);
  CONTR_TAC(leaf, impossible);
  return gnode_prove(root);
}
PROOF thm cm_type_int_char_distinct =
    cm_prove_type_int_char_distinct();

PROOF static thm cm_prove_convert_value_number(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (ty:cm_type) (v:cm_value).
         cm_value_number st (cm_convert_value st ty v) ==
         (if ty == CMCharTy
          then tower_u8 (cm_value_number st v)
          else cm_value_number st v)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm signed_range = specl_rule(
      TERM_LIST(`st:cm_src_state`, `v:cm_value`),
      cm_value_number_signed);
  thm fixed = mp_rule(spec_rule(
      `cm_value_number (st:cm_src_state) (v:cm_value)`,
      get_tower_wrap64_fixed()), signed_range);
  gnode_list int_cases =
      BOOL_CASES_TAC(leaf, `(ty:cm_type) == CMIntTy`, "hint");
  ACCEPT_TAC(int_cases[0], eqt_elim_rule(apply_conversion(
      then_conv(reduce_rewrite_conv(THM_LIST(
          get_cm_convert_value_def(), get_cm_value_number_def(),
          get_tower_wrap64_idempotent(), fixed,
          cm_type_int_char_distinct,
          assume_rule(`(ty:cm_type) == CMIntTy`))),
        reduce_rewrite_conv(THM_LIST())),
      goal_ccl(int_cases[0]->g))));
  gnode_list char_cases = BOOL_CASES_TAC(
      int_cases[1], `(ty:cm_type) == CMCharTy`, "hchar");
  ACCEPT_TAC(char_cases[0], eqt_elim_rule(apply_conversion(
      then_conv(reduce_rewrite_conv(THM_LIST(
          get_cm_convert_value_def(), get_cm_value_number_def(),
          get_tower_u8_idempotent(),
          assume_rule(`~((ty:cm_type) == CMIntTy)`),
          assume_rule(`(ty:cm_type) == CMCharTy`))),
        reduce_rewrite_conv(THM_LIST())),
      goal_ccl(char_cases[0]->g))));
  ACCEPT_TAC(char_cases[1], eqt_elim_rule(apply_conversion(
      then_conv(reduce_rewrite_conv(THM_LIST(
          get_cm_convert_value_def(), cm_pointer_retype_number,
          assume_rule(`~((ty:cm_type) == CMIntTy)`),
          assume_rule(`~((ty:cm_type) == CMCharTy)`))),
        reduce_rewrite_conv(THM_LIST())),
      goal_ccl(char_cases[1]->g))));
  return gnode_prove(root);
}
PROOF thm cm_convert_value_number =
    cm_prove_convert_value_number();

PROOF thm get_cm_value_number_signed_bridge(void) {
  return cm_value_number_signed;
}
PROOF thm get_cm_pointer_retype_number_bridge(void) {
  return cm_pointer_retype_number;
}
PROOF thm get_cm_type_int_char_distinct(void) {
  return cm_type_int_char_distinct;
}
PROOF thm get_cm_convert_value_number_bridge(void) {
  return cm_convert_value_number;
}
