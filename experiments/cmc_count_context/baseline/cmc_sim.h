#pragma once

#include "proof/proof.h"
#include "cmc_codegen.h"

PROOF extern thm cm_spill_slot_def;
PROOF extern thm cm_spill_value_def;
PROOF extern thm cm_spill_holds_def;
PROOF extern thm cm_spill_frame_fid_def;
PROOF extern thm cm_spill_frame_fp_def;
PROOF extern thm cm_spill_frame_spills_def;
PROOF extern thm cm_call_sim_base_def;
PROOF extern thm cm_call_sim_saved_def;
PROOF extern thm cm_call_sim_return_def;
PROOF extern thm cm_value_encoding_def;
PROOF extern thm cm_encode_values_def;
PROOF extern thm cm_live_address_def;
PROOF extern thm cm_live_span_def;
PROOF extern thm cm_tagged_span_valid_def;
PROOF extern thm cm_initialized_bytes_sim_def;
PROOF extern thm cm_stored_provenance_sim_def;
PROOF extern thm cm_spill_list_sim_def;
PROOF extern thm cm_spill_frames_sim_def;
PROOF extern thm cm_call_frames_sim_def;
PROOF extern thm cm_operand_suffix_sim_def;
PROOF extern thm cm_machine_state_sim_def;
PROOF extern thm cm_continuation_sim_def;

PROOF extern thm cm_value_encoding_refl;
PROOF extern thm cm_machine_sim_io;

PROOF thm get_cm_value_number_signed_bridge(void);
PROOF thm get_cm_pointer_retype_number_bridge(void);
PROOF thm get_cm_type_int_char_distinct(void);
PROOF thm get_cm_convert_value_number_bridge(void);
