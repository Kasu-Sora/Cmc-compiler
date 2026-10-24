Require Import SimpleC.EE.QCP_demos_human.cmc_function_ready_migration_lib.
From Coq Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.
Check (cm_function_pcs_current : forall policy functions p fid,
 cm_function_pcs_representable policy p functions fid -> cm_i32_code_count (cm_function_pc policy p fid)).
Check (cm_function_id_ready_from_wf : forall policy cg p fid,
 cm_wf_program policy cg p -> 0 <= fid -> fid < Zlength (cm_program_functions p) -> cm_i32_code_count (fid+1)).
Check (cm_concrete_function_ready_from_wf : forall policy cg p fid f,
 cm_wf_program policy cg p -> 0 <= fid -> fid < Zlength (cm_program_functions p) ->
 cm_function_counts_representable policy p fid f ->
 cm_i32_code_count (cm_function_pc policy p fid) -> cm_i32_code_count (cm_function_pc policy p (fid+1)) ->
 cm_concrete_function_ready policy p fid f).
Check (cm_concrete_functions_suffix_ready : forall policy cg functions p fid,
 cm_wf_program policy cg p -> 0 <= fid -> fid + Zlength functions = Zlength (cm_program_functions p) ->
 cm_functions_counts_representable policy p functions fid -> cm_function_pcs_representable policy p functions fid ->
 cm_concrete_functions_ready policy p fid functions).
Check (cm_concrete_functions_ready_from_wf : forall policy cg p,
 cm_wf_program policy cg p -> cm_concrete_functions_ready policy p 0 (cm_program_functions p)).
Check (cm_function_prefix_step : forall policy functions p index,
 0 <= index < Zlength functions -> cm_function_prefix policy p functions (index+1) =
 cm_function_prefix policy p functions index +
 cm_function_code_count policy p (Zlength (cm_program_functions p)-Zlength functions+index)).
Check (cm_function_pc_step : forall policy p fid,
 0 <= fid < Zlength (cm_program_functions p) ->
 cm_function_pc policy p (fid+1) = cm_function_pc policy p fid + cm_function_code_count policy p fid).
(* The exact 18 source conjuncts, including actual emitted statement length.
   This independently checks the already-published count-normalized definition. *)
Lemma function_ready_original_definition : forall policy p fid f,
 cm_concrete_function_ready policy p fid f <->
 (f = cm_function_at policy fid (cm_program_functions p) /\
  cm_function_counts_representable policy p fid f /\
  cm_stmt_wf policy p f false (cm_function_body f) /\
  cm_stmt_counts_representable policy p fid (cm_function_body f) /\
  cm_param_counts_representable (cm_function_params f) /\
  cm_i32_code_count (cm_function_prologue_count f) /\
  cm_i32_code_count (cm_function_pc policy p fid) /\
  cm_i32_code_count (cm_function_pc policy p fid + cm_function_prologue_count f) /\
  cm_i32_code_count ((cm_function_pc policy p fid + cm_function_prologue_count f) +
    Zlength (cm_emit_stmt policy p fid (cm_function_pc policy p fid + cm_function_prologue_count f)
      0 0 0 (cm_function_body f))) /\
  cm_slots_wf (cm_program_structs p) (cm_function_params f) /\
  cm_slots_wf (cm_program_structs p) (cm_function_locals f) /\
  cm_rep_members_safe (cm_function_params f) /\
  cm_rep_members_safe (cm_function_locals f) /\
  cm_rep_stmt_temps_safe (cm_function_body f) /\
  8 + cm_rep_members_size (cm_function_params f) + cm_rep_members_size (cm_function_locals f) +
    8 * cm_stemps (cm_function_body f) <= 2147483647 /\
  cm_temp_offset policy p fid (cm_stemps (cm_function_body f)) <= 2147483647 /\
  cm_function_pc policy p (fid+1) = cm_function_pc policy p fid + cm_function_code_count policy p fid /\
  cm_i32_code_count (cm_function_pc policy p (fid+1))).
Proof.
 intros. unfold cm_concrete_function_ready.
 rewrite cm_emit_stmt_length__stmt_capacity. reflexivity.
Qed.
Goal forall policy p fid, cm_concrete_functions_ready policy p fid [] <-> True.
Proof. reflexivity. Qed.
Goal forall policy p fid f rest, cm_concrete_functions_ready policy p fid (f::rest) <->
 cm_i32_code_count (fid+1) /\ cm_concrete_function_ready policy p fid f /\
 cm_concrete_functions_ready policy p (fid+1) rest.
Proof. reflexivity. Qed.
Print Assumptions cm_function_prefix_step.
Print Assumptions cm_function_pc_step.
Print Assumptions cm_function_pcs_current.
Print Assumptions cm_function_id_ready_from_wf.
Print Assumptions cm_concrete_function_ready_from_wf.
Print Assumptions cm_concrete_functions_suffix_ready.
Print Assumptions cm_concrete_functions_ready_from_wf.
Print Assumptions function_ready_original_definition.
