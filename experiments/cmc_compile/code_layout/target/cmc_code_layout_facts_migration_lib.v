Require Export SimpleC.EE.QCP_demos_human.cmc_code_layout_defs_migration_lib.
From Coq Require Import ZArith List Bool Lia.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_task_layout_done sp ap p st ctl status ann : cm_task_layout sp ap p (CMDoneTask st ctl status) ann.
Proof. exact I. Qed.
Lemma cm_task_layout_initial sp ap p input : cm_task_layout sp ap p (CMStartTask p input) cm_initial_annotation.
Proof.
 split; [|reflexivity].
 unfold cm_code_at; exists [],([TVMInst TVMPushOp 256;TVMInst TVMModOp 0;TVMInst TVMPushOp 256;TVMInst TVMAddOp 0;TVMInst TVMPushOp 256;TVMInst TVMModOp 0;TVMInst TVMHaltOp 0]++cm_emit_functions (cm_source_function_policy sp) p 0 (cm_program_functions p)); split; reflexivity.
Qed.
Lemma cm_saved_layout_plain sp ap p fid pc temp breakpc continuepc ann :
 cm_saved_layout sp ap p (cm_model_code (cm_source_function_policy sp) p) fid (cm_ann_cursors (cm_ann_plain pc temp breakpc continuepc ann)) (cm_ann_calls (cm_ann_plain pc temp breakpc continuepc ann)) <-> cm_saved_layout sp ap p (cm_model_code (cm_source_function_policy sp) p) fid (cm_ann_cursors ann) (cm_ann_calls ann).
Proof. reflexivity. Qed.
Lemma cm_layout_rvalue_code_length policy p fid expr pc temp : Zlength (cm_emit_rvalue policy p fid pc temp expr)=cm_rvalue_code_count policy p fid expr.
Proof. exact (proj2 (cm_emit_pair_lengths__store_bounds policy p fid expr pc temp)). Qed.
Lemma cm_layout_lvalue_code_length policy p fid expr pc temp : Zlength (cm_emit_lvalue policy p fid pc temp expr)=cm_lvalue_code_count policy p fid expr.
Proof. exact (proj1 (cm_emit_pair_lengths__store_bounds policy p fid expr pc temp)). Qed.
Lemma cm_layout_load_length ty : Zlength (cm_load_code ty)=1.
Proof. destruct ty; reflexivity. Qed.
Lemma cm_layout_store_length ty : Zlength (cm_store_code ty)=1.
Proof. destruct ty; reflexivity. Qed.
Lemma cm_layout_temp_store_length policy p fid temp : Zlength (cm_temp_store_code policy p fid temp)=5.
Proof. reflexivity. Qed.
Lemma cm_layout_temp_load_length policy p fid temp : Zlength (cm_temp_load_code policy p fid temp)=5.
Proof. reflexivity. Qed.
Lemma cm_layout_char_normalize_length ty : Zlength (cm_char_normalize_code ty)=cm_char_normalize_count ty.
Proof. destruct ty; reflexivity. Qed.
Lemma cm_layout_param_store_length policy p fid slot params : Zlength (cm_emit_param_stores policy p fid slot params)=cm_param_stores_count params.
Proof. revert slot; induction params as [|h rest IH]; intro slot; cbn [cm_emit_param_stores cm_param_stores_count]; [reflexivity|]. repeat rewrite Zlength_app. rewrite IH,cm_layout_char_normalize_length,cm_layout_store_length; change (Zlength (cm_fp_relative_address_code (cm_param_offset policy p fid slot))) with 4; lia. Qed.
Lemma cm_layout_prologue_length policy p fid : Zlength (cm_emit_prologue policy p fid)=cm_function_prologue_count (cm_function_at policy fid (cm_program_functions p)).
Proof. unfold cm_emit_prologue,cm_function_prologue_count; rewrite Zlength_app,cm_layout_param_store_length; reflexivity. Qed.
Lemma cm_layout_function_length policy p fid : Zlength (cm_emit_function policy p fid)=cm_function_code_count policy p fid.
Proof. unfold cm_emit_function,cm_function_code_count; repeat rewrite Zlength_app; rewrite cm_layout_prologue_length,cm_emit_stmt_length__stmt_capacity; change (Zlength [TVMInst TVMPushOp 0]) with 1; change (Zlength cm_return_epilogue) with 6; lia. Qed.
