Require Export SimpleC.EE.QCP_demos_human.cmc_target_arg_call_migration_lib.
From AUXLib Require Import ListLib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_spill_within_holds_bounds policy p fid fp oldfp spills slot value :
 cm_frame_segment policy p fid fp oldfp ->cm_spills_within_frame policy p fid fp oldfp spills ->cm_spill_holds slot value spills ->
 0<=slot<cm_temp_slots(cm_function_at policy fid(cm_program_functions p)).
Proof.
 intros SEG;induction spills as[|[s v]rest IH];cbn[cm_spills_within_frame cm_spill_holds cm_spill_slot];[tauto|].
 intros[LOW[HIGH REST]];destruct(s=?slot)eqn:E;intro HOLD;[apply Z.eqb_eq in E;subst s|now apply IH].
 unfold cm_frame_segment,cm_temp_offset,cm_frame_size in *;intuition lia.
Qed.
Lemma cm_runtime_held_slot_bounds policy ap p all cursors fid fp active spills saved calls slot value :
 cm_runtime_stack policy ap p all fid fp active cursors spills saved calls ->0<=fid ->cm_spill_holds slot value spills ->
 0<=slot<cm_temp_slots(cm_function_at policy fid(cm_program_functions p)).
Proof.
 revert fid fp active spills saved calls;induction cursors as[|c rest IH];intros fid fp active spills saved calls RT FID HOLD;[contradiction|].
 cbn[cm_runtime_stack]in RT;destruct(cm_phase_is_call(cm_cursor_phase c)).
 - destruct RT as[_[SEG[SP _]]];eapply cm_spill_within_holds_bounds;eassumption.
 - destruct(cm_phase_is_scope(cm_cursor_phase c));[destruct RT as[_[_ RT]];eapply IH;eassumption|].
   destruct(cm_phase_is_halt(cm_cursor_phase c));[destruct RT as[BAD _];lia|eapply IH;eassumption].
Qed.
Lemma cm_init_succeeds_ready sp p fid slot v st ks :
 cm_task_succeeds sp(cm_vapply sp p fid(CMInitK slot)v st ks) ->
 cm_binding_address_ok sp p fid 1 slot st=true /\cm_store_ok(cm_slot_ty(cm_source_slot_at sp slot(cm_function_locals(cm_source_function_at sp fid p))))(cm_state_env st 1 slot)st=true.
Proof.
 cbn[cm_vapply];destruct(cm_binding_address_ok sp p fid 1 slot st && cm_store_ok(cm_slot_ty(cm_source_slot_at sp slot(cm_function_locals(cm_source_function_at sp fid p))))(cm_state_env st 1 slot)st)eqn:E;intro S;[now apply andb_true_iff in E|cm_ready_error].
Qed.
