Require Export SimpleC.EE.QCP_demos_human.cmc_target_parameter_ready_migration_lib.
From AUXLib Require Import ListLib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_pointer_region_member_ready regions gen base size ty write :
 In(CMRegion gen base 0 size true true)regions ->cm_pointer_region_ok regions(CMPtrV gen 0 size 0 ty)write=true.
Proof.
 induction regions as[|r rs IH];cbn[In];[contradiction|];intros[->|IN];cbn[cm_pointer_region_ok];apply orb_true_iff;[left|right;now apply IH].
 cbn[cm_region_gen cm_region_live cm_region_lo cm_region_hi cm_region_writable cm_ptr_gen cm_ptr_lo cm_ptr_hi];rewrite Z.eqb_refl,!Z.leb_refl;destruct write;reflexivity.
Qed.
Lemma cm_pending_parameter_ready sp p fid st j :
 cm_function_wf(cm_source_function_policy sp)p(cm_source_function_at sp fid p) ->
 cm_frame_segment(cm_source_function_policy sp)p fid(cm_state_fp st-cm_frame_size(cm_program_structs p)(cm_source_function_at sp fid p))(cm_state_fp st) ->
 0<=cm_state_nextgen st ->0<=j<Zlength(cm_function_params(cm_source_function_at sp fid p)) ->
 cm_parameter_ready sp p fid(cm_call_pending_base sp p fid st)j(cm_slot_ty(cm_source_slot_at sp j(cm_function_params(cm_source_function_at sp fid p)))).
Proof.
 intros FW SEG GEN J;pose proof FW as[_[PW[LW _]]].
 pose proof(cm_call_param_geometry sp p fid st j FW SEG J)as[NUM[NEXT _]].
 pose proof(cm_param_slot_store_width _ _ j PW J)as WIDTH.
 pose proof(cm_slots_prefix_cell_bounds _ _ j(proj1 PW)J)as BOUNDS.
 pose proof(cm_slots_size_nonnegative__call_bounds _ _ LW)as LN.
 set(ty:=cm_slot_ty(cm_source_slot_at sp j(cm_function_params(cm_source_function_at sp fid p)))).
 assert(W:cm_slot_size(cm_program_structs p)(cm_source_slot_at sp j(cm_function_params(cm_source_function_at sp fid p)))=cm_store_width ty).
 { unfold ty;rewrite(cm_source_slot_at_valid sp _ j J);exact WIDTH. }
 assert(ENV:cm_state_env(cm_call_pending_base sp p fid st)2 j=CMPtrV(cm_state_nextgen st+j)0(cm_store_width ty)0 ty).
 { change(CMPtrV(cm_state_nextgen st+j)0(cm_slot_size(cm_program_structs p)(cm_source_slot_at sp j(cm_function_params(cm_source_function_at sp fid p))))0 ty=CMPtrV(cm_state_nextgen st+j)0(cm_store_width ty)0 ty). rewrite W;reflexivity. }
 assert(NUM0:cm_value_number(cm_call_pending_base sp p fid st)(cm_state_env(cm_call_pending_base sp p fid st)2 j)=cm_param_base sp p fid j(cm_state_fp st-cm_frame_size(cm_program_structs p)(cm_source_function_at sp fid p)))by exact NUM.
 assert(ADDR:16<=cm_param_base sp p fid j(cm_state_fp st-cm_frame_size(cm_program_structs p)(cm_source_function_at sp fid p)) /\ cm_param_base sp p fid j(cm_state_fp st-cm_frame_size(cm_program_structs p)(cm_source_function_at sp fid p))+cm_store_width ty<=1048576).
 { unfold cm_param_base;unfold cm_frame_segment,cm_temp_offset,cm_source_function_at in SEG;unfold ty;rewrite(cm_source_slot_at_valid sp _ j J);unfold cm_source_function_at in *;intuition lia. }
 assert(REG:forall write,cm_pointer_region_ok(cm_state_regions(cm_call_pending_base sp p fid st))(cm_state_env(cm_call_pending_base sp p fid st)2 j)write=true).
 { intro write;rewrite ENV;apply cm_pointer_region_member_ready with(cm_param_base sp p fid j(cm_state_fp st-cm_frame_size(cm_program_structs p)(cm_source_function_at sp fid p))).
   cbn[cm_call_pending_base cm_call_base_state cm_state_regions];apply in_or_app;left.
   pose proof(cm_regions_for_slots_member(cm_program_structs p)(cm_function_params(cm_source_function_at sp fid p))(cm_state_nextgen st)(cm_state_fp st-cm_frame_size(cm_program_structs p)(cm_source_function_at sp fid p)+8)j J)as IN.
   rewrite WIDTH in IN;unfold ty;rewrite(cm_source_slot_at_valid sp _ j J);exact IN. }
 unfold cm_parameter_ready;split;[reflexivity|];split.
 - unfold cm_store_ok,cm_pointer_writable,cm_pointer_live;rewrite(REG false),(REG true),NUM0,ENV.
   cbn[cm_ptr_gen cm_ptr_lo cm_ptr_hi cm_ptr_offset];repeat rewrite andb_true_iff;repeat split;try(apply Z.leb_le;pose proof(cm_store_width_positive ty);lia).
   destruct ty;first[apply tower_addr_validb_spec|apply tower_word_validb_spec];unfold tower_addr_valid,tower_word_valid;cbn[cm_store_width]in ADDR;lia.
 - rewrite NUM0;cbn[cm_call_pending_base cm_call_base_state cm_state_fp];unfold cm_param_base,cm_param_offset,cm_source_function_at.
   rewrite tower_wrap64_fixed;[lia|unfold tower_signed64;unfold cm_param_base,cm_source_function_at in ADDR;pose proof(cm_store_width_positive ty);lia].
Qed.
