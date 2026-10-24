Require Export SimpleC.EE.QCP_demos_human.cmc_source_execution_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
(* Same numerical/provenance simulation as cmc_sim.c. *)
Inductive cm_spill := CMSpill (slot:Z) (value:cm_value).
Inductive cm_spill_frame := CMSpillFrame (fid fp:Z) (spills:list cm_spill).
Inductive cm_call_sim_frame := CMCallSimFrame (base saved returnpc:Z).
Definition cm_spill_slot s := match s with CMSpill slot _=>slot end.
Definition cm_spill_value s := match s with CMSpill _ value=>value end.
Fixpoint cm_spill_holds slot value spills : Prop := match spills with []=>False | s::rest=>
 if cm_spill_slot s =? slot then cm_spill_value s=value else cm_spill_holds slot value rest end.
Definition cm_spill_frame_fid f := match f with CMSpillFrame fid _ _=>fid end.
Definition cm_spill_frame_fp f := match f with CMSpillFrame _ fp _=>fp end.
Definition cm_spill_frame_spills f := match f with CMSpillFrame _ _ spills=>spills end.
Definition cm_call_sim_base f := match f with CMCallSimFrame b _ _=>b end.
Definition cm_call_sim_saved f := match f with CMCallSimFrame _ s _=>s end.
Definition cm_call_sim_return f := match f with CMCallSimFrame _ _ r=>r end.
Definition cm_value_encoding st v encoded := encoded=cm_value_number st v.
Definition cm_encode_values st values := map (cm_value_number st) values.
Definition cm_live_address st addr := exists region, In region (cm_state_regions st) /\ cm_region_live region=true /\
 cm_region_base (cm_state_regions st) (cm_region_gen region)+cm_region_lo region <= addr /\
 addr < cm_region_base (cm_state_regions st) (cm_region_gen region)+cm_region_hi region.
Definition cm_live_span st base width := forall addr, base<=addr<base+width -> cm_live_address st addr.
Definition cm_tagged_span_valid st := forall addr, cm_state_tagged st addr=true -> cm_live_address st addr -> cm_live_span st addr 8.
Definition cm_initialized_bytes_sim st vmem := forall addr, cm_state_init st addr=true -> cm_live_address st addr -> tower_getb vmem addr=tower_getb (cm_state_mem st) addr.
Definition cm_stored_provenance_sim st vmem := forall addr, cm_state_tagged st addr=true -> cm_live_address st addr ->
 cm_state_init st addr=true /\ tower_getw vmem addr=cm_value_number st (cm_state_tags st addr).
Fixpoint cm_spill_list_sim policy p st vmem fid fp spills : Prop := match spills with []=>True | s::rest=>
 tower_getw vmem (fp+cm_temp_offset policy p fid (cm_spill_slot s))=cm_value_number st (cm_spill_value s) /\
 cm_spill_list_sim policy p st vmem fid fp rest end.
Fixpoint cm_spill_frames_sim policy p st vmem frames : Prop := match frames with []=>True | f::rest=>
 cm_spill_list_sim policy p st vmem (cm_spill_frame_fid f) (cm_spill_frame_fp f) (cm_spill_frame_spills f) /\
 cm_spill_frames_sim policy p st vmem rest end.
Fixpoint cm_call_frames_sim vmem frames calls : Prop := match frames with []=>calls=[] | f::rest=>
 calls<>[] /\ hd 0 calls=cm_call_sim_return f /\ tower_getw vmem (cm_call_sim_base f)=cm_call_sim_saved f /\ cm_call_frames_sim vmem rest (tl calls) end.
Definition cm_operand_suffix_sim st values suffix stack := stack=cm_encode_values st values ++ suffix.
Definition cm_machine_state_sim policy p st target frames spill_frames values suffix :=
 cm_initialized_bytes_sim st (tvm_mem target) /\ cm_stored_provenance_sim st (tvm_mem target) /\
 tower_getw (tvm_mem target) 8=cm_state_fp st /\ cm_call_frames_sim (tvm_mem target) frames (tvm_calls target) /\
 cm_spill_frames_sim policy p st (tvm_mem target) spill_frames /\ tvm_input target=cm_state_input st /\
 tvm_output target=cm_state_output st /\ cm_operand_suffix_sim st values suffix (tvm_stack target).
Definition cm_continuation_sim policy p st (ks:list cm_frame) target frames spill_frames values suffix :=
 cm_machine_state_sim policy p st target frames spill_frames values suffix /\ Zlength frames<=Zlength ks.
Lemma cm_value_encoding_refl st v : cm_value_encoding st v (cm_value_number st v).
Proof. reflexivity. Qed.
Lemma cm_machine_sim_io policy p st target frames spill_frames values suffix :
 cm_machine_state_sim policy p st target frames spill_frames values suffix ->
 tvm_input target=cm_state_input st /\ tvm_output target=cm_state_output st.
Proof. unfold cm_machine_state_sim; tauto. Qed.
Lemma cm_machine_sim_memory policy p st target frames spill_frames values suffix :
 cm_machine_state_sim policy p st target frames spill_frames values suffix ->
 cm_initialized_bytes_sim st (tvm_mem target) /\ cm_stored_provenance_sim st (tvm_mem target).
Proof. unfold cm_machine_state_sim; tauto. Qed.
Lemma cm_value_number_signed st v : tower_signed64 (cm_value_number st v).
Proof. destruct v; cbn [cm_value_number]; try apply tower_wrap64_range.
 - pose proof (tower_u8_range n); unfold tower_signed64,tower_byte_value in *; lia.
 - unfold tower_signed64; lia.
Qed.
Lemma cm_pointer_retype_number st ty v : cm_value_number st (cm_pointer_retype ty v)=cm_value_number st v.
Proof.
 destruct v; cbn [cm_pointer_retype]; try reflexivity.
 - destruct (tower_wrap64 n =? 0) eqn:H; [apply Z.eqb_eq in H; cbn; congruence|reflexivity].
 - destruct (tower_u8 n =? 0) eqn:H; [apply Z.eqb_eq in H; cbn; congruence|reflexivity].
Qed.
Lemma cm_value_number_wrap st v : tower_wrap64 (cm_value_number st v)=cm_value_number st v.
Proof. apply tower_wrap64_fixed,cm_value_number_signed. Qed.
Lemma cm_convert_number st ty v : cm_value_number st (cm_convert_value st ty v)=
 (if cm_type_eqb ty CMCharTy then tower_u8 (cm_value_number st v) else cm_value_number st v).
Proof. destruct ty; cbn [cm_convert_value cm_type_eqb cm_type_dec cm_value_number]; try rewrite cm_pointer_retype_number; try rewrite tower_u8_idempotent; try rewrite tower_wrap64_idempotent,cm_value_number_wrap; reflexivity. Qed.
Lemma tower_getw_ext m1 m2 a : (forall i, 0<=i<8 -> tower_getb m1 (a+i)=tower_getb m2 (a+i)) -> tower_getw m1 a=tower_getw m2 a.
Proof. intro H; unfold tower_getw; rewrite (H 0),(H 1),(H 2),(H 3),(H 4),(H 5),(H 6),(H 7) by lia; reflexivity. Qed.
Lemma cm_initialized_word_bytes init base : cm_bytes_initialized init base 8=true -> forall i, 0<=i<8 -> init (base+i)=true.
Proof. unfold cm_bytes_initialized; cbn; repeat rewrite Bool.andb_true_iff; intros H i Hi.
 assert (i=0 \/ i=1 \/ i=2 \/ i=3 \/ i=4 \/ i=5 \/ i=6 \/ i=7) by lia.
 repeat match goal with H: _ \/ _ |- _ => destruct H end; subst; try rewrite Z.add_0_r; tauto.
Qed.
Lemma cm_initialized_word_sim st vmem base : cm_initialized_bytes_sim st vmem ->
 cm_bytes_initialized (cm_state_init st) base 8=true -> cm_live_span st base 8 -> tower_getw vmem base=tower_getw (cm_state_mem st) base.
Proof. intros Hsim Hinit Hlive; apply tower_getw_ext; intros i Hi; apply Hsim.
 - now apply cm_initialized_word_bytes.
 - apply Hlive; lia.
Qed.
Lemma cm_load_char_sim st vmem ptr : cm_initialized_bytes_sim st vmem ->
 cm_load_ok CMCharTy ptr st=true -> cm_live_span st (cm_value_number st ptr) 1 ->
 cm_value_number st (cm_load_value CMCharTy ptr st)=tower_getb vmem (cm_value_number st ptr).
Proof.
 intros Hsim Hok Hlive. pose proof (cm_load_requires_initialized _ _ _ Hok) as Hi.
 unfold cm_bytes_initialized,cm_store_width in Hi; cbn in Hi; rewrite Bool.andb_true_r in Hi.
 cbn [cm_load_value cm_value_number]; unfold tower_getb at 1; rewrite tower_u8_idempotent.
 symmetry; apply Hsim; [exact Hi|apply Hlive; lia].
Qed.
Lemma cm_load_int_sim st vmem ptr : cm_initialized_bytes_sim st vmem ->
 cm_load_ok CMIntTy ptr st=true -> cm_live_span st (cm_value_number st ptr) 8 ->
 cm_value_number st (cm_load_value CMIntTy ptr st)=tower_getw vmem (cm_value_number st ptr).
Proof.
 intros Hsim Hok Hlive. pose proof (cm_load_requires_initialized _ _ _ Hok) as Hi.
 pose proof (cm_initialized_word_sim st vmem _ Hsim Hi Hlive) as Heq.
 cbn [cm_load_value cm_value_number]. rewrite <-Heq. unfold tower_getw,tower_decode8; apply tower_wrap64_idempotent.
Qed.
Lemma cm_load_pointer_sim st vmem ptr ty : cm_initialized_bytes_sim st vmem -> cm_stored_provenance_sim st vmem ->
 cm_load_ok (CMPtrTy ty) ptr st=true -> cm_live_span st (cm_value_number st ptr) 8 ->
 cm_value_number st (cm_load_value (CMPtrTy ty) ptr st)=tower_getw vmem (cm_value_number st ptr).
Proof.
 intros Hsim Hprov Hok Hlive. pose proof (cm_load_requires_initialized _ _ _ Hok) as Hi.
 pose proof (cm_initialized_word_sim st vmem _ Hsim Hi Hlive) as Heq.
 cbn [cm_load_value]. destruct (tower_getw (cm_state_mem st) (cm_value_number st ptr) =? 0) eqn:Hz.
 - apply Z.eqb_eq in Hz; cbn; congruence.
 - rewrite cm_pointer_retype_number. unfold cm_load_ok in Hok; cbn [cm_is_pointerb] in Hok.
   rewrite Hz in Hok. repeat rewrite Bool.andb_true_iff in Hok. cbn in Hok; repeat rewrite Bool.andb_true_iff in Hok.
   assert (Ht:cm_state_tagged st (cm_value_number st ptr)=true) by tauto.
   symmetry; apply (proj2 (Hprov (cm_value_number st ptr) Ht (Hlive (cm_value_number st ptr) ltac:(lia)))).
Qed.
Lemma cm_store_mem_inside ty base n m1 m2 a : base<=a<base+cm_store_width ty ->
 tower_getb (cm_store_mem ty base n m1) a=tower_getb (cm_store_mem ty base n m2) a.
Proof.
 intro H. destruct ty; cbn [cm_store_mem cm_store_width] in *; unfold tower_getb,tower_setb,tower_setw;
 repeat match goal with |- context[if ?b then _ else _] => destruct b eqn:? end; try reflexivity;
 repeat match goal with H:(_ =? _)=false |- _ => apply Z.eqb_neq in H end; exfalso; lia.
Qed.
Lemma cm_store_mem_outside ty base n mem a : (a<base \/ base+cm_store_width ty<=a) ->
 tower_getb (cm_store_mem ty base n mem) a=tower_getb mem a.
Proof.
 intro H. destruct ty; cbn [cm_store_mem cm_store_width] in *; unfold tower_getb,tower_setb,tower_setw;
 repeat match goal with |- context[if ?b then _ else _] => destruct b eqn:? end; try reflexivity;
 repeat match goal with H:(_ =? _)=true |- _ => apply Z.eqb_eq in H end; exfalso; lia.
Qed.
Lemma cm_store_live_address ty ptr v st a : cm_live_address (cm_state_store ty ptr v st) a <-> cm_live_address st a.
Proof. reflexivity. Qed.
Lemma cm_store_initialized_sim ty ptr v st vmem : cm_initialized_bytes_sim st vmem ->
 cm_initialized_bytes_sim (cm_state_store ty ptr v st)
 (cm_store_mem ty (cm_value_number st ptr) (cm_value_number st (cm_convert_value st ty v)) vmem).
Proof.
 intros Hsim a Hinit Hlive. change (cm_live_address st a) in Hlive.
 change (tower_getb (cm_store_mem ty (cm_value_number st ptr) (cm_value_number st (cm_convert_value st ty v)) vmem) a =
 tower_getb (cm_store_mem ty (cm_value_number st ptr) (cm_value_number st (cm_convert_value st ty v)) (cm_state_mem st)) a).
 destruct (Z_lt_dec a (cm_value_number st ptr)) as [Hlo|Hlo];
 [repeat rewrite cm_store_mem_outside by (left; exact Hlo)|
 destruct (Z_lt_dec a (cm_value_number st ptr+cm_store_width ty)) as [Hhi|Hhi];
 [apply cm_store_mem_inside; lia|repeat rewrite cm_store_mem_outside by (right; lia)]];
 apply Hsim; try exact Hlive;
 change (cm_mark_init (cm_state_init st) (cm_value_number st ptr) (cm_store_width ty) a=true) in Hinit;
 unfold cm_mark_init in Hinit; apply Bool.orb_true_iff in Hinit; destruct Hinit as [Hinit|Hinit]; try exact Hinit;
 apply Bool.andb_true_iff in Hinit; destruct Hinit as [Hb He]; apply Z.leb_le in Hb; apply Z.ltb_lt in He; lia.
Qed.
