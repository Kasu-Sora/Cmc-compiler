(* Source runtime values, provenance and state from cmc_lang.c. *)
Require Export SimpleC.EE.QCP_demos_human.cmc_tvm_execution_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Inductive cm_value := CMIntV (n:Z) | CMCharV (n:Z) | CMNullV | CMPtrV (gen lo hi off:Z) (ty:cm_type).
Inductive cm_region := CMRegion (gen base lo hi:Z) (writable live:bool).
Inductive cm_src_state := CMState (mem:Z->Z) (init:Z->bool) (tags:Z->cm_value)
 (tagged:Z->bool) (env:Z->Z->cm_value) (input output:list Z) (fp nextgen:Z) (regions:list cm_region).
Inductive cm_control := CMNormal | CMBreak | CMContinue | CMReturn (v:cm_value) | CMExit (status:Z) | CMError (status:Z).
Definition cm_region_gen r := match r with CMRegion g _ _ _ _ _ => g end.
Definition cm_region_base_field r := match r with CMRegion _ b _ _ _ _ => b end.
Definition cm_region_lo r := match r with CMRegion _ _ l _ _ _ => l end.
Definition cm_region_hi r := match r with CMRegion _ _ _ h _ _ => h end.
Definition cm_region_writable r := match r with CMRegion _ _ _ _ w _ => w end.
Definition cm_region_live r := match r with CMRegion _ _ _ _ _ l => l end.
Definition cm_state_mem st := match st with CMState m _ _ _ _ _ _ _ _ _ => m end.
Definition cm_state_init st := match st with CMState _ i _ _ _ _ _ _ _ _ => i end.
Definition cm_state_tags st := match st with CMState _ _ t _ _ _ _ _ _ _ => t end.
Definition cm_state_tagged st := match st with CMState _ _ _ t _ _ _ _ _ _ => t end.
Definition cm_state_env st := match st with CMState _ _ _ _ e _ _ _ _ _ => e end.
Definition cm_state_input st := match st with CMState _ _ _ _ _ i _ _ _ _ => i end.
Definition cm_state_output st := match st with CMState _ _ _ _ _ _ o _ _ _ => o end.
Definition cm_state_fp st := match st with CMState _ _ _ _ _ _ _ f _ _ => f end.
Definition cm_state_nextgen st := match st with CMState _ _ _ _ _ _ _ _ n _ => n end.
Definition cm_state_regions st := match st with CMState _ _ _ _ _ _ _ _ _ r => r end.
Definition cm_state_make := CMState.
Fixpoint cm_region_base regions gen := match regions with [] => gen | r::rs =>
 if cm_region_gen r =? gen then cm_region_base_field r else cm_region_base rs gen end.
Definition cm_value_type v := match v with
 | CMIntV _ => CMIntTy | CMCharV _ => CMCharTy | CMNullV => CMPtrTy CMCharTy | CMPtrV _ _ _ _ ty => CMPtrTy ty end.
Definition cm_value_number st v := match v with
 | CMIntV n => tower_wrap64 n | CMCharV n => tower_u8 n | CMNullV => 0
 | CMPtrV gen lo hi off ty => tower_wrap64 (cm_region_base (cm_state_regions st) gen + off) end.
Definition cm_pointer_retype ty v := match v with
 | CMIntV n => if tower_wrap64 n =? 0 then CMNullV else CMIntV n
 | CMCharV n => if tower_u8 n =? 0 then CMNullV else CMCharV n
 | CMNullV => CMNullV | CMPtrV gen lo hi off oldty => CMPtrV gen lo hi off (cm_pointee ty) end.
Definition cm_convert_value st ty v := match ty with
 | CMIntTy => CMIntV (tower_wrap64 (cm_value_number st v))
 | CMCharTy => CMCharV (tower_u8 (cm_value_number st v)) | _ => cm_pointer_retype ty v end.
Definition cm_truth st v := negb (cm_value_number st v =? 0).
Definition cm_ptr_offset v := match v with CMPtrV _ _ _ o _ => o | _ => 0 end.
Definition cm_ptr_gen v := match v with CMPtrV g _ _ _ _ => g | _ => -1 end.
Definition cm_ptr_lo v := match v with CMPtrV _ l _ _ _ => l | _ => 0 end.
Definition cm_ptr_hi v := match v with CMPtrV _ _ h _ _ => h | _ => 0 end.
Definition cm_ptr_view v := match v with CMIntV _ => CMIntTy | CMCharV _ | CMNullV => CMCharTy | CMPtrV _ _ _ _ t => t end.
Definition cm_ptr_add structs p index := CMPtrV (cm_ptr_gen p) (cm_ptr_lo p) (cm_ptr_hi p)
 (cm_ptr_offset p+index*cm_type_size structs (cm_ptr_view p)) (cm_ptr_view p).
Definition cm_is_null_value v := match v with CMNullV => true | _ => false end.
Definition cm_type_dec : forall x y:cm_type, {x=y}+{x<>y}.
Proof. decide equality. apply Z.eq_dec. Defined.
Definition cm_type_eqb x y := if cm_type_dec x y then true else false.
Definition cm_is_pointerb t := match t with CMPtrTy _ => true | _ => false end.
Lemma cm_type_eqb_spec x y : cm_type_eqb x y = true <-> x=y.
Proof. unfold cm_type_eqb. destruct (cm_type_dec x y); intuition congruence. Qed.
Lemma cm_is_pointerb_spec ty : cm_is_pointerb ty = true <-> cm_is_pointer ty.
Proof. destruct ty; cbn; intuition discriminate. Qed.
Fixpoint cm_pointer_region_ok regions ptr write := match regions with [] => false | r::rs =>
 ((cm_region_gen r =? cm_ptr_gen ptr) && cm_region_live r &&
 (cm_region_lo r <=? cm_ptr_lo ptr) && (cm_ptr_hi ptr <=? cm_region_hi r) &&
 (negb write || cm_region_writable r)) || cm_pointer_region_ok rs ptr write end.
Definition cm_pointer_live st ptr := (0 <=? cm_ptr_gen ptr) && (cm_ptr_lo ptr <=? cm_ptr_hi ptr) && cm_pointer_region_ok (cm_state_regions st) ptr false.
Definition cm_pointer_writable st ptr := cm_pointer_live st ptr && cm_pointer_region_ok (cm_state_regions st) ptr true.
Definition cm_pointer_compatible st left right := negb (cm_is_null_value left) && negb (cm_is_null_value right) &&
 cm_pointer_live st left && cm_pointer_live st right &&
 (cm_ptr_gen left =? cm_ptr_gen right) && (cm_ptr_lo left =? cm_ptr_lo right) &&
 (cm_ptr_hi left =? cm_ptr_hi right) && cm_type_eqb (cm_ptr_view left) (cm_ptr_view right).
Definition cm_pointer_equality_ok st left right :=
 (cm_is_null_value left && cm_is_null_value right) ||
 (cm_is_null_value left && cm_pointer_live st right) ||
 (cm_pointer_live st left && cm_is_null_value right) || cm_pointer_compatible st left right.
Definition cm_ptr_shift_ok structs ptr index st := cm_pointer_live st ptr &&
 (0 <? cm_type_size structs (cm_ptr_view ptr)) &&
 (cm_ptr_lo ptr <=? cm_ptr_offset ptr+index*cm_type_size structs (cm_ptr_view ptr)) &&
 (cm_ptr_offset ptr+index*cm_type_size structs (cm_ptr_view ptr) <=? cm_ptr_hi ptr).
Definition cm_ptr_diff_ok structs left right st := cm_pointer_compatible st left right &&
 (0 <? cm_type_size structs (cm_ptr_view left)) &&
 ((cm_ptr_offset left-cm_ptr_offset right) mod cm_type_size structs (cm_ptr_view left) =? 0).
Definition cm_binary_ok p op left right st :=
 if (op =? 2) || (op =? 3) then
   if cm_is_pointerb (cm_value_type left) || cm_is_pointerb (cm_value_type right)
   then cm_pointer_equality_ok st left right else true
 else if (4 <=? op) && (op <=? 7) then
   if cm_is_pointerb (cm_value_type left) || cm_is_pointerb (cm_value_type right)
   then cm_pointer_compatible st left right else true
 else if op =? 8 then
   if cm_is_pointerb (cm_value_type left) then cm_ptr_shift_ok (cm_program_structs p) left (cm_value_number st right) st
   else if cm_is_pointerb (cm_value_type right) then cm_ptr_shift_ok (cm_program_structs p) right (cm_value_number st left) st else true
 else if op =? 9 then
   if cm_is_pointerb (cm_value_type left) && cm_is_pointerb (cm_value_type right)
   then cm_ptr_diff_ok (cm_program_structs p) left right st
   else if cm_is_pointerb (cm_value_type left) then cm_ptr_shift_ok (cm_program_structs p) left (tower_neg (cm_value_number st right)) st else true
 else if (op =? 11) || (op =? 12) then negb (cm_value_number st right =? 0) else true.
Definition cm_state_io st input output := CMState (cm_state_mem st) (cm_state_init st)
 (cm_state_tags st) (cm_state_tagged st) (cm_state_env st) input output (cm_state_fp st) (cm_state_nextgen st) (cm_state_regions st).
Definition cm_state_env_set st env := CMState (cm_state_mem st) (cm_state_init st)
 (cm_state_tags st) (cm_state_tagged st) env (cm_state_input st) (cm_state_output st) (cm_state_fp st) (cm_state_nextgen st) (cm_state_regions st).
Definition cm_state_frame st env fp nextgen regions := CMState (cm_state_mem st) (cm_state_init st)
 (cm_state_tags st) (cm_state_tagged st) env (cm_state_input st) (cm_state_output st) fp nextgen regions.
Definition cm_store_width ty : Z := match ty with CMCharTy => 1 | _ => 8 end.
Definition cm_mark_init (old:Z->bool) base width a := old a || ((base <=? a) && (a <? base+width)).
Definition cm_clear_init (old:Z->bool) base width a := old a && negb ((base <=? a) && (a <? base+width)).
Definition cm_clear_tagged (old:Z->bool) base width a := old a && negb ((0 <? width) && (a <? base+width) && (base <? a+8)).
Definition cm_store_mem ty base n mem := match ty with CMCharTy => tower_setb mem base (tower_u8 n) | _ => tower_setw mem base (tower_wrap64 n) end.
Definition cm_state_store ty ptr v st :=
 let addr := cm_value_number st ptr in
 let value := cm_convert_value st ty v in
 CMState (cm_store_mem ty addr (cm_value_number st value) (cm_state_mem st))
 (cm_mark_init (cm_state_init st) addr (cm_store_width ty))
 (if cm_is_pointerb ty then fun a => if a =? addr then value else cm_state_tags st a else cm_state_tags st)
 (if cm_is_pointerb ty then fun a => ((a =? addr) && negb (cm_value_number st value =? 0)) ||
     cm_clear_tagged (cm_state_tagged st) addr 8 a
  else cm_clear_tagged (cm_state_tagged st) addr (cm_store_width ty))
 (cm_state_env st) (cm_state_input st) (cm_state_output st) (cm_state_fp st) (cm_state_nextgen st) (cm_state_regions st).
Definition cm_bytes_initialized (init:Z->bool) base width := init base && ((width =? 1) ||
 (init (base+1) && init (base+2) && init (base+3) && init (base+4) &&
 init (base+5) && init (base+6) && init (base+7))).
Definition cm_store_ok ty ptr st := cm_pointer_writable st ptr &&
 (cm_ptr_lo ptr <=? cm_ptr_offset ptr) && (cm_ptr_offset ptr+cm_store_width ty <=? cm_ptr_hi ptr) &&
 (match ty with CMCharTy => tower_addr_validb (cm_value_number st ptr) | _ => tower_word_validb (cm_value_number st ptr) end).
Definition cm_load_ok ty ptr st := cm_pointer_live st ptr &&
 (cm_ptr_lo ptr <=? cm_ptr_offset ptr) && (cm_ptr_offset ptr+cm_store_width ty <=? cm_ptr_hi ptr) &&
 (match ty with CMCharTy => tower_addr_validb (cm_value_number st ptr) | _ => tower_word_validb (cm_value_number st ptr) end) &&
 cm_bytes_initialized (cm_state_init st) (cm_value_number st ptr) (cm_store_width ty) &&
 (negb (cm_is_pointerb ty) || ((tower_getw (cm_state_mem st) (cm_value_number st ptr) =? 0) ||
 (cm_state_tagged st (cm_value_number st ptr) && cm_is_pointerb (cm_value_type (cm_state_tags st (cm_value_number st ptr)))))).
Definition cm_load_value ty ptr st := match ty with
 | CMCharTy => CMCharV (tower_getb (cm_state_mem st) (cm_value_number st ptr))
 | CMIntTy => CMIntV (tower_getw (cm_state_mem st) (cm_value_number st ptr))
 | _ => if tower_getw (cm_state_mem st) (cm_value_number st ptr) =? 0 then CMNullV
        else cm_pointer_retype ty (cm_state_tags st (cm_value_number st ptr)) end.
Definition cm_binary_value p op left right (ty:cm_type) st :=
 let l := cm_value_number st left in let r := cm_value_number st right in
 if op =? 0 then CMIntV (tower_bool (cm_truth st left || cm_truth st right))
 else if op =? 1 then CMIntV (tower_bool (cm_truth st left && cm_truth st right))
 else if op =? 2 then CMIntV (tower_bool (l =? r))
 else if op =? 3 then CMIntV (tower_bool (negb (l =? r)))
 else if op =? 4 then CMIntV (tower_bool (l <? r))
 else if op =? 5 then CMIntV (tower_bool (l <=? r))
 else if op =? 6 then CMIntV (tower_bool (r <? l))
 else if op =? 7 then CMIntV (tower_bool (r <=? l))
 else if (op =? 8) && cm_is_pointerb (cm_value_type left) then cm_ptr_add (cm_program_structs p) left r
 else if (op =? 8) && cm_is_pointerb (cm_value_type right) then cm_ptr_add (cm_program_structs p) right l
 else if op =? 8 then CMIntV (tower_add l r)
 else if (op =? 9) && cm_is_pointerb (cm_value_type left) && cm_is_pointerb (cm_value_type right) then
  CMIntV (tower_div (tower_sub (cm_ptr_offset left) (cm_ptr_offset right)) (cm_type_size (cm_program_structs p) (cm_ptr_view left)))
 else if (op =? 9) && cm_is_pointerb (cm_value_type left) then cm_ptr_add (cm_program_structs p) left (tower_neg r)
 else if op =? 9 then CMIntV (tower_sub l r)
 else if op =? 10 then CMIntV (tower_mul l r)
 else if op =? 11 then CMIntV (tower_div l r) else CMIntV (tower_mod l r).
Definition cm_unary_value op arg st := if op =? 0 then CMIntV (tower_neg (cm_value_number st arg)) else CMIntV (tower_bool (negb (cm_truth st arg))).

Lemma cm_store_preserves_observation ty ptr v st :
 cm_state_input (cm_state_store ty ptr v st) = cm_state_input st /\
 cm_state_output (cm_state_store ty ptr v st) = cm_state_output st.
Proof. split; reflexivity. Qed.
Lemma cm_store_preserves_provenance ty ptr v st :
 cm_state_regions (cm_state_store ty ptr v st) = cm_state_regions st /\
 cm_state_env (cm_state_store ty ptr v st) = cm_state_env st /\
 cm_state_fp (cm_state_store ty ptr v st) = cm_state_fp st /\
 cm_state_nextgen (cm_state_store ty ptr v st) = cm_state_nextgen st.
Proof. repeat split; reflexivity. Qed.
Lemma cm_store_value_number ty ptr v st w : cm_value_number (cm_state_store ty ptr v st) w = cm_value_number st w.
Proof. destruct w; reflexivity. Qed.
Lemma cm_mark_init_inside old base width a : base <= a < base+width -> cm_mark_init old base width a = true.
Proof. intros H. unfold cm_mark_init. apply Bool.orb_true_iff; right. apply Bool.andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia. Qed.
Lemma cm_clear_init_inside old base width a : base <= a < base+width -> cm_clear_init old base width a = false.
Proof. intros H. unfold cm_clear_init. assert ((base <=? a) && (a <? base+width) = true) as -> by (apply Bool.andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia). apply Bool.andb_false_r. Qed.
Lemma cm_store_initializes ty ptr v st a :
 cm_value_number st ptr <= a < cm_value_number st ptr + cm_store_width ty ->
 cm_state_init (cm_state_store ty ptr v st) a = true.
Proof. apply cm_mark_init_inside. Qed.
Lemma cm_store_tags_pointer ty ptr v st : cm_is_pointerb ty = true ->
 cm_state_tags (cm_state_store ty ptr v st) (cm_value_number st ptr) = cm_convert_value st ty v.
Proof. intros H; cbn [cm_state_store cm_state_tags]. rewrite H, Z.eqb_refl; reflexivity. Qed.
Lemma cm_load_requires_initialized ty ptr st : cm_load_ok ty ptr st = true ->
 cm_bytes_initialized (cm_state_init st) (cm_value_number st ptr) (cm_store_width ty) = true.
Proof. unfold cm_load_ok; repeat rewrite Bool.andb_true_iff; tauto. Qed.
