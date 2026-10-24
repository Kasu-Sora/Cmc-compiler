Require Export SimpleC.EE.QCP_demos_human.cmc_source_state_migration_lib.
Require Import SimpleC.EE.QCP_demos_human.cmc_emit_globals_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
(* Additional choices at NIL retain HOL's total INTH semantics. These are
   interpretation parameters, not hypotheses of compiler correctness. *)
Record cm_source_lookup_policy := CMSourceLookupPolicy {
 cm_source_function_policy : cm_lookup_policy;
 cm_global_nil : nat -> cm_global_d;
 cm_string_nil : nat -> cm_string_d;
 cm_slot_nil : nat -> cm_slot_d;
 cm_struct_nil : nat -> cm_struct_d
}.
Fixpoint cm_total_nth {A:Type} (nil_choice:nat->A) n (xs:list A) := match xs with
 | [] => nil_choice n | x::rest => match n with O=>x | S k=>cm_total_nth nil_choice k rest end end.
Definition cm_source_at {A:Type} sp (nil_choice:nat->A) i xs :=
 cm_total_nth nil_choice (cm_num_of_int (cm_source_function_policy sp) i) xs.
Definition cm_source_global_at sp := cm_source_at sp (cm_global_nil sp).
Definition cm_source_string_at sp := cm_source_at sp (cm_string_nil sp).
Definition cm_source_slot_at sp := cm_source_at sp (cm_slot_nil sp).
Definition cm_source_struct_at sp := cm_source_at sp (cm_struct_nil sp).
Lemma cm_total_nth_some {A} choice n (xs:list A) x : nth_error xs n=Some x -> cm_total_nth choice n xs=x.
Proof. revert n; induction xs as [|h t IH]; intros [|n] H; cbn in *; try discriminate; try congruence; now apply IH. Qed.
Lemma cm_source_at_valid {A} sp choice i (xs:list A) x : 0<=i -> nth_error xs (Z.to_nat i)=Some x -> cm_source_at sp choice i xs=x.
Proof. intros H Hnth; unfold cm_source_at; rewrite cm_num_of_int_nonnegative by exact H; now apply cm_total_nth_some. Qed.
Lemma cm_total_nth_source {A} (lookup:nat->list A->A) choice
 (Hnil:forall n,lookup n []=choice n)
 (Hcons0:forall x xs,lookup O (x::xs)=x)
 (HconsS:forall n x xs,lookup (S n) (x::xs)=lookup n xs) :
 forall n xs, lookup n xs=cm_total_nth choice n xs.
Proof. intros n xs; revert n; induction xs as [|x xs IH]; intros [|n]; cbn; auto; rewrite HconsS; apply IH. Qed.
Definition cm_global_generation index := 1+index.
Definition cm_string_generation p index := 1+Zlength (cm_program_globals p)+index.
Definition cm_first_dynamic_generation p := 1+Zlength (cm_program_globals p)+Zlength (cm_program_strings p).
Definition cm_global_pointer sp p index :=
 let g:=cm_source_global_at sp index (cm_program_globals p) in
 CMPtrV (cm_global_generation index) 0 (cm_global_size (cm_program_structs p) g) 0 (cm_global_ty g).
Definition cm_string_pointer sp p index :=
 CMPtrV (cm_string_generation p index) 0
 (Zlength (cm_string_bytes (cm_source_string_at sp index (cm_program_strings p)))+1) 0 CMCharTy.
Fixpoint cm_global_regions p gs index := match gs with []=>[] | g::rest=>
 CMRegion (cm_global_generation index) (cm_global_address p index) 0
 (cm_global_size (cm_program_structs p) g) true true :: cm_global_regions p rest (index+1) end.
Fixpoint cm_string_regions p ss index := match ss with []=>[] | s::rest=>
 CMRegion (cm_string_generation p index) (cm_string_address p index) 0
 (Zlength (cm_string_bytes s)+1) false true :: cm_string_regions p rest (index+1) end.
Fixpoint cm_write_bytes mem base bytes := match bytes with []=>mem | byte::rest => cm_write_bytes (tower_setb mem base byte) (base+1) rest end.
Definition cm_static_global_init_bytes g := match cm_global_ty g with CMCharTy=>[tower_u8 (cm_global_init g)] | _=>tower_word_bytes (cm_global_init g) end.
Definition cm_static_global_bytes structs g :=
 let size:=cm_global_size structs g in let initial:=cm_static_global_init_bytes g in
 if 0 <=? size then if cm_global_has_init g && (Zlength initial <=? size)
 then initial ++ repeat 0 (Z.to_nat (size-Zlength initial)) else repeat 0 (Z.to_nat size) else [].
Fixpoint cm_static_globals_bytes structs gs := match gs with []=>[] | g::rest=>cm_static_global_bytes structs g ++ cm_static_globals_bytes structs rest end.
Fixpoint cm_static_strings_bytes ss := match ss with []=>[] | s::rest=>cm_string_bytes s ++ [0] ++ cm_static_strings_bytes rest end.
Definition cm_static_data_bytes p := repeat 0 8 ++ cm_static_globals_bytes (cm_program_structs p) (cm_program_globals p) ++ cm_static_strings_bytes (cm_program_strings p).
Definition cm_initial_mem p := cm_write_bytes tower_zero_mem 8 (cm_static_data_bytes p).
Definition cm_initial_state sp p input := CMState (cm_initial_mem p)
 (fun a => (16 <=? a) && (a <? cm_static_size p)) (fun _=>CMNullV) (fun _=>false)
 (fun scope slot=>if scope =? 0 then cm_global_pointer sp p slot else CMNullV)
 input [] 1048576 (cm_first_dynamic_generation p)
 (cm_global_regions p (cm_program_globals p) 0 ++ cm_string_regions p (cm_program_strings p) 0).
Lemma cm_static_global_init_matches g : cm_static_global_init_bytes g=cm_global_init_bytes g.
Proof. unfold cm_static_global_init_bytes, cm_global_init_bytes; destruct (cm_global_ty g); try reflexivity; symmetry; apply cm_counts_word_bytes_eq_tower. Qed.
Lemma cm_static_global_matches structs g : cm_static_global_bytes structs g=cm_global_bytes structs g.
Proof. unfold cm_static_global_bytes, cm_global_bytes; now rewrite cm_static_global_init_matches. Qed.
Lemma cm_static_globals_match structs gs : cm_static_globals_bytes structs gs=cm_globals_bytes structs gs.
Proof. induction gs; cbn; auto; now rewrite cm_static_global_matches, IHgs. Qed.
Lemma cm_static_strings_match ss : cm_static_strings_bytes ss=cm_strings_bytes ss.
Proof. induction ss; cbn; auto; now rewrite IHss. Qed.
Lemma cm_static_data_matches p : cm_static_data_bytes p=cm_model_data_bytes p.
Proof. unfold cm_static_data_bytes, cm_model_data_bytes; now rewrite cm_static_globals_match, cm_static_strings_match. Qed.
Lemma cm_write_bytes_patches bytes base mem : cm_write_bytes mem base bytes=tvm_apply_patches (cm_bytes_patches bytes base) mem.
Proof. revert base mem; induction bytes; intros; cbn; auto. Qed.
Lemma cm_initial_memory_matches policy sp p input :
 cm_state_mem (cm_initial_state sp p input)=tvm_mem (tvm_initial_state (cm_compile_model policy p) input).
Proof. cbn [cm_initial_state cm_state_mem tvm_initial_state tvm_mem cm_compile_model tvm_object_patches].
 unfold cm_initial_mem, cm_model_patches. rewrite cm_static_data_matches, cm_write_bytes_patches; reflexivity. Qed.
Lemma cm_initial_observation_matches policy sp p input :
 cm_state_input (cm_initial_state sp p input)=tvm_input (tvm_initial_state (cm_compile_model policy p) input) /\
 cm_state_output (cm_initial_state sp p input)=tvm_output (tvm_initial_state (cm_compile_model policy p) input).
Proof. split; reflexivity. Qed.
