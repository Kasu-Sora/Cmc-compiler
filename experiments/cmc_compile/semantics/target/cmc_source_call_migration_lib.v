Require Export SimpleC.EE.QCP_demos_human.cmc_source_initial_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Inductive cm_frame := CMHaltK | CMLoadK (ty:cm_type)
 | CMAssignLK (expr:cm_expr) (ty:cm_type) | CMAssignRK (value:cm_value) (ty:cm_type)
 | CMBinLK (op:Z) (expr:cm_expr) (ty:cm_type) | CMBinRK (op:Z) (value:cm_value) (ty:cm_type)
 | CMUnaryK (op:Z) | CMIndexLK (expr:cm_expr) (ty:cm_type) | CMIndexRK (value:cm_value) (ty:cm_type)
 | CMMemberK (mid:Z) | CMPutcK | CMPutiK | CMExitK | CMExprStmtK | CMInitK (slot:Z)
 | CMBlockK (env:Z->Z->cm_value) (regions:list cm_region) | CMSeqK (stmt:cm_stmt)
 | CMIfK (yes no:cm_stmt) | CMWhileGuardK (guard:cm_expr) (body:cm_stmt)
 | CMWhileBodyK (guard:cm_expr) (body:cm_stmt) (env:Z->Z->cm_value) (regions:list cm_region)
 | CMReturnK | CMArgK (fid:Z) (rest:list cm_expr) (values:list cm_value) (ty:cm_type)
 | CMCallK (caller:Z) (env:Z->Z->cm_value) (fp:Z) (regions:list cm_region) (ty:cm_type).
Inductive cm_task := CMStartTask (p:cm_program) (input:list Z)
 | CMRTask (p:cm_program) (fid:Z) (expr:cm_expr) (st:cm_src_state) (ks:list cm_frame)
 | CMLTask (p:cm_program) (fid:Z) (expr:cm_expr) (st:cm_src_state) (ks:list cm_frame)
 | CMSTask (p:cm_program) (fid:Z) (stmt:cm_stmt) (st:cm_src_state) (ks:list cm_frame)
 | CMVTask (p:cm_program) (fid:Z) (value:cm_value) (st:cm_src_state) (ks:list cm_frame)
 | CMCTask (p:cm_program) (fid:Z) (ctl:cm_control) (st:cm_src_state) (ks:list cm_frame)
 | CMDoneTask (st:cm_src_state) (ctl:cm_control) (status:Z).
Inductive cm_outcome := CMOutcome (st:cm_src_state) (ctl:cm_control) (status:Z).
Fixpoint cm_regions_for_slots structs slots gen base := match slots with []=>[] | slot::rest=>
 CMRegion gen base 0 (cm_slot_size structs slot) true true :: cm_regions_for_slots structs rest (gen+1) (base+cm_slot_size structs slot) end.
Definition cm_source_function_at sp fid p := cm_function_at (cm_source_function_policy sp) fid (cm_program_functions p).
Definition cm_param_base sp p fid index fp := fp+8+cm_slots_prefix (cm_program_structs p) (cm_function_params (cm_source_function_at sp fid p)) index.
Definition cm_local_base sp p fid index fp := fp+8+cm_slots_size (cm_program_structs p) (cm_function_params (cm_source_function_at sp fid p))+
 cm_slots_prefix (cm_program_structs p) (cm_function_locals (cm_source_function_at sp fid p)) index.
Definition cm_call_env sp p fid (oldenv:Z->Z->cm_value) (fp:Z) firstgen scope slot :=
 if scope =? 0 then oldenv 0 slot else if scope =? 2 then
 let s:=cm_source_slot_at sp slot (cm_function_params (cm_source_function_at sp fid p)) in
 CMPtrV (firstgen+slot) 0 (cm_slot_size (cm_program_structs p) s) 0 (cm_slot_ty s) else CMNullV.
Definition cm_call_base_state sp p fid st :=
 let f:=cm_source_function_at sp fid p in let fp:=cm_state_fp st-cm_frame_size (cm_program_structs p) f in
 CMState (tower_setw (cm_state_mem st) fp (cm_state_fp st))
 (cm_state_init st) (cm_state_tags st) (cm_state_tagged st)
 (cm_call_env sp p fid (cm_state_env st) fp (cm_state_nextgen st))
 (cm_state_input st) (cm_state_output st) fp (cm_state_nextgen st+Zlength (cm_function_params f))
 (cm_regions_for_slots (cm_program_structs p) (cm_function_params f) (cm_state_nextgen st) (fp+8) ++ cm_state_regions st).
Fixpoint cm_store_params sp p fid values index st := match values with []=>st | v::rest=>
 cm_store_params sp p fid rest (index+1)
 (cm_state_store (cm_slot_ty (cm_source_slot_at sp index (cm_function_params (cm_source_function_at sp fid p)))) (cm_state_env st 2 index) v st) end.
Definition cm_enter_call sp p fid values st := cm_store_params sp p fid values 0 (cm_call_base_state sp p fid st).
Definition cm_activate_local sp p fid slot st :=
 let s:=cm_source_slot_at sp slot (cm_function_locals (cm_source_function_at sp fid p)) in
 let base:=cm_local_base sp p fid slot (cm_state_fp st) in let size:=cm_slot_size (cm_program_structs p) s in
 CMState (cm_state_mem st) (cm_clear_init (cm_state_init st) base size) (cm_state_tags st)
 (cm_clear_tagged (cm_state_tagged st) base size)
 (fun scope index=>if (scope =? 1) && (index =? slot) then CMPtrV (cm_state_nextgen st) 0 size 0 (cm_slot_ty s) else cm_state_env st scope index)
 (cm_state_input st) (cm_state_output st) (cm_state_fp st) (cm_state_nextgen st+1)
 (CMRegion (cm_state_nextgen st) base 0 size true true :: cm_state_regions st).
Definition cm_region_dec : forall x y:cm_region, {x=y}+{x<>y}.
Proof. decide equality; [apply Bool.bool_dec|apply Bool.bool_dec|apply Z.eq_dec|apply Z.eq_dec|apply Z.eq_dec|apply Z.eq_dec]. Defined.
Definition cm_regions_eqb xs ys := if list_eq_dec cm_region_dec xs ys then true else false.
Lemma cm_regions_eqb_spec xs ys : cm_regions_eqb xs ys=true <-> xs=ys.
Proof. unfold cm_regions_eqb; destruct (list_eq_dec cm_region_dec xs ys); intuition congruence. Qed.
Definition cm_retire_region r := match r with CMRegion g b l h w live=>CMRegion g b l h w false end.
Fixpoint cm_restore_regions current old := match current with []=>old | region::rest=>
 if cm_regions_eqb current old then old else cm_retire_region region :: cm_restore_regions rest old end.
Fixpoint cm_restore_init all current old init := match current with []=>init | region::rest=>
 if cm_regions_eqb current old then init else cm_restore_init all rest old
 (if cm_region_live region then cm_clear_init init (cm_region_base all (cm_region_gen region)+cm_region_lo region) (cm_region_hi region-cm_region_lo region) else init) end.
Fixpoint cm_restore_tagged all current old tagged := match current with []=>tagged | region::rest=>
 if cm_regions_eqb current old then tagged else cm_restore_tagged all rest old
 (if cm_region_live region then cm_clear_tagged tagged (cm_region_base all (cm_region_gen region)+cm_region_lo region) (cm_region_hi region-cm_region_lo region) else tagged) end.
Definition cm_restore_call st oldenv oldfp oldregions := CMState (cm_state_mem st)
 (cm_restore_init (cm_state_regions st) (cm_state_regions st) oldregions (cm_state_init st)) (cm_state_tags st)
 (cm_restore_tagged (cm_state_regions st) (cm_state_regions st) oldregions (cm_state_tagged st)) oldenv
 (cm_state_input st) (cm_state_output st) oldfp (cm_state_nextgen st) (cm_restore_regions (cm_state_regions st) oldregions).
Definition cm_restore_scope st oldenv oldregions := cm_restore_call st oldenv (cm_state_fp st) oldregions.
Definition cm_is_call_frame f := match f with CMCallK _ _ _ _ _=>true | _=>false end.
Fixpoint cm_call_depth ks : Z := match ks with []=>0 | f::rest=>(if cm_is_call_frame f then 1 else 0)+cm_call_depth rest end.
Definition cm_call_ok sp p fid (values:list cm_value) st :=
 let f:=cm_source_function_at sp fid p in let size:=cm_frame_size (cm_program_structs p) f in
 (0 <=? fid) && (fid <? Zlength (cm_program_functions p)) && (Zlength values =? Zlength (cm_function_params f)) &&
 (8 <=? size) && (cm_static_size p <=? cm_state_fp st-size) && (cm_state_fp st <=? 1048576) && tower_word_validb (cm_state_fp st-size).
Definition cm_begin_call sp p caller fid values st ret ks :=
 if cm_call_ok sp p fid values st && (cm_call_depth ks <? 65536) then
 CMSTask p fid (cm_function_body (cm_source_function_at sp fid p)) (cm_enter_call sp p fid values st)
 (CMCallK caller (cm_state_env st) (cm_state_fp st) (cm_state_regions st) ret :: ks)
 else CMCTask p caller (CMError 1) st ks.

Lemma cm_store_params_observation sp p fid values index st :
 cm_state_input (cm_store_params sp p fid values index st)=cm_state_input st /\
 cm_state_output (cm_store_params sp p fid values index st)=cm_state_output st.
Proof. revert index st; induction values; intros; cbn; [auto|rewrite (proj1 (IHvalues _ _)), (proj2 (IHvalues _ _)); apply cm_store_preserves_observation]. Qed.
Lemma cm_enter_call_observation sp p fid values st :
 cm_state_input (cm_enter_call sp p fid values st)=cm_state_input st /\
 cm_state_output (cm_enter_call sp p fid values st)=cm_state_output st.
Proof. unfold cm_enter_call. pose proof (cm_store_params_observation sp p fid values 0 (cm_call_base_state sp p fid st)) as H. exact H. Qed.
Lemma cm_restore_call_observation st env fp regions :
 cm_state_input (cm_restore_call st env fp regions)=cm_state_input st /\
 cm_state_output (cm_restore_call st env fp regions)=cm_state_output st /\
 cm_state_mem (cm_restore_call st env fp regions)=cm_state_mem st.
Proof. repeat split; reflexivity. Qed.
Lemma cm_restore_regions_refl old : cm_restore_regions old old=old.
Proof. destruct old; cbn; auto. unfold cm_regions_eqb; destruct (list_eq_dec cm_region_dec (c::old) (c::old)); congruence. Qed.
Lemma cm_restore_init_refl all old init : cm_restore_init all old old init=init.
Proof. destruct old; cbn; auto. unfold cm_regions_eqb; destruct (list_eq_dec cm_region_dec (c::old) (c::old)); congruence. Qed.
Lemma cm_restore_tagged_refl all old tagged : cm_restore_tagged all old old tagged=tagged.
Proof. destruct old; cbn; auto. unfold cm_regions_eqb; destruct (list_eq_dec cm_region_dec (c::old) (c::old)); congruence. Qed.
Lemma cm_restore_scope_refl st : cm_restore_scope st (cm_state_env st) (cm_state_regions st)=st.
Proof. unfold cm_restore_scope,cm_restore_call; rewrite cm_restore_init_refl,cm_restore_tagged_refl,cm_restore_regions_refl; destruct st; reflexivity. Qed.
Lemma cm_call_depth_nonnegative ks : 0<=cm_call_depth ks.
Proof. induction ks; cbn; [lia|destruct (cm_is_call_frame a); lia]. Qed.
