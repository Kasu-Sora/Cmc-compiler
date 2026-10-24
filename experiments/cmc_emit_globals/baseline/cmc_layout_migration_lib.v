(* Faithful domain/representation migration from cmc_lang.c and cmc_rep.c.
   Recursion below is structural recursion on source syntax and descriptor lists,
   not an interpreter of the runtime C implementation. *)
From Coq Require Import ZArith List Bool String Lia.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import SimpleC.EE.QCP_demos_human.cmc_copy_bytes_migration_lib.
Import ListNotations naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac.

Inductive cm_type := CMIntTy | CMCharTy | CMStructTy (sid:Z) | CMPtrTy (ty:cm_type).
Inductive cm_expr :=
| CMConstE (n:Z) (ty:cm_type) | CMStringE (sid:Z) (ty:cm_type)
| CMVarE (scope slot:Z) (ty:cm_type)
| CMAssignE (dst src:cm_expr) (ty:cm_type)
| CMBinaryE (op:Z) (left right:cm_expr) (ty:cm_type)
| CMUnaryE (op:Z) (arg:cm_expr) (ty:cm_type)
| CMIndexE (base index:cm_expr) (ty:cm_type)
| CMMemberE (base:cm_expr) (mid:Z) (ty:cm_type)
| CMCallE (fid:Z) (args:list cm_expr) (ty:cm_type)
| CMSizeofE (asked ty:cm_type) | CMGetcE (ty:cm_type)
| CMPutcE (arg:cm_expr) (ty:cm_type) | CMPutiE (arg:cm_expr) (ty:cm_type)
| CMExitE (arg:cm_expr) (ty:cm_type).
Inductive cm_stmt := CMSkipS | CMExprS (e:cm_expr) | CMDeclS (slot:Z)
| CMInitS (slot:Z) (e:cm_expr) | CMSeqS (a b:cm_stmt) | CMBlockS (a:cm_stmt)
| CMIfS (e:cm_expr) (a b:cm_stmt) | CMWhileS (e:cm_expr) (a:cm_stmt)
| CMBreakS | CMContinueS | CMReturnS (e:cm_expr).
Record cm_slot_d := CMSlotD {cm_slot_ty:cm_type; cm_slot_count:Z}.
Record cm_struct_d := CMStructD {cm_struct_members:list cm_slot_d}.
Record cm_global_d := CMGlobalD {cm_global_ty:cm_type; cm_global_count:Z;
 cm_global_has_init:bool; cm_global_init:Z}.
Record cm_string_d := CMStringD {cm_string_bytes:list Z}.
Record cm_function_d := CMFunctionD {cm_function_ret:cm_type;
 cm_function_params:list cm_slot_d; cm_function_locals:list cm_slot_d; cm_function_body:cm_stmt}.
Record cm_program := CMProgram {cm_program_structs:list cm_struct_d;
 cm_program_globals:list cm_global_d; cm_program_strings:list cm_string_d;
 cm_program_functions:list cm_function_d; cm_program_main:Z}.
Record cm_tpair := CMTPair {cm_tleft:Z; cm_tright:Z}.
Record cm_apair := CMAPair {cm_acount:Z; cm_adepth:Z}.
Definition cm_imax := Z.max.
Fixpoint cm_type_depth (t:cm_type):Z := match t with CMPtrTy u => 1+cm_type_depth u | _ => 0 end.
Fixpoint cm_type_base_code (t:cm_type):Z := match t with
 CMIntTy => 0 | CMCharTy => 1 | CMStructTy i => i+2 | CMPtrTy u => cm_type_base_code u end.
Definition cm_type_encode t := 1024*cm_type_depth t+cm_type_base_code t.
Fixpoint cm_type_code_wf (t:cm_type):Prop := match t with
 CMStructTy i => 0<=i<1022 | CMPtrTy u => cm_type_code_wf u | _ => True end.
Definition cm_is_pointer t := match t with CMPtrTy _ => True | _ => False end.
Definition cm_is_struct t := match t with CMStructTy _ => True | _ => False end.
Definition cm_pointee t := match t with CMPtrTy u => u | _ => t end.
Fixpoint cm_struct_id t := match t with CMStructTy i => i | CMPtrTy u => cm_struct_id u | _ => -1 end.
Definition cm_rep_bool (b:bool):Z := if b then 1 else 0.
Definition cm_rep_nonzero (n:Z):Z := if Z.eqb n 0 then 0 else 1.
Definition cm_rep_is_pointer_code (n:Z):Z := if Z.leb 1024 n then 1 else 0.
Definition cm_rep_leaf_size (n:Z):Z := if Z.leb 1024 n then 8 else if Z.eqb n 0 then 8 else if Z.eqb n 1 then 1 else 0.
Definition cm_rep_code_slot_size c n := if Z.eqb n 0 then cm_rep_leaf_size c else n*cm_rep_leaf_size c.
Definition cm_rep_member_size m := cm_rep_code_slot_size (cm_type_encode (cm_slot_ty m)) (cm_slot_count m).
Definition cm_rep_global_size g := cm_rep_code_slot_size (cm_type_encode (cm_global_ty g)) (cm_global_count g).
Definition cm_rep_string_length s := Zlength (cm_string_bytes s).
Definition cm_rep_string_size s := cm_rep_string_length s+1.
Fixpoint cm_rep_members_size (l:list cm_slot_d):Z := match l with []=>0 | h::t=>cm_rep_member_size h+cm_rep_members_size t end.
Fixpoint cm_rep_globals_size (l:list cm_global_d):Z := match l with []=>0 | h::t=>cm_rep_global_size h+cm_rep_globals_size t end.
Fixpoint cm_rep_strings_size (l:list cm_string_d):Z := match l with []=>0 | h::t=>cm_rep_string_size h+cm_rep_strings_size t end.
Fixpoint cm_rep_members_safe (l:list cm_slot_d):Prop := match l with []=>True | h::t =>
 0<=cm_rep_member_size h /\ 0<=cm_rep_members_size t /\ cm_rep_members_size l<=1048576 /\ cm_rep_members_safe t end.
Fixpoint cm_rep_globals_safe (l:list cm_global_d):Prop := match l with []=>True | h::t =>
 0<=cm_rep_global_size h /\ 0<=cm_rep_globals_size t /\ cm_rep_globals_size l<=1048560 /\ cm_rep_globals_safe t end.
Fixpoint cm_rep_strings_safe (l:list cm_string_d):Prop := match l with []=>True | h::t =>
 0<=cm_rep_string_size h /\ 0<=cm_rep_strings_size t /\ cm_rep_strings_size l<=1048560 /\ cm_rep_strings_safe t end.
Fixpoint cm_rep_structs_safe (l:list cm_struct_d):Prop := match l with []=>True | h::t =>
 cm_rep_members_safe (cm_struct_members h) /\ cm_rep_structs_safe t end.
Fixpoint cm_rep_member_prefix (l:list cm_slot_d) (i:Z):Z := match l with []=>0 | h::t =>
 if Z.eqb i 0 then 0 else cm_rep_member_size h+cm_rep_member_prefix t (i-1) end.
Fixpoint cm_rep_globals_prefix (l:list cm_global_d) (i:Z):Z := match l with []=>0 | h::t =>
 if Z.eqb i 0 then 0 else cm_rep_global_size h+cm_rep_globals_prefix t (i-1) end.
Fixpoint cm_rep_strings_prefix (l:list cm_string_d) (i:Z):Z := match l with []=>0 | h::t =>
 if Z.eqb i 0 then 0 else cm_rep_string_size h+cm_rep_strings_prefix t (i-1) end.
Fixpoint cm_rep_slot_type (l:list cm_slot_d) (i:Z):Z := match l with []=>0 | h::t =>
 if Z.eqb i 0 then cm_type_encode (cm_slot_ty h) else cm_rep_slot_type t (i-1) end.
Fixpoint cm_rep_member_array (l:list cm_slot_d) (i:Z):Z := match l with []=>0 | h::t =>
 if Z.eqb i 0 then cm_rep_nonzero (cm_slot_count h) else cm_rep_member_array t (i-1) end.
Fixpoint cm_rep_global_array (l:list cm_global_d) (i:Z):Z := match l with []=>0 | h::t =>
 if Z.eqb i 0 then cm_rep_nonzero (cm_global_count h) else cm_rep_global_array t (i-1) end.
Fixpoint cm_rep_struct_size (l:list cm_struct_d) (i:Z):Z := match l with []=>0 | h::t =>
 if Z.eqb i 0 then cm_rep_members_size (cm_struct_members h) else cm_rep_struct_size t (i-1) end.
Fixpoint cm_rep_struct_member_prefix (l:list cm_struct_d) (i j:Z):Z := match l with []=>0 | h::t =>
 if Z.eqb i 0 then cm_rep_member_prefix (cm_struct_members h) j else cm_rep_struct_member_prefix t (i-1) j end.
Fixpoint cm_rep_struct_member_array (l:list cm_struct_d) (i j:Z):Z := match l with []=>0 | h::t =>
 if Z.eqb i 0 then cm_rep_member_array (cm_struct_members h) j else cm_rep_struct_member_array t (i-1) j end.
Definition cm_rep_type_size l c := if Z.leb 1024 c then 8 else if Z.eqb c 0 then 8 else if Z.eqb c 1 then 1 else cm_rep_struct_size l (c-2).
Definition cm_rep_global_address l i := 16+cm_rep_globals_prefix l i.
Definition cm_rep_string_address g s i := 16+cm_rep_globals_size g+cm_rep_strings_prefix s i.
Definition cm_normalize_code_value t : Z := if Z.eqb t 1 then 6 else 0.
Definition cm_default_slot := CMSlotD CMIntTy 0.
Definition cm_default_struct := CMStructD [].
Definition cm_default_global := CMGlobalD CMIntTy 0 false 0.
(* HOL INTH_DEF uses choice-defined num_of_int; NTH_DEF constrains only
   cons lists. These two explicit logical policy components preserve every
   possible source choice, including negative fid and out-of-range fid.
   The contracts quantify over the policy: it is not an assumed oracle or a
   precondition restricting inputs. The original HOL interpretation is one
   instance of this stronger, policy-parametric theorem. *)
Record cm_lookup_policy := CMLookupPolicy {
 cm_negative_nat : nat;
 cm_function_nil : nat -> cm_function_d
}.
Definition cm_num_of_int (policy:cm_lookup_policy) (i:Z):nat :=
 if Z.leb 0 i then Z.to_nat i else cm_negative_nat policy.
Fixpoint cm_function_nth (policy:cm_lookup_policy) (n:nat)
 (l:list cm_function_d):cm_function_d := match l with
 | [] => cm_function_nil policy n
 | h::t => match n with O=>h | S k=>cm_function_nth policy k t end end.
Definition cm_function_at policy i l := cm_function_nth policy (cm_num_of_int policy i) l.
Lemma cm_function_nth_zero policy h t : cm_function_nth policy O (h::t)=h.
Proof. reflexivity. Qed.
Lemma cm_function_nth_succ policy n h t :
 cm_function_nth policy (S n) (h::t)=cm_function_nth policy n t.
Proof. reflexivity. Qed.
Lemma cm_num_of_int_nonnegative policy i :
 0<=i -> cm_num_of_int policy i=Z.to_nat i.
Proof. intros Hnonneg; unfold cm_num_of_int; destruct (Z.leb_spec 0 i); [reflexivity|lia]. Qed.
Lemma cm_function_nth_some policy n l f :
 nth_error l n=Some f -> cm_function_nth policy n l=f.
Proof.
 revert n; induction l as [|h t IH]; intros [|n] H; simpl in *;
 try discriminate; try congruence; apply IH; exact H.
Qed.
Lemma cm_function_at_valid policy i l f :
 0<=i -> nth_error l (Z.to_nat i)=Some f -> cm_function_at policy i l=f.
Proof. intros H Hnth; unfold cm_function_at; rewrite cm_num_of_int_nonnegative by exact H; apply cm_function_nth_some; exact Hnth. Qed.
Definition cm_struct_at i l := nth (Z.to_nat i) l cm_default_struct.
Definition cm_slot_at i l := nth (Z.to_nat i) l cm_default_slot.
Definition cm_global_at i l := nth (Z.to_nat i) l cm_default_global.
Definition cm_binding_valid p f scope slot : Prop :=
 (scope=0 /\ 0<=slot<Zlength (cm_program_globals p)) \/
 (scope=1 /\ 0<=slot<Zlength (cm_function_locals f)) \/
 (scope=2 /\ 0<=slot<Zlength (cm_function_params f)).
Definition cm_member_valid p base mid : Prop :=
 cm_is_pointer base /\ cm_is_struct (cm_pointee base) /\
 0<=cm_struct_id (cm_pointee base)<Zlength (cm_program_structs p) /\
 0<=mid<Zlength (cm_struct_members (cm_struct_at (cm_struct_id (cm_pointee base)) (cm_program_structs p))).
Definition cm_binding_array_code policy p fid scope slot : Z :=
 if Z.eqb scope 0 then cm_rep_nonzero (cm_global_count (cm_global_at slot (cm_program_globals p)))
 else if Z.eqb scope 1 then cm_rep_nonzero (cm_slot_count (cm_slot_at slot (cm_function_locals (cm_function_at policy fid (cm_program_functions p))))) else 0.
Definition cm_member_array_code p base mid : Z :=
 cm_rep_nonzero (cm_slot_count (cm_slot_at mid (cm_struct_members (cm_struct_at (cm_struct_id (cm_pointee base)) (cm_program_structs p))))).

Fixpoint cm_expr_tpair (e:cm_expr) : cm_tpair :=
 match e with
 | CMAssignE a b _ => CMTPair 0 (cm_imax (cm_tleft (cm_expr_tpair a)) (1+cm_tright (cm_expr_tpair b)))
 | CMBinaryE op a b _ => CMTPair 0 (cm_imax (cm_tright (cm_expr_tpair a))
    (if (Z.eqb op 0 || Z.eqb op 1)%bool then cm_tright (cm_expr_tpair b) else 1+cm_tright (cm_expr_tpair b)))
 | CMUnaryE op a _ => if Z.eqb op 2 then CMTPair (cm_tright (cm_expr_tpair a)) (cm_tright (cm_expr_tpair a))
    else CMTPair 0 (if Z.eqb op 3 then cm_tleft (cm_expr_tpair a) else cm_tright (cm_expr_tpair a))
 | CMIndexE a b _ => let n := cm_imax (cm_tright (cm_expr_tpair a)) (1+cm_tright (cm_expr_tpair b)) in CMTPair n n
 | CMMemberE a _ _ => CMTPair (cm_tright (cm_expr_tpair a)) (cm_tright (cm_expr_tpair a))
 | CMCallE _ args _ => let fix ap (l:list cm_expr):cm_apair := match l with
       []=>CMAPair 0 0 | a::t=>let r:=ap t in CMAPair (1+cm_acount r) (cm_imax (cm_tright (cm_expr_tpair a)) (cm_adepth r)) end
    in let r:=ap args in CMTPair 0 (cm_acount r+cm_adepth r)
 | CMPutcE a _ | CMPutiE a _ | CMExitE a _ => CMTPair 0 (cm_tright (cm_expr_tpair a))
 | _ => CMTPair 0 0 end.
Fixpoint cm_args_apair (l:list cm_expr):cm_apair := match l with []=>CMAPair 0 0
 | a::t=>let r:=cm_args_apair t in CMAPair (1+cm_acount r) (cm_imax (cm_tright (cm_expr_tpair a)) (cm_adepth r)) end.
Definition cm_ltemps e := cm_tleft (cm_expr_tpair e).
Definition cm_rtemps e := cm_tright (cm_expr_tpair e).
Definition cm_args_temps l := cm_acount (cm_args_apair l)+cm_adepth (cm_args_apair l).
Fixpoint cm_stemps (s:cm_stmt):Z := match s with
 | CMExprS e | CMInitS _ e | CMReturnS e => cm_rtemps e
 | CMSeqS a b => cm_imax (cm_stemps a) (cm_stemps b)
 | CMBlockS a => cm_stemps a
 | CMIfS e a b => cm_imax (cm_rtemps e) (cm_imax (cm_stemps a) (cm_stemps b))
 | CMWhileS e a => cm_imax (cm_rtemps e) (cm_stemps a) | _=>0 end.
Definition cm_rep_args_length (l:list cm_expr) := Zlength l.
Fixpoint cm_rep_args_safe (l:list cm_expr):Prop := match l with []=>True
 | _::t => 0<=cm_rep_args_length t<2147483647 /\ cm_rep_args_safe t end.
Definition cm_rep_tpair_safe p : Prop := 0<=cm_tleft p<=2147483647 /\ 0<=cm_tright p<=2147483647.
Definition cm_rep_apair_safe p : Prop := 0<=cm_acount p<=2147483647 /\ 0<=cm_adepth p<=2147483647 /\ cm_acount p+cm_adepth p<=2147483647.
Fixpoint cm_rep_expr_temps_safe (e:cm_expr):Prop :=
 cm_rep_tpair_safe (cm_expr_tpair e) /\ match e with
 | CMAssignE a b _ | CMBinaryE _ a b _ | CMIndexE a b _ => cm_rtemps b<2147483647 /\ cm_rep_expr_temps_safe a /\ cm_rep_expr_temps_safe b
 | CMUnaryE _ a _ | CMMemberE a _ _ | CMPutcE a _ | CMPutiE a _ | CMExitE a _ => cm_rep_expr_temps_safe a
 | CMCallE _ args _ => (fix safe (l:list cm_expr):Prop := cm_rep_apair_safe (cm_args_apair l) /\ match l with
    []=>True | a::t=>cm_acount (cm_args_apair t)<2147483647 /\ cm_rep_expr_temps_safe a /\ safe t end) args
 | _=>True end.
Fixpoint cm_rep_args_temps_safe (l:list cm_expr):Prop := cm_rep_apair_safe (cm_args_apair l) /\ match l with
 []=>True | a::t=>cm_acount (cm_args_apair t)<2147483647 /\ cm_rep_expr_temps_safe a /\ cm_rep_args_temps_safe t end.
Fixpoint cm_rep_stmt_children_safe (s:cm_stmt):Prop := match s with
 | CMExprS e | CMInitS _ e | CMReturnS e => cm_rep_expr_temps_safe e
 | CMSeqS a b => (0<=cm_stemps a<=2147483647 /\ cm_rep_stmt_children_safe a) /\ (0<=cm_stemps b<=2147483647 /\ cm_rep_stmt_children_safe b)
 | CMBlockS a => 0<=cm_stemps a<=2147483647 /\ cm_rep_stmt_children_safe a
 | CMIfS e a b => cm_rep_expr_temps_safe e /\ (0<=cm_stemps a<=2147483647 /\ cm_rep_stmt_children_safe a) /\ (0<=cm_stemps b<=2147483647 /\ cm_rep_stmt_children_safe b)
 | CMWhileS e a => cm_rep_expr_temps_safe e /\ (0<=cm_stemps a<=2147483647 /\ cm_rep_stmt_children_safe a)
 | _=>True end.
Definition cm_rep_stmt_temps_safe s := 0<=cm_stemps s<=2147483647 /\ cm_rep_stmt_children_safe s.

Definition cm_expr_type e := match e with CMConstE _ t | CMStringE _ t | CMVarE _ _ t
 | CMAssignE _ _ t | CMBinaryE _ _ _ t | CMUnaryE _ _ t | CMIndexE _ _ t | CMMemberE _ _ t
 | CMCallE _ _ t | CMSizeofE _ t | CMGetcE t | CMPutcE _ t | CMPutiE _ t | CMExitE _ t => t end.
Definition cm_rep_expr_kind e : Z := match e with CMConstE _ _=>0 | CMStringE _ _=>1 | CMVarE _ _ _=>2
 | CMAssignE _ _ _=>3 | CMBinaryE _ _ _ _=>4 | CMUnaryE _ _ _=>5 | CMIndexE _ _ _=>6 | CMMemberE _ _ _=>7
 | CMCallE _ _ _=>8 | CMSizeofE _ _=>9 | CMGetcE _=>10 | CMPutcE _ _=>11 | CMPutiE _ _=>12 | CMExitE _ _=>13 end.
Definition cm_rep_expr_op e : Z := match e with CMVarE n _ _ | CMBinaryE n _ _ _ | CMUnaryE n _ _ => n | _=>0 end.
Definition cm_rep_expr_value e : Z := match e with CMConstE n _ | CMStringE n _ | CMVarE _ n _ | CMMemberE _ n _ | CMCallE n _ _=>n
 | CMSizeofE t _=>cm_type_encode t | _=>0 end.
Definition cm_rep_stmt_kind s : Z := match s with CMSkipS=>0 | CMExprS _=>1 | CMDeclS _=>2 | CMInitS _ _=>3
 | CMSeqS _ _=>4 | CMBlockS _=>5 | CMIfS _ _ _=>6 | CMWhileS _ _=>7 | CMBreakS=>8 | CMContinueS=>9 | CMReturnS _=>10 end.
Definition cm_rep_stmt_slot s : Z := match s with CMDeclS n | CMInitS n _=>n | _=>0 end.

(* Each node owns exactly the fields in the C* representation. No structure-wide
   permission or unrelated program/function fields are added. *)
Fixpoint cm_slot_list_rep (p:Z) (l:list cm_slot_d):Assertion := match l with
 | [] => “p=0” && emp
 | h::t => “p<>0” && EX n:Z,
  &(p # "cm_slot" ->ₛ "ty") # Int |-> cm_type_encode (cm_slot_ty h) **
  &(p # "cm_slot" ->ₛ "count") # Int |-> cm_slot_count h **
  &(p # "cm_slot" ->ₛ "next") # Ptr |-> n ** cm_slot_list_rep n t end.
Fixpoint cm_member_list_rep (p:Z) (l:list cm_slot_d):Assertion := match l with
 | [] => “p=0” && emp
 | h::t => “p<>0” && EX n:Z,
  &(p # "cm_member" ->ₛ "ty") # Int |-> cm_type_encode (cm_slot_ty h) **
  &(p # "cm_member" ->ₛ "count") # Int |-> cm_slot_count h **
  &(p # "cm_member" ->ₛ "next") # Ptr |-> n ** cm_member_list_rep n t end.
Fixpoint cm_struct_list_rep (p:Z) (l:list cm_struct_d):Assertion := match l with
 | [] => “p=0” && emp
 | h::t => “p<>0” && EX m n:Z,
  &(p # "cm_struct" ->ₛ "members") # Ptr |-> m **
  &(p # "cm_struct" ->ₛ "next") # Ptr |-> n **
  cm_member_list_rep m (cm_struct_members h) ** cm_struct_list_rep n t end.
Fixpoint cm_global_list_rep (p:Z) (l:list cm_global_d):Assertion := match l with
 | [] => “p=0” && emp
 | h::t => “p<>0” && EX n:Z,
  &(p # "cm_global" ->ₛ "ty") # Int |-> cm_type_encode (cm_global_ty h) **
  &(p # "cm_global" ->ₛ "count") # Int |-> cm_global_count h **
  &(p # "cm_global" ->ₛ "has_init") # Int |-> cm_rep_bool (cm_global_has_init h) **
  &(p # "cm_global" ->ₛ "init") # Int64 |-> cm_global_init h **
  &(p # "cm_global" ->ₛ "next") # Ptr |-> n ** cm_global_list_rep n t end.
Definition cm_uint8_buffer (p:Z) (bytes:list Z):Assertion := match bytes with
 | []=>emp | _=> “cmc_uint8_buffer_nonnull p bytes” && UCharArray.full p (Zlength bytes) bytes end.
Fixpoint cm_string_list_rep (p:Z) (l:list cm_string_d):Assertion := match l with
 | [] => “p=0” && emp
 | h::t => “p<>0” && EX b n:Z,
  &(p # "cm_string" ->ₛ "bytes") # Ptr |-> b **
  &(p # "cm_string" ->ₛ "length") # Int |-> cm_rep_string_length h **
  &(p # "cm_string" ->ₛ "next") # Ptr |-> n **
  cm_uint8_buffer b (cm_string_bytes h) ** cm_string_list_rep n t end.
Definition cm_expr_node (p:Z) (e:cm_expr) (payload:Z->Z->Z->Assertion):Assertion :=
 “p<>0” && EX a b args:Z,
 &(p # "cm_expr" ->ₛ "kind") # Int |-> cm_rep_expr_kind e **
 &(p # "cm_expr" ->ₛ "op") # Int |-> cm_rep_expr_op e **
 &(p # "cm_expr" ->ₛ "ty") # Int |-> cm_type_encode (cm_expr_type e) **
 &(p # "cm_expr" ->ₛ "value") # Int64 |-> cm_rep_expr_value e **
 &(p # "cm_expr" ->ₛ "a") # Ptr |-> a **
 &(p # "cm_expr" ->ₛ "b") # Ptr |-> b **
 &(p # "cm_expr" ->ₛ "args") # Ptr |-> args ** payload a b args.
Fixpoint cm_expr_rep (p:Z) (e:cm_expr) {struct e}:Assertion :=
 cm_expr_node p e (fun a b args => match e with
 | CMAssignE x y _ | CMBinaryE _ x y _ | CMIndexE x y _ =>
   “args=0” && cm_expr_rep a x ** cm_expr_rep b y
 | CMUnaryE _ x _ | CMMemberE x _ _ | CMPutcE x _ | CMPutiE x _ | CMExitE x _ =>
   “a<>0 /\ b=0 /\ args=0” && cm_expr_rep a x
 | CMCallE _ l _ => “a=0 /\ b=0” &&
   (fix arg_rep (p:Z) (l:list cm_expr) {struct l}:Assertion := match l with
    | []=> “p=0” && emp
    | h::t=> “p<>0” && EX q n:Z,
      &(p # "cm_arg" ->ₛ "expr") # Ptr |-> q ** &(p # "cm_arg" ->ₛ "next") # Ptr |-> n **
      cm_expr_rep q h ** arg_rep n t end) args l
 | _ => “a=0 /\ b=0 /\ args=0” && emp end).
Fixpoint cm_arg_list_rep (p:Z) (l:list cm_expr):Assertion := match l with
 | []=> “p=0” && emp
 | h::t=> “p<>0” && EX q n:Z,
   &(p # "cm_arg" ->ₛ "expr") # Ptr |-> q ** &(p # "cm_arg" ->ₛ "next") # Ptr |-> n **
   cm_expr_rep q h ** cm_arg_list_rep n t end.
Definition cm_expr_payload (e:cm_expr) (a b args:Z):Assertion := match e with
 | CMAssignE x y _ | CMBinaryE _ x y _ | CMIndexE x y _ => “args=0” && cm_expr_rep a x ** cm_expr_rep b y
 | CMUnaryE _ x _ | CMMemberE x _ _ | CMPutcE x _ | CMPutiE x _ | CMExitE x _ =>
   “a<>0 /\ b=0 /\ args=0” && cm_expr_rep a x
 | CMCallE _ l _ => “a=0 /\ b=0” && cm_arg_list_rep args l
 | _ => “a=0 /\ b=0 /\ args=0” && emp end.
Definition cm_stmt_node (p:Z) (s:cm_stmt) (payload:Z->Z->Z->Assertion):Assertion :=
 “p<>0” && EX e a b:Z,
 &(p # "cm_stmt" ->ₛ "kind") # Int |-> cm_rep_stmt_kind s **
 &(p # "cm_stmt" ->ₛ "slot") # Int |-> cm_rep_stmt_slot s **
 &(p # "cm_stmt" ->ₛ "expr") # Ptr |-> e **
 &(p # "cm_stmt" ->ₛ "a") # Ptr |-> a **
 &(p # "cm_stmt" ->ₛ "b") # Ptr |-> b ** payload e a b.
Fixpoint cm_stmt_rep (p:Z) (s:cm_stmt) {struct s}:Assertion :=
 cm_stmt_node p s (fun e a b=>match s with
 | CMExprS x | CMInitS _ x | CMReturnS x => “e<>0 /\ a=0 /\ b=0” && cm_expr_rep e x
 | CMSeqS x y => “e=0” && cm_stmt_rep a x ** cm_stmt_rep b y
 | CMBlockS x => “e=0 /\ a<>0 /\ b=0” && cm_stmt_rep a x
 | CMIfS x y z => cm_expr_rep e x ** cm_stmt_rep a y ** cm_stmt_rep b z
 | CMWhileS x y => “e<>0 /\ a<>0 /\ b=0” && cm_expr_rep e x ** cm_stmt_rep a y
 | _ => “e=0 /\ a=0 /\ b=0” && emp end).
Definition cm_stmt_payload (s:cm_stmt) (e a b:Z):Assertion := match s with
 | CMExprS x | CMInitS _ x | CMReturnS x => “e<>0 /\ a=0 /\ b=0” && cm_expr_rep e x
 | CMSeqS x y => “e=0” && cm_stmt_rep a x ** cm_stmt_rep b y
 | CMBlockS x => “e=0 /\ a<>0 /\ b=0” && cm_stmt_rep a x
 | CMIfS x y z => cm_expr_rep e x ** cm_stmt_rep a y ** cm_stmt_rep b z
 | CMWhileS x y => “e<>0 /\ a<>0 /\ b=0” && cm_expr_rep e x ** cm_stmt_rep a y
 | _ => “e=0 /\ a=0 /\ b=0” && emp end.

(* Transparent bridges between nested structural recursion and public list
   functions; these preserve the original mutual recursion equations. *)
Lemma cm_expr_rep_node p e : cm_expr_rep p e = cm_expr_node p e (cm_expr_payload e).
Proof. destruct e; reflexivity. Qed.
Lemma cm_stmt_rep_node p s : cm_stmt_rep p s = cm_stmt_node p s (cm_stmt_payload s).
Proof. destruct s; reflexivity. Qed.
Lemma cm_expr_tpair_call fid args ty :
 cm_expr_tpair (CMCallE fid args ty) = CMTPair 0 (cm_args_temps args).
Proof. reflexivity. Qed.
Lemma cm_expr_safe_call fid args ty : cm_rep_expr_temps_safe (CMCallE fid args ty) <->
 cm_rep_tpair_safe (cm_expr_tpair (CMCallE fid args ty)) /\ cm_rep_args_temps_safe args.
Proof. reflexivity. Qed.

(* Reuse the accepted copy-bytes nonnull predicate, with the original empty
   buffer ownership (emp) retained. The builtin UCharArray owns the bytes. *)
Lemma cm_uint8_buffer_source p bytes : cm_uint8_buffer p bytes --||--
 match bytes with []=>emp | _=> “p<>0” && UCharArray.full p (Zlength bytes) bytes end.
Proof.
 destruct bytes as [|b bs]; simpl; [reflexivity|].
 unfold cmc_uint8_buffer_nonnull.
 unfold coq_prop, logic_equiv, derivable1, andp.
 split; intros; intuition discriminate.
Qed.

(* NTH_DEF correspondence for any total source interpretation. The nil policy
   is instantiated with that interpretation's NTH n [] values, preserving its
   unconstrained residual-index dependence rather than choosing an inhabitant. *)
Lemma cm_function_nth_source (policy:cm_lookup_policy)
 (source_nth:nat->list cm_function_d->cm_function_d)
 (Hnil:forall n, source_nth n []=cm_function_nil policy n)
 (Hzero:forall h t, source_nth O (h::t)=h)
 (Hsucc:forall n h t, source_nth (S n) (h::t)=source_nth n t) :
 forall n l, source_nth n l=cm_function_nth policy n l.
Proof.
 intros n l; revert n; induction l as [|h t IH]; intros [|n]; simpl.
 - apply Hnil.
 - apply Hnil.
 - apply Hzero.
 - rewrite Hsucc; apply IH.
Qed.
Lemma cm_num_of_int_source (policy:cm_lookup_policy) (convert:Z->nat)
 (Hnonneg:forall i, 0<=i -> convert i=Z.to_nat i)
 (Hneg:forall i, i<0 -> convert i=cm_negative_nat policy) :
 forall i, convert i=cm_num_of_int policy i.
Proof.
 intros i; unfold cm_num_of_int; destruct (Z.leb_spec 0 i).
 - apply Hnonneg; assumption.
 - apply Hneg; lia.
Qed.

Lemma cm_rep_global_array_nth__lookup_bridge : forall l i,
 0 <= i < Zlength l -> cm_rep_global_array l i =
 cm_rep_nonzero (cm_global_count (cm_global_at i l)).
Proof.
 induction l as [|h t IH]; intros i Hi.
 - rewrite Zlength_nil in Hi. lia.
 - rewrite Zlength_cons in Hi.
   destruct (Z.eq_dec i 0) as [->|Hnz].
   + reflexivity.
   + assert (Hpos : 0 <= i-1) by lia.
     assert (Hnat : Z.to_nat i = S (Z.to_nat (i-1))).
     { rewrite <- Z2Nat.inj_succ by exact Hpos. f_equal. lia. }
     simpl cm_rep_global_array. destruct (Z.eqb_spec i 0); [contradiction|].
     unfold cm_global_at. rewrite Hnat. simpl nth.
     apply IH. lia.
Qed.
Lemma cm_rep_member_array_nth__lookup_bridge : forall l i,
 0 <= i < Zlength l -> cm_rep_member_array l i =
 cm_rep_nonzero (cm_slot_count (cm_slot_at i l)).
Proof.
 induction l as [|h t IH]; intros i Hi.
 - rewrite Zlength_nil in Hi. lia.
 - rewrite Zlength_cons in Hi.
   destruct (Z.eq_dec i 0) as [->|Hnz].
   + reflexivity.
   + assert (Hpos : 0 <= i-1) by lia.
     assert (Hnat : Z.to_nat i = S (Z.to_nat (i-1))).
     { rewrite <- Z2Nat.inj_succ by exact Hpos. f_equal. lia. }
     simpl cm_rep_member_array. destruct (Z.eqb_spec i 0); [contradiction|].
     unfold cm_slot_at. rewrite Hnat. simpl nth.
     apply IH. lia.
Qed.
Lemma cm_rep_struct_member_array_nth__lookup_bridge : forall l sid mid,
 0 <= sid < Zlength l ->
 0 <= mid < Zlength (cm_struct_members (cm_struct_at sid l)) ->
 cm_rep_struct_member_array l sid mid =
 cm_rep_nonzero (cm_slot_count (cm_slot_at mid (cm_struct_members (cm_struct_at sid l)))).
Proof.
 induction l as [|h t IH]; intros i j Hi Hj.
 - rewrite Zlength_nil in Hi. lia.
 - rewrite Zlength_cons in Hi.
   destruct (Z.eq_dec i 0) as [->|Hnz].
   + simpl cm_rep_struct_member_array. apply cm_rep_member_array_nth__lookup_bridge. exact Hj.
   + assert (Hpos : 0 <= i-1) by lia.
     assert (Hnat : Z.to_nat i = S (Z.to_nat (i-1))).
     { rewrite <- Z2Nat.inj_succ by exact Hpos. f_equal. lia. }
     simpl cm_rep_struct_member_array. destruct (Z.eqb_spec i 0); [contradiction|].
     unfold cm_struct_at in *. rewrite Hnat in *. simpl nth in *.
     apply IH; [lia|exact Hj].
Qed.
Lemma cm_expr_pair_safe__expr_safety e :
 cm_rep_expr_temps_safe e -> cm_rep_tpair_safe (cm_expr_tpair e).
Proof. destruct e; intros H; exact (proj1 H). Qed.
Lemma cm_args_pair_safe__expr_safety l :
 cm_rep_args_temps_safe l -> cm_rep_apair_safe (cm_args_apair l).
Proof. destruct l; intros H; exact (proj1 H). Qed.
