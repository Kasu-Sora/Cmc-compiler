(* Counts and typing from cmc_codegen.c / cmc_lang.c. Structural recursion
   describes the source AST and its mathematical code-size model. *)
From Coq Require Import ZArith List Bool String Lia.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export SimpleC.EE.QCP_demos_human.cmc_layout_migration_lib.
Import ListNotations naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac.
Local Open Scope list_scope.

Record cm_code_counts := CMCodeCounts {cm_lcount_of:Z; cm_rcount_of:Z}.
Record cm_args_count := CMArgsCount {cm_args_code_count_of:Z; cm_args_arity_of:Z}.
Definition cm_i32_code_count (n:Z) := 0<=n<=2147483647.
Definition cm_char_normalize_count t : Z := match t with CMCharTy=>6 | _=>0 end.
Definition cm_binding_address_count n : Z := if Z.eqb n 0 then 1 else 4.
Definition cm_pointerb t := match t with CMPtrTy _=>true | _=>false end.
Definition cm_binary_tail_count (p:cm_program) op left right : Z :=
 10 + if (Z.eqb op 8 && cm_pointerb (cm_expr_type right))%bool then 4
 else 1 + if (Z.eqb op 8 && cm_pointerb (cm_expr_type left))%bool then 3
 else if (Z.eqb op 9 && cm_pointerb (cm_expr_type left) && cm_pointerb (cm_expr_type right))%bool then 3
 else if (Z.eqb op 9 && cm_pointerb (cm_expr_type left))%bool then 3 else 1.
Fixpoint cm_expr_code_counts policy p fid e : cm_code_counts :=
 match e with
 | CMConstE _ _ | CMStringE _ _ | CMSizeofE _ _ | CMGetcE _ => CMCodeCounts 0 1
 | CMVarE scope slot _ => CMCodeCounts (cm_binding_address_count scope)
   (cm_binding_address_count scope + if Z.eqb (cm_binding_array_code policy p fid scope slot) 0 then 1 else 0)
 | CMAssignE a b ty => CMCodeCounts 0 (cm_lcount_of (cm_expr_code_counts policy p fid a)+5+
   cm_rcount_of (cm_expr_code_counts policy p fid b)+cm_char_normalize_count ty+12)
 | CMBinaryE op a b _ => CMCodeCounts 0 (cm_rcount_of (cm_expr_code_counts policy p fid a)+
   cm_rcount_of (cm_expr_code_counts policy p fid b)+
   if (Z.eqb op 0 || Z.eqb op 1)%bool then 5 else cm_binary_tail_count p op a b)
 | CMUnaryE op a _ => let c:=cm_expr_code_counts policy p fid a in
   if Z.eqb op 2 then CMCodeCounts (cm_rcount_of c) (cm_rcount_of c+1)
   else if Z.eqb op 3 then CMCodeCounts 0 (cm_lcount_of c) else CMCodeCounts 0 (cm_rcount_of c+2)
 | CMIndexE a b _ => let n:=cm_rcount_of (cm_expr_code_counts policy p fid a)+cm_rcount_of (cm_expr_code_counts policy p fid b) in CMCodeCounts (n+13) (n+14)
 | CMMemberE a mid _ => let n:=cm_rcount_of (cm_expr_code_counts policy p fid a)+2 in
   CMCodeCounts n (n+if Z.eqb (cm_member_array_code p (cm_expr_type a) mid) 0 then 1 else 0)
 | CMCallE _ args _ => let fix count (args:list cm_expr):cm_args_count := match args with
   []=>CMArgsCount 1 0 | a::t=>let c:=count t in CMArgsCount
   (cm_rcount_of (cm_expr_code_counts policy p fid a)+10+cm_args_code_count_of c) (1+cm_args_arity_of c) end
   in CMCodeCounts 0 (cm_args_code_count_of (count args))
 | CMPutcE a _ | CMPutiE a _ => CMCodeCounts 0 (cm_rcount_of (cm_expr_code_counts policy p fid a)+2)
 | CMExitE a _ => CMCodeCounts 0 (cm_rcount_of (cm_expr_code_counts policy p fid a)+7)
 end.
Fixpoint cm_args_code_counts policy p fid args : cm_args_count := match args with
 []=>CMArgsCount 1 0 | a::t=>let c:=cm_args_code_counts policy p fid t in CMArgsCount
 (cm_rcount_of (cm_expr_code_counts policy p fid a)+10+cm_args_code_count_of c) (1+cm_args_arity_of c) end.
Definition cm_lvalue_code_count policy p fid e := cm_lcount_of (cm_expr_code_counts policy p fid e).
Definition cm_rvalue_code_count policy p fid e := cm_rcount_of (cm_expr_code_counts policy p fid e).
Definition cm_code_counts_representable c := cm_i32_code_count (cm_lcount_of c) /\ cm_i32_code_count (cm_rcount_of c).
Definition cm_expr_count_node_representable policy p fid e :=
 cm_code_counts_representable (cm_expr_code_counts policy p fid e) /\ cm_type_code_wf (cm_expr_type e) /\ cm_i32_code_count (cm_type_encode (cm_expr_type e)).
Fixpoint cm_expr_counts_representable policy p fid e : Prop :=
 cm_expr_count_node_representable policy p fid e /\ match e with
 | CMStringE sid _ | CMVarE _ sid _ => cm_i32_code_count sid
 | CMAssignE a b _ | CMBinaryE _ a b _ | CMIndexE a b _ => cm_expr_counts_representable policy p fid a /\ cm_expr_counts_representable policy p fid b
 | CMMemberE a mid _ => cm_i32_code_count mid /\ cm_expr_counts_representable policy p fid a
 | CMUnaryE _ a _ | CMPutcE a _ | CMPutiE a _ | CMExitE a _ => cm_expr_counts_representable policy p fid a
 | CMCallE callee args _ => cm_i32_code_count callee /\
   (fix safe (args:list cm_expr):Prop := cm_i32_code_count (cm_args_code_count_of (cm_args_code_counts policy p fid args)) /\ match args with []=>True | a::t=>cm_expr_counts_representable policy p fid a /\ safe t end) args
 | CMSizeofE asked _ => cm_i32_code_count (cm_type_encode asked)
 | _=>True end.
Fixpoint cm_args_counts_representable policy p fid args : Prop :=
 cm_i32_code_count (cm_args_code_count_of (cm_args_code_counts policy p fid args)) /\ match args with
 []=>True | a::t=>cm_expr_counts_representable policy p fid a /\ cm_args_counts_representable policy p fid t end.
Fixpoint cm_stmt_code_count policy p fid s : Z := match s with
 | CMSkipS | CMDeclS _=>0
 | CMExprS e=>cm_rvalue_code_count policy p fid e+1
 | CMInitS slot e=>cm_rvalue_code_count policy p fid e+cm_char_normalize_count (cm_slot_ty (cm_slot_at slot (cm_function_locals (cm_function_at policy fid (cm_program_functions p)))))+5
 | CMSeqS a b=>cm_stmt_code_count policy p fid a+cm_stmt_code_count policy p fid b
 | CMBlockS a=>cm_stmt_code_count policy p fid a
 | CMIfS e a b=>cm_rvalue_code_count policy p fid e+1+cm_stmt_code_count policy p fid a+1+cm_stmt_code_count policy p fid b
 | CMWhileS e a=>cm_rvalue_code_count policy p fid e+1+cm_stmt_code_count policy p fid a+1
 | CMBreakS | CMContinueS=>1
 | CMReturnS e=>cm_rvalue_code_count policy p fid e+cm_char_normalize_count (cm_function_ret (cm_function_at policy fid (cm_program_functions p)))+6 end.
Fixpoint cm_stmt_counts_representable policy p fid s : Prop :=
 cm_i32_code_count (cm_stmt_code_count policy p fid s) /\ match s with
 | CMExprS e=>cm_expr_counts_representable policy p fid e
 | CMInitS slot e=>cm_type_code_wf (cm_slot_ty (cm_slot_at slot (cm_function_locals (cm_function_at policy fid (cm_program_functions p))))) /\ cm_expr_counts_representable policy p fid e
 | CMSeqS a b=>cm_stmt_counts_representable policy p fid a /\ cm_stmt_counts_representable policy p fid b
 | CMBlockS a=>cm_stmt_counts_representable policy p fid a
 | CMIfS e a b=>cm_expr_counts_representable policy p fid e /\ cm_stmt_counts_representable policy p fid a /\ cm_stmt_counts_representable policy p fid b
 | CMWhileS e a=>cm_expr_counts_representable policy p fid e /\ cm_stmt_counts_representable policy p fid a
 | CMReturnS e=>cm_type_code_wf (cm_function_ret (cm_function_at policy fid (cm_program_functions p))) /\ cm_expr_counts_representable policy p fid e
 | _=>True end.
Fixpoint cm_param_stores_count params : Z := match params with []=>0 | h::t=>cm_param_stores_count t+cm_char_normalize_count (cm_slot_ty h)+5 end.
Definition cm_function_prologue_count f := 14+cm_param_stores_count (cm_function_params f).
Definition cm_function_code_count policy p fid := let f:=cm_function_at policy fid (cm_program_functions p) in
 cm_function_prologue_count f+cm_stmt_code_count policy p fid (cm_function_body f)+7.
Fixpoint cm_functions_code_size policy p (functions:list cm_function_d) fid : Z := match functions with []=>0 | _::t=>cm_function_code_count policy p fid+cm_functions_code_size policy p t (fid+1) end.
Fixpoint cm_function_prefix policy p (functions:list cm_function_d) remaining : Z := match functions with []=>0 | _::t=>
 if Z.eqb remaining 0 then 0 else cm_function_code_count policy p (Zlength (cm_program_functions p)-Zlength functions)+cm_function_prefix policy p t (remaining-1) end.
Definition cm_function_pc policy p fid := 11+cm_function_prefix policy p (cm_program_functions p) fid.
Definition cm_model_code_length policy p := 11+cm_functions_code_size policy p (cm_program_functions p) 0.
Fixpoint cm_param_counts_representable params : Prop := match params with []=>True | h::t=>cm_i32_code_count (cm_param_stores_count params) /\ cm_type_code_wf (cm_slot_ty h) /\ cm_param_counts_representable t end.
Definition cm_function_counts_representable policy p fid f :=
 f=cm_function_at policy fid (cm_program_functions p) /\ cm_param_counts_representable (cm_function_params f) /\ cm_i32_code_count (cm_function_prologue_count f) /\ cm_stmt_counts_representable policy p fid (cm_function_body f) /\ cm_i32_code_count (cm_function_code_count policy p fid).
Fixpoint cm_functions_counts_representable policy p functions fid : Prop := match functions with []=>True | f::t=>
 cm_i32_code_count (cm_functions_code_size policy p functions fid) /\ cm_function_counts_representable policy p fid f /\ cm_functions_counts_representable policy p t (fid+1) end.
Fixpoint cm_function_pcs_representable policy p (functions:list cm_function_d) fid : Prop := match functions with
 []=>cm_i32_code_count (cm_function_pc policy p fid) | _::t=>cm_i32_code_count (cm_function_pc policy p fid) /\ cm_function_pcs_representable policy p t (fid+1) end.

(* Exact source typing and layout definitions, distinct from encoded runtime
   sizes on malformed type codes. Existing descriptor/AST representations reused. *)
Definition cm_leaf_size t : Z := match t with CMIntTy | CMPtrTy _=>8 | CMCharTy=>1 | CMStructTy _=>0 end.
Definition cm_struct_member_size s := let n:=cm_slot_count s in if Z.eqb n 0 then cm_leaf_size (cm_slot_ty s) else n*cm_leaf_size (cm_slot_ty s).
Fixpoint cm_struct_slots_size l : Z := match l with []=>0 | h::t=>cm_struct_member_size h+cm_struct_slots_size t end.
Definition cm_struct_size structs sid := if (Z.leb 0 sid && Z.ltb sid (Zlength structs))%bool then cm_struct_slots_size (cm_struct_members (cm_struct_at sid structs)) else 0.
Definition cm_type_size structs ty := match ty with CMIntTy | CMPtrTy _=>8 | CMCharTy=>1 | CMStructTy sid=>cm_struct_size structs sid end.
Definition cm_slot_size structs s := let n:=cm_slot_count s in if Z.eqb n 0 then cm_type_size structs (cm_slot_ty s) else n*cm_type_size structs (cm_slot_ty s).
Fixpoint cm_slots_size structs l : Z := match l with []=>0 | h::t=>cm_slot_size structs h+cm_slots_size structs t end.
Definition cm_global_size structs g := let n:=cm_global_count g in if Z.eqb n 0 then cm_type_size structs (cm_global_ty g) else n*cm_type_size structs (cm_global_ty g).
Fixpoint cm_globals_size structs l : Z := match l with []=>0 | h::t=>cm_global_size structs h+cm_globals_size structs t end.
Definition cm_strings_size := cm_rep_strings_size.
Definition cm_static_size p := 16+cm_globals_size (cm_program_structs p) (cm_program_globals p)+cm_strings_size (cm_program_strings p).
Definition cm_temp_slots f := cm_stemps (cm_function_body f).
Definition cm_frame_size structs f := 8+cm_slots_size structs (cm_function_params f)+cm_slots_size structs (cm_function_locals f)+8*cm_temp_slots f.
Fixpoint cm_type_refs (structs:list cm_struct_d) ty : Prop := match ty with CMStructTy sid=>0<=sid<Zlength structs | CMPtrTy t=>cm_type_refs structs t | _=>True end.
Definition cm_scalar_type structs t := cm_type_code_wf t /\ cm_type_refs structs t /\ ~cm_is_struct t.
Definition cm_slot_expr_type s := if Z.eqb (cm_slot_count s) 0 then cm_slot_ty s else CMPtrTy (cm_slot_ty s).
Definition cm_global_expr_type g := if Z.eqb (cm_global_count g) 0 then cm_global_ty g else CMPtrTy (cm_global_ty g).
Definition cm_integer_type t := t=CMIntTy \/ t=CMCharTy.
Definition cm_scalar_expr_type t := cm_integer_type t \/ cm_is_pointer t.
Definition cm_convertible a b := ~cm_is_struct a /\ ~cm_is_struct b /\ (a=b \/ (cm_integer_type a /\ cm_integer_type b) \/ (cm_is_pointer a /\ cm_is_pointer b /\ (a=CMPtrTy CMCharTy \/ b=CMPtrTy CMCharTy))).
Definition cm_zero_literal e := e=CMConstE 0 CMIntTy.
Definition cm_expr_convertible e t := cm_convertible (cm_expr_type e) t \/ (cm_is_pointer t /\ cm_zero_literal e).
Definition cm_lvalue e : Prop := match e with CMVarE _ _ _ | CMIndexE _ _ _ | CMMemberE _ _ _=>True | CMUnaryE op _ _=>op=2 | _=>False end.
Definition cm_binding_type p f scope slot := if Z.eqb scope 0 then cm_global_expr_type (cm_global_at slot (cm_program_globals p)) else if Z.eqb scope 1 then cm_slot_expr_type (cm_slot_at slot (cm_function_locals f)) else cm_slot_expr_type (cm_slot_at slot (cm_function_params f)).
Definition cm_member_type p base mid := cm_slot_expr_type (cm_slot_at mid (cm_struct_members (cm_struct_at (cm_struct_id (cm_pointee base)) (cm_program_structs p)))).
Definition cm_binary_types op a b result : Prop := 0<=op<=12 /\
 if (Z.eqb op 0 || Z.eqb op 1)%bool then cm_scalar_expr_type a /\ cm_scalar_expr_type b /\ result=CMIntTy
 else if (Z.leb 2 op && Z.leb op 7)%bool then result=CMIntTy /\ ((cm_integer_type a /\ cm_integer_type b) \/ (cm_is_pointer a /\ a=b))
 else if Z.eqb op 8 then (cm_integer_type a /\ cm_integer_type b /\ result=CMIntTy) \/ (cm_is_pointer a /\ cm_integer_type b /\ result=a) \/ (cm_is_pointer b /\ cm_integer_type a /\ result=b)
 else if Z.eqb op 9 then (cm_integer_type a /\ cm_integer_type b /\ result=CMIntTy) \/ (cm_is_pointer a /\ cm_integer_type b /\ result=a) \/ (a=b /\ cm_is_pointer a /\ result=CMIntTy)
 else cm_integer_type a /\ cm_integer_type b /\ result=CMIntTy.
Definition cm_unary_types op a result : Prop := 0<=op<=3 /\
 if (Z.eqb op 0 || Z.eqb op 1)%bool then cm_integer_type a /\ result=CMIntTy
 else if Z.eqb op 2 then cm_is_pointer a /\ result=cm_pointee a else result=CMPtrTy a.
Definition cm_expr_array p f e : Prop := match e with
 | CMVarE scope slot _=>if Z.eqb scope 0 then cm_global_count (cm_global_at slot (cm_program_globals p))<>0 else if Z.eqb scope 1 then cm_slot_count (cm_slot_at slot (cm_function_locals f))<>0 else False
 | CMMemberE a mid _=>cm_slot_count (cm_slot_at mid (cm_struct_members (cm_struct_at (cm_struct_id (cm_pointee (cm_expr_type a))) (cm_program_structs p))))<>0
 | _=>False end.
Fixpoint cm_expr_wf policy p f e : Prop := match e with
 | CMConstE _ ty=>cm_integer_type ty
 | CMStringE sid ty=>0<=sid<Zlength (cm_program_strings p) /\ ty=CMPtrTy CMCharTy
 | CMVarE scope slot ty=>cm_binding_valid p f scope slot /\ ty=cm_binding_type p f scope slot
 | CMAssignE a b ty=>cm_expr_wf policy p f a /\ cm_expr_wf policy p f b /\ cm_lvalue a /\ ~cm_expr_array p f a /\ ty=cm_expr_type a /\ cm_expr_convertible b ty
 | CMBinaryE op a b ty=>cm_expr_wf policy p f a /\ cm_expr_wf policy p f b /\ cm_binary_types op (cm_expr_type a) (cm_expr_type b) ty
 | CMUnaryE op a ty=>cm_expr_wf policy p f a /\ cm_unary_types op (cm_expr_type a) ty /\ (op=3 -> cm_lvalue a /\ ~cm_expr_array p f a)
 | CMIndexE a b ty=>cm_expr_wf policy p f a /\ cm_expr_wf policy p f b /\ cm_is_pointer (cm_expr_type a) /\ cm_integer_type (cm_expr_type b) /\ ty=cm_pointee (cm_expr_type a)
 | CMMemberE a mid ty=>cm_expr_wf policy p f a /\ cm_member_valid p (cm_expr_type a) mid /\ ty=cm_member_type p (cm_expr_type a) mid
 | CMCallE callee args ty=>0<=callee<Zlength (cm_program_functions p) /\
   (fix aw (args:list cm_expr) (slots:list cm_slot_d):Prop := match args,slots with
    [],[]=>True | a::t,h::s=>cm_expr_wf policy p f a /\ cm_expr_convertible a (cm_slot_ty h) /\ aw t s | _,_=>False end) args (cm_function_params (cm_function_at policy callee (cm_program_functions p))) /\ ty=cm_function_ret (cm_function_at policy callee (cm_program_functions p))
 | CMSizeofE asked ty=>cm_type_code_wf asked /\ cm_type_refs (cm_program_structs p) asked /\ ty=CMIntTy
 | CMGetcE ty=>ty=CMIntTy
 | CMPutcE a ty=>cm_expr_wf policy p f a /\ cm_scalar_type (cm_program_structs p) (cm_expr_type a) /\ ty=CMIntTy
 | CMPutiE a ty | CMExitE a ty=>cm_expr_wf policy p f a /\ cm_integer_type (cm_expr_type a) /\ ty=CMIntTy end.
Fixpoint cm_args_wf policy p f args slots : Prop := match args,slots with
 [],[]=>True | a::t,h::s=>cm_expr_wf policy p f a /\ cm_expr_convertible a (cm_slot_ty h) /\ cm_args_wf policy p f t s | _,_=>False end.
Fixpoint cm_stmt_wf policy p f (loop:bool) s : Prop := match s with
 | CMSkipS=>True | CMExprS e=>cm_expr_wf policy p f e /\ cm_scalar_expr_type (cm_expr_type e)
 | CMDeclS slot=>0<=slot<Zlength (cm_function_locals f)
 | CMInitS slot e=>0<=slot<Zlength (cm_function_locals f) /\ cm_slot_count (cm_slot_at slot (cm_function_locals f))=0 /\ cm_expr_wf policy p f e /\ cm_expr_convertible e (cm_slot_ty (cm_slot_at slot (cm_function_locals f)))
 | CMSeqS a b=>cm_stmt_wf policy p f loop a /\ cm_stmt_wf policy p f loop b
 | CMBlockS a=>cm_stmt_wf policy p f loop a
 | CMIfS e a b=>cm_expr_wf policy p f e /\ cm_scalar_expr_type (cm_expr_type e) /\ cm_stmt_wf policy p f loop a /\ cm_stmt_wf policy p f loop b
 | CMWhileS e a=>cm_expr_wf policy p f e /\ cm_scalar_expr_type (cm_expr_type e) /\ cm_stmt_wf policy p f true a
 | CMBreakS | CMContinueS=>loop=true
 | CMReturnS e=>cm_expr_wf policy p f e /\ cm_expr_convertible e (cm_function_ret f) end.
Fixpoint cm_decl_count slot s : Z := match s with
 | CMDeclS n | CMInitS n _=>if Z.eqb n slot then 1 else 0
 | CMSeqS a b | CMIfS _ a b=>cm_decl_count slot a+cm_decl_count slot b
 | CMBlockS a | CMWhileS _ a=>cm_decl_count slot a | _=>0 end.
Definition cm_slot_wf structs s := 0<=cm_slot_count s /\ cm_scalar_type structs (cm_slot_ty s) /\ 0<cm_slot_size structs s<=1048576.
Definition cm_slots_wf structs slots := forall i, 0<=i<Zlength slots -> cm_slot_wf structs (cm_slot_at i slots).
Definition cm_params_wf structs slots := cm_slots_wf structs slots /\ forall i, 0<=i<Zlength slots -> cm_slot_count (cm_slot_at i slots)=0.
Definition cm_struct_wf structs s := cm_struct_members s<>[] /\ cm_slots_wf structs (cm_struct_members s) /\ 0<cm_struct_slots_size (cm_struct_members s)<=1048576.
Definition cm_global_wf structs g := 0<=cm_global_count g /\ cm_scalar_type structs (cm_global_ty g) /\ 0<cm_global_size structs g<=1048576 /\
 (cm_global_has_init g=true -> cm_global_count g=0) /\
 (cm_global_has_init g=true -> -9223372036854775808<=cm_global_init g<=9223372036854775807) /\
 (cm_global_has_init g=true /\ cm_is_pointer (cm_global_ty g) -> cm_global_init g=0).
Definition cm_string_wf s := forall i, 0<=i<Zlength (cm_string_bytes s) -> 0<=Znth i (cm_string_bytes s) 0<=255.
Fixpoint cm_expr_scope_wf (active:Z->Prop) e : Prop := match e with
 | CMVarE scope slot _=>scope<>1 \/ active slot
 | CMAssignE a b _ | CMBinaryE _ a b _ | CMIndexE a b _=>cm_expr_scope_wf active a /\ cm_expr_scope_wf active b
 | CMUnaryE _ a _ | CMMemberE a _ _ | CMPutcE a _ | CMPutiE a _ | CMExitE a _=>cm_expr_scope_wf active a
 | CMCallE _ args _=>(fix all (l:list cm_expr):Prop:=match l with []=>True | h::t=>cm_expr_scope_wf active h /\ all t end) args
 | _=>True end.
Definition cm_scope_add (active:Z->Prop) slot := fun i=>i=slot \/ active i.
Fixpoint cm_stmt_scope_result (active:Z->Prop) s : Z->Prop := match s with
 | CMDeclS n | CMInitS n _=>cm_scope_add active n
 | CMSeqS a b=>cm_stmt_scope_result (cm_stmt_scope_result active a) b | _=>active end.
Fixpoint cm_stmt_scope_wf active s : Prop := match s with
 | CMExprS e | CMReturnS e=>cm_expr_scope_wf active e
 | CMDeclS slot=>~active slot | CMInitS slot e=>~active slot /\ cm_expr_scope_wf active e
 | CMSeqS a b=>cm_stmt_scope_wf active a /\ cm_stmt_scope_wf (cm_stmt_scope_result active a) b
 | CMBlockS a=>cm_stmt_scope_wf active a
 | CMIfS e a b=>cm_expr_scope_wf active e /\ cm_stmt_scope_wf active a /\ cm_stmt_scope_wf active b
 | CMWhileS e a=>cm_expr_scope_wf active e /\ cm_stmt_scope_wf active a | _=>True end.
Definition cm_function_wf policy p f :=
 cm_scalar_type (cm_program_structs p) (cm_function_ret f) /\ cm_params_wf (cm_program_structs p) (cm_function_params f) /\
 cm_slots_wf (cm_program_structs p) (cm_function_locals f) /\ cm_stmt_wf policy p f false (cm_function_body f) /\
 cm_stmt_scope_wf (fun _=>False) (cm_function_body f) /\
 (forall i, 0<=i<Zlength (cm_function_locals f) -> cm_decl_count i (cm_function_body f)=1) /\
 0<=cm_temp_slots f /\ 8<=cm_frame_size (cm_program_structs p) f<=1048560.
Definition cm_typed_program policy p :=
 (forall i, 0<=i<Zlength (cm_program_structs p) -> cm_struct_wf (cm_program_structs p) (cm_struct_at i (cm_program_structs p))) /\
 (forall i, 0<=i<Zlength (cm_program_globals p) -> cm_global_wf (cm_program_structs p) (cm_global_at i (cm_program_globals p))) /\
 (forall i, 0<=i<Zlength (cm_program_strings p) -> cm_string_wf (nth (Z.to_nat i) (cm_program_strings p) (CMStringD []))) /\
 (forall i, 0<=i<Zlength (cm_program_functions p) -> cm_function_wf policy p (cm_function_at policy i (cm_program_functions p))) /\
 0<=cm_program_main p<Zlength (cm_program_functions p) /\
 cm_function_ret (cm_function_at policy (cm_program_main p) (cm_program_functions p))=CMIntTy /\
 cm_function_params (cm_function_at policy (cm_program_main p) (cm_program_functions p))=[] /\
 16<=cm_static_size p<=1048576.
Fixpoint cm_max_function_arity_from l : Z := match l with []=>0 | f::t=>Z.max (Zlength (cm_function_params f)) (cm_max_function_arity_from t) end.
Definition cm_stack_bound_model p := 3+cm_max_function_arity_from (cm_program_functions p).

(* The source defines model_data_length as byte-list length. Keep this definition
   rather than replacing it by representation sizes; source initialization bytes
   are little-endian tower_word_bytes and tower_u8. *)
Definition cm_global_init_bytes g : list Z := match cm_global_ty g with
 | CMCharTy=>[cm_global_init g mod 256]
 | _=>map (fun k:nat=>(cm_global_init g / (256 ^ Z.of_nat k)) mod 256) (seq 0 8) end.
Definition cm_global_bytes structs g := let size:=cm_global_size structs g in
 let initial:=cm_global_init_bytes g in
 if Z.leb 0 size then
  if (cm_global_has_init g && Z.leb (Zlength initial) size)%bool
  then initial ++ repeat 0 (Z.to_nat (size-Zlength initial))
  else repeat 0 (Z.to_nat size)
 else [].
Fixpoint cm_globals_bytes structs l : list Z := match l with []=>[] | h::t=>cm_global_bytes structs h ++ cm_globals_bytes structs t end.
Fixpoint cm_strings_bytes l : list Z := match l with []=>[] | h::t=>cm_string_bytes h ++ [0] ++ cm_strings_bytes t end.
Definition cm_model_data_bytes p := repeat 0 8 ++ cm_globals_bytes (cm_program_structs p) (cm_program_globals p) ++ cm_strings_bytes (cm_program_strings p).
Definition cm_model_data_length p := Zlength (cm_model_data_bytes p).

(* Only emitter fields, unused by all count bodies/proofs, are abstracted.
   Every contract universally quantifies this record. Source instantiation:
   code_shape p = tvm_code_shape (cm_model_code p);
   targets_valid p = tvm_targets_valid (cm_model_code p);
   patches_valid p = tvm_patches_valid (cm_model_patches p);
   entry_valid p = tvm_target_valid (cm_model_code p) 0.
   All four source conjuncts remain present. No axiom or extra premise relates
   these arbitrary predicates to counts; choosing the source predicates gives
   the original contract. This file does not migrate code emission semantics. *)
Record cm_codegen_obligations := CMCodegenObligations {
 cm_codegen_code_shape:cm_program->Prop;
 cm_codegen_targets_valid:cm_program->Prop;
 cm_codegen_patches_valid:cm_program->Prop;
 cm_codegen_entry_valid:cm_program->Prop
}.
Definition cm_codegen_fields_representable cg p := cm_codegen_code_shape cg p /\ cm_codegen_targets_valid cg p /\ cm_codegen_patches_valid cg p /\ cm_codegen_entry_valid cg p.
Definition cm_codegen_counts_representable policy p := cm_functions_counts_representable policy p (cm_program_functions p) 0 /\ cm_function_pcs_representable policy p (cm_program_functions p) 0.
Definition cm_codegen_admissible policy cg p := cm_typed_program policy p /\
 0<=cm_model_code_length policy p<=2147483647 /\ 0<=cm_model_data_length p<=1048568 /\
 0<=cm_stack_bound_model p<=65536 /\ cm_codegen_fields_representable cg p /\ cm_codegen_counts_representable policy p.
Definition cm_wf_program := cm_codegen_admissible.
Lemma cm_codegen_fields_source (shape targets patches entry:cm_program->Prop) p :
 cm_codegen_fields_representable (CMCodegenObligations shape targets patches entry) p <->
 shape p /\ targets p /\ patches p /\ entry p.
Proof. reflexivity. Qed.

Definition cm_program_context_rep (root:Z) p (functions:Z):Assertion :=
 “root<>0” && EX s g t:Z,
 &(root # "cm_program" ->ₛ "structs") # Ptr |-> s **
 &(root # "cm_program" ->ₛ "globals") # Ptr |-> g **
 &(root # "cm_program" ->ₛ "strings") # Ptr |-> t **
 &(root # "cm_program" ->ₛ "functions") # Ptr |-> functions **
 &(root # "cm_program" ->ₛ "main_id") # Int |-> cm_program_main p **
 cm_struct_list_rep s (cm_program_structs p) ** cm_global_list_rep g (cm_program_globals p) ** cm_string_list_rep t (cm_program_strings p).
Definition cm_function_context_rep (root:Z) f (body next:Z):Assertion :=
 “root<>0” && EX params locals:Z,
 &(root # "cm_function" ->ₛ "ret_ty") # Int |-> cm_type_encode (cm_function_ret f) **
 &(root # "cm_function" ->ₛ "params") # Ptr |-> params **
 &(root # "cm_function" ->ₛ "locals") # Ptr |-> locals **
 &(root # "cm_function" ->ₛ "body") # Ptr |-> body **
 &(root # "cm_function" ->ₛ "next") # Ptr |-> next **
 cm_slot_list_rep params (cm_function_params f) ** cm_slot_list_rep locals (cm_function_locals f).
Fixpoint cm_function_header_list_rep (root:Z) fs (bodies:list Z):Assertion := match fs with
 | []=> “root=0 /\ bodies=[]” && emp
 | f::t=> “root<>0” && EX b n:Z, EX bt:list Z,
   “bodies=b::bt” && cm_function_context_rep root f b n ** cm_function_header_list_rep n t bt end.
Fixpoint cm_function_body_list_rep (bodies:list Z) fs:Assertion := match fs with
 | []=> “bodies=[]” && emp
 | f::t=> EX b:Z, EX bt:list Z, “bodies=b::bt” && cm_stmt_rep b (cm_function_body f) ** cm_function_body_list_rep bt t end.
Definition cm_function_list_rep root fs := EX bs:list Z, cm_function_header_list_rep root fs bs ** cm_function_body_list_rep bs fs.

Lemma cm_expr_counts_call policy p fid callee args ty :
 cm_expr_code_counts policy p fid (CMCallE callee args ty) = CMCodeCounts 0 (cm_args_code_count_of (cm_args_code_counts policy p fid args)).
Proof.
 cbn [cm_expr_code_counts]. f_equal.
 induction args as [|a t IH]; cbn [cm_args_code_counts] in *; [reflexivity|].
 cbn in IH |- *. now rewrite IH.
Qed.
Lemma cm_expr_wf_call policy p f callee args ty :
 cm_expr_wf policy p f (CMCallE callee args ty) <->
 0<=callee<Zlength (cm_program_functions p) /\ cm_args_wf policy p f args (cm_function_params (cm_function_at policy callee (cm_program_functions p))) /\ ty=cm_function_ret (cm_function_at policy callee (cm_program_functions p)).
Proof.
 cbn [cm_expr_wf]. apply and_iff_compat_l. apply and_iff_compat_r.
 generalize (cm_function_params (cm_function_at policy callee (cm_program_functions p))) as slots.
 induction args as [|a t IH]; intros [|h slots]; cbn [cm_args_wf]; simpl; try tauto.
 specialize (IH slots). tauto.
Qed.
Lemma cm_expr_counts_repr_call policy p fid callee args ty :
 cm_expr_counts_representable policy p fid (CMCallE callee args ty) <->
 cm_expr_count_node_representable policy p fid (CMCallE callee args ty) /\ cm_i32_code_count callee /\ cm_args_counts_representable policy p fid args.
Proof.
 cbn [cm_expr_counts_representable]. apply and_iff_compat_l. apply and_iff_compat_l.
 induction args as [|a t IH]; cbn [cm_args_counts_representable]; simpl; tauto.
Qed.

(* Transparent annotation projection, used only to name a member child type
   in a call where clause after an existential AST decomposition. *)
Definition cm_member_base_type e := match e with CMMemberE a _ _=>cm_expr_type a | _=>cm_expr_type e end.

Lemma cm_type_depth_nonnegative__expression_assignment_safety t :
  0 <= cm_type_depth t.
Proof. induction t; cbn [cm_type_depth]; lia. Qed.
Lemma cm_type_base_bounds__expression_assignment_safety t :
  cm_type_code_wf t -> 0 <= cm_type_base_code t < 1024.
Proof. induction t; cbn [cm_type_code_wf cm_type_base_code]; intros; try lia; auto. Qed.
Lemma cm_normalize_encode__expression_assignment_safety t :
  cm_type_code_wf t ->
  cm_normalize_code_value (cm_type_encode t) = cm_char_normalize_count t.
Proof.
  intros Hwf. destruct t as [| |z|t]; try reflexivity.
  - unfold cm_normalize_code_value, cm_type_encode.
    cbn [cm_type_depth cm_type_base_code cm_char_normalize_count].
    destruct (Z.eqb (1024 * 0 + (z + 2)) 1) eqn:Heq; try reflexivity.
    apply Z.eqb_eq in Heq. cbn [cm_type_code_wf] in Hwf. lia.
  - pose proof (cm_type_depth_nonnegative__expression_assignment_safety t) as Hd.
    pose proof (cm_type_base_bounds__expression_assignment_safety t Hwf) as Hb.
    unfold cm_normalize_code_value, cm_type_encode.
    cbn [cm_type_depth cm_type_base_code cm_char_normalize_count].
    destruct (Z.eqb (1024 * (1 + cm_type_depth t) + cm_type_base_code t) 1) eqn:Heq; try reflexivity.
    apply Z.eqb_eq in Heq. lia.
Qed.
Lemma cm_type_encoding_bounds__expression_add_safety : forall t,
 cm_type_code_wf t -> 0 <= cm_type_depth t /\ 0 <= cm_type_base_code t < 1024.
Proof.
 induction t; cbn [cm_type_code_wf cm_type_depth cm_type_base_code]; intros H; try lia.
 specialize (IHt H). lia.
Qed.
Lemma cm_pointer_encode__expression_add_safety : forall t,
 cm_type_code_wf t ->
 cm_rep_is_pointer_code (cm_type_encode t) = (if cm_pointerb t then 1 else 0).
Proof.
 intros t H. pose proof (cm_type_encoding_bounds__expression_add_safety t H) as Hb.
 assert (Hd : forall u, 0 <= cm_type_depth u).
 { induction u; cbn [cm_type_depth]; lia. }
 unfold cm_rep_is_pointer_code, cm_type_encode.
 destruct t; cbn [cm_pointerb cm_type_depth cm_type_base_code] in *;
 destruct (Z.leb 1024 _) eqn:He; try reflexivity;
 apply Z.leb_le in He || apply Z.leb_gt in He; try specialize (Hd t); lia.
Qed.
Lemma cm_type_bounds__expression_sub_safety t :
 cm_type_code_wf t -> 0 <= cm_type_depth t /\ 0 <= cm_type_base_code t < 1024.
Proof.
 induction t; cbn [cm_type_code_wf cm_type_depth cm_type_base_code] in *; intros H; try specialize (IHt H); lia.
Qed.
Lemma cm_pointer_encode__expression_sub_safety t :
 cm_type_code_wf t ->
 cm_rep_is_pointer_code (cm_type_encode t) = (if cm_pointerb t then 1 else 0).
Proof.
 intros H. pose proof (cm_type_bounds__expression_sub_safety t H) as Hb.
 destruct t;
 try match goal with H : cm_type_code_wf (CMPtrTy ?u) |- _ =>
 pose proof (cm_type_bounds__expression_sub_safety u H) as Hu end;
 unfold cm_rep_is_pointer_code, cm_type_encode;
 cbn [cm_type_depth cm_type_base_code cm_pointerb] in *;
 match goal with |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b) end;
 try reflexivity; lia.
Qed.
Lemma cm_type_encoding_bounds__expression_assignment_result t :
 cm_type_code_wf t -> 0 <= cm_type_depth t /\ 0 <= cm_type_base_code t < 1024.
Proof.
 induction t; cbn [cm_type_code_wf cm_type_depth cm_type_base_code]; intros H; try lia.
 specialize (IHt H). lia.
Qed.
Lemma cm_normalize_encode__expression_assignment_result t :
 cm_type_code_wf t ->
 cm_normalize_code_value (cm_type_encode t) = cm_char_normalize_count t.
Proof.
 intros H.
 pose proof (cm_type_encoding_bounds__expression_assignment_result t H) as Hb.
 destruct t as [| |z|t]; try reflexivity.
 - unfold cm_normalize_code_value, cm_type_encode.
   cbn [cm_type_depth cm_type_base_code cm_char_normalize_count cm_type_code_wf] in *.
   destruct (Z.eqb (1024 * 0 + (z + 2)) 1) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity].
 - pose proof (cm_type_encoding_bounds__expression_assignment_result t H) as Hinner.
   unfold cm_normalize_code_value, cm_type_encode.
   cbn [cm_type_depth cm_type_base_code cm_char_normalize_count].
   destruct (Z.eqb (1024 * (1 + cm_type_depth t) + cm_type_base_code t) 1) eqn:E;
   [apply Z.eqb_eq in E; lia | reflexivity].
Qed.
Lemma cm_type_encoding_bounds__expression_add_results t :
 cm_type_code_wf t -> 0 <= cm_type_depth t /\ 0 <= cm_type_base_code t < 1024.
Proof.
 induction t; cbn [cm_type_code_wf cm_type_depth cm_type_base_code] in *; intros; try lia.
 specialize (IHt H). lia.
Qed.
Lemma cm_pointer_encode__expression_add_results t :
 cm_type_code_wf t -> cm_rep_is_pointer_code (cm_type_encode t) =
 (if cm_pointerb t then 1 else 0).
Proof.
 intro H. destruct t as [| |z|t].
 - reflexivity.
 - reflexivity.
 - change ((if Z.leb 1024 (z+2) then 1 else 0) = 0).
   cbn [cm_type_code_wf] in H.
   destruct (Z.leb 1024 (z+2)) eqn:E; try reflexivity.
   apply Z.leb_le in E. lia.
 - pose proof (cm_type_encoding_bounds__expression_add_results t H) as B.
   change ((if Z.leb 1024 (1024*(1+cm_type_depth t)+cm_type_base_code t) then 1 else 0) = 1).
   destruct (Z.leb 1024 (1024*(1+cm_type_depth t)+cm_type_base_code t)) eqn:E; try reflexivity.
   apply Z.leb_gt in E. lia.
Qed.
Lemma cm_type_bounds__expression_sub_results t :
 cm_type_code_wf t -> 0 <= cm_type_depth t /\ 0 <= cm_type_base_code t < 1024.
Proof. induction t; cbn [cm_type_code_wf cm_type_depth cm_type_base_code]; intros; try tauto; try lia. specialize (IHt H); lia. Qed.
Lemma cm_pointer_encode__expression_sub_results t :
 cm_type_code_wf t -> cm_rep_is_pointer_code (cm_type_encode t) = (if cm_pointerb t then 1 else 0).
Proof.
 intro H. pose proof (cm_type_bounds__expression_sub_results t H) as Hb.
 destruct t; unfold cm_rep_is_pointer_code, cm_type_encode;
 cbn [cm_pointerb cm_type_depth cm_type_base_code] in *;
 destruct (Z.leb 1024 _) eqn:E; try reflexivity;
 apply Z.leb_le in E || apply Z.leb_gt in E; try lia.
 pose proof (cm_type_bounds__expression_sub_results t H). lia.
Qed.
Lemma cm_type_bounds__statement_normalization_safety t :
 cm_type_code_wf t -> 0 <= cm_type_depth t /\ 0 <= cm_type_base_code t < 1024.
Proof.
 induction t; cbn [cm_type_code_wf cm_type_depth cm_type_base_code]; intros H; try lia.
 specialize (IHt H). lia.
Qed.
Lemma cm_normalize_encode__statement_normalization_safety t :
 cm_type_code_wf t -> cm_normalize_code_value (cm_type_encode t) = cm_char_normalize_count t.
Proof.
 destruct t; intros H; try reflexivity.
 - change (0 <= sid < 1022) in H.
   change ((if Z.eqb (sid+2) 1 then 6 else 0) = 0).
   destruct (Z.eqb_spec (sid+2) 1); [lia|reflexivity].
 - pose proof (cm_type_bounds__statement_normalization_safety t H) as Hb.
   change ((if Z.eqb (1024*(1+cm_type_depth t)+cm_type_base_code t) 1 then 6 else 0) = 0).
   destruct (Z.eqb_spec (1024*(1+cm_type_depth t)+cm_type_base_code t) 1); [lia|reflexivity].
Qed.
Lemma cm_slot_type_encode__statement_normalization_safety : forall l i,
 0 <= i < Zlength l -> cm_rep_slot_type l i = cm_type_encode (cm_slot_ty (cm_slot_at i l)).
Proof.
 induction l as [|h t IH]; intros i Hi.
 - rewrite Zlength_nil in Hi. lia.
 - rewrite Zlength_cons in Hi.
   destruct (Z.eq_dec i 0) as [->|Hnz].
   + reflexivity.
   + assert (Hpos : 0 <= i-1) by lia.
     assert (Hnat : Z.to_nat i = S (Z.to_nat (i-1))).
     { rewrite <- Z2Nat.inj_succ by exact Hpos. f_equal. lia. }
     simpl cm_rep_slot_type. destruct (Z.eqb_spec i 0); [contradiction|].
     unfold cm_slot_at. rewrite Hnat. simpl nth.
     apply IH. lia.
Qed.
Lemma cm_type_bounds__statement_expression_results t : cm_type_code_wf t ->
 0 <= cm_type_depth t /\ 0 <= cm_type_base_code t < 1024.
Proof. induction t; cbn [cm_type_code_wf cm_type_depth cm_type_base_code]; intros H; try lia. specialize (IHt H). lia. Qed.
Lemma cm_normalize_encode__statement_expression_results t : cm_type_code_wf t ->
 cm_normalize_code_value (cm_type_encode t) = cm_char_normalize_count t.
Proof.
 destruct t; intros H; try (unfold cm_normalize_code_value, cm_type_encode; reflexivity).
 - cbn [cm_type_code_wf] in H.
   unfold cm_normalize_code_value, cm_type_encode; cbn [cm_type_depth cm_type_base_code cm_char_normalize_count].
   destruct (Z.eqb_spec (1024 * 0 + (sid + 2)) 1); [lia|reflexivity].
 - pose proof (cm_type_bounds__statement_expression_results t H) as Hb.
   unfold cm_normalize_code_value, cm_type_encode; cbn [cm_type_depth cm_type_base_code cm_char_normalize_count].
   destruct (Z.eqb_spec (1024 * (1 + cm_type_depth t) + cm_type_base_code t) 1); [lia|reflexivity].
Qed.
Lemma cm_slot_encode__statement_expression_results l i :
 0 <= i < Zlength l -> cm_rep_slot_type l i = cm_type_encode (cm_slot_ty (cm_slot_at i l)).
Proof.
 revert i; induction l as [|h t IH]; intros i Hi.
 - rewrite Zlength_nil in Hi. lia.
 - rewrite Zlength_cons in Hi. destruct (Z.eq_dec i 0) as [->|Hnz].
   + reflexivity.
   + assert (Hpos : 0 <= i-1) by lia.
     assert (Hnat : Z.to_nat i = S (Z.to_nat (i-1))).
     { rewrite <- Z2Nat.inj_succ by exact Hpos. f_equal. lia. }
     simpl cm_rep_slot_type. destruct (Z.eqb_spec i 0); [contradiction|].
     unfold cm_slot_at. rewrite Hnat. simpl nth. apply IH. lia.
Qed.
Lemma cm_normalize_encode__parameter_stores : forall t,
 cm_type_code_wf t -> cm_normalize_code_value (cm_type_encode t) = cm_char_normalize_count t.
Proof.
 assert (Hr : forall t, cm_type_code_wf t ->
   0 <= cm_type_depth t /\ 0 <= cm_type_base_code t < 1024).
 { induction t; cbn [cm_type_code_wf cm_type_depth cm_type_base_code] in *;
   intros; try specialize (IHt H); intuition lia. }
 intros t Hw. destruct t as [| |sid|u]; try reflexivity.
 - change ((if Z.eqb (sid+2) 1 then 6 else 0) = 0).
   cbn [cm_type_code_wf] in Hw.
   destruct (Z.eqb_spec (sid+2) 1); [lia|reflexivity].
 - pose proof (Hr u Hw) as Hrange.
   change ((if Z.eqb (1024*(1+cm_type_depth u)+cm_type_base_code u) 1 then 6 else 0) = 0).
   destruct (Z.eqb_spec (1024*(1+cm_type_depth u)+cm_type_base_code u) 1);
     [lia|reflexivity].
Qed.
Lemma cm_function_list_cons__prefix_open root f rest :
 cm_function_list_rep root (f::rest) --||--
 (EX bp np:Z, “root<>0” && cm_function_context_rep root f bp np **
 cm_stmt_rep bp (cm_function_body f) ** cm_function_list_rep np rest).
Proof.
 unfold cm_function_list_rep.
 cbn [cm_function_header_list_rep cm_function_body_list_rep].
 split.
 - Intros bs bp np bt bp' bt'.
   assert (bp'=bp /\ bt'=bt) as [-> ->] by (split; congruence).
   Exists bp np bt.
   split_pure_spatial; [cancel; reflexivity | split_pures; dump_pre_spatial; assumption].
 - Intros bp np bt.

   Exists (bp::bt) bp np bt bp bt.
   split_pure_spatial; [cancel; reflexivity | split_pures; dump_pre_spatial; auto].
Qed.
Lemma cm_function_prefix_nonnegative__prefix_transition policy p fs index remaining :
 cm_functions_counts_representable policy p fs index ->
 index = Zlength (cm_program_functions p) - Zlength fs ->
 0 <= remaining <= Zlength fs ->
 0 <= cm_function_prefix policy p fs remaining.
Proof.
 revert index remaining.
 induction fs as [|f rest IH]; intros index remaining Hrep Hindex Hrange.
 - cbn [cm_function_prefix]. lia.
 - cbn [cm_functions_counts_representable] in Hrep.
   destruct Hrep as [_ [Hhead Htail]].
   unfold cm_function_counts_representable in Hhead.
   destruct Hhead as [_ [_ [_ [_ Hcount]]]].
   unfold cm_i32_code_count in Hcount.
   cbn [cm_function_prefix].
   destruct (Z.eqb remaining 0) eqn:Hguard; [lia|].
   apply Z.eqb_neq in Hguard.
   rewrite <- Hindex.
   rewrite Zlength_cons in Hindex, Hrange.
   assert (Htailindex : index + 1 = Zlength (cm_program_functions p) - Zlength rest) by lia.
   assert (Htailrange : 0 <= remaining - 1 <= Zlength rest) by lia.
   specialize (IH (index + 1) (remaining - 1) Htail Htailindex Htailrange).
   lia.
Qed.
Lemma cm_function_list_cons__prefix_results root f rest :
 cm_function_list_rep root (f::rest) --||--
 (EX bp np:Z, “root<>0” && cm_function_context_rep root f bp np **
 cm_stmt_rep bp (cm_function_body f) ** cm_function_list_rep np rest).
Proof.
 split; unfold cm_function_list_rep; cbn [cm_function_header_list_rep cm_function_body_list_rep].
 - Intros bs b n bt b' bt'.
   assert (b'=b /\ bt'=bt) as [-> ->] by (split; congruence).
   Exists b n bt. split_pure_spatial.
   + cancel. cancel (cm_function_body_list_rep bt rest).
   + dump_pre_spatial. assumption.
 - Intros b n bt.
   Exists (b::bt) b n bt b bt.
   split_pure_spatial.
   + cancel. cancel (cm_function_body_list_rep bt rest).
   + split_pures; dump_pre_spatial; auto.
Qed.
Lemma cm_function_list_cons__functions_open root f rest :
 cm_function_list_rep root (f::rest) --||--
 (EX bp np:Z, “root<>0” && cm_function_context_rep root f bp np **
 cm_stmt_rep bp (cm_function_body f) ** cm_function_list_rep np rest).
Proof.
 split.
 - unfold cm_function_list_rep at 1.
   cbn [cm_function_header_list_rep cm_function_body_list_rep].
   Intros bs bp np bt bp' bt'.
   assert (bp=bp' /\ bt=bt') as [-> ->] by (split; congruence).
   Exists bp' np.
   unfold cm_function_list_rep.
   Exists bt'.
   split_pure_spatial.
   + cancel; reflexivity.
   + split_pures; dump_pre_spatial; assumption.
 - Intros bp np.
   unfold cm_function_list_rep.
   Intros bt.
   Exists (bp::bt).
   cbn [cm_function_header_list_rep cm_function_body_list_rep].
   Exists bp np bt bp bt.
   split_pure_spatial.
   + cancel; reflexivity.
   + split_pures; dump_pre_spatial; auto.
Qed.
Lemma cm_function_list_cons__functions_results root f rest :
 cm_function_list_rep root (f::rest) --||--
 (EX bp np:Z, “root<>0” &&
 cm_function_context_rep root f bp np ** cm_stmt_rep bp (cm_function_body f) ** cm_function_list_rep np rest).
Proof.
 unfold cm_function_list_rep at 1.
 cbn [cm_function_header_list_rep cm_function_body_list_rep].
 split.
 - Intros bs b n bt b' bt'.
   assert (b'=b /\ bt'=bt) as [-> ->] by (split; congruence).
   Exists b n.
   unfold cm_function_list_rep.
   Exists bt.
   split_pure_spatial.
   + cancel. reflexivity.
   + dump_pre_spatial. assumption.
 - Intros b n.
   unfold cm_function_list_rep.
   Intros bt.
   Exists (b::bt) b n bt b bt.
   split_pure_spatial.
   + cancel. reflexivity.
   + split_pures; dump_pre_spatial; auto.
Qed.
Lemma cm_param_count_nonnegative__model_length_bound params :
  0 <= cm_param_stores_count params.
Proof.
  induction params as [|h t IH]; cbn [cm_param_stores_count].
  - lia.
  - unfold cm_char_normalize_count. destruct (cm_slot_ty h); lia.
Qed.
Lemma cm_function_code_positive__model_length_bound policy p fid f :
  cm_function_counts_representable policy p fid f ->
  21 <= cm_function_code_count policy p fid.
Proof.
  intros [Hlookup [_ [_ [Hbody _]]]].
  assert (Hcount : cm_i32_code_count (cm_stmt_code_count policy p fid (cm_function_body f))).
  { destruct (cm_function_body f); cbn [cm_stmt_counts_representable] in Hbody; tauto. }
  pose proof (cm_param_count_nonnegative__model_length_bound (cm_function_params f)) as Hparams.
  unfold cm_function_code_count. rewrite <- Hlookup.
  unfold cm_function_prologue_count, cm_i32_code_count in *.
  lia.
Qed.
Lemma cm_functions_length_bound__model_length_bound policy p fs fid :
  cm_functions_counts_representable policy p fs fid ->
  21 * Zlength fs <= cm_functions_code_size policy p fs fid.
Proof.
  revert fid. induction fs as [|f fs IH]; intros fid Hrep.
  - cbn [cm_functions_code_size]. rewrite Zlength_nil. lia.
  - cbn [cm_functions_counts_representable] in Hrep.
    destruct Hrep as [_ [Hhead Htail]].
    pose proof (cm_function_code_positive__model_length_bound policy p fid f Hhead).
    specialize (IH (fid + 1) Htail).
    cbn [cm_functions_code_size]. rewrite Zlength_cons. lia.
Qed.
