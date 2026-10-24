Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.cmc_count_context_migration_lib.
Local Open Scope sac.

(*----- Function cm_expr_type_code_context -----*)

Definition cm_expr_type_code_context_entail_wit_1 := 
(
forall (code_pre: Z) (expr_pre: Z) (e: cm_expr) ,
  (cm_expr_rep expr_pre e )
  **  ((code_pre) # Int  |->_)
|--
  EX (pargs: Z)  (pb: Z)  (pa: Z) ,
  “ (expr_pre <> 0) ”
  &&  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
  **  ((code_pre) # Int  |->_)
) \/
(
forall (expr_pre: Z) (e: cm_expr) ,
  (cm_expr_rep expr_pre e )
|--
  EX (pargs: Z)  (pb: Z)  (pa: Z) ,
  “ (expr_pre <> 0) ”
  &&  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
).

Definition cm_expr_type_code_context_return_wit_1 := 
(
forall (code_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : (expr_pre <> 0)) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
  **  ((code_pre) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
|--
  (cm_expr_rep expr_pre e )
  **  ((code_pre) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
) \/
(
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (expr_pre <> 0)) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
|--
  (cm_expr_rep expr_pre e )
).

Definition cm_expr_type_code_context_return_wit_1_split_goal_spatial := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (expr_pre <> 0)) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
|--
  (cm_expr_rep expr_pre e )
.

(*----- Function cm_expr_lvalue_count_context -----*)

Definition cm_expr_lvalue_count_context_entail_wit_1 := 
(
forall (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (functions_ptr: Z) (next: Z) (body: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH3 : (cm_expr_wf policy p f e )) (PreH4 : (cm_expr_counts_representable policy p fid_pre e )) (PreH5 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
|--
  EX (zl: Z)  (zp: Z)  (zt: Z)  (zg: Z)  (zs: Z) ,
  “ (program_pre <> 0) ” 
  &&  “ (fn_pre <> 0) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ”
  &&  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> zt)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep zs (cm_program_structs (p)) )
  **  (cm_global_list_rep zg (cm_program_globals (p)) )
  **  (cm_string_list_rep zt (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_expr_rep expr_pre e )
) \/
(
forall (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (functions_ptr: Z) (next: Z) (body: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH3 : (cm_expr_wf policy p f e )) (PreH4 : (cm_expr_counts_representable policy p fid_pre e )) (PreH5 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
|--
  EX (zl: Z)  (zp: Z)  (zt: Z)  (zg: Z)  (zs: Z) ,
  “ (program_pre <> 0) ” 
  &&  “ (fn_pre <> 0) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ”
  &&  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> zt)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep zs (cm_program_structs (p)) )
  **  (cm_global_list_rep zg (cm_program_globals (p)) )
  **  (cm_string_list_rep zt (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_expr_rep expr_pre e )
).

Definition cm_expr_lvalue_count_context_return_wit_1 := 
(
forall (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (functions_ptr: Z) (next: Z) (body: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (zs: Z) (zg: Z) (zt: Z) (zp: Z) (zl: Z) (retval: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH3 : ((cm_program_structs (p)) = (cm_program_structs (p)))) (PreH4 : ((cm_program_globals (p)) = (cm_program_globals (p)))) (PreH5 : ((cm_function_locals (f)) = (cm_function_locals (f)))) (PreH6 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH7 : (cm_expr_wf policy p f e )) (PreH8 : (cm_expr_counts_representable policy p fid_pre e )) (PreH9 : (retval = (cm_lvalue_code_count (policy) (p) (fid_pre) (e)))) (PreH10 : (cm_i32_code_count retval )) (PreH11 : (program_pre <> 0)) (PreH12 : (fn_pre <> 0)) (PreH13 : (cm_wf_program policy cg p )) (PreH14 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH15 : (cm_expr_wf policy p f e )) (PreH16 : (cm_expr_counts_representable policy p fid_pre e )) (PreH17 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  (cm_struct_list_rep zs (cm_program_structs (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  (cm_global_list_rep zg (cm_program_globals (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_expr_rep expr_pre e )
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> zt)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_string_list_rep zt (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (retval = (cm_lvalue_code_count (policy) (p) (fid_pre) (e))) ” 
  &&  “ (cm_i32_code_count retval ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
) \/
(
forall (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (functions_ptr: Z) (next: Z) (body: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (zs: Z) (zg: Z) (zt: Z) (zp: Z) (zl: Z) (retval: Z) (PreH1 : ((cm_type_encode ((cm_function_ret (f)))) <= INT_MAX)) (PreH2 : ((cm_program_main (p)) <= INT_MAX)) (PreH3 : ((cm_type_encode ((cm_function_ret (f)))) >= INT_MIN)) (PreH4 : ((cm_program_main (p)) >= INT_MIN)) (PreH5 : (cm_wf_program policy cg p )) (PreH6 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH7 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH8 : (cm_expr_wf policy p f e )) (PreH9 : (cm_expr_counts_representable policy p fid_pre e )) (PreH10 : (retval = (cm_lvalue_code_count (policy) (p) (fid_pre) (e)))) (PreH11 : (cm_i32_code_count retval )) (PreH12 : (program_pre <> 0)) (PreH13 : (fn_pre <> 0)) (PreH14 : (cm_wf_program policy cg p )) (PreH15 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH16 : (cm_expr_wf policy p f e )) (PreH17 : (cm_expr_counts_representable policy p fid_pre e )) (PreH18 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  (cm_struct_list_rep zs (cm_program_structs (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  (cm_global_list_rep zg (cm_program_globals (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_expr_rep expr_pre e )
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> zt)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_string_list_rep zt (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
).

Definition cm_expr_lvalue_count_context_return_wit_1_split_goal_spatial := 
forall (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (functions_ptr: Z) (next: Z) (body: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (zs: Z) (zg: Z) (zt: Z) (zp: Z) (zl: Z) (retval: Z) (PreH1 : ((cm_type_encode ((cm_function_ret (f)))) <= INT_MAX)) (PreH2 : ((cm_program_main (p)) <= INT_MAX)) (PreH3 : ((cm_type_encode ((cm_function_ret (f)))) >= INT_MIN)) (PreH4 : ((cm_program_main (p)) >= INT_MIN)) (PreH5 : (cm_wf_program policy cg p )) (PreH6 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH7 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH8 : (cm_expr_wf policy p f e )) (PreH9 : (cm_expr_counts_representable policy p fid_pre e )) (PreH10 : (retval = (cm_lvalue_code_count (policy) (p) (fid_pre) (e)))) (PreH11 : (cm_i32_code_count retval )) (PreH12 : (program_pre <> 0)) (PreH13 : (fn_pre <> 0)) (PreH14 : (cm_wf_program policy cg p )) (PreH15 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH16 : (cm_expr_wf policy p f e )) (PreH17 : (cm_expr_counts_representable policy p fid_pre e )) (PreH18 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  (cm_struct_list_rep zs (cm_program_structs (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  (cm_global_list_rep zg (cm_program_globals (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_expr_rep expr_pre e )
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> zt)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_string_list_rep zt (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
.

Definition cm_expr_lvalue_count_context_partial_solve_wit_1_pure := 
forall (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (functions_ptr: Z) (next: Z) (body: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (zs: Z) (zg: Z) (zt: Z) (zp: Z) (zl: Z) (PreH1 : (program_pre <> 0)) (PreH2 : (fn_pre <> 0)) (PreH3 : (cm_wf_program policy cg p )) (PreH4 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH5 : (cm_expr_wf policy p f e )) (PreH6 : (cm_expr_counts_representable policy p fid_pre e )) (PreH7 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> zt)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep zs (cm_program_structs (p)) )
  **  (cm_global_list_rep zg (cm_program_globals (p)) )
  **  (cm_string_list_rep zt (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_expr_rep expr_pre e )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ ((cm_program_structs (p)) = (cm_program_structs (p))) ” 
  &&  “ ((cm_program_globals (p)) = (cm_program_globals (p))) ” 
  &&  “ ((cm_function_locals (f)) = (cm_function_locals (f))) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ”
.

Definition cm_expr_lvalue_count_context_partial_solve_wit_1_aux := 
forall (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (functions_ptr: Z) (next: Z) (body: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (zs: Z) (zg: Z) (zt: Z) (zp: Z) (zl: Z) (PreH1 : (program_pre <> 0)) (PreH2 : (fn_pre <> 0)) (PreH3 : (cm_wf_program policy cg p )) (PreH4 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH5 : (cm_expr_wf policy p f e )) (PreH6 : (cm_expr_counts_representable policy p fid_pre e )) (PreH7 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> zt)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep zs (cm_program_structs (p)) )
  **  (cm_global_list_rep zg (cm_program_globals (p)) )
  **  (cm_string_list_rep zt (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_expr_rep expr_pre e )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ ((cm_program_structs (p)) = (cm_program_structs (p))) ” 
  &&  “ ((cm_program_globals (p)) = (cm_program_globals (p))) ” 
  &&  “ ((cm_function_locals (f)) = (cm_function_locals (f))) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ (program_pre <> 0) ” 
  &&  “ (fn_pre <> 0) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ”
  &&  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  (cm_struct_list_rep zs (cm_program_structs (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  (cm_global_list_rep zg (cm_program_globals (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_expr_rep expr_pre e )
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> zt)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_string_list_rep zt (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
.

Definition cm_expr_lvalue_count_context_partial_solve_wit_1 := cm_expr_lvalue_count_context_partial_solve_wit_1_pure -> cm_expr_lvalue_count_context_partial_solve_wit_1_aux.

(*----- Function cm_expr_rvalue_count_context -----*)

Definition cm_expr_rvalue_count_context_entail_wit_1 := 
(
forall (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (functions_ptr: Z) (next: Z) (body: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH3 : (cm_expr_wf policy p f e )) (PreH4 : (cm_expr_counts_representable policy p fid_pre e )) (PreH5 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
|--
  EX (zl: Z)  (zp: Z)  (zt: Z)  (zg: Z)  (zs: Z) ,
  “ (program_pre <> 0) ” 
  &&  “ (fn_pre <> 0) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ”
  &&  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> zt)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep zs (cm_program_structs (p)) )
  **  (cm_global_list_rep zg (cm_program_globals (p)) )
  **  (cm_string_list_rep zt (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_expr_rep expr_pre e )
) \/
(
forall (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (functions_ptr: Z) (next: Z) (body: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH3 : (cm_expr_wf policy p f e )) (PreH4 : (cm_expr_counts_representable policy p fid_pre e )) (PreH5 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
|--
  EX (zl: Z)  (zp: Z)  (zt: Z)  (zg: Z)  (zs: Z) ,
  “ (program_pre <> 0) ” 
  &&  “ (fn_pre <> 0) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ”
  &&  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> zt)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep zs (cm_program_structs (p)) )
  **  (cm_global_list_rep zg (cm_program_globals (p)) )
  **  (cm_string_list_rep zt (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_expr_rep expr_pre e )
).

Definition cm_expr_rvalue_count_context_return_wit_1 := 
(
forall (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (functions_ptr: Z) (next: Z) (body: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (zs: Z) (zg: Z) (zt: Z) (zp: Z) (zl: Z) (retval: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH3 : ((cm_program_structs (p)) = (cm_program_structs (p)))) (PreH4 : ((cm_program_globals (p)) = (cm_program_globals (p)))) (PreH5 : ((cm_function_locals (f)) = (cm_function_locals (f)))) (PreH6 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH7 : (cm_expr_wf policy p f e )) (PreH8 : (cm_expr_counts_representable policy p fid_pre e )) (PreH9 : (retval = (cm_rvalue_code_count (policy) (p) (fid_pre) (e)))) (PreH10 : (cm_i32_code_count retval )) (PreH11 : (program_pre <> 0)) (PreH12 : (fn_pre <> 0)) (PreH13 : (cm_wf_program policy cg p )) (PreH14 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH15 : (cm_expr_wf policy p f e )) (PreH16 : (cm_expr_counts_representable policy p fid_pre e )) (PreH17 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  (cm_struct_list_rep zs (cm_program_structs (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  (cm_global_list_rep zg (cm_program_globals (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_expr_rep expr_pre e )
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> zt)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_string_list_rep zt (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (retval = (cm_rvalue_code_count (policy) (p) (fid_pre) (e))) ” 
  &&  “ (cm_i32_code_count retval ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
) \/
(
forall (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (functions_ptr: Z) (next: Z) (body: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (zs: Z) (zg: Z) (zt: Z) (zp: Z) (zl: Z) (retval: Z) (PreH1 : ((cm_type_encode ((cm_function_ret (f)))) <= INT_MAX)) (PreH2 : ((cm_program_main (p)) <= INT_MAX)) (PreH3 : ((cm_type_encode ((cm_function_ret (f)))) >= INT_MIN)) (PreH4 : ((cm_program_main (p)) >= INT_MIN)) (PreH5 : (cm_wf_program policy cg p )) (PreH6 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH7 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH8 : (cm_expr_wf policy p f e )) (PreH9 : (cm_expr_counts_representable policy p fid_pre e )) (PreH10 : (retval = (cm_rvalue_code_count (policy) (p) (fid_pre) (e)))) (PreH11 : (cm_i32_code_count retval )) (PreH12 : (program_pre <> 0)) (PreH13 : (fn_pre <> 0)) (PreH14 : (cm_wf_program policy cg p )) (PreH15 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH16 : (cm_expr_wf policy p f e )) (PreH17 : (cm_expr_counts_representable policy p fid_pre e )) (PreH18 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  (cm_struct_list_rep zs (cm_program_structs (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  (cm_global_list_rep zg (cm_program_globals (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_expr_rep expr_pre e )
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> zt)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_string_list_rep zt (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
).

Definition cm_expr_rvalue_count_context_return_wit_1_split_goal_spatial := 
forall (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (functions_ptr: Z) (next: Z) (body: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (zs: Z) (zg: Z) (zt: Z) (zp: Z) (zl: Z) (retval: Z) (PreH1 : ((cm_type_encode ((cm_function_ret (f)))) <= INT_MAX)) (PreH2 : ((cm_program_main (p)) <= INT_MAX)) (PreH3 : ((cm_type_encode ((cm_function_ret (f)))) >= INT_MIN)) (PreH4 : ((cm_program_main (p)) >= INT_MIN)) (PreH5 : (cm_wf_program policy cg p )) (PreH6 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH7 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH8 : (cm_expr_wf policy p f e )) (PreH9 : (cm_expr_counts_representable policy p fid_pre e )) (PreH10 : (retval = (cm_rvalue_code_count (policy) (p) (fid_pre) (e)))) (PreH11 : (cm_i32_code_count retval )) (PreH12 : (program_pre <> 0)) (PreH13 : (fn_pre <> 0)) (PreH14 : (cm_wf_program policy cg p )) (PreH15 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH16 : (cm_expr_wf policy p f e )) (PreH17 : (cm_expr_counts_representable policy p fid_pre e )) (PreH18 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  (cm_struct_list_rep zs (cm_program_structs (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  (cm_global_list_rep zg (cm_program_globals (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_expr_rep expr_pre e )
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> zt)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_string_list_rep zt (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_expr_rep expr_pre e )
.

Definition cm_expr_rvalue_count_context_partial_solve_wit_1_pure := 
forall (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (functions_ptr: Z) (next: Z) (body: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (zs: Z) (zg: Z) (zt: Z) (zp: Z) (zl: Z) (PreH1 : (program_pre <> 0)) (PreH2 : (fn_pre <> 0)) (PreH3 : (cm_wf_program policy cg p )) (PreH4 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH5 : (cm_expr_wf policy p f e )) (PreH6 : (cm_expr_counts_representable policy p fid_pre e )) (PreH7 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> zt)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep zs (cm_program_structs (p)) )
  **  (cm_global_list_rep zg (cm_program_globals (p)) )
  **  (cm_string_list_rep zt (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_expr_rep expr_pre e )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ ((cm_program_structs (p)) = (cm_program_structs (p))) ” 
  &&  “ ((cm_program_globals (p)) = (cm_program_globals (p))) ” 
  &&  “ ((cm_function_locals (f)) = (cm_function_locals (f))) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ”
.

Definition cm_expr_rvalue_count_context_partial_solve_wit_1_aux := 
forall (expr_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (functions_ptr: Z) (next: Z) (body: Z) (e: cm_expr) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (zs: Z) (zg: Z) (zt: Z) (zp: Z) (zl: Z) (PreH1 : (program_pre <> 0)) (PreH2 : (fn_pre <> 0)) (PreH3 : (cm_wf_program policy cg p )) (PreH4 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH5 : (cm_expr_wf policy p f e )) (PreH6 : (cm_expr_counts_representable policy p fid_pre e )) (PreH7 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> zt)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep zs (cm_program_structs (p)) )
  **  (cm_global_list_rep zg (cm_program_globals (p)) )
  **  (cm_string_list_rep zt (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_expr_rep expr_pre e )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ ((cm_program_structs (p)) = (cm_program_structs (p))) ” 
  &&  “ ((cm_program_globals (p)) = (cm_program_globals (p))) ” 
  &&  “ ((cm_function_locals (f)) = (cm_function_locals (f))) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ (program_pre <> 0) ” 
  &&  “ (fn_pre <> 0) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_expr_wf policy p f e ) ” 
  &&  “ (cm_expr_counts_representable policy p fid_pre e ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ”
  &&  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  (cm_struct_list_rep zs (cm_program_structs (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  (cm_global_list_rep zg (cm_program_globals (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_expr_rep expr_pre e )
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> zt)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_string_list_rep zt (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
.

Definition cm_expr_rvalue_count_context_partial_solve_wit_1 := cm_expr_rvalue_count_context_partial_solve_wit_1_pure -> cm_expr_rvalue_count_context_partial_solve_wit_1_aux.

(*----- Function cm_stmt_code_count_context -----*)

Definition cm_stmt_code_count_context_entail_wit_1 := 
(
forall (stmt_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (functions_ptr: Z) (next: Z) (body: Z) (loop_: bool) (s: cm_stmt) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH3 : (cm_stmt_wf policy p f loop_ s )) (PreH4 : (cm_stmt_counts_representable policy p fid_pre s )) (PreH5 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_stmt_rep stmt_pre s )
|--
  EX (zl: Z)  (zp: Z)  (zt: Z)  (zg: Z)  (zs: Z) ,
  “ (program_pre <> 0) ” 
  &&  “ (fn_pre <> 0) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_stmt_wf policy p f loop_ s ) ” 
  &&  “ (cm_stmt_counts_representable policy p fid_pre s ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ”
  &&  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> zt)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep zs (cm_program_structs (p)) )
  **  (cm_global_list_rep zg (cm_program_globals (p)) )
  **  (cm_string_list_rep zt (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_stmt_rep stmt_pre s )
) \/
(
forall (stmt_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (functions_ptr: Z) (next: Z) (body: Z) (loop_: bool) (s: cm_stmt) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH3 : (cm_stmt_wf policy p f loop_ s )) (PreH4 : (cm_stmt_counts_representable policy p fid_pre s )) (PreH5 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_stmt_rep stmt_pre s )
|--
  EX (zl: Z)  (zp: Z)  (zt: Z)  (zg: Z)  (zs: Z) ,
  “ (program_pre <> 0) ” 
  &&  “ (fn_pre <> 0) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_stmt_wf policy p f loop_ s ) ” 
  &&  “ (cm_stmt_counts_representable policy p fid_pre s ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ”
  &&  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> zt)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep zs (cm_program_structs (p)) )
  **  (cm_global_list_rep zg (cm_program_globals (p)) )
  **  (cm_string_list_rep zt (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_stmt_rep stmt_pre s )
).

Definition cm_stmt_code_count_context_return_wit_1 := 
(
forall (stmt_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (functions_ptr: Z) (next: Z) (body: Z) (loop_: bool) (s: cm_stmt) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (zs: Z) (zg: Z) (zt: Z) (zp: Z) (zl: Z) (retval: Z) (PreH1 : (cm_wf_program policy cg p )) (PreH2 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH3 : ((cm_program_structs (p)) = (cm_program_structs (p)))) (PreH4 : ((cm_program_globals (p)) = (cm_program_globals (p)))) (PreH5 : ((cm_function_locals (f)) = (cm_function_locals (f)))) (PreH6 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH7 : (cm_stmt_wf policy p f loop_ s )) (PreH8 : (cm_stmt_counts_representable policy p fid_pre s )) (PreH9 : (retval = (cm_stmt_code_count (policy) (p) (fid_pre) (s)))) (PreH10 : (cm_i32_code_count (cm_stmt_code_count (policy) (p) (fid_pre) (s)) )) (PreH11 : (program_pre <> 0)) (PreH12 : (fn_pre <> 0)) (PreH13 : (cm_wf_program policy cg p )) (PreH14 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH15 : (cm_stmt_wf policy p f loop_ s )) (PreH16 : (cm_stmt_counts_representable policy p fid_pre s )) (PreH17 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  (cm_struct_list_rep zs (cm_program_structs (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  (cm_global_list_rep zg (cm_program_globals (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  (cm_stmt_rep stmt_pre s )
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> zt)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_string_list_rep zt (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_stmt_wf policy p f loop_ s ) ” 
  &&  “ (cm_stmt_counts_representable policy p fid_pre s ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (retval = (cm_stmt_code_count (policy) (p) (fid_pre) (s))) ” 
  &&  “ (cm_i32_code_count retval ) ”
  &&  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_stmt_rep stmt_pre s )
) \/
(
forall (stmt_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (functions_ptr: Z) (next: Z) (body: Z) (loop_: bool) (s: cm_stmt) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (zs: Z) (zg: Z) (zt: Z) (zp: Z) (zl: Z) (retval: Z) (PreH1 : ((cm_program_main (p)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_function_ret (f)))) <= INT_MAX)) (PreH3 : ((cm_program_main (p)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_function_ret (f)))) >= INT_MIN)) (PreH5 : (cm_wf_program policy cg p )) (PreH6 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH7 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH8 : (cm_stmt_wf policy p f loop_ s )) (PreH9 : (cm_stmt_counts_representable policy p fid_pre s )) (PreH10 : (retval = (cm_stmt_code_count (policy) (p) (fid_pre) (s)))) (PreH11 : (cm_i32_code_count (cm_stmt_code_count (policy) (p) (fid_pre) (s)) )) (PreH12 : (program_pre <> 0)) (PreH13 : (fn_pre <> 0)) (PreH14 : (cm_wf_program policy cg p )) (PreH15 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH16 : (cm_stmt_wf policy p f loop_ s )) (PreH17 : (cm_stmt_counts_representable policy p fid_pre s )) (PreH18 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  (cm_struct_list_rep zs (cm_program_structs (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  (cm_global_list_rep zg (cm_program_globals (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  (cm_stmt_rep stmt_pre s )
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> zt)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_string_list_rep zt (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_stmt_rep stmt_pre s )
).

Definition cm_stmt_code_count_context_return_wit_1_split_goal_spatial := 
forall (stmt_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (functions_ptr: Z) (next: Z) (body: Z) (loop_: bool) (s: cm_stmt) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (zs: Z) (zg: Z) (zt: Z) (zp: Z) (zl: Z) (retval: Z) (PreH1 : ((cm_program_main (p)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_function_ret (f)))) <= INT_MAX)) (PreH3 : ((cm_program_main (p)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_function_ret (f)))) >= INT_MIN)) (PreH5 : (cm_wf_program policy cg p )) (PreH6 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH7 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH8 : (cm_stmt_wf policy p f loop_ s )) (PreH9 : (cm_stmt_counts_representable policy p fid_pre s )) (PreH10 : (retval = (cm_stmt_code_count (policy) (p) (fid_pre) (s)))) (PreH11 : (cm_i32_code_count (cm_stmt_code_count (policy) (p) (fid_pre) (s)) )) (PreH12 : (program_pre <> 0)) (PreH13 : (fn_pre <> 0)) (PreH14 : (cm_wf_program policy cg p )) (PreH15 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH16 : (cm_stmt_wf policy p f loop_ s )) (PreH17 : (cm_stmt_counts_representable policy p fid_pre s )) (PreH18 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  (cm_struct_list_rep zs (cm_program_structs (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  (cm_global_list_rep zg (cm_program_globals (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  (cm_stmt_rep stmt_pre s )
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> zt)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_string_list_rep zt (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
|--
  (cm_program_context_rep program_pre p functions_ptr )
  **  (cm_function_context_rep fn_pre f body next )
  **  (cm_stmt_rep stmt_pre s )
.

Definition cm_stmt_code_count_context_partial_solve_wit_1_pure := 
forall (stmt_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (functions_ptr: Z) (next: Z) (body: Z) (loop_: bool) (s: cm_stmt) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (zs: Z) (zg: Z) (zt: Z) (zp: Z) (zl: Z) (PreH1 : (program_pre <> 0)) (PreH2 : (fn_pre <> 0)) (PreH3 : (cm_wf_program policy cg p )) (PreH4 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH5 : (cm_stmt_wf policy p f loop_ s )) (PreH6 : (cm_stmt_counts_representable policy p fid_pre s )) (PreH7 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "stmt" ) )) # Ptr  |-> stmt_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> zt)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep zs (cm_program_structs (p)) )
  **  (cm_global_list_rep zg (cm_program_globals (p)) )
  **  (cm_string_list_rep zt (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_stmt_rep stmt_pre s )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ ((cm_program_structs (p)) = (cm_program_structs (p))) ” 
  &&  “ ((cm_program_globals (p)) = (cm_program_globals (p))) ” 
  &&  “ ((cm_function_locals (f)) = (cm_function_locals (f))) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_stmt_wf policy p f loop_ s ) ” 
  &&  “ (cm_stmt_counts_representable policy p fid_pre s ) ”
.

Definition cm_stmt_code_count_context_partial_solve_wit_1_aux := 
forall (stmt_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (functions_ptr: Z) (next: Z) (body: Z) (loop_: bool) (s: cm_stmt) (f: cm_function_d) (p: cm_program) (cg: cm_codegen_obligations) (policy: cm_lookup_policy) (zs: Z) (zg: Z) (zt: Z) (zp: Z) (zl: Z) (PreH1 : (program_pre <> 0)) (PreH2 : (fn_pre <> 0)) (PreH3 : (cm_wf_program policy cg p )) (PreH4 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH5 : (cm_stmt_wf policy p f loop_ s )) (PreH6 : (cm_stmt_counts_representable policy p fid_pre s )) (PreH7 : (cm_rep_structs_safe (cm_program_structs (p)) )) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> zt)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_struct_list_rep zs (cm_program_structs (p)) )
  **  (cm_global_list_rep zg (cm_program_globals (p)) )
  **  (cm_string_list_rep zt (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  (cm_stmt_rep stmt_pre s )
|--
  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ ((cm_program_structs (p)) = (cm_program_structs (p))) ” 
  &&  “ ((cm_program_globals (p)) = (cm_program_globals (p))) ” 
  &&  “ ((cm_function_locals (f)) = (cm_function_locals (f))) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (cm_stmt_wf policy p f loop_ s ) ” 
  &&  “ (cm_stmt_counts_representable policy p fid_pre s ) ” 
  &&  “ (program_pre <> 0) ” 
  &&  “ (fn_pre <> 0) ” 
  &&  “ (cm_wf_program policy cg p ) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_stmt_wf policy p f loop_ s ) ” 
  &&  “ (cm_stmt_counts_representable policy p fid_pre s ) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ”
  &&  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  (cm_struct_list_rep zs (cm_program_structs (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  (cm_global_list_rep zg (cm_program_globals (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl (cm_function_locals (f)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "ret_ty")) # Int  |-> (cm_type_encode ((cm_function_ret (f)))))
  **  (cm_stmt_rep stmt_pre s )
  **  ((&((program_pre)  # "cm_program" ->ₛ "strings")) # Ptr  |-> zt)
  **  ((&((program_pre)  # "cm_program" ->ₛ "functions")) # Ptr  |-> functions_ptr)
  **  ((&((program_pre)  # "cm_program" ->ₛ "main_id")) # Int  |-> (cm_program_main (p)))
  **  (cm_string_list_rep zt (cm_program_strings (p)) )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> body)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "next")) # Ptr  |-> next)
  **  (cm_slot_list_rep zp (cm_function_params (f)) )
.

Definition cm_stmt_code_count_context_partial_solve_wit_1 := cm_stmt_code_count_context_partial_solve_wit_1_pure -> cm_stmt_code_count_context_partial_solve_wit_1_aux.

Module Type VC_Correct.


Axiom proof_of_cm_expr_type_code_context_entail_wit_1 : cm_expr_type_code_context_entail_wit_1.
Axiom proof_of_cm_expr_type_code_context_return_wit_1 : cm_expr_type_code_context_return_wit_1.
Axiom proof_of_cm_expr_lvalue_count_context_entail_wit_1 : cm_expr_lvalue_count_context_entail_wit_1.
Axiom proof_of_cm_expr_lvalue_count_context_return_wit_1 : cm_expr_lvalue_count_context_return_wit_1.
Axiom proof_of_cm_expr_lvalue_count_context_partial_solve_wit_1_pure : cm_expr_lvalue_count_context_partial_solve_wit_1_pure.
Axiom proof_of_cm_expr_lvalue_count_context_partial_solve_wit_1 : cm_expr_lvalue_count_context_partial_solve_wit_1.
Axiom proof_of_cm_expr_rvalue_count_context_entail_wit_1 : cm_expr_rvalue_count_context_entail_wit_1.
Axiom proof_of_cm_expr_rvalue_count_context_return_wit_1 : cm_expr_rvalue_count_context_return_wit_1.
Axiom proof_of_cm_expr_rvalue_count_context_partial_solve_wit_1_pure : cm_expr_rvalue_count_context_partial_solve_wit_1_pure.
Axiom proof_of_cm_expr_rvalue_count_context_partial_solve_wit_1 : cm_expr_rvalue_count_context_partial_solve_wit_1.
Axiom proof_of_cm_stmt_code_count_context_entail_wit_1 : cm_stmt_code_count_context_entail_wit_1.
Axiom proof_of_cm_stmt_code_count_context_return_wit_1 : cm_stmt_code_count_context_return_wit_1.
Axiom proof_of_cm_stmt_code_count_context_partial_solve_wit_1_pure : cm_stmt_code_count_context_partial_solve_wit_1_pure.
Axiom proof_of_cm_stmt_code_count_context_partial_solve_wit_1 : cm_stmt_code_count_context_partial_solve_wit_1.

End VC_Correct.
