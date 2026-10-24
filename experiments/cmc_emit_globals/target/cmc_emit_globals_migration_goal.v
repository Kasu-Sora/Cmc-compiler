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
Require Import SimpleC.EE.QCP_demos_human.cmc_emit_globals_migration_lib.
Local Open Scope sac.

(*----- Function cmc_emit_globals -----*)

Definition cmc_emit_globals_safety_wit_1 := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (PreH1 : (cm_rep_globals_safe globals )) (PreH2 : (cm_data_globals_wf structs globals )) (PreH3 : (0 <= cursor_pre)) (PreH4 : ((cursor_pre + (cm_rep_globals_size (globals)) ) <= capacity_pre)) (PreH5 : (capacity_pre <= INT_MAX)) ,
  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (cm_global_list_rep node_pre globals )
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_emit_globals_safety_wit_2 := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (PreH1 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH2 : (node_pre <> 0)) (PreH3 : (globals = (cons (head) (tail)))) (PreH4 : (cm_rep_globals_safe globals )) (PreH5 : (cm_data_globals_wf structs globals )) (PreH6 : (cm_rep_globals_safe tail )) (PreH7 : (cm_data_globals_wf structs tail )) (PreH8 : (cm_global_wf structs head )) (PreH9 : (0 <= cursor_pre)) (PreH10 : (capacity_pre <= INT_MAX)) (PreH11 : (0 <= (cm_rep_global_size (head)))) (PreH12 : ((cm_rep_global_size (head)) <= 1048560)) (PreH13 : (0 <= (cm_rep_globals_size (tail)))) (PreH14 : (((cursor_pre + (cm_rep_global_size (head)) ) + (cm_rep_globals_size (tail)) ) <= capacity_pre)) (PreH15 : ((cm_rep_bool ((cm_global_has_init (head)))) <> 0)) ,
  ((( &( "size" ) )) # Int  |-> (signed_last_nbits (retval) (32)))
  **  ((( &( "size64" ) )) # Int64  |-> retval)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "init_value" ) )) # Int64  |-> (cm_global_init (head)))
  **  ((( &( "has_init" ) )) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((( &( "count" ) )) # Int  |-> (cm_global_count (head)))
  **  ((( &( "type_code" ) )) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmc_emit_globals_safety_wit_3 := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (type_code: Z) (count: Z) (has_init: Z) (init_value: Z) (size64: Z) (size: Z) (PreH1 : (node_pre <> 0)) (PreH2 : (globals = (cons (head) (tail)))) (PreH3 : (cm_rep_globals_safe globals )) (PreH4 : (cm_data_globals_wf structs globals )) (PreH5 : (cm_rep_globals_safe tail )) (PreH6 : (cm_data_globals_wf structs tail )) (PreH7 : (cm_global_wf structs head )) (PreH8 : (0 <= cursor_pre)) (PreH9 : (capacity_pre <= INT_MAX)) (PreH10 : (0 <= (cm_rep_global_size (head)))) (PreH11 : ((cm_rep_global_size (head)) <= 1048560)) (PreH12 : (0 <= (cm_rep_globals_size (tail)))) (PreH13 : (((cursor_pre + (cm_rep_global_size (head)) ) + (cm_rep_globals_size (tail)) ) <= capacity_pre)) (PreH14 : (type_code = (cm_type_encode ((cm_global_ty (head)))))) (PreH15 : (count = (cm_global_count (head)))) (PreH16 : (has_init = (cm_rep_bool ((cm_global_has_init (head)))))) (PreH17 : (init_value = (cm_global_init (head)))) (PreH18 : (size64 = (cm_rep_global_size (head)))) (PreH19 : (size = (cm_rep_global_size (head)))) ,
  ((( &( "final_cursor" ) )) # Int  |->_)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "type_code" ) )) # Int  |-> type_code)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "has_init" ) )) # Int  |-> has_init)
  **  ((( &( "init_value" ) )) # Int64  |-> init_value)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size64" ) )) # Int64  |-> size64)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
  **  (UCharArray.seg data_pre 0 (cursor_pre + size ) (app (prefix) ((cm_global_bytes (structs) (head)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + size ) capacity_pre )
|--
  “ ((cursor_pre + size ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cursor_pre + size )) ”
.

Definition cmc_emit_globals_entail_wit_1 := 
(
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (PreH1 : (node_pre <> 0)) (PreH2 : (cm_rep_globals_safe globals )) (PreH3 : (cm_data_globals_wf structs globals )) (PreH4 : (0 <= cursor_pre)) (PreH5 : ((cursor_pre + (cm_rep_globals_size (globals)) ) <= capacity_pre)) (PreH6 : (capacity_pre <= INT_MAX)) ,
  (cm_global_list_rep node_pre globals )
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  EX (nextp: Z)  (head: cm_global_d)  (tail: (@list cm_global_d)) ,
  “ (node_pre <> 0) ” 
  &&  “ (globals = (cons (head) (tail))) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_data_globals_wf structs globals ) ” 
  &&  “ (cm_rep_globals_safe tail ) ” 
  &&  “ (cm_data_globals_wf structs tail ) ” 
  &&  “ (cm_global_wf structs head ) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ (0 <= (cm_rep_global_size (head))) ” 
  &&  “ ((cm_rep_global_size (head)) <= 1048560) ” 
  &&  “ (0 <= (cm_rep_globals_size (tail))) ” 
  &&  “ (((cursor_pre + (cm_rep_global_size (head)) ) + (cm_rep_globals_size (tail)) ) <= capacity_pre) ”
  &&  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
) \/
(
forall (cursor_pre: Z) (capacity_pre: Z) (node_pre: Z) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (PreH1 : (node_pre <> 0)) (PreH2 : (cm_rep_globals_safe globals )) (PreH3 : (cm_data_globals_wf structs globals )) (PreH4 : (0 <= cursor_pre)) (PreH5 : ((cursor_pre + (cm_rep_globals_size (globals)) ) <= capacity_pre)) (PreH6 : (capacity_pre <= INT_MAX)) ,
  (cm_global_list_rep node_pre globals )
|--
  EX (nextp: Z)  (head: cm_global_d)  (tail: (@list cm_global_d)) ,
  “ (node_pre <> 0) ” 
  &&  “ (globals = (cons (head) (tail))) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_data_globals_wf structs globals ) ” 
  &&  “ (cm_rep_globals_safe tail ) ” 
  &&  “ (cm_data_globals_wf structs tail ) ” 
  &&  “ (cm_global_wf structs head ) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ (0 <= (cm_rep_global_size (head))) ” 
  &&  “ ((cm_rep_global_size (head)) <= 1048560) ” 
  &&  “ (0 <= (cm_rep_globals_size (tail))) ” 
  &&  “ (((cursor_pre + (cm_rep_global_size (head)) ) + (cm_rep_globals_size (tail)) ) <= capacity_pre) ”
  &&  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
).

Definition cmc_emit_globals_entail_wit_2_1 := 
(
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (head: cm_global_d) (tail_2: (@list cm_global_d)) (nextp: Z) (retval: Z) (PreH1 : ((cm_type_encode ((cm_global_ty (head)))) = 1)) (PreH2 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH3 : (node_pre <> 0)) (PreH4 : (globals = (cons (head) (tail_2)))) (PreH5 : (cm_rep_globals_safe globals )) (PreH6 : (cm_data_globals_wf structs globals )) (PreH7 : (cm_rep_globals_safe tail_2 )) (PreH8 : (cm_data_globals_wf structs tail_2 )) (PreH9 : (cm_global_wf structs head )) (PreH10 : (0 <= cursor_pre)) (PreH11 : (capacity_pre <= INT_MAX)) (PreH12 : (0 <= (cm_rep_global_size (head)))) (PreH13 : ((cm_rep_global_size (head)) <= 1048560)) (PreH14 : (0 <= (cm_rep_globals_size (tail_2)))) (PreH15 : (((cursor_pre + (cm_rep_global_size (head)) ) + (cm_rep_globals_size (tail_2)) ) <= capacity_pre)) (PreH16 : ((cm_rep_bool ((cm_global_has_init (head)))) <> 0)) ,
  (UCharArray.seg data_pre 0 (cursor_pre + 1 ) (app (prefix) ((cons ((tower_u8 ((cm_global_init (head))))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 1 ) capacity_pre )
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail_2 )
|--
  EX (head_2: cm_global_d)  (tail: (@list cm_global_d)) ,
  “ (node_pre <> 0) ” 
  &&  “ (globals = (cons (head_2) (tail))) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_data_globals_wf structs globals ) ” 
  &&  “ (cm_rep_globals_safe tail ) ” 
  &&  “ (cm_data_globals_wf structs tail ) ” 
  &&  “ (cm_global_wf structs head_2 ) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ (0 <= (cm_rep_global_size (head_2))) ” 
  &&  “ ((cm_rep_global_size (head_2)) <= 1048560) ” 
  &&  “ (0 <= (cm_rep_globals_size (tail))) ” 
  &&  “ (((cursor_pre + (cm_rep_global_size (head_2)) ) + (cm_rep_globals_size (tail)) ) <= capacity_pre) ” 
  &&  “ ((cm_type_encode ((cm_global_ty (head)))) = (cm_type_encode ((cm_global_ty (head_2))))) ” 
  &&  “ ((cm_global_count (head)) = (cm_global_count (head_2))) ” 
  &&  “ ((cm_rep_bool ((cm_global_has_init (head)))) = (cm_rep_bool ((cm_global_has_init (head_2))))) ” 
  &&  “ ((cm_global_init (head)) = (cm_global_init (head_2))) ” 
  &&  “ (retval = (cm_rep_global_size (head_2))) ” 
  &&  “ ((signed_last_nbits (retval) (32)) = (cm_rep_global_size (head_2))) ”
  &&  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head_2)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head_2)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head_2)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head_2)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
  **  (UCharArray.seg data_pre 0 (cursor_pre + (signed_last_nbits (retval) (32)) ) (app (prefix) ((cm_global_bytes (structs) (head_2)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + (signed_last_nbits (retval) (32)) ) capacity_pre )
) \/
(
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (head: cm_global_d) (tail_2: (@list cm_global_d)) (nextp: Z) (retval: Z) (PreH1 : ((cm_type_encode ((cm_global_ty (head)))) = 1)) (PreH2 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH3 : (node_pre <> 0)) (PreH4 : (globals = (cons (head) (tail_2)))) (PreH5 : (cm_rep_globals_safe globals )) (PreH6 : (cm_data_globals_wf structs globals )) (PreH7 : (cm_rep_globals_safe tail_2 )) (PreH8 : (cm_data_globals_wf structs tail_2 )) (PreH9 : (cm_global_wf structs head )) (PreH10 : (0 <= cursor_pre)) (PreH11 : (capacity_pre <= INT_MAX)) (PreH12 : (0 <= (cm_rep_global_size (head)))) (PreH13 : ((cm_rep_global_size (head)) <= 1048560)) (PreH14 : (0 <= (cm_rep_globals_size (tail_2)))) (PreH15 : (((cursor_pre + (cm_rep_global_size (head)) ) + (cm_rep_globals_size (tail_2)) ) <= capacity_pre)) (PreH16 : ((cm_rep_bool ((cm_global_has_init (head)))) <> 0)) ,
  (UCharArray.seg data_pre 0 (cursor_pre + 1 ) (app (prefix) ((cons ((tower_u8 ((cm_global_init (head))))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 1 ) capacity_pre )
  **  (cm_global_list_rep nextp tail_2 )
|--
  EX (head_2: cm_global_d)  (tail: (@list cm_global_d)) ,
  “ ((cm_global_init (head)) = (cm_global_init (head_2))) ” 
  &&  “ ((cm_rep_bool ((cm_global_has_init (head)))) = (cm_rep_bool ((cm_global_has_init (head_2))))) ” 
  &&  “ ((cm_global_count (head)) = (cm_global_count (head_2))) ” 
  &&  “ ((cm_type_encode ((cm_global_ty (head)))) = (cm_type_encode ((cm_global_ty (head_2))))) ” 
  &&  “ (node_pre <> 0) ” 
  &&  “ (globals = (cons (head_2) (tail))) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_data_globals_wf structs globals ) ” 
  &&  “ (cm_rep_globals_safe tail ) ” 
  &&  “ (cm_data_globals_wf structs tail ) ” 
  &&  “ (cm_global_wf structs head_2 ) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ (0 <= (cm_rep_global_size (head_2))) ” 
  &&  “ ((cm_rep_global_size (head_2)) <= 1048560) ” 
  &&  “ (0 <= (cm_rep_globals_size (tail))) ” 
  &&  “ (((cursor_pre + (cm_rep_global_size (head_2)) ) + (cm_rep_globals_size (tail)) ) <= capacity_pre) ” 
  &&  “ ((cm_type_encode ((cm_global_ty (head)))) = (cm_type_encode ((cm_global_ty (head_2))))) ” 
  &&  “ ((cm_global_count (head)) = (cm_global_count (head_2))) ” 
  &&  “ ((cm_rep_bool ((cm_global_has_init (head)))) = (cm_rep_bool ((cm_global_has_init (head_2))))) ” 
  &&  “ ((cm_global_init (head)) = (cm_global_init (head_2))) ” 
  &&  “ (retval = (cm_rep_global_size (head_2))) ” 
  &&  “ ((signed_last_nbits (retval) (32)) = (cm_rep_global_size (head_2))) ”
  &&  (cm_global_list_rep nextp tail )
  **  (UCharArray.seg data_pre 0 (cursor_pre + (signed_last_nbits (retval) (32)) ) (app (prefix) ((cm_global_bytes (structs) (head_2)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + (signed_last_nbits (retval) (32)) ) capacity_pre )
).

Definition cmc_emit_globals_entail_wit_2_2 := 
(
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (head: cm_global_d) (tail_2: (@list cm_global_d)) (nextp: Z) (retval: Z) (PreH1 : ((cm_type_encode ((cm_global_ty (head)))) <> 1)) (PreH2 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH3 : (node_pre <> 0)) (PreH4 : (globals = (cons (head) (tail_2)))) (PreH5 : (cm_rep_globals_safe globals )) (PreH6 : (cm_data_globals_wf structs globals )) (PreH7 : (cm_rep_globals_safe tail_2 )) (PreH8 : (cm_data_globals_wf structs tail_2 )) (PreH9 : (cm_global_wf structs head )) (PreH10 : (0 <= cursor_pre)) (PreH11 : (capacity_pre <= INT_MAX)) (PreH12 : (0 <= (cm_rep_global_size (head)))) (PreH13 : ((cm_rep_global_size (head)) <= 1048560)) (PreH14 : (0 <= (cm_rep_globals_size (tail_2)))) (PreH15 : (((cursor_pre + (cm_rep_global_size (head)) ) + (cm_rep_globals_size (tail_2)) ) <= capacity_pre)) (PreH16 : ((cm_rep_bool ((cm_global_has_init (head)))) <> 0)) ,
  (UCharArray.seg data_pre 0 (cursor_pre + 8 ) (app (prefix) ((tower_word_bytes ((cm_global_init (head)))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 8 ) capacity_pre )
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail_2 )
|--
  EX (head_2: cm_global_d)  (tail: (@list cm_global_d)) ,
  “ (node_pre <> 0) ” 
  &&  “ (globals = (cons (head_2) (tail))) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_data_globals_wf structs globals ) ” 
  &&  “ (cm_rep_globals_safe tail ) ” 
  &&  “ (cm_data_globals_wf structs tail ) ” 
  &&  “ (cm_global_wf structs head_2 ) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ (0 <= (cm_rep_global_size (head_2))) ” 
  &&  “ ((cm_rep_global_size (head_2)) <= 1048560) ” 
  &&  “ (0 <= (cm_rep_globals_size (tail))) ” 
  &&  “ (((cursor_pre + (cm_rep_global_size (head_2)) ) + (cm_rep_globals_size (tail)) ) <= capacity_pre) ” 
  &&  “ ((cm_type_encode ((cm_global_ty (head)))) = (cm_type_encode ((cm_global_ty (head_2))))) ” 
  &&  “ ((cm_global_count (head)) = (cm_global_count (head_2))) ” 
  &&  “ ((cm_rep_bool ((cm_global_has_init (head)))) = (cm_rep_bool ((cm_global_has_init (head_2))))) ” 
  &&  “ ((cm_global_init (head)) = (cm_global_init (head_2))) ” 
  &&  “ (retval = (cm_rep_global_size (head_2))) ” 
  &&  “ ((signed_last_nbits (retval) (32)) = (cm_rep_global_size (head_2))) ”
  &&  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head_2)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head_2)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head_2)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head_2)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
  **  (UCharArray.seg data_pre 0 (cursor_pre + (signed_last_nbits (retval) (32)) ) (app (prefix) ((cm_global_bytes (structs) (head_2)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + (signed_last_nbits (retval) (32)) ) capacity_pre )
) \/
(
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (head: cm_global_d) (tail_2: (@list cm_global_d)) (nextp: Z) (retval: Z) (PreH1 : ((cm_type_encode ((cm_global_ty (head)))) <> 1)) (PreH2 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH3 : (node_pre <> 0)) (PreH4 : (globals = (cons (head) (tail_2)))) (PreH5 : (cm_rep_globals_safe globals )) (PreH6 : (cm_data_globals_wf structs globals )) (PreH7 : (cm_rep_globals_safe tail_2 )) (PreH8 : (cm_data_globals_wf structs tail_2 )) (PreH9 : (cm_global_wf structs head )) (PreH10 : (0 <= cursor_pre)) (PreH11 : (capacity_pre <= INT_MAX)) (PreH12 : (0 <= (cm_rep_global_size (head)))) (PreH13 : ((cm_rep_global_size (head)) <= 1048560)) (PreH14 : (0 <= (cm_rep_globals_size (tail_2)))) (PreH15 : (((cursor_pre + (cm_rep_global_size (head)) ) + (cm_rep_globals_size (tail_2)) ) <= capacity_pre)) (PreH16 : ((cm_rep_bool ((cm_global_has_init (head)))) <> 0)) ,
  (UCharArray.seg data_pre 0 (cursor_pre + 8 ) (app (prefix) ((tower_word_bytes ((cm_global_init (head)))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 8 ) capacity_pre )
  **  (cm_global_list_rep nextp tail_2 )
|--
  EX (head_2: cm_global_d)  (tail: (@list cm_global_d)) ,
  “ ((cm_global_init (head)) = (cm_global_init (head_2))) ” 
  &&  “ ((cm_rep_bool ((cm_global_has_init (head)))) = (cm_rep_bool ((cm_global_has_init (head_2))))) ” 
  &&  “ ((cm_global_count (head)) = (cm_global_count (head_2))) ” 
  &&  “ ((cm_type_encode ((cm_global_ty (head)))) = (cm_type_encode ((cm_global_ty (head_2))))) ” 
  &&  “ (node_pre <> 0) ” 
  &&  “ (globals = (cons (head_2) (tail))) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_data_globals_wf structs globals ) ” 
  &&  “ (cm_rep_globals_safe tail ) ” 
  &&  “ (cm_data_globals_wf structs tail ) ” 
  &&  “ (cm_global_wf structs head_2 ) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ (0 <= (cm_rep_global_size (head_2))) ” 
  &&  “ ((cm_rep_global_size (head_2)) <= 1048560) ” 
  &&  “ (0 <= (cm_rep_globals_size (tail))) ” 
  &&  “ (((cursor_pre + (cm_rep_global_size (head_2)) ) + (cm_rep_globals_size (tail)) ) <= capacity_pre) ” 
  &&  “ ((cm_type_encode ((cm_global_ty (head)))) = (cm_type_encode ((cm_global_ty (head_2))))) ” 
  &&  “ ((cm_global_count (head)) = (cm_global_count (head_2))) ” 
  &&  “ ((cm_rep_bool ((cm_global_has_init (head)))) = (cm_rep_bool ((cm_global_has_init (head_2))))) ” 
  &&  “ ((cm_global_init (head)) = (cm_global_init (head_2))) ” 
  &&  “ (retval = (cm_rep_global_size (head_2))) ” 
  &&  “ ((signed_last_nbits (retval) (32)) = (cm_rep_global_size (head_2))) ”
  &&  (cm_global_list_rep nextp tail )
  **  (UCharArray.seg data_pre 0 (cursor_pre + (signed_last_nbits (retval) (32)) ) (app (prefix) ((cm_global_bytes (structs) (head_2)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + (signed_last_nbits (retval) (32)) ) capacity_pre )
).

Definition cmc_emit_globals_entail_wit_2_3 := 
(
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (head: cm_global_d) (tail_2: (@list cm_global_d)) (nextp: Z) (retval: Z) (PreH1 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH2 : (node_pre <> 0)) (PreH3 : (globals = (cons (head) (tail_2)))) (PreH4 : (cm_rep_globals_safe globals )) (PreH5 : (cm_data_globals_wf structs globals )) (PreH6 : (cm_rep_globals_safe tail_2 )) (PreH7 : (cm_data_globals_wf structs tail_2 )) (PreH8 : (cm_global_wf structs head )) (PreH9 : (0 <= cursor_pre)) (PreH10 : (capacity_pre <= INT_MAX)) (PreH11 : (0 <= (cm_rep_global_size (head)))) (PreH12 : ((cm_rep_global_size (head)) <= 1048560)) (PreH13 : (0 <= (cm_rep_globals_size (tail_2)))) (PreH14 : (((cursor_pre + (cm_rep_global_size (head)) ) + (cm_rep_globals_size (tail_2)) ) <= capacity_pre)) (PreH15 : ((cm_rep_bool ((cm_global_has_init (head)))) = 0)) ,
  (UCharArray.seg data_pre 0 (cursor_pre + (signed_last_nbits (retval) (32)) ) (app (prefix) ((zeros ((signed_last_nbits (retval) (32)))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + (signed_last_nbits (retval) (32)) ) capacity_pre )
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail_2 )
|--
  EX (head_2: cm_global_d)  (tail: (@list cm_global_d)) ,
  “ (node_pre <> 0) ” 
  &&  “ (globals = (cons (head_2) (tail))) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_data_globals_wf structs globals ) ” 
  &&  “ (cm_rep_globals_safe tail ) ” 
  &&  “ (cm_data_globals_wf structs tail ) ” 
  &&  “ (cm_global_wf structs head_2 ) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ (0 <= (cm_rep_global_size (head_2))) ” 
  &&  “ ((cm_rep_global_size (head_2)) <= 1048560) ” 
  &&  “ (0 <= (cm_rep_globals_size (tail))) ” 
  &&  “ (((cursor_pre + (cm_rep_global_size (head_2)) ) + (cm_rep_globals_size (tail)) ) <= capacity_pre) ” 
  &&  “ ((cm_type_encode ((cm_global_ty (head)))) = (cm_type_encode ((cm_global_ty (head_2))))) ” 
  &&  “ ((cm_global_count (head)) = (cm_global_count (head_2))) ” 
  &&  “ ((cm_rep_bool ((cm_global_has_init (head)))) = (cm_rep_bool ((cm_global_has_init (head_2))))) ” 
  &&  “ ((cm_global_init (head)) = (cm_global_init (head_2))) ” 
  &&  “ (retval = (cm_rep_global_size (head_2))) ” 
  &&  “ ((signed_last_nbits (retval) (32)) = (cm_rep_global_size (head_2))) ”
  &&  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head_2)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head_2)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head_2)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head_2)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
  **  (UCharArray.seg data_pre 0 (cursor_pre + (signed_last_nbits (retval) (32)) ) (app (prefix) ((cm_global_bytes (structs) (head_2)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + (signed_last_nbits (retval) (32)) ) capacity_pre )
) \/
(
forall (cursor_pre: Z) (capacity_pre: Z) (node_pre: Z) (prefix: (@list Z)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (head: cm_global_d) (tail_2: (@list cm_global_d)) (retval: Z) (PreH1 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH2 : (node_pre <> 0)) (PreH3 : (globals = (cons (head) (tail_2)))) (PreH4 : (cm_rep_globals_safe globals )) (PreH5 : (cm_data_globals_wf structs globals )) (PreH6 : (cm_rep_globals_safe tail_2 )) (PreH7 : (cm_data_globals_wf structs tail_2 )) (PreH8 : (cm_global_wf structs head )) (PreH9 : (0 <= cursor_pre)) (PreH10 : (capacity_pre <= INT_MAX)) (PreH11 : (0 <= (cm_rep_global_size (head)))) (PreH12 : ((cm_rep_global_size (head)) <= 1048560)) (PreH13 : (0 <= (cm_rep_globals_size (tail_2)))) (PreH14 : (((cursor_pre + (cm_rep_global_size (head)) ) + (cm_rep_globals_size (tail_2)) ) <= capacity_pre)) (PreH15 : ((cm_rep_bool ((cm_global_has_init (head)))) = 0)) ,
  TT && emp 
|--
  EX (head_2: cm_global_d) ,
  “ ((app (prefix) ((zeros ((signed_last_nbits ((cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head))))) (32)))))) = (app (prefix) ((cm_global_bytes (structs) (head_2))))) ” 
  &&  “ ((cm_global_init (head)) = (cm_global_init (head_2))) ” 
  &&  “ ((cm_rep_bool ((cm_global_has_init (head)))) = (cm_rep_bool ((cm_global_has_init (head_2))))) ” 
  &&  “ ((cm_global_count (head)) = (cm_global_count (head_2))) ” 
  &&  “ ((cm_type_encode ((cm_global_ty (head)))) = (cm_type_encode ((cm_global_ty (head_2))))) ” 
  &&  “ ((cons (head) (tail_2)) = (cons (head_2) (tail_2))) ” 
  &&  “ (cm_global_wf structs head_2 ) ” 
  &&  “ (0 <= (cm_rep_global_size (head_2))) ” 
  &&  “ ((cm_rep_global_size (head_2)) <= 1048560) ” 
  &&  “ (((cursor_pre + (cm_rep_global_size (head_2)) ) + (cm_rep_globals_size (tail_2)) ) <= capacity_pre) ” 
  &&  “ ((cm_type_encode ((cm_global_ty (head)))) = (cm_type_encode ((cm_global_ty (head_2))))) ” 
  &&  “ ((cm_global_count (head)) = (cm_global_count (head_2))) ” 
  &&  “ ((cm_rep_bool ((cm_global_has_init (head)))) = (cm_rep_bool ((cm_global_has_init (head_2))))) ” 
  &&  “ ((cm_global_init (head)) = (cm_global_init (head_2))) ” 
  &&  “ ((cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))) = (cm_rep_global_size (head_2))) ” 
  &&  “ ((signed_last_nbits ((cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head))))) (32)) = (cm_rep_global_size (head_2))) ”
  &&  emp
).

Definition cmc_emit_globals_return_wit_1 := 
(
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (type_code: Z) (count: Z) (has_init: Z) (init_value: Z) (size64: Z) (size: Z) (retval: Z) (PreH1 : (cm_rep_globals_safe tail )) (PreH2 : (cm_data_globals_wf structs tail )) (PreH3 : (retval = ((cursor_pre + size ) + (cm_rep_globals_size (tail)) ))) (PreH4 : (node_pre <> 0)) (PreH5 : (globals = (cons (head) (tail)))) (PreH6 : (cm_rep_globals_safe globals )) (PreH7 : (cm_data_globals_wf structs globals )) (PreH8 : (cm_rep_globals_safe tail )) (PreH9 : (cm_data_globals_wf structs tail )) (PreH10 : (cm_global_wf structs head )) (PreH11 : (0 <= cursor_pre)) (PreH12 : (capacity_pre <= INT_MAX)) (PreH13 : (0 <= (cm_rep_global_size (head)))) (PreH14 : ((cm_rep_global_size (head)) <= 1048560)) (PreH15 : (0 <= (cm_rep_globals_size (tail)))) (PreH16 : (((cursor_pre + (cm_rep_global_size (head)) ) + (cm_rep_globals_size (tail)) ) <= capacity_pre)) (PreH17 : (type_code = (cm_type_encode ((cm_global_ty (head)))))) (PreH18 : (count = (cm_global_count (head)))) (PreH19 : (has_init = (cm_rep_bool ((cm_global_has_init (head)))))) (PreH20 : (init_value = (cm_global_init (head)))) (PreH21 : (size64 = (cm_rep_global_size (head)))) (PreH22 : (size = (cm_rep_global_size (head)))) ,
  (cm_global_list_rep nextp tail )
  **  (UCharArray.seg data_pre 0 ((cursor_pre + size ) + (cm_rep_globals_size (tail)) ) (app ((app (prefix) ((cm_global_bytes (structs) (head))))) ((cm_globals_bytes (structs) (tail)))) )
  **  (UCharArray.undef_seg data_pre ((cursor_pre + size ) + (cm_rep_globals_size (tail)) ) capacity_pre )
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_data_globals_wf structs globals ) ” 
  &&  “ (retval = (cursor_pre + (cm_rep_globals_size (globals)) )) ”
  &&  (cm_global_list_rep node_pre globals )
  **  (UCharArray.seg data_pre 0 (cursor_pre + (cm_rep_globals_size (globals)) ) (app (prefix) ((cm_globals_bytes (structs) (globals)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + (cm_rep_globals_size (globals)) ) capacity_pre )
) \/
(
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (type_code: Z) (count: Z) (has_init: Z) (init_value: Z) (size64: Z) (size: Z) (retval: Z) (PreH1 : ((cm_global_init (head)) <= INT64_MAX)) (PreH2 : ((cm_global_init (head)) >= INT64_MIN)) (PreH3 : ((cm_rep_bool ((cm_global_has_init (head)))) <= INT_MAX)) (PreH4 : ((cm_global_count (head)) <= INT_MAX)) (PreH5 : ((cm_type_encode ((cm_global_ty (head)))) <= INT_MAX)) (PreH6 : ((cm_rep_bool ((cm_global_has_init (head)))) >= INT_MIN)) (PreH7 : ((cm_global_count (head)) >= INT_MIN)) (PreH8 : ((cm_type_encode ((cm_global_ty (head)))) >= INT_MIN)) (PreH9 : (cm_rep_globals_safe tail )) (PreH10 : (cm_data_globals_wf structs tail )) (PreH11 : (retval = ((cursor_pre + size ) + (cm_rep_globals_size (tail)) ))) (PreH12 : (node_pre <> 0)) (PreH13 : (globals = (cons (head) (tail)))) (PreH14 : (cm_rep_globals_safe globals )) (PreH15 : (cm_data_globals_wf structs globals )) (PreH16 : (cm_rep_globals_safe tail )) (PreH17 : (cm_data_globals_wf structs tail )) (PreH18 : (cm_global_wf structs head )) (PreH19 : (0 <= cursor_pre)) (PreH20 : (capacity_pre <= INT_MAX)) (PreH21 : (0 <= (cm_rep_global_size (head)))) (PreH22 : ((cm_rep_global_size (head)) <= 1048560)) (PreH23 : (0 <= (cm_rep_globals_size (tail)))) (PreH24 : (((cursor_pre + (cm_rep_global_size (head)) ) + (cm_rep_globals_size (tail)) ) <= capacity_pre)) (PreH25 : (type_code = (cm_type_encode ((cm_global_ty (head)))))) (PreH26 : (count = (cm_global_count (head)))) (PreH27 : (has_init = (cm_rep_bool ((cm_global_has_init (head)))))) (PreH28 : (init_value = (cm_global_init (head)))) (PreH29 : (size64 = (cm_rep_global_size (head)))) (PreH30 : (size = (cm_rep_global_size (head)))) ,
  (cm_global_list_rep nextp tail )
  **  (UCharArray.seg data_pre 0 ((cursor_pre + size ) + (cm_rep_globals_size (tail)) ) (app ((app (prefix) ((cm_global_bytes (structs) (head))))) ((cm_globals_bytes (structs) (tail)))) )
  **  (UCharArray.undef_seg data_pre ((cursor_pre + size ) + (cm_rep_globals_size (tail)) ) capacity_pre )
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (retval = (cursor_pre + (cm_rep_globals_size (globals)) )) ”
  &&  (cm_global_list_rep node_pre globals )
  **  (UCharArray.seg data_pre 0 (cursor_pre + (cm_rep_globals_size (globals)) ) (app (prefix) ((cm_globals_bytes (structs) (globals)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + (cm_rep_globals_size (globals)) ) capacity_pre )
).

Definition cmc_emit_globals_return_wit_1_split_goal_1 := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (type_code: Z) (count: Z) (has_init: Z) (init_value: Z) (size64: Z) (size: Z) (retval: Z) (PreH1 : ((cm_global_init (head)) <= INT64_MAX)) (PreH2 : ((cm_global_init (head)) >= INT64_MIN)) (PreH3 : ((cm_rep_bool ((cm_global_has_init (head)))) <= INT_MAX)) (PreH4 : ((cm_global_count (head)) <= INT_MAX)) (PreH5 : ((cm_type_encode ((cm_global_ty (head)))) <= INT_MAX)) (PreH6 : ((cm_rep_bool ((cm_global_has_init (head)))) >= INT_MIN)) (PreH7 : ((cm_global_count (head)) >= INT_MIN)) (PreH8 : ((cm_type_encode ((cm_global_ty (head)))) >= INT_MIN)) (PreH9 : (cm_rep_globals_safe tail )) (PreH10 : (cm_data_globals_wf structs tail )) (PreH11 : (retval = ((cursor_pre + size ) + (cm_rep_globals_size (tail)) ))) (PreH12 : (node_pre <> 0)) (PreH13 : (globals = (cons (head) (tail)))) (PreH14 : (cm_rep_globals_safe globals )) (PreH15 : (cm_data_globals_wf structs globals )) (PreH16 : (cm_rep_globals_safe tail )) (PreH17 : (cm_data_globals_wf structs tail )) (PreH18 : (cm_global_wf structs head )) (PreH19 : (0 <= cursor_pre)) (PreH20 : (capacity_pre <= INT_MAX)) (PreH21 : (0 <= (cm_rep_global_size (head)))) (PreH22 : ((cm_rep_global_size (head)) <= 1048560)) (PreH23 : (0 <= (cm_rep_globals_size (tail)))) (PreH24 : (((cursor_pre + (cm_rep_global_size (head)) ) + (cm_rep_globals_size (tail)) ) <= capacity_pre)) (PreH25 : (type_code = (cm_type_encode ((cm_global_ty (head)))))) (PreH26 : (count = (cm_global_count (head)))) (PreH27 : (has_init = (cm_rep_bool ((cm_global_has_init (head)))))) (PreH28 : (init_value = (cm_global_init (head)))) (PreH29 : (size64 = (cm_rep_global_size (head)))) (PreH30 : (size = (cm_rep_global_size (head)))) ,
  (cm_global_list_rep nextp tail )
  **  (UCharArray.seg data_pre 0 ((cursor_pre + size ) + (cm_rep_globals_size (tail)) ) (app ((app (prefix) ((cm_global_bytes (structs) (head))))) ((cm_globals_bytes (structs) (tail)))) )
  **  (UCharArray.undef_seg data_pre ((cursor_pre + size ) + (cm_rep_globals_size (tail)) ) capacity_pre )
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (retval = (cursor_pre + (cm_rep_globals_size (globals)) )) ”
.

Definition cmc_emit_globals_return_wit_1_split_goal_spatial := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (type_code: Z) (count: Z) (has_init: Z) (init_value: Z) (size64: Z) (size: Z) (retval: Z) (PreH1 : ((cm_global_init (head)) <= INT64_MAX)) (PreH2 : ((cm_global_init (head)) >= INT64_MIN)) (PreH3 : ((cm_rep_bool ((cm_global_has_init (head)))) <= INT_MAX)) (PreH4 : ((cm_global_count (head)) <= INT_MAX)) (PreH5 : ((cm_type_encode ((cm_global_ty (head)))) <= INT_MAX)) (PreH6 : ((cm_rep_bool ((cm_global_has_init (head)))) >= INT_MIN)) (PreH7 : ((cm_global_count (head)) >= INT_MIN)) (PreH8 : ((cm_type_encode ((cm_global_ty (head)))) >= INT_MIN)) (PreH9 : (cm_rep_globals_safe tail )) (PreH10 : (cm_data_globals_wf structs tail )) (PreH11 : (retval = ((cursor_pre + size ) + (cm_rep_globals_size (tail)) ))) (PreH12 : (node_pre <> 0)) (PreH13 : (globals = (cons (head) (tail)))) (PreH14 : (cm_rep_globals_safe globals )) (PreH15 : (cm_data_globals_wf structs globals )) (PreH16 : (cm_rep_globals_safe tail )) (PreH17 : (cm_data_globals_wf structs tail )) (PreH18 : (cm_global_wf structs head )) (PreH19 : (0 <= cursor_pre)) (PreH20 : (capacity_pre <= INT_MAX)) (PreH21 : (0 <= (cm_rep_global_size (head)))) (PreH22 : ((cm_rep_global_size (head)) <= 1048560)) (PreH23 : (0 <= (cm_rep_globals_size (tail)))) (PreH24 : (((cursor_pre + (cm_rep_global_size (head)) ) + (cm_rep_globals_size (tail)) ) <= capacity_pre)) (PreH25 : (type_code = (cm_type_encode ((cm_global_ty (head)))))) (PreH26 : (count = (cm_global_count (head)))) (PreH27 : (has_init = (cm_rep_bool ((cm_global_has_init (head)))))) (PreH28 : (init_value = (cm_global_init (head)))) (PreH29 : (size64 = (cm_rep_global_size (head)))) (PreH30 : (size = (cm_rep_global_size (head)))) ,
  (cm_global_list_rep nextp tail )
  **  (UCharArray.seg data_pre 0 ((cursor_pre + size ) + (cm_rep_globals_size (tail)) ) (app ((app (prefix) ((cm_global_bytes (structs) (head))))) ((cm_globals_bytes (structs) (tail)))) )
  **  (UCharArray.undef_seg data_pre ((cursor_pre + size ) + (cm_rep_globals_size (tail)) ) capacity_pre )
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
|--
  (cm_global_list_rep node_pre globals )
  **  (UCharArray.seg data_pre 0 (cursor_pre + (cm_rep_globals_size (globals)) ) (app (prefix) ((cm_globals_bytes (structs) (globals)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + (cm_rep_globals_size (globals)) ) capacity_pre )
.

Definition cmc_emit_globals_return_wit_2 := 
(
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (PreH1 : (node_pre = 0)) (PreH2 : (cm_rep_globals_safe globals )) (PreH3 : (cm_data_globals_wf structs globals )) (PreH4 : (0 <= cursor_pre)) (PreH5 : ((cursor_pre + (cm_rep_globals_size (globals)) ) <= capacity_pre)) (PreH6 : (capacity_pre <= INT_MAX)) ,
  (cm_global_list_rep node_pre globals )
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_data_globals_wf structs globals ) ” 
  &&  “ (cursor_pre = (cursor_pre + (cm_rep_globals_size (globals)) )) ”
  &&  (cm_global_list_rep node_pre globals )
  **  (UCharArray.seg data_pre 0 (cursor_pre + (cm_rep_globals_size (globals)) ) (app (prefix) ((cm_globals_bytes (structs) (globals)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + (cm_rep_globals_size (globals)) ) capacity_pre )
) \/
(
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (PreH1 : (node_pre = 0)) (PreH2 : (cm_rep_globals_safe globals )) (PreH3 : (cm_data_globals_wf structs globals )) (PreH4 : (0 <= cursor_pre)) (PreH5 : ((cursor_pre + (cm_rep_globals_size (globals)) ) <= capacity_pre)) (PreH6 : (capacity_pre <= INT_MAX)) ,
  (cm_global_list_rep node_pre globals )
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (cursor_pre = (cursor_pre + (cm_rep_globals_size (globals)) )) ”
  &&  (cm_global_list_rep node_pre globals )
  **  (UCharArray.seg data_pre 0 (cursor_pre + (cm_rep_globals_size (globals)) ) (app (prefix) ((cm_globals_bytes (structs) (globals)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + (cm_rep_globals_size (globals)) ) capacity_pre )
).

Definition cmc_emit_globals_return_wit_2_split_goal_1 := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (PreH1 : (node_pre = 0)) (PreH2 : (cm_rep_globals_safe globals )) (PreH3 : (cm_data_globals_wf structs globals )) (PreH4 : (0 <= cursor_pre)) (PreH5 : ((cursor_pre + (cm_rep_globals_size (globals)) ) <= capacity_pre)) (PreH6 : (capacity_pre <= INT_MAX)) ,
  (cm_global_list_rep node_pre globals )
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (cursor_pre = (cursor_pre + (cm_rep_globals_size (globals)) )) ”
.

Definition cmc_emit_globals_return_wit_2_split_goal_spatial := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (PreH1 : (node_pre = 0)) (PreH2 : (cm_rep_globals_safe globals )) (PreH3 : (cm_data_globals_wf structs globals )) (PreH4 : (0 <= cursor_pre)) (PreH5 : ((cursor_pre + (cm_rep_globals_size (globals)) ) <= capacity_pre)) (PreH6 : (capacity_pre <= INT_MAX)) ,
  (cm_global_list_rep node_pre globals )
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  (cm_global_list_rep node_pre globals )
  **  (UCharArray.seg data_pre 0 (cursor_pre + (cm_rep_globals_size (globals)) ) (app (prefix) ((cm_globals_bytes (structs) (globals)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + (cm_rep_globals_size (globals)) ) capacity_pre )
.

Definition cmc_emit_globals_partial_solve_wit_1 := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (PreH1 : (node_pre <> 0)) (PreH2 : (globals = (cons (head) (tail)))) (PreH3 : (cm_rep_globals_safe globals )) (PreH4 : (cm_data_globals_wf structs globals )) (PreH5 : (cm_rep_globals_safe tail )) (PreH6 : (cm_data_globals_wf structs tail )) (PreH7 : (cm_global_wf structs head )) (PreH8 : (0 <= cursor_pre)) (PreH9 : (capacity_pre <= INT_MAX)) (PreH10 : (0 <= (cm_rep_global_size (head)))) (PreH11 : ((cm_rep_global_size (head)) <= 1048560)) (PreH12 : (0 <= (cm_rep_globals_size (tail)))) (PreH13 : (((cursor_pre + (cm_rep_global_size (head)) ) + (cm_rep_globals_size (tail)) ) <= capacity_pre)) ,
  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (node_pre <> 0) ” 
  &&  “ (globals = (cons (head) (tail))) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_data_globals_wf structs globals ) ” 
  &&  “ (cm_rep_globals_safe tail ) ” 
  &&  “ (cm_data_globals_wf structs tail ) ” 
  &&  “ (cm_global_wf structs head ) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ (0 <= (cm_rep_global_size (head))) ” 
  &&  “ ((cm_rep_global_size (head)) <= 1048560) ” 
  &&  “ (0 <= (cm_rep_globals_size (tail))) ” 
  &&  “ (((cursor_pre + (cm_rep_global_size (head)) ) + (cm_rep_globals_size (tail)) ) <= capacity_pre) ”
  &&  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
.

Definition cmc_emit_globals_partial_solve_wit_2_pure := 
(
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (PreH1 : ((cm_type_encode ((cm_global_ty (head)))) = 1)) (PreH2 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH3 : (node_pre <> 0)) (PreH4 : (globals = (cons (head) (tail)))) (PreH5 : (cm_rep_globals_safe globals )) (PreH6 : (cm_data_globals_wf structs globals )) (PreH7 : (cm_rep_globals_safe tail )) (PreH8 : (cm_data_globals_wf structs tail )) (PreH9 : (cm_global_wf structs head )) (PreH10 : (0 <= cursor_pre)) (PreH11 : (capacity_pre <= INT_MAX)) (PreH12 : (0 <= (cm_rep_global_size (head)))) (PreH13 : ((cm_rep_global_size (head)) <= 1048560)) (PreH14 : (0 <= (cm_rep_globals_size (tail)))) (PreH15 : (((cursor_pre + (cm_rep_global_size (head)) ) + (cm_rep_globals_size (tail)) ) <= capacity_pre)) (PreH16 : ((cm_rep_bool ((cm_global_has_init (head)))) <> 0)) ,
  ((( &( "size" ) )) # Int  |-> (signed_last_nbits (retval) (32)))
  **  ((( &( "size64" ) )) # Int64  |-> retval)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "init_value" ) )) # Int64  |-> (cm_global_init (head)))
  **  ((( &( "has_init" ) )) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((( &( "count" ) )) # Int  |-> (cm_global_count (head)))
  **  ((( &( "type_code" ) )) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (0 <= cursor_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ ((cursor_pre + 1 ) <= capacity_pre) ”
) \/
(
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (PreH1 : ((cm_global_init (head)) <= INT64_MAX)) (PreH2 : (retval <= INT64_MAX)) (PreH3 : ((cm_global_init (head)) >= INT64_MIN)) (PreH4 : (retval >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : ((cm_type_encode ((cm_global_ty (head)))) <= INT_MAX)) (PreH8 : ((cm_global_count (head)) <= INT_MAX)) (PreH9 : ((cm_rep_bool ((cm_global_has_init (head)))) <= INT_MAX)) (PreH10 : ((signed_last_nbits (retval) (32)) <= INT_MAX)) (PreH11 : (cursor_pre >= INT_MIN)) (PreH12 : (capacity_pre >= INT_MIN)) (PreH13 : ((cm_type_encode ((cm_global_ty (head)))) >= INT_MIN)) (PreH14 : ((cm_global_count (head)) >= INT_MIN)) (PreH15 : ((cm_rep_bool ((cm_global_has_init (head)))) >= INT_MIN)) (PreH16 : ((signed_last_nbits (retval) (32)) >= INT_MIN)) (PreH17 : ((cm_type_encode ((cm_global_ty (head)))) = 1)) (PreH18 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH19 : (node_pre <> 0)) (PreH20 : (globals = (cons (head) (tail)))) (PreH21 : (cm_rep_globals_safe globals )) (PreH22 : (cm_data_globals_wf structs globals )) (PreH23 : (cm_rep_globals_safe tail )) (PreH24 : (cm_data_globals_wf structs tail )) (PreH25 : (cm_global_wf structs head )) (PreH26 : (0 <= cursor_pre)) (PreH27 : (capacity_pre <= INT_MAX)) (PreH28 : (0 <= (cm_rep_global_size (head)))) (PreH29 : ((cm_rep_global_size (head)) <= 1048560)) (PreH30 : (0 <= (cm_rep_globals_size (tail)))) (PreH31 : (((cursor_pre + (cm_rep_global_size (head)) ) + (cm_rep_globals_size (tail)) ) <= capacity_pre)) (PreH32 : ((cm_rep_bool ((cm_global_has_init (head)))) <> 0)) ,
  ((( &( "size" ) )) # Int  |-> (signed_last_nbits (retval) (32)))
  **  ((( &( "size64" ) )) # Int64  |-> retval)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "init_value" ) )) # Int64  |-> (cm_global_init (head)))
  **  ((( &( "has_init" ) )) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((( &( "count" ) )) # Int  |-> (cm_global_count (head)))
  **  ((( &( "type_code" ) )) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ ((cursor_pre + 1 ) <= capacity_pre) ”
).

Definition cmc_emit_globals_partial_solve_wit_2_pure_split_goal_1 := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (PreH1 : ((cm_global_init (head)) <= INT64_MAX)) (PreH2 : (retval <= INT64_MAX)) (PreH3 : ((cm_global_init (head)) >= INT64_MIN)) (PreH4 : (retval >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : ((cm_type_encode ((cm_global_ty (head)))) <= INT_MAX)) (PreH8 : ((cm_global_count (head)) <= INT_MAX)) (PreH9 : ((cm_rep_bool ((cm_global_has_init (head)))) <= INT_MAX)) (PreH10 : ((signed_last_nbits (retval) (32)) <= INT_MAX)) (PreH11 : (cursor_pre >= INT_MIN)) (PreH12 : (capacity_pre >= INT_MIN)) (PreH13 : ((cm_type_encode ((cm_global_ty (head)))) >= INT_MIN)) (PreH14 : ((cm_global_count (head)) >= INT_MIN)) (PreH15 : ((cm_rep_bool ((cm_global_has_init (head)))) >= INT_MIN)) (PreH16 : ((signed_last_nbits (retval) (32)) >= INT_MIN)) (PreH17 : ((cm_type_encode ((cm_global_ty (head)))) = 1)) (PreH18 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH19 : (node_pre <> 0)) (PreH20 : (globals = (cons (head) (tail)))) (PreH21 : (cm_rep_globals_safe globals )) (PreH22 : (cm_data_globals_wf structs globals )) (PreH23 : (cm_rep_globals_safe tail )) (PreH24 : (cm_data_globals_wf structs tail )) (PreH25 : (cm_global_wf structs head )) (PreH26 : (0 <= cursor_pre)) (PreH27 : (capacity_pre <= INT_MAX)) (PreH28 : (0 <= (cm_rep_global_size (head)))) (PreH29 : ((cm_rep_global_size (head)) <= 1048560)) (PreH30 : (0 <= (cm_rep_globals_size (tail)))) (PreH31 : (((cursor_pre + (cm_rep_global_size (head)) ) + (cm_rep_globals_size (tail)) ) <= capacity_pre)) (PreH32 : ((cm_rep_bool ((cm_global_has_init (head)))) <> 0)) ,
  ((( &( "size" ) )) # Int  |-> (signed_last_nbits (retval) (32)))
  **  ((( &( "size64" ) )) # Int64  |-> retval)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "init_value" ) )) # Int64  |-> (cm_global_init (head)))
  **  ((( &( "has_init" ) )) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((( &( "count" ) )) # Int  |-> (cm_global_count (head)))
  **  ((( &( "type_code" ) )) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ ((cursor_pre + 1 ) <= capacity_pre) ”
.

Definition cmc_emit_globals_partial_solve_wit_2_aux := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (PreH1 : ((cm_type_encode ((cm_global_ty (head)))) = 1)) (PreH2 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH3 : (node_pre <> 0)) (PreH4 : (globals = (cons (head) (tail)))) (PreH5 : (cm_rep_globals_safe globals )) (PreH6 : (cm_data_globals_wf structs globals )) (PreH7 : (cm_rep_globals_safe tail )) (PreH8 : (cm_data_globals_wf structs tail )) (PreH9 : (cm_global_wf structs head )) (PreH10 : (0 <= cursor_pre)) (PreH11 : (capacity_pre <= INT_MAX)) (PreH12 : (0 <= (cm_rep_global_size (head)))) (PreH13 : ((cm_rep_global_size (head)) <= 1048560)) (PreH14 : (0 <= (cm_rep_globals_size (tail)))) (PreH15 : (((cursor_pre + (cm_rep_global_size (head)) ) + (cm_rep_globals_size (tail)) ) <= capacity_pre)) (PreH16 : ((cm_rep_bool ((cm_global_has_init (head)))) <> 0)) ,
  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (0 <= cursor_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ ((cursor_pre + 1 ) <= capacity_pre) ” 
  &&  “ ((cm_type_encode ((cm_global_ty (head)))) = 1) ” 
  &&  “ (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head))))) ” 
  &&  “ (node_pre <> 0) ” 
  &&  “ (globals = (cons (head) (tail))) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_data_globals_wf structs globals ) ” 
  &&  “ (cm_rep_globals_safe tail ) ” 
  &&  “ (cm_data_globals_wf structs tail ) ” 
  &&  “ (cm_global_wf structs head ) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ (0 <= (cm_rep_global_size (head))) ” 
  &&  “ ((cm_rep_global_size (head)) <= 1048560) ” 
  &&  “ (0 <= (cm_rep_globals_size (tail))) ” 
  &&  “ (((cursor_pre + (cm_rep_global_size (head)) ) + (cm_rep_globals_size (tail)) ) <= capacity_pre) ” 
  &&  “ ((cm_rep_bool ((cm_global_has_init (head)))) <> 0) ”
  &&  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
.

Definition cmc_emit_globals_partial_solve_wit_2 := cmc_emit_globals_partial_solve_wit_2_pure -> cmc_emit_globals_partial_solve_wit_2_aux.

Definition cmc_emit_globals_partial_solve_wit_3_pure := 
(
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (PreH1 : ((cm_type_encode ((cm_global_ty (head)))) <> 1)) (PreH2 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH3 : (node_pre <> 0)) (PreH4 : (globals = (cons (head) (tail)))) (PreH5 : (cm_rep_globals_safe globals )) (PreH6 : (cm_data_globals_wf structs globals )) (PreH7 : (cm_rep_globals_safe tail )) (PreH8 : (cm_data_globals_wf structs tail )) (PreH9 : (cm_global_wf structs head )) (PreH10 : (0 <= cursor_pre)) (PreH11 : (capacity_pre <= INT_MAX)) (PreH12 : (0 <= (cm_rep_global_size (head)))) (PreH13 : ((cm_rep_global_size (head)) <= 1048560)) (PreH14 : (0 <= (cm_rep_globals_size (tail)))) (PreH15 : (((cursor_pre + (cm_rep_global_size (head)) ) + (cm_rep_globals_size (tail)) ) <= capacity_pre)) (PreH16 : ((cm_rep_bool ((cm_global_has_init (head)))) <> 0)) ,
  ((( &( "size" ) )) # Int  |-> (signed_last_nbits (retval) (32)))
  **  ((( &( "size64" ) )) # Int64  |-> retval)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "init_value" ) )) # Int64  |-> (cm_global_init (head)))
  **  ((( &( "has_init" ) )) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((( &( "count" ) )) # Int  |-> (cm_global_count (head)))
  **  ((( &( "type_code" ) )) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (0 <= cursor_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ ((cursor_pre + 8 ) <= capacity_pre) ”
) \/
(
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (PreH1 : ((cm_global_init (head)) <= INT64_MAX)) (PreH2 : (retval <= INT64_MAX)) (PreH3 : ((cm_global_init (head)) >= INT64_MIN)) (PreH4 : (retval >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : ((cm_type_encode ((cm_global_ty (head)))) <= INT_MAX)) (PreH8 : ((cm_global_count (head)) <= INT_MAX)) (PreH9 : ((cm_rep_bool ((cm_global_has_init (head)))) <= INT_MAX)) (PreH10 : ((signed_last_nbits (retval) (32)) <= INT_MAX)) (PreH11 : (cursor_pre >= INT_MIN)) (PreH12 : (capacity_pre >= INT_MIN)) (PreH13 : ((cm_type_encode ((cm_global_ty (head)))) >= INT_MIN)) (PreH14 : ((cm_global_count (head)) >= INT_MIN)) (PreH15 : ((cm_rep_bool ((cm_global_has_init (head)))) >= INT_MIN)) (PreH16 : ((signed_last_nbits (retval) (32)) >= INT_MIN)) (PreH17 : ((cm_type_encode ((cm_global_ty (head)))) <> 1)) (PreH18 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH19 : (node_pre <> 0)) (PreH20 : (globals = (cons (head) (tail)))) (PreH21 : (cm_rep_globals_safe globals )) (PreH22 : (cm_data_globals_wf structs globals )) (PreH23 : (cm_rep_globals_safe tail )) (PreH24 : (cm_data_globals_wf structs tail )) (PreH25 : (cm_global_wf structs head )) (PreH26 : (0 <= cursor_pre)) (PreH27 : (capacity_pre <= INT_MAX)) (PreH28 : (0 <= (cm_rep_global_size (head)))) (PreH29 : ((cm_rep_global_size (head)) <= 1048560)) (PreH30 : (0 <= (cm_rep_globals_size (tail)))) (PreH31 : (((cursor_pre + (cm_rep_global_size (head)) ) + (cm_rep_globals_size (tail)) ) <= capacity_pre)) (PreH32 : ((cm_rep_bool ((cm_global_has_init (head)))) <> 0)) ,
  ((( &( "size" ) )) # Int  |-> (signed_last_nbits (retval) (32)))
  **  ((( &( "size64" ) )) # Int64  |-> retval)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "init_value" ) )) # Int64  |-> (cm_global_init (head)))
  **  ((( &( "has_init" ) )) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((( &( "count" ) )) # Int  |-> (cm_global_count (head)))
  **  ((( &( "type_code" ) )) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ ((cursor_pre + 8 ) <= capacity_pre) ”
).

Definition cmc_emit_globals_partial_solve_wit_3_pure_split_goal_1 := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (PreH1 : ((cm_global_init (head)) <= INT64_MAX)) (PreH2 : (retval <= INT64_MAX)) (PreH3 : ((cm_global_init (head)) >= INT64_MIN)) (PreH4 : (retval >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : ((cm_type_encode ((cm_global_ty (head)))) <= INT_MAX)) (PreH8 : ((cm_global_count (head)) <= INT_MAX)) (PreH9 : ((cm_rep_bool ((cm_global_has_init (head)))) <= INT_MAX)) (PreH10 : ((signed_last_nbits (retval) (32)) <= INT_MAX)) (PreH11 : (cursor_pre >= INT_MIN)) (PreH12 : (capacity_pre >= INT_MIN)) (PreH13 : ((cm_type_encode ((cm_global_ty (head)))) >= INT_MIN)) (PreH14 : ((cm_global_count (head)) >= INT_MIN)) (PreH15 : ((cm_rep_bool ((cm_global_has_init (head)))) >= INT_MIN)) (PreH16 : ((signed_last_nbits (retval) (32)) >= INT_MIN)) (PreH17 : ((cm_type_encode ((cm_global_ty (head)))) <> 1)) (PreH18 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH19 : (node_pre <> 0)) (PreH20 : (globals = (cons (head) (tail)))) (PreH21 : (cm_rep_globals_safe globals )) (PreH22 : (cm_data_globals_wf structs globals )) (PreH23 : (cm_rep_globals_safe tail )) (PreH24 : (cm_data_globals_wf structs tail )) (PreH25 : (cm_global_wf structs head )) (PreH26 : (0 <= cursor_pre)) (PreH27 : (capacity_pre <= INT_MAX)) (PreH28 : (0 <= (cm_rep_global_size (head)))) (PreH29 : ((cm_rep_global_size (head)) <= 1048560)) (PreH30 : (0 <= (cm_rep_globals_size (tail)))) (PreH31 : (((cursor_pre + (cm_rep_global_size (head)) ) + (cm_rep_globals_size (tail)) ) <= capacity_pre)) (PreH32 : ((cm_rep_bool ((cm_global_has_init (head)))) <> 0)) ,
  ((( &( "size" ) )) # Int  |-> (signed_last_nbits (retval) (32)))
  **  ((( &( "size64" ) )) # Int64  |-> retval)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "init_value" ) )) # Int64  |-> (cm_global_init (head)))
  **  ((( &( "has_init" ) )) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((( &( "count" ) )) # Int  |-> (cm_global_count (head)))
  **  ((( &( "type_code" ) )) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ ((cursor_pre + 8 ) <= capacity_pre) ”
.

Definition cmc_emit_globals_partial_solve_wit_3_aux := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (PreH1 : ((cm_type_encode ((cm_global_ty (head)))) <> 1)) (PreH2 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH3 : (node_pre <> 0)) (PreH4 : (globals = (cons (head) (tail)))) (PreH5 : (cm_rep_globals_safe globals )) (PreH6 : (cm_data_globals_wf structs globals )) (PreH7 : (cm_rep_globals_safe tail )) (PreH8 : (cm_data_globals_wf structs tail )) (PreH9 : (cm_global_wf structs head )) (PreH10 : (0 <= cursor_pre)) (PreH11 : (capacity_pre <= INT_MAX)) (PreH12 : (0 <= (cm_rep_global_size (head)))) (PreH13 : ((cm_rep_global_size (head)) <= 1048560)) (PreH14 : (0 <= (cm_rep_globals_size (tail)))) (PreH15 : (((cursor_pre + (cm_rep_global_size (head)) ) + (cm_rep_globals_size (tail)) ) <= capacity_pre)) (PreH16 : ((cm_rep_bool ((cm_global_has_init (head)))) <> 0)) ,
  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (0 <= cursor_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ ((cursor_pre + 8 ) <= capacity_pre) ” 
  &&  “ ((cm_type_encode ((cm_global_ty (head)))) <> 1) ” 
  &&  “ (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head))))) ” 
  &&  “ (node_pre <> 0) ” 
  &&  “ (globals = (cons (head) (tail))) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_data_globals_wf structs globals ) ” 
  &&  “ (cm_rep_globals_safe tail ) ” 
  &&  “ (cm_data_globals_wf structs tail ) ” 
  &&  “ (cm_global_wf structs head ) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ (0 <= (cm_rep_global_size (head))) ” 
  &&  “ ((cm_rep_global_size (head)) <= 1048560) ” 
  &&  “ (0 <= (cm_rep_globals_size (tail))) ” 
  &&  “ (((cursor_pre + (cm_rep_global_size (head)) ) + (cm_rep_globals_size (tail)) ) <= capacity_pre) ” 
  &&  “ ((cm_rep_bool ((cm_global_has_init (head)))) <> 0) ”
  &&  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
.

Definition cmc_emit_globals_partial_solve_wit_3 := cmc_emit_globals_partial_solve_wit_3_pure -> cmc_emit_globals_partial_solve_wit_3_aux.

Definition cmc_emit_globals_partial_solve_wit_4_pure := 
(
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (PreH1 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH2 : (node_pre <> 0)) (PreH3 : (globals = (cons (head) (tail)))) (PreH4 : (cm_rep_globals_safe globals )) (PreH5 : (cm_data_globals_wf structs globals )) (PreH6 : (cm_rep_globals_safe tail )) (PreH7 : (cm_data_globals_wf structs tail )) (PreH8 : (cm_global_wf structs head )) (PreH9 : (0 <= cursor_pre)) (PreH10 : (capacity_pre <= INT_MAX)) (PreH11 : (0 <= (cm_rep_global_size (head)))) (PreH12 : ((cm_rep_global_size (head)) <= 1048560)) (PreH13 : (0 <= (cm_rep_globals_size (tail)))) (PreH14 : (((cursor_pre + (cm_rep_global_size (head)) ) + (cm_rep_globals_size (tail)) ) <= capacity_pre)) (PreH15 : ((cm_rep_bool ((cm_global_has_init (head)))) = 0)) ,
  ((( &( "size" ) )) # Int  |-> (signed_last_nbits (retval) (32)))
  **  ((( &( "size64" ) )) # Int64  |-> retval)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "init_value" ) )) # Int64  |-> (cm_global_init (head)))
  **  ((( &( "has_init" ) )) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((( &( "count" ) )) # Int  |-> (cm_global_count (head)))
  **  ((( &( "type_code" ) )) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (0 <= cursor_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ ((cursor_pre + (signed_last_nbits (retval) (32)) ) <= capacity_pre) ” 
  &&  “ (0 <= (signed_last_nbits (retval) (32))) ”
) \/
(
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (PreH1 : ((cm_global_init (head)) <= INT64_MAX)) (PreH2 : (retval <= INT64_MAX)) (PreH3 : ((cm_global_init (head)) >= INT64_MIN)) (PreH4 : (retval >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : ((cm_type_encode ((cm_global_ty (head)))) <= INT_MAX)) (PreH8 : ((cm_global_count (head)) <= INT_MAX)) (PreH9 : ((cm_rep_bool ((cm_global_has_init (head)))) <= INT_MAX)) (PreH10 : ((signed_last_nbits (retval) (32)) <= INT_MAX)) (PreH11 : (cursor_pre >= INT_MIN)) (PreH12 : (capacity_pre >= INT_MIN)) (PreH13 : ((cm_type_encode ((cm_global_ty (head)))) >= INT_MIN)) (PreH14 : ((cm_global_count (head)) >= INT_MIN)) (PreH15 : ((cm_rep_bool ((cm_global_has_init (head)))) >= INT_MIN)) (PreH16 : ((signed_last_nbits (retval) (32)) >= INT_MIN)) (PreH17 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH18 : (node_pre <> 0)) (PreH19 : (globals = (cons (head) (tail)))) (PreH20 : (cm_rep_globals_safe globals )) (PreH21 : (cm_data_globals_wf structs globals )) (PreH22 : (cm_rep_globals_safe tail )) (PreH23 : (cm_data_globals_wf structs tail )) (PreH24 : (cm_global_wf structs head )) (PreH25 : (0 <= cursor_pre)) (PreH26 : (capacity_pre <= INT_MAX)) (PreH27 : (0 <= (cm_rep_global_size (head)))) (PreH28 : ((cm_rep_global_size (head)) <= 1048560)) (PreH29 : (0 <= (cm_rep_globals_size (tail)))) (PreH30 : (((cursor_pre + (cm_rep_global_size (head)) ) + (cm_rep_globals_size (tail)) ) <= capacity_pre)) (PreH31 : ((cm_rep_bool ((cm_global_has_init (head)))) = 0)) ,
  ((( &( "size" ) )) # Int  |-> (signed_last_nbits (retval) (32)))
  **  ((( &( "size64" ) )) # Int64  |-> retval)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "init_value" ) )) # Int64  |-> (cm_global_init (head)))
  **  ((( &( "has_init" ) )) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((( &( "count" ) )) # Int  |-> (cm_global_count (head)))
  **  ((( &( "type_code" ) )) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (0 <= (signed_last_nbits (retval) (32))) ” 
  &&  “ ((cursor_pre + (signed_last_nbits (retval) (32)) ) <= capacity_pre) ”
).

Definition cmc_emit_globals_partial_solve_wit_4_pure_split_goal_1 := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (PreH1 : ((cm_global_init (head)) <= INT64_MAX)) (PreH2 : (retval <= INT64_MAX)) (PreH3 : ((cm_global_init (head)) >= INT64_MIN)) (PreH4 : (retval >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : ((cm_type_encode ((cm_global_ty (head)))) <= INT_MAX)) (PreH8 : ((cm_global_count (head)) <= INT_MAX)) (PreH9 : ((cm_rep_bool ((cm_global_has_init (head)))) <= INT_MAX)) (PreH10 : ((signed_last_nbits (retval) (32)) <= INT_MAX)) (PreH11 : (cursor_pre >= INT_MIN)) (PreH12 : (capacity_pre >= INT_MIN)) (PreH13 : ((cm_type_encode ((cm_global_ty (head)))) >= INT_MIN)) (PreH14 : ((cm_global_count (head)) >= INT_MIN)) (PreH15 : ((cm_rep_bool ((cm_global_has_init (head)))) >= INT_MIN)) (PreH16 : ((signed_last_nbits (retval) (32)) >= INT_MIN)) (PreH17 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH18 : (node_pre <> 0)) (PreH19 : (globals = (cons (head) (tail)))) (PreH20 : (cm_rep_globals_safe globals )) (PreH21 : (cm_data_globals_wf structs globals )) (PreH22 : (cm_rep_globals_safe tail )) (PreH23 : (cm_data_globals_wf structs tail )) (PreH24 : (cm_global_wf structs head )) (PreH25 : (0 <= cursor_pre)) (PreH26 : (capacity_pre <= INT_MAX)) (PreH27 : (0 <= (cm_rep_global_size (head)))) (PreH28 : ((cm_rep_global_size (head)) <= 1048560)) (PreH29 : (0 <= (cm_rep_globals_size (tail)))) (PreH30 : (((cursor_pre + (cm_rep_global_size (head)) ) + (cm_rep_globals_size (tail)) ) <= capacity_pre)) (PreH31 : ((cm_rep_bool ((cm_global_has_init (head)))) = 0)) ,
  ((( &( "size" ) )) # Int  |-> (signed_last_nbits (retval) (32)))
  **  ((( &( "size64" ) )) # Int64  |-> retval)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "init_value" ) )) # Int64  |-> (cm_global_init (head)))
  **  ((( &( "has_init" ) )) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((( &( "count" ) )) # Int  |-> (cm_global_count (head)))
  **  ((( &( "type_code" ) )) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (0 <= (signed_last_nbits (retval) (32))) ”
.

Definition cmc_emit_globals_partial_solve_wit_4_pure_split_goal_2 := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (PreH1 : ((cm_global_init (head)) <= INT64_MAX)) (PreH2 : (retval <= INT64_MAX)) (PreH3 : ((cm_global_init (head)) >= INT64_MIN)) (PreH4 : (retval >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : ((cm_type_encode ((cm_global_ty (head)))) <= INT_MAX)) (PreH8 : ((cm_global_count (head)) <= INT_MAX)) (PreH9 : ((cm_rep_bool ((cm_global_has_init (head)))) <= INT_MAX)) (PreH10 : ((signed_last_nbits (retval) (32)) <= INT_MAX)) (PreH11 : (cursor_pre >= INT_MIN)) (PreH12 : (capacity_pre >= INT_MIN)) (PreH13 : ((cm_type_encode ((cm_global_ty (head)))) >= INT_MIN)) (PreH14 : ((cm_global_count (head)) >= INT_MIN)) (PreH15 : ((cm_rep_bool ((cm_global_has_init (head)))) >= INT_MIN)) (PreH16 : ((signed_last_nbits (retval) (32)) >= INT_MIN)) (PreH17 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH18 : (node_pre <> 0)) (PreH19 : (globals = (cons (head) (tail)))) (PreH20 : (cm_rep_globals_safe globals )) (PreH21 : (cm_data_globals_wf structs globals )) (PreH22 : (cm_rep_globals_safe tail )) (PreH23 : (cm_data_globals_wf structs tail )) (PreH24 : (cm_global_wf structs head )) (PreH25 : (0 <= cursor_pre)) (PreH26 : (capacity_pre <= INT_MAX)) (PreH27 : (0 <= (cm_rep_global_size (head)))) (PreH28 : ((cm_rep_global_size (head)) <= 1048560)) (PreH29 : (0 <= (cm_rep_globals_size (tail)))) (PreH30 : (((cursor_pre + (cm_rep_global_size (head)) ) + (cm_rep_globals_size (tail)) ) <= capacity_pre)) (PreH31 : ((cm_rep_bool ((cm_global_has_init (head)))) = 0)) ,
  ((( &( "size" ) )) # Int  |-> (signed_last_nbits (retval) (32)))
  **  ((( &( "size64" ) )) # Int64  |-> retval)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "init_value" ) )) # Int64  |-> (cm_global_init (head)))
  **  ((( &( "has_init" ) )) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((( &( "count" ) )) # Int  |-> (cm_global_count (head)))
  **  ((( &( "type_code" ) )) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ ((cursor_pre + (signed_last_nbits (retval) (32)) ) <= capacity_pre) ”
.

Definition cmc_emit_globals_partial_solve_wit_4_aux := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (PreH1 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH2 : (node_pre <> 0)) (PreH3 : (globals = (cons (head) (tail)))) (PreH4 : (cm_rep_globals_safe globals )) (PreH5 : (cm_data_globals_wf structs globals )) (PreH6 : (cm_rep_globals_safe tail )) (PreH7 : (cm_data_globals_wf structs tail )) (PreH8 : (cm_global_wf structs head )) (PreH9 : (0 <= cursor_pre)) (PreH10 : (capacity_pre <= INT_MAX)) (PreH11 : (0 <= (cm_rep_global_size (head)))) (PreH12 : ((cm_rep_global_size (head)) <= 1048560)) (PreH13 : (0 <= (cm_rep_globals_size (tail)))) (PreH14 : (((cursor_pre + (cm_rep_global_size (head)) ) + (cm_rep_globals_size (tail)) ) <= capacity_pre)) (PreH15 : ((cm_rep_bool ((cm_global_has_init (head)))) = 0)) ,
  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (0 <= cursor_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ ((cursor_pre + (signed_last_nbits (retval) (32)) ) <= capacity_pre) ” 
  &&  “ (0 <= (signed_last_nbits (retval) (32))) ” 
  &&  “ (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head))))) ” 
  &&  “ (node_pre <> 0) ” 
  &&  “ (globals = (cons (head) (tail))) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_data_globals_wf structs globals ) ” 
  &&  “ (cm_rep_globals_safe tail ) ” 
  &&  “ (cm_data_globals_wf structs tail ) ” 
  &&  “ (cm_global_wf structs head ) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ (0 <= (cm_rep_global_size (head))) ” 
  &&  “ ((cm_rep_global_size (head)) <= 1048560) ” 
  &&  “ (0 <= (cm_rep_globals_size (tail))) ” 
  &&  “ (((cursor_pre + (cm_rep_global_size (head)) ) + (cm_rep_globals_size (tail)) ) <= capacity_pre) ” 
  &&  “ ((cm_rep_bool ((cm_global_has_init (head)))) = 0) ”
  &&  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
.

Definition cmc_emit_globals_partial_solve_wit_4 := cmc_emit_globals_partial_solve_wit_4_pure -> cmc_emit_globals_partial_solve_wit_4_aux.

Definition cmc_emit_globals_partial_solve_wit_5_pure := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (type_code: Z) (count: Z) (has_init: Z) (init_value: Z) (size64: Z) (size: Z) (PreH1 : (node_pre <> 0)) (PreH2 : (globals = (cons (head) (tail)))) (PreH3 : (cm_rep_globals_safe globals )) (PreH4 : (cm_data_globals_wf structs globals )) (PreH5 : (cm_rep_globals_safe tail )) (PreH6 : (cm_data_globals_wf structs tail )) (PreH7 : (cm_global_wf structs head )) (PreH8 : (0 <= cursor_pre)) (PreH9 : (capacity_pre <= INT_MAX)) (PreH10 : (0 <= (cm_rep_global_size (head)))) (PreH11 : ((cm_rep_global_size (head)) <= 1048560)) (PreH12 : (0 <= (cm_rep_globals_size (tail)))) (PreH13 : (((cursor_pre + (cm_rep_global_size (head)) ) + (cm_rep_globals_size (tail)) ) <= capacity_pre)) (PreH14 : (type_code = (cm_type_encode ((cm_global_ty (head)))))) (PreH15 : (count = (cm_global_count (head)))) (PreH16 : (has_init = (cm_rep_bool ((cm_global_has_init (head)))))) (PreH17 : (init_value = (cm_global_init (head)))) (PreH18 : (size64 = (cm_rep_global_size (head)))) (PreH19 : (size = (cm_rep_global_size (head)))) ,
  ((( &( "final_cursor" ) )) # Int  |->_)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "type_code" ) )) # Int  |-> type_code)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "has_init" ) )) # Int  |-> has_init)
  **  ((( &( "init_value" ) )) # Int64  |-> init_value)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size64" ) )) # Int64  |-> size64)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
  **  (UCharArray.seg data_pre 0 (cursor_pre + size ) (app (prefix) ((cm_global_bytes (structs) (head)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + size ) capacity_pre )
|--
  “ (cm_rep_globals_safe tail ) ” 
  &&  “ (cm_data_globals_wf structs tail ) ” 
  &&  “ (0 <= (cursor_pre + size )) ” 
  &&  “ (((cursor_pre + size ) + (cm_rep_globals_size (tail)) ) <= capacity_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ”
.

Definition cmc_emit_globals_partial_solve_wit_5_aux := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (type_code: Z) (count: Z) (has_init: Z) (init_value: Z) (size64: Z) (size: Z) (PreH1 : (node_pre <> 0)) (PreH2 : (globals = (cons (head) (tail)))) (PreH3 : (cm_rep_globals_safe globals )) (PreH4 : (cm_data_globals_wf structs globals )) (PreH5 : (cm_rep_globals_safe tail )) (PreH6 : (cm_data_globals_wf structs tail )) (PreH7 : (cm_global_wf structs head )) (PreH8 : (0 <= cursor_pre)) (PreH9 : (capacity_pre <= INT_MAX)) (PreH10 : (0 <= (cm_rep_global_size (head)))) (PreH11 : ((cm_rep_global_size (head)) <= 1048560)) (PreH12 : (0 <= (cm_rep_globals_size (tail)))) (PreH13 : (((cursor_pre + (cm_rep_global_size (head)) ) + (cm_rep_globals_size (tail)) ) <= capacity_pre)) (PreH14 : (type_code = (cm_type_encode ((cm_global_ty (head)))))) (PreH15 : (count = (cm_global_count (head)))) (PreH16 : (has_init = (cm_rep_bool ((cm_global_has_init (head)))))) (PreH17 : (init_value = (cm_global_init (head)))) (PreH18 : (size64 = (cm_rep_global_size (head)))) (PreH19 : (size = (cm_rep_global_size (head)))) ,
  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
  **  (UCharArray.seg data_pre 0 (cursor_pre + size ) (app (prefix) ((cm_global_bytes (structs) (head)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + size ) capacity_pre )
|--
  “ (cm_rep_globals_safe tail ) ” 
  &&  “ (cm_data_globals_wf structs tail ) ” 
  &&  “ (0 <= (cursor_pre + size )) ” 
  &&  “ (((cursor_pre + size ) + (cm_rep_globals_size (tail)) ) <= capacity_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ (node_pre <> 0) ” 
  &&  “ (globals = (cons (head) (tail))) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_data_globals_wf structs globals ) ” 
  &&  “ (cm_rep_globals_safe tail ) ” 
  &&  “ (cm_data_globals_wf structs tail ) ” 
  &&  “ (cm_global_wf structs head ) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ (0 <= (cm_rep_global_size (head))) ” 
  &&  “ ((cm_rep_global_size (head)) <= 1048560) ” 
  &&  “ (0 <= (cm_rep_globals_size (tail))) ” 
  &&  “ (((cursor_pre + (cm_rep_global_size (head)) ) + (cm_rep_globals_size (tail)) ) <= capacity_pre) ” 
  &&  “ (type_code = (cm_type_encode ((cm_global_ty (head))))) ” 
  &&  “ (count = (cm_global_count (head))) ” 
  &&  “ (has_init = (cm_rep_bool ((cm_global_has_init (head))))) ” 
  &&  “ (init_value = (cm_global_init (head))) ” 
  &&  “ (size64 = (cm_rep_global_size (head))) ” 
  &&  “ (size = (cm_rep_global_size (head))) ”
  &&  (cm_global_list_rep nextp tail )
  **  (UCharArray.seg data_pre 0 (cursor_pre + size ) (app (prefix) ((cm_global_bytes (structs) (head)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + size ) capacity_pre )
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
.

Definition cmc_emit_globals_partial_solve_wit_5 := cmc_emit_globals_partial_solve_wit_5_pure -> cmc_emit_globals_partial_solve_wit_5_aux.

Module Type VC_Correct.


Axiom proof_of_cmc_emit_globals_safety_wit_1 : cmc_emit_globals_safety_wit_1.
Axiom proof_of_cmc_emit_globals_safety_wit_2 : cmc_emit_globals_safety_wit_2.
Axiom proof_of_cmc_emit_globals_safety_wit_3 : cmc_emit_globals_safety_wit_3.
Axiom proof_of_cmc_emit_globals_entail_wit_1 : cmc_emit_globals_entail_wit_1.
Axiom proof_of_cmc_emit_globals_entail_wit_2_1 : cmc_emit_globals_entail_wit_2_1.
Axiom proof_of_cmc_emit_globals_entail_wit_2_2 : cmc_emit_globals_entail_wit_2_2.
Axiom proof_of_cmc_emit_globals_entail_wit_2_3 : cmc_emit_globals_entail_wit_2_3.
Axiom proof_of_cmc_emit_globals_return_wit_1 : cmc_emit_globals_return_wit_1.
Axiom proof_of_cmc_emit_globals_return_wit_2 : cmc_emit_globals_return_wit_2.
Axiom proof_of_cmc_emit_globals_partial_solve_wit_1 : cmc_emit_globals_partial_solve_wit_1.
Axiom proof_of_cmc_emit_globals_partial_solve_wit_2_pure : cmc_emit_globals_partial_solve_wit_2_pure.
Axiom proof_of_cmc_emit_globals_partial_solve_wit_2 : cmc_emit_globals_partial_solve_wit_2.
Axiom proof_of_cmc_emit_globals_partial_solve_wit_3_pure : cmc_emit_globals_partial_solve_wit_3_pure.
Axiom proof_of_cmc_emit_globals_partial_solve_wit_3 : cmc_emit_globals_partial_solve_wit_3.
Axiom proof_of_cmc_emit_globals_partial_solve_wit_4_pure : cmc_emit_globals_partial_solve_wit_4_pure.
Axiom proof_of_cmc_emit_globals_partial_solve_wit_4 : cmc_emit_globals_partial_solve_wit_4.
Axiom proof_of_cmc_emit_globals_partial_solve_wit_5_pure : cmc_emit_globals_partial_solve_wit_5_pure.
Axiom proof_of_cmc_emit_globals_partial_solve_wit_5 : cmc_emit_globals_partial_solve_wit_5.

End VC_Correct.
