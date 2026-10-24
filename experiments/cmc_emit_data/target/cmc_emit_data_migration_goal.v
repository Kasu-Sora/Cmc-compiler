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
Require Import SimpleC.EE.QCP_demos_human.cmc_emit_data_migration_lib.
Local Open Scope sac.

(*----- Function cmc_emit_data -----*)

Definition cmc_emit_data_safety_wit_1 := 
forall (capacity_pre: Z) (data_pre: Z) (string_node_pre: Z) (global_node_pre: Z) (strings: (@list cm_string_d)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (PreH1 : (cm_rep_globals_safe globals )) (PreH2 : (cm_data_globals_wf structs globals )) (PreH3 : (cm_rep_strings_safe strings )) (PreH4 : (0 <= (cm_rep_globals_size (globals)))) (PreH5 : (0 <= (cm_rep_strings_size (strings)))) (PreH6 : (((8 + (cm_rep_globals_size (globals)) ) + (cm_rep_strings_size (strings)) ) <= capacity_pre)) (PreH7 : (capacity_pre <= INT_MAX)) ,
  ((( &( "global_node" ) )) # Ptr  |-> global_node_pre)
  **  ((( &( "string_node" ) )) # Ptr  |-> string_node_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (cm_global_list_rep global_node_pre globals )
  **  (cm_string_list_rep string_node_pre strings )
  **  (UCharArray.seg data_pre 0 0 (@nil Z) )
  **  (UCharArray.undef_seg data_pre 0 capacity_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_emit_data_safety_wit_2 := 
forall (capacity_pre: Z) (data_pre: Z) (string_node_pre: Z) (global_node_pre: Z) (strings: (@list cm_string_d)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (PreH1 : (cm_rep_globals_safe globals )) (PreH2 : (cm_data_globals_wf structs globals )) (PreH3 : (cm_rep_strings_safe strings )) (PreH4 : (0 <= (cm_rep_globals_size (globals)))) (PreH5 : (0 <= (cm_rep_strings_size (strings)))) (PreH6 : (((8 + (cm_rep_globals_size (globals)) ) + (cm_rep_strings_size (strings)) ) <= capacity_pre)) (PreH7 : (capacity_pre <= INT_MAX)) ,
  ((( &( "global_node" ) )) # Ptr  |-> global_node_pre)
  **  ((( &( "string_node" ) )) # Ptr  |-> string_node_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (cm_global_list_rep global_node_pre globals )
  **  (cm_string_list_rep string_node_pre strings )
  **  (UCharArray.seg data_pre 0 0 (@nil Z) )
  **  (UCharArray.undef_seg data_pre 0 capacity_pre )
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition cmc_emit_data_safety_wit_3 := 
forall (capacity_pre: Z) (data_pre: Z) (string_node_pre: Z) (global_node_pre: Z) (strings: (@list cm_string_d)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (PreH1 : (cm_rep_globals_safe globals )) (PreH2 : (cm_data_globals_wf structs globals )) (PreH3 : (cm_rep_strings_safe strings )) (PreH4 : (0 <= (cm_rep_globals_size (globals)))) (PreH5 : (0 <= (cm_rep_strings_size (strings)))) (PreH6 : (((8 + (cm_rep_globals_size (globals)) ) + (cm_rep_strings_size (strings)) ) <= capacity_pre)) (PreH7 : (capacity_pre <= INT_MAX)) ,
  ((( &( "globals_cursor" ) )) # Int  |->_)
  **  ((( &( "global_node" ) )) # Ptr  |-> global_node_pre)
  **  ((( &( "string_node" ) )) # Ptr  |-> string_node_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (cm_global_list_rep global_node_pre globals )
  **  (cm_string_list_rep string_node_pre strings )
  **  (UCharArray.seg data_pre 0 8 (zeros (8)) )
  **  (UCharArray.undef_seg data_pre 8 capacity_pre )
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition cmc_emit_data_entail_wit_1 := 
(
forall (capacity_pre: Z) (data_pre: Z) (string_node_pre: Z) (global_node_pre: Z) (strings: (@list cm_string_d)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (PreH1 : (cm_rep_globals_safe globals )) (PreH2 : (cm_data_globals_wf structs globals )) (PreH3 : (cm_rep_strings_safe strings )) (PreH4 : (0 <= (cm_rep_globals_size (globals)))) (PreH5 : (0 <= (cm_rep_strings_size (strings)))) (PreH6 : (((8 + (cm_rep_globals_size (globals)) ) + (cm_rep_strings_size (strings)) ) <= capacity_pre)) (PreH7 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 (0 + 8 ) (app (nil) ((zeros (8)))) )
  **  (UCharArray.undef_seg data_pre (0 + 8 ) capacity_pre )
  **  (cm_global_list_rep global_node_pre globals )
  **  (cm_string_list_rep string_node_pre strings )
|--
  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_data_globals_wf structs globals ) ” 
  &&  “ (cm_rep_strings_safe strings ) ” 
  &&  “ (0 <= (cm_rep_globals_size (globals))) ” 
  &&  “ (0 <= (cm_rep_strings_size (strings))) ” 
  &&  “ (((8 + (cm_rep_globals_size (globals)) ) + (cm_rep_strings_size (strings)) ) <= capacity_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ”
  &&  (cm_global_list_rep global_node_pre globals )
  **  (cm_string_list_rep string_node_pre strings )
  **  (UCharArray.seg data_pre 0 8 (zeros (8)) )
  **  (UCharArray.undef_seg data_pre 8 capacity_pre )
) \/
(
forall (capacity_pre: Z) (data_pre: Z) (string_node_pre: Z) (global_node_pre: Z) (strings: (@list cm_string_d)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (PreH1 : (cm_rep_globals_safe globals )) (PreH2 : (cm_data_globals_wf structs globals )) (PreH3 : (cm_rep_strings_safe strings )) (PreH4 : (0 <= (cm_rep_globals_size (globals)))) (PreH5 : (0 <= (cm_rep_strings_size (strings)))) (PreH6 : (((8 + (cm_rep_globals_size (globals)) ) + (cm_rep_strings_size (strings)) ) <= capacity_pre)) (PreH7 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 (0 + 8 ) (app (nil) ((zeros (8)))) )
  **  (cm_global_list_rep global_node_pre globals )
  **  (cm_string_list_rep string_node_pre strings )
|--
  (cm_global_list_rep global_node_pre globals )
  **  (cm_string_list_rep string_node_pre strings )
  **  (UCharArray.seg data_pre 0 8 (zeros (8)) )
).

Definition cmc_emit_data_entail_wit_1_split_goal_spatial := 
forall (capacity_pre: Z) (data_pre: Z) (string_node_pre: Z) (global_node_pre: Z) (strings: (@list cm_string_d)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (PreH1 : (cm_rep_globals_safe globals )) (PreH2 : (cm_data_globals_wf structs globals )) (PreH3 : (cm_rep_strings_safe strings )) (PreH4 : (0 <= (cm_rep_globals_size (globals)))) (PreH5 : (0 <= (cm_rep_strings_size (strings)))) (PreH6 : (((8 + (cm_rep_globals_size (globals)) ) + (cm_rep_strings_size (strings)) ) <= capacity_pre)) (PreH7 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 (0 + 8 ) (app (nil) ((zeros (8)))) )
  **  (cm_global_list_rep global_node_pre globals )
  **  (cm_string_list_rep string_node_pre strings )
|--
  (cm_global_list_rep global_node_pre globals )
  **  (cm_string_list_rep string_node_pre strings )
  **  (UCharArray.seg data_pre 0 8 (zeros (8)) )
.

Definition cmc_emit_data_return_wit_1 := 
(
forall (capacity_pre: Z) (data_pre: Z) (string_node_pre: Z) (global_node_pre: Z) (strings: (@list cm_string_d)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (retval_2: Z) (retval: Z) (PreH1 : (cm_rep_strings_safe strings )) (PreH2 : (retval = (retval_2 + (cm_rep_strings_size (strings)) ))) (PreH3 : (cm_rep_globals_safe globals )) (PreH4 : (cm_data_globals_wf structs globals )) (PreH5 : (retval_2 = (8 + (cm_rep_globals_size (globals)) ))) (PreH6 : (cm_rep_globals_safe globals )) (PreH7 : (cm_data_globals_wf structs globals )) (PreH8 : (cm_rep_strings_safe strings )) (PreH9 : (0 <= (cm_rep_globals_size (globals)))) (PreH10 : (0 <= (cm_rep_strings_size (strings)))) (PreH11 : (((8 + (cm_rep_globals_size (globals)) ) + (cm_rep_strings_size (strings)) ) <= capacity_pre)) (PreH12 : (capacity_pre <= INT_MAX)) ,
  (cm_string_list_rep string_node_pre strings )
  **  (UCharArray.seg data_pre 0 (retval_2 + (cm_rep_strings_size (strings)) ) (app ((app ((zeros (8))) ((cm_globals_bytes (structs) (globals))))) ((cm_strings_bytes (strings)))) )
  **  (UCharArray.undef_seg data_pre (retval_2 + (cm_rep_strings_size (strings)) ) capacity_pre )
  **  (cm_global_list_rep global_node_pre globals )
|--
  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_data_globals_wf structs globals ) ” 
  &&  “ (cm_rep_strings_safe strings ) ” 
  &&  “ (0 <= (cm_rep_globals_size (globals))) ” 
  &&  “ (0 <= (cm_rep_strings_size (strings))) ” 
  &&  “ (((8 + (cm_rep_globals_size (globals)) ) + (cm_rep_strings_size (strings)) ) <= capacity_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ (retval = ((8 + (cm_rep_globals_size (globals)) ) + (cm_rep_strings_size (strings)) )) ”
  &&  (cm_global_list_rep global_node_pre globals )
  **  (cm_string_list_rep string_node_pre strings )
  **  (UCharArray.seg data_pre 0 ((8 + (cm_rep_globals_size (globals)) ) + (cm_rep_strings_size (strings)) ) (app ((app ((zeros (8))) ((cm_globals_bytes (structs) (globals))))) ((cm_strings_bytes (strings)))) )
  **  (UCharArray.undef_seg data_pre ((8 + (cm_rep_globals_size (globals)) ) + (cm_rep_strings_size (strings)) ) capacity_pre )
) \/
(
forall (capacity_pre: Z) (data_pre: Z) (string_node_pre: Z) (global_node_pre: Z) (strings: (@list cm_string_d)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (retval_2: Z) (retval: Z) (PreH1 : (cm_rep_strings_safe strings )) (PreH2 : (retval = (retval_2 + (cm_rep_strings_size (strings)) ))) (PreH3 : (cm_rep_globals_safe globals )) (PreH4 : (cm_data_globals_wf structs globals )) (PreH5 : (retval_2 = (8 + (cm_rep_globals_size (globals)) ))) (PreH6 : (cm_rep_globals_safe globals )) (PreH7 : (cm_data_globals_wf structs globals )) (PreH8 : (cm_rep_strings_safe strings )) (PreH9 : (0 <= (cm_rep_globals_size (globals)))) (PreH10 : (0 <= (cm_rep_strings_size (strings)))) (PreH11 : (((8 + (cm_rep_globals_size (globals)) ) + (cm_rep_strings_size (strings)) ) <= capacity_pre)) (PreH12 : (capacity_pre <= INT_MAX)) ,
  (cm_string_list_rep string_node_pre strings )
  **  (UCharArray.seg data_pre 0 (retval_2 + (cm_rep_strings_size (strings)) ) (app ((app ((zeros (8))) ((cm_globals_bytes (structs) (globals))))) ((cm_strings_bytes (strings)))) )
  **  (UCharArray.undef_seg data_pre (retval_2 + (cm_rep_strings_size (strings)) ) capacity_pre )
  **  (cm_global_list_rep global_node_pre globals )
|--
  “ (retval = (retval_2 + (cm_rep_strings_size (strings)) )) ”
  &&  (cm_global_list_rep global_node_pre globals )
  **  (cm_string_list_rep string_node_pre strings )
  **  (UCharArray.seg data_pre 0 ((8 + (cm_rep_globals_size (globals)) ) + (cm_rep_strings_size (strings)) ) (app ((app ((zeros (8))) ((cm_globals_bytes (structs) (globals))))) ((cm_strings_bytes (strings)))) )
  **  (UCharArray.undef_seg data_pre ((8 + (cm_rep_globals_size (globals)) ) + (cm_rep_strings_size (strings)) ) capacity_pre )
).

Definition cmc_emit_data_return_wit_1_split_goal_1 := 
forall (capacity_pre: Z) (data_pre: Z) (string_node_pre: Z) (global_node_pre: Z) (strings: (@list cm_string_d)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (retval_2: Z) (retval: Z) (PreH1 : (cm_rep_strings_safe strings )) (PreH2 : (retval = (retval_2 + (cm_rep_strings_size (strings)) ))) (PreH3 : (cm_rep_globals_safe globals )) (PreH4 : (cm_data_globals_wf structs globals )) (PreH5 : (retval_2 = (8 + (cm_rep_globals_size (globals)) ))) (PreH6 : (cm_rep_globals_safe globals )) (PreH7 : (cm_data_globals_wf structs globals )) (PreH8 : (cm_rep_strings_safe strings )) (PreH9 : (0 <= (cm_rep_globals_size (globals)))) (PreH10 : (0 <= (cm_rep_strings_size (strings)))) (PreH11 : (((8 + (cm_rep_globals_size (globals)) ) + (cm_rep_strings_size (strings)) ) <= capacity_pre)) (PreH12 : (capacity_pre <= INT_MAX)) ,
  (cm_string_list_rep string_node_pre strings )
  **  (UCharArray.seg data_pre 0 (retval_2 + (cm_rep_strings_size (strings)) ) (app ((app ((zeros (8))) ((cm_globals_bytes (structs) (globals))))) ((cm_strings_bytes (strings)))) )
  **  (UCharArray.undef_seg data_pre (retval_2 + (cm_rep_strings_size (strings)) ) capacity_pre )
  **  (cm_global_list_rep global_node_pre globals )
|--
  “ (retval = (retval_2 + (cm_rep_strings_size (strings)) )) ”
.

Definition cmc_emit_data_return_wit_1_split_goal_spatial := 
forall (capacity_pre: Z) (data_pre: Z) (string_node_pre: Z) (global_node_pre: Z) (strings: (@list cm_string_d)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (retval_2: Z) (retval: Z) (PreH1 : (cm_rep_strings_safe strings )) (PreH2 : (retval = (retval_2 + (cm_rep_strings_size (strings)) ))) (PreH3 : (cm_rep_globals_safe globals )) (PreH4 : (cm_data_globals_wf structs globals )) (PreH5 : (retval_2 = (8 + (cm_rep_globals_size (globals)) ))) (PreH6 : (cm_rep_globals_safe globals )) (PreH7 : (cm_data_globals_wf structs globals )) (PreH8 : (cm_rep_strings_safe strings )) (PreH9 : (0 <= (cm_rep_globals_size (globals)))) (PreH10 : (0 <= (cm_rep_strings_size (strings)))) (PreH11 : (((8 + (cm_rep_globals_size (globals)) ) + (cm_rep_strings_size (strings)) ) <= capacity_pre)) (PreH12 : (capacity_pre <= INT_MAX)) ,
  (cm_string_list_rep string_node_pre strings )
  **  (UCharArray.seg data_pre 0 (retval_2 + (cm_rep_strings_size (strings)) ) (app ((app ((zeros (8))) ((cm_globals_bytes (structs) (globals))))) ((cm_strings_bytes (strings)))) )
  **  (UCharArray.undef_seg data_pre (retval_2 + (cm_rep_strings_size (strings)) ) capacity_pre )
  **  (cm_global_list_rep global_node_pre globals )
|--
  (cm_global_list_rep global_node_pre globals )
  **  (cm_string_list_rep string_node_pre strings )
  **  (UCharArray.seg data_pre 0 ((8 + (cm_rep_globals_size (globals)) ) + (cm_rep_strings_size (strings)) ) (app ((app ((zeros (8))) ((cm_globals_bytes (structs) (globals))))) ((cm_strings_bytes (strings)))) )
  **  (UCharArray.undef_seg data_pre ((8 + (cm_rep_globals_size (globals)) ) + (cm_rep_strings_size (strings)) ) capacity_pre )
.

Definition cmc_emit_data_partial_solve_wit_1_pure := 
(
forall (capacity_pre: Z) (data_pre: Z) (string_node_pre: Z) (global_node_pre: Z) (strings: (@list cm_string_d)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (PreH1 : (cm_rep_globals_safe globals )) (PreH2 : (cm_data_globals_wf structs globals )) (PreH3 : (cm_rep_strings_safe strings )) (PreH4 : (0 <= (cm_rep_globals_size (globals)))) (PreH5 : (0 <= (cm_rep_strings_size (strings)))) (PreH6 : (((8 + (cm_rep_globals_size (globals)) ) + (cm_rep_strings_size (strings)) ) <= capacity_pre)) (PreH7 : (capacity_pre <= INT_MAX)) ,
  ((( &( "global_node" ) )) # Ptr  |-> global_node_pre)
  **  ((( &( "string_node" ) )) # Ptr  |-> string_node_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (cm_global_list_rep global_node_pre globals )
  **  (cm_string_list_rep string_node_pre strings )
  **  (UCharArray.seg data_pre 0 0 (@nil Z) )
  **  (UCharArray.undef_seg data_pre 0 capacity_pre )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 8) ” 
  &&  “ ((0 + 8 ) <= capacity_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ ((@nil Z) = nil) ”
) \/
(
forall (capacity_pre: Z) (data_pre: Z) (string_node_pre: Z) (global_node_pre: Z) (strings: (@list cm_string_d)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (PreH1 : (capacity_pre <= INT_MAX)) (PreH2 : (capacity_pre >= INT_MIN)) (PreH3 : (cm_rep_globals_safe globals )) (PreH4 : (cm_data_globals_wf structs globals )) (PreH5 : (cm_rep_strings_safe strings )) (PreH6 : (0 <= (cm_rep_globals_size (globals)))) (PreH7 : (0 <= (cm_rep_strings_size (strings)))) (PreH8 : (((8 + (cm_rep_globals_size (globals)) ) + (cm_rep_strings_size (strings)) ) <= capacity_pre)) (PreH9 : (capacity_pre <= INT_MAX)) ,
  ((( &( "global_node" ) )) # Ptr  |-> global_node_pre)
  **  ((( &( "string_node" ) )) # Ptr  |-> string_node_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (cm_global_list_rep global_node_pre globals )
  **  (cm_string_list_rep string_node_pre strings )
  **  (UCharArray.seg data_pre 0 0 (@nil Z) )
  **  (UCharArray.undef_seg data_pre 0 capacity_pre )
|--
  “ ((@nil Z) = nil) ”
).

Definition cmc_emit_data_partial_solve_wit_1_pure_split_goal_1 := 
forall (capacity_pre: Z) (data_pre: Z) (string_node_pre: Z) (global_node_pre: Z) (strings: (@list cm_string_d)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (PreH1 : (capacity_pre <= INT_MAX)) (PreH2 : (capacity_pre >= INT_MIN)) (PreH3 : (cm_rep_globals_safe globals )) (PreH4 : (cm_data_globals_wf structs globals )) (PreH5 : (cm_rep_strings_safe strings )) (PreH6 : (0 <= (cm_rep_globals_size (globals)))) (PreH7 : (0 <= (cm_rep_strings_size (strings)))) (PreH8 : (((8 + (cm_rep_globals_size (globals)) ) + (cm_rep_strings_size (strings)) ) <= capacity_pre)) (PreH9 : (capacity_pre <= INT_MAX)) ,
  ((( &( "global_node" ) )) # Ptr  |-> global_node_pre)
  **  ((( &( "string_node" ) )) # Ptr  |-> string_node_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (cm_global_list_rep global_node_pre globals )
  **  (cm_string_list_rep string_node_pre strings )
  **  (UCharArray.seg data_pre 0 0 (@nil Z) )
  **  (UCharArray.undef_seg data_pre 0 capacity_pre )
|--
  “ ((@nil Z) = nil) ”
.

Definition cmc_emit_data_partial_solve_wit_1_aux := 
forall (capacity_pre: Z) (data_pre: Z) (string_node_pre: Z) (global_node_pre: Z) (strings: (@list cm_string_d)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (PreH1 : (cm_rep_globals_safe globals )) (PreH2 : (cm_data_globals_wf structs globals )) (PreH3 : (cm_rep_strings_safe strings )) (PreH4 : (0 <= (cm_rep_globals_size (globals)))) (PreH5 : (0 <= (cm_rep_strings_size (strings)))) (PreH6 : (((8 + (cm_rep_globals_size (globals)) ) + (cm_rep_strings_size (strings)) ) <= capacity_pre)) (PreH7 : (capacity_pre <= INT_MAX)) ,
  (cm_global_list_rep global_node_pre globals )
  **  (cm_string_list_rep string_node_pre strings )
  **  (UCharArray.seg data_pre 0 0 (@nil Z) )
  **  (UCharArray.undef_seg data_pre 0 capacity_pre )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 8) ” 
  &&  “ ((0 + 8 ) <= capacity_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ ((@nil Z) = nil) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_data_globals_wf structs globals ) ” 
  &&  “ (cm_rep_strings_safe strings ) ” 
  &&  “ (0 <= (cm_rep_globals_size (globals))) ” 
  &&  “ (0 <= (cm_rep_strings_size (strings))) ” 
  &&  “ (((8 + (cm_rep_globals_size (globals)) ) + (cm_rep_strings_size (strings)) ) <= capacity_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ”
  &&  (UCharArray.seg data_pre 0 0 nil )
  **  (UCharArray.undef_seg data_pre 0 capacity_pre )
  **  (cm_global_list_rep global_node_pre globals )
  **  (cm_string_list_rep string_node_pre strings )
.

Definition cmc_emit_data_partial_solve_wit_1 := cmc_emit_data_partial_solve_wit_1_pure -> cmc_emit_data_partial_solve_wit_1_aux.

Definition cmc_emit_data_partial_solve_wit_2_pure := 
forall (capacity_pre: Z) (data_pre: Z) (string_node_pre: Z) (global_node_pre: Z) (strings: (@list cm_string_d)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (PreH1 : (cm_rep_globals_safe globals )) (PreH2 : (cm_data_globals_wf structs globals )) (PreH3 : (cm_rep_strings_safe strings )) (PreH4 : (0 <= (cm_rep_globals_size (globals)))) (PreH5 : (0 <= (cm_rep_strings_size (strings)))) (PreH6 : (((8 + (cm_rep_globals_size (globals)) ) + (cm_rep_strings_size (strings)) ) <= capacity_pre)) (PreH7 : (capacity_pre <= INT_MAX)) ,
  ((( &( "globals_cursor" ) )) # Int  |->_)
  **  ((( &( "global_node" ) )) # Ptr  |-> global_node_pre)
  **  ((( &( "string_node" ) )) # Ptr  |-> string_node_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (cm_global_list_rep global_node_pre globals )
  **  (cm_string_list_rep string_node_pre strings )
  **  (UCharArray.seg data_pre 0 8 (zeros (8)) )
  **  (UCharArray.undef_seg data_pre 8 capacity_pre )
|--
  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_data_globals_wf structs globals ) ” 
  &&  “ (0 <= 8) ” 
  &&  “ ((8 + (cm_rep_globals_size (globals)) ) <= capacity_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ”
.

Definition cmc_emit_data_partial_solve_wit_2_aux := 
forall (capacity_pre: Z) (data_pre: Z) (string_node_pre: Z) (global_node_pre: Z) (strings: (@list cm_string_d)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (PreH1 : (cm_rep_globals_safe globals )) (PreH2 : (cm_data_globals_wf structs globals )) (PreH3 : (cm_rep_strings_safe strings )) (PreH4 : (0 <= (cm_rep_globals_size (globals)))) (PreH5 : (0 <= (cm_rep_strings_size (strings)))) (PreH6 : (((8 + (cm_rep_globals_size (globals)) ) + (cm_rep_strings_size (strings)) ) <= capacity_pre)) (PreH7 : (capacity_pre <= INT_MAX)) ,
  (cm_global_list_rep global_node_pre globals )
  **  (cm_string_list_rep string_node_pre strings )
  **  (UCharArray.seg data_pre 0 8 (zeros (8)) )
  **  (UCharArray.undef_seg data_pre 8 capacity_pre )
|--
  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_data_globals_wf structs globals ) ” 
  &&  “ (0 <= 8) ” 
  &&  “ ((8 + (cm_rep_globals_size (globals)) ) <= capacity_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_data_globals_wf structs globals ) ” 
  &&  “ (cm_rep_strings_safe strings ) ” 
  &&  “ (0 <= (cm_rep_globals_size (globals))) ” 
  &&  “ (0 <= (cm_rep_strings_size (strings))) ” 
  &&  “ (((8 + (cm_rep_globals_size (globals)) ) + (cm_rep_strings_size (strings)) ) <= capacity_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ”
  &&  (cm_global_list_rep global_node_pre globals )
  **  (UCharArray.seg data_pre 0 8 (zeros (8)) )
  **  (UCharArray.undef_seg data_pre 8 capacity_pre )
  **  (cm_string_list_rep string_node_pre strings )
.

Definition cmc_emit_data_partial_solve_wit_2 := cmc_emit_data_partial_solve_wit_2_pure -> cmc_emit_data_partial_solve_wit_2_aux.

Definition cmc_emit_data_partial_solve_wit_3_pure := 
(
forall (capacity_pre: Z) (data_pre: Z) (string_node_pre: Z) (global_node_pre: Z) (strings: (@list cm_string_d)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (retval: Z) (PreH1 : (cm_rep_globals_safe globals )) (PreH2 : (cm_data_globals_wf structs globals )) (PreH3 : (retval = (8 + (cm_rep_globals_size (globals)) ))) (PreH4 : (cm_rep_globals_safe globals )) (PreH5 : (cm_data_globals_wf structs globals )) (PreH6 : (cm_rep_strings_safe strings )) (PreH7 : (0 <= (cm_rep_globals_size (globals)))) (PreH8 : (0 <= (cm_rep_strings_size (strings)))) (PreH9 : (((8 + (cm_rep_globals_size (globals)) ) + (cm_rep_strings_size (strings)) ) <= capacity_pre)) (PreH10 : (capacity_pre <= INT_MAX)) ,
  ((( &( "final_cursor" ) )) # Int  |->_)
  **  (cm_global_list_rep global_node_pre globals )
  **  (UCharArray.seg data_pre 0 (8 + (cm_rep_globals_size (globals)) ) (app ((zeros (8))) ((cm_globals_bytes (structs) (globals)))) )
  **  (UCharArray.undef_seg data_pre (8 + (cm_rep_globals_size (globals)) ) capacity_pre )
  **  ((( &( "globals_cursor" ) )) # Int  |-> retval)
  **  ((( &( "global_node" ) )) # Ptr  |-> global_node_pre)
  **  ((( &( "string_node" ) )) # Ptr  |-> string_node_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (cm_string_list_rep string_node_pre strings )
|--
  “ (cm_rep_strings_safe strings ) ” 
  &&  “ ((retval + (cm_rep_strings_size (strings)) ) <= capacity_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ (0 <= retval) ”
) \/
(
forall (capacity_pre: Z) (data_pre: Z) (string_node_pre: Z) (global_node_pre: Z) (strings: (@list cm_string_d)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (retval: Z) (PreH1 : (capacity_pre <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (capacity_pre >= INT_MIN)) (PreH4 : (retval >= INT_MIN)) (PreH5 : (cm_rep_globals_safe globals )) (PreH6 : (cm_data_globals_wf structs globals )) (PreH7 : (retval = (8 + (cm_rep_globals_size (globals)) ))) (PreH8 : (cm_rep_globals_safe globals )) (PreH9 : (cm_data_globals_wf structs globals )) (PreH10 : (cm_rep_strings_safe strings )) (PreH11 : (0 <= (cm_rep_globals_size (globals)))) (PreH12 : (0 <= (cm_rep_strings_size (strings)))) (PreH13 : (((8 + (cm_rep_globals_size (globals)) ) + (cm_rep_strings_size (strings)) ) <= capacity_pre)) (PreH14 : (capacity_pre <= INT_MAX)) ,
  ((( &( "final_cursor" ) )) # Int  |->_)
  **  (cm_global_list_rep global_node_pre globals )
  **  (UCharArray.seg data_pre 0 (8 + (cm_rep_globals_size (globals)) ) (app ((zeros (8))) ((cm_globals_bytes (structs) (globals)))) )
  **  (UCharArray.undef_seg data_pre (8 + (cm_rep_globals_size (globals)) ) capacity_pre )
  **  ((( &( "globals_cursor" ) )) # Int  |-> retval)
  **  ((( &( "global_node" ) )) # Ptr  |-> global_node_pre)
  **  ((( &( "string_node" ) )) # Ptr  |-> string_node_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (cm_string_list_rep string_node_pre strings )
|--
  “ (0 <= retval) ”
).

Definition cmc_emit_data_partial_solve_wit_3_pure_split_goal_1 := 
forall (capacity_pre: Z) (data_pre: Z) (string_node_pre: Z) (global_node_pre: Z) (strings: (@list cm_string_d)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (retval: Z) (PreH1 : (capacity_pre <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (capacity_pre >= INT_MIN)) (PreH4 : (retval >= INT_MIN)) (PreH5 : (cm_rep_globals_safe globals )) (PreH6 : (cm_data_globals_wf structs globals )) (PreH7 : (retval = (8 + (cm_rep_globals_size (globals)) ))) (PreH8 : (cm_rep_globals_safe globals )) (PreH9 : (cm_data_globals_wf structs globals )) (PreH10 : (cm_rep_strings_safe strings )) (PreH11 : (0 <= (cm_rep_globals_size (globals)))) (PreH12 : (0 <= (cm_rep_strings_size (strings)))) (PreH13 : (((8 + (cm_rep_globals_size (globals)) ) + (cm_rep_strings_size (strings)) ) <= capacity_pre)) (PreH14 : (capacity_pre <= INT_MAX)) ,
  ((( &( "final_cursor" ) )) # Int  |->_)
  **  (cm_global_list_rep global_node_pre globals )
  **  (UCharArray.seg data_pre 0 (8 + (cm_rep_globals_size (globals)) ) (app ((zeros (8))) ((cm_globals_bytes (structs) (globals)))) )
  **  (UCharArray.undef_seg data_pre (8 + (cm_rep_globals_size (globals)) ) capacity_pre )
  **  ((( &( "globals_cursor" ) )) # Int  |-> retval)
  **  ((( &( "global_node" ) )) # Ptr  |-> global_node_pre)
  **  ((( &( "string_node" ) )) # Ptr  |-> string_node_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (cm_string_list_rep string_node_pre strings )
|--
  “ (0 <= retval) ”
.

Definition cmc_emit_data_partial_solve_wit_3_aux := 
forall (capacity_pre: Z) (data_pre: Z) (string_node_pre: Z) (global_node_pre: Z) (strings: (@list cm_string_d)) (globals: (@list cm_global_d)) (structs: (@list cm_struct_d)) (retval: Z) (PreH1 : (cm_rep_globals_safe globals )) (PreH2 : (cm_data_globals_wf structs globals )) (PreH3 : (retval = (8 + (cm_rep_globals_size (globals)) ))) (PreH4 : (cm_rep_globals_safe globals )) (PreH5 : (cm_data_globals_wf structs globals )) (PreH6 : (cm_rep_strings_safe strings )) (PreH7 : (0 <= (cm_rep_globals_size (globals)))) (PreH8 : (0 <= (cm_rep_strings_size (strings)))) (PreH9 : (((8 + (cm_rep_globals_size (globals)) ) + (cm_rep_strings_size (strings)) ) <= capacity_pre)) (PreH10 : (capacity_pre <= INT_MAX)) ,
  (cm_global_list_rep global_node_pre globals )
  **  (UCharArray.seg data_pre 0 (8 + (cm_rep_globals_size (globals)) ) (app ((zeros (8))) ((cm_globals_bytes (structs) (globals)))) )
  **  (UCharArray.undef_seg data_pre (8 + (cm_rep_globals_size (globals)) ) capacity_pre )
  **  (cm_string_list_rep string_node_pre strings )
|--
  “ (cm_rep_strings_safe strings ) ” 
  &&  “ ((retval + (cm_rep_strings_size (strings)) ) <= capacity_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_data_globals_wf structs globals ) ” 
  &&  “ (retval = (8 + (cm_rep_globals_size (globals)) )) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_data_globals_wf structs globals ) ” 
  &&  “ (cm_rep_strings_safe strings ) ” 
  &&  “ (0 <= (cm_rep_globals_size (globals))) ” 
  &&  “ (0 <= (cm_rep_strings_size (strings))) ” 
  &&  “ (((8 + (cm_rep_globals_size (globals)) ) + (cm_rep_strings_size (strings)) ) <= capacity_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ”
  &&  (cm_string_list_rep string_node_pre strings )
  **  (UCharArray.seg data_pre 0 retval (app ((zeros (8))) ((cm_globals_bytes (structs) (globals)))) )
  **  (UCharArray.undef_seg data_pre retval capacity_pre )
  **  (cm_global_list_rep global_node_pre globals )
.

Definition cmc_emit_data_partial_solve_wit_3 := cmc_emit_data_partial_solve_wit_3_pure -> cmc_emit_data_partial_solve_wit_3_aux.

Module Type VC_Correct.


Axiom proof_of_cmc_emit_data_safety_wit_1 : cmc_emit_data_safety_wit_1.
Axiom proof_of_cmc_emit_data_safety_wit_2 : cmc_emit_data_safety_wit_2.
Axiom proof_of_cmc_emit_data_safety_wit_3 : cmc_emit_data_safety_wit_3.
Axiom proof_of_cmc_emit_data_entail_wit_1 : cmc_emit_data_entail_wit_1.
Axiom proof_of_cmc_emit_data_return_wit_1 : cmc_emit_data_return_wit_1.
Axiom proof_of_cmc_emit_data_partial_solve_wit_1_pure : cmc_emit_data_partial_solve_wit_1_pure.
Axiom proof_of_cmc_emit_data_partial_solve_wit_1 : cmc_emit_data_partial_solve_wit_1.
Axiom proof_of_cmc_emit_data_partial_solve_wit_2_pure : cmc_emit_data_partial_solve_wit_2_pure.
Axiom proof_of_cmc_emit_data_partial_solve_wit_2 : cmc_emit_data_partial_solve_wit_2.
Axiom proof_of_cmc_emit_data_partial_solve_wit_3_pure : cmc_emit_data_partial_solve_wit_3_pure.
Axiom proof_of_cmc_emit_data_partial_solve_wit_3 : cmc_emit_data_partial_solve_wit_3.

End VC_Correct.
