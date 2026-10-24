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
Require Import SimpleC.EE.QCP_demos_human.cmc_emit_strings_migration_lib.
Local Open Scope sac.

(*----- Function cmc_emit_strings -----*)

Definition cmc_emit_strings_safety_wit_1 := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (strings: (@list cm_string_d)) (PreH1 : (cm_rep_strings_safe strings )) (PreH2 : (0 <= cursor_pre)) (PreH3 : ((cursor_pre + (cm_rep_strings_size (strings)) ) <= capacity_pre)) (PreH4 : (capacity_pre <= INT_MAX)) ,
  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (cm_string_list_rep node_pre strings )
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_emit_strings_safety_wit_2 := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (sourcep: Z) (nextp: Z) (PreH1 : (cmc_uint8_buffer_nonnull sourcep (cm_string_bytes (head)) )) (PreH2 : (node_pre <> 0)) (PreH3 : (strings = (cons (head) (tail)))) (PreH4 : (cm_rep_strings_safe strings )) (PreH5 : (cm_rep_strings_safe tail )) (PreH6 : (0 <= cursor_pre)) (PreH7 : (capacity_pre <= INT_MAX)) (PreH8 : (0 <= (cm_rep_string_length (head)))) (PreH9 : ((cm_rep_string_length (head)) = (Zlength ((cm_string_bytes (head)))))) (PreH10 : (0 <= (cm_rep_strings_size (tail)))) (PreH11 : ((((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) + (cm_rep_strings_size (tail)) ) <= capacity_pre)) (PreH12 : (cmc_uint8_buffer_nonnull sourcep (cm_string_bytes (head)) )) ,
  (UCharArray.full sourcep (cm_rep_string_length (head)) (cm_string_bytes (head)) )
  **  (UCharArray.seg data_pre 0 (cursor_pre + (cm_rep_string_length (head)) ) (app (prefix) ((cm_string_bytes (head)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + (cm_rep_string_length (head)) ) capacity_pre )
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "length" ) )) # Int  |-> (cm_rep_string_length (head)))
  **  ((( &( "source" ) )) # Ptr  |-> sourcep)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> sourcep)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_string_list_rep nextp tail )
|--
  “ ((cursor_pre + (cm_rep_string_length (head)) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cursor_pre + (cm_rep_string_length (head)) )) ”
.

Definition cmc_emit_strings_safety_wit_3 := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (sourcep: Z) (nextp: Z) (PreH1 : (cmc_uint8_buffer_nonnull sourcep (cm_string_bytes (head)) )) (PreH2 : (node_pre <> 0)) (PreH3 : (strings = (cons (head) (tail)))) (PreH4 : (cm_rep_strings_safe strings )) (PreH5 : (cm_rep_strings_safe tail )) (PreH6 : (0 <= cursor_pre)) (PreH7 : (capacity_pre <= INT_MAX)) (PreH8 : (0 <= (cm_rep_string_length (head)))) (PreH9 : ((cm_rep_string_length (head)) = (Zlength ((cm_string_bytes (head)))))) (PreH10 : (0 <= (cm_rep_strings_size (tail)))) (PreH11 : ((((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) + (cm_rep_strings_size (tail)) ) <= capacity_pre)) (PreH12 : (cmc_uint8_buffer_nonnull sourcep (cm_string_bytes (head)) )) ,
  (UCharArray.full sourcep (cm_rep_string_length (head)) (cm_string_bytes (head)) )
  **  (UCharArray.seg data_pre 0 (cursor_pre + (cm_rep_string_length (head)) ) (app (prefix) ((cm_string_bytes (head)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + (cm_rep_string_length (head)) ) capacity_pre )
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "length" ) )) # Int  |-> (cm_rep_string_length (head)))
  **  ((( &( "source" ) )) # Ptr  |-> sourcep)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> sourcep)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_string_list_rep nextp tail )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_emit_strings_safety_wit_4 := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (sourcep: Z) (nextp: Z) (PreH1 : (cmc_uint8_buffer_nonnull sourcep (cm_string_bytes (head)) )) (PreH2 : (node_pre <> 0)) (PreH3 : (strings = (cons (head) (tail)))) (PreH4 : (cm_rep_strings_safe strings )) (PreH5 : (cm_rep_strings_safe tail )) (PreH6 : (0 <= cursor_pre)) (PreH7 : (capacity_pre <= INT_MAX)) (PreH8 : (0 <= (cm_rep_string_length (head)))) (PreH9 : ((cm_rep_string_length (head)) = (Zlength ((cm_string_bytes (head)))))) (PreH10 : (0 <= (cm_rep_strings_size (tail)))) (PreH11 : ((((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) + (cm_rep_strings_size (tail)) ) <= capacity_pre)) (PreH12 : (cmc_uint8_buffer_nonnull sourcep (cm_string_bytes (head)) )) ,
  ((( &( "final_cursor" ) )) # Int  |->_)
  **  (UCharArray.seg data_pre 0 ((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) (app ((app (prefix) ((cm_string_bytes (head))))) ((cons (0) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre ((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) capacity_pre )
  **  (UCharArray.full sourcep (cm_rep_string_length (head)) (cm_string_bytes (head)) )
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "length" ) )) # Int  |-> (cm_rep_string_length (head)))
  **  ((( &( "source" ) )) # Ptr  |-> sourcep)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> sourcep)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_string_list_rep nextp tail )
|--
  “ (((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((cursor_pre + (cm_rep_string_length (head)) ) + 1 )) ”
.

Definition cmc_emit_strings_safety_wit_5 := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (sourcep: Z) (nextp: Z) (PreH1 : (cmc_uint8_buffer_nonnull sourcep (cm_string_bytes (head)) )) (PreH2 : (node_pre <> 0)) (PreH3 : (strings = (cons (head) (tail)))) (PreH4 : (cm_rep_strings_safe strings )) (PreH5 : (cm_rep_strings_safe tail )) (PreH6 : (0 <= cursor_pre)) (PreH7 : (capacity_pre <= INT_MAX)) (PreH8 : (0 <= (cm_rep_string_length (head)))) (PreH9 : ((cm_rep_string_length (head)) = (Zlength ((cm_string_bytes (head)))))) (PreH10 : (0 <= (cm_rep_strings_size (tail)))) (PreH11 : ((((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) + (cm_rep_strings_size (tail)) ) <= capacity_pre)) (PreH12 : (cmc_uint8_buffer_nonnull sourcep (cm_string_bytes (head)) )) ,
  ((( &( "final_cursor" ) )) # Int  |->_)
  **  (UCharArray.seg data_pre 0 ((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) (app ((app (prefix) ((cm_string_bytes (head))))) ((cons (0) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre ((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) capacity_pre )
  **  (UCharArray.full sourcep (cm_rep_string_length (head)) (cm_string_bytes (head)) )
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "length" ) )) # Int  |-> (cm_rep_string_length (head)))
  **  ((( &( "source" ) )) # Ptr  |-> sourcep)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> sourcep)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_string_list_rep nextp tail )
|--
  “ ((cursor_pre + (cm_rep_string_length (head)) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cursor_pre + (cm_rep_string_length (head)) )) ”
.

Definition cmc_emit_strings_safety_wit_6 := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (sourcep: Z) (nextp: Z) (PreH1 : (cmc_uint8_buffer_nonnull sourcep (cm_string_bytes (head)) )) (PreH2 : (node_pre <> 0)) (PreH3 : (strings = (cons (head) (tail)))) (PreH4 : (cm_rep_strings_safe strings )) (PreH5 : (cm_rep_strings_safe tail )) (PreH6 : (0 <= cursor_pre)) (PreH7 : (capacity_pre <= INT_MAX)) (PreH8 : (0 <= (cm_rep_string_length (head)))) (PreH9 : ((cm_rep_string_length (head)) = (Zlength ((cm_string_bytes (head)))))) (PreH10 : (0 <= (cm_rep_strings_size (tail)))) (PreH11 : ((((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) + (cm_rep_strings_size (tail)) ) <= capacity_pre)) (PreH12 : (cmc_uint8_buffer_nonnull sourcep (cm_string_bytes (head)) )) ,
  ((( &( "final_cursor" ) )) # Int  |->_)
  **  (UCharArray.seg data_pre 0 ((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) (app ((app (prefix) ((cm_string_bytes (head))))) ((cons (0) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre ((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) capacity_pre )
  **  (UCharArray.full sourcep (cm_rep_string_length (head)) (cm_string_bytes (head)) )
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "length" ) )) # Int  |-> (cm_rep_string_length (head)))
  **  ((( &( "source" ) )) # Ptr  |-> sourcep)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> sourcep)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_string_list_rep nextp tail )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmc_emit_strings_entail_wit_1 := 
(
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (strings: (@list cm_string_d)) (PreH1 : (node_pre <> 0)) (PreH2 : (cm_rep_strings_safe strings )) (PreH3 : (0 <= cursor_pre)) (PreH4 : ((cursor_pre + (cm_rep_strings_size (strings)) ) <= capacity_pre)) (PreH5 : (capacity_pre <= INT_MAX)) ,
  (cm_string_list_rep node_pre strings )
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  EX (nextp: Z)  (sourcep: Z)  (head: cm_string_d)  (tail: (@list cm_string_d)) ,
  “ (node_pre <> 0) ” 
  &&  “ (strings = (cons (head) (tail))) ” 
  &&  “ (cm_rep_strings_safe strings ) ” 
  &&  “ (cm_rep_strings_safe tail ) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ (0 <= (cm_rep_string_length (head))) ” 
  &&  “ ((cm_rep_string_length (head)) = (Zlength ((cm_string_bytes (head))))) ” 
  &&  “ (0 <= (cm_rep_strings_size (tail))) ” 
  &&  “ ((((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) + (cm_rep_strings_size (tail)) ) <= capacity_pre) ” 
  &&  “ (cmc_uint8_buffer_nonnull sourcep (cm_string_bytes (head)) ) ”
  &&  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> sourcep)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
  **  (UCharArray.full sourcep (cm_rep_string_length (head)) (cm_string_bytes (head)) )
  **  (cm_string_list_rep nextp tail )
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
) \/
(
forall (cursor_pre: Z) (capacity_pre: Z) (node_pre: Z) (strings: (@list cm_string_d)) (PreH1 : (node_pre <> 0)) (PreH2 : (cm_rep_strings_safe strings )) (PreH3 : (0 <= cursor_pre)) (PreH4 : ((cursor_pre + (cm_rep_strings_size (strings)) ) <= capacity_pre)) (PreH5 : (capacity_pre <= INT_MAX)) ,
  (cm_string_list_rep node_pre strings )
|--
  EX (nextp: Z)  (sourcep: Z)  (head: cm_string_d)  (tail: (@list cm_string_d)) ,
  “ (node_pre <> 0) ” 
  &&  “ (strings = (cons (head) (tail))) ” 
  &&  “ (cm_rep_strings_safe strings ) ” 
  &&  “ (cm_rep_strings_safe tail ) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ (0 <= (cm_rep_string_length (head))) ” 
  &&  “ ((cm_rep_string_length (head)) = (Zlength ((cm_string_bytes (head))))) ” 
  &&  “ (0 <= (cm_rep_strings_size (tail))) ” 
  &&  “ ((((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) + (cm_rep_strings_size (tail)) ) <= capacity_pre) ” 
  &&  “ (cmc_uint8_buffer_nonnull sourcep (cm_string_bytes (head)) ) ”
  &&  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> sourcep)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
  **  (UCharArray.full sourcep (cm_rep_string_length (head)) (cm_string_bytes (head)) )
  **  (cm_string_list_rep nextp tail )
).

Definition cmc_emit_strings_return_wit_1 := 
(
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (sourcep: Z) (nextp: Z) (retval: Z) (PreH1 : (cm_rep_strings_safe tail )) (PreH2 : (retval = (((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) + (cm_rep_strings_size (tail)) ))) (PreH3 : (cmc_uint8_buffer_nonnull sourcep (cm_string_bytes (head)) )) (PreH4 : (node_pre <> 0)) (PreH5 : (strings = (cons (head) (tail)))) (PreH6 : (cm_rep_strings_safe strings )) (PreH7 : (cm_rep_strings_safe tail )) (PreH8 : (0 <= cursor_pre)) (PreH9 : (capacity_pre <= INT_MAX)) (PreH10 : (0 <= (cm_rep_string_length (head)))) (PreH11 : ((cm_rep_string_length (head)) = (Zlength ((cm_string_bytes (head)))))) (PreH12 : (0 <= (cm_rep_strings_size (tail)))) (PreH13 : ((((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) + (cm_rep_strings_size (tail)) ) <= capacity_pre)) (PreH14 : (cmc_uint8_buffer_nonnull sourcep (cm_string_bytes (head)) )) ,
  (cm_string_list_rep nextp tail )
  **  (UCharArray.seg data_pre 0 (((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) + (cm_rep_strings_size (tail)) ) (app ((app ((app (prefix) ((cm_string_bytes (head))))) ((cons (0) ((@nil Z)))))) ((cm_strings_bytes (tail)))) )
  **  (UCharArray.undef_seg data_pre (((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) + (cm_rep_strings_size (tail)) ) capacity_pre )
  **  (UCharArray.full sourcep (cm_rep_string_length (head)) (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> sourcep)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (cm_rep_strings_safe strings ) ” 
  &&  “ (retval = (cursor_pre + (cm_rep_strings_size (strings)) )) ”
  &&  (cm_string_list_rep node_pre strings )
  **  (UCharArray.seg data_pre 0 (cursor_pre + (cm_rep_strings_size (strings)) ) (app (prefix) ((cm_strings_bytes (strings)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + (cm_rep_strings_size (strings)) ) capacity_pre )
) \/
(
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (sourcep: Z) (nextp: Z) (retval: Z) (PreH1 : ((cm_rep_string_length (head)) <= INT_MAX)) (PreH2 : ((cm_rep_string_length (head)) >= INT_MIN)) (PreH3 : (cm_rep_strings_safe tail )) (PreH4 : (retval = (((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) + (cm_rep_strings_size (tail)) ))) (PreH5 : (cmc_uint8_buffer_nonnull sourcep (cm_string_bytes (head)) )) (PreH6 : (node_pre <> 0)) (PreH7 : (strings = (cons (head) (tail)))) (PreH8 : (cm_rep_strings_safe strings )) (PreH9 : (cm_rep_strings_safe tail )) (PreH10 : (0 <= cursor_pre)) (PreH11 : (capacity_pre <= INT_MAX)) (PreH12 : (0 <= (cm_rep_string_length (head)))) (PreH13 : ((cm_rep_string_length (head)) = (Zlength ((cm_string_bytes (head)))))) (PreH14 : (0 <= (cm_rep_strings_size (tail)))) (PreH15 : ((((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) + (cm_rep_strings_size (tail)) ) <= capacity_pre)) (PreH16 : (cmc_uint8_buffer_nonnull sourcep (cm_string_bytes (head)) )) ,
  (cm_string_list_rep nextp tail )
  **  (UCharArray.seg data_pre 0 (((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) + (cm_rep_strings_size (tail)) ) (app ((app ((app (prefix) ((cm_string_bytes (head))))) ((cons (0) ((@nil Z)))))) ((cm_strings_bytes (tail)))) )
  **  (UCharArray.undef_seg data_pre (((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) + (cm_rep_strings_size (tail)) ) capacity_pre )
  **  (UCharArray.full sourcep (cm_rep_string_length (head)) (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> sourcep)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (retval = (cursor_pre + (cm_rep_strings_size (strings)) )) ”
  &&  (cm_string_list_rep node_pre strings )
  **  (UCharArray.seg data_pre 0 (cursor_pre + (cm_rep_strings_size (strings)) ) (app (prefix) ((cm_strings_bytes (strings)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + (cm_rep_strings_size (strings)) ) capacity_pre )
).

Definition cmc_emit_strings_return_wit_1_split_goal_1 := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (sourcep: Z) (nextp: Z) (retval: Z) (PreH1 : ((cm_rep_string_length (head)) <= INT_MAX)) (PreH2 : ((cm_rep_string_length (head)) >= INT_MIN)) (PreH3 : (cm_rep_strings_safe tail )) (PreH4 : (retval = (((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) + (cm_rep_strings_size (tail)) ))) (PreH5 : (cmc_uint8_buffer_nonnull sourcep (cm_string_bytes (head)) )) (PreH6 : (node_pre <> 0)) (PreH7 : (strings = (cons (head) (tail)))) (PreH8 : (cm_rep_strings_safe strings )) (PreH9 : (cm_rep_strings_safe tail )) (PreH10 : (0 <= cursor_pre)) (PreH11 : (capacity_pre <= INT_MAX)) (PreH12 : (0 <= (cm_rep_string_length (head)))) (PreH13 : ((cm_rep_string_length (head)) = (Zlength ((cm_string_bytes (head)))))) (PreH14 : (0 <= (cm_rep_strings_size (tail)))) (PreH15 : ((((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) + (cm_rep_strings_size (tail)) ) <= capacity_pre)) (PreH16 : (cmc_uint8_buffer_nonnull sourcep (cm_string_bytes (head)) )) ,
  (cm_string_list_rep nextp tail )
  **  (UCharArray.seg data_pre 0 (((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) + (cm_rep_strings_size (tail)) ) (app ((app ((app (prefix) ((cm_string_bytes (head))))) ((cons (0) ((@nil Z)))))) ((cm_strings_bytes (tail)))) )
  **  (UCharArray.undef_seg data_pre (((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) + (cm_rep_strings_size (tail)) ) capacity_pre )
  **  (UCharArray.full sourcep (cm_rep_string_length (head)) (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> sourcep)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (retval = (cursor_pre + (cm_rep_strings_size (strings)) )) ”
.

Definition cmc_emit_strings_return_wit_1_split_goal_spatial := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (sourcep: Z) (nextp: Z) (retval: Z) (PreH1 : ((cm_rep_string_length (head)) <= INT_MAX)) (PreH2 : ((cm_rep_string_length (head)) >= INT_MIN)) (PreH3 : (cm_rep_strings_safe tail )) (PreH4 : (retval = (((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) + (cm_rep_strings_size (tail)) ))) (PreH5 : (cmc_uint8_buffer_nonnull sourcep (cm_string_bytes (head)) )) (PreH6 : (node_pre <> 0)) (PreH7 : (strings = (cons (head) (tail)))) (PreH8 : (cm_rep_strings_safe strings )) (PreH9 : (cm_rep_strings_safe tail )) (PreH10 : (0 <= cursor_pre)) (PreH11 : (capacity_pre <= INT_MAX)) (PreH12 : (0 <= (cm_rep_string_length (head)))) (PreH13 : ((cm_rep_string_length (head)) = (Zlength ((cm_string_bytes (head)))))) (PreH14 : (0 <= (cm_rep_strings_size (tail)))) (PreH15 : ((((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) + (cm_rep_strings_size (tail)) ) <= capacity_pre)) (PreH16 : (cmc_uint8_buffer_nonnull sourcep (cm_string_bytes (head)) )) ,
  (cm_string_list_rep nextp tail )
  **  (UCharArray.seg data_pre 0 (((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) + (cm_rep_strings_size (tail)) ) (app ((app ((app (prefix) ((cm_string_bytes (head))))) ((cons (0) ((@nil Z)))))) ((cm_strings_bytes (tail)))) )
  **  (UCharArray.undef_seg data_pre (((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) + (cm_rep_strings_size (tail)) ) capacity_pre )
  **  (UCharArray.full sourcep (cm_rep_string_length (head)) (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> sourcep)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
|--
  (cm_string_list_rep node_pre strings )
  **  (UCharArray.seg data_pre 0 (cursor_pre + (cm_rep_strings_size (strings)) ) (app (prefix) ((cm_strings_bytes (strings)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + (cm_rep_strings_size (strings)) ) capacity_pre )
.

Definition cmc_emit_strings_return_wit_2 := 
(
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (strings: (@list cm_string_d)) (PreH1 : (node_pre = 0)) (PreH2 : (cm_rep_strings_safe strings )) (PreH3 : (0 <= cursor_pre)) (PreH4 : ((cursor_pre + (cm_rep_strings_size (strings)) ) <= capacity_pre)) (PreH5 : (capacity_pre <= INT_MAX)) ,
  (cm_string_list_rep node_pre strings )
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (cm_rep_strings_safe strings ) ” 
  &&  “ (cursor_pre = (cursor_pre + (cm_rep_strings_size (strings)) )) ”
  &&  (cm_string_list_rep node_pre strings )
  **  (UCharArray.seg data_pre 0 (cursor_pre + (cm_rep_strings_size (strings)) ) (app (prefix) ((cm_strings_bytes (strings)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + (cm_rep_strings_size (strings)) ) capacity_pre )
) \/
(
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (strings: (@list cm_string_d)) (PreH1 : (node_pre = 0)) (PreH2 : (cm_rep_strings_safe strings )) (PreH3 : (0 <= cursor_pre)) (PreH4 : ((cursor_pre + (cm_rep_strings_size (strings)) ) <= capacity_pre)) (PreH5 : (capacity_pre <= INT_MAX)) ,
  (cm_string_list_rep node_pre strings )
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (cursor_pre = (cursor_pre + (cm_rep_strings_size (strings)) )) ”
  &&  (cm_string_list_rep node_pre strings )
  **  (UCharArray.seg data_pre 0 (cursor_pre + (cm_rep_strings_size (strings)) ) (app (prefix) ((cm_strings_bytes (strings)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + (cm_rep_strings_size (strings)) ) capacity_pre )
).

Definition cmc_emit_strings_return_wit_2_split_goal_1 := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (strings: (@list cm_string_d)) (PreH1 : (node_pre = 0)) (PreH2 : (cm_rep_strings_safe strings )) (PreH3 : (0 <= cursor_pre)) (PreH4 : ((cursor_pre + (cm_rep_strings_size (strings)) ) <= capacity_pre)) (PreH5 : (capacity_pre <= INT_MAX)) ,
  (cm_string_list_rep node_pre strings )
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (cursor_pre = (cursor_pre + (cm_rep_strings_size (strings)) )) ”
.

Definition cmc_emit_strings_return_wit_2_split_goal_spatial := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (strings: (@list cm_string_d)) (PreH1 : (node_pre = 0)) (PreH2 : (cm_rep_strings_safe strings )) (PreH3 : (0 <= cursor_pre)) (PreH4 : ((cursor_pre + (cm_rep_strings_size (strings)) ) <= capacity_pre)) (PreH5 : (capacity_pre <= INT_MAX)) ,
  (cm_string_list_rep node_pre strings )
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  (cm_string_list_rep node_pre strings )
  **  (UCharArray.seg data_pre 0 (cursor_pre + (cm_rep_strings_size (strings)) ) (app (prefix) ((cm_strings_bytes (strings)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + (cm_rep_strings_size (strings)) ) capacity_pre )
.

Definition cmc_emit_strings_partial_solve_wit_1_pure := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (sourcep: Z) (nextp: Z) (PreH1 : (node_pre <> 0)) (PreH2 : (strings = (cons (head) (tail)))) (PreH3 : (cm_rep_strings_safe strings )) (PreH4 : (cm_rep_strings_safe tail )) (PreH5 : (0 <= cursor_pre)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (0 <= (cm_rep_string_length (head)))) (PreH8 : ((cm_rep_string_length (head)) = (Zlength ((cm_string_bytes (head)))))) (PreH9 : (0 <= (cm_rep_strings_size (tail)))) (PreH10 : ((((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) + (cm_rep_strings_size (tail)) ) <= capacity_pre)) (PreH11 : (cmc_uint8_buffer_nonnull sourcep (cm_string_bytes (head)) )) ,
  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "length" ) )) # Int  |-> (cm_rep_string_length (head)))
  **  ((( &( "source" ) )) # Ptr  |-> sourcep)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> sourcep)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
  **  (UCharArray.full sourcep (cm_rep_string_length (head)) (cm_string_bytes (head)) )
  **  (cm_string_list_rep nextp tail )
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (0 <= (cm_rep_string_length (head))) ” 
  &&  “ ((Zlength ((cm_string_bytes (head)))) = (cm_rep_string_length (head))) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ ((cursor_pre + (cm_rep_string_length (head)) ) <= capacity_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ (cmc_uint8_buffer_nonnull sourcep (cm_string_bytes (head)) ) ”
.

Definition cmc_emit_strings_partial_solve_wit_1_aux := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (sourcep: Z) (nextp: Z) (PreH1 : (node_pre <> 0)) (PreH2 : (strings = (cons (head) (tail)))) (PreH3 : (cm_rep_strings_safe strings )) (PreH4 : (cm_rep_strings_safe tail )) (PreH5 : (0 <= cursor_pre)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (0 <= (cm_rep_string_length (head)))) (PreH8 : ((cm_rep_string_length (head)) = (Zlength ((cm_string_bytes (head)))))) (PreH9 : (0 <= (cm_rep_strings_size (tail)))) (PreH10 : ((((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) + (cm_rep_strings_size (tail)) ) <= capacity_pre)) (PreH11 : (cmc_uint8_buffer_nonnull sourcep (cm_string_bytes (head)) )) ,
  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> sourcep)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
  **  (UCharArray.full sourcep (cm_rep_string_length (head)) (cm_string_bytes (head)) )
  **  (cm_string_list_rep nextp tail )
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (0 <= (cm_rep_string_length (head))) ” 
  &&  “ ((Zlength ((cm_string_bytes (head)))) = (cm_rep_string_length (head))) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ ((cursor_pre + (cm_rep_string_length (head)) ) <= capacity_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ (cmc_uint8_buffer_nonnull sourcep (cm_string_bytes (head)) ) ” 
  &&  “ (node_pre <> 0) ” 
  &&  “ (strings = (cons (head) (tail))) ” 
  &&  “ (cm_rep_strings_safe strings ) ” 
  &&  “ (cm_rep_strings_safe tail ) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ (0 <= (cm_rep_string_length (head))) ” 
  &&  “ ((cm_rep_string_length (head)) = (Zlength ((cm_string_bytes (head))))) ” 
  &&  “ (0 <= (cm_rep_strings_size (tail))) ” 
  &&  “ ((((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) + (cm_rep_strings_size (tail)) ) <= capacity_pre) ” 
  &&  “ (cmc_uint8_buffer_nonnull sourcep (cm_string_bytes (head)) ) ”
  &&  (UCharArray.full sourcep (cm_rep_string_length (head)) (cm_string_bytes (head)) )
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> sourcep)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_string_list_rep nextp tail )
.

Definition cmc_emit_strings_partial_solve_wit_1 := cmc_emit_strings_partial_solve_wit_1_pure -> cmc_emit_strings_partial_solve_wit_1_aux.

Definition cmc_emit_strings_partial_solve_wit_2_pure := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (sourcep: Z) (nextp: Z) (PreH1 : (cmc_uint8_buffer_nonnull sourcep (cm_string_bytes (head)) )) (PreH2 : (node_pre <> 0)) (PreH3 : (strings = (cons (head) (tail)))) (PreH4 : (cm_rep_strings_safe strings )) (PreH5 : (cm_rep_strings_safe tail )) (PreH6 : (0 <= cursor_pre)) (PreH7 : (capacity_pre <= INT_MAX)) (PreH8 : (0 <= (cm_rep_string_length (head)))) (PreH9 : ((cm_rep_string_length (head)) = (Zlength ((cm_string_bytes (head)))))) (PreH10 : (0 <= (cm_rep_strings_size (tail)))) (PreH11 : ((((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) + (cm_rep_strings_size (tail)) ) <= capacity_pre)) (PreH12 : (cmc_uint8_buffer_nonnull sourcep (cm_string_bytes (head)) )) ,
  (UCharArray.full sourcep (cm_rep_string_length (head)) (cm_string_bytes (head)) )
  **  (UCharArray.seg data_pre 0 (cursor_pre + (cm_rep_string_length (head)) ) (app (prefix) ((cm_string_bytes (head)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + (cm_rep_string_length (head)) ) capacity_pre )
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "length" ) )) # Int  |-> (cm_rep_string_length (head)))
  **  ((( &( "source" ) )) # Ptr  |-> sourcep)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> sourcep)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_string_list_rep nextp tail )
|--
  “ (0 <= (cursor_pre + (cm_rep_string_length (head)) )) ” 
  &&  “ ((cursor_pre + (cm_rep_string_length (head)) ) < capacity_pre) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < 256) ”
.

Definition cmc_emit_strings_partial_solve_wit_2_aux := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (sourcep: Z) (nextp: Z) (PreH1 : (cmc_uint8_buffer_nonnull sourcep (cm_string_bytes (head)) )) (PreH2 : (node_pre <> 0)) (PreH3 : (strings = (cons (head) (tail)))) (PreH4 : (cm_rep_strings_safe strings )) (PreH5 : (cm_rep_strings_safe tail )) (PreH6 : (0 <= cursor_pre)) (PreH7 : (capacity_pre <= INT_MAX)) (PreH8 : (0 <= (cm_rep_string_length (head)))) (PreH9 : ((cm_rep_string_length (head)) = (Zlength ((cm_string_bytes (head)))))) (PreH10 : (0 <= (cm_rep_strings_size (tail)))) (PreH11 : ((((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) + (cm_rep_strings_size (tail)) ) <= capacity_pre)) (PreH12 : (cmc_uint8_buffer_nonnull sourcep (cm_string_bytes (head)) )) ,
  (UCharArray.full sourcep (cm_rep_string_length (head)) (cm_string_bytes (head)) )
  **  (UCharArray.seg data_pre 0 (cursor_pre + (cm_rep_string_length (head)) ) (app (prefix) ((cm_string_bytes (head)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + (cm_rep_string_length (head)) ) capacity_pre )
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> sourcep)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_string_list_rep nextp tail )
|--
  “ (0 <= (cursor_pre + (cm_rep_string_length (head)) )) ” 
  &&  “ ((cursor_pre + (cm_rep_string_length (head)) ) < capacity_pre) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < 256) ” 
  &&  “ (cmc_uint8_buffer_nonnull sourcep (cm_string_bytes (head)) ) ” 
  &&  “ (node_pre <> 0) ” 
  &&  “ (strings = (cons (head) (tail))) ” 
  &&  “ (cm_rep_strings_safe strings ) ” 
  &&  “ (cm_rep_strings_safe tail ) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ (0 <= (cm_rep_string_length (head))) ” 
  &&  “ ((cm_rep_string_length (head)) = (Zlength ((cm_string_bytes (head))))) ” 
  &&  “ (0 <= (cm_rep_strings_size (tail))) ” 
  &&  “ ((((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) + (cm_rep_strings_size (tail)) ) <= capacity_pre) ” 
  &&  “ (cmc_uint8_buffer_nonnull sourcep (cm_string_bytes (head)) ) ”
  &&  (UCharArray.seg data_pre 0 (cursor_pre + (cm_rep_string_length (head)) ) (app (prefix) ((cm_string_bytes (head)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + (cm_rep_string_length (head)) ) capacity_pre )
  **  (UCharArray.full sourcep (cm_rep_string_length (head)) (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> sourcep)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_string_list_rep nextp tail )
.

Definition cmc_emit_strings_partial_solve_wit_2 := cmc_emit_strings_partial_solve_wit_2_pure -> cmc_emit_strings_partial_solve_wit_2_aux.

Definition cmc_emit_strings_partial_solve_wit_3_pure := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (sourcep: Z) (nextp: Z) (PreH1 : (cmc_uint8_buffer_nonnull sourcep (cm_string_bytes (head)) )) (PreH2 : (node_pre <> 0)) (PreH3 : (strings = (cons (head) (tail)))) (PreH4 : (cm_rep_strings_safe strings )) (PreH5 : (cm_rep_strings_safe tail )) (PreH6 : (0 <= cursor_pre)) (PreH7 : (capacity_pre <= INT_MAX)) (PreH8 : (0 <= (cm_rep_string_length (head)))) (PreH9 : ((cm_rep_string_length (head)) = (Zlength ((cm_string_bytes (head)))))) (PreH10 : (0 <= (cm_rep_strings_size (tail)))) (PreH11 : ((((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) + (cm_rep_strings_size (tail)) ) <= capacity_pre)) (PreH12 : (cmc_uint8_buffer_nonnull sourcep (cm_string_bytes (head)) )) ,
  ((( &( "final_cursor" ) )) # Int  |->_)
  **  (UCharArray.seg data_pre 0 ((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) (app ((app (prefix) ((cm_string_bytes (head))))) ((cons (0) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre ((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) capacity_pre )
  **  (UCharArray.full sourcep (cm_rep_string_length (head)) (cm_string_bytes (head)) )
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "length" ) )) # Int  |-> (cm_rep_string_length (head)))
  **  ((( &( "source" ) )) # Ptr  |-> sourcep)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> sourcep)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_string_list_rep nextp tail )
|--
  “ (cm_rep_strings_safe tail ) ” 
  &&  “ (0 <= ((cursor_pre + (cm_rep_string_length (head)) ) + 1 )) ” 
  &&  “ ((((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) + (cm_rep_strings_size (tail)) ) <= capacity_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ”
.

Definition cmc_emit_strings_partial_solve_wit_3_aux := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (node_pre: Z) (prefix: (@list Z)) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (sourcep: Z) (nextp: Z) (PreH1 : (cmc_uint8_buffer_nonnull sourcep (cm_string_bytes (head)) )) (PreH2 : (node_pre <> 0)) (PreH3 : (strings = (cons (head) (tail)))) (PreH4 : (cm_rep_strings_safe strings )) (PreH5 : (cm_rep_strings_safe tail )) (PreH6 : (0 <= cursor_pre)) (PreH7 : (capacity_pre <= INT_MAX)) (PreH8 : (0 <= (cm_rep_string_length (head)))) (PreH9 : ((cm_rep_string_length (head)) = (Zlength ((cm_string_bytes (head)))))) (PreH10 : (0 <= (cm_rep_strings_size (tail)))) (PreH11 : ((((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) + (cm_rep_strings_size (tail)) ) <= capacity_pre)) (PreH12 : (cmc_uint8_buffer_nonnull sourcep (cm_string_bytes (head)) )) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) (app ((app (prefix) ((cm_string_bytes (head))))) ((cons (0) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre ((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) capacity_pre )
  **  (UCharArray.full sourcep (cm_rep_string_length (head)) (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> sourcep)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_string_list_rep nextp tail )
|--
  “ (cm_rep_strings_safe tail ) ” 
  &&  “ (0 <= ((cursor_pre + (cm_rep_string_length (head)) ) + 1 )) ” 
  &&  “ ((((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) + (cm_rep_strings_size (tail)) ) <= capacity_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ (cmc_uint8_buffer_nonnull sourcep (cm_string_bytes (head)) ) ” 
  &&  “ (node_pre <> 0) ” 
  &&  “ (strings = (cons (head) (tail))) ” 
  &&  “ (cm_rep_strings_safe strings ) ” 
  &&  “ (cm_rep_strings_safe tail ) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ (0 <= (cm_rep_string_length (head))) ” 
  &&  “ ((cm_rep_string_length (head)) = (Zlength ((cm_string_bytes (head))))) ” 
  &&  “ (0 <= (cm_rep_strings_size (tail))) ” 
  &&  “ ((((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) + (cm_rep_strings_size (tail)) ) <= capacity_pre) ” 
  &&  “ (cmc_uint8_buffer_nonnull sourcep (cm_string_bytes (head)) ) ”
  &&  (cm_string_list_rep nextp tail )
  **  (UCharArray.seg data_pre 0 ((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) (app ((app (prefix) ((cm_string_bytes (head))))) ((cons (0) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre ((cursor_pre + (cm_rep_string_length (head)) ) + 1 ) capacity_pre )
  **  (UCharArray.full sourcep (cm_rep_string_length (head)) (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> sourcep)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
.

Definition cmc_emit_strings_partial_solve_wit_3 := cmc_emit_strings_partial_solve_wit_3_pure -> cmc_emit_strings_partial_solve_wit_3_aux.

Module Type VC_Correct.


Axiom proof_of_cmc_emit_strings_safety_wit_1 : cmc_emit_strings_safety_wit_1.
Axiom proof_of_cmc_emit_strings_safety_wit_2 : cmc_emit_strings_safety_wit_2.
Axiom proof_of_cmc_emit_strings_safety_wit_3 : cmc_emit_strings_safety_wit_3.
Axiom proof_of_cmc_emit_strings_safety_wit_4 : cmc_emit_strings_safety_wit_4.
Axiom proof_of_cmc_emit_strings_safety_wit_5 : cmc_emit_strings_safety_wit_5.
Axiom proof_of_cmc_emit_strings_safety_wit_6 : cmc_emit_strings_safety_wit_6.
Axiom proof_of_cmc_emit_strings_entail_wit_1 : cmc_emit_strings_entail_wit_1.
Axiom proof_of_cmc_emit_strings_return_wit_1 : cmc_emit_strings_return_wit_1.
Axiom proof_of_cmc_emit_strings_return_wit_2 : cmc_emit_strings_return_wit_2.
Axiom proof_of_cmc_emit_strings_partial_solve_wit_1_pure : cmc_emit_strings_partial_solve_wit_1_pure.
Axiom proof_of_cmc_emit_strings_partial_solve_wit_1 : cmc_emit_strings_partial_solve_wit_1.
Axiom proof_of_cmc_emit_strings_partial_solve_wit_2_pure : cmc_emit_strings_partial_solve_wit_2_pure.
Axiom proof_of_cmc_emit_strings_partial_solve_wit_2 : cmc_emit_strings_partial_solve_wit_2.
Axiom proof_of_cmc_emit_strings_partial_solve_wit_3_pure : cmc_emit_strings_partial_solve_wit_3_pure.
Axiom proof_of_cmc_emit_strings_partial_solve_wit_3 : cmc_emit_strings_partial_solve_wit_3.

End VC_Correct.
