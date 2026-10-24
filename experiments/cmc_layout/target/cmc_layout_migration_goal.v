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
Require Import SimpleC.EE.QCP_demos_human.cmc_layout_migration_lib.
Local Open Scope sac.

(*----- Function cm_max -----*)

Definition cm_max_return_wit_1 := 
(
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <= b_pre)) ,
  TT && emp 
|--
  “ (b_pre = (cm_imax (a_pre) (b_pre))) ”
  &&  emp
) \/
(
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <= b_pre)) ,
  TT && emp 
|--
  “ (b_pre = (cm_imax (a_pre) (b_pre))) ”
  &&  emp
).

Definition cm_max_return_wit_1_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <= b_pre)) ,
  (b_pre = (cm_imax (a_pre) (b_pre)))
.

Definition cm_max_return_wit_2 := 
(
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre > b_pre)) ,
  TT && emp 
|--
  “ (a_pre = (cm_imax (a_pre) (b_pre))) ”
  &&  emp
) \/
(
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre > b_pre)) ,
  TT && emp 
|--
  “ (a_pre = (cm_imax (a_pre) (b_pre))) ”
  &&  emp
).

Definition cm_max_return_wit_2_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre > b_pre)) ,
  (a_pre = (cm_imax (a_pre) (b_pre)))
.

(*----- Function cmc_is_pointer -----*)

Definition cmc_is_pointer_safety_wit_1 := 
forall (ty_pre: Z) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (1024 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1024) ”
.

Definition cmc_is_pointer_safety_wit_2 := 
forall (ty_pre: Z) (PreH1 : (ty_pre >= 1024)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmc_is_pointer_safety_wit_3 := 
forall (ty_pre: Z) (PreH1 : (ty_pre < 1024)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_is_pointer_return_wit_1 := 
(
forall (ty_pre: Z) (PreH1 : (ty_pre >= 1024)) ,
  TT && emp 
|--
  “ (1 = (cm_rep_is_pointer_code (ty_pre))) ”
  &&  emp
) \/
(
forall (ty_pre: Z) (PreH1 : (ty_pre >= 1024)) ,
  TT && emp 
|--
  “ (1 = (cm_rep_is_pointer_code (ty_pre))) ”
  &&  emp
).

Definition cmc_is_pointer_return_wit_1_split_goal_1 := 
forall (ty_pre: Z) (PreH1 : (ty_pre >= 1024)) ,
  (1 = (cm_rep_is_pointer_code (ty_pre)))
.

Definition cmc_is_pointer_return_wit_2 := 
(
forall (ty_pre: Z) (PreH1 : (ty_pre < 1024)) ,
  TT && emp 
|--
  “ (0 = (cm_rep_is_pointer_code (ty_pre))) ”
  &&  emp
) \/
(
forall (ty_pre: Z) (PreH1 : (ty_pre < 1024)) ,
  TT && emp 
|--
  “ (0 = (cm_rep_is_pointer_code (ty_pre))) ”
  &&  emp
).

Definition cmc_is_pointer_return_wit_2_split_goal_1 := 
forall (ty_pre: Z) (PreH1 : (ty_pre < 1024)) ,
  (0 = (cm_rep_is_pointer_code (ty_pre)))
.

(*----- Function cmc_is_pointer_value -----*)

Definition cmc_is_pointer_value_return_wit_1 := 
forall (pointer_pre: Z) (ty_pre: Z) (retval: Z) (PreH1 : (retval = (cm_rep_is_pointer_code (ty_pre)))) ,
  ((pointer_pre) # Int  |-> retval)
|--
  ((pointer_pre) # Int  |-> (cm_rep_is_pointer_code (ty_pre)))
.

Definition cmc_is_pointer_value_partial_solve_wit_1 := 
forall (pointer_pre: Z) ,
  ((pointer_pre) # Int  |->_)
|--
  ((pointer_pre) # Int  |->_)
.

(*----- Function cmc_pointee -----*)

Definition cmc_pointee_safety_wit_1 := 
forall (ty_pre: Z) (PreH1 : (1024 <= ty_pre)) (PreH2 : (ty_pre <= INT_MAX)) ,
  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ ((ty_pre - 1024 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ty_pre - 1024 )) ”
.

Definition cmc_pointee_safety_wit_2 := 
forall (ty_pre: Z) (PreH1 : (1024 <= ty_pre)) (PreH2 : (ty_pre <= INT_MAX)) ,
  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (1024 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1024) ”
.

Definition cmc_pointee_return_wit_1 := 
forall (ty_pre: Z) (PreH1 : (1024 <= ty_pre)) (PreH2 : (ty_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((ty_pre - 1024 ) = (ty_pre - 1024 )) ”
  &&  emp
.

(*----- Function cmc_leaf_size -----*)

Definition cmc_leaf_size_safety_wit_1 := 
forall (ty_pre: Z) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (1024 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1024) ”
.

Definition cmc_leaf_size_safety_wit_2 := 
forall (ty_pre: Z) (PreH1 : (ty_pre >= 1024)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition cmc_leaf_size_safety_wit_3 := 
forall (ty_pre: Z) (PreH1 : (ty_pre < 1024)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_leaf_size_safety_wit_4 := 
forall (ty_pre: Z) (PreH1 : (ty_pre = 0)) (PreH2 : (ty_pre < 1024)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition cmc_leaf_size_safety_wit_5 := 
forall (ty_pre: Z) (PreH1 : (ty_pre <> 0)) (PreH2 : (ty_pre < 1024)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmc_leaf_size_safety_wit_6 := 
forall (ty_pre: Z) (PreH1 : (ty_pre = 1)) (PreH2 : (ty_pre <> 0)) (PreH3 : (ty_pre < 1024)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmc_leaf_size_safety_wit_7 := 
forall (ty_pre: Z) (PreH1 : (ty_pre <> 1)) (PreH2 : (ty_pre <> 0)) (PreH3 : (ty_pre < 1024)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_leaf_size_return_wit_1 := 
(
forall (ty_pre: Z) (PreH1 : (ty_pre >= 1024)) ,
  TT && emp 
|--
  “ (8 = (cm_rep_leaf_size (ty_pre))) ”
  &&  emp
) \/
(
forall (ty_pre: Z) (PreH1 : (ty_pre >= 1024)) ,
  TT && emp 
|--
  “ (8 = (cm_rep_leaf_size (ty_pre))) ”
  &&  emp
).

Definition cmc_leaf_size_return_wit_1_split_goal_1 := 
forall (ty_pre: Z) (PreH1 : (ty_pre >= 1024)) ,
  (8 = (cm_rep_leaf_size (ty_pre)))
.

Definition cmc_leaf_size_return_wit_2 := 
(
forall (ty_pre: Z) (PreH1 : (ty_pre = 0)) (PreH2 : (ty_pre < 1024)) ,
  TT && emp 
|--
  “ (8 = (cm_rep_leaf_size (ty_pre))) ”
  &&  emp
) \/
(
forall (ty_pre: Z) (PreH1 : (ty_pre = 0)) (PreH2 : (ty_pre < 1024)) ,
  TT && emp 
|--
  “ (8 = (cm_rep_leaf_size (0))) ”
  &&  emp
).

Definition cmc_leaf_size_return_wit_2_split_goal_1 := 
forall (ty_pre: Z) (PreH1 : (ty_pre = 0)) (PreH2 : (ty_pre < 1024)) ,
  (8 = (cm_rep_leaf_size (0)))
.

Definition cmc_leaf_size_return_wit_3 := 
(
forall (ty_pre: Z) (PreH1 : (ty_pre = 1)) (PreH2 : (ty_pre <> 0)) (PreH3 : (ty_pre < 1024)) ,
  TT && emp 
|--
  “ (1 = (cm_rep_leaf_size (ty_pre))) ”
  &&  emp
) \/
(
forall (ty_pre: Z) (PreH1 : (ty_pre = 1)) (PreH2 : (ty_pre <> 0)) (PreH3 : (ty_pre < 1024)) ,
  TT && emp 
|--
  “ (1 = (cm_rep_leaf_size (1))) ”
  &&  emp
).

Definition cmc_leaf_size_return_wit_3_split_goal_1 := 
forall (ty_pre: Z) (PreH1 : (ty_pre = 1)) (PreH2 : (ty_pre <> 0)) (PreH3 : (ty_pre < 1024)) ,
  (1 = (cm_rep_leaf_size (1)))
.

Definition cmc_leaf_size_return_wit_4 := 
(
forall (ty_pre: Z) (PreH1 : (ty_pre <> 1)) (PreH2 : (ty_pre <> 0)) (PreH3 : (ty_pre < 1024)) ,
  TT && emp 
|--
  “ (0 = (cm_rep_leaf_size (ty_pre))) ”
  &&  emp
) \/
(
forall (ty_pre: Z) (PreH1 : (ty_pre <> 1)) (PreH2 : (ty_pre <> 0)) (PreH3 : (ty_pre < 1024)) ,
  TT && emp 
|--
  “ (0 = (cm_rep_leaf_size (ty_pre))) ”
  &&  emp
).

Definition cmc_leaf_size_return_wit_4_split_goal_1 := 
forall (ty_pre: Z) (PreH1 : (ty_pre <> 1)) (PreH2 : (ty_pre <> 0)) (PreH3 : (ty_pre < 1024)) ,
  (0 = (cm_rep_leaf_size (ty_pre)))
.

(*----- Function cmc_code_slot_size -----*)

Definition cmc_code_slot_size_safety_wit_1 := 
forall (count_pre: Z) (code_pre: Z) (retval: Z) (PreH1 : (retval = (cm_rep_leaf_size (code_pre)))) ,
  ((( &( "result" ) )) # Int64  |->_)
  **  ((( &( "leaf" ) )) # Int  |-> retval)
  **  ((( &( "code" ) )) # Int  |-> code_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_code_slot_size_safety_wit_2 := 
forall (count_pre: Z) (code_pre: Z) (retval: Z) (PreH1 : (count_pre <> 0)) (PreH2 : (retval = (cm_rep_leaf_size (code_pre)))) ,
  ((( &( "result" ) )) # Int64  |->_)
  **  ((( &( "leaf" ) )) # Int  |-> retval)
  **  ((( &( "code" ) )) # Int  |-> code_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
|--
  “ ((count_pre * retval ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (count_pre * retval )) ”
.

Definition cmc_code_slot_size_return_wit_1 := 
(
forall (count_pre: Z) (code_pre: Z) (retval: Z) (PreH1 : (count_pre = 0)) (PreH2 : (retval = (cm_rep_leaf_size (code_pre)))) ,
  TT && emp 
|--
  “ (retval = (cm_rep_code_slot_size (code_pre) (count_pre))) ”
  &&  emp
) \/
(
forall (count_pre: Z) (code_pre: Z) (retval: Z) (PreH1 : (count_pre = 0)) (PreH2 : (retval = (cm_rep_leaf_size (code_pre)))) ,
  TT && emp 
|--
  “ (retval = (cm_rep_code_slot_size (code_pre) (0))) ”
  &&  emp
).

Definition cmc_code_slot_size_return_wit_1_split_goal_1 := 
forall (count_pre: Z) (code_pre: Z) (retval: Z) (PreH1 : (count_pre = 0)) (PreH2 : (retval = (cm_rep_leaf_size (code_pre)))) ,
  (retval = (cm_rep_code_slot_size (code_pre) (0)))
.

Definition cmc_code_slot_size_return_wit_2 := 
(
forall (count_pre: Z) (code_pre: Z) (retval: Z) (PreH1 : (count_pre <> 0)) (PreH2 : (retval = (cm_rep_leaf_size (code_pre)))) ,
  TT && emp 
|--
  “ ((count_pre * retval ) = (cm_rep_code_slot_size (code_pre) (count_pre))) ”
  &&  emp
) \/
(
forall (count_pre: Z) (code_pre: Z) (retval: Z) (PreH1 : (count_pre <> 0)) (PreH2 : (retval = (cm_rep_leaf_size (code_pre)))) ,
  TT && emp 
|--
  “ ((count_pre * retval ) = (cm_rep_code_slot_size (code_pre) (count_pre))) ”
  &&  emp
).

Definition cmc_code_slot_size_return_wit_2_split_goal_1 := 
forall (count_pre: Z) (code_pre: Z) (retval: Z) (PreH1 : (count_pre <> 0)) (PreH2 : (retval = (cm_rep_leaf_size (code_pre)))) ,
  ((count_pre * retval ) = (cm_rep_code_slot_size (code_pre) (count_pre)))
.

Definition cmc_code_slot_size_partial_solve_wit_1 := 
  TT && emp 
|--
  TT && emp 
.

(*----- Function cmc_members_size -----*)

Definition cmc_members_size_safety_wit_1 := 
forall (member_pre: Z) (members: (@list cm_slot_d)) (PreH1 : (cm_rep_members_safe members )) ,
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "member" ) )) # Ptr  |-> member_pre)
  **  (cm_member_list_rep member_pre members )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_members_size_safety_wit_2 := 
forall (member_pre: Z) (members: (@list cm_slot_d)) (PreH1 : (member_pre = 0)) (PreH2 : (cm_rep_members_safe members )) ,
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "member" ) )) # Ptr  |-> member_pre)
  **  (cm_member_list_rep member_pre members )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_members_size_safety_wit_3 := 
(
forall (member_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : (cm_rep_members_safe tail )) (PreH2 : (retval_2 = (cm_rep_members_size (tail)))) (PreH3 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH4 : (member_pre <> 0)) (PreH5 : (members = (cons (head) (tail)))) (PreH6 : (cm_rep_members_safe members )) (PreH7 : (cm_rep_members_safe tail )) ,
  (cm_member_list_rep nextp tail )
  **  ((( &( "rest_size" ) )) # Int64  |-> retval_2)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> retval)
  **  ((( &( "member" ) )) # Ptr  |-> member_pre)
  **  ((&((member_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((member_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((member_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ ((retval + retval_2 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (retval + retval_2 )) ”
) \/
(
forall (member_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : (cm_rep_members_safe tail )) (PreH2 : (retval_2 = (cm_rep_members_size (tail)))) (PreH3 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH4 : (member_pre <> 0)) (PreH5 : (members = (cons (head) (tail)))) (PreH6 : (cm_rep_members_safe members )) (PreH7 : (cm_rep_members_safe tail )) ,
  (cm_member_list_rep nextp tail )
  **  ((( &( "rest_size" ) )) # Int64  |-> retval_2)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> retval)
  **  ((( &( "member" ) )) # Ptr  |-> member_pre)
  **  ((&((member_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((member_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((member_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ ((retval + retval_2 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (retval + retval_2 )) ”
).

Definition cmc_members_size_safety_wit_3_split_goal_1 := 
forall (member_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : (cm_rep_members_safe tail )) (PreH2 : (retval_2 = (cm_rep_members_size (tail)))) (PreH3 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH4 : (member_pre <> 0)) (PreH5 : (members = (cons (head) (tail)))) (PreH6 : (cm_rep_members_safe members )) (PreH7 : (cm_rep_members_safe tail )) ,
  (cm_member_list_rep nextp tail )
  **  ((( &( "rest_size" ) )) # Int64  |-> retval_2)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> retval)
  **  ((( &( "member" ) )) # Ptr  |-> member_pre)
  **  ((&((member_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((member_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((member_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ ((retval + retval_2 ) <= INT64_MAX) ”
.

Definition cmc_members_size_safety_wit_3_split_goal_2 := 
forall (member_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : (cm_rep_members_safe tail )) (PreH2 : (retval_2 = (cm_rep_members_size (tail)))) (PreH3 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH4 : (member_pre <> 0)) (PreH5 : (members = (cons (head) (tail)))) (PreH6 : (cm_rep_members_safe members )) (PreH7 : (cm_rep_members_safe tail )) ,
  (cm_member_list_rep nextp tail )
  **  ((( &( "rest_size" ) )) # Int64  |-> retval_2)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> retval)
  **  ((( &( "member" ) )) # Ptr  |-> member_pre)
  **  ((&((member_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((member_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((member_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ ((INT64_MIN) <= (retval + retval_2 )) ”
.

Definition cmc_members_size_entail_wit_1 := 
(
forall (member_pre: Z) (members: (@list cm_slot_d)) (PreH1 : (member_pre <> 0)) (PreH2 : (cm_rep_members_safe members )) ,
  (cm_member_list_rep member_pre members )
|--
  EX (nextp: Z)  (head: cm_slot_d)  (tail: (@list cm_slot_d)) ,
  “ (member_pre <> 0) ” 
  &&  “ (members = (cons (head) (tail))) ” 
  &&  “ (cm_rep_members_safe members ) ” 
  &&  “ (cm_rep_members_safe tail ) ”
  &&  ((&((member_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((member_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((member_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_member_list_rep nextp tail )
) \/
(
forall (member_pre: Z) (members: (@list cm_slot_d)) (PreH1 : (member_pre <> 0)) (PreH2 : (cm_rep_members_safe members )) ,
  (cm_member_list_rep member_pre members )
|--
  EX (nextp: Z)  (head: cm_slot_d)  (tail: (@list cm_slot_d)) ,
  “ (member_pre <> 0) ” 
  &&  “ (members = (cons (head) (tail))) ” 
  &&  “ (cm_rep_members_safe members ) ” 
  &&  “ (cm_rep_members_safe tail ) ”
  &&  ((&((member_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((member_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((member_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_member_list_rep nextp tail )
).

Definition cmc_members_size_return_wit_1 := 
(
forall (member_pre: Z) (members: (@list cm_slot_d)) (PreH1 : (member_pre = 0)) (PreH2 : (cm_rep_members_safe members )) ,
  (cm_member_list_rep member_pre members )
|--
  “ (cm_rep_members_safe members ) ” 
  &&  “ (0 = (cm_rep_members_size (members))) ”
  &&  (cm_member_list_rep member_pre members )
) \/
(
forall (member_pre: Z) (members: (@list cm_slot_d)) (PreH1 : (member_pre = 0)) (PreH2 : (cm_rep_members_safe members )) ,
  TT && emp 
|--
  “ (0 = (cm_rep_members_size (members))) ”
  &&  emp
).

Definition cmc_members_size_return_wit_1_split_goal_1 := 
forall (member_pre: Z) (members: (@list cm_slot_d)) (PreH1 : (member_pre = 0)) (PreH2 : (cm_rep_members_safe members )) ,
  (0 = (cm_rep_members_size (members)))
.

Definition cmc_members_size_return_wit_2 := 
(
forall (member_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : (cm_rep_members_safe tail )) (PreH2 : (retval_2 = (cm_rep_members_size (tail)))) (PreH3 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH4 : (member_pre <> 0)) (PreH5 : (members = (cons (head) (tail)))) (PreH6 : (cm_rep_members_safe members )) (PreH7 : (cm_rep_members_safe tail )) ,
  (cm_member_list_rep nextp tail )
  **  ((&((member_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((member_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((member_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (cm_rep_members_safe members ) ” 
  &&  “ ((retval + retval_2 ) = (cm_rep_members_size (members))) ”
  &&  (cm_member_list_rep member_pre members )
) \/
(
forall (member_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (cm_rep_members_safe tail )) (PreH6 : (retval_2 = (cm_rep_members_size (tail)))) (PreH7 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH8 : (member_pre <> 0)) (PreH9 : (members = (cons (head) (tail)))) (PreH10 : (cm_rep_members_safe members )) (PreH11 : (cm_rep_members_safe tail )) ,
  (cm_member_list_rep nextp tail )
  **  ((&((member_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((member_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((member_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ ((retval + retval_2 ) = (cm_rep_members_size (members))) ”
  &&  (cm_member_list_rep member_pre members )
).

Definition cmc_members_size_return_wit_2_split_goal_1 := 
forall (member_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (cm_rep_members_safe tail )) (PreH6 : (retval_2 = (cm_rep_members_size (tail)))) (PreH7 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH8 : (member_pre <> 0)) (PreH9 : (members = (cons (head) (tail)))) (PreH10 : (cm_rep_members_safe members )) (PreH11 : (cm_rep_members_safe tail )) ,
  (cm_member_list_rep nextp tail )
  **  ((&((member_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((member_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((member_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ ((retval + retval_2 ) = (cm_rep_members_size (members))) ”
.

Definition cmc_members_size_return_wit_2_split_goal_spatial := 
forall (member_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (cm_rep_members_safe tail )) (PreH6 : (retval_2 = (cm_rep_members_size (tail)))) (PreH7 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH8 : (member_pre <> 0)) (PreH9 : (members = (cons (head) (tail)))) (PreH10 : (cm_rep_members_safe members )) (PreH11 : (cm_rep_members_safe tail )) ,
  (cm_member_list_rep nextp tail )
  **  ((&((member_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((member_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((member_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
|--
  (cm_member_list_rep member_pre members )
.

Definition cmc_members_size_partial_solve_wit_1 := 
forall (member_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (PreH1 : (member_pre <> 0)) (PreH2 : (members = (cons (head) (tail)))) (PreH3 : (cm_rep_members_safe members )) (PreH4 : (cm_rep_members_safe tail )) ,
  ((&((member_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((member_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((member_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_member_list_rep nextp tail )
|--
  “ (member_pre <> 0) ” 
  &&  “ (members = (cons (head) (tail))) ” 
  &&  “ (cm_rep_members_safe members ) ” 
  &&  “ (cm_rep_members_safe tail ) ”
  &&  ((&((member_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((member_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((member_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_member_list_rep nextp tail )
.

Definition cmc_members_size_partial_solve_wit_2_pure := 
forall (member_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (PreH1 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH2 : (member_pre <> 0)) (PreH3 : (members = (cons (head) (tail)))) (PreH4 : (cm_rep_members_safe members )) (PreH5 : (cm_rep_members_safe tail )) ,
  ((( &( "rest_size" ) )) # Int64  |->_)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> retval)
  **  ((( &( "member" ) )) # Ptr  |-> member_pre)
  **  ((&((member_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((member_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((member_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_member_list_rep nextp tail )
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ (cm_rep_members_safe tail ) ”
.

Definition cmc_members_size_partial_solve_wit_2_aux := 
forall (member_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (PreH1 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH2 : (member_pre <> 0)) (PreH3 : (members = (cons (head) (tail)))) (PreH4 : (cm_rep_members_safe members )) (PreH5 : (cm_rep_members_safe tail )) ,
  ((&((member_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((member_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((member_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_member_list_rep nextp tail )
|--
  “ (cm_rep_members_safe tail ) ” 
  &&  “ (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head))))) ” 
  &&  “ (member_pre <> 0) ” 
  &&  “ (members = (cons (head) (tail))) ” 
  &&  “ (cm_rep_members_safe members ) ” 
  &&  “ (cm_rep_members_safe tail ) ”
  &&  (cm_member_list_rep nextp tail )
  **  ((&((member_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((member_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((member_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
.

Definition cmc_members_size_partial_solve_wit_2 := cmc_members_size_partial_solve_wit_2_pure -> cmc_members_size_partial_solve_wit_2_aux.

(*----- Function cmc_struct_size_at -----*)

Definition cmc_struct_size_at_safety_wit_1 := 
forall (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (0 <= sid_pre)) (PreH2 : (cm_rep_structs_safe structs )) ,
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "sid" ) )) # Int  |-> sid_pre)
  **  (cm_struct_list_rep item_pre structs )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_struct_size_at_safety_wit_2 := 
forall (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (item_pre = 0)) (PreH2 : (0 <= sid_pre)) (PreH3 : (cm_rep_structs_safe structs )) ,
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "sid" ) )) # Int  |-> sid_pre)
  **  (cm_struct_list_rep item_pre structs )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_struct_size_at_safety_wit_3 := 
forall (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (PreH1 : (item_pre <> 0)) (PreH2 : (structs = (cons (head) (tail)))) (PreH3 : (0 <= sid_pre)) (PreH4 : (cm_rep_structs_safe structs )) (PreH5 : (cm_rep_structs_safe tail )) (PreH6 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "sid" ) )) # Int  |-> sid_pre)
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_struct_size_at_safety_wit_4 := 
forall (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (PreH1 : (sid_pre <> 0)) (PreH2 : (item_pre <> 0)) (PreH3 : (structs = (cons (head) (tail)))) (PreH4 : (0 <= sid_pre)) (PreH5 : (cm_rep_structs_safe structs )) (PreH6 : (cm_rep_structs_safe tail )) (PreH7 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "sid" ) )) # Int  |-> sid_pre)
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ ((sid_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sid_pre - 1 )) ”
.

Definition cmc_struct_size_at_safety_wit_5 := 
forall (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (PreH1 : (sid_pre <> 0)) (PreH2 : (item_pre <> 0)) (PreH3 : (structs = (cons (head) (tail)))) (PreH4 : (0 <= sid_pre)) (PreH5 : (cm_rep_structs_safe structs )) (PreH6 : (cm_rep_structs_safe tail )) (PreH7 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "sid" ) )) # Int  |-> sid_pre)
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmc_struct_size_at_entail_wit_1 := 
(
forall (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (item_pre <> 0)) (PreH2 : (0 <= sid_pre)) (PreH3 : (cm_rep_structs_safe structs )) ,
  (cm_struct_list_rep item_pre structs )
|--
  EX (nextp: Z)  (memberp: Z)  (head: cm_struct_d)  (tail: (@list cm_struct_d)) ,
  “ (item_pre <> 0) ” 
  &&  “ (structs = (cons (head) (tail))) ” 
  &&  “ (0 <= sid_pre) ” 
  &&  “ (cm_rep_structs_safe structs ) ” 
  &&  “ (cm_rep_structs_safe tail ) ” 
  &&  “ (cm_rep_members_safe (cm_struct_members (head)) ) ”
  &&  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
) \/
(
forall (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (item_pre <> 0)) (PreH2 : (0 <= sid_pre)) (PreH3 : (cm_rep_structs_safe structs )) ,
  (cm_struct_list_rep item_pre structs )
|--
  EX (nextp: Z)  (memberp: Z)  (head: cm_struct_d)  (tail: (@list cm_struct_d)) ,
  “ (item_pre <> 0) ” 
  &&  “ (structs = (cons (head) (tail))) ” 
  &&  “ (0 <= sid_pre) ” 
  &&  “ (cm_rep_structs_safe structs ) ” 
  &&  “ (cm_rep_structs_safe tail ) ” 
  &&  “ (cm_rep_members_safe (cm_struct_members (head)) ) ”
  &&  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
).

Definition cmc_struct_size_at_return_wit_1 := 
(
forall (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (item_pre = 0)) (PreH2 : (0 <= sid_pre)) (PreH3 : (cm_rep_structs_safe structs )) ,
  (cm_struct_list_rep item_pre structs )
|--
  “ (0 <= sid_pre) ” 
  &&  “ (cm_rep_structs_safe structs ) ” 
  &&  “ (0 = (cm_rep_struct_size (structs) (sid_pre))) ”
  &&  (cm_struct_list_rep item_pre structs )
) \/
(
forall (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (item_pre = 0)) (PreH2 : (0 <= sid_pre)) (PreH3 : (cm_rep_structs_safe structs )) ,
  TT && emp 
|--
  “ (0 = (cm_rep_struct_size (structs) (sid_pre))) ”
  &&  emp
).

Definition cmc_struct_size_at_return_wit_1_split_goal_1 := 
forall (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (item_pre = 0)) (PreH2 : (0 <= sid_pre)) (PreH3 : (cm_rep_structs_safe structs )) ,
  (0 = (cm_rep_struct_size (structs) (sid_pre)))
.

Definition cmc_struct_size_at_return_wit_2 := 
(
forall (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (retval: Z) (PreH1 : (cm_rep_members_safe (cm_struct_members (head)) )) (PreH2 : (retval = (cm_rep_members_size ((cm_struct_members (head)))))) (PreH3 : (sid_pre = 0)) (PreH4 : (item_pre <> 0)) (PreH5 : (structs = (cons (head) (tail)))) (PreH6 : (0 <= sid_pre)) (PreH7 : (cm_rep_structs_safe structs )) (PreH8 : (cm_rep_structs_safe tail )) (PreH9 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
|--
  “ (0 <= sid_pre) ” 
  &&  “ (cm_rep_structs_safe structs ) ” 
  &&  “ (retval = (cm_rep_struct_size (structs) (sid_pre))) ”
  &&  (cm_struct_list_rep item_pre structs )
) \/
(
forall (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (retval: Z) (PreH1 : (cm_rep_members_safe (cm_struct_members (head)) )) (PreH2 : (retval = (cm_rep_members_size ((cm_struct_members (head)))))) (PreH3 : (sid_pre = 0)) (PreH4 : (item_pre <> 0)) (PreH5 : (structs = (cons (head) (tail)))) (PreH6 : (0 <= sid_pre)) (PreH7 : (cm_rep_structs_safe structs )) (PreH8 : (cm_rep_structs_safe tail )) (PreH9 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
|--
  “ (retval = (cm_rep_struct_size (structs) (0))) ”
  &&  (cm_struct_list_rep item_pre structs )
).

Definition cmc_struct_size_at_return_wit_2_split_goal_1 := 
forall (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (retval: Z) (PreH1 : (cm_rep_members_safe (cm_struct_members (head)) )) (PreH2 : (retval = (cm_rep_members_size ((cm_struct_members (head)))))) (PreH3 : (sid_pre = 0)) (PreH4 : (item_pre <> 0)) (PreH5 : (structs = (cons (head) (tail)))) (PreH6 : (0 <= sid_pre)) (PreH7 : (cm_rep_structs_safe structs )) (PreH8 : (cm_rep_structs_safe tail )) (PreH9 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
|--
  “ (retval = (cm_rep_struct_size (structs) (0))) ”
.

Definition cmc_struct_size_at_return_wit_2_split_goal_spatial := 
forall (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (retval: Z) (PreH1 : (cm_rep_members_safe (cm_struct_members (head)) )) (PreH2 : (retval = (cm_rep_members_size ((cm_struct_members (head)))))) (PreH3 : (sid_pre = 0)) (PreH4 : (item_pre <> 0)) (PreH5 : (structs = (cons (head) (tail)))) (PreH6 : (0 <= sid_pre)) (PreH7 : (cm_rep_structs_safe structs )) (PreH8 : (cm_rep_structs_safe tail )) (PreH9 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
|--
  (cm_struct_list_rep item_pre structs )
.

Definition cmc_struct_size_at_return_wit_3 := 
(
forall (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (retval: Z) (PreH1 : (0 <= (sid_pre - 1 ))) (PreH2 : (cm_rep_structs_safe tail )) (PreH3 : (retval = (cm_rep_struct_size (tail) ((sid_pre - 1 ))))) (PreH4 : (sid_pre <> 0)) (PreH5 : (item_pre <> 0)) (PreH6 : (structs = (cons (head) (tail)))) (PreH7 : (0 <= sid_pre)) (PreH8 : (cm_rep_structs_safe structs )) (PreH9 : (cm_rep_structs_safe tail )) (PreH10 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  (cm_struct_list_rep nextp tail )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (0 <= sid_pre) ” 
  &&  “ (cm_rep_structs_safe structs ) ” 
  &&  “ (retval = (cm_rep_struct_size (structs) (sid_pre))) ”
  &&  (cm_struct_list_rep item_pre structs )
) \/
(
forall (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (retval: Z) (PreH1 : (0 <= (sid_pre - 1 ))) (PreH2 : (cm_rep_structs_safe tail )) (PreH3 : (retval = (cm_rep_struct_size (tail) ((sid_pre - 1 ))))) (PreH4 : (sid_pre <> 0)) (PreH5 : (item_pre <> 0)) (PreH6 : (structs = (cons (head) (tail)))) (PreH7 : (0 <= sid_pre)) (PreH8 : (cm_rep_structs_safe structs )) (PreH9 : (cm_rep_structs_safe tail )) (PreH10 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  (cm_struct_list_rep nextp tail )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (retval = (cm_rep_struct_size (structs) (sid_pre))) ”
  &&  (cm_struct_list_rep item_pre structs )
).

Definition cmc_struct_size_at_return_wit_3_split_goal_1 := 
forall (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (retval: Z) (PreH1 : (0 <= (sid_pre - 1 ))) (PreH2 : (cm_rep_structs_safe tail )) (PreH3 : (retval = (cm_rep_struct_size (tail) ((sid_pre - 1 ))))) (PreH4 : (sid_pre <> 0)) (PreH5 : (item_pre <> 0)) (PreH6 : (structs = (cons (head) (tail)))) (PreH7 : (0 <= sid_pre)) (PreH8 : (cm_rep_structs_safe structs )) (PreH9 : (cm_rep_structs_safe tail )) (PreH10 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  (cm_struct_list_rep nextp tail )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (retval = (cm_rep_struct_size (structs) (sid_pre))) ”
.

Definition cmc_struct_size_at_return_wit_3_split_goal_spatial := 
forall (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (retval: Z) (PreH1 : (0 <= (sid_pre - 1 ))) (PreH2 : (cm_rep_structs_safe tail )) (PreH3 : (retval = (cm_rep_struct_size (tail) ((sid_pre - 1 ))))) (PreH4 : (sid_pre <> 0)) (PreH5 : (item_pre <> 0)) (PreH6 : (structs = (cons (head) (tail)))) (PreH7 : (0 <= sid_pre)) (PreH8 : (cm_rep_structs_safe structs )) (PreH9 : (cm_rep_structs_safe tail )) (PreH10 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  (cm_struct_list_rep nextp tail )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
|--
  (cm_struct_list_rep item_pre structs )
.

Definition cmc_struct_size_at_partial_solve_wit_1_pure := 
forall (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (PreH1 : (sid_pre = 0)) (PreH2 : (item_pre <> 0)) (PreH3 : (structs = (cons (head) (tail)))) (PreH4 : (0 <= sid_pre)) (PreH5 : (cm_rep_structs_safe structs )) (PreH6 : (cm_rep_structs_safe tail )) (PreH7 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "sid" ) )) # Int  |-> sid_pre)
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ (cm_rep_members_safe (cm_struct_members (head)) ) ”
.

Definition cmc_struct_size_at_partial_solve_wit_1_aux := 
forall (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (PreH1 : (sid_pre = 0)) (PreH2 : (item_pre <> 0)) (PreH3 : (structs = (cons (head) (tail)))) (PreH4 : (0 <= sid_pre)) (PreH5 : (cm_rep_structs_safe structs )) (PreH6 : (cm_rep_structs_safe tail )) (PreH7 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
|--
  “ (cm_rep_members_safe (cm_struct_members (head)) ) ” 
  &&  “ (sid_pre = 0) ” 
  &&  “ (item_pre <> 0) ” 
  &&  “ (structs = (cons (head) (tail))) ” 
  &&  “ (0 <= sid_pre) ” 
  &&  “ (cm_rep_structs_safe structs ) ” 
  &&  “ (cm_rep_structs_safe tail ) ” 
  &&  “ (cm_rep_members_safe (cm_struct_members (head)) ) ”
  &&  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
.

Definition cmc_struct_size_at_partial_solve_wit_1 := cmc_struct_size_at_partial_solve_wit_1_pure -> cmc_struct_size_at_partial_solve_wit_1_aux.

Definition cmc_struct_size_at_partial_solve_wit_2_pure := 
forall (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (PreH1 : (sid_pre <> 0)) (PreH2 : (item_pre <> 0)) (PreH3 : (structs = (cons (head) (tail)))) (PreH4 : (0 <= sid_pre)) (PreH5 : (cm_rep_structs_safe structs )) (PreH6 : (cm_rep_structs_safe tail )) (PreH7 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "sid" ) )) # Int  |-> sid_pre)
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ (0 <= (sid_pre - 1 )) ” 
  &&  “ (cm_rep_structs_safe tail ) ”
.

Definition cmc_struct_size_at_partial_solve_wit_2_aux := 
forall (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (PreH1 : (sid_pre <> 0)) (PreH2 : (item_pre <> 0)) (PreH3 : (structs = (cons (head) (tail)))) (PreH4 : (0 <= sid_pre)) (PreH5 : (cm_rep_structs_safe structs )) (PreH6 : (cm_rep_structs_safe tail )) (PreH7 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
|--
  “ (0 <= (sid_pre - 1 )) ” 
  &&  “ (cm_rep_structs_safe tail ) ” 
  &&  “ (sid_pre <> 0) ” 
  &&  “ (item_pre <> 0) ” 
  &&  “ (structs = (cons (head) (tail))) ” 
  &&  “ (0 <= sid_pre) ” 
  &&  “ (cm_rep_structs_safe structs ) ” 
  &&  “ (cm_rep_structs_safe tail ) ” 
  &&  “ (cm_rep_members_safe (cm_struct_members (head)) ) ”
  &&  (cm_struct_list_rep nextp tail )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
.

Definition cmc_struct_size_at_partial_solve_wit_2 := cmc_struct_size_at_partial_solve_wit_2_pure -> cmc_struct_size_at_partial_solve_wit_2_aux.

(*----- Function cmc_nonzero -----*)

Definition cmc_nonzero_safety_wit_1 := 
forall (n_pre: Z) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_nonzero_safety_wit_2 := 
forall (n_pre: Z) (PreH1 : (n_pre = 0)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_nonzero_safety_wit_3 := 
forall (n_pre: Z) (PreH1 : (n_pre <> 0)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmc_nonzero_return_wit_1 := 
(
forall (n_pre: Z) (PreH1 : (n_pre = 0)) ,
  TT && emp 
|--
  “ (0 = (cm_rep_nonzero (n_pre))) ”
  &&  emp
) \/
(
forall (n_pre: Z) (PreH1 : (n_pre = 0)) ,
  TT && emp 
|--
  “ (0 = (cm_rep_nonzero (0))) ”
  &&  emp
).

Definition cmc_nonzero_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (PreH1 : (n_pre = 0)) ,
  (0 = (cm_rep_nonzero (0)))
.

Definition cmc_nonzero_return_wit_2 := 
(
forall (n_pre: Z) (PreH1 : (n_pre <> 0)) ,
  TT && emp 
|--
  “ (1 = (cm_rep_nonzero (n_pre))) ”
  &&  emp
) \/
(
forall (n_pre: Z) (PreH1 : (n_pre <> 0)) ,
  TT && emp 
|--
  “ (1 = (cm_rep_nonzero (n_pre))) ”
  &&  emp
).

Definition cmc_nonzero_return_wit_2_split_goal_1 := 
forall (n_pre: Z) (PreH1 : (n_pre <> 0)) ,
  (1 = (cm_rep_nonzero (n_pre)))
.

(*----- Function cmc_global_array_at -----*)

Definition cmc_global_array_at_safety_wit_1 := 
forall (index_pre: Z) (item_pre: Z) (globals: (@list cm_global_d)) (PreH1 : (0 <= index_pre)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  (cm_global_list_rep item_pre globals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_global_array_at_safety_wit_2 := 
forall (index_pre: Z) (item_pre: Z) (globals: (@list cm_global_d)) (PreH1 : (item_pre = 0)) (PreH2 : (0 <= index_pre)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  (cm_global_list_rep item_pre globals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_global_array_at_safety_wit_3 := 
forall (index_pre: Z) (item_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (PreH1 : (item_pre <> 0)) (PreH2 : (globals = (cons (head) (tail)))) (PreH3 : (0 <= index_pre)) ,
  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((item_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((item_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((item_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((item_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((item_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
  **  ((( &( "result" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_global_array_at_safety_wit_4 := 
forall (index_pre: Z) (item_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (PreH1 : (index_pre <> 0)) (PreH2 : (item_pre <> 0)) (PreH3 : (globals = (cons (head) (tail)))) (PreH4 : (0 <= index_pre)) ,
  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((item_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((item_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((item_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((item_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((item_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
  **  ((( &( "result" ) )) # Int  |->_)
|--
  “ ((index_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (index_pre - 1 )) ”
.

Definition cmc_global_array_at_safety_wit_5 := 
forall (index_pre: Z) (item_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (PreH1 : (index_pre <> 0)) (PreH2 : (item_pre <> 0)) (PreH3 : (globals = (cons (head) (tail)))) (PreH4 : (0 <= index_pre)) ,
  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((item_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((item_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((item_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((item_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((item_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
  **  ((( &( "result" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmc_global_array_at_entail_wit_1 := 
(
forall (index_pre: Z) (item_pre: Z) (globals: (@list cm_global_d)) (PreH1 : (item_pre <> 0)) (PreH2 : (0 <= index_pre)) ,
  (cm_global_list_rep item_pre globals )
|--
  EX (nextp: Z)  (head: cm_global_d)  (tail: (@list cm_global_d)) ,
  “ (item_pre <> 0) ” 
  &&  “ (globals = (cons (head) (tail))) ” 
  &&  “ (0 <= index_pre) ”
  &&  ((&((item_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((item_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((item_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((item_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((item_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
) \/
(
forall (index_pre: Z) (item_pre: Z) (globals: (@list cm_global_d)) (PreH1 : (item_pre <> 0)) (PreH2 : (0 <= index_pre)) ,
  (cm_global_list_rep item_pre globals )
|--
  EX (nextp: Z)  (head: cm_global_d)  (tail: (@list cm_global_d)) ,
  “ (item_pre <> 0) ” 
  &&  “ (globals = (cons (head) (tail))) ” 
  &&  “ (0 <= index_pre) ”
  &&  ((&((item_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((item_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((item_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((item_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((item_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
).

Definition cmc_global_array_at_return_wit_1 := 
(
forall (index_pre: Z) (item_pre: Z) (globals: (@list cm_global_d)) (PreH1 : (item_pre = 0)) (PreH2 : (0 <= index_pre)) ,
  (cm_global_list_rep item_pre globals )
|--
  “ (0 <= index_pre) ” 
  &&  “ (0 = (cm_rep_global_array (globals) (index_pre))) ”
  &&  (cm_global_list_rep item_pre globals )
) \/
(
forall (index_pre: Z) (item_pre: Z) (globals: (@list cm_global_d)) (PreH1 : (item_pre = 0)) (PreH2 : (0 <= index_pre)) ,
  TT && emp 
|--
  “ (0 = (cm_rep_global_array (globals) (index_pre))) ”
  &&  emp
).

Definition cmc_global_array_at_return_wit_1_split_goal_1 := 
forall (index_pre: Z) (item_pre: Z) (globals: (@list cm_global_d)) (PreH1 : (item_pre = 0)) (PreH2 : (0 <= index_pre)) ,
  (0 = (cm_rep_global_array (globals) (index_pre)))
.

Definition cmc_global_array_at_return_wit_2 := 
(
forall (index_pre: Z) (item_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (PreH1 : (retval = (cm_rep_nonzero ((cm_global_count (head)))))) (PreH2 : (index_pre = 0)) (PreH3 : (item_pre <> 0)) (PreH4 : (globals = (cons (head) (tail)))) (PreH5 : (0 <= index_pre)) ,
  ((&((item_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((item_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((item_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((item_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((item_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
|--
  “ (0 <= index_pre) ” 
  &&  “ (retval = (cm_rep_global_array (globals) (index_pre))) ”
  &&  (cm_global_list_rep item_pre globals )
) \/
(
forall (index_pre: Z) (item_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (PreH1 : ((cm_global_init (head)) <= INT64_MAX)) (PreH2 : ((cm_global_init (head)) >= INT64_MIN)) (PreH3 : ((cm_rep_bool ((cm_global_has_init (head)))) <= INT_MAX)) (PreH4 : ((cm_global_count (head)) <= INT_MAX)) (PreH5 : ((cm_type_encode ((cm_global_ty (head)))) <= INT_MAX)) (PreH6 : ((cm_rep_bool ((cm_global_has_init (head)))) >= INT_MIN)) (PreH7 : ((cm_global_count (head)) >= INT_MIN)) (PreH8 : ((cm_type_encode ((cm_global_ty (head)))) >= INT_MIN)) (PreH9 : (retval = (cm_rep_nonzero ((cm_global_count (head)))))) (PreH10 : (index_pre = 0)) (PreH11 : (item_pre <> 0)) (PreH12 : (globals = (cons (head) (tail)))) (PreH13 : (0 <= index_pre)) ,
  ((&((item_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((item_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((item_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((item_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((item_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
|--
  “ (retval = (cm_rep_global_array (globals) (0))) ”
  &&  (cm_global_list_rep item_pre globals )
).

Definition cmc_global_array_at_return_wit_2_split_goal_1 := 
forall (index_pre: Z) (item_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (PreH1 : ((cm_global_init (head)) <= INT64_MAX)) (PreH2 : ((cm_global_init (head)) >= INT64_MIN)) (PreH3 : ((cm_rep_bool ((cm_global_has_init (head)))) <= INT_MAX)) (PreH4 : ((cm_global_count (head)) <= INT_MAX)) (PreH5 : ((cm_type_encode ((cm_global_ty (head)))) <= INT_MAX)) (PreH6 : ((cm_rep_bool ((cm_global_has_init (head)))) >= INT_MIN)) (PreH7 : ((cm_global_count (head)) >= INT_MIN)) (PreH8 : ((cm_type_encode ((cm_global_ty (head)))) >= INT_MIN)) (PreH9 : (retval = (cm_rep_nonzero ((cm_global_count (head)))))) (PreH10 : (index_pre = 0)) (PreH11 : (item_pre <> 0)) (PreH12 : (globals = (cons (head) (tail)))) (PreH13 : (0 <= index_pre)) ,
  ((&((item_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((item_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((item_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((item_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((item_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
|--
  “ (retval = (cm_rep_global_array (globals) (0))) ”
.

Definition cmc_global_array_at_return_wit_2_split_goal_spatial := 
forall (index_pre: Z) (item_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (PreH1 : ((cm_global_init (head)) <= INT64_MAX)) (PreH2 : ((cm_global_init (head)) >= INT64_MIN)) (PreH3 : ((cm_rep_bool ((cm_global_has_init (head)))) <= INT_MAX)) (PreH4 : ((cm_global_count (head)) <= INT_MAX)) (PreH5 : ((cm_type_encode ((cm_global_ty (head)))) <= INT_MAX)) (PreH6 : ((cm_rep_bool ((cm_global_has_init (head)))) >= INT_MIN)) (PreH7 : ((cm_global_count (head)) >= INT_MIN)) (PreH8 : ((cm_type_encode ((cm_global_ty (head)))) >= INT_MIN)) (PreH9 : (retval = (cm_rep_nonzero ((cm_global_count (head)))))) (PreH10 : (index_pre = 0)) (PreH11 : (item_pre <> 0)) (PreH12 : (globals = (cons (head) (tail)))) (PreH13 : (0 <= index_pre)) ,
  ((&((item_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((item_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((item_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((item_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((item_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
|--
  (cm_global_list_rep item_pre globals )
.

Definition cmc_global_array_at_return_wit_3 := 
(
forall (index_pre: Z) (item_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (PreH1 : (0 <= (index_pre - 1 ))) (PreH2 : (retval = (cm_rep_global_array (tail) ((index_pre - 1 ))))) (PreH3 : (index_pre <> 0)) (PreH4 : (item_pre <> 0)) (PreH5 : (globals = (cons (head) (tail)))) (PreH6 : (0 <= index_pre)) ,
  (cm_global_list_rep nextp tail )
  **  ((&((item_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((item_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((item_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((item_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((item_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (0 <= index_pre) ” 
  &&  “ (retval = (cm_rep_global_array (globals) (index_pre))) ”
  &&  (cm_global_list_rep item_pre globals )
) \/
(
forall (index_pre: Z) (item_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (PreH1 : ((cm_global_init (head)) <= INT64_MAX)) (PreH2 : ((cm_global_init (head)) >= INT64_MIN)) (PreH3 : ((cm_rep_bool ((cm_global_has_init (head)))) <= INT_MAX)) (PreH4 : ((cm_global_count (head)) <= INT_MAX)) (PreH5 : ((cm_type_encode ((cm_global_ty (head)))) <= INT_MAX)) (PreH6 : ((cm_rep_bool ((cm_global_has_init (head)))) >= INT_MIN)) (PreH7 : ((cm_global_count (head)) >= INT_MIN)) (PreH8 : ((cm_type_encode ((cm_global_ty (head)))) >= INT_MIN)) (PreH9 : (0 <= (index_pre - 1 ))) (PreH10 : (retval = (cm_rep_global_array (tail) ((index_pre - 1 ))))) (PreH11 : (index_pre <> 0)) (PreH12 : (item_pre <> 0)) (PreH13 : (globals = (cons (head) (tail)))) (PreH14 : (0 <= index_pre)) ,
  (cm_global_list_rep nextp tail )
  **  ((&((item_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((item_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((item_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((item_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((item_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (retval = (cm_rep_global_array (globals) (index_pre))) ”
  &&  (cm_global_list_rep item_pre globals )
).

Definition cmc_global_array_at_return_wit_3_split_goal_1 := 
forall (index_pre: Z) (item_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (PreH1 : ((cm_global_init (head)) <= INT64_MAX)) (PreH2 : ((cm_global_init (head)) >= INT64_MIN)) (PreH3 : ((cm_rep_bool ((cm_global_has_init (head)))) <= INT_MAX)) (PreH4 : ((cm_global_count (head)) <= INT_MAX)) (PreH5 : ((cm_type_encode ((cm_global_ty (head)))) <= INT_MAX)) (PreH6 : ((cm_rep_bool ((cm_global_has_init (head)))) >= INT_MIN)) (PreH7 : ((cm_global_count (head)) >= INT_MIN)) (PreH8 : ((cm_type_encode ((cm_global_ty (head)))) >= INT_MIN)) (PreH9 : (0 <= (index_pre - 1 ))) (PreH10 : (retval = (cm_rep_global_array (tail) ((index_pre - 1 ))))) (PreH11 : (index_pre <> 0)) (PreH12 : (item_pre <> 0)) (PreH13 : (globals = (cons (head) (tail)))) (PreH14 : (0 <= index_pre)) ,
  (cm_global_list_rep nextp tail )
  **  ((&((item_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((item_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((item_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((item_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((item_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (retval = (cm_rep_global_array (globals) (index_pre))) ”
.

Definition cmc_global_array_at_return_wit_3_split_goal_spatial := 
forall (index_pre: Z) (item_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (PreH1 : ((cm_global_init (head)) <= INT64_MAX)) (PreH2 : ((cm_global_init (head)) >= INT64_MIN)) (PreH3 : ((cm_rep_bool ((cm_global_has_init (head)))) <= INT_MAX)) (PreH4 : ((cm_global_count (head)) <= INT_MAX)) (PreH5 : ((cm_type_encode ((cm_global_ty (head)))) <= INT_MAX)) (PreH6 : ((cm_rep_bool ((cm_global_has_init (head)))) >= INT_MIN)) (PreH7 : ((cm_global_count (head)) >= INT_MIN)) (PreH8 : ((cm_type_encode ((cm_global_ty (head)))) >= INT_MIN)) (PreH9 : (0 <= (index_pre - 1 ))) (PreH10 : (retval = (cm_rep_global_array (tail) ((index_pre - 1 ))))) (PreH11 : (index_pre <> 0)) (PreH12 : (item_pre <> 0)) (PreH13 : (globals = (cons (head) (tail)))) (PreH14 : (0 <= index_pre)) ,
  (cm_global_list_rep nextp tail )
  **  ((&((item_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((item_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((item_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((item_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((item_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
|--
  (cm_global_list_rep item_pre globals )
.

Definition cmc_global_array_at_partial_solve_wit_1 := 
forall (index_pre: Z) (item_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (PreH1 : (index_pre = 0)) (PreH2 : (item_pre <> 0)) (PreH3 : (globals = (cons (head) (tail)))) (PreH4 : (0 <= index_pre)) ,
  ((&((item_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((item_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((item_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((item_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((item_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
|--
  “ (index_pre = 0) ” 
  &&  “ (item_pre <> 0) ” 
  &&  “ (globals = (cons (head) (tail))) ” 
  &&  “ (0 <= index_pre) ”
  &&  ((&((item_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((item_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((item_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((item_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((item_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
.

Definition cmc_global_array_at_partial_solve_wit_2_pure := 
forall (index_pre: Z) (item_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (PreH1 : (index_pre <> 0)) (PreH2 : (item_pre <> 0)) (PreH3 : (globals = (cons (head) (tail)))) (PreH4 : (0 <= index_pre)) ,
  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((item_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((item_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((item_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((item_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((item_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
  **  ((( &( "result" ) )) # Int  |->_)
|--
  “ (0 <= (index_pre - 1 )) ”
.

Definition cmc_global_array_at_partial_solve_wit_2_aux := 
forall (index_pre: Z) (item_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (PreH1 : (index_pre <> 0)) (PreH2 : (item_pre <> 0)) (PreH3 : (globals = (cons (head) (tail)))) (PreH4 : (0 <= index_pre)) ,
  ((&((item_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((item_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((item_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((item_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((item_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
|--
  “ (0 <= (index_pre - 1 )) ” 
  &&  “ (index_pre <> 0) ” 
  &&  “ (item_pre <> 0) ” 
  &&  “ (globals = (cons (head) (tail))) ” 
  &&  “ (0 <= index_pre) ”
  &&  (cm_global_list_rep nextp tail )
  **  ((&((item_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((item_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((item_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((item_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((item_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
.

Definition cmc_global_array_at_partial_solve_wit_2 := cmc_global_array_at_partial_solve_wit_2_pure -> cmc_global_array_at_partial_solve_wit_2_aux.

(*----- Function cmc_slot_array_at -----*)

Definition cmc_slot_array_at_safety_wit_1 := 
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (PreH1 : (0 <= index_pre)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  (cm_slot_list_rep item_pre slots )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_slot_array_at_safety_wit_2 := 
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (PreH1 : (item_pre = 0)) (PreH2 : (0 <= index_pre)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  (cm_slot_list_rep item_pre slots )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_slot_array_at_safety_wit_3 := 
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (PreH1 : (item_pre <> 0)) (PreH2 : (slots = (cons (head) (tail)))) (PreH3 : (0 <= index_pre)) ,
  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((item_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
  **  ((( &( "result" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_slot_array_at_safety_wit_4 := 
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (PreH1 : (index_pre <> 0)) (PreH2 : (item_pre <> 0)) (PreH3 : (slots = (cons (head) (tail)))) (PreH4 : (0 <= index_pre)) ,
  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((item_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
  **  ((( &( "result" ) )) # Int  |->_)
|--
  “ ((index_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (index_pre - 1 )) ”
.

Definition cmc_slot_array_at_safety_wit_5 := 
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (PreH1 : (index_pre <> 0)) (PreH2 : (item_pre <> 0)) (PreH3 : (slots = (cons (head) (tail)))) (PreH4 : (0 <= index_pre)) ,
  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((item_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
  **  ((( &( "result" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmc_slot_array_at_entail_wit_1 := 
(
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (PreH1 : (item_pre <> 0)) (PreH2 : (0 <= index_pre)) ,
  (cm_slot_list_rep item_pre slots )
|--
  EX (nextp: Z)  (head: cm_slot_d)  (tail: (@list cm_slot_d)) ,
  “ (item_pre <> 0) ” 
  &&  “ (slots = (cons (head) (tail))) ” 
  &&  “ (0 <= index_pre) ”
  &&  ((&((item_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
) \/
(
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (PreH1 : (item_pre <> 0)) (PreH2 : (0 <= index_pre)) ,
  (cm_slot_list_rep item_pre slots )
|--
  EX (nextp: Z)  (head: cm_slot_d)  (tail: (@list cm_slot_d)) ,
  “ (item_pre <> 0) ” 
  &&  “ (slots = (cons (head) (tail))) ” 
  &&  “ (0 <= index_pre) ”
  &&  ((&((item_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
).

Definition cmc_slot_array_at_return_wit_1 := 
(
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (PreH1 : (item_pre = 0)) (PreH2 : (0 <= index_pre)) ,
  (cm_slot_list_rep item_pre slots )
|--
  “ (0 <= index_pre) ” 
  &&  “ (0 = (cm_rep_member_array (slots) (index_pre))) ”
  &&  (cm_slot_list_rep item_pre slots )
) \/
(
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (PreH1 : (item_pre = 0)) (PreH2 : (0 <= index_pre)) ,
  TT && emp 
|--
  “ (0 = (cm_rep_member_array (slots) (index_pre))) ”
  &&  emp
).

Definition cmc_slot_array_at_return_wit_1_split_goal_1 := 
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (PreH1 : (item_pre = 0)) (PreH2 : (0 <= index_pre)) ,
  (0 = (cm_rep_member_array (slots) (index_pre)))
.

Definition cmc_slot_array_at_return_wit_2 := 
(
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (PreH1 : (retval = (cm_rep_nonzero ((cm_slot_count (head)))))) (PreH2 : (index_pre = 0)) (PreH3 : (item_pre <> 0)) (PreH4 : (slots = (cons (head) (tail)))) (PreH5 : (0 <= index_pre)) ,
  ((&((item_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
|--
  “ (0 <= index_pre) ” 
  &&  “ (retval = (cm_rep_member_array (slots) (index_pre))) ”
  &&  (cm_slot_list_rep item_pre slots )
) \/
(
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (retval = (cm_rep_nonzero ((cm_slot_count (head)))))) (PreH6 : (index_pre = 0)) (PreH7 : (item_pre <> 0)) (PreH8 : (slots = (cons (head) (tail)))) (PreH9 : (0 <= index_pre)) ,
  ((&((item_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
|--
  “ (retval = (cm_rep_member_array (slots) (0))) ”
  &&  (cm_slot_list_rep item_pre slots )
).

Definition cmc_slot_array_at_return_wit_2_split_goal_1 := 
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (retval = (cm_rep_nonzero ((cm_slot_count (head)))))) (PreH6 : (index_pre = 0)) (PreH7 : (item_pre <> 0)) (PreH8 : (slots = (cons (head) (tail)))) (PreH9 : (0 <= index_pre)) ,
  ((&((item_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
|--
  “ (retval = (cm_rep_member_array (slots) (0))) ”
.

Definition cmc_slot_array_at_return_wit_2_split_goal_spatial := 
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (retval = (cm_rep_nonzero ((cm_slot_count (head)))))) (PreH6 : (index_pre = 0)) (PreH7 : (item_pre <> 0)) (PreH8 : (slots = (cons (head) (tail)))) (PreH9 : (0 <= index_pre)) ,
  ((&((item_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
|--
  (cm_slot_list_rep item_pre slots )
.

Definition cmc_slot_array_at_return_wit_3 := 
(
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (PreH1 : (0 <= (index_pre - 1 ))) (PreH2 : (retval = (cm_rep_member_array (tail) ((index_pre - 1 ))))) (PreH3 : (index_pre <> 0)) (PreH4 : (item_pre <> 0)) (PreH5 : (slots = (cons (head) (tail)))) (PreH6 : (0 <= index_pre)) ,
  (cm_slot_list_rep nextp tail )
  **  ((&((item_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (0 <= index_pre) ” 
  &&  “ (retval = (cm_rep_member_array (slots) (index_pre))) ”
  &&  (cm_slot_list_rep item_pre slots )
) \/
(
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (0 <= (index_pre - 1 ))) (PreH6 : (retval = (cm_rep_member_array (tail) ((index_pre - 1 ))))) (PreH7 : (index_pre <> 0)) (PreH8 : (item_pre <> 0)) (PreH9 : (slots = (cons (head) (tail)))) (PreH10 : (0 <= index_pre)) ,
  (cm_slot_list_rep nextp tail )
  **  ((&((item_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (retval = (cm_rep_member_array (slots) (index_pre))) ”
  &&  (cm_slot_list_rep item_pre slots )
).

Definition cmc_slot_array_at_return_wit_3_split_goal_1 := 
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (0 <= (index_pre - 1 ))) (PreH6 : (retval = (cm_rep_member_array (tail) ((index_pre - 1 ))))) (PreH7 : (index_pre <> 0)) (PreH8 : (item_pre <> 0)) (PreH9 : (slots = (cons (head) (tail)))) (PreH10 : (0 <= index_pre)) ,
  (cm_slot_list_rep nextp tail )
  **  ((&((item_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (retval = (cm_rep_member_array (slots) (index_pre))) ”
.

Definition cmc_slot_array_at_return_wit_3_split_goal_spatial := 
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (0 <= (index_pre - 1 ))) (PreH6 : (retval = (cm_rep_member_array (tail) ((index_pre - 1 ))))) (PreH7 : (index_pre <> 0)) (PreH8 : (item_pre <> 0)) (PreH9 : (slots = (cons (head) (tail)))) (PreH10 : (0 <= index_pre)) ,
  (cm_slot_list_rep nextp tail )
  **  ((&((item_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
|--
  (cm_slot_list_rep item_pre slots )
.

Definition cmc_slot_array_at_partial_solve_wit_1 := 
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (PreH1 : (index_pre = 0)) (PreH2 : (item_pre <> 0)) (PreH3 : (slots = (cons (head) (tail)))) (PreH4 : (0 <= index_pre)) ,
  ((&((item_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
|--
  “ (index_pre = 0) ” 
  &&  “ (item_pre <> 0) ” 
  &&  “ (slots = (cons (head) (tail))) ” 
  &&  “ (0 <= index_pre) ”
  &&  ((&((item_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
.

Definition cmc_slot_array_at_partial_solve_wit_2_pure := 
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (PreH1 : (index_pre <> 0)) (PreH2 : (item_pre <> 0)) (PreH3 : (slots = (cons (head) (tail)))) (PreH4 : (0 <= index_pre)) ,
  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((item_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
  **  ((( &( "result" ) )) # Int  |->_)
|--
  “ (0 <= (index_pre - 1 )) ”
.

Definition cmc_slot_array_at_partial_solve_wit_2_aux := 
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (PreH1 : (index_pre <> 0)) (PreH2 : (item_pre <> 0)) (PreH3 : (slots = (cons (head) (tail)))) (PreH4 : (0 <= index_pre)) ,
  ((&((item_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
|--
  “ (0 <= (index_pre - 1 )) ” 
  &&  “ (index_pre <> 0) ” 
  &&  “ (item_pre <> 0) ” 
  &&  “ (slots = (cons (head) (tail))) ” 
  &&  “ (0 <= index_pre) ”
  &&  (cm_slot_list_rep nextp tail )
  **  ((&((item_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
.

Definition cmc_slot_array_at_partial_solve_wit_2 := cmc_slot_array_at_partial_solve_wit_2_pure -> cmc_slot_array_at_partial_solve_wit_2_aux.

(*----- Function cmc_slot_type_at -----*)

Definition cmc_slot_type_at_safety_wit_1 := 
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (PreH1 : (0 <= index_pre)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  (cm_slot_list_rep item_pre slots )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_slot_type_at_safety_wit_2 := 
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (PreH1 : (item_pre = 0)) (PreH2 : (0 <= index_pre)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  (cm_slot_list_rep item_pre slots )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_slot_type_at_safety_wit_3 := 
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (PreH1 : (item_pre <> 0)) (PreH2 : (slots = (cons (head) (tail)))) (PreH3 : (0 <= index_pre)) ,
  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((item_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
  **  ((( &( "result" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_slot_type_at_safety_wit_4 := 
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (PreH1 : (index_pre <> 0)) (PreH2 : (item_pre <> 0)) (PreH3 : (slots = (cons (head) (tail)))) (PreH4 : (0 <= index_pre)) ,
  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((item_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
  **  ((( &( "result" ) )) # Int  |->_)
|--
  “ ((index_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (index_pre - 1 )) ”
.

Definition cmc_slot_type_at_safety_wit_5 := 
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (PreH1 : (index_pre <> 0)) (PreH2 : (item_pre <> 0)) (PreH3 : (slots = (cons (head) (tail)))) (PreH4 : (0 <= index_pre)) ,
  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((item_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
  **  ((( &( "result" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmc_slot_type_at_entail_wit_1 := 
(
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (PreH1 : (item_pre <> 0)) (PreH2 : (0 <= index_pre)) ,
  (cm_slot_list_rep item_pre slots )
|--
  EX (nextp: Z)  (head: cm_slot_d)  (tail: (@list cm_slot_d)) ,
  “ (item_pre <> 0) ” 
  &&  “ (slots = (cons (head) (tail))) ” 
  &&  “ (0 <= index_pre) ”
  &&  ((&((item_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
) \/
(
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (PreH1 : (item_pre <> 0)) (PreH2 : (0 <= index_pre)) ,
  (cm_slot_list_rep item_pre slots )
|--
  EX (nextp: Z)  (head: cm_slot_d)  (tail: (@list cm_slot_d)) ,
  “ (item_pre <> 0) ” 
  &&  “ (slots = (cons (head) (tail))) ” 
  &&  “ (0 <= index_pre) ”
  &&  ((&((item_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
).

Definition cmc_slot_type_at_return_wit_1 := 
(
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (PreH1 : (item_pre = 0)) (PreH2 : (0 <= index_pre)) ,
  (cm_slot_list_rep item_pre slots )
|--
  “ (0 <= index_pre) ” 
  &&  “ (0 = (cm_rep_slot_type (slots) (index_pre))) ”
  &&  (cm_slot_list_rep item_pre slots )
) \/
(
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (PreH1 : (item_pre = 0)) (PreH2 : (0 <= index_pre)) ,
  TT && emp 
|--
  “ (0 = (cm_rep_slot_type (slots) (index_pre))) ”
  &&  emp
).

Definition cmc_slot_type_at_return_wit_1_split_goal_1 := 
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (PreH1 : (item_pre = 0)) (PreH2 : (0 <= index_pre)) ,
  (0 = (cm_rep_slot_type (slots) (index_pre)))
.

Definition cmc_slot_type_at_return_wit_2 := 
(
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (PreH1 : (index_pre = 0)) (PreH2 : (item_pre <> 0)) (PreH3 : (slots = (cons (head) (tail)))) (PreH4 : (0 <= index_pre)) ,
  ((&((item_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
|--
  “ (0 <= index_pre) ” 
  &&  “ ((cm_type_encode ((cm_slot_ty (head)))) = (cm_rep_slot_type (slots) (index_pre))) ”
  &&  (cm_slot_list_rep item_pre slots )
) \/
(
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (index_pre = 0)) (PreH6 : (item_pre <> 0)) (PreH7 : (slots = (cons (head) (tail)))) (PreH8 : (0 <= index_pre)) ,
  ((&((item_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
|--
  “ ((cm_type_encode ((cm_slot_ty (head)))) = (cm_rep_slot_type (slots) (0))) ”
  &&  (cm_slot_list_rep item_pre slots )
).

Definition cmc_slot_type_at_return_wit_2_split_goal_1 := 
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (index_pre = 0)) (PreH6 : (item_pre <> 0)) (PreH7 : (slots = (cons (head) (tail)))) (PreH8 : (0 <= index_pre)) ,
  ((&((item_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
|--
  “ ((cm_type_encode ((cm_slot_ty (head)))) = (cm_rep_slot_type (slots) (0))) ”
.

Definition cmc_slot_type_at_return_wit_2_split_goal_spatial := 
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (index_pre = 0)) (PreH6 : (item_pre <> 0)) (PreH7 : (slots = (cons (head) (tail)))) (PreH8 : (0 <= index_pre)) ,
  ((&((item_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
|--
  (cm_slot_list_rep item_pre slots )
.

Definition cmc_slot_type_at_return_wit_3 := 
(
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (PreH1 : (0 <= (index_pre - 1 ))) (PreH2 : (retval = (cm_rep_slot_type (tail) ((index_pre - 1 ))))) (PreH3 : (index_pre <> 0)) (PreH4 : (item_pre <> 0)) (PreH5 : (slots = (cons (head) (tail)))) (PreH6 : (0 <= index_pre)) ,
  (cm_slot_list_rep nextp tail )
  **  ((&((item_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (0 <= index_pre) ” 
  &&  “ (retval = (cm_rep_slot_type (slots) (index_pre))) ”
  &&  (cm_slot_list_rep item_pre slots )
) \/
(
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (0 <= (index_pre - 1 ))) (PreH6 : (retval = (cm_rep_slot_type (tail) ((index_pre - 1 ))))) (PreH7 : (index_pre <> 0)) (PreH8 : (item_pre <> 0)) (PreH9 : (slots = (cons (head) (tail)))) (PreH10 : (0 <= index_pre)) ,
  (cm_slot_list_rep nextp tail )
  **  ((&((item_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (retval = (cm_rep_slot_type (slots) (index_pre))) ”
  &&  (cm_slot_list_rep item_pre slots )
).

Definition cmc_slot_type_at_return_wit_3_split_goal_1 := 
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (0 <= (index_pre - 1 ))) (PreH6 : (retval = (cm_rep_slot_type (tail) ((index_pre - 1 ))))) (PreH7 : (index_pre <> 0)) (PreH8 : (item_pre <> 0)) (PreH9 : (slots = (cons (head) (tail)))) (PreH10 : (0 <= index_pre)) ,
  (cm_slot_list_rep nextp tail )
  **  ((&((item_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (retval = (cm_rep_slot_type (slots) (index_pre))) ”
.

Definition cmc_slot_type_at_return_wit_3_split_goal_spatial := 
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (0 <= (index_pre - 1 ))) (PreH6 : (retval = (cm_rep_slot_type (tail) ((index_pre - 1 ))))) (PreH7 : (index_pre <> 0)) (PreH8 : (item_pre <> 0)) (PreH9 : (slots = (cons (head) (tail)))) (PreH10 : (0 <= index_pre)) ,
  (cm_slot_list_rep nextp tail )
  **  ((&((item_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
|--
  (cm_slot_list_rep item_pre slots )
.

Definition cmc_slot_type_at_partial_solve_wit_1_pure := 
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (PreH1 : (index_pre <> 0)) (PreH2 : (item_pre <> 0)) (PreH3 : (slots = (cons (head) (tail)))) (PreH4 : (0 <= index_pre)) ,
  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((item_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
  **  ((( &( "result" ) )) # Int  |->_)
|--
  “ (0 <= (index_pre - 1 )) ”
.

Definition cmc_slot_type_at_partial_solve_wit_1_aux := 
forall (index_pre: Z) (item_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (PreH1 : (index_pre <> 0)) (PreH2 : (item_pre <> 0)) (PreH3 : (slots = (cons (head) (tail)))) (PreH4 : (0 <= index_pre)) ,
  ((&((item_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
|--
  “ (0 <= (index_pre - 1 )) ” 
  &&  “ (index_pre <> 0) ” 
  &&  “ (item_pre <> 0) ” 
  &&  “ (slots = (cons (head) (tail))) ” 
  &&  “ (0 <= index_pre) ”
  &&  (cm_slot_list_rep nextp tail )
  **  ((&((item_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
.

Definition cmc_slot_type_at_partial_solve_wit_1 := cmc_slot_type_at_partial_solve_wit_1_pure -> cmc_slot_type_at_partial_solve_wit_1_aux.

(*----- Function cmc_member_array_at -----*)

Definition cmc_member_array_at_safety_wit_1 := 
forall (index_pre: Z) (item_pre: Z) (members: (@list cm_slot_d)) (PreH1 : (0 <= index_pre)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  (cm_member_list_rep item_pre members )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_member_array_at_safety_wit_2 := 
forall (index_pre: Z) (item_pre: Z) (members: (@list cm_slot_d)) (PreH1 : (item_pre = 0)) (PreH2 : (0 <= index_pre)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  (cm_member_list_rep item_pre members )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_member_array_at_safety_wit_3 := 
forall (index_pre: Z) (item_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (PreH1 : (item_pre <> 0)) (PreH2 : (members = (cons (head) (tail)))) (PreH3 : (0 <= index_pre)) ,
  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((item_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_member_list_rep nextp tail )
  **  ((( &( "result" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_member_array_at_safety_wit_4 := 
forall (index_pre: Z) (item_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (PreH1 : (index_pre <> 0)) (PreH2 : (item_pre <> 0)) (PreH3 : (members = (cons (head) (tail)))) (PreH4 : (0 <= index_pre)) ,
  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((item_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_member_list_rep nextp tail )
  **  ((( &( "result" ) )) # Int  |->_)
|--
  “ ((index_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (index_pre - 1 )) ”
.

Definition cmc_member_array_at_safety_wit_5 := 
forall (index_pre: Z) (item_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (PreH1 : (index_pre <> 0)) (PreH2 : (item_pre <> 0)) (PreH3 : (members = (cons (head) (tail)))) (PreH4 : (0 <= index_pre)) ,
  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((item_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_member_list_rep nextp tail )
  **  ((( &( "result" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmc_member_array_at_entail_wit_1 := 
(
forall (index_pre: Z) (item_pre: Z) (members: (@list cm_slot_d)) (PreH1 : (item_pre <> 0)) (PreH2 : (0 <= index_pre)) ,
  (cm_member_list_rep item_pre members )
|--
  EX (nextp: Z)  (head: cm_slot_d)  (tail: (@list cm_slot_d)) ,
  “ (item_pre <> 0) ” 
  &&  “ (members = (cons (head) (tail))) ” 
  &&  “ (0 <= index_pre) ”
  &&  ((&((item_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_member_list_rep nextp tail )
) \/
(
forall (index_pre: Z) (item_pre: Z) (members: (@list cm_slot_d)) (PreH1 : (item_pre <> 0)) (PreH2 : (0 <= index_pre)) ,
  (cm_member_list_rep item_pre members )
|--
  EX (nextp: Z)  (head: cm_slot_d)  (tail: (@list cm_slot_d)) ,
  “ (item_pre <> 0) ” 
  &&  “ (members = (cons (head) (tail))) ” 
  &&  “ (0 <= index_pre) ”
  &&  ((&((item_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_member_list_rep nextp tail )
).

Definition cmc_member_array_at_return_wit_1 := 
(
forall (index_pre: Z) (item_pre: Z) (members: (@list cm_slot_d)) (PreH1 : (item_pre = 0)) (PreH2 : (0 <= index_pre)) ,
  (cm_member_list_rep item_pre members )
|--
  “ (0 <= index_pre) ” 
  &&  “ (0 = (cm_rep_member_array (members) (index_pre))) ”
  &&  (cm_member_list_rep item_pre members )
) \/
(
forall (index_pre: Z) (item_pre: Z) (members: (@list cm_slot_d)) (PreH1 : (item_pre = 0)) (PreH2 : (0 <= index_pre)) ,
  TT && emp 
|--
  “ (0 = (cm_rep_member_array (members) (index_pre))) ”
  &&  emp
).

Definition cmc_member_array_at_return_wit_1_split_goal_1 := 
forall (index_pre: Z) (item_pre: Z) (members: (@list cm_slot_d)) (PreH1 : (item_pre = 0)) (PreH2 : (0 <= index_pre)) ,
  (0 = (cm_rep_member_array (members) (index_pre)))
.

Definition cmc_member_array_at_return_wit_2 := 
(
forall (index_pre: Z) (item_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (PreH1 : (retval = (cm_rep_nonzero ((cm_slot_count (head)))))) (PreH2 : (index_pre = 0)) (PreH3 : (item_pre <> 0)) (PreH4 : (members = (cons (head) (tail)))) (PreH5 : (0 <= index_pre)) ,
  ((&((item_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_member_list_rep nextp tail )
|--
  “ (0 <= index_pre) ” 
  &&  “ (retval = (cm_rep_member_array (members) (index_pre))) ”
  &&  (cm_member_list_rep item_pre members )
) \/
(
forall (index_pre: Z) (item_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (retval = (cm_rep_nonzero ((cm_slot_count (head)))))) (PreH6 : (index_pre = 0)) (PreH7 : (item_pre <> 0)) (PreH8 : (members = (cons (head) (tail)))) (PreH9 : (0 <= index_pre)) ,
  ((&((item_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_member_list_rep nextp tail )
|--
  “ (retval = (cm_rep_member_array (members) (0))) ”
  &&  (cm_member_list_rep item_pre members )
).

Definition cmc_member_array_at_return_wit_2_split_goal_1 := 
forall (index_pre: Z) (item_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (retval = (cm_rep_nonzero ((cm_slot_count (head)))))) (PreH6 : (index_pre = 0)) (PreH7 : (item_pre <> 0)) (PreH8 : (members = (cons (head) (tail)))) (PreH9 : (0 <= index_pre)) ,
  ((&((item_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_member_list_rep nextp tail )
|--
  “ (retval = (cm_rep_member_array (members) (0))) ”
.

Definition cmc_member_array_at_return_wit_2_split_goal_spatial := 
forall (index_pre: Z) (item_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (retval = (cm_rep_nonzero ((cm_slot_count (head)))))) (PreH6 : (index_pre = 0)) (PreH7 : (item_pre <> 0)) (PreH8 : (members = (cons (head) (tail)))) (PreH9 : (0 <= index_pre)) ,
  ((&((item_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_member_list_rep nextp tail )
|--
  (cm_member_list_rep item_pre members )
.

Definition cmc_member_array_at_return_wit_3 := 
(
forall (index_pre: Z) (item_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (PreH1 : (0 <= (index_pre - 1 ))) (PreH2 : (retval = (cm_rep_member_array (tail) ((index_pre - 1 ))))) (PreH3 : (index_pre <> 0)) (PreH4 : (item_pre <> 0)) (PreH5 : (members = (cons (head) (tail)))) (PreH6 : (0 <= index_pre)) ,
  (cm_member_list_rep nextp tail )
  **  ((&((item_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (0 <= index_pre) ” 
  &&  “ (retval = (cm_rep_member_array (members) (index_pre))) ”
  &&  (cm_member_list_rep item_pre members )
) \/
(
forall (index_pre: Z) (item_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (0 <= (index_pre - 1 ))) (PreH6 : (retval = (cm_rep_member_array (tail) ((index_pre - 1 ))))) (PreH7 : (index_pre <> 0)) (PreH8 : (item_pre <> 0)) (PreH9 : (members = (cons (head) (tail)))) (PreH10 : (0 <= index_pre)) ,
  (cm_member_list_rep nextp tail )
  **  ((&((item_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (retval = (cm_rep_member_array (members) (index_pre))) ”
  &&  (cm_member_list_rep item_pre members )
).

Definition cmc_member_array_at_return_wit_3_split_goal_1 := 
forall (index_pre: Z) (item_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (0 <= (index_pre - 1 ))) (PreH6 : (retval = (cm_rep_member_array (tail) ((index_pre - 1 ))))) (PreH7 : (index_pre <> 0)) (PreH8 : (item_pre <> 0)) (PreH9 : (members = (cons (head) (tail)))) (PreH10 : (0 <= index_pre)) ,
  (cm_member_list_rep nextp tail )
  **  ((&((item_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (retval = (cm_rep_member_array (members) (index_pre))) ”
.

Definition cmc_member_array_at_return_wit_3_split_goal_spatial := 
forall (index_pre: Z) (item_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (0 <= (index_pre - 1 ))) (PreH6 : (retval = (cm_rep_member_array (tail) ((index_pre - 1 ))))) (PreH7 : (index_pre <> 0)) (PreH8 : (item_pre <> 0)) (PreH9 : (members = (cons (head) (tail)))) (PreH10 : (0 <= index_pre)) ,
  (cm_member_list_rep nextp tail )
  **  ((&((item_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
|--
  (cm_member_list_rep item_pre members )
.

Definition cmc_member_array_at_partial_solve_wit_1 := 
forall (index_pre: Z) (item_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (PreH1 : (index_pre = 0)) (PreH2 : (item_pre <> 0)) (PreH3 : (members = (cons (head) (tail)))) (PreH4 : (0 <= index_pre)) ,
  ((&((item_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_member_list_rep nextp tail )
|--
  “ (index_pre = 0) ” 
  &&  “ (item_pre <> 0) ” 
  &&  “ (members = (cons (head) (tail))) ” 
  &&  “ (0 <= index_pre) ”
  &&  ((&((item_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_member_list_rep nextp tail )
.

Definition cmc_member_array_at_partial_solve_wit_2_pure := 
forall (index_pre: Z) (item_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (PreH1 : (index_pre <> 0)) (PreH2 : (item_pre <> 0)) (PreH3 : (members = (cons (head) (tail)))) (PreH4 : (0 <= index_pre)) ,
  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((item_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_member_list_rep nextp tail )
  **  ((( &( "result" ) )) # Int  |->_)
|--
  “ (0 <= (index_pre - 1 )) ”
.

Definition cmc_member_array_at_partial_solve_wit_2_aux := 
forall (index_pre: Z) (item_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (PreH1 : (index_pre <> 0)) (PreH2 : (item_pre <> 0)) (PreH3 : (members = (cons (head) (tail)))) (PreH4 : (0 <= index_pre)) ,
  ((&((item_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_member_list_rep nextp tail )
|--
  “ (0 <= (index_pre - 1 )) ” 
  &&  “ (index_pre <> 0) ” 
  &&  “ (item_pre <> 0) ” 
  &&  “ (members = (cons (head) (tail))) ” 
  &&  “ (0 <= index_pre) ”
  &&  (cm_member_list_rep nextp tail )
  **  ((&((item_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((item_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((item_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
.

Definition cmc_member_array_at_partial_solve_wit_2 := cmc_member_array_at_partial_solve_wit_2_pure -> cmc_member_array_at_partial_solve_wit_2_aux.

(*----- Function cmc_type_size_at -----*)

Definition cmc_type_size_at_safety_wit_1 := 
forall (ty_pre: Z) (items_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (0 <= ty_pre)) (PreH2 : (cm_rep_structs_safe structs )) ,
  ((( &( "result" ) )) # Int64  |->_)
  **  ((( &( "items" ) )) # Ptr  |-> items_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_struct_list_rep items_pre structs )
|--
  “ (1024 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1024) ”
.

Definition cmc_type_size_at_safety_wit_2 := 
forall (ty_pre: Z) (items_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (ty_pre >= 1024)) (PreH2 : (0 <= ty_pre)) (PreH3 : (cm_rep_structs_safe structs )) ,
  ((( &( "result" ) )) # Int64  |->_)
  **  ((( &( "items" ) )) # Ptr  |-> items_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_struct_list_rep items_pre structs )
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition cmc_type_size_at_safety_wit_3 := 
forall (ty_pre: Z) (items_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (ty_pre < 1024)) (PreH2 : (0 <= ty_pre)) (PreH3 : (cm_rep_structs_safe structs )) ,
  ((( &( "result" ) )) # Int64  |->_)
  **  ((( &( "items" ) )) # Ptr  |-> items_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_struct_list_rep items_pre structs )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_type_size_at_safety_wit_4 := 
forall (ty_pre: Z) (items_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (ty_pre = 0)) (PreH2 : (ty_pre < 1024)) (PreH3 : (0 <= ty_pre)) (PreH4 : (cm_rep_structs_safe structs )) ,
  ((( &( "result" ) )) # Int64  |->_)
  **  ((( &( "items" ) )) # Ptr  |-> items_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_struct_list_rep items_pre structs )
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition cmc_type_size_at_safety_wit_5 := 
forall (ty_pre: Z) (items_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (ty_pre <> 0)) (PreH2 : (ty_pre < 1024)) (PreH3 : (0 <= ty_pre)) (PreH4 : (cm_rep_structs_safe structs )) ,
  ((( &( "result" ) )) # Int64  |->_)
  **  ((( &( "items" ) )) # Ptr  |-> items_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_struct_list_rep items_pre structs )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmc_type_size_at_safety_wit_6 := 
forall (ty_pre: Z) (items_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (ty_pre = 1)) (PreH2 : (ty_pre <> 0)) (PreH3 : (ty_pre < 1024)) (PreH4 : (0 <= ty_pre)) (PreH5 : (cm_rep_structs_safe structs )) ,
  ((( &( "result" ) )) # Int64  |->_)
  **  ((( &( "items" ) )) # Ptr  |-> items_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_struct_list_rep items_pre structs )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmc_type_size_at_safety_wit_7 := 
forall (ty_pre: Z) (items_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (ty_pre <> 1)) (PreH2 : (ty_pre <> 0)) (PreH3 : (ty_pre < 1024)) (PreH4 : (0 <= ty_pre)) (PreH5 : (cm_rep_structs_safe structs )) ,
  ((( &( "result" ) )) # Int64  |->_)
  **  ((( &( "items" ) )) # Ptr  |-> items_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_struct_list_rep items_pre structs )
|--
  “ ((ty_pre - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ty_pre - 2 )) ”
.

Definition cmc_type_size_at_safety_wit_8 := 
forall (ty_pre: Z) (items_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (ty_pre <> 1)) (PreH2 : (ty_pre <> 0)) (PreH3 : (ty_pre < 1024)) (PreH4 : (0 <= ty_pre)) (PreH5 : (cm_rep_structs_safe structs )) ,
  ((( &( "result" ) )) # Int64  |->_)
  **  ((( &( "items" ) )) # Ptr  |-> items_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_struct_list_rep items_pre structs )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition cmc_type_size_at_return_wit_1 := 
(
forall (ty_pre: Z) (items_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (ty_pre >= 1024)) (PreH2 : (0 <= ty_pre)) (PreH3 : (cm_rep_structs_safe structs )) ,
  (cm_struct_list_rep items_pre structs )
|--
  “ (0 <= ty_pre) ” 
  &&  “ (cm_rep_structs_safe structs ) ” 
  &&  “ (8 = (cm_rep_type_size (structs) (ty_pre))) ”
  &&  (cm_struct_list_rep items_pre structs )
) \/
(
forall (ty_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (ty_pre >= 1024)) (PreH2 : (0 <= ty_pre)) (PreH3 : (cm_rep_structs_safe structs )) ,
  TT && emp 
|--
  “ (8 = (cm_rep_type_size (structs) (ty_pre))) ”
  &&  emp
).

Definition cmc_type_size_at_return_wit_1_split_goal_1 := 
forall (ty_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (ty_pre >= 1024)) (PreH2 : (0 <= ty_pre)) (PreH3 : (cm_rep_structs_safe structs )) ,
  (8 = (cm_rep_type_size (structs) (ty_pre)))
.

Definition cmc_type_size_at_return_wit_2 := 
(
forall (ty_pre: Z) (items_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (ty_pre = 0)) (PreH2 : (ty_pre < 1024)) (PreH3 : (0 <= ty_pre)) (PreH4 : (cm_rep_structs_safe structs )) ,
  (cm_struct_list_rep items_pre structs )
|--
  “ (0 <= ty_pre) ” 
  &&  “ (cm_rep_structs_safe structs ) ” 
  &&  “ (8 = (cm_rep_type_size (structs) (ty_pre))) ”
  &&  (cm_struct_list_rep items_pre structs )
) \/
(
forall (ty_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (ty_pre = 0)) (PreH2 : (ty_pre < 1024)) (PreH3 : (0 <= ty_pre)) (PreH4 : (cm_rep_structs_safe structs )) ,
  TT && emp 
|--
  “ (8 = (cm_rep_type_size (structs) (0))) ”
  &&  emp
).

Definition cmc_type_size_at_return_wit_2_split_goal_1 := 
forall (ty_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (ty_pre = 0)) (PreH2 : (ty_pre < 1024)) (PreH3 : (0 <= ty_pre)) (PreH4 : (cm_rep_structs_safe structs )) ,
  (8 = (cm_rep_type_size (structs) (0)))
.

Definition cmc_type_size_at_return_wit_3 := 
(
forall (ty_pre: Z) (items_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (ty_pre = 1)) (PreH2 : (ty_pre <> 0)) (PreH3 : (ty_pre < 1024)) (PreH4 : (0 <= ty_pre)) (PreH5 : (cm_rep_structs_safe structs )) ,
  (cm_struct_list_rep items_pre structs )
|--
  “ (0 <= ty_pre) ” 
  &&  “ (cm_rep_structs_safe structs ) ” 
  &&  “ (1 = (cm_rep_type_size (structs) (ty_pre))) ”
  &&  (cm_struct_list_rep items_pre structs )
) \/
(
forall (ty_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (ty_pre = 1)) (PreH2 : (ty_pre <> 0)) (PreH3 : (ty_pre < 1024)) (PreH4 : (0 <= ty_pre)) (PreH5 : (cm_rep_structs_safe structs )) ,
  TT && emp 
|--
  “ (1 = (cm_rep_type_size (structs) (1))) ”
  &&  emp
).

Definition cmc_type_size_at_return_wit_3_split_goal_1 := 
forall (ty_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (ty_pre = 1)) (PreH2 : (ty_pre <> 0)) (PreH3 : (ty_pre < 1024)) (PreH4 : (0 <= ty_pre)) (PreH5 : (cm_rep_structs_safe structs )) ,
  (1 = (cm_rep_type_size (structs) (1)))
.

Definition cmc_type_size_at_return_wit_4 := 
(
forall (ty_pre: Z) (items_pre: Z) (structs: (@list cm_struct_d)) (retval: Z) (PreH1 : (0 <= (ty_pre - 2 ))) (PreH2 : (cm_rep_structs_safe structs )) (PreH3 : (retval = (cm_rep_struct_size (structs) ((ty_pre - 2 ))))) (PreH4 : (ty_pre <> 1)) (PreH5 : (ty_pre <> 0)) (PreH6 : (ty_pre < 1024)) (PreH7 : (0 <= ty_pre)) (PreH8 : (cm_rep_structs_safe structs )) ,
  (cm_struct_list_rep items_pre structs )
|--
  “ (0 <= ty_pre) ” 
  &&  “ (cm_rep_structs_safe structs ) ” 
  &&  “ (retval = (cm_rep_type_size (structs) (ty_pre))) ”
  &&  (cm_struct_list_rep items_pre structs )
) \/
(
forall (ty_pre: Z) (structs: (@list cm_struct_d)) (retval: Z) (PreH1 : (0 <= (ty_pre - 2 ))) (PreH2 : (cm_rep_structs_safe structs )) (PreH3 : (retval = (cm_rep_struct_size (structs) ((ty_pre - 2 ))))) (PreH4 : (ty_pre <> 1)) (PreH5 : (ty_pre <> 0)) (PreH6 : (ty_pre < 1024)) (PreH7 : (0 <= ty_pre)) (PreH8 : (cm_rep_structs_safe structs )) ,
  TT && emp 
|--
  “ (retval = (cm_rep_type_size (structs) (ty_pre))) ”
  &&  emp
).

Definition cmc_type_size_at_return_wit_4_split_goal_1 := 
forall (ty_pre: Z) (structs: (@list cm_struct_d)) (retval: Z) (PreH1 : (0 <= (ty_pre - 2 ))) (PreH2 : (cm_rep_structs_safe structs )) (PreH3 : (retval = (cm_rep_struct_size (structs) ((ty_pre - 2 ))))) (PreH4 : (ty_pre <> 1)) (PreH5 : (ty_pre <> 0)) (PreH6 : (ty_pre < 1024)) (PreH7 : (0 <= ty_pre)) (PreH8 : (cm_rep_structs_safe structs )) ,
  (retval = (cm_rep_type_size (structs) (ty_pre)))
.

Definition cmc_type_size_at_partial_solve_wit_1_pure := 
forall (ty_pre: Z) (items_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (ty_pre <> 1)) (PreH2 : (ty_pre <> 0)) (PreH3 : (ty_pre < 1024)) (PreH4 : (0 <= ty_pre)) (PreH5 : (cm_rep_structs_safe structs )) ,
  ((( &( "result" ) )) # Int64  |->_)
  **  ((( &( "items" ) )) # Ptr  |-> items_pre)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
  **  (cm_struct_list_rep items_pre structs )
|--
  “ (0 <= (ty_pre - 2 )) ” 
  &&  “ (cm_rep_structs_safe structs ) ”
.

Definition cmc_type_size_at_partial_solve_wit_1_aux := 
forall (ty_pre: Z) (items_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (ty_pre <> 1)) (PreH2 : (ty_pre <> 0)) (PreH3 : (ty_pre < 1024)) (PreH4 : (0 <= ty_pre)) (PreH5 : (cm_rep_structs_safe structs )) ,
  (cm_struct_list_rep items_pre structs )
|--
  “ (0 <= (ty_pre - 2 )) ” 
  &&  “ (cm_rep_structs_safe structs ) ” 
  &&  “ (ty_pre <> 1) ” 
  &&  “ (ty_pre <> 0) ” 
  &&  “ (ty_pre < 1024) ” 
  &&  “ (0 <= ty_pre) ” 
  &&  “ (cm_rep_structs_safe structs ) ”
  &&  (cm_struct_list_rep items_pre structs )
.

Definition cmc_type_size_at_partial_solve_wit_1 := cmc_type_size_at_partial_solve_wit_1_pure -> cmc_type_size_at_partial_solve_wit_1_aux.

(*----- Function cmc_slots_size -----*)

Definition cmc_slots_size_safety_wit_1 := 
forall (slot_pre: Z) (slots: (@list cm_slot_d)) (PreH1 : (cm_rep_members_safe slots )) ,
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "slot" ) )) # Ptr  |-> slot_pre)
  **  (cm_slot_list_rep slot_pre slots )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_slots_size_safety_wit_2 := 
forall (slot_pre: Z) (slots: (@list cm_slot_d)) (PreH1 : (slot_pre = 0)) (PreH2 : (cm_rep_members_safe slots )) ,
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "slot" ) )) # Ptr  |-> slot_pre)
  **  (cm_slot_list_rep slot_pre slots )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_slots_size_safety_wit_3 := 
(
forall (slot_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : (cm_rep_members_safe tail )) (PreH2 : (retval_2 = (cm_rep_members_size (tail)))) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1048576)) (PreH5 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH6 : (slot_pre <> 0)) (PreH7 : (slots = (cons (head) (tail)))) (PreH8 : (cm_rep_members_safe slots )) (PreH9 : (cm_rep_members_safe tail )) ,
  (cm_slot_list_rep nextp tail )
  **  ((( &( "rest_size" ) )) # Int64  |-> retval_2)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> retval)
  **  ((( &( "slot" ) )) # Ptr  |-> slot_pre)
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ ((retval + retval_2 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (retval + retval_2 )) ”
) \/
(
forall (slot_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : (cm_rep_members_safe tail )) (PreH2 : (retval_2 = (cm_rep_members_size (tail)))) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1048576)) (PreH5 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH6 : (slot_pre <> 0)) (PreH7 : (slots = (cons (head) (tail)))) (PreH8 : (cm_rep_members_safe slots )) (PreH9 : (cm_rep_members_safe tail )) ,
  (cm_slot_list_rep nextp tail )
  **  ((( &( "rest_size" ) )) # Int64  |-> retval_2)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> retval)
  **  ((( &( "slot" ) )) # Ptr  |-> slot_pre)
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ ((retval + retval_2 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (retval + retval_2 )) ”
).

Definition cmc_slots_size_safety_wit_3_split_goal_1 := 
forall (slot_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : (cm_rep_members_safe tail )) (PreH2 : (retval_2 = (cm_rep_members_size (tail)))) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1048576)) (PreH5 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH6 : (slot_pre <> 0)) (PreH7 : (slots = (cons (head) (tail)))) (PreH8 : (cm_rep_members_safe slots )) (PreH9 : (cm_rep_members_safe tail )) ,
  (cm_slot_list_rep nextp tail )
  **  ((( &( "rest_size" ) )) # Int64  |-> retval_2)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> retval)
  **  ((( &( "slot" ) )) # Ptr  |-> slot_pre)
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ ((retval + retval_2 ) <= INT64_MAX) ”
.

Definition cmc_slots_size_safety_wit_3_split_goal_2 := 
forall (slot_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : (cm_rep_members_safe tail )) (PreH2 : (retval_2 = (cm_rep_members_size (tail)))) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1048576)) (PreH5 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH6 : (slot_pre <> 0)) (PreH7 : (slots = (cons (head) (tail)))) (PreH8 : (cm_rep_members_safe slots )) (PreH9 : (cm_rep_members_safe tail )) ,
  (cm_slot_list_rep nextp tail )
  **  ((( &( "rest_size" ) )) # Int64  |-> retval_2)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> retval)
  **  ((( &( "slot" ) )) # Ptr  |-> slot_pre)
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ ((INT64_MIN) <= (retval + retval_2 )) ”
.

Definition cmc_slots_size_entail_wit_1 := 
(
forall (slot_pre: Z) (slots: (@list cm_slot_d)) (PreH1 : (slot_pre <> 0)) (PreH2 : (cm_rep_members_safe slots )) ,
  (cm_slot_list_rep slot_pre slots )
|--
  EX (nextp: Z)  (head: cm_slot_d)  (tail: (@list cm_slot_d)) ,
  “ (slot_pre <> 0) ” 
  &&  “ (slots = (cons (head) (tail))) ” 
  &&  “ (cm_rep_members_safe slots ) ” 
  &&  “ (cm_rep_members_safe tail ) ”
  &&  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
) \/
(
forall (slot_pre: Z) (slots: (@list cm_slot_d)) (PreH1 : (slot_pre <> 0)) (PreH2 : (cm_rep_members_safe slots )) ,
  (cm_slot_list_rep slot_pre slots )
|--
  EX (nextp: Z)  (head: cm_slot_d)  (tail: (@list cm_slot_d)) ,
  “ (slot_pre <> 0) ” 
  &&  “ (slots = (cons (head) (tail))) ” 
  &&  “ (cm_rep_members_safe slots ) ” 
  &&  “ (cm_rep_members_safe tail ) ”
  &&  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
).

Definition cmc_slots_size_return_wit_1 := 
(
forall (slot_pre: Z) (slots: (@list cm_slot_d)) (PreH1 : (slot_pre = 0)) (PreH2 : (cm_rep_members_safe slots )) ,
  (cm_slot_list_rep slot_pre slots )
|--
  “ (cm_rep_members_safe slots ) ” 
  &&  “ (0 = (cm_rep_members_size (slots))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1048576) ”
  &&  (cm_slot_list_rep slot_pre slots )
) \/
(
forall (slot_pre: Z) (slots: (@list cm_slot_d)) (PreH1 : (slot_pre = 0)) (PreH2 : (cm_rep_members_safe slots )) ,
  TT && emp 
|--
  “ (0 = (cm_rep_members_size (slots))) ”
  &&  emp
).

Definition cmc_slots_size_return_wit_1_split_goal_1 := 
forall (slot_pre: Z) (slots: (@list cm_slot_d)) (PreH1 : (slot_pre = 0)) (PreH2 : (cm_rep_members_safe slots )) ,
  (0 = (cm_rep_members_size (slots)))
.

Definition cmc_slots_size_return_wit_2 := 
(
forall (slot_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : (cm_rep_members_safe tail )) (PreH2 : (retval_2 = (cm_rep_members_size (tail)))) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1048576)) (PreH5 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH6 : (slot_pre <> 0)) (PreH7 : (slots = (cons (head) (tail)))) (PreH8 : (cm_rep_members_safe slots )) (PreH9 : (cm_rep_members_safe tail )) ,
  (cm_slot_list_rep nextp tail )
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (cm_rep_members_safe slots ) ” 
  &&  “ ((retval + retval_2 ) = (cm_rep_members_size (slots))) ” 
  &&  “ (0 <= (retval + retval_2 )) ” 
  &&  “ ((retval + retval_2 ) <= 1048576) ”
  &&  (cm_slot_list_rep slot_pre slots )
) \/
(
forall (slot_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (cm_rep_members_safe tail )) (PreH6 : (retval_2 = (cm_rep_members_size (tail)))) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 <= 1048576)) (PreH9 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH10 : (slot_pre <> 0)) (PreH11 : (slots = (cons (head) (tail)))) (PreH12 : (cm_rep_members_safe slots )) (PreH13 : (cm_rep_members_safe tail )) ,
  (cm_slot_list_rep nextp tail )
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ ((retval + retval_2 ) <= 1048576) ” 
  &&  “ (0 <= (retval + retval_2 )) ” 
  &&  “ ((retval + retval_2 ) = (cm_rep_members_size (slots))) ”
  &&  (cm_slot_list_rep slot_pre slots )
).

Definition cmc_slots_size_return_wit_2_split_goal_1 := 
forall (slot_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (cm_rep_members_safe tail )) (PreH6 : (retval_2 = (cm_rep_members_size (tail)))) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 <= 1048576)) (PreH9 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH10 : (slot_pre <> 0)) (PreH11 : (slots = (cons (head) (tail)))) (PreH12 : (cm_rep_members_safe slots )) (PreH13 : (cm_rep_members_safe tail )) ,
  (cm_slot_list_rep nextp tail )
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ ((retval + retval_2 ) <= 1048576) ”
.

Definition cmc_slots_size_return_wit_2_split_goal_2 := 
forall (slot_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (cm_rep_members_safe tail )) (PreH6 : (retval_2 = (cm_rep_members_size (tail)))) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 <= 1048576)) (PreH9 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH10 : (slot_pre <> 0)) (PreH11 : (slots = (cons (head) (tail)))) (PreH12 : (cm_rep_members_safe slots )) (PreH13 : (cm_rep_members_safe tail )) ,
  (cm_slot_list_rep nextp tail )
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (0 <= (retval + retval_2 )) ”
.

Definition cmc_slots_size_return_wit_2_split_goal_3 := 
forall (slot_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (cm_rep_members_safe tail )) (PreH6 : (retval_2 = (cm_rep_members_size (tail)))) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 <= 1048576)) (PreH9 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH10 : (slot_pre <> 0)) (PreH11 : (slots = (cons (head) (tail)))) (PreH12 : (cm_rep_members_safe slots )) (PreH13 : (cm_rep_members_safe tail )) ,
  (cm_slot_list_rep nextp tail )
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ ((retval + retval_2 ) = (cm_rep_members_size (slots))) ”
.

Definition cmc_slots_size_return_wit_2_split_goal_spatial := 
forall (slot_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (cm_rep_members_safe tail )) (PreH6 : (retval_2 = (cm_rep_members_size (tail)))) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 <= 1048576)) (PreH9 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH10 : (slot_pre <> 0)) (PreH11 : (slots = (cons (head) (tail)))) (PreH12 : (cm_rep_members_safe slots )) (PreH13 : (cm_rep_members_safe tail )) ,
  (cm_slot_list_rep nextp tail )
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
|--
  (cm_slot_list_rep slot_pre slots )
.

Definition cmc_slots_size_partial_solve_wit_1 := 
forall (slot_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (PreH1 : (slot_pre <> 0)) (PreH2 : (slots = (cons (head) (tail)))) (PreH3 : (cm_rep_members_safe slots )) (PreH4 : (cm_rep_members_safe tail )) ,
  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
|--
  “ (slot_pre <> 0) ” 
  &&  “ (slots = (cons (head) (tail))) ” 
  &&  “ (cm_rep_members_safe slots ) ” 
  &&  “ (cm_rep_members_safe tail ) ”
  &&  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
.

Definition cmc_slots_size_partial_solve_wit_2_pure := 
forall (slot_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (PreH1 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH2 : (slot_pre <> 0)) (PreH3 : (slots = (cons (head) (tail)))) (PreH4 : (cm_rep_members_safe slots )) (PreH5 : (cm_rep_members_safe tail )) ,
  ((( &( "rest_size" ) )) # Int64  |->_)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> retval)
  **  ((( &( "slot" ) )) # Ptr  |-> slot_pre)
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ (cm_rep_members_safe tail ) ”
.

Definition cmc_slots_size_partial_solve_wit_2_aux := 
forall (slot_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (PreH1 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH2 : (slot_pre <> 0)) (PreH3 : (slots = (cons (head) (tail)))) (PreH4 : (cm_rep_members_safe slots )) (PreH5 : (cm_rep_members_safe tail )) ,
  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
|--
  “ (cm_rep_members_safe tail ) ” 
  &&  “ (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head))))) ” 
  &&  “ (slot_pre <> 0) ” 
  &&  “ (slots = (cons (head) (tail))) ” 
  &&  “ (cm_rep_members_safe slots ) ” 
  &&  “ (cm_rep_members_safe tail ) ”
  &&  (cm_slot_list_rep nextp tail )
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
.

Definition cmc_slots_size_partial_solve_wit_2 := cmc_slots_size_partial_solve_wit_2_pure -> cmc_slots_size_partial_solve_wit_2_aux.

(*----- Function cmc_slots_prefix -----*)

Definition cmc_slots_prefix_safety_wit_1 := 
forall (index_pre: Z) (slot_pre: Z) (slots: (@list cm_slot_d)) (PreH1 : (0 <= index_pre)) (PreH2 : (cm_rep_members_safe slots )) ,
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "slot" ) )) # Ptr  |-> slot_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  (cm_slot_list_rep slot_pre slots )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_slots_prefix_safety_wit_2 := 
forall (index_pre: Z) (slot_pre: Z) (slots: (@list cm_slot_d)) (PreH1 : (slot_pre = 0)) (PreH2 : (0 <= index_pre)) (PreH3 : (cm_rep_members_safe slots )) ,
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "slot" ) )) # Ptr  |-> slot_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  (cm_slot_list_rep slot_pre slots )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_slots_prefix_safety_wit_3 := 
forall (index_pre: Z) (slot_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (PreH1 : (slot_pre <> 0)) (PreH2 : (slots = (cons (head) (tail)))) (PreH3 : (0 <= index_pre)) (PreH4 : (cm_rep_members_safe slots )) (PreH5 : (cm_rep_members_safe tail )) ,
  ((( &( "slot" ) )) # Ptr  |-> slot_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_slots_prefix_safety_wit_4 := 
forall (index_pre: Z) (slot_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (PreH1 : (index_pre = 0)) (PreH2 : (slot_pre <> 0)) (PreH3 : (slots = (cons (head) (tail)))) (PreH4 : (0 <= index_pre)) (PreH5 : (cm_rep_members_safe slots )) (PreH6 : (cm_rep_members_safe tail )) ,
  ((( &( "slot" ) )) # Ptr  |-> slot_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_slots_prefix_safety_wit_5 := 
forall (index_pre: Z) (slot_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (PreH1 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH2 : (index_pre <> 0)) (PreH3 : (slot_pre <> 0)) (PreH4 : (slots = (cons (head) (tail)))) (PreH5 : (0 <= index_pre)) (PreH6 : (cm_rep_members_safe slots )) (PreH7 : (cm_rep_members_safe tail )) ,
  ((( &( "rest_size" ) )) # Int64  |->_)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> retval)
  **  ((( &( "slot" ) )) # Ptr  |-> slot_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ ((index_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (index_pre - 1 )) ”
.

Definition cmc_slots_prefix_safety_wit_6 := 
forall (index_pre: Z) (slot_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (PreH1 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH2 : (index_pre <> 0)) (PreH3 : (slot_pre <> 0)) (PreH4 : (slots = (cons (head) (tail)))) (PreH5 : (0 <= index_pre)) (PreH6 : (cm_rep_members_safe slots )) (PreH7 : (cm_rep_members_safe tail )) ,
  ((( &( "rest_size" ) )) # Int64  |->_)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> retval)
  **  ((( &( "slot" ) )) # Ptr  |-> slot_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmc_slots_prefix_safety_wit_7 := 
(
forall (index_pre: Z) (slot_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (index_pre - 1 ))) (PreH2 : (cm_rep_members_safe tail )) (PreH3 : (retval_2 = (cm_rep_member_prefix (tail) ((index_pre - 1 ))))) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1048576)) (PreH6 : (retval_2 <= (cm_rep_members_size (tail)))) (PreH7 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH8 : (index_pre <> 0)) (PreH9 : (slot_pre <> 0)) (PreH10 : (slots = (cons (head) (tail)))) (PreH11 : (0 <= index_pre)) (PreH12 : (cm_rep_members_safe slots )) (PreH13 : (cm_rep_members_safe tail )) ,
  (cm_slot_list_rep nextp tail )
  **  ((( &( "rest_size" ) )) # Int64  |-> retval_2)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> retval)
  **  ((( &( "slot" ) )) # Ptr  |-> slot_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ ((retval + retval_2 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (retval + retval_2 )) ”
) \/
(
forall (index_pre: Z) (slot_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (index_pre - 1 ))) (PreH2 : (cm_rep_members_safe tail )) (PreH3 : (retval_2 = (cm_rep_member_prefix (tail) ((index_pre - 1 ))))) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1048576)) (PreH6 : (retval_2 <= (cm_rep_members_size (tail)))) (PreH7 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH8 : (index_pre <> 0)) (PreH9 : (slot_pre <> 0)) (PreH10 : (slots = (cons (head) (tail)))) (PreH11 : (0 <= index_pre)) (PreH12 : (cm_rep_members_safe slots )) (PreH13 : (cm_rep_members_safe tail )) ,
  (cm_slot_list_rep nextp tail )
  **  ((( &( "rest_size" ) )) # Int64  |-> retval_2)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> retval)
  **  ((( &( "slot" ) )) # Ptr  |-> slot_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ ((retval + retval_2 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (retval + retval_2 )) ”
).

Definition cmc_slots_prefix_safety_wit_7_split_goal_1 := 
forall (index_pre: Z) (slot_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (index_pre - 1 ))) (PreH2 : (cm_rep_members_safe tail )) (PreH3 : (retval_2 = (cm_rep_member_prefix (tail) ((index_pre - 1 ))))) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1048576)) (PreH6 : (retval_2 <= (cm_rep_members_size (tail)))) (PreH7 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH8 : (index_pre <> 0)) (PreH9 : (slot_pre <> 0)) (PreH10 : (slots = (cons (head) (tail)))) (PreH11 : (0 <= index_pre)) (PreH12 : (cm_rep_members_safe slots )) (PreH13 : (cm_rep_members_safe tail )) ,
  (cm_slot_list_rep nextp tail )
  **  ((( &( "rest_size" ) )) # Int64  |-> retval_2)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> retval)
  **  ((( &( "slot" ) )) # Ptr  |-> slot_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ ((retval + retval_2 ) <= INT64_MAX) ”
.

Definition cmc_slots_prefix_safety_wit_7_split_goal_2 := 
forall (index_pre: Z) (slot_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (index_pre - 1 ))) (PreH2 : (cm_rep_members_safe tail )) (PreH3 : (retval_2 = (cm_rep_member_prefix (tail) ((index_pre - 1 ))))) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1048576)) (PreH6 : (retval_2 <= (cm_rep_members_size (tail)))) (PreH7 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH8 : (index_pre <> 0)) (PreH9 : (slot_pre <> 0)) (PreH10 : (slots = (cons (head) (tail)))) (PreH11 : (0 <= index_pre)) (PreH12 : (cm_rep_members_safe slots )) (PreH13 : (cm_rep_members_safe tail )) ,
  (cm_slot_list_rep nextp tail )
  **  ((( &( "rest_size" ) )) # Int64  |-> retval_2)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> retval)
  **  ((( &( "slot" ) )) # Ptr  |-> slot_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ ((INT64_MIN) <= (retval + retval_2 )) ”
.

Definition cmc_slots_prefix_entail_wit_1 := 
(
forall (index_pre: Z) (slot_pre: Z) (slots: (@list cm_slot_d)) (PreH1 : (slot_pre <> 0)) (PreH2 : (0 <= index_pre)) (PreH3 : (cm_rep_members_safe slots )) ,
  (cm_slot_list_rep slot_pre slots )
|--
  EX (nextp: Z)  (head: cm_slot_d)  (tail: (@list cm_slot_d)) ,
  “ (slot_pre <> 0) ” 
  &&  “ (slots = (cons (head) (tail))) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_members_safe slots ) ” 
  &&  “ (cm_rep_members_safe tail ) ”
  &&  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
) \/
(
forall (index_pre: Z) (slot_pre: Z) (slots: (@list cm_slot_d)) (PreH1 : (slot_pre <> 0)) (PreH2 : (0 <= index_pre)) (PreH3 : (cm_rep_members_safe slots )) ,
  (cm_slot_list_rep slot_pre slots )
|--
  EX (nextp: Z)  (head: cm_slot_d)  (tail: (@list cm_slot_d)) ,
  “ (slot_pre <> 0) ” 
  &&  “ (slots = (cons (head) (tail))) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_members_safe slots ) ” 
  &&  “ (cm_rep_members_safe tail ) ”
  &&  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
).

Definition cmc_slots_prefix_return_wit_1 := 
(
forall (index_pre: Z) (slot_pre: Z) (slots: (@list cm_slot_d)) (PreH1 : (slot_pre = 0)) (PreH2 : (0 <= index_pre)) (PreH3 : (cm_rep_members_safe slots )) ,
  (cm_slot_list_rep slot_pre slots )
|--
  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_members_safe slots ) ” 
  &&  “ (0 = (cm_rep_member_prefix (slots) (index_pre))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1048576) ” 
  &&  “ (0 <= (cm_rep_members_size (slots))) ”
  &&  (cm_slot_list_rep slot_pre slots )
) \/
(
forall (index_pre: Z) (slot_pre: Z) (slots: (@list cm_slot_d)) (PreH1 : (slot_pre = 0)) (PreH2 : (0 <= index_pre)) (PreH3 : (cm_rep_members_safe slots )) ,
  TT && emp 
|--
  “ (0 <= (cm_rep_members_size (slots))) ” 
  &&  “ (0 = (cm_rep_member_prefix (slots) (index_pre))) ”
  &&  emp
).

Definition cmc_slots_prefix_return_wit_1_split_goal_1 := 
forall (index_pre: Z) (slot_pre: Z) (slots: (@list cm_slot_d)) (PreH1 : (slot_pre = 0)) (PreH2 : (0 <= index_pre)) (PreH3 : (cm_rep_members_safe slots )) ,
  (0 <= (cm_rep_members_size (slots)))
.

Definition cmc_slots_prefix_return_wit_1_split_goal_2 := 
forall (index_pre: Z) (slot_pre: Z) (slots: (@list cm_slot_d)) (PreH1 : (slot_pre = 0)) (PreH2 : (0 <= index_pre)) (PreH3 : (cm_rep_members_safe slots )) ,
  (0 = (cm_rep_member_prefix (slots) (index_pre)))
.

Definition cmc_slots_prefix_return_wit_2 := 
(
forall (index_pre: Z) (slot_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (PreH1 : (index_pre = 0)) (PreH2 : (slot_pre <> 0)) (PreH3 : (slots = (cons (head) (tail)))) (PreH4 : (0 <= index_pre)) (PreH5 : (cm_rep_members_safe slots )) (PreH6 : (cm_rep_members_safe tail )) ,
  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
|--
  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_members_safe slots ) ” 
  &&  “ (0 = (cm_rep_member_prefix (slots) (index_pre))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1048576) ” 
  &&  “ (0 <= (cm_rep_members_size (slots))) ”
  &&  (cm_slot_list_rep slot_pre slots )
) \/
(
forall (index_pre: Z) (slot_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (index_pre = 0)) (PreH6 : (slot_pre <> 0)) (PreH7 : (slots = (cons (head) (tail)))) (PreH8 : (0 <= index_pre)) (PreH9 : (cm_rep_members_safe slots )) (PreH10 : (cm_rep_members_safe tail )) ,
  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
|--
  “ (0 <= (cm_rep_members_size (slots))) ” 
  &&  “ (0 = (cm_rep_member_prefix (slots) (0))) ”
  &&  (cm_slot_list_rep slot_pre slots )
).

Definition cmc_slots_prefix_return_wit_2_split_goal_1 := 
forall (index_pre: Z) (slot_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (index_pre = 0)) (PreH6 : (slot_pre <> 0)) (PreH7 : (slots = (cons (head) (tail)))) (PreH8 : (0 <= index_pre)) (PreH9 : (cm_rep_members_safe slots )) (PreH10 : (cm_rep_members_safe tail )) ,
  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
|--
  “ (0 <= (cm_rep_members_size (slots))) ”
.

Definition cmc_slots_prefix_return_wit_2_split_goal_2 := 
forall (index_pre: Z) (slot_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (index_pre = 0)) (PreH6 : (slot_pre <> 0)) (PreH7 : (slots = (cons (head) (tail)))) (PreH8 : (0 <= index_pre)) (PreH9 : (cm_rep_members_safe slots )) (PreH10 : (cm_rep_members_safe tail )) ,
  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
|--
  “ (0 = (cm_rep_member_prefix (slots) (0))) ”
.

Definition cmc_slots_prefix_return_wit_2_split_goal_spatial := 
forall (index_pre: Z) (slot_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (index_pre = 0)) (PreH6 : (slot_pre <> 0)) (PreH7 : (slots = (cons (head) (tail)))) (PreH8 : (0 <= index_pre)) (PreH9 : (cm_rep_members_safe slots )) (PreH10 : (cm_rep_members_safe tail )) ,
  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
|--
  (cm_slot_list_rep slot_pre slots )
.

Definition cmc_slots_prefix_return_wit_3 := 
(
forall (index_pre: Z) (slot_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (index_pre - 1 ))) (PreH2 : (cm_rep_members_safe tail )) (PreH3 : (retval_2 = (cm_rep_member_prefix (tail) ((index_pre - 1 ))))) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1048576)) (PreH6 : (retval_2 <= (cm_rep_members_size (tail)))) (PreH7 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH8 : (index_pre <> 0)) (PreH9 : (slot_pre <> 0)) (PreH10 : (slots = (cons (head) (tail)))) (PreH11 : (0 <= index_pre)) (PreH12 : (cm_rep_members_safe slots )) (PreH13 : (cm_rep_members_safe tail )) ,
  (cm_slot_list_rep nextp tail )
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_members_safe slots ) ” 
  &&  “ ((retval + retval_2 ) = (cm_rep_member_prefix (slots) (index_pre))) ” 
  &&  “ (0 <= (retval + retval_2 )) ” 
  &&  “ ((retval + retval_2 ) <= 1048576) ” 
  &&  “ ((retval + retval_2 ) <= (cm_rep_members_size (slots))) ”
  &&  (cm_slot_list_rep slot_pre slots )
) \/
(
forall (index_pre: Z) (slot_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (0 <= (index_pre - 1 ))) (PreH6 : (cm_rep_members_safe tail )) (PreH7 : (retval_2 = (cm_rep_member_prefix (tail) ((index_pre - 1 ))))) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1048576)) (PreH10 : (retval_2 <= (cm_rep_members_size (tail)))) (PreH11 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH12 : (index_pre <> 0)) (PreH13 : (slot_pre <> 0)) (PreH14 : (slots = (cons (head) (tail)))) (PreH15 : (0 <= index_pre)) (PreH16 : (cm_rep_members_safe slots )) (PreH17 : (cm_rep_members_safe tail )) ,
  (cm_slot_list_rep nextp tail )
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ ((retval + retval_2 ) <= (cm_rep_members_size (slots))) ” 
  &&  “ ((retval + retval_2 ) <= 1048576) ” 
  &&  “ (0 <= (retval + retval_2 )) ” 
  &&  “ ((retval + retval_2 ) = (cm_rep_member_prefix (slots) (index_pre))) ”
  &&  (cm_slot_list_rep slot_pre slots )
).

Definition cmc_slots_prefix_return_wit_3_split_goal_1 := 
forall (index_pre: Z) (slot_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (0 <= (index_pre - 1 ))) (PreH6 : (cm_rep_members_safe tail )) (PreH7 : (retval_2 = (cm_rep_member_prefix (tail) ((index_pre - 1 ))))) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1048576)) (PreH10 : (retval_2 <= (cm_rep_members_size (tail)))) (PreH11 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH12 : (index_pre <> 0)) (PreH13 : (slot_pre <> 0)) (PreH14 : (slots = (cons (head) (tail)))) (PreH15 : (0 <= index_pre)) (PreH16 : (cm_rep_members_safe slots )) (PreH17 : (cm_rep_members_safe tail )) ,
  (cm_slot_list_rep nextp tail )
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ ((retval + retval_2 ) <= (cm_rep_members_size (slots))) ”
.

Definition cmc_slots_prefix_return_wit_3_split_goal_2 := 
forall (index_pre: Z) (slot_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (0 <= (index_pre - 1 ))) (PreH6 : (cm_rep_members_safe tail )) (PreH7 : (retval_2 = (cm_rep_member_prefix (tail) ((index_pre - 1 ))))) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1048576)) (PreH10 : (retval_2 <= (cm_rep_members_size (tail)))) (PreH11 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH12 : (index_pre <> 0)) (PreH13 : (slot_pre <> 0)) (PreH14 : (slots = (cons (head) (tail)))) (PreH15 : (0 <= index_pre)) (PreH16 : (cm_rep_members_safe slots )) (PreH17 : (cm_rep_members_safe tail )) ,
  (cm_slot_list_rep nextp tail )
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ ((retval + retval_2 ) <= 1048576) ”
.

Definition cmc_slots_prefix_return_wit_3_split_goal_3 := 
forall (index_pre: Z) (slot_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (0 <= (index_pre - 1 ))) (PreH6 : (cm_rep_members_safe tail )) (PreH7 : (retval_2 = (cm_rep_member_prefix (tail) ((index_pre - 1 ))))) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1048576)) (PreH10 : (retval_2 <= (cm_rep_members_size (tail)))) (PreH11 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH12 : (index_pre <> 0)) (PreH13 : (slot_pre <> 0)) (PreH14 : (slots = (cons (head) (tail)))) (PreH15 : (0 <= index_pre)) (PreH16 : (cm_rep_members_safe slots )) (PreH17 : (cm_rep_members_safe tail )) ,
  (cm_slot_list_rep nextp tail )
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (0 <= (retval + retval_2 )) ”
.

Definition cmc_slots_prefix_return_wit_3_split_goal_4 := 
forall (index_pre: Z) (slot_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (0 <= (index_pre - 1 ))) (PreH6 : (cm_rep_members_safe tail )) (PreH7 : (retval_2 = (cm_rep_member_prefix (tail) ((index_pre - 1 ))))) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1048576)) (PreH10 : (retval_2 <= (cm_rep_members_size (tail)))) (PreH11 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH12 : (index_pre <> 0)) (PreH13 : (slot_pre <> 0)) (PreH14 : (slots = (cons (head) (tail)))) (PreH15 : (0 <= index_pre)) (PreH16 : (cm_rep_members_safe slots )) (PreH17 : (cm_rep_members_safe tail )) ,
  (cm_slot_list_rep nextp tail )
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ ((retval + retval_2 ) = (cm_rep_member_prefix (slots) (index_pre))) ”
.

Definition cmc_slots_prefix_return_wit_3_split_goal_spatial := 
forall (index_pre: Z) (slot_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (0 <= (index_pre - 1 ))) (PreH6 : (cm_rep_members_safe tail )) (PreH7 : (retval_2 = (cm_rep_member_prefix (tail) ((index_pre - 1 ))))) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1048576)) (PreH10 : (retval_2 <= (cm_rep_members_size (tail)))) (PreH11 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH12 : (index_pre <> 0)) (PreH13 : (slot_pre <> 0)) (PreH14 : (slots = (cons (head) (tail)))) (PreH15 : (0 <= index_pre)) (PreH16 : (cm_rep_members_safe slots )) (PreH17 : (cm_rep_members_safe tail )) ,
  (cm_slot_list_rep nextp tail )
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
|--
  (cm_slot_list_rep slot_pre slots )
.

Definition cmc_slots_prefix_partial_solve_wit_1 := 
forall (index_pre: Z) (slot_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (PreH1 : (index_pre <> 0)) (PreH2 : (slot_pre <> 0)) (PreH3 : (slots = (cons (head) (tail)))) (PreH4 : (0 <= index_pre)) (PreH5 : (cm_rep_members_safe slots )) (PreH6 : (cm_rep_members_safe tail )) ,
  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
|--
  “ (index_pre <> 0) ” 
  &&  “ (slot_pre <> 0) ” 
  &&  “ (slots = (cons (head) (tail))) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_members_safe slots ) ” 
  &&  “ (cm_rep_members_safe tail ) ”
  &&  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
.

Definition cmc_slots_prefix_partial_solve_wit_2_pure := 
forall (index_pre: Z) (slot_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (PreH1 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH2 : (index_pre <> 0)) (PreH3 : (slot_pre <> 0)) (PreH4 : (slots = (cons (head) (tail)))) (PreH5 : (0 <= index_pre)) (PreH6 : (cm_rep_members_safe slots )) (PreH7 : (cm_rep_members_safe tail )) ,
  ((( &( "rest_size" ) )) # Int64  |->_)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> retval)
  **  ((( &( "slot" ) )) # Ptr  |-> slot_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ (0 <= (index_pre - 1 )) ” 
  &&  “ (cm_rep_members_safe tail ) ”
.

Definition cmc_slots_prefix_partial_solve_wit_2_aux := 
forall (index_pre: Z) (slot_pre: Z) (slots: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (PreH1 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH2 : (index_pre <> 0)) (PreH3 : (slot_pre <> 0)) (PreH4 : (slots = (cons (head) (tail)))) (PreH5 : (0 <= index_pre)) (PreH6 : (cm_rep_members_safe slots )) (PreH7 : (cm_rep_members_safe tail )) ,
  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_slot_list_rep nextp tail )
|--
  “ (0 <= (index_pre - 1 )) ” 
  &&  “ (cm_rep_members_safe tail ) ” 
  &&  “ (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head))))) ” 
  &&  “ (index_pre <> 0) ” 
  &&  “ (slot_pre <> 0) ” 
  &&  “ (slots = (cons (head) (tail))) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_members_safe slots ) ” 
  &&  “ (cm_rep_members_safe tail ) ”
  &&  (cm_slot_list_rep nextp tail )
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((slot_pre)  # "cm_slot" ->ₛ "next")) # Ptr  |-> nextp)
.

Definition cmc_slots_prefix_partial_solve_wit_2 := cmc_slots_prefix_partial_solve_wit_2_pure -> cmc_slots_prefix_partial_solve_wit_2_aux.

(*----- Function cmc_members_prefix -----*)

Definition cmc_members_prefix_safety_wit_1 := 
forall (index_pre: Z) (node_pre: Z) (members: (@list cm_slot_d)) (PreH1 : (0 <= index_pre)) (PreH2 : (cm_rep_members_safe members )) ,
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  (cm_member_list_rep node_pre members )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_members_prefix_safety_wit_2 := 
forall (index_pre: Z) (node_pre: Z) (members: (@list cm_slot_d)) (PreH1 : (node_pre = 0)) (PreH2 : (0 <= index_pre)) (PreH3 : (cm_rep_members_safe members )) ,
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  (cm_member_list_rep node_pre members )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_members_prefix_safety_wit_3 := 
forall (index_pre: Z) (node_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (PreH1 : (node_pre <> 0)) (PreH2 : (members = (cons (head) (tail)))) (PreH3 : (0 <= index_pre)) (PreH4 : (cm_rep_members_safe members )) (PreH5 : (cm_rep_members_safe tail )) ,
  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((node_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((node_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((node_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_member_list_rep nextp tail )
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_members_prefix_safety_wit_4 := 
forall (index_pre: Z) (node_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (PreH1 : (index_pre = 0)) (PreH2 : (node_pre <> 0)) (PreH3 : (members = (cons (head) (tail)))) (PreH4 : (0 <= index_pre)) (PreH5 : (cm_rep_members_safe members )) (PreH6 : (cm_rep_members_safe tail )) ,
  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((node_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((node_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((node_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_member_list_rep nextp tail )
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_members_prefix_safety_wit_5 := 
forall (index_pre: Z) (node_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (PreH1 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH2 : (index_pre <> 0)) (PreH3 : (node_pre <> 0)) (PreH4 : (members = (cons (head) (tail)))) (PreH5 : (0 <= index_pre)) (PreH6 : (cm_rep_members_safe members )) (PreH7 : (cm_rep_members_safe tail )) ,
  ((( &( "rest_size" ) )) # Int64  |->_)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> retval)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((node_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((node_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((node_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_member_list_rep nextp tail )
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ ((index_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (index_pre - 1 )) ”
.

Definition cmc_members_prefix_safety_wit_6 := 
forall (index_pre: Z) (node_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (PreH1 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH2 : (index_pre <> 0)) (PreH3 : (node_pre <> 0)) (PreH4 : (members = (cons (head) (tail)))) (PreH5 : (0 <= index_pre)) (PreH6 : (cm_rep_members_safe members )) (PreH7 : (cm_rep_members_safe tail )) ,
  ((( &( "rest_size" ) )) # Int64  |->_)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> retval)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((node_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((node_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((node_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_member_list_rep nextp tail )
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmc_members_prefix_safety_wit_7 := 
(
forall (index_pre: Z) (node_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (index_pre - 1 ))) (PreH2 : (cm_rep_members_safe tail )) (PreH3 : (retval_2 = (cm_rep_member_prefix (tail) ((index_pre - 1 ))))) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1048576)) (PreH6 : (retval_2 <= (cm_rep_members_size (tail)))) (PreH7 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH8 : (index_pre <> 0)) (PreH9 : (node_pre <> 0)) (PreH10 : (members = (cons (head) (tail)))) (PreH11 : (0 <= index_pre)) (PreH12 : (cm_rep_members_safe members )) (PreH13 : (cm_rep_members_safe tail )) ,
  (cm_member_list_rep nextp tail )
  **  ((( &( "rest_size" ) )) # Int64  |-> retval_2)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> retval)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((node_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((node_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((node_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ ((retval + retval_2 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (retval + retval_2 )) ”
) \/
(
forall (index_pre: Z) (node_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (index_pre - 1 ))) (PreH2 : (cm_rep_members_safe tail )) (PreH3 : (retval_2 = (cm_rep_member_prefix (tail) ((index_pre - 1 ))))) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1048576)) (PreH6 : (retval_2 <= (cm_rep_members_size (tail)))) (PreH7 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH8 : (index_pre <> 0)) (PreH9 : (node_pre <> 0)) (PreH10 : (members = (cons (head) (tail)))) (PreH11 : (0 <= index_pre)) (PreH12 : (cm_rep_members_safe members )) (PreH13 : (cm_rep_members_safe tail )) ,
  (cm_member_list_rep nextp tail )
  **  ((( &( "rest_size" ) )) # Int64  |-> retval_2)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> retval)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((node_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((node_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((node_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ ((retval + retval_2 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (retval + retval_2 )) ”
).

Definition cmc_members_prefix_safety_wit_7_split_goal_1 := 
forall (index_pre: Z) (node_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (index_pre - 1 ))) (PreH2 : (cm_rep_members_safe tail )) (PreH3 : (retval_2 = (cm_rep_member_prefix (tail) ((index_pre - 1 ))))) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1048576)) (PreH6 : (retval_2 <= (cm_rep_members_size (tail)))) (PreH7 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH8 : (index_pre <> 0)) (PreH9 : (node_pre <> 0)) (PreH10 : (members = (cons (head) (tail)))) (PreH11 : (0 <= index_pre)) (PreH12 : (cm_rep_members_safe members )) (PreH13 : (cm_rep_members_safe tail )) ,
  (cm_member_list_rep nextp tail )
  **  ((( &( "rest_size" ) )) # Int64  |-> retval_2)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> retval)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((node_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((node_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((node_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ ((retval + retval_2 ) <= INT64_MAX) ”
.

Definition cmc_members_prefix_safety_wit_7_split_goal_2 := 
forall (index_pre: Z) (node_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (index_pre - 1 ))) (PreH2 : (cm_rep_members_safe tail )) (PreH3 : (retval_2 = (cm_rep_member_prefix (tail) ((index_pre - 1 ))))) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1048576)) (PreH6 : (retval_2 <= (cm_rep_members_size (tail)))) (PreH7 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH8 : (index_pre <> 0)) (PreH9 : (node_pre <> 0)) (PreH10 : (members = (cons (head) (tail)))) (PreH11 : (0 <= index_pre)) (PreH12 : (cm_rep_members_safe members )) (PreH13 : (cm_rep_members_safe tail )) ,
  (cm_member_list_rep nextp tail )
  **  ((( &( "rest_size" ) )) # Int64  |-> retval_2)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> retval)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((node_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((node_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((node_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ ((INT64_MIN) <= (retval + retval_2 )) ”
.

Definition cmc_members_prefix_entail_wit_1 := 
(
forall (index_pre: Z) (node_pre: Z) (members: (@list cm_slot_d)) (PreH1 : (node_pre <> 0)) (PreH2 : (0 <= index_pre)) (PreH3 : (cm_rep_members_safe members )) ,
  (cm_member_list_rep node_pre members )
|--
  EX (nextp: Z)  (head: cm_slot_d)  (tail: (@list cm_slot_d)) ,
  “ (node_pre <> 0) ” 
  &&  “ (members = (cons (head) (tail))) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_members_safe members ) ” 
  &&  “ (cm_rep_members_safe tail ) ”
  &&  ((&((node_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((node_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((node_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_member_list_rep nextp tail )
) \/
(
forall (index_pre: Z) (node_pre: Z) (members: (@list cm_slot_d)) (PreH1 : (node_pre <> 0)) (PreH2 : (0 <= index_pre)) (PreH3 : (cm_rep_members_safe members )) ,
  (cm_member_list_rep node_pre members )
|--
  EX (nextp: Z)  (head: cm_slot_d)  (tail: (@list cm_slot_d)) ,
  “ (node_pre <> 0) ” 
  &&  “ (members = (cons (head) (tail))) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_members_safe members ) ” 
  &&  “ (cm_rep_members_safe tail ) ”
  &&  ((&((node_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((node_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((node_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_member_list_rep nextp tail )
).

Definition cmc_members_prefix_return_wit_1 := 
(
forall (index_pre: Z) (node_pre: Z) (members: (@list cm_slot_d)) (PreH1 : (node_pre = 0)) (PreH2 : (0 <= index_pre)) (PreH3 : (cm_rep_members_safe members )) ,
  (cm_member_list_rep node_pre members )
|--
  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_members_safe members ) ” 
  &&  “ (0 = (cm_rep_member_prefix (members) (index_pre))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1048576) ” 
  &&  “ (0 <= (cm_rep_members_size (members))) ”
  &&  (cm_member_list_rep node_pre members )
) \/
(
forall (index_pre: Z) (node_pre: Z) (members: (@list cm_slot_d)) (PreH1 : (node_pre = 0)) (PreH2 : (0 <= index_pre)) (PreH3 : (cm_rep_members_safe members )) ,
  TT && emp 
|--
  “ (0 <= (cm_rep_members_size (members))) ” 
  &&  “ (0 = (cm_rep_member_prefix (members) (index_pre))) ”
  &&  emp
).

Definition cmc_members_prefix_return_wit_1_split_goal_1 := 
forall (index_pre: Z) (node_pre: Z) (members: (@list cm_slot_d)) (PreH1 : (node_pre = 0)) (PreH2 : (0 <= index_pre)) (PreH3 : (cm_rep_members_safe members )) ,
  (0 <= (cm_rep_members_size (members)))
.

Definition cmc_members_prefix_return_wit_1_split_goal_2 := 
forall (index_pre: Z) (node_pre: Z) (members: (@list cm_slot_d)) (PreH1 : (node_pre = 0)) (PreH2 : (0 <= index_pre)) (PreH3 : (cm_rep_members_safe members )) ,
  (0 = (cm_rep_member_prefix (members) (index_pre)))
.

Definition cmc_members_prefix_return_wit_2 := 
(
forall (index_pre: Z) (node_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (PreH1 : (index_pre = 0)) (PreH2 : (node_pre <> 0)) (PreH3 : (members = (cons (head) (tail)))) (PreH4 : (0 <= index_pre)) (PreH5 : (cm_rep_members_safe members )) (PreH6 : (cm_rep_members_safe tail )) ,
  ((&((node_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((node_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((node_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_member_list_rep nextp tail )
|--
  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_members_safe members ) ” 
  &&  “ (0 = (cm_rep_member_prefix (members) (index_pre))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1048576) ” 
  &&  “ (0 <= (cm_rep_members_size (members))) ”
  &&  (cm_member_list_rep node_pre members )
) \/
(
forall (index_pre: Z) (node_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (index_pre = 0)) (PreH6 : (node_pre <> 0)) (PreH7 : (members = (cons (head) (tail)))) (PreH8 : (0 <= index_pre)) (PreH9 : (cm_rep_members_safe members )) (PreH10 : (cm_rep_members_safe tail )) ,
  ((&((node_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((node_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((node_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_member_list_rep nextp tail )
|--
  “ (0 <= (cm_rep_members_size (members))) ” 
  &&  “ (0 = (cm_rep_member_prefix (members) (0))) ”
  &&  (cm_member_list_rep node_pre members )
).

Definition cmc_members_prefix_return_wit_2_split_goal_1 := 
forall (index_pre: Z) (node_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (index_pre = 0)) (PreH6 : (node_pre <> 0)) (PreH7 : (members = (cons (head) (tail)))) (PreH8 : (0 <= index_pre)) (PreH9 : (cm_rep_members_safe members )) (PreH10 : (cm_rep_members_safe tail )) ,
  ((&((node_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((node_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((node_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_member_list_rep nextp tail )
|--
  “ (0 <= (cm_rep_members_size (members))) ”
.

Definition cmc_members_prefix_return_wit_2_split_goal_2 := 
forall (index_pre: Z) (node_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (index_pre = 0)) (PreH6 : (node_pre <> 0)) (PreH7 : (members = (cons (head) (tail)))) (PreH8 : (0 <= index_pre)) (PreH9 : (cm_rep_members_safe members )) (PreH10 : (cm_rep_members_safe tail )) ,
  ((&((node_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((node_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((node_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_member_list_rep nextp tail )
|--
  “ (0 = (cm_rep_member_prefix (members) (0))) ”
.

Definition cmc_members_prefix_return_wit_2_split_goal_spatial := 
forall (index_pre: Z) (node_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (index_pre = 0)) (PreH6 : (node_pre <> 0)) (PreH7 : (members = (cons (head) (tail)))) (PreH8 : (0 <= index_pre)) (PreH9 : (cm_rep_members_safe members )) (PreH10 : (cm_rep_members_safe tail )) ,
  ((&((node_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((node_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((node_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_member_list_rep nextp tail )
|--
  (cm_member_list_rep node_pre members )
.

Definition cmc_members_prefix_return_wit_3 := 
(
forall (index_pre: Z) (node_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (index_pre - 1 ))) (PreH2 : (cm_rep_members_safe tail )) (PreH3 : (retval_2 = (cm_rep_member_prefix (tail) ((index_pre - 1 ))))) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1048576)) (PreH6 : (retval_2 <= (cm_rep_members_size (tail)))) (PreH7 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH8 : (index_pre <> 0)) (PreH9 : (node_pre <> 0)) (PreH10 : (members = (cons (head) (tail)))) (PreH11 : (0 <= index_pre)) (PreH12 : (cm_rep_members_safe members )) (PreH13 : (cm_rep_members_safe tail )) ,
  (cm_member_list_rep nextp tail )
  **  ((&((node_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((node_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((node_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_members_safe members ) ” 
  &&  “ ((retval + retval_2 ) = (cm_rep_member_prefix (members) (index_pre))) ” 
  &&  “ (0 <= (retval + retval_2 )) ” 
  &&  “ ((retval + retval_2 ) <= 1048576) ” 
  &&  “ ((retval + retval_2 ) <= (cm_rep_members_size (members))) ”
  &&  (cm_member_list_rep node_pre members )
) \/
(
forall (index_pre: Z) (node_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (0 <= (index_pre - 1 ))) (PreH6 : (cm_rep_members_safe tail )) (PreH7 : (retval_2 = (cm_rep_member_prefix (tail) ((index_pre - 1 ))))) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1048576)) (PreH10 : (retval_2 <= (cm_rep_members_size (tail)))) (PreH11 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH12 : (index_pre <> 0)) (PreH13 : (node_pre <> 0)) (PreH14 : (members = (cons (head) (tail)))) (PreH15 : (0 <= index_pre)) (PreH16 : (cm_rep_members_safe members )) (PreH17 : (cm_rep_members_safe tail )) ,
  (cm_member_list_rep nextp tail )
  **  ((&((node_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((node_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((node_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ ((retval + retval_2 ) <= (cm_rep_members_size (members))) ” 
  &&  “ ((retval + retval_2 ) <= 1048576) ” 
  &&  “ (0 <= (retval + retval_2 )) ” 
  &&  “ ((retval + retval_2 ) = (cm_rep_member_prefix (members) (index_pre))) ”
  &&  (cm_member_list_rep node_pre members )
).

Definition cmc_members_prefix_return_wit_3_split_goal_1 := 
forall (index_pre: Z) (node_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (0 <= (index_pre - 1 ))) (PreH6 : (cm_rep_members_safe tail )) (PreH7 : (retval_2 = (cm_rep_member_prefix (tail) ((index_pre - 1 ))))) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1048576)) (PreH10 : (retval_2 <= (cm_rep_members_size (tail)))) (PreH11 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH12 : (index_pre <> 0)) (PreH13 : (node_pre <> 0)) (PreH14 : (members = (cons (head) (tail)))) (PreH15 : (0 <= index_pre)) (PreH16 : (cm_rep_members_safe members )) (PreH17 : (cm_rep_members_safe tail )) ,
  (cm_member_list_rep nextp tail )
  **  ((&((node_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((node_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((node_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ ((retval + retval_2 ) <= (cm_rep_members_size (members))) ”
.

Definition cmc_members_prefix_return_wit_3_split_goal_2 := 
forall (index_pre: Z) (node_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (0 <= (index_pre - 1 ))) (PreH6 : (cm_rep_members_safe tail )) (PreH7 : (retval_2 = (cm_rep_member_prefix (tail) ((index_pre - 1 ))))) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1048576)) (PreH10 : (retval_2 <= (cm_rep_members_size (tail)))) (PreH11 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH12 : (index_pre <> 0)) (PreH13 : (node_pre <> 0)) (PreH14 : (members = (cons (head) (tail)))) (PreH15 : (0 <= index_pre)) (PreH16 : (cm_rep_members_safe members )) (PreH17 : (cm_rep_members_safe tail )) ,
  (cm_member_list_rep nextp tail )
  **  ((&((node_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((node_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((node_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ ((retval + retval_2 ) <= 1048576) ”
.

Definition cmc_members_prefix_return_wit_3_split_goal_3 := 
forall (index_pre: Z) (node_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (0 <= (index_pre - 1 ))) (PreH6 : (cm_rep_members_safe tail )) (PreH7 : (retval_2 = (cm_rep_member_prefix (tail) ((index_pre - 1 ))))) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1048576)) (PreH10 : (retval_2 <= (cm_rep_members_size (tail)))) (PreH11 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH12 : (index_pre <> 0)) (PreH13 : (node_pre <> 0)) (PreH14 : (members = (cons (head) (tail)))) (PreH15 : (0 <= index_pre)) (PreH16 : (cm_rep_members_safe members )) (PreH17 : (cm_rep_members_safe tail )) ,
  (cm_member_list_rep nextp tail )
  **  ((&((node_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((node_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((node_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (0 <= (retval + retval_2 )) ”
.

Definition cmc_members_prefix_return_wit_3_split_goal_4 := 
forall (index_pre: Z) (node_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (0 <= (index_pre - 1 ))) (PreH6 : (cm_rep_members_safe tail )) (PreH7 : (retval_2 = (cm_rep_member_prefix (tail) ((index_pre - 1 ))))) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1048576)) (PreH10 : (retval_2 <= (cm_rep_members_size (tail)))) (PreH11 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH12 : (index_pre <> 0)) (PreH13 : (node_pre <> 0)) (PreH14 : (members = (cons (head) (tail)))) (PreH15 : (0 <= index_pre)) (PreH16 : (cm_rep_members_safe members )) (PreH17 : (cm_rep_members_safe tail )) ,
  (cm_member_list_rep nextp tail )
  **  ((&((node_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((node_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((node_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ ((retval + retval_2 ) = (cm_rep_member_prefix (members) (index_pre))) ”
.

Definition cmc_members_prefix_return_wit_3_split_goal_spatial := 
forall (index_pre: Z) (node_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : ((cm_slot_count (head)) <= INT_MAX)) (PreH2 : ((cm_type_encode ((cm_slot_ty (head)))) <= INT_MAX)) (PreH3 : ((cm_slot_count (head)) >= INT_MIN)) (PreH4 : ((cm_type_encode ((cm_slot_ty (head)))) >= INT_MIN)) (PreH5 : (0 <= (index_pre - 1 ))) (PreH6 : (cm_rep_members_safe tail )) (PreH7 : (retval_2 = (cm_rep_member_prefix (tail) ((index_pre - 1 ))))) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1048576)) (PreH10 : (retval_2 <= (cm_rep_members_size (tail)))) (PreH11 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH12 : (index_pre <> 0)) (PreH13 : (node_pre <> 0)) (PreH14 : (members = (cons (head) (tail)))) (PreH15 : (0 <= index_pre)) (PreH16 : (cm_rep_members_safe members )) (PreH17 : (cm_rep_members_safe tail )) ,
  (cm_member_list_rep nextp tail )
  **  ((&((node_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((node_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((node_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
|--
  (cm_member_list_rep node_pre members )
.

Definition cmc_members_prefix_partial_solve_wit_1 := 
forall (index_pre: Z) (node_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (PreH1 : (index_pre <> 0)) (PreH2 : (node_pre <> 0)) (PreH3 : (members = (cons (head) (tail)))) (PreH4 : (0 <= index_pre)) (PreH5 : (cm_rep_members_safe members )) (PreH6 : (cm_rep_members_safe tail )) ,
  ((&((node_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((node_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((node_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_member_list_rep nextp tail )
|--
  “ (index_pre <> 0) ” 
  &&  “ (node_pre <> 0) ” 
  &&  “ (members = (cons (head) (tail))) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_members_safe members ) ” 
  &&  “ (cm_rep_members_safe tail ) ”
  &&  ((&((node_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((node_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((node_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_member_list_rep nextp tail )
.

Definition cmc_members_prefix_partial_solve_wit_2_pure := 
forall (index_pre: Z) (node_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (PreH1 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH2 : (index_pre <> 0)) (PreH3 : (node_pre <> 0)) (PreH4 : (members = (cons (head) (tail)))) (PreH5 : (0 <= index_pre)) (PreH6 : (cm_rep_members_safe members )) (PreH7 : (cm_rep_members_safe tail )) ,
  ((( &( "rest_size" ) )) # Int64  |->_)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> retval)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((node_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((node_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((node_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_member_list_rep nextp tail )
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ (0 <= (index_pre - 1 )) ” 
  &&  “ (cm_rep_members_safe tail ) ”
.

Definition cmc_members_prefix_partial_solve_wit_2_aux := 
forall (index_pre: Z) (node_pre: Z) (members: (@list cm_slot_d)) (head: cm_slot_d) (tail: (@list cm_slot_d)) (nextp: Z) (retval: Z) (PreH1 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head)))))) (PreH2 : (index_pre <> 0)) (PreH3 : (node_pre <> 0)) (PreH4 : (members = (cons (head) (tail)))) (PreH5 : (0 <= index_pre)) (PreH6 : (cm_rep_members_safe members )) (PreH7 : (cm_rep_members_safe tail )) ,
  ((&((node_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((node_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((node_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_member_list_rep nextp tail )
|--
  “ (0 <= (index_pre - 1 )) ” 
  &&  “ (cm_rep_members_safe tail ) ” 
  &&  “ (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_slot_ty (head))))) ((cm_slot_count (head))))) ” 
  &&  “ (index_pre <> 0) ” 
  &&  “ (node_pre <> 0) ” 
  &&  “ (members = (cons (head) (tail))) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_members_safe members ) ” 
  &&  “ (cm_rep_members_safe tail ) ”
  &&  (cm_member_list_rep nextp tail )
  **  ((&((node_pre)  # "cm_member" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_slot_ty (head)))))
  **  ((&((node_pre)  # "cm_member" ->ₛ "count")) # Int  |-> (cm_slot_count (head)))
  **  ((&((node_pre)  # "cm_member" ->ₛ "next")) # Ptr  |-> nextp)
.

Definition cmc_members_prefix_partial_solve_wit_2 := cmc_members_prefix_partial_solve_wit_2_pure -> cmc_members_prefix_partial_solve_wit_2_aux.

(*----- Function cmc_member_offset_at -----*)

Definition cmc_member_offset_at_safety_wit_1 := 
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (0 <= sid_pre)) (PreH2 : (0 <= index_pre)) (PreH3 : (cm_rep_structs_safe structs )) ,
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "sid" ) )) # Int  |-> sid_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  (cm_struct_list_rep item_pre structs )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_member_offset_at_safety_wit_2 := 
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (item_pre = 0)) (PreH2 : (0 <= sid_pre)) (PreH3 : (0 <= index_pre)) (PreH4 : (cm_rep_structs_safe structs )) ,
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "sid" ) )) # Int  |-> sid_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  (cm_struct_list_rep item_pre structs )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_member_offset_at_safety_wit_3 := 
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (PreH1 : (item_pre <> 0)) (PreH2 : (structs = (cons (head) (tail)))) (PreH3 : (0 <= sid_pre)) (PreH4 : (0 <= index_pre)) (PreH5 : (cm_rep_structs_safe structs )) (PreH6 : (cm_rep_structs_safe tail )) (PreH7 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "sid" ) )) # Int  |-> sid_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_member_offset_at_safety_wit_4 := 
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (PreH1 : (sid_pre <> 0)) (PreH2 : (item_pre <> 0)) (PreH3 : (structs = (cons (head) (tail)))) (PreH4 : (0 <= sid_pre)) (PreH5 : (0 <= index_pre)) (PreH6 : (cm_rep_structs_safe structs )) (PreH7 : (cm_rep_structs_safe tail )) (PreH8 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "sid" ) )) # Int  |-> sid_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ ((sid_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sid_pre - 1 )) ”
.

Definition cmc_member_offset_at_safety_wit_5 := 
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (PreH1 : (sid_pre <> 0)) (PreH2 : (item_pre <> 0)) (PreH3 : (structs = (cons (head) (tail)))) (PreH4 : (0 <= sid_pre)) (PreH5 : (0 <= index_pre)) (PreH6 : (cm_rep_structs_safe structs )) (PreH7 : (cm_rep_structs_safe tail )) (PreH8 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "sid" ) )) # Int  |-> sid_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmc_member_offset_at_entail_wit_1 := 
(
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (item_pre <> 0)) (PreH2 : (0 <= sid_pre)) (PreH3 : (0 <= index_pre)) (PreH4 : (cm_rep_structs_safe structs )) ,
  (cm_struct_list_rep item_pre structs )
|--
  EX (nextp: Z)  (memberp: Z)  (head: cm_struct_d)  (tail: (@list cm_struct_d)) ,
  “ (item_pre <> 0) ” 
  &&  “ (structs = (cons (head) (tail))) ” 
  &&  “ (0 <= sid_pre) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_structs_safe structs ) ” 
  &&  “ (cm_rep_structs_safe tail ) ” 
  &&  “ (cm_rep_members_safe (cm_struct_members (head)) ) ”
  &&  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
) \/
(
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (item_pre <> 0)) (PreH2 : (0 <= sid_pre)) (PreH3 : (0 <= index_pre)) (PreH4 : (cm_rep_structs_safe structs )) ,
  (cm_struct_list_rep item_pre structs )
|--
  EX (nextp: Z)  (memberp: Z)  (head: cm_struct_d)  (tail: (@list cm_struct_d)) ,
  “ (item_pre <> 0) ” 
  &&  “ (structs = (cons (head) (tail))) ” 
  &&  “ (0 <= sid_pre) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_structs_safe structs ) ” 
  &&  “ (cm_rep_structs_safe tail ) ” 
  &&  “ (cm_rep_members_safe (cm_struct_members (head)) ) ”
  &&  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
).

Definition cmc_member_offset_at_return_wit_1 := 
(
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (item_pre = 0)) (PreH2 : (0 <= sid_pre)) (PreH3 : (0 <= index_pre)) (PreH4 : (cm_rep_structs_safe structs )) ,
  (cm_struct_list_rep item_pre structs )
|--
  “ (0 <= sid_pre) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_structs_safe structs ) ” 
  &&  “ (0 = (cm_rep_struct_member_prefix (structs) (sid_pre) (index_pre))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1048576) ”
  &&  (cm_struct_list_rep item_pre structs )
) \/
(
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (item_pre = 0)) (PreH2 : (0 <= sid_pre)) (PreH3 : (0 <= index_pre)) (PreH4 : (cm_rep_structs_safe structs )) ,
  TT && emp 
|--
  “ (0 = (cm_rep_struct_member_prefix (structs) (sid_pre) (index_pre))) ”
  &&  emp
).

Definition cmc_member_offset_at_return_wit_1_split_goal_1 := 
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (item_pre = 0)) (PreH2 : (0 <= sid_pre)) (PreH3 : (0 <= index_pre)) (PreH4 : (cm_rep_structs_safe structs )) ,
  (0 = (cm_rep_struct_member_prefix (structs) (sid_pre) (index_pre)))
.

Definition cmc_member_offset_at_return_wit_2 := 
(
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (retval: Z) (PreH1 : (0 <= index_pre)) (PreH2 : (cm_rep_members_safe (cm_struct_members (head)) )) (PreH3 : (retval = (cm_rep_member_prefix ((cm_struct_members (head))) (index_pre)))) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1048576)) (PreH6 : (retval <= (cm_rep_members_size ((cm_struct_members (head)))))) (PreH7 : (sid_pre = 0)) (PreH8 : (item_pre <> 0)) (PreH9 : (structs = (cons (head) (tail)))) (PreH10 : (0 <= sid_pre)) (PreH11 : (0 <= index_pre)) (PreH12 : (cm_rep_structs_safe structs )) (PreH13 : (cm_rep_structs_safe tail )) (PreH14 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
|--
  “ (0 <= sid_pre) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_structs_safe structs ) ” 
  &&  “ (retval = (cm_rep_struct_member_prefix (structs) (sid_pre) (index_pre))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1048576) ”
  &&  (cm_struct_list_rep item_pre structs )
) \/
(
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (retval: Z) (PreH1 : (0 <= index_pre)) (PreH2 : (cm_rep_members_safe (cm_struct_members (head)) )) (PreH3 : (retval = (cm_rep_member_prefix ((cm_struct_members (head))) (index_pre)))) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1048576)) (PreH6 : (retval <= (cm_rep_members_size ((cm_struct_members (head)))))) (PreH7 : (sid_pre = 0)) (PreH8 : (item_pre <> 0)) (PreH9 : (structs = (cons (head) (tail)))) (PreH10 : (0 <= sid_pre)) (PreH11 : (0 <= index_pre)) (PreH12 : (cm_rep_structs_safe structs )) (PreH13 : (cm_rep_structs_safe tail )) (PreH14 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
|--
  “ (retval = (cm_rep_struct_member_prefix (structs) (0) (index_pre))) ”
  &&  (cm_struct_list_rep item_pre structs )
).

Definition cmc_member_offset_at_return_wit_2_split_goal_1 := 
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (retval: Z) (PreH1 : (0 <= index_pre)) (PreH2 : (cm_rep_members_safe (cm_struct_members (head)) )) (PreH3 : (retval = (cm_rep_member_prefix ((cm_struct_members (head))) (index_pre)))) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1048576)) (PreH6 : (retval <= (cm_rep_members_size ((cm_struct_members (head)))))) (PreH7 : (sid_pre = 0)) (PreH8 : (item_pre <> 0)) (PreH9 : (structs = (cons (head) (tail)))) (PreH10 : (0 <= sid_pre)) (PreH11 : (0 <= index_pre)) (PreH12 : (cm_rep_structs_safe structs )) (PreH13 : (cm_rep_structs_safe tail )) (PreH14 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
|--
  “ (retval = (cm_rep_struct_member_prefix (structs) (0) (index_pre))) ”
.

Definition cmc_member_offset_at_return_wit_2_split_goal_spatial := 
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (retval: Z) (PreH1 : (0 <= index_pre)) (PreH2 : (cm_rep_members_safe (cm_struct_members (head)) )) (PreH3 : (retval = (cm_rep_member_prefix ((cm_struct_members (head))) (index_pre)))) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1048576)) (PreH6 : (retval <= (cm_rep_members_size ((cm_struct_members (head)))))) (PreH7 : (sid_pre = 0)) (PreH8 : (item_pre <> 0)) (PreH9 : (structs = (cons (head) (tail)))) (PreH10 : (0 <= sid_pre)) (PreH11 : (0 <= index_pre)) (PreH12 : (cm_rep_structs_safe structs )) (PreH13 : (cm_rep_structs_safe tail )) (PreH14 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
|--
  (cm_struct_list_rep item_pre structs )
.

Definition cmc_member_offset_at_return_wit_3 := 
(
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (retval: Z) (PreH1 : (0 <= (sid_pre - 1 ))) (PreH2 : (0 <= index_pre)) (PreH3 : (cm_rep_structs_safe tail )) (PreH4 : (retval = (cm_rep_struct_member_prefix (tail) ((sid_pre - 1 )) (index_pre)))) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1048576)) (PreH7 : (sid_pre <> 0)) (PreH8 : (item_pre <> 0)) (PreH9 : (structs = (cons (head) (tail)))) (PreH10 : (0 <= sid_pre)) (PreH11 : (0 <= index_pre)) (PreH12 : (cm_rep_structs_safe structs )) (PreH13 : (cm_rep_structs_safe tail )) (PreH14 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  (cm_struct_list_rep nextp tail )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (0 <= sid_pre) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_structs_safe structs ) ” 
  &&  “ (retval = (cm_rep_struct_member_prefix (structs) (sid_pre) (index_pre))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1048576) ”
  &&  (cm_struct_list_rep item_pre structs )
) \/
(
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (retval: Z) (PreH1 : (0 <= (sid_pre - 1 ))) (PreH2 : (0 <= index_pre)) (PreH3 : (cm_rep_structs_safe tail )) (PreH4 : (retval = (cm_rep_struct_member_prefix (tail) ((sid_pre - 1 )) (index_pre)))) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1048576)) (PreH7 : (sid_pre <> 0)) (PreH8 : (item_pre <> 0)) (PreH9 : (structs = (cons (head) (tail)))) (PreH10 : (0 <= sid_pre)) (PreH11 : (0 <= index_pre)) (PreH12 : (cm_rep_structs_safe structs )) (PreH13 : (cm_rep_structs_safe tail )) (PreH14 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  (cm_struct_list_rep nextp tail )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (retval = (cm_rep_struct_member_prefix (structs) (sid_pre) (index_pre))) ”
  &&  (cm_struct_list_rep item_pre structs )
).

Definition cmc_member_offset_at_return_wit_3_split_goal_1 := 
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (retval: Z) (PreH1 : (0 <= (sid_pre - 1 ))) (PreH2 : (0 <= index_pre)) (PreH3 : (cm_rep_structs_safe tail )) (PreH4 : (retval = (cm_rep_struct_member_prefix (tail) ((sid_pre - 1 )) (index_pre)))) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1048576)) (PreH7 : (sid_pre <> 0)) (PreH8 : (item_pre <> 0)) (PreH9 : (structs = (cons (head) (tail)))) (PreH10 : (0 <= sid_pre)) (PreH11 : (0 <= index_pre)) (PreH12 : (cm_rep_structs_safe structs )) (PreH13 : (cm_rep_structs_safe tail )) (PreH14 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  (cm_struct_list_rep nextp tail )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (retval = (cm_rep_struct_member_prefix (structs) (sid_pre) (index_pre))) ”
.

Definition cmc_member_offset_at_return_wit_3_split_goal_spatial := 
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (retval: Z) (PreH1 : (0 <= (sid_pre - 1 ))) (PreH2 : (0 <= index_pre)) (PreH3 : (cm_rep_structs_safe tail )) (PreH4 : (retval = (cm_rep_struct_member_prefix (tail) ((sid_pre - 1 )) (index_pre)))) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1048576)) (PreH7 : (sid_pre <> 0)) (PreH8 : (item_pre <> 0)) (PreH9 : (structs = (cons (head) (tail)))) (PreH10 : (0 <= sid_pre)) (PreH11 : (0 <= index_pre)) (PreH12 : (cm_rep_structs_safe structs )) (PreH13 : (cm_rep_structs_safe tail )) (PreH14 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  (cm_struct_list_rep nextp tail )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
|--
  (cm_struct_list_rep item_pre structs )
.

Definition cmc_member_offset_at_partial_solve_wit_1_pure := 
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (PreH1 : (sid_pre = 0)) (PreH2 : (item_pre <> 0)) (PreH3 : (structs = (cons (head) (tail)))) (PreH4 : (0 <= sid_pre)) (PreH5 : (0 <= index_pre)) (PreH6 : (cm_rep_structs_safe structs )) (PreH7 : (cm_rep_structs_safe tail )) (PreH8 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "sid" ) )) # Int  |-> sid_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_members_safe (cm_struct_members (head)) ) ”
.

Definition cmc_member_offset_at_partial_solve_wit_1_aux := 
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (PreH1 : (sid_pre = 0)) (PreH2 : (item_pre <> 0)) (PreH3 : (structs = (cons (head) (tail)))) (PreH4 : (0 <= sid_pre)) (PreH5 : (0 <= index_pre)) (PreH6 : (cm_rep_structs_safe structs )) (PreH7 : (cm_rep_structs_safe tail )) (PreH8 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
|--
  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_members_safe (cm_struct_members (head)) ) ” 
  &&  “ (sid_pre = 0) ” 
  &&  “ (item_pre <> 0) ” 
  &&  “ (structs = (cons (head) (tail))) ” 
  &&  “ (0 <= sid_pre) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_structs_safe structs ) ” 
  &&  “ (cm_rep_structs_safe tail ) ” 
  &&  “ (cm_rep_members_safe (cm_struct_members (head)) ) ”
  &&  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
.

Definition cmc_member_offset_at_partial_solve_wit_1 := cmc_member_offset_at_partial_solve_wit_1_pure -> cmc_member_offset_at_partial_solve_wit_1_aux.

Definition cmc_member_offset_at_partial_solve_wit_2_pure := 
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (PreH1 : (sid_pre <> 0)) (PreH2 : (item_pre <> 0)) (PreH3 : (structs = (cons (head) (tail)))) (PreH4 : (0 <= sid_pre)) (PreH5 : (0 <= index_pre)) (PreH6 : (cm_rep_structs_safe structs )) (PreH7 : (cm_rep_structs_safe tail )) (PreH8 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "sid" ) )) # Int  |-> sid_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ (0 <= (sid_pre - 1 )) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_structs_safe tail ) ”
.

Definition cmc_member_offset_at_partial_solve_wit_2_aux := 
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (PreH1 : (sid_pre <> 0)) (PreH2 : (item_pre <> 0)) (PreH3 : (structs = (cons (head) (tail)))) (PreH4 : (0 <= sid_pre)) (PreH5 : (0 <= index_pre)) (PreH6 : (cm_rep_structs_safe structs )) (PreH7 : (cm_rep_structs_safe tail )) (PreH8 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
|--
  “ (0 <= (sid_pre - 1 )) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_structs_safe tail ) ” 
  &&  “ (sid_pre <> 0) ” 
  &&  “ (item_pre <> 0) ” 
  &&  “ (structs = (cons (head) (tail))) ” 
  &&  “ (0 <= sid_pre) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_structs_safe structs ) ” 
  &&  “ (cm_rep_structs_safe tail ) ” 
  &&  “ (cm_rep_members_safe (cm_struct_members (head)) ) ”
  &&  (cm_struct_list_rep nextp tail )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
.

Definition cmc_member_offset_at_partial_solve_wit_2 := cmc_member_offset_at_partial_solve_wit_2_pure -> cmc_member_offset_at_partial_solve_wit_2_aux.

(*----- Function cmc_struct_member_array_at -----*)

Definition cmc_struct_member_array_at_safety_wit_1 := 
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (0 <= sid_pre)) (PreH2 : (0 <= index_pre)) (PreH3 : (cm_rep_structs_safe structs )) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "sid" ) )) # Int  |-> sid_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  (cm_struct_list_rep item_pre structs )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_struct_member_array_at_safety_wit_2 := 
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (item_pre = 0)) (PreH2 : (0 <= sid_pre)) (PreH3 : (0 <= index_pre)) (PreH4 : (cm_rep_structs_safe structs )) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "sid" ) )) # Int  |-> sid_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  (cm_struct_list_rep item_pre structs )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_struct_member_array_at_safety_wit_3 := 
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (PreH1 : (item_pre <> 0)) (PreH2 : (structs = (cons (head) (tail)))) (PreH3 : (0 <= sid_pre)) (PreH4 : (0 <= index_pre)) (PreH5 : (cm_rep_structs_safe structs )) (PreH6 : (cm_rep_structs_safe tail )) (PreH7 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "sid" ) )) # Int  |-> sid_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
  **  ((( &( "result" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_struct_member_array_at_safety_wit_4 := 
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (PreH1 : (sid_pre <> 0)) (PreH2 : (item_pre <> 0)) (PreH3 : (structs = (cons (head) (tail)))) (PreH4 : (0 <= sid_pre)) (PreH5 : (0 <= index_pre)) (PreH6 : (cm_rep_structs_safe structs )) (PreH7 : (cm_rep_structs_safe tail )) (PreH8 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "sid" ) )) # Int  |-> sid_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
  **  ((( &( "result" ) )) # Int  |->_)
|--
  “ ((sid_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sid_pre - 1 )) ”
.

Definition cmc_struct_member_array_at_safety_wit_5 := 
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (PreH1 : (sid_pre <> 0)) (PreH2 : (item_pre <> 0)) (PreH3 : (structs = (cons (head) (tail)))) (PreH4 : (0 <= sid_pre)) (PreH5 : (0 <= index_pre)) (PreH6 : (cm_rep_structs_safe structs )) (PreH7 : (cm_rep_structs_safe tail )) (PreH8 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "sid" ) )) # Int  |-> sid_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
  **  ((( &( "result" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmc_struct_member_array_at_entail_wit_1 := 
(
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (item_pre <> 0)) (PreH2 : (0 <= sid_pre)) (PreH3 : (0 <= index_pre)) (PreH4 : (cm_rep_structs_safe structs )) ,
  (cm_struct_list_rep item_pre structs )
|--
  EX (nextp: Z)  (memberp: Z)  (head: cm_struct_d)  (tail: (@list cm_struct_d)) ,
  “ (item_pre <> 0) ” 
  &&  “ (structs = (cons (head) (tail))) ” 
  &&  “ (0 <= sid_pre) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_structs_safe structs ) ” 
  &&  “ (cm_rep_structs_safe tail ) ” 
  &&  “ (cm_rep_members_safe (cm_struct_members (head)) ) ”
  &&  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
) \/
(
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (item_pre <> 0)) (PreH2 : (0 <= sid_pre)) (PreH3 : (0 <= index_pre)) (PreH4 : (cm_rep_structs_safe structs )) ,
  (cm_struct_list_rep item_pre structs )
|--
  EX (nextp: Z)  (memberp: Z)  (head: cm_struct_d)  (tail: (@list cm_struct_d)) ,
  “ (item_pre <> 0) ” 
  &&  “ (structs = (cons (head) (tail))) ” 
  &&  “ (0 <= sid_pre) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_structs_safe structs ) ” 
  &&  “ (cm_rep_structs_safe tail ) ” 
  &&  “ (cm_rep_members_safe (cm_struct_members (head)) ) ”
  &&  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
).

Definition cmc_struct_member_array_at_return_wit_1 := 
(
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (item_pre = 0)) (PreH2 : (0 <= sid_pre)) (PreH3 : (0 <= index_pre)) (PreH4 : (cm_rep_structs_safe structs )) ,
  (cm_struct_list_rep item_pre structs )
|--
  “ (0 <= sid_pre) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_structs_safe structs ) ” 
  &&  “ (0 = (cm_rep_struct_member_array (structs) (sid_pre) (index_pre))) ”
  &&  (cm_struct_list_rep item_pre structs )
) \/
(
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (item_pre = 0)) (PreH2 : (0 <= sid_pre)) (PreH3 : (0 <= index_pre)) (PreH4 : (cm_rep_structs_safe structs )) ,
  TT && emp 
|--
  “ (0 = (cm_rep_struct_member_array (structs) (sid_pre) (index_pre))) ”
  &&  emp
).

Definition cmc_struct_member_array_at_return_wit_1_split_goal_1 := 
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (PreH1 : (item_pre = 0)) (PreH2 : (0 <= sid_pre)) (PreH3 : (0 <= index_pre)) (PreH4 : (cm_rep_structs_safe structs )) ,
  (0 = (cm_rep_struct_member_array (structs) (sid_pre) (index_pre)))
.

Definition cmc_struct_member_array_at_return_wit_2 := 
(
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (retval: Z) (PreH1 : (0 <= index_pre)) (PreH2 : (retval = (cm_rep_member_array ((cm_struct_members (head))) (index_pre)))) (PreH3 : (sid_pre = 0)) (PreH4 : (item_pre <> 0)) (PreH5 : (structs = (cons (head) (tail)))) (PreH6 : (0 <= sid_pre)) (PreH7 : (0 <= index_pre)) (PreH8 : (cm_rep_structs_safe structs )) (PreH9 : (cm_rep_structs_safe tail )) (PreH10 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
|--
  “ (0 <= sid_pre) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_structs_safe structs ) ” 
  &&  “ (retval = (cm_rep_struct_member_array (structs) (sid_pre) (index_pre))) ”
  &&  (cm_struct_list_rep item_pre structs )
) \/
(
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (retval: Z) (PreH1 : (0 <= index_pre)) (PreH2 : (retval = (cm_rep_member_array ((cm_struct_members (head))) (index_pre)))) (PreH3 : (sid_pre = 0)) (PreH4 : (item_pre <> 0)) (PreH5 : (structs = (cons (head) (tail)))) (PreH6 : (0 <= sid_pre)) (PreH7 : (0 <= index_pre)) (PreH8 : (cm_rep_structs_safe structs )) (PreH9 : (cm_rep_structs_safe tail )) (PreH10 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
|--
  “ (retval = (cm_rep_struct_member_array (structs) (0) (index_pre))) ”
  &&  (cm_struct_list_rep item_pre structs )
).

Definition cmc_struct_member_array_at_return_wit_2_split_goal_1 := 
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (retval: Z) (PreH1 : (0 <= index_pre)) (PreH2 : (retval = (cm_rep_member_array ((cm_struct_members (head))) (index_pre)))) (PreH3 : (sid_pre = 0)) (PreH4 : (item_pre <> 0)) (PreH5 : (structs = (cons (head) (tail)))) (PreH6 : (0 <= sid_pre)) (PreH7 : (0 <= index_pre)) (PreH8 : (cm_rep_structs_safe structs )) (PreH9 : (cm_rep_structs_safe tail )) (PreH10 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
|--
  “ (retval = (cm_rep_struct_member_array (structs) (0) (index_pre))) ”
.

Definition cmc_struct_member_array_at_return_wit_2_split_goal_spatial := 
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (retval: Z) (PreH1 : (0 <= index_pre)) (PreH2 : (retval = (cm_rep_member_array ((cm_struct_members (head))) (index_pre)))) (PreH3 : (sid_pre = 0)) (PreH4 : (item_pre <> 0)) (PreH5 : (structs = (cons (head) (tail)))) (PreH6 : (0 <= sid_pre)) (PreH7 : (0 <= index_pre)) (PreH8 : (cm_rep_structs_safe structs )) (PreH9 : (cm_rep_structs_safe tail )) (PreH10 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
|--
  (cm_struct_list_rep item_pre structs )
.

Definition cmc_struct_member_array_at_return_wit_3 := 
(
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (retval: Z) (PreH1 : (0 <= (sid_pre - 1 ))) (PreH2 : (0 <= index_pre)) (PreH3 : (cm_rep_structs_safe tail )) (PreH4 : (retval = (cm_rep_struct_member_array (tail) ((sid_pre - 1 )) (index_pre)))) (PreH5 : (sid_pre <> 0)) (PreH6 : (item_pre <> 0)) (PreH7 : (structs = (cons (head) (tail)))) (PreH8 : (0 <= sid_pre)) (PreH9 : (0 <= index_pre)) (PreH10 : (cm_rep_structs_safe structs )) (PreH11 : (cm_rep_structs_safe tail )) (PreH12 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  (cm_struct_list_rep nextp tail )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (0 <= sid_pre) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_structs_safe structs ) ” 
  &&  “ (retval = (cm_rep_struct_member_array (structs) (sid_pre) (index_pre))) ”
  &&  (cm_struct_list_rep item_pre structs )
) \/
(
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (retval: Z) (PreH1 : (0 <= (sid_pre - 1 ))) (PreH2 : (0 <= index_pre)) (PreH3 : (cm_rep_structs_safe tail )) (PreH4 : (retval = (cm_rep_struct_member_array (tail) ((sid_pre - 1 )) (index_pre)))) (PreH5 : (sid_pre <> 0)) (PreH6 : (item_pre <> 0)) (PreH7 : (structs = (cons (head) (tail)))) (PreH8 : (0 <= sid_pre)) (PreH9 : (0 <= index_pre)) (PreH10 : (cm_rep_structs_safe structs )) (PreH11 : (cm_rep_structs_safe tail )) (PreH12 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  (cm_struct_list_rep nextp tail )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (retval = (cm_rep_struct_member_array (structs) (sid_pre) (index_pre))) ”
  &&  (cm_struct_list_rep item_pre structs )
).

Definition cmc_struct_member_array_at_return_wit_3_split_goal_1 := 
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (retval: Z) (PreH1 : (0 <= (sid_pre - 1 ))) (PreH2 : (0 <= index_pre)) (PreH3 : (cm_rep_structs_safe tail )) (PreH4 : (retval = (cm_rep_struct_member_array (tail) ((sid_pre - 1 )) (index_pre)))) (PreH5 : (sid_pre <> 0)) (PreH6 : (item_pre <> 0)) (PreH7 : (structs = (cons (head) (tail)))) (PreH8 : (0 <= sid_pre)) (PreH9 : (0 <= index_pre)) (PreH10 : (cm_rep_structs_safe structs )) (PreH11 : (cm_rep_structs_safe tail )) (PreH12 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  (cm_struct_list_rep nextp tail )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (retval = (cm_rep_struct_member_array (structs) (sid_pre) (index_pre))) ”
.

Definition cmc_struct_member_array_at_return_wit_3_split_goal_spatial := 
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (retval: Z) (PreH1 : (0 <= (sid_pre - 1 ))) (PreH2 : (0 <= index_pre)) (PreH3 : (cm_rep_structs_safe tail )) (PreH4 : (retval = (cm_rep_struct_member_array (tail) ((sid_pre - 1 )) (index_pre)))) (PreH5 : (sid_pre <> 0)) (PreH6 : (item_pre <> 0)) (PreH7 : (structs = (cons (head) (tail)))) (PreH8 : (0 <= sid_pre)) (PreH9 : (0 <= index_pre)) (PreH10 : (cm_rep_structs_safe structs )) (PreH11 : (cm_rep_structs_safe tail )) (PreH12 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  (cm_struct_list_rep nextp tail )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
|--
  (cm_struct_list_rep item_pre structs )
.

Definition cmc_struct_member_array_at_partial_solve_wit_1_pure := 
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (PreH1 : (sid_pre = 0)) (PreH2 : (item_pre <> 0)) (PreH3 : (structs = (cons (head) (tail)))) (PreH4 : (0 <= sid_pre)) (PreH5 : (0 <= index_pre)) (PreH6 : (cm_rep_structs_safe structs )) (PreH7 : (cm_rep_structs_safe tail )) (PreH8 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "sid" ) )) # Int  |-> sid_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
  **  ((( &( "result" ) )) # Int  |->_)
|--
  “ (0 <= index_pre) ”
.

Definition cmc_struct_member_array_at_partial_solve_wit_1_aux := 
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (PreH1 : (sid_pre = 0)) (PreH2 : (item_pre <> 0)) (PreH3 : (structs = (cons (head) (tail)))) (PreH4 : (0 <= sid_pre)) (PreH5 : (0 <= index_pre)) (PreH6 : (cm_rep_structs_safe structs )) (PreH7 : (cm_rep_structs_safe tail )) (PreH8 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
|--
  “ (0 <= index_pre) ” 
  &&  “ (sid_pre = 0) ” 
  &&  “ (item_pre <> 0) ” 
  &&  “ (structs = (cons (head) (tail))) ” 
  &&  “ (0 <= sid_pre) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_structs_safe structs ) ” 
  &&  “ (cm_rep_structs_safe tail ) ” 
  &&  “ (cm_rep_members_safe (cm_struct_members (head)) ) ”
  &&  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
.

Definition cmc_struct_member_array_at_partial_solve_wit_1 := cmc_struct_member_array_at_partial_solve_wit_1_pure -> cmc_struct_member_array_at_partial_solve_wit_1_aux.

Definition cmc_struct_member_array_at_partial_solve_wit_2_pure := 
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (PreH1 : (sid_pre <> 0)) (PreH2 : (item_pre <> 0)) (PreH3 : (structs = (cons (head) (tail)))) (PreH4 : (0 <= sid_pre)) (PreH5 : (0 <= index_pre)) (PreH6 : (cm_rep_structs_safe structs )) (PreH7 : (cm_rep_structs_safe tail )) (PreH8 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "item" ) )) # Ptr  |-> item_pre)
  **  ((( &( "sid" ) )) # Int  |-> sid_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
  **  ((( &( "result" ) )) # Int  |->_)
|--
  “ (0 <= (sid_pre - 1 )) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_structs_safe tail ) ”
.

Definition cmc_struct_member_array_at_partial_solve_wit_2_aux := 
forall (index_pre: Z) (sid_pre: Z) (item_pre: Z) (structs: (@list cm_struct_d)) (head: cm_struct_d) (tail: (@list cm_struct_d)) (nextp: Z) (memberp: Z) (PreH1 : (sid_pre <> 0)) (PreH2 : (item_pre <> 0)) (PreH3 : (structs = (cons (head) (tail)))) (PreH4 : (0 <= sid_pre)) (PreH5 : (0 <= index_pre)) (PreH6 : (cm_rep_structs_safe structs )) (PreH7 : (cm_rep_structs_safe tail )) (PreH8 : (cm_rep_members_safe (cm_struct_members (head)) )) ,
  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_struct_list_rep nextp tail )
|--
  “ (0 <= (sid_pre - 1 )) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_structs_safe tail ) ” 
  &&  “ (sid_pre <> 0) ” 
  &&  “ (item_pre <> 0) ” 
  &&  “ (structs = (cons (head) (tail))) ” 
  &&  “ (0 <= sid_pre) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_structs_safe structs ) ” 
  &&  “ (cm_rep_structs_safe tail ) ” 
  &&  “ (cm_rep_members_safe (cm_struct_members (head)) ) ”
  &&  (cm_struct_list_rep nextp tail )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "members")) # Ptr  |-> memberp)
  **  (cm_member_list_rep memberp (cm_struct_members (head)) )
  **  ((&((item_pre)  # "cm_struct" ->ₛ "next")) # Ptr  |-> nextp)
.

Definition cmc_struct_member_array_at_partial_solve_wit_2 := cmc_struct_member_array_at_partial_solve_wit_2_pure -> cmc_struct_member_array_at_partial_solve_wit_2_aux.

(*----- Function cmc_globals_size -----*)

Definition cmc_globals_size_safety_wit_1 := 
forall (node_pre: Z) (globals: (@list cm_global_d)) (PreH1 : (cm_rep_globals_safe globals )) ,
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  (cm_global_list_rep node_pre globals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_globals_size_safety_wit_2 := 
forall (node_pre: Z) (globals: (@list cm_global_d)) (PreH1 : (node_pre = 0)) (PreH2 : (cm_rep_globals_safe globals )) ,
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  (cm_global_list_rep node_pre globals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_globals_size_safety_wit_3 := 
(
forall (node_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : (cm_rep_globals_safe tail )) (PreH2 : (retval_2 = (cm_rep_globals_size (tail)))) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1048560)) (PreH5 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH6 : (node_pre <> 0)) (PreH7 : (globals = (cons (head) (tail)))) (PreH8 : (cm_rep_globals_safe globals )) (PreH9 : (cm_rep_globals_safe tail )) ,
  (cm_global_list_rep nextp tail )
  **  ((( &( "rest_size" ) )) # Int64  |-> retval_2)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> retval)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ ((retval + retval_2 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (retval + retval_2 )) ”
) \/
(
forall (node_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : (cm_rep_globals_safe tail )) (PreH2 : (retval_2 = (cm_rep_globals_size (tail)))) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1048560)) (PreH5 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH6 : (node_pre <> 0)) (PreH7 : (globals = (cons (head) (tail)))) (PreH8 : (cm_rep_globals_safe globals )) (PreH9 : (cm_rep_globals_safe tail )) ,
  (cm_global_list_rep nextp tail )
  **  ((( &( "rest_size" ) )) # Int64  |-> retval_2)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> retval)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ ((retval + retval_2 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (retval + retval_2 )) ”
).

Definition cmc_globals_size_safety_wit_3_split_goal_1 := 
forall (node_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : (cm_rep_globals_safe tail )) (PreH2 : (retval_2 = (cm_rep_globals_size (tail)))) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1048560)) (PreH5 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH6 : (node_pre <> 0)) (PreH7 : (globals = (cons (head) (tail)))) (PreH8 : (cm_rep_globals_safe globals )) (PreH9 : (cm_rep_globals_safe tail )) ,
  (cm_global_list_rep nextp tail )
  **  ((( &( "rest_size" ) )) # Int64  |-> retval_2)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> retval)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ ((retval + retval_2 ) <= INT64_MAX) ”
.

Definition cmc_globals_size_safety_wit_3_split_goal_2 := 
forall (node_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : (cm_rep_globals_safe tail )) (PreH2 : (retval_2 = (cm_rep_globals_size (tail)))) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1048560)) (PreH5 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH6 : (node_pre <> 0)) (PreH7 : (globals = (cons (head) (tail)))) (PreH8 : (cm_rep_globals_safe globals )) (PreH9 : (cm_rep_globals_safe tail )) ,
  (cm_global_list_rep nextp tail )
  **  ((( &( "rest_size" ) )) # Int64  |-> retval_2)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> retval)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ ((INT64_MIN) <= (retval + retval_2 )) ”
.

Definition cmc_globals_size_entail_wit_1 := 
(
forall (node_pre: Z) (globals: (@list cm_global_d)) (PreH1 : (node_pre <> 0)) (PreH2 : (cm_rep_globals_safe globals )) ,
  (cm_global_list_rep node_pre globals )
|--
  EX (nextp: Z)  (head: cm_global_d)  (tail: (@list cm_global_d)) ,
  “ (node_pre <> 0) ” 
  &&  “ (globals = (cons (head) (tail))) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_rep_globals_safe tail ) ”
  &&  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
) \/
(
forall (node_pre: Z) (globals: (@list cm_global_d)) (PreH1 : (node_pre <> 0)) (PreH2 : (cm_rep_globals_safe globals )) ,
  (cm_global_list_rep node_pre globals )
|--
  EX (nextp: Z)  (head: cm_global_d)  (tail: (@list cm_global_d)) ,
  “ (node_pre <> 0) ” 
  &&  “ (globals = (cons (head) (tail))) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_rep_globals_safe tail ) ”
  &&  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
).

Definition cmc_globals_size_return_wit_1 := 
(
forall (node_pre: Z) (globals: (@list cm_global_d)) (PreH1 : (node_pre = 0)) (PreH2 : (cm_rep_globals_safe globals )) ,
  (cm_global_list_rep node_pre globals )
|--
  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (0 = (cm_rep_globals_size (globals))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1048560) ”
  &&  (cm_global_list_rep node_pre globals )
) \/
(
forall (node_pre: Z) (globals: (@list cm_global_d)) (PreH1 : (node_pre = 0)) (PreH2 : (cm_rep_globals_safe globals )) ,
  TT && emp 
|--
  “ (0 = (cm_rep_globals_size (globals))) ”
  &&  emp
).

Definition cmc_globals_size_return_wit_1_split_goal_1 := 
forall (node_pre: Z) (globals: (@list cm_global_d)) (PreH1 : (node_pre = 0)) (PreH2 : (cm_rep_globals_safe globals )) ,
  (0 = (cm_rep_globals_size (globals)))
.

Definition cmc_globals_size_return_wit_2 := 
(
forall (node_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : (cm_rep_globals_safe tail )) (PreH2 : (retval_2 = (cm_rep_globals_size (tail)))) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1048560)) (PreH5 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH6 : (node_pre <> 0)) (PreH7 : (globals = (cons (head) (tail)))) (PreH8 : (cm_rep_globals_safe globals )) (PreH9 : (cm_rep_globals_safe tail )) ,
  (cm_global_list_rep nextp tail )
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (cm_rep_globals_safe globals ) ” 
  &&  “ ((retval + retval_2 ) = (cm_rep_globals_size (globals))) ” 
  &&  “ (0 <= (retval + retval_2 )) ” 
  &&  “ ((retval + retval_2 ) <= 1048560) ”
  &&  (cm_global_list_rep node_pre globals )
) \/
(
forall (node_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : ((cm_global_init (head)) <= INT64_MAX)) (PreH2 : ((cm_global_init (head)) >= INT64_MIN)) (PreH3 : ((cm_rep_bool ((cm_global_has_init (head)))) <= INT_MAX)) (PreH4 : ((cm_global_count (head)) <= INT_MAX)) (PreH5 : ((cm_type_encode ((cm_global_ty (head)))) <= INT_MAX)) (PreH6 : ((cm_rep_bool ((cm_global_has_init (head)))) >= INT_MIN)) (PreH7 : ((cm_global_count (head)) >= INT_MIN)) (PreH8 : ((cm_type_encode ((cm_global_ty (head)))) >= INT_MIN)) (PreH9 : (cm_rep_globals_safe tail )) (PreH10 : (retval_2 = (cm_rep_globals_size (tail)))) (PreH11 : (0 <= retval_2)) (PreH12 : (retval_2 <= 1048560)) (PreH13 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH14 : (node_pre <> 0)) (PreH15 : (globals = (cons (head) (tail)))) (PreH16 : (cm_rep_globals_safe globals )) (PreH17 : (cm_rep_globals_safe tail )) ,
  (cm_global_list_rep nextp tail )
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ ((retval + retval_2 ) <= 1048560) ” 
  &&  “ (0 <= (retval + retval_2 )) ” 
  &&  “ ((retval + retval_2 ) = (cm_rep_globals_size (globals))) ”
  &&  (cm_global_list_rep node_pre globals )
).

Definition cmc_globals_size_return_wit_2_split_goal_1 := 
forall (node_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : ((cm_global_init (head)) <= INT64_MAX)) (PreH2 : ((cm_global_init (head)) >= INT64_MIN)) (PreH3 : ((cm_rep_bool ((cm_global_has_init (head)))) <= INT_MAX)) (PreH4 : ((cm_global_count (head)) <= INT_MAX)) (PreH5 : ((cm_type_encode ((cm_global_ty (head)))) <= INT_MAX)) (PreH6 : ((cm_rep_bool ((cm_global_has_init (head)))) >= INT_MIN)) (PreH7 : ((cm_global_count (head)) >= INT_MIN)) (PreH8 : ((cm_type_encode ((cm_global_ty (head)))) >= INT_MIN)) (PreH9 : (cm_rep_globals_safe tail )) (PreH10 : (retval_2 = (cm_rep_globals_size (tail)))) (PreH11 : (0 <= retval_2)) (PreH12 : (retval_2 <= 1048560)) (PreH13 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH14 : (node_pre <> 0)) (PreH15 : (globals = (cons (head) (tail)))) (PreH16 : (cm_rep_globals_safe globals )) (PreH17 : (cm_rep_globals_safe tail )) ,
  (cm_global_list_rep nextp tail )
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ ((retval + retval_2 ) <= 1048560) ”
.

Definition cmc_globals_size_return_wit_2_split_goal_2 := 
forall (node_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : ((cm_global_init (head)) <= INT64_MAX)) (PreH2 : ((cm_global_init (head)) >= INT64_MIN)) (PreH3 : ((cm_rep_bool ((cm_global_has_init (head)))) <= INT_MAX)) (PreH4 : ((cm_global_count (head)) <= INT_MAX)) (PreH5 : ((cm_type_encode ((cm_global_ty (head)))) <= INT_MAX)) (PreH6 : ((cm_rep_bool ((cm_global_has_init (head)))) >= INT_MIN)) (PreH7 : ((cm_global_count (head)) >= INT_MIN)) (PreH8 : ((cm_type_encode ((cm_global_ty (head)))) >= INT_MIN)) (PreH9 : (cm_rep_globals_safe tail )) (PreH10 : (retval_2 = (cm_rep_globals_size (tail)))) (PreH11 : (0 <= retval_2)) (PreH12 : (retval_2 <= 1048560)) (PreH13 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH14 : (node_pre <> 0)) (PreH15 : (globals = (cons (head) (tail)))) (PreH16 : (cm_rep_globals_safe globals )) (PreH17 : (cm_rep_globals_safe tail )) ,
  (cm_global_list_rep nextp tail )
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (0 <= (retval + retval_2 )) ”
.

Definition cmc_globals_size_return_wit_2_split_goal_3 := 
forall (node_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : ((cm_global_init (head)) <= INT64_MAX)) (PreH2 : ((cm_global_init (head)) >= INT64_MIN)) (PreH3 : ((cm_rep_bool ((cm_global_has_init (head)))) <= INT_MAX)) (PreH4 : ((cm_global_count (head)) <= INT_MAX)) (PreH5 : ((cm_type_encode ((cm_global_ty (head)))) <= INT_MAX)) (PreH6 : ((cm_rep_bool ((cm_global_has_init (head)))) >= INT_MIN)) (PreH7 : ((cm_global_count (head)) >= INT_MIN)) (PreH8 : ((cm_type_encode ((cm_global_ty (head)))) >= INT_MIN)) (PreH9 : (cm_rep_globals_safe tail )) (PreH10 : (retval_2 = (cm_rep_globals_size (tail)))) (PreH11 : (0 <= retval_2)) (PreH12 : (retval_2 <= 1048560)) (PreH13 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH14 : (node_pre <> 0)) (PreH15 : (globals = (cons (head) (tail)))) (PreH16 : (cm_rep_globals_safe globals )) (PreH17 : (cm_rep_globals_safe tail )) ,
  (cm_global_list_rep nextp tail )
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ ((retval + retval_2 ) = (cm_rep_globals_size (globals))) ”
.

Definition cmc_globals_size_return_wit_2_split_goal_spatial := 
forall (node_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : ((cm_global_init (head)) <= INT64_MAX)) (PreH2 : ((cm_global_init (head)) >= INT64_MIN)) (PreH3 : ((cm_rep_bool ((cm_global_has_init (head)))) <= INT_MAX)) (PreH4 : ((cm_global_count (head)) <= INT_MAX)) (PreH5 : ((cm_type_encode ((cm_global_ty (head)))) <= INT_MAX)) (PreH6 : ((cm_rep_bool ((cm_global_has_init (head)))) >= INT_MIN)) (PreH7 : ((cm_global_count (head)) >= INT_MIN)) (PreH8 : ((cm_type_encode ((cm_global_ty (head)))) >= INT_MIN)) (PreH9 : (cm_rep_globals_safe tail )) (PreH10 : (retval_2 = (cm_rep_globals_size (tail)))) (PreH11 : (0 <= retval_2)) (PreH12 : (retval_2 <= 1048560)) (PreH13 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH14 : (node_pre <> 0)) (PreH15 : (globals = (cons (head) (tail)))) (PreH16 : (cm_rep_globals_safe globals )) (PreH17 : (cm_rep_globals_safe tail )) ,
  (cm_global_list_rep nextp tail )
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
|--
  (cm_global_list_rep node_pre globals )
.

Definition cmc_globals_size_partial_solve_wit_1 := 
forall (node_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (PreH1 : (node_pre <> 0)) (PreH2 : (globals = (cons (head) (tail)))) (PreH3 : (cm_rep_globals_safe globals )) (PreH4 : (cm_rep_globals_safe tail )) ,
  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
|--
  “ (node_pre <> 0) ” 
  &&  “ (globals = (cons (head) (tail))) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_rep_globals_safe tail ) ”
  &&  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
.

Definition cmc_globals_size_partial_solve_wit_2_pure := 
forall (node_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (PreH1 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH2 : (node_pre <> 0)) (PreH3 : (globals = (cons (head) (tail)))) (PreH4 : (cm_rep_globals_safe globals )) (PreH5 : (cm_rep_globals_safe tail )) ,
  ((( &( "rest_size" ) )) # Int64  |->_)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> retval)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ (cm_rep_globals_safe tail ) ”
.

Definition cmc_globals_size_partial_solve_wit_2_aux := 
forall (node_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (PreH1 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH2 : (node_pre <> 0)) (PreH3 : (globals = (cons (head) (tail)))) (PreH4 : (cm_rep_globals_safe globals )) (PreH5 : (cm_rep_globals_safe tail )) ,
  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
|--
  “ (cm_rep_globals_safe tail ) ” 
  &&  “ (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head))))) ” 
  &&  “ (node_pre <> 0) ” 
  &&  “ (globals = (cons (head) (tail))) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_rep_globals_safe tail ) ”
  &&  (cm_global_list_rep nextp tail )
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
.

Definition cmc_globals_size_partial_solve_wit_2 := cmc_globals_size_partial_solve_wit_2_pure -> cmc_globals_size_partial_solve_wit_2_aux.

(*----- Function cmc_globals_prefix -----*)

Definition cmc_globals_prefix_safety_wit_1 := 
forall (index_pre: Z) (node_pre: Z) (globals: (@list cm_global_d)) (PreH1 : (0 <= index_pre)) (PreH2 : (cm_rep_globals_safe globals )) ,
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  (cm_global_list_rep node_pre globals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_globals_prefix_safety_wit_2 := 
forall (index_pre: Z) (node_pre: Z) (globals: (@list cm_global_d)) (PreH1 : (node_pre = 0)) (PreH2 : (0 <= index_pre)) (PreH3 : (cm_rep_globals_safe globals )) ,
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  (cm_global_list_rep node_pre globals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_globals_prefix_safety_wit_3 := 
forall (index_pre: Z) (node_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (PreH1 : (node_pre <> 0)) (PreH2 : (globals = (cons (head) (tail)))) (PreH3 : (0 <= index_pre)) (PreH4 : (cm_rep_globals_safe globals )) (PreH5 : (cm_rep_globals_safe tail )) ,
  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_globals_prefix_safety_wit_4 := 
forall (index_pre: Z) (node_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (PreH1 : (index_pre = 0)) (PreH2 : (node_pre <> 0)) (PreH3 : (globals = (cons (head) (tail)))) (PreH4 : (0 <= index_pre)) (PreH5 : (cm_rep_globals_safe globals )) (PreH6 : (cm_rep_globals_safe tail )) ,
  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_globals_prefix_safety_wit_5 := 
forall (index_pre: Z) (node_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (PreH1 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH2 : (index_pre <> 0)) (PreH3 : (node_pre <> 0)) (PreH4 : (globals = (cons (head) (tail)))) (PreH5 : (0 <= index_pre)) (PreH6 : (cm_rep_globals_safe globals )) (PreH7 : (cm_rep_globals_safe tail )) ,
  ((( &( "rest_size" ) )) # Int64  |->_)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> retval)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ ((index_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (index_pre - 1 )) ”
.

Definition cmc_globals_prefix_safety_wit_6 := 
forall (index_pre: Z) (node_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (PreH1 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH2 : (index_pre <> 0)) (PreH3 : (node_pre <> 0)) (PreH4 : (globals = (cons (head) (tail)))) (PreH5 : (0 <= index_pre)) (PreH6 : (cm_rep_globals_safe globals )) (PreH7 : (cm_rep_globals_safe tail )) ,
  ((( &( "rest_size" ) )) # Int64  |->_)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> retval)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmc_globals_prefix_safety_wit_7 := 
(
forall (index_pre: Z) (node_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (index_pre - 1 ))) (PreH2 : (cm_rep_globals_safe tail )) (PreH3 : (retval_2 = (cm_rep_globals_prefix (tail) ((index_pre - 1 ))))) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1048560)) (PreH6 : (retval_2 <= (cm_rep_globals_size (tail)))) (PreH7 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH8 : (index_pre <> 0)) (PreH9 : (node_pre <> 0)) (PreH10 : (globals = (cons (head) (tail)))) (PreH11 : (0 <= index_pre)) (PreH12 : (cm_rep_globals_safe globals )) (PreH13 : (cm_rep_globals_safe tail )) ,
  (cm_global_list_rep nextp tail )
  **  ((( &( "rest_size" ) )) # Int64  |-> retval_2)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> retval)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ ((retval + retval_2 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (retval + retval_2 )) ”
) \/
(
forall (index_pre: Z) (node_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (index_pre - 1 ))) (PreH2 : (cm_rep_globals_safe tail )) (PreH3 : (retval_2 = (cm_rep_globals_prefix (tail) ((index_pre - 1 ))))) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1048560)) (PreH6 : (retval_2 <= (cm_rep_globals_size (tail)))) (PreH7 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH8 : (index_pre <> 0)) (PreH9 : (node_pre <> 0)) (PreH10 : (globals = (cons (head) (tail)))) (PreH11 : (0 <= index_pre)) (PreH12 : (cm_rep_globals_safe globals )) (PreH13 : (cm_rep_globals_safe tail )) ,
  (cm_global_list_rep nextp tail )
  **  ((( &( "rest_size" ) )) # Int64  |-> retval_2)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> retval)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ ((retval + retval_2 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (retval + retval_2 )) ”
).

Definition cmc_globals_prefix_safety_wit_7_split_goal_1 := 
forall (index_pre: Z) (node_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (index_pre - 1 ))) (PreH2 : (cm_rep_globals_safe tail )) (PreH3 : (retval_2 = (cm_rep_globals_prefix (tail) ((index_pre - 1 ))))) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1048560)) (PreH6 : (retval_2 <= (cm_rep_globals_size (tail)))) (PreH7 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH8 : (index_pre <> 0)) (PreH9 : (node_pre <> 0)) (PreH10 : (globals = (cons (head) (tail)))) (PreH11 : (0 <= index_pre)) (PreH12 : (cm_rep_globals_safe globals )) (PreH13 : (cm_rep_globals_safe tail )) ,
  (cm_global_list_rep nextp tail )
  **  ((( &( "rest_size" ) )) # Int64  |-> retval_2)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> retval)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ ((retval + retval_2 ) <= INT64_MAX) ”
.

Definition cmc_globals_prefix_safety_wit_7_split_goal_2 := 
forall (index_pre: Z) (node_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (index_pre - 1 ))) (PreH2 : (cm_rep_globals_safe tail )) (PreH3 : (retval_2 = (cm_rep_globals_prefix (tail) ((index_pre - 1 ))))) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1048560)) (PreH6 : (retval_2 <= (cm_rep_globals_size (tail)))) (PreH7 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH8 : (index_pre <> 0)) (PreH9 : (node_pre <> 0)) (PreH10 : (globals = (cons (head) (tail)))) (PreH11 : (0 <= index_pre)) (PreH12 : (cm_rep_globals_safe globals )) (PreH13 : (cm_rep_globals_safe tail )) ,
  (cm_global_list_rep nextp tail )
  **  ((( &( "rest_size" ) )) # Int64  |-> retval_2)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> retval)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ ((INT64_MIN) <= (retval + retval_2 )) ”
.

Definition cmc_globals_prefix_entail_wit_1 := 
(
forall (index_pre: Z) (node_pre: Z) (globals: (@list cm_global_d)) (PreH1 : (node_pre <> 0)) (PreH2 : (0 <= index_pre)) (PreH3 : (cm_rep_globals_safe globals )) ,
  (cm_global_list_rep node_pre globals )
|--
  EX (nextp: Z)  (head: cm_global_d)  (tail: (@list cm_global_d)) ,
  “ (node_pre <> 0) ” 
  &&  “ (globals = (cons (head) (tail))) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_rep_globals_safe tail ) ”
  &&  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
) \/
(
forall (index_pre: Z) (node_pre: Z) (globals: (@list cm_global_d)) (PreH1 : (node_pre <> 0)) (PreH2 : (0 <= index_pre)) (PreH3 : (cm_rep_globals_safe globals )) ,
  (cm_global_list_rep node_pre globals )
|--
  EX (nextp: Z)  (head: cm_global_d)  (tail: (@list cm_global_d)) ,
  “ (node_pre <> 0) ” 
  &&  “ (globals = (cons (head) (tail))) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_rep_globals_safe tail ) ”
  &&  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
).

Definition cmc_globals_prefix_return_wit_1 := 
(
forall (index_pre: Z) (node_pre: Z) (globals: (@list cm_global_d)) (PreH1 : (node_pre = 0)) (PreH2 : (0 <= index_pre)) (PreH3 : (cm_rep_globals_safe globals )) ,
  (cm_global_list_rep node_pre globals )
|--
  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (0 = (cm_rep_globals_prefix (globals) (index_pre))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1048560) ” 
  &&  “ (0 <= (cm_rep_globals_size (globals))) ”
  &&  (cm_global_list_rep node_pre globals )
) \/
(
forall (index_pre: Z) (node_pre: Z) (globals: (@list cm_global_d)) (PreH1 : (node_pre = 0)) (PreH2 : (0 <= index_pre)) (PreH3 : (cm_rep_globals_safe globals )) ,
  TT && emp 
|--
  “ (0 <= (cm_rep_globals_size (globals))) ” 
  &&  “ (0 = (cm_rep_globals_prefix (globals) (index_pre))) ”
  &&  emp
).

Definition cmc_globals_prefix_return_wit_1_split_goal_1 := 
forall (index_pre: Z) (node_pre: Z) (globals: (@list cm_global_d)) (PreH1 : (node_pre = 0)) (PreH2 : (0 <= index_pre)) (PreH3 : (cm_rep_globals_safe globals )) ,
  (0 <= (cm_rep_globals_size (globals)))
.

Definition cmc_globals_prefix_return_wit_1_split_goal_2 := 
forall (index_pre: Z) (node_pre: Z) (globals: (@list cm_global_d)) (PreH1 : (node_pre = 0)) (PreH2 : (0 <= index_pre)) (PreH3 : (cm_rep_globals_safe globals )) ,
  (0 = (cm_rep_globals_prefix (globals) (index_pre)))
.

Definition cmc_globals_prefix_return_wit_2 := 
(
forall (index_pre: Z) (node_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (PreH1 : (index_pre = 0)) (PreH2 : (node_pre <> 0)) (PreH3 : (globals = (cons (head) (tail)))) (PreH4 : (0 <= index_pre)) (PreH5 : (cm_rep_globals_safe globals )) (PreH6 : (cm_rep_globals_safe tail )) ,
  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
|--
  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (0 = (cm_rep_globals_prefix (globals) (index_pre))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1048560) ” 
  &&  “ (0 <= (cm_rep_globals_size (globals))) ”
  &&  (cm_global_list_rep node_pre globals )
) \/
(
forall (index_pre: Z) (node_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (PreH1 : ((cm_global_init (head)) <= INT64_MAX)) (PreH2 : ((cm_global_init (head)) >= INT64_MIN)) (PreH3 : ((cm_rep_bool ((cm_global_has_init (head)))) <= INT_MAX)) (PreH4 : ((cm_global_count (head)) <= INT_MAX)) (PreH5 : ((cm_type_encode ((cm_global_ty (head)))) <= INT_MAX)) (PreH6 : ((cm_rep_bool ((cm_global_has_init (head)))) >= INT_MIN)) (PreH7 : ((cm_global_count (head)) >= INT_MIN)) (PreH8 : ((cm_type_encode ((cm_global_ty (head)))) >= INT_MIN)) (PreH9 : (index_pre = 0)) (PreH10 : (node_pre <> 0)) (PreH11 : (globals = (cons (head) (tail)))) (PreH12 : (0 <= index_pre)) (PreH13 : (cm_rep_globals_safe globals )) (PreH14 : (cm_rep_globals_safe tail )) ,
  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
|--
  “ (0 <= (cm_rep_globals_size (globals))) ” 
  &&  “ (0 = (cm_rep_globals_prefix (globals) (0))) ”
  &&  (cm_global_list_rep node_pre globals )
).

Definition cmc_globals_prefix_return_wit_2_split_goal_1 := 
forall (index_pre: Z) (node_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (PreH1 : ((cm_global_init (head)) <= INT64_MAX)) (PreH2 : ((cm_global_init (head)) >= INT64_MIN)) (PreH3 : ((cm_rep_bool ((cm_global_has_init (head)))) <= INT_MAX)) (PreH4 : ((cm_global_count (head)) <= INT_MAX)) (PreH5 : ((cm_type_encode ((cm_global_ty (head)))) <= INT_MAX)) (PreH6 : ((cm_rep_bool ((cm_global_has_init (head)))) >= INT_MIN)) (PreH7 : ((cm_global_count (head)) >= INT_MIN)) (PreH8 : ((cm_type_encode ((cm_global_ty (head)))) >= INT_MIN)) (PreH9 : (index_pre = 0)) (PreH10 : (node_pre <> 0)) (PreH11 : (globals = (cons (head) (tail)))) (PreH12 : (0 <= index_pre)) (PreH13 : (cm_rep_globals_safe globals )) (PreH14 : (cm_rep_globals_safe tail )) ,
  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
|--
  “ (0 <= (cm_rep_globals_size (globals))) ”
.

Definition cmc_globals_prefix_return_wit_2_split_goal_2 := 
forall (index_pre: Z) (node_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (PreH1 : ((cm_global_init (head)) <= INT64_MAX)) (PreH2 : ((cm_global_init (head)) >= INT64_MIN)) (PreH3 : ((cm_rep_bool ((cm_global_has_init (head)))) <= INT_MAX)) (PreH4 : ((cm_global_count (head)) <= INT_MAX)) (PreH5 : ((cm_type_encode ((cm_global_ty (head)))) <= INT_MAX)) (PreH6 : ((cm_rep_bool ((cm_global_has_init (head)))) >= INT_MIN)) (PreH7 : ((cm_global_count (head)) >= INT_MIN)) (PreH8 : ((cm_type_encode ((cm_global_ty (head)))) >= INT_MIN)) (PreH9 : (index_pre = 0)) (PreH10 : (node_pre <> 0)) (PreH11 : (globals = (cons (head) (tail)))) (PreH12 : (0 <= index_pre)) (PreH13 : (cm_rep_globals_safe globals )) (PreH14 : (cm_rep_globals_safe tail )) ,
  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
|--
  “ (0 = (cm_rep_globals_prefix (globals) (0))) ”
.

Definition cmc_globals_prefix_return_wit_2_split_goal_spatial := 
forall (index_pre: Z) (node_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (PreH1 : ((cm_global_init (head)) <= INT64_MAX)) (PreH2 : ((cm_global_init (head)) >= INT64_MIN)) (PreH3 : ((cm_rep_bool ((cm_global_has_init (head)))) <= INT_MAX)) (PreH4 : ((cm_global_count (head)) <= INT_MAX)) (PreH5 : ((cm_type_encode ((cm_global_ty (head)))) <= INT_MAX)) (PreH6 : ((cm_rep_bool ((cm_global_has_init (head)))) >= INT_MIN)) (PreH7 : ((cm_global_count (head)) >= INT_MIN)) (PreH8 : ((cm_type_encode ((cm_global_ty (head)))) >= INT_MIN)) (PreH9 : (index_pre = 0)) (PreH10 : (node_pre <> 0)) (PreH11 : (globals = (cons (head) (tail)))) (PreH12 : (0 <= index_pre)) (PreH13 : (cm_rep_globals_safe globals )) (PreH14 : (cm_rep_globals_safe tail )) ,
  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
|--
  (cm_global_list_rep node_pre globals )
.

Definition cmc_globals_prefix_return_wit_3 := 
(
forall (index_pre: Z) (node_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= (index_pre - 1 ))) (PreH2 : (cm_rep_globals_safe tail )) (PreH3 : (retval_2 = (cm_rep_globals_prefix (tail) ((index_pre - 1 ))))) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1048560)) (PreH6 : (retval_2 <= (cm_rep_globals_size (tail)))) (PreH7 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH8 : (index_pre <> 0)) (PreH9 : (node_pre <> 0)) (PreH10 : (globals = (cons (head) (tail)))) (PreH11 : (0 <= index_pre)) (PreH12 : (cm_rep_globals_safe globals )) (PreH13 : (cm_rep_globals_safe tail )) ,
  (cm_global_list_rep nextp tail )
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ ((retval + retval_2 ) = (cm_rep_globals_prefix (globals) (index_pre))) ” 
  &&  “ (0 <= (retval + retval_2 )) ” 
  &&  “ ((retval + retval_2 ) <= 1048560) ” 
  &&  “ ((retval + retval_2 ) <= (cm_rep_globals_size (globals))) ”
  &&  (cm_global_list_rep node_pre globals )
) \/
(
forall (index_pre: Z) (node_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : ((cm_global_init (head)) <= INT64_MAX)) (PreH2 : ((cm_global_init (head)) >= INT64_MIN)) (PreH3 : ((cm_rep_bool ((cm_global_has_init (head)))) <= INT_MAX)) (PreH4 : ((cm_global_count (head)) <= INT_MAX)) (PreH5 : ((cm_type_encode ((cm_global_ty (head)))) <= INT_MAX)) (PreH6 : ((cm_rep_bool ((cm_global_has_init (head)))) >= INT_MIN)) (PreH7 : ((cm_global_count (head)) >= INT_MIN)) (PreH8 : ((cm_type_encode ((cm_global_ty (head)))) >= INT_MIN)) (PreH9 : (0 <= (index_pre - 1 ))) (PreH10 : (cm_rep_globals_safe tail )) (PreH11 : (retval_2 = (cm_rep_globals_prefix (tail) ((index_pre - 1 ))))) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 <= 1048560)) (PreH14 : (retval_2 <= (cm_rep_globals_size (tail)))) (PreH15 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH16 : (index_pre <> 0)) (PreH17 : (node_pre <> 0)) (PreH18 : (globals = (cons (head) (tail)))) (PreH19 : (0 <= index_pre)) (PreH20 : (cm_rep_globals_safe globals )) (PreH21 : (cm_rep_globals_safe tail )) ,
  (cm_global_list_rep nextp tail )
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ ((retval + retval_2 ) <= (cm_rep_globals_size (globals))) ” 
  &&  “ ((retval + retval_2 ) <= 1048560) ” 
  &&  “ (0 <= (retval + retval_2 )) ” 
  &&  “ ((retval + retval_2 ) = (cm_rep_globals_prefix (globals) (index_pre))) ”
  &&  (cm_global_list_rep node_pre globals )
).

Definition cmc_globals_prefix_return_wit_3_split_goal_1 := 
forall (index_pre: Z) (node_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : ((cm_global_init (head)) <= INT64_MAX)) (PreH2 : ((cm_global_init (head)) >= INT64_MIN)) (PreH3 : ((cm_rep_bool ((cm_global_has_init (head)))) <= INT_MAX)) (PreH4 : ((cm_global_count (head)) <= INT_MAX)) (PreH5 : ((cm_type_encode ((cm_global_ty (head)))) <= INT_MAX)) (PreH6 : ((cm_rep_bool ((cm_global_has_init (head)))) >= INT_MIN)) (PreH7 : ((cm_global_count (head)) >= INT_MIN)) (PreH8 : ((cm_type_encode ((cm_global_ty (head)))) >= INT_MIN)) (PreH9 : (0 <= (index_pre - 1 ))) (PreH10 : (cm_rep_globals_safe tail )) (PreH11 : (retval_2 = (cm_rep_globals_prefix (tail) ((index_pre - 1 ))))) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 <= 1048560)) (PreH14 : (retval_2 <= (cm_rep_globals_size (tail)))) (PreH15 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH16 : (index_pre <> 0)) (PreH17 : (node_pre <> 0)) (PreH18 : (globals = (cons (head) (tail)))) (PreH19 : (0 <= index_pre)) (PreH20 : (cm_rep_globals_safe globals )) (PreH21 : (cm_rep_globals_safe tail )) ,
  (cm_global_list_rep nextp tail )
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ ((retval + retval_2 ) <= (cm_rep_globals_size (globals))) ”
.

Definition cmc_globals_prefix_return_wit_3_split_goal_2 := 
forall (index_pre: Z) (node_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : ((cm_global_init (head)) <= INT64_MAX)) (PreH2 : ((cm_global_init (head)) >= INT64_MIN)) (PreH3 : ((cm_rep_bool ((cm_global_has_init (head)))) <= INT_MAX)) (PreH4 : ((cm_global_count (head)) <= INT_MAX)) (PreH5 : ((cm_type_encode ((cm_global_ty (head)))) <= INT_MAX)) (PreH6 : ((cm_rep_bool ((cm_global_has_init (head)))) >= INT_MIN)) (PreH7 : ((cm_global_count (head)) >= INT_MIN)) (PreH8 : ((cm_type_encode ((cm_global_ty (head)))) >= INT_MIN)) (PreH9 : (0 <= (index_pre - 1 ))) (PreH10 : (cm_rep_globals_safe tail )) (PreH11 : (retval_2 = (cm_rep_globals_prefix (tail) ((index_pre - 1 ))))) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 <= 1048560)) (PreH14 : (retval_2 <= (cm_rep_globals_size (tail)))) (PreH15 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH16 : (index_pre <> 0)) (PreH17 : (node_pre <> 0)) (PreH18 : (globals = (cons (head) (tail)))) (PreH19 : (0 <= index_pre)) (PreH20 : (cm_rep_globals_safe globals )) (PreH21 : (cm_rep_globals_safe tail )) ,
  (cm_global_list_rep nextp tail )
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ ((retval + retval_2 ) <= 1048560) ”
.

Definition cmc_globals_prefix_return_wit_3_split_goal_3 := 
forall (index_pre: Z) (node_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : ((cm_global_init (head)) <= INT64_MAX)) (PreH2 : ((cm_global_init (head)) >= INT64_MIN)) (PreH3 : ((cm_rep_bool ((cm_global_has_init (head)))) <= INT_MAX)) (PreH4 : ((cm_global_count (head)) <= INT_MAX)) (PreH5 : ((cm_type_encode ((cm_global_ty (head)))) <= INT_MAX)) (PreH6 : ((cm_rep_bool ((cm_global_has_init (head)))) >= INT_MIN)) (PreH7 : ((cm_global_count (head)) >= INT_MIN)) (PreH8 : ((cm_type_encode ((cm_global_ty (head)))) >= INT_MIN)) (PreH9 : (0 <= (index_pre - 1 ))) (PreH10 : (cm_rep_globals_safe tail )) (PreH11 : (retval_2 = (cm_rep_globals_prefix (tail) ((index_pre - 1 ))))) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 <= 1048560)) (PreH14 : (retval_2 <= (cm_rep_globals_size (tail)))) (PreH15 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH16 : (index_pre <> 0)) (PreH17 : (node_pre <> 0)) (PreH18 : (globals = (cons (head) (tail)))) (PreH19 : (0 <= index_pre)) (PreH20 : (cm_rep_globals_safe globals )) (PreH21 : (cm_rep_globals_safe tail )) ,
  (cm_global_list_rep nextp tail )
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (0 <= (retval + retval_2 )) ”
.

Definition cmc_globals_prefix_return_wit_3_split_goal_4 := 
forall (index_pre: Z) (node_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : ((cm_global_init (head)) <= INT64_MAX)) (PreH2 : ((cm_global_init (head)) >= INT64_MIN)) (PreH3 : ((cm_rep_bool ((cm_global_has_init (head)))) <= INT_MAX)) (PreH4 : ((cm_global_count (head)) <= INT_MAX)) (PreH5 : ((cm_type_encode ((cm_global_ty (head)))) <= INT_MAX)) (PreH6 : ((cm_rep_bool ((cm_global_has_init (head)))) >= INT_MIN)) (PreH7 : ((cm_global_count (head)) >= INT_MIN)) (PreH8 : ((cm_type_encode ((cm_global_ty (head)))) >= INT_MIN)) (PreH9 : (0 <= (index_pre - 1 ))) (PreH10 : (cm_rep_globals_safe tail )) (PreH11 : (retval_2 = (cm_rep_globals_prefix (tail) ((index_pre - 1 ))))) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 <= 1048560)) (PreH14 : (retval_2 <= (cm_rep_globals_size (tail)))) (PreH15 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH16 : (index_pre <> 0)) (PreH17 : (node_pre <> 0)) (PreH18 : (globals = (cons (head) (tail)))) (PreH19 : (0 <= index_pre)) (PreH20 : (cm_rep_globals_safe globals )) (PreH21 : (cm_rep_globals_safe tail )) ,
  (cm_global_list_rep nextp tail )
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ ((retval + retval_2 ) = (cm_rep_globals_prefix (globals) (index_pre))) ”
.

Definition cmc_globals_prefix_return_wit_3_split_goal_spatial := 
forall (index_pre: Z) (node_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (retval_2: Z) (PreH1 : ((cm_global_init (head)) <= INT64_MAX)) (PreH2 : ((cm_global_init (head)) >= INT64_MIN)) (PreH3 : ((cm_rep_bool ((cm_global_has_init (head)))) <= INT_MAX)) (PreH4 : ((cm_global_count (head)) <= INT_MAX)) (PreH5 : ((cm_type_encode ((cm_global_ty (head)))) <= INT_MAX)) (PreH6 : ((cm_rep_bool ((cm_global_has_init (head)))) >= INT_MIN)) (PreH7 : ((cm_global_count (head)) >= INT_MIN)) (PreH8 : ((cm_type_encode ((cm_global_ty (head)))) >= INT_MIN)) (PreH9 : (0 <= (index_pre - 1 ))) (PreH10 : (cm_rep_globals_safe tail )) (PreH11 : (retval_2 = (cm_rep_globals_prefix (tail) ((index_pre - 1 ))))) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 <= 1048560)) (PreH14 : (retval_2 <= (cm_rep_globals_size (tail)))) (PreH15 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH16 : (index_pre <> 0)) (PreH17 : (node_pre <> 0)) (PreH18 : (globals = (cons (head) (tail)))) (PreH19 : (0 <= index_pre)) (PreH20 : (cm_rep_globals_safe globals )) (PreH21 : (cm_rep_globals_safe tail )) ,
  (cm_global_list_rep nextp tail )
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
|--
  (cm_global_list_rep node_pre globals )
.

Definition cmc_globals_prefix_partial_solve_wit_1 := 
forall (index_pre: Z) (node_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (PreH1 : (index_pre <> 0)) (PreH2 : (node_pre <> 0)) (PreH3 : (globals = (cons (head) (tail)))) (PreH4 : (0 <= index_pre)) (PreH5 : (cm_rep_globals_safe globals )) (PreH6 : (cm_rep_globals_safe tail )) ,
  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
|--
  “ (index_pre <> 0) ” 
  &&  “ (node_pre <> 0) ” 
  &&  “ (globals = (cons (head) (tail))) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_rep_globals_safe tail ) ”
  &&  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
.

Definition cmc_globals_prefix_partial_solve_wit_2_pure := 
forall (index_pre: Z) (node_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (PreH1 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH2 : (index_pre <> 0)) (PreH3 : (node_pre <> 0)) (PreH4 : (globals = (cons (head) (tail)))) (PreH5 : (0 <= index_pre)) (PreH6 : (cm_rep_globals_safe globals )) (PreH7 : (cm_rep_globals_safe tail )) ,
  ((( &( "rest_size" ) )) # Int64  |->_)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> retval)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ (0 <= (index_pre - 1 )) ” 
  &&  “ (cm_rep_globals_safe tail ) ”
.

Definition cmc_globals_prefix_partial_solve_wit_2_aux := 
forall (index_pre: Z) (node_pre: Z) (globals: (@list cm_global_d)) (head: cm_global_d) (tail: (@list cm_global_d)) (nextp: Z) (retval: Z) (PreH1 : (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head)))))) (PreH2 : (index_pre <> 0)) (PreH3 : (node_pre <> 0)) (PreH4 : (globals = (cons (head) (tail)))) (PreH5 : (0 <= index_pre)) (PreH6 : (cm_rep_globals_safe globals )) (PreH7 : (cm_rep_globals_safe tail )) ,
  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_global_list_rep nextp tail )
|--
  “ (0 <= (index_pre - 1 )) ” 
  &&  “ (cm_rep_globals_safe tail ) ” 
  &&  “ (retval = (cm_rep_code_slot_size ((cm_type_encode ((cm_global_ty (head))))) ((cm_global_count (head))))) ” 
  &&  “ (index_pre <> 0) ” 
  &&  “ (node_pre <> 0) ” 
  &&  “ (globals = (cons (head) (tail))) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_globals_safe globals ) ” 
  &&  “ (cm_rep_globals_safe tail ) ”
  &&  (cm_global_list_rep nextp tail )
  **  ((&((node_pre)  # "cm_global" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_global_ty (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "count")) # Int  |-> (cm_global_count (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "has_init")) # Int  |-> (cm_rep_bool ((cm_global_has_init (head)))))
  **  ((&((node_pre)  # "cm_global" ->ₛ "init")) # Int64  |-> (cm_global_init (head)))
  **  ((&((node_pre)  # "cm_global" ->ₛ "next")) # Ptr  |-> nextp)
.

Definition cmc_globals_prefix_partial_solve_wit_2 := cmc_globals_prefix_partial_solve_wit_2_pure -> cmc_globals_prefix_partial_solve_wit_2_aux.

(*----- Function cmc_strings_size -----*)

Definition cmc_strings_size_safety_wit_1 := 
forall (node_pre: Z) (strings: (@list cm_string_d)) (PreH1 : (cm_rep_strings_safe strings )) ,
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  (cm_string_list_rep node_pre strings )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_strings_size_safety_wit_2 := 
forall (node_pre: Z) (strings: (@list cm_string_d)) (PreH1 : (node_pre = 0)) (PreH2 : (cm_rep_strings_safe strings )) ,
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  (cm_string_list_rep node_pre strings )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_strings_size_safety_wit_3 := 
forall (node_pre: Z) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (nextp: Z) (bytesp: Z) (PreH1 : (node_pre <> 0)) (PreH2 : (strings = (cons (head) (tail)))) (PreH3 : (cm_rep_strings_safe strings )) (PreH4 : (cm_rep_strings_safe tail )) ,
  ((( &( "size" ) )) # Int64  |-> (cm_rep_string_length (head)))
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> bytesp)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  (cm_uint8_buffer bytesp (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_string_list_rep nextp tail )
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ (((cm_rep_string_length (head)) + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((cm_rep_string_length (head)) + 1 )) ”
.

Definition cmc_strings_size_safety_wit_4 := 
forall (node_pre: Z) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (nextp: Z) (bytesp: Z) (PreH1 : (node_pre <> 0)) (PreH2 : (strings = (cons (head) (tail)))) (PreH3 : (cm_rep_strings_safe strings )) (PreH4 : (cm_rep_strings_safe tail )) ,
  ((( &( "size" ) )) # Int64  |-> (cm_rep_string_length (head)))
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> bytesp)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  (cm_uint8_buffer bytesp (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_string_list_rep nextp tail )
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmc_strings_size_safety_wit_5 := 
forall (node_pre: Z) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (nextp: Z) (bytesp: Z) (retval: Z) (PreH1 : (cm_rep_strings_safe tail )) (PreH2 : (retval = (cm_rep_strings_size (tail)))) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1048560)) (PreH5 : (node_pre <> 0)) (PreH6 : (strings = (cons (head) (tail)))) (PreH7 : (cm_rep_strings_safe strings )) (PreH8 : (cm_rep_strings_safe tail )) ,
  (cm_string_list_rep nextp tail )
  **  ((( &( "rest_size" ) )) # Int64  |-> retval)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> ((cm_rep_string_length (head)) + 1 ))
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> bytesp)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  (cm_uint8_buffer bytesp (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ ((((cm_rep_string_length (head)) + 1 ) + retval ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((cm_rep_string_length (head)) + 1 ) + retval )) ”
.

Definition cmc_strings_size_entail_wit_1 := 
(
forall (node_pre: Z) (strings: (@list cm_string_d)) (PreH1 : (node_pre <> 0)) (PreH2 : (cm_rep_strings_safe strings )) ,
  (cm_string_list_rep node_pre strings )
|--
  EX (nextp: Z)  (bytesp: Z)  (head: cm_string_d)  (tail: (@list cm_string_d)) ,
  “ (node_pre <> 0) ” 
  &&  “ (strings = (cons (head) (tail))) ” 
  &&  “ (cm_rep_strings_safe strings ) ” 
  &&  “ (cm_rep_strings_safe tail ) ”
  &&  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> bytesp)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  (cm_uint8_buffer bytesp (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_string_list_rep nextp tail )
) \/
(
forall (node_pre: Z) (strings: (@list cm_string_d)) (PreH1 : (node_pre <> 0)) (PreH2 : (cm_rep_strings_safe strings )) ,
  (cm_string_list_rep node_pre strings )
|--
  EX (nextp: Z)  (bytesp: Z)  (head: cm_string_d)  (tail: (@list cm_string_d)) ,
  “ (node_pre <> 0) ” 
  &&  “ (strings = (cons (head) (tail))) ” 
  &&  “ (cm_rep_strings_safe strings ) ” 
  &&  “ (cm_rep_strings_safe tail ) ”
  &&  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> bytesp)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  (cm_uint8_buffer bytesp (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_string_list_rep nextp tail )
).

Definition cmc_strings_size_return_wit_1 := 
(
forall (node_pre: Z) (strings: (@list cm_string_d)) (PreH1 : (node_pre = 0)) (PreH2 : (cm_rep_strings_safe strings )) ,
  (cm_string_list_rep node_pre strings )
|--
  “ (cm_rep_strings_safe strings ) ” 
  &&  “ (0 = (cm_rep_strings_size (strings))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1048560) ”
  &&  (cm_string_list_rep node_pre strings )
) \/
(
forall (node_pre: Z) (strings: (@list cm_string_d)) (PreH1 : (node_pre = 0)) (PreH2 : (cm_rep_strings_safe strings )) ,
  TT && emp 
|--
  “ (0 = (cm_rep_strings_size (strings))) ”
  &&  emp
).

Definition cmc_strings_size_return_wit_1_split_goal_1 := 
forall (node_pre: Z) (strings: (@list cm_string_d)) (PreH1 : (node_pre = 0)) (PreH2 : (cm_rep_strings_safe strings )) ,
  (0 = (cm_rep_strings_size (strings)))
.

Definition cmc_strings_size_return_wit_2 := 
(
forall (node_pre: Z) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (nextp: Z) (bytesp: Z) (retval: Z) (PreH1 : (cm_rep_strings_safe tail )) (PreH2 : (retval = (cm_rep_strings_size (tail)))) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1048560)) (PreH5 : (node_pre <> 0)) (PreH6 : (strings = (cons (head) (tail)))) (PreH7 : (cm_rep_strings_safe strings )) (PreH8 : (cm_rep_strings_safe tail )) ,
  (cm_string_list_rep nextp tail )
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> bytesp)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  (cm_uint8_buffer bytesp (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (cm_rep_strings_safe strings ) ” 
  &&  “ ((((cm_rep_string_length (head)) + 1 ) + retval ) = (cm_rep_strings_size (strings))) ” 
  &&  “ (0 <= (((cm_rep_string_length (head)) + 1 ) + retval )) ” 
  &&  “ ((((cm_rep_string_length (head)) + 1 ) + retval ) <= 1048560) ”
  &&  (cm_string_list_rep node_pre strings )
) \/
(
forall (node_pre: Z) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (nextp: Z) (bytesp: Z) (retval: Z) (PreH1 : ((cm_rep_string_length (head)) <= INT_MAX)) (PreH2 : ((cm_rep_string_length (head)) >= INT_MIN)) (PreH3 : (cm_rep_strings_safe tail )) (PreH4 : (retval = (cm_rep_strings_size (tail)))) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1048560)) (PreH7 : (node_pre <> 0)) (PreH8 : (strings = (cons (head) (tail)))) (PreH9 : (cm_rep_strings_safe strings )) (PreH10 : (cm_rep_strings_safe tail )) ,
  (cm_string_list_rep nextp tail )
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> bytesp)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  (cm_uint8_buffer bytesp (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ ((((cm_rep_string_length (head)) + 1 ) + retval ) <= 1048560) ” 
  &&  “ (0 <= (((cm_rep_string_length (head)) + 1 ) + retval )) ” 
  &&  “ ((((cm_rep_string_length (head)) + 1 ) + retval ) = (cm_rep_strings_size (strings))) ”
  &&  (cm_string_list_rep node_pre strings )
).

Definition cmc_strings_size_return_wit_2_split_goal_1 := 
forall (node_pre: Z) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (nextp: Z) (bytesp: Z) (retval: Z) (PreH1 : ((cm_rep_string_length (head)) <= INT_MAX)) (PreH2 : ((cm_rep_string_length (head)) >= INT_MIN)) (PreH3 : (cm_rep_strings_safe tail )) (PreH4 : (retval = (cm_rep_strings_size (tail)))) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1048560)) (PreH7 : (node_pre <> 0)) (PreH8 : (strings = (cons (head) (tail)))) (PreH9 : (cm_rep_strings_safe strings )) (PreH10 : (cm_rep_strings_safe tail )) ,
  (cm_string_list_rep nextp tail )
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> bytesp)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  (cm_uint8_buffer bytesp (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ ((((cm_rep_string_length (head)) + 1 ) + retval ) <= 1048560) ”
.

Definition cmc_strings_size_return_wit_2_split_goal_2 := 
forall (node_pre: Z) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (nextp: Z) (bytesp: Z) (retval: Z) (PreH1 : ((cm_rep_string_length (head)) <= INT_MAX)) (PreH2 : ((cm_rep_string_length (head)) >= INT_MIN)) (PreH3 : (cm_rep_strings_safe tail )) (PreH4 : (retval = (cm_rep_strings_size (tail)))) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1048560)) (PreH7 : (node_pre <> 0)) (PreH8 : (strings = (cons (head) (tail)))) (PreH9 : (cm_rep_strings_safe strings )) (PreH10 : (cm_rep_strings_safe tail )) ,
  (cm_string_list_rep nextp tail )
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> bytesp)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  (cm_uint8_buffer bytesp (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (0 <= (((cm_rep_string_length (head)) + 1 ) + retval )) ”
.

Definition cmc_strings_size_return_wit_2_split_goal_3 := 
forall (node_pre: Z) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (nextp: Z) (bytesp: Z) (retval: Z) (PreH1 : ((cm_rep_string_length (head)) <= INT_MAX)) (PreH2 : ((cm_rep_string_length (head)) >= INT_MIN)) (PreH3 : (cm_rep_strings_safe tail )) (PreH4 : (retval = (cm_rep_strings_size (tail)))) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1048560)) (PreH7 : (node_pre <> 0)) (PreH8 : (strings = (cons (head) (tail)))) (PreH9 : (cm_rep_strings_safe strings )) (PreH10 : (cm_rep_strings_safe tail )) ,
  (cm_string_list_rep nextp tail )
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> bytesp)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  (cm_uint8_buffer bytesp (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ ((((cm_rep_string_length (head)) + 1 ) + retval ) = (cm_rep_strings_size (strings))) ”
.

Definition cmc_strings_size_return_wit_2_split_goal_spatial := 
forall (node_pre: Z) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (nextp: Z) (bytesp: Z) (retval: Z) (PreH1 : ((cm_rep_string_length (head)) <= INT_MAX)) (PreH2 : ((cm_rep_string_length (head)) >= INT_MIN)) (PreH3 : (cm_rep_strings_safe tail )) (PreH4 : (retval = (cm_rep_strings_size (tail)))) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1048560)) (PreH7 : (node_pre <> 0)) (PreH8 : (strings = (cons (head) (tail)))) (PreH9 : (cm_rep_strings_safe strings )) (PreH10 : (cm_rep_strings_safe tail )) ,
  (cm_string_list_rep nextp tail )
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> bytesp)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  (cm_uint8_buffer bytesp (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
|--
  (cm_string_list_rep node_pre strings )
.

Definition cmc_strings_size_partial_solve_wit_1_pure := 
forall (node_pre: Z) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (nextp: Z) (bytesp: Z) (PreH1 : (node_pre <> 0)) (PreH2 : (strings = (cons (head) (tail)))) (PreH3 : (cm_rep_strings_safe strings )) (PreH4 : (cm_rep_strings_safe tail )) ,
  ((( &( "rest_size" ) )) # Int64  |->_)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> ((cm_rep_string_length (head)) + 1 ))
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> bytesp)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  (cm_uint8_buffer bytesp (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_string_list_rep nextp tail )
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ (cm_rep_strings_safe tail ) ”
.

Definition cmc_strings_size_partial_solve_wit_1_aux := 
forall (node_pre: Z) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (nextp: Z) (bytesp: Z) (PreH1 : (node_pre <> 0)) (PreH2 : (strings = (cons (head) (tail)))) (PreH3 : (cm_rep_strings_safe strings )) (PreH4 : (cm_rep_strings_safe tail )) ,
  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> bytesp)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  (cm_uint8_buffer bytesp (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_string_list_rep nextp tail )
|--
  “ (cm_rep_strings_safe tail ) ” 
  &&  “ (node_pre <> 0) ” 
  &&  “ (strings = (cons (head) (tail))) ” 
  &&  “ (cm_rep_strings_safe strings ) ” 
  &&  “ (cm_rep_strings_safe tail ) ”
  &&  (cm_string_list_rep nextp tail )
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> bytesp)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  (cm_uint8_buffer bytesp (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
.

Definition cmc_strings_size_partial_solve_wit_1 := cmc_strings_size_partial_solve_wit_1_pure -> cmc_strings_size_partial_solve_wit_1_aux.

(*----- Function cmc_strings_prefix -----*)

Definition cmc_strings_prefix_safety_wit_1 := 
forall (index_pre: Z) (node_pre: Z) (strings: (@list cm_string_d)) (PreH1 : (0 <= index_pre)) (PreH2 : (cm_rep_strings_safe strings )) ,
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  (cm_string_list_rep node_pre strings )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_strings_prefix_safety_wit_2 := 
forall (index_pre: Z) (node_pre: Z) (strings: (@list cm_string_d)) (PreH1 : (node_pre = 0)) (PreH2 : (0 <= index_pre)) (PreH3 : (cm_rep_strings_safe strings )) ,
  ((( &( "total" ) )) # Int64  |->_)
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  (cm_string_list_rep node_pre strings )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_strings_prefix_safety_wit_3 := 
forall (index_pre: Z) (node_pre: Z) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (nextp: Z) (bytesp: Z) (PreH1 : (node_pre <> 0)) (PreH2 : (strings = (cons (head) (tail)))) (PreH3 : (0 <= index_pre)) (PreH4 : (cm_rep_strings_safe strings )) (PreH5 : (cm_rep_strings_safe tail )) ,
  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> bytesp)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  (cm_uint8_buffer bytesp (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_string_list_rep nextp tail )
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_strings_prefix_safety_wit_4 := 
forall (index_pre: Z) (node_pre: Z) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (nextp: Z) (bytesp: Z) (PreH1 : (index_pre = 0)) (PreH2 : (node_pre <> 0)) (PreH3 : (strings = (cons (head) (tail)))) (PreH4 : (0 <= index_pre)) (PreH5 : (cm_rep_strings_safe strings )) (PreH6 : (cm_rep_strings_safe tail )) ,
  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> bytesp)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  (cm_uint8_buffer bytesp (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_string_list_rep nextp tail )
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_strings_prefix_safety_wit_5 := 
forall (index_pre: Z) (node_pre: Z) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (nextp: Z) (bytesp: Z) (PreH1 : (index_pre <> 0)) (PreH2 : (node_pre <> 0)) (PreH3 : (strings = (cons (head) (tail)))) (PreH4 : (0 <= index_pre)) (PreH5 : (cm_rep_strings_safe strings )) (PreH6 : (cm_rep_strings_safe tail )) ,
  ((( &( "size" ) )) # Int64  |-> (cm_rep_string_length (head)))
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> bytesp)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  (cm_uint8_buffer bytesp (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_string_list_rep nextp tail )
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ (((cm_rep_string_length (head)) + 1 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((cm_rep_string_length (head)) + 1 )) ”
.

Definition cmc_strings_prefix_safety_wit_6 := 
forall (index_pre: Z) (node_pre: Z) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (nextp: Z) (bytesp: Z) (PreH1 : (index_pre <> 0)) (PreH2 : (node_pre <> 0)) (PreH3 : (strings = (cons (head) (tail)))) (PreH4 : (0 <= index_pre)) (PreH5 : (cm_rep_strings_safe strings )) (PreH6 : (cm_rep_strings_safe tail )) ,
  ((( &( "size" ) )) # Int64  |-> (cm_rep_string_length (head)))
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> bytesp)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  (cm_uint8_buffer bytesp (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_string_list_rep nextp tail )
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmc_strings_prefix_safety_wit_7 := 
forall (index_pre: Z) (node_pre: Z) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (nextp: Z) (bytesp: Z) (PreH1 : (index_pre <> 0)) (PreH2 : (node_pre <> 0)) (PreH3 : (strings = (cons (head) (tail)))) (PreH4 : (0 <= index_pre)) (PreH5 : (cm_rep_strings_safe strings )) (PreH6 : (cm_rep_strings_safe tail )) ,
  ((( &( "rest_size" ) )) # Int64  |->_)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> ((cm_rep_string_length (head)) + 1 ))
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> bytesp)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  (cm_uint8_buffer bytesp (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_string_list_rep nextp tail )
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ ((index_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (index_pre - 1 )) ”
.

Definition cmc_strings_prefix_safety_wit_8 := 
forall (index_pre: Z) (node_pre: Z) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (nextp: Z) (bytesp: Z) (PreH1 : (index_pre <> 0)) (PreH2 : (node_pre <> 0)) (PreH3 : (strings = (cons (head) (tail)))) (PreH4 : (0 <= index_pre)) (PreH5 : (cm_rep_strings_safe strings )) (PreH6 : (cm_rep_strings_safe tail )) ,
  ((( &( "rest_size" ) )) # Int64  |->_)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> ((cm_rep_string_length (head)) + 1 ))
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> bytesp)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  (cm_uint8_buffer bytesp (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_string_list_rep nextp tail )
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmc_strings_prefix_safety_wit_9 := 
forall (index_pre: Z) (node_pre: Z) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (nextp: Z) (bytesp: Z) (retval: Z) (PreH1 : (0 <= (index_pre - 1 ))) (PreH2 : (cm_rep_strings_safe tail )) (PreH3 : (retval = (cm_rep_strings_prefix (tail) ((index_pre - 1 ))))) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1048560)) (PreH6 : (retval <= (cm_rep_strings_size (tail)))) (PreH7 : (index_pre <> 0)) (PreH8 : (node_pre <> 0)) (PreH9 : (strings = (cons (head) (tail)))) (PreH10 : (0 <= index_pre)) (PreH11 : (cm_rep_strings_safe strings )) (PreH12 : (cm_rep_strings_safe tail )) ,
  (cm_string_list_rep nextp tail )
  **  ((( &( "rest_size" ) )) # Int64  |-> retval)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> ((cm_rep_string_length (head)) + 1 ))
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> bytesp)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  (cm_uint8_buffer bytesp (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ ((((cm_rep_string_length (head)) + 1 ) + retval ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((cm_rep_string_length (head)) + 1 ) + retval )) ”
.

Definition cmc_strings_prefix_entail_wit_1 := 
(
forall (index_pre: Z) (node_pre: Z) (strings: (@list cm_string_d)) (PreH1 : (node_pre <> 0)) (PreH2 : (0 <= index_pre)) (PreH3 : (cm_rep_strings_safe strings )) ,
  (cm_string_list_rep node_pre strings )
|--
  EX (nextp: Z)  (bytesp: Z)  (head: cm_string_d)  (tail: (@list cm_string_d)) ,
  “ (node_pre <> 0) ” 
  &&  “ (strings = (cons (head) (tail))) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_strings_safe strings ) ” 
  &&  “ (cm_rep_strings_safe tail ) ”
  &&  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> bytesp)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  (cm_uint8_buffer bytesp (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_string_list_rep nextp tail )
) \/
(
forall (index_pre: Z) (node_pre: Z) (strings: (@list cm_string_d)) (PreH1 : (node_pre <> 0)) (PreH2 : (0 <= index_pre)) (PreH3 : (cm_rep_strings_safe strings )) ,
  (cm_string_list_rep node_pre strings )
|--
  EX (nextp: Z)  (bytesp: Z)  (head: cm_string_d)  (tail: (@list cm_string_d)) ,
  “ (node_pre <> 0) ” 
  &&  “ (strings = (cons (head) (tail))) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_strings_safe strings ) ” 
  &&  “ (cm_rep_strings_safe tail ) ”
  &&  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> bytesp)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  (cm_uint8_buffer bytesp (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_string_list_rep nextp tail )
).

Definition cmc_strings_prefix_return_wit_1 := 
(
forall (index_pre: Z) (node_pre: Z) (strings: (@list cm_string_d)) (PreH1 : (node_pre = 0)) (PreH2 : (0 <= index_pre)) (PreH3 : (cm_rep_strings_safe strings )) ,
  (cm_string_list_rep node_pre strings )
|--
  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_strings_safe strings ) ” 
  &&  “ (0 = (cm_rep_strings_prefix (strings) (index_pre))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1048560) ” 
  &&  “ (0 <= (cm_rep_strings_size (strings))) ”
  &&  (cm_string_list_rep node_pre strings )
) \/
(
forall (index_pre: Z) (node_pre: Z) (strings: (@list cm_string_d)) (PreH1 : (node_pre = 0)) (PreH2 : (0 <= index_pre)) (PreH3 : (cm_rep_strings_safe strings )) ,
  TT && emp 
|--
  “ (0 <= (cm_rep_strings_size (strings))) ” 
  &&  “ (0 = (cm_rep_strings_prefix (strings) (index_pre))) ”
  &&  emp
).

Definition cmc_strings_prefix_return_wit_1_split_goal_1 := 
forall (index_pre: Z) (node_pre: Z) (strings: (@list cm_string_d)) (PreH1 : (node_pre = 0)) (PreH2 : (0 <= index_pre)) (PreH3 : (cm_rep_strings_safe strings )) ,
  (0 <= (cm_rep_strings_size (strings)))
.

Definition cmc_strings_prefix_return_wit_1_split_goal_2 := 
forall (index_pre: Z) (node_pre: Z) (strings: (@list cm_string_d)) (PreH1 : (node_pre = 0)) (PreH2 : (0 <= index_pre)) (PreH3 : (cm_rep_strings_safe strings )) ,
  (0 = (cm_rep_strings_prefix (strings) (index_pre)))
.

Definition cmc_strings_prefix_return_wit_2 := 
(
forall (index_pre: Z) (node_pre: Z) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (nextp: Z) (bytesp: Z) (PreH1 : (index_pre = 0)) (PreH2 : (node_pre <> 0)) (PreH3 : (strings = (cons (head) (tail)))) (PreH4 : (0 <= index_pre)) (PreH5 : (cm_rep_strings_safe strings )) (PreH6 : (cm_rep_strings_safe tail )) ,
  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> bytesp)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  (cm_uint8_buffer bytesp (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_string_list_rep nextp tail )
|--
  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_strings_safe strings ) ” 
  &&  “ (0 = (cm_rep_strings_prefix (strings) (index_pre))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1048560) ” 
  &&  “ (0 <= (cm_rep_strings_size (strings))) ”
  &&  (cm_string_list_rep node_pre strings )
) \/
(
forall (index_pre: Z) (node_pre: Z) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (nextp: Z) (bytesp: Z) (PreH1 : ((cm_rep_string_length (head)) <= INT_MAX)) (PreH2 : ((cm_rep_string_length (head)) >= INT_MIN)) (PreH3 : (index_pre = 0)) (PreH4 : (node_pre <> 0)) (PreH5 : (strings = (cons (head) (tail)))) (PreH6 : (0 <= index_pre)) (PreH7 : (cm_rep_strings_safe strings )) (PreH8 : (cm_rep_strings_safe tail )) ,
  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> bytesp)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  (cm_uint8_buffer bytesp (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_string_list_rep nextp tail )
|--
  “ (0 <= (cm_rep_strings_size (strings))) ” 
  &&  “ (0 = (cm_rep_strings_prefix (strings) (0))) ”
  &&  (cm_string_list_rep node_pre strings )
).

Definition cmc_strings_prefix_return_wit_2_split_goal_1 := 
forall (index_pre: Z) (node_pre: Z) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (nextp: Z) (bytesp: Z) (PreH1 : ((cm_rep_string_length (head)) <= INT_MAX)) (PreH2 : ((cm_rep_string_length (head)) >= INT_MIN)) (PreH3 : (index_pre = 0)) (PreH4 : (node_pre <> 0)) (PreH5 : (strings = (cons (head) (tail)))) (PreH6 : (0 <= index_pre)) (PreH7 : (cm_rep_strings_safe strings )) (PreH8 : (cm_rep_strings_safe tail )) ,
  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> bytesp)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  (cm_uint8_buffer bytesp (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_string_list_rep nextp tail )
|--
  “ (0 <= (cm_rep_strings_size (strings))) ”
.

Definition cmc_strings_prefix_return_wit_2_split_goal_2 := 
forall (index_pre: Z) (node_pre: Z) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (nextp: Z) (bytesp: Z) (PreH1 : ((cm_rep_string_length (head)) <= INT_MAX)) (PreH2 : ((cm_rep_string_length (head)) >= INT_MIN)) (PreH3 : (index_pre = 0)) (PreH4 : (node_pre <> 0)) (PreH5 : (strings = (cons (head) (tail)))) (PreH6 : (0 <= index_pre)) (PreH7 : (cm_rep_strings_safe strings )) (PreH8 : (cm_rep_strings_safe tail )) ,
  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> bytesp)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  (cm_uint8_buffer bytesp (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_string_list_rep nextp tail )
|--
  “ (0 = (cm_rep_strings_prefix (strings) (0))) ”
.

Definition cmc_strings_prefix_return_wit_2_split_goal_spatial := 
forall (index_pre: Z) (node_pre: Z) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (nextp: Z) (bytesp: Z) (PreH1 : ((cm_rep_string_length (head)) <= INT_MAX)) (PreH2 : ((cm_rep_string_length (head)) >= INT_MIN)) (PreH3 : (index_pre = 0)) (PreH4 : (node_pre <> 0)) (PreH5 : (strings = (cons (head) (tail)))) (PreH6 : (0 <= index_pre)) (PreH7 : (cm_rep_strings_safe strings )) (PreH8 : (cm_rep_strings_safe tail )) ,
  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> bytesp)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  (cm_uint8_buffer bytesp (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_string_list_rep nextp tail )
|--
  (cm_string_list_rep node_pre strings )
.

Definition cmc_strings_prefix_return_wit_3 := 
(
forall (index_pre: Z) (node_pre: Z) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (nextp: Z) (bytesp: Z) (retval: Z) (PreH1 : (0 <= (index_pre - 1 ))) (PreH2 : (cm_rep_strings_safe tail )) (PreH3 : (retval = (cm_rep_strings_prefix (tail) ((index_pre - 1 ))))) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1048560)) (PreH6 : (retval <= (cm_rep_strings_size (tail)))) (PreH7 : (index_pre <> 0)) (PreH8 : (node_pre <> 0)) (PreH9 : (strings = (cons (head) (tail)))) (PreH10 : (0 <= index_pre)) (PreH11 : (cm_rep_strings_safe strings )) (PreH12 : (cm_rep_strings_safe tail )) ,
  (cm_string_list_rep nextp tail )
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> bytesp)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  (cm_uint8_buffer bytesp (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_strings_safe strings ) ” 
  &&  “ ((((cm_rep_string_length (head)) + 1 ) + retval ) = (cm_rep_strings_prefix (strings) (index_pre))) ” 
  &&  “ (0 <= (((cm_rep_string_length (head)) + 1 ) + retval )) ” 
  &&  “ ((((cm_rep_string_length (head)) + 1 ) + retval ) <= 1048560) ” 
  &&  “ ((((cm_rep_string_length (head)) + 1 ) + retval ) <= (cm_rep_strings_size (strings))) ”
  &&  (cm_string_list_rep node_pre strings )
) \/
(
forall (index_pre: Z) (node_pre: Z) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (nextp: Z) (bytesp: Z) (retval: Z) (PreH1 : ((cm_rep_string_length (head)) <= INT_MAX)) (PreH2 : ((cm_rep_string_length (head)) >= INT_MIN)) (PreH3 : (0 <= (index_pre - 1 ))) (PreH4 : (cm_rep_strings_safe tail )) (PreH5 : (retval = (cm_rep_strings_prefix (tail) ((index_pre - 1 ))))) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1048560)) (PreH8 : (retval <= (cm_rep_strings_size (tail)))) (PreH9 : (index_pre <> 0)) (PreH10 : (node_pre <> 0)) (PreH11 : (strings = (cons (head) (tail)))) (PreH12 : (0 <= index_pre)) (PreH13 : (cm_rep_strings_safe strings )) (PreH14 : (cm_rep_strings_safe tail )) ,
  (cm_string_list_rep nextp tail )
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> bytesp)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  (cm_uint8_buffer bytesp (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ ((((cm_rep_string_length (head)) + 1 ) + retval ) <= (cm_rep_strings_size (strings))) ” 
  &&  “ ((((cm_rep_string_length (head)) + 1 ) + retval ) <= 1048560) ” 
  &&  “ (0 <= (((cm_rep_string_length (head)) + 1 ) + retval )) ” 
  &&  “ ((((cm_rep_string_length (head)) + 1 ) + retval ) = (cm_rep_strings_prefix (strings) (index_pre))) ”
  &&  (cm_string_list_rep node_pre strings )
).

Definition cmc_strings_prefix_return_wit_3_split_goal_1 := 
forall (index_pre: Z) (node_pre: Z) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (nextp: Z) (bytesp: Z) (retval: Z) (PreH1 : ((cm_rep_string_length (head)) <= INT_MAX)) (PreH2 : ((cm_rep_string_length (head)) >= INT_MIN)) (PreH3 : (0 <= (index_pre - 1 ))) (PreH4 : (cm_rep_strings_safe tail )) (PreH5 : (retval = (cm_rep_strings_prefix (tail) ((index_pre - 1 ))))) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1048560)) (PreH8 : (retval <= (cm_rep_strings_size (tail)))) (PreH9 : (index_pre <> 0)) (PreH10 : (node_pre <> 0)) (PreH11 : (strings = (cons (head) (tail)))) (PreH12 : (0 <= index_pre)) (PreH13 : (cm_rep_strings_safe strings )) (PreH14 : (cm_rep_strings_safe tail )) ,
  (cm_string_list_rep nextp tail )
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> bytesp)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  (cm_uint8_buffer bytesp (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ ((((cm_rep_string_length (head)) + 1 ) + retval ) <= (cm_rep_strings_size (strings))) ”
.

Definition cmc_strings_prefix_return_wit_3_split_goal_2 := 
forall (index_pre: Z) (node_pre: Z) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (nextp: Z) (bytesp: Z) (retval: Z) (PreH1 : ((cm_rep_string_length (head)) <= INT_MAX)) (PreH2 : ((cm_rep_string_length (head)) >= INT_MIN)) (PreH3 : (0 <= (index_pre - 1 ))) (PreH4 : (cm_rep_strings_safe tail )) (PreH5 : (retval = (cm_rep_strings_prefix (tail) ((index_pre - 1 ))))) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1048560)) (PreH8 : (retval <= (cm_rep_strings_size (tail)))) (PreH9 : (index_pre <> 0)) (PreH10 : (node_pre <> 0)) (PreH11 : (strings = (cons (head) (tail)))) (PreH12 : (0 <= index_pre)) (PreH13 : (cm_rep_strings_safe strings )) (PreH14 : (cm_rep_strings_safe tail )) ,
  (cm_string_list_rep nextp tail )
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> bytesp)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  (cm_uint8_buffer bytesp (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ ((((cm_rep_string_length (head)) + 1 ) + retval ) <= 1048560) ”
.

Definition cmc_strings_prefix_return_wit_3_split_goal_3 := 
forall (index_pre: Z) (node_pre: Z) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (nextp: Z) (bytesp: Z) (retval: Z) (PreH1 : ((cm_rep_string_length (head)) <= INT_MAX)) (PreH2 : ((cm_rep_string_length (head)) >= INT_MIN)) (PreH3 : (0 <= (index_pre - 1 ))) (PreH4 : (cm_rep_strings_safe tail )) (PreH5 : (retval = (cm_rep_strings_prefix (tail) ((index_pre - 1 ))))) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1048560)) (PreH8 : (retval <= (cm_rep_strings_size (tail)))) (PreH9 : (index_pre <> 0)) (PreH10 : (node_pre <> 0)) (PreH11 : (strings = (cons (head) (tail)))) (PreH12 : (0 <= index_pre)) (PreH13 : (cm_rep_strings_safe strings )) (PreH14 : (cm_rep_strings_safe tail )) ,
  (cm_string_list_rep nextp tail )
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> bytesp)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  (cm_uint8_buffer bytesp (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ (0 <= (((cm_rep_string_length (head)) + 1 ) + retval )) ”
.

Definition cmc_strings_prefix_return_wit_3_split_goal_4 := 
forall (index_pre: Z) (node_pre: Z) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (nextp: Z) (bytesp: Z) (retval: Z) (PreH1 : ((cm_rep_string_length (head)) <= INT_MAX)) (PreH2 : ((cm_rep_string_length (head)) >= INT_MIN)) (PreH3 : (0 <= (index_pre - 1 ))) (PreH4 : (cm_rep_strings_safe tail )) (PreH5 : (retval = (cm_rep_strings_prefix (tail) ((index_pre - 1 ))))) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1048560)) (PreH8 : (retval <= (cm_rep_strings_size (tail)))) (PreH9 : (index_pre <> 0)) (PreH10 : (node_pre <> 0)) (PreH11 : (strings = (cons (head) (tail)))) (PreH12 : (0 <= index_pre)) (PreH13 : (cm_rep_strings_safe strings )) (PreH14 : (cm_rep_strings_safe tail )) ,
  (cm_string_list_rep nextp tail )
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> bytesp)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  (cm_uint8_buffer bytesp (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
|--
  “ ((((cm_rep_string_length (head)) + 1 ) + retval ) = (cm_rep_strings_prefix (strings) (index_pre))) ”
.

Definition cmc_strings_prefix_return_wit_3_split_goal_spatial := 
forall (index_pre: Z) (node_pre: Z) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (nextp: Z) (bytesp: Z) (retval: Z) (PreH1 : ((cm_rep_string_length (head)) <= INT_MAX)) (PreH2 : ((cm_rep_string_length (head)) >= INT_MIN)) (PreH3 : (0 <= (index_pre - 1 ))) (PreH4 : (cm_rep_strings_safe tail )) (PreH5 : (retval = (cm_rep_strings_prefix (tail) ((index_pre - 1 ))))) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1048560)) (PreH8 : (retval <= (cm_rep_strings_size (tail)))) (PreH9 : (index_pre <> 0)) (PreH10 : (node_pre <> 0)) (PreH11 : (strings = (cons (head) (tail)))) (PreH12 : (0 <= index_pre)) (PreH13 : (cm_rep_strings_safe strings )) (PreH14 : (cm_rep_strings_safe tail )) ,
  (cm_string_list_rep nextp tail )
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> bytesp)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  (cm_uint8_buffer bytesp (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
|--
  (cm_string_list_rep node_pre strings )
.

Definition cmc_strings_prefix_partial_solve_wit_1_pure := 
forall (index_pre: Z) (node_pre: Z) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (nextp: Z) (bytesp: Z) (PreH1 : (index_pre <> 0)) (PreH2 : (node_pre <> 0)) (PreH3 : (strings = (cons (head) (tail)))) (PreH4 : (0 <= index_pre)) (PreH5 : (cm_rep_strings_safe strings )) (PreH6 : (cm_rep_strings_safe tail )) ,
  ((( &( "rest_size" ) )) # Int64  |->_)
  **  ((( &( "next" ) )) # Ptr  |-> nextp)
  **  ((( &( "size" ) )) # Int64  |-> ((cm_rep_string_length (head)) + 1 ))
  **  ((( &( "node" ) )) # Ptr  |-> node_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> bytesp)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  (cm_uint8_buffer bytesp (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_string_list_rep nextp tail )
  **  ((( &( "total" ) )) # Int64  |->_)
|--
  “ (0 <= (index_pre - 1 )) ” 
  &&  “ (cm_rep_strings_safe tail ) ”
.

Definition cmc_strings_prefix_partial_solve_wit_1_aux := 
forall (index_pre: Z) (node_pre: Z) (strings: (@list cm_string_d)) (head: cm_string_d) (tail: (@list cm_string_d)) (nextp: Z) (bytesp: Z) (PreH1 : (index_pre <> 0)) (PreH2 : (node_pre <> 0)) (PreH3 : (strings = (cons (head) (tail)))) (PreH4 : (0 <= index_pre)) (PreH5 : (cm_rep_strings_safe strings )) (PreH6 : (cm_rep_strings_safe tail )) ,
  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> bytesp)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  (cm_uint8_buffer bytesp (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
  **  (cm_string_list_rep nextp tail )
|--
  “ (0 <= (index_pre - 1 )) ” 
  &&  “ (cm_rep_strings_safe tail ) ” 
  &&  “ (index_pre <> 0) ” 
  &&  “ (node_pre <> 0) ” 
  &&  “ (strings = (cons (head) (tail))) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_strings_safe strings ) ” 
  &&  “ (cm_rep_strings_safe tail ) ”
  &&  (cm_string_list_rep nextp tail )
  **  ((&((node_pre)  # "cm_string" ->ₛ "bytes")) # Ptr  |-> bytesp)
  **  ((&((node_pre)  # "cm_string" ->ₛ "length")) # Int  |-> (cm_rep_string_length (head)))
  **  (cm_uint8_buffer bytesp (cm_string_bytes (head)) )
  **  ((&((node_pre)  # "cm_string" ->ₛ "next")) # Ptr  |-> nextp)
.

Definition cmc_strings_prefix_partial_solve_wit_1 := cmc_strings_prefix_partial_solve_wit_1_pure -> cmc_strings_prefix_partial_solve_wit_1_aux.

(*----- Function cmc_global_address -----*)

Definition cmc_global_address_safety_wit_1 := 
forall (index_pre: Z) (globals_pre: Z) (items: (@list cm_global_d)) (retval: Z) (PreH1 : (0 <= index_pre)) (PreH2 : (cm_rep_globals_safe items )) (PreH3 : (retval = (cm_rep_globals_prefix (items) (index_pre)))) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1048560)) (PreH6 : (retval <= (cm_rep_globals_size (items)))) (PreH7 : (0 <= index_pre)) (PreH8 : (cm_rep_globals_safe items )) ,
  ((( &( "address" ) )) # Int64  |->_)
  **  (cm_global_list_rep globals_pre items )
  **  ((( &( "prefix" ) )) # Int64  |-> retval)
  **  ((( &( "globals" ) )) # Ptr  |-> globals_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
|--
  “ ((16 + retval ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (16 + retval )) ”
.

Definition cmc_global_address_safety_wit_2 := 
forall (index_pre: Z) (globals_pre: Z) (items: (@list cm_global_d)) (retval: Z) (PreH1 : (0 <= index_pre)) (PreH2 : (cm_rep_globals_safe items )) (PreH3 : (retval = (cm_rep_globals_prefix (items) (index_pre)))) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1048560)) (PreH6 : (retval <= (cm_rep_globals_size (items)))) (PreH7 : (0 <= index_pre)) (PreH8 : (cm_rep_globals_safe items )) ,
  ((( &( "address" ) )) # Int64  |->_)
  **  (cm_global_list_rep globals_pre items )
  **  ((( &( "prefix" ) )) # Int64  |-> retval)
  **  ((( &( "globals" ) )) # Ptr  |-> globals_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
|--
  “ (16 <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= 16) ”
.

Definition cmc_global_address_return_wit_1 := 
(
forall (index_pre: Z) (globals_pre: Z) (items: (@list cm_global_d)) (retval: Z) (PreH1 : (0 <= index_pre)) (PreH2 : (cm_rep_globals_safe items )) (PreH3 : (retval = (cm_rep_globals_prefix (items) (index_pre)))) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1048560)) (PreH6 : (retval <= (cm_rep_globals_size (items)))) (PreH7 : (0 <= index_pre)) (PreH8 : (cm_rep_globals_safe items )) ,
  (cm_global_list_rep globals_pre items )
|--
  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_globals_safe items ) ” 
  &&  “ ((16 + retval ) = (cm_rep_global_address (items) (index_pre))) ” 
  &&  “ (16 <= (16 + retval )) ” 
  &&  “ ((16 + retval ) <= 1048576) ”
  &&  (cm_global_list_rep globals_pre items )
) \/
(
forall (index_pre: Z) (items: (@list cm_global_d)) (retval: Z) (PreH1 : (0 <= index_pre)) (PreH2 : (cm_rep_globals_safe items )) (PreH3 : (retval = (cm_rep_globals_prefix (items) (index_pre)))) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1048560)) (PreH6 : (retval <= (cm_rep_globals_size (items)))) (PreH7 : (0 <= index_pre)) (PreH8 : (cm_rep_globals_safe items )) ,
  TT && emp 
|--
  “ ((16 + retval ) = (cm_rep_global_address (items) (index_pre))) ”
  &&  emp
).

Definition cmc_global_address_return_wit_1_split_goal_1 := 
forall (index_pre: Z) (items: (@list cm_global_d)) (retval: Z) (PreH1 : (0 <= index_pre)) (PreH2 : (cm_rep_globals_safe items )) (PreH3 : (retval = (cm_rep_globals_prefix (items) (index_pre)))) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1048560)) (PreH6 : (retval <= (cm_rep_globals_size (items)))) (PreH7 : (0 <= index_pre)) (PreH8 : (cm_rep_globals_safe items )) ,
  ((16 + retval ) = (cm_rep_global_address (items) (index_pre)))
.

Definition cmc_global_address_partial_solve_wit_1_pure := 
forall (index_pre: Z) (globals_pre: Z) (items: (@list cm_global_d)) (PreH1 : (0 <= index_pre)) (PreH2 : (cm_rep_globals_safe items )) ,
  ((( &( "prefix" ) )) # Int64  |->_)
  **  ((( &( "globals" ) )) # Ptr  |-> globals_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  (cm_global_list_rep globals_pre items )
|--
  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_globals_safe items ) ”
.

Definition cmc_global_address_partial_solve_wit_1_aux := 
forall (index_pre: Z) (globals_pre: Z) (items: (@list cm_global_d)) (PreH1 : (0 <= index_pre)) (PreH2 : (cm_rep_globals_safe items )) ,
  (cm_global_list_rep globals_pre items )
|--
  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_globals_safe items ) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_globals_safe items ) ”
  &&  (cm_global_list_rep globals_pre items )
.

Definition cmc_global_address_partial_solve_wit_1 := cmc_global_address_partial_solve_wit_1_pure -> cmc_global_address_partial_solve_wit_1_aux.

(*----- Function cmc_string_address -----*)

Definition cmc_string_address_safety_wit_1 := 
forall (index_pre: Z) (strings_pre: Z) (globals_pre: Z) (string_items: (@list cm_string_d)) (global_items: (@list cm_global_d)) (retval: Z) (retval_2: Z) (PreH1 : (0 <= index_pre)) (PreH2 : (cm_rep_strings_safe string_items )) (PreH3 : (retval_2 = (cm_rep_strings_prefix (string_items) (index_pre)))) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1048560)) (PreH6 : (retval_2 <= (cm_rep_strings_size (string_items)))) (PreH7 : (cm_rep_globals_safe global_items )) (PreH8 : (retval = (cm_rep_globals_size (global_items)))) (PreH9 : (0 <= retval)) (PreH10 : (retval <= 1048560)) (PreH11 : (0 <= index_pre)) (PreH12 : (cm_rep_globals_safe global_items )) (PreH13 : (cm_rep_strings_safe string_items )) (PreH14 : (((cm_rep_globals_size (global_items)) + (cm_rep_strings_size (string_items)) ) <= 1048560)) ,
  ((( &( "address" ) )) # Int64  |->_)
  **  (cm_string_list_rep strings_pre string_items )
  **  ((( &( "prefix" ) )) # Int64  |-> retval_2)
  **  (cm_global_list_rep globals_pre global_items )
  **  ((( &( "global_size" ) )) # Int64  |-> retval)
  **  ((( &( "globals" ) )) # Ptr  |-> globals_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
|--
  “ ((16 + retval ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (16 + retval )) ”
.

Definition cmc_string_address_safety_wit_2 := 
forall (index_pre: Z) (strings_pre: Z) (globals_pre: Z) (string_items: (@list cm_string_d)) (global_items: (@list cm_global_d)) (retval: Z) (retval_2: Z) (PreH1 : (0 <= index_pre)) (PreH2 : (cm_rep_strings_safe string_items )) (PreH3 : (retval_2 = (cm_rep_strings_prefix (string_items) (index_pre)))) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1048560)) (PreH6 : (retval_2 <= (cm_rep_strings_size (string_items)))) (PreH7 : (cm_rep_globals_safe global_items )) (PreH8 : (retval = (cm_rep_globals_size (global_items)))) (PreH9 : (0 <= retval)) (PreH10 : (retval <= 1048560)) (PreH11 : (0 <= index_pre)) (PreH12 : (cm_rep_globals_safe global_items )) (PreH13 : (cm_rep_strings_safe string_items )) (PreH14 : (((cm_rep_globals_size (global_items)) + (cm_rep_strings_size (string_items)) ) <= 1048560)) ,
  ((( &( "address" ) )) # Int64  |->_)
  **  (cm_string_list_rep strings_pre string_items )
  **  ((( &( "prefix" ) )) # Int64  |-> retval_2)
  **  (cm_global_list_rep globals_pre global_items )
  **  ((( &( "global_size" ) )) # Int64  |-> retval)
  **  ((( &( "globals" ) )) # Ptr  |-> globals_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
|--
  “ (16 <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= 16) ”
.

Definition cmc_string_address_safety_wit_3 := 
forall (index_pre: Z) (strings_pre: Z) (globals_pre: Z) (string_items: (@list cm_string_d)) (global_items: (@list cm_global_d)) (retval: Z) (retval_2: Z) (PreH1 : (0 <= index_pre)) (PreH2 : (cm_rep_strings_safe string_items )) (PreH3 : (retval_2 = (cm_rep_strings_prefix (string_items) (index_pre)))) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1048560)) (PreH6 : (retval_2 <= (cm_rep_strings_size (string_items)))) (PreH7 : (cm_rep_globals_safe global_items )) (PreH8 : (retval = (cm_rep_globals_size (global_items)))) (PreH9 : (0 <= retval)) (PreH10 : (retval <= 1048560)) (PreH11 : (0 <= index_pre)) (PreH12 : (cm_rep_globals_safe global_items )) (PreH13 : (cm_rep_strings_safe string_items )) (PreH14 : (((cm_rep_globals_size (global_items)) + (cm_rep_strings_size (string_items)) ) <= 1048560)) ,
  ((( &( "address" ) )) # Int64  |-> (16 + retval ))
  **  (cm_string_list_rep strings_pre string_items )
  **  ((( &( "prefix" ) )) # Int64  |-> retval_2)
  **  (cm_global_list_rep globals_pre global_items )
  **  ((( &( "global_size" ) )) # Int64  |-> retval)
  **  ((( &( "globals" ) )) # Ptr  |-> globals_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
|--
  “ (((16 + retval ) + retval_2 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((16 + retval ) + retval_2 )) ”
.

Definition cmc_string_address_return_wit_1 := 
(
forall (index_pre: Z) (strings_pre: Z) (globals_pre: Z) (string_items: (@list cm_string_d)) (global_items: (@list cm_global_d)) (retval: Z) (retval_2: Z) (PreH1 : (0 <= index_pre)) (PreH2 : (cm_rep_strings_safe string_items )) (PreH3 : (retval_2 = (cm_rep_strings_prefix (string_items) (index_pre)))) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1048560)) (PreH6 : (retval_2 <= (cm_rep_strings_size (string_items)))) (PreH7 : (cm_rep_globals_safe global_items )) (PreH8 : (retval = (cm_rep_globals_size (global_items)))) (PreH9 : (0 <= retval)) (PreH10 : (retval <= 1048560)) (PreH11 : (0 <= index_pre)) (PreH12 : (cm_rep_globals_safe global_items )) (PreH13 : (cm_rep_strings_safe string_items )) (PreH14 : (((cm_rep_globals_size (global_items)) + (cm_rep_strings_size (string_items)) ) <= 1048560)) ,
  (cm_string_list_rep strings_pre string_items )
  **  (cm_global_list_rep globals_pre global_items )
|--
  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_globals_safe global_items ) ” 
  &&  “ (cm_rep_strings_safe string_items ) ” 
  &&  “ (((cm_rep_globals_size (global_items)) + (cm_rep_strings_size (string_items)) ) <= 1048560) ” 
  &&  “ (((16 + retval ) + retval_2 ) = (cm_rep_string_address (global_items) (string_items) (index_pre))) ” 
  &&  “ (16 <= ((16 + retval ) + retval_2 )) ” 
  &&  “ (((16 + retval ) + retval_2 ) <= 1048576) ”
  &&  (cm_global_list_rep globals_pre global_items )
  **  (cm_string_list_rep strings_pre string_items )
) \/
(
forall (index_pre: Z) (string_items: (@list cm_string_d)) (global_items: (@list cm_global_d)) (retval: Z) (retval_2: Z) (PreH1 : (0 <= index_pre)) (PreH2 : (cm_rep_strings_safe string_items )) (PreH3 : (retval_2 = (cm_rep_strings_prefix (string_items) (index_pre)))) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1048560)) (PreH6 : (retval_2 <= (cm_rep_strings_size (string_items)))) (PreH7 : (cm_rep_globals_safe global_items )) (PreH8 : (retval = (cm_rep_globals_size (global_items)))) (PreH9 : (0 <= retval)) (PreH10 : (retval <= 1048560)) (PreH11 : (0 <= index_pre)) (PreH12 : (cm_rep_globals_safe global_items )) (PreH13 : (cm_rep_strings_safe string_items )) (PreH14 : (((cm_rep_globals_size (global_items)) + (cm_rep_strings_size (string_items)) ) <= 1048560)) ,
  TT && emp 
|--
  “ (((16 + retval ) + retval_2 ) = (cm_rep_string_address (global_items) (string_items) (index_pre))) ”
  &&  emp
).

Definition cmc_string_address_return_wit_1_split_goal_1 := 
forall (index_pre: Z) (string_items: (@list cm_string_d)) (global_items: (@list cm_global_d)) (retval: Z) (retval_2: Z) (PreH1 : (0 <= index_pre)) (PreH2 : (cm_rep_strings_safe string_items )) (PreH3 : (retval_2 = (cm_rep_strings_prefix (string_items) (index_pre)))) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1048560)) (PreH6 : (retval_2 <= (cm_rep_strings_size (string_items)))) (PreH7 : (cm_rep_globals_safe global_items )) (PreH8 : (retval = (cm_rep_globals_size (global_items)))) (PreH9 : (0 <= retval)) (PreH10 : (retval <= 1048560)) (PreH11 : (0 <= index_pre)) (PreH12 : (cm_rep_globals_safe global_items )) (PreH13 : (cm_rep_strings_safe string_items )) (PreH14 : (((cm_rep_globals_size (global_items)) + (cm_rep_strings_size (string_items)) ) <= 1048560)) ,
  (((16 + retval ) + retval_2 ) = (cm_rep_string_address (global_items) (string_items) (index_pre)))
.

Definition cmc_string_address_partial_solve_wit_1_pure := 
forall (index_pre: Z) (strings_pre: Z) (globals_pre: Z) (string_items: (@list cm_string_d)) (global_items: (@list cm_global_d)) (PreH1 : (0 <= index_pre)) (PreH2 : (cm_rep_globals_safe global_items )) (PreH3 : (cm_rep_strings_safe string_items )) (PreH4 : (((cm_rep_globals_size (global_items)) + (cm_rep_strings_size (string_items)) ) <= 1048560)) ,
  ((( &( "global_size" ) )) # Int64  |->_)
  **  ((( &( "globals" ) )) # Ptr  |-> globals_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  (cm_global_list_rep globals_pre global_items )
  **  (cm_string_list_rep strings_pre string_items )
|--
  “ (cm_rep_globals_safe global_items ) ”
.

Definition cmc_string_address_partial_solve_wit_1_aux := 
forall (index_pre: Z) (strings_pre: Z) (globals_pre: Z) (string_items: (@list cm_string_d)) (global_items: (@list cm_global_d)) (PreH1 : (0 <= index_pre)) (PreH2 : (cm_rep_globals_safe global_items )) (PreH3 : (cm_rep_strings_safe string_items )) (PreH4 : (((cm_rep_globals_size (global_items)) + (cm_rep_strings_size (string_items)) ) <= 1048560)) ,
  (cm_global_list_rep globals_pre global_items )
  **  (cm_string_list_rep strings_pre string_items )
|--
  “ (cm_rep_globals_safe global_items ) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_globals_safe global_items ) ” 
  &&  “ (cm_rep_strings_safe string_items ) ” 
  &&  “ (((cm_rep_globals_size (global_items)) + (cm_rep_strings_size (string_items)) ) <= 1048560) ”
  &&  (cm_global_list_rep globals_pre global_items )
  **  (cm_string_list_rep strings_pre string_items )
.

Definition cmc_string_address_partial_solve_wit_1 := cmc_string_address_partial_solve_wit_1_pure -> cmc_string_address_partial_solve_wit_1_aux.

Definition cmc_string_address_partial_solve_wit_2_pure := 
forall (index_pre: Z) (strings_pre: Z) (globals_pre: Z) (string_items: (@list cm_string_d)) (global_items: (@list cm_global_d)) (retval: Z) (PreH1 : (cm_rep_globals_safe global_items )) (PreH2 : (retval = (cm_rep_globals_size (global_items)))) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1048560)) (PreH5 : (0 <= index_pre)) (PreH6 : (cm_rep_globals_safe global_items )) (PreH7 : (cm_rep_strings_safe string_items )) (PreH8 : (((cm_rep_globals_size (global_items)) + (cm_rep_strings_size (string_items)) ) <= 1048560)) ,
  ((( &( "prefix" ) )) # Int64  |->_)
  **  (cm_global_list_rep globals_pre global_items )
  **  ((( &( "global_size" ) )) # Int64  |-> retval)
  **  ((( &( "globals" ) )) # Ptr  |-> globals_pre)
  **  ((( &( "strings" ) )) # Ptr  |-> strings_pre)
  **  ((( &( "index" ) )) # Int  |-> index_pre)
  **  (cm_string_list_rep strings_pre string_items )
|--
  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_strings_safe string_items ) ”
.

Definition cmc_string_address_partial_solve_wit_2_aux := 
forall (index_pre: Z) (strings_pre: Z) (globals_pre: Z) (string_items: (@list cm_string_d)) (global_items: (@list cm_global_d)) (retval: Z) (PreH1 : (cm_rep_globals_safe global_items )) (PreH2 : (retval = (cm_rep_globals_size (global_items)))) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1048560)) (PreH5 : (0 <= index_pre)) (PreH6 : (cm_rep_globals_safe global_items )) (PreH7 : (cm_rep_strings_safe string_items )) (PreH8 : (((cm_rep_globals_size (global_items)) + (cm_rep_strings_size (string_items)) ) <= 1048560)) ,
  (cm_global_list_rep globals_pre global_items )
  **  (cm_string_list_rep strings_pre string_items )
|--
  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_strings_safe string_items ) ” 
  &&  “ (cm_rep_globals_safe global_items ) ” 
  &&  “ (retval = (cm_rep_globals_size (global_items))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1048560) ” 
  &&  “ (0 <= index_pre) ” 
  &&  “ (cm_rep_globals_safe global_items ) ” 
  &&  “ (cm_rep_strings_safe string_items ) ” 
  &&  “ (((cm_rep_globals_size (global_items)) + (cm_rep_strings_size (string_items)) ) <= 1048560) ”
  &&  (cm_string_list_rep strings_pre string_items )
  **  (cm_global_list_rep globals_pre global_items )
.

Definition cmc_string_address_partial_solve_wit_2 := cmc_string_address_partial_solve_wit_2_pure -> cmc_string_address_partial_solve_wit_2_aux.

(*----- Function cmc_binding_array_value -----*)

Definition cmc_binding_array_value_safety_wit_1 := 
forall (array_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (zl: Z) (zg: Z) (locals: (@list cm_slot_d)) (globals: (@list cm_global_d)) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= slot_pre)) (PreH2 : (globals = (cm_program_globals (p)))) (PreH3 : (locals = (cm_function_locals (f)))) (PreH4 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH5 : (cm_binding_valid p f scope_pre slot_pre )) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "scope" ) )) # Int  |-> scope_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "array" ) )) # Ptr  |-> array_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  (cm_global_list_rep zg globals )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl locals )
  **  ((array_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_binding_array_value_safety_wit_2 := 
forall (array_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (zl: Z) (zg: Z) (locals: (@list cm_slot_d)) (globals: (@list cm_global_d)) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (scope_pre <> 0)) (PreH2 : (0 <= slot_pre)) (PreH3 : (globals = (cm_program_globals (p)))) (PreH4 : (locals = (cm_function_locals (f)))) (PreH5 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH6 : (cm_binding_valid p f scope_pre slot_pre )) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "scope" ) )) # Int  |-> scope_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "array" ) )) # Ptr  |-> array_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  (cm_global_list_rep zg globals )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl locals )
  **  ((array_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmc_binding_array_value_safety_wit_3 := 
forall (array_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (zl: Z) (zg: Z) (locals: (@list cm_slot_d)) (globals: (@list cm_global_d)) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (scope_pre <> 1)) (PreH2 : (scope_pre <> 0)) (PreH3 : (0 <= slot_pre)) (PreH4 : (globals = (cm_program_globals (p)))) (PreH5 : (locals = (cm_function_locals (f)))) (PreH6 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH7 : (cm_binding_valid p f scope_pre slot_pre )) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "scope" ) )) # Int  |-> scope_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "array" ) )) # Ptr  |-> array_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  (cm_global_list_rep zg globals )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl locals )
  **  ((array_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_binding_array_value_return_wit_1 := 
(
forall (array_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (zl: Z) (zg: Z) (locals: (@list cm_slot_d)) (globals: (@list cm_global_d)) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (0 <= slot_pre)) (PreH2 : (retval = (cm_rep_global_array ((cm_program_globals (p))) (slot_pre)))) (PreH3 : (scope_pre = 0)) (PreH4 : (0 <= slot_pre)) (PreH5 : (globals = (cm_program_globals (p)))) (PreH6 : (locals = (cm_function_locals (f)))) (PreH7 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH8 : (cm_binding_valid p f scope_pre slot_pre )) ,
  (cm_global_list_rep zg (cm_program_globals (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl locals )
  **  ((array_pre) # Int  |-> retval)
|--
  “ (0 <= slot_pre) ” 
  &&  “ (globals = (cm_program_globals (p))) ” 
  &&  “ (locals = (cm_function_locals (f))) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_binding_valid p f scope_pre slot_pre ) ”
  &&  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  (cm_global_list_rep zg globals )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl locals )
  **  ((array_pre) # Int  |-> (cm_binding_array_code (policy) (p) (fid_pre) (scope_pre) (slot_pre)))
) \/
(
forall (slot_pre: Z) (scope_pre: Z) (fid_pre: Z) (locals: (@list cm_slot_d)) (globals: (@list cm_global_d)) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (0 <= slot_pre)) (PreH2 : (retval = (cm_rep_global_array ((cm_program_globals (p))) (slot_pre)))) (PreH3 : (scope_pre = 0)) (PreH4 : (0 <= slot_pre)) (PreH5 : (globals = (cm_program_globals (p)))) (PreH6 : (locals = (cm_function_locals (f)))) (PreH7 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH8 : (cm_binding_valid p f scope_pre slot_pre )) ,
  TT && emp 
|--
  “ (retval = (cm_binding_array_code (policy) (p) (fid_pre) (0) (slot_pre))) ”
  &&  emp
).

Definition cmc_binding_array_value_return_wit_1_split_goal_1 := 
forall (slot_pre: Z) (scope_pre: Z) (fid_pre: Z) (locals: (@list cm_slot_d)) (globals: (@list cm_global_d)) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (0 <= slot_pre)) (PreH2 : (retval = (cm_rep_global_array ((cm_program_globals (p))) (slot_pre)))) (PreH3 : (scope_pre = 0)) (PreH4 : (0 <= slot_pre)) (PreH5 : (globals = (cm_program_globals (p)))) (PreH6 : (locals = (cm_function_locals (f)))) (PreH7 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH8 : (cm_binding_valid p f scope_pre slot_pre )) ,
  (retval = (cm_binding_array_code (policy) (p) (fid_pre) (0) (slot_pre)))
.

Definition cmc_binding_array_value_return_wit_2 := 
(
forall (array_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (zl: Z) (zg: Z) (locals: (@list cm_slot_d)) (globals: (@list cm_global_d)) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (0 <= slot_pre)) (PreH2 : (retval = (cm_rep_member_array ((cm_function_locals ((cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))))) (slot_pre)))) (PreH3 : (scope_pre = 1)) (PreH4 : (scope_pre <> 0)) (PreH5 : (0 <= slot_pre)) (PreH6 : (globals = (cm_program_globals (p)))) (PreH7 : (locals = (cm_function_locals (f)))) (PreH8 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH9 : (cm_binding_valid p f scope_pre slot_pre )) ,
  (cm_slot_list_rep zl (cm_function_locals ((cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  (cm_global_list_rep zg globals )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((array_pre) # Int  |-> retval)
|--
  “ (0 <= slot_pre) ” 
  &&  “ (globals = (cm_program_globals (p))) ” 
  &&  “ (locals = (cm_function_locals (f))) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_binding_valid p f scope_pre slot_pre ) ”
  &&  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  (cm_global_list_rep zg globals )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl locals )
  **  ((array_pre) # Int  |-> (cm_binding_array_code (policy) (p) (fid_pre) (scope_pre) (slot_pre)))
) \/
(
forall (slot_pre: Z) (scope_pre: Z) (fid_pre: Z) (locals: (@list cm_slot_d)) (globals: (@list cm_global_d)) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (0 <= slot_pre)) (PreH2 : (retval = (cm_rep_member_array ((cm_function_locals ((cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))))) (slot_pre)))) (PreH3 : (scope_pre = 1)) (PreH4 : (scope_pre <> 0)) (PreH5 : (0 <= slot_pre)) (PreH6 : (globals = (cm_program_globals (p)))) (PreH7 : (locals = (cm_function_locals (f)))) (PreH8 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH9 : (cm_binding_valid p f scope_pre slot_pre )) ,
  TT && emp 
|--
  “ (retval = (cm_binding_array_code (policy) (p) (fid_pre) (1) (slot_pre))) ”
  &&  emp
).

Definition cmc_binding_array_value_return_wit_2_split_goal_1 := 
forall (slot_pre: Z) (scope_pre: Z) (fid_pre: Z) (locals: (@list cm_slot_d)) (globals: (@list cm_global_d)) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (retval: Z) (PreH1 : (0 <= slot_pre)) (PreH2 : (retval = (cm_rep_member_array ((cm_function_locals ((cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))))) (slot_pre)))) (PreH3 : (scope_pre = 1)) (PreH4 : (scope_pre <> 0)) (PreH5 : (0 <= slot_pre)) (PreH6 : (globals = (cm_program_globals (p)))) (PreH7 : (locals = (cm_function_locals (f)))) (PreH8 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH9 : (cm_binding_valid p f scope_pre slot_pre )) ,
  (retval = (cm_binding_array_code (policy) (p) (fid_pre) (1) (slot_pre)))
.

Definition cmc_binding_array_value_return_wit_3 := 
(
forall (array_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (zl: Z) (zg: Z) (locals: (@list cm_slot_d)) (globals: (@list cm_global_d)) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (scope_pre <> 1)) (PreH2 : (scope_pre <> 0)) (PreH3 : (0 <= slot_pre)) (PreH4 : (globals = (cm_program_globals (p)))) (PreH5 : (locals = (cm_function_locals (f)))) (PreH6 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH7 : (cm_binding_valid p f scope_pre slot_pre )) ,
  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  (cm_global_list_rep zg globals )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl locals )
  **  ((array_pre) # Int  |-> 0)
|--
  “ (0 <= slot_pre) ” 
  &&  “ (globals = (cm_program_globals (p))) ” 
  &&  “ (locals = (cm_function_locals (f))) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_binding_valid p f scope_pre slot_pre ) ”
  &&  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  (cm_global_list_rep zg globals )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl locals )
  **  ((array_pre) # Int  |-> (cm_binding_array_code (policy) (p) (fid_pre) (scope_pre) (slot_pre)))
) \/
(
forall (slot_pre: Z) (scope_pre: Z) (fid_pre: Z) (locals: (@list cm_slot_d)) (globals: (@list cm_global_d)) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (scope_pre <> 1)) (PreH2 : (scope_pre <> 0)) (PreH3 : (0 <= slot_pre)) (PreH4 : (globals = (cm_program_globals (p)))) (PreH5 : (locals = (cm_function_locals (f)))) (PreH6 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH7 : (cm_binding_valid p f scope_pre slot_pre )) ,
  TT && emp 
|--
  “ (0 = (cm_binding_array_code (policy) (p) (fid_pre) (scope_pre) (slot_pre))) ”
  &&  emp
).

Definition cmc_binding_array_value_return_wit_3_split_goal_1 := 
forall (slot_pre: Z) (scope_pre: Z) (fid_pre: Z) (locals: (@list cm_slot_d)) (globals: (@list cm_global_d)) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (scope_pre <> 1)) (PreH2 : (scope_pre <> 0)) (PreH3 : (0 <= slot_pre)) (PreH4 : (globals = (cm_program_globals (p)))) (PreH5 : (locals = (cm_function_locals (f)))) (PreH6 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH7 : (cm_binding_valid p f scope_pre slot_pre )) ,
  (0 = (cm_binding_array_code (policy) (p) (fid_pre) (scope_pre) (slot_pre)))
.

Definition cmc_binding_array_value_partial_solve_wit_1_pure := 
forall (array_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (zl: Z) (zg: Z) (locals: (@list cm_slot_d)) (globals: (@list cm_global_d)) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (scope_pre = 0)) (PreH2 : (0 <= slot_pre)) (PreH3 : (globals = (cm_program_globals (p)))) (PreH4 : (locals = (cm_function_locals (f)))) (PreH5 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH6 : (cm_binding_valid p f scope_pre slot_pre )) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "scope" ) )) # Int  |-> scope_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "array" ) )) # Ptr  |-> array_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  (cm_global_list_rep zg globals )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl locals )
  **  ((array_pre) # Int  |->_)
|--
  “ (0 <= slot_pre) ”
.

Definition cmc_binding_array_value_partial_solve_wit_1_aux := 
forall (array_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (zl: Z) (zg: Z) (locals: (@list cm_slot_d)) (globals: (@list cm_global_d)) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (scope_pre = 0)) (PreH2 : (0 <= slot_pre)) (PreH3 : (globals = (cm_program_globals (p)))) (PreH4 : (locals = (cm_function_locals (f)))) (PreH5 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH6 : (cm_binding_valid p f scope_pre slot_pre )) ,
  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  (cm_global_list_rep zg globals )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl locals )
  **  ((array_pre) # Int  |->_)
|--
  “ (0 <= slot_pre) ” 
  &&  “ (scope_pre = 0) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ (globals = (cm_program_globals (p))) ” 
  &&  “ (locals = (cm_function_locals (f))) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_binding_valid p f scope_pre slot_pre ) ”
  &&  (cm_global_list_rep zg (cm_program_globals (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl locals )
  **  ((array_pre) # Int  |->_)
.

Definition cmc_binding_array_value_partial_solve_wit_1 := cmc_binding_array_value_partial_solve_wit_1_pure -> cmc_binding_array_value_partial_solve_wit_1_aux.

Definition cmc_binding_array_value_partial_solve_wit_2_pure := 
forall (array_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (zl: Z) (zg: Z) (locals: (@list cm_slot_d)) (globals: (@list cm_global_d)) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (scope_pre = 1)) (PreH2 : (scope_pre <> 0)) (PreH3 : (0 <= slot_pre)) (PreH4 : (globals = (cm_program_globals (p)))) (PreH5 : (locals = (cm_function_locals (f)))) (PreH6 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH7 : (cm_binding_valid p f scope_pre slot_pre )) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "scope" ) )) # Int  |-> scope_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((( &( "array" ) )) # Ptr  |-> array_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  (cm_global_list_rep zg globals )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl locals )
  **  ((array_pre) # Int  |->_)
|--
  “ (0 <= slot_pre) ”
.

Definition cmc_binding_array_value_partial_solve_wit_2_aux := 
forall (array_pre: Z) (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (zl: Z) (zg: Z) (locals: (@list cm_slot_d)) (globals: (@list cm_global_d)) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (scope_pre = 1)) (PreH2 : (scope_pre <> 0)) (PreH3 : (0 <= slot_pre)) (PreH4 : (globals = (cm_program_globals (p)))) (PreH5 : (locals = (cm_function_locals (f)))) (PreH6 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH7 : (cm_binding_valid p f scope_pre slot_pre )) ,
  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  (cm_global_list_rep zg globals )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl locals )
  **  ((array_pre) # Int  |->_)
|--
  “ (0 <= slot_pre) ” 
  &&  “ (scope_pre = 1) ” 
  &&  “ (scope_pre <> 0) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ (globals = (cm_program_globals (p))) ” 
  &&  “ (locals = (cm_function_locals (f))) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_binding_valid p f scope_pre slot_pre ) ”
  &&  (cm_slot_list_rep zl (cm_function_locals ((cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  (cm_global_list_rep zg globals )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((array_pre) # Int  |->_)
.

Definition cmc_binding_array_value_partial_solve_wit_2 := cmc_binding_array_value_partial_solve_wit_2_pure -> cmc_binding_array_value_partial_solve_wit_2_aux.

(*----- Function cmc_binding_array -----*)

Definition cmc_binding_array_return_wit_1 := 
forall (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (zl: Z) (zg: Z) (locals: (@list cm_slot_d)) (globals: (@list cm_global_d)) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= slot_pre)) (PreH2 : (globals = (cm_program_globals (p)))) (PreH3 : (locals = (cm_function_locals (f)))) (PreH4 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH5 : (cm_binding_valid p f scope_pre slot_pre )) (PreH6 : (0 <= slot_pre)) (PreH7 : (globals = (cm_program_globals (p)))) (PreH8 : (locals = (cm_function_locals (f)))) (PreH9 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH10 : (cm_binding_valid p f scope_pre slot_pre )) ,
  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  (cm_global_list_rep zg globals )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl locals )
|--
  “ (0 <= slot_pre) ” 
  &&  “ (globals = (cm_program_globals (p))) ” 
  &&  “ (locals = (cm_function_locals (f))) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_binding_valid p f scope_pre slot_pre ) ” 
  &&  “ ((cm_binding_array_code (policy) (p) (fid_pre) (scope_pre) (slot_pre)) = (cm_binding_array_code (policy) (p) (fid_pre) (scope_pre) (slot_pre))) ”
  &&  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  (cm_global_list_rep zg globals )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl locals )
.

Definition cmc_binding_array_partial_solve_wit_1_pure := 
forall (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (zl: Z) (zg: Z) (locals: (@list cm_slot_d)) (globals: (@list cm_global_d)) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= slot_pre)) (PreH2 : (globals = (cm_program_globals (p)))) (PreH3 : (locals = (cm_function_locals (f)))) (PreH4 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH5 : (cm_binding_valid p f scope_pre slot_pre )) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "fid" ) )) # Int  |-> fid_pre)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "scope" ) )) # Int  |-> scope_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  (cm_global_list_rep zg globals )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl locals )
|--
  “ (0 <= slot_pre) ” 
  &&  “ (globals = (cm_program_globals (p))) ” 
  &&  “ (locals = (cm_function_locals (f))) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_binding_valid p f scope_pre slot_pre ) ”
.

Definition cmc_binding_array_partial_solve_wit_1_aux := 
forall (slot_pre: Z) (scope_pre: Z) (fn_pre: Z) (fid_pre: Z) (program_pre: Z) (zl: Z) (zg: Z) (locals: (@list cm_slot_d)) (globals: (@list cm_global_d)) (f: cm_function_d) (p: cm_program) (policy: cm_lookup_policy) (PreH1 : (0 <= slot_pre)) (PreH2 : (globals = (cm_program_globals (p)))) (PreH3 : (locals = (cm_function_locals (f)))) (PreH4 : (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p)))))) (PreH5 : (cm_binding_valid p f scope_pre slot_pre )) ,
  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  (cm_global_list_rep zg globals )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl locals )
|--
  “ (0 <= slot_pre) ” 
  &&  “ (globals = (cm_program_globals (p))) ” 
  &&  “ (locals = (cm_function_locals (f))) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_binding_valid p f scope_pre slot_pre ) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ (globals = (cm_program_globals (p))) ” 
  &&  “ (locals = (cm_function_locals (f))) ” 
  &&  “ (f = (cm_function_at (policy) (fid_pre) ((cm_program_functions (p))))) ” 
  &&  “ (cm_binding_valid p f scope_pre slot_pre ) ”
  &&  ((&((program_pre)  # "cm_program" ->ₛ "globals")) # Ptr  |-> zg)
  **  (cm_global_list_rep zg globals )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl locals )
.

Definition cmc_binding_array_partial_solve_wit_1 := cmc_binding_array_partial_solve_wit_1_pure -> cmc_binding_array_partial_solve_wit_1_aux.

(*----- Function cmc_member_array -----*)

Definition cmc_member_array_safety_wit_1 := 
(
forall (mid_pre: Z) (base_ty_pre: Z) (program_pre: Z) (zs: Z) (structs: (@list cm_struct_d)) (base: cm_type) (p: cm_program) (retval: Z) (PreH1 : (retval = (base_ty_pre - 1024 ))) (PreH2 : (1024 <= base_ty_pre)) (PreH3 : (base_ty_pre <= INT_MAX)) (PreH4 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH5 : (0 <= mid_pre)) (PreH6 : (structs = (cm_program_structs (p)))) (PreH7 : (base_ty_pre = (cm_type_encode (base)))) (PreH8 : (cm_type_code_wf base )) (PreH9 : (cm_member_valid p base mid_pre )) (PreH10 : (cm_rep_structs_safe structs )) ,
  ((( &( "sid" ) )) # Int  |->_)
  **  ((( &( "pointee" ) )) # Int  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "base_ty" ) )) # Int  |-> base_ty_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  (cm_struct_list_rep zs structs )
|--
  “ (((retval % ( 1024 ) ) - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((retval % ( 1024 ) ) - 2 )) ”
) \/
(
forall (mid_pre: Z) (base_ty_pre: Z) (program_pre: Z) (zs: Z) (structs: (@list cm_struct_d)) (base: cm_type) (p: cm_program) (retval: Z) (PreH1 : (retval = (base_ty_pre - 1024 ))) (PreH2 : (1024 <= base_ty_pre)) (PreH3 : (base_ty_pre <= INT_MAX)) (PreH4 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH5 : (0 <= mid_pre)) (PreH6 : (structs = (cm_program_structs (p)))) (PreH7 : (base_ty_pre = (cm_type_encode (base)))) (PreH8 : (cm_type_code_wf base )) (PreH9 : (cm_member_valid p base mid_pre )) (PreH10 : (cm_rep_structs_safe structs )) ,
  ((( &( "sid" ) )) # Int  |->_)
  **  ((( &( "pointee" ) )) # Int  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "base_ty" ) )) # Int  |-> base_ty_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  (cm_struct_list_rep zs structs )
|--
  “ (((retval % ( 1024 ) ) - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((retval % ( 1024 ) ) - 2 )) ”
).

Definition cmc_member_array_safety_wit_1_split_goal_1 := 
forall (mid_pre: Z) (base_ty_pre: Z) (program_pre: Z) (zs: Z) (structs: (@list cm_struct_d)) (base: cm_type) (p: cm_program) (retval: Z) (PreH1 : (retval = (base_ty_pre - 1024 ))) (PreH2 : (1024 <= base_ty_pre)) (PreH3 : (base_ty_pre <= INT_MAX)) (PreH4 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH5 : (0 <= mid_pre)) (PreH6 : (structs = (cm_program_structs (p)))) (PreH7 : (base_ty_pre = (cm_type_encode (base)))) (PreH8 : (cm_type_code_wf base )) (PreH9 : (cm_member_valid p base mid_pre )) (PreH10 : (cm_rep_structs_safe structs )) ,
  ((( &( "sid" ) )) # Int  |->_)
  **  ((( &( "pointee" ) )) # Int  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "base_ty" ) )) # Int  |-> base_ty_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  (cm_struct_list_rep zs structs )
|--
  “ (((retval % ( 1024 ) ) - 2 ) <= INT_MAX) ”
.

Definition cmc_member_array_safety_wit_1_split_goal_2 := 
forall (mid_pre: Z) (base_ty_pre: Z) (program_pre: Z) (zs: Z) (structs: (@list cm_struct_d)) (base: cm_type) (p: cm_program) (retval: Z) (PreH1 : (retval = (base_ty_pre - 1024 ))) (PreH2 : (1024 <= base_ty_pre)) (PreH3 : (base_ty_pre <= INT_MAX)) (PreH4 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH5 : (0 <= mid_pre)) (PreH6 : (structs = (cm_program_structs (p)))) (PreH7 : (base_ty_pre = (cm_type_encode (base)))) (PreH8 : (cm_type_code_wf base )) (PreH9 : (cm_member_valid p base mid_pre )) (PreH10 : (cm_rep_structs_safe structs )) ,
  ((( &( "sid" ) )) # Int  |->_)
  **  ((( &( "pointee" ) )) # Int  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "base_ty" ) )) # Int  |-> base_ty_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  (cm_struct_list_rep zs structs )
|--
  “ ((INT_MIN) <= ((retval % ( 1024 ) ) - 2 )) ”
.

Definition cmc_member_array_safety_wit_2 := 
forall (mid_pre: Z) (base_ty_pre: Z) (program_pre: Z) (zs: Z) (structs: (@list cm_struct_d)) (base: cm_type) (p: cm_program) (retval: Z) (PreH1 : (retval = (base_ty_pre - 1024 ))) (PreH2 : (1024 <= base_ty_pre)) (PreH3 : (base_ty_pre <= INT_MAX)) (PreH4 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH5 : (0 <= mid_pre)) (PreH6 : (structs = (cm_program_structs (p)))) (PreH7 : (base_ty_pre = (cm_type_encode (base)))) (PreH8 : (cm_type_code_wf base )) (PreH9 : (cm_member_valid p base mid_pre )) (PreH10 : (cm_rep_structs_safe structs )) ,
  ((( &( "sid" ) )) # Int  |->_)
  **  ((( &( "pointee" ) )) # Int  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "base_ty" ) )) # Int  |-> base_ty_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  (cm_struct_list_rep zs structs )
|--
  “ ((retval <> (INT_MIN)) \/ (1024 <> (-1))) ” 
  &&  “ (1024 <> 0) ”
.

Definition cmc_member_array_safety_wit_3 := 
forall (mid_pre: Z) (base_ty_pre: Z) (program_pre: Z) (zs: Z) (structs: (@list cm_struct_d)) (base: cm_type) (p: cm_program) (retval: Z) (PreH1 : (retval = (base_ty_pre - 1024 ))) (PreH2 : (1024 <= base_ty_pre)) (PreH3 : (base_ty_pre <= INT_MAX)) (PreH4 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH5 : (0 <= mid_pre)) (PreH6 : (structs = (cm_program_structs (p)))) (PreH7 : (base_ty_pre = (cm_type_encode (base)))) (PreH8 : (cm_type_code_wf base )) (PreH9 : (cm_member_valid p base mid_pre )) (PreH10 : (cm_rep_structs_safe structs )) ,
  ((( &( "sid" ) )) # Int  |->_)
  **  ((( &( "pointee" ) )) # Int  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "base_ty" ) )) # Int  |-> base_ty_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  (cm_struct_list_rep zs structs )
|--
  “ (1024 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1024) ”
.

Definition cmc_member_array_safety_wit_4 := 
forall (mid_pre: Z) (base_ty_pre: Z) (program_pre: Z) (zs: Z) (structs: (@list cm_struct_d)) (base: cm_type) (p: cm_program) (retval: Z) (PreH1 : (retval = (base_ty_pre - 1024 ))) (PreH2 : (1024 <= base_ty_pre)) (PreH3 : (base_ty_pre <= INT_MAX)) (PreH4 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH5 : (0 <= mid_pre)) (PreH6 : (structs = (cm_program_structs (p)))) (PreH7 : (base_ty_pre = (cm_type_encode (base)))) (PreH8 : (cm_type_code_wf base )) (PreH9 : (cm_member_valid p base mid_pre )) (PreH10 : (cm_rep_structs_safe structs )) ,
  ((( &( "sid" ) )) # Int  |->_)
  **  ((( &( "pointee" ) )) # Int  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "base_ty" ) )) # Int  |-> base_ty_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  (cm_struct_list_rep zs structs )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition cmc_member_array_return_wit_1 := 
(
forall (mid_pre: Z) (base_ty_pre: Z) (program_pre: Z) (zs: Z) (structs: (@list cm_struct_d)) (base: cm_type) (p: cm_program) (retval_2: Z) (retval: Z) (PreH1 : (0 <= ((retval_2 % ( 1024 ) ) - 2 ))) (PreH2 : (0 <= mid_pre)) (PreH3 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH4 : (retval = (cm_rep_struct_member_array ((cm_program_structs (p))) (((retval_2 % ( 1024 ) ) - 2 )) (mid_pre)))) (PreH5 : (retval_2 = (base_ty_pre - 1024 ))) (PreH6 : (1024 <= base_ty_pre)) (PreH7 : (base_ty_pre <= INT_MAX)) (PreH8 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH9 : (0 <= mid_pre)) (PreH10 : (structs = (cm_program_structs (p)))) (PreH11 : (base_ty_pre = (cm_type_encode (base)))) (PreH12 : (cm_type_code_wf base )) (PreH13 : (cm_member_valid p base mid_pre )) (PreH14 : (cm_rep_structs_safe structs )) ,
  (cm_struct_list_rep zs (cm_program_structs (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
|--
  “ (1024 <= base_ty_pre) ” 
  &&  “ (base_ty_pre <= INT_MAX) ” 
  &&  “ (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 )) ” 
  &&  “ (0 <= mid_pre) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (base_ty_pre = (cm_type_encode (base))) ” 
  &&  “ (cm_type_code_wf base ) ” 
  &&  “ (cm_member_valid p base mid_pre ) ” 
  &&  “ (cm_rep_structs_safe structs ) ” 
  &&  “ (retval = (cm_member_array_code (p) (base) (mid_pre))) ”
  &&  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  (cm_struct_list_rep zs structs )
) \/
(
forall (mid_pre: Z) (base_ty_pre: Z) (structs: (@list cm_struct_d)) (base: cm_type) (p: cm_program) (retval_2: Z) (retval: Z) (PreH1 : (0 <= ((retval_2 % ( 1024 ) ) - 2 ))) (PreH2 : (0 <= mid_pre)) (PreH3 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH4 : (retval = (cm_rep_struct_member_array ((cm_program_structs (p))) (((retval_2 % ( 1024 ) ) - 2 )) (mid_pre)))) (PreH5 : (retval_2 = (base_ty_pre - 1024 ))) (PreH6 : (1024 <= base_ty_pre)) (PreH7 : (base_ty_pre <= INT_MAX)) (PreH8 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH9 : (0 <= mid_pre)) (PreH10 : (structs = (cm_program_structs (p)))) (PreH11 : (base_ty_pre = (cm_type_encode (base)))) (PreH12 : (cm_type_code_wf base )) (PreH13 : (cm_member_valid p base mid_pre )) (PreH14 : (cm_rep_structs_safe structs )) ,
  TT && emp 
|--
  “ ((cm_rep_struct_member_array (structs) ((((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 )) (mid_pre)) = (cm_member_array_code (p) (base) (mid_pre))) ”
  &&  emp
).

Definition cmc_member_array_return_wit_1_split_goal_1 := 
forall (mid_pre: Z) (base_ty_pre: Z) (structs: (@list cm_struct_d)) (base: cm_type) (p: cm_program) (retval_2: Z) (retval: Z) (PreH1 : (0 <= ((retval_2 % ( 1024 ) ) - 2 ))) (PreH2 : (0 <= mid_pre)) (PreH3 : (cm_rep_structs_safe (cm_program_structs (p)) )) (PreH4 : (retval = (cm_rep_struct_member_array ((cm_program_structs (p))) (((retval_2 % ( 1024 ) ) - 2 )) (mid_pre)))) (PreH5 : (retval_2 = (base_ty_pre - 1024 ))) (PreH6 : (1024 <= base_ty_pre)) (PreH7 : (base_ty_pre <= INT_MAX)) (PreH8 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH9 : (0 <= mid_pre)) (PreH10 : (structs = (cm_program_structs (p)))) (PreH11 : (base_ty_pre = (cm_type_encode (base)))) (PreH12 : (cm_type_code_wf base )) (PreH13 : (cm_member_valid p base mid_pre )) (PreH14 : (cm_rep_structs_safe structs )) ,
  ((cm_rep_struct_member_array (structs) ((((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 )) (mid_pre)) = (cm_member_array_code (p) (base) (mid_pre)))
.

Definition cmc_member_array_partial_solve_wit_1_pure := 
forall (mid_pre: Z) (base_ty_pre: Z) (program_pre: Z) (zs: Z) (structs: (@list cm_struct_d)) (base: cm_type) (p: cm_program) (PreH1 : (1024 <= base_ty_pre)) (PreH2 : (base_ty_pre <= INT_MAX)) (PreH3 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH4 : (0 <= mid_pre)) (PreH5 : (structs = (cm_program_structs (p)))) (PreH6 : (base_ty_pre = (cm_type_encode (base)))) (PreH7 : (cm_type_code_wf base )) (PreH8 : (cm_member_valid p base mid_pre )) (PreH9 : (cm_rep_structs_safe structs )) ,
  ((( &( "pointee" ) )) # Int  |->_)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "base_ty" ) )) # Int  |-> base_ty_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  (cm_struct_list_rep zs structs )
|--
  “ (1024 <= base_ty_pre) ” 
  &&  “ (base_ty_pre <= INT_MAX) ”
.

Definition cmc_member_array_partial_solve_wit_1_aux := 
forall (mid_pre: Z) (base_ty_pre: Z) (program_pre: Z) (zs: Z) (structs: (@list cm_struct_d)) (base: cm_type) (p: cm_program) (PreH1 : (1024 <= base_ty_pre)) (PreH2 : (base_ty_pre <= INT_MAX)) (PreH3 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH4 : (0 <= mid_pre)) (PreH5 : (structs = (cm_program_structs (p)))) (PreH6 : (base_ty_pre = (cm_type_encode (base)))) (PreH7 : (cm_type_code_wf base )) (PreH8 : (cm_member_valid p base mid_pre )) (PreH9 : (cm_rep_structs_safe structs )) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  (cm_struct_list_rep zs structs )
|--
  “ (1024 <= base_ty_pre) ” 
  &&  “ (base_ty_pre <= INT_MAX) ” 
  &&  “ (1024 <= base_ty_pre) ” 
  &&  “ (base_ty_pre <= INT_MAX) ” 
  &&  “ (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 )) ” 
  &&  “ (0 <= mid_pre) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (base_ty_pre = (cm_type_encode (base))) ” 
  &&  “ (cm_type_code_wf base ) ” 
  &&  “ (cm_member_valid p base mid_pre ) ” 
  &&  “ (cm_rep_structs_safe structs ) ”
  &&  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  (cm_struct_list_rep zs structs )
.

Definition cmc_member_array_partial_solve_wit_1 := cmc_member_array_partial_solve_wit_1_pure -> cmc_member_array_partial_solve_wit_1_aux.

Definition cmc_member_array_partial_solve_wit_2_pure := 
forall (mid_pre: Z) (base_ty_pre: Z) (program_pre: Z) (zs: Z) (structs: (@list cm_struct_d)) (base: cm_type) (p: cm_program) (retval: Z) (PreH1 : (retval = (base_ty_pre - 1024 ))) (PreH2 : (1024 <= base_ty_pre)) (PreH3 : (base_ty_pre <= INT_MAX)) (PreH4 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH5 : (0 <= mid_pre)) (PreH6 : (structs = (cm_program_structs (p)))) (PreH7 : (base_ty_pre = (cm_type_encode (base)))) (PreH8 : (cm_type_code_wf base )) (PreH9 : (cm_member_valid p base mid_pre )) (PreH10 : (cm_rep_structs_safe structs )) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "sid" ) )) # Int  |-> ((retval % ( 1024 ) ) - 2 ))
  **  ((( &( "pointee" ) )) # Int  |-> retval)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "base_ty" ) )) # Int  |-> base_ty_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  (cm_struct_list_rep zs structs )
|--
  “ (0 <= ((retval % ( 1024 ) ) - 2 )) ” 
  &&  “ (0 <= mid_pre) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ”
.

Definition cmc_member_array_partial_solve_wit_2_aux := 
forall (mid_pre: Z) (base_ty_pre: Z) (program_pre: Z) (zs: Z) (structs: (@list cm_struct_d)) (base: cm_type) (p: cm_program) (retval: Z) (PreH1 : (retval = (base_ty_pre - 1024 ))) (PreH2 : (1024 <= base_ty_pre)) (PreH3 : (base_ty_pre <= INT_MAX)) (PreH4 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH5 : (0 <= mid_pre)) (PreH6 : (structs = (cm_program_structs (p)))) (PreH7 : (base_ty_pre = (cm_type_encode (base)))) (PreH8 : (cm_type_code_wf base )) (PreH9 : (cm_member_valid p base mid_pre )) (PreH10 : (cm_rep_structs_safe structs )) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  (cm_struct_list_rep zs structs )
|--
  “ (0 <= ((retval % ( 1024 ) ) - 2 )) ” 
  &&  “ (0 <= mid_pre) ” 
  &&  “ (cm_rep_structs_safe (cm_program_structs (p)) ) ” 
  &&  “ (retval = (base_ty_pre - 1024 )) ” 
  &&  “ (1024 <= base_ty_pre) ” 
  &&  “ (base_ty_pre <= INT_MAX) ” 
  &&  “ (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 )) ” 
  &&  “ (0 <= mid_pre) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (base_ty_pre = (cm_type_encode (base))) ” 
  &&  “ (cm_type_code_wf base ) ” 
  &&  “ (cm_member_valid p base mid_pre ) ” 
  &&  “ (cm_rep_structs_safe structs ) ”
  &&  (cm_struct_list_rep zs (cm_program_structs (p)) )
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
.

Definition cmc_member_array_partial_solve_wit_2 := cmc_member_array_partial_solve_wit_2_pure -> cmc_member_array_partial_solve_wit_2_aux.

(*----- Function cmc_member_array_value -----*)

Definition cmc_member_array_value_return_wit_1 := 
forall (array_pre: Z) (mid_pre: Z) (base_ty_pre: Z) (program_pre: Z) (zs: Z) (structs: (@list cm_struct_d)) (base: cm_type) (p: cm_program) (retval: Z) (PreH1 : (1024 <= base_ty_pre)) (PreH2 : (base_ty_pre <= INT_MAX)) (PreH3 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH4 : (0 <= mid_pre)) (PreH5 : (structs = (cm_program_structs (p)))) (PreH6 : (base_ty_pre = (cm_type_encode (base)))) (PreH7 : (cm_type_code_wf base )) (PreH8 : (cm_member_valid p base mid_pre )) (PreH9 : (cm_rep_structs_safe structs )) (PreH10 : (retval = (cm_member_array_code (p) (base) (mid_pre)))) (PreH11 : (1024 <= base_ty_pre)) (PreH12 : (base_ty_pre <= INT_MAX)) (PreH13 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH14 : (0 <= mid_pre)) (PreH15 : (structs = (cm_program_structs (p)))) (PreH16 : (base_ty_pre = (cm_type_encode (base)))) (PreH17 : (cm_type_code_wf base )) (PreH18 : (cm_member_valid p base mid_pre )) (PreH19 : (cm_rep_structs_safe structs )) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  (cm_struct_list_rep zs structs )
  **  ((array_pre) # Int  |-> retval)
|--
  “ (1024 <= base_ty_pre) ” 
  &&  “ (base_ty_pre <= INT_MAX) ” 
  &&  “ (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 )) ” 
  &&  “ (0 <= mid_pre) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (base_ty_pre = (cm_type_encode (base))) ” 
  &&  “ (cm_type_code_wf base ) ” 
  &&  “ (cm_member_valid p base mid_pre ) ” 
  &&  “ (cm_rep_structs_safe structs ) ”
  &&  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  (cm_struct_list_rep zs structs )
  **  ((array_pre) # Int  |-> (cm_member_array_code (p) (base) (mid_pre)))
.

Definition cmc_member_array_value_partial_solve_wit_1_pure := 
forall (array_pre: Z) (mid_pre: Z) (base_ty_pre: Z) (program_pre: Z) (zs: Z) (structs: (@list cm_struct_d)) (base: cm_type) (p: cm_program) (PreH1 : (1024 <= base_ty_pre)) (PreH2 : (base_ty_pre <= INT_MAX)) (PreH3 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH4 : (0 <= mid_pre)) (PreH5 : (structs = (cm_program_structs (p)))) (PreH6 : (base_ty_pre = (cm_type_encode (base)))) (PreH7 : (cm_type_code_wf base )) (PreH8 : (cm_member_valid p base mid_pre )) (PreH9 : (cm_rep_structs_safe structs )) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "program" ) )) # Ptr  |-> program_pre)
  **  ((( &( "base_ty" ) )) # Int  |-> base_ty_pre)
  **  ((( &( "mid" ) )) # Int  |-> mid_pre)
  **  ((( &( "array" ) )) # Ptr  |-> array_pre)
  **  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  (cm_struct_list_rep zs structs )
  **  ((array_pre) # Int  |->_)
|--
  “ (1024 <= base_ty_pre) ” 
  &&  “ (base_ty_pre <= INT_MAX) ” 
  &&  “ (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 )) ” 
  &&  “ (0 <= mid_pre) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (base_ty_pre = (cm_type_encode (base))) ” 
  &&  “ (cm_type_code_wf base ) ” 
  &&  “ (cm_member_valid p base mid_pre ) ” 
  &&  “ (cm_rep_structs_safe structs ) ”
.

Definition cmc_member_array_value_partial_solve_wit_1_aux := 
forall (array_pre: Z) (mid_pre: Z) (base_ty_pre: Z) (program_pre: Z) (zs: Z) (structs: (@list cm_struct_d)) (base: cm_type) (p: cm_program) (PreH1 : (1024 <= base_ty_pre)) (PreH2 : (base_ty_pre <= INT_MAX)) (PreH3 : (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 ))) (PreH4 : (0 <= mid_pre)) (PreH5 : (structs = (cm_program_structs (p)))) (PreH6 : (base_ty_pre = (cm_type_encode (base)))) (PreH7 : (cm_type_code_wf base )) (PreH8 : (cm_member_valid p base mid_pre )) (PreH9 : (cm_rep_structs_safe structs )) ,
  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  (cm_struct_list_rep zs structs )
  **  ((array_pre) # Int  |->_)
|--
  “ (1024 <= base_ty_pre) ” 
  &&  “ (base_ty_pre <= INT_MAX) ” 
  &&  “ (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 )) ” 
  &&  “ (0 <= mid_pre) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (base_ty_pre = (cm_type_encode (base))) ” 
  &&  “ (cm_type_code_wf base ) ” 
  &&  “ (cm_member_valid p base mid_pre ) ” 
  &&  “ (cm_rep_structs_safe structs ) ” 
  &&  “ (1024 <= base_ty_pre) ” 
  &&  “ (base_ty_pre <= INT_MAX) ” 
  &&  “ (0 <= (((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 )) ” 
  &&  “ (0 <= mid_pre) ” 
  &&  “ (structs = (cm_program_structs (p))) ” 
  &&  “ (base_ty_pre = (cm_type_encode (base))) ” 
  &&  “ (cm_type_code_wf base ) ” 
  &&  “ (cm_member_valid p base mid_pre ) ” 
  &&  “ (cm_rep_structs_safe structs ) ”
  &&  ((&((program_pre)  # "cm_program" ->ₛ "structs")) # Ptr  |-> zs)
  **  (cm_struct_list_rep zs structs )
  **  ((array_pre) # Int  |->_)
.

Definition cmc_member_array_value_partial_solve_wit_1 := cmc_member_array_value_partial_solve_wit_1_pure -> cmc_member_array_value_partial_solve_wit_1_aux.

(*----- Function cm_args_length -----*)

Definition cm_args_length_safety_wit_1 := 
forall (arg_pre: Z) (args: (@list cm_expr)) (PreH1 : (cm_rep_args_safe args )) ,
  ((( &( "count" ) )) # Int  |->_)
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  (cm_arg_list_rep arg_pre args )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_args_length_safety_wit_2 := 
forall (arg_pre: Z) (args: (@list cm_expr)) (PreH1 : (arg_pre = 0)) (PreH2 : (cm_rep_args_safe args )) ,
  ((( &( "count" ) )) # Int  |->_)
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  (cm_arg_list_rep arg_pre args )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_args_length_safety_wit_3 := 
(
forall (arg_pre: Z) (args: (@list cm_expr)) (head: cm_expr) (tail: (@list cm_expr)) (ep: Z) (np: Z) (retval: Z) (PreH1 : (cm_rep_args_safe tail )) (PreH2 : (retval = (cm_rep_args_length (tail)))) (PreH3 : (arg_pre <> 0)) (PreH4 : (args = (cons (head) (tail)))) (PreH5 : (cm_rep_args_safe args )) (PreH6 : (cm_rep_args_safe tail )) ,
  (cm_arg_list_rep np tail )
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep head )
  **  ((( &( "count" ) )) # Int  |-> retval)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
) \/
(
forall (arg_pre: Z) (args: (@list cm_expr)) (head: cm_expr) (tail: (@list cm_expr)) (ep: Z) (np: Z) (retval: Z) (PreH1 : (cm_rep_args_safe tail )) (PreH2 : (retval = (cm_rep_args_length (tail)))) (PreH3 : (arg_pre <> 0)) (PreH4 : (args = (cons (head) (tail)))) (PreH5 : (cm_rep_args_safe args )) (PreH6 : (cm_rep_args_safe tail )) ,
  (cm_arg_list_rep np tail )
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep head )
  **  ((( &( "count" ) )) # Int  |-> retval)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
).

Definition cm_args_length_safety_wit_3_split_goal_1 := 
forall (arg_pre: Z) (args: (@list cm_expr)) (head: cm_expr) (tail: (@list cm_expr)) (ep: Z) (np: Z) (retval: Z) (PreH1 : (cm_rep_args_safe tail )) (PreH2 : (retval = (cm_rep_args_length (tail)))) (PreH3 : (arg_pre <> 0)) (PreH4 : (args = (cons (head) (tail)))) (PreH5 : (cm_rep_args_safe args )) (PreH6 : (cm_rep_args_safe tail )) ,
  (cm_arg_list_rep np tail )
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep head )
  **  ((( &( "count" ) )) # Int  |-> retval)
|--
  “ ((retval + 1 ) <= INT_MAX) ”
.

Definition cm_args_length_safety_wit_3_split_goal_2 := 
forall (arg_pre: Z) (args: (@list cm_expr)) (head: cm_expr) (tail: (@list cm_expr)) (ep: Z) (np: Z) (retval: Z) (PreH1 : (cm_rep_args_safe tail )) (PreH2 : (retval = (cm_rep_args_length (tail)))) (PreH3 : (arg_pre <> 0)) (PreH4 : (args = (cons (head) (tail)))) (PreH5 : (cm_rep_args_safe args )) (PreH6 : (cm_rep_args_safe tail )) ,
  (cm_arg_list_rep np tail )
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep head )
  **  ((( &( "count" ) )) # Int  |-> retval)
|--
  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition cm_args_length_safety_wit_4 := 
forall (arg_pre: Z) (args: (@list cm_expr)) (head: cm_expr) (tail: (@list cm_expr)) (ep: Z) (np: Z) (retval: Z) (PreH1 : (cm_rep_args_safe tail )) (PreH2 : (retval = (cm_rep_args_length (tail)))) (PreH3 : (arg_pre <> 0)) (PreH4 : (args = (cons (head) (tail)))) (PreH5 : (cm_rep_args_safe args )) (PreH6 : (cm_rep_args_safe tail )) ,
  (cm_arg_list_rep np tail )
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep head )
  **  ((( &( "count" ) )) # Int  |-> retval)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cm_args_length_entail_wit_1 := 
(
forall (arg_pre: Z) (args: (@list cm_expr)) (PreH1 : (arg_pre <> 0)) (PreH2 : (cm_rep_args_safe args )) ,
  (cm_arg_list_rep arg_pre args )
|--
  EX (np: Z)  (ep: Z)  (head: cm_expr)  (tail: (@list cm_expr)) ,
  “ (arg_pre <> 0) ” 
  &&  “ (args = (cons (head) (tail))) ” 
  &&  “ (cm_rep_args_safe args ) ” 
  &&  “ (cm_rep_args_safe tail ) ”
  &&  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep head )
  **  (cm_arg_list_rep np tail )
) \/
(
forall (arg_pre: Z) (args: (@list cm_expr)) (PreH1 : (arg_pre <> 0)) (PreH2 : (cm_rep_args_safe args )) ,
  (cm_arg_list_rep arg_pre args )
|--
  EX (np: Z)  (ep: Z)  (head: cm_expr)  (tail: (@list cm_expr)) ,
  “ (arg_pre <> 0) ” 
  &&  “ (args = (cons (head) (tail))) ” 
  &&  “ (cm_rep_args_safe args ) ” 
  &&  “ (cm_rep_args_safe tail ) ”
  &&  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep head )
  **  (cm_arg_list_rep np tail )
).

Definition cm_args_length_return_wit_1 := 
(
forall (arg_pre: Z) (args: (@list cm_expr)) (PreH1 : (arg_pre = 0)) (PreH2 : (cm_rep_args_safe args )) ,
  (cm_arg_list_rep arg_pre args )
|--
  “ (cm_rep_args_safe args ) ” 
  &&  “ (0 = (cm_rep_args_length (args))) ”
  &&  (cm_arg_list_rep arg_pre args )
) \/
(
forall (arg_pre: Z) (args: (@list cm_expr)) (PreH1 : (arg_pre = 0)) (PreH2 : (cm_rep_args_safe args )) ,
  TT && emp 
|--
  “ (0 = (cm_rep_args_length (args))) ”
  &&  emp
).

Definition cm_args_length_return_wit_1_split_goal_1 := 
forall (arg_pre: Z) (args: (@list cm_expr)) (PreH1 : (arg_pre = 0)) (PreH2 : (cm_rep_args_safe args )) ,
  (0 = (cm_rep_args_length (args)))
.

Definition cm_args_length_return_wit_2 := 
(
forall (arg_pre: Z) (args: (@list cm_expr)) (head: cm_expr) (tail: (@list cm_expr)) (ep: Z) (np: Z) (retval: Z) (PreH1 : (cm_rep_args_safe tail )) (PreH2 : (retval = (cm_rep_args_length (tail)))) (PreH3 : (arg_pre <> 0)) (PreH4 : (args = (cons (head) (tail)))) (PreH5 : (cm_rep_args_safe args )) (PreH6 : (cm_rep_args_safe tail )) ,
  (cm_arg_list_rep np tail )
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep head )
|--
  “ (cm_rep_args_safe args ) ” 
  &&  “ ((retval + 1 ) = (cm_rep_args_length (args))) ”
  &&  (cm_arg_list_rep arg_pre args )
) \/
(
forall (arg_pre: Z) (args: (@list cm_expr)) (head: cm_expr) (tail: (@list cm_expr)) (ep: Z) (np: Z) (retval: Z) (PreH1 : (cm_rep_args_safe tail )) (PreH2 : (retval = (cm_rep_args_length (tail)))) (PreH3 : (arg_pre <> 0)) (PreH4 : (args = (cons (head) (tail)))) (PreH5 : (cm_rep_args_safe args )) (PreH6 : (cm_rep_args_safe tail )) ,
  (cm_arg_list_rep np tail )
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep head )
|--
  “ ((retval + 1 ) = (cm_rep_args_length (args))) ”
  &&  (cm_arg_list_rep arg_pre args )
).

Definition cm_args_length_return_wit_2_split_goal_1 := 
forall (arg_pre: Z) (args: (@list cm_expr)) (head: cm_expr) (tail: (@list cm_expr)) (ep: Z) (np: Z) (retval: Z) (PreH1 : (cm_rep_args_safe tail )) (PreH2 : (retval = (cm_rep_args_length (tail)))) (PreH3 : (arg_pre <> 0)) (PreH4 : (args = (cons (head) (tail)))) (PreH5 : (cm_rep_args_safe args )) (PreH6 : (cm_rep_args_safe tail )) ,
  (cm_arg_list_rep np tail )
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep head )
|--
  “ ((retval + 1 ) = (cm_rep_args_length (args))) ”
.

Definition cm_args_length_return_wit_2_split_goal_spatial := 
forall (arg_pre: Z) (args: (@list cm_expr)) (head: cm_expr) (tail: (@list cm_expr)) (ep: Z) (np: Z) (retval: Z) (PreH1 : (cm_rep_args_safe tail )) (PreH2 : (retval = (cm_rep_args_length (tail)))) (PreH3 : (arg_pre <> 0)) (PreH4 : (args = (cons (head) (tail)))) (PreH5 : (cm_rep_args_safe args )) (PreH6 : (cm_rep_args_safe tail )) ,
  (cm_arg_list_rep np tail )
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep head )
|--
  (cm_arg_list_rep arg_pre args )
.

Definition cm_args_length_partial_solve_wit_1_pure := 
forall (arg_pre: Z) (args: (@list cm_expr)) (head: cm_expr) (tail: (@list cm_expr)) (ep: Z) (np: Z) (PreH1 : (arg_pre <> 0)) (PreH2 : (args = (cons (head) (tail)))) (PreH3 : (cm_rep_args_safe args )) (PreH4 : (cm_rep_args_safe tail )) ,
  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep head )
  **  (cm_arg_list_rep np tail )
  **  ((( &( "count" ) )) # Int  |->_)
|--
  “ (cm_rep_args_safe tail ) ”
.

Definition cm_args_length_partial_solve_wit_1_aux := 
forall (arg_pre: Z) (args: (@list cm_expr)) (head: cm_expr) (tail: (@list cm_expr)) (ep: Z) (np: Z) (PreH1 : (arg_pre <> 0)) (PreH2 : (args = (cons (head) (tail)))) (PreH3 : (cm_rep_args_safe args )) (PreH4 : (cm_rep_args_safe tail )) ,
  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep head )
  **  (cm_arg_list_rep np tail )
|--
  “ (cm_rep_args_safe tail ) ” 
  &&  “ (arg_pre <> 0) ” 
  &&  “ (args = (cons (head) (tail))) ” 
  &&  “ (cm_rep_args_safe args ) ” 
  &&  “ (cm_rep_args_safe tail ) ”
  &&  (cm_arg_list_rep np tail )
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep head )
.

Definition cm_args_length_partial_solve_wit_1 := cm_args_length_partial_solve_wit_1_pure -> cm_args_length_partial_solve_wit_1_aux.

(*----- Function cmc_args_tpair -----*)

Definition cmc_args_tpair_safety_wit_1 := 
forall (depth_pre: Z) (count_pre: Z) (arg_pre: Z) (args: (@list cm_expr)) (PreH1 : (cm_rep_args_temps_safe args )) ,
  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count_pre)
  **  ((( &( "depth" ) )) # Ptr  |-> depth_pre)
  **  (cm_arg_list_rep arg_pre args )
  **  ((count_pre) # Int  |->_)
  **  ((depth_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_args_tpair_safety_wit_2 := 
forall (depth_pre: Z) (count_pre: Z) (arg_pre: Z) (args: (@list cm_expr)) (PreH1 : (arg_pre = 0)) (PreH2 : (cm_rep_args_temps_safe args )) ,
  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count_pre)
  **  ((( &( "depth" ) )) # Ptr  |-> depth_pre)
  **  (cm_arg_list_rep arg_pre args )
  **  ((count_pre) # Int  |->_)
  **  ((depth_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_args_tpair_safety_wit_3 := 
forall (depth_pre: Z) (count_pre: Z) (arg_pre: Z) (args: (@list cm_expr)) (PreH1 : (arg_pre = 0)) (PreH2 : (cm_rep_args_temps_safe args )) ,
  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count_pre)
  **  ((( &( "depth" ) )) # Ptr  |-> depth_pre)
  **  (cm_arg_list_rep arg_pre args )
  **  ((count_pre) # Int  |-> 0)
  **  ((depth_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_args_tpair_safety_wit_4 := 
(
forall (depth_pre: Z) (count_pre: Z) (arg_pre: Z) (args: (@list cm_expr)) (head: cm_expr) (tail: (@list cm_expr)) (ep: Z) (np: Z) (PreH1 : (cm_rep_args_temps_safe tail )) (PreH2 : (cm_rep_expr_temps_safe head )) (PreH3 : (arg_pre <> 0)) (PreH4 : (args = (cons (head) (tail)))) (PreH5 : (cm_rep_args_temps_safe args )) (PreH6 : (cm_rep_args_temps_safe tail )) (PreH7 : (cm_rep_expr_temps_safe head )) ,
  ((( &( "new_count" ) )) # Int  |->_)
  **  (cm_arg_list_rep np tail )
  **  ((( &( "rest_count" ) )) # Int  |-> (cm_acount ((cm_args_apair (tail)))))
  **  ((( &( "rest_depth" ) )) # Int  |-> (cm_adepth ((cm_args_apair (tail)))))
  **  (cm_expr_rep ep head )
  **  ((( &( "child_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (head)))))
  **  ((( &( "child_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (head)))))
  **  ((( &( "child" ) )) # Ptr  |-> ep)
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count_pre)
  **  ((( &( "depth" ) )) # Ptr  |-> depth_pre)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  ((count_pre) # Int  |->_)
  **  ((depth_pre) # Int  |->_)
|--
  “ (((cm_acount ((cm_args_apair (tail)))) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((cm_acount ((cm_args_apair (tail)))) + 1 )) ”
) \/
(
forall (depth_pre: Z) (count_pre: Z) (arg_pre: Z) (args: (@list cm_expr)) (head: cm_expr) (tail: (@list cm_expr)) (ep: Z) (np: Z) (PreH1 : (cm_rep_args_temps_safe tail )) (PreH2 : (cm_rep_expr_temps_safe head )) (PreH3 : (arg_pre <> 0)) (PreH4 : (args = (cons (head) (tail)))) (PreH5 : (cm_rep_args_temps_safe args )) (PreH6 : (cm_rep_args_temps_safe tail )) (PreH7 : (cm_rep_expr_temps_safe head )) ,
  ((( &( "new_count" ) )) # Int  |->_)
  **  (cm_arg_list_rep np tail )
  **  ((( &( "rest_count" ) )) # Int  |-> (cm_acount ((cm_args_apair (tail)))))
  **  ((( &( "rest_depth" ) )) # Int  |-> (cm_adepth ((cm_args_apair (tail)))))
  **  (cm_expr_rep ep head )
  **  ((( &( "child_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (head)))))
  **  ((( &( "child_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (head)))))
  **  ((( &( "child" ) )) # Ptr  |-> ep)
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count_pre)
  **  ((( &( "depth" ) )) # Ptr  |-> depth_pre)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  ((count_pre) # Int  |->_)
  **  ((depth_pre) # Int  |->_)
|--
  “ (((cm_acount ((cm_args_apair (tail)))) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((cm_acount ((cm_args_apair (tail)))) + 1 )) ”
).

Definition cmc_args_tpair_safety_wit_4_split_goal_1 := 
forall (depth_pre: Z) (count_pre: Z) (arg_pre: Z) (args: (@list cm_expr)) (head: cm_expr) (tail: (@list cm_expr)) (ep: Z) (np: Z) (PreH1 : (cm_rep_args_temps_safe tail )) (PreH2 : (cm_rep_expr_temps_safe head )) (PreH3 : (arg_pre <> 0)) (PreH4 : (args = (cons (head) (tail)))) (PreH5 : (cm_rep_args_temps_safe args )) (PreH6 : (cm_rep_args_temps_safe tail )) (PreH7 : (cm_rep_expr_temps_safe head )) ,
  ((( &( "new_count" ) )) # Int  |->_)
  **  (cm_arg_list_rep np tail )
  **  ((( &( "rest_count" ) )) # Int  |-> (cm_acount ((cm_args_apair (tail)))))
  **  ((( &( "rest_depth" ) )) # Int  |-> (cm_adepth ((cm_args_apair (tail)))))
  **  (cm_expr_rep ep head )
  **  ((( &( "child_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (head)))))
  **  ((( &( "child_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (head)))))
  **  ((( &( "child" ) )) # Ptr  |-> ep)
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count_pre)
  **  ((( &( "depth" ) )) # Ptr  |-> depth_pre)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  ((count_pre) # Int  |->_)
  **  ((depth_pre) # Int  |->_)
|--
  “ (((cm_acount ((cm_args_apair (tail)))) + 1 ) <= INT_MAX) ”
.

Definition cmc_args_tpair_safety_wit_4_split_goal_2 := 
forall (depth_pre: Z) (count_pre: Z) (arg_pre: Z) (args: (@list cm_expr)) (head: cm_expr) (tail: (@list cm_expr)) (ep: Z) (np: Z) (PreH1 : (cm_rep_args_temps_safe tail )) (PreH2 : (cm_rep_expr_temps_safe head )) (PreH3 : (arg_pre <> 0)) (PreH4 : (args = (cons (head) (tail)))) (PreH5 : (cm_rep_args_temps_safe args )) (PreH6 : (cm_rep_args_temps_safe tail )) (PreH7 : (cm_rep_expr_temps_safe head )) ,
  ((( &( "new_count" ) )) # Int  |->_)
  **  (cm_arg_list_rep np tail )
  **  ((( &( "rest_count" ) )) # Int  |-> (cm_acount ((cm_args_apair (tail)))))
  **  ((( &( "rest_depth" ) )) # Int  |-> (cm_adepth ((cm_args_apair (tail)))))
  **  (cm_expr_rep ep head )
  **  ((( &( "child_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (head)))))
  **  ((( &( "child_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (head)))))
  **  ((( &( "child" ) )) # Ptr  |-> ep)
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count_pre)
  **  ((( &( "depth" ) )) # Ptr  |-> depth_pre)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  ((count_pre) # Int  |->_)
  **  ((depth_pre) # Int  |->_)
|--
  “ ((INT_MIN) <= ((cm_acount ((cm_args_apair (tail)))) + 1 )) ”
.

Definition cmc_args_tpair_safety_wit_5 := 
forall (depth_pre: Z) (count_pre: Z) (arg_pre: Z) (args: (@list cm_expr)) (head: cm_expr) (tail: (@list cm_expr)) (ep: Z) (np: Z) (PreH1 : (cm_rep_args_temps_safe tail )) (PreH2 : (cm_rep_expr_temps_safe head )) (PreH3 : (arg_pre <> 0)) (PreH4 : (args = (cons (head) (tail)))) (PreH5 : (cm_rep_args_temps_safe args )) (PreH6 : (cm_rep_args_temps_safe tail )) (PreH7 : (cm_rep_expr_temps_safe head )) ,
  ((( &( "new_count" ) )) # Int  |->_)
  **  (cm_arg_list_rep np tail )
  **  ((( &( "rest_count" ) )) # Int  |-> (cm_acount ((cm_args_apair (tail)))))
  **  ((( &( "rest_depth" ) )) # Int  |-> (cm_adepth ((cm_args_apair (tail)))))
  **  (cm_expr_rep ep head )
  **  ((( &( "child_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (head)))))
  **  ((( &( "child_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (head)))))
  **  ((( &( "child" ) )) # Ptr  |-> ep)
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count_pre)
  **  ((( &( "depth" ) )) # Ptr  |-> depth_pre)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  ((count_pre) # Int  |->_)
  **  ((depth_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmc_args_tpair_entail_wit_1 := 
(
forall (depth_pre: Z) (count_pre: Z) (arg_pre: Z) (args: (@list cm_expr)) (PreH1 : (arg_pre <> 0)) (PreH2 : (cm_rep_args_temps_safe args )) ,
  (cm_arg_list_rep arg_pre args )
  **  ((count_pre) # Int  |->_)
  **  ((depth_pre) # Int  |->_)
|--
  EX (np: Z)  (ep: Z)  (head: cm_expr)  (tail: (@list cm_expr)) ,
  “ (arg_pre <> 0) ” 
  &&  “ (args = (cons (head) (tail))) ” 
  &&  “ (cm_rep_args_temps_safe args ) ” 
  &&  “ (cm_rep_args_temps_safe tail ) ” 
  &&  “ (cm_rep_expr_temps_safe head ) ”
  &&  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep head )
  **  (cm_arg_list_rep np tail )
  **  ((count_pre) # Int  |->_)
  **  ((depth_pre) # Int  |->_)
) \/
(
forall (arg_pre: Z) (args: (@list cm_expr)) (PreH1 : (arg_pre <> 0)) (PreH2 : (cm_rep_args_temps_safe args )) ,
  (cm_arg_list_rep arg_pre args )
|--
  EX (np: Z)  (ep: Z)  (head: cm_expr)  (tail: (@list cm_expr)) ,
  “ (arg_pre <> 0) ” 
  &&  “ (args = (cons (head) (tail))) ” 
  &&  “ (cm_rep_args_temps_safe args ) ” 
  &&  “ (cm_rep_args_temps_safe tail ) ” 
  &&  “ (cm_rep_expr_temps_safe head ) ”
  &&  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep head )
  **  (cm_arg_list_rep np tail )
).

Definition cmc_args_tpair_return_wit_1 := 
(
forall (depth_pre: Z) (count_pre: Z) (arg_pre: Z) (args: (@list cm_expr)) (PreH1 : (arg_pre = 0)) (PreH2 : (cm_rep_args_temps_safe args )) ,
  (cm_arg_list_rep arg_pre args )
  **  ((count_pre) # Int  |-> 0)
  **  ((depth_pre) # Int  |-> 0)
|--
  “ (cm_rep_args_temps_safe args ) ”
  &&  (cm_arg_list_rep arg_pre args )
  **  ((count_pre) # Int  |-> (cm_acount ((cm_args_apair (args)))))
  **  ((depth_pre) # Int  |-> (cm_adepth ((cm_args_apair (args)))))
) \/
(
forall (arg_pre: Z) (args: (@list cm_expr)) (PreH1 : (arg_pre = 0)) (PreH2 : (cm_rep_args_temps_safe args )) ,
  TT && emp 
|--
  “ (0 = (cm_acount ((cm_args_apair (args))))) ” 
  &&  “ (0 = (cm_adepth ((cm_args_apair (args))))) ”
  &&  emp
).

Definition cmc_args_tpair_return_wit_1_split_goal_1 := 
forall (arg_pre: Z) (args: (@list cm_expr)) (PreH1 : (arg_pre = 0)) (PreH2 : (cm_rep_args_temps_safe args )) ,
  (0 = (cm_acount ((cm_args_apair (args)))))
.

Definition cmc_args_tpair_return_wit_1_split_goal_2 := 
forall (arg_pre: Z) (args: (@list cm_expr)) (PreH1 : (arg_pre = 0)) (PreH2 : (cm_rep_args_temps_safe args )) ,
  (0 = (cm_adepth ((cm_args_apair (args)))))
.

Definition cmc_args_tpair_return_wit_2 := 
(
forall (depth_pre: Z) (count_pre: Z) (arg_pre: Z) (args: (@list cm_expr)) (head: cm_expr) (tail: (@list cm_expr)) (ep: Z) (np: Z) (retval: Z) (PreH1 : (retval = (cm_imax ((cm_tright ((cm_expr_tpair (head))))) ((cm_adepth ((cm_args_apair (tail)))))))) (PreH2 : (cm_rep_args_temps_safe tail )) (PreH3 : (cm_rep_expr_temps_safe head )) (PreH4 : (arg_pre <> 0)) (PreH5 : (args = (cons (head) (tail)))) (PreH6 : (cm_rep_args_temps_safe args )) (PreH7 : (cm_rep_args_temps_safe tail )) (PreH8 : (cm_rep_expr_temps_safe head )) ,
  (cm_arg_list_rep np tail )
  **  (cm_expr_rep ep head )
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  ((count_pre) # Int  |-> ((cm_acount ((cm_args_apair (tail)))) + 1 ))
  **  ((depth_pre) # Int  |-> retval)
|--
  “ (cm_rep_args_temps_safe args ) ”
  &&  (cm_arg_list_rep arg_pre args )
  **  ((count_pre) # Int  |-> (cm_acount ((cm_args_apair (args)))))
  **  ((depth_pre) # Int  |-> (cm_adepth ((cm_args_apair (args)))))
) \/
(
forall (arg_pre: Z) (args: (@list cm_expr)) (head: cm_expr) (tail: (@list cm_expr)) (ep: Z) (np: Z) (retval: Z) (PreH1 : (retval = (cm_imax ((cm_tright ((cm_expr_tpair (head))))) ((cm_adepth ((cm_args_apair (tail)))))))) (PreH2 : (cm_rep_args_temps_safe tail )) (PreH3 : (cm_rep_expr_temps_safe head )) (PreH4 : (arg_pre <> 0)) (PreH5 : (args = (cons (head) (tail)))) (PreH6 : (cm_rep_args_temps_safe args )) (PreH7 : (cm_rep_args_temps_safe tail )) (PreH8 : (cm_rep_expr_temps_safe head )) ,
  (cm_arg_list_rep np tail )
  **  (cm_expr_rep ep head )
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
|--
  “ (((cm_acount ((cm_args_apair (tail)))) + 1 ) = (cm_acount ((cm_args_apair (args))))) ” 
  &&  “ (retval = (cm_adepth ((cm_args_apair (args))))) ”
  &&  (cm_arg_list_rep arg_pre args )
).

Definition cmc_args_tpair_return_wit_2_split_goal_1 := 
forall (arg_pre: Z) (args: (@list cm_expr)) (head: cm_expr) (tail: (@list cm_expr)) (ep: Z) (np: Z) (retval: Z) (PreH1 : (retval = (cm_imax ((cm_tright ((cm_expr_tpair (head))))) ((cm_adepth ((cm_args_apair (tail)))))))) (PreH2 : (cm_rep_args_temps_safe tail )) (PreH3 : (cm_rep_expr_temps_safe head )) (PreH4 : (arg_pre <> 0)) (PreH5 : (args = (cons (head) (tail)))) (PreH6 : (cm_rep_args_temps_safe args )) (PreH7 : (cm_rep_args_temps_safe tail )) (PreH8 : (cm_rep_expr_temps_safe head )) ,
  (cm_arg_list_rep np tail )
  **  (cm_expr_rep ep head )
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
|--
  “ (((cm_acount ((cm_args_apair (tail)))) + 1 ) = (cm_acount ((cm_args_apair (args))))) ”
.

Definition cmc_args_tpair_return_wit_2_split_goal_2 := 
forall (arg_pre: Z) (args: (@list cm_expr)) (head: cm_expr) (tail: (@list cm_expr)) (ep: Z) (np: Z) (retval: Z) (PreH1 : (retval = (cm_imax ((cm_tright ((cm_expr_tpair (head))))) ((cm_adepth ((cm_args_apair (tail)))))))) (PreH2 : (cm_rep_args_temps_safe tail )) (PreH3 : (cm_rep_expr_temps_safe head )) (PreH4 : (arg_pre <> 0)) (PreH5 : (args = (cons (head) (tail)))) (PreH6 : (cm_rep_args_temps_safe args )) (PreH7 : (cm_rep_args_temps_safe tail )) (PreH8 : (cm_rep_expr_temps_safe head )) ,
  (cm_arg_list_rep np tail )
  **  (cm_expr_rep ep head )
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
|--
  “ (retval = (cm_adepth ((cm_args_apair (args))))) ”
.

Definition cmc_args_tpair_return_wit_2_split_goal_spatial := 
forall (arg_pre: Z) (args: (@list cm_expr)) (head: cm_expr) (tail: (@list cm_expr)) (ep: Z) (np: Z) (retval: Z) (PreH1 : (retval = (cm_imax ((cm_tright ((cm_expr_tpair (head))))) ((cm_adepth ((cm_args_apair (tail)))))))) (PreH2 : (cm_rep_args_temps_safe tail )) (PreH3 : (cm_rep_expr_temps_safe head )) (PreH4 : (arg_pre <> 0)) (PreH5 : (args = (cons (head) (tail)))) (PreH6 : (cm_rep_args_temps_safe args )) (PreH7 : (cm_rep_args_temps_safe tail )) (PreH8 : (cm_rep_expr_temps_safe head )) ,
  (cm_arg_list_rep np tail )
  **  (cm_expr_rep ep head )
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
|--
  (cm_arg_list_rep arg_pre args )
.

Definition cmc_args_tpair_partial_solve_wit_1_pure := 
forall (depth_pre: Z) (count_pre: Z) (arg_pre: Z) (args: (@list cm_expr)) (head: cm_expr) (tail: (@list cm_expr)) (ep: Z) (np: Z) (PreH1 : (arg_pre <> 0)) (PreH2 : (args = (cons (head) (tail)))) (PreH3 : (cm_rep_args_temps_safe args )) (PreH4 : (cm_rep_args_temps_safe tail )) (PreH5 : (cm_rep_expr_temps_safe head )) ,
  ((( &( "child_rvalue" ) )) # Int  |->_)
  **  ((( &( "child_lvalue" ) )) # Int  |->_)
  **  ((( &( "child" ) )) # Ptr  |-> ep)
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count_pre)
  **  ((( &( "depth" ) )) # Ptr  |-> depth_pre)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep head )
  **  (cm_arg_list_rep np tail )
  **  ((count_pre) # Int  |->_)
  **  ((depth_pre) # Int  |->_)
|--
  “ (cm_rep_expr_temps_safe head ) ”
.

Definition cmc_args_tpair_partial_solve_wit_1_aux := 
forall (depth_pre: Z) (count_pre: Z) (arg_pre: Z) (args: (@list cm_expr)) (head: cm_expr) (tail: (@list cm_expr)) (ep: Z) (np: Z) (PreH1 : (arg_pre <> 0)) (PreH2 : (args = (cons (head) (tail)))) (PreH3 : (cm_rep_args_temps_safe args )) (PreH4 : (cm_rep_args_temps_safe tail )) (PreH5 : (cm_rep_expr_temps_safe head )) ,
  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_expr_rep ep head )
  **  (cm_arg_list_rep np tail )
  **  ((count_pre) # Int  |->_)
  **  ((depth_pre) # Int  |->_)
|--
  “ (cm_rep_expr_temps_safe head ) ” 
  &&  “ (arg_pre <> 0) ” 
  &&  “ (args = (cons (head) (tail))) ” 
  &&  “ (cm_rep_args_temps_safe args ) ” 
  &&  “ (cm_rep_args_temps_safe tail ) ” 
  &&  “ (cm_rep_expr_temps_safe head ) ”
  &&  (cm_expr_rep ep head )
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_arg_list_rep np tail )
  **  ((count_pre) # Int  |->_)
  **  ((depth_pre) # Int  |->_)
.

Definition cmc_args_tpair_partial_solve_wit_1 := cmc_args_tpair_partial_solve_wit_1_pure -> cmc_args_tpair_partial_solve_wit_1_aux.

Definition cmc_args_tpair_partial_solve_wit_2_pure := 
forall (depth_pre: Z) (count_pre: Z) (arg_pre: Z) (args: (@list cm_expr)) (head: cm_expr) (tail: (@list cm_expr)) (ep: Z) (np: Z) (PreH1 : (cm_rep_expr_temps_safe head )) (PreH2 : (arg_pre <> 0)) (PreH3 : (args = (cons (head) (tail)))) (PreH4 : (cm_rep_args_temps_safe args )) (PreH5 : (cm_rep_args_temps_safe tail )) (PreH6 : (cm_rep_expr_temps_safe head )) ,
  ((( &( "rest_depth" ) )) # Int  |->_)
  **  ((( &( "rest_count" ) )) # Int  |->_)
  **  (cm_expr_rep ep head )
  **  ((( &( "child_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (head)))))
  **  ((( &( "child_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (head)))))
  **  ((( &( "child" ) )) # Ptr  |-> ep)
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((( &( "count" ) )) # Ptr  |-> count_pre)
  **  ((( &( "depth" ) )) # Ptr  |-> depth_pre)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_arg_list_rep np tail )
  **  ((count_pre) # Int  |->_)
  **  ((depth_pre) # Int  |->_)
|--
  “ (cm_rep_args_temps_safe tail ) ”
.

Definition cmc_args_tpair_partial_solve_wit_2_aux := 
forall (depth_pre: Z) (count_pre: Z) (arg_pre: Z) (args: (@list cm_expr)) (head: cm_expr) (tail: (@list cm_expr)) (ep: Z) (np: Z) (PreH1 : (cm_rep_expr_temps_safe head )) (PreH2 : (arg_pre <> 0)) (PreH3 : (args = (cons (head) (tail)))) (PreH4 : (cm_rep_args_temps_safe args )) (PreH5 : (cm_rep_args_temps_safe tail )) (PreH6 : (cm_rep_expr_temps_safe head )) ,
  (cm_expr_rep ep head )
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  (cm_arg_list_rep np tail )
  **  ((count_pre) # Int  |->_)
  **  ((depth_pre) # Int  |->_)
|--
  “ (cm_rep_args_temps_safe tail ) ” 
  &&  “ (cm_rep_expr_temps_safe head ) ” 
  &&  “ (arg_pre <> 0) ” 
  &&  “ (args = (cons (head) (tail))) ” 
  &&  “ (cm_rep_args_temps_safe args ) ” 
  &&  “ (cm_rep_args_temps_safe tail ) ” 
  &&  “ (cm_rep_expr_temps_safe head ) ”
  &&  (cm_arg_list_rep np tail )
  **  (cm_expr_rep ep head )
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  ((count_pre) # Int  |->_)
  **  ((depth_pre) # Int  |->_)
.

Definition cmc_args_tpair_partial_solve_wit_2 := cmc_args_tpair_partial_solve_wit_2_pure -> cmc_args_tpair_partial_solve_wit_2_aux.

Definition cmc_args_tpair_partial_solve_wit_3 := 
forall (depth_pre: Z) (count_pre: Z) (arg_pre: Z) (args: (@list cm_expr)) (head: cm_expr) (tail: (@list cm_expr)) (ep: Z) (np: Z) (PreH1 : (cm_rep_args_temps_safe tail )) (PreH2 : (cm_rep_expr_temps_safe head )) (PreH3 : (arg_pre <> 0)) (PreH4 : (args = (cons (head) (tail)))) (PreH5 : (cm_rep_args_temps_safe args )) (PreH6 : (cm_rep_args_temps_safe tail )) (PreH7 : (cm_rep_expr_temps_safe head )) ,
  (cm_arg_list_rep np tail )
  **  (cm_expr_rep ep head )
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  ((count_pre) # Int  |->_)
  **  ((depth_pre) # Int  |->_)
|--
  “ (cm_rep_args_temps_safe tail ) ” 
  &&  “ (cm_rep_expr_temps_safe head ) ” 
  &&  “ (arg_pre <> 0) ” 
  &&  “ (args = (cons (head) (tail))) ” 
  &&  “ (cm_rep_args_temps_safe args ) ” 
  &&  “ (cm_rep_args_temps_safe tail ) ” 
  &&  “ (cm_rep_expr_temps_safe head ) ”
  &&  (cm_arg_list_rep np tail )
  **  (cm_expr_rep ep head )
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "expr")) # Ptr  |-> ep)
  **  ((&((arg_pre)  # "cm_arg" ->ₛ "next")) # Ptr  |-> np)
  **  ((count_pre) # Int  |->_)
  **  ((depth_pre) # Int  |->_)
.

(*----- Function cm_expr_temps -----*)

Definition cm_expr_temps_safety_wit_1 := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : (expr_pre <> 0)) (PreH2 : (cm_rep_expr_temps_safe e )) ,
  ((( &( "out_lvalue" ) )) # Int  |->_)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_expr_temps_safety_wit_2 := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : (expr_pre <> 0)) (PreH2 : (cm_rep_expr_temps_safe e )) ,
  ((( &( "out_rvalue" ) )) # Int  |->_)
  **  ((( &( "out_lvalue" ) )) # Int  |-> 0)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_expr_temps_safety_wit_3 := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : (expr_pre <> 0)) (PreH2 : (cm_rep_expr_temps_safe e )) ,
  ((( &( "out_rvalue" ) )) # Int  |-> 0)
  **  ((( &( "out_lvalue" ) )) # Int  |-> 0)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition cm_expr_temps_safety_wit_4 := 
(
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (cm_rep_expr_temps_safe y )) (PreH2 : (cm_rep_expr_temps_safe x )) (PreH3 : (expr_pre <> 0)) (PreH4 : (cm_rep_expr_temps_safe e )) (PreH5 : (e = (CMAssignE (x) (y) (t)))) (PreH6 : (out_lvalue = 0)) (PreH7 : (out_rvalue = 0)) (PreH8 : (cm_rep_expr_temps_safe x )) (PreH9 : (cm_rep_expr_temps_safe y )) (PreH10 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  ((( &( "right_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (y)))))
  **  ((( &( "right_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (y)))))
  **  (cm_expr_rep pa x )
  **  ((( &( "left_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (x)))))
  **  ((( &( "left_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (x)))))
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((( &( "out_lvalue" ) )) # Int  |-> out_lvalue)
  **  ((( &( "out_rvalue" ) )) # Int  |-> out_rvalue)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ ((1 + (cm_tright ((cm_expr_tpair (y)))) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (1 + (cm_tright ((cm_expr_tpair (y)))) )) ”
) \/
(
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (cm_rep_expr_temps_safe y )) (PreH2 : (cm_rep_expr_temps_safe x )) (PreH3 : (expr_pre <> 0)) (PreH4 : (cm_rep_expr_temps_safe e )) (PreH5 : (e = (CMAssignE (x) (y) (t)))) (PreH6 : (out_lvalue = 0)) (PreH7 : (out_rvalue = 0)) (PreH8 : (cm_rep_expr_temps_safe x )) (PreH9 : (cm_rep_expr_temps_safe y )) (PreH10 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  ((( &( "right_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (y)))))
  **  ((( &( "right_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (y)))))
  **  (cm_expr_rep pa x )
  **  ((( &( "left_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (x)))))
  **  ((( &( "left_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (x)))))
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((( &( "out_lvalue" ) )) # Int  |-> out_lvalue)
  **  ((( &( "out_rvalue" ) )) # Int  |-> out_rvalue)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ ((1 + (cm_tright ((cm_expr_tpair (y)))) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (1 + (cm_tright ((cm_expr_tpair (y)))) )) ”
).

Definition cm_expr_temps_safety_wit_4_split_goal_1 := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (cm_rep_expr_temps_safe y )) (PreH2 : (cm_rep_expr_temps_safe x )) (PreH3 : (expr_pre <> 0)) (PreH4 : (cm_rep_expr_temps_safe e )) (PreH5 : (e = (CMAssignE (x) (y) (t)))) (PreH6 : (out_lvalue = 0)) (PreH7 : (out_rvalue = 0)) (PreH8 : (cm_rep_expr_temps_safe x )) (PreH9 : (cm_rep_expr_temps_safe y )) (PreH10 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  ((( &( "right_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (y)))))
  **  ((( &( "right_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (y)))))
  **  (cm_expr_rep pa x )
  **  ((( &( "left_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (x)))))
  **  ((( &( "left_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (x)))))
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((( &( "out_lvalue" ) )) # Int  |-> out_lvalue)
  **  ((( &( "out_rvalue" ) )) # Int  |-> out_rvalue)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ ((1 + (cm_tright ((cm_expr_tpair (y)))) ) <= INT_MAX) ”
.

Definition cm_expr_temps_safety_wit_4_split_goal_2 := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (cm_rep_expr_temps_safe y )) (PreH2 : (cm_rep_expr_temps_safe x )) (PreH3 : (expr_pre <> 0)) (PreH4 : (cm_rep_expr_temps_safe e )) (PreH5 : (e = (CMAssignE (x) (y) (t)))) (PreH6 : (out_lvalue = 0)) (PreH7 : (out_rvalue = 0)) (PreH8 : (cm_rep_expr_temps_safe x )) (PreH9 : (cm_rep_expr_temps_safe y )) (PreH10 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  ((( &( "right_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (y)))))
  **  ((( &( "right_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (y)))))
  **  (cm_expr_rep pa x )
  **  ((( &( "left_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (x)))))
  **  ((( &( "left_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (x)))))
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((( &( "out_lvalue" ) )) # Int  |-> out_lvalue)
  **  ((( &( "out_rvalue" ) )) # Int  |-> out_rvalue)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ ((INT_MIN) <= (1 + (cm_tright ((cm_expr_tpair (y)))) )) ”
.

Definition cm_expr_temps_safety_wit_5 := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (cm_rep_expr_temps_safe y )) (PreH2 : (cm_rep_expr_temps_safe x )) (PreH3 : (expr_pre <> 0)) (PreH4 : (cm_rep_expr_temps_safe e )) (PreH5 : (e = (CMAssignE (x) (y) (t)))) (PreH6 : (out_lvalue = 0)) (PreH7 : (out_rvalue = 0)) (PreH8 : (cm_rep_expr_temps_safe x )) (PreH9 : (cm_rep_expr_temps_safe y )) (PreH10 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  ((( &( "right_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (y)))))
  **  ((( &( "right_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (y)))))
  **  (cm_expr_rep pa x )
  **  ((( &( "left_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (x)))))
  **  ((( &( "left_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (x)))))
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((( &( "out_lvalue" ) )) # Int  |-> out_lvalue)
  **  ((( &( "out_rvalue" ) )) # Int  |-> out_rvalue)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cm_expr_temps_safety_wit_6 := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_kind (e)) <> 3)) (PreH2 : (expr_pre <> 0)) (PreH3 : (cm_rep_expr_temps_safe e )) ,
  ((( &( "out_rvalue" ) )) # Int  |-> 0)
  **  ((( &( "out_lvalue" ) )) # Int  |-> 0)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition cm_expr_temps_safety_wit_7 := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (cm_rep_expr_temps_safe y )) (PreH2 : (cm_rep_expr_temps_safe x )) (PreH3 : (expr_pre <> 0)) (PreH4 : (cm_rep_expr_temps_safe e )) (PreH5 : (e = (CMBinaryE (op) (x) (y) (t)))) (PreH6 : (out_lvalue = 0)) (PreH7 : (out_rvalue = 0)) (PreH8 : (cm_rep_expr_temps_safe x )) (PreH9 : (cm_rep_expr_temps_safe y )) (PreH10 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  ((( &( "right_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (y)))))
  **  ((( &( "right_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (y)))))
  **  (cm_expr_rep pa x )
  **  ((( &( "left_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (x)))))
  **  ((( &( "left_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (x)))))
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((( &( "out_lvalue" ) )) # Int  |-> out_lvalue)
  **  ((( &( "out_rvalue" ) )) # Int  |-> out_rvalue)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_expr_temps_safety_wit_8 := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_op (e)) <> 0)) (PreH2 : (cm_rep_expr_temps_safe y )) (PreH3 : (cm_rep_expr_temps_safe x )) (PreH4 : (expr_pre <> 0)) (PreH5 : (cm_rep_expr_temps_safe e )) (PreH6 : (e = (CMBinaryE (op) (x) (y) (t)))) (PreH7 : (out_lvalue = 0)) (PreH8 : (out_rvalue = 0)) (PreH9 : (cm_rep_expr_temps_safe x )) (PreH10 : (cm_rep_expr_temps_safe y )) (PreH11 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  ((( &( "right_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (y)))))
  **  ((( &( "right_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (y)))))
  **  (cm_expr_rep pa x )
  **  ((( &( "left_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (x)))))
  **  ((( &( "left_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (x)))))
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((( &( "out_lvalue" ) )) # Int  |-> out_lvalue)
  **  ((( &( "out_rvalue" ) )) # Int  |-> out_rvalue)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cm_expr_temps_safety_wit_9 := 
(
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_op (e)) <> 1)) (PreH2 : ((cm_rep_expr_op (e)) <> 0)) (PreH3 : (cm_rep_expr_temps_safe y )) (PreH4 : (cm_rep_expr_temps_safe x )) (PreH5 : (expr_pre <> 0)) (PreH6 : (cm_rep_expr_temps_safe e )) (PreH7 : (e = (CMBinaryE (op) (x) (y) (t)))) (PreH8 : (out_lvalue = 0)) (PreH9 : (out_rvalue = 0)) (PreH10 : (cm_rep_expr_temps_safe x )) (PreH11 : (cm_rep_expr_temps_safe y )) (PreH12 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  ((( &( "right_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (y)))))
  **  ((( &( "right_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (y)))))
  **  (cm_expr_rep pa x )
  **  ((( &( "left_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (x)))))
  **  ((( &( "left_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (x)))))
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((( &( "out_lvalue" ) )) # Int  |-> out_lvalue)
  **  ((( &( "out_rvalue" ) )) # Int  |-> out_rvalue)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ ((1 + (cm_tright ((cm_expr_tpair (y)))) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (1 + (cm_tright ((cm_expr_tpair (y)))) )) ”
) \/
(
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_op (e)) <> 1)) (PreH2 : ((cm_rep_expr_op (e)) <> 0)) (PreH3 : (cm_rep_expr_temps_safe y )) (PreH4 : (cm_rep_expr_temps_safe x )) (PreH5 : (expr_pre <> 0)) (PreH6 : (cm_rep_expr_temps_safe e )) (PreH7 : (e = (CMBinaryE (op) (x) (y) (t)))) (PreH8 : (out_lvalue = 0)) (PreH9 : (out_rvalue = 0)) (PreH10 : (cm_rep_expr_temps_safe x )) (PreH11 : (cm_rep_expr_temps_safe y )) (PreH12 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  ((( &( "right_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (y)))))
  **  ((( &( "right_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (y)))))
  **  (cm_expr_rep pa x )
  **  ((( &( "left_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (x)))))
  **  ((( &( "left_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (x)))))
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((( &( "out_lvalue" ) )) # Int  |-> out_lvalue)
  **  ((( &( "out_rvalue" ) )) # Int  |-> out_rvalue)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ ((1 + (cm_tright ((cm_expr_tpair (y)))) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (1 + (cm_tright ((cm_expr_tpair (y)))) )) ”
).

Definition cm_expr_temps_safety_wit_9_split_goal_1 := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_op (e)) <> 1)) (PreH2 : ((cm_rep_expr_op (e)) <> 0)) (PreH3 : (cm_rep_expr_temps_safe y )) (PreH4 : (cm_rep_expr_temps_safe x )) (PreH5 : (expr_pre <> 0)) (PreH6 : (cm_rep_expr_temps_safe e )) (PreH7 : (e = (CMBinaryE (op) (x) (y) (t)))) (PreH8 : (out_lvalue = 0)) (PreH9 : (out_rvalue = 0)) (PreH10 : (cm_rep_expr_temps_safe x )) (PreH11 : (cm_rep_expr_temps_safe y )) (PreH12 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  ((( &( "right_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (y)))))
  **  ((( &( "right_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (y)))))
  **  (cm_expr_rep pa x )
  **  ((( &( "left_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (x)))))
  **  ((( &( "left_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (x)))))
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((( &( "out_lvalue" ) )) # Int  |-> out_lvalue)
  **  ((( &( "out_rvalue" ) )) # Int  |-> out_rvalue)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ ((1 + (cm_tright ((cm_expr_tpair (y)))) ) <= INT_MAX) ”
.

Definition cm_expr_temps_safety_wit_9_split_goal_2 := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_op (e)) <> 1)) (PreH2 : ((cm_rep_expr_op (e)) <> 0)) (PreH3 : (cm_rep_expr_temps_safe y )) (PreH4 : (cm_rep_expr_temps_safe x )) (PreH5 : (expr_pre <> 0)) (PreH6 : (cm_rep_expr_temps_safe e )) (PreH7 : (e = (CMBinaryE (op) (x) (y) (t)))) (PreH8 : (out_lvalue = 0)) (PreH9 : (out_rvalue = 0)) (PreH10 : (cm_rep_expr_temps_safe x )) (PreH11 : (cm_rep_expr_temps_safe y )) (PreH12 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  ((( &( "right_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (y)))))
  **  ((( &( "right_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (y)))))
  **  (cm_expr_rep pa x )
  **  ((( &( "left_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (x)))))
  **  ((( &( "left_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (x)))))
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((( &( "out_lvalue" ) )) # Int  |-> out_lvalue)
  **  ((( &( "out_rvalue" ) )) # Int  |-> out_rvalue)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ ((INT_MIN) <= (1 + (cm_tright ((cm_expr_tpair (y)))) )) ”
.

Definition cm_expr_temps_safety_wit_10 := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_op (e)) <> 1)) (PreH2 : ((cm_rep_expr_op (e)) <> 0)) (PreH3 : (cm_rep_expr_temps_safe y )) (PreH4 : (cm_rep_expr_temps_safe x )) (PreH5 : (expr_pre <> 0)) (PreH6 : (cm_rep_expr_temps_safe e )) (PreH7 : (e = (CMBinaryE (op) (x) (y) (t)))) (PreH8 : (out_lvalue = 0)) (PreH9 : (out_rvalue = 0)) (PreH10 : (cm_rep_expr_temps_safe x )) (PreH11 : (cm_rep_expr_temps_safe y )) (PreH12 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  ((( &( "right_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (y)))))
  **  ((( &( "right_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (y)))))
  **  (cm_expr_rep pa x )
  **  ((( &( "left_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (x)))))
  **  ((( &( "left_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (x)))))
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((( &( "out_lvalue" ) )) # Int  |-> out_lvalue)
  **  ((( &( "out_rvalue" ) )) # Int  |-> out_rvalue)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cm_expr_temps_safety_wit_11 := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_kind (e)) <> 4)) (PreH2 : ((cm_rep_expr_kind (e)) <> 3)) (PreH3 : (expr_pre <> 0)) (PreH4 : (cm_rep_expr_temps_safe e )) ,
  ((( &( "out_rvalue" ) )) # Int  |-> 0)
  **  ((( &( "out_lvalue" ) )) # Int  |-> 0)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (5 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 5) ”
.

Definition cm_expr_temps_safety_wit_12 := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (cm_rep_expr_temps_safe x )) (PreH2 : (expr_pre <> 0)) (PreH3 : (cm_rep_expr_temps_safe e )) (PreH4 : (e = (CMUnaryE (op) (x) (t)))) (PreH5 : (out_lvalue = 0)) (PreH6 : (out_rvalue = 0)) (PreH7 : (cm_rep_expr_temps_safe x )) (PreH8 : (pa <> 0)) (PreH9 : (pb = 0)) (PreH10 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((( &( "child_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (x)))))
  **  ((( &( "child_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (x)))))
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((( &( "out_lvalue" ) )) # Int  |-> out_lvalue)
  **  ((( &( "out_rvalue" ) )) # Int  |-> out_rvalue)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition cm_expr_temps_safety_wit_13 := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_op (e)) <> 2)) (PreH2 : (cm_rep_expr_temps_safe x )) (PreH3 : (expr_pre <> 0)) (PreH4 : (cm_rep_expr_temps_safe e )) (PreH5 : (e = (CMUnaryE (op) (x) (t)))) (PreH6 : (out_lvalue = 0)) (PreH7 : (out_rvalue = 0)) (PreH8 : (cm_rep_expr_temps_safe x )) (PreH9 : (pa <> 0)) (PreH10 : (pb = 0)) (PreH11 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((( &( "child_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (x)))))
  **  ((( &( "child_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (x)))))
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((( &( "out_lvalue" ) )) # Int  |-> out_lvalue)
  **  ((( &( "out_rvalue" ) )) # Int  |-> out_rvalue)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition cm_expr_temps_safety_wit_14 := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_kind (e)) <> 5)) (PreH2 : ((cm_rep_expr_kind (e)) <> 4)) (PreH3 : ((cm_rep_expr_kind (e)) <> 3)) (PreH4 : (expr_pre <> 0)) (PreH5 : (cm_rep_expr_temps_safe e )) ,
  ((( &( "out_rvalue" ) )) # Int  |-> 0)
  **  ((( &( "out_lvalue" ) )) # Int  |-> 0)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (6 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 6) ”
.

Definition cm_expr_temps_safety_wit_15 := 
(
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (cm_rep_expr_temps_safe y )) (PreH2 : (cm_rep_expr_temps_safe x )) (PreH3 : (expr_pre <> 0)) (PreH4 : (cm_rep_expr_temps_safe e )) (PreH5 : (e = (CMIndexE (x) (y) (t)))) (PreH6 : (out_lvalue = 0)) (PreH7 : (out_rvalue = 0)) (PreH8 : (cm_rep_expr_temps_safe x )) (PreH9 : (cm_rep_expr_temps_safe y )) (PreH10 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  ((( &( "index_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (y)))))
  **  ((( &( "index_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (y)))))
  **  (cm_expr_rep pa x )
  **  ((( &( "base_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (x)))))
  **  ((( &( "base_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (x)))))
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((( &( "out_lvalue" ) )) # Int  |-> out_lvalue)
  **  ((( &( "out_rvalue" ) )) # Int  |-> out_rvalue)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ ((1 + (cm_tright ((cm_expr_tpair (y)))) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (1 + (cm_tright ((cm_expr_tpair (y)))) )) ”
) \/
(
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (cm_rep_expr_temps_safe y )) (PreH2 : (cm_rep_expr_temps_safe x )) (PreH3 : (expr_pre <> 0)) (PreH4 : (cm_rep_expr_temps_safe e )) (PreH5 : (e = (CMIndexE (x) (y) (t)))) (PreH6 : (out_lvalue = 0)) (PreH7 : (out_rvalue = 0)) (PreH8 : (cm_rep_expr_temps_safe x )) (PreH9 : (cm_rep_expr_temps_safe y )) (PreH10 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  ((( &( "index_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (y)))))
  **  ((( &( "index_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (y)))))
  **  (cm_expr_rep pa x )
  **  ((( &( "base_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (x)))))
  **  ((( &( "base_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (x)))))
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((( &( "out_lvalue" ) )) # Int  |-> out_lvalue)
  **  ((( &( "out_rvalue" ) )) # Int  |-> out_rvalue)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ ((1 + (cm_tright ((cm_expr_tpair (y)))) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (1 + (cm_tright ((cm_expr_tpair (y)))) )) ”
).

Definition cm_expr_temps_safety_wit_15_split_goal_1 := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (cm_rep_expr_temps_safe y )) (PreH2 : (cm_rep_expr_temps_safe x )) (PreH3 : (expr_pre <> 0)) (PreH4 : (cm_rep_expr_temps_safe e )) (PreH5 : (e = (CMIndexE (x) (y) (t)))) (PreH6 : (out_lvalue = 0)) (PreH7 : (out_rvalue = 0)) (PreH8 : (cm_rep_expr_temps_safe x )) (PreH9 : (cm_rep_expr_temps_safe y )) (PreH10 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  ((( &( "index_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (y)))))
  **  ((( &( "index_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (y)))))
  **  (cm_expr_rep pa x )
  **  ((( &( "base_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (x)))))
  **  ((( &( "base_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (x)))))
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((( &( "out_lvalue" ) )) # Int  |-> out_lvalue)
  **  ((( &( "out_rvalue" ) )) # Int  |-> out_rvalue)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ ((1 + (cm_tright ((cm_expr_tpair (y)))) ) <= INT_MAX) ”
.

Definition cm_expr_temps_safety_wit_15_split_goal_2 := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (cm_rep_expr_temps_safe y )) (PreH2 : (cm_rep_expr_temps_safe x )) (PreH3 : (expr_pre <> 0)) (PreH4 : (cm_rep_expr_temps_safe e )) (PreH5 : (e = (CMIndexE (x) (y) (t)))) (PreH6 : (out_lvalue = 0)) (PreH7 : (out_rvalue = 0)) (PreH8 : (cm_rep_expr_temps_safe x )) (PreH9 : (cm_rep_expr_temps_safe y )) (PreH10 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  ((( &( "index_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (y)))))
  **  ((( &( "index_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (y)))))
  **  (cm_expr_rep pa x )
  **  ((( &( "base_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (x)))))
  **  ((( &( "base_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (x)))))
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((( &( "out_lvalue" ) )) # Int  |-> out_lvalue)
  **  ((( &( "out_rvalue" ) )) # Int  |-> out_rvalue)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ ((INT_MIN) <= (1 + (cm_tright ((cm_expr_tpair (y)))) )) ”
.

Definition cm_expr_temps_safety_wit_16 := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (cm_rep_expr_temps_safe y )) (PreH2 : (cm_rep_expr_temps_safe x )) (PreH3 : (expr_pre <> 0)) (PreH4 : (cm_rep_expr_temps_safe e )) (PreH5 : (e = (CMIndexE (x) (y) (t)))) (PreH6 : (out_lvalue = 0)) (PreH7 : (out_rvalue = 0)) (PreH8 : (cm_rep_expr_temps_safe x )) (PreH9 : (cm_rep_expr_temps_safe y )) (PreH10 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  ((( &( "index_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (y)))))
  **  ((( &( "index_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (y)))))
  **  (cm_expr_rep pa x )
  **  ((( &( "base_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (x)))))
  **  ((( &( "base_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (x)))))
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((( &( "out_lvalue" ) )) # Int  |-> out_lvalue)
  **  ((( &( "out_rvalue" ) )) # Int  |-> out_rvalue)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cm_expr_temps_safety_wit_17 := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_kind (e)) <> 6)) (PreH2 : ((cm_rep_expr_kind (e)) <> 5)) (PreH3 : ((cm_rep_expr_kind (e)) <> 4)) (PreH4 : ((cm_rep_expr_kind (e)) <> 3)) (PreH5 : (expr_pre <> 0)) (PreH6 : (cm_rep_expr_temps_safe e )) ,
  ((( &( "out_rvalue" ) )) # Int  |-> 0)
  **  ((( &( "out_lvalue" ) )) # Int  |-> 0)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (7 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 7) ”
.

Definition cm_expr_temps_safety_wit_18 := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_kind (e)) <> 7)) (PreH2 : ((cm_rep_expr_kind (e)) <> 6)) (PreH3 : ((cm_rep_expr_kind (e)) <> 5)) (PreH4 : ((cm_rep_expr_kind (e)) <> 4)) (PreH5 : ((cm_rep_expr_kind (e)) <> 3)) (PreH6 : (expr_pre <> 0)) (PreH7 : (cm_rep_expr_temps_safe e )) ,
  ((( &( "out_rvalue" ) )) # Int  |-> 0)
  **  ((( &( "out_lvalue" ) )) # Int  |-> 0)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition cm_expr_temps_safety_wit_19 := 
(
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (fid: Z) (eargs: (@list cm_expr)) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (cm_rep_args_temps_safe eargs )) (PreH2 : (expr_pre <> 0)) (PreH3 : (cm_rep_expr_temps_safe e )) (PreH4 : (e = (CMCallE (fid) (eargs) (t)))) (PreH5 : (out_lvalue = 0)) (PreH6 : (out_rvalue = 0)) (PreH7 : (cm_rep_args_temps_safe eargs )) (PreH8 : (pa = 0)) (PreH9 : (pb = 0)) ,
  (cm_arg_list_rep pargs eargs )
  **  ((( &( "count" ) )) # Int  |-> (cm_acount ((cm_args_apair (eargs)))))
  **  ((( &( "depth" ) )) # Int  |-> (cm_adepth ((cm_args_apair (eargs)))))
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((( &( "out_lvalue" ) )) # Int  |-> out_lvalue)
  **  ((( &( "out_rvalue" ) )) # Int  |-> out_rvalue)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (((cm_acount ((cm_args_apair (eargs)))) + (cm_adepth ((cm_args_apair (eargs)))) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((cm_acount ((cm_args_apair (eargs)))) + (cm_adepth ((cm_args_apair (eargs)))) )) ”
) \/
(
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (fid: Z) (eargs: (@list cm_expr)) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (cm_rep_args_temps_safe eargs )) (PreH2 : (expr_pre <> 0)) (PreH3 : (cm_rep_expr_temps_safe e )) (PreH4 : (e = (CMCallE (fid) (eargs) (t)))) (PreH5 : (out_lvalue = 0)) (PreH6 : (out_rvalue = 0)) (PreH7 : (cm_rep_args_temps_safe eargs )) (PreH8 : (pa = 0)) (PreH9 : (pb = 0)) ,
  (cm_arg_list_rep pargs eargs )
  **  ((( &( "count" ) )) # Int  |-> (cm_acount ((cm_args_apair (eargs)))))
  **  ((( &( "depth" ) )) # Int  |-> (cm_adepth ((cm_args_apair (eargs)))))
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((( &( "out_lvalue" ) )) # Int  |-> out_lvalue)
  **  ((( &( "out_rvalue" ) )) # Int  |-> out_rvalue)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (((cm_acount ((cm_args_apair (eargs)))) + (cm_adepth ((cm_args_apair (eargs)))) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((cm_acount ((cm_args_apair (eargs)))) + (cm_adepth ((cm_args_apair (eargs)))) )) ”
).

Definition cm_expr_temps_safety_wit_19_split_goal_1 := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (fid: Z) (eargs: (@list cm_expr)) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (cm_rep_args_temps_safe eargs )) (PreH2 : (expr_pre <> 0)) (PreH3 : (cm_rep_expr_temps_safe e )) (PreH4 : (e = (CMCallE (fid) (eargs) (t)))) (PreH5 : (out_lvalue = 0)) (PreH6 : (out_rvalue = 0)) (PreH7 : (cm_rep_args_temps_safe eargs )) (PreH8 : (pa = 0)) (PreH9 : (pb = 0)) ,
  (cm_arg_list_rep pargs eargs )
  **  ((( &( "count" ) )) # Int  |-> (cm_acount ((cm_args_apair (eargs)))))
  **  ((( &( "depth" ) )) # Int  |-> (cm_adepth ((cm_args_apair (eargs)))))
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((( &( "out_lvalue" ) )) # Int  |-> out_lvalue)
  **  ((( &( "out_rvalue" ) )) # Int  |-> out_rvalue)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (((cm_acount ((cm_args_apair (eargs)))) + (cm_adepth ((cm_args_apair (eargs)))) ) <= INT_MAX) ”
.

Definition cm_expr_temps_safety_wit_19_split_goal_2 := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (fid: Z) (eargs: (@list cm_expr)) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (cm_rep_args_temps_safe eargs )) (PreH2 : (expr_pre <> 0)) (PreH3 : (cm_rep_expr_temps_safe e )) (PreH4 : (e = (CMCallE (fid) (eargs) (t)))) (PreH5 : (out_lvalue = 0)) (PreH6 : (out_rvalue = 0)) (PreH7 : (cm_rep_args_temps_safe eargs )) (PreH8 : (pa = 0)) (PreH9 : (pb = 0)) ,
  (cm_arg_list_rep pargs eargs )
  **  ((( &( "count" ) )) # Int  |-> (cm_acount ((cm_args_apair (eargs)))))
  **  ((( &( "depth" ) )) # Int  |-> (cm_adepth ((cm_args_apair (eargs)))))
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((( &( "out_lvalue" ) )) # Int  |-> out_lvalue)
  **  ((( &( "out_rvalue" ) )) # Int  |-> out_rvalue)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ ((INT_MIN) <= ((cm_acount ((cm_args_apair (eargs)))) + (cm_adepth ((cm_args_apair (eargs)))) )) ”
.

Definition cm_expr_temps_safety_wit_20 := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_kind (e)) <> 8)) (PreH2 : ((cm_rep_expr_kind (e)) <> 7)) (PreH3 : ((cm_rep_expr_kind (e)) <> 6)) (PreH4 : ((cm_rep_expr_kind (e)) <> 5)) (PreH5 : ((cm_rep_expr_kind (e)) <> 4)) (PreH6 : ((cm_rep_expr_kind (e)) <> 3)) (PreH7 : (expr_pre <> 0)) (PreH8 : (cm_rep_expr_temps_safe e )) ,
  ((( &( "out_rvalue" ) )) # Int  |-> 0)
  **  ((( &( "out_lvalue" ) )) # Int  |-> 0)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (11 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 11) ”
.

Definition cm_expr_temps_safety_wit_21 := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_kind (e)) <> 11)) (PreH2 : ((cm_rep_expr_kind (e)) <> 8)) (PreH3 : ((cm_rep_expr_kind (e)) <> 7)) (PreH4 : ((cm_rep_expr_kind (e)) <> 6)) (PreH5 : ((cm_rep_expr_kind (e)) <> 5)) (PreH6 : ((cm_rep_expr_kind (e)) <> 4)) (PreH7 : ((cm_rep_expr_kind (e)) <> 3)) (PreH8 : (expr_pre <> 0)) (PreH9 : (cm_rep_expr_temps_safe e )) ,
  ((( &( "out_rvalue" ) )) # Int  |-> 0)
  **  ((( &( "out_lvalue" ) )) # Int  |-> 0)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (12 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 12) ”
.

Definition cm_expr_temps_safety_wit_22 := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_kind (e)) <> 12)) (PreH2 : ((cm_rep_expr_kind (e)) <> 11)) (PreH3 : ((cm_rep_expr_kind (e)) <> 8)) (PreH4 : ((cm_rep_expr_kind (e)) <> 7)) (PreH5 : ((cm_rep_expr_kind (e)) <> 6)) (PreH6 : ((cm_rep_expr_kind (e)) <> 5)) (PreH7 : ((cm_rep_expr_kind (e)) <> 4)) (PreH8 : ((cm_rep_expr_kind (e)) <> 3)) (PreH9 : (expr_pre <> 0)) (PreH10 : (cm_rep_expr_temps_safe e )) ,
  ((( &( "out_rvalue" ) )) # Int  |-> 0)
  **  ((( &( "out_lvalue" ) )) # Int  |-> 0)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (13 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 13) ”
.

Definition cm_expr_temps_safety_wit_23 := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_kind (e)) <> 13)) (PreH2 : ((cm_rep_expr_kind (e)) <> 12)) (PreH3 : ((cm_rep_expr_kind (e)) <> 11)) (PreH4 : ((cm_rep_expr_kind (e)) <> 8)) (PreH5 : ((cm_rep_expr_kind (e)) <> 7)) (PreH6 : ((cm_rep_expr_kind (e)) <> 6)) (PreH7 : ((cm_rep_expr_kind (e)) <> 5)) (PreH8 : ((cm_rep_expr_kind (e)) <> 4)) (PreH9 : ((cm_rep_expr_kind (e)) <> 3)) (PreH10 : (expr_pre <> 0)) (PreH11 : (cm_rep_expr_temps_safe e )) ,
  ((( &( "out_rvalue" ) )) # Int  |-> 0)
  **  ((( &( "out_lvalue" ) )) # Int  |-> 0)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_expr_temps_safety_wit_24 := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_kind (e)) <> 0)) (PreH2 : ((cm_rep_expr_kind (e)) <> 13)) (PreH3 : ((cm_rep_expr_kind (e)) <> 12)) (PreH4 : ((cm_rep_expr_kind (e)) <> 11)) (PreH5 : ((cm_rep_expr_kind (e)) <> 8)) (PreH6 : ((cm_rep_expr_kind (e)) <> 7)) (PreH7 : ((cm_rep_expr_kind (e)) <> 6)) (PreH8 : ((cm_rep_expr_kind (e)) <> 5)) (PreH9 : ((cm_rep_expr_kind (e)) <> 4)) (PreH10 : ((cm_rep_expr_kind (e)) <> 3)) (PreH11 : (expr_pre <> 0)) (PreH12 : (cm_rep_expr_temps_safe e )) ,
  ((( &( "out_rvalue" ) )) # Int  |-> 0)
  **  ((( &( "out_lvalue" ) )) # Int  |-> 0)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cm_expr_temps_safety_wit_25 := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_kind (e)) <> 1)) (PreH2 : ((cm_rep_expr_kind (e)) <> 0)) (PreH3 : ((cm_rep_expr_kind (e)) <> 13)) (PreH4 : ((cm_rep_expr_kind (e)) <> 12)) (PreH5 : ((cm_rep_expr_kind (e)) <> 11)) (PreH6 : ((cm_rep_expr_kind (e)) <> 8)) (PreH7 : ((cm_rep_expr_kind (e)) <> 7)) (PreH8 : ((cm_rep_expr_kind (e)) <> 6)) (PreH9 : ((cm_rep_expr_kind (e)) <> 5)) (PreH10 : ((cm_rep_expr_kind (e)) <> 4)) (PreH11 : ((cm_rep_expr_kind (e)) <> 3)) (PreH12 : (expr_pre <> 0)) (PreH13 : (cm_rep_expr_temps_safe e )) ,
  ((( &( "out_rvalue" ) )) # Int  |-> 0)
  **  ((( &( "out_lvalue" ) )) # Int  |-> 0)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition cm_expr_temps_safety_wit_26 := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_kind (e)) <> 2)) (PreH2 : ((cm_rep_expr_kind (e)) <> 1)) (PreH3 : ((cm_rep_expr_kind (e)) <> 0)) (PreH4 : ((cm_rep_expr_kind (e)) <> 13)) (PreH5 : ((cm_rep_expr_kind (e)) <> 12)) (PreH6 : ((cm_rep_expr_kind (e)) <> 11)) (PreH7 : ((cm_rep_expr_kind (e)) <> 8)) (PreH8 : ((cm_rep_expr_kind (e)) <> 7)) (PreH9 : ((cm_rep_expr_kind (e)) <> 6)) (PreH10 : ((cm_rep_expr_kind (e)) <> 5)) (PreH11 : ((cm_rep_expr_kind (e)) <> 4)) (PreH12 : ((cm_rep_expr_kind (e)) <> 3)) (PreH13 : (expr_pre <> 0)) (PreH14 : (cm_rep_expr_temps_safe e )) ,
  ((( &( "out_rvalue" ) )) # Int  |-> 0)
  **  ((( &( "out_lvalue" ) )) # Int  |-> 0)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (9 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 9) ”
.

Definition cm_expr_temps_safety_wit_27 := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_kind (e)) <> 9)) (PreH2 : ((cm_rep_expr_kind (e)) <> 2)) (PreH3 : ((cm_rep_expr_kind (e)) <> 1)) (PreH4 : ((cm_rep_expr_kind (e)) <> 0)) (PreH5 : ((cm_rep_expr_kind (e)) <> 13)) (PreH6 : ((cm_rep_expr_kind (e)) <> 12)) (PreH7 : ((cm_rep_expr_kind (e)) <> 11)) (PreH8 : ((cm_rep_expr_kind (e)) <> 8)) (PreH9 : ((cm_rep_expr_kind (e)) <> 7)) (PreH10 : ((cm_rep_expr_kind (e)) <> 6)) (PreH11 : ((cm_rep_expr_kind (e)) <> 5)) (PreH12 : ((cm_rep_expr_kind (e)) <> 4)) (PreH13 : ((cm_rep_expr_kind (e)) <> 3)) (PreH14 : (expr_pre <> 0)) (PreH15 : (cm_rep_expr_temps_safe e )) ,
  ((( &( "out_rvalue" ) )) # Int  |-> 0)
  **  ((( &( "out_lvalue" ) )) # Int  |-> 0)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition cm_expr_temps_entail_wit_1 := 
(
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (PreH1 : (cm_rep_expr_temps_safe e )) ,
  (cm_expr_rep expr_pre e )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  EX (pargs: Z)  (pb: Z)  (pa: Z) ,
  “ (expr_pre <> 0) ” 
  &&  “ (cm_rep_expr_temps_safe e ) ”
  &&  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
) \/
(
forall (expr_pre: Z) (e: cm_expr) (PreH1 : (cm_rep_expr_temps_safe e )) ,
  (cm_expr_rep expr_pre e )
|--
  EX (pargs: Z)  (pb: Z)  (pa: Z) ,
  “ (expr_pre <> 0) ” 
  &&  “ (cm_rep_expr_temps_safe e ) ”
  &&  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
).

Definition cm_expr_temps_entail_wit_2 := 
(
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa_2: Z) (pb_2: Z) (pargs_2: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 3)) (PreH2 : (expr_pre <> 0)) (PreH3 : (cm_rep_expr_temps_safe e )) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa_2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb_2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs_2)
  **  (cm_expr_payload e pa_2 pb_2 pargs_2 )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  EX (pb: Z)  (pa: Z)  (pargs: Z)  (x: cm_expr)  (y: cm_expr)  (t: cm_type) ,
  “ (expr_pre <> 0) ” 
  &&  “ (cm_rep_expr_temps_safe e ) ” 
  &&  “ (e = (CMAssignE (x) (y) (t))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (cm_rep_expr_temps_safe y ) ” 
  &&  “ (pargs = 0) ”
  &&  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_rep pa x )
  **  (cm_expr_rep pb y )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
) \/
(
forall (expr_pre: Z) (e: cm_expr) (pa_2: Z) (pb_2: Z) (pargs_2: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 3)) (PreH2 : (expr_pre <> 0)) (PreH3 : (cm_rep_expr_temps_safe e )) ,
  (cm_expr_payload e pa_2 pb_2 pargs_2 )
|--
  EX (x: cm_expr)  (y: cm_expr)  (t: cm_type) ,
  “ (pargs_2 = 0) ” 
  &&  “ (pargs_2 = 0) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (cm_rep_expr_temps_safe e ) ” 
  &&  “ (e = (CMAssignE (x) (y) (t))) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (cm_rep_expr_temps_safe y ) ”
  &&  (cm_expr_rep pa_2 x )
  **  (cm_expr_rep pb_2 y )
).

Definition cm_expr_temps_entail_wit_3 := 
(
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa_2: Z) (pb_2: Z) (pargs_2: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 4)) (PreH2 : ((cm_rep_expr_kind (e)) <> 3)) (PreH3 : (expr_pre <> 0)) (PreH4 : (cm_rep_expr_temps_safe e )) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa_2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb_2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs_2)
  **  (cm_expr_payload e pa_2 pb_2 pargs_2 )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  EX (pb: Z)  (pa: Z)  (pargs: Z)  (op: Z)  (x: cm_expr)  (y: cm_expr)  (t: cm_type) ,
  “ (expr_pre <> 0) ” 
  &&  “ (cm_rep_expr_temps_safe e ) ” 
  &&  “ (e = (CMBinaryE (op) (x) (y) (t))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (cm_rep_expr_temps_safe y ) ” 
  &&  “ (pargs = 0) ”
  &&  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_rep pa x )
  **  (cm_expr_rep pb y )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
) \/
(
forall (expr_pre: Z) (e: cm_expr) (pa_2: Z) (pb_2: Z) (pargs_2: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 4)) (PreH2 : ((cm_rep_expr_kind (e)) <> 3)) (PreH3 : (expr_pre <> 0)) (PreH4 : (cm_rep_expr_temps_safe e )) ,
  (cm_expr_payload e pa_2 pb_2 pargs_2 )
|--
  EX (op: Z)  (x: cm_expr)  (y: cm_expr)  (t: cm_type) ,
  “ (pargs_2 = 0) ” 
  &&  “ (pargs_2 = 0) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (cm_rep_expr_temps_safe e ) ” 
  &&  “ (e = (CMBinaryE (op) (x) (y) (t))) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (cm_rep_expr_temps_safe y ) ”
  &&  (cm_expr_rep pa_2 x )
  **  (cm_expr_rep pb_2 y )
).

Definition cm_expr_temps_entail_wit_4 := 
(
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa_2: Z) (pb_2: Z) (pargs_2: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 5)) (PreH2 : ((cm_rep_expr_kind (e)) <> 4)) (PreH3 : ((cm_rep_expr_kind (e)) <> 3)) (PreH4 : (expr_pre <> 0)) (PreH5 : (cm_rep_expr_temps_safe e )) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa_2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb_2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs_2)
  **  (cm_expr_payload e pa_2 pb_2 pargs_2 )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  EX (pargs: Z)  (pb: Z)  (pa: Z)  (op: Z)  (x: cm_expr)  (t: cm_type) ,
  “ (expr_pre <> 0) ” 
  &&  “ (cm_rep_expr_temps_safe e ) ” 
  &&  “ (e = (CMUnaryE (op) (x) (t))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (pa <> 0) ” 
  &&  “ (pb = 0) ” 
  &&  “ (pargs = 0) ”
  &&  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_rep pa x )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
) \/
(
forall (expr_pre: Z) (e: cm_expr) (pa_2: Z) (pb_2: Z) (pargs_2: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 5)) (PreH2 : ((cm_rep_expr_kind (e)) <> 4)) (PreH3 : ((cm_rep_expr_kind (e)) <> 3)) (PreH4 : (expr_pre <> 0)) (PreH5 : (cm_rep_expr_temps_safe e )) ,
  (cm_expr_payload e pa_2 pb_2 pargs_2 )
|--
  EX (op: Z)  (x: cm_expr)  (t: cm_type) ,
  “ (pargs_2 = 0) ” 
  &&  “ (pb_2 = 0) ” 
  &&  “ (pargs_2 = 0) ” 
  &&  “ (pb_2 = 0) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (cm_rep_expr_temps_safe e ) ” 
  &&  “ (e = (CMUnaryE (op) (x) (t))) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (pa_2 <> 0) ”
  &&  (cm_expr_rep pa_2 x )
).

Definition cm_expr_temps_entail_wit_5 := 
(
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa_2: Z) (pb_2: Z) (pargs_2: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 6)) (PreH2 : ((cm_rep_expr_kind (e)) <> 5)) (PreH3 : ((cm_rep_expr_kind (e)) <> 4)) (PreH4 : ((cm_rep_expr_kind (e)) <> 3)) (PreH5 : (expr_pre <> 0)) (PreH6 : (cm_rep_expr_temps_safe e )) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa_2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb_2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs_2)
  **  (cm_expr_payload e pa_2 pb_2 pargs_2 )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  EX (pb: Z)  (pa: Z)  (pargs: Z)  (x: cm_expr)  (y: cm_expr)  (t: cm_type) ,
  “ (expr_pre <> 0) ” 
  &&  “ (cm_rep_expr_temps_safe e ) ” 
  &&  “ (e = (CMIndexE (x) (y) (t))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (cm_rep_expr_temps_safe y ) ” 
  &&  “ (pargs = 0) ”
  &&  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_rep pa x )
  **  (cm_expr_rep pb y )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
) \/
(
forall (expr_pre: Z) (e: cm_expr) (pa_2: Z) (pb_2: Z) (pargs_2: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 6)) (PreH2 : ((cm_rep_expr_kind (e)) <> 5)) (PreH3 : ((cm_rep_expr_kind (e)) <> 4)) (PreH4 : ((cm_rep_expr_kind (e)) <> 3)) (PreH5 : (expr_pre <> 0)) (PreH6 : (cm_rep_expr_temps_safe e )) ,
  (cm_expr_payload e pa_2 pb_2 pargs_2 )
|--
  EX (x: cm_expr)  (y: cm_expr)  (t: cm_type) ,
  “ (pargs_2 = 0) ” 
  &&  “ (pargs_2 = 0) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (cm_rep_expr_temps_safe e ) ” 
  &&  “ (e = (CMIndexE (x) (y) (t))) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (cm_rep_expr_temps_safe y ) ”
  &&  (cm_expr_rep pa_2 x )
  **  (cm_expr_rep pb_2 y )
).

Definition cm_expr_temps_entail_wit_6 := 
(
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa_2: Z) (pb_2: Z) (pargs_2: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 7)) (PreH2 : ((cm_rep_expr_kind (e)) <> 6)) (PreH3 : ((cm_rep_expr_kind (e)) <> 5)) (PreH4 : ((cm_rep_expr_kind (e)) <> 4)) (PreH5 : ((cm_rep_expr_kind (e)) <> 3)) (PreH6 : (expr_pre <> 0)) (PreH7 : (cm_rep_expr_temps_safe e )) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa_2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb_2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs_2)
  **  (cm_expr_payload e pa_2 pb_2 pargs_2 )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  EX (pargs: Z)  (pb: Z)  (pa: Z)  (x: cm_expr)  (mid: Z)  (t: cm_type) ,
  “ (expr_pre <> 0) ” 
  &&  “ (cm_rep_expr_temps_safe e ) ” 
  &&  “ (e = (CMMemberE (x) (mid) (t))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (pa <> 0) ” 
  &&  “ (pb = 0) ” 
  &&  “ (pargs = 0) ”
  &&  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_rep pa x )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
) \/
(
forall (expr_pre: Z) (e: cm_expr) (pa_2: Z) (pb_2: Z) (pargs_2: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 7)) (PreH2 : ((cm_rep_expr_kind (e)) <> 6)) (PreH3 : ((cm_rep_expr_kind (e)) <> 5)) (PreH4 : ((cm_rep_expr_kind (e)) <> 4)) (PreH5 : ((cm_rep_expr_kind (e)) <> 3)) (PreH6 : (expr_pre <> 0)) (PreH7 : (cm_rep_expr_temps_safe e )) ,
  (cm_expr_payload e pa_2 pb_2 pargs_2 )
|--
  EX (x: cm_expr)  (mid: Z)  (t: cm_type) ,
  “ (pargs_2 = 0) ” 
  &&  “ (pb_2 = 0) ” 
  &&  “ (pargs_2 = 0) ” 
  &&  “ (pb_2 = 0) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (cm_rep_expr_temps_safe e ) ” 
  &&  “ (e = (CMMemberE (x) (mid) (t))) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (pa_2 <> 0) ”
  &&  (cm_expr_rep pa_2 x )
).

Definition cm_expr_temps_entail_wit_7 := 
(
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa_2: Z) (pb_2: Z) (pargs_2: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 8)) (PreH2 : ((cm_rep_expr_kind (e)) <> 7)) (PreH3 : ((cm_rep_expr_kind (e)) <> 6)) (PreH4 : ((cm_rep_expr_kind (e)) <> 5)) (PreH5 : ((cm_rep_expr_kind (e)) <> 4)) (PreH6 : ((cm_rep_expr_kind (e)) <> 3)) (PreH7 : (expr_pre <> 0)) (PreH8 : (cm_rep_expr_temps_safe e )) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa_2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb_2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs_2)
  **  (cm_expr_payload e pa_2 pb_2 pargs_2 )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  EX (pargs: Z)  (pb: Z)  (pa: Z)  (fid: Z)  (eargs: (@list cm_expr))  (t: cm_type) ,
  “ (expr_pre <> 0) ” 
  &&  “ (cm_rep_expr_temps_safe e ) ” 
  &&  “ (e = (CMCallE (fid) (eargs) (t))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (cm_rep_args_temps_safe eargs ) ” 
  &&  “ (pa = 0) ” 
  &&  “ (pb = 0) ”
  &&  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_arg_list_rep pargs eargs )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
) \/
(
forall (expr_pre: Z) (e: cm_expr) (pa_2: Z) (pb_2: Z) (pargs_2: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 8)) (PreH2 : ((cm_rep_expr_kind (e)) <> 7)) (PreH3 : ((cm_rep_expr_kind (e)) <> 6)) (PreH4 : ((cm_rep_expr_kind (e)) <> 5)) (PreH5 : ((cm_rep_expr_kind (e)) <> 4)) (PreH6 : ((cm_rep_expr_kind (e)) <> 3)) (PreH7 : (expr_pre <> 0)) (PreH8 : (cm_rep_expr_temps_safe e )) ,
  (cm_expr_payload e pa_2 pb_2 pargs_2 )
|--
  EX (fid: Z)  (eargs: (@list cm_expr))  (t: cm_type) ,
  “ (pb_2 = 0) ” 
  &&  “ (pa_2 = 0) ” 
  &&  “ (pb_2 = 0) ” 
  &&  “ (pa_2 = 0) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (cm_rep_expr_temps_safe e ) ” 
  &&  “ (e = (CMCallE (fid) (eargs) (t))) ” 
  &&  “ (cm_rep_args_temps_safe eargs ) ”
  &&  (cm_arg_list_rep pargs_2 eargs )
).

Definition cm_expr_temps_entail_wit_8 := 
(
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa_2: Z) (pb_2: Z) (pargs_2: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 11)) (PreH2 : ((cm_rep_expr_kind (e)) <> 8)) (PreH3 : ((cm_rep_expr_kind (e)) <> 7)) (PreH4 : ((cm_rep_expr_kind (e)) <> 6)) (PreH5 : ((cm_rep_expr_kind (e)) <> 5)) (PreH6 : ((cm_rep_expr_kind (e)) <> 4)) (PreH7 : ((cm_rep_expr_kind (e)) <> 3)) (PreH8 : (expr_pre <> 0)) (PreH9 : (cm_rep_expr_temps_safe e )) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa_2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb_2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs_2)
  **  (cm_expr_payload e pa_2 pb_2 pargs_2 )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  EX (pargs: Z)  (pb: Z)  (pa: Z)  (x: cm_expr)  (t: cm_type) ,
  “ (expr_pre <> 0) ” 
  &&  “ (cm_rep_expr_temps_safe e ) ” 
  &&  “ (e = (CMPutcE (x) (t))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (pa <> 0) ” 
  &&  “ (pb = 0) ” 
  &&  “ (pargs = 0) ”
  &&  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_rep pa x )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
) \/
(
forall (expr_pre: Z) (e: cm_expr) (pa_2: Z) (pb_2: Z) (pargs_2: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 11)) (PreH2 : ((cm_rep_expr_kind (e)) <> 8)) (PreH3 : ((cm_rep_expr_kind (e)) <> 7)) (PreH4 : ((cm_rep_expr_kind (e)) <> 6)) (PreH5 : ((cm_rep_expr_kind (e)) <> 5)) (PreH6 : ((cm_rep_expr_kind (e)) <> 4)) (PreH7 : ((cm_rep_expr_kind (e)) <> 3)) (PreH8 : (expr_pre <> 0)) (PreH9 : (cm_rep_expr_temps_safe e )) ,
  (cm_expr_payload e pa_2 pb_2 pargs_2 )
|--
  EX (x: cm_expr)  (t: cm_type) ,
  “ (pargs_2 = 0) ” 
  &&  “ (pb_2 = 0) ” 
  &&  “ (pargs_2 = 0) ” 
  &&  “ (pb_2 = 0) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (cm_rep_expr_temps_safe e ) ” 
  &&  “ (e = (CMPutcE (x) (t))) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (pa_2 <> 0) ”
  &&  (cm_expr_rep pa_2 x )
).

Definition cm_expr_temps_entail_wit_9 := 
(
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa_2: Z) (pb_2: Z) (pargs_2: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 12)) (PreH2 : ((cm_rep_expr_kind (e)) <> 11)) (PreH3 : ((cm_rep_expr_kind (e)) <> 8)) (PreH4 : ((cm_rep_expr_kind (e)) <> 7)) (PreH5 : ((cm_rep_expr_kind (e)) <> 6)) (PreH6 : ((cm_rep_expr_kind (e)) <> 5)) (PreH7 : ((cm_rep_expr_kind (e)) <> 4)) (PreH8 : ((cm_rep_expr_kind (e)) <> 3)) (PreH9 : (expr_pre <> 0)) (PreH10 : (cm_rep_expr_temps_safe e )) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa_2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb_2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs_2)
  **  (cm_expr_payload e pa_2 pb_2 pargs_2 )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  EX (pargs: Z)  (pb: Z)  (pa: Z)  (x: cm_expr)  (t: cm_type) ,
  “ (expr_pre <> 0) ” 
  &&  “ (cm_rep_expr_temps_safe e ) ” 
  &&  “ (e = (CMPutiE (x) (t))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (pa <> 0) ” 
  &&  “ (pb = 0) ” 
  &&  “ (pargs = 0) ”
  &&  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_rep pa x )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
) \/
(
forall (expr_pre: Z) (e: cm_expr) (pa_2: Z) (pb_2: Z) (pargs_2: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 12)) (PreH2 : ((cm_rep_expr_kind (e)) <> 11)) (PreH3 : ((cm_rep_expr_kind (e)) <> 8)) (PreH4 : ((cm_rep_expr_kind (e)) <> 7)) (PreH5 : ((cm_rep_expr_kind (e)) <> 6)) (PreH6 : ((cm_rep_expr_kind (e)) <> 5)) (PreH7 : ((cm_rep_expr_kind (e)) <> 4)) (PreH8 : ((cm_rep_expr_kind (e)) <> 3)) (PreH9 : (expr_pre <> 0)) (PreH10 : (cm_rep_expr_temps_safe e )) ,
  (cm_expr_payload e pa_2 pb_2 pargs_2 )
|--
  EX (x: cm_expr)  (t: cm_type) ,
  “ (pargs_2 = 0) ” 
  &&  “ (pb_2 = 0) ” 
  &&  “ (pargs_2 = 0) ” 
  &&  “ (pb_2 = 0) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (cm_rep_expr_temps_safe e ) ” 
  &&  “ (e = (CMPutiE (x) (t))) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (pa_2 <> 0) ”
  &&  (cm_expr_rep pa_2 x )
).

Definition cm_expr_temps_entail_wit_10 := 
(
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa_2: Z) (pb_2: Z) (pargs_2: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 13)) (PreH2 : ((cm_rep_expr_kind (e)) <> 12)) (PreH3 : ((cm_rep_expr_kind (e)) <> 11)) (PreH4 : ((cm_rep_expr_kind (e)) <> 8)) (PreH5 : ((cm_rep_expr_kind (e)) <> 7)) (PreH6 : ((cm_rep_expr_kind (e)) <> 6)) (PreH7 : ((cm_rep_expr_kind (e)) <> 5)) (PreH8 : ((cm_rep_expr_kind (e)) <> 4)) (PreH9 : ((cm_rep_expr_kind (e)) <> 3)) (PreH10 : (expr_pre <> 0)) (PreH11 : (cm_rep_expr_temps_safe e )) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa_2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb_2)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs_2)
  **  (cm_expr_payload e pa_2 pb_2 pargs_2 )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  EX (pargs: Z)  (pb: Z)  (pa: Z)  (x: cm_expr)  (t: cm_type) ,
  “ (expr_pre <> 0) ” 
  &&  “ (cm_rep_expr_temps_safe e ) ” 
  &&  “ (e = (CMExitE (x) (t))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (pa <> 0) ” 
  &&  “ (pb = 0) ” 
  &&  “ (pargs = 0) ”
  &&  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_rep pa x )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
) \/
(
forall (expr_pre: Z) (e: cm_expr) (pa_2: Z) (pb_2: Z) (pargs_2: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 13)) (PreH2 : ((cm_rep_expr_kind (e)) <> 12)) (PreH3 : ((cm_rep_expr_kind (e)) <> 11)) (PreH4 : ((cm_rep_expr_kind (e)) <> 8)) (PreH5 : ((cm_rep_expr_kind (e)) <> 7)) (PreH6 : ((cm_rep_expr_kind (e)) <> 6)) (PreH7 : ((cm_rep_expr_kind (e)) <> 5)) (PreH8 : ((cm_rep_expr_kind (e)) <> 4)) (PreH9 : ((cm_rep_expr_kind (e)) <> 3)) (PreH10 : (expr_pre <> 0)) (PreH11 : (cm_rep_expr_temps_safe e )) ,
  (cm_expr_payload e pa_2 pb_2 pargs_2 )
|--
  EX (x: cm_expr)  (t: cm_type) ,
  “ (pargs_2 = 0) ” 
  &&  “ (pb_2 = 0) ” 
  &&  “ (pargs_2 = 0) ” 
  &&  “ (pb_2 = 0) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (cm_rep_expr_temps_safe e ) ” 
  &&  “ (e = (CMExitE (x) (t))) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (pa_2 <> 0) ”
  &&  (cm_expr_rep pa_2 x )
).

Definition cm_expr_temps_return_wit_1 := 
(
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (retval: Z) (PreH1 : (retval = (cm_imax ((cm_tleft ((cm_expr_tpair (x))))) ((1 + (cm_tright ((cm_expr_tpair (y)))) ))))) (PreH2 : (cm_rep_expr_temps_safe y )) (PreH3 : (cm_rep_expr_temps_safe x )) (PreH4 : (expr_pre <> 0)) (PreH5 : (cm_rep_expr_temps_safe e )) (PreH6 : (e = (CMAssignE (x) (y) (t)))) (PreH7 : (out_lvalue = 0)) (PreH8 : (out_rvalue = 0)) (PreH9 : (cm_rep_expr_temps_safe x )) (PreH10 : (cm_rep_expr_temps_safe y )) (PreH11 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |-> out_lvalue)
  **  ((rvalue_pre) # Int  |-> retval)
|--
  “ (cm_rep_expr_temps_safe e ) ”
  &&  (cm_expr_rep expr_pre e )
  **  ((lvalue_pre) # Int  |-> (cm_tleft ((cm_expr_tpair (e)))))
  **  ((rvalue_pre) # Int  |-> (cm_tright ((cm_expr_tpair (e)))))
) \/
(
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (retval: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (retval = (cm_imax ((cm_tleft ((cm_expr_tpair (x))))) ((1 + (cm_tright ((cm_expr_tpair (y)))) ))))) (PreH10 : (cm_rep_expr_temps_safe y )) (PreH11 : (cm_rep_expr_temps_safe x )) (PreH12 : (expr_pre <> 0)) (PreH13 : (cm_rep_expr_temps_safe e )) (PreH14 : (e = (CMAssignE (x) (y) (t)))) (PreH15 : (out_lvalue = 0)) (PreH16 : (out_rvalue = 0)) (PreH17 : (cm_rep_expr_temps_safe x )) (PreH18 : (cm_rep_expr_temps_safe y )) (PreH19 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ” 
  &&  “ (retval = (cm_tright ((cm_expr_tpair (e))))) ”
  &&  (cm_expr_rep expr_pre e )
).

Definition cm_expr_temps_return_wit_1_split_goal_1 := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (retval: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (retval = (cm_imax ((cm_tleft ((cm_expr_tpair (x))))) ((1 + (cm_tright ((cm_expr_tpair (y)))) ))))) (PreH10 : (cm_rep_expr_temps_safe y )) (PreH11 : (cm_rep_expr_temps_safe x )) (PreH12 : (expr_pre <> 0)) (PreH13 : (cm_rep_expr_temps_safe e )) (PreH14 : (e = (CMAssignE (x) (y) (t)))) (PreH15 : (out_lvalue = 0)) (PreH16 : (out_rvalue = 0)) (PreH17 : (cm_rep_expr_temps_safe x )) (PreH18 : (cm_rep_expr_temps_safe y )) (PreH19 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ”
.

Definition cm_expr_temps_return_wit_1_split_goal_2 := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (retval: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (retval = (cm_imax ((cm_tleft ((cm_expr_tpair (x))))) ((1 + (cm_tright ((cm_expr_tpair (y)))) ))))) (PreH10 : (cm_rep_expr_temps_safe y )) (PreH11 : (cm_rep_expr_temps_safe x )) (PreH12 : (expr_pre <> 0)) (PreH13 : (cm_rep_expr_temps_safe e )) (PreH14 : (e = (CMAssignE (x) (y) (t)))) (PreH15 : (out_lvalue = 0)) (PreH16 : (out_rvalue = 0)) (PreH17 : (cm_rep_expr_temps_safe x )) (PreH18 : (cm_rep_expr_temps_safe y )) (PreH19 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  “ (retval = (cm_tright ((cm_expr_tpair (e))))) ”
.

Definition cm_expr_temps_return_wit_1_split_goal_spatial := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (retval: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (retval = (cm_imax ((cm_tleft ((cm_expr_tpair (x))))) ((1 + (cm_tright ((cm_expr_tpair (y)))) ))))) (PreH10 : (cm_rep_expr_temps_safe y )) (PreH11 : (cm_rep_expr_temps_safe x )) (PreH12 : (expr_pre <> 0)) (PreH13 : (cm_rep_expr_temps_safe e )) (PreH14 : (e = (CMAssignE (x) (y) (t)))) (PreH15 : (out_lvalue = 0)) (PreH16 : (out_rvalue = 0)) (PreH17 : (cm_rep_expr_temps_safe x )) (PreH18 : (cm_rep_expr_temps_safe y )) (PreH19 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  (cm_expr_rep expr_pre e )
.

Definition cm_expr_temps_return_wit_2 := 
(
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (retval: Z) (PreH1 : (retval = (cm_imax ((cm_tright ((cm_expr_tpair (x))))) ((cm_tright ((cm_expr_tpair (y)))))))) (PreH2 : ((cm_rep_expr_op (e)) = 0)) (PreH3 : (cm_rep_expr_temps_safe y )) (PreH4 : (cm_rep_expr_temps_safe x )) (PreH5 : (expr_pre <> 0)) (PreH6 : (cm_rep_expr_temps_safe e )) (PreH7 : (e = (CMBinaryE (op) (x) (y) (t)))) (PreH8 : (out_lvalue = 0)) (PreH9 : (out_rvalue = 0)) (PreH10 : (cm_rep_expr_temps_safe x )) (PreH11 : (cm_rep_expr_temps_safe y )) (PreH12 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |-> out_lvalue)
  **  ((rvalue_pre) # Int  |-> retval)
|--
  “ (cm_rep_expr_temps_safe e ) ”
  &&  (cm_expr_rep expr_pre e )
  **  ((lvalue_pre) # Int  |-> (cm_tleft ((cm_expr_tpair (e)))))
  **  ((rvalue_pre) # Int  |-> (cm_tright ((cm_expr_tpair (e)))))
) \/
(
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (retval: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (retval = (cm_imax ((cm_tright ((cm_expr_tpair (x))))) ((cm_tright ((cm_expr_tpair (y)))))))) (PreH10 : ((cm_rep_expr_op (e)) = 0)) (PreH11 : (cm_rep_expr_temps_safe y )) (PreH12 : (cm_rep_expr_temps_safe x )) (PreH13 : (expr_pre <> 0)) (PreH14 : (cm_rep_expr_temps_safe e )) (PreH15 : (e = (CMBinaryE (op) (x) (y) (t)))) (PreH16 : (out_lvalue = 0)) (PreH17 : (out_rvalue = 0)) (PreH18 : (cm_rep_expr_temps_safe x )) (PreH19 : (cm_rep_expr_temps_safe y )) (PreH20 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ” 
  &&  “ (retval = (cm_tright ((cm_expr_tpair (e))))) ”
  &&  (cm_expr_rep expr_pre e )
).

Definition cm_expr_temps_return_wit_2_split_goal_1 := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (retval: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (retval = (cm_imax ((cm_tright ((cm_expr_tpair (x))))) ((cm_tright ((cm_expr_tpair (y)))))))) (PreH10 : ((cm_rep_expr_op (e)) = 0)) (PreH11 : (cm_rep_expr_temps_safe y )) (PreH12 : (cm_rep_expr_temps_safe x )) (PreH13 : (expr_pre <> 0)) (PreH14 : (cm_rep_expr_temps_safe e )) (PreH15 : (e = (CMBinaryE (op) (x) (y) (t)))) (PreH16 : (out_lvalue = 0)) (PreH17 : (out_rvalue = 0)) (PreH18 : (cm_rep_expr_temps_safe x )) (PreH19 : (cm_rep_expr_temps_safe y )) (PreH20 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ”
.

Definition cm_expr_temps_return_wit_2_split_goal_2 := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (retval: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (retval = (cm_imax ((cm_tright ((cm_expr_tpair (x))))) ((cm_tright ((cm_expr_tpair (y)))))))) (PreH10 : ((cm_rep_expr_op (e)) = 0)) (PreH11 : (cm_rep_expr_temps_safe y )) (PreH12 : (cm_rep_expr_temps_safe x )) (PreH13 : (expr_pre <> 0)) (PreH14 : (cm_rep_expr_temps_safe e )) (PreH15 : (e = (CMBinaryE (op) (x) (y) (t)))) (PreH16 : (out_lvalue = 0)) (PreH17 : (out_rvalue = 0)) (PreH18 : (cm_rep_expr_temps_safe x )) (PreH19 : (cm_rep_expr_temps_safe y )) (PreH20 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  “ (retval = (cm_tright ((cm_expr_tpair (e))))) ”
.

Definition cm_expr_temps_return_wit_2_split_goal_spatial := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (retval: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (retval = (cm_imax ((cm_tright ((cm_expr_tpair (x))))) ((cm_tright ((cm_expr_tpair (y)))))))) (PreH10 : ((cm_rep_expr_op (e)) = 0)) (PreH11 : (cm_rep_expr_temps_safe y )) (PreH12 : (cm_rep_expr_temps_safe x )) (PreH13 : (expr_pre <> 0)) (PreH14 : (cm_rep_expr_temps_safe e )) (PreH15 : (e = (CMBinaryE (op) (x) (y) (t)))) (PreH16 : (out_lvalue = 0)) (PreH17 : (out_rvalue = 0)) (PreH18 : (cm_rep_expr_temps_safe x )) (PreH19 : (cm_rep_expr_temps_safe y )) (PreH20 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  (cm_expr_rep expr_pre e )
.

Definition cm_expr_temps_return_wit_3 := 
(
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (retval: Z) (PreH1 : (retval = (cm_imax ((cm_tright ((cm_expr_tpair (x))))) ((cm_tright ((cm_expr_tpair (y)))))))) (PreH2 : ((cm_rep_expr_op (e)) = 1)) (PreH3 : ((cm_rep_expr_op (e)) <> 0)) (PreH4 : (cm_rep_expr_temps_safe y )) (PreH5 : (cm_rep_expr_temps_safe x )) (PreH6 : (expr_pre <> 0)) (PreH7 : (cm_rep_expr_temps_safe e )) (PreH8 : (e = (CMBinaryE (op) (x) (y) (t)))) (PreH9 : (out_lvalue = 0)) (PreH10 : (out_rvalue = 0)) (PreH11 : (cm_rep_expr_temps_safe x )) (PreH12 : (cm_rep_expr_temps_safe y )) (PreH13 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |-> out_lvalue)
  **  ((rvalue_pre) # Int  |-> retval)
|--
  “ (cm_rep_expr_temps_safe e ) ”
  &&  (cm_expr_rep expr_pre e )
  **  ((lvalue_pre) # Int  |-> (cm_tleft ((cm_expr_tpair (e)))))
  **  ((rvalue_pre) # Int  |-> (cm_tright ((cm_expr_tpair (e)))))
) \/
(
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (retval: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (retval = (cm_imax ((cm_tright ((cm_expr_tpair (x))))) ((cm_tright ((cm_expr_tpair (y)))))))) (PreH10 : ((cm_rep_expr_op (e)) = 1)) (PreH11 : ((cm_rep_expr_op (e)) <> 0)) (PreH12 : (cm_rep_expr_temps_safe y )) (PreH13 : (cm_rep_expr_temps_safe x )) (PreH14 : (expr_pre <> 0)) (PreH15 : (cm_rep_expr_temps_safe e )) (PreH16 : (e = (CMBinaryE (op) (x) (y) (t)))) (PreH17 : (out_lvalue = 0)) (PreH18 : (out_rvalue = 0)) (PreH19 : (cm_rep_expr_temps_safe x )) (PreH20 : (cm_rep_expr_temps_safe y )) (PreH21 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ” 
  &&  “ (retval = (cm_tright ((cm_expr_tpair (e))))) ”
  &&  (cm_expr_rep expr_pre e )
).

Definition cm_expr_temps_return_wit_3_split_goal_1 := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (retval: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (retval = (cm_imax ((cm_tright ((cm_expr_tpair (x))))) ((cm_tright ((cm_expr_tpair (y)))))))) (PreH10 : ((cm_rep_expr_op (e)) = 1)) (PreH11 : ((cm_rep_expr_op (e)) <> 0)) (PreH12 : (cm_rep_expr_temps_safe y )) (PreH13 : (cm_rep_expr_temps_safe x )) (PreH14 : (expr_pre <> 0)) (PreH15 : (cm_rep_expr_temps_safe e )) (PreH16 : (e = (CMBinaryE (op) (x) (y) (t)))) (PreH17 : (out_lvalue = 0)) (PreH18 : (out_rvalue = 0)) (PreH19 : (cm_rep_expr_temps_safe x )) (PreH20 : (cm_rep_expr_temps_safe y )) (PreH21 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ”
.

Definition cm_expr_temps_return_wit_3_split_goal_2 := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (retval: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (retval = (cm_imax ((cm_tright ((cm_expr_tpair (x))))) ((cm_tright ((cm_expr_tpair (y)))))))) (PreH10 : ((cm_rep_expr_op (e)) = 1)) (PreH11 : ((cm_rep_expr_op (e)) <> 0)) (PreH12 : (cm_rep_expr_temps_safe y )) (PreH13 : (cm_rep_expr_temps_safe x )) (PreH14 : (expr_pre <> 0)) (PreH15 : (cm_rep_expr_temps_safe e )) (PreH16 : (e = (CMBinaryE (op) (x) (y) (t)))) (PreH17 : (out_lvalue = 0)) (PreH18 : (out_rvalue = 0)) (PreH19 : (cm_rep_expr_temps_safe x )) (PreH20 : (cm_rep_expr_temps_safe y )) (PreH21 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  “ (retval = (cm_tright ((cm_expr_tpair (e))))) ”
.

Definition cm_expr_temps_return_wit_3_split_goal_spatial := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (retval: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (retval = (cm_imax ((cm_tright ((cm_expr_tpair (x))))) ((cm_tright ((cm_expr_tpair (y)))))))) (PreH10 : ((cm_rep_expr_op (e)) = 1)) (PreH11 : ((cm_rep_expr_op (e)) <> 0)) (PreH12 : (cm_rep_expr_temps_safe y )) (PreH13 : (cm_rep_expr_temps_safe x )) (PreH14 : (expr_pre <> 0)) (PreH15 : (cm_rep_expr_temps_safe e )) (PreH16 : (e = (CMBinaryE (op) (x) (y) (t)))) (PreH17 : (out_lvalue = 0)) (PreH18 : (out_rvalue = 0)) (PreH19 : (cm_rep_expr_temps_safe x )) (PreH20 : (cm_rep_expr_temps_safe y )) (PreH21 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  (cm_expr_rep expr_pre e )
.

Definition cm_expr_temps_return_wit_4 := 
(
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (retval: Z) (PreH1 : (retval = (cm_imax ((cm_tright ((cm_expr_tpair (x))))) ((1 + (cm_tright ((cm_expr_tpair (y)))) ))))) (PreH2 : ((cm_rep_expr_op (e)) <> 1)) (PreH3 : ((cm_rep_expr_op (e)) <> 0)) (PreH4 : (cm_rep_expr_temps_safe y )) (PreH5 : (cm_rep_expr_temps_safe x )) (PreH6 : (expr_pre <> 0)) (PreH7 : (cm_rep_expr_temps_safe e )) (PreH8 : (e = (CMBinaryE (op) (x) (y) (t)))) (PreH9 : (out_lvalue = 0)) (PreH10 : (out_rvalue = 0)) (PreH11 : (cm_rep_expr_temps_safe x )) (PreH12 : (cm_rep_expr_temps_safe y )) (PreH13 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |-> out_lvalue)
  **  ((rvalue_pre) # Int  |-> retval)
|--
  “ (cm_rep_expr_temps_safe e ) ”
  &&  (cm_expr_rep expr_pre e )
  **  ((lvalue_pre) # Int  |-> (cm_tleft ((cm_expr_tpair (e)))))
  **  ((rvalue_pre) # Int  |-> (cm_tright ((cm_expr_tpair (e)))))
) \/
(
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (retval: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (retval = (cm_imax ((cm_tright ((cm_expr_tpair (x))))) ((1 + (cm_tright ((cm_expr_tpair (y)))) ))))) (PreH10 : ((cm_rep_expr_op (e)) <> 1)) (PreH11 : ((cm_rep_expr_op (e)) <> 0)) (PreH12 : (cm_rep_expr_temps_safe y )) (PreH13 : (cm_rep_expr_temps_safe x )) (PreH14 : (expr_pre <> 0)) (PreH15 : (cm_rep_expr_temps_safe e )) (PreH16 : (e = (CMBinaryE (op) (x) (y) (t)))) (PreH17 : (out_lvalue = 0)) (PreH18 : (out_rvalue = 0)) (PreH19 : (cm_rep_expr_temps_safe x )) (PreH20 : (cm_rep_expr_temps_safe y )) (PreH21 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ” 
  &&  “ (retval = (cm_tright ((cm_expr_tpair (e))))) ”
  &&  (cm_expr_rep expr_pre e )
).

Definition cm_expr_temps_return_wit_4_split_goal_1 := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (retval: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (retval = (cm_imax ((cm_tright ((cm_expr_tpair (x))))) ((1 + (cm_tright ((cm_expr_tpair (y)))) ))))) (PreH10 : ((cm_rep_expr_op (e)) <> 1)) (PreH11 : ((cm_rep_expr_op (e)) <> 0)) (PreH12 : (cm_rep_expr_temps_safe y )) (PreH13 : (cm_rep_expr_temps_safe x )) (PreH14 : (expr_pre <> 0)) (PreH15 : (cm_rep_expr_temps_safe e )) (PreH16 : (e = (CMBinaryE (op) (x) (y) (t)))) (PreH17 : (out_lvalue = 0)) (PreH18 : (out_rvalue = 0)) (PreH19 : (cm_rep_expr_temps_safe x )) (PreH20 : (cm_rep_expr_temps_safe y )) (PreH21 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ”
.

Definition cm_expr_temps_return_wit_4_split_goal_2 := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (retval: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (retval = (cm_imax ((cm_tright ((cm_expr_tpair (x))))) ((1 + (cm_tright ((cm_expr_tpair (y)))) ))))) (PreH10 : ((cm_rep_expr_op (e)) <> 1)) (PreH11 : ((cm_rep_expr_op (e)) <> 0)) (PreH12 : (cm_rep_expr_temps_safe y )) (PreH13 : (cm_rep_expr_temps_safe x )) (PreH14 : (expr_pre <> 0)) (PreH15 : (cm_rep_expr_temps_safe e )) (PreH16 : (e = (CMBinaryE (op) (x) (y) (t)))) (PreH17 : (out_lvalue = 0)) (PreH18 : (out_rvalue = 0)) (PreH19 : (cm_rep_expr_temps_safe x )) (PreH20 : (cm_rep_expr_temps_safe y )) (PreH21 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  “ (retval = (cm_tright ((cm_expr_tpair (e))))) ”
.

Definition cm_expr_temps_return_wit_4_split_goal_spatial := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (retval: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (retval = (cm_imax ((cm_tright ((cm_expr_tpair (x))))) ((1 + (cm_tright ((cm_expr_tpair (y)))) ))))) (PreH10 : ((cm_rep_expr_op (e)) <> 1)) (PreH11 : ((cm_rep_expr_op (e)) <> 0)) (PreH12 : (cm_rep_expr_temps_safe y )) (PreH13 : (cm_rep_expr_temps_safe x )) (PreH14 : (expr_pre <> 0)) (PreH15 : (cm_rep_expr_temps_safe e )) (PreH16 : (e = (CMBinaryE (op) (x) (y) (t)))) (PreH17 : (out_lvalue = 0)) (PreH18 : (out_rvalue = 0)) (PreH19 : (cm_rep_expr_temps_safe x )) (PreH20 : (cm_rep_expr_temps_safe y )) (PreH21 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  (cm_expr_rep expr_pre e )
.

Definition cm_expr_temps_return_wit_5 := 
(
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_op (e)) = 2)) (PreH2 : (cm_rep_expr_temps_safe x )) (PreH3 : (expr_pre <> 0)) (PreH4 : (cm_rep_expr_temps_safe e )) (PreH5 : (e = (CMUnaryE (op) (x) (t)))) (PreH6 : (out_lvalue = 0)) (PreH7 : (out_rvalue = 0)) (PreH8 : (cm_rep_expr_temps_safe x )) (PreH9 : (pa <> 0)) (PreH10 : (pb = 0)) (PreH11 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |-> (cm_tright ((cm_expr_tpair (x)))))
  **  ((rvalue_pre) # Int  |-> (cm_tright ((cm_expr_tpair (x)))))
|--
  “ (cm_rep_expr_temps_safe e ) ”
  &&  (cm_expr_rep expr_pre e )
  **  ((lvalue_pre) # Int  |-> (cm_tleft ((cm_expr_tpair (e)))))
  **  ((rvalue_pre) # Int  |-> (cm_tright ((cm_expr_tpair (e)))))
) \/
(
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_op (e)) = 2)) (PreH10 : (cm_rep_expr_temps_safe x )) (PreH11 : (expr_pre <> 0)) (PreH12 : (cm_rep_expr_temps_safe e )) (PreH13 : (e = (CMUnaryE (op) (x) (t)))) (PreH14 : (out_lvalue = 0)) (PreH15 : (out_rvalue = 0)) (PreH16 : (cm_rep_expr_temps_safe x )) (PreH17 : (pa <> 0)) (PreH18 : (pb = 0)) (PreH19 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  “ ((cm_tright ((cm_expr_tpair (x)))) = (cm_tleft ((cm_expr_tpair (e))))) ” 
  &&  “ ((cm_tright ((cm_expr_tpair (x)))) = (cm_tright ((cm_expr_tpair (e))))) ”
  &&  (cm_expr_rep expr_pre e )
).

Definition cm_expr_temps_return_wit_5_split_goal_1 := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_op (e)) = 2)) (PreH10 : (cm_rep_expr_temps_safe x )) (PreH11 : (expr_pre <> 0)) (PreH12 : (cm_rep_expr_temps_safe e )) (PreH13 : (e = (CMUnaryE (op) (x) (t)))) (PreH14 : (out_lvalue = 0)) (PreH15 : (out_rvalue = 0)) (PreH16 : (cm_rep_expr_temps_safe x )) (PreH17 : (pa <> 0)) (PreH18 : (pb = 0)) (PreH19 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  “ ((cm_tright ((cm_expr_tpair (x)))) = (cm_tleft ((cm_expr_tpair (e))))) ”
.

Definition cm_expr_temps_return_wit_5_split_goal_2 := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_op (e)) = 2)) (PreH10 : (cm_rep_expr_temps_safe x )) (PreH11 : (expr_pre <> 0)) (PreH12 : (cm_rep_expr_temps_safe e )) (PreH13 : (e = (CMUnaryE (op) (x) (t)))) (PreH14 : (out_lvalue = 0)) (PreH15 : (out_rvalue = 0)) (PreH16 : (cm_rep_expr_temps_safe x )) (PreH17 : (pa <> 0)) (PreH18 : (pb = 0)) (PreH19 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  “ ((cm_tright ((cm_expr_tpair (x)))) = (cm_tright ((cm_expr_tpair (e))))) ”
.

Definition cm_expr_temps_return_wit_5_split_goal_spatial := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_op (e)) = 2)) (PreH10 : (cm_rep_expr_temps_safe x )) (PreH11 : (expr_pre <> 0)) (PreH12 : (cm_rep_expr_temps_safe e )) (PreH13 : (e = (CMUnaryE (op) (x) (t)))) (PreH14 : (out_lvalue = 0)) (PreH15 : (out_rvalue = 0)) (PreH16 : (cm_rep_expr_temps_safe x )) (PreH17 : (pa <> 0)) (PreH18 : (pb = 0)) (PreH19 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  (cm_expr_rep expr_pre e )
.

Definition cm_expr_temps_return_wit_6 := 
(
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_op (e)) = 3)) (PreH2 : ((cm_rep_expr_op (e)) <> 2)) (PreH3 : (cm_rep_expr_temps_safe x )) (PreH4 : (expr_pre <> 0)) (PreH5 : (cm_rep_expr_temps_safe e )) (PreH6 : (e = (CMUnaryE (op) (x) (t)))) (PreH7 : (out_lvalue = 0)) (PreH8 : (out_rvalue = 0)) (PreH9 : (cm_rep_expr_temps_safe x )) (PreH10 : (pa <> 0)) (PreH11 : (pb = 0)) (PreH12 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |-> out_lvalue)
  **  ((rvalue_pre) # Int  |-> (cm_tleft ((cm_expr_tpair (x)))))
|--
  “ (cm_rep_expr_temps_safe e ) ”
  &&  (cm_expr_rep expr_pre e )
  **  ((lvalue_pre) # Int  |-> (cm_tleft ((cm_expr_tpair (e)))))
  **  ((rvalue_pre) # Int  |-> (cm_tright ((cm_expr_tpair (e)))))
) \/
(
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_op (e)) = 3)) (PreH10 : ((cm_rep_expr_op (e)) <> 2)) (PreH11 : (cm_rep_expr_temps_safe x )) (PreH12 : (expr_pre <> 0)) (PreH13 : (cm_rep_expr_temps_safe e )) (PreH14 : (e = (CMUnaryE (op) (x) (t)))) (PreH15 : (out_lvalue = 0)) (PreH16 : (out_rvalue = 0)) (PreH17 : (cm_rep_expr_temps_safe x )) (PreH18 : (pa <> 0)) (PreH19 : (pb = 0)) (PreH20 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ” 
  &&  “ ((cm_tleft ((cm_expr_tpair (x)))) = (cm_tright ((cm_expr_tpair (e))))) ”
  &&  (cm_expr_rep expr_pre e )
).

Definition cm_expr_temps_return_wit_6_split_goal_1 := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_op (e)) = 3)) (PreH10 : ((cm_rep_expr_op (e)) <> 2)) (PreH11 : (cm_rep_expr_temps_safe x )) (PreH12 : (expr_pre <> 0)) (PreH13 : (cm_rep_expr_temps_safe e )) (PreH14 : (e = (CMUnaryE (op) (x) (t)))) (PreH15 : (out_lvalue = 0)) (PreH16 : (out_rvalue = 0)) (PreH17 : (cm_rep_expr_temps_safe x )) (PreH18 : (pa <> 0)) (PreH19 : (pb = 0)) (PreH20 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ”
.

Definition cm_expr_temps_return_wit_6_split_goal_2 := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_op (e)) = 3)) (PreH10 : ((cm_rep_expr_op (e)) <> 2)) (PreH11 : (cm_rep_expr_temps_safe x )) (PreH12 : (expr_pre <> 0)) (PreH13 : (cm_rep_expr_temps_safe e )) (PreH14 : (e = (CMUnaryE (op) (x) (t)))) (PreH15 : (out_lvalue = 0)) (PreH16 : (out_rvalue = 0)) (PreH17 : (cm_rep_expr_temps_safe x )) (PreH18 : (pa <> 0)) (PreH19 : (pb = 0)) (PreH20 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  “ ((cm_tleft ((cm_expr_tpair (x)))) = (cm_tright ((cm_expr_tpair (e))))) ”
.

Definition cm_expr_temps_return_wit_6_split_goal_spatial := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_op (e)) = 3)) (PreH10 : ((cm_rep_expr_op (e)) <> 2)) (PreH11 : (cm_rep_expr_temps_safe x )) (PreH12 : (expr_pre <> 0)) (PreH13 : (cm_rep_expr_temps_safe e )) (PreH14 : (e = (CMUnaryE (op) (x) (t)))) (PreH15 : (out_lvalue = 0)) (PreH16 : (out_rvalue = 0)) (PreH17 : (cm_rep_expr_temps_safe x )) (PreH18 : (pa <> 0)) (PreH19 : (pb = 0)) (PreH20 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  (cm_expr_rep expr_pre e )
.

Definition cm_expr_temps_return_wit_7 := 
(
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_op (e)) <> 3)) (PreH2 : ((cm_rep_expr_op (e)) <> 2)) (PreH3 : (cm_rep_expr_temps_safe x )) (PreH4 : (expr_pre <> 0)) (PreH5 : (cm_rep_expr_temps_safe e )) (PreH6 : (e = (CMUnaryE (op) (x) (t)))) (PreH7 : (out_lvalue = 0)) (PreH8 : (out_rvalue = 0)) (PreH9 : (cm_rep_expr_temps_safe x )) (PreH10 : (pa <> 0)) (PreH11 : (pb = 0)) (PreH12 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |-> out_lvalue)
  **  ((rvalue_pre) # Int  |-> (cm_tright ((cm_expr_tpair (x)))))
|--
  “ (cm_rep_expr_temps_safe e ) ”
  &&  (cm_expr_rep expr_pre e )
  **  ((lvalue_pre) # Int  |-> (cm_tleft ((cm_expr_tpair (e)))))
  **  ((rvalue_pre) # Int  |-> (cm_tright ((cm_expr_tpair (e)))))
) \/
(
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_op (e)) <> 3)) (PreH10 : ((cm_rep_expr_op (e)) <> 2)) (PreH11 : (cm_rep_expr_temps_safe x )) (PreH12 : (expr_pre <> 0)) (PreH13 : (cm_rep_expr_temps_safe e )) (PreH14 : (e = (CMUnaryE (op) (x) (t)))) (PreH15 : (out_lvalue = 0)) (PreH16 : (out_rvalue = 0)) (PreH17 : (cm_rep_expr_temps_safe x )) (PreH18 : (pa <> 0)) (PreH19 : (pb = 0)) (PreH20 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ” 
  &&  “ ((cm_tright ((cm_expr_tpair (x)))) = (cm_tright ((cm_expr_tpair (e))))) ”
  &&  (cm_expr_rep expr_pre e )
).

Definition cm_expr_temps_return_wit_7_split_goal_1 := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_op (e)) <> 3)) (PreH10 : ((cm_rep_expr_op (e)) <> 2)) (PreH11 : (cm_rep_expr_temps_safe x )) (PreH12 : (expr_pre <> 0)) (PreH13 : (cm_rep_expr_temps_safe e )) (PreH14 : (e = (CMUnaryE (op) (x) (t)))) (PreH15 : (out_lvalue = 0)) (PreH16 : (out_rvalue = 0)) (PreH17 : (cm_rep_expr_temps_safe x )) (PreH18 : (pa <> 0)) (PreH19 : (pb = 0)) (PreH20 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ”
.

Definition cm_expr_temps_return_wit_7_split_goal_2 := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_op (e)) <> 3)) (PreH10 : ((cm_rep_expr_op (e)) <> 2)) (PreH11 : (cm_rep_expr_temps_safe x )) (PreH12 : (expr_pre <> 0)) (PreH13 : (cm_rep_expr_temps_safe e )) (PreH14 : (e = (CMUnaryE (op) (x) (t)))) (PreH15 : (out_lvalue = 0)) (PreH16 : (out_rvalue = 0)) (PreH17 : (cm_rep_expr_temps_safe x )) (PreH18 : (pa <> 0)) (PreH19 : (pb = 0)) (PreH20 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  “ ((cm_tright ((cm_expr_tpair (x)))) = (cm_tright ((cm_expr_tpair (e))))) ”
.

Definition cm_expr_temps_return_wit_7_split_goal_spatial := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_op (e)) <> 3)) (PreH10 : ((cm_rep_expr_op (e)) <> 2)) (PreH11 : (cm_rep_expr_temps_safe x )) (PreH12 : (expr_pre <> 0)) (PreH13 : (cm_rep_expr_temps_safe e )) (PreH14 : (e = (CMUnaryE (op) (x) (t)))) (PreH15 : (out_lvalue = 0)) (PreH16 : (out_rvalue = 0)) (PreH17 : (cm_rep_expr_temps_safe x )) (PreH18 : (pa <> 0)) (PreH19 : (pb = 0)) (PreH20 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  (cm_expr_rep expr_pre e )
.

Definition cm_expr_temps_return_wit_8 := 
(
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (retval: Z) (PreH1 : (retval = (cm_imax ((cm_tright ((cm_expr_tpair (x))))) ((1 + (cm_tright ((cm_expr_tpair (y)))) ))))) (PreH2 : (cm_rep_expr_temps_safe y )) (PreH3 : (cm_rep_expr_temps_safe x )) (PreH4 : (expr_pre <> 0)) (PreH5 : (cm_rep_expr_temps_safe e )) (PreH6 : (e = (CMIndexE (x) (y) (t)))) (PreH7 : (out_lvalue = 0)) (PreH8 : (out_rvalue = 0)) (PreH9 : (cm_rep_expr_temps_safe x )) (PreH10 : (cm_rep_expr_temps_safe y )) (PreH11 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |-> retval)
  **  ((rvalue_pre) # Int  |-> retval)
|--
  “ (cm_rep_expr_temps_safe e ) ”
  &&  (cm_expr_rep expr_pre e )
  **  ((lvalue_pre) # Int  |-> (cm_tleft ((cm_expr_tpair (e)))))
  **  ((rvalue_pre) # Int  |-> (cm_tright ((cm_expr_tpair (e)))))
) \/
(
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (retval: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (retval = (cm_imax ((cm_tright ((cm_expr_tpair (x))))) ((1 + (cm_tright ((cm_expr_tpair (y)))) ))))) (PreH10 : (cm_rep_expr_temps_safe y )) (PreH11 : (cm_rep_expr_temps_safe x )) (PreH12 : (expr_pre <> 0)) (PreH13 : (cm_rep_expr_temps_safe e )) (PreH14 : (e = (CMIndexE (x) (y) (t)))) (PreH15 : (out_lvalue = 0)) (PreH16 : (out_rvalue = 0)) (PreH17 : (cm_rep_expr_temps_safe x )) (PreH18 : (cm_rep_expr_temps_safe y )) (PreH19 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  “ (retval = (cm_tleft ((cm_expr_tpair (e))))) ” 
  &&  “ (retval = (cm_tright ((cm_expr_tpair (e))))) ”
  &&  (cm_expr_rep expr_pre e )
).

Definition cm_expr_temps_return_wit_8_split_goal_1 := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (retval: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (retval = (cm_imax ((cm_tright ((cm_expr_tpair (x))))) ((1 + (cm_tright ((cm_expr_tpair (y)))) ))))) (PreH10 : (cm_rep_expr_temps_safe y )) (PreH11 : (cm_rep_expr_temps_safe x )) (PreH12 : (expr_pre <> 0)) (PreH13 : (cm_rep_expr_temps_safe e )) (PreH14 : (e = (CMIndexE (x) (y) (t)))) (PreH15 : (out_lvalue = 0)) (PreH16 : (out_rvalue = 0)) (PreH17 : (cm_rep_expr_temps_safe x )) (PreH18 : (cm_rep_expr_temps_safe y )) (PreH19 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  “ (retval = (cm_tleft ((cm_expr_tpair (e))))) ”
.

Definition cm_expr_temps_return_wit_8_split_goal_2 := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (retval: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (retval = (cm_imax ((cm_tright ((cm_expr_tpair (x))))) ((1 + (cm_tright ((cm_expr_tpair (y)))) ))))) (PreH10 : (cm_rep_expr_temps_safe y )) (PreH11 : (cm_rep_expr_temps_safe x )) (PreH12 : (expr_pre <> 0)) (PreH13 : (cm_rep_expr_temps_safe e )) (PreH14 : (e = (CMIndexE (x) (y) (t)))) (PreH15 : (out_lvalue = 0)) (PreH16 : (out_rvalue = 0)) (PreH17 : (cm_rep_expr_temps_safe x )) (PreH18 : (cm_rep_expr_temps_safe y )) (PreH19 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  “ (retval = (cm_tright ((cm_expr_tpair (e))))) ”
.

Definition cm_expr_temps_return_wit_8_split_goal_spatial := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (retval: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (retval = (cm_imax ((cm_tright ((cm_expr_tpair (x))))) ((1 + (cm_tright ((cm_expr_tpair (y)))) ))))) (PreH10 : (cm_rep_expr_temps_safe y )) (PreH11 : (cm_rep_expr_temps_safe x )) (PreH12 : (expr_pre <> 0)) (PreH13 : (cm_rep_expr_temps_safe e )) (PreH14 : (e = (CMIndexE (x) (y) (t)))) (PreH15 : (out_lvalue = 0)) (PreH16 : (out_rvalue = 0)) (PreH17 : (cm_rep_expr_temps_safe x )) (PreH18 : (cm_rep_expr_temps_safe y )) (PreH19 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  (cm_expr_rep expr_pre e )
.

Definition cm_expr_temps_return_wit_9 := 
(
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (mid: Z) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (cm_rep_expr_temps_safe x )) (PreH2 : (expr_pre <> 0)) (PreH3 : (cm_rep_expr_temps_safe e )) (PreH4 : (e = (CMMemberE (x) (mid) (t)))) (PreH5 : (out_lvalue = 0)) (PreH6 : (out_rvalue = 0)) (PreH7 : (cm_rep_expr_temps_safe x )) (PreH8 : (pa <> 0)) (PreH9 : (pb = 0)) (PreH10 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |-> (cm_tright ((cm_expr_tpair (x)))))
  **  ((rvalue_pre) # Int  |-> (cm_tright ((cm_expr_tpair (x)))))
|--
  “ (cm_rep_expr_temps_safe e ) ”
  &&  (cm_expr_rep expr_pre e )
  **  ((lvalue_pre) # Int  |-> (cm_tleft ((cm_expr_tpair (e)))))
  **  ((rvalue_pre) # Int  |-> (cm_tright ((cm_expr_tpair (e)))))
) \/
(
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (mid: Z) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (cm_rep_expr_temps_safe x )) (PreH10 : (expr_pre <> 0)) (PreH11 : (cm_rep_expr_temps_safe e )) (PreH12 : (e = (CMMemberE (x) (mid) (t)))) (PreH13 : (out_lvalue = 0)) (PreH14 : (out_rvalue = 0)) (PreH15 : (cm_rep_expr_temps_safe x )) (PreH16 : (pa <> 0)) (PreH17 : (pb = 0)) (PreH18 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  “ ((cm_tright ((cm_expr_tpair (x)))) = (cm_tleft ((cm_expr_tpair (e))))) ” 
  &&  “ ((cm_tright ((cm_expr_tpair (x)))) = (cm_tright ((cm_expr_tpair (e))))) ”
  &&  (cm_expr_rep expr_pre e )
).

Definition cm_expr_temps_return_wit_9_split_goal_1 := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (mid: Z) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (cm_rep_expr_temps_safe x )) (PreH10 : (expr_pre <> 0)) (PreH11 : (cm_rep_expr_temps_safe e )) (PreH12 : (e = (CMMemberE (x) (mid) (t)))) (PreH13 : (out_lvalue = 0)) (PreH14 : (out_rvalue = 0)) (PreH15 : (cm_rep_expr_temps_safe x )) (PreH16 : (pa <> 0)) (PreH17 : (pb = 0)) (PreH18 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  “ ((cm_tright ((cm_expr_tpair (x)))) = (cm_tleft ((cm_expr_tpair (e))))) ”
.

Definition cm_expr_temps_return_wit_9_split_goal_2 := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (mid: Z) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (cm_rep_expr_temps_safe x )) (PreH10 : (expr_pre <> 0)) (PreH11 : (cm_rep_expr_temps_safe e )) (PreH12 : (e = (CMMemberE (x) (mid) (t)))) (PreH13 : (out_lvalue = 0)) (PreH14 : (out_rvalue = 0)) (PreH15 : (cm_rep_expr_temps_safe x )) (PreH16 : (pa <> 0)) (PreH17 : (pb = 0)) (PreH18 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  “ ((cm_tright ((cm_expr_tpair (x)))) = (cm_tright ((cm_expr_tpair (e))))) ”
.

Definition cm_expr_temps_return_wit_9_split_goal_spatial := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (mid: Z) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (cm_rep_expr_temps_safe x )) (PreH10 : (expr_pre <> 0)) (PreH11 : (cm_rep_expr_temps_safe e )) (PreH12 : (e = (CMMemberE (x) (mid) (t)))) (PreH13 : (out_lvalue = 0)) (PreH14 : (out_rvalue = 0)) (PreH15 : (cm_rep_expr_temps_safe x )) (PreH16 : (pa <> 0)) (PreH17 : (pb = 0)) (PreH18 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  (cm_expr_rep expr_pre e )
.

Definition cm_expr_temps_return_wit_10 := 
(
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (fid: Z) (eargs: (@list cm_expr)) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (cm_rep_args_temps_safe eargs )) (PreH2 : (expr_pre <> 0)) (PreH3 : (cm_rep_expr_temps_safe e )) (PreH4 : (e = (CMCallE (fid) (eargs) (t)))) (PreH5 : (out_lvalue = 0)) (PreH6 : (out_rvalue = 0)) (PreH7 : (cm_rep_args_temps_safe eargs )) (PreH8 : (pa = 0)) (PreH9 : (pb = 0)) ,
  (cm_arg_list_rep pargs eargs )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |-> out_lvalue)
  **  ((rvalue_pre) # Int  |-> ((cm_acount ((cm_args_apair (eargs)))) + (cm_adepth ((cm_args_apair (eargs)))) ))
|--
  “ (cm_rep_expr_temps_safe e ) ”
  &&  (cm_expr_rep expr_pre e )
  **  ((lvalue_pre) # Int  |-> (cm_tleft ((cm_expr_tpair (e)))))
  **  ((rvalue_pre) # Int  |-> (cm_tright ((cm_expr_tpair (e)))))
) \/
(
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (fid: Z) (eargs: (@list cm_expr)) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (cm_rep_args_temps_safe eargs )) (PreH10 : (expr_pre <> 0)) (PreH11 : (cm_rep_expr_temps_safe e )) (PreH12 : (e = (CMCallE (fid) (eargs) (t)))) (PreH13 : (out_lvalue = 0)) (PreH14 : (out_rvalue = 0)) (PreH15 : (cm_rep_args_temps_safe eargs )) (PreH16 : (pa = 0)) (PreH17 : (pb = 0)) ,
  (cm_arg_list_rep pargs eargs )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ” 
  &&  “ (((cm_acount ((cm_args_apair (eargs)))) + (cm_adepth ((cm_args_apair (eargs)))) ) = (cm_tright ((cm_expr_tpair (e))))) ”
  &&  (cm_expr_rep expr_pre e )
).

Definition cm_expr_temps_return_wit_10_split_goal_1 := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (fid: Z) (eargs: (@list cm_expr)) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (cm_rep_args_temps_safe eargs )) (PreH10 : (expr_pre <> 0)) (PreH11 : (cm_rep_expr_temps_safe e )) (PreH12 : (e = (CMCallE (fid) (eargs) (t)))) (PreH13 : (out_lvalue = 0)) (PreH14 : (out_rvalue = 0)) (PreH15 : (cm_rep_args_temps_safe eargs )) (PreH16 : (pa = 0)) (PreH17 : (pb = 0)) ,
  (cm_arg_list_rep pargs eargs )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ”
.

Definition cm_expr_temps_return_wit_10_split_goal_2 := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (fid: Z) (eargs: (@list cm_expr)) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (cm_rep_args_temps_safe eargs )) (PreH10 : (expr_pre <> 0)) (PreH11 : (cm_rep_expr_temps_safe e )) (PreH12 : (e = (CMCallE (fid) (eargs) (t)))) (PreH13 : (out_lvalue = 0)) (PreH14 : (out_rvalue = 0)) (PreH15 : (cm_rep_args_temps_safe eargs )) (PreH16 : (pa = 0)) (PreH17 : (pb = 0)) ,
  (cm_arg_list_rep pargs eargs )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  “ (((cm_acount ((cm_args_apair (eargs)))) + (cm_adepth ((cm_args_apair (eargs)))) ) = (cm_tright ((cm_expr_tpair (e))))) ”
.

Definition cm_expr_temps_return_wit_10_split_goal_spatial := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (fid: Z) (eargs: (@list cm_expr)) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (cm_rep_args_temps_safe eargs )) (PreH10 : (expr_pre <> 0)) (PreH11 : (cm_rep_expr_temps_safe e )) (PreH12 : (e = (CMCallE (fid) (eargs) (t)))) (PreH13 : (out_lvalue = 0)) (PreH14 : (out_rvalue = 0)) (PreH15 : (cm_rep_args_temps_safe eargs )) (PreH16 : (pa = 0)) (PreH17 : (pb = 0)) ,
  (cm_arg_list_rep pargs eargs )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  (cm_expr_rep expr_pre e )
.

Definition cm_expr_temps_return_wit_11 := 
(
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (cm_rep_expr_temps_safe x )) (PreH2 : (expr_pre <> 0)) (PreH3 : (cm_rep_expr_temps_safe e )) (PreH4 : (e = (CMPutcE (x) (t)))) (PreH5 : (out_lvalue = 0)) (PreH6 : (out_rvalue = 0)) (PreH7 : (cm_rep_expr_temps_safe x )) (PreH8 : (pa <> 0)) (PreH9 : (pb = 0)) (PreH10 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |-> out_lvalue)
  **  ((rvalue_pre) # Int  |-> (cm_tright ((cm_expr_tpair (x)))))
|--
  “ (cm_rep_expr_temps_safe e ) ”
  &&  (cm_expr_rep expr_pre e )
  **  ((lvalue_pre) # Int  |-> (cm_tleft ((cm_expr_tpair (e)))))
  **  ((rvalue_pre) # Int  |-> (cm_tright ((cm_expr_tpair (e)))))
) \/
(
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (cm_rep_expr_temps_safe x )) (PreH10 : (expr_pre <> 0)) (PreH11 : (cm_rep_expr_temps_safe e )) (PreH12 : (e = (CMPutcE (x) (t)))) (PreH13 : (out_lvalue = 0)) (PreH14 : (out_rvalue = 0)) (PreH15 : (cm_rep_expr_temps_safe x )) (PreH16 : (pa <> 0)) (PreH17 : (pb = 0)) (PreH18 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ” 
  &&  “ ((cm_tright ((cm_expr_tpair (x)))) = (cm_tright ((cm_expr_tpair (e))))) ”
  &&  (cm_expr_rep expr_pre e )
).

Definition cm_expr_temps_return_wit_11_split_goal_1 := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (cm_rep_expr_temps_safe x )) (PreH10 : (expr_pre <> 0)) (PreH11 : (cm_rep_expr_temps_safe e )) (PreH12 : (e = (CMPutcE (x) (t)))) (PreH13 : (out_lvalue = 0)) (PreH14 : (out_rvalue = 0)) (PreH15 : (cm_rep_expr_temps_safe x )) (PreH16 : (pa <> 0)) (PreH17 : (pb = 0)) (PreH18 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ”
.

Definition cm_expr_temps_return_wit_11_split_goal_2 := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (cm_rep_expr_temps_safe x )) (PreH10 : (expr_pre <> 0)) (PreH11 : (cm_rep_expr_temps_safe e )) (PreH12 : (e = (CMPutcE (x) (t)))) (PreH13 : (out_lvalue = 0)) (PreH14 : (out_rvalue = 0)) (PreH15 : (cm_rep_expr_temps_safe x )) (PreH16 : (pa <> 0)) (PreH17 : (pb = 0)) (PreH18 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  “ ((cm_tright ((cm_expr_tpair (x)))) = (cm_tright ((cm_expr_tpair (e))))) ”
.

Definition cm_expr_temps_return_wit_11_split_goal_spatial := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (cm_rep_expr_temps_safe x )) (PreH10 : (expr_pre <> 0)) (PreH11 : (cm_rep_expr_temps_safe e )) (PreH12 : (e = (CMPutcE (x) (t)))) (PreH13 : (out_lvalue = 0)) (PreH14 : (out_rvalue = 0)) (PreH15 : (cm_rep_expr_temps_safe x )) (PreH16 : (pa <> 0)) (PreH17 : (pb = 0)) (PreH18 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  (cm_expr_rep expr_pre e )
.

Definition cm_expr_temps_return_wit_12 := 
(
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (cm_rep_expr_temps_safe x )) (PreH2 : (expr_pre <> 0)) (PreH3 : (cm_rep_expr_temps_safe e )) (PreH4 : (e = (CMPutiE (x) (t)))) (PreH5 : (out_lvalue = 0)) (PreH6 : (out_rvalue = 0)) (PreH7 : (cm_rep_expr_temps_safe x )) (PreH8 : (pa <> 0)) (PreH9 : (pb = 0)) (PreH10 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |-> out_lvalue)
  **  ((rvalue_pre) # Int  |-> (cm_tright ((cm_expr_tpair (x)))))
|--
  “ (cm_rep_expr_temps_safe e ) ”
  &&  (cm_expr_rep expr_pre e )
  **  ((lvalue_pre) # Int  |-> (cm_tleft ((cm_expr_tpair (e)))))
  **  ((rvalue_pre) # Int  |-> (cm_tright ((cm_expr_tpair (e)))))
) \/
(
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (cm_rep_expr_temps_safe x )) (PreH10 : (expr_pre <> 0)) (PreH11 : (cm_rep_expr_temps_safe e )) (PreH12 : (e = (CMPutiE (x) (t)))) (PreH13 : (out_lvalue = 0)) (PreH14 : (out_rvalue = 0)) (PreH15 : (cm_rep_expr_temps_safe x )) (PreH16 : (pa <> 0)) (PreH17 : (pb = 0)) (PreH18 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ” 
  &&  “ ((cm_tright ((cm_expr_tpair (x)))) = (cm_tright ((cm_expr_tpair (e))))) ”
  &&  (cm_expr_rep expr_pre e )
).

Definition cm_expr_temps_return_wit_12_split_goal_1 := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (cm_rep_expr_temps_safe x )) (PreH10 : (expr_pre <> 0)) (PreH11 : (cm_rep_expr_temps_safe e )) (PreH12 : (e = (CMPutiE (x) (t)))) (PreH13 : (out_lvalue = 0)) (PreH14 : (out_rvalue = 0)) (PreH15 : (cm_rep_expr_temps_safe x )) (PreH16 : (pa <> 0)) (PreH17 : (pb = 0)) (PreH18 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ”
.

Definition cm_expr_temps_return_wit_12_split_goal_2 := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (cm_rep_expr_temps_safe x )) (PreH10 : (expr_pre <> 0)) (PreH11 : (cm_rep_expr_temps_safe e )) (PreH12 : (e = (CMPutiE (x) (t)))) (PreH13 : (out_lvalue = 0)) (PreH14 : (out_rvalue = 0)) (PreH15 : (cm_rep_expr_temps_safe x )) (PreH16 : (pa <> 0)) (PreH17 : (pb = 0)) (PreH18 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  “ ((cm_tright ((cm_expr_tpair (x)))) = (cm_tright ((cm_expr_tpair (e))))) ”
.

Definition cm_expr_temps_return_wit_12_split_goal_spatial := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (cm_rep_expr_temps_safe x )) (PreH10 : (expr_pre <> 0)) (PreH11 : (cm_rep_expr_temps_safe e )) (PreH12 : (e = (CMPutiE (x) (t)))) (PreH13 : (out_lvalue = 0)) (PreH14 : (out_rvalue = 0)) (PreH15 : (cm_rep_expr_temps_safe x )) (PreH16 : (pa <> 0)) (PreH17 : (pb = 0)) (PreH18 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  (cm_expr_rep expr_pre e )
.

Definition cm_expr_temps_return_wit_13 := 
(
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (cm_rep_expr_temps_safe x )) (PreH2 : (expr_pre <> 0)) (PreH3 : (cm_rep_expr_temps_safe e )) (PreH4 : (e = (CMExitE (x) (t)))) (PreH5 : (out_lvalue = 0)) (PreH6 : (out_rvalue = 0)) (PreH7 : (cm_rep_expr_temps_safe x )) (PreH8 : (pa <> 0)) (PreH9 : (pb = 0)) (PreH10 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |-> out_lvalue)
  **  ((rvalue_pre) # Int  |-> (cm_tright ((cm_expr_tpair (x)))))
|--
  “ (cm_rep_expr_temps_safe e ) ”
  &&  (cm_expr_rep expr_pre e )
  **  ((lvalue_pre) # Int  |-> (cm_tleft ((cm_expr_tpair (e)))))
  **  ((rvalue_pre) # Int  |-> (cm_tright ((cm_expr_tpair (e)))))
) \/
(
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (cm_rep_expr_temps_safe x )) (PreH10 : (expr_pre <> 0)) (PreH11 : (cm_rep_expr_temps_safe e )) (PreH12 : (e = (CMExitE (x) (t)))) (PreH13 : (out_lvalue = 0)) (PreH14 : (out_rvalue = 0)) (PreH15 : (cm_rep_expr_temps_safe x )) (PreH16 : (pa <> 0)) (PreH17 : (pb = 0)) (PreH18 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ” 
  &&  “ ((cm_tright ((cm_expr_tpair (x)))) = (cm_tright ((cm_expr_tpair (e))))) ”
  &&  (cm_expr_rep expr_pre e )
).

Definition cm_expr_temps_return_wit_13_split_goal_1 := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (cm_rep_expr_temps_safe x )) (PreH10 : (expr_pre <> 0)) (PreH11 : (cm_rep_expr_temps_safe e )) (PreH12 : (e = (CMExitE (x) (t)))) (PreH13 : (out_lvalue = 0)) (PreH14 : (out_rvalue = 0)) (PreH15 : (cm_rep_expr_temps_safe x )) (PreH16 : (pa <> 0)) (PreH17 : (pb = 0)) (PreH18 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ”
.

Definition cm_expr_temps_return_wit_13_split_goal_2 := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (cm_rep_expr_temps_safe x )) (PreH10 : (expr_pre <> 0)) (PreH11 : (cm_rep_expr_temps_safe e )) (PreH12 : (e = (CMExitE (x) (t)))) (PreH13 : (out_lvalue = 0)) (PreH14 : (out_rvalue = 0)) (PreH15 : (cm_rep_expr_temps_safe x )) (PreH16 : (pa <> 0)) (PreH17 : (pb = 0)) (PreH18 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  “ ((cm_tright ((cm_expr_tpair (x)))) = (cm_tright ((cm_expr_tpair (e))))) ”
.

Definition cm_expr_temps_return_wit_13_split_goal_spatial := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : (cm_rep_expr_temps_safe x )) (PreH10 : (expr_pre <> 0)) (PreH11 : (cm_rep_expr_temps_safe e )) (PreH12 : (e = (CMExitE (x) (t)))) (PreH13 : (out_lvalue = 0)) (PreH14 : (out_rvalue = 0)) (PreH15 : (cm_rep_expr_temps_safe x )) (PreH16 : (pa <> 0)) (PreH17 : (pb = 0)) (PreH18 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
|--
  (cm_expr_rep expr_pre e )
.

Definition cm_expr_temps_return_wit_14 := 
(
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 0)) (PreH2 : ((cm_rep_expr_kind (e)) <> 13)) (PreH3 : ((cm_rep_expr_kind (e)) <> 12)) (PreH4 : ((cm_rep_expr_kind (e)) <> 11)) (PreH5 : ((cm_rep_expr_kind (e)) <> 8)) (PreH6 : ((cm_rep_expr_kind (e)) <> 7)) (PreH7 : ((cm_rep_expr_kind (e)) <> 6)) (PreH8 : ((cm_rep_expr_kind (e)) <> 5)) (PreH9 : ((cm_rep_expr_kind (e)) <> 4)) (PreH10 : ((cm_rep_expr_kind (e)) <> 3)) (PreH11 : (expr_pre <> 0)) (PreH12 : (cm_rep_expr_temps_safe e )) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
  **  ((lvalue_pre) # Int  |-> 0)
  **  ((rvalue_pre) # Int  |-> 0)
|--
  “ (cm_rep_expr_temps_safe e ) ”
  &&  (cm_expr_rep expr_pre e )
  **  ((lvalue_pre) # Int  |-> (cm_tleft ((cm_expr_tpair (e)))))
  **  ((rvalue_pre) # Int  |-> (cm_tright ((cm_expr_tpair (e)))))
) \/
(
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_kind (e)) = 0)) (PreH10 : ((cm_rep_expr_kind (e)) <> 13)) (PreH11 : ((cm_rep_expr_kind (e)) <> 12)) (PreH12 : ((cm_rep_expr_kind (e)) <> 11)) (PreH13 : ((cm_rep_expr_kind (e)) <> 8)) (PreH14 : ((cm_rep_expr_kind (e)) <> 7)) (PreH15 : ((cm_rep_expr_kind (e)) <> 6)) (PreH16 : ((cm_rep_expr_kind (e)) <> 5)) (PreH17 : ((cm_rep_expr_kind (e)) <> 4)) (PreH18 : ((cm_rep_expr_kind (e)) <> 3)) (PreH19 : (expr_pre <> 0)) (PreH20 : (cm_rep_expr_temps_safe e )) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
|--
  “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ” 
  &&  “ (0 = (cm_tright ((cm_expr_tpair (e))))) ”
  &&  (cm_expr_rep expr_pre e )
).

Definition cm_expr_temps_return_wit_14_split_goal_1 := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_kind (e)) = 0)) (PreH10 : ((cm_rep_expr_kind (e)) <> 13)) (PreH11 : ((cm_rep_expr_kind (e)) <> 12)) (PreH12 : ((cm_rep_expr_kind (e)) <> 11)) (PreH13 : ((cm_rep_expr_kind (e)) <> 8)) (PreH14 : ((cm_rep_expr_kind (e)) <> 7)) (PreH15 : ((cm_rep_expr_kind (e)) <> 6)) (PreH16 : ((cm_rep_expr_kind (e)) <> 5)) (PreH17 : ((cm_rep_expr_kind (e)) <> 4)) (PreH18 : ((cm_rep_expr_kind (e)) <> 3)) (PreH19 : (expr_pre <> 0)) (PreH20 : (cm_rep_expr_temps_safe e )) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
|--
  “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ”
.

Definition cm_expr_temps_return_wit_14_split_goal_2 := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_kind (e)) = 0)) (PreH10 : ((cm_rep_expr_kind (e)) <> 13)) (PreH11 : ((cm_rep_expr_kind (e)) <> 12)) (PreH12 : ((cm_rep_expr_kind (e)) <> 11)) (PreH13 : ((cm_rep_expr_kind (e)) <> 8)) (PreH14 : ((cm_rep_expr_kind (e)) <> 7)) (PreH15 : ((cm_rep_expr_kind (e)) <> 6)) (PreH16 : ((cm_rep_expr_kind (e)) <> 5)) (PreH17 : ((cm_rep_expr_kind (e)) <> 4)) (PreH18 : ((cm_rep_expr_kind (e)) <> 3)) (PreH19 : (expr_pre <> 0)) (PreH20 : (cm_rep_expr_temps_safe e )) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
|--
  “ (0 = (cm_tright ((cm_expr_tpair (e))))) ”
.

Definition cm_expr_temps_return_wit_14_split_goal_spatial := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_kind (e)) = 0)) (PreH10 : ((cm_rep_expr_kind (e)) <> 13)) (PreH11 : ((cm_rep_expr_kind (e)) <> 12)) (PreH12 : ((cm_rep_expr_kind (e)) <> 11)) (PreH13 : ((cm_rep_expr_kind (e)) <> 8)) (PreH14 : ((cm_rep_expr_kind (e)) <> 7)) (PreH15 : ((cm_rep_expr_kind (e)) <> 6)) (PreH16 : ((cm_rep_expr_kind (e)) <> 5)) (PreH17 : ((cm_rep_expr_kind (e)) <> 4)) (PreH18 : ((cm_rep_expr_kind (e)) <> 3)) (PreH19 : (expr_pre <> 0)) (PreH20 : (cm_rep_expr_temps_safe e )) ,
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

Definition cm_expr_temps_return_wit_15 := 
(
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 1)) (PreH2 : ((cm_rep_expr_kind (e)) <> 0)) (PreH3 : ((cm_rep_expr_kind (e)) <> 13)) (PreH4 : ((cm_rep_expr_kind (e)) <> 12)) (PreH5 : ((cm_rep_expr_kind (e)) <> 11)) (PreH6 : ((cm_rep_expr_kind (e)) <> 8)) (PreH7 : ((cm_rep_expr_kind (e)) <> 7)) (PreH8 : ((cm_rep_expr_kind (e)) <> 6)) (PreH9 : ((cm_rep_expr_kind (e)) <> 5)) (PreH10 : ((cm_rep_expr_kind (e)) <> 4)) (PreH11 : ((cm_rep_expr_kind (e)) <> 3)) (PreH12 : (expr_pre <> 0)) (PreH13 : (cm_rep_expr_temps_safe e )) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
  **  ((lvalue_pre) # Int  |-> 0)
  **  ((rvalue_pre) # Int  |-> 0)
|--
  “ (cm_rep_expr_temps_safe e ) ”
  &&  (cm_expr_rep expr_pre e )
  **  ((lvalue_pre) # Int  |-> (cm_tleft ((cm_expr_tpair (e)))))
  **  ((rvalue_pre) # Int  |-> (cm_tright ((cm_expr_tpair (e)))))
) \/
(
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_kind (e)) = 1)) (PreH10 : ((cm_rep_expr_kind (e)) <> 0)) (PreH11 : ((cm_rep_expr_kind (e)) <> 13)) (PreH12 : ((cm_rep_expr_kind (e)) <> 12)) (PreH13 : ((cm_rep_expr_kind (e)) <> 11)) (PreH14 : ((cm_rep_expr_kind (e)) <> 8)) (PreH15 : ((cm_rep_expr_kind (e)) <> 7)) (PreH16 : ((cm_rep_expr_kind (e)) <> 6)) (PreH17 : ((cm_rep_expr_kind (e)) <> 5)) (PreH18 : ((cm_rep_expr_kind (e)) <> 4)) (PreH19 : ((cm_rep_expr_kind (e)) <> 3)) (PreH20 : (expr_pre <> 0)) (PreH21 : (cm_rep_expr_temps_safe e )) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
|--
  “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ” 
  &&  “ (0 = (cm_tright ((cm_expr_tpair (e))))) ”
  &&  (cm_expr_rep expr_pre e )
).

Definition cm_expr_temps_return_wit_15_split_goal_1 := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_kind (e)) = 1)) (PreH10 : ((cm_rep_expr_kind (e)) <> 0)) (PreH11 : ((cm_rep_expr_kind (e)) <> 13)) (PreH12 : ((cm_rep_expr_kind (e)) <> 12)) (PreH13 : ((cm_rep_expr_kind (e)) <> 11)) (PreH14 : ((cm_rep_expr_kind (e)) <> 8)) (PreH15 : ((cm_rep_expr_kind (e)) <> 7)) (PreH16 : ((cm_rep_expr_kind (e)) <> 6)) (PreH17 : ((cm_rep_expr_kind (e)) <> 5)) (PreH18 : ((cm_rep_expr_kind (e)) <> 4)) (PreH19 : ((cm_rep_expr_kind (e)) <> 3)) (PreH20 : (expr_pre <> 0)) (PreH21 : (cm_rep_expr_temps_safe e )) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
|--
  “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ”
.

Definition cm_expr_temps_return_wit_15_split_goal_2 := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_kind (e)) = 1)) (PreH10 : ((cm_rep_expr_kind (e)) <> 0)) (PreH11 : ((cm_rep_expr_kind (e)) <> 13)) (PreH12 : ((cm_rep_expr_kind (e)) <> 12)) (PreH13 : ((cm_rep_expr_kind (e)) <> 11)) (PreH14 : ((cm_rep_expr_kind (e)) <> 8)) (PreH15 : ((cm_rep_expr_kind (e)) <> 7)) (PreH16 : ((cm_rep_expr_kind (e)) <> 6)) (PreH17 : ((cm_rep_expr_kind (e)) <> 5)) (PreH18 : ((cm_rep_expr_kind (e)) <> 4)) (PreH19 : ((cm_rep_expr_kind (e)) <> 3)) (PreH20 : (expr_pre <> 0)) (PreH21 : (cm_rep_expr_temps_safe e )) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
|--
  “ (0 = (cm_tright ((cm_expr_tpair (e))))) ”
.

Definition cm_expr_temps_return_wit_15_split_goal_spatial := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_kind (e)) = 1)) (PreH10 : ((cm_rep_expr_kind (e)) <> 0)) (PreH11 : ((cm_rep_expr_kind (e)) <> 13)) (PreH12 : ((cm_rep_expr_kind (e)) <> 12)) (PreH13 : ((cm_rep_expr_kind (e)) <> 11)) (PreH14 : ((cm_rep_expr_kind (e)) <> 8)) (PreH15 : ((cm_rep_expr_kind (e)) <> 7)) (PreH16 : ((cm_rep_expr_kind (e)) <> 6)) (PreH17 : ((cm_rep_expr_kind (e)) <> 5)) (PreH18 : ((cm_rep_expr_kind (e)) <> 4)) (PreH19 : ((cm_rep_expr_kind (e)) <> 3)) (PreH20 : (expr_pre <> 0)) (PreH21 : (cm_rep_expr_temps_safe e )) ,
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

Definition cm_expr_temps_return_wit_16 := 
(
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 2)) (PreH2 : ((cm_rep_expr_kind (e)) <> 1)) (PreH3 : ((cm_rep_expr_kind (e)) <> 0)) (PreH4 : ((cm_rep_expr_kind (e)) <> 13)) (PreH5 : ((cm_rep_expr_kind (e)) <> 12)) (PreH6 : ((cm_rep_expr_kind (e)) <> 11)) (PreH7 : ((cm_rep_expr_kind (e)) <> 8)) (PreH8 : ((cm_rep_expr_kind (e)) <> 7)) (PreH9 : ((cm_rep_expr_kind (e)) <> 6)) (PreH10 : ((cm_rep_expr_kind (e)) <> 5)) (PreH11 : ((cm_rep_expr_kind (e)) <> 4)) (PreH12 : ((cm_rep_expr_kind (e)) <> 3)) (PreH13 : (expr_pre <> 0)) (PreH14 : (cm_rep_expr_temps_safe e )) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
  **  ((lvalue_pre) # Int  |-> 0)
  **  ((rvalue_pre) # Int  |-> 0)
|--
  “ (cm_rep_expr_temps_safe e ) ”
  &&  (cm_expr_rep expr_pre e )
  **  ((lvalue_pre) # Int  |-> (cm_tleft ((cm_expr_tpair (e)))))
  **  ((rvalue_pre) # Int  |-> (cm_tright ((cm_expr_tpair (e)))))
) \/
(
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_kind (e)) = 2)) (PreH10 : ((cm_rep_expr_kind (e)) <> 1)) (PreH11 : ((cm_rep_expr_kind (e)) <> 0)) (PreH12 : ((cm_rep_expr_kind (e)) <> 13)) (PreH13 : ((cm_rep_expr_kind (e)) <> 12)) (PreH14 : ((cm_rep_expr_kind (e)) <> 11)) (PreH15 : ((cm_rep_expr_kind (e)) <> 8)) (PreH16 : ((cm_rep_expr_kind (e)) <> 7)) (PreH17 : ((cm_rep_expr_kind (e)) <> 6)) (PreH18 : ((cm_rep_expr_kind (e)) <> 5)) (PreH19 : ((cm_rep_expr_kind (e)) <> 4)) (PreH20 : ((cm_rep_expr_kind (e)) <> 3)) (PreH21 : (expr_pre <> 0)) (PreH22 : (cm_rep_expr_temps_safe e )) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
|--
  “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ” 
  &&  “ (0 = (cm_tright ((cm_expr_tpair (e))))) ”
  &&  (cm_expr_rep expr_pre e )
).

Definition cm_expr_temps_return_wit_16_split_goal_1 := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_kind (e)) = 2)) (PreH10 : ((cm_rep_expr_kind (e)) <> 1)) (PreH11 : ((cm_rep_expr_kind (e)) <> 0)) (PreH12 : ((cm_rep_expr_kind (e)) <> 13)) (PreH13 : ((cm_rep_expr_kind (e)) <> 12)) (PreH14 : ((cm_rep_expr_kind (e)) <> 11)) (PreH15 : ((cm_rep_expr_kind (e)) <> 8)) (PreH16 : ((cm_rep_expr_kind (e)) <> 7)) (PreH17 : ((cm_rep_expr_kind (e)) <> 6)) (PreH18 : ((cm_rep_expr_kind (e)) <> 5)) (PreH19 : ((cm_rep_expr_kind (e)) <> 4)) (PreH20 : ((cm_rep_expr_kind (e)) <> 3)) (PreH21 : (expr_pre <> 0)) (PreH22 : (cm_rep_expr_temps_safe e )) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
|--
  “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ”
.

Definition cm_expr_temps_return_wit_16_split_goal_2 := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_kind (e)) = 2)) (PreH10 : ((cm_rep_expr_kind (e)) <> 1)) (PreH11 : ((cm_rep_expr_kind (e)) <> 0)) (PreH12 : ((cm_rep_expr_kind (e)) <> 13)) (PreH13 : ((cm_rep_expr_kind (e)) <> 12)) (PreH14 : ((cm_rep_expr_kind (e)) <> 11)) (PreH15 : ((cm_rep_expr_kind (e)) <> 8)) (PreH16 : ((cm_rep_expr_kind (e)) <> 7)) (PreH17 : ((cm_rep_expr_kind (e)) <> 6)) (PreH18 : ((cm_rep_expr_kind (e)) <> 5)) (PreH19 : ((cm_rep_expr_kind (e)) <> 4)) (PreH20 : ((cm_rep_expr_kind (e)) <> 3)) (PreH21 : (expr_pre <> 0)) (PreH22 : (cm_rep_expr_temps_safe e )) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
|--
  “ (0 = (cm_tright ((cm_expr_tpair (e))))) ”
.

Definition cm_expr_temps_return_wit_16_split_goal_spatial := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_kind (e)) = 2)) (PreH10 : ((cm_rep_expr_kind (e)) <> 1)) (PreH11 : ((cm_rep_expr_kind (e)) <> 0)) (PreH12 : ((cm_rep_expr_kind (e)) <> 13)) (PreH13 : ((cm_rep_expr_kind (e)) <> 12)) (PreH14 : ((cm_rep_expr_kind (e)) <> 11)) (PreH15 : ((cm_rep_expr_kind (e)) <> 8)) (PreH16 : ((cm_rep_expr_kind (e)) <> 7)) (PreH17 : ((cm_rep_expr_kind (e)) <> 6)) (PreH18 : ((cm_rep_expr_kind (e)) <> 5)) (PreH19 : ((cm_rep_expr_kind (e)) <> 4)) (PreH20 : ((cm_rep_expr_kind (e)) <> 3)) (PreH21 : (expr_pre <> 0)) (PreH22 : (cm_rep_expr_temps_safe e )) ,
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

Definition cm_expr_temps_return_wit_17 := 
(
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 9)) (PreH2 : ((cm_rep_expr_kind (e)) <> 2)) (PreH3 : ((cm_rep_expr_kind (e)) <> 1)) (PreH4 : ((cm_rep_expr_kind (e)) <> 0)) (PreH5 : ((cm_rep_expr_kind (e)) <> 13)) (PreH6 : ((cm_rep_expr_kind (e)) <> 12)) (PreH7 : ((cm_rep_expr_kind (e)) <> 11)) (PreH8 : ((cm_rep_expr_kind (e)) <> 8)) (PreH9 : ((cm_rep_expr_kind (e)) <> 7)) (PreH10 : ((cm_rep_expr_kind (e)) <> 6)) (PreH11 : ((cm_rep_expr_kind (e)) <> 5)) (PreH12 : ((cm_rep_expr_kind (e)) <> 4)) (PreH13 : ((cm_rep_expr_kind (e)) <> 3)) (PreH14 : (expr_pre <> 0)) (PreH15 : (cm_rep_expr_temps_safe e )) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
  **  ((lvalue_pre) # Int  |-> 0)
  **  ((rvalue_pre) # Int  |-> 0)
|--
  “ (cm_rep_expr_temps_safe e ) ”
  &&  (cm_expr_rep expr_pre e )
  **  ((lvalue_pre) # Int  |-> (cm_tleft ((cm_expr_tpair (e)))))
  **  ((rvalue_pre) # Int  |-> (cm_tright ((cm_expr_tpair (e)))))
) \/
(
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_kind (e)) = 9)) (PreH10 : ((cm_rep_expr_kind (e)) <> 2)) (PreH11 : ((cm_rep_expr_kind (e)) <> 1)) (PreH12 : ((cm_rep_expr_kind (e)) <> 0)) (PreH13 : ((cm_rep_expr_kind (e)) <> 13)) (PreH14 : ((cm_rep_expr_kind (e)) <> 12)) (PreH15 : ((cm_rep_expr_kind (e)) <> 11)) (PreH16 : ((cm_rep_expr_kind (e)) <> 8)) (PreH17 : ((cm_rep_expr_kind (e)) <> 7)) (PreH18 : ((cm_rep_expr_kind (e)) <> 6)) (PreH19 : ((cm_rep_expr_kind (e)) <> 5)) (PreH20 : ((cm_rep_expr_kind (e)) <> 4)) (PreH21 : ((cm_rep_expr_kind (e)) <> 3)) (PreH22 : (expr_pre <> 0)) (PreH23 : (cm_rep_expr_temps_safe e )) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
|--
  “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ” 
  &&  “ (0 = (cm_tright ((cm_expr_tpair (e))))) ”
  &&  (cm_expr_rep expr_pre e )
).

Definition cm_expr_temps_return_wit_17_split_goal_1 := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_kind (e)) = 9)) (PreH10 : ((cm_rep_expr_kind (e)) <> 2)) (PreH11 : ((cm_rep_expr_kind (e)) <> 1)) (PreH12 : ((cm_rep_expr_kind (e)) <> 0)) (PreH13 : ((cm_rep_expr_kind (e)) <> 13)) (PreH14 : ((cm_rep_expr_kind (e)) <> 12)) (PreH15 : ((cm_rep_expr_kind (e)) <> 11)) (PreH16 : ((cm_rep_expr_kind (e)) <> 8)) (PreH17 : ((cm_rep_expr_kind (e)) <> 7)) (PreH18 : ((cm_rep_expr_kind (e)) <> 6)) (PreH19 : ((cm_rep_expr_kind (e)) <> 5)) (PreH20 : ((cm_rep_expr_kind (e)) <> 4)) (PreH21 : ((cm_rep_expr_kind (e)) <> 3)) (PreH22 : (expr_pre <> 0)) (PreH23 : (cm_rep_expr_temps_safe e )) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
|--
  “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ”
.

Definition cm_expr_temps_return_wit_17_split_goal_2 := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_kind (e)) = 9)) (PreH10 : ((cm_rep_expr_kind (e)) <> 2)) (PreH11 : ((cm_rep_expr_kind (e)) <> 1)) (PreH12 : ((cm_rep_expr_kind (e)) <> 0)) (PreH13 : ((cm_rep_expr_kind (e)) <> 13)) (PreH14 : ((cm_rep_expr_kind (e)) <> 12)) (PreH15 : ((cm_rep_expr_kind (e)) <> 11)) (PreH16 : ((cm_rep_expr_kind (e)) <> 8)) (PreH17 : ((cm_rep_expr_kind (e)) <> 7)) (PreH18 : ((cm_rep_expr_kind (e)) <> 6)) (PreH19 : ((cm_rep_expr_kind (e)) <> 5)) (PreH20 : ((cm_rep_expr_kind (e)) <> 4)) (PreH21 : ((cm_rep_expr_kind (e)) <> 3)) (PreH22 : (expr_pre <> 0)) (PreH23 : (cm_rep_expr_temps_safe e )) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
|--
  “ (0 = (cm_tright ((cm_expr_tpair (e))))) ”
.

Definition cm_expr_temps_return_wit_17_split_goal_spatial := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_kind (e)) = 9)) (PreH10 : ((cm_rep_expr_kind (e)) <> 2)) (PreH11 : ((cm_rep_expr_kind (e)) <> 1)) (PreH12 : ((cm_rep_expr_kind (e)) <> 0)) (PreH13 : ((cm_rep_expr_kind (e)) <> 13)) (PreH14 : ((cm_rep_expr_kind (e)) <> 12)) (PreH15 : ((cm_rep_expr_kind (e)) <> 11)) (PreH16 : ((cm_rep_expr_kind (e)) <> 8)) (PreH17 : ((cm_rep_expr_kind (e)) <> 7)) (PreH18 : ((cm_rep_expr_kind (e)) <> 6)) (PreH19 : ((cm_rep_expr_kind (e)) <> 5)) (PreH20 : ((cm_rep_expr_kind (e)) <> 4)) (PreH21 : ((cm_rep_expr_kind (e)) <> 3)) (PreH22 : (expr_pre <> 0)) (PreH23 : (cm_rep_expr_temps_safe e )) ,
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

Definition cm_expr_temps_return_wit_18 := 
(
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_kind (e)) = 10)) (PreH2 : ((cm_rep_expr_kind (e)) <> 9)) (PreH3 : ((cm_rep_expr_kind (e)) <> 2)) (PreH4 : ((cm_rep_expr_kind (e)) <> 1)) (PreH5 : ((cm_rep_expr_kind (e)) <> 0)) (PreH6 : ((cm_rep_expr_kind (e)) <> 13)) (PreH7 : ((cm_rep_expr_kind (e)) <> 12)) (PreH8 : ((cm_rep_expr_kind (e)) <> 11)) (PreH9 : ((cm_rep_expr_kind (e)) <> 8)) (PreH10 : ((cm_rep_expr_kind (e)) <> 7)) (PreH11 : ((cm_rep_expr_kind (e)) <> 6)) (PreH12 : ((cm_rep_expr_kind (e)) <> 5)) (PreH13 : ((cm_rep_expr_kind (e)) <> 4)) (PreH14 : ((cm_rep_expr_kind (e)) <> 3)) (PreH15 : (expr_pre <> 0)) (PreH16 : (cm_rep_expr_temps_safe e )) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
  **  ((lvalue_pre) # Int  |-> 0)
  **  ((rvalue_pre) # Int  |-> 0)
|--
  “ (cm_rep_expr_temps_safe e ) ”
  &&  (cm_expr_rep expr_pre e )
  **  ((lvalue_pre) # Int  |-> (cm_tleft ((cm_expr_tpair (e)))))
  **  ((rvalue_pre) # Int  |-> (cm_tright ((cm_expr_tpair (e)))))
) \/
(
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_kind (e)) = 10)) (PreH10 : ((cm_rep_expr_kind (e)) <> 9)) (PreH11 : ((cm_rep_expr_kind (e)) <> 2)) (PreH12 : ((cm_rep_expr_kind (e)) <> 1)) (PreH13 : ((cm_rep_expr_kind (e)) <> 0)) (PreH14 : ((cm_rep_expr_kind (e)) <> 13)) (PreH15 : ((cm_rep_expr_kind (e)) <> 12)) (PreH16 : ((cm_rep_expr_kind (e)) <> 11)) (PreH17 : ((cm_rep_expr_kind (e)) <> 8)) (PreH18 : ((cm_rep_expr_kind (e)) <> 7)) (PreH19 : ((cm_rep_expr_kind (e)) <> 6)) (PreH20 : ((cm_rep_expr_kind (e)) <> 5)) (PreH21 : ((cm_rep_expr_kind (e)) <> 4)) (PreH22 : ((cm_rep_expr_kind (e)) <> 3)) (PreH23 : (expr_pre <> 0)) (PreH24 : (cm_rep_expr_temps_safe e )) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
|--
  “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ” 
  &&  “ (0 = (cm_tright ((cm_expr_tpair (e))))) ”
  &&  (cm_expr_rep expr_pre e )
).

Definition cm_expr_temps_return_wit_18_split_goal_1 := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_kind (e)) = 10)) (PreH10 : ((cm_rep_expr_kind (e)) <> 9)) (PreH11 : ((cm_rep_expr_kind (e)) <> 2)) (PreH12 : ((cm_rep_expr_kind (e)) <> 1)) (PreH13 : ((cm_rep_expr_kind (e)) <> 0)) (PreH14 : ((cm_rep_expr_kind (e)) <> 13)) (PreH15 : ((cm_rep_expr_kind (e)) <> 12)) (PreH16 : ((cm_rep_expr_kind (e)) <> 11)) (PreH17 : ((cm_rep_expr_kind (e)) <> 8)) (PreH18 : ((cm_rep_expr_kind (e)) <> 7)) (PreH19 : ((cm_rep_expr_kind (e)) <> 6)) (PreH20 : ((cm_rep_expr_kind (e)) <> 5)) (PreH21 : ((cm_rep_expr_kind (e)) <> 4)) (PreH22 : ((cm_rep_expr_kind (e)) <> 3)) (PreH23 : (expr_pre <> 0)) (PreH24 : (cm_rep_expr_temps_safe e )) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
|--
  “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ”
.

Definition cm_expr_temps_return_wit_18_split_goal_2 := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_kind (e)) = 10)) (PreH10 : ((cm_rep_expr_kind (e)) <> 9)) (PreH11 : ((cm_rep_expr_kind (e)) <> 2)) (PreH12 : ((cm_rep_expr_kind (e)) <> 1)) (PreH13 : ((cm_rep_expr_kind (e)) <> 0)) (PreH14 : ((cm_rep_expr_kind (e)) <> 13)) (PreH15 : ((cm_rep_expr_kind (e)) <> 12)) (PreH16 : ((cm_rep_expr_kind (e)) <> 11)) (PreH17 : ((cm_rep_expr_kind (e)) <> 8)) (PreH18 : ((cm_rep_expr_kind (e)) <> 7)) (PreH19 : ((cm_rep_expr_kind (e)) <> 6)) (PreH20 : ((cm_rep_expr_kind (e)) <> 5)) (PreH21 : ((cm_rep_expr_kind (e)) <> 4)) (PreH22 : ((cm_rep_expr_kind (e)) <> 3)) (PreH23 : (expr_pre <> 0)) (PreH24 : (cm_rep_expr_temps_safe e )) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
|--
  “ (0 = (cm_tright ((cm_expr_tpair (e))))) ”
.

Definition cm_expr_temps_return_wit_18_split_goal_spatial := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_kind (e)) = 10)) (PreH10 : ((cm_rep_expr_kind (e)) <> 9)) (PreH11 : ((cm_rep_expr_kind (e)) <> 2)) (PreH12 : ((cm_rep_expr_kind (e)) <> 1)) (PreH13 : ((cm_rep_expr_kind (e)) <> 0)) (PreH14 : ((cm_rep_expr_kind (e)) <> 13)) (PreH15 : ((cm_rep_expr_kind (e)) <> 12)) (PreH16 : ((cm_rep_expr_kind (e)) <> 11)) (PreH17 : ((cm_rep_expr_kind (e)) <> 8)) (PreH18 : ((cm_rep_expr_kind (e)) <> 7)) (PreH19 : ((cm_rep_expr_kind (e)) <> 6)) (PreH20 : ((cm_rep_expr_kind (e)) <> 5)) (PreH21 : ((cm_rep_expr_kind (e)) <> 4)) (PreH22 : ((cm_rep_expr_kind (e)) <> 3)) (PreH23 : (expr_pre <> 0)) (PreH24 : (cm_rep_expr_temps_safe e )) ,
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

Definition cm_expr_temps_return_wit_19 := 
(
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_kind (e)) <> 10)) (PreH2 : ((cm_rep_expr_kind (e)) <> 9)) (PreH3 : ((cm_rep_expr_kind (e)) <> 2)) (PreH4 : ((cm_rep_expr_kind (e)) <> 1)) (PreH5 : ((cm_rep_expr_kind (e)) <> 0)) (PreH6 : ((cm_rep_expr_kind (e)) <> 13)) (PreH7 : ((cm_rep_expr_kind (e)) <> 12)) (PreH8 : ((cm_rep_expr_kind (e)) <> 11)) (PreH9 : ((cm_rep_expr_kind (e)) <> 8)) (PreH10 : ((cm_rep_expr_kind (e)) <> 7)) (PreH11 : ((cm_rep_expr_kind (e)) <> 6)) (PreH12 : ((cm_rep_expr_kind (e)) <> 5)) (PreH13 : ((cm_rep_expr_kind (e)) <> 4)) (PreH14 : ((cm_rep_expr_kind (e)) <> 3)) (PreH15 : (expr_pre <> 0)) (PreH16 : (cm_rep_expr_temps_safe e )) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
  **  ((lvalue_pre) # Int  |-> 0)
  **  ((rvalue_pre) # Int  |-> 0)
|--
  “ (cm_rep_expr_temps_safe e ) ”
  &&  (cm_expr_rep expr_pre e )
  **  ((lvalue_pre) # Int  |-> (cm_tleft ((cm_expr_tpair (e)))))
  **  ((rvalue_pre) # Int  |-> (cm_tright ((cm_expr_tpair (e)))))
) \/
(
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_kind (e)) <> 10)) (PreH10 : ((cm_rep_expr_kind (e)) <> 9)) (PreH11 : ((cm_rep_expr_kind (e)) <> 2)) (PreH12 : ((cm_rep_expr_kind (e)) <> 1)) (PreH13 : ((cm_rep_expr_kind (e)) <> 0)) (PreH14 : ((cm_rep_expr_kind (e)) <> 13)) (PreH15 : ((cm_rep_expr_kind (e)) <> 12)) (PreH16 : ((cm_rep_expr_kind (e)) <> 11)) (PreH17 : ((cm_rep_expr_kind (e)) <> 8)) (PreH18 : ((cm_rep_expr_kind (e)) <> 7)) (PreH19 : ((cm_rep_expr_kind (e)) <> 6)) (PreH20 : ((cm_rep_expr_kind (e)) <> 5)) (PreH21 : ((cm_rep_expr_kind (e)) <> 4)) (PreH22 : ((cm_rep_expr_kind (e)) <> 3)) (PreH23 : (expr_pre <> 0)) (PreH24 : (cm_rep_expr_temps_safe e )) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
|--
  “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ” 
  &&  “ (0 = (cm_tright ((cm_expr_tpair (e))))) ”
  &&  (cm_expr_rep expr_pre e )
).

Definition cm_expr_temps_return_wit_19_split_goal_1 := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_kind (e)) <> 10)) (PreH10 : ((cm_rep_expr_kind (e)) <> 9)) (PreH11 : ((cm_rep_expr_kind (e)) <> 2)) (PreH12 : ((cm_rep_expr_kind (e)) <> 1)) (PreH13 : ((cm_rep_expr_kind (e)) <> 0)) (PreH14 : ((cm_rep_expr_kind (e)) <> 13)) (PreH15 : ((cm_rep_expr_kind (e)) <> 12)) (PreH16 : ((cm_rep_expr_kind (e)) <> 11)) (PreH17 : ((cm_rep_expr_kind (e)) <> 8)) (PreH18 : ((cm_rep_expr_kind (e)) <> 7)) (PreH19 : ((cm_rep_expr_kind (e)) <> 6)) (PreH20 : ((cm_rep_expr_kind (e)) <> 5)) (PreH21 : ((cm_rep_expr_kind (e)) <> 4)) (PreH22 : ((cm_rep_expr_kind (e)) <> 3)) (PreH23 : (expr_pre <> 0)) (PreH24 : (cm_rep_expr_temps_safe e )) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
|--
  “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ”
.

Definition cm_expr_temps_return_wit_19_split_goal_2 := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_kind (e)) <> 10)) (PreH10 : ((cm_rep_expr_kind (e)) <> 9)) (PreH11 : ((cm_rep_expr_kind (e)) <> 2)) (PreH12 : ((cm_rep_expr_kind (e)) <> 1)) (PreH13 : ((cm_rep_expr_kind (e)) <> 0)) (PreH14 : ((cm_rep_expr_kind (e)) <> 13)) (PreH15 : ((cm_rep_expr_kind (e)) <> 12)) (PreH16 : ((cm_rep_expr_kind (e)) <> 11)) (PreH17 : ((cm_rep_expr_kind (e)) <> 8)) (PreH18 : ((cm_rep_expr_kind (e)) <> 7)) (PreH19 : ((cm_rep_expr_kind (e)) <> 6)) (PreH20 : ((cm_rep_expr_kind (e)) <> 5)) (PreH21 : ((cm_rep_expr_kind (e)) <> 4)) (PreH22 : ((cm_rep_expr_kind (e)) <> 3)) (PreH23 : (expr_pre <> 0)) (PreH24 : (cm_rep_expr_temps_safe e )) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_payload e pa pb pargs )
|--
  “ (0 = (cm_tright ((cm_expr_tpair (e))))) ”
.

Definition cm_expr_temps_return_wit_19_split_goal_spatial := 
forall (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (PreH1 : ((cm_rep_expr_value (e)) <= INT64_MAX)) (PreH2 : ((cm_rep_expr_value (e)) >= INT64_MIN)) (PreH3 : ((cm_type_encode ((cm_expr_type (e)))) <= INT_MAX)) (PreH4 : ((cm_rep_expr_op (e)) <= INT_MAX)) (PreH5 : ((cm_rep_expr_kind (e)) <= INT_MAX)) (PreH6 : ((cm_type_encode ((cm_expr_type (e)))) >= INT_MIN)) (PreH7 : ((cm_rep_expr_op (e)) >= INT_MIN)) (PreH8 : ((cm_rep_expr_kind (e)) >= INT_MIN)) (PreH9 : ((cm_rep_expr_kind (e)) <> 10)) (PreH10 : ((cm_rep_expr_kind (e)) <> 9)) (PreH11 : ((cm_rep_expr_kind (e)) <> 2)) (PreH12 : ((cm_rep_expr_kind (e)) <> 1)) (PreH13 : ((cm_rep_expr_kind (e)) <> 0)) (PreH14 : ((cm_rep_expr_kind (e)) <> 13)) (PreH15 : ((cm_rep_expr_kind (e)) <> 12)) (PreH16 : ((cm_rep_expr_kind (e)) <> 11)) (PreH17 : ((cm_rep_expr_kind (e)) <> 8)) (PreH18 : ((cm_rep_expr_kind (e)) <> 7)) (PreH19 : ((cm_rep_expr_kind (e)) <> 6)) (PreH20 : ((cm_rep_expr_kind (e)) <> 5)) (PreH21 : ((cm_rep_expr_kind (e)) <> 4)) (PreH22 : ((cm_rep_expr_kind (e)) <> 3)) (PreH23 : (expr_pre <> 0)) (PreH24 : (cm_rep_expr_temps_safe e )) ,
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

Definition cm_expr_temps_partial_solve_wit_1_pure := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (expr_pre <> 0)) (PreH2 : (cm_rep_expr_temps_safe e )) (PreH3 : (e = (CMAssignE (x) (y) (t)))) (PreH4 : (out_lvalue = 0)) (PreH5 : (out_rvalue = 0)) (PreH6 : (cm_rep_expr_temps_safe x )) (PreH7 : (cm_rep_expr_temps_safe y )) (PreH8 : (pargs = 0)) ,
  ((( &( "right_rvalue" ) )) # Int  |->_)
  **  ((( &( "right_lvalue" ) )) # Int  |->_)
  **  ((( &( "left_rvalue" ) )) # Int  |->_)
  **  ((( &( "left_lvalue" ) )) # Int  |->_)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((( &( "out_lvalue" ) )) # Int  |-> out_lvalue)
  **  ((( &( "out_rvalue" ) )) # Int  |-> out_rvalue)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_rep pa x )
  **  (cm_expr_rep pb y )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (cm_rep_expr_temps_safe x ) ”
.

Definition cm_expr_temps_partial_solve_wit_1_aux := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (expr_pre <> 0)) (PreH2 : (cm_rep_expr_temps_safe e )) (PreH3 : (e = (CMAssignE (x) (y) (t)))) (PreH4 : (out_lvalue = 0)) (PreH5 : (out_rvalue = 0)) (PreH6 : (cm_rep_expr_temps_safe x )) (PreH7 : (cm_rep_expr_temps_safe y )) (PreH8 : (pargs = 0)) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_rep pa x )
  **  (cm_expr_rep pb y )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (cm_rep_expr_temps_safe e ) ” 
  &&  “ (e = (CMAssignE (x) (y) (t))) ” 
  &&  “ (out_lvalue = 0) ” 
  &&  “ (out_rvalue = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (cm_rep_expr_temps_safe y ) ” 
  &&  “ (pargs = 0) ”
  &&  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_rep pb y )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
.

Definition cm_expr_temps_partial_solve_wit_1 := cm_expr_temps_partial_solve_wit_1_pure -> cm_expr_temps_partial_solve_wit_1_aux.

Definition cm_expr_temps_partial_solve_wit_2_pure := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (cm_rep_expr_temps_safe x )) (PreH2 : (expr_pre <> 0)) (PreH3 : (cm_rep_expr_temps_safe e )) (PreH4 : (e = (CMAssignE (x) (y) (t)))) (PreH5 : (out_lvalue = 0)) (PreH6 : (out_rvalue = 0)) (PreH7 : (cm_rep_expr_temps_safe x )) (PreH8 : (cm_rep_expr_temps_safe y )) (PreH9 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((( &( "left_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (x)))))
  **  ((( &( "left_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (x)))))
  **  ((( &( "right_rvalue" ) )) # Int  |->_)
  **  ((( &( "right_lvalue" ) )) # Int  |->_)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((( &( "out_lvalue" ) )) # Int  |-> out_lvalue)
  **  ((( &( "out_rvalue" ) )) # Int  |-> out_rvalue)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_rep pb y )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (cm_rep_expr_temps_safe y ) ”
.

Definition cm_expr_temps_partial_solve_wit_2_aux := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (cm_rep_expr_temps_safe x )) (PreH2 : (expr_pre <> 0)) (PreH3 : (cm_rep_expr_temps_safe e )) (PreH4 : (e = (CMAssignE (x) (y) (t)))) (PreH5 : (out_lvalue = 0)) (PreH6 : (out_rvalue = 0)) (PreH7 : (cm_rep_expr_temps_safe x )) (PreH8 : (cm_rep_expr_temps_safe y )) (PreH9 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_rep pb y )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (cm_rep_expr_temps_safe y ) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (cm_rep_expr_temps_safe e ) ” 
  &&  “ (e = (CMAssignE (x) (y) (t))) ” 
  &&  “ (out_lvalue = 0) ” 
  &&  “ (out_rvalue = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (cm_rep_expr_temps_safe y ) ” 
  &&  “ (pargs = 0) ”
  &&  (cm_expr_rep pb y )
  **  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
.

Definition cm_expr_temps_partial_solve_wit_2 := cm_expr_temps_partial_solve_wit_2_pure -> cm_expr_temps_partial_solve_wit_2_aux.

Definition cm_expr_temps_partial_solve_wit_3 := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (cm_rep_expr_temps_safe y )) (PreH2 : (cm_rep_expr_temps_safe x )) (PreH3 : (expr_pre <> 0)) (PreH4 : (cm_rep_expr_temps_safe e )) (PreH5 : (e = (CMAssignE (x) (y) (t)))) (PreH6 : (out_lvalue = 0)) (PreH7 : (out_rvalue = 0)) (PreH8 : (cm_rep_expr_temps_safe x )) (PreH9 : (cm_rep_expr_temps_safe y )) (PreH10 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (cm_rep_expr_temps_safe y ) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (cm_rep_expr_temps_safe e ) ” 
  &&  “ (e = (CMAssignE (x) (y) (t))) ” 
  &&  “ (out_lvalue = 0) ” 
  &&  “ (out_rvalue = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (cm_rep_expr_temps_safe y ) ” 
  &&  “ (pargs = 0) ”
  &&  (cm_expr_rep pb y )
  **  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
.

Definition cm_expr_temps_partial_solve_wit_4_pure := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (expr_pre <> 0)) (PreH2 : (cm_rep_expr_temps_safe e )) (PreH3 : (e = (CMBinaryE (op) (x) (y) (t)))) (PreH4 : (out_lvalue = 0)) (PreH5 : (out_rvalue = 0)) (PreH6 : (cm_rep_expr_temps_safe x )) (PreH7 : (cm_rep_expr_temps_safe y )) (PreH8 : (pargs = 0)) ,
  ((( &( "right_rvalue" ) )) # Int  |->_)
  **  ((( &( "right_lvalue" ) )) # Int  |->_)
  **  ((( &( "left_rvalue" ) )) # Int  |->_)
  **  ((( &( "left_lvalue" ) )) # Int  |->_)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((( &( "out_lvalue" ) )) # Int  |-> out_lvalue)
  **  ((( &( "out_rvalue" ) )) # Int  |-> out_rvalue)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_rep pa x )
  **  (cm_expr_rep pb y )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (cm_rep_expr_temps_safe x ) ”
.

Definition cm_expr_temps_partial_solve_wit_4_aux := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (expr_pre <> 0)) (PreH2 : (cm_rep_expr_temps_safe e )) (PreH3 : (e = (CMBinaryE (op) (x) (y) (t)))) (PreH4 : (out_lvalue = 0)) (PreH5 : (out_rvalue = 0)) (PreH6 : (cm_rep_expr_temps_safe x )) (PreH7 : (cm_rep_expr_temps_safe y )) (PreH8 : (pargs = 0)) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_rep pa x )
  **  (cm_expr_rep pb y )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (cm_rep_expr_temps_safe e ) ” 
  &&  “ (e = (CMBinaryE (op) (x) (y) (t))) ” 
  &&  “ (out_lvalue = 0) ” 
  &&  “ (out_rvalue = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (cm_rep_expr_temps_safe y ) ” 
  &&  “ (pargs = 0) ”
  &&  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_rep pb y )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
.

Definition cm_expr_temps_partial_solve_wit_4 := cm_expr_temps_partial_solve_wit_4_pure -> cm_expr_temps_partial_solve_wit_4_aux.

Definition cm_expr_temps_partial_solve_wit_5_pure := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (cm_rep_expr_temps_safe x )) (PreH2 : (expr_pre <> 0)) (PreH3 : (cm_rep_expr_temps_safe e )) (PreH4 : (e = (CMBinaryE (op) (x) (y) (t)))) (PreH5 : (out_lvalue = 0)) (PreH6 : (out_rvalue = 0)) (PreH7 : (cm_rep_expr_temps_safe x )) (PreH8 : (cm_rep_expr_temps_safe y )) (PreH9 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((( &( "left_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (x)))))
  **  ((( &( "left_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (x)))))
  **  ((( &( "right_rvalue" ) )) # Int  |->_)
  **  ((( &( "right_lvalue" ) )) # Int  |->_)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((( &( "out_lvalue" ) )) # Int  |-> out_lvalue)
  **  ((( &( "out_rvalue" ) )) # Int  |-> out_rvalue)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_rep pb y )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (cm_rep_expr_temps_safe y ) ”
.

Definition cm_expr_temps_partial_solve_wit_5_aux := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (cm_rep_expr_temps_safe x )) (PreH2 : (expr_pre <> 0)) (PreH3 : (cm_rep_expr_temps_safe e )) (PreH4 : (e = (CMBinaryE (op) (x) (y) (t)))) (PreH5 : (out_lvalue = 0)) (PreH6 : (out_rvalue = 0)) (PreH7 : (cm_rep_expr_temps_safe x )) (PreH8 : (cm_rep_expr_temps_safe y )) (PreH9 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_rep pb y )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (cm_rep_expr_temps_safe y ) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (cm_rep_expr_temps_safe e ) ” 
  &&  “ (e = (CMBinaryE (op) (x) (y) (t))) ” 
  &&  “ (out_lvalue = 0) ” 
  &&  “ (out_rvalue = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (cm_rep_expr_temps_safe y ) ” 
  &&  “ (pargs = 0) ”
  &&  (cm_expr_rep pb y )
  **  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
.

Definition cm_expr_temps_partial_solve_wit_5 := cm_expr_temps_partial_solve_wit_5_pure -> cm_expr_temps_partial_solve_wit_5_aux.

Definition cm_expr_temps_partial_solve_wit_6 := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_op (e)) = 0)) (PreH2 : (cm_rep_expr_temps_safe y )) (PreH3 : (cm_rep_expr_temps_safe x )) (PreH4 : (expr_pre <> 0)) (PreH5 : (cm_rep_expr_temps_safe e )) (PreH6 : (e = (CMBinaryE (op) (x) (y) (t)))) (PreH7 : (out_lvalue = 0)) (PreH8 : (out_rvalue = 0)) (PreH9 : (cm_rep_expr_temps_safe x )) (PreH10 : (cm_rep_expr_temps_safe y )) (PreH11 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ ((cm_rep_expr_op (e)) = 0) ” 
  &&  “ (cm_rep_expr_temps_safe y ) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (cm_rep_expr_temps_safe e ) ” 
  &&  “ (e = (CMBinaryE (op) (x) (y) (t))) ” 
  &&  “ (out_lvalue = 0) ” 
  &&  “ (out_rvalue = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (cm_rep_expr_temps_safe y ) ” 
  &&  “ (pargs = 0) ”
  &&  (cm_expr_rep pb y )
  **  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
.

Definition cm_expr_temps_partial_solve_wit_7 := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_op (e)) = 1)) (PreH2 : ((cm_rep_expr_op (e)) <> 0)) (PreH3 : (cm_rep_expr_temps_safe y )) (PreH4 : (cm_rep_expr_temps_safe x )) (PreH5 : (expr_pre <> 0)) (PreH6 : (cm_rep_expr_temps_safe e )) (PreH7 : (e = (CMBinaryE (op) (x) (y) (t)))) (PreH8 : (out_lvalue = 0)) (PreH9 : (out_rvalue = 0)) (PreH10 : (cm_rep_expr_temps_safe x )) (PreH11 : (cm_rep_expr_temps_safe y )) (PreH12 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ ((cm_rep_expr_op (e)) = 1) ” 
  &&  “ ((cm_rep_expr_op (e)) <> 0) ” 
  &&  “ (cm_rep_expr_temps_safe y ) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (cm_rep_expr_temps_safe e ) ” 
  &&  “ (e = (CMBinaryE (op) (x) (y) (t))) ” 
  &&  “ (out_lvalue = 0) ” 
  &&  “ (out_rvalue = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (cm_rep_expr_temps_safe y ) ” 
  &&  “ (pargs = 0) ”
  &&  (cm_expr_rep pb y )
  **  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
.

Definition cm_expr_temps_partial_solve_wit_8 := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : ((cm_rep_expr_op (e)) <> 1)) (PreH2 : ((cm_rep_expr_op (e)) <> 0)) (PreH3 : (cm_rep_expr_temps_safe y )) (PreH4 : (cm_rep_expr_temps_safe x )) (PreH5 : (expr_pre <> 0)) (PreH6 : (cm_rep_expr_temps_safe e )) (PreH7 : (e = (CMBinaryE (op) (x) (y) (t)))) (PreH8 : (out_lvalue = 0)) (PreH9 : (out_rvalue = 0)) (PreH10 : (cm_rep_expr_temps_safe x )) (PreH11 : (cm_rep_expr_temps_safe y )) (PreH12 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ ((cm_rep_expr_op (e)) <> 1) ” 
  &&  “ ((cm_rep_expr_op (e)) <> 0) ” 
  &&  “ (cm_rep_expr_temps_safe y ) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (cm_rep_expr_temps_safe e ) ” 
  &&  “ (e = (CMBinaryE (op) (x) (y) (t))) ” 
  &&  “ (out_lvalue = 0) ” 
  &&  “ (out_rvalue = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (cm_rep_expr_temps_safe y ) ” 
  &&  “ (pargs = 0) ”
  &&  (cm_expr_rep pb y )
  **  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
.

Definition cm_expr_temps_partial_solve_wit_9_pure := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (expr_pre <> 0)) (PreH2 : (cm_rep_expr_temps_safe e )) (PreH3 : (e = (CMUnaryE (op) (x) (t)))) (PreH4 : (out_lvalue = 0)) (PreH5 : (out_rvalue = 0)) (PreH6 : (cm_rep_expr_temps_safe x )) (PreH7 : (pa <> 0)) (PreH8 : (pb = 0)) (PreH9 : (pargs = 0)) ,
  ((( &( "child_rvalue" ) )) # Int  |->_)
  **  ((( &( "child_lvalue" ) )) # Int  |->_)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((( &( "out_lvalue" ) )) # Int  |-> out_lvalue)
  **  ((( &( "out_rvalue" ) )) # Int  |-> out_rvalue)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_rep pa x )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (cm_rep_expr_temps_safe x ) ”
.

Definition cm_expr_temps_partial_solve_wit_9_aux := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (op: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (expr_pre <> 0)) (PreH2 : (cm_rep_expr_temps_safe e )) (PreH3 : (e = (CMUnaryE (op) (x) (t)))) (PreH4 : (out_lvalue = 0)) (PreH5 : (out_rvalue = 0)) (PreH6 : (cm_rep_expr_temps_safe x )) (PreH7 : (pa <> 0)) (PreH8 : (pb = 0)) (PreH9 : (pargs = 0)) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_rep pa x )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (cm_rep_expr_temps_safe e ) ” 
  &&  “ (e = (CMUnaryE (op) (x) (t))) ” 
  &&  “ (out_lvalue = 0) ” 
  &&  “ (out_rvalue = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (pa <> 0) ” 
  &&  “ (pb = 0) ” 
  &&  “ (pargs = 0) ”
  &&  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
.

Definition cm_expr_temps_partial_solve_wit_9 := cm_expr_temps_partial_solve_wit_9_pure -> cm_expr_temps_partial_solve_wit_9_aux.

Definition cm_expr_temps_partial_solve_wit_10_pure := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (expr_pre <> 0)) (PreH2 : (cm_rep_expr_temps_safe e )) (PreH3 : (e = (CMIndexE (x) (y) (t)))) (PreH4 : (out_lvalue = 0)) (PreH5 : (out_rvalue = 0)) (PreH6 : (cm_rep_expr_temps_safe x )) (PreH7 : (cm_rep_expr_temps_safe y )) (PreH8 : (pargs = 0)) ,
  ((( &( "index_rvalue" ) )) # Int  |->_)
  **  ((( &( "index_lvalue" ) )) # Int  |->_)
  **  ((( &( "base_rvalue" ) )) # Int  |->_)
  **  ((( &( "base_lvalue" ) )) # Int  |->_)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((( &( "out_lvalue" ) )) # Int  |-> out_lvalue)
  **  ((( &( "out_rvalue" ) )) # Int  |-> out_rvalue)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_rep pa x )
  **  (cm_expr_rep pb y )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (cm_rep_expr_temps_safe x ) ”
.

Definition cm_expr_temps_partial_solve_wit_10_aux := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (expr_pre <> 0)) (PreH2 : (cm_rep_expr_temps_safe e )) (PreH3 : (e = (CMIndexE (x) (y) (t)))) (PreH4 : (out_lvalue = 0)) (PreH5 : (out_rvalue = 0)) (PreH6 : (cm_rep_expr_temps_safe x )) (PreH7 : (cm_rep_expr_temps_safe y )) (PreH8 : (pargs = 0)) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_rep pa x )
  **  (cm_expr_rep pb y )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (cm_rep_expr_temps_safe e ) ” 
  &&  “ (e = (CMIndexE (x) (y) (t))) ” 
  &&  “ (out_lvalue = 0) ” 
  &&  “ (out_rvalue = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (cm_rep_expr_temps_safe y ) ” 
  &&  “ (pargs = 0) ”
  &&  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_rep pb y )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
.

Definition cm_expr_temps_partial_solve_wit_10 := cm_expr_temps_partial_solve_wit_10_pure -> cm_expr_temps_partial_solve_wit_10_aux.

Definition cm_expr_temps_partial_solve_wit_11_pure := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (cm_rep_expr_temps_safe x )) (PreH2 : (expr_pre <> 0)) (PreH3 : (cm_rep_expr_temps_safe e )) (PreH4 : (e = (CMIndexE (x) (y) (t)))) (PreH5 : (out_lvalue = 0)) (PreH6 : (out_rvalue = 0)) (PreH7 : (cm_rep_expr_temps_safe x )) (PreH8 : (cm_rep_expr_temps_safe y )) (PreH9 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((( &( "base_lvalue" ) )) # Int  |-> (cm_tleft ((cm_expr_tpair (x)))))
  **  ((( &( "base_rvalue" ) )) # Int  |-> (cm_tright ((cm_expr_tpair (x)))))
  **  ((( &( "index_rvalue" ) )) # Int  |->_)
  **  ((( &( "index_lvalue" ) )) # Int  |->_)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((( &( "out_lvalue" ) )) # Int  |-> out_lvalue)
  **  ((( &( "out_rvalue" ) )) # Int  |-> out_rvalue)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_rep pb y )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (cm_rep_expr_temps_safe y ) ”
.

Definition cm_expr_temps_partial_solve_wit_11_aux := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (cm_rep_expr_temps_safe x )) (PreH2 : (expr_pre <> 0)) (PreH3 : (cm_rep_expr_temps_safe e )) (PreH4 : (e = (CMIndexE (x) (y) (t)))) (PreH5 : (out_lvalue = 0)) (PreH6 : (out_rvalue = 0)) (PreH7 : (cm_rep_expr_temps_safe x )) (PreH8 : (cm_rep_expr_temps_safe y )) (PreH9 : (pargs = 0)) ,
  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_rep pb y )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (cm_rep_expr_temps_safe y ) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (cm_rep_expr_temps_safe e ) ” 
  &&  “ (e = (CMIndexE (x) (y) (t))) ” 
  &&  “ (out_lvalue = 0) ” 
  &&  “ (out_rvalue = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (cm_rep_expr_temps_safe y ) ” 
  &&  “ (pargs = 0) ”
  &&  (cm_expr_rep pb y )
  **  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
.

Definition cm_expr_temps_partial_solve_wit_11 := cm_expr_temps_partial_solve_wit_11_pure -> cm_expr_temps_partial_solve_wit_11_aux.

Definition cm_expr_temps_partial_solve_wit_12 := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (y: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (cm_rep_expr_temps_safe y )) (PreH2 : (cm_rep_expr_temps_safe x )) (PreH3 : (expr_pre <> 0)) (PreH4 : (cm_rep_expr_temps_safe e )) (PreH5 : (e = (CMIndexE (x) (y) (t)))) (PreH6 : (out_lvalue = 0)) (PreH7 : (out_rvalue = 0)) (PreH8 : (cm_rep_expr_temps_safe x )) (PreH9 : (cm_rep_expr_temps_safe y )) (PreH10 : (pargs = 0)) ,
  (cm_expr_rep pb y )
  **  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (cm_rep_expr_temps_safe y ) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (cm_rep_expr_temps_safe e ) ” 
  &&  “ (e = (CMIndexE (x) (y) (t))) ” 
  &&  “ (out_lvalue = 0) ” 
  &&  “ (out_rvalue = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (cm_rep_expr_temps_safe y ) ” 
  &&  “ (pargs = 0) ”
  &&  (cm_expr_rep pb y )
  **  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
.

Definition cm_expr_temps_partial_solve_wit_13_pure := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (mid: Z) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (expr_pre <> 0)) (PreH2 : (cm_rep_expr_temps_safe e )) (PreH3 : (e = (CMMemberE (x) (mid) (t)))) (PreH4 : (out_lvalue = 0)) (PreH5 : (out_rvalue = 0)) (PreH6 : (cm_rep_expr_temps_safe x )) (PreH7 : (pa <> 0)) (PreH8 : (pb = 0)) (PreH9 : (pargs = 0)) ,
  ((( &( "base_rvalue" ) )) # Int  |->_)
  **  ((( &( "base_lvalue" ) )) # Int  |->_)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((( &( "out_lvalue" ) )) # Int  |-> out_lvalue)
  **  ((( &( "out_rvalue" ) )) # Int  |-> out_rvalue)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_rep pa x )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (cm_rep_expr_temps_safe x ) ”
.

Definition cm_expr_temps_partial_solve_wit_13_aux := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (mid: Z) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (expr_pre <> 0)) (PreH2 : (cm_rep_expr_temps_safe e )) (PreH3 : (e = (CMMemberE (x) (mid) (t)))) (PreH4 : (out_lvalue = 0)) (PreH5 : (out_rvalue = 0)) (PreH6 : (cm_rep_expr_temps_safe x )) (PreH7 : (pa <> 0)) (PreH8 : (pb = 0)) (PreH9 : (pargs = 0)) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_rep pa x )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (cm_rep_expr_temps_safe e ) ” 
  &&  “ (e = (CMMemberE (x) (mid) (t))) ” 
  &&  “ (out_lvalue = 0) ” 
  &&  “ (out_rvalue = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (pa <> 0) ” 
  &&  “ (pb = 0) ” 
  &&  “ (pargs = 0) ”
  &&  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
.

Definition cm_expr_temps_partial_solve_wit_13 := cm_expr_temps_partial_solve_wit_13_pure -> cm_expr_temps_partial_solve_wit_13_aux.

Definition cm_expr_temps_partial_solve_wit_14_pure := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (fid: Z) (eargs: (@list cm_expr)) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (expr_pre <> 0)) (PreH2 : (cm_rep_expr_temps_safe e )) (PreH3 : (e = (CMCallE (fid) (eargs) (t)))) (PreH4 : (out_lvalue = 0)) (PreH5 : (out_rvalue = 0)) (PreH6 : (cm_rep_args_temps_safe eargs )) (PreH7 : (pa = 0)) (PreH8 : (pb = 0)) ,
  ((( &( "depth" ) )) # Int  |->_)
  **  ((( &( "count" ) )) # Int  |->_)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((( &( "out_lvalue" ) )) # Int  |-> out_lvalue)
  **  ((( &( "out_rvalue" ) )) # Int  |-> out_rvalue)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_arg_list_rep pargs eargs )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (cm_rep_args_temps_safe eargs ) ”
.

Definition cm_expr_temps_partial_solve_wit_14_aux := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (fid: Z) (eargs: (@list cm_expr)) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (expr_pre <> 0)) (PreH2 : (cm_rep_expr_temps_safe e )) (PreH3 : (e = (CMCallE (fid) (eargs) (t)))) (PreH4 : (out_lvalue = 0)) (PreH5 : (out_rvalue = 0)) (PreH6 : (cm_rep_args_temps_safe eargs )) (PreH7 : (pa = 0)) (PreH8 : (pb = 0)) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_arg_list_rep pargs eargs )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (cm_rep_args_temps_safe eargs ) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (cm_rep_expr_temps_safe e ) ” 
  &&  “ (e = (CMCallE (fid) (eargs) (t))) ” 
  &&  “ (out_lvalue = 0) ” 
  &&  “ (out_rvalue = 0) ” 
  &&  “ (cm_rep_args_temps_safe eargs ) ” 
  &&  “ (pa = 0) ” 
  &&  “ (pb = 0) ”
  &&  (cm_arg_list_rep pargs eargs )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
.

Definition cm_expr_temps_partial_solve_wit_14 := cm_expr_temps_partial_solve_wit_14_pure -> cm_expr_temps_partial_solve_wit_14_aux.

Definition cm_expr_temps_partial_solve_wit_15_pure := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (expr_pre <> 0)) (PreH2 : (cm_rep_expr_temps_safe e )) (PreH3 : (e = (CMPutcE (x) (t)))) (PreH4 : (out_lvalue = 0)) (PreH5 : (out_rvalue = 0)) (PreH6 : (cm_rep_expr_temps_safe x )) (PreH7 : (pa <> 0)) (PreH8 : (pb = 0)) (PreH9 : (pargs = 0)) ,
  ((( &( "child_rvalue" ) )) # Int  |->_)
  **  ((( &( "child_lvalue" ) )) # Int  |->_)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((( &( "out_lvalue" ) )) # Int  |-> out_lvalue)
  **  ((( &( "out_rvalue" ) )) # Int  |-> out_rvalue)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_rep pa x )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (cm_rep_expr_temps_safe x ) ”
.

Definition cm_expr_temps_partial_solve_wit_15_aux := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (expr_pre <> 0)) (PreH2 : (cm_rep_expr_temps_safe e )) (PreH3 : (e = (CMPutcE (x) (t)))) (PreH4 : (out_lvalue = 0)) (PreH5 : (out_rvalue = 0)) (PreH6 : (cm_rep_expr_temps_safe x )) (PreH7 : (pa <> 0)) (PreH8 : (pb = 0)) (PreH9 : (pargs = 0)) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_rep pa x )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (cm_rep_expr_temps_safe e ) ” 
  &&  “ (e = (CMPutcE (x) (t))) ” 
  &&  “ (out_lvalue = 0) ” 
  &&  “ (out_rvalue = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (pa <> 0) ” 
  &&  “ (pb = 0) ” 
  &&  “ (pargs = 0) ”
  &&  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
.

Definition cm_expr_temps_partial_solve_wit_15 := cm_expr_temps_partial_solve_wit_15_pure -> cm_expr_temps_partial_solve_wit_15_aux.

Definition cm_expr_temps_partial_solve_wit_16_pure := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (expr_pre <> 0)) (PreH2 : (cm_rep_expr_temps_safe e )) (PreH3 : (e = (CMPutiE (x) (t)))) (PreH4 : (out_lvalue = 0)) (PreH5 : (out_rvalue = 0)) (PreH6 : (cm_rep_expr_temps_safe x )) (PreH7 : (pa <> 0)) (PreH8 : (pb = 0)) (PreH9 : (pargs = 0)) ,
  ((( &( "child_rvalue" ) )) # Int  |->_)
  **  ((( &( "child_lvalue" ) )) # Int  |->_)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((( &( "out_lvalue" ) )) # Int  |-> out_lvalue)
  **  ((( &( "out_rvalue" ) )) # Int  |-> out_rvalue)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_rep pa x )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (cm_rep_expr_temps_safe x ) ”
.

Definition cm_expr_temps_partial_solve_wit_16_aux := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (expr_pre <> 0)) (PreH2 : (cm_rep_expr_temps_safe e )) (PreH3 : (e = (CMPutiE (x) (t)))) (PreH4 : (out_lvalue = 0)) (PreH5 : (out_rvalue = 0)) (PreH6 : (cm_rep_expr_temps_safe x )) (PreH7 : (pa <> 0)) (PreH8 : (pb = 0)) (PreH9 : (pargs = 0)) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_rep pa x )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (cm_rep_expr_temps_safe e ) ” 
  &&  “ (e = (CMPutiE (x) (t))) ” 
  &&  “ (out_lvalue = 0) ” 
  &&  “ (out_rvalue = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (pa <> 0) ” 
  &&  “ (pb = 0) ” 
  &&  “ (pargs = 0) ”
  &&  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
.

Definition cm_expr_temps_partial_solve_wit_16 := cm_expr_temps_partial_solve_wit_16_pure -> cm_expr_temps_partial_solve_wit_16_aux.

Definition cm_expr_temps_partial_solve_wit_17_pure := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (expr_pre <> 0)) (PreH2 : (cm_rep_expr_temps_safe e )) (PreH3 : (e = (CMExitE (x) (t)))) (PreH4 : (out_lvalue = 0)) (PreH5 : (out_rvalue = 0)) (PreH6 : (cm_rep_expr_temps_safe x )) (PreH7 : (pa <> 0)) (PreH8 : (pb = 0)) (PreH9 : (pargs = 0)) ,
  ((( &( "child_rvalue" ) )) # Int  |->_)
  **  ((( &( "child_lvalue" ) )) # Int  |->_)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  ((( &( "lvalue" ) )) # Ptr  |-> lvalue_pre)
  **  ((( &( "rvalue" ) )) # Ptr  |-> rvalue_pre)
  **  ((( &( "out_lvalue" ) )) # Int  |-> out_lvalue)
  **  ((( &( "out_rvalue" ) )) # Int  |-> out_rvalue)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_rep pa x )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (cm_rep_expr_temps_safe x ) ”
.

Definition cm_expr_temps_partial_solve_wit_17_aux := 
forall (rvalue_pre: Z) (lvalue_pre: Z) (expr_pre: Z) (e: cm_expr) (pa: Z) (pb: Z) (pargs: Z) (x: cm_expr) (t: cm_type) (out_lvalue: Z) (out_rvalue: Z) (PreH1 : (expr_pre <> 0)) (PreH2 : (cm_rep_expr_temps_safe e )) (PreH3 : (e = (CMExitE (x) (t)))) (PreH4 : (out_lvalue = 0)) (PreH5 : (out_rvalue = 0)) (PreH6 : (cm_rep_expr_temps_safe x )) (PreH7 : (pa <> 0)) (PreH8 : (pb = 0)) (PreH9 : (pargs = 0)) ,
  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  (cm_expr_rep pa x )
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
|--
  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (expr_pre <> 0) ” 
  &&  “ (cm_rep_expr_temps_safe e ) ” 
  &&  “ (e = (CMExitE (x) (t))) ” 
  &&  “ (out_lvalue = 0) ” 
  &&  “ (out_rvalue = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (pa <> 0) ” 
  &&  “ (pb = 0) ” 
  &&  “ (pargs = 0) ”
  &&  (cm_expr_rep pa x )
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "kind")) # Int  |-> (cm_rep_expr_kind (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "op")) # Int  |-> (cm_rep_expr_op (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "ty")) # Int  |-> (cm_type_encode ((cm_expr_type (e)))))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "value")) # Int64  |-> (cm_rep_expr_value (e)))
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "b")) # Ptr  |-> pb)
  **  ((&((expr_pre)  # "cm_expr" ->ₛ "args")) # Ptr  |-> pargs)
  **  ((lvalue_pre) # Int  |->_)
  **  ((rvalue_pre) # Int  |->_)
.

Definition cm_expr_temps_partial_solve_wit_17 := cm_expr_temps_partial_solve_wit_17_pure -> cm_expr_temps_partial_solve_wit_17_aux.

(*----- Function cm_expr_rtemps -----*)

Definition cm_expr_rtemps_return_wit_1 := 
forall (expr_pre: Z) (e: cm_expr) (PreH1 : (cm_rep_expr_temps_safe e )) (PreH2 : (cm_rep_expr_temps_safe e )) ,
  (cm_expr_rep expr_pre e )
|--
  “ (cm_rep_expr_temps_safe e ) ” 
  &&  “ ((cm_tright ((cm_expr_tpair (e)))) = (cm_tright ((cm_expr_tpair (e))))) ”
  &&  (cm_expr_rep expr_pre e )
.

Definition cm_expr_rtemps_partial_solve_wit_1_pure := 
forall (expr_pre: Z) (e: cm_expr) (PreH1 : (cm_rep_expr_temps_safe e )) ,
  ((( &( "rvalue" ) )) # Int  |->_)
  **  ((( &( "lvalue" ) )) # Int  |->_)
  **  ((( &( "expr" ) )) # Ptr  |-> expr_pre)
  **  (cm_expr_rep expr_pre e )
|--
  “ (cm_rep_expr_temps_safe e ) ”
.

Definition cm_expr_rtemps_partial_solve_wit_1_aux := 
forall (expr_pre: Z) (e: cm_expr) (PreH1 : (cm_rep_expr_temps_safe e )) ,
  (cm_expr_rep expr_pre e )
|--
  “ (cm_rep_expr_temps_safe e ) ” 
  &&  “ (cm_rep_expr_temps_safe e ) ”
  &&  (cm_expr_rep expr_pre e )
.

Definition cm_expr_rtemps_partial_solve_wit_1 := cm_expr_rtemps_partial_solve_wit_1_pure -> cm_expr_rtemps_partial_solve_wit_1_aux.

(*----- Function cmc_stmt_temps -----*)

Definition cmc_stmt_temps_safety_wit_1 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : (stmt_pre <> 0)) (PreH2 : (cm_rep_stmt_temps_safe s )) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "stmt" ) )) # Ptr  |-> stmt_pre)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_stmt_temps_safety_wit_2 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : (stmt_pre <> 0)) (PreH2 : (cm_rep_stmt_temps_safe s )) ,
  ((( &( "result" ) )) # Int  |-> 0)
  **  ((( &( "stmt" ) )) # Ptr  |-> stmt_pre)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmc_stmt_temps_safety_wit_3 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH2 : (stmt_pre <> 0)) (PreH3 : (cm_rep_stmt_temps_safe s )) ,
  ((( &( "result" ) )) # Int  |-> 0)
  **  ((( &( "stmt" ) )) # Ptr  |-> stmt_pre)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition cmc_stmt_temps_safety_wit_4 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH2 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH3 : (stmt_pre <> 0)) (PreH4 : (cm_rep_stmt_temps_safe s )) ,
  ((( &( "result" ) )) # Int  |-> 0)
  **  ((( &( "stmt" ) )) # Ptr  |-> stmt_pre)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition cmc_stmt_temps_safety_wit_5 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH2 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH3 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH4 : (stmt_pre <> 0)) (PreH5 : (cm_rep_stmt_temps_safe s )) ,
  ((( &( "result" ) )) # Int  |-> 0)
  **  ((( &( "stmt" ) )) # Ptr  |-> stmt_pre)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition cmc_stmt_temps_safety_wit_6 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH2 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH3 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH4 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH5 : (stmt_pre <> 0)) (PreH6 : (cm_rep_stmt_temps_safe s )) ,
  ((( &( "result" ) )) # Int  |-> 0)
  **  ((( &( "stmt" ) )) # Ptr  |-> stmt_pre)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ (5 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 5) ”
.

Definition cmc_stmt_temps_safety_wit_7 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH2 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH3 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH4 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH5 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH6 : (stmt_pre <> 0)) (PreH7 : (cm_rep_stmt_temps_safe s )) ,
  ((( &( "result" ) )) # Int  |-> 0)
  **  ((( &( "stmt" ) )) # Ptr  |-> stmt_pre)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ (6 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 6) ”
.

Definition cmc_stmt_temps_safety_wit_8 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH2 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH3 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH4 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH5 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH7 : (stmt_pre <> 0)) (PreH8 : (cm_rep_stmt_temps_safe s )) ,
  ((( &( "result" ) )) # Int  |-> 0)
  **  ((( &( "stmt" ) )) # Ptr  |-> stmt_pre)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ (7 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 7) ”
.

Definition cmc_stmt_temps_safety_wit_9 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_kind (s)) <> 7)) (PreH2 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH3 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH4 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH5 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH8 : (stmt_pre <> 0)) (PreH9 : (cm_rep_stmt_temps_safe s )) ,
  ((( &( "result" ) )) # Int  |-> 0)
  **  ((( &( "stmt" ) )) # Ptr  |-> stmt_pre)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_stmt_temps_safety_wit_10 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_kind (s)) = 0)) (PreH2 : ((cm_rep_stmt_kind (s)) <> 7)) (PreH3 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH4 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH5 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH8 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH9 : (stmt_pre <> 0)) (PreH10 : (cm_rep_stmt_temps_safe s )) ,
  ((( &( "result" ) )) # Int  |-> 0)
  **  ((( &( "stmt" ) )) # Ptr  |-> stmt_pre)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_stmt_temps_safety_wit_11 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_kind (s)) <> 0)) (PreH2 : ((cm_rep_stmt_kind (s)) <> 7)) (PreH3 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH4 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH5 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH8 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH9 : (stmt_pre <> 0)) (PreH10 : (cm_rep_stmt_temps_safe s )) ,
  ((( &( "result" ) )) # Int  |-> 0)
  **  ((( &( "stmt" ) )) # Ptr  |-> stmt_pre)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition cmc_stmt_temps_safety_wit_12 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_kind (s)) = 2)) (PreH2 : ((cm_rep_stmt_kind (s)) <> 0)) (PreH3 : ((cm_rep_stmt_kind (s)) <> 7)) (PreH4 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH5 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH8 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH9 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH10 : (stmt_pre <> 0)) (PreH11 : (cm_rep_stmt_temps_safe s )) ,
  ((( &( "result" ) )) # Int  |-> 0)
  **  ((( &( "stmt" ) )) # Ptr  |-> stmt_pre)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_stmt_temps_safety_wit_13 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_kind (s)) <> 2)) (PreH2 : ((cm_rep_stmt_kind (s)) <> 0)) (PreH3 : ((cm_rep_stmt_kind (s)) <> 7)) (PreH4 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH5 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH8 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH9 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH10 : (stmt_pre <> 0)) (PreH11 : (cm_rep_stmt_temps_safe s )) ,
  ((( &( "result" ) )) # Int  |-> 0)
  **  ((( &( "stmt" ) )) # Ptr  |-> stmt_pre)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition cmc_stmt_temps_safety_wit_14 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_kind (s)) = 8)) (PreH2 : ((cm_rep_stmt_kind (s)) <> 2)) (PreH3 : ((cm_rep_stmt_kind (s)) <> 0)) (PreH4 : ((cm_rep_stmt_kind (s)) <> 7)) (PreH5 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH8 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH9 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH10 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH11 : (stmt_pre <> 0)) (PreH12 : (cm_rep_stmt_temps_safe s )) ,
  ((( &( "result" ) )) # Int  |-> 0)
  **  ((( &( "stmt" ) )) # Ptr  |-> stmt_pre)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_stmt_temps_safety_wit_15 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_kind (s)) <> 8)) (PreH2 : ((cm_rep_stmt_kind (s)) <> 2)) (PreH3 : ((cm_rep_stmt_kind (s)) <> 0)) (PreH4 : ((cm_rep_stmt_kind (s)) <> 7)) (PreH5 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH8 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH9 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH10 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH11 : (stmt_pre <> 0)) (PreH12 : (cm_rep_stmt_temps_safe s )) ,
  ((( &( "result" ) )) # Int  |-> 0)
  **  ((( &( "stmt" ) )) # Ptr  |-> stmt_pre)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ (9 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 9) ”
.

Definition cmc_stmt_temps_safety_wit_16 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_kind (s)) = 9)) (PreH2 : ((cm_rep_stmt_kind (s)) <> 8)) (PreH3 : ((cm_rep_stmt_kind (s)) <> 2)) (PreH4 : ((cm_rep_stmt_kind (s)) <> 0)) (PreH5 : ((cm_rep_stmt_kind (s)) <> 7)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH8 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH9 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH10 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH11 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH12 : (stmt_pre <> 0)) (PreH13 : (cm_rep_stmt_temps_safe s )) ,
  ((( &( "result" ) )) # Int  |-> 0)
  **  ((( &( "stmt" ) )) # Ptr  |-> stmt_pre)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_stmt_temps_safety_wit_17 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_kind (s)) <> 9)) (PreH2 : ((cm_rep_stmt_kind (s)) <> 8)) (PreH3 : ((cm_rep_stmt_kind (s)) <> 2)) (PreH4 : ((cm_rep_stmt_kind (s)) <> 0)) (PreH5 : ((cm_rep_stmt_kind (s)) <> 7)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH8 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH9 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH10 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH11 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH12 : (stmt_pre <> 0)) (PreH13 : (cm_rep_stmt_temps_safe s )) ,
  ((( &( "result" ) )) # Int  |-> 0)
  **  ((( &( "stmt" ) )) # Ptr  |-> stmt_pre)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_stmt_temps_entail_wit_1 := 
(
forall (stmt_pre: Z) (s: cm_stmt) (PreH1 : (cm_rep_stmt_temps_safe s )) ,
  (cm_stmt_rep stmt_pre s )
|--
  EX (pb: Z)  (pa: Z)  (pe: Z) ,
  “ (stmt_pre <> 0) ” 
  &&  “ (cm_rep_stmt_temps_safe s ) ”
  &&  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
) \/
(
forall (stmt_pre: Z) (s: cm_stmt) (PreH1 : (cm_rep_stmt_temps_safe s )) ,
  (cm_stmt_rep stmt_pre s )
|--
  EX (pb: Z)  (pa: Z)  (pe: Z) ,
  “ (stmt_pre <> 0) ” 
  &&  “ (cm_rep_stmt_temps_safe s ) ”
  &&  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
).

Definition cmc_stmt_temps_entail_wit_2 := 
(
forall (stmt_pre: Z) (s: cm_stmt) (pe_2: Z) (pa_2: Z) (pb_2: Z) (PreH1 : ((cm_rep_stmt_kind (s)) = 1)) (PreH2 : (stmt_pre <> 0)) (PreH3 : (cm_rep_stmt_temps_safe s )) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe_2)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa_2)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb_2)
  **  (cm_stmt_payload s pe_2 pa_2 pb_2 )
|--
  EX (pb: Z)  (pa: Z)  (pe: Z)  (x: cm_expr) ,
  “ (stmt_pre <> 0) ” 
  &&  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (s = (CMExprS (x))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pa = 0) ” 
  &&  “ (pb = 0) ”
  &&  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_expr_rep pe x )
) \/
(
forall (stmt_pre: Z) (s: cm_stmt) (pe_2: Z) (pa_2: Z) (pb_2: Z) (PreH1 : ((cm_rep_stmt_kind (s)) = 1)) (PreH2 : (stmt_pre <> 0)) (PreH3 : (cm_rep_stmt_temps_safe s )) ,
  (cm_stmt_payload s pe_2 pa_2 pb_2 )
|--
  EX (x: cm_expr) ,
  “ (pb_2 = 0) ” 
  &&  “ (pa_2 = 0) ” 
  &&  “ (pb_2 = 0) ” 
  &&  “ (pa_2 = 0) ” 
  &&  “ (stmt_pre <> 0) ” 
  &&  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (s = (CMExprS (x))) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (pe_2 <> 0) ”
  &&  (cm_expr_rep pe_2 x )
).

Definition cmc_stmt_temps_entail_wit_3 := 
(
forall (stmt_pre: Z) (s: cm_stmt) (pe_2: Z) (pa_2: Z) (pb_2: Z) (PreH1 : ((cm_rep_stmt_kind (s)) = 3)) (PreH2 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH3 : (stmt_pre <> 0)) (PreH4 : (cm_rep_stmt_temps_safe s )) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe_2)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa_2)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb_2)
  **  (cm_stmt_payload s pe_2 pa_2 pb_2 )
|--
  EX (pb: Z)  (pa: Z)  (pe: Z)  (slotid: Z)  (x: cm_expr) ,
  “ (stmt_pre <> 0) ” 
  &&  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (s = (CMInitS (slotid) (x))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pa = 0) ” 
  &&  “ (pb = 0) ”
  &&  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_expr_rep pe x )
) \/
(
forall (stmt_pre: Z) (s: cm_stmt) (pe_2: Z) (pa_2: Z) (pb_2: Z) (PreH1 : ((cm_rep_stmt_kind (s)) = 3)) (PreH2 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH3 : (stmt_pre <> 0)) (PreH4 : (cm_rep_stmt_temps_safe s )) ,
  (cm_stmt_payload s pe_2 pa_2 pb_2 )
|--
  EX (slotid: Z)  (x: cm_expr) ,
  “ (pb_2 = 0) ” 
  &&  “ (pa_2 = 0) ” 
  &&  “ (pb_2 = 0) ” 
  &&  “ (pa_2 = 0) ” 
  &&  “ (stmt_pre <> 0) ” 
  &&  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (s = (CMInitS (slotid) (x))) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (pe_2 <> 0) ”
  &&  (cm_expr_rep pe_2 x )
).

Definition cmc_stmt_temps_entail_wit_4 := 
(
forall (stmt_pre: Z) (s: cm_stmt) (pe_2: Z) (pa_2: Z) (pb_2: Z) (PreH1 : ((cm_rep_stmt_kind (s)) = 10)) (PreH2 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH3 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH4 : (stmt_pre <> 0)) (PreH5 : (cm_rep_stmt_temps_safe s )) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe_2)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa_2)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb_2)
  **  (cm_stmt_payload s pe_2 pa_2 pb_2 )
|--
  EX (pb: Z)  (pa: Z)  (pe: Z)  (x: cm_expr) ,
  “ (stmt_pre <> 0) ” 
  &&  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (s = (CMReturnS (x))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pa = 0) ” 
  &&  “ (pb = 0) ”
  &&  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_expr_rep pe x )
) \/
(
forall (stmt_pre: Z) (s: cm_stmt) (pe_2: Z) (pa_2: Z) (pb_2: Z) (PreH1 : ((cm_rep_stmt_kind (s)) = 10)) (PreH2 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH3 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH4 : (stmt_pre <> 0)) (PreH5 : (cm_rep_stmt_temps_safe s )) ,
  (cm_stmt_payload s pe_2 pa_2 pb_2 )
|--
  EX (x: cm_expr) ,
  “ (pb_2 = 0) ” 
  &&  “ (pa_2 = 0) ” 
  &&  “ (pb_2 = 0) ” 
  &&  “ (pa_2 = 0) ” 
  &&  “ (stmt_pre <> 0) ” 
  &&  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (s = (CMReturnS (x))) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (pe_2 <> 0) ”
  &&  (cm_expr_rep pe_2 x )
).

Definition cmc_stmt_temps_entail_wit_5 := 
(
forall (stmt_pre: Z) (s: cm_stmt) (pe_2: Z) (pa_2: Z) (pb_2: Z) (PreH1 : ((cm_rep_stmt_kind (s)) = 4)) (PreH2 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH3 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH4 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH5 : (stmt_pre <> 0)) (PreH6 : (cm_rep_stmt_temps_safe s )) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe_2)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa_2)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb_2)
  **  (cm_stmt_payload s pe_2 pa_2 pb_2 )
|--
  EX (pb: Z)  (pa: Z)  (pe: Z)  (x: cm_stmt)  (y: cm_stmt) ,
  “ (stmt_pre <> 0) ” 
  &&  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (s = (CMSeqS (x) (y))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (cm_rep_stmt_temps_safe x ) ” 
  &&  “ (cm_rep_stmt_temps_safe y ) ” 
  &&  “ (pe = 0) ”
  &&  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_rep pa x )
  **  (cm_stmt_rep pb y )
) \/
(
forall (stmt_pre: Z) (s: cm_stmt) (pe_2: Z) (pa_2: Z) (pb_2: Z) (PreH1 : ((cm_rep_stmt_kind (s)) = 4)) (PreH2 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH3 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH4 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH5 : (stmt_pre <> 0)) (PreH6 : (cm_rep_stmt_temps_safe s )) ,
  (cm_stmt_payload s pe_2 pa_2 pb_2 )
|--
  EX (x: cm_stmt)  (y: cm_stmt) ,
  “ (pe_2 = 0) ” 
  &&  “ (pe_2 = 0) ” 
  &&  “ (stmt_pre <> 0) ” 
  &&  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (s = (CMSeqS (x) (y))) ” 
  &&  “ (cm_rep_stmt_temps_safe x ) ” 
  &&  “ (cm_rep_stmt_temps_safe y ) ”
  &&  (cm_stmt_rep pa_2 x )
  **  (cm_stmt_rep pb_2 y )
).

Definition cmc_stmt_temps_entail_wit_6 := 
(
forall (stmt_pre: Z) (s: cm_stmt) (pe_2: Z) (pa_2: Z) (pb_2: Z) (PreH1 : ((cm_rep_stmt_kind (s)) = 5)) (PreH2 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH3 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH4 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH5 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH6 : (stmt_pre <> 0)) (PreH7 : (cm_rep_stmt_temps_safe s )) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe_2)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa_2)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb_2)
  **  (cm_stmt_payload s pe_2 pa_2 pb_2 )
|--
  EX (pb: Z)  (pa: Z)  (pe: Z)  (x: cm_stmt) ,
  “ (stmt_pre <> 0) ” 
  &&  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (s = (CMBlockS (x))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (cm_rep_stmt_temps_safe x ) ” 
  &&  “ (pe = 0) ” 
  &&  “ (pa <> 0) ” 
  &&  “ (pb = 0) ”
  &&  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_rep pa x )
) \/
(
forall (stmt_pre: Z) (s: cm_stmt) (pe_2: Z) (pa_2: Z) (pb_2: Z) (PreH1 : ((cm_rep_stmt_kind (s)) = 5)) (PreH2 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH3 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH4 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH5 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH6 : (stmt_pre <> 0)) (PreH7 : (cm_rep_stmt_temps_safe s )) ,
  (cm_stmt_payload s pe_2 pa_2 pb_2 )
|--
  EX (x: cm_stmt) ,
  “ (pb_2 = 0) ” 
  &&  “ (pe_2 = 0) ” 
  &&  “ (pb_2 = 0) ” 
  &&  “ (pe_2 = 0) ” 
  &&  “ (stmt_pre <> 0) ” 
  &&  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (s = (CMBlockS (x))) ” 
  &&  “ (cm_rep_stmt_temps_safe x ) ” 
  &&  “ (pa_2 <> 0) ”
  &&  (cm_stmt_rep pa_2 x )
).

Definition cmc_stmt_temps_entail_wit_7 := 
(
forall (stmt_pre: Z) (s: cm_stmt) (pe_2: Z) (pa_2: Z) (pb_2: Z) (PreH1 : ((cm_rep_stmt_kind (s)) = 6)) (PreH2 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH3 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH4 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH5 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH7 : (stmt_pre <> 0)) (PreH8 : (cm_rep_stmt_temps_safe s )) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe_2)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa_2)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb_2)
  **  (cm_stmt_payload s pe_2 pa_2 pb_2 )
|--
  EX (pb: Z)  (pa: Z)  (pe: Z)  (x: cm_expr)  (y: cm_stmt)  (z: cm_stmt) ,
  “ (stmt_pre <> 0) ” 
  &&  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (s = (CMIfS (x) (y) (z))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (cm_rep_stmt_temps_safe y ) ” 
  &&  “ (cm_rep_stmt_temps_safe z ) ”
  &&  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_expr_rep pe x )
  **  (cm_stmt_rep pa y )
  **  (cm_stmt_rep pb z )
) \/
(
forall (stmt_pre: Z) (s: cm_stmt) (pe_2: Z) (pa_2: Z) (pb_2: Z) (PreH1 : ((cm_rep_stmt_kind (s)) = 6)) (PreH2 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH3 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH4 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH5 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH7 : (stmt_pre <> 0)) (PreH8 : (cm_rep_stmt_temps_safe s )) ,
  (cm_stmt_payload s pe_2 pa_2 pb_2 )
|--
  EX (x: cm_expr)  (y: cm_stmt)  (z: cm_stmt) ,
  “ (stmt_pre <> 0) ” 
  &&  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (s = (CMIfS (x) (y) (z))) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (cm_rep_stmt_temps_safe y ) ” 
  &&  “ (cm_rep_stmt_temps_safe z ) ”
  &&  (cm_expr_rep pe_2 x )
  **  (cm_stmt_rep pa_2 y )
  **  (cm_stmt_rep pb_2 z )
).

Definition cmc_stmt_temps_entail_wit_8 := 
(
forall (stmt_pre: Z) (s: cm_stmt) (pe_2: Z) (pa_2: Z) (pb_2: Z) (PreH1 : ((cm_rep_stmt_kind (s)) = 7)) (PreH2 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH3 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH4 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH5 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH8 : (stmt_pre <> 0)) (PreH9 : (cm_rep_stmt_temps_safe s )) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe_2)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa_2)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb_2)
  **  (cm_stmt_payload s pe_2 pa_2 pb_2 )
|--
  EX (pb: Z)  (pa: Z)  (pe: Z)  (x: cm_expr)  (y: cm_stmt) ,
  “ (stmt_pre <> 0) ” 
  &&  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (s = (CMWhileS (x) (y))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (cm_rep_stmt_temps_safe y ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pa <> 0) ” 
  &&  “ (pb = 0) ”
  &&  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_expr_rep pe x )
  **  (cm_stmt_rep pa y )
) \/
(
forall (stmt_pre: Z) (s: cm_stmt) (pe_2: Z) (pa_2: Z) (pb_2: Z) (PreH1 : ((cm_rep_stmt_kind (s)) = 7)) (PreH2 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH3 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH4 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH5 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH8 : (stmt_pre <> 0)) (PreH9 : (cm_rep_stmt_temps_safe s )) ,
  (cm_stmt_payload s pe_2 pa_2 pb_2 )
|--
  EX (x: cm_expr)  (y: cm_stmt) ,
  “ (pb_2 = 0) ” 
  &&  “ (pb_2 = 0) ” 
  &&  “ (stmt_pre <> 0) ” 
  &&  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (s = (CMWhileS (x) (y))) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (cm_rep_stmt_temps_safe y ) ” 
  &&  “ (pe_2 <> 0) ” 
  &&  “ (pa_2 <> 0) ”
  &&  (cm_expr_rep pe_2 x )
  **  (cm_stmt_rep pa_2 y )
).

Definition cmc_stmt_temps_return_wit_1 := 
(
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (result: Z) (retval: Z) (PreH1 : (cm_rep_expr_temps_safe x )) (PreH2 : (retval = (cm_tright ((cm_expr_tpair (x)))))) (PreH3 : (stmt_pre <> 0)) (PreH4 : (cm_rep_stmt_temps_safe s )) (PreH5 : (s = (CMExprS (x)))) (PreH6 : (result = 0)) (PreH7 : (cm_rep_expr_temps_safe x )) (PreH8 : (pe <> 0)) (PreH9 : (pa = 0)) (PreH10 : (pb = 0)) ,
  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (retval = (cm_stemps (s))) ” 
  &&  “ (0 <= (cm_stemps (s))) ” 
  &&  “ ((cm_stemps (s)) <= INT_MAX) ”
  &&  (cm_stmt_rep stmt_pre s )
) \/
(
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (result: Z) (retval: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : (cm_rep_expr_temps_safe x )) (PreH6 : (retval = (cm_tright ((cm_expr_tpair (x)))))) (PreH7 : (stmt_pre <> 0)) (PreH8 : (cm_rep_stmt_temps_safe s )) (PreH9 : (s = (CMExprS (x)))) (PreH10 : (result = 0)) (PreH11 : (cm_rep_expr_temps_safe x )) (PreH12 : (pe <> 0)) (PreH13 : (pa = 0)) (PreH14 : (pb = 0)) ,
  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  “ ((cm_stemps (s)) <= INT_MAX) ” 
  &&  “ (0 <= (cm_stemps (s))) ” 
  &&  “ (retval = (cm_stemps (s))) ”
  &&  (cm_stmt_rep stmt_pre s )
).

Definition cmc_stmt_temps_return_wit_1_split_goal_1 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (result: Z) (retval: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : (cm_rep_expr_temps_safe x )) (PreH6 : (retval = (cm_tright ((cm_expr_tpair (x)))))) (PreH7 : (stmt_pre <> 0)) (PreH8 : (cm_rep_stmt_temps_safe s )) (PreH9 : (s = (CMExprS (x)))) (PreH10 : (result = 0)) (PreH11 : (cm_rep_expr_temps_safe x )) (PreH12 : (pe <> 0)) (PreH13 : (pa = 0)) (PreH14 : (pb = 0)) ,
  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  “ ((cm_stemps (s)) <= INT_MAX) ”
.

Definition cmc_stmt_temps_return_wit_1_split_goal_2 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (result: Z) (retval: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : (cm_rep_expr_temps_safe x )) (PreH6 : (retval = (cm_tright ((cm_expr_tpair (x)))))) (PreH7 : (stmt_pre <> 0)) (PreH8 : (cm_rep_stmt_temps_safe s )) (PreH9 : (s = (CMExprS (x)))) (PreH10 : (result = 0)) (PreH11 : (cm_rep_expr_temps_safe x )) (PreH12 : (pe <> 0)) (PreH13 : (pa = 0)) (PreH14 : (pb = 0)) ,
  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  “ (0 <= (cm_stemps (s))) ”
.

Definition cmc_stmt_temps_return_wit_1_split_goal_3 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (result: Z) (retval: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : (cm_rep_expr_temps_safe x )) (PreH6 : (retval = (cm_tright ((cm_expr_tpair (x)))))) (PreH7 : (stmt_pre <> 0)) (PreH8 : (cm_rep_stmt_temps_safe s )) (PreH9 : (s = (CMExprS (x)))) (PreH10 : (result = 0)) (PreH11 : (cm_rep_expr_temps_safe x )) (PreH12 : (pe <> 0)) (PreH13 : (pa = 0)) (PreH14 : (pb = 0)) ,
  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  “ (retval = (cm_stemps (s))) ”
.

Definition cmc_stmt_temps_return_wit_1_split_goal_spatial := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (result: Z) (retval: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : (cm_rep_expr_temps_safe x )) (PreH6 : (retval = (cm_tright ((cm_expr_tpair (x)))))) (PreH7 : (stmt_pre <> 0)) (PreH8 : (cm_rep_stmt_temps_safe s )) (PreH9 : (s = (CMExprS (x)))) (PreH10 : (result = 0)) (PreH11 : (cm_rep_expr_temps_safe x )) (PreH12 : (pe <> 0)) (PreH13 : (pa = 0)) (PreH14 : (pb = 0)) ,
  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  (cm_stmt_rep stmt_pre s )
.

Definition cmc_stmt_temps_return_wit_2 := 
(
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (slotid: Z) (x: cm_expr) (result: Z) (retval: Z) (PreH1 : (cm_rep_expr_temps_safe x )) (PreH2 : (retval = (cm_tright ((cm_expr_tpair (x)))))) (PreH3 : (stmt_pre <> 0)) (PreH4 : (cm_rep_stmt_temps_safe s )) (PreH5 : (s = (CMInitS (slotid) (x)))) (PreH6 : (result = 0)) (PreH7 : (cm_rep_expr_temps_safe x )) (PreH8 : (pe <> 0)) (PreH9 : (pa = 0)) (PreH10 : (pb = 0)) ,
  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (retval = (cm_stemps (s))) ” 
  &&  “ (0 <= (cm_stemps (s))) ” 
  &&  “ ((cm_stemps (s)) <= INT_MAX) ”
  &&  (cm_stmt_rep stmt_pre s )
) \/
(
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (slotid: Z) (x: cm_expr) (result: Z) (retval: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : (cm_rep_expr_temps_safe x )) (PreH6 : (retval = (cm_tright ((cm_expr_tpair (x)))))) (PreH7 : (stmt_pre <> 0)) (PreH8 : (cm_rep_stmt_temps_safe s )) (PreH9 : (s = (CMInitS (slotid) (x)))) (PreH10 : (result = 0)) (PreH11 : (cm_rep_expr_temps_safe x )) (PreH12 : (pe <> 0)) (PreH13 : (pa = 0)) (PreH14 : (pb = 0)) ,
  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  “ ((cm_stemps (s)) <= INT_MAX) ” 
  &&  “ (0 <= (cm_stemps (s))) ” 
  &&  “ (retval = (cm_stemps (s))) ”
  &&  (cm_stmt_rep stmt_pre s )
).

Definition cmc_stmt_temps_return_wit_2_split_goal_1 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (slotid: Z) (x: cm_expr) (result: Z) (retval: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : (cm_rep_expr_temps_safe x )) (PreH6 : (retval = (cm_tright ((cm_expr_tpair (x)))))) (PreH7 : (stmt_pre <> 0)) (PreH8 : (cm_rep_stmt_temps_safe s )) (PreH9 : (s = (CMInitS (slotid) (x)))) (PreH10 : (result = 0)) (PreH11 : (cm_rep_expr_temps_safe x )) (PreH12 : (pe <> 0)) (PreH13 : (pa = 0)) (PreH14 : (pb = 0)) ,
  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  “ ((cm_stemps (s)) <= INT_MAX) ”
.

Definition cmc_stmt_temps_return_wit_2_split_goal_2 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (slotid: Z) (x: cm_expr) (result: Z) (retval: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : (cm_rep_expr_temps_safe x )) (PreH6 : (retval = (cm_tright ((cm_expr_tpair (x)))))) (PreH7 : (stmt_pre <> 0)) (PreH8 : (cm_rep_stmt_temps_safe s )) (PreH9 : (s = (CMInitS (slotid) (x)))) (PreH10 : (result = 0)) (PreH11 : (cm_rep_expr_temps_safe x )) (PreH12 : (pe <> 0)) (PreH13 : (pa = 0)) (PreH14 : (pb = 0)) ,
  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  “ (0 <= (cm_stemps (s))) ”
.

Definition cmc_stmt_temps_return_wit_2_split_goal_3 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (slotid: Z) (x: cm_expr) (result: Z) (retval: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : (cm_rep_expr_temps_safe x )) (PreH6 : (retval = (cm_tright ((cm_expr_tpair (x)))))) (PreH7 : (stmt_pre <> 0)) (PreH8 : (cm_rep_stmt_temps_safe s )) (PreH9 : (s = (CMInitS (slotid) (x)))) (PreH10 : (result = 0)) (PreH11 : (cm_rep_expr_temps_safe x )) (PreH12 : (pe <> 0)) (PreH13 : (pa = 0)) (PreH14 : (pb = 0)) ,
  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  “ (retval = (cm_stemps (s))) ”
.

Definition cmc_stmt_temps_return_wit_2_split_goal_spatial := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (slotid: Z) (x: cm_expr) (result: Z) (retval: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : (cm_rep_expr_temps_safe x )) (PreH6 : (retval = (cm_tright ((cm_expr_tpair (x)))))) (PreH7 : (stmt_pre <> 0)) (PreH8 : (cm_rep_stmt_temps_safe s )) (PreH9 : (s = (CMInitS (slotid) (x)))) (PreH10 : (result = 0)) (PreH11 : (cm_rep_expr_temps_safe x )) (PreH12 : (pe <> 0)) (PreH13 : (pa = 0)) (PreH14 : (pb = 0)) ,
  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  (cm_stmt_rep stmt_pre s )
.

Definition cmc_stmt_temps_return_wit_3 := 
(
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (result: Z) (retval: Z) (PreH1 : (cm_rep_expr_temps_safe x )) (PreH2 : (retval = (cm_tright ((cm_expr_tpair (x)))))) (PreH3 : (stmt_pre <> 0)) (PreH4 : (cm_rep_stmt_temps_safe s )) (PreH5 : (s = (CMReturnS (x)))) (PreH6 : (result = 0)) (PreH7 : (cm_rep_expr_temps_safe x )) (PreH8 : (pe <> 0)) (PreH9 : (pa = 0)) (PreH10 : (pb = 0)) ,
  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (retval = (cm_stemps (s))) ” 
  &&  “ (0 <= (cm_stemps (s))) ” 
  &&  “ ((cm_stemps (s)) <= INT_MAX) ”
  &&  (cm_stmt_rep stmt_pre s )
) \/
(
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (result: Z) (retval: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : (cm_rep_expr_temps_safe x )) (PreH6 : (retval = (cm_tright ((cm_expr_tpair (x)))))) (PreH7 : (stmt_pre <> 0)) (PreH8 : (cm_rep_stmt_temps_safe s )) (PreH9 : (s = (CMReturnS (x)))) (PreH10 : (result = 0)) (PreH11 : (cm_rep_expr_temps_safe x )) (PreH12 : (pe <> 0)) (PreH13 : (pa = 0)) (PreH14 : (pb = 0)) ,
  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  “ ((cm_stemps (s)) <= INT_MAX) ” 
  &&  “ (0 <= (cm_stemps (s))) ” 
  &&  “ (retval = (cm_stemps (s))) ”
  &&  (cm_stmt_rep stmt_pre s )
).

Definition cmc_stmt_temps_return_wit_3_split_goal_1 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (result: Z) (retval: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : (cm_rep_expr_temps_safe x )) (PreH6 : (retval = (cm_tright ((cm_expr_tpair (x)))))) (PreH7 : (stmt_pre <> 0)) (PreH8 : (cm_rep_stmt_temps_safe s )) (PreH9 : (s = (CMReturnS (x)))) (PreH10 : (result = 0)) (PreH11 : (cm_rep_expr_temps_safe x )) (PreH12 : (pe <> 0)) (PreH13 : (pa = 0)) (PreH14 : (pb = 0)) ,
  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  “ ((cm_stemps (s)) <= INT_MAX) ”
.

Definition cmc_stmt_temps_return_wit_3_split_goal_2 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (result: Z) (retval: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : (cm_rep_expr_temps_safe x )) (PreH6 : (retval = (cm_tright ((cm_expr_tpair (x)))))) (PreH7 : (stmt_pre <> 0)) (PreH8 : (cm_rep_stmt_temps_safe s )) (PreH9 : (s = (CMReturnS (x)))) (PreH10 : (result = 0)) (PreH11 : (cm_rep_expr_temps_safe x )) (PreH12 : (pe <> 0)) (PreH13 : (pa = 0)) (PreH14 : (pb = 0)) ,
  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  “ (0 <= (cm_stemps (s))) ”
.

Definition cmc_stmt_temps_return_wit_3_split_goal_3 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (result: Z) (retval: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : (cm_rep_expr_temps_safe x )) (PreH6 : (retval = (cm_tright ((cm_expr_tpair (x)))))) (PreH7 : (stmt_pre <> 0)) (PreH8 : (cm_rep_stmt_temps_safe s )) (PreH9 : (s = (CMReturnS (x)))) (PreH10 : (result = 0)) (PreH11 : (cm_rep_expr_temps_safe x )) (PreH12 : (pe <> 0)) (PreH13 : (pa = 0)) (PreH14 : (pb = 0)) ,
  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  “ (retval = (cm_stemps (s))) ”
.

Definition cmc_stmt_temps_return_wit_3_split_goal_spatial := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (result: Z) (retval: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : (cm_rep_expr_temps_safe x )) (PreH6 : (retval = (cm_tright ((cm_expr_tpair (x)))))) (PreH7 : (stmt_pre <> 0)) (PreH8 : (cm_rep_stmt_temps_safe s )) (PreH9 : (s = (CMReturnS (x)))) (PreH10 : (result = 0)) (PreH11 : (cm_rep_expr_temps_safe x )) (PreH12 : (pe <> 0)) (PreH13 : (pa = 0)) (PreH14 : (pb = 0)) ,
  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  (cm_stmt_rep stmt_pre s )
.

Definition cmc_stmt_temps_return_wit_4 := 
(
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_stmt) (y: cm_stmt) (result: Z) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (retval = (cm_imax (retval_2) (retval_3)))) (PreH2 : (cm_rep_stmt_temps_safe y )) (PreH3 : (retval_3 = (cm_stemps (y)))) (PreH4 : (0 <= (cm_stemps (y)))) (PreH5 : ((cm_stemps (y)) <= INT_MAX)) (PreH6 : (cm_rep_stmt_temps_safe x )) (PreH7 : (retval_2 = (cm_stemps (x)))) (PreH8 : (0 <= (cm_stemps (x)))) (PreH9 : ((cm_stemps (x)) <= INT_MAX)) (PreH10 : (stmt_pre <> 0)) (PreH11 : (cm_rep_stmt_temps_safe s )) (PreH12 : (s = (CMSeqS (x) (y)))) (PreH13 : (result = 0)) (PreH14 : (cm_rep_stmt_temps_safe x )) (PreH15 : (cm_rep_stmt_temps_safe y )) (PreH16 : (pe = 0)) ,
  (cm_stmt_rep pb y )
  **  (cm_stmt_rep pa x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (retval = (cm_stemps (s))) ” 
  &&  “ (0 <= (cm_stemps (s))) ” 
  &&  “ ((cm_stemps (s)) <= INT_MAX) ”
  &&  (cm_stmt_rep stmt_pre s )
) \/
(
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_stmt) (y: cm_stmt) (result: Z) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : (retval = (cm_imax (retval_2) (retval_3)))) (PreH6 : (cm_rep_stmt_temps_safe y )) (PreH7 : (retval_3 = (cm_stemps (y)))) (PreH8 : (0 <= (cm_stemps (y)))) (PreH9 : ((cm_stemps (y)) <= INT_MAX)) (PreH10 : (cm_rep_stmt_temps_safe x )) (PreH11 : (retval_2 = (cm_stemps (x)))) (PreH12 : (0 <= (cm_stemps (x)))) (PreH13 : ((cm_stemps (x)) <= INT_MAX)) (PreH14 : (stmt_pre <> 0)) (PreH15 : (cm_rep_stmt_temps_safe s )) (PreH16 : (s = (CMSeqS (x) (y)))) (PreH17 : (result = 0)) (PreH18 : (cm_rep_stmt_temps_safe x )) (PreH19 : (cm_rep_stmt_temps_safe y )) (PreH20 : (pe = 0)) ,
  (cm_stmt_rep pb y )
  **  (cm_stmt_rep pa x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  “ ((cm_stemps (s)) <= INT_MAX) ” 
  &&  “ (0 <= (cm_stemps (s))) ” 
  &&  “ (retval = (cm_stemps (s))) ”
  &&  (cm_stmt_rep stmt_pre s )
).

Definition cmc_stmt_temps_return_wit_4_split_goal_1 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_stmt) (y: cm_stmt) (result: Z) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : (retval = (cm_imax (retval_2) (retval_3)))) (PreH6 : (cm_rep_stmt_temps_safe y )) (PreH7 : (retval_3 = (cm_stemps (y)))) (PreH8 : (0 <= (cm_stemps (y)))) (PreH9 : ((cm_stemps (y)) <= INT_MAX)) (PreH10 : (cm_rep_stmt_temps_safe x )) (PreH11 : (retval_2 = (cm_stemps (x)))) (PreH12 : (0 <= (cm_stemps (x)))) (PreH13 : ((cm_stemps (x)) <= INT_MAX)) (PreH14 : (stmt_pre <> 0)) (PreH15 : (cm_rep_stmt_temps_safe s )) (PreH16 : (s = (CMSeqS (x) (y)))) (PreH17 : (result = 0)) (PreH18 : (cm_rep_stmt_temps_safe x )) (PreH19 : (cm_rep_stmt_temps_safe y )) (PreH20 : (pe = 0)) ,
  (cm_stmt_rep pb y )
  **  (cm_stmt_rep pa x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  “ ((cm_stemps (s)) <= INT_MAX) ”
.

Definition cmc_stmt_temps_return_wit_4_split_goal_2 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_stmt) (y: cm_stmt) (result: Z) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : (retval = (cm_imax (retval_2) (retval_3)))) (PreH6 : (cm_rep_stmt_temps_safe y )) (PreH7 : (retval_3 = (cm_stemps (y)))) (PreH8 : (0 <= (cm_stemps (y)))) (PreH9 : ((cm_stemps (y)) <= INT_MAX)) (PreH10 : (cm_rep_stmt_temps_safe x )) (PreH11 : (retval_2 = (cm_stemps (x)))) (PreH12 : (0 <= (cm_stemps (x)))) (PreH13 : ((cm_stemps (x)) <= INT_MAX)) (PreH14 : (stmt_pre <> 0)) (PreH15 : (cm_rep_stmt_temps_safe s )) (PreH16 : (s = (CMSeqS (x) (y)))) (PreH17 : (result = 0)) (PreH18 : (cm_rep_stmt_temps_safe x )) (PreH19 : (cm_rep_stmt_temps_safe y )) (PreH20 : (pe = 0)) ,
  (cm_stmt_rep pb y )
  **  (cm_stmt_rep pa x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  “ (0 <= (cm_stemps (s))) ”
.

Definition cmc_stmt_temps_return_wit_4_split_goal_3 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_stmt) (y: cm_stmt) (result: Z) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : (retval = (cm_imax (retval_2) (retval_3)))) (PreH6 : (cm_rep_stmt_temps_safe y )) (PreH7 : (retval_3 = (cm_stemps (y)))) (PreH8 : (0 <= (cm_stemps (y)))) (PreH9 : ((cm_stemps (y)) <= INT_MAX)) (PreH10 : (cm_rep_stmt_temps_safe x )) (PreH11 : (retval_2 = (cm_stemps (x)))) (PreH12 : (0 <= (cm_stemps (x)))) (PreH13 : ((cm_stemps (x)) <= INT_MAX)) (PreH14 : (stmt_pre <> 0)) (PreH15 : (cm_rep_stmt_temps_safe s )) (PreH16 : (s = (CMSeqS (x) (y)))) (PreH17 : (result = 0)) (PreH18 : (cm_rep_stmt_temps_safe x )) (PreH19 : (cm_rep_stmt_temps_safe y )) (PreH20 : (pe = 0)) ,
  (cm_stmt_rep pb y )
  **  (cm_stmt_rep pa x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  “ (retval = (cm_stemps (s))) ”
.

Definition cmc_stmt_temps_return_wit_4_split_goal_spatial := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_stmt) (y: cm_stmt) (result: Z) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : (retval = (cm_imax (retval_2) (retval_3)))) (PreH6 : (cm_rep_stmt_temps_safe y )) (PreH7 : (retval_3 = (cm_stemps (y)))) (PreH8 : (0 <= (cm_stemps (y)))) (PreH9 : ((cm_stemps (y)) <= INT_MAX)) (PreH10 : (cm_rep_stmt_temps_safe x )) (PreH11 : (retval_2 = (cm_stemps (x)))) (PreH12 : (0 <= (cm_stemps (x)))) (PreH13 : ((cm_stemps (x)) <= INT_MAX)) (PreH14 : (stmt_pre <> 0)) (PreH15 : (cm_rep_stmt_temps_safe s )) (PreH16 : (s = (CMSeqS (x) (y)))) (PreH17 : (result = 0)) (PreH18 : (cm_rep_stmt_temps_safe x )) (PreH19 : (cm_rep_stmt_temps_safe y )) (PreH20 : (pe = 0)) ,
  (cm_stmt_rep pb y )
  **  (cm_stmt_rep pa x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  (cm_stmt_rep stmt_pre s )
.

Definition cmc_stmt_temps_return_wit_5 := 
(
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_stmt) (result: Z) (retval: Z) (PreH1 : (cm_rep_stmt_temps_safe x )) (PreH2 : (retval = (cm_stemps (x)))) (PreH3 : (0 <= (cm_stemps (x)))) (PreH4 : ((cm_stemps (x)) <= INT_MAX)) (PreH5 : (stmt_pre <> 0)) (PreH6 : (cm_rep_stmt_temps_safe s )) (PreH7 : (s = (CMBlockS (x)))) (PreH8 : (result = 0)) (PreH9 : (cm_rep_stmt_temps_safe x )) (PreH10 : (pe = 0)) (PreH11 : (pa <> 0)) (PreH12 : (pb = 0)) ,
  (cm_stmt_rep pa x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (retval = (cm_stemps (s))) ” 
  &&  “ (0 <= (cm_stemps (s))) ” 
  &&  “ ((cm_stemps (s)) <= INT_MAX) ”
  &&  (cm_stmt_rep stmt_pre s )
) \/
(
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_stmt) (result: Z) (retval: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : (cm_rep_stmt_temps_safe x )) (PreH6 : (retval = (cm_stemps (x)))) (PreH7 : (0 <= (cm_stemps (x)))) (PreH8 : ((cm_stemps (x)) <= INT_MAX)) (PreH9 : (stmt_pre <> 0)) (PreH10 : (cm_rep_stmt_temps_safe s )) (PreH11 : (s = (CMBlockS (x)))) (PreH12 : (result = 0)) (PreH13 : (cm_rep_stmt_temps_safe x )) (PreH14 : (pe = 0)) (PreH15 : (pa <> 0)) (PreH16 : (pb = 0)) ,
  (cm_stmt_rep pa x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  “ ((cm_stemps (s)) <= INT_MAX) ” 
  &&  “ (0 <= (cm_stemps (s))) ” 
  &&  “ (retval = (cm_stemps (s))) ”
  &&  (cm_stmt_rep stmt_pre s )
).

Definition cmc_stmt_temps_return_wit_5_split_goal_1 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_stmt) (result: Z) (retval: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : (cm_rep_stmt_temps_safe x )) (PreH6 : (retval = (cm_stemps (x)))) (PreH7 : (0 <= (cm_stemps (x)))) (PreH8 : ((cm_stemps (x)) <= INT_MAX)) (PreH9 : (stmt_pre <> 0)) (PreH10 : (cm_rep_stmt_temps_safe s )) (PreH11 : (s = (CMBlockS (x)))) (PreH12 : (result = 0)) (PreH13 : (cm_rep_stmt_temps_safe x )) (PreH14 : (pe = 0)) (PreH15 : (pa <> 0)) (PreH16 : (pb = 0)) ,
  (cm_stmt_rep pa x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  “ ((cm_stemps (s)) <= INT_MAX) ”
.

Definition cmc_stmt_temps_return_wit_5_split_goal_2 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_stmt) (result: Z) (retval: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : (cm_rep_stmt_temps_safe x )) (PreH6 : (retval = (cm_stemps (x)))) (PreH7 : (0 <= (cm_stemps (x)))) (PreH8 : ((cm_stemps (x)) <= INT_MAX)) (PreH9 : (stmt_pre <> 0)) (PreH10 : (cm_rep_stmt_temps_safe s )) (PreH11 : (s = (CMBlockS (x)))) (PreH12 : (result = 0)) (PreH13 : (cm_rep_stmt_temps_safe x )) (PreH14 : (pe = 0)) (PreH15 : (pa <> 0)) (PreH16 : (pb = 0)) ,
  (cm_stmt_rep pa x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  “ (0 <= (cm_stemps (s))) ”
.

Definition cmc_stmt_temps_return_wit_5_split_goal_3 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_stmt) (result: Z) (retval: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : (cm_rep_stmt_temps_safe x )) (PreH6 : (retval = (cm_stemps (x)))) (PreH7 : (0 <= (cm_stemps (x)))) (PreH8 : ((cm_stemps (x)) <= INT_MAX)) (PreH9 : (stmt_pre <> 0)) (PreH10 : (cm_rep_stmt_temps_safe s )) (PreH11 : (s = (CMBlockS (x)))) (PreH12 : (result = 0)) (PreH13 : (cm_rep_stmt_temps_safe x )) (PreH14 : (pe = 0)) (PreH15 : (pa <> 0)) (PreH16 : (pb = 0)) ,
  (cm_stmt_rep pa x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  “ (retval = (cm_stemps (s))) ”
.

Definition cmc_stmt_temps_return_wit_5_split_goal_spatial := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_stmt) (result: Z) (retval: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : (cm_rep_stmt_temps_safe x )) (PreH6 : (retval = (cm_stemps (x)))) (PreH7 : (0 <= (cm_stemps (x)))) (PreH8 : ((cm_stemps (x)) <= INT_MAX)) (PreH9 : (stmt_pre <> 0)) (PreH10 : (cm_rep_stmt_temps_safe s )) (PreH11 : (s = (CMBlockS (x)))) (PreH12 : (result = 0)) (PreH13 : (cm_rep_stmt_temps_safe x )) (PreH14 : (pe = 0)) (PreH15 : (pa <> 0)) (PreH16 : (pb = 0)) ,
  (cm_stmt_rep pa x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  (cm_stmt_rep stmt_pre s )
.

Definition cmc_stmt_temps_return_wit_6 := 
(
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (y: cm_stmt) (z: cm_stmt) (result: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (PreH1 : (retval = (cm_imax (retval_2) (retval_5)))) (PreH2 : (retval_5 = (cm_imax (retval_3) (retval_4)))) (PreH3 : (cm_rep_stmt_temps_safe z )) (PreH4 : (retval_4 = (cm_stemps (z)))) (PreH5 : (0 <= (cm_stemps (z)))) (PreH6 : ((cm_stemps (z)) <= INT_MAX)) (PreH7 : (cm_rep_stmt_temps_safe y )) (PreH8 : (retval_3 = (cm_stemps (y)))) (PreH9 : (0 <= (cm_stemps (y)))) (PreH10 : ((cm_stemps (y)) <= INT_MAX)) (PreH11 : (cm_rep_expr_temps_safe x )) (PreH12 : (retval_2 = (cm_tright ((cm_expr_tpair (x)))))) (PreH13 : (stmt_pre <> 0)) (PreH14 : (cm_rep_stmt_temps_safe s )) (PreH15 : (s = (CMIfS (x) (y) (z)))) (PreH16 : (result = 0)) (PreH17 : (cm_rep_expr_temps_safe x )) (PreH18 : (cm_rep_stmt_temps_safe y )) (PreH19 : (cm_rep_stmt_temps_safe z )) ,
  (cm_stmt_rep pb z )
  **  (cm_stmt_rep pa y )
  **  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (retval = (cm_stemps (s))) ” 
  &&  “ (0 <= (cm_stemps (s))) ” 
  &&  “ ((cm_stemps (s)) <= INT_MAX) ”
  &&  (cm_stmt_rep stmt_pre s )
) \/
(
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (y: cm_stmt) (z: cm_stmt) (result: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : (retval = (cm_imax (retval_2) (retval_5)))) (PreH6 : (retval_5 = (cm_imax (retval_3) (retval_4)))) (PreH7 : (cm_rep_stmt_temps_safe z )) (PreH8 : (retval_4 = (cm_stemps (z)))) (PreH9 : (0 <= (cm_stemps (z)))) (PreH10 : ((cm_stemps (z)) <= INT_MAX)) (PreH11 : (cm_rep_stmt_temps_safe y )) (PreH12 : (retval_3 = (cm_stemps (y)))) (PreH13 : (0 <= (cm_stemps (y)))) (PreH14 : ((cm_stemps (y)) <= INT_MAX)) (PreH15 : (cm_rep_expr_temps_safe x )) (PreH16 : (retval_2 = (cm_tright ((cm_expr_tpair (x)))))) (PreH17 : (stmt_pre <> 0)) (PreH18 : (cm_rep_stmt_temps_safe s )) (PreH19 : (s = (CMIfS (x) (y) (z)))) (PreH20 : (result = 0)) (PreH21 : (cm_rep_expr_temps_safe x )) (PreH22 : (cm_rep_stmt_temps_safe y )) (PreH23 : (cm_rep_stmt_temps_safe z )) ,
  (cm_stmt_rep pb z )
  **  (cm_stmt_rep pa y )
  **  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  “ ((cm_stemps (s)) <= INT_MAX) ” 
  &&  “ (0 <= (cm_stemps (s))) ” 
  &&  “ (retval = (cm_stemps (s))) ”
  &&  (cm_stmt_rep stmt_pre s )
).

Definition cmc_stmt_temps_return_wit_6_split_goal_1 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (y: cm_stmt) (z: cm_stmt) (result: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : (retval = (cm_imax (retval_2) (retval_5)))) (PreH6 : (retval_5 = (cm_imax (retval_3) (retval_4)))) (PreH7 : (cm_rep_stmt_temps_safe z )) (PreH8 : (retval_4 = (cm_stemps (z)))) (PreH9 : (0 <= (cm_stemps (z)))) (PreH10 : ((cm_stemps (z)) <= INT_MAX)) (PreH11 : (cm_rep_stmt_temps_safe y )) (PreH12 : (retval_3 = (cm_stemps (y)))) (PreH13 : (0 <= (cm_stemps (y)))) (PreH14 : ((cm_stemps (y)) <= INT_MAX)) (PreH15 : (cm_rep_expr_temps_safe x )) (PreH16 : (retval_2 = (cm_tright ((cm_expr_tpair (x)))))) (PreH17 : (stmt_pre <> 0)) (PreH18 : (cm_rep_stmt_temps_safe s )) (PreH19 : (s = (CMIfS (x) (y) (z)))) (PreH20 : (result = 0)) (PreH21 : (cm_rep_expr_temps_safe x )) (PreH22 : (cm_rep_stmt_temps_safe y )) (PreH23 : (cm_rep_stmt_temps_safe z )) ,
  (cm_stmt_rep pb z )
  **  (cm_stmt_rep pa y )
  **  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  “ ((cm_stemps (s)) <= INT_MAX) ”
.

Definition cmc_stmt_temps_return_wit_6_split_goal_2 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (y: cm_stmt) (z: cm_stmt) (result: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : (retval = (cm_imax (retval_2) (retval_5)))) (PreH6 : (retval_5 = (cm_imax (retval_3) (retval_4)))) (PreH7 : (cm_rep_stmt_temps_safe z )) (PreH8 : (retval_4 = (cm_stemps (z)))) (PreH9 : (0 <= (cm_stemps (z)))) (PreH10 : ((cm_stemps (z)) <= INT_MAX)) (PreH11 : (cm_rep_stmt_temps_safe y )) (PreH12 : (retval_3 = (cm_stemps (y)))) (PreH13 : (0 <= (cm_stemps (y)))) (PreH14 : ((cm_stemps (y)) <= INT_MAX)) (PreH15 : (cm_rep_expr_temps_safe x )) (PreH16 : (retval_2 = (cm_tright ((cm_expr_tpair (x)))))) (PreH17 : (stmt_pre <> 0)) (PreH18 : (cm_rep_stmt_temps_safe s )) (PreH19 : (s = (CMIfS (x) (y) (z)))) (PreH20 : (result = 0)) (PreH21 : (cm_rep_expr_temps_safe x )) (PreH22 : (cm_rep_stmt_temps_safe y )) (PreH23 : (cm_rep_stmt_temps_safe z )) ,
  (cm_stmt_rep pb z )
  **  (cm_stmt_rep pa y )
  **  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  “ (0 <= (cm_stemps (s))) ”
.

Definition cmc_stmt_temps_return_wit_6_split_goal_3 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (y: cm_stmt) (z: cm_stmt) (result: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : (retval = (cm_imax (retval_2) (retval_5)))) (PreH6 : (retval_5 = (cm_imax (retval_3) (retval_4)))) (PreH7 : (cm_rep_stmt_temps_safe z )) (PreH8 : (retval_4 = (cm_stemps (z)))) (PreH9 : (0 <= (cm_stemps (z)))) (PreH10 : ((cm_stemps (z)) <= INT_MAX)) (PreH11 : (cm_rep_stmt_temps_safe y )) (PreH12 : (retval_3 = (cm_stemps (y)))) (PreH13 : (0 <= (cm_stemps (y)))) (PreH14 : ((cm_stemps (y)) <= INT_MAX)) (PreH15 : (cm_rep_expr_temps_safe x )) (PreH16 : (retval_2 = (cm_tright ((cm_expr_tpair (x)))))) (PreH17 : (stmt_pre <> 0)) (PreH18 : (cm_rep_stmt_temps_safe s )) (PreH19 : (s = (CMIfS (x) (y) (z)))) (PreH20 : (result = 0)) (PreH21 : (cm_rep_expr_temps_safe x )) (PreH22 : (cm_rep_stmt_temps_safe y )) (PreH23 : (cm_rep_stmt_temps_safe z )) ,
  (cm_stmt_rep pb z )
  **  (cm_stmt_rep pa y )
  **  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  “ (retval = (cm_stemps (s))) ”
.

Definition cmc_stmt_temps_return_wit_6_split_goal_spatial := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (y: cm_stmt) (z: cm_stmt) (result: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : (retval = (cm_imax (retval_2) (retval_5)))) (PreH6 : (retval_5 = (cm_imax (retval_3) (retval_4)))) (PreH7 : (cm_rep_stmt_temps_safe z )) (PreH8 : (retval_4 = (cm_stemps (z)))) (PreH9 : (0 <= (cm_stemps (z)))) (PreH10 : ((cm_stemps (z)) <= INT_MAX)) (PreH11 : (cm_rep_stmt_temps_safe y )) (PreH12 : (retval_3 = (cm_stemps (y)))) (PreH13 : (0 <= (cm_stemps (y)))) (PreH14 : ((cm_stemps (y)) <= INT_MAX)) (PreH15 : (cm_rep_expr_temps_safe x )) (PreH16 : (retval_2 = (cm_tright ((cm_expr_tpair (x)))))) (PreH17 : (stmt_pre <> 0)) (PreH18 : (cm_rep_stmt_temps_safe s )) (PreH19 : (s = (CMIfS (x) (y) (z)))) (PreH20 : (result = 0)) (PreH21 : (cm_rep_expr_temps_safe x )) (PreH22 : (cm_rep_stmt_temps_safe y )) (PreH23 : (cm_rep_stmt_temps_safe z )) ,
  (cm_stmt_rep pb z )
  **  (cm_stmt_rep pa y )
  **  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  (cm_stmt_rep stmt_pre s )
.

Definition cmc_stmt_temps_return_wit_7 := 
(
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (y: cm_stmt) (result: Z) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (retval = (cm_imax (retval_2) (retval_3)))) (PreH2 : (cm_rep_stmt_temps_safe y )) (PreH3 : (retval_3 = (cm_stemps (y)))) (PreH4 : (0 <= (cm_stemps (y)))) (PreH5 : ((cm_stemps (y)) <= INT_MAX)) (PreH6 : (cm_rep_expr_temps_safe x )) (PreH7 : (retval_2 = (cm_tright ((cm_expr_tpair (x)))))) (PreH8 : (stmt_pre <> 0)) (PreH9 : (cm_rep_stmt_temps_safe s )) (PreH10 : (s = (CMWhileS (x) (y)))) (PreH11 : (result = 0)) (PreH12 : (cm_rep_expr_temps_safe x )) (PreH13 : (cm_rep_stmt_temps_safe y )) (PreH14 : (pe <> 0)) (PreH15 : (pa <> 0)) (PreH16 : (pb = 0)) ,
  (cm_stmt_rep pa y )
  **  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (retval = (cm_stemps (s))) ” 
  &&  “ (0 <= (cm_stemps (s))) ” 
  &&  “ ((cm_stemps (s)) <= INT_MAX) ”
  &&  (cm_stmt_rep stmt_pre s )
) \/
(
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (y: cm_stmt) (result: Z) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : (retval = (cm_imax (retval_2) (retval_3)))) (PreH6 : (cm_rep_stmt_temps_safe y )) (PreH7 : (retval_3 = (cm_stemps (y)))) (PreH8 : (0 <= (cm_stemps (y)))) (PreH9 : ((cm_stemps (y)) <= INT_MAX)) (PreH10 : (cm_rep_expr_temps_safe x )) (PreH11 : (retval_2 = (cm_tright ((cm_expr_tpair (x)))))) (PreH12 : (stmt_pre <> 0)) (PreH13 : (cm_rep_stmt_temps_safe s )) (PreH14 : (s = (CMWhileS (x) (y)))) (PreH15 : (result = 0)) (PreH16 : (cm_rep_expr_temps_safe x )) (PreH17 : (cm_rep_stmt_temps_safe y )) (PreH18 : (pe <> 0)) (PreH19 : (pa <> 0)) (PreH20 : (pb = 0)) ,
  (cm_stmt_rep pa y )
  **  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  “ ((cm_stemps (s)) <= INT_MAX) ” 
  &&  “ (0 <= (cm_stemps (s))) ” 
  &&  “ (retval = (cm_stemps (s))) ”
  &&  (cm_stmt_rep stmt_pre s )
).

Definition cmc_stmt_temps_return_wit_7_split_goal_1 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (y: cm_stmt) (result: Z) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : (retval = (cm_imax (retval_2) (retval_3)))) (PreH6 : (cm_rep_stmt_temps_safe y )) (PreH7 : (retval_3 = (cm_stemps (y)))) (PreH8 : (0 <= (cm_stemps (y)))) (PreH9 : ((cm_stemps (y)) <= INT_MAX)) (PreH10 : (cm_rep_expr_temps_safe x )) (PreH11 : (retval_2 = (cm_tright ((cm_expr_tpair (x)))))) (PreH12 : (stmt_pre <> 0)) (PreH13 : (cm_rep_stmt_temps_safe s )) (PreH14 : (s = (CMWhileS (x) (y)))) (PreH15 : (result = 0)) (PreH16 : (cm_rep_expr_temps_safe x )) (PreH17 : (cm_rep_stmt_temps_safe y )) (PreH18 : (pe <> 0)) (PreH19 : (pa <> 0)) (PreH20 : (pb = 0)) ,
  (cm_stmt_rep pa y )
  **  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  “ ((cm_stemps (s)) <= INT_MAX) ”
.

Definition cmc_stmt_temps_return_wit_7_split_goal_2 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (y: cm_stmt) (result: Z) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : (retval = (cm_imax (retval_2) (retval_3)))) (PreH6 : (cm_rep_stmt_temps_safe y )) (PreH7 : (retval_3 = (cm_stemps (y)))) (PreH8 : (0 <= (cm_stemps (y)))) (PreH9 : ((cm_stemps (y)) <= INT_MAX)) (PreH10 : (cm_rep_expr_temps_safe x )) (PreH11 : (retval_2 = (cm_tright ((cm_expr_tpair (x)))))) (PreH12 : (stmt_pre <> 0)) (PreH13 : (cm_rep_stmt_temps_safe s )) (PreH14 : (s = (CMWhileS (x) (y)))) (PreH15 : (result = 0)) (PreH16 : (cm_rep_expr_temps_safe x )) (PreH17 : (cm_rep_stmt_temps_safe y )) (PreH18 : (pe <> 0)) (PreH19 : (pa <> 0)) (PreH20 : (pb = 0)) ,
  (cm_stmt_rep pa y )
  **  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  “ (0 <= (cm_stemps (s))) ”
.

Definition cmc_stmt_temps_return_wit_7_split_goal_3 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (y: cm_stmt) (result: Z) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : (retval = (cm_imax (retval_2) (retval_3)))) (PreH6 : (cm_rep_stmt_temps_safe y )) (PreH7 : (retval_3 = (cm_stemps (y)))) (PreH8 : (0 <= (cm_stemps (y)))) (PreH9 : ((cm_stemps (y)) <= INT_MAX)) (PreH10 : (cm_rep_expr_temps_safe x )) (PreH11 : (retval_2 = (cm_tright ((cm_expr_tpair (x)))))) (PreH12 : (stmt_pre <> 0)) (PreH13 : (cm_rep_stmt_temps_safe s )) (PreH14 : (s = (CMWhileS (x) (y)))) (PreH15 : (result = 0)) (PreH16 : (cm_rep_expr_temps_safe x )) (PreH17 : (cm_rep_stmt_temps_safe y )) (PreH18 : (pe <> 0)) (PreH19 : (pa <> 0)) (PreH20 : (pb = 0)) ,
  (cm_stmt_rep pa y )
  **  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  “ (retval = (cm_stemps (s))) ”
.

Definition cmc_stmt_temps_return_wit_7_split_goal_spatial := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (y: cm_stmt) (result: Z) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : (retval = (cm_imax (retval_2) (retval_3)))) (PreH6 : (cm_rep_stmt_temps_safe y )) (PreH7 : (retval_3 = (cm_stemps (y)))) (PreH8 : (0 <= (cm_stemps (y)))) (PreH9 : ((cm_stemps (y)) <= INT_MAX)) (PreH10 : (cm_rep_expr_temps_safe x )) (PreH11 : (retval_2 = (cm_tright ((cm_expr_tpair (x)))))) (PreH12 : (stmt_pre <> 0)) (PreH13 : (cm_rep_stmt_temps_safe s )) (PreH14 : (s = (CMWhileS (x) (y)))) (PreH15 : (result = 0)) (PreH16 : (cm_rep_expr_temps_safe x )) (PreH17 : (cm_rep_stmt_temps_safe y )) (PreH18 : (pe <> 0)) (PreH19 : (pa <> 0)) (PreH20 : (pb = 0)) ,
  (cm_stmt_rep pa y )
  **  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  (cm_stmt_rep stmt_pre s )
.

Definition cmc_stmt_temps_return_wit_8 := 
(
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_kind (s)) = 0)) (PreH2 : ((cm_rep_stmt_kind (s)) <> 7)) (PreH3 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH4 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH5 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH8 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH9 : (stmt_pre <> 0)) (PreH10 : (cm_rep_stmt_temps_safe s )) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (0 = (cm_stemps (s))) ” 
  &&  “ (0 <= (cm_stemps (s))) ” 
  &&  “ ((cm_stemps (s)) <= INT_MAX) ”
  &&  (cm_stmt_rep stmt_pre s )
) \/
(
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : ((cm_rep_stmt_kind (s)) = 0)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 7)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH8 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH9 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH10 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH11 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH12 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH13 : (stmt_pre <> 0)) (PreH14 : (cm_rep_stmt_temps_safe s )) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ ((cm_stemps (s)) <= INT_MAX) ” 
  &&  “ (0 <= (cm_stemps (s))) ” 
  &&  “ (0 = (cm_stemps (s))) ”
  &&  (cm_stmt_rep stmt_pre s )
).

Definition cmc_stmt_temps_return_wit_8_split_goal_1 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : ((cm_rep_stmt_kind (s)) = 0)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 7)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH8 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH9 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH10 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH11 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH12 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH13 : (stmt_pre <> 0)) (PreH14 : (cm_rep_stmt_temps_safe s )) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ ((cm_stemps (s)) <= INT_MAX) ”
.

Definition cmc_stmt_temps_return_wit_8_split_goal_2 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : ((cm_rep_stmt_kind (s)) = 0)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 7)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH8 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH9 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH10 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH11 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH12 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH13 : (stmt_pre <> 0)) (PreH14 : (cm_rep_stmt_temps_safe s )) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ (0 <= (cm_stemps (s))) ”
.

Definition cmc_stmt_temps_return_wit_8_split_goal_3 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : ((cm_rep_stmt_kind (s)) = 0)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 7)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH8 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH9 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH10 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH11 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH12 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH13 : (stmt_pre <> 0)) (PreH14 : (cm_rep_stmt_temps_safe s )) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ (0 = (cm_stemps (s))) ”
.

Definition cmc_stmt_temps_return_wit_8_split_goal_spatial := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : ((cm_rep_stmt_kind (s)) = 0)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 7)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH8 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH9 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH10 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH11 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH12 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH13 : (stmt_pre <> 0)) (PreH14 : (cm_rep_stmt_temps_safe s )) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  (cm_stmt_rep stmt_pre s )
.

Definition cmc_stmt_temps_return_wit_9 := 
(
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_kind (s)) = 2)) (PreH2 : ((cm_rep_stmt_kind (s)) <> 0)) (PreH3 : ((cm_rep_stmt_kind (s)) <> 7)) (PreH4 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH5 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH8 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH9 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH10 : (stmt_pre <> 0)) (PreH11 : (cm_rep_stmt_temps_safe s )) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (0 = (cm_stemps (s))) ” 
  &&  “ (0 <= (cm_stemps (s))) ” 
  &&  “ ((cm_stemps (s)) <= INT_MAX) ”
  &&  (cm_stmt_rep stmt_pre s )
) \/
(
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : ((cm_rep_stmt_kind (s)) = 2)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 0)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 7)) (PreH8 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH9 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH10 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH11 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH12 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH13 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH14 : (stmt_pre <> 0)) (PreH15 : (cm_rep_stmt_temps_safe s )) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ ((cm_stemps (s)) <= INT_MAX) ” 
  &&  “ (0 <= (cm_stemps (s))) ” 
  &&  “ (0 = (cm_stemps (s))) ”
  &&  (cm_stmt_rep stmt_pre s )
).

Definition cmc_stmt_temps_return_wit_9_split_goal_1 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : ((cm_rep_stmt_kind (s)) = 2)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 0)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 7)) (PreH8 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH9 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH10 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH11 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH12 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH13 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH14 : (stmt_pre <> 0)) (PreH15 : (cm_rep_stmt_temps_safe s )) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ ((cm_stemps (s)) <= INT_MAX) ”
.

Definition cmc_stmt_temps_return_wit_9_split_goal_2 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : ((cm_rep_stmt_kind (s)) = 2)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 0)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 7)) (PreH8 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH9 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH10 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH11 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH12 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH13 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH14 : (stmt_pre <> 0)) (PreH15 : (cm_rep_stmt_temps_safe s )) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ (0 <= (cm_stemps (s))) ”
.

Definition cmc_stmt_temps_return_wit_9_split_goal_3 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : ((cm_rep_stmt_kind (s)) = 2)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 0)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 7)) (PreH8 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH9 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH10 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH11 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH12 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH13 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH14 : (stmt_pre <> 0)) (PreH15 : (cm_rep_stmt_temps_safe s )) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ (0 = (cm_stemps (s))) ”
.

Definition cmc_stmt_temps_return_wit_9_split_goal_spatial := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : ((cm_rep_stmt_kind (s)) = 2)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 0)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 7)) (PreH8 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH9 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH10 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH11 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH12 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH13 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH14 : (stmt_pre <> 0)) (PreH15 : (cm_rep_stmt_temps_safe s )) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  (cm_stmt_rep stmt_pre s )
.

Definition cmc_stmt_temps_return_wit_10 := 
(
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_kind (s)) = 8)) (PreH2 : ((cm_rep_stmt_kind (s)) <> 2)) (PreH3 : ((cm_rep_stmt_kind (s)) <> 0)) (PreH4 : ((cm_rep_stmt_kind (s)) <> 7)) (PreH5 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH8 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH9 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH10 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH11 : (stmt_pre <> 0)) (PreH12 : (cm_rep_stmt_temps_safe s )) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (0 = (cm_stemps (s))) ” 
  &&  “ (0 <= (cm_stemps (s))) ” 
  &&  “ ((cm_stemps (s)) <= INT_MAX) ”
  &&  (cm_stmt_rep stmt_pre s )
) \/
(
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : ((cm_rep_stmt_kind (s)) = 8)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 2)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 0)) (PreH8 : ((cm_rep_stmt_kind (s)) <> 7)) (PreH9 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH10 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH11 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH12 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH13 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH14 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH15 : (stmt_pre <> 0)) (PreH16 : (cm_rep_stmt_temps_safe s )) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ ((cm_stemps (s)) <= INT_MAX) ” 
  &&  “ (0 <= (cm_stemps (s))) ” 
  &&  “ (0 = (cm_stemps (s))) ”
  &&  (cm_stmt_rep stmt_pre s )
).

Definition cmc_stmt_temps_return_wit_10_split_goal_1 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : ((cm_rep_stmt_kind (s)) = 8)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 2)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 0)) (PreH8 : ((cm_rep_stmt_kind (s)) <> 7)) (PreH9 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH10 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH11 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH12 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH13 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH14 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH15 : (stmt_pre <> 0)) (PreH16 : (cm_rep_stmt_temps_safe s )) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ ((cm_stemps (s)) <= INT_MAX) ”
.

Definition cmc_stmt_temps_return_wit_10_split_goal_2 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : ((cm_rep_stmt_kind (s)) = 8)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 2)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 0)) (PreH8 : ((cm_rep_stmt_kind (s)) <> 7)) (PreH9 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH10 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH11 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH12 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH13 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH14 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH15 : (stmt_pre <> 0)) (PreH16 : (cm_rep_stmt_temps_safe s )) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ (0 <= (cm_stemps (s))) ”
.

Definition cmc_stmt_temps_return_wit_10_split_goal_3 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : ((cm_rep_stmt_kind (s)) = 8)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 2)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 0)) (PreH8 : ((cm_rep_stmt_kind (s)) <> 7)) (PreH9 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH10 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH11 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH12 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH13 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH14 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH15 : (stmt_pre <> 0)) (PreH16 : (cm_rep_stmt_temps_safe s )) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ (0 = (cm_stemps (s))) ”
.

Definition cmc_stmt_temps_return_wit_10_split_goal_spatial := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : ((cm_rep_stmt_kind (s)) = 8)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 2)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 0)) (PreH8 : ((cm_rep_stmt_kind (s)) <> 7)) (PreH9 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH10 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH11 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH12 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH13 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH14 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH15 : (stmt_pre <> 0)) (PreH16 : (cm_rep_stmt_temps_safe s )) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  (cm_stmt_rep stmt_pre s )
.

Definition cmc_stmt_temps_return_wit_11 := 
(
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_kind (s)) = 9)) (PreH2 : ((cm_rep_stmt_kind (s)) <> 8)) (PreH3 : ((cm_rep_stmt_kind (s)) <> 2)) (PreH4 : ((cm_rep_stmt_kind (s)) <> 0)) (PreH5 : ((cm_rep_stmt_kind (s)) <> 7)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH8 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH9 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH10 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH11 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH12 : (stmt_pre <> 0)) (PreH13 : (cm_rep_stmt_temps_safe s )) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (0 = (cm_stemps (s))) ” 
  &&  “ (0 <= (cm_stemps (s))) ” 
  &&  “ ((cm_stemps (s)) <= INT_MAX) ”
  &&  (cm_stmt_rep stmt_pre s )
) \/
(
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : ((cm_rep_stmt_kind (s)) = 9)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 8)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 2)) (PreH8 : ((cm_rep_stmt_kind (s)) <> 0)) (PreH9 : ((cm_rep_stmt_kind (s)) <> 7)) (PreH10 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH11 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH12 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH13 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH14 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH15 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH16 : (stmt_pre <> 0)) (PreH17 : (cm_rep_stmt_temps_safe s )) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ ((cm_stemps (s)) <= INT_MAX) ” 
  &&  “ (0 <= (cm_stemps (s))) ” 
  &&  “ (0 = (cm_stemps (s))) ”
  &&  (cm_stmt_rep stmt_pre s )
).

Definition cmc_stmt_temps_return_wit_11_split_goal_1 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : ((cm_rep_stmt_kind (s)) = 9)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 8)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 2)) (PreH8 : ((cm_rep_stmt_kind (s)) <> 0)) (PreH9 : ((cm_rep_stmt_kind (s)) <> 7)) (PreH10 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH11 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH12 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH13 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH14 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH15 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH16 : (stmt_pre <> 0)) (PreH17 : (cm_rep_stmt_temps_safe s )) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ ((cm_stemps (s)) <= INT_MAX) ”
.

Definition cmc_stmt_temps_return_wit_11_split_goal_2 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : ((cm_rep_stmt_kind (s)) = 9)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 8)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 2)) (PreH8 : ((cm_rep_stmt_kind (s)) <> 0)) (PreH9 : ((cm_rep_stmt_kind (s)) <> 7)) (PreH10 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH11 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH12 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH13 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH14 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH15 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH16 : (stmt_pre <> 0)) (PreH17 : (cm_rep_stmt_temps_safe s )) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ (0 <= (cm_stemps (s))) ”
.

Definition cmc_stmt_temps_return_wit_11_split_goal_3 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : ((cm_rep_stmt_kind (s)) = 9)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 8)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 2)) (PreH8 : ((cm_rep_stmt_kind (s)) <> 0)) (PreH9 : ((cm_rep_stmt_kind (s)) <> 7)) (PreH10 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH11 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH12 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH13 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH14 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH15 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH16 : (stmt_pre <> 0)) (PreH17 : (cm_rep_stmt_temps_safe s )) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ (0 = (cm_stemps (s))) ”
.

Definition cmc_stmt_temps_return_wit_11_split_goal_spatial := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : ((cm_rep_stmt_kind (s)) = 9)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 8)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 2)) (PreH8 : ((cm_rep_stmt_kind (s)) <> 0)) (PreH9 : ((cm_rep_stmt_kind (s)) <> 7)) (PreH10 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH11 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH12 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH13 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH14 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH15 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH16 : (stmt_pre <> 0)) (PreH17 : (cm_rep_stmt_temps_safe s )) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  (cm_stmt_rep stmt_pre s )
.

Definition cmc_stmt_temps_return_wit_12 := 
(
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_kind (s)) <> 9)) (PreH2 : ((cm_rep_stmt_kind (s)) <> 8)) (PreH3 : ((cm_rep_stmt_kind (s)) <> 2)) (PreH4 : ((cm_rep_stmt_kind (s)) <> 0)) (PreH5 : ((cm_rep_stmt_kind (s)) <> 7)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH8 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH9 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH10 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH11 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH12 : (stmt_pre <> 0)) (PreH13 : (cm_rep_stmt_temps_safe s )) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (0 = (cm_stemps (s))) ” 
  &&  “ (0 <= (cm_stemps (s))) ” 
  &&  “ ((cm_stemps (s)) <= INT_MAX) ”
  &&  (cm_stmt_rep stmt_pre s )
) \/
(
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : ((cm_rep_stmt_kind (s)) <> 9)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 8)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 2)) (PreH8 : ((cm_rep_stmt_kind (s)) <> 0)) (PreH9 : ((cm_rep_stmt_kind (s)) <> 7)) (PreH10 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH11 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH12 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH13 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH14 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH15 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH16 : (stmt_pre <> 0)) (PreH17 : (cm_rep_stmt_temps_safe s )) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ ((cm_stemps (s)) <= INT_MAX) ” 
  &&  “ (0 <= (cm_stemps (s))) ” 
  &&  “ (0 = (cm_stemps (s))) ”
  &&  (cm_stmt_rep stmt_pre s )
).

Definition cmc_stmt_temps_return_wit_12_split_goal_1 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : ((cm_rep_stmt_kind (s)) <> 9)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 8)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 2)) (PreH8 : ((cm_rep_stmt_kind (s)) <> 0)) (PreH9 : ((cm_rep_stmt_kind (s)) <> 7)) (PreH10 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH11 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH12 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH13 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH14 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH15 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH16 : (stmt_pre <> 0)) (PreH17 : (cm_rep_stmt_temps_safe s )) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ ((cm_stemps (s)) <= INT_MAX) ”
.

Definition cmc_stmt_temps_return_wit_12_split_goal_2 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : ((cm_rep_stmt_kind (s)) <> 9)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 8)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 2)) (PreH8 : ((cm_rep_stmt_kind (s)) <> 0)) (PreH9 : ((cm_rep_stmt_kind (s)) <> 7)) (PreH10 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH11 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH12 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH13 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH14 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH15 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH16 : (stmt_pre <> 0)) (PreH17 : (cm_rep_stmt_temps_safe s )) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ (0 <= (cm_stemps (s))) ”
.

Definition cmc_stmt_temps_return_wit_12_split_goal_3 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : ((cm_rep_stmt_kind (s)) <> 9)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 8)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 2)) (PreH8 : ((cm_rep_stmt_kind (s)) <> 0)) (PreH9 : ((cm_rep_stmt_kind (s)) <> 7)) (PreH10 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH11 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH12 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH13 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH14 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH15 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH16 : (stmt_pre <> 0)) (PreH17 : (cm_rep_stmt_temps_safe s )) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  “ (0 = (cm_stemps (s))) ”
.

Definition cmc_stmt_temps_return_wit_12_split_goal_spatial := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (PreH1 : ((cm_rep_stmt_slot (s)) <= INT_MAX)) (PreH2 : ((cm_rep_stmt_kind (s)) <= INT_MAX)) (PreH3 : ((cm_rep_stmt_slot (s)) >= INT_MIN)) (PreH4 : ((cm_rep_stmt_kind (s)) >= INT_MIN)) (PreH5 : ((cm_rep_stmt_kind (s)) <> 9)) (PreH6 : ((cm_rep_stmt_kind (s)) <> 8)) (PreH7 : ((cm_rep_stmt_kind (s)) <> 2)) (PreH8 : ((cm_rep_stmt_kind (s)) <> 0)) (PreH9 : ((cm_rep_stmt_kind (s)) <> 7)) (PreH10 : ((cm_rep_stmt_kind (s)) <> 6)) (PreH11 : ((cm_rep_stmt_kind (s)) <> 5)) (PreH12 : ((cm_rep_stmt_kind (s)) <> 4)) (PreH13 : ((cm_rep_stmt_kind (s)) <> 10)) (PreH14 : ((cm_rep_stmt_kind (s)) <> 3)) (PreH15 : ((cm_rep_stmt_kind (s)) <> 1)) (PreH16 : (stmt_pre <> 0)) (PreH17 : (cm_rep_stmt_temps_safe s )) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_payload s pe pa pb )
|--
  (cm_stmt_rep stmt_pre s )
.

Definition cmc_stmt_temps_partial_solve_wit_1_pure := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (result: Z) (PreH1 : (stmt_pre <> 0)) (PreH2 : (cm_rep_stmt_temps_safe s )) (PreH3 : (s = (CMExprS (x)))) (PreH4 : (result = 0)) (PreH5 : (cm_rep_expr_temps_safe x )) (PreH6 : (pe <> 0)) (PreH7 : (pa = 0)) (PreH8 : (pb = 0)) ,
  ((( &( "stmt" ) )) # Ptr  |-> stmt_pre)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_expr_rep pe x )
|--
  “ (cm_rep_expr_temps_safe x ) ”
.

Definition cmc_stmt_temps_partial_solve_wit_1_aux := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (result: Z) (PreH1 : (stmt_pre <> 0)) (PreH2 : (cm_rep_stmt_temps_safe s )) (PreH3 : (s = (CMExprS (x)))) (PreH4 : (result = 0)) (PreH5 : (cm_rep_expr_temps_safe x )) (PreH6 : (pe <> 0)) (PreH7 : (pa = 0)) (PreH8 : (pb = 0)) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_expr_rep pe x )
|--
  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (stmt_pre <> 0) ” 
  &&  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (s = (CMExprS (x))) ” 
  &&  “ (result = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pa = 0) ” 
  &&  “ (pb = 0) ”
  &&  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
.

Definition cmc_stmt_temps_partial_solve_wit_1 := cmc_stmt_temps_partial_solve_wit_1_pure -> cmc_stmt_temps_partial_solve_wit_1_aux.

Definition cmc_stmt_temps_partial_solve_wit_2_pure := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (slotid: Z) (x: cm_expr) (result: Z) (PreH1 : (stmt_pre <> 0)) (PreH2 : (cm_rep_stmt_temps_safe s )) (PreH3 : (s = (CMInitS (slotid) (x)))) (PreH4 : (result = 0)) (PreH5 : (cm_rep_expr_temps_safe x )) (PreH6 : (pe <> 0)) (PreH7 : (pa = 0)) (PreH8 : (pb = 0)) ,
  ((( &( "stmt" ) )) # Ptr  |-> stmt_pre)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_expr_rep pe x )
|--
  “ (cm_rep_expr_temps_safe x ) ”
.

Definition cmc_stmt_temps_partial_solve_wit_2_aux := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (slotid: Z) (x: cm_expr) (result: Z) (PreH1 : (stmt_pre <> 0)) (PreH2 : (cm_rep_stmt_temps_safe s )) (PreH3 : (s = (CMInitS (slotid) (x)))) (PreH4 : (result = 0)) (PreH5 : (cm_rep_expr_temps_safe x )) (PreH6 : (pe <> 0)) (PreH7 : (pa = 0)) (PreH8 : (pb = 0)) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_expr_rep pe x )
|--
  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (stmt_pre <> 0) ” 
  &&  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (s = (CMInitS (slotid) (x))) ” 
  &&  “ (result = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pa = 0) ” 
  &&  “ (pb = 0) ”
  &&  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
.

Definition cmc_stmt_temps_partial_solve_wit_2 := cmc_stmt_temps_partial_solve_wit_2_pure -> cmc_stmt_temps_partial_solve_wit_2_aux.

Definition cmc_stmt_temps_partial_solve_wit_3_pure := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (result: Z) (PreH1 : (stmt_pre <> 0)) (PreH2 : (cm_rep_stmt_temps_safe s )) (PreH3 : (s = (CMReturnS (x)))) (PreH4 : (result = 0)) (PreH5 : (cm_rep_expr_temps_safe x )) (PreH6 : (pe <> 0)) (PreH7 : (pa = 0)) (PreH8 : (pb = 0)) ,
  ((( &( "stmt" ) )) # Ptr  |-> stmt_pre)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_expr_rep pe x )
|--
  “ (cm_rep_expr_temps_safe x ) ”
.

Definition cmc_stmt_temps_partial_solve_wit_3_aux := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (result: Z) (PreH1 : (stmt_pre <> 0)) (PreH2 : (cm_rep_stmt_temps_safe s )) (PreH3 : (s = (CMReturnS (x)))) (PreH4 : (result = 0)) (PreH5 : (cm_rep_expr_temps_safe x )) (PreH6 : (pe <> 0)) (PreH7 : (pa = 0)) (PreH8 : (pb = 0)) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_expr_rep pe x )
|--
  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (stmt_pre <> 0) ” 
  &&  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (s = (CMReturnS (x))) ” 
  &&  “ (result = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pa = 0) ” 
  &&  “ (pb = 0) ”
  &&  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
.

Definition cmc_stmt_temps_partial_solve_wit_3 := cmc_stmt_temps_partial_solve_wit_3_pure -> cmc_stmt_temps_partial_solve_wit_3_aux.

Definition cmc_stmt_temps_partial_solve_wit_4_pure := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_stmt) (y: cm_stmt) (result: Z) (PreH1 : (stmt_pre <> 0)) (PreH2 : (cm_rep_stmt_temps_safe s )) (PreH3 : (s = (CMSeqS (x) (y)))) (PreH4 : (result = 0)) (PreH5 : (cm_rep_stmt_temps_safe x )) (PreH6 : (cm_rep_stmt_temps_safe y )) (PreH7 : (pe = 0)) ,
  ((( &( "first_temps" ) )) # Int  |->_)
  **  ((( &( "stmt" ) )) # Ptr  |-> stmt_pre)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_rep pa x )
  **  (cm_stmt_rep pb y )
|--
  “ (cm_rep_stmt_temps_safe x ) ”
.

Definition cmc_stmt_temps_partial_solve_wit_4_aux := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_stmt) (y: cm_stmt) (result: Z) (PreH1 : (stmt_pre <> 0)) (PreH2 : (cm_rep_stmt_temps_safe s )) (PreH3 : (s = (CMSeqS (x) (y)))) (PreH4 : (result = 0)) (PreH5 : (cm_rep_stmt_temps_safe x )) (PreH6 : (cm_rep_stmt_temps_safe y )) (PreH7 : (pe = 0)) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_rep pa x )
  **  (cm_stmt_rep pb y )
|--
  “ (cm_rep_stmt_temps_safe x ) ” 
  &&  “ (stmt_pre <> 0) ” 
  &&  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (s = (CMSeqS (x) (y))) ” 
  &&  “ (result = 0) ” 
  &&  “ (cm_rep_stmt_temps_safe x ) ” 
  &&  “ (cm_rep_stmt_temps_safe y ) ” 
  &&  “ (pe = 0) ”
  &&  (cm_stmt_rep pa x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_rep pb y )
.

Definition cmc_stmt_temps_partial_solve_wit_4 := cmc_stmt_temps_partial_solve_wit_4_pure -> cmc_stmt_temps_partial_solve_wit_4_aux.

Definition cmc_stmt_temps_partial_solve_wit_5_pure := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_stmt) (y: cm_stmt) (result: Z) (retval: Z) (PreH1 : (cm_rep_stmt_temps_safe x )) (PreH2 : (retval = (cm_stemps (x)))) (PreH3 : (0 <= (cm_stemps (x)))) (PreH4 : ((cm_stemps (x)) <= INT_MAX)) (PreH5 : (stmt_pre <> 0)) (PreH6 : (cm_rep_stmt_temps_safe s )) (PreH7 : (s = (CMSeqS (x) (y)))) (PreH8 : (result = 0)) (PreH9 : (cm_rep_stmt_temps_safe x )) (PreH10 : (cm_rep_stmt_temps_safe y )) (PreH11 : (pe = 0)) ,
  ((( &( "second_temps" ) )) # Int  |->_)
  **  (cm_stmt_rep pa x )
  **  ((( &( "first_temps" ) )) # Int  |-> retval)
  **  ((( &( "stmt" ) )) # Ptr  |-> stmt_pre)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_rep pb y )
|--
  “ (cm_rep_stmt_temps_safe y ) ”
.

Definition cmc_stmt_temps_partial_solve_wit_5_aux := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_stmt) (y: cm_stmt) (result: Z) (retval: Z) (PreH1 : (cm_rep_stmt_temps_safe x )) (PreH2 : (retval = (cm_stemps (x)))) (PreH3 : (0 <= (cm_stemps (x)))) (PreH4 : ((cm_stemps (x)) <= INT_MAX)) (PreH5 : (stmt_pre <> 0)) (PreH6 : (cm_rep_stmt_temps_safe s )) (PreH7 : (s = (CMSeqS (x) (y)))) (PreH8 : (result = 0)) (PreH9 : (cm_rep_stmt_temps_safe x )) (PreH10 : (cm_rep_stmt_temps_safe y )) (PreH11 : (pe = 0)) ,
  (cm_stmt_rep pa x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_rep pb y )
|--
  “ (cm_rep_stmt_temps_safe y ) ” 
  &&  “ (cm_rep_stmt_temps_safe x ) ” 
  &&  “ (retval = (cm_stemps (x))) ” 
  &&  “ (0 <= (cm_stemps (x))) ” 
  &&  “ ((cm_stemps (x)) <= INT_MAX) ” 
  &&  “ (stmt_pre <> 0) ” 
  &&  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (s = (CMSeqS (x) (y))) ” 
  &&  “ (result = 0) ” 
  &&  “ (cm_rep_stmt_temps_safe x ) ” 
  &&  “ (cm_rep_stmt_temps_safe y ) ” 
  &&  “ (pe = 0) ”
  &&  (cm_stmt_rep pb y )
  **  (cm_stmt_rep pa x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
.

Definition cmc_stmt_temps_partial_solve_wit_5 := cmc_stmt_temps_partial_solve_wit_5_pure -> cmc_stmt_temps_partial_solve_wit_5_aux.

Definition cmc_stmt_temps_partial_solve_wit_6 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_stmt) (y: cm_stmt) (result: Z) (retval: Z) (retval_2: Z) (PreH1 : (cm_rep_stmt_temps_safe y )) (PreH2 : (retval_2 = (cm_stemps (y)))) (PreH3 : (0 <= (cm_stemps (y)))) (PreH4 : ((cm_stemps (y)) <= INT_MAX)) (PreH5 : (cm_rep_stmt_temps_safe x )) (PreH6 : (retval = (cm_stemps (x)))) (PreH7 : (0 <= (cm_stemps (x)))) (PreH8 : ((cm_stemps (x)) <= INT_MAX)) (PreH9 : (stmt_pre <> 0)) (PreH10 : (cm_rep_stmt_temps_safe s )) (PreH11 : (s = (CMSeqS (x) (y)))) (PreH12 : (result = 0)) (PreH13 : (cm_rep_stmt_temps_safe x )) (PreH14 : (cm_rep_stmt_temps_safe y )) (PreH15 : (pe = 0)) ,
  (cm_stmt_rep pb y )
  **  (cm_stmt_rep pa x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  “ (cm_rep_stmt_temps_safe y ) ” 
  &&  “ (retval_2 = (cm_stemps (y))) ” 
  &&  “ (0 <= (cm_stemps (y))) ” 
  &&  “ ((cm_stemps (y)) <= INT_MAX) ” 
  &&  “ (cm_rep_stmt_temps_safe x ) ” 
  &&  “ (retval = (cm_stemps (x))) ” 
  &&  “ (0 <= (cm_stemps (x))) ” 
  &&  “ ((cm_stemps (x)) <= INT_MAX) ” 
  &&  “ (stmt_pre <> 0) ” 
  &&  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (s = (CMSeqS (x) (y))) ” 
  &&  “ (result = 0) ” 
  &&  “ (cm_rep_stmt_temps_safe x ) ” 
  &&  “ (cm_rep_stmt_temps_safe y ) ” 
  &&  “ (pe = 0) ”
  &&  (cm_stmt_rep pb y )
  **  (cm_stmt_rep pa x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
.

Definition cmc_stmt_temps_partial_solve_wit_7_pure := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_stmt) (result: Z) (PreH1 : (stmt_pre <> 0)) (PreH2 : (cm_rep_stmt_temps_safe s )) (PreH3 : (s = (CMBlockS (x)))) (PreH4 : (result = 0)) (PreH5 : (cm_rep_stmt_temps_safe x )) (PreH6 : (pe = 0)) (PreH7 : (pa <> 0)) (PreH8 : (pb = 0)) ,
  ((( &( "stmt" ) )) # Ptr  |-> stmt_pre)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_rep pa x )
|--
  “ (cm_rep_stmt_temps_safe x ) ”
.

Definition cmc_stmt_temps_partial_solve_wit_7_aux := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_stmt) (result: Z) (PreH1 : (stmt_pre <> 0)) (PreH2 : (cm_rep_stmt_temps_safe s )) (PreH3 : (s = (CMBlockS (x)))) (PreH4 : (result = 0)) (PreH5 : (cm_rep_stmt_temps_safe x )) (PreH6 : (pe = 0)) (PreH7 : (pa <> 0)) (PreH8 : (pb = 0)) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_rep pa x )
|--
  “ (cm_rep_stmt_temps_safe x ) ” 
  &&  “ (stmt_pre <> 0) ” 
  &&  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (s = (CMBlockS (x))) ” 
  &&  “ (result = 0) ” 
  &&  “ (cm_rep_stmt_temps_safe x ) ” 
  &&  “ (pe = 0) ” 
  &&  “ (pa <> 0) ” 
  &&  “ (pb = 0) ”
  &&  (cm_stmt_rep pa x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
.

Definition cmc_stmt_temps_partial_solve_wit_7 := cmc_stmt_temps_partial_solve_wit_7_pure -> cmc_stmt_temps_partial_solve_wit_7_aux.

Definition cmc_stmt_temps_partial_solve_wit_8_pure := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (y: cm_stmt) (z: cm_stmt) (result: Z) (PreH1 : (stmt_pre <> 0)) (PreH2 : (cm_rep_stmt_temps_safe s )) (PreH3 : (s = (CMIfS (x) (y) (z)))) (PreH4 : (result = 0)) (PreH5 : (cm_rep_expr_temps_safe x )) (PreH6 : (cm_rep_stmt_temps_safe y )) (PreH7 : (cm_rep_stmt_temps_safe z )) ,
  ((( &( "guard_temps" ) )) # Int  |->_)
  **  ((( &( "stmt" ) )) # Ptr  |-> stmt_pre)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_expr_rep pe x )
  **  (cm_stmt_rep pa y )
  **  (cm_stmt_rep pb z )
|--
  “ (cm_rep_expr_temps_safe x ) ”
.

Definition cmc_stmt_temps_partial_solve_wit_8_aux := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (y: cm_stmt) (z: cm_stmt) (result: Z) (PreH1 : (stmt_pre <> 0)) (PreH2 : (cm_rep_stmt_temps_safe s )) (PreH3 : (s = (CMIfS (x) (y) (z)))) (PreH4 : (result = 0)) (PreH5 : (cm_rep_expr_temps_safe x )) (PreH6 : (cm_rep_stmt_temps_safe y )) (PreH7 : (cm_rep_stmt_temps_safe z )) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_expr_rep pe x )
  **  (cm_stmt_rep pa y )
  **  (cm_stmt_rep pb z )
|--
  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (stmt_pre <> 0) ” 
  &&  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (s = (CMIfS (x) (y) (z))) ” 
  &&  “ (result = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (cm_rep_stmt_temps_safe y ) ” 
  &&  “ (cm_rep_stmt_temps_safe z ) ”
  &&  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_rep pa y )
  **  (cm_stmt_rep pb z )
.

Definition cmc_stmt_temps_partial_solve_wit_8 := cmc_stmt_temps_partial_solve_wit_8_pure -> cmc_stmt_temps_partial_solve_wit_8_aux.

Definition cmc_stmt_temps_partial_solve_wit_9_pure := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (y: cm_stmt) (z: cm_stmt) (result: Z) (retval: Z) (PreH1 : (cm_rep_expr_temps_safe x )) (PreH2 : (retval = (cm_tright ((cm_expr_tpair (x)))))) (PreH3 : (stmt_pre <> 0)) (PreH4 : (cm_rep_stmt_temps_safe s )) (PreH5 : (s = (CMIfS (x) (y) (z)))) (PreH6 : (result = 0)) (PreH7 : (cm_rep_expr_temps_safe x )) (PreH8 : (cm_rep_stmt_temps_safe y )) (PreH9 : (cm_rep_stmt_temps_safe z )) ,
  ((( &( "yes_temps" ) )) # Int  |->_)
  **  (cm_expr_rep pe x )
  **  ((( &( "guard_temps" ) )) # Int  |-> retval)
  **  ((( &( "stmt" ) )) # Ptr  |-> stmt_pre)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_rep pa y )
  **  (cm_stmt_rep pb z )
|--
  “ (cm_rep_stmt_temps_safe y ) ”
.

Definition cmc_stmt_temps_partial_solve_wit_9_aux := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (y: cm_stmt) (z: cm_stmt) (result: Z) (retval: Z) (PreH1 : (cm_rep_expr_temps_safe x )) (PreH2 : (retval = (cm_tright ((cm_expr_tpair (x)))))) (PreH3 : (stmt_pre <> 0)) (PreH4 : (cm_rep_stmt_temps_safe s )) (PreH5 : (s = (CMIfS (x) (y) (z)))) (PreH6 : (result = 0)) (PreH7 : (cm_rep_expr_temps_safe x )) (PreH8 : (cm_rep_stmt_temps_safe y )) (PreH9 : (cm_rep_stmt_temps_safe z )) ,
  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_rep pa y )
  **  (cm_stmt_rep pb z )
|--
  “ (cm_rep_stmt_temps_safe y ) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (retval = (cm_tright ((cm_expr_tpair (x))))) ” 
  &&  “ (stmt_pre <> 0) ” 
  &&  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (s = (CMIfS (x) (y) (z))) ” 
  &&  “ (result = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (cm_rep_stmt_temps_safe y ) ” 
  &&  “ (cm_rep_stmt_temps_safe z ) ”
  &&  (cm_stmt_rep pa y )
  **  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_rep pb z )
.

Definition cmc_stmt_temps_partial_solve_wit_9 := cmc_stmt_temps_partial_solve_wit_9_pure -> cmc_stmt_temps_partial_solve_wit_9_aux.

Definition cmc_stmt_temps_partial_solve_wit_10_pure := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (y: cm_stmt) (z: cm_stmt) (result: Z) (retval: Z) (retval_2: Z) (PreH1 : (cm_rep_stmt_temps_safe y )) (PreH2 : (retval_2 = (cm_stemps (y)))) (PreH3 : (0 <= (cm_stemps (y)))) (PreH4 : ((cm_stemps (y)) <= INT_MAX)) (PreH5 : (cm_rep_expr_temps_safe x )) (PreH6 : (retval = (cm_tright ((cm_expr_tpair (x)))))) (PreH7 : (stmt_pre <> 0)) (PreH8 : (cm_rep_stmt_temps_safe s )) (PreH9 : (s = (CMIfS (x) (y) (z)))) (PreH10 : (result = 0)) (PreH11 : (cm_rep_expr_temps_safe x )) (PreH12 : (cm_rep_stmt_temps_safe y )) (PreH13 : (cm_rep_stmt_temps_safe z )) ,
  ((( &( "no_temps" ) )) # Int  |->_)
  **  (cm_stmt_rep pa y )
  **  ((( &( "yes_temps" ) )) # Int  |-> retval_2)
  **  (cm_expr_rep pe x )
  **  ((( &( "guard_temps" ) )) # Int  |-> retval)
  **  ((( &( "stmt" ) )) # Ptr  |-> stmt_pre)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_rep pb z )
|--
  “ (cm_rep_stmt_temps_safe z ) ”
.

Definition cmc_stmt_temps_partial_solve_wit_10_aux := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (y: cm_stmt) (z: cm_stmt) (result: Z) (retval: Z) (retval_2: Z) (PreH1 : (cm_rep_stmt_temps_safe y )) (PreH2 : (retval_2 = (cm_stemps (y)))) (PreH3 : (0 <= (cm_stemps (y)))) (PreH4 : ((cm_stemps (y)) <= INT_MAX)) (PreH5 : (cm_rep_expr_temps_safe x )) (PreH6 : (retval = (cm_tright ((cm_expr_tpair (x)))))) (PreH7 : (stmt_pre <> 0)) (PreH8 : (cm_rep_stmt_temps_safe s )) (PreH9 : (s = (CMIfS (x) (y) (z)))) (PreH10 : (result = 0)) (PreH11 : (cm_rep_expr_temps_safe x )) (PreH12 : (cm_rep_stmt_temps_safe y )) (PreH13 : (cm_rep_stmt_temps_safe z )) ,
  (cm_stmt_rep pa y )
  **  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_rep pb z )
|--
  “ (cm_rep_stmt_temps_safe z ) ” 
  &&  “ (cm_rep_stmt_temps_safe y ) ” 
  &&  “ (retval_2 = (cm_stemps (y))) ” 
  &&  “ (0 <= (cm_stemps (y))) ” 
  &&  “ ((cm_stemps (y)) <= INT_MAX) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (retval = (cm_tright ((cm_expr_tpair (x))))) ” 
  &&  “ (stmt_pre <> 0) ” 
  &&  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (s = (CMIfS (x) (y) (z))) ” 
  &&  “ (result = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (cm_rep_stmt_temps_safe y ) ” 
  &&  “ (cm_rep_stmt_temps_safe z ) ”
  &&  (cm_stmt_rep pb z )
  **  (cm_stmt_rep pa y )
  **  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
.

Definition cmc_stmt_temps_partial_solve_wit_10 := cmc_stmt_temps_partial_solve_wit_10_pure -> cmc_stmt_temps_partial_solve_wit_10_aux.

Definition cmc_stmt_temps_partial_solve_wit_11 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (y: cm_stmt) (z: cm_stmt) (result: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (cm_rep_stmt_temps_safe z )) (PreH2 : (retval_3 = (cm_stemps (z)))) (PreH3 : (0 <= (cm_stemps (z)))) (PreH4 : ((cm_stemps (z)) <= INT_MAX)) (PreH5 : (cm_rep_stmt_temps_safe y )) (PreH6 : (retval_2 = (cm_stemps (y)))) (PreH7 : (0 <= (cm_stemps (y)))) (PreH8 : ((cm_stemps (y)) <= INT_MAX)) (PreH9 : (cm_rep_expr_temps_safe x )) (PreH10 : (retval = (cm_tright ((cm_expr_tpair (x)))))) (PreH11 : (stmt_pre <> 0)) (PreH12 : (cm_rep_stmt_temps_safe s )) (PreH13 : (s = (CMIfS (x) (y) (z)))) (PreH14 : (result = 0)) (PreH15 : (cm_rep_expr_temps_safe x )) (PreH16 : (cm_rep_stmt_temps_safe y )) (PreH17 : (cm_rep_stmt_temps_safe z )) ,
  (cm_stmt_rep pb z )
  **  (cm_stmt_rep pa y )
  **  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  “ (cm_rep_stmt_temps_safe z ) ” 
  &&  “ (retval_3 = (cm_stemps (z))) ” 
  &&  “ (0 <= (cm_stemps (z))) ” 
  &&  “ ((cm_stemps (z)) <= INT_MAX) ” 
  &&  “ (cm_rep_stmt_temps_safe y ) ” 
  &&  “ (retval_2 = (cm_stemps (y))) ” 
  &&  “ (0 <= (cm_stemps (y))) ” 
  &&  “ ((cm_stemps (y)) <= INT_MAX) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (retval = (cm_tright ((cm_expr_tpair (x))))) ” 
  &&  “ (stmt_pre <> 0) ” 
  &&  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (s = (CMIfS (x) (y) (z))) ” 
  &&  “ (result = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (cm_rep_stmt_temps_safe y ) ” 
  &&  “ (cm_rep_stmt_temps_safe z ) ”
  &&  (cm_stmt_rep pb z )
  **  (cm_stmt_rep pa y )
  **  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
.

Definition cmc_stmt_temps_partial_solve_wit_12 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (y: cm_stmt) (z: cm_stmt) (result: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = (cm_imax (retval_2) (retval_3)))) (PreH2 : (cm_rep_stmt_temps_safe z )) (PreH3 : (retval_3 = (cm_stemps (z)))) (PreH4 : (0 <= (cm_stemps (z)))) (PreH5 : ((cm_stemps (z)) <= INT_MAX)) (PreH6 : (cm_rep_stmt_temps_safe y )) (PreH7 : (retval_2 = (cm_stemps (y)))) (PreH8 : (0 <= (cm_stemps (y)))) (PreH9 : ((cm_stemps (y)) <= INT_MAX)) (PreH10 : (cm_rep_expr_temps_safe x )) (PreH11 : (retval = (cm_tright ((cm_expr_tpair (x)))))) (PreH12 : (stmt_pre <> 0)) (PreH13 : (cm_rep_stmt_temps_safe s )) (PreH14 : (s = (CMIfS (x) (y) (z)))) (PreH15 : (result = 0)) (PreH16 : (cm_rep_expr_temps_safe x )) (PreH17 : (cm_rep_stmt_temps_safe y )) (PreH18 : (cm_rep_stmt_temps_safe z )) ,
  (cm_stmt_rep pb z )
  **  (cm_stmt_rep pa y )
  **  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  “ (retval_4 = (cm_imax (retval_2) (retval_3))) ” 
  &&  “ (cm_rep_stmt_temps_safe z ) ” 
  &&  “ (retval_3 = (cm_stemps (z))) ” 
  &&  “ (0 <= (cm_stemps (z))) ” 
  &&  “ ((cm_stemps (z)) <= INT_MAX) ” 
  &&  “ (cm_rep_stmt_temps_safe y ) ” 
  &&  “ (retval_2 = (cm_stemps (y))) ” 
  &&  “ (0 <= (cm_stemps (y))) ” 
  &&  “ ((cm_stemps (y)) <= INT_MAX) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (retval = (cm_tright ((cm_expr_tpair (x))))) ” 
  &&  “ (stmt_pre <> 0) ” 
  &&  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (s = (CMIfS (x) (y) (z))) ” 
  &&  “ (result = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (cm_rep_stmt_temps_safe y ) ” 
  &&  “ (cm_rep_stmt_temps_safe z ) ”
  &&  (cm_stmt_rep pb z )
  **  (cm_stmt_rep pa y )
  **  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
.

Definition cmc_stmt_temps_partial_solve_wit_13_pure := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (y: cm_stmt) (result: Z) (PreH1 : (stmt_pre <> 0)) (PreH2 : (cm_rep_stmt_temps_safe s )) (PreH3 : (s = (CMWhileS (x) (y)))) (PreH4 : (result = 0)) (PreH5 : (cm_rep_expr_temps_safe x )) (PreH6 : (cm_rep_stmt_temps_safe y )) (PreH7 : (pe <> 0)) (PreH8 : (pa <> 0)) (PreH9 : (pb = 0)) ,
  ((( &( "guard_temps" ) )) # Int  |->_)
  **  ((( &( "stmt" ) )) # Ptr  |-> stmt_pre)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_expr_rep pe x )
  **  (cm_stmt_rep pa y )
|--
  “ (cm_rep_expr_temps_safe x ) ”
.

Definition cmc_stmt_temps_partial_solve_wit_13_aux := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (y: cm_stmt) (result: Z) (PreH1 : (stmt_pre <> 0)) (PreH2 : (cm_rep_stmt_temps_safe s )) (PreH3 : (s = (CMWhileS (x) (y)))) (PreH4 : (result = 0)) (PreH5 : (cm_rep_expr_temps_safe x )) (PreH6 : (cm_rep_stmt_temps_safe y )) (PreH7 : (pe <> 0)) (PreH8 : (pa <> 0)) (PreH9 : (pb = 0)) ,
  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_expr_rep pe x )
  **  (cm_stmt_rep pa y )
|--
  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (stmt_pre <> 0) ” 
  &&  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (s = (CMWhileS (x) (y))) ” 
  &&  “ (result = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (cm_rep_stmt_temps_safe y ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pa <> 0) ” 
  &&  “ (pb = 0) ”
  &&  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_rep pa y )
.

Definition cmc_stmt_temps_partial_solve_wit_13 := cmc_stmt_temps_partial_solve_wit_13_pure -> cmc_stmt_temps_partial_solve_wit_13_aux.

Definition cmc_stmt_temps_partial_solve_wit_14_pure := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (y: cm_stmt) (result: Z) (retval: Z) (PreH1 : (cm_rep_expr_temps_safe x )) (PreH2 : (retval = (cm_tright ((cm_expr_tpair (x)))))) (PreH3 : (stmt_pre <> 0)) (PreH4 : (cm_rep_stmt_temps_safe s )) (PreH5 : (s = (CMWhileS (x) (y)))) (PreH6 : (result = 0)) (PreH7 : (cm_rep_expr_temps_safe x )) (PreH8 : (cm_rep_stmt_temps_safe y )) (PreH9 : (pe <> 0)) (PreH10 : (pa <> 0)) (PreH11 : (pb = 0)) ,
  ((( &( "body_temps" ) )) # Int  |->_)
  **  (cm_expr_rep pe x )
  **  ((( &( "guard_temps" ) )) # Int  |-> retval)
  **  ((( &( "stmt" ) )) # Ptr  |-> stmt_pre)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_rep pa y )
|--
  “ (cm_rep_stmt_temps_safe y ) ”
.

Definition cmc_stmt_temps_partial_solve_wit_14_aux := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (y: cm_stmt) (result: Z) (retval: Z) (PreH1 : (cm_rep_expr_temps_safe x )) (PreH2 : (retval = (cm_tright ((cm_expr_tpair (x)))))) (PreH3 : (stmt_pre <> 0)) (PreH4 : (cm_rep_stmt_temps_safe s )) (PreH5 : (s = (CMWhileS (x) (y)))) (PreH6 : (result = 0)) (PreH7 : (cm_rep_expr_temps_safe x )) (PreH8 : (cm_rep_stmt_temps_safe y )) (PreH9 : (pe <> 0)) (PreH10 : (pa <> 0)) (PreH11 : (pb = 0)) ,
  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
  **  (cm_stmt_rep pa y )
|--
  “ (cm_rep_stmt_temps_safe y ) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (retval = (cm_tright ((cm_expr_tpair (x))))) ” 
  &&  “ (stmt_pre <> 0) ” 
  &&  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (s = (CMWhileS (x) (y))) ” 
  &&  “ (result = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (cm_rep_stmt_temps_safe y ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pa <> 0) ” 
  &&  “ (pb = 0) ”
  &&  (cm_stmt_rep pa y )
  **  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
.

Definition cmc_stmt_temps_partial_solve_wit_14 := cmc_stmt_temps_partial_solve_wit_14_pure -> cmc_stmt_temps_partial_solve_wit_14_aux.

Definition cmc_stmt_temps_partial_solve_wit_15 := 
forall (stmt_pre: Z) (s: cm_stmt) (pe: Z) (pa: Z) (pb: Z) (x: cm_expr) (y: cm_stmt) (result: Z) (retval: Z) (retval_2: Z) (PreH1 : (cm_rep_stmt_temps_safe y )) (PreH2 : (retval_2 = (cm_stemps (y)))) (PreH3 : (0 <= (cm_stemps (y)))) (PreH4 : ((cm_stemps (y)) <= INT_MAX)) (PreH5 : (cm_rep_expr_temps_safe x )) (PreH6 : (retval = (cm_tright ((cm_expr_tpair (x)))))) (PreH7 : (stmt_pre <> 0)) (PreH8 : (cm_rep_stmt_temps_safe s )) (PreH9 : (s = (CMWhileS (x) (y)))) (PreH10 : (result = 0)) (PreH11 : (cm_rep_expr_temps_safe x )) (PreH12 : (cm_rep_stmt_temps_safe y )) (PreH13 : (pe <> 0)) (PreH14 : (pa <> 0)) (PreH15 : (pb = 0)) ,
  (cm_stmt_rep pa y )
  **  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
|--
  “ (cm_rep_stmt_temps_safe y ) ” 
  &&  “ (retval_2 = (cm_stemps (y))) ” 
  &&  “ (0 <= (cm_stemps (y))) ” 
  &&  “ ((cm_stemps (y)) <= INT_MAX) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (retval = (cm_tright ((cm_expr_tpair (x))))) ” 
  &&  “ (stmt_pre <> 0) ” 
  &&  “ (cm_rep_stmt_temps_safe s ) ” 
  &&  “ (s = (CMWhileS (x) (y))) ” 
  &&  “ (result = 0) ” 
  &&  “ (cm_rep_expr_temps_safe x ) ” 
  &&  “ (cm_rep_stmt_temps_safe y ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pa <> 0) ” 
  &&  “ (pb = 0) ”
  &&  (cm_stmt_rep pa y )
  **  (cm_expr_rep pe x )
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "kind")) # Int  |-> (cm_rep_stmt_kind (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "slot")) # Int  |-> (cm_rep_stmt_slot (s)))
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "expr")) # Ptr  |-> pe)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "a")) # Ptr  |-> pa)
  **  ((&((stmt_pre)  # "cm_stmt" ->ₛ "b")) # Ptr  |-> pb)
.

(*----- Function cmc_frame_size -----*)

Definition cmc_frame_size_safety_wit_1 := 
forall (fn_pre: Z) (zb: Z) (body: cm_stmt) (zl: Z) (locals: (@list cm_slot_d)) (zp: Z) (params: (@list cm_slot_d)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (cm_rep_stmt_temps_safe body )) (PreH2 : (retval_3 = (cm_stemps (body)))) (PreH3 : (0 <= (cm_stemps (body)))) (PreH4 : ((cm_stemps (body)) <= INT_MAX)) (PreH5 : (cm_rep_members_safe locals )) (PreH6 : (retval_2 = (cm_rep_members_size (locals)))) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 <= 1048576)) (PreH9 : (cm_rep_members_safe params )) (PreH10 : (retval = (cm_rep_members_size (params)))) (PreH11 : (0 <= retval)) (PreH12 : (retval <= 1048576)) (PreH13 : (cm_rep_members_safe params )) (PreH14 : (cm_rep_members_safe locals )) (PreH15 : (cm_rep_stmt_temps_safe body )) (PreH16 : ((((8 + (cm_rep_members_size (params)) ) + (cm_rep_members_size (locals)) ) + (8 * (cm_stemps (body)) ) ) <= INT_MAX)) ,
  (cm_stmt_rep zb body )
  **  ((( &( "temps" ) )) # Int  |-> retval_3)
  **  (cm_slot_list_rep zl locals )
  **  ((( &( "locals_size" ) )) # Int64  |-> retval_2)
  **  (cm_slot_list_rep zp params )
  **  ((( &( "params_size" ) )) # Int64  |-> retval)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> zb)
|--
  “ ((((8 + retval ) + retval_2 ) + (8 * retval_3 ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((8 + retval ) + retval_2 ) + (8 * retval_3 ) )) ”
.

Definition cmc_frame_size_safety_wit_2 := 
forall (fn_pre: Z) (zb: Z) (body: cm_stmt) (zl: Z) (locals: (@list cm_slot_d)) (zp: Z) (params: (@list cm_slot_d)) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (cm_rep_stmt_temps_safe body )) (PreH2 : (retval = (cm_stemps (body)))) (PreH3 : (0 <= (cm_stemps (body)))) (PreH4 : ((cm_stemps (body)) <= INT_MAX)) (PreH5 : (cm_rep_members_safe locals )) (PreH6 : (retval_3 = (cm_rep_members_size (locals)))) (PreH7 : (0 <= retval_3)) (PreH8 : (retval_3 <= 1048576)) (PreH9 : (cm_rep_members_safe params )) (PreH10 : (retval_2 = (cm_rep_members_size (params)))) (PreH11 : (0 <= retval_2)) (PreH12 : (retval_2 <= 1048576)) (PreH13 : (cm_rep_members_safe params )) (PreH14 : (cm_rep_members_safe locals )) (PreH15 : (cm_rep_stmt_temps_safe body )) (PreH16 : ((((8 + (cm_rep_members_size (params)) ) + (cm_rep_members_size (locals)) ) + (8 * (cm_stemps (body)) ) ) <= INT_MAX)) ,
  (cm_stmt_rep zb body )
  **  ((( &( "temps" ) )) # Int  |-> retval)
  **  (cm_slot_list_rep zl locals )
  **  ((( &( "locals_size" ) )) # Int64  |-> retval_3)
  **  (cm_slot_list_rep zp params )
  **  ((( &( "params_size" ) )) # Int64  |-> retval_2)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> zb)
|--
  “ ((8 * retval ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (8 * retval )) ”
.

Definition cmc_frame_size_safety_wit_3 := 
forall (fn_pre: Z) (zb: Z) (body: cm_stmt) (zl: Z) (locals: (@list cm_slot_d)) (zp: Z) (params: (@list cm_slot_d)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (cm_rep_stmt_temps_safe body )) (PreH2 : (retval_3 = (cm_stemps (body)))) (PreH3 : (0 <= (cm_stemps (body)))) (PreH4 : ((cm_stemps (body)) <= INT_MAX)) (PreH5 : (cm_rep_members_safe locals )) (PreH6 : (retval_2 = (cm_rep_members_size (locals)))) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 <= 1048576)) (PreH9 : (cm_rep_members_safe params )) (PreH10 : (retval = (cm_rep_members_size (params)))) (PreH11 : (0 <= retval)) (PreH12 : (retval <= 1048576)) (PreH13 : (cm_rep_members_safe params )) (PreH14 : (cm_rep_members_safe locals )) (PreH15 : (cm_rep_stmt_temps_safe body )) (PreH16 : ((((8 + (cm_rep_members_size (params)) ) + (cm_rep_members_size (locals)) ) + (8 * (cm_stemps (body)) ) ) <= INT_MAX)) ,
  (cm_stmt_rep zb body )
  **  ((( &( "temps" ) )) # Int  |-> retval_3)
  **  (cm_slot_list_rep zl locals )
  **  ((( &( "locals_size" ) )) # Int64  |-> retval_2)
  **  (cm_slot_list_rep zp params )
  **  ((( &( "params_size" ) )) # Int64  |-> retval)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> zb)
|--
  “ (((8 + retval ) + retval_2 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((8 + retval ) + retval_2 )) ”
.

Definition cmc_frame_size_safety_wit_4 := 
forall (fn_pre: Z) (zb: Z) (body: cm_stmt) (zl: Z) (locals: (@list cm_slot_d)) (zp: Z) (params: (@list cm_slot_d)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (cm_rep_stmt_temps_safe body )) (PreH2 : (retval_3 = (cm_stemps (body)))) (PreH3 : (0 <= (cm_stemps (body)))) (PreH4 : ((cm_stemps (body)) <= INT_MAX)) (PreH5 : (cm_rep_members_safe locals )) (PreH6 : (retval_2 = (cm_rep_members_size (locals)))) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 <= 1048576)) (PreH9 : (cm_rep_members_safe params )) (PreH10 : (retval = (cm_rep_members_size (params)))) (PreH11 : (0 <= retval)) (PreH12 : (retval <= 1048576)) (PreH13 : (cm_rep_members_safe params )) (PreH14 : (cm_rep_members_safe locals )) (PreH15 : (cm_rep_stmt_temps_safe body )) (PreH16 : ((((8 + (cm_rep_members_size (params)) ) + (cm_rep_members_size (locals)) ) + (8 * (cm_stemps (body)) ) ) <= INT_MAX)) ,
  (cm_stmt_rep zb body )
  **  ((( &( "temps" ) )) # Int  |-> retval_3)
  **  (cm_slot_list_rep zl locals )
  **  ((( &( "locals_size" ) )) # Int64  |-> retval_2)
  **  (cm_slot_list_rep zp params )
  **  ((( &( "params_size" ) )) # Int64  |-> retval)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> zb)
|--
  “ ((8 + retval ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (8 + retval )) ”
.

Definition cmc_frame_size_safety_wit_5 := 
forall (fn_pre: Z) (zb: Z) (body: cm_stmt) (zl: Z) (locals: (@list cm_slot_d)) (zp: Z) (params: (@list cm_slot_d)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (cm_rep_stmt_temps_safe body )) (PreH2 : (retval_3 = (cm_stemps (body)))) (PreH3 : (0 <= (cm_stemps (body)))) (PreH4 : ((cm_stemps (body)) <= INT_MAX)) (PreH5 : (cm_rep_members_safe locals )) (PreH6 : (retval_2 = (cm_rep_members_size (locals)))) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 <= 1048576)) (PreH9 : (cm_rep_members_safe params )) (PreH10 : (retval = (cm_rep_members_size (params)))) (PreH11 : (0 <= retval)) (PreH12 : (retval <= 1048576)) (PreH13 : (cm_rep_members_safe params )) (PreH14 : (cm_rep_members_safe locals )) (PreH15 : (cm_rep_stmt_temps_safe body )) (PreH16 : ((((8 + (cm_rep_members_size (params)) ) + (cm_rep_members_size (locals)) ) + (8 * (cm_stemps (body)) ) ) <= INT_MAX)) ,
  (cm_stmt_rep zb body )
  **  ((( &( "temps" ) )) # Int  |-> retval_3)
  **  (cm_slot_list_rep zl locals )
  **  ((( &( "locals_size" ) )) # Int64  |-> retval_2)
  **  (cm_slot_list_rep zp params )
  **  ((( &( "params_size" ) )) # Int64  |-> retval)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> zb)
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition cmc_frame_size_safety_wit_6 := 
forall (fn_pre: Z) (zb: Z) (body: cm_stmt) (zl: Z) (locals: (@list cm_slot_d)) (zp: Z) (params: (@list cm_slot_d)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (cm_rep_stmt_temps_safe body )) (PreH2 : (retval_3 = (cm_stemps (body)))) (PreH3 : (0 <= (cm_stemps (body)))) (PreH4 : ((cm_stemps (body)) <= INT_MAX)) (PreH5 : (cm_rep_members_safe locals )) (PreH6 : (retval_2 = (cm_rep_members_size (locals)))) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 <= 1048576)) (PreH9 : (cm_rep_members_safe params )) (PreH10 : (retval = (cm_rep_members_size (params)))) (PreH11 : (0 <= retval)) (PreH12 : (retval <= 1048576)) (PreH13 : (cm_rep_members_safe params )) (PreH14 : (cm_rep_members_safe locals )) (PreH15 : (cm_rep_stmt_temps_safe body )) (PreH16 : ((((8 + (cm_rep_members_size (params)) ) + (cm_rep_members_size (locals)) ) + (8 * (cm_stemps (body)) ) ) <= INT_MAX)) ,
  (cm_stmt_rep zb body )
  **  ((( &( "temps" ) )) # Int  |-> retval_3)
  **  (cm_slot_list_rep zl locals )
  **  ((( &( "locals_size" ) )) # Int64  |-> retval_2)
  **  (cm_slot_list_rep zp params )
  **  ((( &( "params_size" ) )) # Int64  |-> retval)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> zb)
|--
  “ (8 <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= 8) ”
.

Definition cmc_frame_size_return_wit_1 := 
forall (fn_pre: Z) (zb: Z) (body: cm_stmt) (zl: Z) (locals: (@list cm_slot_d)) (zp: Z) (params: (@list cm_slot_d)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (cm_rep_stmt_temps_safe body )) (PreH2 : (retval_3 = (cm_stemps (body)))) (PreH3 : (0 <= (cm_stemps (body)))) (PreH4 : ((cm_stemps (body)) <= INT_MAX)) (PreH5 : (cm_rep_members_safe locals )) (PreH6 : (retval_2 = (cm_rep_members_size (locals)))) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 <= 1048576)) (PreH9 : (cm_rep_members_safe params )) (PreH10 : (retval = (cm_rep_members_size (params)))) (PreH11 : (0 <= retval)) (PreH12 : (retval <= 1048576)) (PreH13 : (cm_rep_members_safe params )) (PreH14 : (cm_rep_members_safe locals )) (PreH15 : (cm_rep_stmt_temps_safe body )) (PreH16 : ((((8 + (cm_rep_members_size (params)) ) + (cm_rep_members_size (locals)) ) + (8 * (cm_stemps (body)) ) ) <= INT_MAX)) ,
  (cm_stmt_rep zb body )
  **  (cm_slot_list_rep zl locals )
  **  (cm_slot_list_rep zp params )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> zb)
|--
  “ (cm_rep_members_safe params ) ” 
  &&  “ (cm_rep_members_safe locals ) ” 
  &&  “ (cm_rep_stmt_temps_safe body ) ” 
  &&  “ ((((8 + (cm_rep_members_size (params)) ) + (cm_rep_members_size (locals)) ) + (8 * (cm_stemps (body)) ) ) <= INT_MAX) ” 
  &&  “ ((((8 + retval ) + retval_2 ) + (8 * retval_3 ) ) = (((8 + (cm_rep_members_size (params)) ) + (cm_rep_members_size (locals)) ) + (8 * (cm_stemps (body)) ) )) ”
  &&  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  (cm_slot_list_rep zp params )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl locals )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> zb)
  **  (cm_stmt_rep zb body )
.

Definition cmc_frame_size_partial_solve_wit_1_pure := 
forall (fn_pre: Z) (zb: Z) (body: cm_stmt) (zl: Z) (locals: (@list cm_slot_d)) (zp: Z) (params: (@list cm_slot_d)) (PreH1 : (cm_rep_members_safe params )) (PreH2 : (cm_rep_members_safe locals )) (PreH3 : (cm_rep_stmt_temps_safe body )) (PreH4 : ((((8 + (cm_rep_members_size (params)) ) + (cm_rep_members_size (locals)) ) + (8 * (cm_stemps (body)) ) ) <= INT_MAX)) ,
  ((( &( "params_size" ) )) # Int64  |->_)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  (cm_slot_list_rep zp params )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl locals )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> zb)
  **  (cm_stmt_rep zb body )
|--
  “ (cm_rep_members_safe params ) ”
.

Definition cmc_frame_size_partial_solve_wit_1_aux := 
forall (fn_pre: Z) (zb: Z) (body: cm_stmt) (zl: Z) (locals: (@list cm_slot_d)) (zp: Z) (params: (@list cm_slot_d)) (PreH1 : (cm_rep_members_safe params )) (PreH2 : (cm_rep_members_safe locals )) (PreH3 : (cm_rep_stmt_temps_safe body )) (PreH4 : ((((8 + (cm_rep_members_size (params)) ) + (cm_rep_members_size (locals)) ) + (8 * (cm_stemps (body)) ) ) <= INT_MAX)) ,
  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  (cm_slot_list_rep zp params )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl locals )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> zb)
  **  (cm_stmt_rep zb body )
|--
  “ (cm_rep_members_safe params ) ” 
  &&  “ (cm_rep_members_safe params ) ” 
  &&  “ (cm_rep_members_safe locals ) ” 
  &&  “ (cm_rep_stmt_temps_safe body ) ” 
  &&  “ ((((8 + (cm_rep_members_size (params)) ) + (cm_rep_members_size (locals)) ) + (8 * (cm_stemps (body)) ) ) <= INT_MAX) ”
  &&  (cm_slot_list_rep zp params )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl locals )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> zb)
  **  (cm_stmt_rep zb body )
.

Definition cmc_frame_size_partial_solve_wit_1 := cmc_frame_size_partial_solve_wit_1_pure -> cmc_frame_size_partial_solve_wit_1_aux.

Definition cmc_frame_size_partial_solve_wit_2_pure := 
forall (fn_pre: Z) (zb: Z) (body: cm_stmt) (zl: Z) (locals: (@list cm_slot_d)) (zp: Z) (params: (@list cm_slot_d)) (retval: Z) (PreH1 : (cm_rep_members_safe params )) (PreH2 : (retval = (cm_rep_members_size (params)))) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1048576)) (PreH5 : (cm_rep_members_safe params )) (PreH6 : (cm_rep_members_safe locals )) (PreH7 : (cm_rep_stmt_temps_safe body )) (PreH8 : ((((8 + (cm_rep_members_size (params)) ) + (cm_rep_members_size (locals)) ) + (8 * (cm_stemps (body)) ) ) <= INT_MAX)) ,
  ((( &( "locals_size" ) )) # Int64  |->_)
  **  (cm_slot_list_rep zp params )
  **  ((( &( "params_size" ) )) # Int64  |-> retval)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl locals )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> zb)
  **  (cm_stmt_rep zb body )
|--
  “ (cm_rep_members_safe locals ) ”
.

Definition cmc_frame_size_partial_solve_wit_2_aux := 
forall (fn_pre: Z) (zb: Z) (body: cm_stmt) (zl: Z) (locals: (@list cm_slot_d)) (zp: Z) (params: (@list cm_slot_d)) (retval: Z) (PreH1 : (cm_rep_members_safe params )) (PreH2 : (retval = (cm_rep_members_size (params)))) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1048576)) (PreH5 : (cm_rep_members_safe params )) (PreH6 : (cm_rep_members_safe locals )) (PreH7 : (cm_rep_stmt_temps_safe body )) (PreH8 : ((((8 + (cm_rep_members_size (params)) ) + (cm_rep_members_size (locals)) ) + (8 * (cm_stemps (body)) ) ) <= INT_MAX)) ,
  (cm_slot_list_rep zp params )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl locals )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> zb)
  **  (cm_stmt_rep zb body )
|--
  “ (cm_rep_members_safe locals ) ” 
  &&  “ (cm_rep_members_safe params ) ” 
  &&  “ (retval = (cm_rep_members_size (params))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1048576) ” 
  &&  “ (cm_rep_members_safe params ) ” 
  &&  “ (cm_rep_members_safe locals ) ” 
  &&  “ (cm_rep_stmt_temps_safe body ) ” 
  &&  “ ((((8 + (cm_rep_members_size (params)) ) + (cm_rep_members_size (locals)) ) + (8 * (cm_stemps (body)) ) ) <= INT_MAX) ”
  &&  (cm_slot_list_rep zl locals )
  **  (cm_slot_list_rep zp params )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> zb)
  **  (cm_stmt_rep zb body )
.

Definition cmc_frame_size_partial_solve_wit_2 := cmc_frame_size_partial_solve_wit_2_pure -> cmc_frame_size_partial_solve_wit_2_aux.

Definition cmc_frame_size_partial_solve_wit_3_pure := 
forall (fn_pre: Z) (zb: Z) (body: cm_stmt) (zl: Z) (locals: (@list cm_slot_d)) (zp: Z) (params: (@list cm_slot_d)) (retval: Z) (retval_2: Z) (PreH1 : (cm_rep_members_safe locals )) (PreH2 : (retval_2 = (cm_rep_members_size (locals)))) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1048576)) (PreH5 : (cm_rep_members_safe params )) (PreH6 : (retval = (cm_rep_members_size (params)))) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1048576)) (PreH9 : (cm_rep_members_safe params )) (PreH10 : (cm_rep_members_safe locals )) (PreH11 : (cm_rep_stmt_temps_safe body )) (PreH12 : ((((8 + (cm_rep_members_size (params)) ) + (cm_rep_members_size (locals)) ) + (8 * (cm_stemps (body)) ) ) <= INT_MAX)) ,
  ((( &( "temps" ) )) # Int  |->_)
  **  (cm_slot_list_rep zl locals )
  **  ((( &( "locals_size" ) )) # Int64  |-> retval_2)
  **  (cm_slot_list_rep zp params )
  **  ((( &( "params_size" ) )) # Int64  |-> retval)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> zb)
  **  (cm_stmt_rep zb body )
|--
  “ (cm_rep_stmt_temps_safe body ) ”
.

Definition cmc_frame_size_partial_solve_wit_3_aux := 
forall (fn_pre: Z) (zb: Z) (body: cm_stmt) (zl: Z) (locals: (@list cm_slot_d)) (zp: Z) (params: (@list cm_slot_d)) (retval: Z) (retval_2: Z) (PreH1 : (cm_rep_members_safe locals )) (PreH2 : (retval_2 = (cm_rep_members_size (locals)))) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1048576)) (PreH5 : (cm_rep_members_safe params )) (PreH6 : (retval = (cm_rep_members_size (params)))) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1048576)) (PreH9 : (cm_rep_members_safe params )) (PreH10 : (cm_rep_members_safe locals )) (PreH11 : (cm_rep_stmt_temps_safe body )) (PreH12 : ((((8 + (cm_rep_members_size (params)) ) + (cm_rep_members_size (locals)) ) + (8 * (cm_stemps (body)) ) ) <= INT_MAX)) ,
  (cm_slot_list_rep zl locals )
  **  (cm_slot_list_rep zp params )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> zb)
  **  (cm_stmt_rep zb body )
|--
  “ (cm_rep_stmt_temps_safe body ) ” 
  &&  “ (cm_rep_members_safe locals ) ” 
  &&  “ (retval_2 = (cm_rep_members_size (locals))) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1048576) ” 
  &&  “ (cm_rep_members_safe params ) ” 
  &&  “ (retval = (cm_rep_members_size (params))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1048576) ” 
  &&  “ (cm_rep_members_safe params ) ” 
  &&  “ (cm_rep_members_safe locals ) ” 
  &&  “ (cm_rep_stmt_temps_safe body ) ” 
  &&  “ ((((8 + (cm_rep_members_size (params)) ) + (cm_rep_members_size (locals)) ) + (8 * (cm_stemps (body)) ) ) <= INT_MAX) ”
  &&  (cm_stmt_rep zb body )
  **  (cm_slot_list_rep zl locals )
  **  (cm_slot_list_rep zp params )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "body")) # Ptr  |-> zb)
.

Definition cmc_frame_size_partial_solve_wit_3 := cmc_frame_size_partial_solve_wit_3_pure -> cmc_frame_size_partial_solve_wit_3_aux.

(*----- Function cmc_param_offset -----*)

Definition cmc_param_offset_safety_wit_1 := 
forall (slot_pre: Z) (fn_pre: Z) (zp: Z) (params: (@list cm_slot_d)) (retval: Z) (PreH1 : (0 <= slot_pre)) (PreH2 : (cm_rep_members_safe params )) (PreH3 : (retval = (cm_rep_member_prefix (params) (slot_pre)))) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1048576)) (PreH6 : (retval <= (cm_rep_members_size (params)))) (PreH7 : (cm_rep_members_safe params )) (PreH8 : (0 <= slot_pre)) ,
  (cm_slot_list_rep zp params )
  **  ((( &( "prefix" ) )) # Int64  |-> retval)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
|--
  “ ((8 + retval ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (8 + retval )) ”
.

Definition cmc_param_offset_safety_wit_2 := 
forall (slot_pre: Z) (fn_pre: Z) (zp: Z) (params: (@list cm_slot_d)) (retval: Z) (PreH1 : (0 <= slot_pre)) (PreH2 : (cm_rep_members_safe params )) (PreH3 : (retval = (cm_rep_member_prefix (params) (slot_pre)))) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1048576)) (PreH6 : (retval <= (cm_rep_members_size (params)))) (PreH7 : (cm_rep_members_safe params )) (PreH8 : (0 <= slot_pre)) ,
  (cm_slot_list_rep zp params )
  **  ((( &( "prefix" ) )) # Int64  |-> retval)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition cmc_param_offset_return_wit_1 := 
forall (slot_pre: Z) (fn_pre: Z) (zp: Z) (params: (@list cm_slot_d)) (retval: Z) (PreH1 : (0 <= slot_pre)) (PreH2 : (cm_rep_members_safe params )) (PreH3 : (retval = (cm_rep_member_prefix (params) (slot_pre)))) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1048576)) (PreH6 : (retval <= (cm_rep_members_size (params)))) (PreH7 : (cm_rep_members_safe params )) (PreH8 : (0 <= slot_pre)) ,
  (cm_slot_list_rep zp params )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
|--
  “ (cm_rep_members_safe params ) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ ((8 + retval ) = (8 + (cm_rep_member_prefix (params) (slot_pre)) )) ”
  &&  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  (cm_slot_list_rep zp params )
.

Definition cmc_param_offset_partial_solve_wit_1_pure := 
forall (slot_pre: Z) (fn_pre: Z) (zp: Z) (params: (@list cm_slot_d)) (PreH1 : (cm_rep_members_safe params )) (PreH2 : (0 <= slot_pre)) ,
  ((( &( "prefix" ) )) # Int64  |->_)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  (cm_slot_list_rep zp params )
|--
  “ (0 <= slot_pre) ” 
  &&  “ (cm_rep_members_safe params ) ”
.

Definition cmc_param_offset_partial_solve_wit_1_aux := 
forall (slot_pre: Z) (fn_pre: Z) (zp: Z) (params: (@list cm_slot_d)) (PreH1 : (cm_rep_members_safe params )) (PreH2 : (0 <= slot_pre)) ,
  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  (cm_slot_list_rep zp params )
|--
  “ (0 <= slot_pre) ” 
  &&  “ (cm_rep_members_safe params ) ” 
  &&  “ (cm_rep_members_safe params ) ” 
  &&  “ (0 <= slot_pre) ”
  &&  (cm_slot_list_rep zp params )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
.

Definition cmc_param_offset_partial_solve_wit_1 := cmc_param_offset_partial_solve_wit_1_pure -> cmc_param_offset_partial_solve_wit_1_aux.

(*----- Function cmc_local_offset -----*)

Definition cmc_local_offset_safety_wit_1 := 
forall (slot_pre: Z) (fn_pre: Z) (zl: Z) (locals: (@list cm_slot_d)) (zp: Z) (params: (@list cm_slot_d)) (retval: Z) (retval_2: Z) (PreH1 : (0 <= slot_pre)) (PreH2 : (cm_rep_members_safe locals )) (PreH3 : (retval_2 = (cm_rep_member_prefix (locals) (slot_pre)))) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1048576)) (PreH6 : (retval_2 <= (cm_rep_members_size (locals)))) (PreH7 : (cm_rep_members_safe params )) (PreH8 : (retval = (cm_rep_members_size (params)))) (PreH9 : (0 <= retval)) (PreH10 : (retval <= 1048576)) (PreH11 : (cm_rep_members_safe params )) (PreH12 : (cm_rep_members_safe locals )) (PreH13 : (0 <= slot_pre)) ,
  (cm_slot_list_rep zl locals )
  **  ((( &( "prefix" ) )) # Int64  |-> retval_2)
  **  (cm_slot_list_rep zp params )
  **  ((( &( "params_size" ) )) # Int64  |-> retval)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
|--
  “ (((8 + retval ) + retval_2 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((8 + retval ) + retval_2 )) ”
.

Definition cmc_local_offset_safety_wit_2 := 
forall (slot_pre: Z) (fn_pre: Z) (zl: Z) (locals: (@list cm_slot_d)) (zp: Z) (params: (@list cm_slot_d)) (retval: Z) (retval_2: Z) (PreH1 : (0 <= slot_pre)) (PreH2 : (cm_rep_members_safe locals )) (PreH3 : (retval_2 = (cm_rep_member_prefix (locals) (slot_pre)))) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1048576)) (PreH6 : (retval_2 <= (cm_rep_members_size (locals)))) (PreH7 : (cm_rep_members_safe params )) (PreH8 : (retval = (cm_rep_members_size (params)))) (PreH9 : (0 <= retval)) (PreH10 : (retval <= 1048576)) (PreH11 : (cm_rep_members_safe params )) (PreH12 : (cm_rep_members_safe locals )) (PreH13 : (0 <= slot_pre)) ,
  (cm_slot_list_rep zl locals )
  **  ((( &( "prefix" ) )) # Int64  |-> retval_2)
  **  (cm_slot_list_rep zp params )
  **  ((( &( "params_size" ) )) # Int64  |-> retval)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
|--
  “ ((8 + retval ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (8 + retval )) ”
.

Definition cmc_local_offset_safety_wit_3 := 
forall (slot_pre: Z) (fn_pre: Z) (zl: Z) (locals: (@list cm_slot_d)) (zp: Z) (params: (@list cm_slot_d)) (retval: Z) (retval_2: Z) (PreH1 : (0 <= slot_pre)) (PreH2 : (cm_rep_members_safe locals )) (PreH3 : (retval_2 = (cm_rep_member_prefix (locals) (slot_pre)))) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1048576)) (PreH6 : (retval_2 <= (cm_rep_members_size (locals)))) (PreH7 : (cm_rep_members_safe params )) (PreH8 : (retval = (cm_rep_members_size (params)))) (PreH9 : (0 <= retval)) (PreH10 : (retval <= 1048576)) (PreH11 : (cm_rep_members_safe params )) (PreH12 : (cm_rep_members_safe locals )) (PreH13 : (0 <= slot_pre)) ,
  (cm_slot_list_rep zl locals )
  **  ((( &( "prefix" ) )) # Int64  |-> retval_2)
  **  (cm_slot_list_rep zp params )
  **  ((( &( "params_size" ) )) # Int64  |-> retval)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition cmc_local_offset_return_wit_1 := 
forall (slot_pre: Z) (fn_pre: Z) (zl: Z) (locals: (@list cm_slot_d)) (zp: Z) (params: (@list cm_slot_d)) (retval: Z) (retval_2: Z) (PreH1 : (0 <= slot_pre)) (PreH2 : (cm_rep_members_safe locals )) (PreH3 : (retval_2 = (cm_rep_member_prefix (locals) (slot_pre)))) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1048576)) (PreH6 : (retval_2 <= (cm_rep_members_size (locals)))) (PreH7 : (cm_rep_members_safe params )) (PreH8 : (retval = (cm_rep_members_size (params)))) (PreH9 : (0 <= retval)) (PreH10 : (retval <= 1048576)) (PreH11 : (cm_rep_members_safe params )) (PreH12 : (cm_rep_members_safe locals )) (PreH13 : (0 <= slot_pre)) ,
  (cm_slot_list_rep zl locals )
  **  (cm_slot_list_rep zp params )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
|--
  “ (cm_rep_members_safe params ) ” 
  &&  “ (cm_rep_members_safe locals ) ” 
  &&  “ (0 <= slot_pre) ” 
  &&  “ (((8 + retval ) + retval_2 ) = ((8 + (cm_rep_members_size (params)) ) + (cm_rep_member_prefix (locals) (slot_pre)) )) ”
  &&  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  (cm_slot_list_rep zp params )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl locals )
.

Definition cmc_local_offset_partial_solve_wit_1_pure := 
forall (slot_pre: Z) (fn_pre: Z) (zl: Z) (locals: (@list cm_slot_d)) (zp: Z) (params: (@list cm_slot_d)) (PreH1 : (cm_rep_members_safe params )) (PreH2 : (cm_rep_members_safe locals )) (PreH3 : (0 <= slot_pre)) ,
  ((( &( "params_size" ) )) # Int64  |->_)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  (cm_slot_list_rep zp params )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl locals )
|--
  “ (cm_rep_members_safe params ) ”
.

Definition cmc_local_offset_partial_solve_wit_1_aux := 
forall (slot_pre: Z) (fn_pre: Z) (zl: Z) (locals: (@list cm_slot_d)) (zp: Z) (params: (@list cm_slot_d)) (PreH1 : (cm_rep_members_safe params )) (PreH2 : (cm_rep_members_safe locals )) (PreH3 : (0 <= slot_pre)) ,
  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  (cm_slot_list_rep zp params )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl locals )
|--
  “ (cm_rep_members_safe params ) ” 
  &&  “ (cm_rep_members_safe params ) ” 
  &&  “ (cm_rep_members_safe locals ) ” 
  &&  “ (0 <= slot_pre) ”
  &&  (cm_slot_list_rep zp params )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl locals )
.

Definition cmc_local_offset_partial_solve_wit_1 := cmc_local_offset_partial_solve_wit_1_pure -> cmc_local_offset_partial_solve_wit_1_aux.

Definition cmc_local_offset_partial_solve_wit_2_pure := 
forall (slot_pre: Z) (fn_pre: Z) (zl: Z) (locals: (@list cm_slot_d)) (zp: Z) (params: (@list cm_slot_d)) (retval: Z) (PreH1 : (cm_rep_members_safe params )) (PreH2 : (retval = (cm_rep_members_size (params)))) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1048576)) (PreH5 : (cm_rep_members_safe params )) (PreH6 : (cm_rep_members_safe locals )) (PreH7 : (0 <= slot_pre)) ,
  ((( &( "prefix" ) )) # Int64  |->_)
  **  (cm_slot_list_rep zp params )
  **  ((( &( "params_size" ) )) # Int64  |-> retval)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "slot" ) )) # Int  |-> slot_pre)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl locals )
|--
  “ (0 <= slot_pre) ” 
  &&  “ (cm_rep_members_safe locals ) ”
.

Definition cmc_local_offset_partial_solve_wit_2_aux := 
forall (slot_pre: Z) (fn_pre: Z) (zl: Z) (locals: (@list cm_slot_d)) (zp: Z) (params: (@list cm_slot_d)) (retval: Z) (PreH1 : (cm_rep_members_safe params )) (PreH2 : (retval = (cm_rep_members_size (params)))) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1048576)) (PreH5 : (cm_rep_members_safe params )) (PreH6 : (cm_rep_members_safe locals )) (PreH7 : (0 <= slot_pre)) ,
  (cm_slot_list_rep zp params )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl locals )
|--
  “ (0 <= slot_pre) ” 
  &&  “ (cm_rep_members_safe locals ) ” 
  &&  “ (cm_rep_members_safe params ) ” 
  &&  “ (retval = (cm_rep_members_size (params))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1048576) ” 
  &&  “ (cm_rep_members_safe params ) ” 
  &&  “ (cm_rep_members_safe locals ) ” 
  &&  “ (0 <= slot_pre) ”
  &&  (cm_slot_list_rep zl locals )
  **  (cm_slot_list_rep zp params )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
.

Definition cmc_local_offset_partial_solve_wit_2 := cmc_local_offset_partial_solve_wit_2_pure -> cmc_local_offset_partial_solve_wit_2_aux.

(*----- Function cmc_temp_offset -----*)

Definition cmc_temp_offset_safety_wit_1 := 
forall (temp_pre: Z) (fn_pre: Z) (zl: Z) (locals: (@list cm_slot_d)) (zp: Z) (params: (@list cm_slot_d)) (retval: Z) (retval_2: Z) (PreH1 : (cm_rep_members_safe locals )) (PreH2 : (retval_2 = (cm_rep_members_size (locals)))) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1048576)) (PreH5 : (cm_rep_members_safe params )) (PreH6 : (retval = (cm_rep_members_size (params)))) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1048576)) (PreH9 : (cm_rep_members_safe params )) (PreH10 : (cm_rep_members_safe locals )) (PreH11 : (0 <= temp_pre)) (PreH12 : ((((8 + (cm_rep_members_size (params)) ) + (cm_rep_members_size (locals)) ) + (8 * temp_pre ) ) <= INT_MAX)) ,
  (cm_slot_list_rep zl locals )
  **  ((( &( "locals_size" ) )) # Int64  |-> retval_2)
  **  (cm_slot_list_rep zp params )
  **  ((( &( "params_size" ) )) # Int64  |-> retval)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
|--
  “ ((((8 + retval ) + retval_2 ) + (8 * temp_pre ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((8 + retval ) + retval_2 ) + (8 * temp_pre ) )) ”
.

Definition cmc_temp_offset_safety_wit_2 := 
forall (temp_pre: Z) (fn_pre: Z) (zl: Z) (locals: (@list cm_slot_d)) (zp: Z) (params: (@list cm_slot_d)) (retval: Z) (retval_2: Z) (PreH1 : (cm_rep_members_safe locals )) (PreH2 : (retval_2 = (cm_rep_members_size (locals)))) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1048576)) (PreH5 : (cm_rep_members_safe params )) (PreH6 : (retval = (cm_rep_members_size (params)))) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1048576)) (PreH9 : (cm_rep_members_safe params )) (PreH10 : (cm_rep_members_safe locals )) (PreH11 : (0 <= temp_pre)) (PreH12 : ((((8 + (cm_rep_members_size (params)) ) + (cm_rep_members_size (locals)) ) + (8 * temp_pre ) ) <= INT_MAX)) ,
  (cm_slot_list_rep zl locals )
  **  ((( &( "locals_size" ) )) # Int64  |-> retval_2)
  **  (cm_slot_list_rep zp params )
  **  ((( &( "params_size" ) )) # Int64  |-> retval)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
|--
  “ ((8 * temp_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (8 * temp_pre )) ”
.

Definition cmc_temp_offset_safety_wit_3 := 
forall (temp_pre: Z) (fn_pre: Z) (zl: Z) (locals: (@list cm_slot_d)) (zp: Z) (params: (@list cm_slot_d)) (retval: Z) (retval_2: Z) (PreH1 : (cm_rep_members_safe locals )) (PreH2 : (retval_2 = (cm_rep_members_size (locals)))) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1048576)) (PreH5 : (cm_rep_members_safe params )) (PreH6 : (retval = (cm_rep_members_size (params)))) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1048576)) (PreH9 : (cm_rep_members_safe params )) (PreH10 : (cm_rep_members_safe locals )) (PreH11 : (0 <= temp_pre)) (PreH12 : ((((8 + (cm_rep_members_size (params)) ) + (cm_rep_members_size (locals)) ) + (8 * temp_pre ) ) <= INT_MAX)) ,
  (cm_slot_list_rep zl locals )
  **  ((( &( "locals_size" ) )) # Int64  |-> retval_2)
  **  (cm_slot_list_rep zp params )
  **  ((( &( "params_size" ) )) # Int64  |-> retval)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
|--
  “ (((8 + retval ) + retval_2 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((8 + retval ) + retval_2 )) ”
.

Definition cmc_temp_offset_safety_wit_4 := 
forall (temp_pre: Z) (fn_pre: Z) (zl: Z) (locals: (@list cm_slot_d)) (zp: Z) (params: (@list cm_slot_d)) (retval: Z) (retval_2: Z) (PreH1 : (cm_rep_members_safe locals )) (PreH2 : (retval_2 = (cm_rep_members_size (locals)))) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1048576)) (PreH5 : (cm_rep_members_safe params )) (PreH6 : (retval = (cm_rep_members_size (params)))) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1048576)) (PreH9 : (cm_rep_members_safe params )) (PreH10 : (cm_rep_members_safe locals )) (PreH11 : (0 <= temp_pre)) (PreH12 : ((((8 + (cm_rep_members_size (params)) ) + (cm_rep_members_size (locals)) ) + (8 * temp_pre ) ) <= INT_MAX)) ,
  (cm_slot_list_rep zl locals )
  **  ((( &( "locals_size" ) )) # Int64  |-> retval_2)
  **  (cm_slot_list_rep zp params )
  **  ((( &( "params_size" ) )) # Int64  |-> retval)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
|--
  “ ((8 + retval ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (8 + retval )) ”
.

Definition cmc_temp_offset_safety_wit_5 := 
forall (temp_pre: Z) (fn_pre: Z) (zl: Z) (locals: (@list cm_slot_d)) (zp: Z) (params: (@list cm_slot_d)) (retval: Z) (retval_2: Z) (PreH1 : (cm_rep_members_safe locals )) (PreH2 : (retval_2 = (cm_rep_members_size (locals)))) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1048576)) (PreH5 : (cm_rep_members_safe params )) (PreH6 : (retval = (cm_rep_members_size (params)))) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1048576)) (PreH9 : (cm_rep_members_safe params )) (PreH10 : (cm_rep_members_safe locals )) (PreH11 : (0 <= temp_pre)) (PreH12 : ((((8 + (cm_rep_members_size (params)) ) + (cm_rep_members_size (locals)) ) + (8 * temp_pre ) ) <= INT_MAX)) ,
  (cm_slot_list_rep zl locals )
  **  ((( &( "locals_size" ) )) # Int64  |-> retval_2)
  **  (cm_slot_list_rep zp params )
  **  ((( &( "params_size" ) )) # Int64  |-> retval)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition cmc_temp_offset_safety_wit_6 := 
forall (temp_pre: Z) (fn_pre: Z) (zl: Z) (locals: (@list cm_slot_d)) (zp: Z) (params: (@list cm_slot_d)) (retval: Z) (retval_2: Z) (PreH1 : (cm_rep_members_safe locals )) (PreH2 : (retval_2 = (cm_rep_members_size (locals)))) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1048576)) (PreH5 : (cm_rep_members_safe params )) (PreH6 : (retval = (cm_rep_members_size (params)))) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1048576)) (PreH9 : (cm_rep_members_safe params )) (PreH10 : (cm_rep_members_safe locals )) (PreH11 : (0 <= temp_pre)) (PreH12 : ((((8 + (cm_rep_members_size (params)) ) + (cm_rep_members_size (locals)) ) + (8 * temp_pre ) ) <= INT_MAX)) ,
  (cm_slot_list_rep zl locals )
  **  ((( &( "locals_size" ) )) # Int64  |-> retval_2)
  **  (cm_slot_list_rep zp params )
  **  ((( &( "params_size" ) )) # Int64  |-> retval)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
|--
  “ (8 <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= 8) ”
.

Definition cmc_temp_offset_return_wit_1 := 
forall (temp_pre: Z) (fn_pre: Z) (zl: Z) (locals: (@list cm_slot_d)) (zp: Z) (params: (@list cm_slot_d)) (retval: Z) (retval_2: Z) (PreH1 : (cm_rep_members_safe locals )) (PreH2 : (retval_2 = (cm_rep_members_size (locals)))) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1048576)) (PreH5 : (cm_rep_members_safe params )) (PreH6 : (retval = (cm_rep_members_size (params)))) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1048576)) (PreH9 : (cm_rep_members_safe params )) (PreH10 : (cm_rep_members_safe locals )) (PreH11 : (0 <= temp_pre)) (PreH12 : ((((8 + (cm_rep_members_size (params)) ) + (cm_rep_members_size (locals)) ) + (8 * temp_pre ) ) <= INT_MAX)) ,
  (cm_slot_list_rep zl locals )
  **  (cm_slot_list_rep zp params )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
|--
  “ (cm_rep_members_safe params ) ” 
  &&  “ (cm_rep_members_safe locals ) ” 
  &&  “ (0 <= temp_pre) ” 
  &&  “ ((((8 + (cm_rep_members_size (params)) ) + (cm_rep_members_size (locals)) ) + (8 * temp_pre ) ) <= INT_MAX) ” 
  &&  “ ((((8 + retval ) + retval_2 ) + (8 * temp_pre ) ) = (((8 + (cm_rep_members_size (params)) ) + (cm_rep_members_size (locals)) ) + (8 * temp_pre ) )) ”
  &&  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  (cm_slot_list_rep zp params )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl locals )
.

Definition cmc_temp_offset_partial_solve_wit_1_pure := 
forall (temp_pre: Z) (fn_pre: Z) (zl: Z) (locals: (@list cm_slot_d)) (zp: Z) (params: (@list cm_slot_d)) (PreH1 : (cm_rep_members_safe params )) (PreH2 : (cm_rep_members_safe locals )) (PreH3 : (0 <= temp_pre)) (PreH4 : ((((8 + (cm_rep_members_size (params)) ) + (cm_rep_members_size (locals)) ) + (8 * temp_pre ) ) <= INT_MAX)) ,
  ((( &( "params_size" ) )) # Int64  |->_)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  (cm_slot_list_rep zp params )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl locals )
|--
  “ (cm_rep_members_safe params ) ”
.

Definition cmc_temp_offset_partial_solve_wit_1_aux := 
forall (temp_pre: Z) (fn_pre: Z) (zl: Z) (locals: (@list cm_slot_d)) (zp: Z) (params: (@list cm_slot_d)) (PreH1 : (cm_rep_members_safe params )) (PreH2 : (cm_rep_members_safe locals )) (PreH3 : (0 <= temp_pre)) (PreH4 : ((((8 + (cm_rep_members_size (params)) ) + (cm_rep_members_size (locals)) ) + (8 * temp_pre ) ) <= INT_MAX)) ,
  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  (cm_slot_list_rep zp params )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl locals )
|--
  “ (cm_rep_members_safe params ) ” 
  &&  “ (cm_rep_members_safe params ) ” 
  &&  “ (cm_rep_members_safe locals ) ” 
  &&  “ (0 <= temp_pre) ” 
  &&  “ ((((8 + (cm_rep_members_size (params)) ) + (cm_rep_members_size (locals)) ) + (8 * temp_pre ) ) <= INT_MAX) ”
  &&  (cm_slot_list_rep zp params )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl locals )
.

Definition cmc_temp_offset_partial_solve_wit_1 := cmc_temp_offset_partial_solve_wit_1_pure -> cmc_temp_offset_partial_solve_wit_1_aux.

Definition cmc_temp_offset_partial_solve_wit_2_pure := 
forall (temp_pre: Z) (fn_pre: Z) (zl: Z) (locals: (@list cm_slot_d)) (zp: Z) (params: (@list cm_slot_d)) (retval: Z) (PreH1 : (cm_rep_members_safe params )) (PreH2 : (retval = (cm_rep_members_size (params)))) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1048576)) (PreH5 : (cm_rep_members_safe params )) (PreH6 : (cm_rep_members_safe locals )) (PreH7 : (0 <= temp_pre)) (PreH8 : ((((8 + (cm_rep_members_size (params)) ) + (cm_rep_members_size (locals)) ) + (8 * temp_pre ) ) <= INT_MAX)) ,
  ((( &( "locals_size" ) )) # Int64  |->_)
  **  (cm_slot_list_rep zp params )
  **  ((( &( "params_size" ) )) # Int64  |-> retval)
  **  ((( &( "fn" ) )) # Ptr  |-> fn_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_pre)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl locals )
|--
  “ (cm_rep_members_safe locals ) ”
.

Definition cmc_temp_offset_partial_solve_wit_2_aux := 
forall (temp_pre: Z) (fn_pre: Z) (zl: Z) (locals: (@list cm_slot_d)) (zp: Z) (params: (@list cm_slot_d)) (retval: Z) (PreH1 : (cm_rep_members_safe params )) (PreH2 : (retval = (cm_rep_members_size (params)))) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1048576)) (PreH5 : (cm_rep_members_safe params )) (PreH6 : (cm_rep_members_safe locals )) (PreH7 : (0 <= temp_pre)) (PreH8 : ((((8 + (cm_rep_members_size (params)) ) + (cm_rep_members_size (locals)) ) + (8 * temp_pre ) ) <= INT_MAX)) ,
  (cm_slot_list_rep zp params )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
  **  (cm_slot_list_rep zl locals )
|--
  “ (cm_rep_members_safe locals ) ” 
  &&  “ (cm_rep_members_safe params ) ” 
  &&  “ (retval = (cm_rep_members_size (params))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1048576) ” 
  &&  “ (cm_rep_members_safe params ) ” 
  &&  “ (cm_rep_members_safe locals ) ” 
  &&  “ (0 <= temp_pre) ” 
  &&  “ ((((8 + (cm_rep_members_size (params)) ) + (cm_rep_members_size (locals)) ) + (8 * temp_pre ) ) <= INT_MAX) ”
  &&  (cm_slot_list_rep zl locals )
  **  (cm_slot_list_rep zp params )
  **  ((&((fn_pre)  # "cm_function" ->ₛ "params")) # Ptr  |-> zp)
  **  ((&((fn_pre)  # "cm_function" ->ₛ "locals")) # Ptr  |-> zl)
.

Definition cmc_temp_offset_partial_solve_wit_2 := cmc_temp_offset_partial_solve_wit_2_pure -> cmc_temp_offset_partial_solve_wit_2_aux.

(*----- Function cm_normalize_count -----*)

Definition cm_normalize_count_safety_wit_1 := 
forall (ty_pre: Z) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cm_normalize_count_safety_wit_2 := 
forall (ty_pre: Z) (PreH1 : (ty_pre = 1)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (6 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 6) ”
.

Definition cm_normalize_count_safety_wit_3 := 
forall (ty_pre: Z) (PreH1 : (ty_pre <> 1)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "ty" ) )) # Int  |-> ty_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cm_normalize_count_return_wit_1 := 
(
forall (ty_pre: Z) (PreH1 : (ty_pre = 1)) ,
  TT && emp 
|--
  “ (6 = (cm_normalize_code_value (ty_pre))) ”
  &&  emp
) \/
(
forall (ty_pre: Z) (PreH1 : (ty_pre = 1)) ,
  TT && emp 
|--
  “ (6 = (cm_normalize_code_value (1))) ”
  &&  emp
).

Definition cm_normalize_count_return_wit_1_split_goal_1 := 
forall (ty_pre: Z) (PreH1 : (ty_pre = 1)) ,
  (6 = (cm_normalize_code_value (1)))
.

Definition cm_normalize_count_return_wit_2 := 
(
forall (ty_pre: Z) (PreH1 : (ty_pre <> 1)) ,
  TT && emp 
|--
  “ (0 = (cm_normalize_code_value (ty_pre))) ”
  &&  emp
) \/
(
forall (ty_pre: Z) (PreH1 : (ty_pre <> 1)) ,
  TT && emp 
|--
  “ (0 = (cm_normalize_code_value (ty_pre))) ”
  &&  emp
).

Definition cm_normalize_count_return_wit_2_split_goal_1 := 
forall (ty_pre: Z) (PreH1 : (ty_pre <> 1)) ,
  (0 = (cm_normalize_code_value (ty_pre)))
.

Module Type VC_Correct.


Axiom proof_of_cm_max_return_wit_1 : cm_max_return_wit_1.
Axiom proof_of_cm_max_return_wit_2 : cm_max_return_wit_2.
Axiom proof_of_cmc_is_pointer_safety_wit_1 : cmc_is_pointer_safety_wit_1.
Axiom proof_of_cmc_is_pointer_safety_wit_2 : cmc_is_pointer_safety_wit_2.
Axiom proof_of_cmc_is_pointer_safety_wit_3 : cmc_is_pointer_safety_wit_3.
Axiom proof_of_cmc_is_pointer_return_wit_1 : cmc_is_pointer_return_wit_1.
Axiom proof_of_cmc_is_pointer_return_wit_2 : cmc_is_pointer_return_wit_2.
Axiom proof_of_cmc_is_pointer_value_return_wit_1 : cmc_is_pointer_value_return_wit_1.
Axiom proof_of_cmc_is_pointer_value_partial_solve_wit_1 : cmc_is_pointer_value_partial_solve_wit_1.
Axiom proof_of_cmc_pointee_safety_wit_1 : cmc_pointee_safety_wit_1.
Axiom proof_of_cmc_pointee_safety_wit_2 : cmc_pointee_safety_wit_2.
Axiom proof_of_cmc_pointee_return_wit_1 : cmc_pointee_return_wit_1.
Axiom proof_of_cmc_leaf_size_safety_wit_1 : cmc_leaf_size_safety_wit_1.
Axiom proof_of_cmc_leaf_size_safety_wit_2 : cmc_leaf_size_safety_wit_2.
Axiom proof_of_cmc_leaf_size_safety_wit_3 : cmc_leaf_size_safety_wit_3.
Axiom proof_of_cmc_leaf_size_safety_wit_4 : cmc_leaf_size_safety_wit_4.
Axiom proof_of_cmc_leaf_size_safety_wit_5 : cmc_leaf_size_safety_wit_5.
Axiom proof_of_cmc_leaf_size_safety_wit_6 : cmc_leaf_size_safety_wit_6.
Axiom proof_of_cmc_leaf_size_safety_wit_7 : cmc_leaf_size_safety_wit_7.
Axiom proof_of_cmc_leaf_size_return_wit_1 : cmc_leaf_size_return_wit_1.
Axiom proof_of_cmc_leaf_size_return_wit_2 : cmc_leaf_size_return_wit_2.
Axiom proof_of_cmc_leaf_size_return_wit_3 : cmc_leaf_size_return_wit_3.
Axiom proof_of_cmc_leaf_size_return_wit_4 : cmc_leaf_size_return_wit_4.
Axiom proof_of_cmc_code_slot_size_safety_wit_1 : cmc_code_slot_size_safety_wit_1.
Axiom proof_of_cmc_code_slot_size_safety_wit_2 : cmc_code_slot_size_safety_wit_2.
Axiom proof_of_cmc_code_slot_size_return_wit_1 : cmc_code_slot_size_return_wit_1.
Axiom proof_of_cmc_code_slot_size_return_wit_2 : cmc_code_slot_size_return_wit_2.
Axiom proof_of_cmc_code_slot_size_partial_solve_wit_1 : cmc_code_slot_size_partial_solve_wit_1.
Axiom proof_of_cmc_members_size_safety_wit_1 : cmc_members_size_safety_wit_1.
Axiom proof_of_cmc_members_size_safety_wit_2 : cmc_members_size_safety_wit_2.
Axiom proof_of_cmc_members_size_safety_wit_3 : cmc_members_size_safety_wit_3.
Axiom proof_of_cmc_members_size_entail_wit_1 : cmc_members_size_entail_wit_1.
Axiom proof_of_cmc_members_size_return_wit_1 : cmc_members_size_return_wit_1.
Axiom proof_of_cmc_members_size_return_wit_2 : cmc_members_size_return_wit_2.
Axiom proof_of_cmc_members_size_partial_solve_wit_1 : cmc_members_size_partial_solve_wit_1.
Axiom proof_of_cmc_members_size_partial_solve_wit_2_pure : cmc_members_size_partial_solve_wit_2_pure.
Axiom proof_of_cmc_members_size_partial_solve_wit_2 : cmc_members_size_partial_solve_wit_2.
Axiom proof_of_cmc_struct_size_at_safety_wit_1 : cmc_struct_size_at_safety_wit_1.
Axiom proof_of_cmc_struct_size_at_safety_wit_2 : cmc_struct_size_at_safety_wit_2.
Axiom proof_of_cmc_struct_size_at_safety_wit_3 : cmc_struct_size_at_safety_wit_3.
Axiom proof_of_cmc_struct_size_at_safety_wit_4 : cmc_struct_size_at_safety_wit_4.
Axiom proof_of_cmc_struct_size_at_safety_wit_5 : cmc_struct_size_at_safety_wit_5.
Axiom proof_of_cmc_struct_size_at_entail_wit_1 : cmc_struct_size_at_entail_wit_1.
Axiom proof_of_cmc_struct_size_at_return_wit_1 : cmc_struct_size_at_return_wit_1.
Axiom proof_of_cmc_struct_size_at_return_wit_2 : cmc_struct_size_at_return_wit_2.
Axiom proof_of_cmc_struct_size_at_return_wit_3 : cmc_struct_size_at_return_wit_3.
Axiom proof_of_cmc_struct_size_at_partial_solve_wit_1_pure : cmc_struct_size_at_partial_solve_wit_1_pure.
Axiom proof_of_cmc_struct_size_at_partial_solve_wit_1 : cmc_struct_size_at_partial_solve_wit_1.
Axiom proof_of_cmc_struct_size_at_partial_solve_wit_2_pure : cmc_struct_size_at_partial_solve_wit_2_pure.
Axiom proof_of_cmc_struct_size_at_partial_solve_wit_2 : cmc_struct_size_at_partial_solve_wit_2.
Axiom proof_of_cmc_nonzero_safety_wit_1 : cmc_nonzero_safety_wit_1.
Axiom proof_of_cmc_nonzero_safety_wit_2 : cmc_nonzero_safety_wit_2.
Axiom proof_of_cmc_nonzero_safety_wit_3 : cmc_nonzero_safety_wit_3.
Axiom proof_of_cmc_nonzero_return_wit_1 : cmc_nonzero_return_wit_1.
Axiom proof_of_cmc_nonzero_return_wit_2 : cmc_nonzero_return_wit_2.
Axiom proof_of_cmc_global_array_at_safety_wit_1 : cmc_global_array_at_safety_wit_1.
Axiom proof_of_cmc_global_array_at_safety_wit_2 : cmc_global_array_at_safety_wit_2.
Axiom proof_of_cmc_global_array_at_safety_wit_3 : cmc_global_array_at_safety_wit_3.
Axiom proof_of_cmc_global_array_at_safety_wit_4 : cmc_global_array_at_safety_wit_4.
Axiom proof_of_cmc_global_array_at_safety_wit_5 : cmc_global_array_at_safety_wit_5.
Axiom proof_of_cmc_global_array_at_entail_wit_1 : cmc_global_array_at_entail_wit_1.
Axiom proof_of_cmc_global_array_at_return_wit_1 : cmc_global_array_at_return_wit_1.
Axiom proof_of_cmc_global_array_at_return_wit_2 : cmc_global_array_at_return_wit_2.
Axiom proof_of_cmc_global_array_at_return_wit_3 : cmc_global_array_at_return_wit_3.
Axiom proof_of_cmc_global_array_at_partial_solve_wit_1 : cmc_global_array_at_partial_solve_wit_1.
Axiom proof_of_cmc_global_array_at_partial_solve_wit_2_pure : cmc_global_array_at_partial_solve_wit_2_pure.
Axiom proof_of_cmc_global_array_at_partial_solve_wit_2 : cmc_global_array_at_partial_solve_wit_2.
Axiom proof_of_cmc_slot_array_at_safety_wit_1 : cmc_slot_array_at_safety_wit_1.
Axiom proof_of_cmc_slot_array_at_safety_wit_2 : cmc_slot_array_at_safety_wit_2.
Axiom proof_of_cmc_slot_array_at_safety_wit_3 : cmc_slot_array_at_safety_wit_3.
Axiom proof_of_cmc_slot_array_at_safety_wit_4 : cmc_slot_array_at_safety_wit_4.
Axiom proof_of_cmc_slot_array_at_safety_wit_5 : cmc_slot_array_at_safety_wit_5.
Axiom proof_of_cmc_slot_array_at_entail_wit_1 : cmc_slot_array_at_entail_wit_1.
Axiom proof_of_cmc_slot_array_at_return_wit_1 : cmc_slot_array_at_return_wit_1.
Axiom proof_of_cmc_slot_array_at_return_wit_2 : cmc_slot_array_at_return_wit_2.
Axiom proof_of_cmc_slot_array_at_return_wit_3 : cmc_slot_array_at_return_wit_3.
Axiom proof_of_cmc_slot_array_at_partial_solve_wit_1 : cmc_slot_array_at_partial_solve_wit_1.
Axiom proof_of_cmc_slot_array_at_partial_solve_wit_2_pure : cmc_slot_array_at_partial_solve_wit_2_pure.
Axiom proof_of_cmc_slot_array_at_partial_solve_wit_2 : cmc_slot_array_at_partial_solve_wit_2.
Axiom proof_of_cmc_slot_type_at_safety_wit_1 : cmc_slot_type_at_safety_wit_1.
Axiom proof_of_cmc_slot_type_at_safety_wit_2 : cmc_slot_type_at_safety_wit_2.
Axiom proof_of_cmc_slot_type_at_safety_wit_3 : cmc_slot_type_at_safety_wit_3.
Axiom proof_of_cmc_slot_type_at_safety_wit_4 : cmc_slot_type_at_safety_wit_4.
Axiom proof_of_cmc_slot_type_at_safety_wit_5 : cmc_slot_type_at_safety_wit_5.
Axiom proof_of_cmc_slot_type_at_entail_wit_1 : cmc_slot_type_at_entail_wit_1.
Axiom proof_of_cmc_slot_type_at_return_wit_1 : cmc_slot_type_at_return_wit_1.
Axiom proof_of_cmc_slot_type_at_return_wit_2 : cmc_slot_type_at_return_wit_2.
Axiom proof_of_cmc_slot_type_at_return_wit_3 : cmc_slot_type_at_return_wit_3.
Axiom proof_of_cmc_slot_type_at_partial_solve_wit_1_pure : cmc_slot_type_at_partial_solve_wit_1_pure.
Axiom proof_of_cmc_slot_type_at_partial_solve_wit_1 : cmc_slot_type_at_partial_solve_wit_1.
Axiom proof_of_cmc_member_array_at_safety_wit_1 : cmc_member_array_at_safety_wit_1.
Axiom proof_of_cmc_member_array_at_safety_wit_2 : cmc_member_array_at_safety_wit_2.
Axiom proof_of_cmc_member_array_at_safety_wit_3 : cmc_member_array_at_safety_wit_3.
Axiom proof_of_cmc_member_array_at_safety_wit_4 : cmc_member_array_at_safety_wit_4.
Axiom proof_of_cmc_member_array_at_safety_wit_5 : cmc_member_array_at_safety_wit_5.
Axiom proof_of_cmc_member_array_at_entail_wit_1 : cmc_member_array_at_entail_wit_1.
Axiom proof_of_cmc_member_array_at_return_wit_1 : cmc_member_array_at_return_wit_1.
Axiom proof_of_cmc_member_array_at_return_wit_2 : cmc_member_array_at_return_wit_2.
Axiom proof_of_cmc_member_array_at_return_wit_3 : cmc_member_array_at_return_wit_3.
Axiom proof_of_cmc_member_array_at_partial_solve_wit_1 : cmc_member_array_at_partial_solve_wit_1.
Axiom proof_of_cmc_member_array_at_partial_solve_wit_2_pure : cmc_member_array_at_partial_solve_wit_2_pure.
Axiom proof_of_cmc_member_array_at_partial_solve_wit_2 : cmc_member_array_at_partial_solve_wit_2.
Axiom proof_of_cmc_type_size_at_safety_wit_1 : cmc_type_size_at_safety_wit_1.
Axiom proof_of_cmc_type_size_at_safety_wit_2 : cmc_type_size_at_safety_wit_2.
Axiom proof_of_cmc_type_size_at_safety_wit_3 : cmc_type_size_at_safety_wit_3.
Axiom proof_of_cmc_type_size_at_safety_wit_4 : cmc_type_size_at_safety_wit_4.
Axiom proof_of_cmc_type_size_at_safety_wit_5 : cmc_type_size_at_safety_wit_5.
Axiom proof_of_cmc_type_size_at_safety_wit_6 : cmc_type_size_at_safety_wit_6.
Axiom proof_of_cmc_type_size_at_safety_wit_7 : cmc_type_size_at_safety_wit_7.
Axiom proof_of_cmc_type_size_at_safety_wit_8 : cmc_type_size_at_safety_wit_8.
Axiom proof_of_cmc_type_size_at_return_wit_1 : cmc_type_size_at_return_wit_1.
Axiom proof_of_cmc_type_size_at_return_wit_2 : cmc_type_size_at_return_wit_2.
Axiom proof_of_cmc_type_size_at_return_wit_3 : cmc_type_size_at_return_wit_3.
Axiom proof_of_cmc_type_size_at_return_wit_4 : cmc_type_size_at_return_wit_4.
Axiom proof_of_cmc_type_size_at_partial_solve_wit_1_pure : cmc_type_size_at_partial_solve_wit_1_pure.
Axiom proof_of_cmc_type_size_at_partial_solve_wit_1 : cmc_type_size_at_partial_solve_wit_1.
Axiom proof_of_cmc_slots_size_safety_wit_1 : cmc_slots_size_safety_wit_1.
Axiom proof_of_cmc_slots_size_safety_wit_2 : cmc_slots_size_safety_wit_2.
Axiom proof_of_cmc_slots_size_safety_wit_3 : cmc_slots_size_safety_wit_3.
Axiom proof_of_cmc_slots_size_entail_wit_1 : cmc_slots_size_entail_wit_1.
Axiom proof_of_cmc_slots_size_return_wit_1 : cmc_slots_size_return_wit_1.
Axiom proof_of_cmc_slots_size_return_wit_2 : cmc_slots_size_return_wit_2.
Axiom proof_of_cmc_slots_size_partial_solve_wit_1 : cmc_slots_size_partial_solve_wit_1.
Axiom proof_of_cmc_slots_size_partial_solve_wit_2_pure : cmc_slots_size_partial_solve_wit_2_pure.
Axiom proof_of_cmc_slots_size_partial_solve_wit_2 : cmc_slots_size_partial_solve_wit_2.
Axiom proof_of_cmc_slots_prefix_safety_wit_1 : cmc_slots_prefix_safety_wit_1.
Axiom proof_of_cmc_slots_prefix_safety_wit_2 : cmc_slots_prefix_safety_wit_2.
Axiom proof_of_cmc_slots_prefix_safety_wit_3 : cmc_slots_prefix_safety_wit_3.
Axiom proof_of_cmc_slots_prefix_safety_wit_4 : cmc_slots_prefix_safety_wit_4.
Axiom proof_of_cmc_slots_prefix_safety_wit_5 : cmc_slots_prefix_safety_wit_5.
Axiom proof_of_cmc_slots_prefix_safety_wit_6 : cmc_slots_prefix_safety_wit_6.
Axiom proof_of_cmc_slots_prefix_safety_wit_7 : cmc_slots_prefix_safety_wit_7.
Axiom proof_of_cmc_slots_prefix_entail_wit_1 : cmc_slots_prefix_entail_wit_1.
Axiom proof_of_cmc_slots_prefix_return_wit_1 : cmc_slots_prefix_return_wit_1.
Axiom proof_of_cmc_slots_prefix_return_wit_2 : cmc_slots_prefix_return_wit_2.
Axiom proof_of_cmc_slots_prefix_return_wit_3 : cmc_slots_prefix_return_wit_3.
Axiom proof_of_cmc_slots_prefix_partial_solve_wit_1 : cmc_slots_prefix_partial_solve_wit_1.
Axiom proof_of_cmc_slots_prefix_partial_solve_wit_2_pure : cmc_slots_prefix_partial_solve_wit_2_pure.
Axiom proof_of_cmc_slots_prefix_partial_solve_wit_2 : cmc_slots_prefix_partial_solve_wit_2.
Axiom proof_of_cmc_members_prefix_safety_wit_1 : cmc_members_prefix_safety_wit_1.
Axiom proof_of_cmc_members_prefix_safety_wit_2 : cmc_members_prefix_safety_wit_2.
Axiom proof_of_cmc_members_prefix_safety_wit_3 : cmc_members_prefix_safety_wit_3.
Axiom proof_of_cmc_members_prefix_safety_wit_4 : cmc_members_prefix_safety_wit_4.
Axiom proof_of_cmc_members_prefix_safety_wit_5 : cmc_members_prefix_safety_wit_5.
Axiom proof_of_cmc_members_prefix_safety_wit_6 : cmc_members_prefix_safety_wit_6.
Axiom proof_of_cmc_members_prefix_safety_wit_7 : cmc_members_prefix_safety_wit_7.
Axiom proof_of_cmc_members_prefix_entail_wit_1 : cmc_members_prefix_entail_wit_1.
Axiom proof_of_cmc_members_prefix_return_wit_1 : cmc_members_prefix_return_wit_1.
Axiom proof_of_cmc_members_prefix_return_wit_2 : cmc_members_prefix_return_wit_2.
Axiom proof_of_cmc_members_prefix_return_wit_3 : cmc_members_prefix_return_wit_3.
Axiom proof_of_cmc_members_prefix_partial_solve_wit_1 : cmc_members_prefix_partial_solve_wit_1.
Axiom proof_of_cmc_members_prefix_partial_solve_wit_2_pure : cmc_members_prefix_partial_solve_wit_2_pure.
Axiom proof_of_cmc_members_prefix_partial_solve_wit_2 : cmc_members_prefix_partial_solve_wit_2.
Axiom proof_of_cmc_member_offset_at_safety_wit_1 : cmc_member_offset_at_safety_wit_1.
Axiom proof_of_cmc_member_offset_at_safety_wit_2 : cmc_member_offset_at_safety_wit_2.
Axiom proof_of_cmc_member_offset_at_safety_wit_3 : cmc_member_offset_at_safety_wit_3.
Axiom proof_of_cmc_member_offset_at_safety_wit_4 : cmc_member_offset_at_safety_wit_4.
Axiom proof_of_cmc_member_offset_at_safety_wit_5 : cmc_member_offset_at_safety_wit_5.
Axiom proof_of_cmc_member_offset_at_entail_wit_1 : cmc_member_offset_at_entail_wit_1.
Axiom proof_of_cmc_member_offset_at_return_wit_1 : cmc_member_offset_at_return_wit_1.
Axiom proof_of_cmc_member_offset_at_return_wit_2 : cmc_member_offset_at_return_wit_2.
Axiom proof_of_cmc_member_offset_at_return_wit_3 : cmc_member_offset_at_return_wit_3.
Axiom proof_of_cmc_member_offset_at_partial_solve_wit_1_pure : cmc_member_offset_at_partial_solve_wit_1_pure.
Axiom proof_of_cmc_member_offset_at_partial_solve_wit_1 : cmc_member_offset_at_partial_solve_wit_1.
Axiom proof_of_cmc_member_offset_at_partial_solve_wit_2_pure : cmc_member_offset_at_partial_solve_wit_2_pure.
Axiom proof_of_cmc_member_offset_at_partial_solve_wit_2 : cmc_member_offset_at_partial_solve_wit_2.
Axiom proof_of_cmc_struct_member_array_at_safety_wit_1 : cmc_struct_member_array_at_safety_wit_1.
Axiom proof_of_cmc_struct_member_array_at_safety_wit_2 : cmc_struct_member_array_at_safety_wit_2.
Axiom proof_of_cmc_struct_member_array_at_safety_wit_3 : cmc_struct_member_array_at_safety_wit_3.
Axiom proof_of_cmc_struct_member_array_at_safety_wit_4 : cmc_struct_member_array_at_safety_wit_4.
Axiom proof_of_cmc_struct_member_array_at_safety_wit_5 : cmc_struct_member_array_at_safety_wit_5.
Axiom proof_of_cmc_struct_member_array_at_entail_wit_1 : cmc_struct_member_array_at_entail_wit_1.
Axiom proof_of_cmc_struct_member_array_at_return_wit_1 : cmc_struct_member_array_at_return_wit_1.
Axiom proof_of_cmc_struct_member_array_at_return_wit_2 : cmc_struct_member_array_at_return_wit_2.
Axiom proof_of_cmc_struct_member_array_at_return_wit_3 : cmc_struct_member_array_at_return_wit_3.
Axiom proof_of_cmc_struct_member_array_at_partial_solve_wit_1_pure : cmc_struct_member_array_at_partial_solve_wit_1_pure.
Axiom proof_of_cmc_struct_member_array_at_partial_solve_wit_1 : cmc_struct_member_array_at_partial_solve_wit_1.
Axiom proof_of_cmc_struct_member_array_at_partial_solve_wit_2_pure : cmc_struct_member_array_at_partial_solve_wit_2_pure.
Axiom proof_of_cmc_struct_member_array_at_partial_solve_wit_2 : cmc_struct_member_array_at_partial_solve_wit_2.
Axiom proof_of_cmc_globals_size_safety_wit_1 : cmc_globals_size_safety_wit_1.
Axiom proof_of_cmc_globals_size_safety_wit_2 : cmc_globals_size_safety_wit_2.
Axiom proof_of_cmc_globals_size_safety_wit_3 : cmc_globals_size_safety_wit_3.
Axiom proof_of_cmc_globals_size_entail_wit_1 : cmc_globals_size_entail_wit_1.
Axiom proof_of_cmc_globals_size_return_wit_1 : cmc_globals_size_return_wit_1.
Axiom proof_of_cmc_globals_size_return_wit_2 : cmc_globals_size_return_wit_2.
Axiom proof_of_cmc_globals_size_partial_solve_wit_1 : cmc_globals_size_partial_solve_wit_1.
Axiom proof_of_cmc_globals_size_partial_solve_wit_2_pure : cmc_globals_size_partial_solve_wit_2_pure.
Axiom proof_of_cmc_globals_size_partial_solve_wit_2 : cmc_globals_size_partial_solve_wit_2.
Axiom proof_of_cmc_globals_prefix_safety_wit_1 : cmc_globals_prefix_safety_wit_1.
Axiom proof_of_cmc_globals_prefix_safety_wit_2 : cmc_globals_prefix_safety_wit_2.
Axiom proof_of_cmc_globals_prefix_safety_wit_3 : cmc_globals_prefix_safety_wit_3.
Axiom proof_of_cmc_globals_prefix_safety_wit_4 : cmc_globals_prefix_safety_wit_4.
Axiom proof_of_cmc_globals_prefix_safety_wit_5 : cmc_globals_prefix_safety_wit_5.
Axiom proof_of_cmc_globals_prefix_safety_wit_6 : cmc_globals_prefix_safety_wit_6.
Axiom proof_of_cmc_globals_prefix_safety_wit_7 : cmc_globals_prefix_safety_wit_7.
Axiom proof_of_cmc_globals_prefix_entail_wit_1 : cmc_globals_prefix_entail_wit_1.
Axiom proof_of_cmc_globals_prefix_return_wit_1 : cmc_globals_prefix_return_wit_1.
Axiom proof_of_cmc_globals_prefix_return_wit_2 : cmc_globals_prefix_return_wit_2.
Axiom proof_of_cmc_globals_prefix_return_wit_3 : cmc_globals_prefix_return_wit_3.
Axiom proof_of_cmc_globals_prefix_partial_solve_wit_1 : cmc_globals_prefix_partial_solve_wit_1.
Axiom proof_of_cmc_globals_prefix_partial_solve_wit_2_pure : cmc_globals_prefix_partial_solve_wit_2_pure.
Axiom proof_of_cmc_globals_prefix_partial_solve_wit_2 : cmc_globals_prefix_partial_solve_wit_2.
Axiom proof_of_cmc_strings_size_safety_wit_1 : cmc_strings_size_safety_wit_1.
Axiom proof_of_cmc_strings_size_safety_wit_2 : cmc_strings_size_safety_wit_2.
Axiom proof_of_cmc_strings_size_safety_wit_3 : cmc_strings_size_safety_wit_3.
Axiom proof_of_cmc_strings_size_safety_wit_4 : cmc_strings_size_safety_wit_4.
Axiom proof_of_cmc_strings_size_safety_wit_5 : cmc_strings_size_safety_wit_5.
Axiom proof_of_cmc_strings_size_entail_wit_1 : cmc_strings_size_entail_wit_1.
Axiom proof_of_cmc_strings_size_return_wit_1 : cmc_strings_size_return_wit_1.
Axiom proof_of_cmc_strings_size_return_wit_2 : cmc_strings_size_return_wit_2.
Axiom proof_of_cmc_strings_size_partial_solve_wit_1_pure : cmc_strings_size_partial_solve_wit_1_pure.
Axiom proof_of_cmc_strings_size_partial_solve_wit_1 : cmc_strings_size_partial_solve_wit_1.
Axiom proof_of_cmc_strings_prefix_safety_wit_1 : cmc_strings_prefix_safety_wit_1.
Axiom proof_of_cmc_strings_prefix_safety_wit_2 : cmc_strings_prefix_safety_wit_2.
Axiom proof_of_cmc_strings_prefix_safety_wit_3 : cmc_strings_prefix_safety_wit_3.
Axiom proof_of_cmc_strings_prefix_safety_wit_4 : cmc_strings_prefix_safety_wit_4.
Axiom proof_of_cmc_strings_prefix_safety_wit_5 : cmc_strings_prefix_safety_wit_5.
Axiom proof_of_cmc_strings_prefix_safety_wit_6 : cmc_strings_prefix_safety_wit_6.
Axiom proof_of_cmc_strings_prefix_safety_wit_7 : cmc_strings_prefix_safety_wit_7.
Axiom proof_of_cmc_strings_prefix_safety_wit_8 : cmc_strings_prefix_safety_wit_8.
Axiom proof_of_cmc_strings_prefix_safety_wit_9 : cmc_strings_prefix_safety_wit_9.
Axiom proof_of_cmc_strings_prefix_entail_wit_1 : cmc_strings_prefix_entail_wit_1.
Axiom proof_of_cmc_strings_prefix_return_wit_1 : cmc_strings_prefix_return_wit_1.
Axiom proof_of_cmc_strings_prefix_return_wit_2 : cmc_strings_prefix_return_wit_2.
Axiom proof_of_cmc_strings_prefix_return_wit_3 : cmc_strings_prefix_return_wit_3.
Axiom proof_of_cmc_strings_prefix_partial_solve_wit_1_pure : cmc_strings_prefix_partial_solve_wit_1_pure.
Axiom proof_of_cmc_strings_prefix_partial_solve_wit_1 : cmc_strings_prefix_partial_solve_wit_1.
Axiom proof_of_cmc_global_address_safety_wit_1 : cmc_global_address_safety_wit_1.
Axiom proof_of_cmc_global_address_safety_wit_2 : cmc_global_address_safety_wit_2.
Axiom proof_of_cmc_global_address_return_wit_1 : cmc_global_address_return_wit_1.
Axiom proof_of_cmc_global_address_partial_solve_wit_1_pure : cmc_global_address_partial_solve_wit_1_pure.
Axiom proof_of_cmc_global_address_partial_solve_wit_1 : cmc_global_address_partial_solve_wit_1.
Axiom proof_of_cmc_string_address_safety_wit_1 : cmc_string_address_safety_wit_1.
Axiom proof_of_cmc_string_address_safety_wit_2 : cmc_string_address_safety_wit_2.
Axiom proof_of_cmc_string_address_safety_wit_3 : cmc_string_address_safety_wit_3.
Axiom proof_of_cmc_string_address_return_wit_1 : cmc_string_address_return_wit_1.
Axiom proof_of_cmc_string_address_partial_solve_wit_1_pure : cmc_string_address_partial_solve_wit_1_pure.
Axiom proof_of_cmc_string_address_partial_solve_wit_1 : cmc_string_address_partial_solve_wit_1.
Axiom proof_of_cmc_string_address_partial_solve_wit_2_pure : cmc_string_address_partial_solve_wit_2_pure.
Axiom proof_of_cmc_string_address_partial_solve_wit_2 : cmc_string_address_partial_solve_wit_2.
Axiom proof_of_cmc_binding_array_value_safety_wit_1 : cmc_binding_array_value_safety_wit_1.
Axiom proof_of_cmc_binding_array_value_safety_wit_2 : cmc_binding_array_value_safety_wit_2.
Axiom proof_of_cmc_binding_array_value_safety_wit_3 : cmc_binding_array_value_safety_wit_3.
Axiom proof_of_cmc_binding_array_value_return_wit_1 : cmc_binding_array_value_return_wit_1.
Axiom proof_of_cmc_binding_array_value_return_wit_2 : cmc_binding_array_value_return_wit_2.
Axiom proof_of_cmc_binding_array_value_return_wit_3 : cmc_binding_array_value_return_wit_3.
Axiom proof_of_cmc_binding_array_value_partial_solve_wit_1_pure : cmc_binding_array_value_partial_solve_wit_1_pure.
Axiom proof_of_cmc_binding_array_value_partial_solve_wit_1 : cmc_binding_array_value_partial_solve_wit_1.
Axiom proof_of_cmc_binding_array_value_partial_solve_wit_2_pure : cmc_binding_array_value_partial_solve_wit_2_pure.
Axiom proof_of_cmc_binding_array_value_partial_solve_wit_2 : cmc_binding_array_value_partial_solve_wit_2.
Axiom proof_of_cmc_binding_array_return_wit_1 : cmc_binding_array_return_wit_1.
Axiom proof_of_cmc_binding_array_partial_solve_wit_1_pure : cmc_binding_array_partial_solve_wit_1_pure.
Axiom proof_of_cmc_binding_array_partial_solve_wit_1 : cmc_binding_array_partial_solve_wit_1.
Axiom proof_of_cmc_member_array_safety_wit_1 : cmc_member_array_safety_wit_1.
Axiom proof_of_cmc_member_array_safety_wit_2 : cmc_member_array_safety_wit_2.
Axiom proof_of_cmc_member_array_safety_wit_3 : cmc_member_array_safety_wit_3.
Axiom proof_of_cmc_member_array_safety_wit_4 : cmc_member_array_safety_wit_4.
Axiom proof_of_cmc_member_array_return_wit_1 : cmc_member_array_return_wit_1.
Axiom proof_of_cmc_member_array_partial_solve_wit_1_pure : cmc_member_array_partial_solve_wit_1_pure.
Axiom proof_of_cmc_member_array_partial_solve_wit_1 : cmc_member_array_partial_solve_wit_1.
Axiom proof_of_cmc_member_array_partial_solve_wit_2_pure : cmc_member_array_partial_solve_wit_2_pure.
Axiom proof_of_cmc_member_array_partial_solve_wit_2 : cmc_member_array_partial_solve_wit_2.
Axiom proof_of_cmc_member_array_value_return_wit_1 : cmc_member_array_value_return_wit_1.
Axiom proof_of_cmc_member_array_value_partial_solve_wit_1_pure : cmc_member_array_value_partial_solve_wit_1_pure.
Axiom proof_of_cmc_member_array_value_partial_solve_wit_1 : cmc_member_array_value_partial_solve_wit_1.
Axiom proof_of_cm_args_length_safety_wit_1 : cm_args_length_safety_wit_1.
Axiom proof_of_cm_args_length_safety_wit_2 : cm_args_length_safety_wit_2.
Axiom proof_of_cm_args_length_safety_wit_3 : cm_args_length_safety_wit_3.
Axiom proof_of_cm_args_length_safety_wit_4 : cm_args_length_safety_wit_4.
Axiom proof_of_cm_args_length_entail_wit_1 : cm_args_length_entail_wit_1.
Axiom proof_of_cm_args_length_return_wit_1 : cm_args_length_return_wit_1.
Axiom proof_of_cm_args_length_return_wit_2 : cm_args_length_return_wit_2.
Axiom proof_of_cm_args_length_partial_solve_wit_1_pure : cm_args_length_partial_solve_wit_1_pure.
Axiom proof_of_cm_args_length_partial_solve_wit_1 : cm_args_length_partial_solve_wit_1.
Axiom proof_of_cmc_args_tpair_safety_wit_1 : cmc_args_tpair_safety_wit_1.
Axiom proof_of_cmc_args_tpair_safety_wit_2 : cmc_args_tpair_safety_wit_2.
Axiom proof_of_cmc_args_tpair_safety_wit_3 : cmc_args_tpair_safety_wit_3.
Axiom proof_of_cmc_args_tpair_safety_wit_4 : cmc_args_tpair_safety_wit_4.
Axiom proof_of_cmc_args_tpair_safety_wit_5 : cmc_args_tpair_safety_wit_5.
Axiom proof_of_cmc_args_tpair_entail_wit_1 : cmc_args_tpair_entail_wit_1.
Axiom proof_of_cmc_args_tpair_return_wit_1 : cmc_args_tpair_return_wit_1.
Axiom proof_of_cmc_args_tpair_return_wit_2 : cmc_args_tpair_return_wit_2.
Axiom proof_of_cmc_args_tpair_partial_solve_wit_1_pure : cmc_args_tpair_partial_solve_wit_1_pure.
Axiom proof_of_cmc_args_tpair_partial_solve_wit_1 : cmc_args_tpair_partial_solve_wit_1.
Axiom proof_of_cmc_args_tpair_partial_solve_wit_2_pure : cmc_args_tpair_partial_solve_wit_2_pure.
Axiom proof_of_cmc_args_tpair_partial_solve_wit_2 : cmc_args_tpair_partial_solve_wit_2.
Axiom proof_of_cmc_args_tpair_partial_solve_wit_3 : cmc_args_tpair_partial_solve_wit_3.
Axiom proof_of_cm_expr_temps_safety_wit_1 : cm_expr_temps_safety_wit_1.
Axiom proof_of_cm_expr_temps_safety_wit_2 : cm_expr_temps_safety_wit_2.
Axiom proof_of_cm_expr_temps_safety_wit_3 : cm_expr_temps_safety_wit_3.
Axiom proof_of_cm_expr_temps_safety_wit_4 : cm_expr_temps_safety_wit_4.
Axiom proof_of_cm_expr_temps_safety_wit_5 : cm_expr_temps_safety_wit_5.
Axiom proof_of_cm_expr_temps_safety_wit_6 : cm_expr_temps_safety_wit_6.
Axiom proof_of_cm_expr_temps_safety_wit_7 : cm_expr_temps_safety_wit_7.
Axiom proof_of_cm_expr_temps_safety_wit_8 : cm_expr_temps_safety_wit_8.
Axiom proof_of_cm_expr_temps_safety_wit_9 : cm_expr_temps_safety_wit_9.
Axiom proof_of_cm_expr_temps_safety_wit_10 : cm_expr_temps_safety_wit_10.
Axiom proof_of_cm_expr_temps_safety_wit_11 : cm_expr_temps_safety_wit_11.
Axiom proof_of_cm_expr_temps_safety_wit_12 : cm_expr_temps_safety_wit_12.
Axiom proof_of_cm_expr_temps_safety_wit_13 : cm_expr_temps_safety_wit_13.
Axiom proof_of_cm_expr_temps_safety_wit_14 : cm_expr_temps_safety_wit_14.
Axiom proof_of_cm_expr_temps_safety_wit_15 : cm_expr_temps_safety_wit_15.
Axiom proof_of_cm_expr_temps_safety_wit_16 : cm_expr_temps_safety_wit_16.
Axiom proof_of_cm_expr_temps_safety_wit_17 : cm_expr_temps_safety_wit_17.
Axiom proof_of_cm_expr_temps_safety_wit_18 : cm_expr_temps_safety_wit_18.
Axiom proof_of_cm_expr_temps_safety_wit_19 : cm_expr_temps_safety_wit_19.
Axiom proof_of_cm_expr_temps_safety_wit_20 : cm_expr_temps_safety_wit_20.
Axiom proof_of_cm_expr_temps_safety_wit_21 : cm_expr_temps_safety_wit_21.
Axiom proof_of_cm_expr_temps_safety_wit_22 : cm_expr_temps_safety_wit_22.
Axiom proof_of_cm_expr_temps_safety_wit_23 : cm_expr_temps_safety_wit_23.
Axiom proof_of_cm_expr_temps_safety_wit_24 : cm_expr_temps_safety_wit_24.
Axiom proof_of_cm_expr_temps_safety_wit_25 : cm_expr_temps_safety_wit_25.
Axiom proof_of_cm_expr_temps_safety_wit_26 : cm_expr_temps_safety_wit_26.
Axiom proof_of_cm_expr_temps_safety_wit_27 : cm_expr_temps_safety_wit_27.
Axiom proof_of_cm_expr_temps_entail_wit_1 : cm_expr_temps_entail_wit_1.
Axiom proof_of_cm_expr_temps_entail_wit_2 : cm_expr_temps_entail_wit_2.
Axiom proof_of_cm_expr_temps_entail_wit_3 : cm_expr_temps_entail_wit_3.
Axiom proof_of_cm_expr_temps_entail_wit_4 : cm_expr_temps_entail_wit_4.
Axiom proof_of_cm_expr_temps_entail_wit_5 : cm_expr_temps_entail_wit_5.
Axiom proof_of_cm_expr_temps_entail_wit_6 : cm_expr_temps_entail_wit_6.
Axiom proof_of_cm_expr_temps_entail_wit_7 : cm_expr_temps_entail_wit_7.
Axiom proof_of_cm_expr_temps_entail_wit_8 : cm_expr_temps_entail_wit_8.
Axiom proof_of_cm_expr_temps_entail_wit_9 : cm_expr_temps_entail_wit_9.
Axiom proof_of_cm_expr_temps_entail_wit_10 : cm_expr_temps_entail_wit_10.
Axiom proof_of_cm_expr_temps_return_wit_1 : cm_expr_temps_return_wit_1.
Axiom proof_of_cm_expr_temps_return_wit_2 : cm_expr_temps_return_wit_2.
Axiom proof_of_cm_expr_temps_return_wit_3 : cm_expr_temps_return_wit_3.
Axiom proof_of_cm_expr_temps_return_wit_4 : cm_expr_temps_return_wit_4.
Axiom proof_of_cm_expr_temps_return_wit_5 : cm_expr_temps_return_wit_5.
Axiom proof_of_cm_expr_temps_return_wit_6 : cm_expr_temps_return_wit_6.
Axiom proof_of_cm_expr_temps_return_wit_7 : cm_expr_temps_return_wit_7.
Axiom proof_of_cm_expr_temps_return_wit_8 : cm_expr_temps_return_wit_8.
Axiom proof_of_cm_expr_temps_return_wit_9 : cm_expr_temps_return_wit_9.
Axiom proof_of_cm_expr_temps_return_wit_10 : cm_expr_temps_return_wit_10.
Axiom proof_of_cm_expr_temps_return_wit_11 : cm_expr_temps_return_wit_11.
Axiom proof_of_cm_expr_temps_return_wit_12 : cm_expr_temps_return_wit_12.
Axiom proof_of_cm_expr_temps_return_wit_13 : cm_expr_temps_return_wit_13.
Axiom proof_of_cm_expr_temps_return_wit_14 : cm_expr_temps_return_wit_14.
Axiom proof_of_cm_expr_temps_return_wit_15 : cm_expr_temps_return_wit_15.
Axiom proof_of_cm_expr_temps_return_wit_16 : cm_expr_temps_return_wit_16.
Axiom proof_of_cm_expr_temps_return_wit_17 : cm_expr_temps_return_wit_17.
Axiom proof_of_cm_expr_temps_return_wit_18 : cm_expr_temps_return_wit_18.
Axiom proof_of_cm_expr_temps_return_wit_19 : cm_expr_temps_return_wit_19.
Axiom proof_of_cm_expr_temps_partial_solve_wit_1_pure : cm_expr_temps_partial_solve_wit_1_pure.
Axiom proof_of_cm_expr_temps_partial_solve_wit_1 : cm_expr_temps_partial_solve_wit_1.
Axiom proof_of_cm_expr_temps_partial_solve_wit_2_pure : cm_expr_temps_partial_solve_wit_2_pure.
Axiom proof_of_cm_expr_temps_partial_solve_wit_2 : cm_expr_temps_partial_solve_wit_2.
Axiom proof_of_cm_expr_temps_partial_solve_wit_3 : cm_expr_temps_partial_solve_wit_3.
Axiom proof_of_cm_expr_temps_partial_solve_wit_4_pure : cm_expr_temps_partial_solve_wit_4_pure.
Axiom proof_of_cm_expr_temps_partial_solve_wit_4 : cm_expr_temps_partial_solve_wit_4.
Axiom proof_of_cm_expr_temps_partial_solve_wit_5_pure : cm_expr_temps_partial_solve_wit_5_pure.
Axiom proof_of_cm_expr_temps_partial_solve_wit_5 : cm_expr_temps_partial_solve_wit_5.
Axiom proof_of_cm_expr_temps_partial_solve_wit_6 : cm_expr_temps_partial_solve_wit_6.
Axiom proof_of_cm_expr_temps_partial_solve_wit_7 : cm_expr_temps_partial_solve_wit_7.
Axiom proof_of_cm_expr_temps_partial_solve_wit_8 : cm_expr_temps_partial_solve_wit_8.
Axiom proof_of_cm_expr_temps_partial_solve_wit_9_pure : cm_expr_temps_partial_solve_wit_9_pure.
Axiom proof_of_cm_expr_temps_partial_solve_wit_9 : cm_expr_temps_partial_solve_wit_9.
Axiom proof_of_cm_expr_temps_partial_solve_wit_10_pure : cm_expr_temps_partial_solve_wit_10_pure.
Axiom proof_of_cm_expr_temps_partial_solve_wit_10 : cm_expr_temps_partial_solve_wit_10.
Axiom proof_of_cm_expr_temps_partial_solve_wit_11_pure : cm_expr_temps_partial_solve_wit_11_pure.
Axiom proof_of_cm_expr_temps_partial_solve_wit_11 : cm_expr_temps_partial_solve_wit_11.
Axiom proof_of_cm_expr_temps_partial_solve_wit_12 : cm_expr_temps_partial_solve_wit_12.
Axiom proof_of_cm_expr_temps_partial_solve_wit_13_pure : cm_expr_temps_partial_solve_wit_13_pure.
Axiom proof_of_cm_expr_temps_partial_solve_wit_13 : cm_expr_temps_partial_solve_wit_13.
Axiom proof_of_cm_expr_temps_partial_solve_wit_14_pure : cm_expr_temps_partial_solve_wit_14_pure.
Axiom proof_of_cm_expr_temps_partial_solve_wit_14 : cm_expr_temps_partial_solve_wit_14.
Axiom proof_of_cm_expr_temps_partial_solve_wit_15_pure : cm_expr_temps_partial_solve_wit_15_pure.
Axiom proof_of_cm_expr_temps_partial_solve_wit_15 : cm_expr_temps_partial_solve_wit_15.
Axiom proof_of_cm_expr_temps_partial_solve_wit_16_pure : cm_expr_temps_partial_solve_wit_16_pure.
Axiom proof_of_cm_expr_temps_partial_solve_wit_16 : cm_expr_temps_partial_solve_wit_16.
Axiom proof_of_cm_expr_temps_partial_solve_wit_17_pure : cm_expr_temps_partial_solve_wit_17_pure.
Axiom proof_of_cm_expr_temps_partial_solve_wit_17 : cm_expr_temps_partial_solve_wit_17.
Axiom proof_of_cm_expr_rtemps_return_wit_1 : cm_expr_rtemps_return_wit_1.
Axiom proof_of_cm_expr_rtemps_partial_solve_wit_1_pure : cm_expr_rtemps_partial_solve_wit_1_pure.
Axiom proof_of_cm_expr_rtemps_partial_solve_wit_1 : cm_expr_rtemps_partial_solve_wit_1.
Axiom proof_of_cmc_stmt_temps_safety_wit_1 : cmc_stmt_temps_safety_wit_1.
Axiom proof_of_cmc_stmt_temps_safety_wit_2 : cmc_stmt_temps_safety_wit_2.
Axiom proof_of_cmc_stmt_temps_safety_wit_3 : cmc_stmt_temps_safety_wit_3.
Axiom proof_of_cmc_stmt_temps_safety_wit_4 : cmc_stmt_temps_safety_wit_4.
Axiom proof_of_cmc_stmt_temps_safety_wit_5 : cmc_stmt_temps_safety_wit_5.
Axiom proof_of_cmc_stmt_temps_safety_wit_6 : cmc_stmt_temps_safety_wit_6.
Axiom proof_of_cmc_stmt_temps_safety_wit_7 : cmc_stmt_temps_safety_wit_7.
Axiom proof_of_cmc_stmt_temps_safety_wit_8 : cmc_stmt_temps_safety_wit_8.
Axiom proof_of_cmc_stmt_temps_safety_wit_9 : cmc_stmt_temps_safety_wit_9.
Axiom proof_of_cmc_stmt_temps_safety_wit_10 : cmc_stmt_temps_safety_wit_10.
Axiom proof_of_cmc_stmt_temps_safety_wit_11 : cmc_stmt_temps_safety_wit_11.
Axiom proof_of_cmc_stmt_temps_safety_wit_12 : cmc_stmt_temps_safety_wit_12.
Axiom proof_of_cmc_stmt_temps_safety_wit_13 : cmc_stmt_temps_safety_wit_13.
Axiom proof_of_cmc_stmt_temps_safety_wit_14 : cmc_stmt_temps_safety_wit_14.
Axiom proof_of_cmc_stmt_temps_safety_wit_15 : cmc_stmt_temps_safety_wit_15.
Axiom proof_of_cmc_stmt_temps_safety_wit_16 : cmc_stmt_temps_safety_wit_16.
Axiom proof_of_cmc_stmt_temps_safety_wit_17 : cmc_stmt_temps_safety_wit_17.
Axiom proof_of_cmc_stmt_temps_entail_wit_1 : cmc_stmt_temps_entail_wit_1.
Axiom proof_of_cmc_stmt_temps_entail_wit_2 : cmc_stmt_temps_entail_wit_2.
Axiom proof_of_cmc_stmt_temps_entail_wit_3 : cmc_stmt_temps_entail_wit_3.
Axiom proof_of_cmc_stmt_temps_entail_wit_4 : cmc_stmt_temps_entail_wit_4.
Axiom proof_of_cmc_stmt_temps_entail_wit_5 : cmc_stmt_temps_entail_wit_5.
Axiom proof_of_cmc_stmt_temps_entail_wit_6 : cmc_stmt_temps_entail_wit_6.
Axiom proof_of_cmc_stmt_temps_entail_wit_7 : cmc_stmt_temps_entail_wit_7.
Axiom proof_of_cmc_stmt_temps_entail_wit_8 : cmc_stmt_temps_entail_wit_8.
Axiom proof_of_cmc_stmt_temps_return_wit_1 : cmc_stmt_temps_return_wit_1.
Axiom proof_of_cmc_stmt_temps_return_wit_2 : cmc_stmt_temps_return_wit_2.
Axiom proof_of_cmc_stmt_temps_return_wit_3 : cmc_stmt_temps_return_wit_3.
Axiom proof_of_cmc_stmt_temps_return_wit_4 : cmc_stmt_temps_return_wit_4.
Axiom proof_of_cmc_stmt_temps_return_wit_5 : cmc_stmt_temps_return_wit_5.
Axiom proof_of_cmc_stmt_temps_return_wit_6 : cmc_stmt_temps_return_wit_6.
Axiom proof_of_cmc_stmt_temps_return_wit_7 : cmc_stmt_temps_return_wit_7.
Axiom proof_of_cmc_stmt_temps_return_wit_8 : cmc_stmt_temps_return_wit_8.
Axiom proof_of_cmc_stmt_temps_return_wit_9 : cmc_stmt_temps_return_wit_9.
Axiom proof_of_cmc_stmt_temps_return_wit_10 : cmc_stmt_temps_return_wit_10.
Axiom proof_of_cmc_stmt_temps_return_wit_11 : cmc_stmt_temps_return_wit_11.
Axiom proof_of_cmc_stmt_temps_return_wit_12 : cmc_stmt_temps_return_wit_12.
Axiom proof_of_cmc_stmt_temps_partial_solve_wit_1_pure : cmc_stmt_temps_partial_solve_wit_1_pure.
Axiom proof_of_cmc_stmt_temps_partial_solve_wit_1 : cmc_stmt_temps_partial_solve_wit_1.
Axiom proof_of_cmc_stmt_temps_partial_solve_wit_2_pure : cmc_stmt_temps_partial_solve_wit_2_pure.
Axiom proof_of_cmc_stmt_temps_partial_solve_wit_2 : cmc_stmt_temps_partial_solve_wit_2.
Axiom proof_of_cmc_stmt_temps_partial_solve_wit_3_pure : cmc_stmt_temps_partial_solve_wit_3_pure.
Axiom proof_of_cmc_stmt_temps_partial_solve_wit_3 : cmc_stmt_temps_partial_solve_wit_3.
Axiom proof_of_cmc_stmt_temps_partial_solve_wit_4_pure : cmc_stmt_temps_partial_solve_wit_4_pure.
Axiom proof_of_cmc_stmt_temps_partial_solve_wit_4 : cmc_stmt_temps_partial_solve_wit_4.
Axiom proof_of_cmc_stmt_temps_partial_solve_wit_5_pure : cmc_stmt_temps_partial_solve_wit_5_pure.
Axiom proof_of_cmc_stmt_temps_partial_solve_wit_5 : cmc_stmt_temps_partial_solve_wit_5.
Axiom proof_of_cmc_stmt_temps_partial_solve_wit_6 : cmc_stmt_temps_partial_solve_wit_6.
Axiom proof_of_cmc_stmt_temps_partial_solve_wit_7_pure : cmc_stmt_temps_partial_solve_wit_7_pure.
Axiom proof_of_cmc_stmt_temps_partial_solve_wit_7 : cmc_stmt_temps_partial_solve_wit_7.
Axiom proof_of_cmc_stmt_temps_partial_solve_wit_8_pure : cmc_stmt_temps_partial_solve_wit_8_pure.
Axiom proof_of_cmc_stmt_temps_partial_solve_wit_8 : cmc_stmt_temps_partial_solve_wit_8.
Axiom proof_of_cmc_stmt_temps_partial_solve_wit_9_pure : cmc_stmt_temps_partial_solve_wit_9_pure.
Axiom proof_of_cmc_stmt_temps_partial_solve_wit_9 : cmc_stmt_temps_partial_solve_wit_9.
Axiom proof_of_cmc_stmt_temps_partial_solve_wit_10_pure : cmc_stmt_temps_partial_solve_wit_10_pure.
Axiom proof_of_cmc_stmt_temps_partial_solve_wit_10 : cmc_stmt_temps_partial_solve_wit_10.
Axiom proof_of_cmc_stmt_temps_partial_solve_wit_11 : cmc_stmt_temps_partial_solve_wit_11.
Axiom proof_of_cmc_stmt_temps_partial_solve_wit_12 : cmc_stmt_temps_partial_solve_wit_12.
Axiom proof_of_cmc_stmt_temps_partial_solve_wit_13_pure : cmc_stmt_temps_partial_solve_wit_13_pure.
Axiom proof_of_cmc_stmt_temps_partial_solve_wit_13 : cmc_stmt_temps_partial_solve_wit_13.
Axiom proof_of_cmc_stmt_temps_partial_solve_wit_14_pure : cmc_stmt_temps_partial_solve_wit_14_pure.
Axiom proof_of_cmc_stmt_temps_partial_solve_wit_14 : cmc_stmt_temps_partial_solve_wit_14.
Axiom proof_of_cmc_stmt_temps_partial_solve_wit_15 : cmc_stmt_temps_partial_solve_wit_15.
Axiom proof_of_cmc_frame_size_safety_wit_1 : cmc_frame_size_safety_wit_1.
Axiom proof_of_cmc_frame_size_safety_wit_2 : cmc_frame_size_safety_wit_2.
Axiom proof_of_cmc_frame_size_safety_wit_3 : cmc_frame_size_safety_wit_3.
Axiom proof_of_cmc_frame_size_safety_wit_4 : cmc_frame_size_safety_wit_4.
Axiom proof_of_cmc_frame_size_safety_wit_5 : cmc_frame_size_safety_wit_5.
Axiom proof_of_cmc_frame_size_safety_wit_6 : cmc_frame_size_safety_wit_6.
Axiom proof_of_cmc_frame_size_return_wit_1 : cmc_frame_size_return_wit_1.
Axiom proof_of_cmc_frame_size_partial_solve_wit_1_pure : cmc_frame_size_partial_solve_wit_1_pure.
Axiom proof_of_cmc_frame_size_partial_solve_wit_1 : cmc_frame_size_partial_solve_wit_1.
Axiom proof_of_cmc_frame_size_partial_solve_wit_2_pure : cmc_frame_size_partial_solve_wit_2_pure.
Axiom proof_of_cmc_frame_size_partial_solve_wit_2 : cmc_frame_size_partial_solve_wit_2.
Axiom proof_of_cmc_frame_size_partial_solve_wit_3_pure : cmc_frame_size_partial_solve_wit_3_pure.
Axiom proof_of_cmc_frame_size_partial_solve_wit_3 : cmc_frame_size_partial_solve_wit_3.
Axiom proof_of_cmc_param_offset_safety_wit_1 : cmc_param_offset_safety_wit_1.
Axiom proof_of_cmc_param_offset_safety_wit_2 : cmc_param_offset_safety_wit_2.
Axiom proof_of_cmc_param_offset_return_wit_1 : cmc_param_offset_return_wit_1.
Axiom proof_of_cmc_param_offset_partial_solve_wit_1_pure : cmc_param_offset_partial_solve_wit_1_pure.
Axiom proof_of_cmc_param_offset_partial_solve_wit_1 : cmc_param_offset_partial_solve_wit_1.
Axiom proof_of_cmc_local_offset_safety_wit_1 : cmc_local_offset_safety_wit_1.
Axiom proof_of_cmc_local_offset_safety_wit_2 : cmc_local_offset_safety_wit_2.
Axiom proof_of_cmc_local_offset_safety_wit_3 : cmc_local_offset_safety_wit_3.
Axiom proof_of_cmc_local_offset_return_wit_1 : cmc_local_offset_return_wit_1.
Axiom proof_of_cmc_local_offset_partial_solve_wit_1_pure : cmc_local_offset_partial_solve_wit_1_pure.
Axiom proof_of_cmc_local_offset_partial_solve_wit_1 : cmc_local_offset_partial_solve_wit_1.
Axiom proof_of_cmc_local_offset_partial_solve_wit_2_pure : cmc_local_offset_partial_solve_wit_2_pure.
Axiom proof_of_cmc_local_offset_partial_solve_wit_2 : cmc_local_offset_partial_solve_wit_2.
Axiom proof_of_cmc_temp_offset_safety_wit_1 : cmc_temp_offset_safety_wit_1.
Axiom proof_of_cmc_temp_offset_safety_wit_2 : cmc_temp_offset_safety_wit_2.
Axiom proof_of_cmc_temp_offset_safety_wit_3 : cmc_temp_offset_safety_wit_3.
Axiom proof_of_cmc_temp_offset_safety_wit_4 : cmc_temp_offset_safety_wit_4.
Axiom proof_of_cmc_temp_offset_safety_wit_5 : cmc_temp_offset_safety_wit_5.
Axiom proof_of_cmc_temp_offset_safety_wit_6 : cmc_temp_offset_safety_wit_6.
Axiom proof_of_cmc_temp_offset_return_wit_1 : cmc_temp_offset_return_wit_1.
Axiom proof_of_cmc_temp_offset_partial_solve_wit_1_pure : cmc_temp_offset_partial_solve_wit_1_pure.
Axiom proof_of_cmc_temp_offset_partial_solve_wit_1 : cmc_temp_offset_partial_solve_wit_1.
Axiom proof_of_cmc_temp_offset_partial_solve_wit_2_pure : cmc_temp_offset_partial_solve_wit_2_pure.
Axiom proof_of_cmc_temp_offset_partial_solve_wit_2 : cmc_temp_offset_partial_solve_wit_2.
Axiom proof_of_cm_normalize_count_safety_wit_1 : cm_normalize_count_safety_wit_1.
Axiom proof_of_cm_normalize_count_safety_wit_2 : cm_normalize_count_safety_wit_2.
Axiom proof_of_cm_normalize_count_safety_wit_3 : cm_normalize_count_safety_wit_3.
Axiom proof_of_cm_normalize_count_return_wit_1 : cm_normalize_count_return_wit_1.
Axiom proof_of_cm_normalize_count_return_wit_2 : cm_normalize_count_return_wit_2.

End VC_Correct.
