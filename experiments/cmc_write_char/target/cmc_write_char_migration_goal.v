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
Require Import SimpleC.EE.QCP_demos_human.cmc_write_word_migration_lib.
Local Open Scope sac.

(*----- Function cmc_write_char -----*)

Definition cmc_write_char_safety_wit_1 := 
forall (char_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : ((cursor_pre + 1 ) <= capacity_pre)) (PreH3 : (capacity_pre <= INT_MAX)) ,
  ((( &( "byte" ) )) # UChar  |->_)
  **  ((( &( "bits" ) )) # UInt64  |-> (unsigned_last_nbits (char_value_pre) (64)))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "char_value" ) )) # Int64  |-> char_value_pre)
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (256 <> 0) ”
.

Definition cmc_write_char_return_wit_1 := 
forall (char_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : ((cursor_pre + 1 ) <= capacity_pre)) (PreH3 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 (cursor_pre + 1 ) (app (prefix) ((cons ((tower_u8 (char_value_pre))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 1 ) capacity_pre )
|--
  (UCharArray.seg data_pre 0 (cursor_pre + 1 ) (app (prefix) ((cons ((tower_u8 (char_value_pre))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 1 ) capacity_pre )
.

Definition cmc_write_char_partial_solve_wit_1_pure := 
(
forall (char_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : ((cursor_pre + 1 ) <= capacity_pre)) (PreH3 : (capacity_pre <= INT_MAX)) ,
  ((( &( "byte" ) )) # UChar  |-> (unsigned_last_nbits (((unsigned_last_nbits (char_value_pre) (64)) % ( 256 ) )) (8)))
  **  ((( &( "bits" ) )) # UInt64  |-> (unsigned_last_nbits (char_value_pre) (64)))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "char_value" ) )) # Int64  |-> char_value_pre)
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (0 <= cursor_pre) ” 
  &&  “ (cursor_pre < capacity_pre) ” 
  &&  “ ((tower_u8 (char_value_pre)) < 256) ” 
  &&  “ (0 <= (tower_u8 (char_value_pre))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (char_value_pre) (64)) % ( 256 ) )) (8)) = (tower_u8 (char_value_pre))) ”
) \/
(
forall (char_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : ((unsigned_last_nbits (char_value_pre) (64)) <= UINT64_MAX)) (PreH2 : ((unsigned_last_nbits (char_value_pre) (64)) >= 0)) (PreH3 : (char_value_pre <= INT64_MAX)) (PreH4 : (char_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 1 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  ((( &( "byte" ) )) # UChar  |-> (unsigned_last_nbits (((unsigned_last_nbits (char_value_pre) (64)) % ( 256 ) )) (8)))
  **  ((( &( "bits" ) )) # UInt64  |-> (unsigned_last_nbits (char_value_pre) (64)))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "char_value" ) )) # Int64  |-> char_value_pre)
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ ((unsigned_last_nbits (((unsigned_last_nbits (char_value_pre) (64)) % ( 256 ) )) (8)) = (tower_u8 (char_value_pre))) ” 
  &&  “ (0 <= (tower_u8 (char_value_pre))) ” 
  &&  “ ((tower_u8 (char_value_pre)) < 256) ”
).

Definition cmc_write_char_partial_solve_wit_1_pure_split_goal_1 := 
forall (char_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : ((unsigned_last_nbits (char_value_pre) (64)) <= UINT64_MAX)) (PreH2 : ((unsigned_last_nbits (char_value_pre) (64)) >= 0)) (PreH3 : (char_value_pre <= INT64_MAX)) (PreH4 : (char_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 1 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  ((( &( "byte" ) )) # UChar  |-> (unsigned_last_nbits (((unsigned_last_nbits (char_value_pre) (64)) % ( 256 ) )) (8)))
  **  ((( &( "bits" ) )) # UInt64  |-> (unsigned_last_nbits (char_value_pre) (64)))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "char_value" ) )) # Int64  |-> char_value_pre)
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ ((unsigned_last_nbits (((unsigned_last_nbits (char_value_pre) (64)) % ( 256 ) )) (8)) = (tower_u8 (char_value_pre))) ”
.

Definition cmc_write_char_partial_solve_wit_1_pure_split_goal_2 := 
forall (char_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : ((unsigned_last_nbits (char_value_pre) (64)) <= UINT64_MAX)) (PreH2 : ((unsigned_last_nbits (char_value_pre) (64)) >= 0)) (PreH3 : (char_value_pre <= INT64_MAX)) (PreH4 : (char_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 1 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  ((( &( "byte" ) )) # UChar  |-> (unsigned_last_nbits (((unsigned_last_nbits (char_value_pre) (64)) % ( 256 ) )) (8)))
  **  ((( &( "bits" ) )) # UInt64  |-> (unsigned_last_nbits (char_value_pre) (64)))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "char_value" ) )) # Int64  |-> char_value_pre)
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (0 <= (tower_u8 (char_value_pre))) ”
.

Definition cmc_write_char_partial_solve_wit_1_pure_split_goal_3 := 
forall (char_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : ((unsigned_last_nbits (char_value_pre) (64)) <= UINT64_MAX)) (PreH2 : ((unsigned_last_nbits (char_value_pre) (64)) >= 0)) (PreH3 : (char_value_pre <= INT64_MAX)) (PreH4 : (char_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 1 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  ((( &( "byte" ) )) # UChar  |-> (unsigned_last_nbits (((unsigned_last_nbits (char_value_pre) (64)) % ( 256 ) )) (8)))
  **  ((( &( "bits" ) )) # UInt64  |-> (unsigned_last_nbits (char_value_pre) (64)))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "char_value" ) )) # Int64  |-> char_value_pre)
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ ((tower_u8 (char_value_pre)) < 256) ”
.

Definition cmc_write_char_partial_solve_wit_1_aux := 
forall (char_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : ((cursor_pre + 1 ) <= capacity_pre)) (PreH3 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (0 <= cursor_pre) ” 
  &&  “ (cursor_pre < capacity_pre) ” 
  &&  “ ((tower_u8 (char_value_pre)) < 256) ” 
  &&  “ (0 <= (tower_u8 (char_value_pre))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (char_value_pre) (64)) % ( 256 ) )) (8)) = (tower_u8 (char_value_pre))) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ ((cursor_pre + 1 ) <= capacity_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ”
  &&  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
.

Definition cmc_write_char_partial_solve_wit_1 := cmc_write_char_partial_solve_wit_1_pure -> cmc_write_char_partial_solve_wit_1_aux.

Module Type VC_Correct.


Axiom proof_of_cmc_write_char_safety_wit_1 : cmc_write_char_safety_wit_1.
Axiom proof_of_cmc_write_char_return_wit_1 : cmc_write_char_return_wit_1.
Axiom proof_of_cmc_write_char_partial_solve_wit_1_pure : cmc_write_char_partial_solve_wit_1_pure.
Axiom proof_of_cmc_write_char_partial_solve_wit_1 : cmc_write_char_partial_solve_wit_1.

End VC_Correct.
