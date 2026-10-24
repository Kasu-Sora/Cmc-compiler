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
Local Open Scope sac.

(*----- Function cmc_write_zeroes -----*)

Definition cmc_write_zeroes_safety_wit_1 := 
forall (count_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : (0 <= count_pre)) (PreH3 : ((cursor_pre + count_pre ) <= capacity_pre)) (PreH4 : (capacity_pre <= INT_MAX)) ,
  ((( &( "index" ) )) # Int  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_write_zeroes_safety_wit_2 := 
forall (count_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (index: Z) (PreH1 : (index <> count_pre)) (PreH2 : (0 <= index)) (PreH3 : (index <= count_pre)) (PreH4 : (0 <= cursor_pre)) (PreH5 : (0 <= count_pre)) (PreH6 : ((cursor_pre + count_pre ) <= capacity_pre)) (PreH7 : (capacity_pre <= INT_MAX)) ,
  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  (UCharArray.seg data_pre 0 (cursor_pre + index ) (app (prefix) ((zeros (index)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + index ) capacity_pre )
|--
  “ ((cursor_pre + index ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cursor_pre + index )) ”
.

Definition cmc_write_zeroes_safety_wit_3 := 
forall (count_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (index: Z) (PreH1 : (index <> count_pre)) (PreH2 : (0 <= index)) (PreH3 : (index <= count_pre)) (PreH4 : (0 <= cursor_pre)) (PreH5 : (0 <= count_pre)) (PreH6 : ((cursor_pre + count_pre ) <= capacity_pre)) (PreH7 : (capacity_pre <= INT_MAX)) ,
  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  (UCharArray.seg data_pre 0 (cursor_pre + index ) (app (prefix) ((zeros (index)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + index ) capacity_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_write_zeroes_safety_wit_4 := 
forall (count_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (index: Z) (PreH1 : (index <> count_pre)) (PreH2 : (0 <= index)) (PreH3 : (index <= count_pre)) (PreH4 : (0 <= cursor_pre)) (PreH5 : (0 <= count_pre)) (PreH6 : ((cursor_pre + count_pre ) <= capacity_pre)) (PreH7 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + index ) + 1 ) (app ((app (prefix) ((zeros (index))))) ((cons (0) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre ((cursor_pre + index ) + 1 ) capacity_pre )
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "index" ) )) # Int  |-> index)
|--
  “ ((index + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (index + 1 )) ”
.

Definition cmc_write_zeroes_safety_wit_5 := 
forall (count_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (index: Z) (PreH1 : (index <> count_pre)) (PreH2 : (0 <= index)) (PreH3 : (index <= count_pre)) (PreH4 : (0 <= cursor_pre)) (PreH5 : (0 <= count_pre)) (PreH6 : ((cursor_pre + count_pre ) <= capacity_pre)) (PreH7 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + index ) + 1 ) (app ((app (prefix) ((zeros (index))))) ((cons (0) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre ((cursor_pre + index ) + 1 ) capacity_pre )
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "index" ) )) # Int  |-> index)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmc_write_zeroes_entail_wit_1 := 
(
forall (count_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : (0 <= count_pre)) (PreH3 : ((cursor_pre + count_pre ) <= capacity_pre)) (PreH4 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= count_pre) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ (0 <= count_pre) ” 
  &&  “ ((cursor_pre + count_pre ) <= capacity_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ”
  &&  (UCharArray.seg data_pre 0 (cursor_pre + 0 ) (app (prefix) ((zeros (0)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 0 ) capacity_pre )
) \/
(
forall (count_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : (0 <= count_pre)) (PreH3 : ((cursor_pre + count_pre ) <= capacity_pre)) (PreH4 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 cursor_pre prefix )
|--
  (UCharArray.seg data_pre 0 (cursor_pre + 0 ) (app (prefix) ((zeros (0)))) )
).

Definition cmc_write_zeroes_entail_wit_1_split_goal_spatial := 
forall (count_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : (0 <= count_pre)) (PreH3 : ((cursor_pre + count_pre ) <= capacity_pre)) (PreH4 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 cursor_pre prefix )
|--
  (UCharArray.seg data_pre 0 (cursor_pre + 0 ) (app (prefix) ((zeros (0)))) )
.

Definition cmc_write_zeroes_entail_wit_2 := 
(
forall (count_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (index: Z) (PreH1 : (index <> count_pre)) (PreH2 : (0 <= index)) (PreH3 : (index <= count_pre)) (PreH4 : (0 <= cursor_pre)) (PreH5 : (0 <= count_pre)) (PreH6 : ((cursor_pre + count_pre ) <= capacity_pre)) (PreH7 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + index ) + 1 ) (app ((app (prefix) ((zeros (index))))) ((cons (0) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre ((cursor_pre + index ) + 1 ) capacity_pre )
|--
  “ (0 <= (index + 1 )) ” 
  &&  “ ((index + 1 ) <= count_pre) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ (0 <= count_pre) ” 
  &&  “ ((cursor_pre + count_pre ) <= capacity_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ”
  &&  (UCharArray.seg data_pre 0 (cursor_pre + (index + 1 ) ) (app (prefix) ((zeros ((index + 1 ))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + (index + 1 ) ) capacity_pre )
) \/
(
forall (count_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (index: Z) (PreH1 : (index <> count_pre)) (PreH2 : (0 <= index)) (PreH3 : (index <= count_pre)) (PreH4 : (0 <= cursor_pre)) (PreH5 : (0 <= count_pre)) (PreH6 : ((cursor_pre + count_pre ) <= capacity_pre)) (PreH7 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + index ) + 1 ) (app ((app (prefix) ((zeros (index))))) ((cons (0) ((@nil Z))))) )
|--
  (UCharArray.seg data_pre 0 (cursor_pre + (index + 1 ) ) (app (prefix) ((zeros ((index + 1 ))))) )
).

Definition cmc_write_zeroes_entail_wit_2_split_goal_spatial := 
forall (count_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (index: Z) (PreH1 : (index <> count_pre)) (PreH2 : (0 <= index)) (PreH3 : (index <= count_pre)) (PreH4 : (0 <= cursor_pre)) (PreH5 : (0 <= count_pre)) (PreH6 : ((cursor_pre + count_pre ) <= capacity_pre)) (PreH7 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + index ) + 1 ) (app ((app (prefix) ((zeros (index))))) ((cons (0) ((@nil Z))))) )
|--
  (UCharArray.seg data_pre 0 (cursor_pre + (index + 1 ) ) (app (prefix) ((zeros ((index + 1 ))))) )
.

Definition cmc_write_zeroes_return_wit_1 := 
(
forall (count_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (index: Z) (PreH1 : (index = count_pre)) (PreH2 : (0 <= index)) (PreH3 : (index <= count_pre)) (PreH4 : (0 <= cursor_pre)) (PreH5 : (0 <= count_pre)) (PreH6 : ((cursor_pre + count_pre ) <= capacity_pre)) (PreH7 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 (cursor_pre + index ) (app (prefix) ((zeros (index)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + index ) capacity_pre )
|--
  (UCharArray.seg data_pre 0 (cursor_pre + count_pre ) (app (prefix) ((zeros (count_pre)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + count_pre ) capacity_pre )
) \/
(
forall (count_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (index: Z) (PreH1 : (index = count_pre)) (PreH2 : (0 <= index)) (PreH3 : (index <= count_pre)) (PreH4 : (0 <= cursor_pre)) (PreH5 : (0 <= count_pre)) (PreH6 : ((cursor_pre + count_pre ) <= capacity_pre)) (PreH7 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 (cursor_pre + index ) (app (prefix) ((zeros (index)))) )
|--
  (UCharArray.seg data_pre 0 (cursor_pre + count_pre ) (app (prefix) ((zeros (count_pre)))) )
).

Definition cmc_write_zeroes_return_wit_1_split_goal_spatial := 
forall (count_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (index: Z) (PreH1 : (index = count_pre)) (PreH2 : (0 <= index)) (PreH3 : (index <= count_pre)) (PreH4 : (0 <= cursor_pre)) (PreH5 : (0 <= count_pre)) (PreH6 : ((cursor_pre + count_pre ) <= capacity_pre)) (PreH7 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 (cursor_pre + index ) (app (prefix) ((zeros (index)))) )
|--
  (UCharArray.seg data_pre 0 (cursor_pre + count_pre ) (app (prefix) ((zeros (count_pre)))) )
.

Definition cmc_write_zeroes_partial_solve_wit_1 := 
forall (count_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (index: Z) (PreH1 : (index <> count_pre)) (PreH2 : (0 <= index)) (PreH3 : (index <= count_pre)) (PreH4 : (0 <= cursor_pre)) (PreH5 : (0 <= count_pre)) (PreH6 : ((cursor_pre + count_pre ) <= capacity_pre)) (PreH7 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 (cursor_pre + index ) (app (prefix) ((zeros (index)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + index ) capacity_pre )
|--
  “ (index <> count_pre) ” 
  &&  “ (0 <= index) ” 
  &&  “ (index <= count_pre) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ (0 <= count_pre) ” 
  &&  “ ((cursor_pre + count_pre ) <= capacity_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ”
  &&  (((data_pre + ((cursor_pre + index ) * sizeof(UCHAR)))) # UChar  |->_)
  **  (UCharArray.undef_seg data_pre ((cursor_pre + index ) + 1 ) capacity_pre )
  **  (UCharArray.seg data_pre 0 (cursor_pre + index ) (app (prefix) ((zeros (index)))) )
.

Module Type VC_Correct.


Axiom proof_of_cmc_write_zeroes_safety_wit_1 : cmc_write_zeroes_safety_wit_1.
Axiom proof_of_cmc_write_zeroes_safety_wit_2 : cmc_write_zeroes_safety_wit_2.
Axiom proof_of_cmc_write_zeroes_safety_wit_3 : cmc_write_zeroes_safety_wit_3.
Axiom proof_of_cmc_write_zeroes_safety_wit_4 : cmc_write_zeroes_safety_wit_4.
Axiom proof_of_cmc_write_zeroes_safety_wit_5 : cmc_write_zeroes_safety_wit_5.
Axiom proof_of_cmc_write_zeroes_entail_wit_1 : cmc_write_zeroes_entail_wit_1.
Axiom proof_of_cmc_write_zeroes_entail_wit_2 : cmc_write_zeroes_entail_wit_2.
Axiom proof_of_cmc_write_zeroes_return_wit_1 : cmc_write_zeroes_return_wit_1.
Axiom proof_of_cmc_write_zeroes_partial_solve_wit_1 : cmc_write_zeroes_partial_solve_wit_1.

End VC_Correct.
