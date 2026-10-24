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
Require Import SimpleC.EE.QCP_demos_human.cmc_copy_bytes_migration_lib.
Local Open Scope sac.

(*----- Function cmc_copy_bytes -----*)

Definition cmc_copy_bytes_safety_wit_1 := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (length_pre: Z) (source_pre: Z) (bytes: (@list Z)) (prefix: (@list Z)) (PreH1 : (0 <= length_pre)) (PreH2 : ((Zlength (bytes)) = length_pre)) (PreH3 : (0 <= cursor_pre)) (PreH4 : ((cursor_pre + length_pre ) <= capacity_pre)) (PreH5 : (capacity_pre <= INT_MAX)) (PreH6 : (cmc_uint8_buffer_nonnull source_pre bytes )) ,
  ((( &( "source" ) )) # Ptr  |-> source_pre)
  **  ((( &( "length" ) )) # Int  |-> length_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.full source_pre length_pre bytes )
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_copy_bytes_safety_wit_2 := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (length_pre: Z) (source_pre: Z) (bytes: (@list Z)) (prefix: (@list Z)) (PreH1 : (length_pre <> 0)) (PreH2 : (0 <= length_pre)) (PreH3 : ((Zlength (bytes)) = length_pre)) (PreH4 : (0 <= cursor_pre)) (PreH5 : ((cursor_pre + length_pre ) <= capacity_pre)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cmc_uint8_buffer_nonnull source_pre bytes )) ,
  ((( &( "index" ) )) # Int  |->_)
  **  ((( &( "source" ) )) # Ptr  |-> source_pre)
  **  ((( &( "length" ) )) # Int  |-> length_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.full source_pre length_pre bytes )
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmc_copy_bytes_safety_wit_3 := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (length_pre: Z) (source_pre: Z) (bytes: (@list Z)) (prefix: (@list Z)) (index: Z) (PreH1 : (index < length_pre)) (PreH2 : (0 < length_pre)) (PreH3 : ((Zlength (bytes)) = length_pre)) (PreH4 : (source_pre <> 0)) (PreH5 : (0 <= index)) (PreH6 : (index <= length_pre)) (PreH7 : (0 <= cursor_pre)) (PreH8 : ((cursor_pre + length_pre ) <= capacity_pre)) (PreH9 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.full source_pre length_pre bytes )
  **  ((( &( "byte" ) )) # UChar  |-> (Znth index bytes 0))
  **  ((( &( "source" ) )) # Ptr  |-> source_pre)
  **  ((( &( "length" ) )) # Int  |-> length_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "index" ) )) # Int  |-> index)
  **  (UCharArray.seg data_pre 0 (cursor_pre + index ) (app (prefix) ((sublist (0) (index) (bytes)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + index ) capacity_pre )
|--
  “ ((cursor_pre + index ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cursor_pre + index )) ”
.

Definition cmc_copy_bytes_safety_wit_4 := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (length_pre: Z) (source_pre: Z) (bytes: (@list Z)) (prefix: (@list Z)) (index: Z) (PreH1 : (index < length_pre)) (PreH2 : (0 < length_pre)) (PreH3 : ((Zlength (bytes)) = length_pre)) (PreH4 : (source_pre <> 0)) (PreH5 : (0 <= index)) (PreH6 : (index <= length_pre)) (PreH7 : (0 <= cursor_pre)) (PreH8 : ((cursor_pre + length_pre ) <= capacity_pre)) (PreH9 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + index ) + 1 ) (app ((app (prefix) ((sublist (0) (index) (bytes))))) ((cons ((Znth index bytes 0)) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre ((cursor_pre + index ) + 1 ) capacity_pre )
  **  (UCharArray.full source_pre length_pre bytes )
  **  ((( &( "byte" ) )) # UChar  |-> (Znth index bytes 0))
  **  ((( &( "source" ) )) # Ptr  |-> source_pre)
  **  ((( &( "length" ) )) # Int  |-> length_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "index" ) )) # Int  |-> index)
|--
  “ ((index + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (index + 1 )) ”
.

Definition cmc_copy_bytes_safety_wit_5 := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (length_pre: Z) (source_pre: Z) (bytes: (@list Z)) (prefix: (@list Z)) (index: Z) (PreH1 : (index < length_pre)) (PreH2 : (0 < length_pre)) (PreH3 : ((Zlength (bytes)) = length_pre)) (PreH4 : (source_pre <> 0)) (PreH5 : (0 <= index)) (PreH6 : (index <= length_pre)) (PreH7 : (0 <= cursor_pre)) (PreH8 : ((cursor_pre + length_pre ) <= capacity_pre)) (PreH9 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + index ) + 1 ) (app ((app (prefix) ((sublist (0) (index) (bytes))))) ((cons ((Znth index bytes 0)) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre ((cursor_pre + index ) + 1 ) capacity_pre )
  **  (UCharArray.full source_pre length_pre bytes )
  **  ((( &( "byte" ) )) # UChar  |-> (Znth index bytes 0))
  **  ((( &( "source" ) )) # Ptr  |-> source_pre)
  **  ((( &( "length" ) )) # Int  |-> length_pre)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "index" ) )) # Int  |-> index)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmc_copy_bytes_entail_wit_1 := 
(
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (length_pre: Z) (source_pre: Z) (bytes: (@list Z)) (prefix: (@list Z)) (PreH1 : (length_pre <> 0)) (PreH2 : (0 <= length_pre)) (PreH3 : ((Zlength (bytes)) = length_pre)) (PreH4 : (0 <= cursor_pre)) (PreH5 : ((cursor_pre + length_pre ) <= capacity_pre)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cmc_uint8_buffer_nonnull source_pre bytes )) ,
  (UCharArray.full source_pre length_pre bytes )
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (0 < length_pre) ” 
  &&  “ ((Zlength (bytes)) = length_pre) ” 
  &&  “ (source_pre <> 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= length_pre) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ ((cursor_pre + length_pre ) <= capacity_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ”
  &&  (UCharArray.full source_pre length_pre bytes )
  **  (UCharArray.seg data_pre 0 (cursor_pre + 0 ) (app (prefix) ((sublist (0) (0) (bytes)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 0 ) capacity_pre )
) \/
(
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (length_pre: Z) (source_pre: Z) (bytes: (@list Z)) (prefix: (@list Z)) (PreH1 : (length_pre <> 0)) (PreH2 : (0 <= length_pre)) (PreH3 : ((Zlength (bytes)) = length_pre)) (PreH4 : (0 <= cursor_pre)) (PreH5 : ((cursor_pre + length_pre ) <= capacity_pre)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cmc_uint8_buffer_nonnull source_pre bytes )) ,
  (UCharArray.seg data_pre 0 cursor_pre prefix )
|--
  “ (source_pre <> 0) ”
  &&  (UCharArray.seg data_pre 0 (cursor_pre + 0 ) (app (prefix) ((sublist (0) (0) (bytes)))) )
).

Definition cmc_copy_bytes_entail_wit_1_split_goal_1 := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (length_pre: Z) (source_pre: Z) (bytes: (@list Z)) (prefix: (@list Z)) (PreH1 : (length_pre <> 0)) (PreH2 : (0 <= length_pre)) (PreH3 : ((Zlength (bytes)) = length_pre)) (PreH4 : (0 <= cursor_pre)) (PreH5 : ((cursor_pre + length_pre ) <= capacity_pre)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cmc_uint8_buffer_nonnull source_pre bytes )) ,
  (UCharArray.seg data_pre 0 cursor_pre prefix )
|--
  “ (source_pre <> 0) ”
.

Definition cmc_copy_bytes_entail_wit_1_split_goal_spatial := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (length_pre: Z) (source_pre: Z) (bytes: (@list Z)) (prefix: (@list Z)) (PreH1 : (length_pre <> 0)) (PreH2 : (0 <= length_pre)) (PreH3 : ((Zlength (bytes)) = length_pre)) (PreH4 : (0 <= cursor_pre)) (PreH5 : ((cursor_pre + length_pre ) <= capacity_pre)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cmc_uint8_buffer_nonnull source_pre bytes )) ,
  (UCharArray.seg data_pre 0 cursor_pre prefix )
|--
  (UCharArray.seg data_pre 0 (cursor_pre + 0 ) (app (prefix) ((sublist (0) (0) (bytes)))) )
.

Definition cmc_copy_bytes_entail_wit_2 := 
(
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (length_pre: Z) (source_pre: Z) (bytes: (@list Z)) (prefix: (@list Z)) (index: Z) (PreH1 : (index < length_pre)) (PreH2 : (0 < length_pre)) (PreH3 : ((Zlength (bytes)) = length_pre)) (PreH4 : (source_pre <> 0)) (PreH5 : (0 <= index)) (PreH6 : (index <= length_pre)) (PreH7 : (0 <= cursor_pre)) (PreH8 : ((cursor_pre + length_pre ) <= capacity_pre)) (PreH9 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + index ) + 1 ) (app ((app (prefix) ((sublist (0) (index) (bytes))))) ((cons ((Znth index bytes 0)) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre ((cursor_pre + index ) + 1 ) capacity_pre )
  **  (UCharArray.full source_pre length_pre bytes )
|--
  “ (0 < length_pre) ” 
  &&  “ ((Zlength (bytes)) = length_pre) ” 
  &&  “ (source_pre <> 0) ” 
  &&  “ (0 <= (index + 1 )) ” 
  &&  “ ((index + 1 ) <= length_pre) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ ((cursor_pre + length_pre ) <= capacity_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ”
  &&  (UCharArray.full source_pre length_pre bytes )
  **  (UCharArray.seg data_pre 0 (cursor_pre + (index + 1 ) ) (app (prefix) ((sublist (0) ((index + 1 )) (bytes)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + (index + 1 ) ) capacity_pre )
) \/
(
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (length_pre: Z) (source_pre: Z) (bytes: (@list Z)) (prefix: (@list Z)) (index: Z) (PreH1 : (index < length_pre)) (PreH2 : (0 < length_pre)) (PreH3 : ((Zlength (bytes)) = length_pre)) (PreH4 : (source_pre <> 0)) (PreH5 : (0 <= index)) (PreH6 : (index <= length_pre)) (PreH7 : (0 <= cursor_pre)) (PreH8 : ((cursor_pre + length_pre ) <= capacity_pre)) (PreH9 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + index ) + 1 ) (app ((app (prefix) ((sublist (0) (index) (bytes))))) ((cons ((Znth index bytes 0)) ((@nil Z))))) )
|--
  (UCharArray.seg data_pre 0 (cursor_pre + (index + 1 ) ) (app (prefix) ((sublist (0) ((index + 1 )) (bytes)))) )
).

Definition cmc_copy_bytes_entail_wit_2_split_goal_spatial := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (length_pre: Z) (source_pre: Z) (bytes: (@list Z)) (prefix: (@list Z)) (index: Z) (PreH1 : (index < length_pre)) (PreH2 : (0 < length_pre)) (PreH3 : ((Zlength (bytes)) = length_pre)) (PreH4 : (source_pre <> 0)) (PreH5 : (0 <= index)) (PreH6 : (index <= length_pre)) (PreH7 : (0 <= cursor_pre)) (PreH8 : ((cursor_pre + length_pre ) <= capacity_pre)) (PreH9 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + index ) + 1 ) (app ((app (prefix) ((sublist (0) (index) (bytes))))) ((cons ((Znth index bytes 0)) ((@nil Z))))) )
|--
  (UCharArray.seg data_pre 0 (cursor_pre + (index + 1 ) ) (app (prefix) ((sublist (0) ((index + 1 )) (bytes)))) )
.

Definition cmc_copy_bytes_return_wit_1 := 
(
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (length_pre: Z) (source_pre: Z) (bytes: (@list Z)) (prefix: (@list Z)) (PreH1 : (length_pre = 0)) (PreH2 : (0 <= length_pre)) (PreH3 : ((Zlength (bytes)) = length_pre)) (PreH4 : (0 <= cursor_pre)) (PreH5 : ((cursor_pre + length_pre ) <= capacity_pre)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cmc_uint8_buffer_nonnull source_pre bytes )) ,
  (UCharArray.full source_pre length_pre bytes )
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (cmc_uint8_buffer_nonnull source_pre bytes ) ”
  &&  (UCharArray.full source_pre length_pre bytes )
  **  (UCharArray.seg data_pre 0 (cursor_pre + length_pre ) (app (prefix) (bytes)) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + length_pre ) capacity_pre )
) \/
(
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (length_pre: Z) (source_pre: Z) (bytes: (@list Z)) (prefix: (@list Z)) (PreH1 : (length_pre = 0)) (PreH2 : (0 <= length_pre)) (PreH3 : ((Zlength (bytes)) = length_pre)) (PreH4 : (0 <= cursor_pre)) (PreH5 : ((cursor_pre + length_pre ) <= capacity_pre)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cmc_uint8_buffer_nonnull source_pre bytes )) ,
  (UCharArray.seg data_pre 0 cursor_pre prefix )
|--
  (UCharArray.seg data_pre 0 (cursor_pre + length_pre ) (app (prefix) (bytes)) )
).

Definition cmc_copy_bytes_return_wit_1_split_goal_spatial := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (length_pre: Z) (source_pre: Z) (bytes: (@list Z)) (prefix: (@list Z)) (PreH1 : (length_pre = 0)) (PreH2 : (0 <= length_pre)) (PreH3 : ((Zlength (bytes)) = length_pre)) (PreH4 : (0 <= cursor_pre)) (PreH5 : ((cursor_pre + length_pre ) <= capacity_pre)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cmc_uint8_buffer_nonnull source_pre bytes )) ,
  (UCharArray.seg data_pre 0 cursor_pre prefix )
|--
  (UCharArray.seg data_pre 0 (cursor_pre + length_pre ) (app (prefix) (bytes)) )
.

Definition cmc_copy_bytes_return_wit_2 := 
(
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (length_pre: Z) (source_pre: Z) (bytes: (@list Z)) (prefix: (@list Z)) (index: Z) (PreH1 : (index >= length_pre)) (PreH2 : (0 < length_pre)) (PreH3 : ((Zlength (bytes)) = length_pre)) (PreH4 : (source_pre <> 0)) (PreH5 : (0 <= index)) (PreH6 : (index <= length_pre)) (PreH7 : (0 <= cursor_pre)) (PreH8 : ((cursor_pre + length_pre ) <= capacity_pre)) (PreH9 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.full source_pre length_pre bytes )
  **  (UCharArray.seg data_pre 0 (cursor_pre + index ) (app (prefix) ((sublist (0) (index) (bytes)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + index ) capacity_pre )
|--
  “ (cmc_uint8_buffer_nonnull source_pre bytes ) ”
  &&  (UCharArray.full source_pre length_pre bytes )
  **  (UCharArray.seg data_pre 0 (cursor_pre + length_pre ) (app (prefix) (bytes)) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + length_pre ) capacity_pre )
) \/
(
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (length_pre: Z) (source_pre: Z) (bytes: (@list Z)) (prefix: (@list Z)) (index: Z) (PreH1 : (index >= length_pre)) (PreH2 : (0 < length_pre)) (PreH3 : ((Zlength (bytes)) = length_pre)) (PreH4 : (source_pre <> 0)) (PreH5 : (0 <= index)) (PreH6 : (index <= length_pre)) (PreH7 : (0 <= cursor_pre)) (PreH8 : ((cursor_pre + length_pre ) <= capacity_pre)) (PreH9 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 (cursor_pre + index ) (app (prefix) ((sublist (0) (index) (bytes)))) )
|--
  “ (cmc_uint8_buffer_nonnull source_pre bytes ) ”
  &&  (UCharArray.seg data_pre 0 (cursor_pre + length_pre ) (app (prefix) (bytes)) )
).

Definition cmc_copy_bytes_return_wit_2_split_goal_1 := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (length_pre: Z) (source_pre: Z) (bytes: (@list Z)) (prefix: (@list Z)) (index: Z) (PreH1 : (index >= length_pre)) (PreH2 : (0 < length_pre)) (PreH3 : ((Zlength (bytes)) = length_pre)) (PreH4 : (source_pre <> 0)) (PreH5 : (0 <= index)) (PreH6 : (index <= length_pre)) (PreH7 : (0 <= cursor_pre)) (PreH8 : ((cursor_pre + length_pre ) <= capacity_pre)) (PreH9 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 (cursor_pre + index ) (app (prefix) ((sublist (0) (index) (bytes)))) )
|--
  “ (cmc_uint8_buffer_nonnull source_pre bytes ) ”
.

Definition cmc_copy_bytes_return_wit_2_split_goal_spatial := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (length_pre: Z) (source_pre: Z) (bytes: (@list Z)) (prefix: (@list Z)) (index: Z) (PreH1 : (index >= length_pre)) (PreH2 : (0 < length_pre)) (PreH3 : ((Zlength (bytes)) = length_pre)) (PreH4 : (source_pre <> 0)) (PreH5 : (0 <= index)) (PreH6 : (index <= length_pre)) (PreH7 : (0 <= cursor_pre)) (PreH8 : ((cursor_pre + length_pre ) <= capacity_pre)) (PreH9 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 (cursor_pre + index ) (app (prefix) ((sublist (0) (index) (bytes)))) )
|--
  (UCharArray.seg data_pre 0 (cursor_pre + length_pre ) (app (prefix) (bytes)) )
.

Definition cmc_copy_bytes_partial_solve_wit_1 := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (length_pre: Z) (source_pre: Z) (bytes: (@list Z)) (prefix: (@list Z)) (index: Z) (PreH1 : (index < length_pre)) (PreH2 : (0 < length_pre)) (PreH3 : ((Zlength (bytes)) = length_pre)) (PreH4 : (source_pre <> 0)) (PreH5 : (0 <= index)) (PreH6 : (index <= length_pre)) (PreH7 : (0 <= cursor_pre)) (PreH8 : ((cursor_pre + length_pre ) <= capacity_pre)) (PreH9 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.full source_pre length_pre bytes )
  **  (UCharArray.seg data_pre 0 (cursor_pre + index ) (app (prefix) ((sublist (0) (index) (bytes)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + index ) capacity_pre )
|--
  “ (index < length_pre) ” 
  &&  “ (0 < length_pre) ” 
  &&  “ ((Zlength (bytes)) = length_pre) ” 
  &&  “ (source_pre <> 0) ” 
  &&  “ (0 <= index) ” 
  &&  “ (index <= length_pre) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ ((cursor_pre + length_pre ) <= capacity_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ”
  &&  (((source_pre + (index * sizeof(UCHAR)))) # UChar  |-> (Znth index bytes 0))
  **  (UCharArray.missing_i source_pre index 0 length_pre bytes )
  **  (UCharArray.seg data_pre 0 (cursor_pre + index ) (app (prefix) ((sublist (0) (index) (bytes)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + index ) capacity_pre )
.

Definition cmc_copy_bytes_partial_solve_wit_2 := 
forall (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (length_pre: Z) (source_pre: Z) (bytes: (@list Z)) (prefix: (@list Z)) (index: Z) (PreH1 : (index < length_pre)) (PreH2 : (0 < length_pre)) (PreH3 : ((Zlength (bytes)) = length_pre)) (PreH4 : (source_pre <> 0)) (PreH5 : (0 <= index)) (PreH6 : (index <= length_pre)) (PreH7 : (0 <= cursor_pre)) (PreH8 : ((cursor_pre + length_pre ) <= capacity_pre)) (PreH9 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.full source_pre length_pre bytes )
  **  (UCharArray.seg data_pre 0 (cursor_pre + index ) (app (prefix) ((sublist (0) (index) (bytes)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + index ) capacity_pre )
|--
  “ (index < length_pre) ” 
  &&  “ (0 < length_pre) ” 
  &&  “ ((Zlength (bytes)) = length_pre) ” 
  &&  “ (source_pre <> 0) ” 
  &&  “ (0 <= index) ” 
  &&  “ (index <= length_pre) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ ((cursor_pre + length_pre ) <= capacity_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ”
  &&  (((data_pre + ((cursor_pre + index ) * sizeof(UCHAR)))) # UChar  |->_)
  **  (UCharArray.undef_seg data_pre ((cursor_pre + index ) + 1 ) capacity_pre )
  **  (UCharArray.full source_pre length_pre bytes )
  **  (UCharArray.seg data_pre 0 (cursor_pre + index ) (app (prefix) ((sublist (0) (index) (bytes)))) )
.

Module Type VC_Correct.


Axiom proof_of_cmc_copy_bytes_safety_wit_1 : cmc_copy_bytes_safety_wit_1.
Axiom proof_of_cmc_copy_bytes_safety_wit_2 : cmc_copy_bytes_safety_wit_2.
Axiom proof_of_cmc_copy_bytes_safety_wit_3 : cmc_copy_bytes_safety_wit_3.
Axiom proof_of_cmc_copy_bytes_safety_wit_4 : cmc_copy_bytes_safety_wit_4.
Axiom proof_of_cmc_copy_bytes_safety_wit_5 : cmc_copy_bytes_safety_wit_5.
Axiom proof_of_cmc_copy_bytes_entail_wit_1 : cmc_copy_bytes_entail_wit_1.
Axiom proof_of_cmc_copy_bytes_entail_wit_2 : cmc_copy_bytes_entail_wit_2.
Axiom proof_of_cmc_copy_bytes_return_wit_1 : cmc_copy_bytes_return_wit_1.
Axiom proof_of_cmc_copy_bytes_return_wit_2 : cmc_copy_bytes_return_wit_2.
Axiom proof_of_cmc_copy_bytes_partial_solve_wit_1 : cmc_copy_bytes_partial_solve_wit_1.
Axiom proof_of_cmc_copy_bytes_partial_solve_wit_2 : cmc_copy_bytes_partial_solve_wit_2.

End VC_Correct.
