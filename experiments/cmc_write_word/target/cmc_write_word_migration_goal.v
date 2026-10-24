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

(*----- Function cmc_write_word -----*)

Definition cmc_write_word_safety_wit_1 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH3 : (capacity_pre <= INT_MAX)) ,
  ((( &( "b0" ) )) # UChar  |->_)
  **  ((( &( "bits" ) )) # UInt64  |-> (unsigned_last_nbits (word_value_pre) (64)))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (256 <> 0) ”
.

Definition cmc_write_word_safety_wit_2 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH3 : (capacity_pre <= INT_MAX)) ,
  ((( &( "b1" ) )) # UChar  |->_)
  **  ((( &( "b0" ) )) # UChar  |-> (unsigned_last_nbits (((unsigned_last_nbits (word_value_pre) (64)) % ( 256 ) )) (8)))
  **  ((( &( "bits" ) )) # UInt64  |-> (unsigned_last_nbits (word_value_pre) (64)))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (256 <> 0) ”
.

Definition cmc_write_word_safety_wit_3 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH3 : (capacity_pre <= INT_MAX)) ,
  ((( &( "b1" ) )) # UChar  |->_)
  **  ((( &( "b0" ) )) # UChar  |-> (unsigned_last_nbits (((unsigned_last_nbits (word_value_pre) (64)) % ( 256 ) )) (8)))
  **  ((( &( "bits" ) )) # UInt64  |-> (unsigned_last_nbits (word_value_pre) (64)))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (256 <> 0) ”
.

Definition cmc_write_word_safety_wit_4 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH3 : (capacity_pre <= INT_MAX)) ,
  ((( &( "b2" ) )) # UChar  |->_)
  **  ((( &( "b1" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 256 ) % ( 256 ) )) (8)))
  **  ((( &( "b0" ) )) # UChar  |-> (unsigned_last_nbits (((unsigned_last_nbits (word_value_pre) (64)) % ( 256 ) )) (8)))
  **  ((( &( "bits" ) )) # UInt64  |-> (unsigned_last_nbits (word_value_pre) (64)))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (256 <> 0) ”
.

Definition cmc_write_word_safety_wit_5 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH3 : (capacity_pre <= INT_MAX)) ,
  ((( &( "b2" ) )) # UChar  |->_)
  **  ((( &( "b1" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 256 ) % ( 256 ) )) (8)))
  **  ((( &( "b0" ) )) # UChar  |-> (unsigned_last_nbits (((unsigned_last_nbits (word_value_pre) (64)) % ( 256 ) )) (8)))
  **  ((( &( "bits" ) )) # UInt64  |-> (unsigned_last_nbits (word_value_pre) (64)))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (65536 <> 0) ”
.

Definition cmc_write_word_safety_wit_6 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH3 : (capacity_pre <= INT_MAX)) ,
  ((( &( "b3" ) )) # UChar  |->_)
  **  ((( &( "b2" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 65536 ) % ( 256 ) )) (8)))
  **  ((( &( "b1" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 256 ) % ( 256 ) )) (8)))
  **  ((( &( "b0" ) )) # UChar  |-> (unsigned_last_nbits (((unsigned_last_nbits (word_value_pre) (64)) % ( 256 ) )) (8)))
  **  ((( &( "bits" ) )) # UInt64  |-> (unsigned_last_nbits (word_value_pre) (64)))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (256 <> 0) ”
.

Definition cmc_write_word_safety_wit_7 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH3 : (capacity_pre <= INT_MAX)) ,
  ((( &( "b3" ) )) # UChar  |->_)
  **  ((( &( "b2" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 65536 ) % ( 256 ) )) (8)))
  **  ((( &( "b1" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 256 ) % ( 256 ) )) (8)))
  **  ((( &( "b0" ) )) # UChar  |-> (unsigned_last_nbits (((unsigned_last_nbits (word_value_pre) (64)) % ( 256 ) )) (8)))
  **  ((( &( "bits" ) )) # UInt64  |-> (unsigned_last_nbits (word_value_pre) (64)))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (16777216 <> 0) ”
.

Definition cmc_write_word_safety_wit_8 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH3 : (capacity_pre <= INT_MAX)) ,
  ((( &( "b4" ) )) # UChar  |->_)
  **  ((( &( "b3" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 16777216 ) % ( 256 ) )) (8)))
  **  ((( &( "b2" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 65536 ) % ( 256 ) )) (8)))
  **  ((( &( "b1" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 256 ) % ( 256 ) )) (8)))
  **  ((( &( "b0" ) )) # UChar  |-> (unsigned_last_nbits (((unsigned_last_nbits (word_value_pre) (64)) % ( 256 ) )) (8)))
  **  ((( &( "bits" ) )) # UInt64  |-> (unsigned_last_nbits (word_value_pre) (64)))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (256 <> 0) ”
.

Definition cmc_write_word_safety_wit_9 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH3 : (capacity_pre <= INT_MAX)) ,
  ((( &( "b4" ) )) # UChar  |->_)
  **  ((( &( "b3" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 16777216 ) % ( 256 ) )) (8)))
  **  ((( &( "b2" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 65536 ) % ( 256 ) )) (8)))
  **  ((( &( "b1" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 256 ) % ( 256 ) )) (8)))
  **  ((( &( "b0" ) )) # UChar  |-> (unsigned_last_nbits (((unsigned_last_nbits (word_value_pre) (64)) % ( 256 ) )) (8)))
  **  ((( &( "bits" ) )) # UInt64  |-> (unsigned_last_nbits (word_value_pre) (64)))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (4294967296 <> 0) ”
.

Definition cmc_write_word_safety_wit_10 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH3 : (capacity_pre <= INT_MAX)) ,
  ((( &( "b5" ) )) # UChar  |->_)
  **  ((( &( "b4" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 4294967296 ) % ( 256 ) )) (8)))
  **  ((( &( "b3" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 16777216 ) % ( 256 ) )) (8)))
  **  ((( &( "b2" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 65536 ) % ( 256 ) )) (8)))
  **  ((( &( "b1" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 256 ) % ( 256 ) )) (8)))
  **  ((( &( "b0" ) )) # UChar  |-> (unsigned_last_nbits (((unsigned_last_nbits (word_value_pre) (64)) % ( 256 ) )) (8)))
  **  ((( &( "bits" ) )) # UInt64  |-> (unsigned_last_nbits (word_value_pre) (64)))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (256 <> 0) ”
.

Definition cmc_write_word_safety_wit_11 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH3 : (capacity_pre <= INT_MAX)) ,
  ((( &( "b5" ) )) # UChar  |->_)
  **  ((( &( "b4" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 4294967296 ) % ( 256 ) )) (8)))
  **  ((( &( "b3" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 16777216 ) % ( 256 ) )) (8)))
  **  ((( &( "b2" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 65536 ) % ( 256 ) )) (8)))
  **  ((( &( "b1" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 256 ) % ( 256 ) )) (8)))
  **  ((( &( "b0" ) )) # UChar  |-> (unsigned_last_nbits (((unsigned_last_nbits (word_value_pre) (64)) % ( 256 ) )) (8)))
  **  ((( &( "bits" ) )) # UInt64  |-> (unsigned_last_nbits (word_value_pre) (64)))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (1099511627776 <> 0) ”
.

Definition cmc_write_word_safety_wit_12 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH3 : (capacity_pre <= INT_MAX)) ,
  ((( &( "b6" ) )) # UChar  |->_)
  **  ((( &( "b5" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 1099511627776 ) % ( 256 ) )) (8)))
  **  ((( &( "b4" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 4294967296 ) % ( 256 ) )) (8)))
  **  ((( &( "b3" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 16777216 ) % ( 256 ) )) (8)))
  **  ((( &( "b2" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 65536 ) % ( 256 ) )) (8)))
  **  ((( &( "b1" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 256 ) % ( 256 ) )) (8)))
  **  ((( &( "b0" ) )) # UChar  |-> (unsigned_last_nbits (((unsigned_last_nbits (word_value_pre) (64)) % ( 256 ) )) (8)))
  **  ((( &( "bits" ) )) # UInt64  |-> (unsigned_last_nbits (word_value_pre) (64)))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (256 <> 0) ”
.

Definition cmc_write_word_safety_wit_13 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH3 : (capacity_pre <= INT_MAX)) ,
  ((( &( "b6" ) )) # UChar  |->_)
  **  ((( &( "b5" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 1099511627776 ) % ( 256 ) )) (8)))
  **  ((( &( "b4" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 4294967296 ) % ( 256 ) )) (8)))
  **  ((( &( "b3" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 16777216 ) % ( 256 ) )) (8)))
  **  ((( &( "b2" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 65536 ) % ( 256 ) )) (8)))
  **  ((( &( "b1" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 256 ) % ( 256 ) )) (8)))
  **  ((( &( "b0" ) )) # UChar  |-> (unsigned_last_nbits (((unsigned_last_nbits (word_value_pre) (64)) % ( 256 ) )) (8)))
  **  ((( &( "bits" ) )) # UInt64  |-> (unsigned_last_nbits (word_value_pre) (64)))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (281474976710656 <> 0) ”
.

Definition cmc_write_word_safety_wit_14 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH3 : (capacity_pre <= INT_MAX)) ,
  ((( &( "b7" ) )) # UChar  |->_)
  **  ((( &( "b6" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 281474976710656 ) % ( 256 ) )) (8)))
  **  ((( &( "b5" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 1099511627776 ) % ( 256 ) )) (8)))
  **  ((( &( "b4" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 4294967296 ) % ( 256 ) )) (8)))
  **  ((( &( "b3" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 16777216 ) % ( 256 ) )) (8)))
  **  ((( &( "b2" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 65536 ) % ( 256 ) )) (8)))
  **  ((( &( "b1" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 256 ) % ( 256 ) )) (8)))
  **  ((( &( "b0" ) )) # UChar  |-> (unsigned_last_nbits (((unsigned_last_nbits (word_value_pre) (64)) % ( 256 ) )) (8)))
  **  ((( &( "bits" ) )) # UInt64  |-> (unsigned_last_nbits (word_value_pre) (64)))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (256 <> 0) ”
.

Definition cmc_write_word_safety_wit_15 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH3 : (capacity_pre <= INT_MAX)) ,
  ((( &( "b7" ) )) # UChar  |->_)
  **  ((( &( "b6" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 281474976710656 ) % ( 256 ) )) (8)))
  **  ((( &( "b5" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 1099511627776 ) % ( 256 ) )) (8)))
  **  ((( &( "b4" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 4294967296 ) % ( 256 ) )) (8)))
  **  ((( &( "b3" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 16777216 ) % ( 256 ) )) (8)))
  **  ((( &( "b2" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 65536 ) % ( 256 ) )) (8)))
  **  ((( &( "b1" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 256 ) % ( 256 ) )) (8)))
  **  ((( &( "b0" ) )) # UChar  |-> (unsigned_last_nbits (((unsigned_last_nbits (word_value_pre) (64)) % ( 256 ) )) (8)))
  **  ((( &( "bits" ) )) # UInt64  |-> (unsigned_last_nbits (word_value_pre) (64)))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (72057594037927936 <> 0) ”
.

Definition cmc_write_word_safety_wit_16 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH3 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 (cursor_pre + 1 ) (app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 1 ) capacity_pre )
  **  ((( &( "b7" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 72057594037927936 ) % ( 256 ) )) (8)))
  **  ((( &( "b6" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 281474976710656 ) % ( 256 ) )) (8)))
  **  ((( &( "b5" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 1099511627776 ) % ( 256 ) )) (8)))
  **  ((( &( "b4" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 4294967296 ) % ( 256 ) )) (8)))
  **  ((( &( "b3" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 16777216 ) % ( 256 ) )) (8)))
  **  ((( &( "b2" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 65536 ) % ( 256 ) )) (8)))
  **  ((( &( "b1" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 256 ) % ( 256 ) )) (8)))
  **  ((( &( "b0" ) )) # UChar  |-> (unsigned_last_nbits (((unsigned_last_nbits (word_value_pre) (64)) % ( 256 ) )) (8)))
  **  ((( &( "bits" ) )) # UInt64  |-> (unsigned_last_nbits (word_value_pre) (64)))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
|--
  “ ((cursor_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cursor_pre + 1 )) ”
.

Definition cmc_write_word_safety_wit_17 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH3 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 (cursor_pre + 1 ) (app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 1 ) capacity_pre )
  **  ((( &( "b7" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 72057594037927936 ) % ( 256 ) )) (8)))
  **  ((( &( "b6" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 281474976710656 ) % ( 256 ) )) (8)))
  **  ((( &( "b5" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 1099511627776 ) % ( 256 ) )) (8)))
  **  ((( &( "b4" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 4294967296 ) % ( 256 ) )) (8)))
  **  ((( &( "b3" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 16777216 ) % ( 256 ) )) (8)))
  **  ((( &( "b2" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 65536 ) % ( 256 ) )) (8)))
  **  ((( &( "b1" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 256 ) % ( 256 ) )) (8)))
  **  ((( &( "b0" ) )) # UChar  |-> (unsigned_last_nbits (((unsigned_last_nbits (word_value_pre) (64)) % ( 256 ) )) (8)))
  **  ((( &( "bits" ) )) # UInt64  |-> (unsigned_last_nbits (word_value_pre) (64)))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmc_write_word_safety_wit_18 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 2 ) (app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 2 ) capacity_pre )
|--
  “ ((cursor_pre + 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cursor_pre + 2 )) ”
.

Definition cmc_write_word_safety_wit_19 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 2 ) (app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 2 ) capacity_pre )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition cmc_write_word_safety_wit_20 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 3 ) (app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 3 ) capacity_pre )
|--
  “ ((cursor_pre + 3 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cursor_pre + 3 )) ”
.

Definition cmc_write_word_safety_wit_21 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 3 ) (app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 3 ) capacity_pre )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition cmc_write_word_safety_wit_22 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 4 ) (app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 4 ) capacity_pre )
|--
  “ ((cursor_pre + 4 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cursor_pre + 4 )) ”
.

Definition cmc_write_word_safety_wit_23 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 4 ) (app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 4 ) capacity_pre )
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition cmc_write_word_safety_wit_24 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 5 ) (app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 5 ) capacity_pre )
|--
  “ ((cursor_pre + 5 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cursor_pre + 5 )) ”
.

Definition cmc_write_word_safety_wit_25 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 5 ) (app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 5 ) capacity_pre )
|--
  “ (5 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 5) ”
.

Definition cmc_write_word_safety_wit_26 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 6 ) (app ((app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (5))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 6 ) capacity_pre )
|--
  “ ((cursor_pre + 6 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cursor_pre + 6 )) ”
.

Definition cmc_write_word_safety_wit_27 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 6 ) (app ((app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (5))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 6 ) capacity_pre )
|--
  “ (6 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 6) ”
.

Definition cmc_write_word_safety_wit_28 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 7 ) (app ((app ((app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (5))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (6))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 7 ) capacity_pre )
|--
  “ ((cursor_pre + 7 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cursor_pre + 7 )) ”
.

Definition cmc_write_word_safety_wit_29 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 7 ) (app ((app ((app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (5))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (6))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 7 ) capacity_pre )
|--
  “ (7 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 7) ”
.

Definition cmc_write_word_entail_wit_1 := 
(
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH3 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + 1 ) + 1 ) (app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre ((cursor_pre + 1 ) + 1 ) capacity_pre )
|--
  “ ((unsigned_last_nbits (((unsigned_last_nbits (word_value_pre) (64)) % ( 256 ) )) (8)) = (tower_encode_byte (word_value_pre) (0))) ” 
  &&  “ ((unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 256 ) % ( 256 ) )) (8)) = (tower_encode_byte (word_value_pre) (1))) ” 
  &&  “ ((unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 65536 ) % ( 256 ) )) (8)) = (tower_encode_byte (word_value_pre) (2))) ” 
  &&  “ ((unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 16777216 ) % ( 256 ) )) (8)) = (tower_encode_byte (word_value_pre) (3))) ” 
  &&  “ ((unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 4294967296 ) % ( 256 ) )) (8)) = (tower_encode_byte (word_value_pre) (4))) ” 
  &&  “ ((unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 1099511627776 ) % ( 256 ) )) (8)) = (tower_encode_byte (word_value_pre) (5))) ” 
  &&  “ ((unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 281474976710656 ) % ( 256 ) )) (8)) = (tower_encode_byte (word_value_pre) (6))) ” 
  &&  “ ((unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 72057594037927936 ) % ( 256 ) )) (8)) = (tower_encode_byte (word_value_pre) (7))) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ ((cursor_pre + 8 ) <= capacity_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ”
  &&  (UCharArray.seg data_pre 0 (cursor_pre + 2 ) (app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 2 ) capacity_pre )
) \/
(
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH3 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + 1 ) + 1 ) (app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z))))) )
|--
  “ ((unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 72057594037927936 ) % ( 256 ) )) (8)) = (tower_encode_byte (word_value_pre) (7))) ” 
  &&  “ ((unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 281474976710656 ) % ( 256 ) )) (8)) = (tower_encode_byte (word_value_pre) (6))) ” 
  &&  “ ((unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 1099511627776 ) % ( 256 ) )) (8)) = (tower_encode_byte (word_value_pre) (5))) ” 
  &&  “ ((unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 4294967296 ) % ( 256 ) )) (8)) = (tower_encode_byte (word_value_pre) (4))) ” 
  &&  “ ((unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 16777216 ) % ( 256 ) )) (8)) = (tower_encode_byte (word_value_pre) (3))) ” 
  &&  “ ((unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 65536 ) % ( 256 ) )) (8)) = (tower_encode_byte (word_value_pre) (2))) ” 
  &&  “ ((unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 256 ) % ( 256 ) )) (8)) = (tower_encode_byte (word_value_pre) (1))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (word_value_pre) (64)) % ( 256 ) )) (8)) = (tower_encode_byte (word_value_pre) (0))) ”
  &&  (UCharArray.seg data_pre 0 (cursor_pre + 2 ) (app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z))))) )
).

Definition cmc_write_word_entail_wit_1_split_goal_1 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH3 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + 1 ) + 1 ) (app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z))))) )
|--
  “ ((unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 72057594037927936 ) % ( 256 ) )) (8)) = (tower_encode_byte (word_value_pre) (7))) ”
.

Definition cmc_write_word_entail_wit_1_split_goal_2 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH3 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + 1 ) + 1 ) (app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z))))) )
|--
  “ ((unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 281474976710656 ) % ( 256 ) )) (8)) = (tower_encode_byte (word_value_pre) (6))) ”
.

Definition cmc_write_word_entail_wit_1_split_goal_3 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH3 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + 1 ) + 1 ) (app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z))))) )
|--
  “ ((unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 1099511627776 ) % ( 256 ) )) (8)) = (tower_encode_byte (word_value_pre) (5))) ”
.

Definition cmc_write_word_entail_wit_1_split_goal_4 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH3 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + 1 ) + 1 ) (app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z))))) )
|--
  “ ((unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 4294967296 ) % ( 256 ) )) (8)) = (tower_encode_byte (word_value_pre) (4))) ”
.

Definition cmc_write_word_entail_wit_1_split_goal_5 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH3 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + 1 ) + 1 ) (app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z))))) )
|--
  “ ((unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 16777216 ) % ( 256 ) )) (8)) = (tower_encode_byte (word_value_pre) (3))) ”
.

Definition cmc_write_word_entail_wit_1_split_goal_6 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH3 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + 1 ) + 1 ) (app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z))))) )
|--
  “ ((unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 65536 ) % ( 256 ) )) (8)) = (tower_encode_byte (word_value_pre) (2))) ”
.

Definition cmc_write_word_entail_wit_1_split_goal_7 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH3 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + 1 ) + 1 ) (app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z))))) )
|--
  “ ((unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 256 ) % ( 256 ) )) (8)) = (tower_encode_byte (word_value_pre) (1))) ”
.

Definition cmc_write_word_entail_wit_1_split_goal_8 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH3 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + 1 ) + 1 ) (app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z))))) )
|--
  “ ((unsigned_last_nbits (((unsigned_last_nbits (word_value_pre) (64)) % ( 256 ) )) (8)) = (tower_encode_byte (word_value_pre) (0))) ”
.

Definition cmc_write_word_entail_wit_1_split_goal_spatial := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH3 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + 1 ) + 1 ) (app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z))))) )
|--
  (UCharArray.seg data_pre 0 (cursor_pre + 2 ) (app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z))))) )
.

Definition cmc_write_word_entail_wit_2 := 
(
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + 2 ) + 1 ) (app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre ((cursor_pre + 2 ) + 1 ) capacity_pre )
|--
  “ (b0 = (tower_encode_byte (word_value_pre) (0))) ” 
  &&  “ (b1 = (tower_encode_byte (word_value_pre) (1))) ” 
  &&  “ (b2 = (tower_encode_byte (word_value_pre) (2))) ” 
  &&  “ (b3 = (tower_encode_byte (word_value_pre) (3))) ” 
  &&  “ (b4 = (tower_encode_byte (word_value_pre) (4))) ” 
  &&  “ (b5 = (tower_encode_byte (word_value_pre) (5))) ” 
  &&  “ (b6 = (tower_encode_byte (word_value_pre) (6))) ” 
  &&  “ (b7 = (tower_encode_byte (word_value_pre) (7))) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ ((cursor_pre + 8 ) <= capacity_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ”
  &&  (UCharArray.seg data_pre 0 (cursor_pre + 3 ) (app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 3 ) capacity_pre )
) \/
(
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + 2 ) + 1 ) (app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z))))) )
|--
  (UCharArray.seg data_pre 0 (cursor_pre + 3 ) (app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z))))) )
).

Definition cmc_write_word_entail_wit_2_split_goal_spatial := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + 2 ) + 1 ) (app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z))))) )
|--
  (UCharArray.seg data_pre 0 (cursor_pre + 3 ) (app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z))))) )
.

Definition cmc_write_word_entail_wit_3 := 
(
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + 3 ) + 1 ) (app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre ((cursor_pre + 3 ) + 1 ) capacity_pre )
|--
  “ (b0 = (tower_encode_byte (word_value_pre) (0))) ” 
  &&  “ (b1 = (tower_encode_byte (word_value_pre) (1))) ” 
  &&  “ (b2 = (tower_encode_byte (word_value_pre) (2))) ” 
  &&  “ (b3 = (tower_encode_byte (word_value_pre) (3))) ” 
  &&  “ (b4 = (tower_encode_byte (word_value_pre) (4))) ” 
  &&  “ (b5 = (tower_encode_byte (word_value_pre) (5))) ” 
  &&  “ (b6 = (tower_encode_byte (word_value_pre) (6))) ” 
  &&  “ (b7 = (tower_encode_byte (word_value_pre) (7))) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ ((cursor_pre + 8 ) <= capacity_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ”
  &&  (UCharArray.seg data_pre 0 (cursor_pre + 4 ) (app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 4 ) capacity_pre )
) \/
(
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + 3 ) + 1 ) (app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z))))) )
|--
  (UCharArray.seg data_pre 0 (cursor_pre + 4 ) (app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z))))) )
).

Definition cmc_write_word_entail_wit_3_split_goal_spatial := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + 3 ) + 1 ) (app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z))))) )
|--
  (UCharArray.seg data_pre 0 (cursor_pre + 4 ) (app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z))))) )
.

Definition cmc_write_word_entail_wit_4 := 
(
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + 4 ) + 1 ) (app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre ((cursor_pre + 4 ) + 1 ) capacity_pre )
|--
  “ (b0 = (tower_encode_byte (word_value_pre) (0))) ” 
  &&  “ (b1 = (tower_encode_byte (word_value_pre) (1))) ” 
  &&  “ (b2 = (tower_encode_byte (word_value_pre) (2))) ” 
  &&  “ (b3 = (tower_encode_byte (word_value_pre) (3))) ” 
  &&  “ (b4 = (tower_encode_byte (word_value_pre) (4))) ” 
  &&  “ (b5 = (tower_encode_byte (word_value_pre) (5))) ” 
  &&  “ (b6 = (tower_encode_byte (word_value_pre) (6))) ” 
  &&  “ (b7 = (tower_encode_byte (word_value_pre) (7))) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ ((cursor_pre + 8 ) <= capacity_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ”
  &&  (UCharArray.seg data_pre 0 (cursor_pre + 5 ) (app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 5 ) capacity_pre )
) \/
(
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + 4 ) + 1 ) (app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z))))) )
|--
  (UCharArray.seg data_pre 0 (cursor_pre + 5 ) (app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z))))) )
).

Definition cmc_write_word_entail_wit_4_split_goal_spatial := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + 4 ) + 1 ) (app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z))))) )
|--
  (UCharArray.seg data_pre 0 (cursor_pre + 5 ) (app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z))))) )
.

Definition cmc_write_word_entail_wit_5 := 
(
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + 5 ) + 1 ) (app ((app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (5))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre ((cursor_pre + 5 ) + 1 ) capacity_pre )
|--
  “ (b0 = (tower_encode_byte (word_value_pre) (0))) ” 
  &&  “ (b1 = (tower_encode_byte (word_value_pre) (1))) ” 
  &&  “ (b2 = (tower_encode_byte (word_value_pre) (2))) ” 
  &&  “ (b3 = (tower_encode_byte (word_value_pre) (3))) ” 
  &&  “ (b4 = (tower_encode_byte (word_value_pre) (4))) ” 
  &&  “ (b5 = (tower_encode_byte (word_value_pre) (5))) ” 
  &&  “ (b6 = (tower_encode_byte (word_value_pre) (6))) ” 
  &&  “ (b7 = (tower_encode_byte (word_value_pre) (7))) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ ((cursor_pre + 8 ) <= capacity_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ”
  &&  (UCharArray.seg data_pre 0 (cursor_pre + 6 ) (app ((app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (5))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 6 ) capacity_pre )
) \/
(
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + 5 ) + 1 ) (app ((app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (5))) ((@nil Z))))) )
|--
  (UCharArray.seg data_pre 0 (cursor_pre + 6 ) (app ((app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (5))) ((@nil Z))))) )
).

Definition cmc_write_word_entail_wit_5_split_goal_spatial := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + 5 ) + 1 ) (app ((app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (5))) ((@nil Z))))) )
|--
  (UCharArray.seg data_pre 0 (cursor_pre + 6 ) (app ((app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (5))) ((@nil Z))))) )
.

Definition cmc_write_word_entail_wit_6 := 
(
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + 6 ) + 1 ) (app ((app ((app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (5))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (6))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre ((cursor_pre + 6 ) + 1 ) capacity_pre )
|--
  “ (b0 = (tower_encode_byte (word_value_pre) (0))) ” 
  &&  “ (b1 = (tower_encode_byte (word_value_pre) (1))) ” 
  &&  “ (b2 = (tower_encode_byte (word_value_pre) (2))) ” 
  &&  “ (b3 = (tower_encode_byte (word_value_pre) (3))) ” 
  &&  “ (b4 = (tower_encode_byte (word_value_pre) (4))) ” 
  &&  “ (b5 = (tower_encode_byte (word_value_pre) (5))) ” 
  &&  “ (b6 = (tower_encode_byte (word_value_pre) (6))) ” 
  &&  “ (b7 = (tower_encode_byte (word_value_pre) (7))) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ ((cursor_pre + 8 ) <= capacity_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ”
  &&  (UCharArray.seg data_pre 0 (cursor_pre + 7 ) (app ((app ((app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (5))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (6))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 7 ) capacity_pre )
) \/
(
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + 6 ) + 1 ) (app ((app ((app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (5))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (6))) ((@nil Z))))) )
|--
  (UCharArray.seg data_pre 0 (cursor_pre + 7 ) (app ((app ((app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (5))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (6))) ((@nil Z))))) )
).

Definition cmc_write_word_entail_wit_6_split_goal_spatial := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + 6 ) + 1 ) (app ((app ((app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (5))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (6))) ((@nil Z))))) )
|--
  (UCharArray.seg data_pre 0 (cursor_pre + 7 ) (app ((app ((app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (5))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (6))) ((@nil Z))))) )
.

Definition cmc_write_word_return_wit_1 := 
(
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + 7 ) + 1 ) (app ((app ((app ((app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (5))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (6))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (7))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre ((cursor_pre + 7 ) + 1 ) capacity_pre )
|--
  (UCharArray.seg data_pre 0 (cursor_pre + 8 ) (app (prefix) ((tower_word_bytes (word_value_pre)))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 8 ) capacity_pre )
) \/
(
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + 7 ) + 1 ) (app ((app ((app ((app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (5))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (6))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (7))) ((@nil Z))))) )
|--
  (UCharArray.seg data_pre 0 (cursor_pre + 8 ) (app (prefix) ((tower_word_bytes (word_value_pre)))) )
).

Definition cmc_write_word_return_wit_1_split_goal_spatial := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 ((cursor_pre + 7 ) + 1 ) (app ((app ((app ((app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (5))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (6))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (7))) ((@nil Z))))) )
|--
  (UCharArray.seg data_pre 0 (cursor_pre + 8 ) (app (prefix) ((tower_word_bytes (word_value_pre)))) )
.

Definition cmc_write_word_partial_solve_wit_1_pure := 
(
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH3 : (capacity_pre <= INT_MAX)) ,
  ((( &( "b7" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 72057594037927936 ) % ( 256 ) )) (8)))
  **  ((( &( "b6" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 281474976710656 ) % ( 256 ) )) (8)))
  **  ((( &( "b5" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 1099511627776 ) % ( 256 ) )) (8)))
  **  ((( &( "b4" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 4294967296 ) % ( 256 ) )) (8)))
  **  ((( &( "b3" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 16777216 ) % ( 256 ) )) (8)))
  **  ((( &( "b2" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 65536 ) % ( 256 ) )) (8)))
  **  ((( &( "b1" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 256 ) % ( 256 ) )) (8)))
  **  ((( &( "b0" ) )) # UChar  |-> (unsigned_last_nbits (((unsigned_last_nbits (word_value_pre) (64)) % ( 256 ) )) (8)))
  **  ((( &( "bits" ) )) # UInt64  |-> (unsigned_last_nbits (word_value_pre) (64)))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (0 <= cursor_pre) ” 
  &&  “ (cursor_pre < capacity_pre) ” 
  &&  “ ((tower_encode_byte (word_value_pre) (0)) < 256) ” 
  &&  “ (0 <= (tower_encode_byte (word_value_pre) (0))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (word_value_pre) (64)) % ( 256 ) )) (8)) = (tower_encode_byte (word_value_pre) (0))) ”
) \/
(
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : ((unsigned_last_nbits (word_value_pre) (64)) <= UINT64_MAX)) (PreH2 : ((unsigned_last_nbits (word_value_pre) (64)) >= 0)) (PreH3 : (word_value_pre <= INT64_MAX)) (PreH4 : (word_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  ((( &( "b7" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 72057594037927936 ) % ( 256 ) )) (8)))
  **  ((( &( "b6" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 281474976710656 ) % ( 256 ) )) (8)))
  **  ((( &( "b5" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 1099511627776 ) % ( 256 ) )) (8)))
  **  ((( &( "b4" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 4294967296 ) % ( 256 ) )) (8)))
  **  ((( &( "b3" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 16777216 ) % ( 256 ) )) (8)))
  **  ((( &( "b2" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 65536 ) % ( 256 ) )) (8)))
  **  ((( &( "b1" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 256 ) % ( 256 ) )) (8)))
  **  ((( &( "b0" ) )) # UChar  |-> (unsigned_last_nbits (((unsigned_last_nbits (word_value_pre) (64)) % ( 256 ) )) (8)))
  **  ((( &( "bits" ) )) # UInt64  |-> (unsigned_last_nbits (word_value_pre) (64)))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ ((unsigned_last_nbits (((unsigned_last_nbits (word_value_pre) (64)) % ( 256 ) )) (8)) = (tower_encode_byte (word_value_pre) (0))) ” 
  &&  “ (0 <= (tower_encode_byte (word_value_pre) (0))) ” 
  &&  “ ((tower_encode_byte (word_value_pre) (0)) < 256) ”
).

Definition cmc_write_word_partial_solve_wit_1_pure_split_goal_1 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : ((unsigned_last_nbits (word_value_pre) (64)) <= UINT64_MAX)) (PreH2 : ((unsigned_last_nbits (word_value_pre) (64)) >= 0)) (PreH3 : (word_value_pre <= INT64_MAX)) (PreH4 : (word_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  ((( &( "b7" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 72057594037927936 ) % ( 256 ) )) (8)))
  **  ((( &( "b6" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 281474976710656 ) % ( 256 ) )) (8)))
  **  ((( &( "b5" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 1099511627776 ) % ( 256 ) )) (8)))
  **  ((( &( "b4" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 4294967296 ) % ( 256 ) )) (8)))
  **  ((( &( "b3" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 16777216 ) % ( 256 ) )) (8)))
  **  ((( &( "b2" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 65536 ) % ( 256 ) )) (8)))
  **  ((( &( "b1" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 256 ) % ( 256 ) )) (8)))
  **  ((( &( "b0" ) )) # UChar  |-> (unsigned_last_nbits (((unsigned_last_nbits (word_value_pre) (64)) % ( 256 ) )) (8)))
  **  ((( &( "bits" ) )) # UInt64  |-> (unsigned_last_nbits (word_value_pre) (64)))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ ((unsigned_last_nbits (((unsigned_last_nbits (word_value_pre) (64)) % ( 256 ) )) (8)) = (tower_encode_byte (word_value_pre) (0))) ”
.

Definition cmc_write_word_partial_solve_wit_1_pure_split_goal_2 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : ((unsigned_last_nbits (word_value_pre) (64)) <= UINT64_MAX)) (PreH2 : ((unsigned_last_nbits (word_value_pre) (64)) >= 0)) (PreH3 : (word_value_pre <= INT64_MAX)) (PreH4 : (word_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  ((( &( "b7" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 72057594037927936 ) % ( 256 ) )) (8)))
  **  ((( &( "b6" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 281474976710656 ) % ( 256 ) )) (8)))
  **  ((( &( "b5" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 1099511627776 ) % ( 256 ) )) (8)))
  **  ((( &( "b4" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 4294967296 ) % ( 256 ) )) (8)))
  **  ((( &( "b3" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 16777216 ) % ( 256 ) )) (8)))
  **  ((( &( "b2" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 65536 ) % ( 256 ) )) (8)))
  **  ((( &( "b1" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 256 ) % ( 256 ) )) (8)))
  **  ((( &( "b0" ) )) # UChar  |-> (unsigned_last_nbits (((unsigned_last_nbits (word_value_pre) (64)) % ( 256 ) )) (8)))
  **  ((( &( "bits" ) )) # UInt64  |-> (unsigned_last_nbits (word_value_pre) (64)))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (0 <= (tower_encode_byte (word_value_pre) (0))) ”
.

Definition cmc_write_word_partial_solve_wit_1_pure_split_goal_3 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : ((unsigned_last_nbits (word_value_pre) (64)) <= UINT64_MAX)) (PreH2 : ((unsigned_last_nbits (word_value_pre) (64)) >= 0)) (PreH3 : (word_value_pre <= INT64_MAX)) (PreH4 : (word_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  ((( &( "b7" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 72057594037927936 ) % ( 256 ) )) (8)))
  **  ((( &( "b6" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 281474976710656 ) % ( 256 ) )) (8)))
  **  ((( &( "b5" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 1099511627776 ) % ( 256 ) )) (8)))
  **  ((( &( "b4" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 4294967296 ) % ( 256 ) )) (8)))
  **  ((( &( "b3" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 16777216 ) % ( 256 ) )) (8)))
  **  ((( &( "b2" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 65536 ) % ( 256 ) )) (8)))
  **  ((( &( "b1" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 256 ) % ( 256 ) )) (8)))
  **  ((( &( "b0" ) )) # UChar  |-> (unsigned_last_nbits (((unsigned_last_nbits (word_value_pre) (64)) % ( 256 ) )) (8)))
  **  ((( &( "bits" ) )) # UInt64  |-> (unsigned_last_nbits (word_value_pre) (64)))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ ((tower_encode_byte (word_value_pre) (0)) < 256) ”
.

Definition cmc_write_word_partial_solve_wit_1_aux := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH3 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (0 <= cursor_pre) ” 
  &&  “ (cursor_pre < capacity_pre) ” 
  &&  “ ((tower_encode_byte (word_value_pre) (0)) < 256) ” 
  &&  “ (0 <= (tower_encode_byte (word_value_pre) (0))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (word_value_pre) (64)) % ( 256 ) )) (8)) = (tower_encode_byte (word_value_pre) (0))) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ ((cursor_pre + 8 ) <= capacity_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ”
  &&  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
.

Definition cmc_write_word_partial_solve_wit_1 := cmc_write_word_partial_solve_wit_1_pure -> cmc_write_word_partial_solve_wit_1_aux.

Definition cmc_write_word_partial_solve_wit_2_pure := 
(
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH3 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 (cursor_pre + 1 ) (app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 1 ) capacity_pre )
  **  ((( &( "b7" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 72057594037927936 ) % ( 256 ) )) (8)))
  **  ((( &( "b6" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 281474976710656 ) % ( 256 ) )) (8)))
  **  ((( &( "b5" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 1099511627776 ) % ( 256 ) )) (8)))
  **  ((( &( "b4" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 4294967296 ) % ( 256 ) )) (8)))
  **  ((( &( "b3" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 16777216 ) % ( 256 ) )) (8)))
  **  ((( &( "b2" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 65536 ) % ( 256 ) )) (8)))
  **  ((( &( "b1" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 256 ) % ( 256 ) )) (8)))
  **  ((( &( "b0" ) )) # UChar  |-> (unsigned_last_nbits (((unsigned_last_nbits (word_value_pre) (64)) % ( 256 ) )) (8)))
  **  ((( &( "bits" ) )) # UInt64  |-> (unsigned_last_nbits (word_value_pre) (64)))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
|--
  “ (0 <= (cursor_pre + 1 )) ” 
  &&  “ ((cursor_pre + 1 ) < capacity_pre) ” 
  &&  “ ((tower_encode_byte (word_value_pre) (1)) < 256) ” 
  &&  “ (0 <= (tower_encode_byte (word_value_pre) (1))) ” 
  &&  “ ((unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 256 ) % ( 256 ) )) (8)) = (tower_encode_byte (word_value_pre) (1))) ”
) \/
(
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : ((unsigned_last_nbits (word_value_pre) (64)) <= UINT64_MAX)) (PreH2 : ((unsigned_last_nbits (word_value_pre) (64)) >= 0)) (PreH3 : (word_value_pre <= INT64_MAX)) (PreH4 : (word_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 (cursor_pre + 1 ) (app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 1 ) capacity_pre )
  **  ((( &( "b7" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 72057594037927936 ) % ( 256 ) )) (8)))
  **  ((( &( "b6" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 281474976710656 ) % ( 256 ) )) (8)))
  **  ((( &( "b5" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 1099511627776 ) % ( 256 ) )) (8)))
  **  ((( &( "b4" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 4294967296 ) % ( 256 ) )) (8)))
  **  ((( &( "b3" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 16777216 ) % ( 256 ) )) (8)))
  **  ((( &( "b2" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 65536 ) % ( 256 ) )) (8)))
  **  ((( &( "b1" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 256 ) % ( 256 ) )) (8)))
  **  ((( &( "b0" ) )) # UChar  |-> (unsigned_last_nbits (((unsigned_last_nbits (word_value_pre) (64)) % ( 256 ) )) (8)))
  **  ((( &( "bits" ) )) # UInt64  |-> (unsigned_last_nbits (word_value_pre) (64)))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
|--
  “ ((unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 256 ) % ( 256 ) )) (8)) = (tower_encode_byte (word_value_pre) (1))) ” 
  &&  “ (0 <= (tower_encode_byte (word_value_pre) (1))) ” 
  &&  “ ((tower_encode_byte (word_value_pre) (1)) < 256) ”
).

Definition cmc_write_word_partial_solve_wit_2_pure_split_goal_1 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : ((unsigned_last_nbits (word_value_pre) (64)) <= UINT64_MAX)) (PreH2 : ((unsigned_last_nbits (word_value_pre) (64)) >= 0)) (PreH3 : (word_value_pre <= INT64_MAX)) (PreH4 : (word_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 (cursor_pre + 1 ) (app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 1 ) capacity_pre )
  **  ((( &( "b7" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 72057594037927936 ) % ( 256 ) )) (8)))
  **  ((( &( "b6" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 281474976710656 ) % ( 256 ) )) (8)))
  **  ((( &( "b5" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 1099511627776 ) % ( 256 ) )) (8)))
  **  ((( &( "b4" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 4294967296 ) % ( 256 ) )) (8)))
  **  ((( &( "b3" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 16777216 ) % ( 256 ) )) (8)))
  **  ((( &( "b2" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 65536 ) % ( 256 ) )) (8)))
  **  ((( &( "b1" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 256 ) % ( 256 ) )) (8)))
  **  ((( &( "b0" ) )) # UChar  |-> (unsigned_last_nbits (((unsigned_last_nbits (word_value_pre) (64)) % ( 256 ) )) (8)))
  **  ((( &( "bits" ) )) # UInt64  |-> (unsigned_last_nbits (word_value_pre) (64)))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
|--
  “ ((unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 256 ) % ( 256 ) )) (8)) = (tower_encode_byte (word_value_pre) (1))) ”
.

Definition cmc_write_word_partial_solve_wit_2_pure_split_goal_2 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : ((unsigned_last_nbits (word_value_pre) (64)) <= UINT64_MAX)) (PreH2 : ((unsigned_last_nbits (word_value_pre) (64)) >= 0)) (PreH3 : (word_value_pre <= INT64_MAX)) (PreH4 : (word_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 (cursor_pre + 1 ) (app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 1 ) capacity_pre )
  **  ((( &( "b7" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 72057594037927936 ) % ( 256 ) )) (8)))
  **  ((( &( "b6" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 281474976710656 ) % ( 256 ) )) (8)))
  **  ((( &( "b5" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 1099511627776 ) % ( 256 ) )) (8)))
  **  ((( &( "b4" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 4294967296 ) % ( 256 ) )) (8)))
  **  ((( &( "b3" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 16777216 ) % ( 256 ) )) (8)))
  **  ((( &( "b2" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 65536 ) % ( 256 ) )) (8)))
  **  ((( &( "b1" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 256 ) % ( 256 ) )) (8)))
  **  ((( &( "b0" ) )) # UChar  |-> (unsigned_last_nbits (((unsigned_last_nbits (word_value_pre) (64)) % ( 256 ) )) (8)))
  **  ((( &( "bits" ) )) # UInt64  |-> (unsigned_last_nbits (word_value_pre) (64)))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
|--
  “ (0 <= (tower_encode_byte (word_value_pre) (1))) ”
.

Definition cmc_write_word_partial_solve_wit_2_pure_split_goal_3 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : ((unsigned_last_nbits (word_value_pre) (64)) <= UINT64_MAX)) (PreH2 : ((unsigned_last_nbits (word_value_pre) (64)) >= 0)) (PreH3 : (word_value_pre <= INT64_MAX)) (PreH4 : (word_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 (cursor_pre + 1 ) (app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 1 ) capacity_pre )
  **  ((( &( "b7" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 72057594037927936 ) % ( 256 ) )) (8)))
  **  ((( &( "b6" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 281474976710656 ) % ( 256 ) )) (8)))
  **  ((( &( "b5" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 1099511627776 ) % ( 256 ) )) (8)))
  **  ((( &( "b4" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 4294967296 ) % ( 256 ) )) (8)))
  **  ((( &( "b3" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 16777216 ) % ( 256 ) )) (8)))
  **  ((( &( "b2" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 65536 ) % ( 256 ) )) (8)))
  **  ((( &( "b1" ) )) # UChar  |-> (unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 256 ) % ( 256 ) )) (8)))
  **  ((( &( "b0" ) )) # UChar  |-> (unsigned_last_nbits (((unsigned_last_nbits (word_value_pre) (64)) % ( 256 ) )) (8)))
  **  ((( &( "bits" ) )) # UInt64  |-> (unsigned_last_nbits (word_value_pre) (64)))
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
|--
  “ ((tower_encode_byte (word_value_pre) (1)) < 256) ”
.

Definition cmc_write_word_partial_solve_wit_2_aux := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH3 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 (cursor_pre + 1 ) (app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 1 ) capacity_pre )
|--
  “ (0 <= (cursor_pre + 1 )) ” 
  &&  “ ((cursor_pre + 1 ) < capacity_pre) ” 
  &&  “ ((tower_encode_byte (word_value_pre) (1)) < 256) ” 
  &&  “ (0 <= (tower_encode_byte (word_value_pre) (1))) ” 
  &&  “ ((unsigned_last_nbits ((((unsigned_last_nbits (word_value_pre) (64)) ÷ 256 ) % ( 256 ) )) (8)) = (tower_encode_byte (word_value_pre) (1))) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ ((cursor_pre + 8 ) <= capacity_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ”
  &&  (UCharArray.seg data_pre 0 (cursor_pre + 1 ) (app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 1 ) capacity_pre )
.

Definition cmc_write_word_partial_solve_wit_2 := cmc_write_word_partial_solve_wit_2_pure -> cmc_write_word_partial_solve_wit_2_aux.

Definition cmc_write_word_partial_solve_wit_3_pure := 
(
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 2 ) (app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 2 ) capacity_pre )
|--
  “ (0 <= (cursor_pre + 2 )) ” 
  &&  “ ((cursor_pre + 2 ) < capacity_pre) ” 
  &&  “ (b2 = (tower_encode_byte (word_value_pre) (2))) ” 
  &&  “ (0 <= (tower_encode_byte (word_value_pre) (2))) ” 
  &&  “ ((tower_encode_byte (word_value_pre) (2)) < 256) ” 
  &&  “ (b2 < 256) ” 
  &&  “ (0 <= b2) ”
) \/
(
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (bits_value <= UINT64_MAX)) (PreH2 : (bits_value >= 0)) (PreH3 : (word_value_pre <= INT64_MAX)) (PreH4 : (word_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH10 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH11 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH12 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH13 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH14 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH15 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH16 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH17 : (0 <= cursor_pre)) (PreH18 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH19 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 2 ) (app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 2 ) capacity_pre )
|--
  “ (0 <= b2) ” 
  &&  “ (b2 < 256) ” 
  &&  “ (b2 < 256) ” 
  &&  “ (0 <= b2) ”
).

Definition cmc_write_word_partial_solve_wit_3_pure_split_goal_1 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (bits_value <= UINT64_MAX)) (PreH2 : (bits_value >= 0)) (PreH3 : (word_value_pre <= INT64_MAX)) (PreH4 : (word_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH10 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH11 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH12 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH13 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH14 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH15 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH16 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH17 : (0 <= cursor_pre)) (PreH18 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH19 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 2 ) (app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 2 ) capacity_pre )
|--
  “ (0 <= b2) ”
.

Definition cmc_write_word_partial_solve_wit_3_pure_split_goal_2 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (bits_value <= UINT64_MAX)) (PreH2 : (bits_value >= 0)) (PreH3 : (word_value_pre <= INT64_MAX)) (PreH4 : (word_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH10 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH11 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH12 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH13 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH14 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH15 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH16 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH17 : (0 <= cursor_pre)) (PreH18 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH19 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 2 ) (app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 2 ) capacity_pre )
|--
  “ (b2 < 256) ”
.

Definition cmc_write_word_partial_solve_wit_3_pure_split_goal_3 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (bits_value <= UINT64_MAX)) (PreH2 : (bits_value >= 0)) (PreH3 : (word_value_pre <= INT64_MAX)) (PreH4 : (word_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH10 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH11 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH12 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH13 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH14 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH15 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH16 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH17 : (0 <= cursor_pre)) (PreH18 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH19 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 2 ) (app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 2 ) capacity_pre )
|--
  “ (b2 < 256) ”
.

Definition cmc_write_word_partial_solve_wit_3_pure_split_goal_4 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (bits_value <= UINT64_MAX)) (PreH2 : (bits_value >= 0)) (PreH3 : (word_value_pre <= INT64_MAX)) (PreH4 : (word_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH10 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH11 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH12 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH13 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH14 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH15 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH16 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH17 : (0 <= cursor_pre)) (PreH18 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH19 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 2 ) (app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 2 ) capacity_pre )
|--
  “ (0 <= b2) ”
.

Definition cmc_write_word_partial_solve_wit_3_aux := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 (cursor_pre + 2 ) (app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 2 ) capacity_pre )
|--
  “ (0 <= (cursor_pre + 2 )) ” 
  &&  “ ((cursor_pre + 2 ) < capacity_pre) ” 
  &&  “ (b2 = (tower_encode_byte (word_value_pre) (2))) ” 
  &&  “ (0 <= (tower_encode_byte (word_value_pre) (2))) ” 
  &&  “ ((tower_encode_byte (word_value_pre) (2)) < 256) ” 
  &&  “ (b2 < 256) ” 
  &&  “ (0 <= b2) ” 
  &&  “ (b0 = (tower_encode_byte (word_value_pre) (0))) ” 
  &&  “ (b1 = (tower_encode_byte (word_value_pre) (1))) ” 
  &&  “ (b2 = (tower_encode_byte (word_value_pre) (2))) ” 
  &&  “ (b3 = (tower_encode_byte (word_value_pre) (3))) ” 
  &&  “ (b4 = (tower_encode_byte (word_value_pre) (4))) ” 
  &&  “ (b5 = (tower_encode_byte (word_value_pre) (5))) ” 
  &&  “ (b6 = (tower_encode_byte (word_value_pre) (6))) ” 
  &&  “ (b7 = (tower_encode_byte (word_value_pre) (7))) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ ((cursor_pre + 8 ) <= capacity_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ”
  &&  (UCharArray.seg data_pre 0 (cursor_pre + 2 ) (app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 2 ) capacity_pre )
.

Definition cmc_write_word_partial_solve_wit_3 := cmc_write_word_partial_solve_wit_3_pure -> cmc_write_word_partial_solve_wit_3_aux.

Definition cmc_write_word_partial_solve_wit_4_pure := 
(
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 3 ) (app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 3 ) capacity_pre )
|--
  “ (0 <= (cursor_pre + 3 )) ” 
  &&  “ ((cursor_pre + 3 ) < capacity_pre) ” 
  &&  “ (b3 = (tower_encode_byte (word_value_pre) (3))) ” 
  &&  “ (0 <= (tower_encode_byte (word_value_pre) (3))) ” 
  &&  “ ((tower_encode_byte (word_value_pre) (3)) < 256) ” 
  &&  “ (b3 < 256) ” 
  &&  “ (0 <= b3) ”
) \/
(
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (bits_value <= UINT64_MAX)) (PreH2 : (bits_value >= 0)) (PreH3 : (word_value_pre <= INT64_MAX)) (PreH4 : (word_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH10 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH11 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH12 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH13 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH14 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH15 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH16 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH17 : (0 <= cursor_pre)) (PreH18 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH19 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 3 ) (app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 3 ) capacity_pre )
|--
  “ (0 <= b3) ” 
  &&  “ (b3 < 256) ” 
  &&  “ (b3 < 256) ” 
  &&  “ (0 <= b3) ”
).

Definition cmc_write_word_partial_solve_wit_4_pure_split_goal_1 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (bits_value <= UINT64_MAX)) (PreH2 : (bits_value >= 0)) (PreH3 : (word_value_pre <= INT64_MAX)) (PreH4 : (word_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH10 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH11 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH12 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH13 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH14 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH15 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH16 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH17 : (0 <= cursor_pre)) (PreH18 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH19 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 3 ) (app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 3 ) capacity_pre )
|--
  “ (0 <= b3) ”
.

Definition cmc_write_word_partial_solve_wit_4_pure_split_goal_2 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (bits_value <= UINT64_MAX)) (PreH2 : (bits_value >= 0)) (PreH3 : (word_value_pre <= INT64_MAX)) (PreH4 : (word_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH10 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH11 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH12 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH13 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH14 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH15 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH16 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH17 : (0 <= cursor_pre)) (PreH18 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH19 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 3 ) (app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 3 ) capacity_pre )
|--
  “ (b3 < 256) ”
.

Definition cmc_write_word_partial_solve_wit_4_pure_split_goal_3 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (bits_value <= UINT64_MAX)) (PreH2 : (bits_value >= 0)) (PreH3 : (word_value_pre <= INT64_MAX)) (PreH4 : (word_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH10 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH11 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH12 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH13 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH14 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH15 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH16 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH17 : (0 <= cursor_pre)) (PreH18 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH19 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 3 ) (app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 3 ) capacity_pre )
|--
  “ (b3 < 256) ”
.

Definition cmc_write_word_partial_solve_wit_4_pure_split_goal_4 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (bits_value <= UINT64_MAX)) (PreH2 : (bits_value >= 0)) (PreH3 : (word_value_pre <= INT64_MAX)) (PreH4 : (word_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH10 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH11 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH12 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH13 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH14 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH15 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH16 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH17 : (0 <= cursor_pre)) (PreH18 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH19 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 3 ) (app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 3 ) capacity_pre )
|--
  “ (0 <= b3) ”
.

Definition cmc_write_word_partial_solve_wit_4_aux := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 (cursor_pre + 3 ) (app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 3 ) capacity_pre )
|--
  “ (0 <= (cursor_pre + 3 )) ” 
  &&  “ ((cursor_pre + 3 ) < capacity_pre) ” 
  &&  “ (b3 = (tower_encode_byte (word_value_pre) (3))) ” 
  &&  “ (0 <= (tower_encode_byte (word_value_pre) (3))) ” 
  &&  “ ((tower_encode_byte (word_value_pre) (3)) < 256) ” 
  &&  “ (b3 < 256) ” 
  &&  “ (0 <= b3) ” 
  &&  “ (b0 = (tower_encode_byte (word_value_pre) (0))) ” 
  &&  “ (b1 = (tower_encode_byte (word_value_pre) (1))) ” 
  &&  “ (b2 = (tower_encode_byte (word_value_pre) (2))) ” 
  &&  “ (b3 = (tower_encode_byte (word_value_pre) (3))) ” 
  &&  “ (b4 = (tower_encode_byte (word_value_pre) (4))) ” 
  &&  “ (b5 = (tower_encode_byte (word_value_pre) (5))) ” 
  &&  “ (b6 = (tower_encode_byte (word_value_pre) (6))) ” 
  &&  “ (b7 = (tower_encode_byte (word_value_pre) (7))) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ ((cursor_pre + 8 ) <= capacity_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ”
  &&  (UCharArray.seg data_pre 0 (cursor_pre + 3 ) (app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 3 ) capacity_pre )
.

Definition cmc_write_word_partial_solve_wit_4 := cmc_write_word_partial_solve_wit_4_pure -> cmc_write_word_partial_solve_wit_4_aux.

Definition cmc_write_word_partial_solve_wit_5_pure := 
(
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 4 ) (app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 4 ) capacity_pre )
|--
  “ (0 <= (cursor_pre + 4 )) ” 
  &&  “ ((cursor_pre + 4 ) < capacity_pre) ” 
  &&  “ (b4 = (tower_encode_byte (word_value_pre) (4))) ” 
  &&  “ (0 <= (tower_encode_byte (word_value_pre) (4))) ” 
  &&  “ ((tower_encode_byte (word_value_pre) (4)) < 256) ” 
  &&  “ (b4 < 256) ” 
  &&  “ (0 <= b4) ”
) \/
(
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (bits_value <= UINT64_MAX)) (PreH2 : (bits_value >= 0)) (PreH3 : (word_value_pre <= INT64_MAX)) (PreH4 : (word_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH10 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH11 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH12 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH13 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH14 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH15 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH16 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH17 : (0 <= cursor_pre)) (PreH18 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH19 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 4 ) (app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 4 ) capacity_pre )
|--
  “ (0 <= b4) ” 
  &&  “ (b4 < 256) ” 
  &&  “ (b4 < 256) ” 
  &&  “ (0 <= b4) ”
).

Definition cmc_write_word_partial_solve_wit_5_pure_split_goal_1 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (bits_value <= UINT64_MAX)) (PreH2 : (bits_value >= 0)) (PreH3 : (word_value_pre <= INT64_MAX)) (PreH4 : (word_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH10 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH11 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH12 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH13 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH14 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH15 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH16 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH17 : (0 <= cursor_pre)) (PreH18 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH19 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 4 ) (app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 4 ) capacity_pre )
|--
  “ (0 <= b4) ”
.

Definition cmc_write_word_partial_solve_wit_5_pure_split_goal_2 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (bits_value <= UINT64_MAX)) (PreH2 : (bits_value >= 0)) (PreH3 : (word_value_pre <= INT64_MAX)) (PreH4 : (word_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH10 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH11 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH12 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH13 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH14 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH15 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH16 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH17 : (0 <= cursor_pre)) (PreH18 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH19 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 4 ) (app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 4 ) capacity_pre )
|--
  “ (b4 < 256) ”
.

Definition cmc_write_word_partial_solve_wit_5_pure_split_goal_3 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (bits_value <= UINT64_MAX)) (PreH2 : (bits_value >= 0)) (PreH3 : (word_value_pre <= INT64_MAX)) (PreH4 : (word_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH10 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH11 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH12 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH13 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH14 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH15 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH16 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH17 : (0 <= cursor_pre)) (PreH18 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH19 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 4 ) (app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 4 ) capacity_pre )
|--
  “ (b4 < 256) ”
.

Definition cmc_write_word_partial_solve_wit_5_pure_split_goal_4 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (bits_value <= UINT64_MAX)) (PreH2 : (bits_value >= 0)) (PreH3 : (word_value_pre <= INT64_MAX)) (PreH4 : (word_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH10 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH11 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH12 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH13 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH14 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH15 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH16 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH17 : (0 <= cursor_pre)) (PreH18 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH19 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 4 ) (app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 4 ) capacity_pre )
|--
  “ (0 <= b4) ”
.

Definition cmc_write_word_partial_solve_wit_5_aux := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 (cursor_pre + 4 ) (app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 4 ) capacity_pre )
|--
  “ (0 <= (cursor_pre + 4 )) ” 
  &&  “ ((cursor_pre + 4 ) < capacity_pre) ” 
  &&  “ (b4 = (tower_encode_byte (word_value_pre) (4))) ” 
  &&  “ (0 <= (tower_encode_byte (word_value_pre) (4))) ” 
  &&  “ ((tower_encode_byte (word_value_pre) (4)) < 256) ” 
  &&  “ (b4 < 256) ” 
  &&  “ (0 <= b4) ” 
  &&  “ (b0 = (tower_encode_byte (word_value_pre) (0))) ” 
  &&  “ (b1 = (tower_encode_byte (word_value_pre) (1))) ” 
  &&  “ (b2 = (tower_encode_byte (word_value_pre) (2))) ” 
  &&  “ (b3 = (tower_encode_byte (word_value_pre) (3))) ” 
  &&  “ (b4 = (tower_encode_byte (word_value_pre) (4))) ” 
  &&  “ (b5 = (tower_encode_byte (word_value_pre) (5))) ” 
  &&  “ (b6 = (tower_encode_byte (word_value_pre) (6))) ” 
  &&  “ (b7 = (tower_encode_byte (word_value_pre) (7))) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ ((cursor_pre + 8 ) <= capacity_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ”
  &&  (UCharArray.seg data_pre 0 (cursor_pre + 4 ) (app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 4 ) capacity_pre )
.

Definition cmc_write_word_partial_solve_wit_5 := cmc_write_word_partial_solve_wit_5_pure -> cmc_write_word_partial_solve_wit_5_aux.

Definition cmc_write_word_partial_solve_wit_6_pure := 
(
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 5 ) (app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 5 ) capacity_pre )
|--
  “ (0 <= (cursor_pre + 5 )) ” 
  &&  “ ((cursor_pre + 5 ) < capacity_pre) ” 
  &&  “ (b5 = (tower_encode_byte (word_value_pre) (5))) ” 
  &&  “ (0 <= (tower_encode_byte (word_value_pre) (5))) ” 
  &&  “ ((tower_encode_byte (word_value_pre) (5)) < 256) ” 
  &&  “ (b5 < 256) ” 
  &&  “ (0 <= b5) ”
) \/
(
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (bits_value <= UINT64_MAX)) (PreH2 : (bits_value >= 0)) (PreH3 : (word_value_pre <= INT64_MAX)) (PreH4 : (word_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH10 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH11 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH12 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH13 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH14 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH15 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH16 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH17 : (0 <= cursor_pre)) (PreH18 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH19 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 5 ) (app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 5 ) capacity_pre )
|--
  “ (0 <= b5) ” 
  &&  “ (b5 < 256) ” 
  &&  “ (b5 < 256) ” 
  &&  “ (0 <= b5) ”
).

Definition cmc_write_word_partial_solve_wit_6_pure_split_goal_1 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (bits_value <= UINT64_MAX)) (PreH2 : (bits_value >= 0)) (PreH3 : (word_value_pre <= INT64_MAX)) (PreH4 : (word_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH10 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH11 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH12 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH13 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH14 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH15 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH16 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH17 : (0 <= cursor_pre)) (PreH18 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH19 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 5 ) (app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 5 ) capacity_pre )
|--
  “ (0 <= b5) ”
.

Definition cmc_write_word_partial_solve_wit_6_pure_split_goal_2 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (bits_value <= UINT64_MAX)) (PreH2 : (bits_value >= 0)) (PreH3 : (word_value_pre <= INT64_MAX)) (PreH4 : (word_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH10 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH11 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH12 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH13 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH14 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH15 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH16 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH17 : (0 <= cursor_pre)) (PreH18 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH19 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 5 ) (app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 5 ) capacity_pre )
|--
  “ (b5 < 256) ”
.

Definition cmc_write_word_partial_solve_wit_6_pure_split_goal_3 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (bits_value <= UINT64_MAX)) (PreH2 : (bits_value >= 0)) (PreH3 : (word_value_pre <= INT64_MAX)) (PreH4 : (word_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH10 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH11 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH12 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH13 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH14 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH15 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH16 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH17 : (0 <= cursor_pre)) (PreH18 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH19 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 5 ) (app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 5 ) capacity_pre )
|--
  “ (b5 < 256) ”
.

Definition cmc_write_word_partial_solve_wit_6_pure_split_goal_4 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (bits_value <= UINT64_MAX)) (PreH2 : (bits_value >= 0)) (PreH3 : (word_value_pre <= INT64_MAX)) (PreH4 : (word_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH10 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH11 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH12 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH13 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH14 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH15 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH16 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH17 : (0 <= cursor_pre)) (PreH18 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH19 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 5 ) (app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 5 ) capacity_pre )
|--
  “ (0 <= b5) ”
.

Definition cmc_write_word_partial_solve_wit_6_aux := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 (cursor_pre + 5 ) (app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 5 ) capacity_pre )
|--
  “ (0 <= (cursor_pre + 5 )) ” 
  &&  “ ((cursor_pre + 5 ) < capacity_pre) ” 
  &&  “ (b5 = (tower_encode_byte (word_value_pre) (5))) ” 
  &&  “ (0 <= (tower_encode_byte (word_value_pre) (5))) ” 
  &&  “ ((tower_encode_byte (word_value_pre) (5)) < 256) ” 
  &&  “ (b5 < 256) ” 
  &&  “ (0 <= b5) ” 
  &&  “ (b0 = (tower_encode_byte (word_value_pre) (0))) ” 
  &&  “ (b1 = (tower_encode_byte (word_value_pre) (1))) ” 
  &&  “ (b2 = (tower_encode_byte (word_value_pre) (2))) ” 
  &&  “ (b3 = (tower_encode_byte (word_value_pre) (3))) ” 
  &&  “ (b4 = (tower_encode_byte (word_value_pre) (4))) ” 
  &&  “ (b5 = (tower_encode_byte (word_value_pre) (5))) ” 
  &&  “ (b6 = (tower_encode_byte (word_value_pre) (6))) ” 
  &&  “ (b7 = (tower_encode_byte (word_value_pre) (7))) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ ((cursor_pre + 8 ) <= capacity_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ”
  &&  (UCharArray.seg data_pre 0 (cursor_pre + 5 ) (app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 5 ) capacity_pre )
.

Definition cmc_write_word_partial_solve_wit_6 := cmc_write_word_partial_solve_wit_6_pure -> cmc_write_word_partial_solve_wit_6_aux.

Definition cmc_write_word_partial_solve_wit_7_pure := 
(
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 6 ) (app ((app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (5))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 6 ) capacity_pre )
|--
  “ (0 <= (cursor_pre + 6 )) ” 
  &&  “ ((cursor_pre + 6 ) < capacity_pre) ” 
  &&  “ (b6 = (tower_encode_byte (word_value_pre) (6))) ” 
  &&  “ (0 <= (tower_encode_byte (word_value_pre) (6))) ” 
  &&  “ ((tower_encode_byte (word_value_pre) (6)) < 256) ” 
  &&  “ (b6 < 256) ” 
  &&  “ (0 <= b6) ”
) \/
(
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (bits_value <= UINT64_MAX)) (PreH2 : (bits_value >= 0)) (PreH3 : (word_value_pre <= INT64_MAX)) (PreH4 : (word_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH10 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH11 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH12 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH13 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH14 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH15 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH16 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH17 : (0 <= cursor_pre)) (PreH18 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH19 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 6 ) (app ((app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (5))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 6 ) capacity_pre )
|--
  “ (0 <= b6) ” 
  &&  “ (b6 < 256) ” 
  &&  “ (b6 < 256) ” 
  &&  “ (0 <= b6) ”
).

Definition cmc_write_word_partial_solve_wit_7_pure_split_goal_1 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (bits_value <= UINT64_MAX)) (PreH2 : (bits_value >= 0)) (PreH3 : (word_value_pre <= INT64_MAX)) (PreH4 : (word_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH10 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH11 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH12 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH13 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH14 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH15 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH16 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH17 : (0 <= cursor_pre)) (PreH18 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH19 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 6 ) (app ((app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (5))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 6 ) capacity_pre )
|--
  “ (0 <= b6) ”
.

Definition cmc_write_word_partial_solve_wit_7_pure_split_goal_2 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (bits_value <= UINT64_MAX)) (PreH2 : (bits_value >= 0)) (PreH3 : (word_value_pre <= INT64_MAX)) (PreH4 : (word_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH10 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH11 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH12 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH13 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH14 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH15 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH16 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH17 : (0 <= cursor_pre)) (PreH18 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH19 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 6 ) (app ((app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (5))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 6 ) capacity_pre )
|--
  “ (b6 < 256) ”
.

Definition cmc_write_word_partial_solve_wit_7_pure_split_goal_3 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (bits_value <= UINT64_MAX)) (PreH2 : (bits_value >= 0)) (PreH3 : (word_value_pre <= INT64_MAX)) (PreH4 : (word_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH10 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH11 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH12 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH13 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH14 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH15 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH16 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH17 : (0 <= cursor_pre)) (PreH18 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH19 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 6 ) (app ((app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (5))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 6 ) capacity_pre )
|--
  “ (b6 < 256) ”
.

Definition cmc_write_word_partial_solve_wit_7_pure_split_goal_4 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (bits_value <= UINT64_MAX)) (PreH2 : (bits_value >= 0)) (PreH3 : (word_value_pre <= INT64_MAX)) (PreH4 : (word_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH10 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH11 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH12 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH13 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH14 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH15 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH16 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH17 : (0 <= cursor_pre)) (PreH18 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH19 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 6 ) (app ((app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (5))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 6 ) capacity_pre )
|--
  “ (0 <= b6) ”
.

Definition cmc_write_word_partial_solve_wit_7_aux := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 (cursor_pre + 6 ) (app ((app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (5))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 6 ) capacity_pre )
|--
  “ (0 <= (cursor_pre + 6 )) ” 
  &&  “ ((cursor_pre + 6 ) < capacity_pre) ” 
  &&  “ (b6 = (tower_encode_byte (word_value_pre) (6))) ” 
  &&  “ (0 <= (tower_encode_byte (word_value_pre) (6))) ” 
  &&  “ ((tower_encode_byte (word_value_pre) (6)) < 256) ” 
  &&  “ (b6 < 256) ” 
  &&  “ (0 <= b6) ” 
  &&  “ (b0 = (tower_encode_byte (word_value_pre) (0))) ” 
  &&  “ (b1 = (tower_encode_byte (word_value_pre) (1))) ” 
  &&  “ (b2 = (tower_encode_byte (word_value_pre) (2))) ” 
  &&  “ (b3 = (tower_encode_byte (word_value_pre) (3))) ” 
  &&  “ (b4 = (tower_encode_byte (word_value_pre) (4))) ” 
  &&  “ (b5 = (tower_encode_byte (word_value_pre) (5))) ” 
  &&  “ (b6 = (tower_encode_byte (word_value_pre) (6))) ” 
  &&  “ (b7 = (tower_encode_byte (word_value_pre) (7))) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ ((cursor_pre + 8 ) <= capacity_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ”
  &&  (UCharArray.seg data_pre 0 (cursor_pre + 6 ) (app ((app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (5))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 6 ) capacity_pre )
.

Definition cmc_write_word_partial_solve_wit_7 := cmc_write_word_partial_solve_wit_7_pure -> cmc_write_word_partial_solve_wit_7_aux.

Definition cmc_write_word_partial_solve_wit_8_pure := 
(
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 7 ) (app ((app ((app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (5))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (6))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 7 ) capacity_pre )
|--
  “ (0 <= (cursor_pre + 7 )) ” 
  &&  “ ((cursor_pre + 7 ) < capacity_pre) ” 
  &&  “ (b7 = (tower_encode_byte (word_value_pre) (7))) ” 
  &&  “ (0 <= (tower_encode_byte (word_value_pre) (7))) ” 
  &&  “ ((tower_encode_byte (word_value_pre) (7)) < 256) ” 
  &&  “ (b7 < 256) ” 
  &&  “ (0 <= b7) ”
) \/
(
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (bits_value <= UINT64_MAX)) (PreH2 : (bits_value >= 0)) (PreH3 : (word_value_pre <= INT64_MAX)) (PreH4 : (word_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH10 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH11 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH12 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH13 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH14 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH15 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH16 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH17 : (0 <= cursor_pre)) (PreH18 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH19 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 7 ) (app ((app ((app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (5))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (6))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 7 ) capacity_pre )
|--
  “ (0 <= b7) ” 
  &&  “ (b7 < 256) ” 
  &&  “ (b7 < 256) ” 
  &&  “ (0 <= b7) ”
).

Definition cmc_write_word_partial_solve_wit_8_pure_split_goal_1 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (bits_value <= UINT64_MAX)) (PreH2 : (bits_value >= 0)) (PreH3 : (word_value_pre <= INT64_MAX)) (PreH4 : (word_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH10 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH11 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH12 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH13 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH14 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH15 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH16 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH17 : (0 <= cursor_pre)) (PreH18 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH19 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 7 ) (app ((app ((app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (5))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (6))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 7 ) capacity_pre )
|--
  “ (0 <= b7) ”
.

Definition cmc_write_word_partial_solve_wit_8_pure_split_goal_2 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (bits_value <= UINT64_MAX)) (PreH2 : (bits_value >= 0)) (PreH3 : (word_value_pre <= INT64_MAX)) (PreH4 : (word_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH10 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH11 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH12 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH13 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH14 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH15 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH16 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH17 : (0 <= cursor_pre)) (PreH18 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH19 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 7 ) (app ((app ((app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (5))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (6))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 7 ) capacity_pre )
|--
  “ (b7 < 256) ”
.

Definition cmc_write_word_partial_solve_wit_8_pure_split_goal_3 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (bits_value <= UINT64_MAX)) (PreH2 : (bits_value >= 0)) (PreH3 : (word_value_pre <= INT64_MAX)) (PreH4 : (word_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH10 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH11 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH12 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH13 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH14 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH15 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH16 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH17 : (0 <= cursor_pre)) (PreH18 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH19 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 7 ) (app ((app ((app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (5))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (6))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 7 ) capacity_pre )
|--
  “ (b7 < 256) ”
.

Definition cmc_write_word_partial_solve_wit_8_pure_split_goal_4 := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (bits_value: Z) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (bits_value <= UINT64_MAX)) (PreH2 : (bits_value >= 0)) (PreH3 : (word_value_pre <= INT64_MAX)) (PreH4 : (word_value_pre >= INT64_MIN)) (PreH5 : (cursor_pre <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (cursor_pre >= INT_MIN)) (PreH8 : (capacity_pre >= INT_MIN)) (PreH9 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH10 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH11 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH12 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH13 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH14 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH15 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH16 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH17 : (0 <= cursor_pre)) (PreH18 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH19 : (capacity_pre <= INT_MAX)) ,
  ((( &( "bits" ) )) # UInt64  |-> bits_value)
  **  ((( &( "b0" ) )) # UChar  |-> b0)
  **  ((( &( "word_value" ) )) # Int64  |-> word_value_pre)
  **  ((( &( "b1" ) )) # UChar  |-> b1)
  **  ((( &( "b2" ) )) # UChar  |-> b2)
  **  ((( &( "b3" ) )) # UChar  |-> b3)
  **  ((( &( "b4" ) )) # UChar  |-> b4)
  **  ((( &( "b5" ) )) # UChar  |-> b5)
  **  ((( &( "b6" ) )) # UChar  |-> b6)
  **  ((( &( "b7" ) )) # UChar  |-> b7)
  **  ((( &( "data" ) )) # Ptr  |-> data_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "cursor" ) )) # Int  |-> cursor_pre)
  **  (UCharArray.seg data_pre 0 (cursor_pre + 7 ) (app ((app ((app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (5))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (6))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 7 ) capacity_pre )
|--
  “ (0 <= b7) ”
.

Definition cmc_write_word_partial_solve_wit_8_aux := 
forall (word_value_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (prefix: (@list Z)) (b0: Z) (b1: Z) (b2: Z) (b3: Z) (b4: Z) (b5: Z) (b6: Z) (b7: Z) (PreH1 : (b0 = (tower_encode_byte (word_value_pre) (0)))) (PreH2 : (b1 = (tower_encode_byte (word_value_pre) (1)))) (PreH3 : (b2 = (tower_encode_byte (word_value_pre) (2)))) (PreH4 : (b3 = (tower_encode_byte (word_value_pre) (3)))) (PreH5 : (b4 = (tower_encode_byte (word_value_pre) (4)))) (PreH6 : (b5 = (tower_encode_byte (word_value_pre) (5)))) (PreH7 : (b6 = (tower_encode_byte (word_value_pre) (6)))) (PreH8 : (b7 = (tower_encode_byte (word_value_pre) (7)))) (PreH9 : (0 <= cursor_pre)) (PreH10 : ((cursor_pre + 8 ) <= capacity_pre)) (PreH11 : (capacity_pre <= INT_MAX)) ,
  (UCharArray.seg data_pre 0 (cursor_pre + 7 ) (app ((app ((app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (5))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (6))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 7 ) capacity_pre )
|--
  “ (0 <= (cursor_pre + 7 )) ” 
  &&  “ ((cursor_pre + 7 ) < capacity_pre) ” 
  &&  “ (b7 = (tower_encode_byte (word_value_pre) (7))) ” 
  &&  “ (0 <= (tower_encode_byte (word_value_pre) (7))) ” 
  &&  “ ((tower_encode_byte (word_value_pre) (7)) < 256) ” 
  &&  “ (b7 < 256) ” 
  &&  “ (0 <= b7) ” 
  &&  “ (b0 = (tower_encode_byte (word_value_pre) (0))) ” 
  &&  “ (b1 = (tower_encode_byte (word_value_pre) (1))) ” 
  &&  “ (b2 = (tower_encode_byte (word_value_pre) (2))) ” 
  &&  “ (b3 = (tower_encode_byte (word_value_pre) (3))) ” 
  &&  “ (b4 = (tower_encode_byte (word_value_pre) (4))) ” 
  &&  “ (b5 = (tower_encode_byte (word_value_pre) (5))) ” 
  &&  “ (b6 = (tower_encode_byte (word_value_pre) (6))) ” 
  &&  “ (b7 = (tower_encode_byte (word_value_pre) (7))) ” 
  &&  “ (0 <= cursor_pre) ” 
  &&  “ ((cursor_pre + 8 ) <= capacity_pre) ” 
  &&  “ (capacity_pre <= INT_MAX) ”
  &&  (UCharArray.seg data_pre 0 (cursor_pre + 7 ) (app ((app ((app ((app ((app ((app ((app (prefix) ((cons ((tower_encode_byte (word_value_pre) (0))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (1))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (2))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (3))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (4))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (5))) ((@nil Z)))))) ((cons ((tower_encode_byte (word_value_pre) (6))) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 7 ) capacity_pre )
.

Definition cmc_write_word_partial_solve_wit_8 := cmc_write_word_partial_solve_wit_8_pure -> cmc_write_word_partial_solve_wit_8_aux.

Module Type VC_Correct.


Axiom proof_of_cmc_write_word_safety_wit_1 : cmc_write_word_safety_wit_1.
Axiom proof_of_cmc_write_word_safety_wit_2 : cmc_write_word_safety_wit_2.
Axiom proof_of_cmc_write_word_safety_wit_3 : cmc_write_word_safety_wit_3.
Axiom proof_of_cmc_write_word_safety_wit_4 : cmc_write_word_safety_wit_4.
Axiom proof_of_cmc_write_word_safety_wit_5 : cmc_write_word_safety_wit_5.
Axiom proof_of_cmc_write_word_safety_wit_6 : cmc_write_word_safety_wit_6.
Axiom proof_of_cmc_write_word_safety_wit_7 : cmc_write_word_safety_wit_7.
Axiom proof_of_cmc_write_word_safety_wit_8 : cmc_write_word_safety_wit_8.
Axiom proof_of_cmc_write_word_safety_wit_9 : cmc_write_word_safety_wit_9.
Axiom proof_of_cmc_write_word_safety_wit_10 : cmc_write_word_safety_wit_10.
Axiom proof_of_cmc_write_word_safety_wit_11 : cmc_write_word_safety_wit_11.
Axiom proof_of_cmc_write_word_safety_wit_12 : cmc_write_word_safety_wit_12.
Axiom proof_of_cmc_write_word_safety_wit_13 : cmc_write_word_safety_wit_13.
Axiom proof_of_cmc_write_word_safety_wit_14 : cmc_write_word_safety_wit_14.
Axiom proof_of_cmc_write_word_safety_wit_15 : cmc_write_word_safety_wit_15.
Axiom proof_of_cmc_write_word_safety_wit_16 : cmc_write_word_safety_wit_16.
Axiom proof_of_cmc_write_word_safety_wit_17 : cmc_write_word_safety_wit_17.
Axiom proof_of_cmc_write_word_safety_wit_18 : cmc_write_word_safety_wit_18.
Axiom proof_of_cmc_write_word_safety_wit_19 : cmc_write_word_safety_wit_19.
Axiom proof_of_cmc_write_word_safety_wit_20 : cmc_write_word_safety_wit_20.
Axiom proof_of_cmc_write_word_safety_wit_21 : cmc_write_word_safety_wit_21.
Axiom proof_of_cmc_write_word_safety_wit_22 : cmc_write_word_safety_wit_22.
Axiom proof_of_cmc_write_word_safety_wit_23 : cmc_write_word_safety_wit_23.
Axiom proof_of_cmc_write_word_safety_wit_24 : cmc_write_word_safety_wit_24.
Axiom proof_of_cmc_write_word_safety_wit_25 : cmc_write_word_safety_wit_25.
Axiom proof_of_cmc_write_word_safety_wit_26 : cmc_write_word_safety_wit_26.
Axiom proof_of_cmc_write_word_safety_wit_27 : cmc_write_word_safety_wit_27.
Axiom proof_of_cmc_write_word_safety_wit_28 : cmc_write_word_safety_wit_28.
Axiom proof_of_cmc_write_word_safety_wit_29 : cmc_write_word_safety_wit_29.
Axiom proof_of_cmc_write_word_entail_wit_1 : cmc_write_word_entail_wit_1.
Axiom proof_of_cmc_write_word_entail_wit_2 : cmc_write_word_entail_wit_2.
Axiom proof_of_cmc_write_word_entail_wit_3 : cmc_write_word_entail_wit_3.
Axiom proof_of_cmc_write_word_entail_wit_4 : cmc_write_word_entail_wit_4.
Axiom proof_of_cmc_write_word_entail_wit_5 : cmc_write_word_entail_wit_5.
Axiom proof_of_cmc_write_word_entail_wit_6 : cmc_write_word_entail_wit_6.
Axiom proof_of_cmc_write_word_return_wit_1 : cmc_write_word_return_wit_1.
Axiom proof_of_cmc_write_word_partial_solve_wit_1_pure : cmc_write_word_partial_solve_wit_1_pure.
Axiom proof_of_cmc_write_word_partial_solve_wit_1 : cmc_write_word_partial_solve_wit_1.
Axiom proof_of_cmc_write_word_partial_solve_wit_2_pure : cmc_write_word_partial_solve_wit_2_pure.
Axiom proof_of_cmc_write_word_partial_solve_wit_2 : cmc_write_word_partial_solve_wit_2.
Axiom proof_of_cmc_write_word_partial_solve_wit_3_pure : cmc_write_word_partial_solve_wit_3_pure.
Axiom proof_of_cmc_write_word_partial_solve_wit_3 : cmc_write_word_partial_solve_wit_3.
Axiom proof_of_cmc_write_word_partial_solve_wit_4_pure : cmc_write_word_partial_solve_wit_4_pure.
Axiom proof_of_cmc_write_word_partial_solve_wit_4 : cmc_write_word_partial_solve_wit_4.
Axiom proof_of_cmc_write_word_partial_solve_wit_5_pure : cmc_write_word_partial_solve_wit_5_pure.
Axiom proof_of_cmc_write_word_partial_solve_wit_5 : cmc_write_word_partial_solve_wit_5.
Axiom proof_of_cmc_write_word_partial_solve_wit_6_pure : cmc_write_word_partial_solve_wit_6_pure.
Axiom proof_of_cmc_write_word_partial_solve_wit_6 : cmc_write_word_partial_solve_wit_6.
Axiom proof_of_cmc_write_word_partial_solve_wit_7_pure : cmc_write_word_partial_solve_wit_7_pure.
Axiom proof_of_cmc_write_word_partial_solve_wit_7 : cmc_write_word_partial_solve_wit_7.
Axiom proof_of_cmc_write_word_partial_solve_wit_8_pure : cmc_write_word_partial_solve_wit_8_pure.
Axiom proof_of_cmc_write_word_partial_solve_wit_8 : cmc_write_word_partial_solve_wit_8.

End VC_Correct.
