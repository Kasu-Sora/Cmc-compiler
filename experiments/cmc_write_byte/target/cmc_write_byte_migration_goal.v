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

(*----- Function cmc_write_byte -----*)

Definition cmc_write_byte_return_wit_1 := 
forall (byte_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (model_byte: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : (cursor_pre < capacity_pre)) (PreH3 : (byte_pre = model_byte)) (PreH4 : (0 <= model_byte)) (PreH5 : (model_byte < 256)) ,
  (UCharArray.seg data_pre 0 (cursor_pre + 1 ) (app (prefix) ((cons (byte_pre) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 1 ) capacity_pre )
|--
  (UCharArray.seg data_pre 0 (cursor_pre + 1 ) (app (prefix) ((cons (model_byte) ((@nil Z))))) )
  **  (UCharArray.undef_seg data_pre (cursor_pre + 1 ) capacity_pre )
.

Definition cmc_write_byte_partial_solve_wit_1 := 
forall (byte_pre: Z) (cursor_pre: Z) (capacity_pre: Z) (data_pre: Z) (model_byte: Z) (prefix: (@list Z)) (PreH1 : (0 <= cursor_pre)) (PreH2 : (cursor_pre < capacity_pre)) (PreH3 : (byte_pre = model_byte)) (PreH4 : (0 <= model_byte)) (PreH5 : (model_byte < 256)) ,
  (UCharArray.seg data_pre 0 cursor_pre prefix )
  **  (UCharArray.undef_seg data_pre cursor_pre capacity_pre )
|--
  “ (0 <= cursor_pre) ” 
  &&  “ (cursor_pre < capacity_pre) ” 
  &&  “ (byte_pre = model_byte) ” 
  &&  “ (0 <= model_byte) ” 
  &&  “ (model_byte < 256) ”
  &&  (((data_pre + (cursor_pre * sizeof(UCHAR)))) # UChar  |->_)
  **  (UCharArray.undef_seg data_pre (cursor_pre + 1 ) capacity_pre )
  **  (UCharArray.seg data_pre 0 cursor_pre prefix )
.

Module Type VC_Correct.


Axiom proof_of_cmc_write_byte_return_wit_1 : cmc_write_byte_return_wit_1.
Axiom proof_of_cmc_write_byte_partial_solve_wit_1 : cmc_write_byte_partial_solve_wit_1.

End VC_Correct.
