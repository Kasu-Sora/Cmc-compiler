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
From SimpleC.EE.QCP_demos_human Require Import cmc_emit_expr_leaf_migration_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.cmc_emit_expr_leaf_migration_lib.
Local Open Scope sac.

Lemma proof_of_cmc_const_immediate_safety_wit_1 : cmc_const_immediate_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_const_immediate_safety_wit_2 : cmc_const_immediate_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cm_emit_const_expr_safety_wit_1 : cm_emit_const_expr_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cm_emit_const_expr_partial_solve_wit_1_pure : cm_emit_const_expr_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_cm_emit_const_expr_partial_solve_wit_1 : cm_emit_const_expr_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cm_emit_const_expr_partial_solve_wit_2_pure : cm_emit_const_expr_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_cm_emit_const_expr_partial_solve_wit_2 : cm_emit_const_expr_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_cm_emit_const_expr_partial_solve_wit_3_pure : cm_emit_const_expr_partial_solve_wit_3_pure.
Proof. Admitted. 

Lemma proof_of_cm_emit_const_expr_partial_solve_wit_3 : cm_emit_const_expr_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_cm_emit_string_expr_safety_wit_1 : cm_emit_string_expr_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cm_emit_string_expr_partial_solve_wit_1 : cm_emit_string_expr_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cm_emit_string_expr_partial_solve_wit_2_pure : cm_emit_string_expr_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_cm_emit_string_expr_partial_solve_wit_2 : cm_emit_string_expr_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_cm_emit_string_expr_partial_solve_wit_3_pure : cm_emit_string_expr_partial_solve_wit_3_pure.
Proof. Admitted. 

Lemma proof_of_cm_emit_string_expr_partial_solve_wit_3 : cm_emit_string_expr_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_cm_emit_string_expr_partial_solve_wit_4_pure : cm_emit_string_expr_partial_solve_wit_4_pure.
Proof. Admitted. 

Lemma proof_of_cm_emit_string_expr_partial_solve_wit_4 : cm_emit_string_expr_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_cm_emit_getc_expr_safety_wit_1 : cm_emit_getc_expr_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cm_emit_getc_expr_safety_wit_2 : cm_emit_getc_expr_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cm_emit_getc_expr_partial_solve_wit_1_pure : cm_emit_getc_expr_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_cm_emit_getc_expr_partial_solve_wit_1 : cm_emit_getc_expr_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cm_emit_getc_expr_partial_solve_wit_2_pure : cm_emit_getc_expr_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_cm_emit_getc_expr_partial_solve_wit_2 : cm_emit_getc_expr_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_cm_sizeof_value_safety_wit_1 : cm_sizeof_value_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cm_sizeof_value_safety_wit_2 : cm_sizeof_value_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cm_sizeof_value_partial_solve_wit_1_pure : cm_sizeof_value_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_cm_sizeof_value_partial_solve_wit_1 : cm_sizeof_value_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cm_sizeof_value_partial_solve_wit_2 : cm_sizeof_value_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_cm_sizeof_value_partial_solve_wit_3_pure : cm_sizeof_value_partial_solve_wit_3_pure.
Proof. Admitted. 

Lemma proof_of_cm_sizeof_value_partial_solve_wit_3 : cm_sizeof_value_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_cm_type_size_value_return_wit_1 : cm_type_size_value_return_wit_1.
Proof. Admitted. 

Lemma proof_of_cm_type_size_value_partial_solve_wit_1_pure : cm_type_size_value_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_cm_type_size_value_partial_solve_wit_1 : cm_type_size_value_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cm_emit_sizeof_expr_safety_wit_1 : cm_emit_sizeof_expr_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cm_emit_sizeof_expr_partial_solve_wit_1_pure : cm_emit_sizeof_expr_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_cm_emit_sizeof_expr_partial_solve_wit_1 : cm_emit_sizeof_expr_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cm_emit_sizeof_expr_partial_solve_wit_2_pure : cm_emit_sizeof_expr_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_cm_emit_sizeof_expr_partial_solve_wit_2 : cm_emit_sizeof_expr_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_cm_emit_sizeof_expr_partial_solve_wit_3_pure : cm_emit_sizeof_expr_partial_solve_wit_3_pure.
Proof. Admitted. 

Lemma proof_of_cm_emit_sizeof_expr_partial_solve_wit_3 : cm_emit_sizeof_expr_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_cm_member_array_value_context_partial_solve_wit_1_pure : cm_member_array_value_context_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_cm_member_array_value_context_partial_solve_wit_1 : cm_member_array_value_context_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cm_member_offset_value_context_safety_wit_2 : cm_member_offset_value_context_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cm_member_offset_value_context_safety_wit_3 : cm_member_offset_value_context_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_cm_member_offset_value_context_safety_wit_4 : cm_member_offset_value_context_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_cm_member_offset_value_context_partial_solve_wit_1_pure : cm_member_offset_value_context_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_cm_member_offset_value_context_partial_solve_wit_1 : cm_member_offset_value_context_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cm_member_offset_value_context_partial_solve_wit_2_pure : cm_member_offset_value_context_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_cm_member_offset_value_context_partial_solve_wit_2 : cm_member_offset_value_context_partial_solve_wit_2.
Proof. Admitted. 

