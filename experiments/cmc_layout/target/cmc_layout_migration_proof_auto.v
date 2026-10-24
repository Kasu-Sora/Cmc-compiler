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
From SimpleC.EE.QCP_demos_human Require Import cmc_layout_migration_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.cmc_layout_migration_lib.
Local Open Scope sac.

Lemma proof_of_cmc_is_pointer_safety_wit_1 : cmc_is_pointer_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_is_pointer_safety_wit_2 : cmc_is_pointer_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_is_pointer_safety_wit_3 : cmc_is_pointer_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_cmc_is_pointer_value_return_wit_1 : cmc_is_pointer_value_return_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_is_pointer_value_partial_solve_wit_1 : cmc_is_pointer_value_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_pointee_safety_wit_1 : cmc_pointee_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_pointee_safety_wit_2 : cmc_pointee_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_pointee_return_wit_1 : cmc_pointee_return_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_leaf_size_safety_wit_1 : cmc_leaf_size_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_leaf_size_safety_wit_2 : cmc_leaf_size_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_leaf_size_safety_wit_3 : cmc_leaf_size_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_cmc_leaf_size_safety_wit_4 : cmc_leaf_size_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_cmc_leaf_size_safety_wit_5 : cmc_leaf_size_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_cmc_leaf_size_safety_wit_6 : cmc_leaf_size_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_cmc_leaf_size_safety_wit_7 : cmc_leaf_size_safety_wit_7.
Proof. Admitted. 

Lemma proof_of_cmc_code_slot_size_safety_wit_1 : cmc_code_slot_size_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_code_slot_size_safety_wit_2 : cmc_code_slot_size_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_code_slot_size_partial_solve_wit_1 : cmc_code_slot_size_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_members_size_safety_wit_1 : cmc_members_size_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_members_size_safety_wit_2 : cmc_members_size_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_members_size_partial_solve_wit_1 : cmc_members_size_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_members_size_partial_solve_wit_2_pure : cmc_members_size_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_cmc_members_size_partial_solve_wit_2 : cmc_members_size_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_struct_size_at_safety_wit_1 : cmc_struct_size_at_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_struct_size_at_safety_wit_2 : cmc_struct_size_at_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_struct_size_at_safety_wit_3 : cmc_struct_size_at_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_cmc_struct_size_at_safety_wit_4 : cmc_struct_size_at_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_cmc_struct_size_at_safety_wit_5 : cmc_struct_size_at_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_cmc_struct_size_at_partial_solve_wit_1_pure : cmc_struct_size_at_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_cmc_struct_size_at_partial_solve_wit_1 : cmc_struct_size_at_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_struct_size_at_partial_solve_wit_2_pure : cmc_struct_size_at_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_cmc_struct_size_at_partial_solve_wit_2 : cmc_struct_size_at_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_nonzero_safety_wit_1 : cmc_nonzero_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_nonzero_safety_wit_2 : cmc_nonzero_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_nonzero_safety_wit_3 : cmc_nonzero_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_cmc_global_array_at_safety_wit_1 : cmc_global_array_at_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_global_array_at_safety_wit_2 : cmc_global_array_at_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_global_array_at_safety_wit_3 : cmc_global_array_at_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_cmc_global_array_at_safety_wit_4 : cmc_global_array_at_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_cmc_global_array_at_safety_wit_5 : cmc_global_array_at_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_cmc_global_array_at_partial_solve_wit_1 : cmc_global_array_at_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_global_array_at_partial_solve_wit_2_pure : cmc_global_array_at_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_cmc_global_array_at_partial_solve_wit_2 : cmc_global_array_at_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_slot_array_at_safety_wit_1 : cmc_slot_array_at_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_slot_array_at_safety_wit_2 : cmc_slot_array_at_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_slot_array_at_safety_wit_3 : cmc_slot_array_at_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_cmc_slot_array_at_safety_wit_4 : cmc_slot_array_at_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_cmc_slot_array_at_safety_wit_5 : cmc_slot_array_at_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_cmc_slot_array_at_partial_solve_wit_1 : cmc_slot_array_at_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_slot_array_at_partial_solve_wit_2_pure : cmc_slot_array_at_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_cmc_slot_array_at_partial_solve_wit_2 : cmc_slot_array_at_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_slot_type_at_safety_wit_1 : cmc_slot_type_at_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_slot_type_at_safety_wit_2 : cmc_slot_type_at_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_slot_type_at_safety_wit_3 : cmc_slot_type_at_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_cmc_slot_type_at_safety_wit_4 : cmc_slot_type_at_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_cmc_slot_type_at_safety_wit_5 : cmc_slot_type_at_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_cmc_slot_type_at_partial_solve_wit_1_pure : cmc_slot_type_at_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_cmc_slot_type_at_partial_solve_wit_1 : cmc_slot_type_at_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_member_array_at_safety_wit_1 : cmc_member_array_at_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_member_array_at_safety_wit_2 : cmc_member_array_at_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_member_array_at_safety_wit_3 : cmc_member_array_at_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_cmc_member_array_at_safety_wit_4 : cmc_member_array_at_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_cmc_member_array_at_safety_wit_5 : cmc_member_array_at_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_cmc_member_array_at_partial_solve_wit_1 : cmc_member_array_at_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_member_array_at_partial_solve_wit_2_pure : cmc_member_array_at_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_cmc_member_array_at_partial_solve_wit_2 : cmc_member_array_at_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_type_size_at_safety_wit_1 : cmc_type_size_at_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_type_size_at_safety_wit_2 : cmc_type_size_at_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_type_size_at_safety_wit_3 : cmc_type_size_at_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_cmc_type_size_at_safety_wit_4 : cmc_type_size_at_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_cmc_type_size_at_safety_wit_5 : cmc_type_size_at_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_cmc_type_size_at_safety_wit_6 : cmc_type_size_at_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_cmc_type_size_at_safety_wit_7 : cmc_type_size_at_safety_wit_7.
Proof. Admitted. 

Lemma proof_of_cmc_type_size_at_safety_wit_8 : cmc_type_size_at_safety_wit_8.
Proof. Admitted. 

Lemma proof_of_cmc_type_size_at_partial_solve_wit_1_pure : cmc_type_size_at_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_cmc_type_size_at_partial_solve_wit_1 : cmc_type_size_at_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_slots_size_safety_wit_1 : cmc_slots_size_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_slots_size_safety_wit_2 : cmc_slots_size_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_slots_size_partial_solve_wit_1 : cmc_slots_size_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_slots_size_partial_solve_wit_2_pure : cmc_slots_size_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_cmc_slots_size_partial_solve_wit_2 : cmc_slots_size_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_slots_prefix_safety_wit_1 : cmc_slots_prefix_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_slots_prefix_safety_wit_2 : cmc_slots_prefix_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_slots_prefix_safety_wit_3 : cmc_slots_prefix_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_cmc_slots_prefix_safety_wit_4 : cmc_slots_prefix_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_cmc_slots_prefix_safety_wit_5 : cmc_slots_prefix_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_cmc_slots_prefix_safety_wit_6 : cmc_slots_prefix_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_cmc_slots_prefix_partial_solve_wit_1 : cmc_slots_prefix_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_slots_prefix_partial_solve_wit_2_pure : cmc_slots_prefix_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_cmc_slots_prefix_partial_solve_wit_2 : cmc_slots_prefix_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_members_prefix_safety_wit_1 : cmc_members_prefix_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_members_prefix_safety_wit_2 : cmc_members_prefix_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_members_prefix_safety_wit_3 : cmc_members_prefix_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_cmc_members_prefix_safety_wit_4 : cmc_members_prefix_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_cmc_members_prefix_safety_wit_5 : cmc_members_prefix_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_cmc_members_prefix_safety_wit_6 : cmc_members_prefix_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_cmc_members_prefix_partial_solve_wit_1 : cmc_members_prefix_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_members_prefix_partial_solve_wit_2_pure : cmc_members_prefix_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_cmc_members_prefix_partial_solve_wit_2 : cmc_members_prefix_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_member_offset_at_safety_wit_1 : cmc_member_offset_at_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_member_offset_at_safety_wit_2 : cmc_member_offset_at_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_member_offset_at_safety_wit_3 : cmc_member_offset_at_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_cmc_member_offset_at_safety_wit_4 : cmc_member_offset_at_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_cmc_member_offset_at_safety_wit_5 : cmc_member_offset_at_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_cmc_member_offset_at_partial_solve_wit_1_pure : cmc_member_offset_at_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_cmc_member_offset_at_partial_solve_wit_1 : cmc_member_offset_at_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_member_offset_at_partial_solve_wit_2_pure : cmc_member_offset_at_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_cmc_member_offset_at_partial_solve_wit_2 : cmc_member_offset_at_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_struct_member_array_at_safety_wit_1 : cmc_struct_member_array_at_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_struct_member_array_at_safety_wit_2 : cmc_struct_member_array_at_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_struct_member_array_at_safety_wit_3 : cmc_struct_member_array_at_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_cmc_struct_member_array_at_safety_wit_4 : cmc_struct_member_array_at_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_cmc_struct_member_array_at_safety_wit_5 : cmc_struct_member_array_at_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_cmc_struct_member_array_at_partial_solve_wit_1_pure : cmc_struct_member_array_at_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_cmc_struct_member_array_at_partial_solve_wit_1 : cmc_struct_member_array_at_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_struct_member_array_at_partial_solve_wit_2_pure : cmc_struct_member_array_at_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_cmc_struct_member_array_at_partial_solve_wit_2 : cmc_struct_member_array_at_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_globals_size_safety_wit_1 : cmc_globals_size_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_globals_size_safety_wit_2 : cmc_globals_size_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_globals_size_partial_solve_wit_1 : cmc_globals_size_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_globals_size_partial_solve_wit_2_pure : cmc_globals_size_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_cmc_globals_size_partial_solve_wit_2 : cmc_globals_size_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_globals_prefix_safety_wit_1 : cmc_globals_prefix_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_globals_prefix_safety_wit_2 : cmc_globals_prefix_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_globals_prefix_safety_wit_3 : cmc_globals_prefix_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_cmc_globals_prefix_safety_wit_4 : cmc_globals_prefix_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_cmc_globals_prefix_safety_wit_5 : cmc_globals_prefix_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_cmc_globals_prefix_safety_wit_6 : cmc_globals_prefix_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_cmc_globals_prefix_partial_solve_wit_1 : cmc_globals_prefix_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_globals_prefix_partial_solve_wit_2_pure : cmc_globals_prefix_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_cmc_globals_prefix_partial_solve_wit_2 : cmc_globals_prefix_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_strings_size_safety_wit_1 : cmc_strings_size_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_strings_size_safety_wit_2 : cmc_strings_size_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_strings_size_safety_wit_3 : cmc_strings_size_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_cmc_strings_size_safety_wit_4 : cmc_strings_size_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_cmc_strings_size_safety_wit_5 : cmc_strings_size_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_cmc_strings_size_partial_solve_wit_1_pure : cmc_strings_size_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_cmc_strings_size_partial_solve_wit_1 : cmc_strings_size_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_strings_prefix_safety_wit_1 : cmc_strings_prefix_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_strings_prefix_safety_wit_2 : cmc_strings_prefix_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_strings_prefix_safety_wit_3 : cmc_strings_prefix_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_cmc_strings_prefix_safety_wit_4 : cmc_strings_prefix_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_cmc_strings_prefix_safety_wit_5 : cmc_strings_prefix_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_cmc_strings_prefix_safety_wit_6 : cmc_strings_prefix_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_cmc_strings_prefix_safety_wit_7 : cmc_strings_prefix_safety_wit_7.
Proof. Admitted. 

Lemma proof_of_cmc_strings_prefix_safety_wit_8 : cmc_strings_prefix_safety_wit_8.
Proof. Admitted. 

Lemma proof_of_cmc_strings_prefix_safety_wit_9 : cmc_strings_prefix_safety_wit_9.
Proof. Admitted. 

Lemma proof_of_cmc_strings_prefix_partial_solve_wit_1_pure : cmc_strings_prefix_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_cmc_strings_prefix_partial_solve_wit_1 : cmc_strings_prefix_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_global_address_safety_wit_1 : cmc_global_address_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_global_address_safety_wit_2 : cmc_global_address_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_global_address_partial_solve_wit_1_pure : cmc_global_address_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_cmc_global_address_partial_solve_wit_1 : cmc_global_address_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_string_address_safety_wit_1 : cmc_string_address_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_string_address_safety_wit_2 : cmc_string_address_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_string_address_safety_wit_3 : cmc_string_address_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_cmc_string_address_partial_solve_wit_1_pure : cmc_string_address_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_cmc_string_address_partial_solve_wit_1 : cmc_string_address_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_string_address_partial_solve_wit_2_pure : cmc_string_address_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_cmc_string_address_partial_solve_wit_2 : cmc_string_address_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_binding_array_value_safety_wit_1 : cmc_binding_array_value_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_binding_array_value_safety_wit_2 : cmc_binding_array_value_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_binding_array_value_safety_wit_3 : cmc_binding_array_value_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_cmc_binding_array_value_partial_solve_wit_1_pure : cmc_binding_array_value_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_cmc_binding_array_value_partial_solve_wit_1 : cmc_binding_array_value_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_binding_array_value_partial_solve_wit_2_pure : cmc_binding_array_value_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_cmc_binding_array_value_partial_solve_wit_2 : cmc_binding_array_value_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_binding_array_return_wit_1 : cmc_binding_array_return_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_binding_array_partial_solve_wit_1_pure : cmc_binding_array_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_cmc_binding_array_partial_solve_wit_1 : cmc_binding_array_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_member_array_safety_wit_2 : cmc_member_array_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_member_array_safety_wit_3 : cmc_member_array_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_cmc_member_array_safety_wit_4 : cmc_member_array_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_cmc_member_array_partial_solve_wit_1_pure : cmc_member_array_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_cmc_member_array_partial_solve_wit_1 : cmc_member_array_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_member_array_partial_solve_wit_2_pure : cmc_member_array_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_cmc_member_array_partial_solve_wit_2 : cmc_member_array_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_member_array_value_return_wit_1 : cmc_member_array_value_return_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_member_array_value_partial_solve_wit_1_pure : cmc_member_array_value_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_cmc_member_array_value_partial_solve_wit_1 : cmc_member_array_value_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cm_args_length_safety_wit_1 : cm_args_length_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cm_args_length_safety_wit_2 : cm_args_length_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cm_args_length_safety_wit_4 : cm_args_length_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_cm_args_length_partial_solve_wit_1_pure : cm_args_length_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_cm_args_length_partial_solve_wit_1 : cm_args_length_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_args_tpair_safety_wit_1 : cmc_args_tpair_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_args_tpair_safety_wit_2 : cmc_args_tpair_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_args_tpair_safety_wit_3 : cmc_args_tpair_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_cmc_args_tpair_safety_wit_5 : cmc_args_tpair_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_cmc_args_tpair_partial_solve_wit_1_pure : cmc_args_tpair_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_cmc_args_tpair_partial_solve_wit_1 : cmc_args_tpair_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_args_tpair_partial_solve_wit_2_pure : cmc_args_tpair_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_cmc_args_tpair_partial_solve_wit_2 : cmc_args_tpair_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_args_tpair_partial_solve_wit_3 : cmc_args_tpair_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_safety_wit_1 : cm_expr_temps_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_safety_wit_2 : cm_expr_temps_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_safety_wit_3 : cm_expr_temps_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_safety_wit_5 : cm_expr_temps_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_safety_wit_6 : cm_expr_temps_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_safety_wit_7 : cm_expr_temps_safety_wit_7.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_safety_wit_8 : cm_expr_temps_safety_wit_8.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_safety_wit_10 : cm_expr_temps_safety_wit_10.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_safety_wit_11 : cm_expr_temps_safety_wit_11.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_safety_wit_12 : cm_expr_temps_safety_wit_12.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_safety_wit_13 : cm_expr_temps_safety_wit_13.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_safety_wit_14 : cm_expr_temps_safety_wit_14.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_safety_wit_16 : cm_expr_temps_safety_wit_16.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_safety_wit_17 : cm_expr_temps_safety_wit_17.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_safety_wit_18 : cm_expr_temps_safety_wit_18.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_safety_wit_20 : cm_expr_temps_safety_wit_20.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_safety_wit_21 : cm_expr_temps_safety_wit_21.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_safety_wit_22 : cm_expr_temps_safety_wit_22.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_safety_wit_23 : cm_expr_temps_safety_wit_23.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_safety_wit_24 : cm_expr_temps_safety_wit_24.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_safety_wit_25 : cm_expr_temps_safety_wit_25.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_safety_wit_26 : cm_expr_temps_safety_wit_26.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_safety_wit_27 : cm_expr_temps_safety_wit_27.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_partial_solve_wit_1_pure : cm_expr_temps_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_partial_solve_wit_1 : cm_expr_temps_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_partial_solve_wit_2_pure : cm_expr_temps_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_partial_solve_wit_2 : cm_expr_temps_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_partial_solve_wit_3 : cm_expr_temps_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_partial_solve_wit_4_pure : cm_expr_temps_partial_solve_wit_4_pure.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_partial_solve_wit_4 : cm_expr_temps_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_partial_solve_wit_5_pure : cm_expr_temps_partial_solve_wit_5_pure.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_partial_solve_wit_5 : cm_expr_temps_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_partial_solve_wit_6 : cm_expr_temps_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_partial_solve_wit_7 : cm_expr_temps_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_partial_solve_wit_8 : cm_expr_temps_partial_solve_wit_8.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_partial_solve_wit_9_pure : cm_expr_temps_partial_solve_wit_9_pure.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_partial_solve_wit_9 : cm_expr_temps_partial_solve_wit_9.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_partial_solve_wit_10_pure : cm_expr_temps_partial_solve_wit_10_pure.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_partial_solve_wit_10 : cm_expr_temps_partial_solve_wit_10.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_partial_solve_wit_11_pure : cm_expr_temps_partial_solve_wit_11_pure.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_partial_solve_wit_11 : cm_expr_temps_partial_solve_wit_11.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_partial_solve_wit_12 : cm_expr_temps_partial_solve_wit_12.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_partial_solve_wit_13_pure : cm_expr_temps_partial_solve_wit_13_pure.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_partial_solve_wit_13 : cm_expr_temps_partial_solve_wit_13.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_partial_solve_wit_14_pure : cm_expr_temps_partial_solve_wit_14_pure.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_partial_solve_wit_14 : cm_expr_temps_partial_solve_wit_14.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_partial_solve_wit_15_pure : cm_expr_temps_partial_solve_wit_15_pure.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_partial_solve_wit_15 : cm_expr_temps_partial_solve_wit_15.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_partial_solve_wit_16_pure : cm_expr_temps_partial_solve_wit_16_pure.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_partial_solve_wit_16 : cm_expr_temps_partial_solve_wit_16.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_partial_solve_wit_17_pure : cm_expr_temps_partial_solve_wit_17_pure.
Proof. Admitted. 

Lemma proof_of_cm_expr_temps_partial_solve_wit_17 : cm_expr_temps_partial_solve_wit_17.
Proof. Admitted. 

Lemma proof_of_cm_expr_rtemps_return_wit_1 : cm_expr_rtemps_return_wit_1.
Proof. Admitted. 

Lemma proof_of_cm_expr_rtemps_partial_solve_wit_1_pure : cm_expr_rtemps_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_cm_expr_rtemps_partial_solve_wit_1 : cm_expr_rtemps_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_safety_wit_1 : cmc_stmt_temps_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_safety_wit_2 : cmc_stmt_temps_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_safety_wit_3 : cmc_stmt_temps_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_safety_wit_4 : cmc_stmt_temps_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_safety_wit_5 : cmc_stmt_temps_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_safety_wit_6 : cmc_stmt_temps_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_safety_wit_7 : cmc_stmt_temps_safety_wit_7.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_safety_wit_8 : cmc_stmt_temps_safety_wit_8.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_safety_wit_9 : cmc_stmt_temps_safety_wit_9.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_safety_wit_10 : cmc_stmt_temps_safety_wit_10.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_safety_wit_11 : cmc_stmt_temps_safety_wit_11.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_safety_wit_12 : cmc_stmt_temps_safety_wit_12.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_safety_wit_13 : cmc_stmt_temps_safety_wit_13.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_safety_wit_14 : cmc_stmt_temps_safety_wit_14.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_safety_wit_15 : cmc_stmt_temps_safety_wit_15.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_safety_wit_16 : cmc_stmt_temps_safety_wit_16.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_safety_wit_17 : cmc_stmt_temps_safety_wit_17.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_partial_solve_wit_1_pure : cmc_stmt_temps_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_partial_solve_wit_1 : cmc_stmt_temps_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_partial_solve_wit_2_pure : cmc_stmt_temps_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_partial_solve_wit_2 : cmc_stmt_temps_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_partial_solve_wit_3_pure : cmc_stmt_temps_partial_solve_wit_3_pure.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_partial_solve_wit_3 : cmc_stmt_temps_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_partial_solve_wit_4_pure : cmc_stmt_temps_partial_solve_wit_4_pure.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_partial_solve_wit_4 : cmc_stmt_temps_partial_solve_wit_4.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_partial_solve_wit_5_pure : cmc_stmt_temps_partial_solve_wit_5_pure.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_partial_solve_wit_5 : cmc_stmt_temps_partial_solve_wit_5.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_partial_solve_wit_6 : cmc_stmt_temps_partial_solve_wit_6.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_partial_solve_wit_7_pure : cmc_stmt_temps_partial_solve_wit_7_pure.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_partial_solve_wit_7 : cmc_stmt_temps_partial_solve_wit_7.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_partial_solve_wit_8_pure : cmc_stmt_temps_partial_solve_wit_8_pure.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_partial_solve_wit_8 : cmc_stmt_temps_partial_solve_wit_8.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_partial_solve_wit_9_pure : cmc_stmt_temps_partial_solve_wit_9_pure.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_partial_solve_wit_9 : cmc_stmt_temps_partial_solve_wit_9.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_partial_solve_wit_10_pure : cmc_stmt_temps_partial_solve_wit_10_pure.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_partial_solve_wit_10 : cmc_stmt_temps_partial_solve_wit_10.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_partial_solve_wit_11 : cmc_stmt_temps_partial_solve_wit_11.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_partial_solve_wit_12 : cmc_stmt_temps_partial_solve_wit_12.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_partial_solve_wit_13_pure : cmc_stmt_temps_partial_solve_wit_13_pure.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_partial_solve_wit_13 : cmc_stmt_temps_partial_solve_wit_13.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_partial_solve_wit_14_pure : cmc_stmt_temps_partial_solve_wit_14_pure.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_partial_solve_wit_14 : cmc_stmt_temps_partial_solve_wit_14.
Proof. Admitted. 

Lemma proof_of_cmc_stmt_temps_partial_solve_wit_15 : cmc_stmt_temps_partial_solve_wit_15.
Proof. Admitted. 

Lemma proof_of_cmc_frame_size_safety_wit_1 : cmc_frame_size_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_frame_size_safety_wit_2 : cmc_frame_size_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_frame_size_safety_wit_3 : cmc_frame_size_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_cmc_frame_size_safety_wit_4 : cmc_frame_size_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_cmc_frame_size_safety_wit_5 : cmc_frame_size_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_cmc_frame_size_safety_wit_6 : cmc_frame_size_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_cmc_frame_size_return_wit_1 : cmc_frame_size_return_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_frame_size_partial_solve_wit_1_pure : cmc_frame_size_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_cmc_frame_size_partial_solve_wit_1 : cmc_frame_size_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_frame_size_partial_solve_wit_2_pure : cmc_frame_size_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_cmc_frame_size_partial_solve_wit_2 : cmc_frame_size_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_frame_size_partial_solve_wit_3_pure : cmc_frame_size_partial_solve_wit_3_pure.
Proof. Admitted. 

Lemma proof_of_cmc_frame_size_partial_solve_wit_3 : cmc_frame_size_partial_solve_wit_3.
Proof. Admitted. 

Lemma proof_of_cmc_param_offset_safety_wit_1 : cmc_param_offset_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_param_offset_safety_wit_2 : cmc_param_offset_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_param_offset_return_wit_1 : cmc_param_offset_return_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_param_offset_partial_solve_wit_1_pure : cmc_param_offset_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_cmc_param_offset_partial_solve_wit_1 : cmc_param_offset_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_local_offset_safety_wit_1 : cmc_local_offset_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_local_offset_safety_wit_2 : cmc_local_offset_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_local_offset_safety_wit_3 : cmc_local_offset_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_cmc_local_offset_return_wit_1 : cmc_local_offset_return_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_local_offset_partial_solve_wit_1_pure : cmc_local_offset_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_cmc_local_offset_partial_solve_wit_1 : cmc_local_offset_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_local_offset_partial_solve_wit_2_pure : cmc_local_offset_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_cmc_local_offset_partial_solve_wit_2 : cmc_local_offset_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_temp_offset_safety_wit_1 : cmc_temp_offset_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_temp_offset_safety_wit_2 : cmc_temp_offset_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cmc_temp_offset_safety_wit_3 : cmc_temp_offset_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_cmc_temp_offset_safety_wit_4 : cmc_temp_offset_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_cmc_temp_offset_safety_wit_5 : cmc_temp_offset_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_cmc_temp_offset_safety_wit_6 : cmc_temp_offset_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_cmc_temp_offset_return_wit_1 : cmc_temp_offset_return_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_temp_offset_partial_solve_wit_1_pure : cmc_temp_offset_partial_solve_wit_1_pure.
Proof. Admitted. 

Lemma proof_of_cmc_temp_offset_partial_solve_wit_1 : cmc_temp_offset_partial_solve_wit_1.
Proof. Admitted. 

Lemma proof_of_cmc_temp_offset_partial_solve_wit_2_pure : cmc_temp_offset_partial_solve_wit_2_pure.
Proof. Admitted. 

Lemma proof_of_cmc_temp_offset_partial_solve_wit_2 : cmc_temp_offset_partial_solve_wit_2.
Proof. Admitted. 

Lemma proof_of_cm_normalize_count_safety_wit_1 : cm_normalize_count_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cm_normalize_count_safety_wit_2 : cm_normalize_count_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cm_normalize_count_safety_wit_3 : cm_normalize_count_safety_wit_3.
Proof. Admitted. 

