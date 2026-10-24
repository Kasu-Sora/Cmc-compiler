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
From SimpleC.EE.QCP_demos_human Require Import cmc_write_char_migration_goal.
From SimpleC.EE.QCP_demos_human Require Import cmc_write_char_migration_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.cmc_write_word_migration_lib.
Local Open Scope sac.

Lemma proof_of_cmc_write_char_partial_solve_wit_1_pure_split_goal_1 : cmc_write_char_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold unsigned_last_nbits.
  pose proof (tower_machine_rem_byte__byte_encoding char_value_pre 0 ltac:(lia)) as Hbyte.
  cbn [Z.pow] in Hbyte.
  rewrite Z.quot_1_r in Hbyte.
  unfold tower_encode_byte in Hbyte.
  cbn [Z.eqb] in Hbyte.
  exact Hbyte.
Qed.

Lemma proof_of_cmc_write_char_partial_solve_wit_1_pure_split_goal_2 : cmc_write_char_partial_solve_wit_1_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold tower_u8.
  exact (proj1 (Z.mod_pos_bound char_value_pre 256 ltac:(lia))).
Qed.

Lemma proof_of_cmc_write_char_partial_solve_wit_1_pure_split_goal_3 : cmc_write_char_partial_solve_wit_1_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold tower_u8.
  exact (proj2 (Z.mod_pos_bound char_value_pre 256 ltac:(lia))).
Qed.

Lemma proof_of_cmc_write_char_partial_solve_wit_1_pure : cmc_write_char_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_write_char_partial_solve_wit_1_pure_split_goal_1.
  - Goal_apply proof_of_cmc_write_char_partial_solve_wit_1_pure_split_goal_2.
  - Goal_apply proof_of_cmc_write_char_partial_solve_wit_1_pure_split_goal_3.
Qed.

