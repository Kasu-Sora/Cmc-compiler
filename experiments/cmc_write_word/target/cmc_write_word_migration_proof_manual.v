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
From SimpleC.EE.QCP_demos_human Require Import cmc_write_word_migration_goal.
From SimpleC.EE.QCP_demos_human Require Import cmc_write_word_migration_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.cmc_write_word_migration_lib.
Local Open Scope sac.

Lemma proof_of_cmc_write_word_entail_wit_1_split_goal_1 : cmc_write_word_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  exact (tower_machine_rem_byte__byte_encoding word_value_pre 7 ltac:(lia)).
Qed.

Lemma proof_of_cmc_write_word_entail_wit_1_split_goal_2 : cmc_write_word_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  exact (tower_machine_rem_byte__byte_encoding word_value_pre 6 ltac:(lia)).
Qed.

Lemma proof_of_cmc_write_word_entail_wit_1_split_goal_3 : cmc_write_word_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  exact (tower_machine_rem_byte__byte_encoding word_value_pre 5 ltac:(lia)).
Qed.

Lemma proof_of_cmc_write_word_entail_wit_1_split_goal_4 : cmc_write_word_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  exact (tower_machine_rem_byte__byte_encoding word_value_pre 4 ltac:(lia)).
Qed.

Lemma proof_of_cmc_write_word_entail_wit_1_split_goal_5 : cmc_write_word_entail_wit_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  exact (tower_machine_rem_byte__byte_encoding word_value_pre 3 ltac:(lia)).
Qed.

Lemma proof_of_cmc_write_word_entail_wit_1_split_goal_6 : cmc_write_word_entail_wit_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  exact (tower_machine_rem_byte__byte_encoding word_value_pre 2 ltac:(lia)).
Qed.

Lemma proof_of_cmc_write_word_entail_wit_1_split_goal_7 : cmc_write_word_entail_wit_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  exact (tower_machine_rem_byte__byte_encoding word_value_pre 1 ltac:(lia)).
Qed.

Lemma proof_of_cmc_write_word_entail_wit_1_split_goal_8 : cmc_write_word_entail_wit_1_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (tower_machine_rem_byte__byte_encoding word_value_pre 0 ltac:(lia)) as Hbyte.
  change (unsigned_last_nbits (Z.rem (Z.quot (unsigned_last_nbits word_value_pre 64) 1) 256) 8 = tower_encode_byte word_value_pre 0) in Hbyte.
  rewrite Z.quot_1_r in Hbyte. exact Hbyte.
Qed.

Lemma proof_of_cmc_write_word_entail_wit_1_split_goal_spatial : cmc_write_word_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (cursor_pre + 1 + 1) with (cursor_pre + 2) by lia.
  reflexivity.
Qed.

Lemma proof_of_cmc_write_word_entail_wit_1 : cmc_write_word_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_write_word_entail_wit_1_split_goal_spatial.
  - Goal_apply proof_of_cmc_write_word_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_cmc_write_word_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_cmc_write_word_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_cmc_write_word_entail_wit_1_split_goal_4.
  - Goal_apply proof_of_cmc_write_word_entail_wit_1_split_goal_5.
  - Goal_apply proof_of_cmc_write_word_entail_wit_1_split_goal_6.
  - Goal_apply proof_of_cmc_write_word_entail_wit_1_split_goal_7.
  - Goal_apply proof_of_cmc_write_word_entail_wit_1_split_goal_8.
Qed.

Lemma proof_of_cmc_write_word_entail_wit_2_split_goal_spatial : cmc_write_word_entail_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace ((cursor_pre + 2) + 1) with (cursor_pre + 3) by lia.
  reflexivity.
Qed.

Lemma proof_of_cmc_write_word_entail_wit_2 : cmc_write_word_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_write_word_entail_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_cmc_write_word_entail_wit_3_split_goal_spatial : cmc_write_word_entail_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace ((cursor_pre + 3) + 1) with (cursor_pre + 4) by lia.
  reflexivity.
Qed.

Lemma proof_of_cmc_write_word_entail_wit_3 : cmc_write_word_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_write_word_entail_wit_3_split_goal_spatial.
Qed.

Lemma proof_of_cmc_write_word_entail_wit_4_split_goal_spatial : cmc_write_word_entail_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace ((cursor_pre + 4) + 1) with (cursor_pre + 5) by lia.
  reflexivity.
Qed.

Lemma proof_of_cmc_write_word_entail_wit_4 : cmc_write_word_entail_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_write_word_entail_wit_4_split_goal_spatial.
Qed.

Lemma proof_of_cmc_write_word_entail_wit_5_split_goal_spatial : cmc_write_word_entail_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace ((cursor_pre + 5) + 1) with (cursor_pre + 6) by lia.
  reflexivity.
Qed.

Lemma proof_of_cmc_write_word_entail_wit_5 : cmc_write_word_entail_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_write_word_entail_wit_5_split_goal_spatial.
Qed.

Lemma proof_of_cmc_write_word_entail_wit_6_split_goal_spatial : cmc_write_word_entail_wit_6_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace ((cursor_pre + 6) + 1) with (cursor_pre + 7) by lia.
  reflexivity.
Qed.

Lemma proof_of_cmc_write_word_entail_wit_6 : cmc_write_word_entail_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_write_word_entail_wit_6_split_goal_spatial.
Qed.

Lemma proof_of_cmc_write_word_return_wit_1_split_goal_spatial : cmc_write_word_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace ((cursor_pre + 7) + 1) with (cursor_pre + 8) by lia.
  unfold tower_word_bytes.
  repeat rewrite <- app_assoc.
  cbn [app].
  cancel (UCharArray.seg data_pre 0 (cursor_pre + 8)
    (prefix ++ tower_word_bytes word_value_pre)).
Qed.

Lemma proof_of_cmc_write_word_return_wit_1 : cmc_write_word_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_write_word_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cmc_write_word_partial_solve_wit_1_pure_split_goal_1 : cmc_write_word_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (tower_machine_rem_byte__byte_encoding word_value_pre 0 ltac:(lia)) as Hbyte.
  change (unsigned_last_nbits (Z.rem (Z.quot (unsigned_last_nbits word_value_pre 64) 1) 256) 8 = tower_encode_byte word_value_pre 0) in Hbyte.
  rewrite Z.quot_1_r in Hbyte. exact Hbyte.
Qed.

Lemma proof_of_cmc_write_word_partial_solve_wit_1_pure_split_goal_2 : cmc_write_word_partial_solve_wit_1_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold tower_encode_byte, tower_u8.
  apply Z.mod_pos_bound. lia.
Qed.

Lemma proof_of_cmc_write_word_partial_solve_wit_1_pure_split_goal_3 : cmc_write_word_partial_solve_wit_1_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold tower_encode_byte, tower_u8.
  apply Z.mod_pos_bound. lia.
Qed.

Lemma proof_of_cmc_write_word_partial_solve_wit_1_pure : cmc_write_word_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_write_word_partial_solve_wit_1_pure_split_goal_1.
  - Goal_apply proof_of_cmc_write_word_partial_solve_wit_1_pure_split_goal_2.
  - Goal_apply proof_of_cmc_write_word_partial_solve_wit_1_pure_split_goal_3.
Qed.

Lemma proof_of_cmc_write_word_partial_solve_wit_2_pure_split_goal_1 : cmc_write_word_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  exact (tower_machine_rem_byte__byte_encoding word_value_pre 1 ltac:(lia)).
Qed.

Lemma proof_of_cmc_write_word_partial_solve_wit_2_pure_split_goal_2 : cmc_write_word_partial_solve_wit_2_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold tower_encode_byte, tower_u8.
  apply Z.mod_pos_bound. lia.
Qed.

Lemma proof_of_cmc_write_word_partial_solve_wit_2_pure_split_goal_3 : cmc_write_word_partial_solve_wit_2_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  unfold tower_encode_byte, tower_u8.
  apply Z.mod_pos_bound. lia.
Qed.

Lemma proof_of_cmc_write_word_partial_solve_wit_2_pure : cmc_write_word_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_write_word_partial_solve_wit_2_pure_split_goal_1.
  - Goal_apply proof_of_cmc_write_word_partial_solve_wit_2_pure_split_goal_2.
  - Goal_apply proof_of_cmc_write_word_partial_solve_wit_2_pure_split_goal_3.
Qed.

Lemma proof_of_cmc_write_word_partial_solve_wit_3_pure_split_goal_1 : cmc_write_word_partial_solve_wit_3_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  rewrite PreH11.
  cbn [tower_encode_byte tower_u8].
  apply (proj1 (Z.mod_pos_bound _ 256 ltac:(lia))).
Qed.

Lemma proof_of_cmc_write_word_partial_solve_wit_3_pure_split_goal_2 : cmc_write_word_partial_solve_wit_3_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  rewrite PreH11.
  cbn [tower_encode_byte tower_u8].
  apply (proj2 (Z.mod_pos_bound _ 256 ltac:(lia))).
Qed.

Lemma proof_of_cmc_write_word_partial_solve_wit_3_pure_split_goal_3 : cmc_write_word_partial_solve_wit_3_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  rewrite PreH11.
  cbn [tower_encode_byte tower_u8].
  apply (proj2 (Z.mod_pos_bound _ 256 ltac:(lia))).
Qed.

Lemma proof_of_cmc_write_word_partial_solve_wit_3_pure_split_goal_4 : cmc_write_word_partial_solve_wit_3_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  rewrite PreH11.
  cbn [tower_encode_byte tower_u8].
  apply (proj1 (Z.mod_pos_bound _ 256 ltac:(lia))).
Qed.

Lemma proof_of_cmc_write_word_partial_solve_wit_3_pure : cmc_write_word_partial_solve_wit_3_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_write_word_partial_solve_wit_3_pure_split_goal_1.
  - Goal_apply proof_of_cmc_write_word_partial_solve_wit_3_pure_split_goal_2.
  - Goal_apply proof_of_cmc_write_word_partial_solve_wit_3_pure_split_goal_3.
  - Goal_apply proof_of_cmc_write_word_partial_solve_wit_3_pure_split_goal_4.
Qed.

Lemma proof_of_cmc_write_word_partial_solve_wit_4_pure_split_goal_1 : cmc_write_word_partial_solve_wit_4_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  rewrite PreH12.
  cbn [tower_encode_byte tower_u8].
  apply (proj1 (Z.mod_pos_bound _ 256 ltac:(lia))).
Qed.

Lemma proof_of_cmc_write_word_partial_solve_wit_4_pure_split_goal_2 : cmc_write_word_partial_solve_wit_4_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  rewrite PreH12.
  cbn [tower_encode_byte tower_u8].
  apply (proj2 (Z.mod_pos_bound _ 256 ltac:(lia))).
Qed.

Lemma proof_of_cmc_write_word_partial_solve_wit_4_pure_split_goal_3 : cmc_write_word_partial_solve_wit_4_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  rewrite PreH12.
  cbn [tower_encode_byte tower_u8].
  apply (proj2 (Z.mod_pos_bound _ 256 ltac:(lia))).
Qed.

Lemma proof_of_cmc_write_word_partial_solve_wit_4_pure_split_goal_4 : cmc_write_word_partial_solve_wit_4_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  rewrite PreH12.
  cbn [tower_encode_byte tower_u8].
  apply (proj1 (Z.mod_pos_bound _ 256 ltac:(lia))).
Qed.

Lemma proof_of_cmc_write_word_partial_solve_wit_4_pure : cmc_write_word_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_write_word_partial_solve_wit_4_pure_split_goal_1.
  - Goal_apply proof_of_cmc_write_word_partial_solve_wit_4_pure_split_goal_2.
  - Goal_apply proof_of_cmc_write_word_partial_solve_wit_4_pure_split_goal_3.
  - Goal_apply proof_of_cmc_write_word_partial_solve_wit_4_pure_split_goal_4.
Qed.

Lemma proof_of_cmc_write_word_partial_solve_wit_5_pure_split_goal_1 : cmc_write_word_partial_solve_wit_5_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  rewrite PreH13.
  cbn [tower_encode_byte tower_u8].
  apply (proj1 (Z.mod_pos_bound _ 256 ltac:(lia))).
Qed.

Lemma proof_of_cmc_write_word_partial_solve_wit_5_pure_split_goal_2 : cmc_write_word_partial_solve_wit_5_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  rewrite PreH13.
  cbn [tower_encode_byte tower_u8].
  apply (proj2 (Z.mod_pos_bound _ 256 ltac:(lia))).
Qed.

Lemma proof_of_cmc_write_word_partial_solve_wit_5_pure_split_goal_3 : cmc_write_word_partial_solve_wit_5_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  rewrite PreH13.
  cbn [tower_encode_byte tower_u8].
  apply (proj2 (Z.mod_pos_bound _ 256 ltac:(lia))).
Qed.

Lemma proof_of_cmc_write_word_partial_solve_wit_5_pure_split_goal_4 : cmc_write_word_partial_solve_wit_5_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  rewrite PreH13.
  cbn [tower_encode_byte tower_u8].
  apply (proj1 (Z.mod_pos_bound _ 256 ltac:(lia))).
Qed.

Lemma proof_of_cmc_write_word_partial_solve_wit_5_pure : cmc_write_word_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_write_word_partial_solve_wit_5_pure_split_goal_1.
  - Goal_apply proof_of_cmc_write_word_partial_solve_wit_5_pure_split_goal_2.
  - Goal_apply proof_of_cmc_write_word_partial_solve_wit_5_pure_split_goal_3.
  - Goal_apply proof_of_cmc_write_word_partial_solve_wit_5_pure_split_goal_4.
Qed.

Lemma proof_of_cmc_write_word_partial_solve_wit_6_pure_split_goal_1 : cmc_write_word_partial_solve_wit_6_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  rewrite PreH14.
  cbn [tower_encode_byte tower_u8].
  apply (proj1 (Z.mod_pos_bound _ 256 ltac:(lia))).
Qed.

Lemma proof_of_cmc_write_word_partial_solve_wit_6_pure_split_goal_2 : cmc_write_word_partial_solve_wit_6_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  rewrite PreH14.
  cbn [tower_encode_byte tower_u8].
  apply (proj2 (Z.mod_pos_bound _ 256 ltac:(lia))).
Qed.

Lemma proof_of_cmc_write_word_partial_solve_wit_6_pure_split_goal_3 : cmc_write_word_partial_solve_wit_6_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  rewrite PreH14.
  cbn [tower_encode_byte tower_u8].
  apply (proj2 (Z.mod_pos_bound _ 256 ltac:(lia))).
Qed.

Lemma proof_of_cmc_write_word_partial_solve_wit_6_pure_split_goal_4 : cmc_write_word_partial_solve_wit_6_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  rewrite PreH14.
  cbn [tower_encode_byte tower_u8].
  apply (proj1 (Z.mod_pos_bound _ 256 ltac:(lia))).
Qed.

Lemma proof_of_cmc_write_word_partial_solve_wit_6_pure : cmc_write_word_partial_solve_wit_6_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_write_word_partial_solve_wit_6_pure_split_goal_1.
  - Goal_apply proof_of_cmc_write_word_partial_solve_wit_6_pure_split_goal_2.
  - Goal_apply proof_of_cmc_write_word_partial_solve_wit_6_pure_split_goal_3.
  - Goal_apply proof_of_cmc_write_word_partial_solve_wit_6_pure_split_goal_4.
Qed.

Lemma proof_of_cmc_write_word_partial_solve_wit_7_pure_split_goal_1 : cmc_write_word_partial_solve_wit_7_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  rewrite PreH15.
  cbn [tower_encode_byte tower_u8].
  apply (proj1 (Z.mod_pos_bound _ 256 ltac:(lia))).
Qed.

Lemma proof_of_cmc_write_word_partial_solve_wit_7_pure_split_goal_2 : cmc_write_word_partial_solve_wit_7_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  rewrite PreH15.
  cbn [tower_encode_byte tower_u8].
  apply (proj2 (Z.mod_pos_bound _ 256 ltac:(lia))).
Qed.

Lemma proof_of_cmc_write_word_partial_solve_wit_7_pure_split_goal_3 : cmc_write_word_partial_solve_wit_7_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  rewrite PreH15.
  cbn [tower_encode_byte tower_u8].
  apply (proj2 (Z.mod_pos_bound _ 256 ltac:(lia))).
Qed.

Lemma proof_of_cmc_write_word_partial_solve_wit_7_pure_split_goal_4 : cmc_write_word_partial_solve_wit_7_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  rewrite PreH15.
  cbn [tower_encode_byte tower_u8].
  apply (proj1 (Z.mod_pos_bound _ 256 ltac:(lia))).
Qed.

Lemma proof_of_cmc_write_word_partial_solve_wit_7_pure : cmc_write_word_partial_solve_wit_7_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_write_word_partial_solve_wit_7_pure_split_goal_1.
  - Goal_apply proof_of_cmc_write_word_partial_solve_wit_7_pure_split_goal_2.
  - Goal_apply proof_of_cmc_write_word_partial_solve_wit_7_pure_split_goal_3.
  - Goal_apply proof_of_cmc_write_word_partial_solve_wit_7_pure_split_goal_4.
Qed.

Lemma proof_of_cmc_write_word_partial_solve_wit_8_pure_split_goal_1 : cmc_write_word_partial_solve_wit_8_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  rewrite PreH16.
  cbn [tower_encode_byte tower_u8].
  apply (proj1 (Z.mod_pos_bound _ 256 ltac:(lia))).
Qed.

Lemma proof_of_cmc_write_word_partial_solve_wit_8_pure_split_goal_2 : cmc_write_word_partial_solve_wit_8_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  rewrite PreH16.
  cbn [tower_encode_byte tower_u8].
  apply (proj2 (Z.mod_pos_bound _ 256 ltac:(lia))).
Qed.

Lemma proof_of_cmc_write_word_partial_solve_wit_8_pure_split_goal_3 : cmc_write_word_partial_solve_wit_8_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  rewrite PreH16.
  cbn [tower_encode_byte tower_u8].
  apply (proj2 (Z.mod_pos_bound _ 256 ltac:(lia))).
Qed.

Lemma proof_of_cmc_write_word_partial_solve_wit_8_pure_split_goal_4 : cmc_write_word_partial_solve_wit_8_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  rewrite PreH16.
  cbn [tower_encode_byte tower_u8].
  apply (proj1 (Z.mod_pos_bound _ 256 ltac:(lia))).
Qed.

Lemma proof_of_cmc_write_word_partial_solve_wit_8_pure : cmc_write_word_partial_solve_wit_8_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_write_word_partial_solve_wit_8_pure_split_goal_1.
  - Goal_apply proof_of_cmc_write_word_partial_solve_wit_8_pure_split_goal_2.
  - Goal_apply proof_of_cmc_write_word_partial_solve_wit_8_pure_split_goal_3.
  - Goal_apply proof_of_cmc_write_word_partial_solve_wit_8_pure_split_goal_4.
Qed.

