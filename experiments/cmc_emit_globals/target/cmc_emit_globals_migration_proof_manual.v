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
From SimpleC.EE.QCP_demos_human Require Import cmc_emit_globals_migration_goal.
From SimpleC.EE.QCP_demos_human Require Import cmc_emit_globals_migration_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.cmc_emit_globals_migration_lib.
Local Open Scope sac.

Lemma proof_of_cmc_emit_globals_entail_wit_1 : cmc_emit_globals_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct globals as [|head tail].
  - cbn [cm_global_list_rep]. Intros_p Hnull. contradiction.
  - cbn [cm_global_list_rep]. Intros nextp.
    pose proof PreH2 as Hsafe. cbn [cm_rep_globals_safe cm_rep_globals_size] in Hsafe.
    destruct Hsafe as [Hhead [Htail [Htotal Hrest]]].
    pose proof PreH3 as Hwf. cbn [cm_data_globals_wf] in Hwf.
    destruct Hwf as [Hheadwf Htailwf].
    cbn [cm_rep_globals_size] in PreH5.
    Exists nextp head tail.
    split_pure_spatial.
    + repeat progress cancel.
    + split_pures; dump_pre_spatial; auto; lia.
Qed.

Lemma proof_of_cmc_emit_globals_entail_wit_2_1 : cmc_emit_globals_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (cm_initialized_char_facts__initialized_emission structs head PreH9 PreH16 PreH1) as [Hsize Hbytes].
  change (retval = cm_rep_global_size head) in PreH2.
  assert (Hret : retval = 1) by lia.
  assert (Hcast : signed_last_nbits retval 32 = 1) by (rewrite Hret; reflexivity).
  Exists head tail_2.
  rewrite Hcast, Hbytes.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; auto; lia.
Qed. 

Lemma proof_of_cmc_emit_globals_entail_wit_2_2 : cmc_emit_globals_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (cm_initialized_word_facts__initialized_emission structs head PreH9 PreH16 PreH1) as [Hsize Hbytes].
  change (retval = cm_rep_global_size head) in PreH2.
  assert (Hret : retval = 8) by lia.
  assert (Hcast : signed_last_nbits retval 32 = 8) by (rewrite Hret; reflexivity).
  Exists head tail_2.
  rewrite Hcast, Hbytes.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; auto; lia.
Qed. 

Lemma proof_of_cmc_emit_globals_entail_wit_2_3 : cmc_emit_globals_entail_wit_2_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hsize : retval = cm_rep_global_size head) by exact PreH1.
  assert (Hcast : signed_last_nbits retval 32 = cm_rep_global_size head).
  { rewrite signed_last_nbits_eq; [exact Hsize | lia |].
    change (-2147483648 <= retval < 2147483648). lia. }
  assert (Hinit : cm_global_has_init head = false).
  { unfold cm_rep_bool in PreH15.
    destruct (cm_global_has_init head); congruence. }
  pose proof (cm_rep_global_size_matches structs head PreH8) as Hmodel.
  assert (Hbytes : cm_global_bytes structs head = zeros (cm_rep_global_size head)).
  { rewrite cm_global_bytes_zero; [rewrite Hmodel; reflexivity | lia | exact Hinit]. }
  Exists head tail_2.
  rewrite Hcast, Hbytes.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_cmc_emit_globals_return_wit_1_split_goal_1 : cmc_emit_globals_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial. subst globals size. cbn [cm_rep_globals_size]. lia.
Qed.

Lemma proof_of_cmc_emit_globals_return_wit_1_split_goal_spatial : cmc_emit_globals_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst globals size. cbn [cm_rep_globals_size cm_globals_bytes cm_global_list_rep].
  rewrite Z.add_assoc, app_assoc.
  Exists nextp.
  split_pure_spatial.
  - repeat progress cancel.
  - dump_pre_spatial. exact PreH12.
Qed.

Lemma proof_of_cmc_emit_globals_return_wit_1 : cmc_emit_globals_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_globals_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_cmc_emit_globals_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_cmc_emit_globals_return_wit_2_split_goal_1 : cmc_emit_globals_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct globals as [|head tail].
  - cbn [cm_rep_globals_size]. dump_pre_spatial. lia.
  - cbn [cm_global_list_rep]. Intros nextp. contradiction.
Qed.

Lemma proof_of_cmc_emit_globals_return_wit_2_split_goal_spatial : cmc_emit_globals_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct globals as [|head tail].
  - cbn [cm_rep_globals_size cm_globals_bytes].
    rewrite Z.add_0_r, app_nil_r. repeat progress cancel.
  - cbn [cm_global_list_rep]. Intros nextp. contradiction.
Qed.

Lemma proof_of_cmc_emit_globals_return_wit_2 : cmc_emit_globals_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_globals_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_cmc_emit_globals_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_cmc_emit_globals_partial_solve_wit_2_pure_split_goal_1 : cmc_emit_globals_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (cm_initialized_char_facts__initialized_emission structs head PreH25 PreH32 PreH17) as [Hsize Hbytes].
  rewrite Hsize in PreH31.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_cmc_emit_globals_partial_solve_wit_2_pure : cmc_emit_globals_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_globals_partial_solve_wit_2_pure_split_goal_1.
Qed. 

Lemma proof_of_cmc_emit_globals_partial_solve_wit_3_pure_split_goal_1 : cmc_emit_globals_partial_solve_wit_3_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (cm_initialized_word_facts__initialized_emission structs head PreH25 PreH32 PreH17) as [Hsize Hbytes].
  rewrite Hsize in PreH31.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_cmc_emit_globals_partial_solve_wit_3_pure : cmc_emit_globals_partial_solve_wit_3_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_emit_globals_partial_solve_wit_3_pure_split_goal_1.
Qed. 

Lemma proof_of_cmc_emit_globals_partial_solve_wit_4_pure_split_goal_1 : cmc_emit_globals_partial_solve_wit_4_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hsize : retval = cm_rep_global_size head) by exact PreH17.
  dump_pre_spatial.
  rewrite signed_last_nbits_eq; lia.
Qed.

Lemma proof_of_cmc_emit_globals_partial_solve_wit_4_pure_split_goal_2 : cmc_emit_globals_partial_solve_wit_4_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hsize : retval = cm_rep_global_size head) by exact PreH17.
  dump_pre_spatial.
  rewrite signed_last_nbits_eq; lia.
Qed.

Lemma proof_of_cmc_emit_globals_partial_solve_wit_4_pure : cmc_emit_globals_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cmc_emit_globals_partial_solve_wit_4_pure_split_goal_1.
  - Goal_apply proof_of_cmc_emit_globals_partial_solve_wit_4_pure_split_goal_2.
Qed.

