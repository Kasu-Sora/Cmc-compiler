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
From SimpleC.EE.QCP_demos_human Require Import cmc_emit_ast_migration_goal.
From SimpleC.EE.QCP_demos_human Require Import cmc_emit_ast_migration_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.cmc_emit_ast_migration_lib.
Local Open Scope sac.

Lemma proof_of_cm_emit_binding_address_entail_wit_1 : cm_emit_binding_address_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_program_context_rep, cm_function_context_rep.
  Intros sp gp tp zp zl.
  assert (Hslot : 0 <= slot_pre).
  { unfold cm_binding_valid in PreH5. destruct PreH5 as [Hscope | [Hscope | Hscope]]; lia. }
  Exists zl zp tp gp sp.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_cm_emit_binding_address_return_wit_1_split_goal_spatial : cm_emit_binding_address_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hglobals : forall i, 0 <= i < Zlength (cm_program_globals p) ->
    cm_global_wf (cm_program_structs p) (cm_global_at i (cm_program_globals p))).
  { exact (proj1 (proj2 (proj1 PreH14))). }
  assert (Haddress : retval = cm_global_address p slot_pre).
  { rewrite PreH7. unfold cm_rep_global_address, cm_global_address.
    rewrite (cm_rep_globals_prefix_matches _ _ _ Hglobals). reflexivity. }
  unfold cm_binding_address_code. rewrite PreH10. cbn [Z.eqb].
  unfold cm_push_code. rewrite Haddress.
  unfold cm_program_context_rep, cm_function_context_rep.
  Exists sp gp tp zp zl.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_cm_emit_binding_address_return_wit_1 : cm_emit_binding_address_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_binding_address_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_binding_address_return_wit_2_split_goal_spatial : cm_emit_binding_address_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Haddress : retval = cm_local_offset policy p fid slot_pre).
  { rewrite PreH8.
    rewrite (cm_slots_size_matches__temp_context _ _ PreH19).
    rewrite (cm_rep_member_prefix_matches _ _ _ PreH20).
    unfold cm_local_offset. rewrite PreH15, PreH16. reflexivity. }
  unfold cm_binding_address_code. rewrite PreH9. cbn [Z.eqb Pos.eqb].
  rewrite Haddress.
  unfold cm_program_context_rep, cm_function_context_rep.
  Exists sp gp tp zp zl.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_cm_emit_binding_address_return_wit_2 : cm_emit_binding_address_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_binding_address_return_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_binding_address_return_wit_3_split_goal_spatial : cm_emit_binding_address_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Haddress : retval = cm_param_offset policy p fid slot_pre).
  { rewrite PreH7.
    rewrite (cm_rep_member_prefix_matches _ _ _ PreH18).
    unfold cm_param_offset. rewrite PreH14, PreH15. reflexivity. }
  assert (Hscope0 : Z.eqb scope_pre 0 = false) by (apply Z.eqb_neq; exact PreH9).
  assert (Hscope1 : Z.eqb scope_pre 1 = false) by (apply Z.eqb_neq; exact PreH8).
  unfold cm_binding_address_code. rewrite Hscope0, Hscope1, Haddress.
  unfold cm_program_context_rep, cm_function_context_rep.
  Exists sp gp tp zp zl.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_cm_emit_binding_address_return_wit_3 : cm_emit_binding_address_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_binding_address_return_wit_3_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_binding_address_partial_solve_wit_2_pure_split_goal_1 : cm_emit_binding_address_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  all: dump_pre_spatial.
  all: reflexivity.
Qed.

Lemma proof_of_cm_emit_binding_address_partial_solve_wit_2_pure_split_goal_2 : cm_emit_binding_address_partial_solve_wit_2_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  all: dump_pre_spatial.
  all: discriminate.
Qed.

Lemma proof_of_cm_emit_binding_address_partial_solve_wit_2_pure_split_goal_3 : cm_emit_binding_address_partial_solve_wit_2_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  subst scope_pre.
  change (Zlength done + 1 <= capacity) in PreH30.
  exact PreH30.
Qed.

Lemma proof_of_cm_emit_binding_address_partial_solve_wit_2_pure : cm_emit_binding_address_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binding_address_partial_solve_wit_2_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_binding_address_partial_solve_wit_2_pure_split_goal_2.
  - Goal_apply proof_of_cm_emit_binding_address_partial_solve_wit_2_pure_split_goal_3.
Qed.

Lemma proof_of_cm_emit_binding_address_partial_solve_wit_4_pure_split_goal_1 : cm_emit_binding_address_partial_solve_wit_4_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  subst scope_pre.
  change (Zlength done + 4 <= capacity) in PreH30.
  change (Zlength done + 4 <= capacity).
  exact PreH30.
Qed.

Lemma proof_of_cm_emit_binding_address_partial_solve_wit_4_pure_split_goal_2 : cm_emit_binding_address_partial_solve_wit_4_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  subst scope_pre.
  change (Zlength done + 4 <= capacity) in PreH30.
  change (Zlength done + 4 <= capacity).
  exact PreH30.
Qed.

Lemma proof_of_cm_emit_binding_address_partial_solve_wit_4_pure : cm_emit_binding_address_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binding_address_partial_solve_wit_4_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_binding_address_partial_solve_wit_4_pure_split_goal_2.
Qed.

Lemma proof_of_cm_emit_binding_address_partial_solve_wit_6_pure_split_goal_1 : cm_emit_binding_address_partial_solve_wit_6_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  assert (Hscope0 : Z.eqb scope_pre 0 = false) by (apply Z.eqb_neq; assumption).
  assert (Hscope1 : Z.eqb scope_pre 1 = false) by (apply Z.eqb_neq; assumption).
  unfold cm_binding_address_code in PreH29.
  rewrite Hscope0, Hscope1 in PreH29.
  change (Zlength done + 4 <= capacity) in PreH29.
  change (Zlength done + 4 <= capacity).
  exact PreH29.
Qed.

Lemma proof_of_cm_emit_binding_address_partial_solve_wit_6_pure_split_goal_2 : cm_emit_binding_address_partial_solve_wit_6_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  dump_pre_spatial.
  assert (Hscope0 : Z.eqb scope_pre 0 = false) by (apply Z.eqb_neq; assumption).
  assert (Hscope1 : Z.eqb scope_pre 1 = false) by (apply Z.eqb_neq; assumption).
  unfold cm_binding_address_code in PreH29.
  rewrite Hscope0, Hscope1 in PreH29.
  change (Zlength done + 4 <= capacity) in PreH29.
  change (Zlength done + 4 <= capacity).
  exact PreH29.
Qed.

Lemma proof_of_cm_emit_binding_address_partial_solve_wit_6_pure : cm_emit_binding_address_partial_solve_wit_6_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binding_address_partial_solve_wit_6_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_binding_address_partial_solve_wit_6_pure_split_goal_2.
Qed.

Lemma proof_of_cm_emit_binding_address_plan_entail_wit_1_split_goal_1 : cm_emit_binding_address_plan_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_resolved_emitter_plan_rep.
  Intros_p Hcapacity.
  dump_pre_spatial.
  rewrite Zlength_app in Hcapacity.
  pose proof (Zlength_nonneg tail). lia.
Qed.

Lemma proof_of_cm_emit_binding_address_plan_entail_wit_1_split_goal_2 : cm_emit_binding_address_plan_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_resolved_emitter_plan_rep.
  Intros_p Hcapacity.
  dump_pre_spatial.
  rewrite Zlength_app in Hcapacity |- *. lia.
Qed.

Lemma proof_of_cm_emit_binding_address_plan_entail_wit_1_split_goal_spatial : cm_emit_binding_address_plan_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_resolved_emitter_plan_rep.
  Intros_p Hcapacity.
  repeat progress cancel.
Qed.

Lemma proof_of_cm_emit_binding_address_plan_entail_wit_1 : cm_emit_binding_address_plan_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binding_address_plan_entail_wit_1_split_goal_spatial.
  - Goal_apply proof_of_cm_emit_binding_address_plan_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_cm_emit_binding_address_plan_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_cm_emit_binding_address_plan_return_wit_1_split_goal_spatial : cm_emit_binding_address_plan_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_resolved_emitter_plan_rep.
  split_pure_spatial.
  - repeat progress cancel.
  - dump_pre_spatial. exact PreH11.
Qed.

Lemma proof_of_cm_emit_binding_address_plan_return_wit_1 : cm_emit_binding_address_plan_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_binding_address_plan_return_wit_1_split_goal_spatial.
Qed.

