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
From SimpleC.EE.QCP_demos_human Require Import cmc_emit_core_migration_goal.
From SimpleC.EE.QCP_demos_human Require Import cmc_emit_core_migration_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.cmc_emit_core_migration_lib.
Local Open Scope sac.

Lemma proof_of_cm_emit_raw_entail_wit_1 : cm_emit_raw_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_emitter_rep.
  Intros ops imms.
  prop_apply_p (store_int_range (&(out # "cm_output" ->ₛ "code_capacity")) capacity).
  Intros_p Hrange.
  Exists imms ops.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; int_auto.
Qed.

Lemma proof_of_cm_emit_raw_return_wit_1_split_goal_spatial : cm_emit_raw_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_emitter_rep.
  Exists ops imms.
  rewrite !Zlength_app, !Zlength_cons, !Zlength_nil.
  cbn.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures; dump_pre_spatial; lia.
Qed.

Lemma proof_of_cm_emit_raw_return_wit_1 : cm_emit_raw_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_raw_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_entail_wit_1_split_goal_1 : cm_emit_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_emitter_plan_rep.
  Intros_p Hplan.
  dump_pre_spatial.
  rewrite Zlength_cons in Hplan.
  unfold cm_rep_ops.
  rewrite Zlength_correct, length_map, <- Zlength_correct.
  pose proof (Zlength_nonneg tail).
  lia.
Qed.

Lemma proof_of_cm_emit_entail_wit_1_split_goal_2 : cm_emit_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_emitter_plan_rep.
  Intros_p Hplan.
  dump_pre_spatial.
  rewrite Zlength_cons in Hplan.
  lia.
Qed.

Lemma proof_of_cm_emit_entail_wit_1_split_goal_spatial : cm_emit_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cm_emit_entail_wit_1 : cm_emit_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_entail_wit_1_split_goal_spatial.
  - Goal_apply proof_of_cm_emit_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_cm_emit_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_cm_emit_return_wit_1_split_goal_spatial : cm_emit_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_emitter_plan_rep, cm_rep_ops, cm_rep_imms.
  rewrite !map_app.
  cbn [map tvm_inst_op tvm_inst_imm].
  subst op_pre.
  split_pure_spatial.
  - cancel (cm_emitter_rep emitter_pre out capacity
      (map (fun i => tvm_opcode_code (tvm_inst_op i)) done ++ (tvm_opcode_code opcode :: nil))
      (map tvm_inst_imm done ++ (immediate_pre :: nil))).
  - split_pures.
    dump_pre_spatial.
    rewrite Zlength_app_cons.
    lia.
Qed.

Lemma proof_of_cm_emit_return_wit_1 : cm_emit_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_normalize_entail_wit_1_split_goal_1 : cm_emit_normalize_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  assert (Hchar : model_ty = CMCharTy).
  { apply (proj1 (cm_type_encode_char_iff__typed_branches model_ty PreH3)). lia. }
  exact Hchar.
Qed.

Lemma proof_of_cm_emit_normalize_entail_wit_1_split_goal_spatial : cm_emit_normalize_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hchar : model_ty = CMCharTy).
  { apply (proj1 (cm_type_encode_char_iff__typed_branches model_ty PreH3)). lia. }
  subst model_ty. cbn [cm_char_normalize_code app].
  all: match goal with |- ?P |-- ?P => cancel P end.
Qed.

Lemma proof_of_cm_emit_normalize_entail_wit_1 : cm_emit_normalize_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_normalize_entail_wit_1_split_goal_spatial.
  - Goal_apply proof_of_cm_emit_normalize_entail_wit_1_split_goal_1.
Qed. 

Lemma proof_of_cm_emit_normalize_return_wit_1_split_goal_spatial : cm_emit_normalize_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst model_ty.
  unfold cm_char_normalize_code.
  repeat rewrite <- app_assoc.
  cbn [app].
  match goal with |- ?P |-- ?P => cancel P end.
Qed.

Lemma proof_of_cm_emit_normalize_return_wit_1 : cm_emit_normalize_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_normalize_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_normalize_return_wit_2_split_goal_spatial : cm_emit_normalize_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct model_ty;
    try solve [exfalso; apply PreH1; rewrite PreH2; reflexivity];
    cbn [cm_char_normalize_code app]; rewrite app_nil_r;
    match goal with |- ?P |-- ?P => cancel P end.
Qed.

Lemma proof_of_cm_emit_normalize_return_wit_2 : cm_emit_normalize_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_normalize_return_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_normalize_partial_solve_wit_1_pure_split_goal_1 : cm_emit_normalize_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_cm_emit_normalize_partial_solve_wit_1_pure : cm_emit_normalize_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_normalize_partial_solve_wit_1_pure_split_goal_1.
Qed.

Lemma proof_of_cm_emit_normalize_partial_solve_wit_2_pure_split_goal_1 : cm_emit_normalize_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_cm_emit_normalize_partial_solve_wit_2_pure : cm_emit_normalize_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_normalize_partial_solve_wit_2_pure_split_goal_1.
Qed.

Lemma proof_of_cm_emit_normalize_partial_solve_wit_3_pure_split_goal_1 : cm_emit_normalize_partial_solve_wit_3_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_cm_emit_normalize_partial_solve_wit_3_pure : cm_emit_normalize_partial_solve_wit_3_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_normalize_partial_solve_wit_3_pure_split_goal_1.
Qed.

Lemma proof_of_cm_emit_normalize_partial_solve_wit_4_pure_split_goal_1 : cm_emit_normalize_partial_solve_wit_4_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_cm_emit_normalize_partial_solve_wit_4_pure : cm_emit_normalize_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_normalize_partial_solve_wit_4_pure_split_goal_1.
Qed.

Lemma proof_of_cm_emit_normalize_partial_solve_wit_5_pure_split_goal_1 : cm_emit_normalize_partial_solve_wit_5_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_cm_emit_normalize_partial_solve_wit_5_pure : cm_emit_normalize_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_normalize_partial_solve_wit_5_pure_split_goal_1.
Qed.

Lemma proof_of_cm_emit_normalize_partial_solve_wit_6_pure_split_goal_1 : cm_emit_normalize_partial_solve_wit_6_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_cm_emit_normalize_partial_solve_wit_6_pure : cm_emit_normalize_partial_solve_wit_6_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_normalize_partial_solve_wit_6_pure_split_goal_1.
Qed.

Lemma proof_of_cm_emit_load_entail_wit_1_split_goal_1 : cm_emit_load_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  assert (Hchar : model_ty = CMCharTy).
  { apply (proj1 (cm_type_encode_char_iff__typed_branches model_ty PreH3)). lia. }
  exact Hchar.
Qed.

Lemma proof_of_cm_emit_load_entail_wit_1_split_goal_spatial : cm_emit_load_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cm_emit_load_entail_wit_1 : cm_emit_load_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_load_entail_wit_1_split_goal_spatial.
  - Goal_apply proof_of_cm_emit_load_entail_wit_1_split_goal_1.
Qed. 

Lemma proof_of_cm_emit_load_entail_wit_2_split_goal_1 : cm_emit_load_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  assert (Hnon : model_ty <> CMCharTy).
  { intros Hchar. subst model_ty. cbv [cm_type_encode cm_type_depth cm_type_base_code] in PreH2. lia. }
  exact Hnon.
Qed.

Lemma proof_of_cm_emit_load_entail_wit_2_split_goal_spatial : cm_emit_load_entail_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cm_emit_load_entail_wit_2 : cm_emit_load_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_load_entail_wit_2_split_goal_spatial.
  - Goal_apply proof_of_cm_emit_load_entail_wit_2_split_goal_1.
Qed. 

Lemma proof_of_cm_emit_load_return_wit_1_split_goal_spatial : cm_emit_load_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst model_ty.
  unfold cm_load_code; cbn beta iota.
  match goal with |- ?P |-- ?P => cancel P end.
Qed.

Lemma proof_of_cm_emit_load_return_wit_1 : cm_emit_load_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_load_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_load_return_wit_2_split_goal_spatial : cm_emit_load_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct model_ty; try contradiction; unfold cm_load_code; cbn beta iota;
    match goal with |- ?P |-- ?P => cancel P end.
Qed.

Lemma proof_of_cm_emit_load_return_wit_2 : cm_emit_load_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_load_return_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_load_partial_solve_wit_1_pure_split_goal_1 : cm_emit_load_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_cm_emit_load_partial_solve_wit_1_pure : cm_emit_load_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_load_partial_solve_wit_1_pure_split_goal_1.
Qed.

Lemma proof_of_cm_emit_load_partial_solve_wit_2_pure_split_goal_1 : cm_emit_load_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_cm_emit_load_partial_solve_wit_2_pure : cm_emit_load_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_load_partial_solve_wit_2_pure_split_goal_1.
Qed.

Lemma proof_of_cm_emit_store_entail_wit_1_split_goal_1 : cm_emit_store_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  assert (Hchar : model_ty = CMCharTy).
  { apply (proj1 (cm_type_encode_char_iff__typed_branches model_ty PreH3)). lia. }
  exact Hchar.
Qed.

Lemma proof_of_cm_emit_store_entail_wit_1_split_goal_spatial : cm_emit_store_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cm_emit_store_entail_wit_1 : cm_emit_store_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_store_entail_wit_1_split_goal_spatial.
  - Goal_apply proof_of_cm_emit_store_entail_wit_1_split_goal_1.
Qed. 

Lemma proof_of_cm_emit_store_entail_wit_2_split_goal_1 : cm_emit_store_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  assert (Hnon : model_ty <> CMCharTy).
  { intros Hchar. subst model_ty. cbv [cm_type_encode cm_type_depth cm_type_base_code] in PreH2. lia. }
  exact Hnon.
Qed.

Lemma proof_of_cm_emit_store_entail_wit_2_split_goal_spatial : cm_emit_store_entail_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cm_emit_store_entail_wit_2 : cm_emit_store_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_store_entail_wit_2_split_goal_spatial.
  - Goal_apply proof_of_cm_emit_store_entail_wit_2_split_goal_1.
Qed. 

Lemma proof_of_cm_emit_store_return_wit_1_split_goal_spatial : cm_emit_store_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst model_ty.
  unfold cm_store_code; cbn beta iota.
  match goal with |- ?P |-- ?P => cancel P end.
Qed.

Lemma proof_of_cm_emit_store_return_wit_1 : cm_emit_store_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_store_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_store_return_wit_2_split_goal_spatial : cm_emit_store_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct model_ty; try contradiction; unfold cm_store_code; cbn beta iota;
    match goal with |- ?P |-- ?P => cancel P end.
Qed.

Lemma proof_of_cm_emit_store_return_wit_2 : cm_emit_store_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_store_return_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_store_partial_solve_wit_1_pure_split_goal_1 : cm_emit_store_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_cm_emit_store_partial_solve_wit_1_pure : cm_emit_store_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_store_partial_solve_wit_1_pure_split_goal_1.
Qed.

Lemma proof_of_cm_emit_store_partial_solve_wit_2_pure_split_goal_1 : cm_emit_store_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_cm_emit_store_partial_solve_wit_2_pure : cm_emit_store_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_store_partial_solve_wit_2_pure_split_goal_1.
Qed.

Lemma proof_of_cm_emit_fp_address_entail_wit_1_split_goal_spatial : cm_emit_fp_address_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cm_emit_fp_address_entail_wit_1 : cm_emit_fp_address_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_fp_address_entail_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_fp_address_return_wit_1_split_goal_spatial : cm_emit_fp_address_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold cm_fp_relative_address_code.
  repeat rewrite <- app_assoc.
  cbn [app].
  match goal with |- ?P |-- ?P => cancel P end.
Qed.

Lemma proof_of_cm_emit_fp_address_return_wit_1 : cm_emit_fp_address_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_fp_address_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_fp_address_partial_solve_wit_1_pure_split_goal_1 : cm_emit_fp_address_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cm_emit_fp_address_partial_solve_wit_1_pure : cm_emit_fp_address_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_fp_address_partial_solve_wit_1_pure_split_goal_1.
Qed.

Lemma proof_of_cm_emit_fp_address_partial_solve_wit_2_pure_split_goal_1 : cm_emit_fp_address_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cm_emit_fp_address_partial_solve_wit_2_pure : cm_emit_fp_address_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_fp_address_partial_solve_wit_2_pure_split_goal_1.
Qed.

Lemma proof_of_cm_emit_fp_address_partial_solve_wit_3_pure_split_goal_1 : cm_emit_fp_address_partial_solve_wit_3_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cm_emit_fp_address_partial_solve_wit_3_pure : cm_emit_fp_address_partial_solve_wit_3_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_fp_address_partial_solve_wit_3_pure_split_goal_1.
Qed.

Lemma proof_of_cm_emit_fp_address_partial_solve_wit_4_pure_split_goal_1 : cm_emit_fp_address_partial_solve_wit_4_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cm_emit_fp_address_partial_solve_wit_4_pure : cm_emit_fp_address_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_fp_address_partial_solve_wit_4_pure_split_goal_1.
Qed.

Lemma proof_of_cm_emit_temp_store_entail_wit_1 : cm_emit_temp_store_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hoffset : 8 + cm_rep_members_size (cm_function_params f) +
    cm_rep_members_size (cm_function_locals f) + 8*temp_pre =
    cm_temp_offset policy p fid temp_pre).
  { subst structs. eapply cm_temp_offset_matches__temp_context; eauto. }
  unfold cm_function_context_rep.
  Intros pp lp.
  Exists lp pp.
  split_pure_spatial.
  - sepcon_right_assoc. cancel.
  - split_pures; dump_pre_spatial; auto; lia.
Qed. 

Lemma proof_of_cm_emit_temp_store_entail_wit_2_split_goal_spatial : cm_emit_temp_store_entail_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hretval : retval = cm_temp_offset policy p fid temp_pre) by lia.
  rewrite Hretval. unfold cm_temp_store_code.
  rewrite <- app_assoc. cbn [app].
  cancel (cm_emitter_plan_rep emitter_pre out capacity done
    (cm_fp_relative_address_code (cm_temp_offset policy p fid temp_pre) ++
      TVMInst TVMStoreOp 0 :: tail)).
  unfold cm_function_context_rep.
  Exists pp lp.
  split_pure_spatial.
  - sepcon_right_assoc. cancel.
  - dump_pre_spatial. auto.
Qed.

Lemma proof_of_cm_emit_temp_store_entail_wit_2 : cm_emit_temp_store_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_temp_store_entail_wit_2_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_temp_store_return_wit_1_split_goal_spatial : cm_emit_temp_store_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst offset.
  unfold cm_temp_store_code.
  rewrite app_assoc.
  cancel.
Qed.

Lemma proof_of_cm_emit_temp_store_return_wit_1 : cm_emit_temp_store_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_temp_store_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_temp_store_partial_solve_wit_3_pure_split_goal_1 : cm_emit_temp_store_partial_solve_wit_3_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_cm_emit_temp_store_partial_solve_wit_3_pure : cm_emit_temp_store_partial_solve_wit_3_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_temp_store_partial_solve_wit_3_pure_split_goal_1.
Qed.

Lemma proof_of_cm_emit_temp_load_entail_wit_1 : cm_emit_temp_load_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hoffset : 8 + cm_rep_members_size (cm_function_params f) +
    cm_rep_members_size (cm_function_locals f) + 8*temp_pre =
    cm_temp_offset policy p fid temp_pre).
  { subst structs. eapply cm_temp_offset_matches__temp_context; eauto. }
  unfold cm_function_context_rep.
  Intros pp lp.
  Exists lp pp.
  split_pure_spatial.
  - sepcon_right_assoc. cancel.
  - split_pures; dump_pre_spatial; auto; lia.
Qed. 

Lemma proof_of_cm_emit_temp_load_entail_wit_2_split_goal_spatial : cm_emit_temp_load_entail_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hretval : retval = cm_temp_offset policy p fid temp_pre) by lia.
  rewrite Hretval. unfold cm_temp_load_code.
  rewrite <- app_assoc. cbn [app].
  cancel (cm_emitter_plan_rep emitter_pre out capacity done
    (cm_fp_relative_address_code (cm_temp_offset policy p fid temp_pre) ++
      TVMInst TVMLoadOp 0 :: tail)).
  unfold cm_function_context_rep.
  Exists pp lp.
  split_pure_spatial.
  - sepcon_right_assoc. cancel.
  - dump_pre_spatial. auto.
Qed.

Lemma proof_of_cm_emit_temp_load_entail_wit_2 : cm_emit_temp_load_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_temp_load_entail_wit_2_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_temp_load_return_wit_1_split_goal_spatial : cm_emit_temp_load_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst offset.
  unfold cm_temp_load_code.
  rewrite app_assoc.
  cancel.
Qed.

Lemma proof_of_cm_emit_temp_load_return_wit_1 : cm_emit_temp_load_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_temp_load_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_temp_load_partial_solve_wit_3_pure_split_goal_1 : cm_emit_temp_load_partial_solve_wit_3_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_cm_emit_temp_load_partial_solve_wit_3_pure : cm_emit_temp_load_partial_solve_wit_3_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_temp_load_partial_solve_wit_3_pure_split_goal_1.
Qed.

Lemma proof_of_cmc_binary_opcode_return_wit_1_split_goal_1 : cmc_binary_opcode_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_cmc_binary_opcode_return_wit_1 : cmc_binary_opcode_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_binary_opcode_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_cmc_binary_opcode_return_wit_2_split_goal_1 : cmc_binary_opcode_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_cmc_binary_opcode_return_wit_2 : cmc_binary_opcode_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_binary_opcode_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_cmc_binary_opcode_return_wit_3_split_goal_1 : cmc_binary_opcode_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_cmc_binary_opcode_return_wit_3 : cmc_binary_opcode_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_binary_opcode_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_cmc_binary_opcode_return_wit_4_split_goal_1 : cmc_binary_opcode_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_cmc_binary_opcode_return_wit_4 : cmc_binary_opcode_return_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_binary_opcode_return_wit_4_split_goal_1.
Qed.

Lemma proof_of_cmc_binary_opcode_return_wit_5_split_goal_1 : cmc_binary_opcode_return_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_cmc_binary_opcode_return_wit_5 : cmc_binary_opcode_return_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_binary_opcode_return_wit_5_split_goal_1.
Qed.

Lemma proof_of_cmc_binary_opcode_return_wit_6_split_goal_1 : cmc_binary_opcode_return_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_cmc_binary_opcode_return_wit_6 : cmc_binary_opcode_return_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_binary_opcode_return_wit_6_split_goal_1.
Qed.

Lemma proof_of_cmc_binary_opcode_return_wit_7_split_goal_1 : cmc_binary_opcode_return_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_cmc_binary_opcode_return_wit_7 : cmc_binary_opcode_return_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_binary_opcode_return_wit_7_split_goal_1.
Qed.

Lemma proof_of_cmc_binary_opcode_return_wit_8_split_goal_1 : cmc_binary_opcode_return_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_cmc_binary_opcode_return_wit_8 : cmc_binary_opcode_return_wit_8.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_binary_opcode_return_wit_8_split_goal_1.
Qed.

Lemma proof_of_cmc_binary_opcode_return_wit_9_split_goal_1 : cmc_binary_opcode_return_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_cmc_binary_opcode_return_wit_9 : cmc_binary_opcode_return_wit_9.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_binary_opcode_return_wit_9_split_goal_1.
Qed.

Lemma proof_of_cmc_binary_opcode_return_wit_10_split_goal_1 : cmc_binary_opcode_return_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_cmc_binary_opcode_return_wit_10 : cmc_binary_opcode_return_wit_10.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_binary_opcode_return_wit_10_split_goal_1.
Qed.

Lemma proof_of_cmc_binary_opcode_return_wit_11_split_goal_1 : cmc_binary_opcode_return_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold cm_binary_opcode.
  repeat match goal with
  | H : ?x <> ?y |- context [Z.eqb ?x ?y] =>
      rewrite (proj2 (Z.eqb_neq x y) H)
  end.
  reflexivity.
Qed.

Lemma proof_of_cmc_binary_opcode_return_wit_11 : cmc_binary_opcode_return_wit_11.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cmc_binary_opcode_return_wit_11_split_goal_1.
Qed.

