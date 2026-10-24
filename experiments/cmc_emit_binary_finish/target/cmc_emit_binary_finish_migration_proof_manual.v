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
From SimpleC.EE.QCP_demos_human Require Import cmc_emit_binary_finish_migration_goal.
From SimpleC.EE.QCP_demos_human Require Import cmc_emit_binary_finish_migration_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.cmc_emit_binary_finish_migration_lib.
Local Open Scope sac.

Lemma proof_of_cm_pointer_scale_value_return_wit_1_split_goal_1 : cm_pointer_scale_value_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cm_pointer_scale_value_return_wit_1 : cm_pointer_scale_value_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_pointer_scale_value_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_cm_pointer_scale_value_partial_solve_wit_2_pure_split_goal_1 : cm_pointer_scale_value_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct (cm_expr_type e) eqn:Htype; simpl in PreH8; try contradiction.
  cbn [cm_type_code_wf] in PreH5.
  pose proof (cm_type_encoding_bounds__expression_add_safety _ PreH5) as Hb.
  unfold cm_type_encode. cbn [cm_type_depth cm_type_base_code] in *. lia.
Qed.

Lemma proof_of_cm_pointer_scale_value_partial_solve_wit_2_pure : cm_pointer_scale_value_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_pointer_scale_value_partial_solve_wit_2_pure_split_goal_1.
Qed.

Lemma proof_of_cm_pointer_scale_value_partial_solve_wit_3_pure_split_goal_1 : cm_pointer_scale_value_partial_solve_wit_3_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct (cm_expr_type e) eqn:Htype; simpl in PreH11; try contradiction.
  unfold cm_type_encode in *.
  cbn [cm_pointee cm_type_depth cm_type_base_code] in *. lia.
Qed.

Lemma proof_of_cm_pointer_scale_value_partial_solve_wit_3_pure_split_goal_2 : cm_pointer_scale_value_partial_solve_wit_3_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct (cm_expr_type e) eqn:Htype; simpl in PreH11; try contradiction.
  cbn [cm_pointee cm_type_code_wf] in *. exact PreH8.
Qed.

Lemma proof_of_cm_pointer_scale_value_partial_solve_wit_3_pure_split_goal_3 : cm_pointer_scale_value_partial_solve_wit_3_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  destruct (cm_expr_type e) eqn:Htype; simpl in PreH11; try contradiction.
  cbn [cm_pointee cm_type_refs] in *. exact PreH9.
Qed.

Lemma proof_of_cm_pointer_scale_value_partial_solve_wit_3_pure : cm_pointer_scale_value_partial_solve_wit_3_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_pointer_scale_value_partial_solve_wit_3_pure_split_goal_1.
  - Goal_apply proof_of_cm_pointer_scale_value_partial_solve_wit_3_pure_split_goal_2.
  - Goal_apply proof_of_cm_pointer_scale_value_partial_solve_wit_3_pure_split_goal_3.
Qed.

Lemma proof_of_cm_emit_binary_generic_fragment_return_wit_1_split_goal_spatial : cm_emit_binary_generic_fragment_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  repeat rewrite <- app_assoc.
  cbn [app].
  cancel (cm_function_context_rep fn_pre f body next).
  cancel (cm_resolved_emitter_plan_rep policy p emitter_pre out capacity
    (done ++ cm_temp_load_code policy p fid temp_pre ++
      TVMInst TVMSwapOp 0 :: TVMInst (cm_binary_opcode op_pre) 0 :: nil) tail).
Qed.

Lemma proof_of_cm_emit_binary_generic_fragment_return_wit_1 : cm_emit_binary_generic_fragment_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_binary_generic_fragment_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_binary_generic_fragment_partial_solve_wit_3_pure_split_goal_1 : cm_emit_binary_generic_fragment_partial_solve_wit_3_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cm_emit_binary_generic_fragment_partial_solve_wit_3_pure_split_goal_2 : cm_emit_binary_generic_fragment_partial_solve_wit_3_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  discriminate.
Qed.

Lemma proof_of_cm_emit_binary_generic_fragment_partial_solve_wit_3_pure : cm_emit_binary_generic_fragment_partial_solve_wit_3_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_generic_fragment_partial_solve_wit_3_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_generic_fragment_partial_solve_wit_3_pure_split_goal_2.
Qed.

Lemma proof_of_cm_emit_binary_generic_fragment_which_implies_wit_1_split_goal_spatial : cm_emit_binary_generic_fragment_which_implies_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_cm_emit_binary_generic_fragment_which_implies_wit_1 : cm_emit_binary_generic_fragment_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_binary_generic_fragment_which_implies_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_return_wit_1_split_goal_spatial : cm_emit_binary_finish_plan_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hop : op_pre = 8) by lia.
  assert (Hright : cm_pointerb (cm_expr_type right_e) = true).
  { match goal with
    | Hwf : cm_type_code_wf (cm_expr_type right_e) |- _ =>
      pose proof (cm_pointer_encode__expression_add_safety (cm_expr_type right_e) Hwf) as Hencode
    end.
    destruct (cm_pointerb (cm_expr_type right_e)); congruence. }
  unfold cm_binary_finish_code.
  rewrite Hop.
  cbn [Z.eqb Pos.eqb andb].
  rewrite Hright.
  cbn [andb].
  repeat rewrite <- app_assoc.
  cbn [app].
  cancel (cm_program_context_rep program_pre p functions_ptr).
  cancel (cm_function_context_rep fn_pre f body next).
  cancel (cm_expr_rep left_pre left_e).
  cancel (cm_expr_rep right_pre right_e).
  match goal with |- ?P |-- ?P => cancel P end.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_return_wit_1 : cm_emit_binary_finish_plan_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_binary_finish_plan_return_wit_1_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_binary_finish_plan_return_wit_2_split_goal_spatial : cm_emit_binary_finish_plan_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hop : op_pre = 8) by lia.
  assert (Hleft : cm_pointerb (cm_expr_type left_e) = true).
  { match goal with
    | Hwf : cm_type_code_wf (cm_expr_type left_e) |- _ =>
      pose proof (cm_pointer_encode__expression_add_safety (cm_expr_type left_e) Hwf) as Hencode
    end.
    destruct (cm_pointerb (cm_expr_type left_e)); congruence. }
  assert (Hright : cm_pointerb (cm_expr_type right_e) = false).
  { match goal with
    | Hwf : cm_type_code_wf (cm_expr_type right_e) |- _ =>
      pose proof (cm_pointer_encode__expression_add_safety (cm_expr_type right_e) Hwf) as Hencode
    end.
    destruct (cm_pointerb (cm_expr_type right_e)); congruence. }
  unfold cm_binary_finish_code.
  rewrite Hop.
  cbn [Z.eqb Pos.eqb andb].
  rewrite Hleft, Hright.
  cbn [andb].
  repeat rewrite <- app_assoc.
  cbn [app].
  cancel (cm_program_context_rep program_pre p functions_ptr).
  cancel (cm_function_context_rep fn_pre f body next).
  cancel (cm_expr_rep left_pre left_e).
  cancel (cm_expr_rep right_pre right_e).
  match goal with |- ?P |-- ?P => cancel P end.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_return_wit_2 : cm_emit_binary_finish_plan_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_binary_finish_plan_return_wit_2_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_binary_finish_plan_return_wit_3_split_goal_spatial : cm_emit_binary_finish_plan_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hop : op_pre = 9) by lia.
  assert (Hleft : cm_pointerb (cm_expr_type left_e) = true).
  { match goal with
    | Hwf : cm_type_code_wf (cm_expr_type left_e) |- _ =>
      pose proof (cm_pointer_encode__expression_add_safety (cm_expr_type left_e) Hwf) as Hencode
    end.
    destruct (cm_pointerb (cm_expr_type left_e)); congruence. }
  assert (Hright : cm_pointerb (cm_expr_type right_e) = true).
  { match goal with
    | Hwf : cm_type_code_wf (cm_expr_type right_e) |- _ =>
      pose proof (cm_pointer_encode__expression_add_safety (cm_expr_type right_e) Hwf) as Hencode
    end.
    destruct (cm_pointerb (cm_expr_type right_e)); congruence. }
  unfold cm_binary_finish_code.
  rewrite Hop.
  cbn [Z.eqb Pos.eqb andb].
  rewrite Hleft, Hright.
  cbn [andb].
  repeat rewrite <- app_assoc.
  cbn [app].
  cancel (cm_program_context_rep program_pre p functions_ptr).
  cancel (cm_function_context_rep fn_pre f body next).
  cancel (cm_expr_rep left_pre left_e).
  cancel (cm_expr_rep right_pre right_e).
  match goal with |- ?P |-- ?P => cancel P end.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_return_wit_3 : cm_emit_binary_finish_plan_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_binary_finish_plan_return_wit_3_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_binary_finish_plan_return_wit_4_split_goal_spatial : cm_emit_binary_finish_plan_return_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hop : op_pre = 9) by lia.
  assert (Hleft : cm_pointerb (cm_expr_type left_e) = true).
  { match goal with
    | Hwf : cm_type_code_wf (cm_expr_type left_e) |- _ =>
      pose proof (cm_pointer_encode__expression_add_safety (cm_expr_type left_e) Hwf) as Hencode
    end.
    destruct (cm_pointerb (cm_expr_type left_e)); congruence. }
  assert (Hright : cm_pointerb (cm_expr_type right_e) = false).
  { match goal with
    | Hwf : cm_type_code_wf (cm_expr_type right_e) |- _ =>
      pose proof (cm_pointer_encode__expression_add_safety (cm_expr_type right_e) Hwf) as Hencode
    end.
    destruct (cm_pointerb (cm_expr_type right_e)); congruence. }
  unfold cm_binary_finish_code.
  rewrite Hop.
  cbn [Z.eqb Pos.eqb andb].
  rewrite Hleft, Hright.
  cbn [andb].
  repeat rewrite <- app_assoc.
  cbn [app].
  cancel (cm_program_context_rep program_pre p functions_ptr).
  cancel (cm_function_context_rep fn_pre f body next).
  cancel (cm_expr_rep left_pre left_e).
  cancel (cm_expr_rep right_pre right_e).
  match goal with |- ?P |-- ?P => cancel P end.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_return_wit_4 : cm_emit_binary_finish_plan_return_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_binary_finish_plan_return_wit_4_split_goal_spatial.
Qed. 

Lemma proof_of_cm_emit_binary_finish_plan_return_wit_5_split_goal_spatial : cm_emit_binary_finish_plan_return_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hleft : cm_pointerb (cm_expr_type left_e) = false).
  { pose proof (cm_pointer_encode__expression_add_safety (cm_expr_type left_e) PreH8) as Hencode.
    rewrite PreH12 in Hencode.
    destruct (cm_pointerb (cm_expr_type left_e)); congruence. }
  assert (Hright : cm_pointerb (cm_expr_type right_e) = false).
  { pose proof (cm_pointer_encode__expression_add_safety (cm_expr_type right_e) PreH9) as Hencode.
    rewrite PreH13 in Hencode.
    destruct (cm_pointerb (cm_expr_type right_e)); congruence. }
  assert (Hop : op_pre = 8) by lia.
  rewrite Hop.
  unfold cm_binary_finish_code.
  rewrite Hleft, Hright.
  cbn [Z.eqb Pos.eqb andb app].
  cancel.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_return_wit_5 : cm_emit_binary_finish_plan_return_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_binary_finish_plan_return_wit_5_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_return_wit_6_split_goal_spatial : cm_emit_binary_finish_plan_return_wit_6_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hleft : cm_pointerb (cm_expr_type left_e) = false).
  { pose proof (cm_pointer_encode__expression_add_safety (cm_expr_type left_e) PreH8) as Hencode.
    rewrite PreH12 in Hencode.
    destruct (cm_pointerb (cm_expr_type left_e)); congruence. }
  assert (Hop : op_pre = 9) by lia.
  rewrite Hop.
  unfold cm_binary_finish_code.
  rewrite Hleft.
  cbn [Z.eqb Pos.eqb andb app].
  cancel.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_return_wit_6 : cm_emit_binary_finish_plan_return_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_binary_finish_plan_return_wit_6_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_return_wit_7_split_goal_spatial : cm_emit_binary_finish_plan_return_wit_7_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hop8 : Z.eqb op_pre 8 = false) by (apply Z.eqb_neq; assumption).
  assert (Hop9 : Z.eqb op_pre 9 = false) by (apply Z.eqb_neq; assumption).
  unfold cm_binary_finish_code.
  rewrite Hop8, Hop9.
  cbn [andb app].
  cancel.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_return_wit_7 : cm_emit_binary_finish_plan_return_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_binary_finish_plan_return_wit_7_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_5_pure_split_goal_1 : cm_emit_binary_finish_plan_partial_solve_wit_5_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with
  | Hwf : cm_type_code_wf (cm_expr_type right_e),
    Hnz : cm_rep_is_pointer_code (cm_type_encode (cm_expr_type right_e)) <> 0 |- _ =>
      rewrite (cm_pointer_encode__expression_add_safety _ Hwf) in Hnz;
      destruct (cm_expr_type right_e); cbn [cm_pointerb cm_is_pointer] in *;
      first [contradiction | exact I]
  end.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_5_pure : cm_emit_binary_finish_plan_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_binary_finish_plan_partial_solve_wit_5_pure_split_goal_1.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_8_pure_split_goal_1 : cm_emit_binary_finish_plan_partial_solve_wit_8_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial; cbn [tvm_opcode_code]; lia.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_8_pure_split_goal_2 : cm_emit_binary_finish_plan_partial_solve_wit_8_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial; cbn [tvm_opcode_code]; lia.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_8_pure : cm_emit_binary_finish_plan_partial_solve_wit_8_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_finish_plan_partial_solve_wit_8_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_finish_plan_partial_solve_wit_8_pure_split_goal_2.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_9_pure_split_goal_1 : cm_emit_binary_finish_plan_partial_solve_wit_9_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial; cbn [tvm_opcode_code]; lia.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_9_pure_split_goal_2 : cm_emit_binary_finish_plan_partial_solve_wit_9_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial; cbn [tvm_opcode_code]; lia.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_9_pure : cm_emit_binary_finish_plan_partial_solve_wit_9_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_finish_plan_partial_solve_wit_9_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_finish_plan_partial_solve_wit_9_pure_split_goal_2.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_10_pure_split_goal_1 : cm_emit_binary_finish_plan_partial_solve_wit_10_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial; cbn [tvm_opcode_code]; lia.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_10_pure_split_goal_2 : cm_emit_binary_finish_plan_partial_solve_wit_10_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial; cbn [tvm_opcode_code]; lia.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_10_pure : cm_emit_binary_finish_plan_partial_solve_wit_10_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_finish_plan_partial_solve_wit_10_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_finish_plan_partial_solve_wit_10_pure_split_goal_2.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_11_pure_split_goal_1 : cm_emit_binary_finish_plan_partial_solve_wit_11_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial; cbn [tvm_opcode_code]; lia.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_11_pure_split_goal_2 : cm_emit_binary_finish_plan_partial_solve_wit_11_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial; cbn [tvm_opcode_code]; lia.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_11_pure : cm_emit_binary_finish_plan_partial_solve_wit_11_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_finish_plan_partial_solve_wit_11_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_finish_plan_partial_solve_wit_11_pure_split_goal_2.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_12_pure_split_goal_1 : cm_emit_binary_finish_plan_partial_solve_wit_12_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with
  | Hwf : cm_type_code_wf (cm_expr_type left_e),
    Hnz : cm_rep_is_pointer_code (cm_type_encode (cm_expr_type left_e)) <> 0 |- _ =>
      rewrite (cm_pointer_encode__expression_add_safety _ Hwf) in Hnz;
      destruct (cm_expr_type left_e); cbn [cm_pointerb cm_is_pointer] in *;
      first [contradiction | exact I]
  end.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_12_pure : cm_emit_binary_finish_plan_partial_solve_wit_12_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_binary_finish_plan_partial_solve_wit_12_pure_split_goal_1.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_15_pure_split_goal_1 : cm_emit_binary_finish_plan_partial_solve_wit_15_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_15_pure_split_goal_2 : cm_emit_binary_finish_plan_partial_solve_wit_15_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_15_pure : cm_emit_binary_finish_plan_partial_solve_wit_15_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_finish_plan_partial_solve_wit_15_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_finish_plan_partial_solve_wit_15_pure_split_goal_2.
Qed. 

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_16_pure_split_goal_1 : cm_emit_binary_finish_plan_partial_solve_wit_16_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_16_pure_split_goal_2 : cm_emit_binary_finish_plan_partial_solve_wit_16_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_16_pure : cm_emit_binary_finish_plan_partial_solve_wit_16_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_finish_plan_partial_solve_wit_16_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_finish_plan_partial_solve_wit_16_pure_split_goal_2.
Qed. 

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_17_pure_split_goal_1 : cm_emit_binary_finish_plan_partial_solve_wit_17_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_17_pure_split_goal_2 : cm_emit_binary_finish_plan_partial_solve_wit_17_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_17_pure : cm_emit_binary_finish_plan_partial_solve_wit_17_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_finish_plan_partial_solve_wit_17_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_finish_plan_partial_solve_wit_17_pure_split_goal_2.
Qed. 

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_18_pure_split_goal_1 : cm_emit_binary_finish_plan_partial_solve_wit_18_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_18_pure_split_goal_2 : cm_emit_binary_finish_plan_partial_solve_wit_18_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_18_pure : cm_emit_binary_finish_plan_partial_solve_wit_18_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_finish_plan_partial_solve_wit_18_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_finish_plan_partial_solve_wit_18_pure_split_goal_2.
Qed. 

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_19_pure_split_goal_1 : cm_emit_binary_finish_plan_partial_solve_wit_19_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with
  | Hwf : cm_type_code_wf (cm_expr_type left_e),
    Hnz : cm_rep_is_pointer_code (cm_type_encode (cm_expr_type left_e)) <> 0 |- _ =>
      rewrite (cm_pointer_encode__expression_add_safety _ Hwf) in Hnz;
      destruct (cm_expr_type left_e); cbn [cm_pointerb cm_is_pointer] in *;
      first [contradiction | exact I]
  end.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_19_pure : cm_emit_binary_finish_plan_partial_solve_wit_19_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_binary_finish_plan_partial_solve_wit_19_pure_split_goal_1.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_22_pure_split_goal_1 : cm_emit_binary_finish_plan_partial_solve_wit_22_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: cbn [tvm_opcode_code]; reflexivity.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_22_pure_split_goal_2 : cm_emit_binary_finish_plan_partial_solve_wit_22_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: cbn [tvm_opcode_code]; discriminate.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_22_pure : cm_emit_binary_finish_plan_partial_solve_wit_22_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_finish_plan_partial_solve_wit_22_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_finish_plan_partial_solve_wit_22_pure_split_goal_2.
Qed. 

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_23_pure_split_goal_1 : cm_emit_binary_finish_plan_partial_solve_wit_23_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: cbn [tvm_opcode_code]; reflexivity.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_23_pure_split_goal_2 : cm_emit_binary_finish_plan_partial_solve_wit_23_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: cbn [tvm_opcode_code]; discriminate.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_23_pure : cm_emit_binary_finish_plan_partial_solve_wit_23_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_finish_plan_partial_solve_wit_23_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_finish_plan_partial_solve_wit_23_pure_split_goal_2.
Qed. 

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_24_pure_split_goal_1 : cm_emit_binary_finish_plan_partial_solve_wit_24_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: cbn [tvm_opcode_code]; reflexivity.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_24_pure_split_goal_2 : cm_emit_binary_finish_plan_partial_solve_wit_24_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: cbn [tvm_opcode_code]; discriminate.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_24_pure : cm_emit_binary_finish_plan_partial_solve_wit_24_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_finish_plan_partial_solve_wit_24_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_finish_plan_partial_solve_wit_24_pure_split_goal_2.
Qed. 

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_25_pure_split_goal_1 : cm_emit_binary_finish_plan_partial_solve_wit_25_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: cbn [tvm_opcode_code]; reflexivity.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_25_pure_split_goal_2 : cm_emit_binary_finish_plan_partial_solve_wit_25_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: cbn [tvm_opcode_code]; discriminate.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_25_pure : cm_emit_binary_finish_plan_partial_solve_wit_25_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_finish_plan_partial_solve_wit_25_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_finish_plan_partial_solve_wit_25_pure_split_goal_2.
Qed. 

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_26_pure_split_goal_1 : cm_emit_binary_finish_plan_partial_solve_wit_26_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  match goal with
  | Hwf : cm_type_code_wf (cm_expr_type left_e),
    Hnz : cm_rep_is_pointer_code (cm_type_encode (cm_expr_type left_e)) <> 0 |- _ =>
      rewrite (cm_pointer_encode__expression_add_safety _ Hwf) in Hnz;
      destruct (cm_expr_type left_e); cbn [cm_pointerb cm_is_pointer] in *;
      first [contradiction | exact I]
  end.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_26_pure : cm_emit_binary_finish_plan_partial_solve_wit_26_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_binary_finish_plan_partial_solve_wit_26_pure_split_goal_1.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_29_pure_split_goal_1 : cm_emit_binary_finish_plan_partial_solve_wit_29_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_29_pure_split_goal_2 : cm_emit_binary_finish_plan_partial_solve_wit_29_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_29_pure : cm_emit_binary_finish_plan_partial_solve_wit_29_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_finish_plan_partial_solve_wit_29_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_finish_plan_partial_solve_wit_29_pure_split_goal_2.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_30_pure_split_goal_1 : cm_emit_binary_finish_plan_partial_solve_wit_30_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_30_pure_split_goal_2 : cm_emit_binary_finish_plan_partial_solve_wit_30_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_30_pure : cm_emit_binary_finish_plan_partial_solve_wit_30_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_finish_plan_partial_solve_wit_30_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_finish_plan_partial_solve_wit_30_pure_split_goal_2.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_31_pure_split_goal_1 : cm_emit_binary_finish_plan_partial_solve_wit_31_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_31_pure_split_goal_2 : cm_emit_binary_finish_plan_partial_solve_wit_31_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_31_pure : cm_emit_binary_finish_plan_partial_solve_wit_31_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_finish_plan_partial_solve_wit_31_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_finish_plan_partial_solve_wit_31_pure_split_goal_2.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_32_pure_split_goal_1 : cm_emit_binary_finish_plan_partial_solve_wit_32_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_32_pure_split_goal_2 : cm_emit_binary_finish_plan_partial_solve_wit_32_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(cbn [tvm_opcode_code]; lia).
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_partial_solve_wit_32_pure : cm_emit_binary_finish_plan_partial_solve_wit_32_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_binary_finish_plan_partial_solve_wit_32_pure_split_goal_1.
  - Goal_apply proof_of_cm_emit_binary_finish_plan_partial_solve_wit_32_pure_split_goal_2.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_which_implies_wit_1_split_goal_spatial : cm_emit_binary_finish_plan_which_implies_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hop : op = 8) by lia. subst op scale.
  pose proof (cm_pointer_encode__expression_add_safety (cm_expr_type right_e) PreH2) as Hr.
  assert (Hptr : cm_pointerb (cm_expr_type right_e) = true).
  { destruct (cm_pointerb (cm_expr_type right_e)); congruence. }
  unfold cm_binary_finish_code. rewrite Hptr. cbn [Z.eqb andb].
  rewrite <- app_assoc. cbn [app]. reflexivity.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_which_implies_wit_1 : cm_emit_binary_finish_plan_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_binary_finish_plan_which_implies_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_which_implies_wit_2_split_goal_spatial : cm_emit_binary_finish_plan_which_implies_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hop : op = 8) by lia. subst op scale.
  pose proof (cm_pointer_encode__expression_add_safety (cm_expr_type left_e) PreH1) as Hl.
  pose proof (cm_pointer_encode__expression_add_safety (cm_expr_type right_e) PreH2) as Hr.
  assert (Hleft : cm_pointerb (cm_expr_type left_e) = true).
  { destruct (cm_pointerb (cm_expr_type left_e)); congruence. }
  assert (Hright : cm_pointerb (cm_expr_type right_e) = false).
  { destruct (cm_pointerb (cm_expr_type right_e)); congruence. }
  unfold cm_binary_finish_code. rewrite Hleft, Hright. cbn [Z.eqb andb app].
  rewrite <- app_assoc. cbn [app]. reflexivity.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_which_implies_wit_2 : cm_emit_binary_finish_plan_which_implies_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_binary_finish_plan_which_implies_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_which_implies_wit_3_split_goal_spatial : cm_emit_binary_finish_plan_which_implies_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hop : op = 9) by lia. subst op scale.
  pose proof (cm_pointer_encode__expression_add_safety (cm_expr_type left_e) PreH1) as Hl.
  pose proof (cm_pointer_encode__expression_add_safety (cm_expr_type right_e) PreH2) as Hr.
  assert (Hleft : cm_pointerb (cm_expr_type left_e) = true).
  { destruct (cm_pointerb (cm_expr_type left_e)); congruence. }
  assert (Hright : cm_pointerb (cm_expr_type right_e) = true).
  { destruct (cm_pointerb (cm_expr_type right_e)); congruence. }
  unfold cm_binary_finish_code. rewrite Hleft, Hright. cbn [Z.eqb andb app].
  rewrite <- app_assoc. cbn [app]. reflexivity.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_which_implies_wit_3 : cm_emit_binary_finish_plan_which_implies_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_binary_finish_plan_which_implies_wit_3_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_which_implies_wit_4_split_goal_spatial : cm_emit_binary_finish_plan_which_implies_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hop : op = 9) by lia. subst op scale.
  pose proof (cm_pointer_encode__expression_add_safety (cm_expr_type left_e) PreH1) as Hl.
  pose proof (cm_pointer_encode__expression_add_safety (cm_expr_type right_e) PreH2) as Hr.
  assert (Hleft : cm_pointerb (cm_expr_type left_e) = true).
  { destruct (cm_pointerb (cm_expr_type left_e)); congruence. }
  assert (Hright : cm_pointerb (cm_expr_type right_e) = false).
  { destruct (cm_pointerb (cm_expr_type right_e)); congruence. }
  unfold cm_binary_finish_code. rewrite Hleft, Hright. cbn [Z.eqb andb app].
  rewrite <- app_assoc. cbn [app]. reflexivity.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_which_implies_wit_4 : cm_emit_binary_finish_plan_which_implies_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_binary_finish_plan_which_implies_wit_4_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_which_implies_wit_5_split_goal_spatial : cm_emit_binary_finish_plan_which_implies_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (op = 8) by lia. subst op.
  rewrite (cm_pointer_encode__expression_add_safety _ PreH1) in PreH5.
  rewrite (cm_pointer_encode__expression_add_safety _ PreH2) in PreH6.
  unfold cm_binary_finish_code.
  destruct (cm_pointerb (cm_expr_type left_e)); try discriminate.
  destruct (cm_pointerb (cm_expr_type right_e)); try discriminate.
  cbn [Z.eqb andb].
  rewrite <- app_assoc.
  reflexivity.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_which_implies_wit_5 : cm_emit_binary_finish_plan_which_implies_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_binary_finish_plan_which_implies_wit_5_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_which_implies_wit_6_split_goal_spatial : cm_emit_binary_finish_plan_which_implies_wit_6_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (op = 9) by lia. subst op.
  rewrite (cm_pointer_encode__expression_add_safety _ PreH1) in PreH5.
  unfold cm_binary_finish_code.
  destruct (cm_pointerb (cm_expr_type left_e)); try discriminate.
  cbn [Z.eqb andb].
  rewrite <- app_assoc.
  reflexivity.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_which_implies_wit_6 : cm_emit_binary_finish_plan_which_implies_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_binary_finish_plan_which_implies_wit_6_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_which_implies_wit_7_split_goal_spatial : cm_emit_binary_finish_plan_which_implies_wit_7_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (H8 : Z.eqb op 8 = false) by (apply Z.eqb_neq; assumption).
  assert (H9 : Z.eqb op 9 = false) by (apply Z.eqb_neq; assumption).
  unfold cm_binary_finish_code.
  rewrite H8, H9. cbn [andb].
  rewrite <- app_assoc.
  reflexivity.
Qed.

Lemma proof_of_cm_emit_binary_finish_plan_which_implies_wit_7 : cm_emit_binary_finish_plan_which_implies_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_binary_finish_plan_which_implies_wit_7_split_goal_spatial.
Qed.

