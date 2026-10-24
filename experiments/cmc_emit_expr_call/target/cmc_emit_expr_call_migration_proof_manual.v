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
From SimpleC.EE.QCP_demos_human Require Import cmc_emit_expr_call_migration_goal.
From SimpleC.EE.QCP_demos_human Require Import cmc_emit_expr_call_migration_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.QCP_demos_human.cmc_emit_expr_call_migration_lib.
Local Open Scope sac.

Lemma proof_of_cm_emit_args_reload_plan_return_wit_1_split_goal_spatial : cm_emit_args_reload_plan_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst args. cbn [cm_emit_args_reload]. rewrite app_nil_r, app_nil_l.
  cancel.
Qed.

Lemma proof_of_cm_emit_args_reload_plan_return_wit_1 : cm_emit_args_reload_plan_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_args_reload_plan_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_args_reload_plan_return_wit_2_split_goal_spatial : cm_emit_args_reload_plan_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hreload : cm_emit_args_reload policy p fid slot_pre args =
    cm_temp_load_code policy p fid slot_pre ++
    cm_emit_args_reload policy p fid (slot_pre + 1) (cm_args_tail args)).
  { rewrite PreH23 at 1. reflexivity. }
  rewrite Hreload, app_assoc.
  cancel.
Qed.

Lemma proof_of_cm_emit_args_reload_plan_return_wit_2 : cm_emit_args_reload_plan_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_args_reload_plan_return_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_args_reload_plan_which_implies_wit_1_split_goal_1 : cm_emit_args_reload_plan_which_implies_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_cm_emit_args_reload_plan_which_implies_wit_1 : cm_emit_args_reload_plan_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || congruence).
  subst arg_pre. destruct args as [|a args].
  - split_pure_spatial.
    + cancel (cm_arg_list_rep 0 nil).
    + dump_pre_spatial. reflexivity.
  - cbn [cm_arg_list_rep]. Intros ep np. contradiction.
Qed.

Lemma proof_of_cm_emit_args_reload_plan_which_implies_wit_2 : cm_emit_args_reload_plan_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(lia || congruence).
  destruct args as [|a args].
  - cbn [cm_arg_list_rep]. Intros_p H. contradiction.
  - cbn [cm_arg_list_rep cm_args_head cm_args_tail hd tl].
    Intros ep np. Exists np ep.
    split_pure_spatial.
    + repeat progress cancel.
    + split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_cm_emit_args_reload_plan_which_implies_wit_3_split_goal_1 : cm_emit_args_reload_plan_which_implies_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (Zlength_nonneg args).
  unfold cm_temp_offset in *. lia.
Qed.

Lemma proof_of_cm_emit_args_reload_plan_which_implies_wit_3_split_goal_2 : cm_emit_args_reload_plan_which_implies_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH5 in PreH2 at 1.
  rewrite Zlength_cons in PreH2. lia.
Qed.

Lemma proof_of_cm_emit_args_reload_plan_which_implies_wit_3_split_goal_3 : cm_emit_args_reload_plan_which_implies_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH5 in PreH2 at 1.
  rewrite Zlength_cons in PreH2.
  pose proof (Zlength_nonneg (cm_args_tail args)). lia.
Qed.

Lemma proof_of_cm_emit_args_reload_plan_which_implies_wit_3 : cm_emit_args_reload_plan_which_implies_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_args_reload_plan_which_implies_wit_3_split_goal_1.
  - Goal_apply proof_of_cm_emit_args_reload_plan_which_implies_wit_3_split_goal_2.
  - Goal_apply proof_of_cm_emit_args_reload_plan_which_implies_wit_3_split_goal_3.
Qed.

Lemma proof_of_cm_emit_args_reload_plan_which_implies_wit_4_split_goal_spatial : cm_emit_args_reload_plan_which_implies_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH1 at 1.
  cbn [cm_emit_args_reload]. rewrite app_assoc.
  cancel.
Qed.

Lemma proof_of_cm_emit_args_reload_plan_which_implies_wit_4 : cm_emit_args_reload_plan_which_implies_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_args_reload_plan_which_implies_wit_4_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_args_reload_plan_which_implies_wit_5_split_goal_spatial : cm_emit_args_reload_plan_which_implies_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || congruence).
  destruct args as [|a args]; [discriminate|].
  cbn [cm_arg_list_rep cm_args_head cm_args_tail hd tl].
  Exists ep np. split_pure_spatial.
  - repeat progress cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_emit_args_reload_plan_which_implies_wit_5 : cm_emit_args_reload_plan_which_implies_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_args_reload_plan_which_implies_wit_5_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_args_store_plan_return_wit_1_split_goal_spatial : cm_emit_args_store_plan_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst args.
  cbn [cm_emit_args_store].
  rewrite app_nil_r.
  cbn [app].
  cancel.
Qed.

Lemma proof_of_cm_emit_args_store_plan_return_wit_1 : cm_emit_args_store_plan_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_args_store_plan_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_args_store_plan_return_wit_2_split_goal_spatial : cm_emit_args_store_plan_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct args as [|head rest].
  - discriminate.
  - cbn [cm_emit_args_store cm_args_head cm_args_tail hd tl].
    repeat rewrite <- app_assoc.
    cancel.
Qed.

Lemma proof_of_cm_emit_args_store_plan_return_wit_2 : cm_emit_args_store_plan_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_args_store_plan_return_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_args_store_plan_which_implies_wit_1_split_goal_1 : cm_emit_args_store_plan_which_implies_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_cm_emit_args_store_plan_which_implies_wit_1 : cm_emit_args_store_plan_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst arg_pre. destruct args as [|a args].
  - split_pure_spatial.
    + cancel (cm_arg_list_rep 0 nil).
    + dump_pre_spatial. reflexivity.
  - cbn [cm_arg_list_rep]. Intros ep np.
    contradiction.
Qed.

Lemma proof_of_cm_emit_args_store_plan_which_implies_wit_2 : cm_emit_args_store_plan_which_implies_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct args as [|a args].
  - cbn [cm_arg_list_rep]. Intros_p Hzero. contradiction.
  - cbn [cm_arg_list_rep cm_args_head cm_args_tail hd tl].
    Intros ep np. Exists np ep.
    split_pure_spatial.
    + repeat progress cancel.
    + split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_cm_emit_args_store_plan_which_implies_wit_3_split_goal_1 : cm_emit_args_store_plan_which_implies_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct args as [|a args]; [discriminate|].
  cbn [cm_args_counts_representable] in PreH3.
  exact (proj2 (proj2 PreH3)).
Qed.

Lemma proof_of_cm_emit_args_store_plan_which_implies_wit_3_split_goal_2 : cm_emit_args_store_plan_which_implies_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct args as [|a args]; [discriminate|].
  destruct slots as [|s slots]; [contradiction|].
  cbn [cm_args_wf] in PreH2.
  exact (proj2 (proj2 PreH2)).
Qed.

Lemma proof_of_cm_emit_args_store_plan_which_implies_wit_3_split_goal_3 : cm_emit_args_store_plan_which_implies_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct args as [|a args]; [discriminate|].
  cbn [cm_args_counts_representable] in PreH3.
  exact (proj1 (proj2 PreH3)).
Qed.

Lemma proof_of_cm_emit_args_store_plan_which_implies_wit_3_split_goal_4 : cm_emit_args_store_plan_which_implies_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct args as [|a args]; [discriminate|].
  destruct slots as [|s slots]; [contradiction|].
  cbn [cm_args_wf] in PreH2.
  exact (proj1 PreH2).
Qed.

Lemma proof_of_cm_emit_args_store_plan_which_implies_wit_3 : cm_emit_args_store_plan_which_implies_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_args_store_plan_which_implies_wit_3_split_goal_1.
  - Goal_apply proof_of_cm_emit_args_store_plan_which_implies_wit_3_split_goal_2.
  - Goal_apply proof_of_cm_emit_args_store_plan_which_implies_wit_3_split_goal_3.
  - Goal_apply proof_of_cm_emit_args_store_plan_which_implies_wit_3_split_goal_4.
Qed.

Lemma proof_of_cm_emit_args_store_plan_which_implies_wit_4_split_goal_spatial : cm_emit_args_store_plan_which_implies_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst head_count.
  destruct args as [|head rest].
  - discriminate.
  - cbn [cm_emit_args_store cm_args_head cm_args_tail hd tl].
    repeat rewrite <- app_assoc.
    cancel.
Qed.

Lemma proof_of_cm_emit_args_store_plan_which_implies_wit_4 : cm_emit_args_store_plan_which_implies_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_args_store_plan_which_implies_wit_4_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_1 : cm_emit_args_store_plan_which_implies_wit_5_split_goal_1.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 destruct args as [|a t]; [discriminate PreH1|].
 unfold cm_args_head, cm_args_tail in *. cbn [hd tl] in *.
 subst head_count.
 cbn [cm_emit_args_store cm_expr_code_for] in PreH9.
 rewrite !Zlength_app in PreH9.
 rewrite (proj1 (cm_primitive_lengths__store_bounds policy p fid slot CMIntTy)) in PreH9.
 pose proof (proj2 (cm_emit_pair_lengths__store_bounds policy p fid a pc scratch)) as Hlen.
 pose proof (Zlength_nonneg (cm_rcode_of (cm_emit_expr_pair policy p fid pc scratch a))) as Hhead.
 pose proof (Zlength_nonneg (cm_emit_args_store policy p fid
   (pc + cm_rvalue_code_count policy p fid a + 5) (slot+1) scratch t)) as Htail.
 unfold cm_expr_code_for in *. cbn [Z.eqb] in *.
 rewrite Hlen in *.
 unfold cm_i32_code_count in *. lia.
Qed.

Lemma proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_2 : cm_emit_args_store_plan_which_implies_wit_5_split_goal_2.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 destruct args as [|a t]; [discriminate PreH1|].
 unfold cm_args_head, cm_args_tail in *. cbn [hd tl] in *.
 subst head_count.
 cbn [cm_emit_args_store cm_expr_code_for] in PreH9.
 rewrite !Zlength_app in PreH9.
 rewrite (proj1 (cm_primitive_lengths__store_bounds policy p fid slot CMIntTy)) in PreH9.
 pose proof (proj2 (cm_emit_pair_lengths__store_bounds policy p fid a pc scratch)) as Hlen.
 pose proof (Zlength_nonneg (cm_rcode_of (cm_emit_expr_pair policy p fid pc scratch a))) as Hhead.
 pose proof (Zlength_nonneg (cm_emit_args_store policy p fid
   (pc + cm_rvalue_code_count policy p fid a + 5) (slot+1) scratch t)) as Htail.
 unfold cm_expr_code_for in *. cbn [Z.eqb] in *.
 rewrite Hlen in *.
 unfold cm_i32_code_count in *. lia.
Qed.

Lemma proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_3 : cm_emit_args_store_plan_which_implies_wit_5_split_goal_3.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 destruct args as [|a t]; [discriminate PreH1|].
 unfold cm_args_head, cm_args_tail in *. cbn [hd tl] in *.
 subst head_count.
 cbn [cm_emit_args_store cm_expr_code_for] in PreH9.
 rewrite !Zlength_app in PreH9.
 rewrite (proj1 (cm_primitive_lengths__store_bounds policy p fid slot CMIntTy)) in PreH9.
 pose proof (proj2 (cm_emit_pair_lengths__store_bounds policy p fid a pc scratch)) as Hlen.
 pose proof (Zlength_nonneg (cm_rcode_of (cm_emit_expr_pair policy p fid pc scratch a))) as Hhead.
 pose proof (Zlength_nonneg (cm_emit_args_store policy p fid
   (pc + cm_rvalue_code_count policy p fid a + 5) (slot+1) scratch t)) as Htail.
 unfold cm_expr_code_for in *. cbn [Z.eqb] in *.
 rewrite Hlen in *.
 unfold cm_i32_code_count in *. lia.
Qed.

Lemma proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_4 : cm_emit_args_store_plan_which_implies_wit_5_split_goal_4.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 destruct args as [|a t]; [discriminate PreH1|].
 unfold cm_args_head, cm_args_tail in *. cbn [hd tl] in *.
 subst head_count.
 cbn [cm_emit_args_store cm_expr_code_for] in PreH9.
 rewrite !Zlength_app in PreH9.
 rewrite (proj1 (cm_primitive_lengths__store_bounds policy p fid slot CMIntTy)) in PreH9.
 pose proof (proj2 (cm_emit_pair_lengths__store_bounds policy p fid a pc scratch)) as Hlen.
 pose proof (Zlength_nonneg (cm_rcode_of (cm_emit_expr_pair policy p fid pc scratch a))) as Hhead.
 pose proof (Zlength_nonneg (cm_emit_args_store policy p fid
   (pc + cm_rvalue_code_count policy p fid a + 5) (slot+1) scratch t)) as Htail.
 unfold cm_expr_code_for in *. cbn [Z.eqb] in *.
 rewrite Hlen in *.
 unfold cm_i32_code_count in *. lia.
Qed.

Lemma proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_5 : cm_emit_args_store_plan_which_implies_wit_5_split_goal_5.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 destruct args as [|a t]; [discriminate PreH1|].
 unfold cm_args_head, cm_args_tail in *. cbn [hd tl] in *.
 subst head_count.
 cbn [cm_emit_args_store cm_expr_code_for] in PreH9.
 rewrite !Zlength_app in PreH9.
 rewrite (proj1 (cm_primitive_lengths__store_bounds policy p fid slot CMIntTy)) in PreH9.
 pose proof (proj2 (cm_emit_pair_lengths__store_bounds policy p fid a pc scratch)) as Hlen.
 pose proof (Zlength_nonneg (cm_rcode_of (cm_emit_expr_pair policy p fid pc scratch a))) as Hhead.
 pose proof (Zlength_nonneg (cm_emit_args_store policy p fid
   (pc + cm_rvalue_code_count policy p fid a + 5) (slot+1) scratch t)) as Htail.
 unfold cm_expr_code_for in *. cbn [Z.eqb] in *.
 rewrite Hlen in *.
 unfold cm_i32_code_count in *. lia.
Qed.

Lemma proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_6 : cm_emit_args_store_plan_which_implies_wit_5_split_goal_6.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 destruct args as [|a t]; [discriminate PreH1|].
 unfold cm_args_head, cm_args_tail in *. cbn [hd tl] in *.
 subst head_count.
 cbn [cm_emit_args_store cm_expr_code_for] in PreH9.
 rewrite !Zlength_app in PreH9.
 rewrite (proj1 (cm_primitive_lengths__store_bounds policy p fid slot CMIntTy)) in PreH9.
 pose proof (proj2 (cm_emit_pair_lengths__store_bounds policy p fid a pc scratch)) as Hlen.
 pose proof (Zlength_nonneg (cm_rcode_of (cm_emit_expr_pair policy p fid pc scratch a))) as Hhead.
 pose proof (Zlength_nonneg (cm_emit_args_store policy p fid
   (pc + cm_rvalue_code_count policy p fid a + 5) (slot+1) scratch t)) as Htail.
 unfold cm_expr_code_for in *. cbn [Z.eqb] in *.
 rewrite Hlen in *.
 unfold cm_i32_code_count in *. lia.
Qed.

Lemma proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_7 : cm_emit_args_store_plan_which_implies_wit_5_split_goal_7.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 destruct args as [|a t]; [discriminate PreH1|].
 unfold cm_args_head, cm_args_tail in *. cbn [hd tl] in *.
 subst head_count.
 cbn [cm_emit_args_store cm_expr_code_for] in PreH9.
 rewrite !Zlength_app in PreH9.
 rewrite (proj1 (cm_primitive_lengths__store_bounds policy p fid slot CMIntTy)) in PreH9.
 pose proof (proj2 (cm_emit_pair_lengths__store_bounds policy p fid a pc scratch)) as Hlen.
 pose proof (Zlength_nonneg (cm_rcode_of (cm_emit_expr_pair policy p fid pc scratch a))) as Hhead.
 pose proof (Zlength_nonneg (cm_emit_args_store policy p fid
   (pc + cm_rvalue_code_count policy p fid a + 5) (slot+1) scratch t)) as Htail.
 unfold cm_expr_code_for in *. cbn [Z.eqb] in *.
 rewrite Hlen in *.
 unfold cm_i32_code_count in *. lia.
Qed.

Lemma proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_8 : cm_emit_args_store_plan_which_implies_wit_5_split_goal_8.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 destruct args as [|a t]; [discriminate PreH1|].
 unfold cm_args_head, cm_args_tail in *. cbn [hd tl] in *.
 pose proof (Zlength_nonneg t).
 rewrite Zlength_cons in PreH3.
 unfold cm_temp_offset in *. lia.
Qed.

Lemma proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_9 : cm_emit_args_store_plan_which_implies_wit_5_split_goal_9.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 destruct args as [|a t]; [discriminate PreH1|].
 unfold cm_args_head, cm_args_tail in *. cbn [hd tl] in *.
 cbn [cm_args_apair cm_adepth] in PreH5.
 unfold cm_imax in PreH5.
 pose proof (Z.le_max_r (cm_tright (cm_expr_tpair a)) (cm_adepth (cm_args_apair t))). lia.
Qed.

Lemma proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_10 : cm_emit_args_store_plan_which_implies_wit_5_split_goal_10.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 destruct args as [|a t]; [discriminate PreH1|].
 unfold cm_args_head, cm_args_tail in *. cbn [hd tl] in *.
 cbn [cm_args_apair cm_adepth] in PreH5.
 unfold cm_imax in PreH5.
 unfold cm_expr_temps_for. cbn [Z.eqb]. unfold cm_rtemps.
 pose proof (Z.le_max_l (cm_tright (cm_expr_tpair a)) (cm_adepth (cm_args_apair t))). lia.
Qed.

Lemma proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_11 : cm_emit_args_store_plan_which_implies_wit_5_split_goal_11.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 destruct args as [|a t]; [discriminate PreH1|].
 unfold cm_args_head, cm_args_tail in *. cbn [hd tl] in *.
 rewrite Zlength_cons in PreH3. lia.
Qed.

Lemma proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_12 : cm_emit_args_store_plan_which_implies_wit_5_split_goal_12.
Proof.
 LLM_pre_process ltac:(lia || nia || int_auto).
 destruct args as [|a t]; [discriminate PreH1|].
 unfold cm_args_head, cm_args_tail in *. cbn [hd tl] in *.
 rewrite Zlength_cons in PreH3. pose proof (Zlength_nonneg t). lia.
Qed.

Lemma proof_of_cm_emit_args_store_plan_which_implies_wit_5 : cm_emit_args_store_plan_which_implies_wit_5.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_1.
 - Goal_apply proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_2.
 - Goal_apply proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_3.
 - Goal_apply proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_4.
 - Goal_apply proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_5.
 - Goal_apply proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_6.
 - Goal_apply proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_7.
 - Goal_apply proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_8.
 - Goal_apply proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_9.
 - Goal_apply proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_10.
 - Goal_apply proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_11.
 - Goal_apply proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_12.
Qed. 

Lemma proof_of_cm_emit_args_store_plan_which_implies_wit_6_split_goal_spatial : cm_emit_args_store_plan_which_implies_wit_6_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct args as [|a args]; [discriminate|].
  cbn [cm_arg_list_rep cm_args_head cm_args_tail hd tl].
  Exists ep np. split_pure_spatial.
  - repeat progress cancel.
  - dump_pre_spatial. assumption.
Qed.

Lemma proof_of_cm_emit_args_store_plan_which_implies_wit_6 : cm_emit_args_store_plan_which_implies_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_args_store_plan_which_implies_wit_6_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_call_expr_return_wit_1_split_goal_spatial : cm_emit_call_expr_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst lvalue_pre.
  destruct e; cbn [cm_rep_expr_kind] in *; try discriminate.
  cbn [cm_call_args cm_rep_expr_value] in *.
  rewrite cm_call_code_equation.
  repeat rewrite app_assoc.
  cancel.
Qed.

Lemma proof_of_cm_emit_call_expr_return_wit_1 : cm_emit_call_expr_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_call_expr_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_call_expr_return_wit_2_split_goal_spatial : cm_emit_call_expr_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn [cm_rep_expr_kind] in *; try discriminate.
  rewrite cm_call_lvalue_empty by lia.
  cbn [app]. rewrite app_nil_r.
  cancel.
Qed.

Lemma proof_of_cm_emit_call_expr_return_wit_2 : cm_emit_call_expr_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_call_expr_return_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_cm_emit_call_expr_which_implies_wit_1 : cm_emit_call_expr_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn [cm_rep_expr_kind] in *; try discriminate.
  rewrite cm_expr_rep_node.
  unfold cm_expr_node. cbn [cm_expr_payload cm_call_args cm_rep_expr_kind].
  Intros a b args_ptr.
  destruct H0 as [Ha Hb].
  subst a b.
  Exists args_ptr.
  split_pure_spatial; try (dump_pre_spatial; tauto).
  sepcon_right_assoc.
  repeat match goal with |- ?P ** _ |-- _ => cancel P end.
  try match goal with |- ?P |-- _ => cancel P end.
Qed.

Lemma proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_1 : cm_emit_call_expr_which_implies_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst lvalue_pre.
  destruct e; cbn [cm_rep_expr_kind] in PreH1; try discriminate.
  cbn [cm_call_args cm_rep_expr_value] in *.
  unfold cm_expr_temps_for, cm_rtemps in PreH7.
  rewrite cm_expr_tpair_call in PreH7.
  cbn [cm_tright] in PreH7. unfold cm_args_temps in PreH7.
  match type of PreH7 with context [cm_args_apair ?args] =>
    pose proof (cm_args_apair_count_depth__call_bounds args) as [Hcount Hdepth]
  end.
  rewrite Hcount in PreH7. cbn in PreH7.
  lia.
Qed.

Lemma proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_2 : cm_emit_call_expr_which_implies_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst lvalue_pre.
  destruct e; cbn [cm_rep_expr_kind] in PreH1; try discriminate.
  cbn [cm_call_args cm_rep_expr_value] in *.
  unfold cm_expr_temps_for, cm_rtemps in PreH7.
  rewrite cm_expr_tpair_call in PreH7.
  cbn [cm_tright] in PreH7. unfold cm_args_temps in PreH7.
  match type of PreH7 with context [cm_args_apair ?args] =>
    pose proof (cm_args_apair_count_depth__call_bounds args) as [Hcount Hdepth]
  end.
  rewrite Hcount in PreH7. cbn in PreH7.
  pose proof (cm_slots_size_nonnegative__call_bounds _ _ PreH10) as Hp.
  pose proof (cm_slots_size_nonnegative__call_bounds _ _ PreH11) as Hl.
  unfold cm_temp_offset in PreH8. rewrite <- PreH9 in PreH8.
  lia.
Qed.

Lemma proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_3 : cm_emit_call_expr_which_implies_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst lvalue_pre.
  destruct e; cbn [cm_rep_expr_kind] in PreH1; try discriminate.
  cbn [cm_call_args cm_rep_expr_value] in *.
  unfold cm_expr_temps_for, cm_rtemps in PreH7.
  rewrite cm_expr_tpair_call in PreH7.
  cbn [cm_tright] in PreH7. unfold cm_args_temps in PreH7.
  match type of PreH7 with context [cm_args_apair ?args] =>
    pose proof (cm_args_apair_count_depth__call_bounds args) as [Hcount Hdepth]
  end.
  rewrite Hcount in PreH7. cbn in PreH7.
  lia.
Qed.

Lemma proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_4 : cm_emit_call_expr_which_implies_wit_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (Zlength_nonneg (cm_call_args e)). lia.
Qed.

Lemma proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_5 : cm_emit_call_expr_which_implies_wit_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (cm_slots_size_nonnegative__call_bounds _ _ PreH10) as Hp.
  pose proof (cm_slots_size_nonnegative__call_bounds _ _ PreH11) as Hl.
  unfold cm_temp_offset in PreH8. rewrite <- PreH9 in PreH8.
  lia.
Qed.

Lemma proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_6 : cm_emit_call_expr_which_implies_wit_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(reflexivity).
Qed.

Lemma proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_7 : cm_emit_call_expr_which_implies_wit_2_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst lvalue_pre.
  destruct e; cbn [cm_rep_expr_kind] in PreH1; try discriminate.
  cbn [cm_call_args cm_rep_expr_value] in *.
  unfold cm_expr_temps_for, cm_rtemps in PreH7.
  rewrite cm_expr_tpair_call in PreH7.
  cbn [cm_tright] in PreH7. unfold cm_args_temps in PreH7.
  match type of PreH7 with context [cm_args_apair ?args] =>
    pose proof (cm_args_apair_count_depth__call_bounds args) as [Hcount Hdepth]
  end.
  rewrite Hcount in PreH7. cbn in PreH7.
  pose proof (cm_slots_size_nonnegative__call_bounds _ _ PreH10) as Hp.
  pose proof (cm_slots_size_nonnegative__call_bounds _ _ PreH11) as Hl.
  unfold cm_temp_offset in PreH8. rewrite <- PreH9 in PreH8.
  apply cm_rep_args_safe_of_length__call_bounds. lia.
Qed.

Lemma proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_8 : cm_emit_call_expr_which_implies_wit_2_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst lvalue_pre.
  destruct e; cbn [cm_rep_expr_kind] in PreH1; try discriminate.
  cbn [cm_call_args cm_rep_expr_value] in *.
  apply cm_expr_counts_repr_call in PreH4. tauto.
Qed.

Lemma proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_9 : cm_emit_call_expr_which_implies_wit_2_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst lvalue_pre.
  destruct e; cbn [cm_rep_expr_kind] in PreH1; try discriminate.
  cbn [cm_call_args cm_rep_expr_value] in *.
  apply cm_expr_wf_call in PreH3. tauto.
Qed.

Lemma proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_10 : cm_emit_call_expr_which_implies_wit_2_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst lvalue_pre.
  destruct e; cbn [cm_rep_expr_kind] in PreH1; try discriminate.
  cbn [cm_call_args cm_rep_expr_value] in *.
  apply cm_expr_counts_repr_call in PreH4. unfold cm_i32_code_count in *. tauto.
Qed.

Lemma proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_11 : cm_emit_call_expr_which_implies_wit_2_split_goal_11.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst lvalue_pre.
  destruct e; cbn [cm_rep_expr_kind] in PreH1; try discriminate.
  cbn [cm_call_args cm_rep_expr_value] in *.
  apply cm_expr_counts_repr_call in PreH4. unfold cm_i32_code_count in *. tauto.
Qed.

Lemma proof_of_cm_emit_call_expr_which_implies_wit_2 : cm_emit_call_expr_which_implies_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_1.
  - Goal_apply proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_2.
  - Goal_apply proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_3.
  - Goal_apply proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_4.
  - Goal_apply proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_5.
  - Goal_apply proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_6.
  - Goal_apply proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_7.
  - Goal_apply proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_8.
  - Goal_apply proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_9.
  - Goal_apply proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_10.
  - Goal_apply proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_11.
Qed. 

Lemma proof_of_cm_emit_call_expr_which_implies_wit_3_split_goal_1 : cm_emit_call_expr_which_implies_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst lvalue_pre count.
  destruct e; cbn [cm_rep_expr_kind] in *; try discriminate.
  cbn [cm_call_args] in *.
  rewrite cm_call_code_equation in *.
  unfold cm_i32_code_count in *.
  repeat rewrite Zlength_app in *.
  match goal with |- context [cm_emit_args_store ?policy ?p ?fid ?pc ?temp ?scratch ?args] =>
    pose proof (Zlength_nonneg (cm_emit_args_store policy p fid pc temp scratch args));
    pose proof (Zlength_nonneg (cm_emit_args_reload policy p fid temp args))
  end.
  dump_pre_spatial. rewrite Zlength_cons, Zlength_nil in PreH5. lia.
Qed.

Lemma proof_of_cm_emit_call_expr_which_implies_wit_3_split_goal_spatial : cm_emit_call_expr_which_implies_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst lvalue_pre count.
  destruct e; cbn [cm_rep_expr_kind] in *; try discriminate.
  cbn [cm_call_args cm_rep_expr_value] in *.
  rewrite cm_call_code_equation.
  repeat rewrite <- app_assoc. cbn [app].
  cancel.
Qed.

Lemma proof_of_cm_emit_call_expr_which_implies_wit_3 : cm_emit_call_expr_which_implies_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cm_emit_call_expr_which_implies_wit_3_split_goal_spatial.
  - Goal_apply proof_of_cm_emit_call_expr_which_implies_wit_3_split_goal_1.
Qed.

Lemma proof_of_cm_emit_call_expr_which_implies_wit_4_split_goal_spatial : cm_emit_call_expr_which_implies_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct e; cbn [cm_rep_expr_kind] in *; try discriminate.
  rewrite cm_expr_rep_node.
  unfold cm_expr_node. cbn [cm_expr_payload cm_call_args cm_rep_expr_kind].
  Exists 0 0 xargs.
  split_pure_spatial; try (dump_pre_spatial; tauto).
  sepcon_right_assoc.
  repeat match goal with |- ?P ** _ |-- _ => cancel P end.
  try match goal with |- ?P |-- _ => cancel P end.
  split_pures; dump_pre_spatial; tauto.
Qed.

Lemma proof_of_cm_emit_call_expr_which_implies_wit_4 : cm_emit_call_expr_which_implies_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cm_emit_call_expr_which_implies_wit_4_split_goal_spatial.
Qed.

