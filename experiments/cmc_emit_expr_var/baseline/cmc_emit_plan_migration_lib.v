(* A plan is a logical capacity budget over the existing resolved emitter. *)
From Coq Require Import ZArith List Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export SimpleC.EE.QCP_demos_human.cmc_emit_resolved_migration_lib.
Import ListNotations naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope list_scope.

Definition cm_resolved_emitter_plan_rep policy p (emitter out capacity : Z)
    (done todo : list tvm_inst) : Assertion :=
  “Zlength done + Zlength todo <= capacity” &&
  cm_resolved_emitter_rep policy p emitter out capacity done.

(* The two consequences used by every plan-open boundary. *)
Lemma cm_plan_fragment_capacity (done fragment tail : list tvm_inst) capacity :
  Zlength done + Zlength (fragment ++ tail) <= capacity ->
  Zlength done + Zlength fragment <= capacity /\
  Zlength (done ++ fragment) + Zlength tail <= capacity.
Proof.
  rewrite !Zlength_app. pose proof (Zlength_nonneg tail). lia.
Qed.
