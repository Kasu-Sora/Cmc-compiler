Require Export SimpleC.EE.QCP_demos_human.cmc_type_facts_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_args_wf_slots_nonempty policy p f args slots : cm_args_wf policy p f args slots -> args<>[] -> slots<>[].
Proof. destruct args,slots; cbn [cm_args_wf]; intuition discriminate. Qed.
Lemma cm_args_wf_tails policy p f args slots : cm_args_wf policy p f args slots -> args<>[] -> cm_args_wf policy p f (tl args) (tl slots).
Proof. destruct args,slots; cbn [cm_args_wf tl]; intuition discriminate. Qed.
Lemma cm_args_wf_head_convertible policy nilslot nilexpr p f args slots : cm_args_wf policy p f args slots -> args<>[] -> cm_expr_convertible (hd nilexpr args) (cm_slot_ty (hd nilslot slots)).
Proof. destruct args,slots; cbn [cm_args_wf hd]; intuition discriminate. Qed.
Lemma cm_arg_progress_extend policy nilslot p f all_args slots done rest incoming :
 cm_args_wf policy p f all_args slots -> cm_arg_progress_type_ready nilslot all_args slots done rest -> rest<>[] ->
 cm_value_convertible_to incoming (cm_arg_next_type nilslot slots done) ->
 cm_arg_progress_type_ready nilslot all_args slots (done++[incoming]) (tl rest).
Proof.
 revert all_args slots; induction done as [|v done IH]; intros all_args slots WF PROG NONEMPTY CONV.
 - destruct PROG as [AN [SN TAIL]]. cbn [app cm_arg_progress_type_ready cm_arg_next_type] in *.
   repeat split; try assumption.
   + now rewrite TAIL.
   + eapply cm_args_wf_slots_nonempty; [eapply cm_args_wf_tails; eassumption|now rewrite TAIL].
   + now rewrite TAIL.
 - destruct PROG as [AN [SN [V PROG]]]. cbn [app cm_arg_progress_type_ready cm_arg_next_type] in *.
   repeat split; try assumption. apply IH; try assumption; eapply cm_args_wf_tails; eassumption.
Qed.
Lemma cm_arg_progress_next_expr policy nilslot nilexpr p f all_args slots done rest incoming :
 cm_args_wf policy p f all_args slots -> cm_arg_progress_type_ready nilslot all_args slots done rest -> rest<>[] ->
 cm_value_convertible_to incoming (cm_arg_next_type nilslot slots done) ->
 cm_expr_convertible (hd nilexpr rest) (cm_arg_next_type nilslot slots (done++[incoming])).
Proof.
 revert all_args slots; induction done as [|v done IH]; intros all_args slots WF PROG NONEMPTY CONV.
 - destruct PROG as [AN [SN TAIL]]; cbn [app cm_arg_next_type]. rewrite <-TAIL.
   eapply cm_args_wf_head_convertible; [eapply cm_args_wf_tails; eassumption|now rewrite TAIL].
 - destruct PROG as [AN [SN [V PROG]]]; cbn [app cm_arg_next_type] in *.
   apply IH with (all_args:=tl all_args); try assumption; eapply cm_args_wf_tails; eassumption.
Qed.
