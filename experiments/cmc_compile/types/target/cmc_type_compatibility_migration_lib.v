Require Export SimpleC.EE.QCP_demos_human.cmc_type_cursors_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_value_type_scalar v : cm_scalar_expr_type (cm_value_type v).
Proof. destruct v; cbv beta iota delta [cm_value_type cm_scalar_expr_type cm_integer_type cm_is_pointer]; intuition. Qed.
Lemma cm_compatible_scalar v ty : cm_value_type_compatible v ty -> cm_scalar_expr_type ty.
Proof. intros [<-|[_ P]]; [apply cm_value_type_scalar|now right]. Qed.
Lemma cm_compatible_integer v ty : cm_value_type_compatible v ty -> cm_integer_type ty -> cm_integer_type (cm_value_type v).
Proof. intros [<-|[-> P]] I; [exact I|destruct ty; cbv beta iota delta [cm_is_pointer cm_integer_type] in *; intuition discriminate]. Qed.
Lemma cm_compatible_pointer v ty : cm_value_type_compatible v ty -> cm_is_pointer ty -> cm_is_pointer (cm_value_type v).
Proof. intros [<-|[-> P]] H; [exact H|exact I]. Qed.
Lemma cm_compatible_convertible v from to : cm_value_type_compatible v from -> cm_convertible from to -> cm_value_convertible_to v to.
Proof.
 intros [<-|[-> PTR]] CONV; [now left|]. left.
 destruct from,to; cbv beta iota delta [cm_is_pointer cm_convertible cm_value_type cm_is_struct cm_integer_type] in *; intuition congruence.
Qed.
Lemma cm_expr_value_convertible expr v ty : cm_expr_value_type_ready expr v -> cm_expr_convertible expr ty -> cm_value_convertible_to v ty.
Proof.
 intros [COMP ZERO] [CONV|[PTR LIT]]; [eapply cm_compatible_convertible; eassumption|right; split; [now apply ZERO|exact PTR]].
Qed.
Lemma cm_convert_value_type st ty v : cm_scalar_expr_type ty -> cm_value_convertible_to v ty -> cm_value_type_compatible (cm_convert_value st ty v) ty.
Proof.
 destruct ty; intros SC CONV; try solve [left; reflexivity].
 - unfold cm_scalar_expr_type,cm_integer_type,cm_is_pointer in SC; intuition discriminate.
 - destruct v; unfold cm_value_convertible_to,cm_convertible,cm_value_type,cm_is_struct,cm_integer_type,cm_is_pointer in CONV;
   cbv beta iota delta [cm_convert_value cm_pointer_retype cm_pointee cm_value_type_compatible cm_value_type cm_is_pointer];
   try solve [left; reflexivity|right; auto].
   + match goal with n:Z|-_=>assert (n=0) by intuition congruence; subst n end.
     assert (W:tower_wrap64 0=0) by (apply tower_wrap64_fixed; unfold tower_signed64; lia).
     match goal with H:?n=0|-_=>rewrite H end; rewrite W; cbn [Z.eqb]; right; auto.
   + exfalso; intuition discriminate.
Qed.
Lemma cm_phase_expr_value_ready policy nilslot p fid phase expr v : cm_phase_expr_type_ready policy nilslot p fid phase expr -> cm_expr_value_type_ready expr v -> cm_phase_value_type_ready policy nilslot p fid phase v.
Proof.
 intros PH [COMP ZERO]; destruct phase; cbn [cm_phase_expr_type_ready cm_phase_value_type_ready] in *;
 try solve [exact I|contradiction|subst; exact COMP|rewrite <-PH; exact COMP|eapply cm_compatible_integer; eassumption|apply cm_value_type_scalar].
 all: apply cm_expr_value_convertible with (expr:=expr); [split; assumption|exact PH].
Qed.
Lemma cm_cursor_expr_value_ready policy nilslot p fid expr cursors : cm_cursor_head_expr_type_ready policy nilslot p fid expr cursors -> cm_cursor_expr_values_type_ready policy nilslot p fid expr cursors.
Proof. destruct cursors; [contradiction|]; intros H v V; eapply cm_phase_expr_value_ready; eassumption. Qed.
Lemma cm_type_ready_same_cursors policy nilslot p task leftann rightann : cm_ann_cursors leftann=cm_ann_cursors rightann -> cm_task_type_ready policy nilslot p task leftann -> cm_task_type_ready policy nilslot p task rightann.
Proof. intros C H; destruct task; cbn [cm_task_type_ready] in *; try rewrite <-C; exact H. Qed.
