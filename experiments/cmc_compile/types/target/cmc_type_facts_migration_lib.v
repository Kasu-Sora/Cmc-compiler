Require Export SimpleC.EE.QCP_demos_human.cmc_type_compatibility_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_scalar_type_is_expr_type structs ty : cm_scalar_type structs ty -> cm_scalar_expr_type ty.
Proof. destruct ty; unfold cm_scalar_type,cm_scalar_expr_type,cm_integer_type,cm_is_struct,cm_is_pointer; intuition discriminate. Qed.
Lemma cm_convertible_scalar_types from to : cm_convertible from to -> cm_scalar_expr_type from /\ cm_scalar_expr_type to.
Proof. destruct from,to; unfold cm_convertible,cm_scalar_expr_type,cm_integer_type,cm_is_struct,cm_is_pointer; intuition discriminate. Qed.
Lemma cm_expr_convertible_source_scalar expr ty : cm_expr_convertible expr ty -> cm_scalar_expr_type (cm_expr_type expr).
Proof. intros [C|[_ ->]]; [exact (proj1 (cm_convertible_scalar_types _ _ C))|left; now left]. Qed.
Lemma cm_typed_function_at policy p fid : cm_typed_program policy p -> 0<=fid -> fid<Zlength (cm_program_functions p) -> cm_function_wf policy p (cm_function_at policy fid (cm_program_functions p)).
Proof. intros [_ [_ [_ [F _]]]] L U; apply F; auto. Qed.
Lemma cm_stmt_wf_loop_mono policy p f loop stmt : cm_stmt_wf policy p f loop stmt -> cm_stmt_wf policy p f true stmt.
Proof. revert loop; induction stmt; intros loop; cbn [cm_stmt_wf] in *; intuition eauto. Qed.
Lemma cm_args_wf_exprs policy p f args slots : cm_args_wf policy p f args slots -> cm_exprs_type_ready policy p f args.
Proof.
 revert slots; induction args as [|a args IH]; intros [|s slots]; cbn [cm_args_wf cm_exprs_type_ready]; try tauto.
 intros [WF [CONV REST]]; split; [exact WF|]; split; [now apply cm_expr_convertible_source_scalar with (ty:=cm_slot_ty s)|now apply IH with (slots:=slots)].
Qed.
Lemma cm_value_type_compatible_refl v : cm_value_type_compatible v (cm_value_type v).
Proof. now left. Qed.
Lemma cm_pointer_value_view v ty : cm_value_type_compatible v (CMPtrTy ty) -> v<>CMNullV -> cm_ptr_view v=ty.
Proof. destruct v; cbv beta iota delta [cm_value_type_compatible cm_value_type cm_ptr_view]; intros H N; intuition congruence. Qed.
Lemma cm_expr_not_zero_ready expr v : expr<>CMConstE 0 CMIntTy -> cm_value_type_compatible v (cm_expr_type expr) -> cm_expr_value_type_ready expr v.
Proof. intros N V; split; [exact V|intro E; contradiction]. Qed.
Lemma cm_const_expr_value_ready st n ty : cm_integer_type ty -> cm_expr_value_type_ready (CMConstE n ty) (cm_convert_value st ty (CMIntV n)).
Proof.
 intros [-> | ->]; split; try solve [left; reflexivity]; intro ZER; unfold cm_zero_literal in ZER; inversion ZER; subst.
 - unfold cm_convert_value,cm_value_number; assert (W:tower_wrap64 0=0) by (apply tower_wrap64_fixed; unfold tower_signed64; lia); now rewrite W.
Qed.
Lemma cm_cursors_type_tail policy nilslot p fid phase owner ob oc rest : cm_cursors_type_ready policy nilslot p fid (CMACursor phase owner ob oc::rest) -> cm_cursors_type_ready policy nilslot p (cm_phase_next_fid fid phase) rest.
Proof. intros [_ [_ [_ H]]]; exact H. Qed.
Lemma cm_cursors_result_ready policy nilslot p fid phase owner ob oc rest ty v :
 cm_cursors_type_ready policy nilslot p fid (CMACursor phase owner ob oc::rest) -> cm_phase_result_type p fid phase ty -> cm_value_type_compatible v ty ->
 cm_cursor_head_value_type_ready policy nilslot p (cm_phase_next_fid fid phase) v rest.
Proof. intros [_ [_ [RESULT _]]] TY V; exact (RESULT ty v TY V). Qed.
