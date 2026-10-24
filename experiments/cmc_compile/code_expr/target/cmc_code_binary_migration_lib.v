Require Export SimpleC.EE.QCP_demos_human.cmc_code_expr_struct_migration_lib.
From Coq Require Import ZArith List Bool Lia.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_layout_binary_finish_length policy p fid op lhs rhs temp : Zlength (cm_binary_finish_code policy p fid op lhs rhs temp)=cm_binary_tail_count p op lhs rhs-5.
Proof.
 unfold cm_binary_finish_code,cm_binary_tail_count.
 repeat match goal with |-context[if ?b then _ else _]=>destruct b end; repeat rewrite Zlength_app; rewrite cm_layout_temp_load_length; reflexivity.
Qed.
Lemma cm_r_binary_layout_step sp ap p fid op lhs rhs ty st ks ann : cm_task_layout sp ap p (CMRTask p fid (CMBinaryE op lhs rhs ty) st ks) ann -> cm_task_layout sp ap p (cm_rstart sp p fid (CMBinaryE op lhs rhs ty) st ks) (cm_update_annotation (cm_update_r sp ap p fid st ann (CMBinaryE op lhs rhs ty))).
Proof.
 intros [CODE SAVED]; cm_code_expr_reduce; split; [|split; [exact I|exact SAVED]].
 match type of CODE with cm_code_at ?c ?pc ?old=>match goal with |- cm_code_at _ _ ?new=>replace new with old; [exact CODE|] end end.
 unfold cm_emit_rvalue,cm_expr_code_for.
 cbn [Z.eqb cm_emit_expr_pair cm_rcode_of].
 unfold cm_rvalue_code_count; cbn [cm_expr_code_counts cm_rcount_of].
 destruct ((op=?0)||(op=?1)); cbn [cm_rcount_of].
 all: repeat rewrite Zlength_app; repeat rewrite cm_layout_temp_store_length; repeat rewrite cm_layout_binary_finish_length.
 all: repeat match goal with |-context[Zlength (cm_rcode_of (cm_emit_expr_pair ?pol ?pr ?f ?pc ?t ?e))]=>rewrite (proj2 (cm_emit_pair_lengths__store_bounds pol pr f e pc t)) end.
 all: repeat rewrite <-app_assoc; unfold cm_rvalue_code_count; cbn [Zlength]; repeat rewrite Zlength_cons; rewrite ?Zlength_nil; repeat first [reflexivity|solve [lia]|progress f_equal].
Qed.
