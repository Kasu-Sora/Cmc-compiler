Require Import SimpleC.EE.QCP_demos_human.cmc_temp_ready_migration_lib.
From Coq Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.
(* Exact source statements: no well-typedness, validity, or extra bounds added. *)
Check (cm_expr_temps_ready_from_counts : forall policy e p fid,
 cm_expr_counts_representable policy p fid e ->
 cm_rep_expr_temps_safe e /\ cm_ltemps e <= cm_lvalue_code_count policy p fid e /\
 cm_rtemps e <= cm_rvalue_code_count policy p fid e).
Check (cm_args_temps_ready_from_counts : forall policy args p fid,
 cm_args_counts_representable policy p fid args -> cm_rep_args_temps_safe args /\
 cm_args_temps args <= cm_args_code_count_of (cm_args_code_counts policy p fid args)).
Check (cm_stmt_temps_ready_with_bound : forall policy stmt p fid,
 cm_stmt_counts_representable policy p fid stmt ->
 cm_rep_stmt_temps_safe stmt /\ cm_stemps stmt <= cm_stmt_code_count policy p fid stmt).
Check (cm_stmt_temps_ready_from_counts : forall policy stmt p fid,
 cm_stmt_counts_representable policy p fid stmt -> cm_rep_stmt_temps_safe stmt).
Check (cm_temp_imax_upper : forall x y z, cm_imax x y <= z <-> x <= z /\ y <= z).
Check (cm_temp_imax_add_upper : forall base x y z,
 base + cm_imax x y <= z <-> base + x <= z /\ base + y <= z).
Check (cm_binary_tail_positive : forall p op left right, 1 <= cm_binary_tail_count p op left right).
Check (cm_expr_count_node_from_tree : forall policy e p fid,
 cm_expr_counts_representable policy p fid e -> cm_expr_count_node_representable policy p fid e).
Check (cm_args_count_node_from_tree : forall policy args p fid,
 cm_args_counts_representable policy p fid args ->
 cm_i32_code_count (cm_args_code_count_of (cm_args_code_counts policy p fid args))).
Check (cm_args_temps_safe_pair : forall args, cm_rep_args_temps_safe args -> cm_rep_apair_safe (cm_args_apair args)).
Check (cm_stmt_count_node_from_tree : forall policy stmt p fid,
 cm_stmt_counts_representable policy p fid stmt -> cm_i32_code_count (cm_stmt_code_count policy p fid stmt)).
Check (cm_expr_and_args_temps_ready : forall policy,
 (forall e p fid, cm_expr_counts_representable policy p fid e ->
   cm_rep_expr_temps_safe e /\ cm_ltemps e <= cm_lvalue_code_count policy p fid e /\
   cm_rtemps e <= cm_rvalue_code_count policy p fid e) /\
 (forall args p fid, cm_args_counts_representable policy p fid args ->
   cm_rep_args_temps_safe args /\
   cm_args_temps args <= cm_args_code_count_of (cm_args_code_counts policy p fid args))).
Check (cm_args_temps_ready_cons : forall policy p fid a args,
 (cm_rep_expr_temps_safe a /\ cm_ltemps a <= cm_lvalue_code_count policy p fid a /\
   cm_rtemps a <= cm_rvalue_code_count policy p fid a) ->
 (cm_rep_args_temps_safe args /\
   cm_args_temps args <= cm_args_code_count_of (cm_args_code_counts policy p fid args)) ->
 cm_i32_code_count (cm_args_code_count_of (cm_args_code_counts policy p fid (a::args))) ->
 cm_rep_args_temps_safe (a::args) /\
 cm_args_temps (a::args) <= cm_args_code_count_of (cm_args_code_counts policy p fid (a::args))).
Print Assumptions cm_temp_imax_upper.
Print Assumptions cm_temp_imax_add_upper.
Print Assumptions cm_binary_tail_positive.
Print Assumptions cm_expr_count_node_from_tree.
Print Assumptions cm_args_count_node_from_tree.
Print Assumptions cm_args_temps_safe_pair.
Print Assumptions cm_args_temps_ready_cons.
Print Assumptions cm_expr_temps_ready_from_counts.
Print Assumptions cm_args_temps_ready_from_counts.
Print Assumptions cm_expr_and_args_temps_ready.
Print Assumptions cm_stmt_count_node_from_tree.
Print Assumptions cm_stmt_temps_ready_with_bound.
Print Assumptions cm_stmt_temps_ready_from_counts.
