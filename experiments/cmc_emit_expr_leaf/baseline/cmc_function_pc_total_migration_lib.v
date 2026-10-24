From Coq Require Import ZArith List Bool Lia.
From AUXLib Require Import ListLib.
Require Export SimpleC.EE.QCP_demos_human.cmc_counts_migration_lib.
Import ListNotations.
Local Open Scope Z_scope.

(* Source cmc_codegen.c:620-629; use the same total lookup policy as counts. *)
Definition cm_temp_offset policy p fid temp :=
  let f := cm_function_at policy fid (cm_program_functions p) in
  8 + cm_slots_size (cm_program_structs p) (cm_function_params f) +
  cm_slots_size (cm_program_structs p) (cm_function_locals f) + 8 * temp.

(* Complete source cmc_concrete_counts.c:5444-5480. The emitted statement
   length conjunct is normalized using the unconditional source theorem
   cm_stmt_code_length (cmc_codegen.c:1460-1487), exactly as used by
   cmc_concrete_function_ready.c:217-234. This is a source-proved translation
   normalization, not a Rocq proof of the full emitter semantics. *)
Definition cm_concrete_function_ready policy p fid f : Prop :=
  f = cm_function_at policy fid (cm_program_functions p) /\
  cm_function_counts_representable policy p fid f /\
  cm_stmt_wf policy p f false (cm_function_body f) /\
  cm_stmt_counts_representable policy p fid (cm_function_body f) /\
  cm_param_counts_representable (cm_function_params f) /\
  cm_i32_code_count (cm_function_prologue_count f) /\
  cm_i32_code_count (cm_function_pc policy p fid) /\
  cm_i32_code_count (cm_function_pc policy p fid + cm_function_prologue_count f) /\
  cm_i32_code_count ((cm_function_pc policy p fid + cm_function_prologue_count f) +
    cm_stmt_code_count policy p fid (cm_function_body f)) /\
  cm_slots_wf (cm_program_structs p) (cm_function_params f) /\
  cm_slots_wf (cm_program_structs p) (cm_function_locals f) /\
  cm_rep_members_safe (cm_function_params f) /\
  cm_rep_members_safe (cm_function_locals f) /\
  cm_rep_stmt_temps_safe (cm_function_body f) /\
  8 + cm_rep_members_size (cm_function_params f) +
    cm_rep_members_size (cm_function_locals f) +
    8 * cm_stemps (cm_function_body f) <= 2147483647 /\
  cm_temp_offset policy p fid (cm_stemps (cm_function_body f)) <= 2147483647 /\
  cm_function_pc policy p (fid + 1) =
    cm_function_pc policy p fid + cm_function_code_count policy p fid /\
  cm_i32_code_count (cm_function_pc policy p (fid + 1)).

Fixpoint cm_concrete_functions_ready policy p fid functions : Prop :=
  match functions with
  | [] => True
  | f :: rest => cm_i32_code_count (fid + 1) /\
      cm_concrete_function_ready policy p fid f /\
      cm_concrete_functions_ready policy p (fid + 1) rest
  end.
Definition cm_concrete_structs_ready p := cm_rep_structs_safe (cm_program_structs p).
Definition cm_concrete_code_ready policy p := cm_concrete_structs_ready p /\
  cm_concrete_functions_ready policy p 0 (cm_program_functions p).

Lemma cm_char_normalize_count_nonnegative t : 0 <= cm_char_normalize_count t.
Proof. destruct t; cbn [cm_char_normalize_count]; lia. Qed.
Lemma cm_binding_address_count_nonnegative scope : 0 <= cm_binding_address_count scope.
Proof. unfold cm_binding_address_count. destruct (Z.eqb scope 0); lia. Qed.
Lemma cm_binary_tail_count_nonnegative p op left right :
  0 <= cm_binary_tail_count p op left right.
Proof.
  unfold cm_binary_tail_count.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia.
Qed.

Lemma cm_expr_code_counts_nonnegative policy p fid : forall e,
  0 <= cm_lcount_of (cm_expr_code_counts policy p fid e) /\
  0 <= cm_rcount_of (cm_expr_code_counts policy p fid e).
Proof.
  fix IH 1. intro e.
  destruct e as [n ty|sid ty|scope slot ty|a b ty|op a b ty|op a ty|
    a b ty|a mid ty|callee args ty|asked ty|ty|a ty|a ty|a ty].
  all: try pose proof (IH a) as Ha.
  all: try pose proof (IH b) as Hb.
  all: cbn [cm_expr_code_counts cm_lcount_of cm_rcount_of].
  all: try solve [split; lia].
  - pose proof (cm_binding_address_count_nonnegative scope).
    destruct (Z.eqb (cm_binding_array_code policy p fid scope slot) 0); split; lia.
  - pose proof (cm_char_normalize_count_nonnegative ty). split; lia.
  - pose proof (cm_binary_tail_count_nonnegative p op a b).
    destruct ((Z.eqb op 0 || Z.eqb op 1)%bool); split; lia.
  - destruct (Z.eqb op 2); cbn [cm_lcount_of cm_rcount_of]; [split; lia|].
    destruct (Z.eqb op 3); cbn [cm_lcount_of cm_rcount_of]; split; lia.
  - destruct (Z.eqb (cm_member_array_code p (cm_expr_type a) mid) 0); split; lia.
  - split; [lia|]. induction args as [|a rest Hrest].
    + cbn. lia.
    + cbn [cm_args_code_count_of]. pose proof (IH a). lia.
Qed.

Lemma cm_stmt_code_count_nonnegative policy p fid s :
  0 <= cm_stmt_code_count policy p fid s.
Proof.
  induction s; cbn [cm_stmt_code_count].
  all: try match goal with e : cm_expr |- _ =>
    pose proof (cm_expr_code_counts_nonnegative policy p fid e) end.
  all: unfold cm_rvalue_code_count in *.
  all: repeat match goal with |- context [cm_char_normalize_count ?t] =>
    let H := fresh in pose proof (cm_char_normalize_count_nonnegative t) as H;
    remember (cm_char_normalize_count t) as normalization in * end.
  all: lia.
Qed.
Lemma cm_function_code_count_nonnegative policy p fid :
  0 <= cm_function_code_count policy p fid.
Proof.
  unfold cm_function_code_count, cm_function_prologue_count.
  pose proof (cm_param_count_nonnegative__model_length_bound
    (cm_function_params (cm_function_at policy fid (cm_program_functions p)))).
  pose proof (cm_stmt_code_count_nonnegative policy p fid
    (cm_function_body (cm_function_at policy fid (cm_program_functions p)))). lia.
Qed.
Lemma cm_functions_code_size_nonnegative policy p functions : forall fid,
  0 <= cm_functions_code_size policy p functions fid.
Proof.
  induction functions as [|f rest IH]; intro fid; cbn [cm_functions_code_size]; [lia|].
  pose proof (cm_function_code_count_nonnegative policy p fid).
  pose proof (IH (fid + 1)). lia.
Qed.

(* The exported source statement has no readiness, validity or remaining bound. *)
Lemma cm_function_prefix_total_bounds policy functions p remaining :
  0 <= cm_function_prefix policy p functions remaining /\
  cm_function_prefix policy p functions remaining <=
    cm_functions_code_size policy p functions
      (Zlength (cm_program_functions p) - Zlength functions).
Proof.
  revert remaining. induction functions as [|f rest IH]; intro remaining.
  - cbn [cm_function_prefix cm_functions_code_size]. lia.
  - cbn [cm_function_prefix cm_functions_code_size].
    pose proof (cm_function_code_count_nonnegative policy p
      (Zlength (cm_program_functions p) - Zlength (f :: rest))) as Hhead.
    pose proof (cm_functions_code_size_nonnegative policy p rest
      (Zlength (cm_program_functions p) - Zlength (f :: rest) + 1)) as Htail.
    specialize (IH (remaining - 1)).
    rewrite Zlength_cons in *.
    replace (Zlength (cm_program_functions p) - Z.succ (Zlength rest) + 1)
      with (Zlength (cm_program_functions p) - Zlength rest) in * by lia.
    destruct (Z.eqb remaining 0); lia.
Qed.
