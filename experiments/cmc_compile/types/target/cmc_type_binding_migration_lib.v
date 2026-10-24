Require Export SimpleC.EE.QCP_demos_human.cmc_type_expr_struct_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_source_global_at_valid sp globals i : 0<=i<Zlength globals -> cm_source_global_at sp i globals=cm_global_at i globals.
Proof. intros [L U]; unfold cm_source_global_at,cm_global_at; apply cm_source_at_valid; [exact L|apply nth_error_nth'; rewrite Zlength_correct in U; lia]. Qed.
Lemma cm_source_struct_at_valid sp structs i : 0<=i<Zlength structs -> cm_source_struct_at sp i structs=cm_struct_at i structs.
Proof. intros [L U]; unfold cm_source_struct_at,cm_struct_at; apply cm_source_at_valid; [exact L|apply nth_error_nth'; rewrite Zlength_correct in U; lia]. Qed.
Lemma cm_binding_pointer_type sp p fid scope slot ty st :
 cm_binding_valid p (cm_source_function_at sp fid p) scope slot -> cm_binding_address_ok sp p fid scope slot st=true ->
 cm_value_type (if scope=?0 then cm_global_pointer sp p slot else cm_state_env st scope slot)=cm_lvalue_output_type p (cm_source_function_at sp fid p) (CMVarE scope slot ty).
Proof.
 intros B OK; unfold cm_binding_address_ok in OK; repeat rewrite andb_true_iff in OK; destruct OK as [_ TYPE]; apply cm_type_eqb_spec in TYPE.
 destruct B as [[-> B]|[[-> B]|[-> B]]]; cbn [cm_lvalue_output_type Z.eqb Pos.eqb] in *;
 rewrite ?(cm_source_global_at_valid sp _ _ B),?(cm_source_slot_at_valid sp _ _ B) in TYPE; exact TYPE.
Qed.
Lemma cm_binding_output_array sp p fid scope slot ty :
 cm_function_wf (cm_source_function_policy sp) p (cm_source_function_at sp fid p) -> cm_binding_valid p (cm_source_function_at sp fid p) scope slot ->
 cm_lvalue_output_type p (cm_source_function_at sp fid p) (CMVarE scope slot ty)=
 if cm_binding_array sp p fid scope slot then cm_binding_type p (cm_source_function_at sp fid p) scope slot else CMPtrTy (cm_binding_type p (cm_source_function_at sp fid p) scope slot).
Proof.
 intros [_ [[_ PARAMS] _]] B; destruct B as [[-> B]|[[-> B]|[-> B]]];
 cbv beta iota zeta delta [cm_binding_array cm_binding_type cm_lvalue_output_type Z.eqb Pos.eqb];
 rewrite ?(cm_source_global_at_valid sp _ _ B),?(cm_source_slot_at_valid sp _ _ B);
 unfold cm_global_expr_type,cm_slot_expr_type.
 - destruct (cm_global_count (cm_global_at slot (cm_program_globals p))); reflexivity.
 - destruct (cm_slot_count (cm_slot_at slot (cm_function_locals (cm_source_function_at sp fid p)))) eqn:COUNT; reflexivity.
 - rewrite (PARAMS slot B); reflexivity.
Qed.
Lemma cm_member_output_array sp p base mid : cm_member_valid p base mid ->
 cm_member_lvalue_type p base mid=if cm_member_array sp p base mid then cm_member_type p base mid else CMPtrTy (cm_member_type p base mid).
Proof.
 intros [_ [_ [STRUCT MEMBER]]]; unfold cm_member_array.
 rewrite (cm_source_struct_at_valid sp _ _ STRUCT),(cm_source_slot_at_valid sp _ _ MEMBER).
 unfold cm_member_lvalue_type,cm_member_type,cm_slot_expr_type.
 destruct (cm_slot_count (cm_slot_at mid (cm_struct_members (cm_struct_at (cm_struct_id (cm_pointee base)) (cm_program_structs p))))) eqn:COUNT; reflexivity.
Qed.
