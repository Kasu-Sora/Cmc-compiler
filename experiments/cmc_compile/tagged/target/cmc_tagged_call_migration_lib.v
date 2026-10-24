Require Export SimpleC.EE.QCP_demos_human.cmc_tagged_param_geometry_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_slots_prefix_zero structs slots : cm_slots_prefix structs slots 0=0.
Proof. destruct slots; reflexivity. Qed.
Lemma cm_tagged_span_enter_call sp p fid values st :
 cm_typed_program (cm_source_function_policy sp) p -> cm_call_ok sp p fid values st=true ->
 cm_regions_before (cm_state_regions st) (cm_state_nextgen st) -> cm_tagged_span_valid st ->
 cm_tagged_span_valid (cm_enter_call sp p fid values st).
Proof.
 intros WF OK BEFORE VALID.
 pose proof (cm_call_ok_function_wf _ _ _ _ _ WF OK) as FW.
 pose proof (cm_call_frame_segment _ _ _ _ _ WF OK) as SEG.
 assert (ARITY:Zlength values=Zlength (cm_function_params (cm_source_function_at sp fid p))).
 { unfold cm_call_ok in OK; repeat rewrite andb_true_iff in OK; repeat match goal with H:_ /\ _|-_=>destruct H end; apply Z.eqb_eq; assumption. }
 pose proof (cm_tagged_span_call_base_except _ _ _ _ FW BEFORE VALID) as START.
 pose proof (cm_store_params_tagged_except sp p fid values 0 (cm_call_base_state sp p fid st)
 (fun j=>cm_param_base sp p fid j (cm_state_fp st-cm_frame_size (cm_program_structs p) (cm_source_function_at sp fid p)))
 (cm_state_fp st-cm_frame_size (cm_program_structs p) (cm_source_function_at sp fid p)+8+cm_slots_size (cm_program_structs p) (cm_function_params (cm_source_function_at sp fid p)))) as ITER.
 assert (INIT:cm_tagged_span_except (cm_call_base_state sp p fid st) (cm_param_base sp p fid 0 (cm_state_fp st-cm_frame_size (cm_program_structs p) (cm_source_function_at sp fid p))) (cm_state_fp st-cm_frame_size (cm_program_structs p) (cm_source_function_at sp fid p)+8+cm_slots_size (cm_program_structs p) (cm_function_params (cm_source_function_at sp fid p)))).
 { unfold cm_param_base; rewrite cm_slots_prefix_zero,Z.add_0_r; exact START. }
 specialize (ITER ltac:(intros j J; apply cm_call_param_geometry; [exact FW|exact SEG|rewrite <-ARITY; lia]) INIT).
 rewrite Z.add_0_l,ARITY in ITER; unfold cm_param_base in ITER; rewrite cm_slots_prefix_length in ITER.
 exact (cm_tagged_span_except_empty _ _ ITER).
Qed.
