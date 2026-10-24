From Coq Require Import ZArith List Lia.
From AUXLib Require Import ListLib.
Require Export SimpleC.EE.QCP_demos_human.cmc_code_ready_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_temp_ready_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_emit_stmt_migration_lib.
Import ListNotations.
Local Open Scope Z_scope.

(* Newly needed common support: exact stack_local_syntax prefix/PC steps. *)
Lemma cm_function_prefix_step policy functions p index :
 0 <= index < Zlength functions ->
 cm_function_prefix policy p functions (index+1) =
 cm_function_prefix policy p functions index +
 cm_function_code_count policy p (Zlength (cm_program_functions p)-Zlength functions+index).
Proof.
 revert index. induction functions as [|f functions IH]; intros index Hindex.
 - rewrite Zlength_nil in Hindex. lia.
 - rewrite Zlength_cons in *. cbn [cm_function_prefix].
   destruct (Z.eqb_spec index 0) as [->|Hnz].
   + cbn [Z.eqb]. assert (Hz : cm_function_prefix policy p functions 0 = 0).
     { destruct functions; reflexivity. }
     rewrite !Z.add_0_l, Z.sub_diag. cbn [Z.eqb].
     rewrite Hz, Zlength_cons, !Z.add_0_r. reflexivity.
   + assert (Hnext : (index+1 =? 0)=false) by (apply Z.eqb_neq; lia).
     rewrite Hnext. replace (index+1-1) with index by lia.
     pose proof (IH (index-1) ltac:(lia)) as Hstep.
     replace (index-1+1) with index in Hstep by lia.
     replace (Zlength (cm_program_functions p)-Zlength functions+(index-1))
       with (Zlength (cm_program_functions p)-Z.succ (Zlength functions)+index) in Hstep by lia.
     lia.
Qed.
Lemma cm_function_pc_step policy p fid :
 0 <= fid < Zlength (cm_program_functions p) ->
 cm_function_pc policy p (fid+1) = cm_function_pc policy p fid + cm_function_code_count policy p fid.
Proof.
 intro H. unfold cm_function_pc.
 pose proof (cm_function_prefix_step policy (cm_program_functions p) p fid H) as Hstep.
 replace (Zlength (cm_program_functions p)-Zlength (cm_program_functions p)+fid) with fid in Hstep by lia.
 lia.
Qed.

(* Preserve the source premises with arbitrary existing lookup and codegen parameters. *)
Lemma cm_function_pcs_current policy functions p fid :
 cm_function_pcs_representable policy p functions fid -> cm_i32_code_count (cm_function_pc policy p fid).
Proof. destruct functions; cbn [cm_function_pcs_representable]; tauto. Qed.
Theorem cm_function_id_ready_from_wf policy cg p fid :
 cm_wf_program policy cg p -> 0 <= fid -> fid < Zlength (cm_program_functions p) ->
 cm_i32_code_count (fid+1).
Proof.
 unfold cm_wf_program, cm_codegen_admissible, cm_codegen_counts_representable.
 intros [_ [Hlength [_ [_ [_ [Hcounts Hpcs]]]]]] Hlo Hhi.
 pose proof (cm_functions_length_bound__model_length_bound policy p (cm_program_functions p) 0 Hcounts).
 unfold cm_model_code_length in Hlength. unfold cm_i32_code_count. lia.
Qed.
Theorem cm_concrete_function_ready_from_wf policy cg p fid f :
 cm_wf_program policy cg p -> 0 <= fid -> fid < Zlength (cm_program_functions p) ->
 cm_function_counts_representable policy p fid f ->
 cm_i32_code_count (cm_function_pc policy p fid) ->
 cm_i32_code_count (cm_function_pc policy p (fid+1)) ->
 cm_concrete_function_ready policy p fid f.
Proof.
 intros Hwf Hlo Hhi Hcounts Hpc Hnext.
 pose proof Hcounts as [Hmodel [Hparams [Hprologue [Hstmt Hcode]]]].
 destruct Hwf as [Htyped _].
 destruct Htyped as [_ [_ [_ [Hfunctions _]]]].
 specialize (Hfunctions fid ltac:(lia)). rewrite <- Hmodel in Hfunctions.
 destruct Hfunctions as [_ [Hparamswf [Hlocalswf [Hstmtwf [_ [_ [Htemps Hframe]]]]]]].
 destruct Hparamswf as [Hparamswf _].
 pose proof (cm_stmt_temps_ready_with_bound policy (cm_function_body f) p fid Hstmt) as [Hsafe Hbound].
 pose proof (cm_stmt_code_count_nonnegative policy p fid (cm_function_body f)) as Hnonneg.
 pose proof (cm_function_pc_step policy p fid ltac:(lia)) as Hstep.
 assert (Hcodeview : cm_function_code_count policy p fid =
   cm_function_prologue_count f + cm_stmt_code_count policy p fid (cm_function_body f) + 7).
 { unfold cm_function_code_count. rewrite <- Hmodel. reflexivity. }
 pose proof (cm_slots_size_matches__temp_context _ _ Hparamswf) as Hparamsbridge.
 pose proof (cm_slots_size_matches__temp_context _ _ Hlocalswf) as Hlocalsbridge.
 pose proof (cm_slots_nonnegative _ _ Hparamswf) as Hparamsnonneg.
 pose proof (cm_slots_nonnegative _ _ Hlocalswf) as Hlocalsnonneg.
 unfold cm_frame_size, cm_temp_slots in Hframe, Htemps.
 rewrite <- Hparamsbridge, <- Hlocalsbridge in Hframe.
 assert (Hparamssafe : cm_rep_members_safe (cm_function_params f)).
 { apply (cm_slots_safe _ _ Hparamswf). lia. }
 assert (Hlocalssafe : cm_rep_members_safe (cm_function_locals f)).
 { apply (cm_slots_safe _ _ Hlocalswf). lia. }
 assert (Hoffset : cm_temp_offset policy p fid (cm_stemps (cm_function_body f)) <= 2147483647).
 { unfold cm_temp_offset. rewrite <- Hmodel, <- Hparamsbridge, <- Hlocalsbridge. lia. }
 unfold cm_concrete_function_ready. repeat first [assumption | split];
 unfold cm_i32_code_count in *; intuition lia.
Qed.
Lemma cm_concrete_functions_suffix_ready policy cg functions p fid :
 cm_wf_program policy cg p -> 0 <= fid ->
 fid + Zlength functions = Zlength (cm_program_functions p) ->
 cm_functions_counts_representable policy p functions fid ->
 cm_function_pcs_representable policy p functions fid ->
 cm_concrete_functions_ready policy p fid functions.
Proof.
 revert fid. induction functions as [|f functions IH]; intros fid Hwf Hlo Halign Hcounts Hpcs.
 - exact I.
 - destruct Hcounts as [_ [Hhead Htail]]. destruct Hpcs as [Hcurrent Hpcs].
   pose proof (cm_function_pcs_current policy functions p (fid+1) Hpcs) as Hnext.
   rewrite Zlength_cons in Halign. pose proof (Zlength_nonneg functions).
   cbn [cm_concrete_functions_ready]. split.
   + apply (cm_function_id_ready_from_wf policy cg p fid); assumption || lia.
   + split.
     * apply (cm_concrete_function_ready_from_wf policy cg p fid f); assumption || lia.
     * apply IH; assumption || lia.
Qed.
Theorem cm_concrete_functions_ready_from_wf policy cg p :
 cm_wf_program policy cg p -> cm_concrete_functions_ready policy p 0 (cm_program_functions p).
Proof.
 intro Hwf. pose proof Hwf as [_ [_ [_ [_ [_ Hcounts]]]]].
 destruct Hcounts as [Hcounts Hpcs].
 apply (cm_concrete_functions_suffix_ready policy cg); assumption || lia.
Qed.
