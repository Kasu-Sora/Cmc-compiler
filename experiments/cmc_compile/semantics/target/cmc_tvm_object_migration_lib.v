(* Source: tvm_model.c objects/validity and cmc_rep.c decoding.
   Existing opcode, instruction, byte, AST and code models are reused. *)
Require Export SimpleC.EE.QCP_demos_human.cmc_emit_code_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.

Inductive tvm_patch := TVMPatch (addr byte : Z).
Inductive tvm_object := TVMObject (entry : Z) (code : list tvm_inst) (patches : list tvm_patch).
Definition tvm_patch_addr p := match p with TVMPatch a _ => a end.
Definition tvm_patch_byte p := match p with TVMPatch _ b => b end.
Definition tvm_object_entry o := match o with TVMObject e _ _ => e end.
Definition tvm_object_code o := match o with TVMObject _ c _ => c end.
Definition tvm_object_patches o := match o with TVMObject _ _ p => p end.
Definition tower_signed64 z := -9223372036854775808 <= z <= 9223372036854775807.
Definition tower_byte_value z := 0 <= z < 256.
Definition tower_addr_valid a := 0 <= a < 1048576.
Definition tower_word_valid a := 0 <= a /\ a+7 < 1048576.
Definition tower_signed64b z := (-9223372036854775808 <=? z) && (z <=? 9223372036854775807).
Definition tower_byte_valueb z := (0 <=? z) && (z <? 256).
Definition tower_addr_validb a := (0 <=? a) && (a <? 1048576).
Definition tower_word_validb a := (0 <=? a) && (a+7 <? 1048576).
Lemma tower_signed64b_spec z : tower_signed64b z = true <-> tower_signed64 z.
Proof. unfold tower_signed64b, tower_signed64. rewrite andb_true_iff, !Z.leb_le. tauto. Qed.
Lemma tower_byte_valueb_spec z : tower_byte_valueb z = true <-> tower_byte_value z.
Proof. unfold tower_byte_valueb, tower_byte_value. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. Qed.
Lemma tower_addr_validb_spec z : tower_addr_validb z = true <-> tower_addr_valid z.
Proof. unfold tower_addr_validb, tower_addr_valid. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. Qed.
Lemma tower_word_validb_spec z : tower_word_validb z = true <-> tower_word_valid z.
Proof. unfold tower_word_validb, tower_word_valid. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. Qed.

Definition tvm_opcode_decode (c:Z) : tvm_opcode :=
 if c =? 0 then TVMPushOp else if c =? 1 then TVMPopOp else
 if c =? 2 then TVMDupOp else if c =? 3 then TVMSwapOp else
 if c =? 4 then TVMLoadOp else if c =? 5 then TVMStoreOp else
 if c =? 6 then TVMLoadBOp else if c =? 7 then TVMStoreBOp else
 if c =? 8 then TVMAddOp else if c =? 9 then TVMSubOp else
 if c =? 10 then TVMMulOp else if c =? 11 then TVMDivOp else
 if c =? 12 then TVMModOp else if c =? 13 then TVMEqOp else
 if c =? 14 then TVMNeOp else if c =? 15 then TVMLtOp else
 if c =? 16 then TVMLeOp else if c =? 17 then TVMGtOp else
 if c =? 18 then TVMGeOp else if c =? 19 then TVMJmpOp else
 if c =? 20 then TVMJzOp else if c =? 21 then TVMJnzOp else
 if c =? 22 then TVMCallOp else if c =? 23 then TVMRetOp else
 if c =? 24 then TVMGetcOp else if c =? 25 then TVMPutcOp else
 if c =? 26 then TVMPutiOp else TVMHaltOp.
Lemma tvm_opcode_roundtrip op : tvm_opcode_decode (tvm_opcode_code op) = op.
Proof. destruct op; reflexivity. Qed.
Definition tvm_decode_pair op imm := TVMInst (tvm_opcode_decode op) imm.
Definition tvm_opcode_has_imm op :=
 match op with TVMPushOp | TVMJmpOp | TVMJzOp | TVMJnzOp | TVMCallOp => true | _ => false end.
Definition tvm_opcode_is_target op :=
 match op with TVMJmpOp | TVMJzOp | TVMJnzOp | TVMCallOp => true | _ => false end.
Definition tvm_inst_shape i :=
 if tvm_opcode_has_imm (tvm_inst_op i) then tower_signed64 (tvm_inst_imm i)
 else tvm_inst_imm i = 0.
Definition tvm_inst_shapeb i :=
 if tvm_opcode_has_imm (tvm_inst_op i) then tower_signed64b (tvm_inst_imm i)
 else tvm_inst_imm i =? 0.
Definition tvm_patch_valid p := tower_addr_valid (tvm_patch_addr p) /\ tower_byte_value (tvm_patch_byte p).
Definition tvm_patch_validb p := tower_addr_validb (tvm_patch_addr p) && tower_byte_valueb (tvm_patch_byte p).
Definition tvm_target_valid (code:list tvm_inst) target := 0 <= target < Zlength code.
Definition tvm_target_validb (code:list tvm_inst) target := (0 <=? target) && (target <? Zlength code).
Definition tvm_code_shape code := Forall tvm_inst_shape code.
Definition tvm_patches_valid patches := Forall tvm_patch_valid patches.
Definition tvm_targets_valid code := Forall (fun i => tvm_opcode_is_target (tvm_inst_op i) = true -> tvm_target_valid code (tvm_inst_imm i)) code.
Definition tvm_load_ok obj := tvm_patches_valid (tvm_object_patches obj) /\ tvm_code_shape (tvm_object_code obj).
Definition tvm_load_okb obj := forallb tvm_patch_validb (tvm_object_patches obj) && forallb tvm_inst_shapeb (tvm_object_code obj).
Definition tvm_object_wf obj := tvm_load_ok obj /\ tvm_target_valid (tvm_object_code obj) (tvm_object_entry obj) /\ tvm_targets_valid (tvm_object_code obj).
Definition tvm_decode_pair_valid op imm := 0 <= op < 28 /\ tvm_inst_shape (tvm_decode_pair op imm).
Lemma tvm_inst_shapeb_spec i : tvm_inst_shapeb i = true <-> tvm_inst_shape i.
Proof. unfold tvm_inst_shapeb, tvm_inst_shape. destruct (tvm_opcode_has_imm (tvm_inst_op i)); [apply tower_signed64b_spec|apply Z.eqb_eq]. Qed.
Lemma tvm_patch_validb_spec p : tvm_patch_validb p = true <-> tvm_patch_valid p.
Proof. unfold tvm_patch_validb, tvm_patch_valid. rewrite andb_true_iff, tower_addr_validb_spec, tower_byte_valueb_spec. tauto. Qed.
Lemma tvm_target_validb_spec c t : tvm_target_validb c t = true <-> tvm_target_valid c t.
Proof. unfold tvm_target_validb, tvm_target_valid. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. Qed.
Lemma forallb_Forall_bridge {A} (f:A->bool) (P:A->Prop) xs :
 (forall x, f x = true <-> P x) -> (forallb f xs = true <-> Forall P xs).
Proof. intro H. induction xs; simpl; [split; constructor|]. rewrite andb_true_iff, H, IHxs. split; [intros [? ?]; constructor; assumption|intro F; inversion F; auto]. Qed.
Lemma tvm_load_okb_spec obj : tvm_load_okb obj = true <-> tvm_load_ok obj.
Proof. unfold tvm_load_okb, tvm_load_ok, tvm_patches_valid, tvm_code_shape. rewrite andb_true_iff, (forallb_Forall_bridge _ _ _ tvm_patch_validb_spec), (forallb_Forall_bridge _ _ _ tvm_inst_shapeb_spec). tauto. Qed.
(* HOL inth is only observed under its in-bounds guard in these predicates.
   The theorem below holds for ANY default, avoiding a new malformed-input premise. *)
Lemma Forall_index_Z {A} (P:A->Prop) (d:A) xs :
 Forall P xs <-> forall i:Z, 0 <= i -> i < Zlength xs -> P (nth (Z.to_nat i) xs d).
Proof.
 rewrite Forall_forall. split.
 - intros H i Hi Hlen. apply H. apply nth_In. rewrite Zlength_correct in Hlen.
   apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. exact Hlen.
 - intros H x Hx. apply In_nth with (d:=d) in Hx. destruct Hx as [n [Hn Heq]].
   specialize (H (Z.of_nat n)). rewrite Nat2Z.id in H. rewrite <- Heq.
   apply H; [lia|rewrite Zlength_correct; lia].
Qed.
Lemma tvm_code_shape_source code d : tvm_code_shape code <->
 forall i, 0 <= i -> i < Zlength code -> tvm_inst_shape (nth (Z.to_nat i) code d).
Proof. apply Forall_index_Z. Qed.
Lemma tvm_patches_valid_source patches d : tvm_patches_valid patches <->
 forall i, 0 <= i -> i < Zlength patches -> tvm_patch_valid (nth (Z.to_nat i) patches d).
Proof. apply Forall_index_Z. Qed.
Lemma tvm_targets_valid_source code d : tvm_targets_valid code <->
 forall i, 0 <= i -> i < Zlength code ->
 tvm_opcode_is_target (tvm_inst_op (nth (Z.to_nat i) code d)) = true ->
 tvm_target_valid code (tvm_inst_imm (nth (Z.to_nat i) code d)).
Proof. unfold tvm_targets_valid. exact (Forall_index_Z (fun inst => tvm_opcode_is_target (tvm_inst_op inst) = true -> tvm_target_valid code (tvm_inst_imm inst)) d code). Qed.

Fixpoint cm_bytes_patches (bytes:list Z) (addr:Z) : list tvm_patch :=
 match bytes with [] => [] | b::bs => TVMPatch addr b :: cm_bytes_patches bs (addr+1) end.
Definition cm_model_patches p := cm_bytes_patches (cm_model_data_bytes p) 8.
Definition cm_compile_model policy p := TVMObject 0 (cm_model_code policy p) (cm_model_patches p).
Fixpoint cm_decode_pairs (ops imms:list Z) : list tvm_inst :=
 match ops,imms with op::os,imm::is_ => tvm_decode_pair op imm :: cm_decode_pairs os is_ | _,_ => [] end.
Definition cm_output_decodes entry ops imms data obj :=
 (exists code, tvm_code_shape code /\ ops=cm_rep_ops code /\ imms=cm_rep_imms code) /\
 obj=TVMObject entry (cm_decode_pairs ops imms) (cm_bytes_patches data 8).
Definition cm_source_codegen_obligations policy : cm_codegen_obligations :=
 CMCodegenObligations
 (fun p => tvm_code_shape (cm_model_code policy p))
 (fun p => tvm_targets_valid (cm_model_code policy p))
 (fun p => tvm_patches_valid (cm_model_patches p))
 (fun p => tvm_target_valid (cm_model_code policy p) 0).
Definition cm_semantic_wf_program policy := cm_wf_program policy (cm_source_codegen_obligations policy).
Lemma cm_source_codegen_fields policy p :
 cm_codegen_fields_representable (cm_source_codegen_obligations policy) p <->
 tvm_code_shape (cm_model_code policy p) /\ tvm_targets_valid (cm_model_code policy p) /\
 tvm_patches_valid (cm_model_patches p) /\ tvm_target_valid (cm_model_code policy p) 0.
Proof. reflexivity. Qed.
Lemma cm_decode_pairs_rep code : cm_decode_pairs (cm_rep_ops code) (cm_rep_imms code) = code.
Proof. induction code as [|[op imm] rest IH]; [reflexivity|]. cbn [cm_rep_ops cm_rep_imms map cm_decode_pairs tvm_inst_op tvm_inst_imm tvm_decode_pair] in *. unfold tvm_decode_pair. rewrite tvm_opcode_roundtrip. fold (cm_rep_ops rest) (cm_rep_imms rest). rewrite IH. reflexivity. Qed.
Lemma cm_output_decode_unique entry ops imms data obj1 obj2 :
 cm_output_decodes entry ops imms data obj1 -> cm_output_decodes entry ops imms data obj2 -> obj1=obj2.
Proof. intros [_ H1] [_ H2]. congruence. Qed.
Lemma cm_model_output_decodes policy p : cm_semantic_wf_program policy p ->
 cm_output_decodes 0 (cm_rep_ops (cm_model_code policy p)) (cm_rep_imms (cm_model_code policy p)) (cm_model_data_bytes p) (cm_compile_model policy p).
Proof.
 intros H. unfold cm_semantic_wf_program, cm_wf_program, cm_codegen_admissible in H.
 destruct H as [_ [_ [_ [_ [Hfields _]]]]].
 unfold cm_codegen_fields_representable, cm_source_codegen_obligations in Hfields; cbn in Hfields.
 split; [exists (cm_model_code policy p); tauto|].
 unfold cm_compile_model, cm_model_patches. rewrite cm_decode_pairs_rep. reflexivity.
Qed.
Lemma cm_compile_model_wf policy p : cm_semantic_wf_program policy p -> tvm_object_wf (cm_compile_model policy p).
Proof.
 intros H. unfold cm_semantic_wf_program, cm_wf_program, cm_codegen_admissible in H.
 destruct H as [_ [_ [_ [_ [Hfields _]]]]].
 unfold cm_codegen_fields_representable, cm_source_codegen_obligations in Hfields; cbn in Hfields.
 unfold tvm_object_wf, tvm_load_ok, cm_compile_model; cbn. tauto.
Qed.
Lemma cm_decoded_model_unique policy p obj : cm_semantic_wf_program policy p ->
 cm_output_decodes 0 (cm_rep_ops (cm_model_code policy p)) (cm_rep_imms (cm_model_code policy p)) (cm_model_data_bytes p) obj -> obj=cm_compile_model policy p.
Proof. intros Hwf Hdec. eapply cm_output_decode_unique; [exact Hdec|apply cm_model_output_decodes; exact Hwf]. Qed.
