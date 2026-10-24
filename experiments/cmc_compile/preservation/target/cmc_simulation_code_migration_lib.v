Require Export SimpleC.EE.QCP_demos_human.cmc_simulation_memory_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
(* Exact existential fragment placement from cmc_preservation_layout.c. *)
Definition cm_code_at {A:Type} (code:list A) pc fragment := exists before after, code=before++fragment++after /\ Zlength before=pc.
Lemma cm_code_at_front {A} (fragment tail:list A) : cm_code_at (fragment++tail) 0 fragment.
Proof. exists [],tail; split; reflexivity. Qed.
Lemma cm_code_at_append_left {A} (code lhs rhs:list A) pc : cm_code_at code pc (lhs++rhs) -> cm_code_at code pc lhs.
Proof. intros [before [after [-> H]]]; exists before,(rhs++after); split; [repeat rewrite app_assoc; reflexivity|exact H]. Qed.
Lemma cm_code_at_append_right {A} (code lhs rhs:list A) pc : cm_code_at code pc (lhs++rhs) -> cm_code_at code (pc+Zlength lhs) rhs.
Proof. intros [before [after [-> <-]]]; exists (before++lhs),after; split; [repeat rewrite app_assoc; reflexivity|repeat rewrite Zlength_correct; rewrite app_length,Nat2Z.inj_add; reflexivity]. Qed.
Lemma cm_code_at_bounds {A} (code fragment:list A) pc : cm_code_at code pc fragment -> 0<=pc /\ pc+Zlength fragment<=Zlength code.
Proof. intros [before [after [-> <-]]]; repeat rewrite Zlength_correct; repeat rewrite app_length; lia. Qed.
Lemma cm_code_at_head {A} (code:list A) pc head rest default : cm_code_at code pc (head::rest) ->
 0<=pc<Zlength code /\ nth (Z.to_nat pc) code default=head.
Proof.
 intros [before [after [-> <-]]]; split.
 - repeat rewrite Zlength_correct; repeat rewrite app_length; cbn [length]; lia.
 - rewrite Zlength_correct,Nat2Z.id,app_nth2 by lia; rewrite Nat.sub_diag; reflexivity.
Qed.
Lemma cm_code_at_tail {A} (code:list A) pc head rest : cm_code_at code pc (head::rest) -> cm_code_at code (pc+1) rest.
Proof. change (cm_code_at code pc ([head]++rest) -> cm_code_at code (pc+Zlength [head]) rest). apply cm_code_at_append_right. Qed.
Lemma cm_code_at_weaken_suffix {A} (code fragment suffix:list A) pc : cm_code_at code pc fragment -> cm_code_at (code++suffix) pc fragment.
Proof. intros [before [after [-> H]]]; exists before,(after++suffix); split; [repeat rewrite app_assoc; reflexivity|exact H]. Qed.
Lemma cm_code_at_weaken_prefix {A} (code fragment prefix:list A) pc : cm_code_at code pc fragment -> cm_code_at (prefix++code) (Zlength prefix+pc) fragment.
Proof. intros [before [after [-> <-]]]; exists (prefix++before),after; split; [apply app_assoc|repeat rewrite Zlength_correct; rewrite app_length,Nat2Z.inj_add; reflexivity]. Qed.
Lemma cm_code_at_nested {A} (code fragment inner:list A) pc offset : cm_code_at code pc fragment -> cm_code_at fragment offset inner -> cm_code_at code (pc+offset) inner.
Proof.
 intros [pre [post [-> <-]]] [before [after [-> <-]]]; exists (pre++before),(after++post); split.
 - repeat rewrite app_assoc; reflexivity.
 - repeat rewrite Zlength_correct; rewrite app_length,Nat2Z.inj_add; reflexivity.
Qed.
Lemma cm_tvm_code_step obj st op imm rest : cm_code_at (tvm_object_code obj) (tvm_pc st) (TVMInst op imm::rest) ->
 tvm_step (TVMRunTask obj st)=tvm_action_task obj (tvm_inst_step (tvm_object_code obj) op imm st).
Proof.
 intro H; destruct (cm_code_at_head _ _ _ _ (TVMInst TVMHaltOp 0) H) as [Hv Hi].
 apply tvm_target_validb_spec in Hv; cbn [tvm_step]; rewrite Hv,Hi; reflexivity.
Qed.
Lemma cm_tvm_state_step obj st op imm rest next : cm_code_at (tvm_object_code obj) (tvm_pc st) (TVMInst op imm::rest) ->
 tvm_inst_step (tvm_object_code obj) op imm st=TVMStepState next -> tvm_step (TVMRunTask obj st)=TVMRunTask obj next.
Proof. intros H Hs; rewrite (cm_tvm_code_step _ _ _ _ _ H),Hs; reflexivity. Qed.
Lemma cm_tvm_halt_step obj st op imm rest next status : cm_code_at (tvm_object_code obj) (tvm_pc st) (TVMInst op imm::rest) ->
 tvm_inst_step (tvm_object_code obj) op imm st=TVMStepHalt next status -> tvm_step (TVMRunTask obj st)=TVMDoneTask next status 0.
Proof. intros H Hs; rewrite (cm_tvm_code_step _ _ _ _ _ H),Hs; reflexivity. Qed.
Lemma cm_tvm_push_step obj st imm rest : cm_code_at (tvm_object_code obj) (tvm_pc st) (TVMInst TVMPushOp imm::rest) -> Zlength (tvm_stack st)<65536 ->
 tvm_step (TVMRunTask obj st)=TVMRunTask obj (tvm_next_state st (tower_wrap64 imm::tvm_stack st) (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st)).
Proof. intros H Hcap; eapply cm_tvm_state_step; [exact H|]. cbn [tvm_inst_step]. assert (E:(Zlength (tvm_stack st) <? 65536)=true) by (apply Z.ltb_lt; exact Hcap). rewrite E; reflexivity. Qed.
Lemma cm_tvm_pop_step obj st value stack rest : cm_code_at (tvm_object_code obj) (tvm_pc st) (TVMInst TVMPopOp 0::rest) -> tvm_stack st=value::stack ->
 tvm_step (TVMRunTask obj st)=TVMRunTask obj (tvm_next_state st stack (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st)).
Proof. intros H Hstack; eapply cm_tvm_state_step; [exact H|]. cbn [tvm_inst_step]; rewrite Hstack. assert (E:(1<=?Zlength (value::stack))=true) by (apply Z.leb_le; rewrite Zlength_correct; cbn; lia). rewrite E; reflexivity. Qed.
Lemma cm_tvm_load_step obj st addr stack rest : cm_code_at (tvm_object_code obj) (tvm_pc st) (TVMInst TVMLoadOp 0::rest) -> tvm_stack st=addr::stack -> tower_word_valid addr ->
 tvm_step (TVMRunTask obj st)=TVMRunTask obj (tvm_next_state st (tower_getw (tvm_mem st) addr::stack) (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st)).
Proof. intros H Hstack Hv; eapply cm_tvm_state_step; [exact H|]. cbn [tvm_inst_step]; rewrite Hstack. assert (E:(1<=?Zlength (addr::stack))=true) by (apply Z.leb_le; rewrite Zlength_correct; cbn; lia). rewrite E; cbn [hd andb tl]; apply tower_word_validb_spec in Hv; rewrite Hv; reflexivity. Qed.
Lemma cm_tvm_store_step obj st addr value stack rest : cm_code_at (tvm_object_code obj) (tvm_pc st) (TVMInst TVMStoreOp 0::rest) -> tvm_stack st=addr::value::stack -> tower_word_valid addr ->
 tvm_step (TVMRunTask obj st)=TVMRunTask obj (tvm_next_state st stack (tvm_calls st) (tower_setw (tvm_mem st) addr value) (tvm_input st) (tvm_output st)).
Proof. intros H Hstack Hv; eapply cm_tvm_state_step; [exact H|]. cbn [tvm_inst_step]; rewrite Hstack. assert (E:(2<=?Zlength (addr::value::stack))=true) by (apply Z.leb_le; rewrite Zlength_correct; cbn; lia). rewrite E; cbn [hd andb tl]; apply tower_word_validb_spec in Hv; rewrite Hv; reflexivity. Qed.
