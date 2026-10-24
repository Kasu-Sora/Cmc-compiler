(* Concrete TVM operational semantics from tvm_model.c. *)
Require Export SimpleC.EE.QCP_demos_human.cmc_tower_semantics_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Inductive tvm_state := TVMState (pc:Z) (stack calls:list Z) (mem:Z->Z) (input output:list Z).
Inductive tvm_action := TVMStepState (st:tvm_state) | TVMStepHalt (st:tvm_state) (status:Z) | TVMStepError (st:tvm_state).
Inductive tvm_task := TVMBoot (obj:tvm_object) (input:list Z) | TVMRunTask (obj:tvm_object) (st:tvm_state) | TVMDoneTask (st:tvm_state) (status kind:Z).
Inductive tvm_outcome := TVMOutcome (st:tvm_state) (status kind:Z).
Definition tvm_pc st := match st with TVMState pc _ _ _ _ _ => pc end.
Definition tvm_stack st := match st with TVMState _ s _ _ _ _ => s end.
Definition tvm_calls st := match st with TVMState _ _ s _ _ _ => s end.
Definition tvm_mem st := match st with TVMState _ _ _ m _ _ => m end.
Definition tvm_input st := match st with TVMState _ _ _ _ s _ => s end.
Definition tvm_output st := match st with TVMState _ _ _ _ _ s => s end.
Definition tvm_outcome_state out := match out with TVMOutcome s _ _ => s end.
Definition tvm_outcome_status out := match out with TVMOutcome _ s _ => s end.
Definition tvm_outcome_kind out := match out with TVMOutcome _ _ k => k end.
Fixpoint tvm_apply_patches (patches:list tvm_patch) (mem:Z->Z) : Z->Z :=
 match patches with [] => mem | p::ps => tvm_apply_patches ps (tower_setb mem (tvm_patch_addr p) (tvm_patch_byte p)) end.
Definition tvm_initial_state obj input := TVMState (tvm_object_entry obj) [] [] (tvm_apply_patches (tvm_object_patches obj) tower_zero_mem) input [].
Definition tvm_unloaded_state obj input := TVMState (tvm_object_entry obj) [] [] tower_zero_mem input [].
Definition tvm_valid_input input := Forall tower_byte_value input.
Definition tvm_next_state st stack calls mem input output := TVMState (tvm_pc st+1) stack calls mem input output.
Definition tvm_jump_state (st:tvm_state) target stack calls mem input output := TVMState target stack calls mem input output.
Definition list_empty {A} (xs:list A) := match xs with [] => true | _ => false end.
Definition tvm_inst_step (code:list tvm_inst) (op:tvm_opcode) (imm:Z) (st:tvm_state) : tvm_action :=
 match op with
 | TVMPushOp => (if (Zlength (tvm_stack st) <? 65536)
        then TVMStepState
          (tvm_next_state st
            ((tower_wrap64 imm) :: tvm_stack st)
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMPopOp => (if (1 <=? Zlength (tvm_stack st))
        then TVMStepState
          (tvm_next_state st (tl (tvm_stack st))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMDupOp => (if (1 <=? Zlength (tvm_stack st)) &&
           (Zlength (tvm_stack st) <? 65536)
        then TVMStepState
          (tvm_next_state st
            (hd 0 (tvm_stack st) :: tvm_stack st)
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMSwapOp => (if (2 <=? Zlength (tvm_stack st))
        then TVMStepState
          (tvm_next_state st
            (hd 0 (tl (tvm_stack st)) :: hd 0 (tvm_stack st) ::
              tl (tl (tvm_stack st)))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMLoadOp => (if (1 <=? Zlength (tvm_stack st)) &&
           tower_word_validb (hd 0 (tvm_stack st))
        then TVMStepState
          (tvm_next_state st
            (tower_getw (tvm_mem st) (hd 0 (tvm_stack st)) ::
              tl (tvm_stack st))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMStoreOp => (if (2 <=? Zlength (tvm_stack st)) &&
           tower_word_validb (hd 0 (tvm_stack st))
        then TVMStepState
          (tvm_next_state st (tl (tl (tvm_stack st)))
            (tvm_calls st)
            (tower_setw (tvm_mem st) (hd 0 (tvm_stack st))
              (hd 0 (tl (tvm_stack st))))
            (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMLoadBOp => (if (1 <=? Zlength (tvm_stack st)) &&
           tower_addr_validb (hd 0 (tvm_stack st))
        then TVMStepState
          (tvm_next_state st
            (tower_getb (tvm_mem st) (hd 0 (tvm_stack st)) ::
              tl (tvm_stack st))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMStoreBOp => (if (2 <=? Zlength (tvm_stack st)) &&
           tower_addr_validb (hd 0 (tvm_stack st))
        then TVMStepState
          (tvm_next_state st (tl (tl (tvm_stack st)))
            (tvm_calls st)
            (tower_setb (tvm_mem st) (hd 0 (tvm_stack st))
              (hd 0 (tl (tvm_stack st))))
            (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMAddOp => (if (2 <=? Zlength (tvm_stack st))
        then TVMStepState
          (tvm_next_state st
            (tower_add (hd 0 (tl (tvm_stack st))) (hd 0 (tvm_stack st)) ::
              tl (tl (tvm_stack st)))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMSubOp => (if (2 <=? Zlength (tvm_stack st))
        then TVMStepState
          (tvm_next_state st
            (tower_sub (hd 0 (tl (tvm_stack st))) (hd 0 (tvm_stack st)) ::
              tl (tl (tvm_stack st)))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMMulOp => (if (2 <=? Zlength (tvm_stack st))
        then TVMStepState
          (tvm_next_state st
            (tower_mul (hd 0 (tl (tvm_stack st))) (hd 0 (tvm_stack st)) ::
              tl (tl (tvm_stack st)))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMDivOp => (if (2 <=? Zlength (tvm_stack st)) &&
           negb ((hd 0 (tvm_stack st) =? 0))
        then TVMStepState
          (tvm_next_state st
            (tower_div (hd 0 (tl (tvm_stack st))) (hd 0 (tvm_stack st)) ::
              tl (tl (tvm_stack st)))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMModOp => (if (2 <=? Zlength (tvm_stack st)) &&
           negb ((hd 0 (tvm_stack st) =? 0))
        then TVMStepState
          (tvm_next_state st
            (tower_mod (hd 0 (tl (tvm_stack st))) (hd 0 (tvm_stack st)) ::
              tl (tl (tvm_stack st)))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMEqOp => (if (2 <=? Zlength (tvm_stack st))
        then TVMStepState
          (tvm_next_state st
            (tower_bool
              ((hd 0 (tl (tvm_stack st)) =? hd 0 (tvm_stack st))) ::
              tl (tl (tvm_stack st)))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMNeOp => (if (2 <=? Zlength (tvm_stack st))
        then TVMStepState
          (tvm_next_state st
            (tower_bool
              (negb ((hd 0 (tl (tvm_stack st)) =? hd 0 (tvm_stack st)))) ::
              tl (tl (tvm_stack st)))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMLtOp => (if (2 <=? Zlength (tvm_stack st))
        then TVMStepState
          (tvm_next_state st
            (tower_bool
              ((hd 0 (tl (tvm_stack st)) <? hd 0 (tvm_stack st))) ::
              tl (tl (tvm_stack st)))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMLeOp => (if (2 <=? Zlength (tvm_stack st))
        then TVMStepState
          (tvm_next_state st
            (tower_bool
              ((hd 0 (tl (tvm_stack st)) <=? hd 0 (tvm_stack st))) ::
              tl (tl (tvm_stack st)))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMGtOp => (if (2 <=? Zlength (tvm_stack st))
        then TVMStepState
          (tvm_next_state st
            (tower_bool
              ((hd 0 (tvm_stack st) <? hd 0 (tl (tvm_stack st)))) ::
              tl (tl (tvm_stack st)))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMGeOp => (if (2 <=? Zlength (tvm_stack st))
        then TVMStepState
          (tvm_next_state st
            (tower_bool
              ((hd 0 (tvm_stack st) <=? hd 0 (tl (tvm_stack st)))) ::
              tl (tl (tvm_stack st)))
            (tvm_calls st) (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMJmpOp => (if tvm_target_validb code imm
        then TVMStepState
          (tvm_jump_state st imm (tvm_stack st) (tvm_calls st)
            (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMJzOp => (if (1 <=? Zlength (tvm_stack st))
        then if (hd 0 (tvm_stack st) =? 0)
             then if tvm_target_validb code imm
                  then TVMStepState
                    (tvm_jump_state st imm (tl (tvm_stack st))
                      (tvm_calls st) (tvm_mem st) (tvm_input st)
                      (tvm_output st))
                  else TVMStepError st
             else TVMStepState
               (tvm_next_state st (tl (tvm_stack st))
                 (tvm_calls st) (tvm_mem st) (tvm_input st)
                 (tvm_output st))
        else TVMStepError st)
 | TVMJnzOp => (if (1 <=? Zlength (tvm_stack st))
        then if negb ((hd 0 (tvm_stack st) =? 0))
             then if tvm_target_validb code imm
                  then TVMStepState
                    (tvm_jump_state st imm (tl (tvm_stack st))
                      (tvm_calls st) (tvm_mem st) (tvm_input st)
                      (tvm_output st))
                  else TVMStepError st
             else TVMStepState
               (tvm_next_state st (tl (tvm_stack st))
                 (tvm_calls st) (tvm_mem st) (tvm_input st)
                 (tvm_output st))
        else TVMStepError st)
 | TVMCallOp => (if tvm_target_validb code imm &&
           (Zlength (tvm_calls st) <? 65536)
        then TVMStepState
          (tvm_jump_state st imm (tvm_stack st)
            ((tvm_pc st + 1) :: tvm_calls st)
            (tvm_mem st) (tvm_input st) (tvm_output st))
        else TVMStepError st)
 | TVMRetOp => (if (1 <=? Zlength (tvm_calls st))
        then TVMStepState
          (tvm_jump_state st (hd 0 (tvm_calls st)) (tvm_stack st)
            (tl (tvm_calls st)) (tvm_mem st) (tvm_input st)
            (tvm_output st))
        else TVMStepError st)
 | TVMGetcOp => (if (Zlength (tvm_stack st) <? 65536)
        then if list_empty (tvm_input st)
             then TVMStepState
               (tvm_next_state st ((-1) :: tvm_stack st)
                 (tvm_calls st) (tvm_mem st) (tvm_input st)
                 (tvm_output st))
             else TVMStepState
               (tvm_next_state st
                 (tower_u8 (hd 0 (tvm_input st)) :: tvm_stack st)
                 (tvm_calls st) (tvm_mem st) (tl (tvm_input st))
                 (tvm_output st))
        else TVMStepError st)
 | TVMPutcOp => (if (1 <=? Zlength (tvm_stack st))
        then TVMStepState
          (tvm_next_state st (tl (tvm_stack st))
            (tvm_calls st) (tvm_mem st) (tvm_input st)
            (tvm_output st ++ [tower_u8 (hd 0 (tvm_stack st))]))
        else TVMStepError st)
 | TVMPutiOp => (if (1 <=? Zlength (tvm_stack st))
        then TVMStepState
          (tvm_next_state st (tl (tvm_stack st))
            (tvm_calls st) (tvm_mem st) (tvm_input st)
            (tvm_output st ++ tower_decimal (hd 0 (tvm_stack st))))
        else TVMStepError st)
 | TVMHaltOp => (if (1 <=? Zlength (tvm_stack st)) &&
           tower_byte_valueb (hd 0 (tvm_stack st))
        then TVMStepHalt
          (TVMState (tvm_pc st) (tl (tvm_stack st)) (tvm_calls st)
            (tvm_mem st) (tvm_input st) (tvm_output st))
          (hd 0 (tvm_stack st))
        else TVMStepError st)
 end.
Definition tvm_action_task obj action := match action with
 | TVMStepState st => TVMRunTask obj st
 | TVMStepHalt st status => TVMDoneTask st status 0
 | TVMStepError st => TVMDoneTask st 2 1 end.
Definition tvm_step task := match task with
 | TVMBoot obj input => if tvm_load_okb obj then TVMRunTask obj (tvm_initial_state obj input)
                       else TVMDoneTask (tvm_unloaded_state obj input) 3 2
 | TVMRunTask obj st => if tvm_target_validb (tvm_object_code obj) (tvm_pc st) then
   let i := nth (Z.to_nat (tvm_pc st)) (tvm_object_code obj) (TVMInst TVMHaltOp 0) in
   tvm_action_task obj (tvm_inst_step (tvm_object_code obj) (tvm_inst_op i) (tvm_inst_imm i) st)
   else TVMDoneTask st 2 1
 | TVMDoneTask st status kind => TVMDoneTask st status kind end.
Definition tvm_task_done task := match task with TVMDoneTask _ _ _ => true | _ => false end.
Definition tvm_task_outcome task := match task with
 | TVMBoot obj input => TVMOutcome (tvm_unloaded_state obj input) 3 2
 | TVMRunTask _ st => TVMOutcome st 2 1
 | TVMDoneTask st status kind => TVMOutcome st status kind end.
Fixpoint tvm_iter (n:nat) task := match n with O => task | S k => tvm_iter k (tvm_step task) end.
Definition tvm_exec task out := exists (n:nat) st status kind,
 tvm_iter n task = TVMDoneTask st status kind /\ out=TVMOutcome st status kind.
Definition tvm_terminates obj input output status := tvm_valid_input input /\ tower_byte_value status /\
 exists st, tvm_exec (TVMBoot obj input) (TVMOutcome st status 0) /\ tvm_output st=output.
Definition tvm_errors obj input output := tvm_valid_input input /\
 exists st, tvm_exec (TVMBoot obj input) (TVMOutcome st 2 1) /\ tvm_output st=output.
Definition tvm_malformed obj input := exists st, tvm_exec (TVMBoot obj input) (TVMOutcome st 3 2).

Lemma tvm_step_deterministic task n1 n2 : tvm_step task=n1 -> tvm_step task=n2 -> n1=n2.
Proof. congruence. Qed.
Lemma tvm_boot_valid obj input : tvm_load_ok obj -> tvm_step (TVMBoot obj input)=TVMRunTask obj (tvm_initial_state obj input).
Proof. intro H. apply tvm_load_okb_spec in H. cbn [tvm_step]. rewrite H. reflexivity. Qed.
Lemma tvm_boot_malformed obj input : ~tvm_load_ok obj -> tvm_step (TVMBoot obj input)=TVMDoneTask (tvm_unloaded_state obj input) 3 2.
Proof. intro H. cbn [tvm_step]. destruct (tvm_load_okb obj) eqn:E; [apply tvm_load_okb_spec in E; contradiction|reflexivity]. Qed.
Lemma tvm_pc_error obj st : ~tvm_target_valid (tvm_object_code obj) (tvm_pc st) -> tvm_step (TVMRunTask obj st)=TVMDoneTask st 2 1.
Proof. intro H. cbn [tvm_step]. destruct (tvm_target_validb _ _) eqn:E; [apply tvm_target_validb_spec in E; contradiction|reflexivity]. Qed.
Lemma tvm_iter_done n st status kind : tvm_iter n (TVMDoneTask st status kind)=TVMDoneTask st status kind.
Proof. induction n; cbn; auto. Qed.
Lemma tvm_iter_add m n task : tvm_iter (m+n) task=tvm_iter n (tvm_iter m task).
Proof. revert task. induction m; intros; cbn; auto. Qed.
Lemma tvm_exec_done st status kind : tvm_exec (TVMDoneTask st status kind) (TVMOutcome st status kind).
Proof. exists O, st, status, kind. split; reflexivity. Qed.
Lemma tvm_exec_step task out : tvm_exec (tvm_step task) out -> tvm_exec task out.
Proof. intros [n [st [status [kind [H E]]]]]. exists (S n),st,status,kind. auto. Qed.
Lemma tvm_exec_prefix n task out : tvm_exec (tvm_iter n task) out -> tvm_exec task out.
Proof. intros [m [st [status [kind [H E]]]]]. exists (n+m)%nat,st,status,kind. rewrite tvm_iter_add. auto. Qed.
Lemma tvm_exec_deterministic task out1 out2 : tvm_exec task out1 -> tvm_exec task out2 -> out1=out2.
Proof.
 intros [m [st1 [s1 [k1 [H1 E1]]]]] [n [st2 [s2 [k2 [H2 E2]]]]].
 destruct (le_dec m n) as [Hmn|Hnm].
 - replace n with (m+(n-m))%nat in H2 by lia. rewrite tvm_iter_add,H1,tvm_iter_done in H2. inversion H2; subst; reflexivity.
 - replace m with (n+(m-n))%nat in H1 by lia. rewrite tvm_iter_add,H2,tvm_iter_done in H1. inversion H1; subst; reflexivity.
Qed.
Lemma tvm_normal_excludes_error obj input output status :
 tvm_terminates obj input output status -> forall output2, ~tvm_errors obj input output2.
Proof. intros [_ [_ [st [H _]]]] output2 [_ [st2 [H2 _]]]. pose proof (tvm_exec_deterministic _ _ _ H H2). discriminate. Qed.
Lemma tvm_normal_excludes_malformed obj input output status :
 tvm_terminates obj input output status -> ~tvm_malformed obj input.
Proof. intros [_ [_ [st [H _]]]] [st2 H2]. pose proof (tvm_exec_deterministic _ _ _ H H2). discriminate. Qed.
