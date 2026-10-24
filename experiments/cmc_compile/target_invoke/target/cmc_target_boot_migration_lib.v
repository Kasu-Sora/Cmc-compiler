Require Export SimpleC.EE.QCP_demos_human.cmc_target_v_total_migration_lib.
From AUXLib Require Import ListLib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_model_prelude_at policy p :cm_code_at(cm_model_code policy p)0(cm_emit_prelude policy p).
Proof. exists [],(cm_emit_functions policy p 0(cm_program_functions p));split;reflexivity. Qed.
Lemma cm_tvm_prelude_prefix policy p input :cm_semantic_wf_program policy p ->
 tvm_iter 4(TVMBoot(cm_compile_model policy p)input)=
 TVMRunTask(cm_compile_model policy p)(TVMState 3[][](tower_setw(tvm_mem(tvm_initial_state(cm_compile_model policy p)input))8 1048576)input[]).
Proof.
 intro WF;assert(LOAD:tvm_load_okb(cm_compile_model policy p)=true)by(apply tvm_load_okb_spec;exact(proj1(cm_compile_model_wf _ _ WF))).
 pose proof(cm_model_prelude_at policy p)as CODE;unfold cm_emit_prelude in CODE.
 set(mem:=tvm_mem(tvm_initial_state(cm_compile_model policy p)input))in *.
 pose proof(cm_code_at_tail _ _ _ _ CODE)as C1;pose proof(cm_code_at_tail _ _ _ _ C1)as C2.
 change(tvm_iter 4(TVMBoot(cm_compile_model policy p)input))with(tvm_iter 3(tvm_step(TVMBoot(cm_compile_model policy p)input))).
 cbn[tvm_step];rewrite LOAD.
 change(tvm_initial_state(cm_compile_model policy p)input)with(TVMState 0[][](tvm_mem(tvm_initial_state(cm_compile_model policy p)input))input[]).
 fold mem;cbn[tvm_iter];rewrite(cm_tvm_push_step (cm_compile_model policy p)(TVMState 0[][]mem input[]) _ _ CODE ltac:(cbn;lia)).
 unfold tvm_next_state;cbn[tvm_pc tvm_stack tvm_calls tvm_mem tvm_input tvm_output];fold mem;change(tower_wrap64 1048576)with 1048576.
 change(0+1)with 1.
 rewrite(cm_tvm_push_step (cm_compile_model policy p)(TVMState 1[1048576][]mem input[]) _ _ C1 ltac:(cbn;lia)).
 unfold tvm_next_state;cbn[tvm_pc tvm_stack tvm_calls tvm_mem tvm_input tvm_output];fold mem;change(tower_wrap64 8)with 8;change(1+1)with 2.
 rewrite(cm_tvm_store_step (cm_compile_model policy p)(TVMState 2[8;1048576][]mem input[])8 1048576[] _ C2 eq_refl ltac:(unfold tower_word_valid;lia));reflexivity.
Qed.
Lemma cm_initial_machine_sim sp p input pc :
 cm_machine_state_sim(cm_source_function_policy sp)p(cm_initial_state sp p input)
 (TVMState pc[][](tower_setw(tvm_mem(tvm_initial_state(cm_compile_model(cm_source_function_policy sp)p)input))8 1048576)input[])
 [] [CMSpillFrame(-1)1048576[]][][].
Proof.
 unfold cm_machine_state_sim;cbn[tvm_mem tvm_input tvm_output tvm_stack tvm_calls];split.
 - intros addr INIT LIVE;cbn[cm_initial_state cm_state_init]in INIT;apply andb_true_iff in INIT;destruct INIT as[LOW HIGH];apply Z.leb_le in LOW.
   rewrite tower_getb_setw_outside by(right;lia);rewrite <- (cm_initial_memory_matches (cm_source_function_policy sp)sp p input);reflexivity.
 - split;[intros addr TAG;discriminate|].
   split;[rewrite tower_getw_setw;reflexivity|].
   repeat split.
Qed.
