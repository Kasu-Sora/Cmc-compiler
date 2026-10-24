Require Export SimpleC.EE.QCP_demos_human.cmc_target_args_reload_migration_lib.
From AUXLib Require Import ListLib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_target_reload_staged sp ap p fid st ann target base args values rest :
 cm_runtime_core(cm_source_function_policy sp)ap p fid st ann ->0<=fid ->0<=base ->
 base+Zlength args<=cm_temp_slots(cm_source_function_at sp fid p) ->Zlength args=Zlength values ->Zlength values+1<65536 ->
 cm_staged_spills base values(cm_ann_spills ann) ->
 cm_code_at(cm_model_code(cm_source_function_policy sp)p)(cm_ann_pc ann)(cm_emit_args_reload(cm_source_function_policy sp)p fid base args++rest) ->
 cm_running_target_sim(cm_source_function_policy sp)p fid st[]ann target ->
 cm_running_target_sim(cm_source_function_policy sp)p fid st values(cm_ann_linear(cm_emit_args_reload(cm_source_function_policy sp)p fid base args)ann)
 (tvm_iter(cm_code_steps(cm_emit_args_reload(cm_source_function_policy sp)p fid base args))target).
Proof.
 intros RT FID BASE BOUND LEN CAP STAGED CODE[vm[-> [PC SIM]]].
 pose proof SIM as[_[_[FP[_[[SP _]_]]]]].
 pose proof(cm_tvm_reload_staged (cm_source_function_policy sp)p fid st vm(cm_ann_spills ann)base args values[](cm_ann_pc ann)rest LEN BASE BOUND ltac:(rewrite Zlength_nil;lia))as EXEC.
 assert(VALID:forall slot,base<=slot<base+Zlength args ->tower_word_valid(tower_getw(tvm_mem vm)8+cm_temp_offset(cm_source_function_policy sp)p fid slot)).
 { intros slot B;rewrite FP;exact(proj1(cm_runtime_temp_machine_safe (cm_source_function_policy sp) ap p (cm_state_regions st)(cm_ann_cursors ann)fid(cm_state_fp st)(cm_state_regions st)(cm_ann_spills ann)(cm_ann_saved ann)(cm_ann_calls ann)slot (proj2 RT)FID ltac:(unfold cm_source_function_at in BOUND;lia))). }
 specialize(EXEC VALID ltac:(rewrite FP;exact SP) STAGED CODE).
 assert(V:vm=TVMState(cm_ann_pc ann)[](tvm_calls vm)(tvm_mem vm)(tvm_input vm)(tvm_output vm)).
 { pose proof SIM as[_[_[_[_[_[_[_ STACK]]]]]]];destruct vm;cbn in PC,STACK|-*;change(stack=[])in STACK;subst;reflexivity. }
 rewrite V at 1;rewrite EXEC;eexists;split;[reflexivity|split;[reflexivity|]].
 exact(cm_machine_sim_stack _ _ _ _ _ _ _ _ values[](cm_ann_pc ann+Zlength(cm_emit_args_reload(cm_source_function_policy sp)p fid base args))SIM).
Qed.
