Require Export SimpleC.EE.QCP_demos_human.cmc_target_temp_store_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_tvm_fp_load_value obj pc value calls mem input output offset rest :
 tower_word_valid(tower_getw mem 8+offset) ->
 cm_code_at(tvm_object_code obj)pc(cm_fp_relative_address_code offset++TVMInst TVMLoadOp 0::rest) ->
 tvm_iter 5(TVMRunTask obj(TVMState pc[value]calls mem input output))=
 TVMRunTask obj(TVMState(pc+5)[tower_getw mem(tower_getw mem 8+offset);value]calls mem input output).
Proof.
 intros ADDR CODE;pose proof(cm_code_at_append_right _ _ _ _ CODE)as LOAD.
 change(cm_code_at(tvm_object_code obj)(pc+4)(TVMInst TVMLoadOp 0::rest))in LOAD.
 change(tvm_step(tvm_iter 4(TVMRunTask obj(TVMState pc[value]calls mem input output)))=TVMRunTask obj(TVMState(pc+5)[tower_getw mem(tower_getw mem 8+offset);value]calls mem input output)).
 rewrite(cm_tvm_fp_address_value _ _ _ _ _ _ _ _ _ CODE).
 rewrite tower_wrap64_fixed by(unfold tower_signed64,tower_word_valid in *;lia).
 rewrite(cm_tvm_load_step obj(TVMState(pc+4)[tower_getw mem 8+offset;value]calls mem input output)(tower_getw mem 8+offset)[value]_ LOAD eq_refl ADDR).
 cbv beta iota zeta delta [tvm_next_state tvm_pc tvm_stack tvm_calls tvm_mem tvm_input tvm_output];f_equal;f_equal;lia.
Qed.
Lemma cm_spill_sim_holds policy p st mem fid fp spills slot v :
 cm_spill_list_sim policy p st mem fid fp spills -> cm_spill_holds slot v spills ->
 tower_getw mem(fp+cm_temp_offset policy p fid slot)=cm_value_number st v.
Proof.
 induction spills as[|[s w]rest IH];cbn[cm_spill_list_sim cm_spill_holds cm_spill_slot cm_spill_value];[tauto|].
 intros[H T];destruct(s=?slot)eqn:E;intro HOLD;[apply Z.eqb_eq in E;subst;exact H|now apply IH].
Qed.
Lemma cm_tvm_temp_load_held sp ap p fid st vm ann slot left right pc rest :
 cm_runtime_core(cm_source_function_policy sp)ap p fid st ann -> 0<=fid ->
 0<=slot<cm_temp_slots(cm_source_function_at sp fid p) -> cm_spill_holds slot left(cm_ann_spills ann) ->
 cm_machine_state_sim(cm_source_function_policy sp)p st vm(cm_ann_calls ann)(cm_active_spill_frames fid st ann)[right][] ->
 cm_code_at(cm_model_code(cm_source_function_policy sp)p)pc(cm_temp_load_code(cm_source_function_policy sp)p fid slot++rest) ->
 tvm_iter 5(TVMRunTask(cm_compile_model(cm_source_function_policy sp)p)(TVMState pc[cm_value_number st right](tvm_calls vm)(tvm_mem vm)(tvm_input vm)(tvm_output vm)))=
 TVMRunTask(cm_compile_model(cm_source_function_policy sp)p)(TVMState(pc+5)[cm_value_number st left;cm_value_number st right](tvm_calls vm)(tvm_mem vm)(tvm_input vm)(tvm_output vm)).
Proof.
 intros RT FID SLOT HOLD[_[_[FP[_[[SP _]_]]]]]CODE.
 pose proof(cm_spill_sim_holds _ _ _ _ _ _ _ _ _ SP HOLD)as WORD;cbn[cm_spill_frame_fp cm_spill_frame_fid]in WORD.
 pose proof(cm_runtime_temp_machine_safe _ _ _ _ _ _ _ _ _ _ _ _ (proj2 RT)FID SLOT)as[ADDR _].
 unfold cm_temp_load_code in CODE;rewrite <-app_assoc in CODE;rewrite <-FP in ADDR.
 rewrite(cm_tvm_fp_load_value (cm_compile_model(cm_source_function_policy sp)p) pc (cm_value_number st right) (tvm_calls vm)(tvm_mem vm)(tvm_input vm)(tvm_output vm) _ rest ADDR CODE),FP,WORD;reflexivity.
Qed.
