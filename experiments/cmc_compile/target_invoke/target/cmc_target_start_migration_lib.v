Require Export SimpleC.EE.QCP_demos_human.cmc_target_boot_migration_lib.
From AUXLib Require Import ListLib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_target_start_step sp ap p input :
 cm_semantic_wf_program(cm_source_function_policy sp)p ->cm_call_ok sp p(cm_program_main p)[](cm_initial_state sp p input)=true ->
 cm_target_step_result sp ap p(CMStartTask p input)(TVMBoot(cm_compile_model(cm_source_function_policy sp)p)input)cm_initial_annotation.
Proof.
 intros WF OK.
 set(st:=cm_initial_state sp p input).
 set(ann:=CMAnnotation 3 0 0 0[CMACursor CAHaltP 0 0 0][][][]).
 set(vm:=TVMState 3[][](tower_setw(tvm_mem(tvm_initial_state(cm_compile_model(cm_source_function_policy sp)p)input))8 1048576)input[]).
 pose proof(cm_model_prelude_at(cm_source_function_policy sp)p)as C0.
 pose proof(cm_code_at_tail _ _ _ _ C0)as C1;pose proof(cm_code_at_tail _ _ _ _ C1)as C2;pose proof(cm_code_at_tail _ _ _ _ C2)as CALL.
 pose proof(cm_model_function_at(cm_source_function_policy sp)p(cm_program_main p)(cm_call_ok_fid_bounds _ _ _ _ _ OK))as PROLOGUE;unfold cm_emit_function in PROLOGUE.
 pose proof(cm_state_generation_initial sp p input)as[GEN[_ TG]].
 assert(NG:0<=cm_state_nextgen st).
 { unfold st;cbn[cm_initial_state cm_state_nextgen];unfold cm_first_dynamic_generation;pose proof(Zlength_nonneg(cm_program_globals p));pose proof(Zlength_nonneg(cm_program_strings p));lia. }
 destruct(cm_tvm_invoke_function sp ap p(-1)(cm_program_main p)st[]ann(cm_compile_model(cm_source_function_policy sp)p)vm _ _ WF OK
 (cm_runtime_core_halt_initial sp ap p input(proj1 WF))(cm_tagged_span_initial sp p input)NG TG ltac:(split;exact I) I ltac:(change(0<65536);lia)
 (cm_initial_machine_sim sp p input 3)CALL PROLOGUE)as[next[EXEC[PC SIM]]].
 unfold cm_target_step_result;cbv beta iota zeta delta[cm_step cm_begin_call cm_annotation_step];rewrite OK.
 change(cm_call_depth[CMHaltK]<?65536)with true;cbn[andb cm_update_steps cm_update_annotation cm_task_target_sim].
 unfold cm_entry_steps;replace(S(4+cm_code_steps(cm_emit_prologue(cm_source_function_policy sp)p(cm_program_main p))))with(4+S(cm_code_steps(cm_emit_prologue(cm_source_function_policy sp)p(cm_program_main p))))%nat by lia.
 rewrite tvm_iter_add,(cm_tvm_prelude_prefix _ _ _ WF);fold vm;rewrite EXEC.
 split;[reflexivity|];exists next;split;[reflexivity|];split;[exact PC|].
 unfold cm_active_spill_frames,cm_ann_enter_call,cm_enter_call;cbn[cm_ann_calls cm_ann_saved cm_ann_spills];rewrite cm_store_params_fp;exact SIM.
Qed.
