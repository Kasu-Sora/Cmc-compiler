Require Export SimpleC.EE.QCP_demos_human.cmc_target_stack_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_tvm_output_pair obj pc value calls mem input output (character:bool) rest :
 cm_code_at (tvm_object_code obj) pc ([TVMInst TVMDupOp 0;TVMInst (if character then TVMPutcOp else TVMPutiOp) 0]++rest) ->
 tvm_iter 2 (TVMRunTask obj (TVMState pc [value] calls mem input output))=
 TVMRunTask obj (TVMState (pc+2) [value] calls mem input (output++if character then [tower_u8 value] else tower_decimal value)).
Proof.
 intro CODE; cbn [app]in CODE; pose proof(cm_code_at_tail _ _ _ _ CODE)as C1.
 cbn [tvm_iter]; rewrite(cm_tvm_code_step obj (TVMState pc [value] calls mem input output) _ _ _ CODE).
 cbn [tvm_inst_step tvm_stack]; change ((1<=?Zlength [value])&&(Zlength [value]<?65536))with true.
 cbv beta iota zeta delta [tvm_action_task tvm_next_state tvm_pc tvm_calls tvm_mem tvm_input tvm_output hd tl].
 rewrite(cm_tvm_code_step obj (TVMState (pc+1) [value;value] calls mem input output) _ _ _ C1).
 destruct character; cbn [tvm_inst_step tvm_stack]; change(1<=?Zlength [value;value])with true;
 cbv beta iota zeta delta [tvm_action_task tvm_next_state tvm_pc tvm_calls tvm_mem tvm_input tvm_output hd tl]; f_equal; f_equal; lia.
Qed.
Lemma cm_target_v_putc_step sp ap p fid v st pc temp b c owner ob oc tail spills saved calls target :
 let ann:=CMAnnotation pc temp b c (CMACursor CAPutcP owner ob oc::tail) spills saved calls in
 cm_task_layout sp ap p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) ann ->
 cm_task_target_sim (cm_source_function_policy sp) p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) target ann ->
 cm_target_step_result sp ap p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) target ann.
Proof.
 cbn zeta; intros [CODE SAVED] [_ [vm [-> [PC SIM]]]]; pose proof SIM as OLD.
 destruct vm as [vpc stack vcalls mem input output]; cbn [tvm_pc cm_ann_pc]in PC; subst vpc.
 destruct SIM as [M [P [F [C [S [I [O STACK]]]]]]]; change(stack=[cm_value_number st v])in STACK; subst stack.
 pose proof(cm_tvm_output_pair (cm_compile_model(cm_source_function_policy sp)p) pc (cm_value_number st v) vcalls mem input output true (cm_cursor_code sp p fid (pc+2) owner false tail) CODE)as EXEC.
 change(p=p /\ cm_running_target_sim (cm_source_function_policy sp) p fid
 (cm_state_io st (cm_state_input st) (cm_state_output st++[tower_u8(cm_value_number st v)])) [CMIntV(cm_value_number st v)]
 (cm_ann_pop ap (pc+2) (CMAnnotation pc temp b c (CMACursor CAPutcP owner ob oc::tail) spills saved calls))
 (tvm_iter 2 (TVMRunTask (cm_compile_model(cm_source_function_policy sp)p) (TVMState pc [cm_value_number st v] vcalls mem input output)))).
 rewrite EXEC; split;[reflexivity|]. exists(TVMState(pc+2)[cm_value_number st v] vcalls mem input (output++[tower_u8(cm_value_number st v)])); split;[reflexivity|split;[reflexivity|]].
 pose proof(cm_machine_sim_io_stack (cm_source_function_policy sp)p st _ _ _ [v][] [CMIntV(cm_value_number st v)][] (pc+2) (cm_state_input st) (cm_state_output st++[tower_u8(cm_value_number st v)]) OLD)as NEW.
 cbn [cm_encode_values map app cm_value_number]in NEW; rewrite cm_value_number_wrap in NEW.
 cbn [tvm_input]in I; cbn [tvm_output]in O; rewrite I,O; exact NEW.
Qed.
Lemma cm_target_v_puti_step sp ap p fid v st pc temp b c owner ob oc tail spills saved calls target :
 let ann:=CMAnnotation pc temp b c (CMACursor CAPutiP owner ob oc::tail) spills saved calls in
 cm_task_layout sp ap p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) ann ->
 cm_task_target_sim (cm_source_function_policy sp) p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) target ann ->
 cm_target_step_result sp ap p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) target ann.
Proof.
 cbn zeta; intros [CODE SAVED] [_ [vm [-> [PC SIM]]]]; pose proof SIM as OLD.
 destruct vm as [vpc stack vcalls mem input output]; cbn [tvm_pc cm_ann_pc]in PC; subst vpc.
 destruct SIM as [M [P [F [C [S [I [O STACK]]]]]]]; change(stack=[cm_value_number st v])in STACK; subst stack.
 pose proof(cm_tvm_output_pair (cm_compile_model(cm_source_function_policy sp)p) pc (cm_value_number st v) vcalls mem input output false (cm_cursor_code sp p fid (pc+2) owner false tail) CODE)as EXEC.
 change(p=p /\ cm_running_target_sim (cm_source_function_policy sp) p fid
 (cm_state_io st (cm_state_input st) (cm_state_output st++tower_decimal(cm_value_number st v))) [CMIntV(cm_value_number st v)]
 (cm_ann_pop ap (pc+2) (CMAnnotation pc temp b c (CMACursor CAPutiP owner ob oc::tail) spills saved calls))
 (tvm_iter 2 (TVMRunTask (cm_compile_model(cm_source_function_policy sp)p) (TVMState pc [cm_value_number st v] vcalls mem input output)))).
 rewrite EXEC; split;[reflexivity|]. exists(TVMState(pc+2)[cm_value_number st v] vcalls mem input (output++tower_decimal(cm_value_number st v))); split;[reflexivity|split;[reflexivity|]].
 pose proof(cm_machine_sim_io_stack (cm_source_function_policy sp)p st _ _ _ [v][] [CMIntV(cm_value_number st v)][] (pc+2) (cm_state_input st) (cm_state_output st++tower_decimal(cm_value_number st v)) OLD)as NEW.
 cbn [cm_encode_values map app cm_value_number]in NEW; rewrite cm_value_number_wrap in NEW.
 cbn [tvm_input]in I; cbn [tvm_output]in O; rewrite I,O; exact NEW.
Qed.
