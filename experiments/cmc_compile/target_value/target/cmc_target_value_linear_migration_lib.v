Require Export SimpleC.EE.QCP_demos_human.cmc_target_stack_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_target_v_unary_step sp ap p fid op v st pc temp b c owner ob oc tail spills saved calls target :
 let ann:=CMAnnotation pc temp b c (CMACursor (CAUnaryP op) owner ob oc::tail) spills saved calls in
 cm_task_layout sp ap p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) ann ->
 cm_task_target_sim (cm_source_function_policy sp) p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) target ann ->
 cm_target_step_result sp ap p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) target ann.
Proof.
 cbn zeta; intros [CODE SAVED] [_ [vm [-> [PC SIM]]]]; pose proof SIM as OLD.
 destruct vm as [vpc stack vcalls mem input output]; cbn [tvm_pc cm_ann_pc]in PC; subst vpc.
 destruct SIM as [M [P [F [C [S [I [O STACK]]]]]]]; change(stack=[cm_value_number st v])in STACK; subst stack.
 pose proof(cm_tvm_unary (cm_compile_model(cm_source_function_policy sp)p) pc (cm_value_number st v) vcalls mem input output op (cm_cursor_code sp p fid (pc+2) owner false tail) CODE)as EXEC.
 change (p=p /\ cm_running_target_sim (cm_source_function_policy sp) p fid st [cm_unary_value op v st]
 (cm_ann_pop ap (pc+2) (CMAnnotation pc temp b c (CMACursor (CAUnaryP op) owner ob oc::tail) spills saved calls))
 (tvm_iter 2 (TVMRunTask (cm_compile_model(cm_source_function_policy sp)p) (TVMState pc [cm_value_number st v] vcalls mem input output)))).
 rewrite EXEC; split;[reflexivity|].
 exists(TVMState (pc+2) [if op=?0 then tower_neg(cm_value_number st v) else tower_bool(cm_value_number st v=?0)] vcalls mem input output); split;[reflexivity|split;[reflexivity|]].
 pose proof(cm_machine_sim_stack (cm_source_function_policy sp) p st _ _ _ [v] [] [cm_unary_value op v st] [] (pc+2) OLD)as NEW.
 cbn [cm_encode_values map app]in NEW; rewrite cm_unary_number in NEW; exact NEW.
Qed.
Lemma cm_target_v_expr_stmt_step sp ap p fid v st pc temp b c owner ob oc tail spills saved calls target :
 let ann:=CMAnnotation pc temp b c (CMACursor CAExprStmtP owner ob oc::tail) spills saved calls in
 cm_task_layout sp ap p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) ann ->
 cm_task_target_sim (cm_source_function_policy sp) p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) target ann ->
 cm_target_step_result sp ap p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) target ann.
Proof.
 cbn zeta; intros [CODE SAVED] [_ [vm [-> [PC SIM]]]]; pose proof SIM as OLD.
 destruct vm as [vpc stack vcalls mem input output]; cbn [tvm_pc cm_ann_pc]in PC; subst vpc.
 destruct SIM as [M [P [F [C [S [I [O STACK]]]]]]]; change(stack=[cm_value_number st v])in STACK; subst stack.
 pose proof(cm_tvm_pop_step (cm_compile_model(cm_source_function_policy sp)p) (TVMState pc [cm_value_number st v] vcalls mem input output) (cm_value_number st v) [] (cm_cursor_code sp p fid (pc+1) owner true tail) CODE eq_refl)as EXEC.
 change(p=p /\ cm_running_target_sim (cm_source_function_policy sp) p fid st []
 (cm_ann_pop ap (pc+1) (CMAnnotation pc temp b c (CMACursor CAExprStmtP owner ob oc::tail) spills saved calls))
 (tvm_step (TVMRunTask (cm_compile_model(cm_source_function_policy sp)p) (TVMState pc [cm_value_number st v] vcalls mem input output)))).
 rewrite EXEC; split;[reflexivity|]. exists(TVMState(pc+1)[] vcalls mem input output); split;[reflexivity|split;[reflexivity|]].
 exact(cm_machine_sim_stack (cm_source_function_policy sp)p st _ _ _ [v][] [][](pc+1) OLD).
Qed.
