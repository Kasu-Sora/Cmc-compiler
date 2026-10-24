Require Export SimpleC.EE.QCP_demos_human.cmc_code_layout_facts_migration_lib.
From Coq Require Import ZArith List Bool Lia.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Fixpoint cm_function_code_prefix policy p start (functions:list cm_function_d) index : list tvm_inst := match functions with []=>[] | _::rest=>if index=?0 then [] else cm_emit_function policy p start++cm_function_code_prefix policy p (start+1) rest (index-1) end.
Lemma cm_function_code_prefix_length policy p functions start index : start=Zlength (cm_program_functions p)-Zlength functions -> Zlength (cm_function_code_prefix policy p start functions index)=cm_function_prefix policy p functions index.
Proof.
 revert start index; induction functions as [|f fs IH]; intros start index EQ; [reflexivity|].
 cbn [cm_function_code_prefix cm_function_prefix]; destruct (index=?0); [reflexivity|].
 rewrite Zlength_app,cm_layout_function_length,IH; [now rewrite EQ|rewrite Zlength_cons in EQ; lia].
Qed.
Lemma cm_functions_function_at policy p functions start index : 0<=index<Zlength functions -> cm_code_at (cm_emit_functions policy p start functions) (Zlength (cm_function_code_prefix policy p start functions index)) (cm_emit_function policy p (start+index)).
Proof.
 revert start index; induction functions as [|f fs IH]; intros start index B; [change (0<=index<0) in B; lia|].
 cbn [cm_emit_functions cm_function_code_prefix]; destruct (index=?0) eqn:ZERO.
 - apply Z.eqb_eq in ZERO; subst index; rewrite Z.add_0_r; apply cm_code_at_front.
 - apply Z.eqb_neq in ZERO; rewrite Zlength_app.
   replace (start+index) with ((start+1)+(index-1)) by lia.
   apply cm_code_at_weaken_prefix; apply IH; rewrite Zlength_cons in B; lia.
Qed.
Lemma cm_model_function_at policy p fid : 0<=fid<Zlength (cm_program_functions p) -> cm_code_at (cm_model_code policy p) (cm_function_pc policy p fid) (cm_emit_function policy p fid).
Proof.
 intro B; unfold cm_model_code,cm_function_pc.
 replace 11 with (Zlength (cm_emit_prelude policy p)) by reflexivity.
 apply cm_code_at_weaken_prefix.
 rewrite <-(cm_function_code_prefix_length policy p (cm_program_functions p) 0 fid ltac:(lia)).
 replace fid with (0+fid) at 2 by lia; apply cm_functions_function_at; exact B.
Qed.
Lemma cm_model_function_body_tail_at policy p fid : 0<=fid<Zlength (cm_program_functions p) ->
 cm_code_at (cm_model_code policy p) (cm_function_pc policy p fid+cm_function_prologue_count (cm_function_at policy fid (cm_program_functions p)))
 (cm_emit_stmt policy p fid (cm_function_pc policy p fid+cm_function_prologue_count (cm_function_at policy fid (cm_program_functions p))) 0 0 0 (cm_function_body (cm_function_at policy fid (cm_program_functions p))) ++ cm_fallthrough_tail_code).
Proof.
 intro B; pose proof (cm_model_function_at policy p fid B) as CODE; unfold cm_emit_function in CODE.
 apply cm_code_at_append_right in CODE; rewrite cm_layout_prologue_length in CODE; exact CODE.
Qed.
