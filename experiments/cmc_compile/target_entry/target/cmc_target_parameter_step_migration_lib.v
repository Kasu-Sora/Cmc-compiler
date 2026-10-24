Require Export SimpleC.EE.QCP_demos_human.cmc_target_param_store_code_migration_lib.
From Coq Require Import ZArith List Bool Lia.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_store_encode_values ty ptr value st values :cm_encode_values(cm_state_store ty ptr value st)values=cm_encode_values st values.
Proof. unfold cm_encode_values;apply map_ext;intro v;apply cm_store_value_number. Qed.
Lemma cm_reverse_params_encode sp p fid values index st held :cm_encode_values(cm_store_params_reverse sp p fid values index st)held=cm_encode_values st held.
Proof. unfold cm_encode_values;apply map_ext;intro v;apply cm_store_params_reverse_value_number. Qed.
Lemma cm_parameter_store_runtime policy p st calls frames ty ptr v :cm_runtime_memory_layout policy p st calls frames ->cm_runtime_memory_layout policy p(cm_state_store ty ptr v st)calls frames.
Proof. exact(fun H=>H). Qed.
Lemma cm_parameter_store_step policy p st obj pc calls frames vcalls mem input output v held ty ptr offset rest :
 let code:=cm_char_normalize_code ty++cm_fp_relative_address_code offset++cm_store_code ty in
 let next:=cm_state_store ty ptr v st in
 let vm:=TVMState(pc+Zlength code)(cm_encode_values next held)vcalls(cm_store_mem ty(cm_value_number st ptr)(cm_value_number st(cm_convert_value st ty v))mem)input output in
 cm_runtime_memory_layout policy p st calls frames ->cm_store_ok ty ptr st=true ->
 cm_value_number st ptr=tower_wrap64(cm_state_fp st+offset) ->Zlength held+2<65536 ->
 cm_machine_state_sim policy p st(TVMState pc(cm_encode_values st(v::held))vcalls mem input output)calls frames(v::held)[] ->
 cm_code_at(tvm_object_code obj)pc(code++rest) ->
 tvm_iter(cm_code_steps code)(TVMRunTask obj(TVMState pc(cm_encode_values st(v::held))vcalls mem input output))=TVMRunTask obj vm /\
 cm_machine_state_sim policy p next vm calls frames held[].
Proof.
 cbn zeta;intros RT OK NUM CAP SIM CODE.
 pose proof SIM as[_[_[FP _]]];cbn[tvm_mem]in FP.
 assert(ADDR:match ty with CMCharTy=>tower_addr_valid(tower_wrap64(tower_getw mem 8+offset))|_=>tower_word_valid(tower_wrap64(tower_getw mem 8+offset))end).
 { rewrite FP,<-NUM;now apply cm_store_address_valid. }
 split.
 - rewrite <-app_assoc in CODE.
   pose proof(cm_tvm_init_code_stack st v ty obj pc(cm_encode_values st held)vcalls mem input output offset rest ltac:(unfold cm_encode_values;rewrite Zlength_correct,map_length,<-Zlength_correct;exact CAP)ADDR CODE)as EXEC.
   rewrite cm_store_encode_values. change(cm_encode_values st(v::held))with(cm_value_number st v::cm_encode_values st held).
   rewrite EXEC,FP,<-NUM;reflexivity.
 - pose proof(cm_machine_source_store policy p st(TVMState pc(cm_encode_values st(v::held))vcalls mem input output)calls frames(v::held)[]ty ptr v held[](pc+Zlength(cm_char_normalize_code ty++cm_fp_relative_address_code offset++cm_store_code ty))RT OK SIM)as M.
   rewrite app_nil_r in M;exact M.
Qed.
