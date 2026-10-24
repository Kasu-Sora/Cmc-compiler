Require Export SimpleC.EE.QCP_demos_human.cmc_param_pending_relation_migration_lib.
From AUXLib Require Import ListLib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_store_params_pending_eq sp p fid values index a b address finish :
 (forall j,index<=j<index+Zlength values ->
 cm_value_number a(cm_state_env a 2 j)=address j /\
 address j+cm_store_width(cm_slot_ty(cm_source_slot_at sp j(cm_function_params(cm_source_function_at sp fid p))))=address(j+1) /\ address(j+1)<=finish) ->
 cm_state_pending_eq a b(address index)finish ->
 cm_state_pending_eq(cm_store_params sp p fid values index a)(cm_store_params sp p fid values index b)(address(index+Zlength values))finish.
Proof.
 revert index a b;induction values as[|v vs IH];intros index a b FACT EQ.
 - rewrite Zlength_nil,Z.add_0_r;exact EQ.
 - replace(index+Zlength(v::vs))with((index+1)+Zlength vs)by(rewrite Zlength_cons;lia).
   cbn[cm_store_params];apply IH.
   + intros j J;destruct(FACT j ltac:(rewrite Zlength_cons;lia))as[A[N B]].
     split;[rewrite cm_store_value_number;exact A|auto].
   + pose proof EQ as[_[_[_[_[ENV _]]]]].
     pose proof(Zlength_nonneg vs);destruct(FACT index ltac:(rewrite Zlength_cons;lia))as[A[N B]].
     rewrite<-(ENV 2 index),<-N;apply cm_pending_eq_store;auto;lia.
Qed.
Lemma cm_call_base_pending_eq sp p fid st :
 cm_state_pending_eq(cm_call_pending_base sp p fid st)(cm_call_base_state sp p fid st)
 (cm_state_fp st-cm_frame_size(cm_program_structs p)(cm_source_function_at sp fid p)+8)
 (cm_state_fp st-cm_frame_size(cm_program_structs p)(cm_source_function_at sp fid p)+8+cm_call_param_span sp p fid).
Proof.
 unfold cm_state_pending_eq;repeat split;intros;try reflexivity.
 - cbn[cm_call_pending_base cm_call_base_state cm_state_init cm_state_fp];unfold cm_clear_init.
   assert(K:((cm_state_fp st-cm_frame_size(cm_program_structs p)(cm_source_function_at sp fid p)+8<=?x)&&(x<?cm_state_fp st-cm_frame_size(cm_program_structs p)(cm_source_function_at sp fid p)+8+cm_call_param_span sp p fid))=false).
   { apply andb_false_iff;destruct H;[left;apply Z.leb_gt|right;apply Z.ltb_ge];lia. }
   rewrite K;cbn;now rewrite andb_true_r.
 - cbn[cm_call_pending_base cm_call_base_state cm_state_tagged cm_state_fp];unfold cm_clear_tagged.
   assert(K:((0<?cm_call_param_span sp p fid)&&(x<?cm_state_fp st-cm_frame_size(cm_program_structs p)(cm_source_function_at sp fid p)+8+cm_call_param_span sp p fid))&&(cm_state_fp st-cm_frame_size(cm_program_structs p)(cm_source_function_at sp fid p)+8<?x+8)=false).
   { apply not_true_is_false;intro K;repeat rewrite andb_true_iff in K;destruct K as[[A B]C];apply Z.ltb_lt in A,B,C;lia. }
   rewrite K;cbn;now rewrite andb_true_r.
Qed.
Lemma cm_call_params_pending_complete sp p fid st values :
 cm_function_wf(cm_source_function_policy sp)p(cm_source_function_at sp fid p) ->
 cm_frame_segment(cm_source_function_policy sp)p fid(cm_state_fp st-cm_frame_size(cm_program_structs p)(cm_source_function_at sp fid p))(cm_state_fp st) ->
 Zlength values=Zlength(cm_function_params(cm_source_function_at sp fid p)) ->
 cm_state_pointwise_eq(cm_store_params sp p fid values 0(cm_call_pending_base sp p fid st))(cm_enter_call sp p fid values st).
Proof.
 intros FW SEG ARITY.
 set(address:=fun j=>cm_param_base sp p fid j(cm_state_fp st-cm_frame_size(cm_program_structs p)(cm_source_function_at sp fid p))).
 assert(END:address(Zlength values)=cm_state_fp st-cm_frame_size(cm_program_structs p)(cm_source_function_at sp fid p)+8+cm_call_param_span sp p fid).
 { unfold address,cm_param_base,cm_call_param_span;rewrite ARITY,cm_slots_prefix_length;reflexivity. }
 assert(START:address 0=cm_state_fp st-cm_frame_size(cm_program_structs p)(cm_source_function_at sp fid p)+8).
 { unfold address,cm_param_base;rewrite cm_slots_prefix_zero;lia. }
 pose proof(cm_store_params_pending_eq sp p fid values 0(cm_call_pending_base sp p fid st)(cm_call_base_state sp p fid st)address(address(Zlength values)))as ITER.
 rewrite Z.add_0_l in ITER;apply cm_pending_eq_complete with(address(Zlength values));unfold cm_enter_call;apply ITER.
 - intros j J;pose proof(cm_call_param_geometry sp p fid st j FW SEG ltac:(lia))as[A[N _]].
   split;[exact A|];split;[exact N|].
   apply cm_address_monotone;[lia|];intros k K.
   pose proof(cm_call_param_geometry sp p fid st k FW SEG ltac:(lia))as[_[NEXT _]].
   pose proof(cm_store_width_positive(cm_slot_ty(cm_source_slot_at sp k(cm_function_params(cm_source_function_at sp fid p)))));unfold address;lia.
 - rewrite START,END;apply cm_call_base_pending_eq.
Qed.
Lemma cm_call_params_reverse_complete sp p fid st values :
 cm_function_wf(cm_source_function_policy sp)p(cm_source_function_at sp fid p) ->
 cm_frame_segment(cm_source_function_policy sp)p fid(cm_state_fp st-cm_frame_size(cm_program_structs p)(cm_source_function_at sp fid p))(cm_state_fp st) ->
 Zlength values=Zlength(cm_function_params(cm_source_function_at sp fid p)) ->
 cm_state_pointwise_eq(cm_store_params_reverse sp p fid values 0(cm_call_pending_base sp p fid st))(cm_enter_call sp p fid values st).
Proof.
 intros FW SEG ARITY;eapply cm_state_pointwise_trans;[apply cm_call_params_reverse_forward;auto;lia|now apply cm_call_params_pending_complete].
Qed.
