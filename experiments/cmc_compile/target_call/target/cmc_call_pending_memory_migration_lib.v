Require Export SimpleC.EE.QCP_demos_human.cmc_call_pending_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_call_pending_initialized_transport sp p fid st mem :
 cm_function_wf(cm_source_function_policy sp)p(cm_source_function_at sp fid p) ->cm_regions_before(cm_state_regions st)(cm_state_nextgen st) ->
 cm_initialized_bytes_sim st mem ->
 (forall a,cm_live_address st a ->a<cm_state_fp(cm_call_base_state sp p fid st) \/ cm_state_fp(cm_call_base_state sp p fid st)+8<=a) ->
 cm_initialized_bytes_sim(cm_call_pending_base sp p fid st)mem.
Proof.
 intros WF BEFORE SIM OUT a INIT LIVE;destruct(cm_call_pending_live_old_or_param _ _ _ _ _ WF BEFORE LIVE)as[OLD|PARAM].
 - apply andb_true_iff in INIT;destruct INIT as[INIT _];pose proof(SIM a INIT OLD)as BYTE.
   change(tower_getb mem a=tower_getb(tower_setw(cm_state_mem st)(cm_state_fp(cm_call_base_state sp p fid st))(cm_state_fp st))a).
   rewrite tower_getb_setw_outside by exact(OUT a OLD);exact BYTE.
 - change(cm_clear_init(cm_state_init st)(cm_state_fp(cm_call_pending_base sp p fid st)+8)(cm_call_param_span sp p fid)a=true)in INIT.
   unfold cm_clear_init in INIT;apply andb_true_iff in INIT;destruct INIT as[_ BAD];apply negb_true_iff in BAD.
   destruct PARAM as[L H];apply Z.leb_le in L;apply Z.ltb_lt in H;rewrite L,H in BAD;discriminate.
Qed.
Lemma cm_call_pending_provenance_transport sp p fid st mem :
 cm_function_wf(cm_source_function_policy sp)p(cm_source_function_at sp fid p) ->cm_regions_before(cm_state_regions st)(cm_state_nextgen st) ->
 cm_tags_generation_below(cm_state_nextgen st)(cm_state_tags st) ->cm_stored_provenance_sim st mem ->
 cm_stored_provenance_sim(cm_call_pending_base sp p fid st)mem.
Proof.
 intros WF BEFORE GEN SIM a TAG LIVE;pose proof TAG as TAG0;apply andb_true_iff in TAG;destruct TAG as[TAG _].
 destruct(cm_call_pending_live_old_or_param _ _ _ _ _ WF BEFORE LIVE)as[OLD|PARAM].
 - specialize(SIM a TAG OLD);split;[eapply cm_clear_tagged_init;[exact TAG0|exact(proj1 SIM)]|].
   change(tower_getw mem a=cm_value_number(cm_call_pending_base sp p fid st)(cm_state_tags st a)).
   rewrite cm_call_pending_value_number by apply GEN;exact(proj2 SIM).
 - assert(FALSE:cm_clear_init(fun _=>true)(cm_state_fp(cm_call_pending_base sp p fid st)+8)(cm_call_param_span sp p fid)a=true)by(eapply cm_clear_tagged_init;[exact TAG0|reflexivity]).
   unfold cm_clear_init in FALSE;cbn[andb]in FALSE;apply negb_true_iff in FALSE.
   destruct PARAM as[L H];apply Z.leb_le in L;apply Z.ltb_lt in H;rewrite L,H in FALSE;discriminate.
Qed.
Lemma cm_call_pending_spills_transport sp p fid st mem frames :
 cm_spill_frames_generation_below(cm_state_nextgen st)frames ->cm_spill_frames_sim(cm_source_function_policy sp)p st mem frames ->
 cm_spill_frames_sim(cm_source_function_policy sp)p(cm_call_pending_base sp p fid st)mem frames.
Proof. intros GEN SIM;eapply cm_spill_frames_sim_bases;[apply cm_call_pending_bases|exact GEN|exact SIM]. Qed.
