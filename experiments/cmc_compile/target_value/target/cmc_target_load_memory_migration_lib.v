Require Export SimpleC.EE.QCP_demos_human.cmc_target_stack_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_pointer_read_region_witness regions ptr : cm_pointer_region_ok regions ptr false=true ->
 exists r,In r regions /\ cm_region_gen r=cm_ptr_gen ptr /\ cm_region_live r=true /\ cm_region_lo r<=cm_ptr_lo ptr /\ cm_ptr_hi ptr<=cm_region_hi r.
Proof.
 induction regions as [|r rest IH]; cbn [cm_pointer_region_ok];[discriminate|].
 rewrite orb_true_iff; intros [H|H];[|destruct(IH H)as[r0[IN R]];exists r0;split;[now right|exact R]].
 repeat rewrite andb_true_iff in H; cbn [negb orb]in H; destruct H as [[[[G L] LO] HI] _].
 apply Z.eqb_eq in G; apply Z.leb_le in LO,HI; exists r; repeat split;auto;now left.
Qed.
Lemma cm_runtime_load_live_span policy p st calls frames ty ptr :
 cm_runtime_memory_layout policy p st calls frames -> cm_load_ok ty ptr st=true ->
 cm_live_span st (cm_value_number st ptr) (cm_store_width ty).
Proof.
 intros RT LOAD; unfold cm_load_ok in LOAD; repeat rewrite andb_true_iff in LOAD; destruct LOAD as [[[[[LIVE LO] HI] ADDR] INIT] TAG].
 unfold cm_pointer_live in LIVE; repeat rewrite andb_true_iff in LIVE; destruct LIVE as [[GEN0 PTRBOUND] REG].
 destruct(cm_pointer_read_region_witness _ _ REG)as[r[IN[GEN[RL[RLO RHI]]]]].
 specialize(RT r IN); destruct RT as [DEAD|[L0[LH[BL[BH MACHINE]]]]];[congruence|].
 apply Z.leb_le in LO,HI,GEN0; assert(WIDTH:0<cm_store_width ty)by(destruct ty;cbn [cm_store_width];lia).
 destruct ptr as[n|n| |gen lo hi off view];cbn [cm_ptr_gen cm_ptr_lo cm_ptr_hi cm_ptr_offset]in GEN0,GEN,RLO,RHI,LO,HI;try lia.
 assert(BASE:cm_value_number st(CMPtrV gen lo hi off view)=cm_region_base(cm_state_regions st)gen+off).
 { cbn [cm_value_number];apply tower_wrap64_fixed;unfold tower_signed64;rewrite GEN in BL,BH;lia. }
 unfold cm_live_span;rewrite BASE;intros addr RANGE;exists r;repeat split;try assumption;rewrite GEN;lia.
Qed.
Lemma cm_load_machine_number policy p st calls frames ty ptr mem :
 cm_runtime_memory_layout policy p st calls frames -> cm_load_ok ty ptr st=true -> cm_scalar_expr_type ty ->
 cm_initialized_bytes_sim st mem -> cm_stored_provenance_sim st mem ->
 cm_value_number st(cm_load_value ty ptr st)=match ty with CMCharTy=>tower_getb mem(cm_value_number st ptr)|_=>tower_getw mem(cm_value_number st ptr)end.
Proof.
 intros RT OK TYPE MEM PROV; pose proof(cm_runtime_load_live_span _ _ _ _ _ _ _ RT OK)as LIVE.
 destruct ty;cbn [cm_scalar_expr_type cm_integer_type cm_is_pointer]in TYPE;try tauto;
 eauto using cm_load_char_sim,cm_load_int_sim,cm_load_pointer_sim.
unfold cm_scalar_expr_type, cm_integer_type, cm_is_pointer in TYPE; intuition discriminate.
Qed.
