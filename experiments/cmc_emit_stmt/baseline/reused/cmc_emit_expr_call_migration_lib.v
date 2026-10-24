(* Exact mathematical code equations from cmc_codegen.c:650-881.
   This shared model closure covers every source expression, independently of
   the three runtime bodies verified in this module. cm_emit_expr remains an
   external implementation-proof dependency from the original source header. *)
From Coq Require Import ZArith List Bool Lia.
From AUXLib Require Import ListLib.
Require Export SimpleC.EE.QCP_demos_human.cmc_emit_expr_simple_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_count_context_migration_lib.
Import ListNotations.
Local Open Scope Z_scope.

Record cm_emit_pair := CMEmitPair {cm_lcode_of:list tvm_inst; cm_rcode_of:list tvm_inst}.
Definition cm_pointer_scale p e := cm_type_size (cm_program_structs p) (cm_pointee (cm_expr_type e)).
Definition cm_binary_finish_code policy p fid op lhs rhs temp :=
 cm_temp_load_code policy p fid temp ++
 (if (Z.eqb op 8 && cm_pointerb (cm_expr_type rhs))%bool then
 [TVMInst TVMPushOp (cm_pointer_scale p rhs); TVMInst TVMMulOp 0; TVMInst TVMSwapOp 0; TVMInst TVMAddOp 0]
 else [TVMInst TVMSwapOp 0] ++
 (if (Z.eqb op 8 && cm_pointerb (cm_expr_type lhs))%bool then
 [TVMInst TVMPushOp (cm_pointer_scale p lhs); TVMInst TVMMulOp 0; TVMInst TVMAddOp 0]
 else if (Z.eqb op 9 && cm_pointerb (cm_expr_type lhs) && cm_pointerb (cm_expr_type rhs))%bool then
 [TVMInst TVMSubOp 0; TVMInst TVMPushOp (cm_pointer_scale p lhs); TVMInst TVMDivOp 0]
 else if (Z.eqb op 9 && cm_pointerb (cm_expr_type lhs))%bool then
 [TVMInst TVMPushOp (cm_pointer_scale p lhs); TVMInst TVMMulOp 0; TVMInst TVMSubOp 0]
 else [TVMInst (cm_binary_opcode op) 0])).
Fixpoint cm_emit_args_reload policy p fid slot (args:list cm_expr) : list tvm_inst :=
 match args with []=>[] | _::rest=>cm_temp_load_code policy p fid slot ++ cm_emit_args_reload policy p fid (slot+1) rest end.
Fixpoint cm_emit_expr_pair policy p fid pc temp (e:cm_expr) {struct e} : cm_emit_pair :=
 match e with
 | CMConstE n ty=>CMEmitPair [] (cm_push_code (cm_const_immediate ty n))
 | CMStringE sid _=>CMEmitPair [] (cm_push_code (cm_string_address p sid))
 | CMVarE scope slot ty=>CMEmitPair (cm_var_lcode policy p fid scope slot) (cm_var_rcode policy p fid scope slot ty)
 | CMAssignE dst src ty=>CMEmitPair []
   (cm_lcode_of (cm_emit_expr_pair policy p fid pc temp dst) ++
    cm_temp_store_code policy p fid temp ++
    cm_rcode_of (cm_emit_expr_pair policy p fid (pc+cm_lvalue_code_count policy p fid dst+5) (temp+1) src) ++
    cm_char_normalize_code ty ++ cm_temp_load_code policy p fid temp ++ cm_store_code ty ++
    cm_temp_load_code policy p fid temp ++ cm_load_code ty)
 | CMBinaryE op lhs rhs _=>CMEmitPair []
   (if (Z.eqb op 0 || Z.eqb op 1)%bool then
     cm_rcode_of (cm_emit_expr_pair policy p fid pc temp lhs) ++
     [TVMInst (if Z.eqb op 0 then TVMJnzOp else TVMJzOp) (pc+cm_rvalue_code_count policy p fid lhs+cm_rvalue_code_count policy p fid rhs+4)] ++
     cm_rcode_of (cm_emit_expr_pair policy p fid (pc+cm_rvalue_code_count policy p fid lhs+1) temp rhs) ++
     [TVMInst TVMPushOp 0; TVMInst TVMNeOp 0;
      TVMInst TVMJmpOp (pc+cm_rvalue_code_count policy p fid lhs+cm_rvalue_code_count policy p fid rhs+5);
      TVMInst TVMPushOp (if Z.eqb op 0 then 1 else 0)]
   else cm_rcode_of (cm_emit_expr_pair policy p fid pc temp lhs) ++ cm_temp_store_code policy p fid temp ++
     cm_rcode_of (cm_emit_expr_pair policy p fid (pc+cm_rvalue_code_count policy p fid lhs+5) (temp+1) rhs) ++
     cm_binary_finish_code policy p fid op lhs rhs temp)
 | CMUnaryE op arg ty=>let c:=cm_emit_expr_pair policy p fid pc temp arg in
   if Z.eqb op 2 then CMEmitPair (cm_rcode_of c) (cm_rcode_of c ++ cm_load_code ty)
   else if Z.eqb op 3 then CMEmitPair [] (cm_lcode_of c)
   else CMEmitPair [] (cm_rcode_of c ++ [TVMInst TVMPushOp (if Z.eqb op 0 then -1 else 0); TVMInst (if Z.eqb op 0 then TVMMulOp else TVMEqOp) 0])
 | CMIndexE base index ty=>
   let addr:=cm_rcode_of (cm_emit_expr_pair policy p fid pc temp base) ++ cm_temp_store_code policy p fid temp ++
     cm_rcode_of (cm_emit_expr_pair policy p fid (pc+cm_rvalue_code_count policy p fid base+5) (temp+1) index) ++
     [TVMInst TVMPushOp (cm_type_size (cm_program_structs p) ty); TVMInst TVMMulOp 0] ++
     cm_temp_load_code policy p fid temp ++ [TVMInst TVMAddOp 0] in CMEmitPair addr (addr ++ cm_load_code ty)
 | CMMemberE base mid ty=>
   let addr:=cm_rcode_of (cm_emit_expr_pair policy p fid pc temp base) ++
     [TVMInst TVMPushOp (cm_member_offset (cm_program_structs p) (cm_struct_id (cm_pointee (cm_expr_type base))) mid); TVMInst TVMAddOp 0] in
   CMEmitPair addr (addr ++ if Z.eqb (cm_member_array_code p (cm_expr_type base) mid) 0 then cm_load_code ty else [])
 | CMCallE callee args _=>
   let fix store pc slot scratch (args:list cm_expr) {struct args} : list tvm_inst := match args with
   | []=>[] | arg::rest=>cm_rcode_of (cm_emit_expr_pair policy p fid pc scratch arg) ++
     cm_temp_store_code policy p fid slot ++ store (pc+cm_rvalue_code_count policy p fid arg+5) (slot+1) scratch rest end
   in CMEmitPair [] (store pc temp (temp+Zlength args) args ++ cm_emit_args_reload policy p fid temp args ++ [TVMInst TVMCallOp (cm_function_pc policy p callee)])
 | CMSizeofE asked _=>CMEmitPair [] (cm_push_code (cm_type_size (cm_program_structs p) asked))
 | CMGetcE _=>CMEmitPair [] [TVMInst TVMGetcOp 0]
 | CMPutcE arg _=>CMEmitPair [] (cm_rcode_of (cm_emit_expr_pair policy p fid pc temp arg) ++ [TVMInst TVMDupOp 0; TVMInst TVMPutcOp 0])
 | CMPutiE arg _=>CMEmitPair [] (cm_rcode_of (cm_emit_expr_pair policy p fid pc temp arg) ++ [TVMInst TVMDupOp 0; TVMInst TVMPutiOp 0])
 | CMExitE arg _=>CMEmitPair [] (cm_rcode_of (cm_emit_expr_pair policy p fid pc temp arg) ++ cm_char_normalize_code CMCharTy ++ [TVMInst TVMHaltOp 0])
 end.
Definition cm_expr_code_for policy p fid pc temp e (lvalue:Z) :=
 if Z.eqb lvalue 0 then cm_rcode_of (cm_emit_expr_pair policy p fid pc temp e)
 else cm_lcode_of (cm_emit_expr_pair policy p fid pc temp e).
Fixpoint cm_emit_args_store policy p fid pc slot scratch (args:list cm_expr) : list tvm_inst :=
 match args with []=>[] | arg::rest=>
 cm_expr_code_for policy p fid pc scratch arg 0 ++ cm_temp_store_code policy p fid slot ++
 cm_emit_args_store policy p fid (pc+cm_rvalue_code_count policy p fid arg+5) (slot+1) scratch rest end.
Definition cm_expr_temps_for e (lvalue:Z) := if Z.eqb lvalue 0 then cm_rtemps e else cm_ltemps e.


(* Source-private observations; head's empty-list value is never used. *)
Definition cm_args_head (args:list cm_expr) := hd (CMConstE 0 CMIntTy) args.
Definition cm_args_tail (args:list cm_expr) := tl args.
Definition cm_call_slots_tail (slots:list cm_slot_d) := tl slots.
Definition cm_call_args (e:cm_expr) := match e with CMCallE _ args _=>args | _=>[] end.

(* Transparent bridges; no additional model assumptions. *)
Lemma cm_call_code_equation policy p fid pc temp callee args ty :
 cm_expr_code_for policy p fid pc temp (CMCallE callee args ty) 0 =
 cm_emit_args_store policy p fid pc temp (temp+Zlength args) args ++
 cm_emit_args_reload policy p fid temp args ++ [TVMInst TVMCallOp (cm_function_pc policy p callee)].
Proof.
 change ((fix store pc slot scratch (xs:list cm_expr) {struct xs} : list tvm_inst :=
   match xs with []=>[] | a::t=>cm_rcode_of (cm_emit_expr_pair policy p fid pc scratch a) ++
   cm_temp_store_code policy p fid slot ++ store (pc+cm_rvalue_code_count policy p fid a+5) (slot+1) scratch t end)
   pc temp (temp+Zlength args) args ++
   (cm_emit_args_reload policy p fid temp args ++ [TVMInst TVMCallOp (cm_function_pc policy p callee)]) =
   cm_emit_args_store policy p fid pc temp (temp+Zlength args) args ++
   (cm_emit_args_reload policy p fid temp args ++ [TVMInst TVMCallOp (cm_function_pc policy p callee)])).
 f_equal. generalize (temp + Zlength args) as scratch.
 generalize temp as slot. intros slot scratch.
 revert pc slot scratch. induction args; intros; cbn [cm_emit_args_store cm_expr_code_for].
 - reflexivity.
 - rewrite IHargs. reflexivity.
Qed.
Lemma cm_call_lvalue_empty policy p fid pc temp callee args ty lvalue :
 lvalue <> 0 -> cm_expr_code_for policy p fid pc temp (CMCallE callee args ty) lvalue = [].
Proof. intros H. unfold cm_expr_code_for. apply Z.eqb_neq in H. rewrite H. reflexivity. Qed.
Lemma cm_call_source_coverage e :
 cm_rep_expr_kind e = 8 <-> e = CMCallE (cm_rep_expr_value e) (cm_call_args e) (cm_expr_type e).
Proof. destruct e; cbn [cm_rep_expr_kind cm_rep_expr_value cm_call_args cm_expr_type]; split; intros; try discriminate; reflexivity. Qed.
Lemma cm_call_args_observe a args :
 cm_args_head (a::args) = a /\ cm_args_tail (a::args) = args.
Proof. split; reflexivity. Qed.
Lemma cm_args_reload_length policy p fid slot args :
 Zlength (cm_emit_args_reload policy p fid slot args) = 5 * Zlength args.
Proof.
 revert slot. induction args; intro slot; cbn [cm_emit_args_reload].
 - reflexivity.
 - rewrite Zlength_app, IHargs, Zlength_cons.
   assert (Hload : Zlength (cm_temp_load_code policy p fid slot) = 5) by reflexivity.
   rewrite Hload. lia.
Qed.

Lemma cm_primitive_lengths__store_bounds policy p fid temp ty :
 Zlength (cm_temp_store_code policy p fid temp) = 5 /\
 Zlength (cm_temp_load_code policy p fid temp) = 5 /\
 Zlength (cm_load_code ty) = 1 /\
 Zlength (cm_store_code ty) = 1 /\
 Zlength (cm_char_normalize_code ty) = cm_char_normalize_count ty.
Proof. destruct ty; repeat split; reflexivity. Qed.
Lemma cm_emit_pair_lengths__store_bounds : forall policy p fid e pc temp,
 Zlength (cm_lcode_of (cm_emit_expr_pair policy p fid pc temp e)) = cm_lvalue_code_count policy p fid e /\
 Zlength (cm_rcode_of (cm_emit_expr_pair policy p fid pc temp e)) = cm_rvalue_code_count policy p fid e.
Proof.
 fix IH 4. intros policy p fid e pc temp.
 destruct e;
 cbn [cm_emit_expr_pair cm_lcode_of cm_rcode_of];
 unfold cm_lvalue_code_count, cm_rvalue_code_count;
 cbn [cm_expr_code_counts cm_lcount_of cm_rcount_of].
 all: try solve [
 unfold cm_var_lcode, cm_var_rcode, cm_binding_address_code,
 cm_binding_address_count, cm_binary_finish_code, cm_binary_tail_count;
 repeat match goal with |- context [if ?b then _ else _] => destruct b end;
 cbn [cm_lcode_of cm_rcode_of cm_lcount_of cm_rcount_of];
 repeat rewrite Zlength_app;
 repeat match goal with
 | |- context [Zlength (cm_lcode_of (cm_emit_expr_pair ?pol ?pr ?f ?pc0 ?t ?a))] =>
   rewrite (proj1 (IH pol pr f a pc0 t))
 | |- context [Zlength (cm_rcode_of (cm_emit_expr_pair ?pol ?pr ?f ?pc0 ?t ?a))] =>
   rewrite (proj2 (IH pol pr f a pc0 t))
 end;
 unfold cm_lvalue_code_count, cm_rvalue_code_count;
 repeat match goal with
 | |- context [Zlength (cm_temp_store_code ?pol ?pr ?f ?t)] =>
   rewrite (proj1 (cm_primitive_lengths__store_bounds pol pr f t CMIntTy))
 | |- context [Zlength (cm_temp_load_code ?pol ?pr ?f ?t)] =>
   rewrite (proj1 (proj2 (cm_primitive_lengths__store_bounds pol pr f t CMIntTy)))
 | |- context [Zlength (cm_load_code ?ty)] =>
   rewrite (proj1 (proj2 (proj2 (cm_primitive_lengths__store_bounds policy p fid temp ty))))
 | |- context [Zlength (cm_store_code ?ty)] =>
   rewrite (proj1 (proj2 (proj2 (proj2 (cm_primitive_lengths__store_bounds policy p fid temp ty)))))
 | |- context [Zlength (cm_char_normalize_code ?ty)] =>
   rewrite (proj2 (proj2 (proj2 (proj2 (cm_primitive_lengths__store_bounds policy p fid temp ty)))))
 end;
 cbn [cm_push_code cm_fp_relative_address_code];
 repeat rewrite Zlength_cons; rewrite ?Zlength_nil;
 cbn [cm_char_normalize_count]; split; lia].
 all: try (split; reflexivity).
 - unfold cm_var_lcode, cm_var_rcode, cm_binding_address_code, cm_binding_address_count.
   destruct (Z.eqb scope 0); destruct (Z.eqb (cm_binding_array_code policy p fid scope slot) 0);
   repeat rewrite Zlength_app;
   cbn [cm_push_code cm_fp_relative_address_code cm_load_code];
   repeat rewrite Zlength_cons; rewrite ?Zlength_nil.
   all: try (split; reflexivity).
 - split; [reflexivity|].
   rewrite !Zlength_app, cm_args_reload_length.
   rewrite Zlength_cons, Zlength_nil.
   generalize (temp + Zlength args) as scratch.
   revert pc temp. induction args as [|a t IHargs]; intros pc temp scratch.
   + reflexivity.
   + cbn [cm_args_code_count_of].
     rewrite !Zlength_app, Zlength_cons.
     rewrite (proj2 (IH policy p fid a pc scratch)).
     rewrite (proj1 (cm_primitive_lengths__store_bounds policy p fid temp CMIntTy)).
     pose proof (IHargs (pc + cm_rvalue_code_count policy p fid a + 5) (temp+1) scratch) as Htail.
     unfold cm_rvalue_code_count in *. lia.
Qed.
Lemma cm_args_apair_count_depth__call_bounds args :
 cm_acount (cm_args_apair args) = Zlength args /\
 0 <= cm_adepth (cm_args_apair args).
Proof.
 induction args as [|a args [Hcount Hdepth]].
 - split; reflexivity.
 - cbn [cm_args_apair cm_acount cm_adepth]. rewrite Zlength_cons.
   split; [lia|]. unfold cm_imax. eapply Z.le_trans; [exact Hdepth|apply Z.le_max_r].
Qed.
Lemma cm_slots_size_nonnegative__call_bounds structs slots :
 cm_slots_wf structs slots -> 0 <= cm_slots_size structs slots.
Proof.
 induction slots as [|s slots IH]; intro Hwf; [cbn; lia|].
 assert (Hhead : cm_slot_wf structs s).
 { specialize (Hwf 0). rewrite Zlength_cons in Hwf.
   pose proof (Zlength_nonneg slots). apply Hwf. lia. }
 assert (Htail : cm_slots_wf structs slots).
 { intros i Hi. specialize (Hwf (i+1)).
   rewrite Zlength_cons in Hwf.
   assert (Hb : 0 <= i+1 < Zlength slots+1) by lia.
   specialize (Hwf Hb). unfold cm_slot_at in Hwf |- *.
   replace (i+1) with (Z.succ i) in Hwf by lia.
   rewrite Z2Nat.inj_succ in Hwf by lia. exact Hwf. }
 specialize (IH Htail). unfold cm_slot_wf in Hhead.
 cbn [cm_slots_size]. lia.
Qed.
Lemma cm_rep_args_safe_of_length__call_bounds args :
 Zlength args <= 2147483647 -> cm_rep_args_safe args.
Proof.
 induction args as [|a args IH]; intro Hlen; [exact I|].
 rewrite Zlength_cons in Hlen. cbn [cm_rep_args_safe].
 unfold cm_rep_args_length. pose proof (Zlength_nonneg args).
 split; [lia|apply IH; lia].
Qed.
