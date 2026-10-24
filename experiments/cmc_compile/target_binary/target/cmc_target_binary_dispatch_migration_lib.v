Require Export SimpleC.EE.QCP_demos_human.cmc_target_binary_pointer_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_typed_type_size_signed policy p ty : cm_typed_program policy p ->tower_signed64(cm_type_size(cm_program_structs p)ty).
Proof.
 intros[STRUCTS _];destruct ty;cbn[cm_type_size];unfold tower_signed64;try lia.
 unfold cm_struct_size;destruct((0<=?sid)&&(sid<?Zlength(cm_program_structs p)))eqn:E;[|lia].
 apply andb_true_iff in E;destruct E as[L H];apply Z.leb_le in L;apply Z.ltb_lt in H;specialize(STRUCTS sid(conj L H));destruct STRUCTS as[_[_ S]];lia.
Qed.
Lemma cm_integer_type_pointerb ty : cm_integer_type ty ->cm_pointerb ty=false.
Proof. intros[-> | ->];reflexivity. Qed.
Lemma cm_binary_difference_scale_nonzero p st left right view :
 cm_value_type_compatible left(CMPtrTy view) ->cm_is_pointerb(cm_value_type right)=true ->cm_binary_ok p 9 left right st=true ->
 cm_type_size(cm_program_structs p)view<>0.
Proof.
 intros TYPE RP OK;assert(LP:cm_is_pointerb(cm_value_type left)=true)by(exact(cm_compatible_pointerb _ _ TYPE)).
 cbn[cm_binary_ok Z.eqb Pos.eqb Z.leb Z.compare Pos.compare Pos.compare_cont andb orb]in OK;rewrite LP,RP in OK;cbn[andb]in OK.
 unfold cm_ptr_diff_ok in OK;repeat rewrite andb_true_iff in OK;destruct OK as[[COMP POS]_];apply Z.ltb_lt in POS.
 assert(VIEW:cm_ptr_view left=view)by(apply cm_pointer_value_view;[exact TYPE|intro EQ;subst;unfold cm_pointer_compatible in COMP;discriminate]).
 rewrite VIEW in POS;lia.
Qed.
Lemma cm_target_v_binary_ordinary_step sp ap p fid v st op lhs rhs left ty pc temp b c owner ob oc tail spills saved calls target :
 let ann:=CMAnnotation pc temp b c(CMACursor(CABinRP op lhs rhs left ty)owner ob oc::tail)spills saved calls in
 cm_typed_program(cm_source_function_policy sp)p ->
 cm_runtime_core(cm_source_function_policy sp)ap p fid st ann ->0<=fid ->
 0<=owner<cm_temp_slots(cm_source_function_at sp fid p) ->cm_spill_holds owner left spills ->op<>0 ->op<>1 ->
 cm_binary_types op(cm_expr_type lhs)(cm_expr_type rhs)ty ->cm_value_type_compatible left(cm_expr_type lhs) ->cm_value_type_compatible v(cm_expr_type rhs) ->cm_binary_ok p op left v st=true ->
 cm_task_layout sp ap p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))ann ->
 cm_task_target_sim(cm_source_function_policy sp)p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))target ann ->
 cm_target_step_result sp ap p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))target ann.
Proof.
 cbn zeta;intros TYPED RT FID SLOT HOLD N0 N1[BOUND BT]L R OK LAYOUT SIM.
 destruct(Z.eq_dec op 8)as[-> | N8].
 - cbn[Z.eqb Pos.eqb Z.leb Z.compare Pos.compare Pos.compare_cont orb andb]in BT.
   destruct BT as[[AI[BI TY]]|[[AP[BI TY]]|[BP[AI TY]]]].
   + eapply cm_target_v_binary_numeric_step;try eassumption;try lia;intros _;split;now apply cm_integer_type_pointerb.
   + eapply cm_target_v_binary_left_pointer_step;try eassumption;[now left|apply cm_pointer_pointee_type;exact AP|now apply cm_integer_type_pointerb].
   + eapply cm_target_v_binary_right_pointer_step;try eassumption;[apply cm_pointer_pointee_type;exact BP|now apply cm_integer_type_pointerb].
 - destruct(Z.eq_dec op 9)as[-> | N9].
   + cbn[Z.eqb Pos.eqb Z.leb Z.compare Pos.compare Pos.compare_cont orb andb]in BT.
     destruct BT as[[AI[BI TY]]|[[AP[BI TY]]|[EQ[AP TY]]]].
     * eapply cm_target_v_binary_numeric_step;try eassumption;try lia;intros _;split;now apply cm_integer_type_pointerb.
     * eapply cm_target_v_binary_left_pointer_step;try eassumption;[now right|apply cm_pointer_pointee_type;exact AP|now apply cm_integer_type_pointerb].
     * assert(LE:cm_expr_type lhs=CMPtrTy(cm_pointee(cm_expr_type lhs)))by(now apply cm_pointer_pointee_type).
       assert(RP:cm_pointerb(cm_expr_type rhs)=true)by(rewrite <-EQ,LE;reflexivity).
       eapply cm_target_v_binary_difference_pointer_step;try eassumption.
       -- unfold cm_pointer_scale;now apply cm_typed_type_size_signed with(cm_source_function_policy sp).
       -- unfold cm_pointer_scale;eapply cm_binary_difference_scale_nonzero;[rewrite <-LE;exact L|rewrite(cm_compatible_pointerb _ _ R);exact RP|exact OK].
   + eapply cm_target_v_binary_numeric_step;try eassumption;try lia;intros[H|H];contradiction.
Qed.
