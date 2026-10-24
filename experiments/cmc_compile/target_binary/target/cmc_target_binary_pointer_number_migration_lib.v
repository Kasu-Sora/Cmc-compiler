Require Export SimpleC.EE.QCP_demos_human.cmc_target_binary_pointer_tail_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma tower_sub_wrap_both a b : tower_sub(tower_wrap64 a)(tower_wrap64 b)=tower_sub a b.
Proof.
 unfold tower_sub;replace(tower_wrap64 a-tower_wrap64 b)with(a-b+(((b+9223372036854775808)/18446744073709551616)-((a+9223372036854775808)/18446744073709551616))*18446744073709551616).
 - apply tower_wrap64_periodic.
 - unfold tower_wrap64;pose proof(Z.div_mod(a+9223372036854775808)18446744073709551616 ltac:(lia));pose proof(Z.div_mod(b+9223372036854775808)18446744073709551616 ltac:(lia));lia.
Qed.
Lemma tower_add_neg_mul l r size : tower_add l(tower_mul(tower_neg r)size)=tower_sub l(tower_mul r size).
Proof.
 unfold tower_add,tower_mul,tower_neg,tower_sub;rewrite tower_wrap64_add_right.
 replace(tower_wrap64(-r)*size)with(size*tower_wrap64(-r))by ring.
 replace(l+size*tower_wrap64(-r))with(l-r*size+(-size*((-r+9223372036854775808)/18446744073709551616))*18446744073709551616).
 - rewrite tower_wrap64_periodic;replace(l-tower_wrap64(r*size))with(l-r*size+((r*size+9223372036854775808)/18446744073709551616)*18446744073709551616).
   + symmetry;apply tower_wrap64_periodic.
   + unfold tower_wrap64;pose proof(Z.div_mod(r*size+9223372036854775808)18446744073709551616 ltac:(lia));lia.
 - unfold tower_wrap64;pose proof(Z.div_mod(-r+9223372036854775808)18446744073709551616 ltac:(lia));nia.
Qed.
Lemma cm_binary_left_pointer_number p st op left right ty view : op=8 \/ op=9 ->
 cm_value_type_compatible left(CMPtrTy view) ->cm_is_pointerb(cm_value_type right)=false ->cm_binary_ok p op left right st=true ->
 cm_value_number st(cm_binary_value p op left right ty st)=cm_binary_number op(cm_value_number st left)(tower_mul(cm_value_number st right)(cm_type_size(cm_program_structs p)view)).
Proof.
 intros OPS TYPE RP OK;assert(LP:cm_is_pointerb(cm_value_type left)=true)by(exact(cm_compatible_pointerb _ _ TYPE)).
 destruct OPS as[-> | ->];cbn[cm_binary_value cm_binary_number cm_binary_ok Z.eqb Pos.eqb Z.leb Z.compare Pos.compare Pos.compare_cont andb orb]in OK|-*;rewrite LP,?RP in OK|-*;cbn[andb]in OK|-*.
 - now apply cm_ptr_add_number_bridge.
 - rewrite(cm_ptr_add_number_bridge _ _ _ _ _ TYPE OK);apply tower_add_neg_mul.
Qed.
Lemma cm_binary_right_pointer_number p st left right ty view :
 cm_value_type_compatible right(CMPtrTy view) ->cm_is_pointerb(cm_value_type left)=false ->cm_binary_ok p 8 left right st=true ->
 cm_value_number st(cm_binary_value p 8 left right ty st)=tower_add(cm_value_number st right)(tower_mul(cm_value_number st left)(cm_type_size(cm_program_structs p)view)).
Proof.
 intros TYPE LP OK;assert(RP:cm_is_pointerb(cm_value_type right)=true)by(exact(cm_compatible_pointerb _ _ TYPE)).
 cbn[cm_binary_value cm_binary_ok Z.eqb Pos.eqb Z.leb Z.compare Pos.compare Pos.compare_cont andb orb]in OK|-*;rewrite LP,RP in OK|-*;now apply cm_ptr_add_number_bridge.
Qed.
Lemma cm_pointer_difference_number st left right : cm_pointer_compatible st left right=true ->
 tower_sub(cm_value_number st left)(cm_value_number st right)=tower_sub(cm_ptr_offset left)(cm_ptr_offset right).
Proof.
 unfold cm_pointer_compatible;intro OK;repeat rewrite andb_true_iff in OK;destruct OK as[[[[[[[_ _]L]R]GEN]_]_]_];apply Z.eqb_eq in GEN.
 destruct left,right;cbn[cm_pointer_live cm_ptr_gen]in L,R;try discriminate.
 cbn[cm_ptr_gen]in GEN;subst gen0;cbn[cm_value_number cm_ptr_offset];rewrite tower_sub_wrap_both;unfold tower_sub;f_equal;ring.
Qed.
Lemma cm_binary_difference_number p st left right ty view :
 cm_value_type_compatible left(CMPtrTy view) ->cm_is_pointerb(cm_value_type right)=true ->cm_binary_ok p 9 left right st=true ->
 cm_value_number st(cm_binary_value p 9 left right ty st)=tower_div(tower_sub(cm_value_number st left)(cm_value_number st right))(cm_type_size(cm_program_structs p)view).
Proof.
 intros TYPE RP OK;assert(LP:cm_is_pointerb(cm_value_type left)=true)by(exact(cm_compatible_pointerb _ _ TYPE)).
 cbn[cm_binary_value cm_binary_ok Z.eqb Pos.eqb Z.leb Z.compare Pos.compare Pos.compare_cont andb orb]in OK|-*;rewrite LP,RP in OK|-*;cbn[andb]in OK|-*.
 change(tower_wrap64(tower_div(tower_sub(cm_ptr_offset left)(cm_ptr_offset right))(cm_type_size(cm_program_structs p)(cm_ptr_view left)))=tower_div(tower_sub(cm_value_number st left)(cm_value_number st right))(cm_type_size(cm_program_structs p)view)).
 assert(WRAP:forall a b,tower_wrap64(tower_div a b)=tower_div a b)by(intros;apply tower_wrap64_idempotent);rewrite WRAP.
 unfold cm_ptr_diff_ok in OK;repeat rewrite andb_true_iff in OK;destruct OK as[[COMP _]_].
 rewrite(cm_pointer_difference_number _ _ _ COMP);f_equal;f_equal;apply cm_pointer_value_view;[exact TYPE|].
 intro EQ;subst left;unfold cm_pointer_compatible in COMP;discriminate.
Qed.
