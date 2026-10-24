Require Export SimpleC.EE.QCP_demos_human.cmc_type_operations_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_binary_value_type_ready p st op l r a b ty :
 cm_binary_types op a b ty -> cm_value_type_compatible l a -> cm_value_type_compatible r b -> cm_binary_ok p op l r st=true -> cm_value_type_compatible (cm_binary_value p op l r ty st) ty.
Proof.
 intros [BOUND BT] L R OK.
 assert (OPS: op=0 \/ op=1 \/ op=2 \/ op=3 \/ op=4 \/ op=5 \/ op=6 \/ op=7 \/ op=8 \/ op=9 \/ op=10 \/ op=11 \/ op=12) by lia.
 destruct OPS as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]];
 cbv beta iota zeta delta [Z.eqb Pos.eqb Z.leb Z.compare Pos.compare Pos.compare_cont orb andb cm_binary_value cm_binary_ok] in BT,OK|-*.
 all: try solve [assert (ty=CMIntTy) by tauto; subst ty; left; reflexivity].
 - destruct BT as [[AI [BI ->]]|[[AP [BI ->]]|[BP [AI ->]]]].
   + rewrite (cm_integer_pointerb_false _ _ L AI),?(cm_integer_pointerb_false _ _ R BI); left; reflexivity.
   + rewrite (cm_pointer_pointerb_true _ _ L AP) in OK|-*.
     rewrite (cm_pointer_pointee_type _ AP) in L|-*; eapply cm_ptr_shift_type_ready; eauto.
   + rewrite (cm_integer_pointerb_false _ _ L AI),(cm_pointer_pointerb_true _ _ R BP) in OK|-*.
     rewrite (cm_pointer_pointee_type _ BP) in R|-*; eapply cm_ptr_shift_type_ready; eauto.
 - destruct BT as [[AI [BI ->]]|[[AP [BI ->]]|[EQ [AP ->]]]].
   + rewrite (cm_integer_pointerb_false _ _ L AI),?(cm_integer_pointerb_false _ _ R BI); left; reflexivity.
   + rewrite (cm_pointer_pointerb_true _ _ L AP),?(cm_integer_pointerb_false _ _ R BI) in OK|-*.
     rewrite (cm_pointer_pointee_type _ AP) in L|-*; eapply cm_ptr_shift_type_ready; eauto.
   + subst b; rewrite (cm_pointer_pointerb_true _ _ L AP),(cm_pointer_pointerb_true _ _ R AP); left; reflexivity.
Qed.
