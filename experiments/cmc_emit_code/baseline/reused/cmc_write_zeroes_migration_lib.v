From Coq Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.

From Coq Require Import Lia.
Lemma zeros_snoc__zero_step : forall n : Z,
  0 <= n -> repeat 0 (Z.to_nat (n + 1)) = repeat 0 (Z.to_nat n) ++ (0 :: nil).
Proof.
  intros n Hn.
  rewrite Z2Nat.inj_add by lia.
  rewrite repeat_app.
  reflexivity.
Qed.
