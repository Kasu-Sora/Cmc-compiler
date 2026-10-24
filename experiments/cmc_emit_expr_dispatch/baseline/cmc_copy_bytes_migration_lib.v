From Coq Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.

Definition cmc_uint8_buffer_nonnull (p : Z) (bytes : list Z) : Prop :=
  bytes = [] \/ p <> 0.
