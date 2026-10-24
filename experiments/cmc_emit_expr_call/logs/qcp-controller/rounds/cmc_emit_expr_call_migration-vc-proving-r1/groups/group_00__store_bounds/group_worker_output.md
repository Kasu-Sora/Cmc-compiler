# store_bounds proof notes

Completed the assigned store-bound witness and all twelve aggressive split goals. The top-level proof dispatches each branch through its corresponding Goal_apply lemma.

Added cm_primitive_lengths__store_bounds and the planned public cm_emit_pair_lengths__store_bounds. The latter proves both length/count equalities for every expression without a wellformedness premise, using structural recursion on expressions and an inner induction on call arguments with generalized program counter, slot, and scratch values. This is a mathematical code-model theorem; it does not claim verification of the external expression-emitter implementation.

Proof effort: 7 debug invocations, 3 development invocations, and 1 exact group invocation. Two debug invocations failed while attempting to replace an internal recursive store function by the top-level store definition through conversion; the proof instead performs induction directly on the internal function. Two development invocations failed because restricted cbn did not unfold observation/selection wrappers; explicit unfolding repaired those steps. No annotation change was needed.
