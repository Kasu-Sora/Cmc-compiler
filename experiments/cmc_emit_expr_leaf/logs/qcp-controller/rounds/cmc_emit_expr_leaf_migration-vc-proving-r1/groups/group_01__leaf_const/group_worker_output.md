# leaf_const proof development notes

Completed the four assigned top-level witnesses and their seven assigned split goals. The top-level proofs use aggressive_pre_process and only Goal_apply branch dispatch. The library was unchanged; no public or local helpers or imports were added.

Actual optional feedback invocations: group-development 8; coq-debug 3; exact group-check 1. The eight development invocations each exposed a recoverable proof-script issue; the three debug invocations inspected proof states.

Development failures and repairs, in order:

1. Intros already extracted the nonnull pure assertion, so a subsequent Intros_p had no assertion to consume. Removed the redundant extraction and used the hypothesis already in context.
2. The leaf payload equalities were a conjunction. Destructed that conjunction before substituting the three zero pointers.
3. The aggressive preprocessing branch order placed the spatial branch first. Reordered Goal_apply dispatch after inspecting the generated goals.
4. cbn left the emitter code expression folded. Explicitly unfolded cm_leaf_code_for, cm_leaf_rvalue, and cm_push_code.
5. Bare cancel left matching emitter and node resources under different association/order. Explicitly canceled the emitter plan before canceling the remaining fields.
6. The unqualified =? notation selected string scope. Used Z.eqb explicitly.
7. The second return branch needed the same explicit emitter-plan cancellation.
8. Preprocessing already closed the reflexive opcode equality. Removed the redundant following tactics and supplied reflexivity as the preprocessing closer.

No annotation or specification gap was identified. All writes stayed within the assigned proof spans and designated debug/report paths.
