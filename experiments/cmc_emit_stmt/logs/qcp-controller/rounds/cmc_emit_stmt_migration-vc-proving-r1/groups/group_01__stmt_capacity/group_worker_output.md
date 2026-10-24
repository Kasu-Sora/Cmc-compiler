# stmt_capacity proof notes

Completed seven top-level aggressive witnesses and all 71 assigned split goals. No annotation or contract change was required.

```json
{"development_calls":8,"development_failed":7,"debug_calls":2,"debug_failed":0,"exact_calls":1,"exact_failed":0,"new_helpers":4}
```

New helpers: `cm_expr_rvalue_length__stmt_capacity` (thin reuse of the verified expression pair length theorem), public `cm_emit_stmt_length__stmt_capacity` (structural induction generalized over all PCs and target/temp parameters), `cm_stmt_count_nonnegative__stmt_capacity`, and `cm_rvalue_count_nonnegative__stmt_capacity` (nonnegativity from list lengths).

Existing verified dependencies reused directly: `cm_emit_pair_lengths__store_bounds`, `cm_primitive_lengths__store_bounds`, and `cm_slot_type_encode__statement_normalization_safety`, alongside the existing statement typing/count/temp definitions and helper contracts. No snapshot candidate matched the new stmt length theorem.

Repairs made during proof development:
- Replaced assigned seed top-level Admitted placeholders with Abort for development, then proved all with Qed; unassigned spans stayed protected.
- Explicitly unfolded FP address and return epilogue lists when cbn left their lengths opaque in the structural length proof.
- Used all-goal selectors after preprocessing because closed pure opcode goals otherwise triggered No such goal.
- Unfolded expression temp projection and used Z.max_spec to derive child temp bounds from the enclosing statement bound.
- Rewrote the function lookup equality before deriving init/return type well-formedness.
- Exposed nonnegativity of char normalization count in enclosing endpoint bounds.
- After all splits compiled, shortened direct fact/end-point proofs and connected each aggressive branch to its assigned split via Goal_apply. The first exact check passed.

The statement length identity is unconditional: emitted list length equals the existing mathematical stmt count for arbitrary lookup policy, program, function id, statement, PC, temp, break target, and continue target. No execution semantics or termination claim is added.
