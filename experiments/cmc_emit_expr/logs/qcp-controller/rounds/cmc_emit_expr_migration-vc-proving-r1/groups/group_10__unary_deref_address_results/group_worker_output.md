# Unary dereference and address results

Completed the four assigned return VCs and their spatial split goals. Each split proof substitutes the expression constructor and operator, derives the lvalue flag from existing bounds and branch premises, and rewrites a reflexive code-model equality. Append associativity closes the dereference rvalue branch; empty append normalization closes the address lvalue branch. Each top-level proof uses aggressive preprocessing and its corresponding Goal_apply.

Initial development checks exposed that implicit simplification left the code-model terms unchanged under the emitter-plan predicate. Explicit reflexive equalities resolved this. The final open goal was the empty tail prefix in the address lvalue branch, resolved by definitional normalization. No library changes or new helpers were needed.

Three development calls failed during those repairs. Both debug calls passed. The exact group check passed on its first call. Controller finalization and acceptance remain separate.

```json
{"development_calls":3,"development_failed":3,"debug_calls":2,"debug_failed":0,"exact_calls":1,"exact_failed":0,"new_helpers":0}
```
