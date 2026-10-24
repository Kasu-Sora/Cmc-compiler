# Intrinsic results proof delivery

Completed all six assigned intrinsic return witnesses and their spatial split goals. Each split opens with explicit `LLM_pre_process`; each top-level proof uses `aggressive_pre_process` followed only by its corresponding `Goal_apply`.

The proofs establish the lvalue flag, discriminate the intrinsic constructor, unfold the expression code selector, normalize list append, and cancel the retained expression, program, function, and emitter resources. No helpers or library changes were needed.

The first development check exposed an unreduced code selector. Explicit `unfold cm_expr_code_for` and reduction of `Z.eqb` repaired the proof. Two debug calls succeeded; the second showed no remaining goals. The second development check and the exact group check passed.

```json
{"development_calls":2,"development_failed":1,"debug_calls":2,"debug_failed":0,"exact_calls":1,"exact_failed":0,"new_helpers":0}
```
