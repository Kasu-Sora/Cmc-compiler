# Expr/init/return plan transitions

Completed the four assigned split goals and their aggressive top-level dispatches. Constructor discrimination exposes the statement model without recursive selector rewriting. The plan lists are normalized with append associativity, and identical emitter resources are cancelled. No new helper or import is required; the library remains unchanged.

Two development failures were incomplete initializer proofs: the binding-address definition needed explicit unfolding, then its constant positive equality needed `Pos.eqb` reduction in addition to `Z.eqb`. Two debug calls exposed the remaining expressions. The third development call and the exact group check passed. An initial text-edit assertion mismatch (multiline versus inline seed proof placeholders) made no file changes and was repaired before the first check.

```json
{
  "development_calls": 3,
  "development_failed": 2,
  "debug_calls": 2,
  "debug_failed": 0,
  "exact_calls": 1,
  "exact_failed": 0,
  "new_helpers": 0
}
```
