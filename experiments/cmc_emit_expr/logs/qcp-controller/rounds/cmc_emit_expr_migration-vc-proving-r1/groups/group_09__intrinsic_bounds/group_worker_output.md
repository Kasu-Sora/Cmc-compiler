# intrinsic_bounds

Completed the six assigned split goals and the three assigned top-level VCs. Each split proof starts with `LLM_pre_process` and an explicit closer; each top-level proof uses `aggressive_pre_process` followed solely by the corresponding `Goal_apply` branches. The group library is unchanged.

The proofs eliminate non-intrinsic constructors, derive `lvalue = 0`, and reduce the intrinsic code and temporary models. Child code bounds follow from the parent end-PC bound, nonnegative PC, nonnegative child length, and fixed suffix lengths. Child temporary bounds are the parent's identical temporary bound.

The first development check failed because `cbn` left the conditional code wrapper folded. A successful debug call exposed the remaining wrapper. Explicit unfolding and `Z.eqb_refl` rewriting repaired both code and temporary reductions. The second development check passed, and the exact group-check passed. Controller acceptance after sealing remains separate.

```json
{
  "development_calls": 2,
  "development_failed": 1,
  "debug_calls": 1,
  "debug_failed": 0,
  "exact_calls": 1,
  "exact_failed": 0,
  "new_helpers": 0
}
```
