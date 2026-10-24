# index_results_plans

Completed all four assigned top-level VCs and their spatial split goals. Each split uses `LLM_pre_process` with an explicit closer, and each top-level proof uses `aggressive_pre_process` followed only by the corresponding `Goal_apply`.

The proofs preserve emitter ownership and normalize the emitted instruction lists using constructor reduction, the optional-load guard, append associativity, and the equivalent program-counter sums. No helper or import was added; the group library is unchanged.

The first development check found an incomplete cancellation because `cbn` had left `cm_expr_code_for` folded. Explicit unfolding followed by reduction of `Z.eqb` resolved it. The debug call succeeded, the second development check succeeded, and the exact group check succeeded. Controller acceptance remains separate.

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
