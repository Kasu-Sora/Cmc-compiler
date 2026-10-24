Completed the three assigned VCs and their spatial split goals. Each split proof starts with `LLM_pre_process` and an explicit arithmetic closer; each top-level proof uses `aggressive_pre_process` followed by its `Goal_apply`.

The proofs substitute the assignment shape and lvalue branch, explicitly unfold `cm_expr_code_for`, reduce the constructor projections, and normalize list association and program-counter addition before spatial cancellation. The empty lvalue branch additionally reduces nil appends. No helpers or imports were added; the group library remains unchanged.

The first development check exposed an unreduced code definition. The second exposed the remaining nil append in the empty-code branch. After these local proof repairs, the third development check passed. One debug call passed and displayed the intermediate goal. The exact group check passed on its first call. Final controller acceptance remains separate.

```json
{
  "development_calls": 3,
  "development_failed": 2,
  "debug_calls": 1,
  "debug_failed": 0,
  "exact_calls": 1,
  "exact_failed": 0,
  "new_helpers": 0
}
```
