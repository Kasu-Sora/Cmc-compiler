Completed all three assigned unary arithmetic result VCs and their spatial split goals. Each top-level proof uses aggressive preprocessing followed only by its assigned Goal_apply. Split proofs substitute expression shape and branch values, reduce code-selection guards, reassociate append, and cancel the unchanged spatial resources. No helpers or imports were added; the group library remains unchanged.

Two initial development checks exposed incomplete cancellation in the negation result because the code-selection definition and equality guards were not reduced. Explicit unfolding of cm_expr_code_for and reduction of Z.eqb repaired that proof. Both debug calls succeeded; the second showed no remaining goals. The third development check and the exact group check passed. Controller acceptance after finalization remains separate.

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
