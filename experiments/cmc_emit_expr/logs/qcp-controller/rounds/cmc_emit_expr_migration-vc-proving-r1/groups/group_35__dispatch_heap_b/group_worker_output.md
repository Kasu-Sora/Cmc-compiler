Completed the five assigned dispatch heap split goals and their top-level VCs. Each split proof rewrites `cm_expr_rep_node`, unfolds `cm_expr_node`, supplies the existing `xa`, `xb`, and `xargs`, cancels the matching heap resources, and retains the existing non-null premise. Each top-level proof uses `aggressive_pre_process` followed only by its assigned `Goal_apply`.

The first development check failed because a single `cancel` removed the payload but left the seven matching field cells. Debugging exposed that residual entailment; changing to `repeat progress cancel` closed the fields. The second development check passed, and the exact group check passed. No helper or library changes were needed.

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
