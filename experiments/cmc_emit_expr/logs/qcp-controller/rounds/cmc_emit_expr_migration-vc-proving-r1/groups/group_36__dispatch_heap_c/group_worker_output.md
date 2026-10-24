Completed the five assigned dispatch heap folds, witnesses 20, 22, 24, 26, and 28, with all corresponding spatial split goals.

Each split proof rewrites `cm_expr_rep_node`, unfolds `cm_expr_node`, instantiates the existing child pointers, cancels the field cells and payload, and closes nonnullness from the antecedent. Each top-level proof uses `aggressive_pre_process` and the corresponding `Goal_apply` only. No library changes or helpers were needed.

The first development check failed because one cancellation step left the matching field resources. Debug inspection identified those remaining cells; repeating cancellation while it makes progress resolved the failure. The second development check and the exact group check both passed. Controller acceptance remains separate.

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
