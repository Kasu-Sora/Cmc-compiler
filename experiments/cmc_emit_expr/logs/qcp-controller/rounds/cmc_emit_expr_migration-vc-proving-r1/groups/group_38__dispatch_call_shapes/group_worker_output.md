Completed all five assigned shape split goals by unfolding the existing `cm_expr_shape` premise, using an explicit closer in `LLM_pre_process`. Each assigned top-level proof uses `aggressive_pre_process` followed by its corresponding `Goal_apply`.

The exact group-check passed on the first invocation. No repair iteration or helper was needed; the group library is unchanged. Final acceptance remains the controller's finalize-delivery validation.

```json
{
  "development_calls": 0,
  "development_failed": 0,
  "debug_calls": 0,
  "debug_failed": 0,
  "exact_calls": 1,
  "exact_failed": 0,
  "new_helpers": 0
}
```
