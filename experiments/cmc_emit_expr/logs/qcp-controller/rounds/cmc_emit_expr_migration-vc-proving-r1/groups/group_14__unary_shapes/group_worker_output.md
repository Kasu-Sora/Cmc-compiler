Completed the five assigned unary shape witnesses (25–29) and their split goals. Each split goal closes using `LLM_pre_process ltac:(lia || nia || int_auto)`. Each top-level proof uses `aggressive_pre_process` followed only by the corresponding `Goal_apply`.

The initial development check failed with “No such goal” because preprocessing had already closed the first split goal. Removed the redundant trailing pure-goal tactics from all five split proofs. The subsequent exact group-check passed with exit code 0. No helper or library changes were needed. Final controller acceptance remains separate.

```json
{
  "development_calls": 1,
  "development_failed": 1,
  "debug_calls": 0,
  "debug_failed": 0,
  "exact_calls": 1,
  "exact_failed": 0,
  "new_helpers": 0
}
```
