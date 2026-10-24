# Intrinsic constants

Completed all six assigned top-level witnesses and all twelve split goals. Each split proof uses `LLM_pre_process ltac:(cbn; lia)`. Each remaining top-level branch is closed by the corresponding `Goal_apply`. No helpers or imports were added; the group library is unchanged.

The initial development check reached witness 19 and found an extra branch bullet: `aggressive_pre_process` already discharges the `CMCharTy` well-formedness branch, leaving only the encoding equality branch. Removed the redundant second bullet while keeping its split lemma proved. The subsequent complete group check passed.

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
