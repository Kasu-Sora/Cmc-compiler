Completed all four assigned top-level VCs and their eight split goals. Each split proof uses `LLM_pre_process` with explicit opcode reduction and `lia`; each top-level proof uses `aggressive_pre_process` followed only by the corresponding `Goal_apply` applications. No helper additions or substantive repair iterations were necessary.

The exact group check passed on its first invocation. Development and debug checks were not used. Controller acceptance remains separate from this precheck.

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
