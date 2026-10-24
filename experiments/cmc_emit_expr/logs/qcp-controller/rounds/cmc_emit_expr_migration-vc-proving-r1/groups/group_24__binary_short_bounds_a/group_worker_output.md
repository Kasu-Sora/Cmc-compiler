Completed all four assigned top-level VCs and nine split goals. Each split begins with `LLM_pre_process`; each top-level proof uses `aggressive_pre_process` followed only by the corresponding `Goal_apply` branches. The library needed no additions.

Code bounds follow from the parent end-pc bound, the existing exact code-length lemma, and nonnegative child lengths. Temporary bounds follow from the parent maximum budget. Substantive proof repairs exposed the pure safety goals using `dump_pre_spatial`, evaluated both integer and positive equality guards, and explicitly unfolded the child temporary wrapper. The initial development invocation also required replacing assigned seed stubs before compilation.

The final development check and exact group check both passed. Three debug invocations completed successfully and displayed the arithmetic states used for the repairs. Controller acceptance remains separate.

```json
{
  "development_calls": 6,
  "development_failed": 5,
  "debug_calls": 3,
  "debug_failed": 0,
  "exact_calls": 1,
  "exact_failed": 0,
  "new_helpers": 0
}
```
