# while_call_facts

Completed the four assigned top-level witnesses and ten aggressive split goals. The library is unchanged; no helpers were added.

Constructor projections reduce to existing well-formedness/count premises. The while endpoint uses the existing code-count bound and arithmetic reassociation; recursive-call endpoint goals use the existing emission-length bound after rewriting the loop-end argument to the canonical `cm_stmt_code_count (CMWhileS ...)` form.

Repair: the first development check failed because arithmetic was applied while the pure obligation was still wrapped in a separation entailment. The debug state showed all needed bounds already present. Added `dump_pre_spatial` before ordinary arithmetic/rewrite reasoning. The next development check passed. No annotation or specification change was needed. Controller finalization remains the mandatory acceptance step.

```json
{
  "development_calls": 2,
  "development_failed": 1,
  "debug_calls": 1,
  "debug_failed": 0,
  "exact_calls": 0,
  "exact_failed": 0,
  "new_helpers": 0
}
```
