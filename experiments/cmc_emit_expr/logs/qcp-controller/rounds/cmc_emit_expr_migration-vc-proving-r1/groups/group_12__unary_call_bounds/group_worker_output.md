# unary_call_bounds

Completed all five assigned top-level VCs and all ten assigned split goals. Shape goals use definitional equality; call bounds follow from the existing parent end-PC bound after shape and branch substitutions. Every top-level proof uses the assigned aggressive route and corresponding Goal_apply branches. No helpers or library changes were required.

The first development check failed because preprocessing already closed a shape goal before its follow-up tactic. Restricting follow-up closers to remaining goals repaired this. The second development check and the exact group-check both passed. Final controller acceptance remains separate.

```json
{
  "development_calls": 2,
  "development_failed": 1,
  "debug_calls": 0,
  "debug_failed": 0,
  "exact_calls": 1,
  "exact_failed": 0,
  "new_helpers": 0
}
```
