# Emitter wrapper proof

Completed the assigned entailment, return spatial split, and aggressive return dispatcher. No new helper or library edit was needed.

The entailment opens the existential raw representation, preserves its patch equation, derives the capacity bound from the owned Int field with `store_int_range`, and converts both zero-start array segments to full arrays. The return proof reuses `cm_patch_code_length`, converts full arrays back to segments, and preserves all fields and undefined capacity suffixes. Neither proof assumes that the raw prefix equals its resolved form.

```json
{
  "development_calls": 4,
  "development_failed": 3,
  "debug_calls": 0,
  "debug_failed": 0,
  "exact_calls": 1,
  "exact_failed": 0,
  "new_helpers": 0
}
```

Actual repair notes:

1. `Intros raw ops imms` already extracts pure facts; removed redundant `Intros_p` calls that failed because no pure assertion remained.
2. Unfolding this project's `Zlength` does not expose a natural-number list length suitable for `map_length`; changed projection-length reasoning to direct induction with `Zlength_cons`.
3. Cleared irrelevant dependent premises before projection-list induction so the induction hypothesis stays unconditional; this repaired the unsuccessful arithmetic closure.

The fourth development check and the exact group check passed. Final controller acceptance remains the main agent's finalize step.
