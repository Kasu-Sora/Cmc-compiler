# Array opening and empty return

Completed both assigned top-level VCs and the one assigned spatial split goal.
The new public helper `cm_patch_arrays_open__array_open` opens the paired array heads and shifts their tails using the established IntArray/Int64Array full-unfold and segment-to-full lemmas. It adds no non-null or program-validity premises. Empty raw follows from the original length equality and zero branch; patching nil is definitional.

Repair: the first development check found that the helper library did not import the `lia` tactic. Added the official Coq Lia import; the second development check and exact group check passed. No statement, annotation, model, or ownership changes were needed.

```json
{
  "development_calls": 2,
  "development_failed": 1,
  "debug_calls": 0,
  "debug_failed": 0,
  "exact_calls": 1,
  "exact_failed": 0,
  "new_helpers": 1
}
```
