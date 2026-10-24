# Resources proof effort

```json
{"development_calls":5,"development_failed":4,"debug_calls":3,"debug_failed":0,"exact_calls":1,"exact_failed":0,"new_helpers":0}
```

Completed the five assigned top-level witnesses and two aggressive spatial split goals. No new helper or import; group library seed unchanged.

Repair notes:
- Explicitly reduced list append after the nil code model; the first development check exposed a residual `nil ++ tail`.
- Introduced existential header fields with `Intros` before using extracted non-null facts; the second development check exposed the existential/pure order mismatch.
- Split the conjunction before constructor congruence, and named the equality hypothesis separately; the third development check exposed the unsplit conjunction.
- Repeated spatial cancellation to close the residual identical function-body-list resource after folding; the fourth development check exposed that residual goal.
- Replaced provisional shorthand closing tactics with explicit `split_pure_spatial`, repeated cancellation and pure closers before delivery.

Readiness supplies the head descriptor lookup equality; paired header/body equations identify the same body pointer and tail list. Empty, cons, field-open and field-fold proofs preserve all frames.
