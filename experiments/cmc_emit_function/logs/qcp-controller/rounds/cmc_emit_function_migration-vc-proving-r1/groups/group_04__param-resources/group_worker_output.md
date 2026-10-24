# Param resource proofs

Completed the three assigned top-level VCs and both assigned spatial split goals. No helpers or imports were added; the seed library is unchanged.

The return proof distinguishes the empty slot list from the impossible nonempty list at a null pointer, preserving the complete emitter frame. Opening and closing the nonempty list reuse its exact next pointer and three field resources. Head/tail observations are reduced only after the nonempty case is established.

```json
{"development_calls": 7, "development_failed": 6, "debug_calls": 3, "debug_failed": 0, "exact_calls": 1, "exact_failed": 0, "new_helpers": 0}
```

Repair notes: explicitly reduced nil append in the empty return case; used Intros to extract the existential and its pure non-null fact together; unfolded total head/tail observations before field cancellation; cancelled each struct field explicitly because a bare cancel left field resources; replaced an unavailable conjunction lemma with Exists and split_pure_spatial. No annotation or contract repair was required. The final development and exact checks passed.
