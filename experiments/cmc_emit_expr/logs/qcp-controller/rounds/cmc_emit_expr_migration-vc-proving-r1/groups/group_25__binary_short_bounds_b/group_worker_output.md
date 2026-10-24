Completed all seven assigned split goals and the three aggressive dispatchers. Code prefix bounds follow from the parent end-pc bound, exact emitted-code lengths, and nonnegative child lengths. The right-child temporary bound follows from the maximum in the parent temporary budget. No helper or import additions were needed.

The first two development attempts exposed the need to discard the spatial frame before arithmetic and explicitly reduce the positive-integer equality in the short-circuit guard. Both were repaired. The third development check passed, and the exact group check passed. Two early debug calls failed because of an unavailable manual import and an incorrect inspected definition name; the remaining three debug calls succeeded.

```json
{
  "development_calls": 3,
  "development_failed": 2,
  "debug_calls": 5,
  "debug_failed": 2,
  "exact_calls": 1,
  "exact_failed": 0,
  "new_helpers": 0
}
```
