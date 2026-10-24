# if_safety_prefix effort

```json
{"development_calls": 2, "development_failed": 1, "debug_calls": 0, "debug_failed": 0, "exact_calls": 0, "exact_failed": 0, "new_helpers": 0}
```

All 12 assigned split goals use the existing `cm_i32_code_count` and statement count definitions: discard the spatial frame for the pure conclusion, substitute equalities, unfold the range predicate, reduce the known statement constructor, and close with linear arithmetic. The six top-level witnesses only dispatch to their split lemmas. No library changes or new helpers.

Repair: the first development check rejected explicit `unfold INT_MIN, INT_MAX` because these printed constants are not declarations under those names. Removed that unnecessary line; the existing representation already supports `lia`. The second development check passed. Exact precheck was omitted; controller finalization remains the mandatory acceptance check.
