# while_safety effort

Completed six assigned top-level witnesses and all twelve assigned split goals. Existing representable code counts and parent while endpoint suffice: unfold cm_i32_code_count, reduce the known while constructor of cm_stmt_code_count, then use linear arithmetic after discarding the spatial frame. No new helpers or imports.

Repair: the first development attempt tried to unfold INT_MAX and INT_MIN as constants; these are notation in this environment. Removed those unfold arguments. The next development and exact checks passed.

```json
{"development_calls": 2, "development_failed": 1, "debug_calls": 0, "debug_failed": 0, "exact_calls": 1, "exact_failed": 0, "new_helpers": 0}
```
