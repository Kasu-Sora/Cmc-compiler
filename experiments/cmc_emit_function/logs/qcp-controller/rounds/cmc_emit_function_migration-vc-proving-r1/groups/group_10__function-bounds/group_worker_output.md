# Function bounds proof effort

```json
{"development_calls":2,"development_failed":1,"debug_calls":0,"debug_failed":0,"exact_calls":0,"exact_failed":0,"new_helpers":0}
```

Completed the three assigned aggressive top-level witnesses and all six assigned split goals. Bounds follow by unfolding existing `cm_i32_code_count`, substituting the function PC equality, and integer arithmetic. Zero count and push opcode facts are discharged by existing definitions. No new helpers or library changes were required.

One development repair removed attempted unfolding of `INT_MIN`/`INT_MAX`: these identifiers are notation in generated goals, not available constant references. The corrected second development check passed. The initial editing script's layout assertion failed before writing any file; it was adjusted to the actual one-line placeholder format. Exact precheck was omitted; terminal acceptance remains the main controller finalize validation.
