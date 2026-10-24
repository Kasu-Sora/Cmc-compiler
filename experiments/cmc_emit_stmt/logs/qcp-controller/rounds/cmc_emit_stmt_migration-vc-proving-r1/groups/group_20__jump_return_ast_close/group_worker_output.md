Completed three spatial split lemmas and their three aggressive top-level witnesses. Reused the accepted `cm_stmt_rep_node` bridge, folded original node fields and constructor payload, and preserved the return expression resource. No helper or library changes.

Initial development check exposed residual reassociation after a single `cancel`; debug confirmed identical remaining fields. Replaced it with progress-bounded repeated cancellation. Second development check and exact check passed.

```json
{"development_calls":2,"development_failed":1,"debug_calls":1,"debug_failed":0,"exact_calls":1,"exact_failed":0,"new_helpers":0}
```
