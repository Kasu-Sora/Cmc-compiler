# Empty and jump statement plans

Completed 4 top-level witnesses and their 4 spatial splits using constructor equalities, reduction of the statement emission model and list append, followed by direct cancellation of the identical emitter assertion. No new helpers or library changes.

The first development check failed because reducing only `cm_emit_stmt` left `nil ++ tail` unreduced, so explicit cancellation could not match. One debug call confirmed this residual expression; adding `app` to the reduction set repaired all four splits. The second development check passed. Controller acceptance remains separate.

```json
{"development_calls":2,"development_failed":1,"debug_calls":1,"debug_failed":0,"exact_calls":0,"exact_failed":0,"new_helpers":0}
```
