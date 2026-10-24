# return_leaf_facts

Completed 4 assigned top-level witnesses and 16 split proofs. The endpoint/count/well-formedness facts follow by reducing constructor projections and rewriting the original branch equation backwards. Temporary-count facts can close during preprocessing; proof continuations therefore use semicolons to apply only to remaining goals. No new helper or library change.

The first development call failed with `No such goal` after preprocessing had already closed a temporary-count split. Replaced unconditional subsequent proof commands with a semicolon continuation. The second development call passed. Controller acceptance is separate.

```json
{"development_calls": 2, "development_failed": 1, "debug_calls": 0, "debug_failed": 0, "exact_calls": 0, "exact_failed": 0, "new_helpers": 0}
```
