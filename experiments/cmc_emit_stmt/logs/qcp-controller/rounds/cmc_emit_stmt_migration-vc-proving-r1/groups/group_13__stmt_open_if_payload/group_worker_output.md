# stmt_open_if_payload

Completed the six assigned top-level witnesses and four aggressive split goals. Reused the existing `cm_stmt_rep_node` bridge, `cm_stmt_payload`, and statement projections; added no helpers or imports. Opens retain all five fields and the complete payload using the original existential pointers. The if payload and fold use the given constructor equality. The generic fold keeps the payload opaque.

Repairs during proof development: cancellation initially left differing sepcon association, fixed with explicit `sepcon_assoc_change` (plain `normalize` was insufficient). Instantiated `cm_stmt_rep_node stmt s` explicitly so the fold rewrites the parent node rather than the first child predicate. A preliminary edit script regex expected Abort/Qed and failed on the initial admitted template before writing any file; fixed its match for template endings.

```json
{"development_calls": 5, "development_failed": 4, "debug_calls": 1, "debug_failed": 0, "exact_calls": 1, "exact_failed": 0, "new_helpers": 0}
```
