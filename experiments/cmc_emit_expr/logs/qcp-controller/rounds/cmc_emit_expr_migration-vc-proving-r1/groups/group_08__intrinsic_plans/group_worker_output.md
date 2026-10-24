Completed all six assigned split lemmas and their aggressive top-level VCs. Constructor discrimination establishes the putc, puti, and exit shapes; lvalue bounds give zero, then explicit code unfolding and list associativity align the unchanged emitter plans. No helpers or imports were added, and the seed library is unchanged.

The first development check failed because `cbn` did not unfold `cm_expr_code_for` sufficiently for cancellation. A debug call exposed the remaining expression; explicit unfolding, reduction of `Z.eqb`, and list normalization repaired all three spatial proofs. The second development check passed. The exact group check passed. Controller finalization remains separate.

```json
{"development_calls":2,"development_failed":1,"debug_calls":1,"debug_failed":0,"exact_calls":1,"exact_failed":0,"new_helpers":0}
```
