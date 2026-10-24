Completed the assigned binary and member constructor-fact proofs: 34 split lemmas and two aggressive top-level dispatch proofs. Added nine suffixed helpers for slot, binding, member, pointee, binary, unary and complete expression type references, node encoding facts, and temporary bounds.

Material proof repairs were: replacing assigned seed admissions with temporary aborts for development; interleaving conjunction and disjunction decomposition in the binary typing helper; fixing a rewrite-introduction syntax ambiguity; fixing the operator typing premise before resolving helper metavariables; and generalizing the temporary-bound helper over its upper bound to avoid a manual-only integer constant name. No specification or annotation changes were needed.

Effort accounting:

```json
{"development_calls":7,"development_failed":5,"debug_calls":0,"debug_failed":0,"exact_calls":1,"exact_failed":0,"new_helpers":9}
```
