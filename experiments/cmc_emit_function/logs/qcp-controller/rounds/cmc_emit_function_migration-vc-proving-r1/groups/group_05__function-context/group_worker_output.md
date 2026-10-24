# function-context

Completed all four assigned top-level witnesses and both aggressive spatial splits by unfolding the existing function context predicate, preserving the params/locals witness order, and cancelling the seven existing resources. No helper or model changes.

```json
{"development_calls":4,"development_failed":3,"debug_calls":3,"debug_failed":2,"exact_calls":0,"exact_failed":0,"new_helpers":0}
```

Repair notes: `Intros` already introduced the root nonzero pure fact, so removed redundant `Intros_p`. Replaced a single cancellation with repeated progressing cancellation to consume every field/list resource. Replaced the inappropriate disjunction `Split` with existential instantiation followed by pure/spatial splitting when folding the context predicate. Two preliminary debug failures were missing imports in the debug script; copying the protected manual prelude into that debug script resolved them. Final development check passed; controller acceptance remains separate.
