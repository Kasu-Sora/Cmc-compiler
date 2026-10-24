# constructor_facts_a effort

Completed the intrinsic and unary constructor fact proofs, comprising 22 split lemmas and their two top-level dispatch proofs. Added five proved helpers for slot expression references, binary typing references, unary typing references, structural expression references, and node encoding facts.

Material repairs during development: destruct conjunctions introduced by operator disjunction branches; correct a substitution-pattern syntax error; reduce constant binding-scope tests; instantiate binary/unary helper arguments explicitly; retain the complete parent expression well-formedness premise before destructing the unary constructor context. No annotation changes were required.

```json
{
  "development_calls": 7,
  "development_failed": 6,
  "debug_calls": 0,
  "debug_failed": 0,
  "exact_calls": 1,
  "exact_failed": 0,
  "new_helpers": 5
}
```
