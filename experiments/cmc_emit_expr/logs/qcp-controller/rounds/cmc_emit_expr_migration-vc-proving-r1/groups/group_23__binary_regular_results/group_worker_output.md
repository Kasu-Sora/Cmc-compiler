Completed the three assigned binary regular result VCs and their spatial split goals. The proofs substitute the source shape, establish lvalue/operator guards, unfold the code projection, normalize list append and PC addition, and cancel the preserved resources. The empty lvalue branch additionally reduces nil append. Each top-level proof uses aggressive_pre_process followed only by its corresponding Goal_apply.

Substantive repairs during proof development: made Z.eqb explicit to avoid string-scope notation; explicitly unfolded cm_expr_code_for and rewrote Z.eqb_refl because restricted cbn retained its guard; included app in the empty-code reduction. No helpers were added and the seed library was unchanged.

Final development and exact group checks passed. Four earlier development checks failed during those local tactic repairs. Two debug calls inspected residual goals, one failing at the unresolved guard rewrite and one successfully exposing the remaining conditionals.

```json
{
  "development_calls": 5,
  "development_failed": 4,
  "debug_calls": 2,
  "debug_failed": 1,
  "exact_calls": 1,
  "exact_failed": 0,
  "new_helpers": 0
}
```
