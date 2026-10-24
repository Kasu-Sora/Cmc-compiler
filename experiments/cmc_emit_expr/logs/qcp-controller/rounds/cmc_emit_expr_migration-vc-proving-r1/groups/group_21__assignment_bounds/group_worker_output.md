# assignment_bounds

Completed all five assigned top-level VCs and all twelve assigned split goals. Each split opens with `LLM_pre_process` and an explicit closer; each top-level proof dispatches through `aggressive_pre_process` and the corresponding `Goal_apply` calls.

Added and proved `cm_expr_temps_nonnegative__assignment_bounds` and `cm_assignment_prefix_bounds__assignment_bounds`. The first proves both temporary counts nonnegative by structural recursion, including the argument-list case. The second derives the left-child, right-start, and right-child-end bounds from the parent code length using the existing pair-length theorem. No new imports remain.

Substantive repairs: simplified unary temporary-pair projections after boolean case splits; used the existing fully qualified list-length nonnegativity lemma; handled preprocessed pure bounds and spatial-to-pure extraction explicitly; made zero-guard rewriting tolerant when substitution had already occurred; explicitly substituted lvalue = 0 for temporary-budget projections. Removed an unnecessary continuation after preprocessing had already closed the safety lower bound. Development iterations also corrected name-resolution and import-contract errors.

Final development check passed. Exact group-check passed. Controller acceptance remains the separate finalize-delivery step.

```json
{
  "development_calls": 20,
  "development_failed": 19,
  "debug_calls": 0,
  "debug_failed": 0,
  "exact_calls": 1,
  "exact_failed": 0,
  "new_helpers": 2
}
```
