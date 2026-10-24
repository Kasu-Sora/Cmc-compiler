# binary_branch_constants

Completed all 16 assigned split goals and four top-level VCs. Each split proof starts with `LLM_pre_process` and explicitly closes the pure constant assertion using VM computation and congruence. The top-level proofs use `aggressive_pre_process` followed solely by the corresponding `Goal_apply` branches. No helpers or imports were added; the seed library is unchanged.

The first exact check failed because `cbn` left an opcode application unreduced beneath disequality. A successful debug invocation displayed that residual constant proposition. Replacing the closer with `vm_compute; congruence` repaired it. The second exact group check passed (exit code 0, controller status passed). Forbidden-token scan found no matches. Controller acceptance remains separate from this optional precheck.

```json
{
  "development_calls": 0,
  "development_failed": 0,
  "debug_calls": 1,
  "debug_failed": 0,
  "exact_calls": 2,
  "exact_failed": 1,
  "new_helpers": 0
}
```
