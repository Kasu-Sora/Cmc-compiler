Completed all four assigned top-level witnesses and their spatial split goals using the required aggressive route and Goal_apply dispatch. No helper additions or library edits were needed.

The return proofs substitute expression shape, operator and lvalue, explicitly unfold the code wrapper and short opcode, reduce the closed Z/positive equality and boolean tests, normalize list association and scalar addition, then cancel the unchanged frame. The initial reductions left wrappers and closed boolean tests unreduced; explicit unfolding and Pos.eqb reduction repaired these failures. The short-value replacement split is closed directly by LLM_pre_process with its explicit arithmetic closer; redundant following tactics were removed after a no-goal diagnostic.

Four development checks were run and failed during these local repairs. Two debug calls passed and exposed the remaining proof state. The final exact group-check passed with exit code 0. Final acceptance remains the controller finalize-delivery validation.

```json
{
  "development_calls": 4,
  "development_failed": 4,
  "debug_calls": 2,
  "debug_failed": 0,
  "exact_calls": 1,
  "exact_failed": 0,
  "new_helpers": 0
}
```
