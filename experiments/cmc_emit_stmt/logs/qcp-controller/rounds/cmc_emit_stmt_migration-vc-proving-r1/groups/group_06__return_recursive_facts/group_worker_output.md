# return_recursive_facts

Completed the 16 assigned split proofs and 4 aggressive top-level routes without new helpers. The split proofs simplify nested statement projections, rewrite the original branch constructor equation backwards, and reuse the unchanged endpoint, temporary-space, representability and well-formedness premises.

Repair: the first exact check found `No such goal` at the block-case split because `LLM_pre_process` already discharged it. Changed the subsequent normalization/rewrite/assumption sequence to a semicolon continuation, so it runs only on remaining goals. The second exact check passed. No formal statements, contracts, annotations or library definitions changed.

A local edit script initially matched `Abort` for top-level placeholders, whereas those assigned placeholders were `Admitted`; its assertion stopped before any write. Corrected the edit matcher, without a proof-tool call or formal change from that failed script.

```json
{
  "development_calls": 0,
  "development_failed": 0,
  "debug_calls": 0,
  "debug_failed": 0,
  "exact_calls": 2,
  "exact_failed": 1,
  "new_helpers": 0
}
```
