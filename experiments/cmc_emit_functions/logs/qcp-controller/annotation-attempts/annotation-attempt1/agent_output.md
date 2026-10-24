# Annotation delivery

The original one-function C runtime is unchanged. The source BODY contract is translated without a new fid bound or full-program-list restriction. Both external helper BODY contracts are copied unchanged. The common readiness, function-context/list resources and emitter representation are reused.

New definitions: cm_emit_functions is exactly the source list-order concatenation equation, an existing domain model independent of C recursion strategy; cm_emit_functions_tail is the transparent list tail observation. No new lemma, axiom or manual proof is written by this owner. Readiness-to-statement-length uses the already accepted cm_emit_stmt_length__stmt_capacity bridge during proving.

The non-null function list is opened using readiness to identify its head with the policy lookup. All head-helper facts and successor facts are projected before calls. After the head call, the next field is opened/read/restored. The recursive call consumes the tail code and return proof restores list ownership. The empty branch keeps arbitrary fid and proves nil emission from null-list shape.

## Checks and migration effort

```json
{
  "design_calls": 3,
  "design_failed": 0,
  "symexec_calls": 3,
  "symexec_failed": 2,
  "post_lib_calls": 1,
  "post_lib_failed": 0,
  "new_definitions": 2,
  "new_helpers": 0,
  "top_level_manual_witnesses": 12,
  "split_goals": 29
}
```

All terminal checks have actual exit 0 and status passed. There were two failed owner symexec calls before the final passing call:

1. Resource reclaim: next_fn local permission was consumed by a redundant final list-fold partial annotation. Removed that annotation; the return VC now folds head/tail ownership directly, preserving the local store. No runtime/spec change.
2. Syntax: trimming unused Extern declarations accidentally mixed type-kind (::) and value-type (:) entries in one block. Restored separate Extern blocks. No semantic change.

## Assert review

Ordinary full Assert: none. There are seven partial which-implies transformations: non-null list opening; readiness projection; count-result retargeting; emitter head/tail split; context field opening; context field restoration; final emitter append restoration. These are call/resource boundaries or an exit bridge. The count retarget is a local value-binding step needed to expose the verified returned expression. The removed list-fold transformation was redundant with the return obligation. No lexical C loops exist.

## Reference and predicate review

Inspected linked annotation guides and correct sll data-structure examples, and algorithm-mirror negative example. Used prior migration files only as accepted dependency contracts and resource interfaces as specifically required by the handoff. There are no newly introduced pure internal predicates or higher-order existential witnesses. The tail observation is total; the cons shape used on the non-null branch is proved from list ownership and readiness.

## VC comparison

First attempt: no old failed_vcs, vc_comparisons is empty. Current generated goals were inspected for both null/non-null returns, successor arithmetic, readiness projections and context resource restoration.
