# Annotation delivery

The complete cmc_emit_data source contract is translated with all seven pure facts retained in both Require and Ensure, both exact list representations (including owned string byte arrays), exact left-associated zero-header/global/string bytes, precise return cursor, and the remaining undefined suffix. No runtime or ABI tokens changed. Helper contracts are copied from cmc_write_zeroes_migration.c, cmc_emit_globals_migration.c and cmc_emit_strings_migration.c. Those verified examples and their pure libraries inform contract reuse; no existing generated proof is imported.

The new case library contains only two Require Export lines for existing globals and strings pure libraries. New mathematical definitions and lemmas: none. There are no loops or new internal predicates, and no higher-order witnesses. Three call sites use where bindings; the later two infer prefix from the owned segment.

## Ordinary Assert review

location: after cmc_write_zeroes, before declaration/call producing globals_cursor
purpose: function-call-boundary
named_semantic_state: none
upstream_paths: a single straight-line reserved-header write
downstream_work: two emitter calls that append global and string bytes
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: normalize the helper postcondition's [0, 0 + 8) segment containing nil ++ zeros(8) into [0, 8) containing zeros(8), preserving every pure fact and both list resources. QCP cannot match the next helper resource without this boundary normalization. The generated entailment owns the normalization proof; no fact is assumed.

## Design iterations and check outcomes

1. Import-only library plus exact spec and three where clauses: formal-case-lib-design passed (terminal exit 0, status passed). First canonical symexec failed with category symbolic-execution, kind symexec-error at cmc_emit_globals call, line 98. Caller had UCharArray.seg(data, 0, 0 + 8, app(nil, zeros(8))); explicit callee prefix zeros(8) expected UCharArray.seg(data, 0, 8, zeros(8)). This was a call resource-shape normalization issue.
2. Removed explicit prefixes at globals and strings calls so heap inference chooses the exact current prefix: design passed. Second symexec failed at the same call, still unable to match the [0,0+8) resource to [0,8), even with existential inferred prefix. No function specification or runtime changed.
3. Added the single full call-boundary Assert described above and updated the plan. Design passed; canonical symexec passed; post-symexec formal-case-lib passed. All have actual terminal exit 0 and controller JSON status passed.

Owner check totals: 3 design passes, 3 symexec invocations (2 ordinary annotation failures, 1 pass), 1 post-symexec lib pass. There was no tool failure or manual generated-file edit. No proof was authored by annotation owner.

The current generated manual has 4 top-level witnesses and 5 split candidates, awaiting independent VC checking and proving. Automatic output has 7 trusted Admitted exports. These are generated stubs and not a claim of completed verification.

## VC comparison

None: first annotation attempt, vc_comparisons is empty.
