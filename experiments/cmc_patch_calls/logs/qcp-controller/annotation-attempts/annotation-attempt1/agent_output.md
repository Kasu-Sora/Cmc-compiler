# Annotation delivery

Both original runtime bodies and ABI declarations are unchanged. The internal contract retains the original wf/code-ready, signed32 length, logical length equality, program context, full function list and two exact arrays. The public contract retains existential raw physical buffers whose patch is resolved. It assumes neither raw = resolved nor patch idempotence, and adds no valid-fid, nonnegative target, typed-program, or nonnull-empty-array requirement.

## Representation and reuse

`cm_patch_tail raw := tl raw` is the source total list-tail observation (nil maps to nil). `cm_patch_arrays_rep ops imms length raw` is exactly `IntArray.full ops length (cm_rep_ops raw) ** Int64Array.full imms length (cm_rep_imms raw)`. It has no additional pure fact, nonnull requirement or altered ownership. This domain-specific correlated-array view lets QCP infer the hidden raw instruction list as a direct predicate argument, whereas it cannot invert two independent projections in the helper precondition. The new predicate does not implement array memory; it reuses the two existing full-array predicates.

The established `cmc_emit_resolved_migration_lib` supplies the patch semantics and imports core emitter, total-PC and representation libraries. No old generated manual/auto proof is imported. The helper `cmc_function_pc_total` contract was copied exactly from its verified BODY contract. There are 2 new definitions and 0 new proof helpers at annotation delivery; proof support remains for the assigned proof workers.

## Design references

Read the required annotation guides and inspected the array/recursive-call style in `int_array_merge_rel.c` and the algorithm-mirror negative examples. Their code and proof artifacts were not copied. Existing CMC source/contracts are the semantic authority. The patch model was already migrated, so no new algorithm interpreter was introduced.

## Ordinary Assert review

location: cmc_patch_code_arrays, positive length before head reads
purpose: function-call-boundary
named_semantic_state: cm_patch_arrays_rep (contract representation, not a new pure internal state)
upstream_paths: only nonempty raw sequences reach this point; the zero-length path already returns
downstream_work: read head, possibly total-PC lookup/update, recursively patch remaining arrays, rebuild both arrays
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: exposes the two head cells and correlated tail arrays while preserving raw shape, branch observations, lengths and original resources.

location: cmc_patch_resolved_calls, entry before emitter field reads
purpose: semantic-phase-transition
named_semantic_state: cm_resolved_emitter_rep to cm_patch_arrays_rep plus framed fields/tails
upstream_paths: one entry path with an existential raw physical buffer
downstream_work: read emitter/output fields and invoke recursive patcher
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: exposes the actual raw physical sequence, derives the capacity signed32 bound from the owned int field, and preserves all unused suffix and pointer resources.

No lexical loops or branch-control annotations. Head reads retain their exact mathematical bindings through the two C branches. Empty arrays require no dereference. No higher-order existential witness is added.

## Actual checks and repairs

1. Design check passed for the reused library plus total tail definition.
2. Symexec failed: symbolic-execution / undeclared `raw_prefix` at the wrapper where annotation. Existentials introduced by Assert are not lexical names usable in later where expressions. Removed that explicit binding to test ordinary inference.
3. Design check passed. Symexec failed: symbolic-execution / With `raw` not instantiated at the wrapper call. Inference cannot recover raw beneath cm_rep_ops/cm_rep_imms projections. Introduced the exact transparent correlated-array representation in the internal contract and wrapper cut.
4. Design check failed at library line 7: `Scope sac is not declared`. Added the direct standard Mem/SeparationLogic/ArrayLib/Interface imports and naive_C_Rules import used by existing separation assertions.
5. Design check passed. Symexec failed: symbolic-execution / recursive callee precondition could not be derived because the caller still held two separate tail full arrays while the callee expected the new named view. Changed the positive split cut to retain the exact correlated tail view; head cells remain separate.
6. Design check passed. Canonical symexec passed with 6 top-level manual obligations and 4 spatial split declarations. Current generated statements retain raw/tail shape, CALL/non-CALL observation, complete contexts, signed ranges and all array resources.
7. Post-symexec formal-case-lib check passed.

All command processes were polled to real terminal exits; only exit 0 plus controller status passed is recorded as passing. Generated artifacts were written only by controller symexec. Manual proofs remain untouched by this annotation owner.

```json
{"design_calls":5,"design_failed":1,"symexec_calls":4,"symexec_failed":3,"post_lib_calls":1,"post_lib_failed":0,"new_definitions":2,"new_helpers":0}
```

## VC comparison

First attempt: vc_comparisons is empty. The independent VC checker will assess the complete generated obligations; annotation delivery does not claim they are already proved.
