# Annotation iteration 1

Read the full handoff and annotation-designing workflow/guides, including the predicate-first positive majority-element example and negative algorithm-mirror example. The source `.c` and `.h`, the public plan-open/close routines and plan representation in concrete definitions, and the prior resolved contracts/model supplied the authoritative semantics. Teaching examples affected annotation organization only; no example proof was copied.

## Design and source alignment

All eight runtime wrappers are preserved after annotation erasure. All eight resolved-helper contracts are byte-identical to the frozen verified target, checked by extracting their complete annotation blocks. Their implementations and proofs are not imported or copied.

The only new representation is `cm_resolved_emitter_plan_rep`: the sum of lengths of independent `done` and `todo` fits capacity, together with the existing resolved emitter assertion for `done`. The same explicit lookup policy is passed throughout. The resolved assertion retains raw-buffer ownership; CALL resolution remains the existing logical patch map. There are no added reachability, readiness, validity, fid bounds, scalar-only constraints or PC representability constraints.

Each wrapper consumes its exact source fragment from `todo`, appends it to `done`, and leaves `tail` untouched. Both temporary wrappers retain all eight source pure facts in precondition, call boundary, and postcondition, and retain the complete function-context assertion.

The case lib contains one new public definition and one reusable proved list-budget lemma, `cm_plan_fragment_capacity`. Its two conclusions correspond to the source public `cm_plan_open` facts, using existing `Zlength_app` and `Zlength_nonneg`. Closing a plan is folding the public representation using the retained final-capacity fact. There is no new arithmetic axiom, arbitrary PC map, or duplicated resolved implementation proof. The private singleton/call capacity steps reduce the same list-length laws; they do not need separate new lemmas.

No internal-only predicate was needed: each boundary has only the public resolved representation and two explicit capacity consequences. The plan lists all eight boundaries; there are no loops.

## Ordinary Assert semantic review

### cm_emit_plan-call

- location: cm_emit_plan: immediately before cm_emit_resolved
- purpose: function-call-boundary
- named_semantic_state: cm_resolved_emitter_rep (existing public model)
- upstream_paths: the single straight-line entry state owns the plan assertion.
- downstream_work: invoke the matching resolved helper, then restore the plan with the appended fragment and unchanged tail.
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: unfold the logical budget, expose immediate fragment capacity required by the helper, and retain final capacity across the call. This is the source plan-open bridge, not a duplicate return assertion.

### cm_emit_call_plan-call

- location: cm_emit_call_plan: immediately before cm_emit_resolved_call
- purpose: function-call-boundary
- named_semantic_state: cm_resolved_emitter_rep (existing public model)
- upstream_paths: the single straight-line entry state owns the plan assertion.
- downstream_work: invoke the matching resolved helper, then restore the plan with the appended fragment and unchanged tail.
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: unfold the logical budget, expose immediate fragment capacity required by the helper, and retain final capacity across the call. This is the source plan-open bridge, not a duplicate return assertion.

### cm_emit_normalize_plan-call

- location: cm_emit_normalize_plan: immediately before cm_emit_resolved_normalize
- purpose: function-call-boundary
- named_semantic_state: cm_resolved_emitter_rep (existing public model)
- upstream_paths: the single straight-line entry state owns the plan assertion.
- downstream_work: invoke the matching resolved helper, then restore the plan with the appended fragment and unchanged tail.
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: unfold the logical budget, expose immediate fragment capacity required by the helper, and retain final capacity across the call. This is the source plan-open bridge, not a duplicate return assertion.

### cm_emit_load_plan-call

- location: cm_emit_load_plan: immediately before cm_emit_resolved_load
- purpose: function-call-boundary
- named_semantic_state: cm_resolved_emitter_rep (existing public model)
- upstream_paths: the single straight-line entry state owns the plan assertion.
- downstream_work: invoke the matching resolved helper, then restore the plan with the appended fragment and unchanged tail.
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: unfold the logical budget, expose immediate fragment capacity required by the helper, and retain final capacity across the call. This is the source plan-open bridge, not a duplicate return assertion.

### cm_emit_store_plan-call

- location: cm_emit_store_plan: immediately before cm_emit_resolved_store
- purpose: function-call-boundary
- named_semantic_state: cm_resolved_emitter_rep (existing public model)
- upstream_paths: the single straight-line entry state owns the plan assertion.
- downstream_work: invoke the matching resolved helper, then restore the plan with the appended fragment and unchanged tail.
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: unfold the logical budget, expose immediate fragment capacity required by the helper, and retain final capacity across the call. This is the source plan-open bridge, not a duplicate return assertion.

### cm_emit_fp_address_plan-call

- location: cm_emit_fp_address_plan: immediately before cm_emit_resolved_fp_address
- purpose: function-call-boundary
- named_semantic_state: cm_resolved_emitter_rep (existing public model)
- upstream_paths: the single straight-line entry state owns the plan assertion.
- downstream_work: invoke the matching resolved helper, then restore the plan with the appended fragment and unchanged tail.
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: unfold the logical budget, expose immediate fragment capacity required by the helper, and retain final capacity across the call. This is the source plan-open bridge, not a duplicate return assertion.

### cm_emit_temp_store_plan-call

- location: cm_emit_temp_store_plan: immediately before cm_emit_resolved_temp_store
- purpose: function-call-boundary
- named_semantic_state: cm_resolved_emitter_rep (existing public model)
- upstream_paths: the single straight-line entry state owns the plan assertion.
- downstream_work: invoke the matching resolved helper, then restore the plan with the appended fragment and unchanged tail.
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: unfold the logical budget, expose immediate fragment capacity required by the helper, and retain final capacity across the call. This is the source plan-open bridge, not a duplicate return assertion.

### cm_emit_temp_load_plan-call

- location: cm_emit_temp_load_plan: immediately before cm_emit_resolved_temp_load
- purpose: function-call-boundary
- named_semantic_state: cm_resolved_emitter_rep (existing public model)
- upstream_paths: the single straight-line entry state owns the plan assertion.
- downstream_work: invoke the matching resolved helper, then restore the plan with the appended fragment and unchanged tail.
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: unfold the logical budget, expose immediate fragment capacity required by the helper, and retain final capacity across the call. This is the source plan-open bridge, not a duplicate return assertion.

## Actual owner check effort

| Command kind | Invocations | Passed | Failed |
|---|---:|---:|---:|
| formal-case-lib-design | 1 | 1 | 0 |
| symexec | 1 | 1 | 0 |
| formal-case-lib | 1 | 1 | 0 |

Each recorded pass has terminal exit code 0 and controller JSON `status: passed`. No controller-tool failure, infrastructure retry, or substantive repair occurred. The initial design was written once; after checks only plan readiness and notes were finalized.

Symbolic execution generated eight entail witnesses and eight return witnesses. Each entail has two pure capacity splits and one spatial split; each return has one spatial split. The generated pure call-instantiation obligations are already supplied by the boundary. The manual remains unedited, including controller-generated placeholders for the later proving stage. No previous unresolved proof stub or previous manual/auto proof was copied.

## VC comparison

First attempt: no old failed VCs; `vc_comparisons` is empty. Current VCs retain independent mathematical lists, exact fragments, complete resources, and the tail-capacity premise required at return. No annotation gap was found in the generated statements.
