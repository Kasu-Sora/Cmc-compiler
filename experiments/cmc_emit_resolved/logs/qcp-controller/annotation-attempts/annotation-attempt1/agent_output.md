# Annotation iteration 1

The current C runtime wrappers were preserved. The seven core declaration contracts were extracted verbatim from the verified core C file, and a byte comparison passed. The case library imports only the core library and its existing dependency closure, with no auto/manual imports.

The source resolved contracts and cmc_concrete_defs.c lines 465–486 determine the models. The new cm_patch_inst uses the existing total cm_function_pc and lookup policy; cm_patch_code is map; cm_resolved_emitter_rep existentially owns RAW projections. CALL accepts every signed function_id, with no additional validity, readiness, PC range, or program well-formedness condition. Temporary wrappers preserve all eight source pure facts in both pre and post, plus the pre-only exact fragment capacity bound and complete function-context resource.

The positive annotation example int_array_merge_rel.c was read for call-boundary witness/where structure; the algorithm-mirror negative guide was read to check abstraction direction. No implementation mirror was introduced: the patch map is the source's public mathematical view. No internal predicate is needed beyond the public patch relation and existing core plan.

## Checks and repairs

1. formal-case-lib-design failed at the patch-length lemma: Zlength_map is not exported by this environment. Changed to a direct length argument.
2. formal-case-lib-design failed because unfolding this library's Zlength does not expose a nat-length expression for map_length. Changed to structural induction using the existing Zlength_cons lemma.

## Ordinary Assert semantic review

All eight wrapper Assert points have the following shared review; each point and its precise resources/facts is separately listed in annotation_plan.json.

- location: immediately before the sole verified core helper call in each wrapper.
- purpose: function-call-boundary.
- named_semantic_state: cm_emitter_plan_rep with cm_patch_code(raw_prefix) = done (both public/core predicates).
- upstream_paths: one straight-line entry path.
- downstream_work: instantiate the core helper on existential raw_prefix, then re-establish the resolved existential representation of the appended fragment.
- redundant_with_invariant_or_postcondition: no.
- decision: keep.
- rationale: the boundary opens the resolved existential and transfers its length-based capacity to the raw core plan, while preserving caller facts and all spatial resources. This is a representation conversion rather than a copied postcondition.

## VC comparison

None: this is the first attempt, so vc_comparisons is empty.

3. formal-case-lib-design passed. First symexec found a call-instantiation parser error: existential raw_prefix is not in explicit where scope (first occurrence line 123). Removed only explicit done = raw_prefix; the exact cm_emitter_plan_rep spatial assertion lets structural matching infer that witness. All eight boundaries were repaired together.

4. Design recheck passed. Second symexec found a resource-shape mismatch: explicit polymorphic tail = nil lacked its tvm_inst type argument while the caller resource contained typed nil. Removed explicit tail binding, allowing the structurally identical fragment plan to infer both done and tail.

5. Final formal-case-lib-design recheck passed (terminal exit 0, controller status passed).
6. Third symexec passed and generated all four current roles transactionally. Read the generated manual and inspected the entry/return VCs, especially CALL and both temporary wrappers. The raw prefix and patch equality survive core calls; temporary resources and original eight pure facts remain available. There are 16 top-level manual witnesses (8 entry and 8 return); generated split spatial stubs remain untouched for the proving phase.
7. Post-symexec formal-case-lib check passed (terminal exit 0, controller status passed). No manual proof edits were made. The current new library contains three model definitions and ten proved pure lemmas, with no new axioms or admissions. Acceptance and eventual manual proof completion remain controller-owned.

The first-attempt plan is ready with eight genuine call-boundary key points, no loops, no extra internal predicates, and empty vc_comparisons. There were five design checks (two failed, three passed), three symexec runs (two annotation failures, then passed), and one successful post-symexec library check in this iteration.
