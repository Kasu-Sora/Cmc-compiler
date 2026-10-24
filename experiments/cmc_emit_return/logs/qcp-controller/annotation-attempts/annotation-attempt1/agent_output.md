# Annotation delivery

The public contract retains arbitrary policy, p, done, tail, out and capacity. It consumes cm_return_epilogue ++ tail in cm_resolved_emitter_plan_rep and produces done ++ cm_return_epilogue with tail. No readiness, type, positivity or additional capacity premise was introduced. The contract makes the original exact output-plan guarantee only.

The existing cm_emit_plan BODY contract in QCP_examples/QCP_demos_human/cmc_emit_plan_migration.c was copied verbatim as the sole integration prototype. Its lookup-policy parameter remains explicit. A text comparison confirmed the contract matches, and removing comments confirmed the six-call runtime body is unchanged.

The case lib exports cmc_emit_plan_migration_lib and adds only cm_return_epilogue, exactly Push 8, Load 0, Load 0, Push 8, Store 0, Ret 0 as in baseline/cmc_codegen.c lines 694–698. Search of existing Rocq libraries found no prior cm_return_epilogue definition. No prior libraries, helper implementations or proof files were changed or included. No new internal predicates, helper lemmas or proofs were added.

The relevant correct/incorrect annotation examples were inspected: majority_element demonstrates a mathematical contract, while algorithm_mirror/max_sub_array demonstrates why a second loop interpreter is unsuitable. The authoritative cm_emit_plan contract and library determined the actual integration design.

## Actual owner command calls

1. formal-case-lib-design: passed (exit 0, status passed).
2. symexec: failed, symbolic-execution / symexec-error, unexpected ':' where '::' was expected at target C line 11:13. The initial Extern Coq block mixed type and value declarations. Repair: split them into separate blocks.
3. formal-case-lib-design: passed (exit 0, status passed).
4. symexec: failed, symbolic-execution / symexec-error, cannot derive the first cm_emit_plan precondition at target C line 34:37. The caller had the named cm_return_epilogue ++ tail while the callee required the explicit head/suffix and opcode facts. Repair: add one entry call-boundary Assert exposing the exact list and four opcode encodings. The caller retained its emitter local store and complete resolved-plan resource; this was a call instantiation/opaque-list mismatch, not lost ownership.
5. formal-case-lib-design: passed (exit 0, status passed).
6. symexec: passed (exit 0, status passed), generated roles committed by the controller.
7. formal-case-lib: passed (exit 0, status passed).

Totals: 3 design calls (all passed), 3 symexec calls (2 annotation failures, 1 passed), 1 post-library call (passed). There were no tool-class failures. All commands were the unchanged handoff commands with the bound cwd, and all live sessions were continued through terminal exit.

## Ordinary Assert semantic review

- location: cm_emit_return_epilogue_plan entry, before the first call.
- purpose: function-call-boundary.
- named_semantic_state: existing cm_resolved_emitter_plan_rep with the explicit epilogue list.
- upstream_paths: the single function-entry state.
- downstream_work: six cm_emit_plan calls consume the list one instruction at a time.
- redundant_with_invariant_or_postcondition: no.
- decision: keep.
- rationale: QCP requires the explicit cons shape for matching the callee resource. The assertion establishes all fixed opcode facts once, preserves the complete plan and emitter parameter, and generates an independent entailment obligation from the unchanged public precondition.

Six where clauses instantiate the original policy, program, output, capacity, emitted prefix and remaining tail. Their nested append form matches each previous helper postcondition. The return VC only requires list associativity to identify the resulting prefix with done ++ cm_return_epilogue.

## VC comparison

First attempt: no previous failed VCs; vc_comparisons remains empty. The current manual was inspected read-only. It contains the entry entailment (eight closed opcode facts and the definitionally equal list resource) and return entailment (append association); no missing input premise was identified. Generated proof placeholders remain controller-owned for the subsequent proving phase. Owner completion is not controller acceptance or final proof completion.
