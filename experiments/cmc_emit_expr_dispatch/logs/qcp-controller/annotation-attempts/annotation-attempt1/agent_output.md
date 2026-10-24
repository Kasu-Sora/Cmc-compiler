# Dispatch annotation delivery

The whole runtime function cm_emit_leaf_expr is annotated; no C runtime token or ABI edit was made. The four helper declarations reproduce the accepted implementation BODY contracts of cmc_emit_expr_leaf_migration.c (including the const body/header distinction). No old manual or automatic proof is imported.

## Contract and representation

All source pre/post facts are retained: lvalue bounds, source leaf kind membership, wf_program (same policy/codegen obligation boundary), typed_program, total function lookup, expr_wf, counts representability, all three storage safety facts and the combined globals/strings bound. All program/function/expression resources and exact done/leaf-code/tail plan are retained.

The original boolean cm_leaf_expr is renamed cm_dispatch_leaf to avoid collision with the prior target leaf datatype. The logical leaf parameter with e = cm_leaf_source_expr leaf is a representation witness. The proved cm_dispatch_leaf_coverage iff establishes exactly the original input domain; cm_dispatch_leaf_unique and the reused roundtrip establish uniqueness. The semantic plan remains the previously checked explicit leaf specialization, not a dummy general expression emitter. This is a Rocq domain/representation correspondence; it is not a formal HOL-to-Rocq metatheorem or complete compiler/TVM preservation theorem.

Only one new predicate and two domain correspondence lemmas are added. Existing expression counts, well-formedness and memory representation definitions are imported unchanged. Const type-code validity comes from the existing counts node fact; string i32 bounds from the existing counts recursive branch; sizeof type-code validity and references from existing expr_wf. The final branch excludes the first three leaf constructors and yields Getc. None is added as a dispatch input requirement.

## Key points and assertion review

There are no ordinary full Assert annotations and no branch-control commands. Nine partial which-implies bridges expose the expression node (one), derive constructor shape and normalize the exact plan at helper calls (four), and close all seven fields plus payload back to expression representation (four). All other resources are framed. The four call where annotations instantiate only parameters already in the public With list; branch existential witnesses are inferred from the normalized emitter resource.

These are semantic-phase-transition / function-call-boundary bridges, not return-postcondition copies. There are no loops and no new internal predicates. First-attempt vc_comparisons is empty. The current generated manual has 13 top-level obligations and 8 split goals. It was only read; all generated files came from controller symexec.

## Actual command attempts and repairs

- formal-case-lib-design: 4 commands, 3 passed, 1 failed.
- symexec: 3 commands, 1 passed, 2 failed.
- formal-case-lib post-symexec: 1 command, passed.
- No tool/infrastructure failure and no retry round.

1. Initial design check failed at coverage Qed: the reverse kind-membership disjunction remained open with generic auto. Explicitly unfolding the kind predicate and using propositional tauto closed the definition-level proof. The next design check passed.
2. First symexec failed at cm_emit_const_expr: competing e equalities caused callee matching to pick the leaf source-view expression rather than the constructor equality. Reordering branch facts exposed the constructor equality first, preserving all facts. Design check passed, but the second symexec still failed because the emitter plan retained the opaque leaf variable, preventing synthesis of the callee constructor witnesses.
3. The four constructor-shape bridges were extended to transform the exact emitter-plan resource from leaf to its equal branch constructor. This is equality rewriting only; done/tail, program and emitted code are unchanged. Unused inherited Extern declarations were removed in the same revision. The fourth design check, third symexec and post-symexec library check passed with real exit 0 / status passed.

## References

Read all annotation-designing required guides and the relevant positive branch_destruct example, negative algorithm-mirror explanation/material, existing leaf annotation and its library, and existing counts/layout definitions. Existing leaf and var annotations informed resource/call boundaries; no previous manual proof body was copied.

## VC comparison

None: first attempt, no failed_vcs.
