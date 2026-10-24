# Annotation delivery

The complete three-function runtime body token streams match baseline/runtime-source.c after removing annotations. Source main header and BODY contracts have the same pure facts and resources; the QCP main contract preserves them all. No wf_program, op-range, fid-range, expression-typing, positive-scale or pointer-argument-kind restriction was introduced. cm_pointer_scale_value retains its original pointer-type premise.

The canonical case library only exports cmc_emit_expr_call_migration_lib. cm_pointer_scale and cm_binary_finish_code are reused verbatim through that dependency closure. No new definition, lemma, axiom, parameter or proof was written. Existing policy parameterization is retained; cg is unnecessary because these source contracts require only typed_program.

The seven helper declaration contracts are the previously accepted BODY specifications: cm_expr_type_code_context from count_context (the input's leaf attribution was imprecise), cm_type_size_value from emit_expr_leaf, cmc_pointee and cmc_is_pointer_value from layout, cmc_binary_opcode from emit_core, and cm_emit_plan/cm_emit_temp_load_plan from emit_plan. No prior manual or automatic file is imported as a helper dependency.

## Design decisions

The three functions have no loops. No new internal predicates are needed: the shared exact code model, emitter-plan resource and existing expression/type facts already express the mathematical state. Four pointer branches and three generic branches retain the C control flow. Explicit where instances record each consumed code prefix and arbitrary remaining tail. The full program, function and both expression ownership resources are framed across all calls.

Ordinary Assert: none. Eight partial which-implies annotations normalize the generic helper's app/cons boundary and select the seven source-model branch code lists before emission calls. They preserve their branch/type facts and change only the emitter-plan list representation. No Branch name, Destruct, clear, join or multi-invariant is used. There are no higher-order existential witnesses.

References inspected for design include annotation-designing's positive internal-predicate/majority-element examples and negative algorithm-mirror examples. The current implementation uses the preexisting independent source code model instead of adding an algorithm mirror. Existing accepted BODY contracts determined helper interfaces.

## Actual owner invocations and repairs

- formal-case-lib-design: 3 invocations, 3 passed, 0 failed.
- symexec: 3 invocations, 1 passed, 2 annotation failures; 0 tool failures.
- formal-case-lib (post-symexec): 1 invocation, 1 passed, 0 failed.

First symexec failure: symbolic-execution / symexec-error at cm_emit_binary_generic_fragment's cm_emit_temp_load_plan boundary (then line 107). The current emitter resource had load ++ ([swap; binary] ++ tail), while the callee required load ++ swap :: binary :: tail. Repair: explicit partial equivalence at the generic load boundary and corresponding branch-selection equivalences before main emission calls. This is a resource-list presentation mismatch, not missing ownership or stronger preconditions.

Second symexec failure: symbolic-execution / symexec-error in the first selected pointer branch (then line 134). The partial solver substituted op == 8 inside the requested resource but retained the symbolic op in the current resource. Repair: express the exact branch value as 8 <= op <= 8, and analogously 9 <= op <= 9, avoiding eager one-sided substitution. Mathematical branch conditions are unchanged.

Third symexec passed, generating coverage for all three functions and seven main return paths. Inspected pointer pointee/type/ref obligations and branch-code equivalences contain the necessary input, branch and scale facts. Pointer flag reasoning can reuse cm_pointer_encode__expression_add_safety; no duplicate pointer lemma was introduced.

Generated manual placeholders are controller output and remain unedited for the proof stage. Owner checks do not claim those manual obligations proved or replace controller acceptance/clean replay.

## VC comparison

First annotation attempt: vc_comparisons is empty, as required.

Generated manual declarations: 99 total, 59 split declarations; these counts are not proof-completion claims.
