# Annotation attempt 1

Read the full handoff and required annotation-designing guides, including predicate-first positive/negative examples and branch/resource guidance. Used the previous accepted C BODY specifications (not header guesses) for all 15 external helpers, and the call module recursive declaration for the public contract. All seven original BODY contracts preserve their full pure facts and resources; constructor-specific helper assumptions are retained.

New definitions are constructor observations and optional code suffixes only. Existing general expression-code, length/count, lookup, policy and cg models are imported unchanged. No old manual/auto module is imported. No new axioms or admitted facts.

## Check history
1. formal-case-lib-design: passed (exit 0; controller status passed). No symexec or post-lib calls yet.

## Ordinary Assert review
None; planned boundaries use partial entailments and call instances to preserve the ambient local-store frame.

## VC comparison
None (first attempt).

Constructor-specific body elaboration now includes payload opening/reassembly, all recursive child wf/count/type facts, child pc/temp safety boundaries, exact code prefix cuts, and explicit actual helper With bindings. No runtime statement was changed.

2. symexec: failed, syntax at Extern Coq declaration line 23; QCP requires type declarations and value declarations in separate blocks. Repaired by splitting the combined declaration block; runtime unchanged.

3. One malformed attempted design invocation omitted the controller path and exited 1 before controller execution; no check was performed. Immediately reran the exact handoff command.
4. formal-case-lib-design: passed (exit 0; controller status passed).
5. symexec: failed, syntax at declaration line 23: unused namespaced IntArray declarations had been misclassified as types. Removed the two unused inherited array entries.

6. symexec: failed, undeclared logical xa at first payload-opening boundary. Existentials in one partial annotation do not become named variables for later annotation text. Repaired all six helper openings/closures into single quantified node-and-child entailments; removed explicit binding of the dispatcher local existential simple so QCP can infer it from resource/formula matching.

7. symexec: failed at intrinsic code-prefix partial entailment (line 421): local pure rewriting changed the resource expression argument to its constructor, preventing syntactic spatial matching against the original e/lvalue resource. Repaired internal constructor equalities with transparent cm_expr_shape and zero guards with equivalent two-sided bounds; original function specifications remain unchanged.

8. formal-case-lib-design: passed (exit 0/status passed) after cm_expr_shape addition.
9. symexec: failed after fully processing intrinsic, unary, index and assignment; binary line 1288 rejected multiple cases inside a partial entailment. Replaced short-op disjunction with equivalent Z range 0 <= op_ <= 1. Removed redundant repeated input facts from partial consequents (ambient pure frame retained); no contract weakening. Independent token comparison confirms all seven runtime bodies match frozen runtime-source.c exactly.

10. symexec: failed at first lvalue read (line 390) because removing repeated facts also removed local-store ownership implicitly materialized by current-variable reads in partial annotations. Restored the full pure/cell-preserving consequents; retained the short-op range repair. This was an actual failed simplification, not a completed optimization.

11. symexec: failed late in binary short-circuit emission: final PUSH used concrete ternary result (1/0), while pending code retained opaque cm_short_value(op_). Added a call-boundary equality expressed as two inequalities, preserving the local cell and explicitly rewriting the pending immediate to short_value.

12. symexec: progressed past short-circuit PUSH, then failed at ordinary binary_finish call: runtime field value cm_rep_expr_op(e) did not syntactically match the op_ used by the pending finish code. Opened the fixed unary/binary root op field directly at the constructor parameter op_ (and use the same typed field when closing); constructor-shape entailments justify that exact observation.

13. symexec: all six static helper bodies completed; failed at dispatcher first simple call because full-to-simple code conversion dropped pc/temp local cells (simple code does not mention them). Added explicit pc == pc@pre and temp == temp@pre bridges to each simple-view conversion consequent.

## Design review
No loops occur in the seven runtime bodies. No ordinary Assert, Branch clear, Branch join, or multi-invariant was introduced. Partial entailments preserve the live node/child resources and local cells while exposing constructor observations, child wf/count/type/temp/pc facts, and exact instruction suffixes. cm_expr_shape is a transparent equality wrapper used only internally to prevent premature QCP substitution; function contracts retain their original constructor equalities.

The dispatcher simple-view existential is an existing finite algebraic view, not a higher-order function witness. No new higher-order existential was introduced.

14. symexec: passed (exit 0/status passed), 97.433 seconds. All four generated roles were committed by the exact controller command.
15. formal-case-lib (post-symexec): passed (exit 0/status passed).

## Actual local effort totals
- Exact formal-case-lib-design calls: 3; passed: 3; failed: 0.
- Exact symexec calls: 10; passed: 1; failed: 9. All failures were symbolic-execution annotation/syntax/matching failures, not tool-category failures.
- Exact post-symexec formal-case-lib calls: 1; passed: 1; failed: 0.
- Additional malformed attempted design launch: 1; exited before controller execution because the controller path was accidentally omitted. This was corrected immediately and is excluded from passed controller checks.
- No raw Coq, raw symbolic-execution, Dune, or Make invocation was used. Generated roles were never manually edited.

## Generated-obligation review
The current manual has 176 top-level pending witnesses: intrinsic 24, unary 34, index 16, assignment 12, binary 39, member 13, dispatcher 38. Categories: 83 which-implies, 51 partial-solve, 29 return, 13 safety. Source constructor facts, full original premises, exact pending/done code, child heap resources, and arithmetic facts are present in generated statements. Proof completion and controller acceptance remain separate from this annotation delivery; the generated manual placeholders have not been edited by this owner.

First-attempt vc_comparisons remains empty. The plan is ready. Seven runtime body token streams match the frozen runtime source, and the controller's later clean replay/final checks remain authoritative.
