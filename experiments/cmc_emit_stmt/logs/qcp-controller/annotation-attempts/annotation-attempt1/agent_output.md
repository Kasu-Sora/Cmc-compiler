# Statement annotation migration

Both original bodies and the mutual-recursive prototypes use their exact original BODY semantics: arbitrary output prefix/tail, complete program/function/statement resources, all original wellformedness/typing/count/layout/temp/PC facts, and the if constructor condition. No runtime token changes, no stronger input assumptions or weakened outputs.

The library exports the verified expr and return libraries, adds the exact 11-constructor statement emission equations, and three transparent AST projections used to name child logical values across QCP annotation scopes. These projections are stable AST observations, not an evaluator of C locals. Necessary constructor opening/closing, wf/count/temp projection, code-shape/length and intermediate-PC facts are emitted as checked VCs; no tactic-engine claims are assumed. Additional general lemmas may be proved by the controller-owned proof phase.

Accepted helper BODY contracts were read from the canonical verified C files: expr, plan, normalize, store, return epilogue, binding-address, context counts and slot-type lookup. Imports include no earlier generated goal/manual/auto files.

## Design and checks

- formal-case-lib-design: 3 calls, 3 passed, 0 failed. Final review used the unchanged final C/lib candidate.
- symexec: 5 calls, 1 passed, 4 failed. Final successful command exited 0 with `status: passed` in 32.745 seconds.
- post-symexec formal-case-lib: 1 call, passed, 0 failed.

## Repairs

1. First symexec: `xe` was not in the next annotation's lexical logic-variable scope. Added explicit binders at each partial annotation boundary.
2. Second symexec: independent existential output pointers detached child resources from the statement's stored field pointers. Repair keeps all node fields and child payload in the same local conversion. Stable constructor projections avoid reintroducing fresh child AST witnesses in separate annotations.
3. Third symexec: second sequence call expected PC `pc + count(first)` while the local held `pc + retval`; the known equality was opaque to spatial matching. Added local-store canonicalization at the six counter return boundaries, directly corresponding to the source proof's retarget-cell step. This is a proved equality conversion, not a runtime assignment.

4. Fourth symexec: scripted constructor-projection replacement accidentally renamed three `where` keys on the if-helper call. Restored its exact `guard_`, `yes_`, and `no_` formal parameter names; values remain the canonical stmt projections.

## Annotation plan and semantic review

There are no lexical C loops and no full ordinary `Assert`. Local `which implies` conversions serve constructor opening/closing, helper-call code-fragment alignment, counter-result canonicalization, and output restoration. All live local stores remain framed except the explicit canonicalization of the same counter cell. Program/function contexts and statement children are restored after each branch. Empty skip/declaration code is normalized at the exit bridge.

For while, the recursive body's loop flag is exactly true; break target is the loop end and continue target is the incoming PC. If and while instruction order and branch target arithmetic follow the source equations. Initializer and return preserve the original declared-type normalization.

Higher-order-witness review: none newly introduced. The existing arbitrary total lookup policy and codegen-obligation parameters are reused unchanged.

Reference impact: the canonical expr migration supplies accepted helper BODY contracts and the established representation-open/close style. The skill's majority-element and algorithm-mirror examples were reviewed for property-oriented annotation discipline; no algorithm or generated proofs were copied.

## VC comparison

First attempt: no prior failed VCs; `vc_comparisons` is empty.

## Generated obligations

- Top-level manual obligations: 122.
- Split obligations: 280.
- The manual/auto/goal/check files were written only by canonical controller symbolic execution and remain untouched.
- This delivery is annotation completion only; no claim is made that remaining manual obligations are proved.
