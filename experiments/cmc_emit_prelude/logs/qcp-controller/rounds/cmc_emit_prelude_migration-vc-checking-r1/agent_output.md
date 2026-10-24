# VC checking decision summary

## Outcome

All three assigned top-level witnesses have a provable selected target. One group covers them without adding a helper.

## Structural Blocker Scan

- Status: passed
- Top-level VCs scanned: 3
- No-split VCs checked first: 1
- Definite blockers: 0

The no-split context-opening goal was inspected first. Its nonzero fact, five fields, and three list resources are precisely the program-context representation; the emitter plan is framed. Remaining goals preserve program_pre and emitter_pre throughout. The final main_id equality is explicitly present as PreH1. No resource address or current-to-@pre bridge is missing.

## Annotation Comparison Review

None: first proving round. Independently, the first assertion exposes the context resources, the second assertion restores them and establishes the five closed opcode equalities, and the subsequent helper calls preserve the main-id equality. The new cm_emit_prelude definition matches the pending list in the second assertion and the final accumulated list.

## Proof-Mode Decisions

The binary split-first pass was completed before whole-goal analysis or strategy planning:

| Parent | Generated split goals in declaration order | Judgement |
|---|---|---|
| entail_wit_2 | split_goal_1, split_goal_2, split_goal_3, split_goal_4, split_goal_5, split_goal_spatial | all six provable |
| return_wit_1 | split_goal_spatial | provable |

Therefore entail_wit_2 and return_wit_1 use aggressive_pre_process. Their top-level provability was not analyzed beyond the cheap structural scan. entail_wit_1 has no split goals, so its whole goal was judged provable and assigned LLM_pre_process.

## Common Proof Patterns

- Context open/close: unfold cm_program_context_rep only, obtain or provide its nonzero fact and three existing field-value witnesses, then cancel exact field and list resources with the entire emitter plan framed.
- Opcode: reduce the closed tvm_opcode_code constructor application and introduce reflexivity as a pure assertion.
- Append normalization: substitute the explicit main-id equality, unfold the eleven-instruction model, normalize singleton appends using ordinary list associativity, and cancel opaque plan/context predicates.

## VC Deltas

- entail_wit_1: context-open pattern; target existential order is tp, gp, sp, and either identical disjunct suffices.
- entail_wit_2: opcode pattern for HALT 27, ADD 8, MOD 12, STORE 5, PUSH 0 in split declaration order; its spatial split uses context-close plus concrete model unfolding. The provided nonzero fact is PreH3.
- return_wit_1: append-normalization pattern; exactly eleven singleton appends and PreH1 supplies the CALL immediate equality. Spatial factors appear in reversed order.

## Grouping Decisions

prelude_context_plan contains 3 top-level witnesses, 7 aggressive split targets (5 closed equalities and 2 spatial goals), no planned helpers, and difficulty 2. One LLM context-opening goal and the aggressive context-closing goal share the same fixed resource shape. The final normalization goal is independently provable but lightweight; splitting it into a singleton group would add setup without removing a heavy tail. There is no substantial mathematical helper, cross-group dependency, safety bundle, or high-risk comparison. The expected critical path is the two small spatial transformations, using the same plan/context library and eleven-instruction model. No new public or local declarations are planned.

## Risks or Blockers

None identified. Proof scripts still require ordinary group validation. This analysis did not modify any formal source or invoke a checker.

## Accounting

```json
{"checker_calls": 0, "checker_failed": 0, "debug_calls": 0, "debug_failed": 0, "manual_edits": 0, "new_helpers": 0}
```
