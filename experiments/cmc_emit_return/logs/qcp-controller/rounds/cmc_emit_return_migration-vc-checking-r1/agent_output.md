# Outcome

Both assigned top-level witnesses have provable generated split goals. The plan assigns all 10 splits through their parents to two independent, light groups. No helper or annotation change is needed. This is a provability assessment; controller acceptance and actual proof checks remain separate.

## Structural Blocker Scan

- Status: passed
- Top-level VCs scanned: 2
- No-split VCs checked first: 0
- Definite blockers: 0

The entry assertion and return obligation preserve policy, program, emitter_pre, out, capacity, and tail at the required resource address. There are no existential witnesses or unbridged current/prestate scalar references. The only resource differences are concrete return-list expansion and association of the completed prefix. No whole-goal countermodel was found. No whole-goal proof strategy was developed after this structural scan.

## Annotation Comparison Review

There are no comparisons in this first proving round. The eight opcode facts are established by the definition of tvm_opcode_code exported through the case library (Ret 23, Store 5, Load 4, Push 0); they need no additional premise. The entry entailment establishes these facts before the six emission calls. cm_return_epilogue in the current case library defines exactly the six instructions consumed by those calls.

## Proof-Mode Decisions

The complete binary split pass, in declaration order, found:

| Parent | Split suffix | Judgment |
| --- | --- | --- |
| proof_of_cm_emit_return_epilogue_plan_entail_wit_1 | _split_goal_1 | provable |
| same | _split_goal_2 | provable |
| same | _split_goal_3 | provable |
| same | _split_goal_4 | provable |
| same | _split_goal_5 | provable |
| same | _split_goal_6 | provable |
| same | _split_goal_7 | provable |
| same | _split_goal_8 | provable |
| same | _split_goal_spatial | provable |
| proof_of_cm_emit_return_epilogue_plan_return_wit_1 | _split_goal_spatial | provable |

Only after this pass, both parents were assigned aggressive_pre_process because every generated split was provable. No top-level provability analysis was needed.

## Common Proof Patterns

- P1, constant pure conclusion: the antecedent is the existing plan resource; the consequent is a pure proposition with no existential. Introduce the pure proposition independently of the heap, compute the opcode definition, and use reflexivity or arithmetic. No guards, bounds, resource change, or new helper is needed.
- P2, plan argument normalization: preserve the opaque plan resource and all scalar parameters. Normalize only the list argument until antecedent and consequent coincide, then use entailment reflexivity. There is no heap split/merge, existential instantiation, or extra refinement transition; these obligations connect the abstract plan representation before and after the already specified calls.

## VC Deltas

- Entry split goals 1 through 8 use P1 with, in order: Ret non-call, Ret code, Store non-call, Store code, Load non-call, Load code, Push non-call, Push code. Their literal target values are 23, 5, 4, and 0, all distinct from 22.
- Entry spatial split uses P2 by unfolding cm_return_epilogue and computing its append to tail; done stays unchanged.
- Return spatial split uses P2 by unfolding cm_return_epilogue and associating the six singleton appends to the right using List.app_assoc, then reducing the concrete appends. The completed prefix becomes done ++ cm_return_epilogue. The eight opcode assumptions are available but unnecessary for this equality.

## Grouping Decisions

Initial grouping separated the entry assertion from the final-result boundary. The load-and-coupling review retained that division: both use the same imported library but have no persistent proof context or new helper ownership coupling. Each single-witness group is justified by its distinct program phase; splitting the independent final-result normalization follows the required critical-path review.

| Group | Top-level count | Aggressive split count | New helpers | Difficulty | Critical-path assessment |
| --- | --- | --- | --- | --- | --- |
| epilogue-open | 1 | 9 | 0 | 1 | Eight constant facts and one definitional list expansion; repeated light obligations, no substantial mathematical tail. |
| epilogue-return | 1 | 1 | 0 | 1 | Independent final-result association; existing List.app_assoc supplies the only mathematical rewrite. |

The opening group may take longer only because of split count. There is no heavy helper/library load and no stable cross-group fact to prove or promote. Both groups are independent and require no sibling output. The maximum of six witnesses is respected.

## Risks or Blockers

None identified. No C, case library, goal, auto, check, or manual bytes were changed. Proof reuse was not analyzed.

## Effort Accounting

- Controller coq-debug calls: 0.
- Controller coq-check calls: 0.
- Debug/check failures: 0.
- Temporary Show insertions: 0.

The current goal definitions and transparent library definitions were sufficient for this analysis; no Rocq debug inspection was needed. These counts exclude subsequent controller acceptance and worker proof checks.
