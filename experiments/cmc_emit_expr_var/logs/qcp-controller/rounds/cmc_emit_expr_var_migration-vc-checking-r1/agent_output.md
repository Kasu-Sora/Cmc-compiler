## Outcome

All nine assigned top-level VCs are suitable for proving. The nine generated split goals were independently judged provable before fixing proof modes. Eight parents use aggressive preprocessing; the sole no-split parent uses whole-goal preprocessing. These are analysis judgements, not completed Rocq proofs.

## Structural Blocker Scan

- Status: passed
- Top-level VCs scanned: 9
- No-split VCs checked first: 1
- Definite blockers: 0

The first structural check was `proof_of_cm_emit_var_expr_which_implies_wit_2`: its existential addresses are exactly those bound inside the two context representations, and both nonzero facts are stored in those representations. The other eight parents retain every required address, constructor equality, branch guard and expression nonzero fact. Return resources and conclusions consistently use the same `_pre` pointers; the implication VCs use the same current pointers on both sides. No missing current-to-pre bridge or whole-goal countermodel was found. This scan did not attempt full top-level proofs.

## Annotation Comparison Review

No comparisons were supplied in this first round. The current case library gives the concrete variable-code definitions. Their imported context definitions bind precisely sp/gp/tp and pp/lp, and the CMVarE representation owns seven fields with zero child pointers. Branch implications carry the zero/nonzero guards explicitly. The return split goals carry both the CMVarE equality and expression nonzero fact. No new mathematical premise or annotation repair is needed.

## Proof-Mode Decisions

The split-only pass visited these goals in declaration order, recording only the following binary outcomes before mode selection:

| Split goal (prefix `proof_of_cm_emit_var_expr_`) | Judgement |
|---|---|
| return_wit_1_split_goal_spatial | provable |
| return_wit_2_split_goal_spatial | provable |
| return_wit_3_split_goal_spatial | provable |
| which_implies_wit_1_split_goal_1 | provable |
| which_implies_wit_1_split_goal_spatial | provable |
| which_implies_wit_3_split_goal_spatial | provable |
| which_implies_wit_4_split_goal_spatial | provable |
| which_implies_wit_5_split_goal_spatial | provable |
| which_implies_wit_6_split_goal_spatial | provable |

All eight parents with splits therefore select `aggressive_pre_process`; their whole-goal provability was not analyzed beyond the required structural scan. Only after finishing all split judgements, the no-split `which_implies_wit_2` was judged provable as a whole and assigned `LLM_pre_process`. Its two disjuncts are identical. Strategies below and in the plan were written after every mode was fixed.

## Common Proof Patterns

- **Expression representation:** specialize the CMVarE equality, reduce the representation/node and constructor projections, extract or introduce nonnullness, and expose or instantiate the child-pointer existentials with zero. The leaf payload is three zero equalities and emp, so the seven fields cancel.
- **Context representation:** unfold only the program/function context predicates, move their pure facts and five pointer existentials across the entailment, and cancel the ten fields plus five list predicates. Lists remain opaque.
- **Code normalization:** reduce the variable lvalue/rvalue code with the existing branch equalities or inequalities. Zero lvalue is already supplied at returns and follows by lia from the two bounds at branch implications. The scalar rvalue adds load; the array rvalue adds an empty list; the lvalue selects address directly. Existing list associativity and right-unit laws identify identical emitter-plan resources without unfolding the emitter.

## VC Deltas

Names below omit `proof_of_cm_emit_var_expr_`; strategies apply only to the selected formal goals.

| Parent | Pattern and actual delta |
|---|---|
| return_wit_1 | Expression representation plus code normalization; scalar rvalue joins `(done ++ address) ++ load`; frame both contexts. |
| return_wit_2 | Same expression fold; array rvalue reduces `address ++ []`; frame both contexts. |
| return_wit_3 | Same expression fold; nonzero lvalue selects address without inspecting array code. |
| which_implies_wit_1 | Expression opening; first split projects nonnullness, second extracts all seven fields. |
| which_implies_wit_2 | Whole-goal context opening; choose a disjunct and supply existential order lp,pp,tp,gp,sp. |
| which_implies_wit_3 | Context closing; pointer witnesses are already universal parameters and both nonzero facts are explicit. |
| which_implies_wit_4 | Scalar-rvalue code normalization; reassociate pending `(address ++ load) ++ tail`. |
| which_implies_wit_5 | Array-rvalue normalization; eliminate `address ++ []`. |
| which_implies_wit_6 | Lvalue normalization; only the nonzero lvalue guard is needed. |

## Grouping Decisions

Initial grouping by representation transformation and program phase yielded three coherent groups. The second load/coupling review retained them:

| Group | Parents | Aggressive splits | New helpers | Difficulty | Context / critical path |
|---|---:|---:|---:|---:|---|
| return_reassembly | 3 | 3 | 0 | 2 | Expression reconstruction, opaque context/emitter frames, three code branches. Possible tail due to larger contexts, but no induction or new library theorem. |
| representation_context | 3 | 3 | 0 | 2 | Two representation definitions; includes one whole-goal VC. Possible tail due to five existential witnesses and separation reassociation, with no new library load. |
| branch_plan_normalization | 3 | 3 | 0 | 1 | Pure code equations over one opaque emitter resource. Shortest expected group. |

The final-result group is separate from independently provable context transitions and branch preparation, so the larger return contexts cannot serialize those checks. All groups are independent and use the existing case-library export chain; there is no sibling-output dependency or helper ownership coupling. Standard `app_assoc`, `app_nil_r` and zero-test facts suffice; no public helper needs to be introduced. Every group has three parents, within both the preferred range and the hard maximum of twelve. No singleton or oversized-group exception is used.

## Risks or Blockers

No blocker. Tactic-level details remain for the workers, particularly pure extraction and existential ordering. The current definitions make all needed identities transparent, so no temporary `Show.` insertion was needed.

Actual owner command counts: coq-debug runs 0, debug failures 0, coq-check runs 0, check failures 0. No compiled-proof claim is made; controller acceptance is separate. No source or formal file was modified.
