# Outcome

All 13 current top-level witnesses have a proving assignment. No annotation, specification or dependency blocker was found. This is a proofability analysis, not a proof-check result. No formal file was modified and no debug/check command was necessary.

## Structural Blocker Scan

- Status: passed
- Top-level VCs scanned: 13
- No-split VCs checked first: 5
- Definite blockers: 0

The five no-split whole goals (which_implies 1, 2, 4, 6, 8) were checked first. Opening the expression provides the actual node resource addresses; branch refinement retains the same emitter/out/capacity/done/tail and carries e = cm_leaf_source_expr leaf. The remaining eight goals retain their node addresses or explicit source-view equalities. No current-to-@pre bridge is missing, and all target existentials can be selected from existing node fields or leaf constructor payloads.

## Annotation Comparison Review

No comparisons were supplied (first proving round). Current branch scalar facts have concrete sources: Const well-formedness implies integer type; String counts representability contains the signed-32-bit sid bound; Sizeof well-formedness contains requested-type code well-formedness and references; Getc follows from the finite leaf domain and the three excluded tags. Expression field resources are established by which_implies 1 and restored by 3/5/7/9.

## Proof-Mode Decisions

The complete split-first pass, in declaration order, yielded:

| Split goal suffix (prefix proof_of_cm_emit_leaf_expr_) | Judgement |
|---|---|
| return_wit_1_split_goal_1 | provable |
| return_wit_2_split_goal_1 | provable |
| return_wit_3_split_goal_1 | provable |
| return_wit_4_split_goal_1 | provable |
| which_implies_wit_3_split_goal_spatial | provable |
| which_implies_wit_5_split_goal_spatial | provable |
| which_implies_wit_7_split_goal_spatial | provable |
| which_implies_wit_9_split_goal_spatial | provable |

All eight parents select aggressive_pre_process solely because every generated split is provable; their whole-goal provability was not separately analyzed after the structural scan. The five no-split whole goals select LLM_pre_process after whole-goal analysis. Strategies were written only after these decisions. No failed split or blocker exists.

## Common Proof Patterns

- **P1 — equality projection:** the split is a pure source-view equality already supplied among quantified hypotheses. Introduce and select that premise; no spatial or existential work.
- **P2 — representation open/close:** destruct the expression constructor to expose the recursive representation, node and payload. Opening extracts existing pointer witnesses and nonnull; closing packages the same pointers and uses supplied nonnull. Fields and payload cancel exactly. The call branch has definitionally identical recursive argument-list resources, so do not unfold recursive subtrees unnecessarily.
- **P3 — leaf branch refinement:** substitute the source-view equality, then destruct the four-way leaf view. Guard equalities/exclusions eliminate other constructors. Select the remaining payload as existential witness; derive the branch-specific pure facts from wf/counts while retaining copies of those original facts. Source and target emitter plans are identical after constructor substitution. No output bytes, list length, frame or abstract execution state changes at this annotation point.

No newly proved or modified helper is planned; the routes are finite constructor reduction, premise projection and separation cancellation. No proof reuse analysis was performed.

## VC Deltas

All names below use prefix proof_of_cm_emit_leaf_expr_.

| VC | Pattern and actual delta |
|---|---|
| return_wit_1 | P1; Const, equality at PreH7 (also PreH17). |
| return_wit_2 | P1; String, equality at PreH12 (also PreH24). |
| return_wit_3 | P1; Sizeof, equality at PreH10 (also PreH23). |
| return_wit_4 | P1; Getc, equality at PreH6 (also PreH18). |
| which_implies_wit_1 | P2 opening; whole goal has duplicate disjuncts; target existential order is xargs, xb, xa. |
| which_implies_wit_2 | P3; kind 0, choose n/ty; cm_integer_type ty entails cm_type_code_wf ty. |
| which_implies_wit_3 | P2 closing; Const branch location, general e and supplied xa/xb/xargs. |
| which_implies_wit_4 | P3; kind 1, choose sid/ty; cm_i32_code_count sid provides both sid bounds. |
| which_implies_wit_5 | P2 closing; String branch location, same general representation statement. |
| which_implies_wit_6 | P3; kind 9, choose asked/ty; wf supplies both requested-type properties. |
| which_implies_wit_7 | P2 closing; Sizeof branch location, same general representation statement. |
| which_implies_wit_8 | P3; tags 0/1/9 excluded, choose Getc ty; duplicated dispatch fact is harmless. |
| which_implies_wit_9 | P2 closing; Getc branch location, same general representation statement. |

## Grouping Decisions

| Group | Top-level | Aggressive splits | New helpers | Difficulty | Context/load |
|---|---:|---:|---:|---:|---|
| return_projection | 4 | 4 | 0 | 1 | Pure terminal equalities; no spatial context. |
| expression_representation | 5 | 4 | 0 | 2 | One LLM open plus four aggressive closures; same recursive node/payload definitions and seven field resources. |
| branch_refinement | 4 | 0 | 0 | 2 | Four LLM branches; shared leaf view, tag discrimination, wf/count projections and one unchanged emitter plan. |

The second load/coupling review keeps all groups within 2–6 witnesses and the hard limit 12. Likely tails are representation handling (four spatial splits and one whole opening; recursive representation library context, zero helper burden) and branch refinement (four whole goals, zero splits/helpers; finite wf/count conjunction context). Independent final-result projection work is separated from both transitions. No mathematical helper family couples these groups, no cross-group dependency is needed, and no permutation/sum/length fact is introduced. Every group can be proved from the frozen common inputs alone.

## Risks or Blockers

No definite blocker. Small proof-engineering risks are constructor reduction of recursive expression representation, existential ordering, and preserving wf/count assumptions while extracting their conjuncts. All needed facts and addresses are present. Terminal status does not claim controller acceptance.
