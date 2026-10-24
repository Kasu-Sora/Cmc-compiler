# VC checking decision summary

## Outcome

All 7 current top-level manual witnesses are assigned to 3 independent groups. The 4 generated splits are provable. No formal source or manual was edited and no debug command was required.

## Structural Blocker Scan

- Status: passed
- Top-level VCs scanned: 7
- No-split VCs checked first: 3
- Definite blockers: 0

The no-split goals (which_implies 1, 2, 4) were checked first. Node opening has the necessary owned node and nonzero address; branch refinement keeps the same emitter/out/capacity and done/tail. Its e/source-view equality bridges constructor selection. Counts-representable supplies the variable slot i32 range and type-code well-formedness; expression-wf supplies binding validity. Return goals carry explicit simple-constructor equalities and identical pre-state resource addresses. Node closure goals have all seven fields, payload, and nonzero address. No required current-to-@pre bridge or resource is missing.

## Annotation Comparison Review

No comparisons were supplied (first proving round). Independently checked the current branch facts: variable binding validity comes from cm_expr_wf, type-code-wf from the node component of cm_expr_counts_representable, and slot bounds from its CMVarE component. Simple-view and kind facts select the existing constructor; no additional mathematical assumption is introduced.

## Proof-Mode Decisions

The full split-only pass completed before mode selection: return_wit_1, return_wit_2, which_implies_wit_3, and which_implies_wit_5 each have exactly one spatial split, all provable. Their modes are aggressive_pre_process; their whole-goal provability was not analyzed. The three no-split whole goals (which_implies_wit_1, 2, 4) are provable and use LLM_pre_process. Detailed strategies were prepared only after these decisions.

## Common Proof Patterns

- **B — branch refinement:** preserve the single emitter-plan resource; use e = source(simple), discriminate the impossible simple constructor from kind, select existing constructor fields, project the necessary wf/count bounds, and reduce the code function. Instantiation never changes done, tail, or emitter addresses.
- **N — expression node representation:** the cm_expr_rep_node equality and cm_expr_node expose or package the same seven fields and opaque payload. Opening reverses existential ordering to match xargs/xb/xa; closing uses the supplied xa/xb/xargs and nonzero pointer.
- **R — return code normalization:** the explicit equality naming the selected simple constructor reduces cm_simple_code_for, after which all four framed resources cancel without list rearrangement.

## VC Deltas

| Witness suffix | Pattern | Actual delta |
|---|---|---|
| return_wit_1 | R | Variable constructor; preserve var code appended to done. |
| return_wit_2 | R | Leaf constructor; preserve leaf code appended to done. |
| which_implies_wit_1 | N | Whole goal opens node and supplies target existentials in xargs/xb/xa order. |
| which_implies_wit_2 | B | kind = 2; instantiate scope/slot/ty and extract slot bounds, type-code-wf and binding validity. |
| which_implies_wit_3 | N | Spatial split packages node after variable selection. |
| which_implies_wit_4 | B | kind <> 2; instantiate leaf and establish its leaf-domain predicate. |
| which_implies_wit_5 | N | Spatial split packages node after leaf selection. |

## Grouping Decisions

Initial grouping by program phase and proof idea gave branch_selection (2 whole goals), expression_representation (1 whole goal + 2 spatial splits), and return_plans (2 spatial splits). The second load-and-coupling review retained these groups: each has 2–3 witnesses, no planned new helper family, and no inter-group dependency. No singleton or group above six is present.

The likely tail is branch_selection: 2 whole goals, 0 splits, 0 new helpers, and the shared simple/leaf/variable model plus wf/counts projection context; difficulty 2. Its two branch alternatives share the finite view discrimination pattern, so keeping them together avoids unnecessary context duplication. Expression_representation has 2 splits, 0 helpers and a single representation bridge/context; difficulty 2. Return_plans is independently provable final-result work, separated from both transition and representation work; 2 splits, 0 helpers, difficulty 1. All required model equations are already in the current dependency closure. No stable mathematical helper needs newly proving or promotion.

## Risks or Blockers

No blocker identified. Care is needed with existential order in node opening and the nested conjunction structure when projecting variable range/type facts. These are proof construction details, not missing annotation premises. Provability judgments are planning results; controller group checks remain the proof acceptance gate.
