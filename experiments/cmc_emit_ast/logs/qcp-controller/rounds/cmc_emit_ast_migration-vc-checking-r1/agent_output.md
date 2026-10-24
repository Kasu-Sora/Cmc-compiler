# VC-checking decision summary

## Outcome

All 9 manual top-level witnesses have a proof mode and an independent proving assignment. All 14 generated split goals are judged provable. This is a source-based feasibility analysis; controller acceptance and actual proofs remain separate.

## Structural Blocker Scan

- Status: passed
- Top-level VCs scanned: 9
- No-split VCs checked first: 1
- Definite blockers: 0

The no-split `proof_of_cm_emit_binding_address_entail_wit_1` was checked first. Both context predicates own precisely the field/list resources required by its assertion; their existential pointers supply all five witnesses and their pure conjuncts supply nonzero roots. Every alternative of `cm_binding_valid` supplies a nonnegative slot. Across the remaining eight top-level VCs, the generated addresses and scalar parameters use the same pre-state values on both sides. Return heaps retain every field/list needed to fold the contexts. The plan predicate contains the needed capacity fact and resolved-emitter resource. No missing address, scalar equality, or current-to-pre bridge was found.

## Annotation Comparison Review

No comparisons were supplied in this first round. Fact-source checks were made against current definitions: `cm_wf_program` contains `cm_typed_program`, whose global conjunct is exactly the premise of `cm_rep_globals_prefix_matches`; the explicit parameter/local `cm_slots_wf` premises support both member-prefix and parameter-size bridges. Callee result equalities and scope guards are present in the return splits. `cm_plan_fragment_capacity` is already proved in the imported case-library closure. No new mathematical premise or helper is required.

## Proof-Mode Decisions

The split-only pass finished before whole-goal mode selection and before strategy/group planning. The three return spatial splits, all seven call-precondition pure splits, the three plan-entry splits, and the plan-return spatial split are each provable. Therefore all eight parents select `aggressive_pre_process`; no whole-goal strategy is assigned to them. The one no-split entry entailment is provable as a whole and selects `LLM_pre_process`.

| Parent suffix after `proof_of_cm_emit_binding_address_` | Split suffixes, each provable | Mode |
| --- | --- | --- |
| return_wit_1 | spatial | aggressive_pre_process |
| return_wit_2 | spatial | aggressive_pre_process |
| return_wit_3 | spatial | aggressive_pre_process |
| partial_solve_wit_2_pure | 1, 2, 3 | aggressive_pre_process |
| partial_solve_wit_4_pure | 1, 2 | aggressive_pre_process |
| partial_solve_wit_6_pure | 1, 2 | aggressive_pre_process |
| plan_entail_wit_1 | 1, 2, spatial | aggressive_pre_process |
| plan_return_wit_1 | spatial | aggressive_pre_process |
| entail_wit_1 | none | LLM_pre_process |

## Common Proof Patterns

- **Context boundary:** unfold only the program/function context predicates, retain the resolved-emitter frame, instantiate the same five pointers, and cancel the exact field/list resources. Nonzero roots are extracted at entry and supplied from explicit premises at return.
- **Fragment identity:** resolve scope guards and use the established representation-prefix/size lemmas under the supplied well-formedness facts; rewrite the emitted instruction list while keeping the resolved-emitter predicate opaque.
- **Pure call capacity:** reduce opcode constants or fragment lengths. A push has length 1 and every fp-relative address fragment has length 4, regardless of its offset. These obligations do not require the representation-to-model address equality.
- **Plan budget:** expose only the plan predicate's pure bound; existing append-length arithmetic gives fragment and remaining-tail bounds, and the spatial resource itself is unchanged.

## VC Deltas

Names below use the parent suffixes in the table. Exact split-specific strategies are in the plan.

- `entail_wit_1`: context boundary in the opening direction; derive slot nonnegativity from the three binding-valid alternatives and choose the first whole-goal disjunct.
- `return_wit_1`: fragment identity for globals uses the global well-formedness projection from the program; context boundary closes both contexts.
- `return_wit_2`: fragment identity for locals combines parameter total-size and local-prefix bridges; context boundary closes both contexts.
- `return_wit_3`: fragment identity for parameters uses two false scope guards and the parameter-prefix bridge; context boundary closes both contexts.
- `partial_solve_wit_2_pure`: pure call capacity adds the two PUSH opcode checks and the singleton-length capacity check.
- `partial_solve_wit_4_pure`: pure call capacity for the local branch; its two generated conclusions coincide after preprocessing.
- `partial_solve_wit_6_pure`: pure call capacity for the parameter branch; its two generated conclusions also coincide.
- `plan_entail_wit_1`: plan budget supplies two pure consequences and strips the plan wrapper under an unchanged context frame.
- `plan_return_wit_1`: plan budget closes the wrapper using the retained bound on the new prefix and tail.

## Grouping Decisions

| Group | Top-level witnesses | Aggressive splits | Difficulty | New helper load |
| --- | ---: | ---: | ---: | ---: |
| return_contexts | 3 | 3 | 3 | 0 |
| call_capacity | 3 | 7 | 1 | 0 |
| context_plan | 3 | 4 | 2 | 0 |

The initial partition follows final-result reconstruction, pure call prerequisites, and context/plan boundaries. The second load-and-coupling review retains three groups of three; there are no singletons or groups above six. `return_contexts` is the likely critical path because its three spatial goals combine context folding with three distinct address rewrites. Its library load is the existing global/member prefix bridges and parameter-size bridge, and its persistent context is the same program/function field layout. It needs no new induction or helper family. This group is placed first. The seven lightweight pure splits are isolated in `call_capacity`, so they do not lengthen that final-result group. The independent opening and plan-wrapper work belongs to `context_plan`; the sole whole-goal mode is confined there. All groups can finish without sibling outputs. Stable prefix, size, and append-length facts already exist in the active library closure, so there are no new public or local declarations to plan.

## Risks or Blockers

No annotation, specification, or dependency blocker was found. Context folding may need explicit existential ordering and spatial reassociation, but all resources and witnesses are present. Avoid unfolding the resolved-emitter representation during the return reconstruction, because fragment rewriting suffices.

## Execution and Effort

- Manual edits: 0.
- Controller `coq-debug` invocations: 0.
- Controller checks run by this owner: 0.
- Failed controller/debug checks: 0.
- Proof compilation attempts: 0; no proof success is claimed.

The source definitions fully determined the feasibility decisions, so no `Show.` instrumentation or debug execution was needed. One read-only `rg` search returned no match in the initially searched dependency file; the definitions were then found in its imported counts library. This was a lookup miss, not a proof or controller failure.
