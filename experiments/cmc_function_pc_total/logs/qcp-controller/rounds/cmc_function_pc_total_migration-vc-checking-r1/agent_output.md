# Outcome

All 12 assigned top-level VCs admit a proving assignment: 8 aggressive and 4 whole-goal assignments, in 5 independent groups. No annotation, specification or dependency blocker was found. This is a provability analysis, not a completed Rocq proof or controller acceptance.

## Structural Blocker Scan

- Status: passed
- Top-level VCs scanned: 12
- No-split VCs checked first: 3
- Definite blockers: 0

The three no-split goals were prefix entail 1, prefix entail 2 and PC entail 1. All resource addresses match their pre-state addresses. Existentials can be instantiated from list/context representations; the scalar values in the assertions are consistently the pre-state values. The remaining nine top-level goals likewise have the necessary addresses, index bridges and return equations. Null-list information is present in the whole return goal even though its generated pure split omits it.

# Annotation Comparison Review

There are no comparisons in this first round. The current inputs independently establish the important facts: prefix entail 1 projects head/tail representability and successor readiness from the recursive predicates; prefix entail 2 retains those facts across the count call; the recursive-call precondition establishes the successor index equation. PC entail 1 obtains global counts from wellformedness and concrete readiness from the entry premise. The imported cm_wf_program definition includes the model-code-length bound; it is not an extra assumption introduced by this plan. The current case library proves cm_function_prefix_total_bounds without a target-range condition, so arbitrary negative and oversized targets are covered.

# Proof-Mode Decisions

Abbreviations in the following tables: P denotes `proof_of_cmc_function_prefix_total_`, C denotes `proof_of_cmc_function_pc_total_`. Each row refers to the exact suffix appended to that prefix. Split judgements were completed in declaration order before deciding whole-goal modes; the entries below record only the binary result from that pass.

| Parent | Split suffix in declaration order | Provable |
|---|---|---|
| P safety_wit_4 | split_goal_1, split_goal_2 | yes, yes |
| P safety_wit_6 | split_goal_1, split_goal_2 | yes, yes |
| P return_wit_1 | split_goal_1, split_goal_2, split_goal_spatial | yes, yes, yes |
| P return_wit_2 | split_goal_1, split_goal_2 | yes, yes |
| P return_wit_3 | split_goal_1, split_goal_2 | yes, no |
| P partial_solve_wit_2_pure | split_goal_1, split_goal_2 | yes, yes |
| C safety_wit_2 | split_goal_1, split_goal_2 | yes, yes |
| C entail_wit_2 | split_goal_spatial | yes |
| C return_wit_1 | split_goal_1, split_goal_2 | yes, yes |

There are 18 splits: 17 provable and 1 unprovable. Every parent whose splits are all provable selects aggressive_pre_process, without further whole-goal provability analysis. P entail_wit_1, P entail_wit_2 and C entail_wit_1 have no splits and select LLM_pre_process after whole-goal analysis. P return_wit_3 also selects LLM_pre_process: its first disjunct retains the list representation and therefore establishes the empty-list case. Its failed pure split has fn_pre=0 but no relation between that scalar and functions; a nonempty function list and target different from the index can have a positive prefix. This failed split is not a whole-goal blocker.

# Common Proof Patterns

**B — Total-prefix bounds.** Apply the already proved cm_function_prefix_total_bounds. For recursive addition, the recursive index equality identifies the tail's starting index, and the cons representability premise supplies the full code-size bound. Unfold code size once and use the count-result equations. For 11+prefix, project the model-code-length bound from wellformedness and normalize the full-list starting index to zero. All resulting arithmetic is linear. Spatial antecedents of pure entailments are frames; pure splits have none. No existential or heap conversion is needed.

**I — Index and base equations.** Substitute the cons equality, rewrite Zlength_cons and use the invariant's index equation and bound. Stop-at-target uses the zero test in cm_function_prefix; count zero is representable. This is the transition from current index to successor index, or from a zero remaining count to the base result.

**F — Function-list resources.** The list representation separates header and body lists. The existing cons equivalences expose or rebuild a function context, body and tail. Context opening supplies params/locals pointers; context closing chooses those existing pointers. Program representation stays framed. Null-pointer return must retain the header resource to rule out a cons list. Pure head/tail facts come from counts/readiness definitions, not from an unproved assertion.

**P — Program context.** Open or close the context with its existing structs/globals/strings pointers, retaining the function-list frame. Wellformedness supplies global counts and code length; concrete readiness supplies safe structs and ready functions. The existing positive-code-size/length lemma gives the list-length bound.

**E — Return equations.** A recursive return unfolds only the cons case of cm_function_prefix, uses the nonzero remaining-count guard, and normalizes the recursive argument. The PC equation is cm_function_pc's definition after substituting the returned prefix.

# VC Deltas

| VC | Selected pattern and actual delta |
|---|---|
| P safety_wit_4 | I: successor upper bound is already in cm_i32_code_count; lower bound uses nonnegative index. |
| P safety_wit_6 | B: bound head+recursive prefix by the full cons code size; lower bound uses the two returned nonnegativity facts. |
| P entail_wit_1 | F: distinguish nil/cons using nonzero fn, expose bp,np, and project successor readiness plus head statement-wf. |
| P entail_wit_2 | F: keep f_2/rest_2/bp_2/np_2 and expose only params/locals pointers after the count call. |
| P return_wit_1 | B for split 1; E for split 2; F backwards for the spatial split, choosing pp,lp,bp,np. |
| P return_wit_2 | I: zero is representable, and target-target reduces to zero for either list constructor. |
| P return_wit_3 | F whole-goal first disjunct: null root forces nil, after which the prefix is zero for every target and resources cancel. |
| P partial_solve_wit_2_pure | I: the two splits are respectively successor index equality and successor length bound. |
| C safety_wit_2 | B: the additional constant 11 is covered by the full model-code bound, not by prefix representability alone. |
| C entail_wit_1 | P: instantiate tp,gp,sp and derive the length bound using the imported length lemma and global counts. |
| C entail_wit_2 | P backwards: instantiate sp,gp,tp and cancel all program fields/list resources. |
| C return_wit_1 | B for representability; E for the definition of PC. Both selected splits are pure. |

# Grouping Decisions

Strategies were fixed before grouping. Initial families were resource opening, index transitions, arithmetic bounds and return reconstruction. A second load/coupling review split independently provable addition safety from final-result work.

| Group | Top-level VCs | Active aggressive splits | New helpers | Difficulty | Load/context review |
|---|---:|---:|---:|---:|---|
| result_reconstruction | 2 | 5 | 0 | 3 | Likely tail: two bound/equality families and one function-list rebuild. Existing total-prefix and cons lemmas cover the mathematics; mixed pure/spatial context is confined to these results. |
| addition_safety | 2 | 4 | 0 | 2 | Independent upper/lower arithmetic checks; separated from final results so they do not extend that tail. Uses existing bounds directly. |
| prefix_resource_opening | 3 | 0 | 0 | 3 | Likely tail: three whole-goal proofs with list/context unfolding. They share header/body-list representation context; no heavy arithmetic or helper development. |
| prefix_index_transition | 3 | 6 | 0 | 1 | Lightweight aggressive normalization, constant bounds and successor equations. No persistent spatial manipulation. |
| program_context_transition | 2 | 1 | 0 | 2 | One whole-goal opening and one aggressive closing; common five-field/three-list context and one established length bound. |

All groups contain 2–3 top-level VCs, below the maximum of 12. There are no singleton or over-six groups. The two likely tails have no indivisible new helper family; final results have already been separated from transition/safety work. Stable sum/length facts are already proved in the current case library/imported library: cm_function_prefix_total_bounds, cm_functions_length_bound__model_length_bound and the function-list cons equivalences. No new or modified helper declaration is expected, so the plan has no helper entries. Groups do not depend on sibling results.

# Risks or Blockers

No blocker. Keep the null-list return in whole-goal mode; switching it to the pure splits would discard an essential resource-derived fact. Preserve the full model-code bound when proving 11+prefix, since prefix's own 32-bit bound alone is insufficient. No manual Show insertion was necessary, and no formal source file was modified.
