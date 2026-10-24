# Outcome

All 41 top-level obligations have a proof assignment. All 84 generated split goals were judged provable in the split-first pass; 38 parents therefore use aggressive_pre_process without separate whole-goal analysis. Three no-split representation-opening obligations use LLM_pre_process. No formal files were changed and no proof reuse analysis was performed.

## Structural Blocker Scan

- Status: passed
- Top-level VCs scanned: 41
- No-split VCs checked first: 3
- Definite blockers: 0

The no-split parameter-list opening and two function-context openings were inspected first. Existential next/params/locals addresses come from the same source predicate. Then all 41 top-level resource/scalar shapes were scanned: return and folding addresses match, rewritten slot/offset/fid values retain their entry bridges, and body_pc retains its defining equality. No missing resource address, scalar equality, or current-to-entry bridge was found. This was a structural screen, not a whole-goal proof analysis for split parents.

# Annotation Comparison Review

No comparisons were supplied (first proving round). The new recursive facts are established by parameter which_implies 3, rather than assumed: list shape comes from which_implies 1, semantic member size from which_implies 2, and each tail property/size/length bound has a split establishing obligation. Prologue frame-size equality and parameter bounds are established by its which_implies 2 and 4. No additional premise was accepted solely because an annotation claimed it.

# Proof-Mode Decisions

Split judgements were completed before choosing modes; only after all modes were fixed were strategies/helpers/groups planned. The following ledger is in current manual parent order; every listed split is individually judged provable. An interval lists all integer split suffixes in declaration order. No split failed and no split parent needed fallback whole-goal analysis.

| Parent (proof_of_ prefix omitted) | Split suffixes judged provable | Mode |
|---|---|---|
| cmc_emit_param_stores_from_return_wit_1 | spatial | aggressive |
| cmc_emit_param_stores_from_return_wit_2 | 1, 2, 3, 4, 5 | aggressive |
| cmc_emit_param_stores_from_partial_solve_wit_5_pure | 1, 2, 3, 4, 5 | aggressive |
| cmc_emit_param_stores_from_partial_solve_wit_6_pure | 1, 2, 3 | aggressive |
| cmc_emit_param_stores_from_partial_solve_wit_10_pure | 1, 2, 3, 4, 5, 6 | aggressive |
| cmc_emit_param_stores_from_partial_solve_wit_11_pure | 1 | aggressive |
| cmc_emit_param_stores_from_which_implies_wit_1 | none; whole goal provable | LLM |
| cmc_emit_param_stores_from_which_implies_wit_2 | 1 | aggressive |
| cmc_emit_param_stores_from_which_implies_wit_3 | 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12 | aggressive |
| cmc_emit_param_stores_from_which_implies_wit_4 | spatial | aggressive |
| cmc_emit_param_stores_from_which_implies_wit_5 | spatial | aggressive |
| cmc_emit_param_stores_from_which_implies_wit_6 | spatial | aggressive |
| cmc_emit_prologue_partial_solve_wit_5_pure | 1, 2 | aggressive |
| cmc_emit_prologue_partial_solve_wit_6_pure | 1, 2 | aggressive |
| cmc_emit_prologue_partial_solve_wit_7_pure | 1, 2 | aggressive |
| cmc_emit_prologue_partial_solve_wit_8_pure | 1, 2 | aggressive |
| cmc_emit_prologue_partial_solve_wit_9_pure | 1, 2 | aggressive |
| cmc_emit_prologue_partial_solve_wit_10_pure | 1, 2 | aggressive |
| cmc_emit_prologue_partial_solve_wit_11_pure | 1, 2 | aggressive |
| cmc_emit_prologue_partial_solve_wit_12_pure | 1, 2 | aggressive |
| cmc_emit_prologue_partial_solve_wit_13_pure | 1, 2 | aggressive |
| cmc_emit_prologue_partial_solve_wit_14_pure | 1, 2 | aggressive |
| cmc_emit_prologue_partial_solve_wit_15_pure | 1, 2 | aggressive |
| cmc_emit_prologue_partial_solve_wit_16_pure | 1, 2 | aggressive |
| cmc_emit_prologue_partial_solve_wit_17_pure | 1, 2 | aggressive |
| cmc_emit_prologue_partial_solve_wit_18_pure | 1, 2 | aggressive |
| cmc_emit_prologue_partial_solve_wit_20_pure | 1, 2, 3 | aggressive |
| cmc_emit_prologue_which_implies_wit_1 | none; whole goal provable | LLM |
| cmc_emit_prologue_which_implies_wit_2 | 1 | aggressive |
| cmc_emit_prologue_which_implies_wit_3 | spatial | aggressive |
| cmc_emit_prologue_which_implies_wit_4 | 1, 2 | aggressive |
| cmc_emit_prologue_which_implies_wit_5 | spatial | aggressive |
| cmc_emit_prologue_which_implies_wit_6 | spatial | aggressive |
| cmc_emit_function_safety_wit_1 | 1, 2 | aggressive |
| cmc_emit_function_partial_solve_wit_9_pure | 1, 2 | aggressive |
| cmc_emit_function_partial_solve_wit_11_pure | 1, 2 | aggressive |
| cmc_emit_function_which_implies_wit_2 | none; whole goal provable | LLM |
| cmc_emit_function_which_implies_wit_3 | spatial | aggressive |
| cmc_emit_function_which_implies_wit_5 | spatial | aggressive |
| cmc_emit_function_which_implies_wit_6 | spatial | aggressive |
| cmc_emit_function_which_implies_wit_7 | spatial | aggressive |

# Common Proof Patterns

- **OBS**: Existing pure facts are transported through repeated head/tail observations on syntactic cons lists. Compute observations inward-out, then use the original reconstruction equality once; avoid a self-expanding rewrite loop. Pure entailments keep the heap as a frame; standalone Prop targets need no resource operation.
- **SLOT**: The list representation distinguishes null/nil and nonnull/cons. Open a cons with its existing next-pointer existential, or close it with that pointer and unchanged three field cells/tail. The null return's impossible cons case follows from the representation's nonzero fact.
- **TRANS**: Indexed slot well-formedness gives head positivity/scalar type and tail well-formedness by index shift; recursive safety/count predicates yield tail conjuncts. Length, additive list size and snoc equations establish recursive bounds. No assumption about prefix well-formedness is introduced.
- **LAYOUT**: Scalar slots have equal encoded and semantic sizes; lift by list induction. Substitute function/body identities for frame equality. Member safety bounds total size; count representability plus an unconditional length/count inequality bounds parameter length.
- **PARAM-CODE**: Derive param_offset=8+size(prefix) from the full parameter list split and slot=length(prefix), unfold one tail-first emission equation, then reassociate app in the remaining or completed code argument. All emitter resource arguments remain fixed.
- **CONTEXT**: Unfold/fold function context, keeping the five fields and both slot lists; choose the same zp/zl witnesses in the required order. No body AST ownership is created here.
- **PROLOGUE-CODE / FUNCTION-CODE**: Substitute supplied lookup/frame/body/PC equalities, unfold the corresponding emission definition, and normalize only list concatenation. The emitter predicate then cancels; no new resource or existential is needed.
- **OPCODE / EMPTY / BOUNDS**: Compute opcode constants, zero sublists and nil size/length, or project the explicit code-count bound. Introduce the resulting pure fact over the existing heap.

# VC Deltas

Each row below references one pattern; exact per-split deltas and premises are in group_plan.json. These are strategies for the chosen targets only, not whole-parent analyses of aggressive witnesses.

- `proof_of_cmc_emit_param_stores_from_return_wit_1`: SLOT; 1 split target(s); see declaration-ordered split deltas in plan.
- `proof_of_cmc_emit_param_stores_from_return_wit_2`: OBS; 5 split target(s); see declaration-ordered split deltas in plan.
- `proof_of_cmc_emit_param_stores_from_partial_solve_wit_5_pure`: OBS; 5 split target(s); see declaration-ordered split deltas in plan.
- `proof_of_cmc_emit_param_stores_from_partial_solve_wit_6_pure`: OBS; 3 split target(s); see declaration-ordered split deltas in plan.
- `proof_of_cmc_emit_param_stores_from_partial_solve_wit_10_pure`: OBS; 6 split target(s); see declaration-ordered split deltas in plan.
- `proof_of_cmc_emit_param_stores_from_partial_solve_wit_11_pure`: OBS; 1 split target(s); see declaration-ordered split deltas in plan.
- `proof_of_cmc_emit_param_stores_from_which_implies_wit_1`: SLOT; whole opening with existing existential pointers.
- `proof_of_cmc_emit_param_stores_from_which_implies_wit_2`: LAYOUT; 1 split target(s); see declaration-ordered split deltas in plan.
- `proof_of_cmc_emit_param_stores_from_which_implies_wit_3`: TRANS; 12 split target(s); see declaration-ordered split deltas in plan.
- `proof_of_cmc_emit_param_stores_from_which_implies_wit_4`: PARAM-CODE; 1 split target(s); see declaration-ordered split deltas in plan.
- `proof_of_cmc_emit_param_stores_from_which_implies_wit_5`: PARAM-CODE; 1 split target(s); see declaration-ordered split deltas in plan.
- `proof_of_cmc_emit_param_stores_from_which_implies_wit_6`: SLOT; 1 split target(s); see declaration-ordered split deltas in plan.
- `proof_of_cmc_emit_prologue_partial_solve_wit_5_pure`: OPCODE; 2 split target(s); see declaration-ordered split deltas in plan.
- `proof_of_cmc_emit_prologue_partial_solve_wit_6_pure`: OPCODE; 2 split target(s); see declaration-ordered split deltas in plan.
- `proof_of_cmc_emit_prologue_partial_solve_wit_7_pure`: OPCODE; 2 split target(s); see declaration-ordered split deltas in plan.
- `proof_of_cmc_emit_prologue_partial_solve_wit_8_pure`: OPCODE; 2 split target(s); see declaration-ordered split deltas in plan.
- `proof_of_cmc_emit_prologue_partial_solve_wit_9_pure`: OPCODE; 2 split target(s); see declaration-ordered split deltas in plan.
- `proof_of_cmc_emit_prologue_partial_solve_wit_10_pure`: OPCODE; 2 split target(s); see declaration-ordered split deltas in plan.
- `proof_of_cmc_emit_prologue_partial_solve_wit_11_pure`: OPCODE; 2 split target(s); see declaration-ordered split deltas in plan.
- `proof_of_cmc_emit_prologue_partial_solve_wit_12_pure`: OPCODE; 2 split target(s); see declaration-ordered split deltas in plan.
- `proof_of_cmc_emit_prologue_partial_solve_wit_13_pure`: OPCODE; 2 split target(s); see declaration-ordered split deltas in plan.
- `proof_of_cmc_emit_prologue_partial_solve_wit_14_pure`: OPCODE; 2 split target(s); see declaration-ordered split deltas in plan.
- `proof_of_cmc_emit_prologue_partial_solve_wit_15_pure`: OPCODE; 2 split target(s); see declaration-ordered split deltas in plan.
- `proof_of_cmc_emit_prologue_partial_solve_wit_16_pure`: OPCODE; 2 split target(s); see declaration-ordered split deltas in plan.
- `proof_of_cmc_emit_prologue_partial_solve_wit_17_pure`: OPCODE; 2 split target(s); see declaration-ordered split deltas in plan.
- `proof_of_cmc_emit_prologue_partial_solve_wit_18_pure`: OPCODE; 2 split target(s); see declaration-ordered split deltas in plan.
- `proof_of_cmc_emit_prologue_partial_solve_wit_20_pure`: EMPTY; 3 split target(s); see declaration-ordered split deltas in plan.
- `proof_of_cmc_emit_prologue_which_implies_wit_1`: CONTEXT; whole opening with existing existential pointers.
- `proof_of_cmc_emit_prologue_which_implies_wit_2`: LAYOUT; 1 split target(s); see declaration-ordered split deltas in plan.
- `proof_of_cmc_emit_prologue_which_implies_wit_3`: PROLOGUE-CODE; 1 split target(s); see declaration-ordered split deltas in plan.
- `proof_of_cmc_emit_prologue_which_implies_wit_4`: LAYOUT; 2 split target(s); see declaration-ordered split deltas in plan.
- `proof_of_cmc_emit_prologue_which_implies_wit_5`: PROLOGUE-CODE; 1 split target(s); see declaration-ordered split deltas in plan.
- `proof_of_cmc_emit_prologue_which_implies_wit_6`: CONTEXT; 1 split target(s); see declaration-ordered split deltas in plan.
- `proof_of_cmc_emit_function_safety_wit_1`: BOUNDS; 2 split target(s); see declaration-ordered split deltas in plan.
- `proof_of_cmc_emit_function_partial_solve_wit_9_pure`: BOUNDS; 2 split target(s); see declaration-ordered split deltas in plan.
- `proof_of_cmc_emit_function_partial_solve_wit_11_pure`: OPCODE; 2 split target(s); see declaration-ordered split deltas in plan.
- `proof_of_cmc_emit_function_which_implies_wit_2`: CONTEXT; whole opening with existing existential pointers.
- `proof_of_cmc_emit_function_which_implies_wit_3`: CONTEXT; 1 split target(s); see declaration-ordered split deltas in plan.
- `proof_of_cmc_emit_function_which_implies_wit_5`: FUNCTION-CODE; 1 split target(s); see declaration-ordered split deltas in plan.
- `proof_of_cmc_emit_function_which_implies_wit_6`: FUNCTION-CODE; 1 split target(s); see declaration-ordered split deltas in plan.
- `proof_of_cmc_emit_function_which_implies_wit_7`: FUNCTION-CODE; 1 split target(s); see declaration-ordered split deltas in plan.

# Grouping Decisions

Groups were first formed by resource/semantic transformation, then reviewed against witness, split and helper/context load. The arithmetic/semantic groups are separated from opcode projections and observation normalization. No group has more than 6 witnesses; there are no singleton groups. Groups are independent and none requires another group's new helper. Planned public helpers are stable, premise-minimal facts owned by exactly one group; if an adequate established fact exists, workers may discharge the goal without duplicating it under their normal helper workflow.

| Group | Witnesses | Aggressive splits | Difficulty | Expected helper/context load |
|---|---:|---:|---:|---|
| param-transition | 2 | 13 | 4 | 1 public snoc-size fact; indexed slots, scalar encoding, tail safety and arithmetic |
| param-emission | 2 | 2 | 4 | 1 public prefix/append fact; two inverse uses of the same param-offset equation |
| prologue-layout | 3 | 6 | 4 | 1 public length/count fact; semantic/encoded size sums and parameter bounds |
| param-observations | 5 | 20 | 2 | no mandatory helper; 20 syntactically large but shallow observation normalizations |
| param-resources | 3 | 2 | 2 | mixed modes, one list-representation context; null return and open/close |
| function-context | 4 | 2 | 2 | mixed modes, one function representation and reversed existential order |
| prologue-emission | 2 | 2 | 2 | 14-instruction list normalization and frame equality |
| prologue-opcodes-a | 5 | 10 | 1 | no helpers; literal opcode computation, consecutive program phase |
| prologue-opcodes-b | 5 | 10 | 1 | no helpers; literal opcode computation, consecutive program phase |
| prologue-opcodes-c | 4 | 8 | 1 | no helpers; literal opcode computation, consecutive program phase |
| function-bounds | 3 | 6 | 1 | only explicit i32 bounds and constants |
| function-emission | 3 | 3 | 2 | whole-function code equation; three independent app transitions |

Expected critical path: param-transition has 13 splits, one list-size helper family and indexed slot/type arithmetic; param-emission has only 2 splits but one structural prefix induction shared by both unfold/fold directions; prologue-layout has 6 splits, one count/length helper and semantic-size bridges. Their final-result counterparts are already separate: parameter return/observation work is outside transition, prologue emission folding is outside layout, and function emission is outside PC safety. The remaining inverse unfold/fold pairs deliberately stay together because their exact code equation/prefix context is the same. These three heavy groups are listed first and assigned difficulty 4. No comparison-driven high-risk priority requirement applies in this first round.

# Risks or Blockers

No blocker identified. Care is needed with indexed cm_slots_wf (not a structural Forall), total lookup at arbitrary fid, non-well-formed prefixes (the prefix helper must be unconditional), and nested head/tail rewrites. Do not infer termination or compiler preservation from these implementation VCs. Generated auto admissions remain the repository's separate trust boundary; this analysis claims only semantic provability of assigned manual targets.

Checker command calls: 0. Checker command failures: 0. No debug command, temporary Show insertion, formal change, or repair was needed. Controller acceptance and subsequent checked proofs are separate from this analysis.
