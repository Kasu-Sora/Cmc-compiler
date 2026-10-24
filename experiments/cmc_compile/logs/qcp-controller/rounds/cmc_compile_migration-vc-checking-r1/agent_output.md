## Outcome

All nine assigned top-level witnesses have a proving route. Six use whole-goal preprocessing; the three return witnesses use their generated spatial split goals. This is a proofability/assignment decision, not a completed Rocq proof or controller acceptance.

## Structural Blocker Scan

- Status: passed
- Top-level VCs scanned: 9
- No-split VCs checked first: 6
- Definite blockers: 0

Scanned entail witnesses 1–6 first, then return witnesses 1–3. All addresses in the conclusions are supplied by the current antecedent, possibly beneath the program/output/emitter representation predicates. Current program/output parameters have already normalized to the same `_pre` variables. Existential output, descriptor and function pointers can be taken from the corresponding owned fields or representation witnesses.

Two apparent missing scalar facts have legitimate sources: the first assertion's capacity upper bounds follow from the owned signed-Int fields; the second assertion's nonzero buffer pointers follow after proving both capacities positive. Code capacity is positive from the model's 11-instruction prelude and the existing counts-representable bound; data capacity is at least 8 from the size equality and nonnegative component sizes. No null-buffer countermodel survives these facts.

## Annotation Comparison Review

No comparisons were supplied for this first round. Current fact sources were checked directly: semantic well-formedness is definitionally the required `cm_wf_program`; its typed projection and the imported readiness theorems establish the entry assertions. `cm_program_context_rep` contains root nonzeroness. `cmc_compile_success_bridge` has exactly the semantic-wf, source-termination and decoding premises needed by the successful postcondition. These are existing library declarations, not new premises assumed by the plan.

## Proof-Mode Decisions

After the structural scan, the complete split-only binary pass, in declaration order, was:

| Split goal | Judgement |
|---|---|
| `proof_of_cmc_compile_return_wit_1_split_goal_spatial` | Provable |
| `proof_of_cmc_compile_return_wit_2_split_goal_spatial` | Provable |
| `proof_of_cmc_compile_return_wit_3_split_goal_spatial` | Provable |

Only then were whole-goal decisions made. Entail witnesses 1–6 have no generated splits; each whole goal is provable and selects `LLM_pre_process`. Return witnesses 1–3 each have one provable split and therefore select `aggressive_pre_process`; no whole-return proofability analysis or strategy is used. The strategies below were fixed after those mode decisions.

## Common Proof Patterns

**Context representation.** Open only the relevant program/output representation, expose its existing witnesses and pure facts, and refold or frame unchanged components. Derive signed scalar bounds from their owned cells when necessary. Reestablish right-hand existential witnesses with the original pointers. This covers entry/context-open and capacity-result packaging.

**Emitter transition.** Preserve the program/data frame. Empty raw code initializes the resolved emitter; an exhausted plan drops just its pure budget; patched emitter resources expose the final concrete opcode/immediate buffers. The two planned public length facts prove the exact code-count equality from the existing function-length theorem and the fixed prelude. They require no new well-formedness premise.

**Prefix result.** Obtain the initialized list's length from the spatial array itself. Convert zero-based initialized/undefined segments to the public prefix-buffer representation using the existing empty-segment, full-array and shifted-undefined-segment identities. Split the zero-length branch explicitly. The three planned public helpers differ only by array type and element width. Preserve all output field values and add the semantic simulation fact through the already proved success bridge.

## VC Deltas

| Witness | Pattern and actual delta |
|---|---|
| `proof_of_cmc_compile_entail_wit_1` | Context representation: expose old output values; derive data/code readiness from semantic wf and upper capacity bounds from Int resources. |
| `proof_of_cmc_compile_entail_wit_2` | Context representation: guarded positive capacities expose nonzero pointers; insert the three empty initialized segments. |
| `proof_of_cmc_compile_entail_wit_3` | Emitter transition: raw prefix is empty; the todo budget is the complete model code and needs the planned length equality. |
| `proof_of_cmc_compile_entail_wit_4` | Emitter transition: normalize `[] ++ code`; retain the resolved representation while dropping the plan budget. |
| `proof_of_cmc_compile_entail_wit_5` | Context representation: expose structs/globals/strings and the five program fields before data emission; emitter is framed intact. |
| `proof_of_cmc_compile_entail_wit_6` | Emitter transition: expose final ops/imms; recover model pc from list length, refold program context, and normalize emitted data bytes and endpoint. |
| `proof_of_cmc_compile_return_wit_1` split | Prefix result: pack three final buffers, use entry 0, and discharge the universal semantic guarantee by `cmc_compile_success_bridge`. |
| `proof_of_cmc_compile_return_wit_2` split | Context representation: select data overflow; retain undefined buffers and entry -1. |
| `proof_of_cmc_compile_return_wit_3` split | Context representation: select code overflow; retain undefined buffers and entry -1. |

## Grouping Decisions

The initial proof-family grouping was reviewed for load, stage, preprocessing mode, shared helper ownership and persistent context. Final groups are:

| Group | Top-level / aggressive splits | New helpers | Difficulty | Coupling and critical path |
|---|---:|---:|---:|---|
| `entry_context` | 3 / 0 | 0 | 3 | Entry readiness, positive-buffer opening and program-context opening share representation and readiness context. The context-only witness 5 is light. |
| `emitter_transitions` | 3 / 0 | 2 public | 3 | Witnesses 3 and 6 share the exact model-length helper; witness 4 is a light adjacent plan projection. No final-result work is bundled here. |
| `success_result` | 1 / 1 | 3 public | 3 | Independent final-result boundary with three typed buffer conversions and the existing semantic bridge. The single witness is justified by this distinct helper family and output-contract context. |
| `capacity_returns` | 2 / 2 | 0 | 1 | Both spatial goals use the same output-capacity representation and differ only in overflow side. |

Likely tails are `success_result` and `emitter_transitions`. The former has one split and three small array-transport helpers; its library/context load is array identities plus the existing success theorem. The latter has no splits, a two-lemma length family, emitter representation unfolding, and program-context reassembly. Splitting the final result from emitter transitions is possible because `seg_Zlength` supplies final-buffer lengths directly; no group reads sibling outputs or waits for newly promoted helpers. The model-length family is planned as public for future use instead of being rediscovered by a tail group. There are no groups above six witnesses and no new substantial semantic-preservation theorem.

## Risks or Blockers

No annotation/specification/dependency blocker was found. The main implementation details to check during proving are separation-logic framing around spatial range extraction, normalization of generated emitter field notation, and typed element widths in suffix shifts. These are proof-engineering obligations with existing premises, not reasons to modify annotation or specifications. No formal source or manual proof was edited, and no debug command was needed.
