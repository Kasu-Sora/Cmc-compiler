# VC Checking Decision Summary

## Outcome

All 16 manual top-level witnesses receive aggressive preprocessing after all 32 generated split goals were independently judged provable. The plan has four independent groups; no new helper is needed. This is a feasibility assessment, not a completed proof or controller acceptance.

## Structural Blocker Scan

- Status: passed
- Top-level VCs scanned: 16
- No-split VCs checked first: 0
- Definite blockers: 0

Every manual top-level VC has splits. The cheap scan checked all entry/return pairs before the split-provability pass. All spatial addresses use the same emitter_pre; temporary operations also preserve fn_pre. Scalar instruction parameters use immediate_pre, function_id_pre, ty_pre, offset_pre or temp_pre consistently. The explicit C current-to-@pre assertions result in matching normalized parameters. Every return includes the extended-list budget as a premise. No resource, scalar bridge, or existential witness is missing.

## Annotation Comparison Review

There are no comparisons in this first round. The current case library defines the plan as its total capacity bound conjoined with the resolved-emitter resource. Its proved cm_plan_fragment_capacity lemma supplies both fragment and residual-budget consequences. Entry entailment witnesses establish the assertions used by the resolved callees; their postconditions supply the extended resolved-emitter resource. Return PreH1 (ordinary operations) or PreH9 (temporary operations) retains the asserted residual budget. Temporary function-context resources and the slot/offset facts remain present on the corresponding boundaries.

## Proof-Mode Decisions

The binary pass judged all splits before fixing modes or writing strategies. In the following table, E1, E2 and ES mean the exact suffixes _entail_wit_1_split_goal_1, _entail_wit_1_split_goal_2 and _entail_wit_1_split_goal_spatial; RS means _return_wit_1_split_goal_spatial. Each prefix is proof_of_ followed by the listed function.

| Function | E1 | E2 | ES | RS |
|---|---|---|---|---|
| cm_emit_plan | provable | provable | provable | provable |
| cm_emit_call_plan | provable | provable | provable | provable |
| cm_emit_normalize_plan | provable | provable | provable | provable |
| cm_emit_load_plan | provable | provable | provable | provable |
| cm_emit_store_plan | provable | provable | provable | provable |
| cm_emit_fp_address_plan | provable | provable | provable | provable |
| cm_emit_temp_store_plan | provable | provable | provable | provable |
| cm_emit_temp_load_plan | provable | provable | provable | provable |

Every entail and return witness therefore selects aggressive_pre_process. No whole-goal provability analysis or whole-goal strategy was needed after the structural scan.

## Common Proof Patterns

- P1 (fragment capacity): unfold only the plan wrapper; extract its total-budget pure fact. Apply the existing cm_plan_fragment_capacity first projection, or rewrite lengths and use nonnegative tail length to discharge the pure fragment-capacity split.
- P2 (remaining budget): extract the same fact and rewrite Zlength_app to reassociate the total budget into Zlength (done ++ fragment) + Zlength tail. Singleton fragments additionally use cons/nil lengths.
- P3 (open plan): project away the pure budget and retain the resolved emitter resource unchanged.
- P4 (close plan): introduce the plan's pure budget from the explicit return premise and cancel the unchanged extended resolved-emitter resource.
- F (context frame): for temporary operations, extract the plan pure fact through the function-context separating conjunction; preserve/cancel the opaque context in spatial goals. No array decomposition, underlying emitted-code expansion, or existential construction occurs in any pattern.

These patterns describe only the selected split goals. The emitted-list transition itself is already in the resolved callee's supplied postcondition.

## VC Deltas

Names below use the exact prefix proof_of_ and indicated entail_wit_1 or return_wit_1 suffix.

| Function | Entail delta (P1/P2/P3) | Return delta (P4) |
|---|---|---|
| cm_emit_plan | Singleton TVMInst opcode immediate_pre; opcode premises remain available | Singleton appended to done; budget PreH1 |
| cm_emit_call_plan | Singleton TVMCallOp with resolved function PC, left opaque | Same call singleton; budget PreH1 |
| cm_emit_normalize_plan | Fragment cm_char_normalize_code model_ty; no type case split | Same fragment; budget PreH1 |
| cm_emit_load_plan | Fragment cm_load_code model_ty; no type case split | Same fragment; budget PreH1 |
| cm_emit_store_plan | Fragment cm_store_code model_ty; no type case split | Same fragment; budget PreH1 |
| cm_emit_fp_address_plan | Fragment cm_fp_relative_address_code offset_pre; offset stays opaque | Same fragment; budget PreH1 |
| cm_emit_temp_store_plan | F plus fragment cm_temp_store_code policy p fid temp_pre | F, same fragment; budget PreH9 |
| cm_emit_temp_load_plan | F plus fragment cm_temp_load_code policy p fid temp_pre | F, same fragment; budget PreH9 |

## Grouping Decisions

Initial clusters were singleton instruction budgets, unframed general fragments, typed load/store fragments, and temporary operations carrying a function frame. A second load-and-coupling review retained four groups of four top-level witnesses and eight aggressive splits each:

| Group | Top-level | Splits | New helpers | Difficulty | Context |
|---|---:|---:|---:|---:|---|
| single_instruction | 4 | 8 | 0 | 1 | Two singleton cases |
| general_fragments | 4 | 8 | 0 | 1 | Normalize and frame-relative address lists remain opaque |
| typed_memory | 4 | 8 | 0 | 1 | Load/store lists and type facts remain opaque |
| temp_context | 4 | 8 | 0 | 2 | Two identical function frames; extra pure premises |

All groups use the same already-approved plan definition and capacity lemma. There is no new mathematical helper family, public-helper promotion, or sibling dependency. No group exceeds six witnesses or has a single witness.

Critical path review: temp_context is the likeliest tail solely because extracting a pure fact beneath a separating conjunction adds context handling. Its load is eight splits, zero new helpers, one opaque function frame, and the same existing case-library capacity lemma. Its two return goals are lightweight fold/cancel steps. Splitting them from six entry splits would add a separate tiny group without reducing any heavy helper or library work, so the entry/return pairs remain together. The other groups are balanced at eight shallow splits. No heavy refinement or final-result argument is bundled with them. Stable length facts are already supplied by the approved case library and ListLib.

## Risks or Blockers

No definite annotation, specification, or dependency blocker found. Workers should avoid unfolding resolved-emitter or function-context internals: only the plan wrapper changes. Framed pure extraction is the sole additional tactic-level risk.

No manual edits, coq-debug invocations, or check invocations were needed in this phase; no command failed. C, goal, auto, check, case library and manual remain unchanged.
