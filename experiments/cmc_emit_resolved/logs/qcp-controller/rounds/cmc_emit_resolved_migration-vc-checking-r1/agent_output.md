## Outcome

All 16 target witnesses have a provable selected target. The plan contains four independent groups and no new helper declarations. This is a provability assessment, not completed Rocq proofs.

## Structural Blocker Scan

- Status: passed
- Top-level VCs scanned: 16
- No-split VCs checked first: 8
- Definite blockers: 0

Checked all eight entry entailments before the eight return top-level statements. Every emitter address is the same emitter_pre on both sides; temporary routes also retain fn_pre, temp_pre, body, and next. Scalar premises occur explicitly in the antecedent quantifiers. The raw-prefix existential and its patch equality come from cm_resolved_emitter_rep. Return witnesses receive the same patch equality from the assertion. No missing resource address or current-to-@pre bridge was found.

## Annotation Comparison Review

No comparisons were supplied (first round). Independently checked the current manual declarations against the generated goal definitions. The case library defines the resolved predicate by an existential raw prefix and exports the core plan predicate, which adds only Zlength done + Zlength todo <= capacity to the unchanged emitter representation. Existing cm_patch_code_length, cm_patch_code_append, and all eight route patch lemmas establish the mathematical facts used below. No premise needs a new establishing VC.

## Proof-Mode Decisions

The split-only pass judged each of the eight generated split_goal_spatial goals provable, in manual declaration order: generic instruction, call, normalize, load, store, fp_address, temp_store, temp_load. All eight parent return witnesses therefore select aggressive_pre_process; their whole-goal provability was not analyzed beyond the preceding structural scan. Subsequently, each no-split entry entailment was judged provable as a whole and selects LLM_pre_process. Detailed strategies were formulated only after these modes were fixed.

## Common Proof Patterns

- E (entry): choose the left whole-goal disjunct, expose the raw-prefix existential in cm_resolved_emitter_rep, instantiate the right existential with that prefix, and preserve the identical cm_emitter_rep. Unfold cm_emitter_plan_rep only; convert the supplied resolved-prefix capacity bound to a raw-prefix bound with cm_patch_code_length. Reintroduce supplied pure facts and cancel the identical spatial predicate.
- R (return split): unfold the empty-tail plan and resolved representation, instantiate the raw existential with raw_prefix ++ emitted_code, use cm_patch_code_append and the route patch lemma plus the incoming prefix equality, and cancel the unchanged emitter representation. There is no physical CALL patching or array update in this logical conversion.
- F (frame modifier): preserve cm_function_context_rep opaquely under separating conjunction. Entry pure conditions are supplied directly; return split goals contain only the framed spatial conversion.

## VC Deltas

Each row covers exact names proof_of_cm_emit_resolved<suffix>_entail_wit_1 (E) and proof_of_cm_emit_resolved<suffix>_return_wit_1 (R), with R applying only to its _split_goal_spatial target.

| Suffix | Entry delta | Return split delta |
|---|---|---|
| empty | E; singleton length 1, opcode equality and non-CALL premise | R; cm_patch_noncall with PreH2 |
| _call | E; singleton length 1, CALL opcode equality by reflexivity | R; cm_patch_call changes the logical operand to cm_function_pc |
| _normalize | E; app_nil_r and given type facts | R; cm_patch_char_normalize |
| _load | E; app_nil_r and given type facts | R; cm_patch_load |
| _store | E; app_nil_r and given type facts | R; cm_patch_store |
| _fp_address | E; app_nil_r, offset_pre retained | R; cm_patch_fp_address |
| _temp_store | E+F; app_nil_r, PreH1–PreH8 retained | R+F; cm_patch_temp_store and PreH17 prefix equation |
| _temp_load | E+F; app_nil_r, PreH1–PreH8 retained | R+F; cm_patch_temp_load and PreH17 prefix equation |

## Grouping Decisions

Initial route families were single instructions, type-dependent code, frame-pointer address code, and framed temporary code. The second load-and-coupling review separates entry transitions from independently provable final results and keeps opaque function-context framing separate:

| Group | Top-level witnesses | Aggressive splits | New helpers | Difficulty | Context/load |
|---|---:|---:|---:|---:|---|
| entry_unframed | 6 | 0 | 0 | 1 | E; one length lemma and direct premises |
| return_unframed | 6 | 6 | 0 | 2 | R; append plus six existing route rewrite lemmas |
| entry_framed | 2 | 0 | 0 | 2 | E+F; extra pure premises, opaque frame |
| return_framed | 2 | 2 | 0 | 2 | R+F; two existing temporary-code patch lemmas |

Expected tail candidates are return_unframed (six short spatial splits, no helpers, only existing patch-library context) and return_framed (two short splits, no helpers, opaque function context). Their entry transitions are assigned independently. Neither tail requires substantial mathematical or array work; the six return splits share only the established append/patch pattern. No group exceeds six witnesses or has one witness. All groups are independent and require no sibling outputs. Stable length and append facts already exist in the annotation-approved library, so no duplicate public or local helper is planned.

## Risks or Blockers

No annotation, specification, or dependency blocker was found. Framing and existential/pure assertion normalization are the only tactic-level details left to workers. No manual edits, Show insertions, coq-debug invocations, controller validation/check invocations, or failed commands occurred in this phase. Inspection used current generated declarations and read-only predicate/lemma definitions; controller acceptance remains separate.
