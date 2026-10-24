# Outcome

All nine manual top-level VCs are semantically provable. The plan assigns four whole-goal proofs and five aggressive proofs containing eight split goals. No source or generated proof file was changed; no Rocq debug run was needed. This is a proof plan, not a completed proof check.

## Structural Blocker Scan

- Status: passed
- Top-level VCs scanned: 9
- No-split VCs checked first: 4
- Definite blockers: 0

The four no-split entailment VCs were checked first, then both returns and all three call-precondition VCs. All target node fields have matching addresses; nextp is obtained from the list representation or already present. Current node/data/capacity/cursor values have been normalized to their pre-state values. Branch witnesses can use the original head and tail. The size/cast equalities are backed by the slot-size return specification and the explicit head-size bounds. No missing ownership or scalar bridge was found.

## Annotation Comparison Review

There are no prior comparisons. The entry assertion establishes the structural head/tail facts from cm_global_list_rep, cm_rep_globals_safe and cm_data_globals_wf. The second assertion is established separately by the three branch entailments. Each branch retains all five node fields and the tail predicate. cm_global_wf contains scalarity and initialized-implies-count-zero; the case library supplies encoded/model size equality and initialized/zero byte equations. Thus the byte facts have actual establishing obligations and matching library facts, rather than unsupported premises.

## Proof-Mode Decisions

After the structural scan, the complete split-only pass judged the following in declaration order, before whole-goal analysis or strategy construction:

| Split goal (prefix proof_of_cmc_emit_globals_) | Judgement |
| --- | --- |
| return_wit_1_split_goal_1 | provable |
| return_wit_1_split_goal_spatial | provable |
| return_wit_2_split_goal_1 | provable |
| return_wit_2_split_goal_spatial | provable |
| partial_solve_wit_2_pure_split_goal_1 | provable |
| partial_solve_wit_3_pure_split_goal_1 | provable |
| partial_solve_wit_4_pure_split_goal_1 | provable |
| partial_solve_wit_4_pure_split_goal_2 | provable |

Consequently the parents of all eight split goals use aggressive_pre_process, without a separate parent provability analysis. The four entailment VCs have no generated splits; their whole goals are provable and use LLM_pre_process. Every mode was fixed before helper and group planning.

## Common Proof Patterns

- **L (list shape):** Unfold the descriptor-list predicate once. Nil supplies p=0; cons supplies p<>0 and a next-pointer witness plus five fields and tail. Extract or reconstruct this shape while preserving both buffer segments. Safe-list and well-formed-list conjunctions supply the head/tail pure projections.
- **I (initialized bytes):** Nonzero represented Boolean implies true; well-formedness then gives count=0. The code guard and scalarity distinguish char size 1 from int/pointer size 8. Existing model/representation size and byte lemmas yield the exact writer byte list. The two public helper declarations in the plan package these pure facts, with only premises present in the VCs.
- **C (cast):** The slot-size return is definitionally the head representation size; its 0..1048560 range is inside signed 32-bit range. Eliminate signed_last_nbits using the existing arithmetic library. No new cast lemma is planned.
- **Z (zero bytes):** The zero represented flag implies false. Apply cm_rep_global_size_matches and cm_global_bytes_zero with the supplied nonnegative head size, then rewrite the segment byte list.
- **R (recursive composition):** Cons definitions give additive size and concatenated bytes. Use addition/list associativity and fold the list predicate with the existing nextp; output segments cancel after these rewrites.
- **B (capacity):** Replace head size by the required writer amount and combine the total capacity bound with nonnegative tail size. The result is a pure entailment; stack/heap resources need no reconstruction.

## VC Deltas

Names below omit proof_of_cmc_emit_globals_. The plan holds the precise selected-target strategies.

| VC | Pattern and actual delta |
| --- | --- |
| entail_wit_1 | L: unfold the input representation; obtain head upper bound from total-safe bound and nonnegative tail. |
| entail_wit_2_1 | I+C: initialized char; witnesses are existing head/tail; match one-byte writer output and cancel fields/tail. |
| entail_wit_2_2 | I+C: initialized non-char scalar; match eight-byte tower writer output. |
| entail_wit_2_3 | Z+C: uninitialized branch; match zeros of cast size. |
| return_wit_1 splits | R: pure split is additive return equality; spatial split folds the head and reassociates prefix/head/tail bytes. |
| return_wit_2 splits | L: null pointer rules out cons; nil makes size zero and byte append empty. |
| partial_solve_wit_2_pure split | I+B: char amount 1. |
| partial_solve_wit_3_pure split | I+B: word amount 8. |
| partial_solve_wit_4_pure splits | C+B: first split is cast nonnegativity, second is available capacity. |

## Grouping Decisions

Initial grouping followed the two byte-generation routes and the linked-list representation. A second load/coupling review retained three independent groups:

| Group | Top-level VCs | Aggressive splits | New helpers | Difficulty |
| --- | ---: | ---: | ---: | ---: |
| initialized-emission | 4 | 2 | 2 public pure typed-byte facts | 3 |
| zero-emission | 2 | 2 | 0 | 2 |
| list-structure-and-return | 3 | 4 | 0 | 2 |

The likely tail is initialized-emission: two existential frame-preserving transitions, two small pure capacity splits, and two helpers over scalar type cases, type encoding, fixed byte length and model-size correspondence. Each safety split directly consumes the same typed-size fact as its corresponding transition, so retaining them avoids duplicating helper ownership and context. The helpers are stable pure mathematical facts and are public; no group depends on their outputs in this round. Zero-emission uses only existing size/zero/cast facts and is independently provable.

Final-result work is separated from initialized transitions and their helpers. The list group has four aggressive splits but only one recursive list-fold context and standard addition/append identities, with no new helper family. Entry and both returns share nil/cons representation structure, so their three-witness group is coherent. There are no singleton groups or groups above six witnesses. No permutation, variable-length encoding theorem or new cross-group sum/length family is needed; fixed tower length can be reduced or discharged from its existing library definition.

## Risks or Blockers

No definite annotation, specification or dependency blocker. Expected proof effort is in unfolding list separation assertions and showing code=1 excludes pointers using existing depth/base bounds. Initialized pointer values retain the original pointer-init restriction in cm_global_wf; no premise is weakened. All workers remain independently checkable against the frozen case library and their own planned helpers.
