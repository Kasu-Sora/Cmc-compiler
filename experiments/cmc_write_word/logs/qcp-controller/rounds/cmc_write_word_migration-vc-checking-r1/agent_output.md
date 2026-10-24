# Outcome

All 15 assigned top-level VCs have provable generated splits. Plan: four independent groups, 45 split obligations, all aggressive_pre_process. This is a proofability assessment; proofs and controller acceptance remain separate.

## Structural Blocker Scan

- Status: passed
- Top-level VCs scanned: 15
- No-split VCs checked first: 0
- Definite blockers: 0

The cheap scan covered all six entailments, the return, and eight partial-solve pure VCs before split analysis. Every target has splits. Array addresses consistently use data_pre; cursor/capacity/word_value bridges have already been substituted by symbolic execution. The intermediate assertions preserve all eight byte equalities. The return resource has the required address and all eight appended bytes. No missing resource, scalar bridge, or existential witness was found.

# Annotation Comparison Review

No comparisons were supplied in this first round. The first assertion establishes the machine-to-model byte equalities in entail_wit_1; subsequent assertions carry them through entail_wit_2 through entail_wit_6. Each cmc_write_byte result supplies exactly the next prefix segment and undefined suffix. The case library defines floor-division-based encoding and introduces no assumed byte-equivalence lemma. The necessary bridge is therefore genuine new mathematical work, not a missing annotation premise.

# Proof-Mode Decisions

First pass, in manual declaration order: every listed split was judged provable before any mode or detailed strategy was fixed. The table records the complete split judgement set; split suffixes are relative to the exact parent name.

| Parent | Split suffixes (each provable) | Mode |
|---|---|---|
| proof_of_cmc_write_word_entail_wit_1 | _split_goal_1, _split_goal_2, _split_goal_3, _split_goal_4, _split_goal_5, _split_goal_6, _split_goal_7, _split_goal_8, _split_goal_spatial | aggressive_pre_process |
| proof_of_cmc_write_word_entail_wit_2 | _split_goal_spatial | aggressive_pre_process |
| proof_of_cmc_write_word_entail_wit_3 | _split_goal_spatial | aggressive_pre_process |
| proof_of_cmc_write_word_entail_wit_4 | _split_goal_spatial | aggressive_pre_process |
| proof_of_cmc_write_word_entail_wit_5 | _split_goal_spatial | aggressive_pre_process |
| proof_of_cmc_write_word_entail_wit_6 | _split_goal_spatial | aggressive_pre_process |
| proof_of_cmc_write_word_return_wit_1 | _split_goal_spatial | aggressive_pre_process |
| proof_of_cmc_write_word_partial_solve_wit_1_pure | _split_goal_1, _split_goal_2, _split_goal_3 | aggressive_pre_process |
| proof_of_cmc_write_word_partial_solve_wit_2_pure | _split_goal_1, _split_goal_2, _split_goal_3 | aggressive_pre_process |
| proof_of_cmc_write_word_partial_solve_wit_3_pure | _split_goal_1, _split_goal_2, _split_goal_3, _split_goal_4 | aggressive_pre_process |
| proof_of_cmc_write_word_partial_solve_wit_4_pure | _split_goal_1, _split_goal_2, _split_goal_3, _split_goal_4 | aggressive_pre_process |
| proof_of_cmc_write_word_partial_solve_wit_5_pure | _split_goal_1, _split_goal_2, _split_goal_3, _split_goal_4 | aggressive_pre_process |
| proof_of_cmc_write_word_partial_solve_wit_6_pure | _split_goal_1, _split_goal_2, _split_goal_3, _split_goal_4 | aggressive_pre_process |
| proof_of_cmc_write_word_partial_solve_wit_7_pure | _split_goal_1, _split_goal_2, _split_goal_3, _split_goal_4 | aggressive_pre_process |
| proof_of_cmc_write_word_partial_solve_wit_8_pure | _split_goal_1, _split_goal_2, _split_goal_3, _split_goal_4 | aggressive_pre_process |

All parents have at least one split and all their splits are provable, so the prescribed rule fixes every mode to aggressive_pre_process. No whole-goal provability fallback or whole-goal proof strategy was used.

# Common Proof Patterns

- **E — byte encoding.** The antecedent contains either a prefix segment or that segment, the undefined suffix, and local scalar cells. The conclusion is a pure equality, with no existential or target heap resource. For any integer z, truncation modulo 2^64 preserves each of the low eight base-256 digits. Establish the two public helpers in byte_encoding, including negative z. Wrapped values are nonnegative, so the implementation quotient is Euclidean division. The finite index discharges all power/positivity premises. Introduce the resulting pure equality independently of the heap.
- **B — byte bounds.** The conclusion is a pure lower or upper bound. For later calls, first rewrite b_k by the explicit model equality in the context. Unfold the fixed branch of tower_encode_byte and tower_u8; the needed bound is a projection of Z.mod_pos_bound with positive divisor 256. No heap facts, signed-range assumptions, existentials, or refinement state are required.
- **S — segment index normalization.** Both sides own the same UCharArray.seg with the same contents and address. Normalize (cursor_pre + i) + 1 to cursor_pre + (i+1), then reflexivity/cancellation closes the goal. No split or merge of memory is required.
- **R — final list normalization.** Normalize the final index, unfold tower_word_bytes, and reassociate the eight singleton appends into the specified byte list. The resulting segment is identical. This is list algebra over an existing segment, with no new cell ownership or existential.

# VC Deltas

- `proof_of_cmc_write_word_entail_wit_1`: E for split 1..8 at byte indices 7,6,5,4,3,2,1,0 respectively; S for spatial at index 2. Unlike initial call VCs, this context has no signed-word bounds, so E must hold for arbitrary Z.
- `proof_of_cmc_write_word_entail_wit_2`: S only, index 3, prefix now contains bytes 0..2.
- `proof_of_cmc_write_word_entail_wit_3`: S only, index 4, prefix now contains bytes 0..3.
- `proof_of_cmc_write_word_entail_wit_4`: S only, index 5, prefix now contains bytes 0..4.
- `proof_of_cmc_write_word_entail_wit_5`: S only, index 6, prefix now contains bytes 0..5.
- `proof_of_cmc_write_word_entail_wit_6`: S only, index 7, prefix now contains bytes 0..6.
- `proof_of_cmc_write_word_return_wit_1`: R only, final index 8 and eight singleton appends.
- `proof_of_cmc_write_word_partial_solve_wit_1_pure`: E at byte 0 for split 1; B lower/upper for splits 2/3.
- `proof_of_cmc_write_word_partial_solve_wit_2_pure`: E at byte 1 for split 1; B lower/upper for splits 2/3.
- `proof_of_cmc_write_word_partial_solve_wit_3_pure`: B at byte 2, using PreH11; splits 1/4 are lower bounds and 2/3 upper bounds. Prefix length is cursor_pre + 2.
- `proof_of_cmc_write_word_partial_solve_wit_4_pure`: B at byte 3, using PreH12; splits 1/4 are lower bounds and 2/3 upper bounds. Prefix length is cursor_pre + 3.
- `proof_of_cmc_write_word_partial_solve_wit_5_pure`: B at byte 4, using PreH13; splits 1/4 are lower bounds and 2/3 upper bounds. Prefix length is cursor_pre + 4.
- `proof_of_cmc_write_word_partial_solve_wit_6_pure`: B at byte 5, using PreH14; splits 1/4 are lower bounds and 2/3 upper bounds. Prefix length is cursor_pre + 5.
- `proof_of_cmc_write_word_partial_solve_wit_7_pure`: B at byte 6, using PreH15; splits 1/4 are lower bounds and 2/3 upper bounds. Prefix length is cursor_pre + 6.
- `proof_of_cmc_write_word_partial_solve_wit_8_pure`: B at byte 7, using PreH16; splits 1/4 are lower bounds and 2/3 upper bounds. Prefix length is cursor_pre + 7.

# Grouping Decisions

| Group | Top-level | Aggressive splits | New helpers | Difficulty |
|---|---:|---:|---:|---:|
| byte_encoding | 3 | 15 | 2 public | 5 |
| segment_transitions | 5 | 5 | 0 | 1 |
| byte_bounds | 6 | 24 | 0 | 2 |
| final_result | 1 | 1 | 0 | 1 |

Initial grouping followed encoding semantics, segment transition normalization, scalar byte bounds, and final list assembly. The second load/coupling review retained these boundaries: byte_encoding is the likely critical path because of its modular-division helper family and arbitrary-integer context. The two early call VCs share exactly that helper family, so retaining them avoids independent rediscovery; only four trivial bound splits accompany the ten encoding equalities and one spatial split. All stable new arithmetic helpers are public. The other groups require no sibling output.

byte_bounds has 24 splits but only 12 distinct scalar inequalities, all direct modulo bounds under existing equalities; it has no helper or library-development load and is not expected to be a tail group. segment_transitions has five identical arithmetic normalizations with different offsets. All groups have a single proof mode. Final-result work is deliberately separate from encoding and safety: its one-witness group is justified by an independent final list-normalization route, with no shared new helper or persistent arithmetic context. There are no groups above six witnesses.

# Risks or Blockers

No annotation/specification/dependency blocker was found. The only substantial implementation risk is translating modulo/division identities into the available Rocq lemmas, especially quot versus floor division and negative input words. The planned generic bridge explicitly handles these cases. No temporary manual edit or coq-debug run was needed; C, formal files, and library remain unchanged.
