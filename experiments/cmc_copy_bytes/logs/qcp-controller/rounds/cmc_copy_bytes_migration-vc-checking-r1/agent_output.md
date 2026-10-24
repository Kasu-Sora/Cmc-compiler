# Outcome

All six generated split goals are provable from their current premises. All four manual top-level witnesses therefore select `aggressive_pre_process`. No whole-goal provability analysis was performed after the structural scan. Three independent groups cover the manual exactly; no new helper declarations are expected.

## Structural Blocker Scan

- Status: passed
- Top-level VCs scanned: 4
- No-split VCs checked first: 0
- Definite blockers: 0

The scan covered the four top-level declarations in the current manual (the seven auto-file obligations are outside the assigned manual witness set). Every required destination segment has the same base address as its antecedent resource; source/full and destination/suffix frames are present where required. Current parameters are already represented by their matching `_pre` values. The loop index supplies the only changing scalar. There are no unmatched existential resources. No definite countermodel was found. No no-split manual goals existed to prioritize.

# Annotation Comparison Review

No comparisons were supplied in this first round. The case-library predicate is exactly `bytes = [] \/ source_pre <> 0`; entry has that premise together with nonzero length and the list-length equation. The loop invariant explicitly retains source nonnullness and all scalar bridges. Thus the predicate's entry and exit facts have actual establishing premises; there is no assumed new mathematical fact.

# Proof-Mode Decisions

The initial split-only pass, in declaration order, recorded the following binary judgements before selecting modes or writing strategies:

| Split declaration | Judgement |
| --- | --- |
| `proof_of_cmc_copy_bytes_entail_wit_1_split_goal_1` | provable |
| `proof_of_cmc_copy_bytes_entail_wit_1_split_goal_spatial` | provable |
| `proof_of_cmc_copy_bytes_entail_wit_2_split_goal_spatial` | provable |
| `proof_of_cmc_copy_bytes_return_wit_1_split_goal_spatial` | provable |
| `proof_of_cmc_copy_bytes_return_wit_2_split_goal_1` | provable |
| `proof_of_cmc_copy_bytes_return_wit_2_split_goal_spatial` | provable |

Each parent has at least one split and all its splits are provable, fixing `aggressive_pre_process` for entail witnesses 1 and 2 and return witnesses 1 and 2. No fallback whole-goal judgement was needed.

# Common Proof Patterns

**Pure consequence:** introduce a pure proposition under the antecedent segment once it follows from the quantified premises; use the case-library predicate's disjunction directly. No new resource or existential witness is needed.

**Segment normalization:** prove equality of destination endpoints and stored lists, rewrite them, and close by identity/cancellation. The formal split targets contain one initialized segment on each side, so no array split/merge or framed resource reconstruction is required. Standard list/sublist facts suffice. These are concrete loop-state transformations, without a separate abstract-state refinement relation.

# VC Deltas

- `proof_of_cmc_copy_bytes_entail_wit_1`: pure-consequence split excludes `bytes=[]` using nonzero length and `Zlength bytes=length_pre`; spatial split uses an empty sublist, append-right identity and addition by zero. This establishes the empty copied-prefix state.
- `proof_of_cmc_copy_bytes_entail_wit_2`: segment normalization changes the copied prefix from `sublist 0 index bytes ++ [Znth index bytes 0]` to `sublist 0 (index+1) bytes`. Bounds come from `0<=index`, the loop guard, and the list-length equation; append associativity and endpoint associativity finish the step.
- `proof_of_cmc_copy_bytes_return_wit_1`: segment normalization first derives an empty byte list from zero length, then removes the empty append and zero endpoint offset.
- `proof_of_cmc_copy_bytes_return_wit_2`: the pure-consequence split chooses the nonnull disjunct already in PreH4. Segment normalization obtains `index=length_pre` from exit guard plus invariant upper bound, then replaces the full-range sublist by `bytes`.

# Grouping Decisions

Strategies were fixed before grouping. The initial partition follows program phase: entry, copied-prefix transition, and returns. A second load/coupling review retains this partition:

| Group | Top-level VCs | Aggressive splits | New helper families | Difficulty |
| --- | ---: | ---: | ---: | ---: |
| `copy-step` | 1 | 1 | 0 | 2 |
| `copy-entry` | 1 | 2 | 0 | 1 |
| `copy-returns` | 2 | 3 | 0 | 1 |

`copy-step` is the likely tail because its one split needs prefix-extension and singleton-sublist normalization. It has one segment, elementary arithmetic, standard list library context, and no case-library modification or helper load. It is placed first. Its singleton grouping is justified by the independent transition route; final-result work is separately provable and explicitly assigned to `copy-returns`.

`copy-entry` is a singleton because it establishes the initial invariant and excludes the empty-list branch of the nonnull predicate; it shares neither the step transformation nor exit guards. Its two splits are lightweight and have no helper coupling to other groups. `copy-returns` combines the two independently reachable final-result branches and remains small. Every group uses the same proof mode and current case predicate, but no persistent context or new lemma requires groups to share output. All groups are below the hard bound of 12. No substantial stable mathematical helper is being rediscovered or deferred to the tail.

# Risks or Blockers

None identified. Exact standard-library lemma names and tactic syntax remain proof-worker implementation details. No manual edits or debug command were needed, and this report makes no claim of having kernel-checked proofs.
