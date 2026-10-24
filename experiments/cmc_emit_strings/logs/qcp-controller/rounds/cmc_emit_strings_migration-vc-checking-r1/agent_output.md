# VC checking decision summary

## Outcome

All three top-level obligations have a viable proof mode. Four generated splits are provable. Two independent groups cover the nonempty-node opening and the final returns. No new helper is planned.

## Structural Blocker Scan

- Status: passed
- Top-level VCs scanned: 3
- No-split VCs checked first: 1
- Definite blockers: 0

The no-split entailment was scanned first. Its needed three node-field resources, source buffer and tail representation are precisely the cons arm of the existing list representation; the nil arm contradicts the node guard. Each return retains the required source array, head fields and tail list or the unchanged null list. Buffer addresses and pre-state scalars coincide on both sides. Existential pointers are supplied by owned resources, and no current-to-@pre equality is missing. The empty source-byte case permits an arbitrary source pointer: it requires only the empty-list arm of the existing buffer-nonnull predicate and an empty full array.

## Annotation Comparison Review

There are no comparisons in this first proving round. The sole assertion is established by entail_wit_1, rather than assumed. Its length equality is definitional, its nonnegative head length follows from list length, its tail facts come from cm_rep_strings_safe, and its source buffer facts come from cm_uint8_buffer. The recursive postcondition supplies the final return equation and tail resources. No new premise is unaccounted for.

## Proof-Mode Decisions

All split judgments were completed before whole-goal analysis and strategy design, in declaration order:

| Generated split | Judgment |
|---|---|
| proof_of_cmc_emit_strings_return_wit_1_split_goal_1 | Provable |
| proof_of_cmc_emit_strings_return_wit_1_split_goal_spatial | Provable |
| proof_of_cmc_emit_strings_return_wit_2_split_goal_1 | Provable |
| proof_of_cmc_emit_strings_return_wit_2_split_goal_spatial | Provable |

Both return parents therefore select aggressive_pre_process; their top-level provability was not separately analyzed. The entailment has no splits, and its whole goal is provable, so it selects LLM_pre_process. No fallback or unprovable split remains.

## Common Proof Patterns

**List shape and buffer boundary.** Destruct the abstract string list. Its nil representation enforces pointer zero, while its cons arm enforces nonzero and owns bytes/length/next fields, cm_uint8_buffer and the tail list. Opening obtains the exact pointers for existential instantiation; folding uses these same pointers. For an empty byte list, cm_uint8_buffer is emp and the full array of length zero is empty; for a nonempty byte list, the representation already supplies the buffer-nonnull fact and full array. No blanket source-pointer nonzero premise is needed.

**Cons size and byte normalization.** Unfold just the cons equations for cm_rep_strings_size, cm_rep_string_size and cm_strings_bytes. Integer associativity identifies the final cursor, and append associativity identifies prefix followed by head bytes, one zero terminator and tail bytes. The initialized segment and undefined suffix then cancel at identical endpoints.

**Null return.** The null pointer rules out a cons list. Nil size and bytes are zero and empty respectively, so arithmetic and app_nil_r recover the original buffer and cursor.

## VC Deltas

- entail_wit_1: List-shape opening, retaining both output-buffer segments as frame. The witnesses are the represented next and bytes pointers plus the actual head/tail. The extra scalar obligations are tail safety/size from the safety conjunction, head length from Zlength and the capacity sum from the original bound.
- return_wit_1_split_goal_1: Cons-size normalization only; the recursive return equation supplies the result, and heap resources remain frame.
- return_wit_1_split_goal_spatial: Cons-byte normalization and list-shape folding. Its retained buffer-nonnull premise restores the nonempty source-buffer branch. Head fields and tail representation rebuild the list without modifying ownership.
- return_wit_2_split_goal_1: Null-return pattern for the pure cursor equality.
- return_wit_2_split_goal_spatial: Null-return pattern for the three restored resources.

## Grouping Decisions

The initial grouping by representation transition and final-result normalization yields two groups. The second load-and-coupling review keeps this boundary:

| Group | Top-level witnesses | Aggressive splits | New helper families | Difficulty |
|---|---:|---:|---:|---:|
| string-node-opening | 1 | 0 | 0 | 2 |
| string-final-return | 2 | 4 | 0 | 2 |

The single-witness opening group is justified by its independent assertion-establishment transition and whole-goal mode. It does not depend on any final-result fact. Final return work is separated from that transition as required; both returns share list-shape and buffer normalization context and remain together. The expected tail is the final-return group, with four small splits, zero new helpers, the existing layout/counts/copy definitions and no heavy mathematical or recursive proof context. Further splitting would isolate two tiny base-case goals without removing a shared helper bottleneck. Both groups can work independently from the frozen libraries. No group exceeds the witness cap, and no cross-group helper or dependency is planned.

## Risks or Blockers

No semantic blocker identified. The empty source-array conversion and heap folding may require careful unfolding and separation-logic normalization, but their premises are present. No specification strengthening, annotation revision, runtime change or new public lemma is required by the plan. These are proofability judgments; controller acceptance and subsequent group proof checks remain separate.
