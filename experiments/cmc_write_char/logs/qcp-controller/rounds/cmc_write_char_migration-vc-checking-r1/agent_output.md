# Outcome

All three generated split goals are provable. The single parent VC is assigned to one aggressive-preprocessing group; no annotation blocker or new helper is needed.

## Structural Blocker Scan

- Status: passed
- Top-level VCs scanned: 1
- No-split VCs checked first: 0
- Definite blockers: 0

The current manual contains one top-level VC and three associated split declarations. The structural scan found matching current scalar values and local-cell addresses, the prefix and suffix array resources, and no missing current-to-`@pre` bridge. Consequents are pure, with no additional resource or existential demand. No whole-goal countermodel was found. This scan did not perform a whole-goal proof analysis.

## Annotation Comparison Review

There are no comparisons in this first round. The current generated statements include the cursor and capacity preconditions and machine integer bounds explicitly. The imported `cmc_write_word_migration_lib.v` defines `tower_u8 z` as `z mod 256` and supplies the byte-conversion theorem used below. No unsupported annotation premise is needed.

## Proof-Mode Decisions

The complete split-only pass, in declaration order, yielded:

1. `proof_of_cmc_write_char_partial_solve_wit_1_pure_split_goal_1`: provable.
2. `proof_of_cmc_write_char_partial_solve_wit_1_pure_split_goal_2`: provable.
3. `proof_of_cmc_write_char_partial_solve_wit_1_pure_split_goal_3`: provable.

After this complete pass, `proof_of_cmc_write_char_partial_solve_wit_1_pure` was assigned `aggressive_pre_process` because all three splits are provable. Its whole-goal provability was not analyzed and no whole-goal strategy is planned.

## Common Proof Patterns

**Pure byte fact.** Each split has six local scalar cells and the unchanged initialized-prefix/uninitialized-suffix segments in its antecedent. Its consequent contains one pure arithmetic assertion and no spatial resource or existential. Introduce quantified values and assumptions and establish that pure assertion independently of the heap; no cancellation, frame rearrangement, array conversion, or logical-state transition is required. The mathematical facts hold for arbitrary integer `char_value_pre`, so the supplied machine bounds are more than sufficient.

## VC Deltas

All deltas belong to the parent `proof_of_cmc_write_char_partial_solve_wit_1_pure` and use **Pure byte fact**:

- Split 1: unfold `unsigned_last_nbits`. The source `%` is `Z.rem`, as defined by `IntLib.v`. Specialize the existing `tower_machine_rem_byte__byte_encoding` at `k = 0`; simplify division by `256^0 = 1` and the zeroth branch of `tower_encode_byte`. This yields the equality between the C unsigned-cast/remainder expression and `tower_u8 char_value_pre`. The lemma's only premise is `0 <= 0 <= 7`.
- Split 2: unfold `tower_u8`; take the nonnegative component of `Z.mod_pos_bound char_value_pre 256`.
- Split 3: the same modulo-range fact supplies the strict upper bound 256.

These are the detailed strategies for the selected split targets only. There is no proof-reuse analysis.

## Grouping Decisions

`char-byte-conversion` has one top-level witness, three aggressive split goals, difficulty 2, and zero new helpers. Initial grouping follows the scalar byte-conversion pattern at the `cmc_write_byte` call. The second load-and-coupling review confirms a single shared integer/modulo context and a fixed imported dependency, with one modest conversion equality and two lightweight bounds.

The singleton is justified because it is the only target parent VC and represents a single independent conversion route. Splits cannot be assigned independently. This is the only possible tail group: its load is three splits, no helper/library construction, and a small persistent arithmetic context. There is no separately assignable final-result, transition, or safety witness in this manual, and no cross-group mathematical fact to publish. The absent-case-library topology is respected: `helpers` is omitted.

## Risks or Blockers

No blocker. The implementation-specific point is to distinguish `Z.rem` from `Z.modulo`; the imported theorem already covers `Z.rem`. No manual edit or controller debug command was needed. Proving and controller acceptance remain subsequent stages.
