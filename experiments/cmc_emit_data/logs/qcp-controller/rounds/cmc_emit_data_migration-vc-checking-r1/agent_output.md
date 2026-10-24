# Outcome

All 4 assigned top-level witnesses have provable generated splits. The plan contains 2 independent groups and 5 split goals. No annotation, specification, or dependency blocker was found. No new helper is planned.

## Structural Blocker Scan

- Status: passed
- Top-level VCs scanned: 4
- No-split VCs checked first: 0
- Definite blockers: 0

All four targets have generated splits. The scan found matching global/string list addresses and buffer addresses at each boundary. The post-zeroes assertion preserves the current-to-@pre pointer and capacity bridges. Helper postconditions supply both cursor equalities used at return and before the strings call. No missing resource or scalar bridge gives a countermodel.

## Annotation Comparison Review

There are no comparisons in this first proving round. The assertion's pure facts are carried from the original function precondition; the post-zeroes buffer is established by the zeroes contract. The globals and strings postconditions establish the cursor equations and preserve list resources. The case library is an import facade with no new mathematical declarations.

## Proof-Mode Decisions

The complete split-only pass judged the following goals provable, in declaration order:

1. `proof_of_cmc_emit_data_entail_wit_1_split_goal_spatial`.
2. `proof_of_cmc_emit_data_return_wit_1_split_goal_1`.
3. `proof_of_cmc_emit_data_return_wit_1_split_goal_spatial`.
4. `proof_of_cmc_emit_data_partial_solve_wit_1_pure_split_goal_1`.
5. `proof_of_cmc_emit_data_partial_solve_wit_3_pure_split_goal_1`.

Consequently all four parents select `aggressive_pre_process`. No whole-goal provability analysis or whole-goal strategy is needed after the structural scan. Strategies and grouping were chosen only after completing these mode decisions.

## Common Proof Patterns

- **Frame normalization:** introduce arguments, normalize definitional list/arithmetic expressions or substitute an explicitly supplied cursor equality, then cancel identical list and array resources modulo separation conjunction permutation. No array split/join or descriptor unfolding is needed.
- **Pure consequence:** introduce arguments and lift reflexivity, an existing equality, or linear arithmetic into a pure assertion over the spatial frame. The frame can remain opaque; there are no existential witnesses.

## VC Deltas

- `proof_of_cmc_emit_data_entail_wit_1`: frame normalization uses only `0 + 8` and `nil ++ zeros 8`; the two list representations remain unchanged.
- `proof_of_cmc_emit_data_return_wit_1`: the pure split projects `PreH2`; frame normalization in the spatial split substitutes `retval_2` via `PreH5`. The nested byte append expressions already agree exactly.
- `proof_of_cmc_emit_data_partial_solve_wit_1_pure`: pure consequence reduces to equality of two empty lists.
- `proof_of_cmc_emit_data_partial_solve_wit_3_pure`: pure consequence uses `PreH7` for the cursor and `PreH11` for nonnegative global size.

## Grouping Decisions

`buffer-composition` owns the post-zeroes transition and final buffer/list restoration: 2 top-level witnesses, 3 aggressive splits, no helpers, difficulty 1. Both use the same opaque buffer/list frame context. `helper-call-pure` independently owns the two call obligations: 2 top-level witnesses, 2 aggressive splits, no helpers, difficulty 1. Both groups are below the 12-witness limit and within the preferred 2–6 range.

The second load-and-coupling review found no heavy mathematical work, library additions, mode differences, or persistent recursive context. The likely longer group is `buffer-composition`, with 3 small splits and only substitution/cancellation load; the independent call-safety obligations are already separated. Further splitting the result and transition would create single-witness groups without a distinct helper family or meaningful critical-path improvement. Neither group reads sibling outputs or needs a cross-group helper.

## Risks or Blockers

None identified. This is a provability assessment; controller group proof checks must still validate the actual proofs. Generated auto results remain within the existing QCP auto trust boundary.
