# Outcome

All three manual top-level witnesses are assigned. All three generated spatial split goals are provable; every witness uses `aggressive_pre_process`. This is an analysis result, not a completed Rocq proof or controller acceptance.

## Structural Blocker Scan

- Status: passed
- Top-level VCs scanned: 3
- No-split VCs checked first: 0
- Definite blockers: 0

Every target has one spatial split. The initialized, stepped, and returned arrays use the same `data_pre` address and start 0. The invariant explicitly preserves data, capacity, cursor, and count against their entry values; generated goals already use their corresponding pre variables. The exit carries `index = count_pre`. No existential resource or scalar bridge is missing. The auto file contains the five safety witnesses and one partial-solve witness; these are outside the three manual targets.

# Annotation Comparison Review

No comparisons were supplied in this first proving round. The current manual/goal pair agrees on all six declarations. The nonnegativity premise required for the step identity is explicitly `PreH2 : 0 <= index`; exit substitution is `PreH1 : index = count_pre`. The case library currently contains imports only, so the new pure zero-list identity is assigned explicitly below rather than assumed available as a case lemma.

# Proof-Mode Decisions

The split-only binary pass, in manual declaration order, found:

1. `proof_of_cmc_write_zeroes_entail_wit_1_split_goal_spatial`: provable.
2. `proof_of_cmc_write_zeroes_entail_wit_2_split_goal_spatial`: provable.
3. `proof_of_cmc_write_zeroes_return_wit_1_split_goal_spatial`: provable.

All modes were fixed to `aggressive_pre_process` after that pass. No whole-goal provability analysis was needed, and the strategies below apply only to the split goals.

# Common Proof Patterns

**R — Normalize one segment and use reflexivity.** Each split has exactly one `UCharArray.seg` on each side, at `data_pre` and with start 0. Identify its endpoint and content list by equality, then use entailment reflexivity/cancellation. There is no existential instantiation, frame reconstruction, segment split/merge, or abstract-state refinement in these formal targets. The undefined tail has already been removed by the generated split and is not an additional obligation here.

**Z — Zero-list extension.** For nonnegative integer n, prove `zeros (n + 1) = zeros n ++ [0]`. The planned public declaration `zeros_snoc__zero_step` has precisely this premise and conclusion. Reduce the zero-list definition to its natural-length representation and use the constant-list append identity, by standard list laws or induction. This is a small pure mathematical lemma, not a new invariant assumption.

# VC Deltas

- `proof_of_cmc_write_zeroes_entail_wit_1`: R; reduce `zeros 0`, remove append-nil, and normalize addition by zero. Existing bounds are unnecessary for this split.
- `proof_of_cmc_write_zeroes_entail_wit_2`: R + Z; apply Z using `PreH2`, reassociate list append, and normalize the integer endpoint. Guard, upper bounds, and capacity facts are not needed for this spatial equality.
- `proof_of_cmc_write_zeroes_return_wit_1`: R; substitute `PreH1` into the endpoint and zero-list length. No helper is needed.

# Grouping Decisions

Initial grouping separated the zero-list successor transformation from the two boundary normalization goals. The load-and-coupling review retains these two groups:

- `zero_step`: one top-level witness, one aggressive split, one public helper, difficulty 2. The singleton is justified by its distinct zero-list extension helper family and transition phase. It is the likely critical path, but its load is only one elementary list identity and one segment equality. It contains no independent final-result or safety work. Its persistent context is integer nonnegativity and zero-list/list append laws; no sibling library is needed.
- `boundary_rewrites`: two top-level witnesses, two aggressive splits, no helpers, difficulty 1. Initialization and final result share only the lightweight R pattern and require no transition helper. They are grouped to avoid separate trivial singleton tasks and remain independent of `zero_step`.

The independent final-result work is therefore outside the likely tail group. No group exceeds the hard limit of 12 witnesses or the usual upper size of six. There are no comparison-driven high-risk groups or substantial mathematical lemmas. The stable zero-list extension identity is public so it can be promoted after successful owner validation, but this round has no cross-group helper dependency.

# Risks or Blockers

No annotation, specification, or dependency blocker found. A worker must check the concrete imported zero-list definition and discharge the stated successor identity; this is ordinary proof implementation work, not a missing premise. No source or generated formal file was edited, and no debug check was needed.
