# vc-checking handoff

This Markdown file, current files under the main root, and the listed skill docs are the source of truth. Do not use unstated parent-chat context.

## Assignment

- Round: `cmc_emit_expr_dispatch_migration-vc-checking-r1`
- Attempt: `cmc_emit_expr_dispatch_migration-vc-checking-r1-attempt-1` (index 1)
- Main root: `/Users/nizitong/QCP/qcp-binary-democases`
- Terminal report: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_expr_dispatch_migration-20261017164114/rounds/cmc_emit_expr_dispatch_migration-vc-checking-r1/agent_report.json`
- Optional human notes: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_expr_dispatch_migration-20261017164114/rounds/cmc_emit_expr_dispatch_migration-vc-checking-r1/agent_output.md`

## Target files

- C: `QCP_examples/QCP_demos_human/cmc_emit_expr_dispatch_migration.c`
- `formal_case_lib` candidate (present under `create` policy; read-only in this phase): `Rocq/examples/QCP_demos_human/cmc_emit_expr_dispatch_migration_lib.v`
- Manual (present; generated/proved artifact, never edit it as annotation source): `Rocq/examples/QCP_demos_human/cmc_emit_expr_dispatch_migration_proof_manual.v`
- Goal/auto/check: `Rocq/examples/QCP_demos_human/cmc_emit_expr_dispatch_migration_goal.v`, `Rocq/examples/QCP_demos_human/cmc_emit_expr_dispatch_migration_proof_auto.v`, `Rocq/examples/QCP_demos_human/cmc_emit_expr_dispatch_migration_goal_check.v`

## Rules to read

- `.agents/skills/verification-orchestrator/SKILL.md`
- `.agents/skills/verification-orchestrator/workflows/state-handoffs-and-reports.md`
- `.agents/skills/verification-orchestrator/workflows/paths-and-commands.md`
- `.agents/skills/vc-checking/SKILL.md`
- `.agents/skills/vc-checking/workflows/vc-analysis-and-grouping.md`

## Previous attempts

- none

Required lessons:

- none

## Controller command execution contract

Run every listed controller command unchanged with its bound cwd. Prefer a direct system-terminal call. If the runtime
exposes terminal tools only through `functions.exec`, use a transparent bridge. Each bridge cell may await exactly one
terminal operation: `tools.exec_command` to launch the command, or `tools.write_stdin` to continue the same live
session (or the runtime-documented normalized name for that same terminal operation), and may only forward its result.
Pass the rendered command/argv, every argument, and cwd unchanged when launching, and preserve the exact session
handle when continuing. A normalized equivalent is permitted only when its input shape accepts those values unchanged;
never serialize an argv array into shell text, reparse a rendered command, or add quoting.

Do not call a second tool in a bridge cell, add JavaScript/Python orchestration, construct, alter, sequence,
parallelize, or interpret commands, wrap them in a generated shell/PowerShell/Python script or another `uv run`, use
`sh -c`, command substitution, a pipeline or background execution, or invoke another wrapper. Never recreate
controller behavior with a custom command or script.

Preserve every outer cell and inner process/session handle until the actual command reaches a terminal exit. If a
transparent bridge yields a running `functions.exec` cell, resume only that cell with `functions.wait` until its one
nested terminal operation returns. Empty output, an initial-yield response, and outer-cell messages such as
`Script completed` do not prove that the controller command finished. Record a check as passed only after the terminal
process exits with code 0 and the controller JSON reports
`status: passed`.


## VC checking inputs

- Group plan output: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_expr_dispatch_migration-20261017164114/rounds/cmc_emit_expr_dispatch_migration-vc-checking-r1/group_plan.json`
- Maximum witnesses per group: 12

The fixed run topology contains `formal_case_lib`, so groups may plan owner-suffixed helpers when needed.

Target witnesses:

- `proof_of_cm_emit_leaf_expr_return_wit_1`; generated split goals: `proof_of_cm_emit_leaf_expr_return_wit_1_split_goal_1`
- `proof_of_cm_emit_leaf_expr_return_wit_2`; generated split goals: `proof_of_cm_emit_leaf_expr_return_wit_2_split_goal_1`
- `proof_of_cm_emit_leaf_expr_return_wit_3`; generated split goals: `proof_of_cm_emit_leaf_expr_return_wit_3_split_goal_1`
- `proof_of_cm_emit_leaf_expr_return_wit_4`; generated split goals: `proof_of_cm_emit_leaf_expr_return_wit_4_split_goal_1`
- `proof_of_cm_emit_leaf_expr_which_implies_wit_1`; generated split goals: none
- `proof_of_cm_emit_leaf_expr_which_implies_wit_2`; generated split goals: none
- `proof_of_cm_emit_leaf_expr_which_implies_wit_3`; generated split goals: `proof_of_cm_emit_leaf_expr_which_implies_wit_3_split_goal_spatial`
- `proof_of_cm_emit_leaf_expr_which_implies_wit_4`; generated split goals: none
- `proof_of_cm_emit_leaf_expr_which_implies_wit_5`; generated split goals: `proof_of_cm_emit_leaf_expr_which_implies_wit_5_split_goal_spatial`
- `proof_of_cm_emit_leaf_expr_which_implies_wit_6`; generated split goals: none
- `proof_of_cm_emit_leaf_expr_which_implies_wit_7`; generated split goals: `proof_of_cm_emit_leaf_expr_which_implies_wit_7_split_goal_spatial`
- `proof_of_cm_emit_leaf_expr_which_implies_wit_8`; generated split goals: none
- `proof_of_cm_emit_leaf_expr_which_implies_wit_9`; generated split goals: `proof_of_cm_emit_leaf_expr_which_implies_wit_9_split_goal_spatial`

## Annotation VC comparisons

- none (first proving round)

Independently check every claimed fact source against the current manual. A comparison marked `provable` is a priority check, not a proof result. Put its current and related VCs in the first, high-risk group when they require a new substantial mathematical lemma. Return an annotation blocker immediately when a current premise has no establishing VC or matching case-lib lemma.

Before exhaustive split analysis, perform one cheap structural scan over every top-level VC, checking no-split goals
first and looking specifically for missing resource addresses, scalar equalities, and current-to-@pre bridges. Record
the exact counts and outcome in the `Structural Blocker Scan` section of `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_expr_dispatch_migration-20261017164114/rounds/cmc_emit_expr_dispatch_migration-vc-checking-r1/agent_output.md`. A definite whole-goal
countermodel may be returned immediately as an annotation/specification/dependency blocker; do not spend time on all
split goals first. If this scan has no definite blocker, then judge every generated split goal across all target VCs,
without analyzing any top-level VC. In this pass, record only whether each split goal is provable; do not yet plan
helpers, proof strategies, or reuse. For a top-level VC with
at least one generated split goal, select `aggressive_pre_process` exactly when all of its split goals are provable; do
not analyze that top-level VC's provability. If any split goal is not provable, or no split goal exists, then judge only
the whole top-level VC's provability and select `LLM_pre_process` when it is provable. If that whole VC is not provable,
report the annotation/specification boundary instead of creating a proving assignment.

After every `proof_mode` is fixed, write the natural-language proof strategy. For
`aggressive_pre_process`, analyze only the split goals; do not write a top-level proof strategy. For
`LLM_pre_process`, analyze only the whole top-level VC. VC checking does not analyze proof reuse. On a retry, the
previous VC-checking reports listed above may be read for context, but the current main-root manual is authoritative.
Only after the strategies are complete, group the top-level VCs by their proof ideas. Never assign a split goal
independently: every split goal follows its parent top-level VC into the same group.

The C, goal, auto, check, and case library are read-only. You may temporarily edit the main-root manual
`Rocq/examples/QCP_demos_human/cmc_emit_expr_dispatch_migration_proof_manual.v` to insert `Show.` while inspecting a goal; do not create a debug script.
Run this command unchanged after each useful edit:

```text
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-debug --run cmc_emit_expr_dispatch_migration-20261017164114 --round cmc_emit_expr_dispatch_migration-vc-checking-r1
```

After this delivery is accepted, the controller deletes that manual and reruns symbolic execution so group workers
receive a clean generated manual.

Form initial groups by invariant, proof pattern, array/frame transformation, refinement
transition, and helper family. Then perform a second load-and-coupling review using top-level witness count, aggressive
split-goal count, expected helper families, proof-mode differences, program phase, and persistent proof context. Prefer
coherent groups of roughly 2--6 witnesses; justify every group above 6 witnesses and every single-witness group in
`/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_expr_dispatch_migration-20261017164114/rounds/cmc_emit_expr_dispatch_migration-vc-checking-r1/agent_output.md`. Heavy aggressive/helper work should not be bundled with many lightweight projection/rewrite/lia
VCs. Explicitly review the expected critical path: for every likely tail group, record split/helper/library/context
load in `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_expr_dispatch_migration-20261017164114/rounds/cmc_emit_expr_dispatch_migration-vc-checking-r1/agent_output.md`, split final-result work from independently provable transition/safety work when helper
ownership permits, and otherwise explain the indivisible helper/context coupling. Plan stable permutation, sum/length,
mask-clear, and similar cross-group facts as annotation-approved or public helpers rather than rediscovering them in a
tail group. Assign each group an integer `estimated_difficulty` from 1 (light) to 5 (heaviest). Groups remain independent and
cannot read sibling outputs. Put every helper expected to be newly proved or modified in this round in the owner group's
plan with an exact Rocq declaration `name`, a short `strategy`, and `visibility` set to `local` or `public`. Mark a
stable mathematical helper useful to other groups as public. The controller promotes only successfully proved
matching public declarations into the run-level append-only candidate pool; workers copy candidates into their own
group_worker_lib and still pass the ordinary controller group validation. This pool is not an imported or active fourth library.

    Keep `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_expr_dispatch_migration-20261017164114/rounds/cmc_emit_expr_dispatch_migration-vc-checking-r1/agent_output.md` as a decision summary. Record proof-mode reasons, grouping and critical-path decisions,
    define each common proof pattern once, and give each VC only a pattern reference plus its actual delta. Do not copy
    this handoff, the JSON schema, controller commands, or identical proof steps into that Markdown. Write
    `group_plan.json`: each group has `id`, `estimated_difficulty`, witness objects with
`name` and `proof_mode`. An aggressive witness has `split_strategies`, mapping each generated split-goal name to its
short strategy in declaration order, and omits `strategy`. An `LLM_pre_process` witness has one whole-goal `strategy`
and omits `split_strategies`. Optional planned
helpers use `{name, strategy, visibility}`. Do not copy controller metadata or an acceptance marker into the plan.
Write the final report: success contains only `status: completed`; a
    blocked result adds one `blocker` with `failure_class`, `kind`, `vcs`, `message`, and `repair_boundary`. Each VC entry has exact `name`, `parent`, and `annotation_location`. Do not
copy controller checks into the report. Its `failure_class` must be exactly one of
`annotation-gap`, `specification-gap`, `dependency-gap`, `plan-defect`, `report-defect`, or
`infrastructure`. The controller routes the first three to annotation and the last three to a same-phase vc-checking
retry; it never infers the repair phase from `kind` or prose.
