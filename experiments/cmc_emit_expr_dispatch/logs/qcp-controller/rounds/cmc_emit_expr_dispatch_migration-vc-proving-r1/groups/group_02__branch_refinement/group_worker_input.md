# Group worker handoff

Read `.agents/skills/group-worker-proving/SKILL.md`, `.agents/skills/group-worker-proving/workflows/group-worker-proving.md`, and `.agents/skills/group-worker-proving/workflows/commands-and-checks.md` completely. This handoff adds only the current assignment; do not use a parent transcript or sibling output.

## Assignment

- Group: `branch_refinement`; attempt 1; earlier compact attempts 0
- Difficulty hint: 2/5
- Required suffix for every new or adapted helper: `__branch_refinement`


### `proof_of_cm_emit_leaf_expr_which_implies_wit_2` — `LLM_pre_process`

Strategy: Choose one whole-goal disjunct, introduce parameters and preserve a copy of cm_expr_wf. Substitute e = cm_leaf_source_expr leaf and destruct leaf. Kind = 0 rejects String/Sizeof/Getc and leaves CMLeafConst n ty. Instantiate n and ty. Unfold the Const expression well-formedness to cm_integer_type ty; its Char/Int alternatives imply cm_type_code_wf ty by reduction. Preserve the original wf/counts facts, establish constructor and dispatch equalities, and cancel the unchanged emitter plan after constructor substitution. No emitter-state transition occurs.

Prove only the top-level VC, opening with `LLM_pre_process ltac:(...)` and an explicit closer; do not edit its split goals.

Split goals:

  - none generated

### `proof_of_cm_emit_leaf_expr_which_implies_wit_4` — `LLM_pre_process`

Strategy: Choose one whole-goal disjunct and introduce parameters, preserving wf/counts premises. Substitute the source-expression equality and destruct leaf; kind = 1 leaves CMLeafString sid ty. Instantiate sid and ty. The String counts-representable premise contains cm_i32_code_count sid, which supplies 0 <= sid <= INT_MAX after unfolding the bound constant (wf also supplies nonnegativity). Preserve wf/counts and dispatch facts; the constructor equality rewrites the plan to exactly the same resource, which cancels.

Prove only the top-level VC, opening with `LLM_pre_process ltac:(...)` and an explicit closer; do not edit its split goals.

Split goals:

  - none generated

### `proof_of_cm_emit_leaf_expr_which_implies_wit_6` — `LLM_pre_process`

Strategy: Choose one whole-goal disjunct and introduce parameters, preserving wf/counts premises. Substitute e = cm_leaf_source_expr leaf and destruct leaf; kind = 9 leaves CMLeafSizeof asked ty. Instantiate asked and ty. The Sizeof cm_expr_wf conjunction provides cm_type_code_wf asked and cm_type_refs (cm_program_structs p) asked; retain its full original conjunction and counts premise. Constructor equalities establish the leaf identity and make the source/target emitter plans identical for cancellation.

Prove only the top-level VC, opening with `LLM_pre_process ltac:(...)` and an explicit closer; do not edit its split goals.

Split goals:

  - none generated

### `proof_of_cm_emit_leaf_expr_which_implies_wit_8` — `LLM_pre_process`

Strategy: Choose one whole-goal disjunct and introduce parameters. Substitute the source-expression equality and destruct leaf. The three exclusions kind <> 0, <> 1, <> 9 eliminate Const, String and Sizeof, leaving CMLeafGetc ty. Instantiate ty, preserve wf/counts premises and establish both duplicate dispatch facts by reduction. Constructor substitution makes the emitter plan identical, so cancel it. No new bounds or helper are needed.

Prove only the top-level VC, opening with `LLM_pre_process ltac:(...)` and an explicit closer; do not edit its split goals.

Split goals:

  - none generated

## Write boundary

- Editable top-level proof spans: `proof_of_cm_emit_leaf_expr_which_implies_wit_2`, `proof_of_cm_emit_leaf_expr_which_implies_wit_4`, `proof_of_cm_emit_leaf_expr_which_implies_wit_6`, `proof_of_cm_emit_leaf_expr_which_implies_wit_8`.
- Editable aggressive split-goal proof spans: none.
- Protected LLM_pre_process split blocks: none; their tokens remain `Proof. Abort.`.
- In `group_worker_lib`, append only proved suffixed helpers, token-identical sealed helper copies, and needed official imports.
- All declaration statements, other proof tokens, the manual prelude, and the seed library stay protected.

Whitespace, comments, line endings, and the final newline are formatting. The controller compares protected Rocq tokens, declaration ownership, proof mode, and kernel results. For an aggressive top-level proof, follow the worker rule above and use `Goal_apply` for the split lemmas; controller validation deliberately does not inspect that tactic choice.


## Files

- Copied manual: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_expr_dispatch_migration-20261017164114/cmc_emit_expr_dispatch_migration-vc-proving-r1/groups/group_02__branch_refinement/cmc_emit_expr_dispatch_migration_proof_manual.v`
- `group_worker_lib`: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_expr_dispatch_migration-20261017164114/cmc_emit_expr_dispatch_migration-vc-proving-r1/groups/group_02__branch_refinement/cmc_emit_expr_dispatch_migration_lib.v`
- Read-only `formal_case_lib`: `Rocq/examples/QCP_demos_human/cmc_emit_expr_dispatch_migration_lib.v`
- Frozen helper candidates: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_expr_dispatch_migration-20261017164114/cmc_emit_expr_dispatch_migration-vc-proving-r1/public_helper_snapshot.txt` — search by needed helper/predicate names and read only matching declarations; never import this file
- Terminal report: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_expr_dispatch_migration-20261017164114/rounds/cmc_emit_expr_dispatch_migration-vc-proving-r1/groups/group_02__branch_refinement/group_worker_report.json`
- Notes: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_expr_dispatch_migration-20261017164114/rounds/cmc_emit_expr_dispatch_migration-vc-proving-r1/groups/group_02__branch_refinement/group_worker_output.md`. They are optional for ordinary outcomes, but an
  `annotation-gap` blocker requires a non-empty explanation here because the controller preserves this
  exact Markdown as part of the aggregated annotation feedback.
- Previous proving round: none; no reuse note is expected.

The group directory must finish with the copied manual and `group_worker_lib`.

## Planned helpers

- none planned

`local` stays in this group. A proved `public` helper is promoted by the controller for later rounds. Historical token-identical copies may keep their sealed suffix; adaptations use this group's suffix.

## Commands

Run a needed command unchanged with its bound cwd. Prefer a direct system-terminal call. If terminal operations are available only through `functions.exec`, use a transparent cell that awaits exactly one `tools.exec_command` to launch, or one `tools.write_stdin` to continue the same live session (or the runtime-documented normalized equivalent), and only forwards the result. Pass command/argv, every argument, and cwd unchanged when launching; preserve the exact session handle when continuing. Use a normalized equivalent only if its input shape accepts those values unchanged; never serialize argv into shell text, reparse a rendered command, or add quoting. Do not call another tool in the cell, construct, alter, sequence, wrap, pipe, or background commands. Preserve every outer cell and inner process/session handle until terminal exit; if the bridge yields a running cell, resume only that cell with `functions.wait`.

```text
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-debug --run cmc_emit_expr_dispatch_migration-20261017164114 --round cmc_emit_expr_dispatch_migration-vc-proving-r1 --group branch_refinement
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_expr_dispatch_migration-20261017164114 --round cmc_emit_expr_dispatch_migration-vc-proving-r1 --target-kind group-development --group branch_refinement
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_expr_dispatch_migration-20261017164114 --round cmc_emit_expr_dispatch_migration-vc-proving-r1 --target-kind group-check --group branch_refinement
```

Debug script: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_expr_dispatch_migration-20261017164114/_coq_builds/cmc_emit_expr_dispatch_migration-vc-proving-r1/group_02/src/.coq_debug/group_02_branch_refinement.v`. Debug, development, and exact are optional proof feedback. `finalize-delivery` seals the two formal files and immediately runs the single mandatory controller group validation.

## Completion

Do not use raw Coq, Dune, Rocq MCP, `Admitted.`, new assumptions, forbidden lemmas, or the forbidden tactics `entailer!` and the bare alias `pre_process` (both are scanned exactly like a forbidden lemma; calls made inside `LLM_pre_process` and `Goal_apply` are unaffected). Repair a recoverable controller failure in this same worker. At the end, success is exactly `status: completed`; `blocked` adds one complete `blocker`. Do not copy version, diff, check status, or controller output.

If an assigned VC exposes an annotation/specification gap outside this group's write boundary, stop proof-only edits and return `blocked` with `blocker.failure_class` exactly `annotation-gap`. Its `vcs` must list every affected exact sealed-manual `name`, `parent`, and `annotation_location`; `message` explains existing premises and the missing conclusion. The controller validates and schedules from those structured VCs.
