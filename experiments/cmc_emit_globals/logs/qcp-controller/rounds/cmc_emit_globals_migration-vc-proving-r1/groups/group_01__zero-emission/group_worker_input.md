# Group worker handoff

Read `.agents/skills/group-worker-proving/SKILL.md`, `.agents/skills/group-worker-proving/workflows/group-worker-proving.md`, and `.agents/skills/group-worker-proving/workflows/commands-and-checks.md` completely. This handoff adds only the current assignment; do not use a parent transcript or sibling output.

## Assignment

- Group: `zero-emission`; attempt 1; earlier compact attempts 0
- Difficulty hint: 2/5
- Required suffix for every new or adapted helper: `__zero_emission`


### `proof_of_cmc_emit_globals_entail_wit_2_3` — `LLM_pre_process`

Strategy: Choose the full-resource left disjunct and instantiate head_2=head, tail=tail_2. The slot-size return equality identifies retval with cm_rep_global_size head; bounds 0..1048560 eliminate signed_last_nbits retval 32. Decode cm_rep_bool(has_init)=0 to has_init=false. Apply cm_rep_global_size_matches using PreH8, then cm_global_bytes_zero using this flag and the nonnegative size PreH11, to rewrite global bytes as zeros of the cast size. Cancel unchanged five fields, tail list, defined buffer prefix and undefined suffix; copy all pure facts. This converts the zero-writer result to the recursive-call assertion.

Prove only the top-level VC, opening with `LLM_pre_process ltac:(...)` and an explicit closer; do not edit its split goals.

Split goals:

  - none generated

### `proof_of_cmc_emit_globals_partial_solve_wit_4_pure` — `aggressive_pre_process`

Prove every listed split goal first, each opening with `LLM_pre_process ltac:(...)` and an explicit closer. Then prove the top-level VC with `aggressive_pre_process` and close each resulting branch with only `Goal_apply <split-goal lemma>` for the corresponding split goal, with no other tactic in the top-level proof. This is a worker proof rule; controller validation does not inspect the spelling of these applications.

Split goals:

  - `proof_of_cmc_emit_globals_partial_solve_wit_4_pure_split_goal_1`: Identify retval with cm_rep_global_size head using PreH17 and the definition. Its bounds PreH27/PreH28 place it in signed 32-bit range, so eliminate signed_last_nbits retval 32 and use PreH27. Introduce the resulting pure nonnegativity assertion from the arbitrary stack/field/list/buffer antecedent; no existential or spatial transformation. Use the existing signed-cast range lemma or int_auto, without a new helper.
  - `proof_of_cmc_emit_globals_partial_solve_wit_4_pure_split_goal_2`: Normalize the cast using PreH17 and head-size bounds PreH27/PreH28 as in the preceding split. Combine total capacity bound PreH30 with nonnegative tail size PreH29 by lia to prove cursor_pre+size<=capacity_pre. The goal is pure, so stack, node, tail and buffer resources require no reconstruction.

## Write boundary

- Editable top-level proof spans: `proof_of_cmc_emit_globals_entail_wit_2_3`, `proof_of_cmc_emit_globals_partial_solve_wit_4_pure`.
- Editable aggressive split-goal proof spans: `proof_of_cmc_emit_globals_partial_solve_wit_4_pure_split_goal_1`, `proof_of_cmc_emit_globals_partial_solve_wit_4_pure_split_goal_2`.
- Protected LLM_pre_process split blocks: none; their tokens remain `Proof. Abort.`.
- In `group_worker_lib`, append only proved suffixed helpers, token-identical sealed helper copies, and needed official imports.
- All declaration statements, other proof tokens, the manual prelude, and the seed library stay protected.

Whitespace, comments, line endings, and the final newline are formatting. The controller compares protected Rocq tokens, declaration ownership, proof mode, and kernel results. For an aggressive top-level proof, follow the worker rule above and use `Goal_apply` for the split lemmas; controller validation deliberately does not inspect that tactic choice.


## Files

- Copied manual: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_globals_migration-20261016102210/cmc_emit_globals_migration-vc-proving-r1/groups/group_01__zero-emission/cmc_emit_globals_migration_proof_manual.v`
- `group_worker_lib`: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_globals_migration-20261016102210/cmc_emit_globals_migration-vc-proving-r1/groups/group_01__zero-emission/cmc_emit_globals_migration_lib.v`
- Read-only `formal_case_lib`: `Rocq/examples/QCP_demos_human/cmc_emit_globals_migration_lib.v`
- Frozen helper candidates: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_globals_migration-20261016102210/cmc_emit_globals_migration-vc-proving-r1/public_helper_snapshot.txt` — search by needed helper/predicate names and read only matching declarations; never import this file
- Terminal report: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_globals_migration-20261016102210/rounds/cmc_emit_globals_migration-vc-proving-r1/groups/group_01__zero-emission/group_worker_report.json`
- Notes: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_globals_migration-20261016102210/rounds/cmc_emit_globals_migration-vc-proving-r1/groups/group_01__zero-emission/group_worker_output.md`. They are optional for ordinary outcomes, but an
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
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-debug --run cmc_emit_globals_migration-20261016102210 --round cmc_emit_globals_migration-vc-proving-r1 --group zero-emission
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_globals_migration-20261016102210 --round cmc_emit_globals_migration-vc-proving-r1 --target-kind group-development --group zero-emission
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_globals_migration-20261016102210 --round cmc_emit_globals_migration-vc-proving-r1 --target-kind group-check --group zero-emission
```

Debug script: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_globals_migration-20261016102210/_coq_builds/cmc_emit_globals_migration-vc-proving-r1/group_01/src/.coq_debug/group_01_zero_emission.v`. Debug, development, and exact are optional proof feedback. `finalize-delivery` seals the two formal files and immediately runs the single mandatory controller group validation.

## Completion

Do not use raw Coq, Dune, Rocq MCP, `Admitted.`, new assumptions, forbidden lemmas, or the forbidden tactics `entailer!` and the bare alias `pre_process` (both are scanned exactly like a forbidden lemma; calls made inside `LLM_pre_process` and `Goal_apply` are unaffected). Repair a recoverable controller failure in this same worker. At the end, success is exactly `status: completed`; `blocked` adds one complete `blocker`. Do not copy version, diff, check status, or controller output.

If an assigned VC exposes an annotation/specification gap outside this group's write boundary, stop proof-only edits and return `blocked` with `blocker.failure_class` exactly `annotation-gap`. Its `vcs` must list every affected exact sealed-manual `name`, `parent`, and `annotation_location`; `message` explains existing premises and the missing conclusion. The controller validates and schedules from those structured VCs.
