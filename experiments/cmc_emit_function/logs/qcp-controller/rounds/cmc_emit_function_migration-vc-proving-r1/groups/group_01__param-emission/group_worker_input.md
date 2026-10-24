# Group worker handoff

Read `.agents/skills/group-worker-proving/SKILL.md`, `.agents/skills/group-worker-proving/workflows/group-worker-proving.md`, and `.agents/skills/group-worker-proving/workflows/commands-and-checks.md` completely. This handoff adds only the current assignment; do not use a parent transcript or sibling output.

## Assignment

- Group: `param-emission`; attempt 1; earlier compact attempts 0
- Difficulty hint: 4/5
- Required suffix for every new or adapted helper: `__param_emission`


### `proof_of_cmc_emit_param_stores_from_which_implies_wit_4` — `aggressive_pre_process`

Prove every listed split goal first, each opening with `LLM_pre_process ltac:(...)` and an explicit closer. Then prove the top-level VC with `aggressive_pre_process` and close each resulting branch with only `Goal_apply <split-goal lemma>` for the corresponding split goal, with no other tactic in the top-level proof. This is a worker proof rule; controller validation does not inspect the spelling of these applications.

Split goals:

  - `proof_of_cmc_emit_param_stores_from_which_implies_wit_4_split_goal_spatial`: Expand the remaining-code side of cm_emit_param_stores once using params=head::tail. Establish cm_param_offset policy p fid slot_pre=offset_pre using full=params_of_f=prefix++params, slot_pre=Zlength prefix, offset_pre=8+size prefix, and the stable slots-prefix-at-append-length helper. Reassociate list app; the emitter predicate becomes identical with unchanged policy/pointer/output/capacity/tail.

### `proof_of_cmc_emit_param_stores_from_which_implies_wit_5` — `aggressive_pre_process`

Prove every listed split goal first, each opening with `LLM_pre_process ltac:(...)` and an explicit closer. Then prove the top-level VC with `aggressive_pre_process` and close each resulting branch with only `Goal_apply <split-goal lemma>` for the corresponding split goal, with no other tactic in the top-level proof. This is a worker proof rule; controller validation does not inspect the spelling of these applications.

Split goals:

  - `proof_of_cmc_emit_param_stores_from_which_implies_wit_5_split_goal_spatial`: Fold the completed-code side of cm_emit_param_stores once using params=head::tail. Establish cm_param_offset policy p fid slot_pre=offset_pre using full=params_of_f=prefix++params, slot_pre=Zlength prefix, offset_pre=8+size prefix, and the stable slots-prefix-at-append-length helper. Reassociate list app; the emitter predicate becomes identical with unchanged policy/pointer/output/capacity/tail.

## Write boundary

- Editable top-level proof spans: `proof_of_cmc_emit_param_stores_from_which_implies_wit_4`, `proof_of_cmc_emit_param_stores_from_which_implies_wit_5`.
- Editable aggressive split-goal proof spans: `proof_of_cmc_emit_param_stores_from_which_implies_wit_4_split_goal_spatial`, `proof_of_cmc_emit_param_stores_from_which_implies_wit_5_split_goal_spatial`.
- Protected LLM_pre_process split blocks: none; their tokens remain `Proof. Abort.`.
- In `group_worker_lib`, append only proved suffixed helpers, token-identical sealed helper copies, and needed official imports.
- All declaration statements, other proof tokens, the manual prelude, and the seed library stay protected.

Whitespace, comments, line endings, and the final newline are formatting. The controller compares protected Rocq tokens, declaration ownership, proof mode, and kernel results. For an aggressive top-level proof, follow the worker rule above and use `Goal_apply` for the split lemmas; controller validation deliberately does not inspect that tactic choice.


## Files

- Copied manual: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_function_migration-20261019100342/cmc_emit_function_migration-vc-proving-r1/groups/group_01__param-emission/cmc_emit_function_migration_proof_manual.v`
- `group_worker_lib`: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_function_migration-20261019100342/cmc_emit_function_migration-vc-proving-r1/groups/group_01__param-emission/cmc_emit_function_migration_lib.v`
- Read-only `formal_case_lib`: `Rocq/examples/QCP_demos_human/cmc_emit_function_migration_lib.v`
- Frozen helper candidates: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_function_migration-20261019100342/cmc_emit_function_migration-vc-proving-r1/public_helper_snapshot.txt` — search by needed helper/predicate names and read only matching declarations; never import this file
- Terminal report: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_function_migration-20261019100342/rounds/cmc_emit_function_migration-vc-proving-r1/groups/group_01__param-emission/group_worker_report.json`
- Notes: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_function_migration-20261019100342/rounds/cmc_emit_function_migration-vc-proving-r1/groups/group_01__param-emission/group_worker_output.md`. They are optional for ordinary outcomes, but an
  `annotation-gap` blocker requires a non-empty explanation here because the controller preserves this
  exact Markdown as part of the aggregated annotation feedback.
- Previous proving round: none; no reuse note is expected.

The group directory must finish with the copied manual and `group_worker_lib`.

## Planned helpers

- `cm_function_slots_prefix_app__param_emission`; public; expected use: For all structs,prefix,rest, prove cm_slots_prefix structs (prefix++rest) (Zlength prefix)=cm_slots_size structs prefix by induction on prefix. Nil computes index zero; cons uses positive Zlength, the nonzero branch and successor-minus-one arithmetic. No prefix wf needed. This identifies the current param offset for both emission transitions.

`local` stays in this group. A proved `public` helper is promoted by the controller for later rounds. Historical token-identical copies may keep their sealed suffix; adaptations use this group's suffix.

## Commands

Run a needed command unchanged with its bound cwd. Prefer a direct system-terminal call. If terminal operations are available only through `functions.exec`, use a transparent cell that awaits exactly one `tools.exec_command` to launch, or one `tools.write_stdin` to continue the same live session (or the runtime-documented normalized equivalent), and only forwards the result. Pass command/argv, every argument, and cwd unchanged when launching; preserve the exact session handle when continuing. Use a normalized equivalent only if its input shape accepts those values unchanged; never serialize argv into shell text, reparse a rendered command, or add quoting. Do not call another tool in the cell, construct, alter, sequence, wrap, pipe, or background commands. Preserve every outer cell and inner process/session handle until terminal exit; if the bridge yields a running cell, resume only that cell with `functions.wait`.

```text
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-debug --run cmc_emit_function_migration-20261019100342 --round cmc_emit_function_migration-vc-proving-r1 --group param-emission
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_function_migration-20261019100342 --round cmc_emit_function_migration-vc-proving-r1 --target-kind group-development --group param-emission
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_function_migration-20261019100342 --round cmc_emit_function_migration-vc-proving-r1 --target-kind group-check --group param-emission
```

Debug script: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_function_migration-20261019100342/_coq_builds/cmc_emit_function_migration-vc-proving-r1/group_01/src/.coq_debug/group_01_param_emission.v`. Debug, development, and exact are optional proof feedback. `finalize-delivery` seals the two formal files and immediately runs the single mandatory controller group validation.

## Completion

Do not use raw Coq, Dune, Rocq MCP, `Admitted.`, new assumptions, forbidden lemmas, or the forbidden tactics `entailer!` and the bare alias `pre_process` (both are scanned exactly like a forbidden lemma; calls made inside `LLM_pre_process` and `Goal_apply` are unaffected). Repair a recoverable controller failure in this same worker. At the end, success is exactly `status: completed`; `blocked` adds one complete `blocker`. Do not copy version, diff, check status, or controller output.

If an assigned VC exposes an annotation/specification gap outside this group's write boundary, stop proof-only edits and return `blocked` with `blocker.failure_class` exactly `annotation-gap`. Its `vcs` must list every affected exact sealed-manual `name`, `parent`, and `annotation_location`; `message` explains existing premises and the missing conclusion. The controller validates and schedules from those structured VCs.
