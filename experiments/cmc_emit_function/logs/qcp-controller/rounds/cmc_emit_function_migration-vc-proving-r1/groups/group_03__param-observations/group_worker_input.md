# Group worker handoff

Read `.agents/skills/group-worker-proving/SKILL.md`, `.agents/skills/group-worker-proving/workflows/group-worker-proving.md`, and `.agents/skills/group-worker-proving/workflows/commands-and-checks.md` completely. This handoff adds only the current assignment; do not use a parent transcript or sibling output.

## Assignment

- Group: `param-observations`; attempt 1; earlier compact attempts 0
- Difficulty hint: 2/5
- Required suffix for every new or adapted helper: `__param_observations`


### `proof_of_cmc_emit_param_stores_from_return_wit_2` — `aggressive_pre_process`

Prove every listed split goal first, each opening with `LLM_pre_process ltac:(...)` and an explicit closer. Then prove the top-level VC with `aggressive_pre_process` and close each resulting branch with only `Goal_apply <split-goal lemma>` for the corresponding split goal, with no other tactic in the top-level proof. This is a worker proof rule; controller validation does not inspect the spelling of these applications.

Split goals:

  - `proof_of_cmc_emit_param_stores_from_return_wit_2_split_goal_1`: Normalize repeated cm_emit_params_head/cm_emit_params_tail on cons, then rewrite the original params=head::tail equality once. The resulting parameter-count predicate is an explicit precondition; no heap or existential is needed.
  - `proof_of_cmc_emit_param_stores_from_return_wit_2_split_goal_2`: Normalize repeated cm_emit_params_head/cm_emit_params_tail on cons, then rewrite the original params=head::tail equality once. The resulting member-safety predicate is an explicit precondition; no heap or existential is needed.
  - `proof_of_cmc_emit_param_stores_from_return_wit_2_split_goal_3`: Normalize repeated cm_emit_params_head/cm_emit_params_tail on cons, then rewrite the original params=head::tail equality once. The resulting slots-wf predicate is an explicit precondition; no heap or existential is needed.
  - `proof_of_cmc_emit_param_stores_from_return_wit_2_split_goal_4`: Normalize repeated cm_emit_params_head/cm_emit_params_tail on cons, then rewrite the original params=head::tail equality once. The resulting offset plus size upper bound is an explicit precondition; no heap or existential is needed.
  - `proof_of_cmc_emit_param_stores_from_return_wit_2_split_goal_5`: Normalize repeated cm_emit_params_head/cm_emit_params_tail on cons, then rewrite the original params=head::tail equality once. The resulting full=prefix++params equality is an explicit precondition; no heap or existential is needed.

### `proof_of_cmc_emit_param_stores_from_partial_solve_wit_5_pure` — `aggressive_pre_process`

Prove every listed split goal first, each opening with `LLM_pre_process ltac:(...)` and an explicit closer. Then prove the top-level VC with `aggressive_pre_process` and close each resulting branch with only `Goal_apply <split-goal lemma>` for the corresponding split goal, with no other tactic in the top-level proof. This is a worker proof rule; controller validation does not inspect the spelling of these applications.

Split goals:

  - `proof_of_cmc_emit_param_stores_from_partial_solve_wit_5_pure_split_goal_1`: Keep the current stack/slot/emitter resources as a pure-entailment frame. Rewrite params=head::tail and normalize head/tail observations; discharge full-prefix equality from the matching original pure premise (or computation for the shape equation).
  - `proof_of_cmc_emit_param_stores_from_partial_solve_wit_5_pure_split_goal_2`: Keep the current stack/slot/emitter resources as a pure-entailment frame. Rewrite params=head::tail and normalize head/tail observations; discharge slots well-formedness from the matching original pure premise (or computation for the shape equation).
  - `proof_of_cmc_emit_param_stores_from_partial_solve_wit_5_pure_split_goal_3`: Keep the current stack/slot/emitter resources as a pure-entailment frame. Rewrite params=head::tail and normalize head/tail observations; discharge member safety from the matching original pure premise (or computation for the shape equation).
  - `proof_of_cmc_emit_param_stores_from_partial_solve_wit_5_pure_split_goal_4`: Keep the current stack/slot/emitter resources as a pure-entailment frame. Rewrite params=head::tail and normalize head/tail observations; discharge parameter-count representability from the matching original pure premise (or computation for the shape equation).
  - `proof_of_cmc_emit_param_stores_from_partial_solve_wit_5_pure_split_goal_5`: Keep the current stack/slot/emitter resources as a pure-entailment frame. Rewrite params=head::tail and normalize head/tail observations; discharge head/tail reconstruction of a cons from the matching original pure premise (or computation for the shape equation).

### `proof_of_cmc_emit_param_stores_from_partial_solve_wit_6_pure` — `aggressive_pre_process`

Prove every listed split goal first, each opening with `LLM_pre_process ltac:(...)` and an explicit closer. Then prove the top-level VC with `aggressive_pre_process` and close each resulting branch with only `Goal_apply <split-goal lemma>` for the corresponding split goal, with no other tactic in the top-level proof. This is a worker proof rule; controller validation does not inspect the spelling of these applications.

Split goals:

  - `proof_of_cmc_emit_param_stores_from_partial_solve_wit_6_pure_split_goal_1`: Normalize all nested head/tail observations on cons. The remaining snoc size equality follows from the strengthened transition preconditions, substituting offset_pre=8+cm_slots_size structs prefix; leave all spatial resources unchanged and introduce the pure conclusion.
  - `proof_of_cmc_emit_param_stores_from_partial_solve_wit_6_pure_split_goal_2`: Normalize all nested head/tail observations on cons. The remaining nonnegative recursive offset follows from the strengthened transition preconditions, substituting offset_pre=8+cm_slots_size structs prefix; leave all spatial resources unchanged and introduce the pure conclusion.
  - `proof_of_cmc_emit_param_stores_from_partial_solve_wit_6_pure_split_goal_3`: Normalize all nested head/tail observations on cons. The remaining recursive offset plus tail size bound follows from the strengthened transition preconditions, substituting offset_pre=8+cm_slots_size structs prefix; leave all spatial resources unchanged and introduce the pure conclusion.

### `proof_of_cmc_emit_param_stores_from_partial_solve_wit_10_pure` — `aggressive_pre_process`

Prove every listed split goal first, each opening with `LLM_pre_process ltac:(...)` and an explicit closer. Then prove the top-level VC with `aggressive_pre_process` and close each resulting branch with only `Goal_apply <split-goal lemma>` for the corresponding split goal, with no other tactic in the top-level proof. This is a worker proof rule; controller validation does not inspect the spelling of these applications.

Split goals:

  - `proof_of_cmc_emit_param_stores_from_partial_solve_wit_10_pure_split_goal_1`: Normalize nested head/tail observations and use the original params reconstruction equality once. Recover full-prefix equality from preconditions or definitional computation; discard no needed facts when reducing the pure entailment over the emitter and slot-node frame.
  - `proof_of_cmc_emit_param_stores_from_partial_solve_wit_10_pure_split_goal_2`: Normalize nested head/tail observations and use the original params reconstruction equality once. Recover whole-list size bound from preconditions or definitional computation; discard no needed facts when reducing the pure entailment over the emitter and slot-node frame.
  - `proof_of_cmc_emit_param_stores_from_partial_solve_wit_10_pure_split_goal_3`: Normalize nested head/tail observations and use the original params reconstruction equality once. Recover slots well-formedness from preconditions or definitional computation; discard no needed facts when reducing the pure entailment over the emitter and slot-node frame.
  - `proof_of_cmc_emit_param_stores_from_partial_solve_wit_10_pure_split_goal_4`: Normalize nested head/tail observations and use the original params reconstruction equality once. Recover member safety from preconditions or definitional computation; discard no needed facts when reducing the pure entailment over the emitter and slot-node frame.
  - `proof_of_cmc_emit_param_stores_from_partial_solve_wit_10_pure_split_goal_5`: Normalize nested head/tail observations and use the original params reconstruction equality once. Recover parameter-count representability from preconditions or definitional computation; discard no needed facts when reducing the pure entailment over the emitter and slot-node frame.
  - `proof_of_cmc_emit_param_stores_from_partial_solve_wit_10_pure_split_goal_6`: Normalize nested head/tail observations and use the original params reconstruction equality once. Recover cons reconstruction equation from preconditions or definitional computation; discard no needed facts when reducing the pure entailment over the emitter and slot-node frame.

### `proof_of_cmc_emit_param_stores_from_partial_solve_wit_11_pure` — `aggressive_pre_process`

Prove every listed split goal first, each opening with `LLM_pre_process ltac:(...)` and an explicit closer. Then prove the top-level VC with `aggressive_pre_process` and close each resulting branch with only `Goal_apply <split-goal lemma>` for the corresponding split goal, with no other tactic in the top-level proof. This is a worker proof rule; controller validation does not inspect the spelling of these applications.

Split goals:

  - `proof_of_cmc_emit_param_stores_from_partial_solve_wit_11_pure_split_goal_1`: Compute cm_emit_params_head and cm_emit_params_tail on each syntactic cons from inside outward; the two reconstruction expressions are definitionally equal. Introduce the pure equality over the unchanged spatial frame.

## Write boundary

- Editable top-level proof spans: `proof_of_cmc_emit_param_stores_from_return_wit_2`, `proof_of_cmc_emit_param_stores_from_partial_solve_wit_5_pure`, `proof_of_cmc_emit_param_stores_from_partial_solve_wit_6_pure`, `proof_of_cmc_emit_param_stores_from_partial_solve_wit_10_pure`, `proof_of_cmc_emit_param_stores_from_partial_solve_wit_11_pure`.
- Editable aggressive split-goal proof spans: `proof_of_cmc_emit_param_stores_from_return_wit_2_split_goal_1`, `proof_of_cmc_emit_param_stores_from_return_wit_2_split_goal_2`, `proof_of_cmc_emit_param_stores_from_return_wit_2_split_goal_3`, `proof_of_cmc_emit_param_stores_from_return_wit_2_split_goal_4`, `proof_of_cmc_emit_param_stores_from_return_wit_2_split_goal_5`, `proof_of_cmc_emit_param_stores_from_partial_solve_wit_5_pure_split_goal_1`, `proof_of_cmc_emit_param_stores_from_partial_solve_wit_5_pure_split_goal_2`, `proof_of_cmc_emit_param_stores_from_partial_solve_wit_5_pure_split_goal_3`, `proof_of_cmc_emit_param_stores_from_partial_solve_wit_5_pure_split_goal_4`, `proof_of_cmc_emit_param_stores_from_partial_solve_wit_5_pure_split_goal_5`, `proof_of_cmc_emit_param_stores_from_partial_solve_wit_6_pure_split_goal_1`, `proof_of_cmc_emit_param_stores_from_partial_solve_wit_6_pure_split_goal_2`, `proof_of_cmc_emit_param_stores_from_partial_solve_wit_6_pure_split_goal_3`, `proof_of_cmc_emit_param_stores_from_partial_solve_wit_10_pure_split_goal_1`, `proof_of_cmc_emit_param_stores_from_partial_solve_wit_10_pure_split_goal_2`, `proof_of_cmc_emit_param_stores_from_partial_solve_wit_10_pure_split_goal_3`, `proof_of_cmc_emit_param_stores_from_partial_solve_wit_10_pure_split_goal_4`, `proof_of_cmc_emit_param_stores_from_partial_solve_wit_10_pure_split_goal_5`, `proof_of_cmc_emit_param_stores_from_partial_solve_wit_10_pure_split_goal_6`, `proof_of_cmc_emit_param_stores_from_partial_solve_wit_11_pure_split_goal_1`.
- Protected LLM_pre_process split blocks: none; their tokens remain `Proof. Abort.`.
- In `group_worker_lib`, append only proved suffixed helpers, token-identical sealed helper copies, and needed official imports.
- All declaration statements, other proof tokens, the manual prelude, and the seed library stay protected.

Whitespace, comments, line endings, and the final newline are formatting. The controller compares protected Rocq tokens, declaration ownership, proof mode, and kernel results. For an aggressive top-level proof, follow the worker rule above and use `Goal_apply` for the split lemmas; controller validation deliberately does not inspect that tactic choice.


## Files

- Copied manual: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_function_migration-20261019100342/cmc_emit_function_migration-vc-proving-r1/groups/group_03__param-observations/cmc_emit_function_migration_proof_manual.v`
- `group_worker_lib`: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_function_migration-20261019100342/cmc_emit_function_migration-vc-proving-r1/groups/group_03__param-observations/cmc_emit_function_migration_lib.v`
- Read-only `formal_case_lib`: `Rocq/examples/QCP_demos_human/cmc_emit_function_migration_lib.v`
- Frozen helper candidates: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_function_migration-20261019100342/cmc_emit_function_migration-vc-proving-r1/public_helper_snapshot.txt` — search by needed helper/predicate names and read only matching declarations; never import this file
- Terminal report: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_function_migration-20261019100342/rounds/cmc_emit_function_migration-vc-proving-r1/groups/group_03__param-observations/group_worker_report.json`
- Notes: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_function_migration-20261019100342/rounds/cmc_emit_function_migration-vc-proving-r1/groups/group_03__param-observations/group_worker_output.md`. They are optional for ordinary outcomes, but an
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
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-debug --run cmc_emit_function_migration-20261019100342 --round cmc_emit_function_migration-vc-proving-r1 --group param-observations
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_function_migration-20261019100342 --round cmc_emit_function_migration-vc-proving-r1 --target-kind group-development --group param-observations
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_function_migration-20261019100342 --round cmc_emit_function_migration-vc-proving-r1 --target-kind group-check --group param-observations
```

Debug script: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_function_migration-20261019100342/_coq_builds/cmc_emit_function_migration-vc-proving-r1/group_03/src/.coq_debug/group_03_param_observations.v`. Debug, development, and exact are optional proof feedback. `finalize-delivery` seals the two formal files and immediately runs the single mandatory controller group validation.

## Completion

Do not use raw Coq, Dune, Rocq MCP, `Admitted.`, new assumptions, forbidden lemmas, or the forbidden tactics `entailer!` and the bare alias `pre_process` (both are scanned exactly like a forbidden lemma; calls made inside `LLM_pre_process` and `Goal_apply` are unaffected). Repair a recoverable controller failure in this same worker. At the end, success is exactly `status: completed`; `blocked` adds one complete `blocker`. Do not copy version, diff, check status, or controller output.

If an assigned VC exposes an annotation/specification gap outside this group's write boundary, stop proof-only edits and return `blocked` with `blocker.failure_class` exactly `annotation-gap`. Its `vcs` must list every affected exact sealed-manual `name`, `parent`, and `annotation_location`; `message` explains existing premises and the missing conclusion. The controller validates and schedules from those structured VCs.
