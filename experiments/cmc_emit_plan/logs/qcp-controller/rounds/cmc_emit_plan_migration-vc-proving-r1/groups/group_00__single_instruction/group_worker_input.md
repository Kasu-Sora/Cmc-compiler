# Group worker handoff

Read `.agents/skills/group-worker-proving/SKILL.md`, `.agents/skills/group-worker-proving/workflows/group-worker-proving.md`, and `.agents/skills/group-worker-proving/workflows/commands-and-checks.md` completely. This handoff adds only the current assignment; do not use a parent transcript or sibling output.

## Assignment

- Group: `single_instruction`; attempt 1; earlier compact attempts 0
- Difficulty hint: 1/5
- Required suffix for every new or adapted helper: `__single_instruction`


### `proof_of_cm_emit_plan_entail_wit_1` — `aggressive_pre_process`

Prove every listed split goal first, each opening with `LLM_pre_process ltac:(...)` and an explicit closer. Then prove the top-level VC with `aggressive_pre_process` and close each resulting branch with only `Goal_apply <split-goal lemma>` for the corresponding split goal, with no other tactic in the top-level proof. This is a worker proof rule; controller validation does not inspect the spelling of these applications.

Split goals:

  - `proof_of_cm_emit_plan_entail_wit_1_split_goal_1`: Unfold this split definition and cm_resolved_emitter_plan_rep to expose Zlength done + Zlength todo <= capacity. The todo is the head instruction cons tail. Rewrite Zlength_cons, Zlength_nil and Zlength_app for this singleton; use Zlength_nonneg tail and lia.The conclusion is pure; no existential witnesses or emitter internals are needed.
  - `proof_of_cm_emit_plan_entail_wit_1_split_goal_2`: Unfold this split definition and cm_resolved_emitter_plan_rep, and extract its budget. For fragment = [TVMInst opcode immediate_pre], rewrite Zlength_app, Zlength_cons and Zlength_nil to derive Zlength (done ++ fragment) + Zlength tail <= capacity by lia. This merely reassociates the existing total budget; no existential or underlying state transition is required.
  - `proof_of_cm_emit_plan_entail_wit_1_split_goal_spatial`: Unfold this split definition and only cm_resolved_emitter_plan_rep. Drop its pure budget conjunct and retain the identical cm_resolved_emitter_rep policy p emitter_pre out capacity done resource. No array splitting, address conversion, or existential instantiation is needed.

### `proof_of_cm_emit_plan_return_wit_1` — `aggressive_pre_process`

Prove every listed split goal first, each opening with `LLM_pre_process ltac:(...)` and an explicit closer. Then prove the top-level VC with `aggressive_pre_process` and close each resulting branch with only `Goal_apply <split-goal lemma>` for the corresponding split goal, with no other tactic in the top-level proof. This is a worker proof rule; controller validation does not inspect the spelling of these applications.

Split goals:

  - `proof_of_cm_emit_plan_return_wit_1_split_goal_spatial`: Unfold this split definition and the consequent cm_resolved_emitter_plan_rep. Supply its pure remaining-tail budget directly from PreH1, with done replaced by done ++ ([TVMInst opcode immediate_pre]). Cancel the identical resolved emitter resource at emitter_pre, out and capacity. The resolved callee postcondition already supplies the extended emitted list; this step packages it with tail, without new existentials.

### `proof_of_cm_emit_call_plan_entail_wit_1` — `aggressive_pre_process`

Prove every listed split goal first, each opening with `LLM_pre_process ltac:(...)` and an explicit closer. Then prove the top-level VC with `aggressive_pre_process` and close each resulting branch with only `Goal_apply <split-goal lemma>` for the corresponding split goal, with no other tactic in the top-level proof. This is a worker proof rule; controller validation does not inspect the spelling of these applications.

Split goals:

  - `proof_of_cm_emit_call_plan_entail_wit_1_split_goal_1`: Unfold this split definition and cm_resolved_emitter_plan_rep to expose Zlength done + Zlength todo <= capacity. The todo is the head instruction cons tail. Rewrite Zlength_cons, Zlength_nil and Zlength_app for this singleton; use Zlength_nonneg tail and lia.The conclusion is pure; no existential witnesses or emitter internals are needed.
  - `proof_of_cm_emit_call_plan_entail_wit_1_split_goal_2`: Unfold this split definition and cm_resolved_emitter_plan_rep, and extract its budget. For fragment = [TVMInst TVMCallOp (cm_function_pc policy p function_id_pre)], rewrite Zlength_app, Zlength_cons and Zlength_nil to derive Zlength (done ++ fragment) + Zlength tail <= capacity by lia. This merely reassociates the existing total budget; no existential or underlying state transition is required.
  - `proof_of_cm_emit_call_plan_entail_wit_1_split_goal_spatial`: Unfold this split definition and only cm_resolved_emitter_plan_rep. Drop its pure budget conjunct and retain the identical cm_resolved_emitter_rep policy p emitter_pre out capacity done resource. No array splitting, address conversion, or existential instantiation is needed.

### `proof_of_cm_emit_call_plan_return_wit_1` — `aggressive_pre_process`

Prove every listed split goal first, each opening with `LLM_pre_process ltac:(...)` and an explicit closer. Then prove the top-level VC with `aggressive_pre_process` and close each resulting branch with only `Goal_apply <split-goal lemma>` for the corresponding split goal, with no other tactic in the top-level proof. This is a worker proof rule; controller validation does not inspect the spelling of these applications.

Split goals:

  - `proof_of_cm_emit_call_plan_return_wit_1_split_goal_spatial`: Unfold this split definition and the consequent cm_resolved_emitter_plan_rep. Supply its pure remaining-tail budget directly from PreH1, with done replaced by done ++ ([TVMInst TVMCallOp (cm_function_pc policy p function_id_pre)]). Cancel the identical resolved emitter resource at emitter_pre, out and capacity. The resolved callee postcondition already supplies the extended emitted list; this step packages it with tail, without new existentials.

## Write boundary

- Editable top-level proof spans: `proof_of_cm_emit_plan_entail_wit_1`, `proof_of_cm_emit_plan_return_wit_1`, `proof_of_cm_emit_call_plan_entail_wit_1`, `proof_of_cm_emit_call_plan_return_wit_1`.
- Editable aggressive split-goal proof spans: `proof_of_cm_emit_plan_entail_wit_1_split_goal_1`, `proof_of_cm_emit_plan_entail_wit_1_split_goal_2`, `proof_of_cm_emit_plan_entail_wit_1_split_goal_spatial`, `proof_of_cm_emit_plan_return_wit_1_split_goal_spatial`, `proof_of_cm_emit_call_plan_entail_wit_1_split_goal_1`, `proof_of_cm_emit_call_plan_entail_wit_1_split_goal_2`, `proof_of_cm_emit_call_plan_entail_wit_1_split_goal_spatial`, `proof_of_cm_emit_call_plan_return_wit_1_split_goal_spatial`.
- Protected LLM_pre_process split blocks: none; their tokens remain `Proof. Abort.`.
- In `group_worker_lib`, append only proved suffixed helpers, token-identical sealed helper copies, and needed official imports.
- All declaration statements, other proof tokens, the manual prelude, and the seed library stay protected.

Whitespace, comments, line endings, and the final newline are formatting. The controller compares protected Rocq tokens, declaration ownership, proof mode, and kernel results. For an aggressive top-level proof, follow the worker rule above and use `Goal_apply` for the split lemmas; controller validation deliberately does not inspect that tactic choice.


## Files

- Copied manual: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_plan_migration-20261017135154/cmc_emit_plan_migration-vc-proving-r1/groups/group_00__single_instruction/cmc_emit_plan_migration_proof_manual.v`
- `group_worker_lib`: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_plan_migration-20261017135154/cmc_emit_plan_migration-vc-proving-r1/groups/group_00__single_instruction/cmc_emit_plan_migration_lib.v`
- Read-only `formal_case_lib`: `Rocq/examples/QCP_demos_human/cmc_emit_plan_migration_lib.v`
- Frozen helper candidates: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_plan_migration-20261017135154/cmc_emit_plan_migration-vc-proving-r1/public_helper_snapshot.txt` — search by needed helper/predicate names and read only matching declarations; never import this file
- Terminal report: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_plan_migration-20261017135154/rounds/cmc_emit_plan_migration-vc-proving-r1/groups/group_00__single_instruction/group_worker_report.json`
- Notes: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_plan_migration-20261017135154/rounds/cmc_emit_plan_migration-vc-proving-r1/groups/group_00__single_instruction/group_worker_output.md`. They are optional for ordinary outcomes, but an
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
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-debug --run cmc_emit_plan_migration-20261017135154 --round cmc_emit_plan_migration-vc-proving-r1 --group single_instruction
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_plan_migration-20261017135154 --round cmc_emit_plan_migration-vc-proving-r1 --target-kind group-development --group single_instruction
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_plan_migration-20261017135154 --round cmc_emit_plan_migration-vc-proving-r1 --target-kind group-check --group single_instruction
```

Debug script: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_plan_migration-20261017135154/_coq_builds/cmc_emit_plan_migration-vc-proving-r1/group_00/src/.coq_debug/group_00_single_instruction.v`. Debug, development, and exact are optional proof feedback. `finalize-delivery` seals the two formal files and immediately runs the single mandatory controller group validation.

## Completion

Do not use raw Coq, Dune, Rocq MCP, `Admitted.`, new assumptions, forbidden lemmas, or the forbidden tactics `entailer!` and the bare alias `pre_process` (both are scanned exactly like a forbidden lemma; calls made inside `LLM_pre_process` and `Goal_apply` are unaffected). Repair a recoverable controller failure in this same worker. At the end, success is exactly `status: completed`; `blocked` adds one complete `blocker`. Do not copy version, diff, check status, or controller output.

If an assigned VC exposes an annotation/specification gap outside this group's write boundary, stop proof-only edits and return `blocked` with `blocker.failure_class` exactly `annotation-gap`. Its `vcs` must list every affected exact sealed-manual `name`, `parent`, and `annotation_location`; `message` explains existing premises and the missing conclusion. The controller validates and schedules from those structured VCs.
