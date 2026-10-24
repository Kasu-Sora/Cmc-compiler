# Group worker handoff

Read `.agents/skills/group-worker-proving/SKILL.md`, `.agents/skills/group-worker-proving/workflows/group-worker-proving.md`, and `.agents/skills/group-worker-proving/workflows/commands-and-checks.md` completely. This handoff adds only the current assignment; do not use a parent transcript or sibling output.

## Assignment

- Group: `result_reconstruction`; attempt 1; earlier compact attempts 0
- Difficulty hint: 3/5
- Required suffix for every new or adapted helper: `__result_reconstruction`


### `proof_of_cmc_function_prefix_total_return_wit_1` — `aggressive_pre_process`

Prove every listed split goal first, each opening with `LLM_pre_process ltac:(...)` and an explicit closer. Then prove the top-level VC with `aggressive_pre_process` and close each resulting branch with only `Goal_apply <split-goal lemma>` for the corresponding split goal, with no other tactic in the top-level proof. This is a worker proof rule; controller validation does not inspect the spelling of these applications.

Split goals:

  - `proof_of_cmc_function_prefix_total_return_wit_1_split_goal_1`: Use cm_function_prefix_total_bounds on rest and rewrite its start index with the recursive-call index equality. Rewrite functions=f::rest in cm_functions_counts_representable, extract the full code-size bound, and unfold cm_functions_code_size once. Substitute the head_count and retval equalities; lia gives the upper bound. Nonnegativity follows from their cm_i32_code_count premises. The spatial antecedent is only a frame for this pure conclusion. Unfold cm_i32_code_count to obtain the required conjunction.
  - `proof_of_cmc_function_prefix_total_return_wit_1_split_goal_2`: Rewrite functions=f::rest, head_count=cm_function_code_count policy p index_pre and the recursive retval equation. Unfold cm_function_prefix for this cons only; index_pre<>target_pre makes its equality-to-zero test false. Rewrite the model head index using PreH23, and normalize (target_pre-index_pre)-1=target_pre-(index_pre+1). The unchanged spatial resources can be discarded for the pure equality.
  - `proof_of_cmc_function_prefix_total_return_wit_1_split_goal_spatial`: Frame cm_program_context_rep. Rewrite functions=f::rest, fold cm_function_context_rep fn_pre f bp np from the five field cells and slot lists, choosing pp and lp and using fn_pre<>0. Apply the reverse direction of cm_function_list_cons__prefix_results with bp,np to combine that context, the body representation and the tail list. Cancel the unchanged program frame.

### `proof_of_cmc_function_pc_total_return_wit_1` — `aggressive_pre_process`

Prove every listed split goal first, each opening with `LLM_pre_process ltac:(...)` and an explicit closer. Then prove the top-level VC with `aggressive_pre_process` and close each resulting branch with only `Goal_apply <split-goal lemma>` for the corresponding split goal, with no other tactic in the top-level proof. This is a worker proof rule; controller validation does not inspect the spelling of these applications.

Split goals:

  - `proof_of_cmc_function_pc_total_return_wit_1_split_goal_1`: Project 0 <= cm_model_code_length policy p <= 2147483647 from cm_wf_program/cm_codegen_admissible; unfold only cm_model_code_length. Apply cm_function_prefix_total_bounds to cm_program_functions p at target_pre-0, normalize Zlength fs-Zlength fs=0, and rewrite retval. The total prefix bounds and the model bound give 0 <= 11+retval <= INT_MAX for arbitrary target; no target-range premise is needed. This split is pure; introduce its quantified premises and conclude cm_i32_code_count.
  - `proof_of_cmc_function_pc_total_return_wit_1_split_goal_2`: Use the supplied retval equation, normalize target_pre-0, and unfold cm_function_pc. The desired equation is definitional after rewriting; there are no spatial resources or existentials in this split.

## Write boundary

- Editable top-level proof spans: `proof_of_cmc_function_prefix_total_return_wit_1`, `proof_of_cmc_function_pc_total_return_wit_1`.
- Editable aggressive split-goal proof spans: `proof_of_cmc_function_prefix_total_return_wit_1_split_goal_1`, `proof_of_cmc_function_prefix_total_return_wit_1_split_goal_2`, `proof_of_cmc_function_prefix_total_return_wit_1_split_goal_spatial`, `proof_of_cmc_function_pc_total_return_wit_1_split_goal_1`, `proof_of_cmc_function_pc_total_return_wit_1_split_goal_2`.
- Protected LLM_pre_process split blocks: none; their tokens remain `Proof. Abort.`.
- In `group_worker_lib`, append only proved suffixed helpers, token-identical sealed helper copies, and needed official imports.
- All declaration statements, other proof tokens, the manual prelude, and the seed library stay protected.

Whitespace, comments, line endings, and the final newline are formatting. The controller compares protected Rocq tokens, declaration ownership, proof mode, and kernel results. For an aggressive top-level proof, follow the worker rule above and use `Goal_apply` for the split lemmas; controller validation deliberately does not inspect that tactic choice.


## Files

- Copied manual: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_function_pc_total_migration-20261016090222/cmc_function_pc_total_migration-vc-proving-r1/groups/group_00__result_reconstruction/cmc_function_pc_total_migration_proof_manual.v`
- `group_worker_lib`: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_function_pc_total_migration-20261016090222/cmc_function_pc_total_migration-vc-proving-r1/groups/group_00__result_reconstruction/cmc_function_pc_total_migration_lib.v`
- Read-only `formal_case_lib`: `Rocq/examples/QCP_demos_human/cmc_function_pc_total_migration_lib.v`
- Frozen helper candidates: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_function_pc_total_migration-20261016090222/cmc_function_pc_total_migration-vc-proving-r1/public_helper_snapshot.txt` — search by needed helper/predicate names and read only matching declarations; never import this file
- Terminal report: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_function_pc_total_migration-20261016090222/rounds/cmc_function_pc_total_migration-vc-proving-r1/groups/group_00__result_reconstruction/group_worker_report.json`
- Notes: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_function_pc_total_migration-20261016090222/rounds/cmc_function_pc_total_migration-vc-proving-r1/groups/group_00__result_reconstruction/group_worker_output.md`. They are optional for ordinary outcomes, but an
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
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-debug --run cmc_function_pc_total_migration-20261016090222 --round cmc_function_pc_total_migration-vc-proving-r1 --group result_reconstruction
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_function_pc_total_migration-20261016090222 --round cmc_function_pc_total_migration-vc-proving-r1 --target-kind group-development --group result_reconstruction
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_function_pc_total_migration-20261016090222 --round cmc_function_pc_total_migration-vc-proving-r1 --target-kind group-check --group result_reconstruction
```

Debug script: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_function_pc_total_migration-20261016090222/_coq_builds/cmc_function_pc_total_migration-vc-proving-r1/group_00/src/.coq_debug/group_00_result_reconstruction.v`. Debug, development, and exact are optional proof feedback. `finalize-delivery` seals the two formal files and immediately runs the single mandatory controller group validation.

## Completion

Do not use raw Coq, Dune, Rocq MCP, `Admitted.`, new assumptions, forbidden lemmas, or the forbidden tactics `entailer!` and the bare alias `pre_process` (both are scanned exactly like a forbidden lemma; calls made inside `LLM_pre_process` and `Goal_apply` are unaffected). Repair a recoverable controller failure in this same worker. At the end, success is exactly `status: completed`; `blocked` adds one complete `blocker`. Do not copy version, diff, check status, or controller output.

If an assigned VC exposes an annotation/specification gap outside this group's write boundary, stop proof-only edits and return `blocked` with `blocker.failure_class` exactly `annotation-gap`. Its `vcs` must list every affected exact sealed-manual `name`, `parent`, and `annotation_location`; `message` explains existing premises and the missing conclusion. The controller validates and schedules from those structured VCs.
