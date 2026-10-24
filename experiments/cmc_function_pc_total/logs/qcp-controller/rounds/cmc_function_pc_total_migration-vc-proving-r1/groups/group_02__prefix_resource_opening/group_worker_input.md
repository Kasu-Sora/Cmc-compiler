# Group worker handoff

Read `.agents/skills/group-worker-proving/SKILL.md`, `.agents/skills/group-worker-proving/workflows/group-worker-proving.md`, and `.agents/skills/group-worker-proving/workflows/commands-and-checks.md` completely. This handoff adds only the current assignment; do not use a parent transcript or sibling output.

## Assignment

- Group: `prefix_resource_opening`; attempt 1; earlier compact attempts 0
- Difficulty hint: 3/5
- Required suffix for every new or adapted helper: `__prefix_resource_opening`


### `proof_of_cmc_function_prefix_total_entail_wit_1` — `LLM_pre_process`

Strategy: Choose the first disjunct. Frame cm_program_context_rep and destruct functions. The empty branch contradicts fn_pre<>0 after unfolding cm_function_list_rep and its empty header representation. For f::rest, use cm_function_list_cons__prefix_open to expose bp,np and the function context/body/tail. Instantiate f,rest,bp,np from these values. Unfold cm_functions_counts_representable once to project head and tail counts; unfold cm_concrete_functions_ready once and cm_concrete_function_ready to project the statement-wf, successor index bound and tail readiness. Preserve all existing scalar/index facts and cancel the resulting resources.

Prove only the top-level VC, opening with `LLM_pre_process ltac:(...)` and an explicit closer; do not edit its split goals.

Split goals:

  - none generated

### `proof_of_cmc_function_prefix_total_entail_wit_2` — `LLM_pre_process`

Strategy: Choose the first disjunct. Unfold only cm_function_context_rep to expose params and locals pointers. Instantiate np=np_2, bp=bp_2, f=f_2, rest=rest_2, pp=params and lp=locals. All requested pure facts are existing premises, including the call result and preserved index/target relations. Cancel the program frame, five function fields, slot lists, body representation and tail representation.

Prove only the top-level VC, opening with `LLM_pre_process ltac:(...)` and an explicit closer; do not edit its split goals.

Split goals:

  - none generated

### `proof_of_cmc_function_prefix_total_return_wit_3` — `LLM_pre_process`

Strategy: Choose the first disjunct, retaining cm_function_list_rep fn_pre functions. Destruct functions. A nonempty header representation entails fn_pre<>0 and contradicts fn_pre=0; unfold the list/header predicates only as needed. In the empty case cm_function_prefix reduces to zero for every target. Prove cm_i32_code_count 0, retain all pure premises and cancel the original program/list resources. Do not attempt the pure split, which has lost the null-pointer/list link.

Prove only the top-level VC, opening with `LLM_pre_process ltac:(...)` and an explicit closer; do not edit its split goals.

Split goals:

  - `proof_of_cmc_function_prefix_total_return_wit_3_split_goal_1` — leave its generated `Proof. Abort.` block unchanged
  - `proof_of_cmc_function_prefix_total_return_wit_3_split_goal_2` — leave its generated `Proof. Abort.` block unchanged

## Write boundary

- Editable top-level proof spans: `proof_of_cmc_function_prefix_total_entail_wit_1`, `proof_of_cmc_function_prefix_total_entail_wit_2`, `proof_of_cmc_function_prefix_total_return_wit_3`.
- Editable aggressive split-goal proof spans: none.
- Protected LLM_pre_process split blocks: `proof_of_cmc_function_prefix_total_return_wit_3_split_goal_1`, `proof_of_cmc_function_prefix_total_return_wit_3_split_goal_2`; their tokens remain `Proof. Abort.`.
- In `group_worker_lib`, append only proved suffixed helpers, token-identical sealed helper copies, and needed official imports.
- All declaration statements, other proof tokens, the manual prelude, and the seed library stay protected.

Whitespace, comments, line endings, and the final newline are formatting. The controller compares protected Rocq tokens, declaration ownership, proof mode, and kernel results. For an aggressive top-level proof, follow the worker rule above and use `Goal_apply` for the split lemmas; controller validation deliberately does not inspect that tactic choice.


## Files

- Copied manual: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_function_pc_total_migration-20261016090222/cmc_function_pc_total_migration-vc-proving-r1/groups/group_02__prefix_resource_opening/cmc_function_pc_total_migration_proof_manual.v`
- `group_worker_lib`: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_function_pc_total_migration-20261016090222/cmc_function_pc_total_migration-vc-proving-r1/groups/group_02__prefix_resource_opening/cmc_function_pc_total_migration_lib.v`
- Read-only `formal_case_lib`: `Rocq/examples/QCP_demos_human/cmc_function_pc_total_migration_lib.v`
- Frozen helper candidates: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_function_pc_total_migration-20261016090222/cmc_function_pc_total_migration-vc-proving-r1/public_helper_snapshot.txt` — search by needed helper/predicate names and read only matching declarations; never import this file
- Terminal report: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_function_pc_total_migration-20261016090222/rounds/cmc_function_pc_total_migration-vc-proving-r1/groups/group_02__prefix_resource_opening/group_worker_report.json`
- Notes: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_function_pc_total_migration-20261016090222/rounds/cmc_function_pc_total_migration-vc-proving-r1/groups/group_02__prefix_resource_opening/group_worker_output.md`. They are optional for ordinary outcomes, but an
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
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-debug --run cmc_function_pc_total_migration-20261016090222 --round cmc_function_pc_total_migration-vc-proving-r1 --group prefix_resource_opening
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_function_pc_total_migration-20261016090222 --round cmc_function_pc_total_migration-vc-proving-r1 --target-kind group-development --group prefix_resource_opening
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_function_pc_total_migration-20261016090222 --round cmc_function_pc_total_migration-vc-proving-r1 --target-kind group-check --group prefix_resource_opening
```

Debug script: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_function_pc_total_migration-20261016090222/_coq_builds/cmc_function_pc_total_migration-vc-proving-r1/group_02/src/.coq_debug/group_02_prefix_resource_opening.v`. Debug, development, and exact are optional proof feedback. `finalize-delivery` seals the two formal files and immediately runs the single mandatory controller group validation.

## Completion

Do not use raw Coq, Dune, Rocq MCP, `Admitted.`, new assumptions, forbidden lemmas, or the forbidden tactics `entailer!` and the bare alias `pre_process` (both are scanned exactly like a forbidden lemma; calls made inside `LLM_pre_process` and `Goal_apply` are unaffected). Repair a recoverable controller failure in this same worker. At the end, success is exactly `status: completed`; `blocked` adds one complete `blocker`. Do not copy version, diff, check status, or controller output.

If an assigned VC exposes an annotation/specification gap outside this group's write boundary, stop proof-only edits and return `blocked` with `blocker.failure_class` exactly `annotation-gap`. Its `vcs` must list every affected exact sealed-manual `name`, `parent`, and `annotation_location`; `message` explains existing premises and the missing conclusion. The controller validates and schedules from those structured VCs.
