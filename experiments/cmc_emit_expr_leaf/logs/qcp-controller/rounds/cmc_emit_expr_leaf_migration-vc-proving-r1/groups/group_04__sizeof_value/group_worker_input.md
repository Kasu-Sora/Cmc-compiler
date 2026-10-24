# Group worker handoff

Read `.agents/skills/group-worker-proving/SKILL.md`, `.agents/skills/group-worker-proving/workflows/group-worker-proving.md`, and `.agents/skills/group-worker-proving/workflows/commands-and-checks.md` completely. This handoff adds only the current assignment; do not use a parent transcript or sibling output.

## Assignment

- Group: `sizeof_value`; attempt 1; earlier compact attempts 0
- Difficulty hint: 3/5
- Required suffix for every new or adapted helper: `__sizeof_value`


### `proof_of_cm_sizeof_value_return_wit_1` — `aggressive_pre_process`

Prove every listed split goal first, each opening with `LLM_pre_process ltac:(...)` and an explicit closer. Then prove the top-level VC with `aggressive_pre_process` and close each resulting branch with only `Goal_apply <split-goal lemma>` for the corresponding split goal, with no other tactic in the top-level proof. This is a worker proof rule; controller validation does not inspect the spelling of these applications.

Split goals:

  - `proof_of_cm_sizeof_value_return_wit_1_split_goal_1`: Pure equality: destruct asked. The non-pointer constructors contradict code_pre >= 1024 using code_pre=cm_type_encode asked and cm_type_code_wf asked (struct id is in [0,1022)); the pointer constructor has cm_type_size = 8 by definition.

### `proof_of_cm_sizeof_value_return_wit_2` — `aggressive_pre_process`

Prove every listed split goal first, each opening with `LLM_pre_process ltac:(...)` and an explicit closer. Then prove the top-level VC with `aggressive_pre_process` and close each resulting branch with only `Goal_apply <split-goal lemma>` for the corresponding split goal, with no other tactic in the top-level proof. This is a worker proof rule; controller validation does not inspect the spelling of these applications.

Split goals:

  - `proof_of_cm_sizeof_value_return_wit_2_split_goal_1`: Substitute retval. Apply cm_rep_type_size_matches with the supplied cm_type_code_wf and cm_type_refs; obtain its universal struct-well-formedness premise from the first conjunct of cm_typed_program. Lift the resulting equality to a pure assertion; heap resources are irrelevant to this split.
  - `proof_of_cm_sizeof_value_return_wit_2_split_goal_spatial`: Fold cm_program_context_rep, instantiate its s,g,t with the existing sp,gp,tp, establish program_pre <> 0 from the premise, and cancel all five program fields and the three list resources after reordering the struct-list frame.

### `proof_of_cm_sizeof_value_which_implies_wit_1` — `aggressive_pre_process`

Prove every listed split goal first, each opening with `LLM_pre_process ltac:(...)` and an explicit closer. Then prove the top-level VC with `aggressive_pre_process` and close each resulting branch with only `Goal_apply <split-goal lemma>` for the corresponding split goal, with no other tactic in the top-level proof. This is a worker proof rule; controller validation does not inspect the spelling of these applications.

Split goals:

  - `proof_of_cm_sizeof_value_which_implies_wit_1_split_goal_1`: Substitute code; unfold cm_type_encode and combine cm_type_depth_nonnegative__expression_assignment_safety with cm_type_base_bounds__expression_assignment_safety (using cm_type_code_wf asked). Linear arithmetic proves nonnegativity.

### `proof_of_cm_sizeof_value_which_implies_wit_2` — `LLM_pre_process`

Strategy: Choose the left disjunct. Unfold cm_program_context_rep, extract its nonzero root fact and s,g,t witnesses. Instantiate the goal existentials in tp,gp,sp order with t,g,s, and cancel the five fields and the three list resources; no scalar or pointer bridge is missing.

Prove only the top-level VC, opening with `LLM_pre_process ltac:(...)` and an explicit closer; do not edit its split goals.

Split goals:

  - none generated

## Write boundary

- Editable top-level proof spans: `proof_of_cm_sizeof_value_return_wit_1`, `proof_of_cm_sizeof_value_return_wit_2`, `proof_of_cm_sizeof_value_which_implies_wit_1`, `proof_of_cm_sizeof_value_which_implies_wit_2`.
- Editable aggressive split-goal proof spans: `proof_of_cm_sizeof_value_return_wit_1_split_goal_1`, `proof_of_cm_sizeof_value_return_wit_2_split_goal_1`, `proof_of_cm_sizeof_value_return_wit_2_split_goal_spatial`, `proof_of_cm_sizeof_value_which_implies_wit_1_split_goal_1`.
- Protected LLM_pre_process split blocks: none; their tokens remain `Proof. Abort.`.
- In `group_worker_lib`, append only proved suffixed helpers, token-identical sealed helper copies, and needed official imports.
- All declaration statements, other proof tokens, the manual prelude, and the seed library stay protected.

Whitespace, comments, line endings, and the final newline are formatting. The controller compares protected Rocq tokens, declaration ownership, proof mode, and kernel results. For an aggressive top-level proof, follow the worker rule above and use `Goal_apply` for the split lemmas; controller validation deliberately does not inspect that tactic choice.


## Files

- Copied manual: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_expr_leaf_migration-20261017144315/cmc_emit_expr_leaf_migration-vc-proving-r1/groups/group_04__sizeof_value/cmc_emit_expr_leaf_migration_proof_manual.v`
- `group_worker_lib`: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_expr_leaf_migration-20261017144315/cmc_emit_expr_leaf_migration-vc-proving-r1/groups/group_04__sizeof_value/cmc_emit_expr_leaf_migration_lib.v`
- Read-only `formal_case_lib`: `Rocq/examples/QCP_demos_human/cmc_emit_expr_leaf_migration_lib.v`
- Frozen helper candidates: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_expr_leaf_migration-20261017144315/cmc_emit_expr_leaf_migration-vc-proving-r1/public_helper_snapshot.txt` — search by needed helper/predicate names and read only matching declarations; never import this file
- Terminal report: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_expr_leaf_migration-20261017144315/rounds/cmc_emit_expr_leaf_migration-vc-proving-r1/groups/group_04__sizeof_value/group_worker_report.json`
- Notes: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_expr_leaf_migration-20261017144315/rounds/cmc_emit_expr_leaf_migration-vc-proving-r1/groups/group_04__sizeof_value/group_worker_output.md`. They are optional for ordinary outcomes, but an
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
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-debug --run cmc_emit_expr_leaf_migration-20261017144315 --round cmc_emit_expr_leaf_migration-vc-proving-r1 --group sizeof_value
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_expr_leaf_migration-20261017144315 --round cmc_emit_expr_leaf_migration-vc-proving-r1 --target-kind group-development --group sizeof_value
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_expr_leaf_migration-20261017144315 --round cmc_emit_expr_leaf_migration-vc-proving-r1 --target-kind group-check --group sizeof_value
```

Debug script: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_expr_leaf_migration-20261017144315/_coq_builds/cmc_emit_expr_leaf_migration-vc-proving-r1/group_04/src/.coq_debug/group_04_sizeof_value.v`. Debug, development, and exact are optional proof feedback. `finalize-delivery` seals the two formal files and immediately runs the single mandatory controller group validation.

## Completion

Do not use raw Coq, Dune, Rocq MCP, `Admitted.`, new assumptions, forbidden lemmas, or the forbidden tactics `entailer!` and the bare alias `pre_process` (both are scanned exactly like a forbidden lemma; calls made inside `LLM_pre_process` and `Goal_apply` are unaffected). Repair a recoverable controller failure in this same worker. At the end, success is exactly `status: completed`; `blocked` adds one complete `blocker`. Do not copy version, diff, check status, or controller output.

If an assigned VC exposes an annotation/specification gap outside this group's write boundary, stop proof-only edits and return `blocked` with `blocker.failure_class` exactly `annotation-gap`. Its `vcs` must list every affected exact sealed-manual `name`, `parent`, and `annotation_location`; `message` explains existing premises and the missing conclusion. The controller validates and schedules from those structured VCs.
