# Group worker handoff

Read `.agents/skills/group-worker-proving/SKILL.md`, `.agents/skills/group-worker-proving/workflows/group-worker-proving.md`, and `.agents/skills/group-worker-proving/workflows/commands-and-checks.md` completely. This handoff adds only the current assignment; do not use a parent transcript or sibling output.

## Assignment

- Group: `store_bounds`; attempt 1; earlier compact attempts 0
- Difficulty hint: 5/5
- Required suffix for every new or adapted helper: `__store_bounds`


### `proof_of_cm_emit_args_store_plan_which_implies_wit_5` — `aggressive_pre_process`

Prove every listed split goal first, each opening with `LLM_pre_process ltac:(...)` and an explicit closer. Then prove the top-level VC with `aggressive_pre_process` and close each resulting branch with only `Goal_apply <split-goal lemma>` for the corresponding split goal, with no other tactic in the top-level proof. This is a worker proof rule; controller validation does not inspect the spelling of these applications.

Split goals:

  - `proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_1`: Use the cons equality to expand one store step. By cm_emit_pair_lengths__store_bounds the head-code length is head_count; temp-store code has length 5. Zlength_app gives total length=head_count+5+tail-code length. Both list lengths are nonnegative and cm_i32_code_count pc plus the whole endpoint bound are supplied. The recursive endpoint equals the whole endpoint exactly; unfold cm_i32_code_count and finish by arithmetic.
  - `proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_2`: Use the cons equality to expand one store step. By cm_emit_pair_lengths__store_bounds the head-code length is head_count; temp-store code has length 5. Zlength_app gives total length=head_count+5+tail-code length. Both list lengths are nonnegative and cm_i32_code_count pc plus the whole endpoint bound are supplied. Bound pc+head_count+5 between pc and the whole endpoint; unfold cm_i32_code_count and finish by arithmetic.
  - `proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_3`: Use the cons equality to expand one store step. By cm_emit_pair_lengths__store_bounds the head-code length is head_count; temp-store code has length 5. Zlength_app gives total length=head_count+5+tail-code length. Both list lengths are nonnegative and cm_i32_code_count pc plus the whole endpoint bound are supplied. Drop the nonnegative tail-code length from the whole endpoint upper bound.
  - `proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_4`: Use the cons equality to expand one store step. By cm_emit_pair_lengths__store_bounds the head-code length is head_count; temp-store code has length 5. Zlength_app gives total length=head_count+5+tail-code length. Both list lengths are nonnegative and cm_i32_code_count pc plus the whole endpoint bound are supplied. The head count is a list length, so pc>=0 gives the required lower bound.
  - `proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_5`: Use the cons equality to expand one store step. By cm_emit_pair_lengths__store_bounds the head-code length is head_count; temp-store code has length 5. Zlength_app gives total length=head_count+5+tail-code length. Both list lengths are nonnegative and cm_i32_code_count pc plus the whole endpoint bound are supplied. Drop 5 and the nonnegative tail-code length from the whole endpoint upper bound.
  - `proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_6`: Use the cons equality to expand one store step. By cm_emit_pair_lengths__store_bounds the head-code length is head_count; temp-store code has length 5. Zlength_app gives total length=head_count+5+tail-code length. Both list lengths are nonnegative and cm_i32_code_count pc plus the whole endpoint bound are supplied. The head count is a list length; combine its nonnegativity with pc>=0.
  - `proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_7`: Expand one store step and Zlength_app. The head expression code is a prefix of the total store code, with a five-instruction store and nonnegative tail length. Use pc>=0 and the total endpoint bound to prove both inequalities in cm_i32_code_count.
  - `proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_8`: The cons length equality and slot+Zlength args=scratch<=temp_limit give slot<=temp_limit. Unfold the affine cm_temp_offset definition; the common frame-size constant cancels and arithmetic transfers its upper bound.
  - `proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_9`: Rewrite args=head::tail in cm_args_apair. Its depth is cm_imax(head rtemps, tail depth); use the right maximum inequality with the supplied scratch+depth bound.
  - `proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_10`: Reduce cm_expr_temps_for(head,0) to head rtemps. The cons cm_args_apair depth is cm_imax(head rtemps,tail depth), so the left maximum inequality yields the requested scratch bound.
  - `proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_11`: Rewrite Zlength args=1+Zlength tail from the cons equality and use slot+Zlength args=scratch.
  - `proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_12`: The cons length equality, nonnegative tail length and scratch<=temp_limit<=INT_MAX imply slot+1<=INT_MAX.

## Write boundary

- Editable top-level proof spans: `proof_of_cm_emit_args_store_plan_which_implies_wit_5`.
- Editable aggressive split-goal proof spans: `proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_1`, `proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_2`, `proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_3`, `proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_4`, `proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_5`, `proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_6`, `proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_7`, `proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_8`, `proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_9`, `proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_10`, `proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_11`, `proof_of_cm_emit_args_store_plan_which_implies_wit_5_split_goal_12`.
- Protected LLM_pre_process split blocks: none; their tokens remain `Proof. Abort.`.
- In `group_worker_lib`, append only proved suffixed helpers, token-identical sealed helper copies, and needed official imports.
- All declaration statements, other proof tokens, the manual prelude, and the seed library stay protected.

Whitespace, comments, line endings, and the final newline are formatting. The controller compares protected Rocq tokens, declaration ownership, proof mode, and kernel results. For an aggressive top-level proof, follow the worker rule above and use `Goal_apply` for the split lemmas; controller validation deliberately does not inspect that tactic choice.


## Files

- Copied manual: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_expr_call_migration-20261018170809/cmc_emit_expr_call_migration-vc-proving-r1/groups/group_00__store_bounds/cmc_emit_expr_call_migration_proof_manual.v`
- `group_worker_lib`: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_expr_call_migration-20261018170809/cmc_emit_expr_call_migration-vc-proving-r1/groups/group_00__store_bounds/cmc_emit_expr_call_migration_lib.v`
- Read-only `formal_case_lib`: `Rocq/examples/QCP_demos_human/cmc_emit_expr_call_migration_lib.v`
- Frozen helper candidates: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_expr_call_migration-20261018170809/cmc_emit_expr_call_migration-vc-proving-r1/public_helper_snapshot.txt` — search by needed helper/predicate names and read only matching declarations; never import this file
- Terminal report: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_expr_call_migration-20261018170809/rounds/cmc_emit_expr_call_migration-vc-proving-r1/groups/group_00__store_bounds/group_worker_report.json`
- Notes: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_expr_call_migration-20261018170809/rounds/cmc_emit_expr_call_migration-vc-proving-r1/groups/group_00__store_bounds/group_worker_output.md`. They are optional for ordinary outcomes, but an
  `annotation-gap` blocker requires a non-empty explanation here because the controller preserves this
  exact Markdown as part of the aggregated annotation feedback.
- Previous proving round: none; no reuse note is expected.

The group directory must finish with the copied manual and `group_worker_lib`.

## Planned helpers

- `cm_emit_pair_lengths__store_bounds`; public; expected use: Prove forall policy p fid e pc temp, Zlength(cm_lcode_of(cm_emit_expr_pair policy p fid pc temp e))=cm_lvalue_code_count policy p fid e /\ Zlength(cm_rcode_of(cm_emit_expr_pair policy p fid pc temp e))=cm_rvalue_code_count policy p fid e, with no wellformedness premise. Use structural recursion on e carrying both equalities and generalized pc/temp; split the matching boolean branches, reduce primitive code lengths and Zlength_app. In CMCallE use an inner induction on args for the local store fixpoint and cm_args_reload_length; child IHs must permit shifted pc and scratch. This is a mathematical code-model theorem, not an implementation proof of external cm_emit_expr. Its rvalue projection supplies the head_count/length bridge in store-bound splits 1-6.

`local` stays in this group. A proved `public` helper is promoted by the controller for later rounds. Historical token-identical copies may keep their sealed suffix; adaptations use this group's suffix.

## Commands

Run a needed command unchanged with its bound cwd. Prefer a direct system-terminal call. If terminal operations are available only through `functions.exec`, use a transparent cell that awaits exactly one `tools.exec_command` to launch, or one `tools.write_stdin` to continue the same live session (or the runtime-documented normalized equivalent), and only forwards the result. Pass command/argv, every argument, and cwd unchanged when launching; preserve the exact session handle when continuing. Use a normalized equivalent only if its input shape accepts those values unchanged; never serialize argv into shell text, reparse a rendered command, or add quoting. Do not call another tool in the cell, construct, alter, sequence, wrap, pipe, or background commands. Preserve every outer cell and inner process/session handle until terminal exit; if the bridge yields a running cell, resume only that cell with `functions.wait`.

```text
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-debug --run cmc_emit_expr_call_migration-20261018170809 --round cmc_emit_expr_call_migration-vc-proving-r1 --group store_bounds
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_expr_call_migration-20261018170809 --round cmc_emit_expr_call_migration-vc-proving-r1 --target-kind group-development --group store_bounds
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_expr_call_migration-20261018170809 --round cmc_emit_expr_call_migration-vc-proving-r1 --target-kind group-check --group store_bounds
```

Debug script: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_expr_call_migration-20261018170809/_coq_builds/cmc_emit_expr_call_migration-vc-proving-r1/group_00/src/.coq_debug/group_00_store_bounds.v`. Debug, development, and exact are optional proof feedback. `finalize-delivery` seals the two formal files and immediately runs the single mandatory controller group validation.

## Completion

Do not use raw Coq, Dune, Rocq MCP, `Admitted.`, new assumptions, forbidden lemmas, or the forbidden tactics `entailer!` and the bare alias `pre_process` (both are scanned exactly like a forbidden lemma; calls made inside `LLM_pre_process` and `Goal_apply` are unaffected). Repair a recoverable controller failure in this same worker. At the end, success is exactly `status: completed`; `blocked` adds one complete `blocker`. Do not copy version, diff, check status, or controller output.

If an assigned VC exposes an annotation/specification gap outside this group's write boundary, stop proof-only edits and return `blocked` with `blocker.failure_class` exactly `annotation-gap`. Its `vcs` must list every affected exact sealed-manual `name`, `parent`, and `annotation_location`; `message` explains existing premises and the missing conclusion. The controller validates and schedules from those structured VCs.
