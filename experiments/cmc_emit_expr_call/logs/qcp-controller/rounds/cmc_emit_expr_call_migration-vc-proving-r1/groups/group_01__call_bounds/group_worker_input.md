# Group worker handoff

Read `.agents/skills/group-worker-proving/SKILL.md`, `.agents/skills/group-worker-proving/workflows/group-worker-proving.md`, and `.agents/skills/group-worker-proving/workflows/commands-and-checks.md` completely. This handoff adds only the current assignment; do not use a parent transcript or sibling output.

## Assignment

- Group: `call_bounds`; attempt 1; earlier compact attempts 0
- Difficulty hint: 4/5
- Required suffix for every new or adapted helper: `__call_bounds`


### `proof_of_cm_emit_call_expr_which_implies_wit_2` — `aggressive_pre_process`

Prove every listed split goal first, each opening with `LLM_pre_process ltac:(...)` and an explicit closer. Then prove the top-level VC with `aggressive_pre_process` and close each resulting branch with only `Goal_apply <split-goal lemma>` for the corresponding split goal, with no other tactic in the top-level proof. This is a worker proof rule; controller validation does not inspect the spelling of these applications.

Split goals:

  - `proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_1`: Use kind=8 to expose CMCallE and substitute lvalue_pre=0. Rewrite cm_expr_tpair_call, cm_expr_temps_for and cm_args_temps; cm_args_apair_count_depth__call_bounds replaces acount by Zlength. The supplied temp+temps<=temp_limit is exactly this goal after arithmetic reassociation.
  - `proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_2`: Use kind=8 to expose CMCallE and substitute lvalue_pre=0. Derive temp+Zlength args<=temp_limit from the call temporary-depth bound and nonnegative depth. Derive temp_limit<=INT_MAX from affine cm_temp_offset, f lookup and nonnegative parameter/local slot sizes using cm_slots_size_nonnegative__call_bounds; combine the bounds.
  - `proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_3`: Use kind=8 to expose CMCallE and substitute lvalue_pre=0. The call temporary budget is Zlength args+depth by cm_expr_tpair_call and cm_args_apair_count_depth__call_bounds; drop the nonnegative depth from its bound.
  - `proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_4`: Combine the given temp>=0 with Zlength_nonneg; no heap resource or constructor reasoning is needed.
  - `proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_5`: Use f=cm_function_at and both supplied cm_slots_wf facts with cm_slots_size_nonnegative__call_bounds. Unfold cm_temp_offset=8+params_size+locals_size+8*temp_limit; temp_limit>=0 follows from 0<=temp<=temp_limit. Arithmetic with the offset upper bound yields temp_limit<=INT_MAX.
  - `proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_6`: Unfold cm_rep_args_length; the equality to Zlength is definitional.
  - `proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_7`: Use kind=8 to expose CMCallE and substitute lvalue_pre=0. The call temporary budget and nonnegative depth imply Zlength args<=temp_limit. Obtain temp_limit<=INT_MAX from the slot-size/offset argument and apply cm_rep_args_safe_of_length__call_bounds to the resulting length bound.
  - `proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_8`: Use kind=8 to expose CMCallE and substitute lvalue_pre=0. Unfold one cm_expr_counts_representable call layer. Its nested list-safe fixpoint is definitionally cm_args_counts_representable; project that conjunct.
  - `proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_9`: Use kind=8 to expose CMCallE and substitute lvalue_pre=0. Unfold the call branch of cm_expr_wf. Its nested argument/parameter typing fixpoint is definitionally cm_args_wf; project the conjunct with the callee function parameters.
  - `proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_10`: Use kind=8 to expose CMCallE and substitute lvalue_pre=0. Unfold one cm_expr_counts_representable call layer and cm_i32_code_count; project the callee upper bound.
  - `proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_11`: Use kind=8 to expose CMCallE and substitute lvalue_pre=0. Unfold one cm_expr_counts_representable call layer and cm_i32_code_count; project the callee nonnegative bound.

## Write boundary

- Editable top-level proof spans: `proof_of_cm_emit_call_expr_which_implies_wit_2`.
- Editable aggressive split-goal proof spans: `proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_1`, `proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_2`, `proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_3`, `proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_4`, `proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_5`, `proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_6`, `proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_7`, `proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_8`, `proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_9`, `proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_10`, `proof_of_cm_emit_call_expr_which_implies_wit_2_split_goal_11`.
- Protected LLM_pre_process split blocks: none; their tokens remain `Proof. Abort.`.
- In `group_worker_lib`, append only proved suffixed helpers, token-identical sealed helper copies, and needed official imports.
- All declaration statements, other proof tokens, the manual prelude, and the seed library stay protected.

Whitespace, comments, line endings, and the final newline are formatting. The controller compares protected Rocq tokens, declaration ownership, proof mode, and kernel results. For an aggressive top-level proof, follow the worker rule above and use `Goal_apply` for the split lemmas; controller validation deliberately does not inspect that tactic choice.


## Files

- Copied manual: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_expr_call_migration-20261018170809/cmc_emit_expr_call_migration-vc-proving-r1/groups/group_01__call_bounds/cmc_emit_expr_call_migration_proof_manual.v`
- `group_worker_lib`: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_expr_call_migration-20261018170809/cmc_emit_expr_call_migration-vc-proving-r1/groups/group_01__call_bounds/cmc_emit_expr_call_migration_lib.v`
- Read-only `formal_case_lib`: `Rocq/examples/QCP_demos_human/cmc_emit_expr_call_migration_lib.v`
- Frozen helper candidates: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_expr_call_migration-20261018170809/cmc_emit_expr_call_migration-vc-proving-r1/public_helper_snapshot.txt` — search by needed helper/predicate names and read only matching declarations; never import this file
- Terminal report: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_expr_call_migration-20261018170809/rounds/cmc_emit_expr_call_migration-vc-proving-r1/groups/group_01__call_bounds/group_worker_report.json`
- Notes: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_expr_call_migration-20261018170809/rounds/cmc_emit_expr_call_migration-vc-proving-r1/groups/group_01__call_bounds/group_worker_output.md`. They are optional for ordinary outcomes, but an
  `annotation-gap` blocker requires a non-empty explanation here because the controller preserves this
  exact Markdown as part of the aggregated annotation feedback.
- Previous proving round: none; no reuse note is expected.

The group directory must finish with the copied manual and `group_worker_lib`.

## Planned helpers

- `cm_args_apair_count_depth__call_bounds`; public; expected use: Prove forall args, cm_acount(cm_args_apair args)=Zlength args /\ 0<=cm_adepth(cm_args_apair args). Induct on args, use Zlength_cons and that cm_imax dominates its second operand; no assumptions on expressions are needed. Used to convert call temporary budget to scratch and argument-length bounds.
- `cm_slots_size_nonnegative__call_bounds`; public; expected use: Prove forall structs slots, cm_slots_wf structs slots -> 0<=cm_slots_size structs slots. Induct on slots; obtain head positivity from index 0 and tail wellformedness by shifting a valid tail index to index+1, using cm_slot_at list lookup equations. Sum nonnegative sizes. Both parameter and local instances are explicitly supplied by the call-bound VC.
- `cm_rep_args_safe_of_length__call_bounds`; public; expected use: Prove forall args, Zlength args<=2147483647 -> cm_rep_args_safe args. Induct on args; each cons has nonnegative tail length and tail length strictly below 2147483647 by Zlength_cons, and the induction hypothesis applies to the tail. cm_rep_args_length is Zlength. Used after deriving argument-length bound from temporary budget.

`local` stays in this group. A proved `public` helper is promoted by the controller for later rounds. Historical token-identical copies may keep their sealed suffix; adaptations use this group's suffix.

## Commands

Run a needed command unchanged with its bound cwd. Prefer a direct system-terminal call. If terminal operations are available only through `functions.exec`, use a transparent cell that awaits exactly one `tools.exec_command` to launch, or one `tools.write_stdin` to continue the same live session (or the runtime-documented normalized equivalent), and only forwards the result. Pass command/argv, every argument, and cwd unchanged when launching; preserve the exact session handle when continuing. Use a normalized equivalent only if its input shape accepts those values unchanged; never serialize argv into shell text, reparse a rendered command, or add quoting. Do not call another tool in the cell, construct, alter, sequence, wrap, pipe, or background commands. Preserve every outer cell and inner process/session handle until terminal exit; if the bridge yields a running cell, resume only that cell with `functions.wait`.

```text
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-debug --run cmc_emit_expr_call_migration-20261018170809 --round cmc_emit_expr_call_migration-vc-proving-r1 --group call_bounds
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_expr_call_migration-20261018170809 --round cmc_emit_expr_call_migration-vc-proving-r1 --target-kind group-development --group call_bounds
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_expr_call_migration-20261018170809 --round cmc_emit_expr_call_migration-vc-proving-r1 --target-kind group-check --group call_bounds
```

Debug script: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_expr_call_migration-20261018170809/_coq_builds/cmc_emit_expr_call_migration-vc-proving-r1/group_01/src/.coq_debug/group_01_call_bounds.v`. Debug, development, and exact are optional proof feedback. `finalize-delivery` seals the two formal files and immediately runs the single mandatory controller group validation.

## Completion

Do not use raw Coq, Dune, Rocq MCP, `Admitted.`, new assumptions, forbidden lemmas, or the forbidden tactics `entailer!` and the bare alias `pre_process` (both are scanned exactly like a forbidden lemma; calls made inside `LLM_pre_process` and `Goal_apply` are unaffected). Repair a recoverable controller failure in this same worker. At the end, success is exactly `status: completed`; `blocked` adds one complete `blocker`. Do not copy version, diff, check status, or controller output.

If an assigned VC exposes an annotation/specification gap outside this group's write boundary, stop proof-only edits and return `blocked` with `blocker.failure_class` exactly `annotation-gap`. Its `vcs` must list every affected exact sealed-manual `name`, `parent`, and `annotation_location`; `message` explains existing premises and the missing conclusion. The controller validates and schedules from those structured VCs.
