# Group worker handoff

Read `.agents/skills/group-worker-proving/SKILL.md`, `.agents/skills/group-worker-proving/workflows/group-worker-proving.md`, and `.agents/skills/group-worker-proving/workflows/commands-and-checks.md` completely. This handoff adds only the current assignment; do not use a parent transcript or sibling output.

## Assignment

- Group: `lookup_bridge`; attempt 1; earlier compact attempts 0
- Difficulty hint: 4/5
- Required suffix for every new or adapted helper: `__lookup_bridge`


### `proof_of_cmc_binding_array_value_return_wit_1` — `aggressive_pre_process`

Prove every listed split goal first, each opening with `LLM_pre_process ltac:(...)` and an explicit closer. Then prove the top-level VC with `aggressive_pre_process` and close each resulting branch with only `Goal_apply <split-goal lemma>` for the corresponding split goal, with no other tactic in the top-level proof. This is a worker proof rule; controller validation does not inspect the spelling of these applications.

Split goals:

  - `proof_of_cmc_binding_array_value_return_wit_1_split_goal_1`: Binding guards select global/local/default code; cm_binding_valid supplies the corresponding slot bound, and f equals the policy-selected function with no fid restriction. For member lookup destruct base under cm_member_valid to obtain CMPtrTy (CMStructTy sid); encoding/well-formedness gives ((encode-1024) mod 1024)-2=sid and member_valid gives both list bounds. Use the owner public nth helpers and rewrite the recursive return. Exact target: (retval = (cm_binding_array_code (policy) (p) (fid_pre) (0) (slot_pre)))

### `proof_of_cmc_binding_array_value_return_wit_2` — `aggressive_pre_process`

Prove every listed split goal first, each opening with `LLM_pre_process ltac:(...)` and an explicit closer. Then prove the top-level VC with `aggressive_pre_process` and close each resulting branch with only `Goal_apply <split-goal lemma>` for the corresponding split goal, with no other tactic in the top-level proof. This is a worker proof rule; controller validation does not inspect the spelling of these applications.

Split goals:

  - `proof_of_cmc_binding_array_value_return_wit_2_split_goal_1`: Binding guards select global/local/default code; cm_binding_valid supplies the corresponding slot bound, and f equals the policy-selected function with no fid restriction. For member lookup destruct base under cm_member_valid to obtain CMPtrTy (CMStructTy sid); encoding/well-formedness gives ((encode-1024) mod 1024)-2=sid and member_valid gives both list bounds. Use the owner public nth helpers and rewrite the recursive return. Exact target: (retval = (cm_binding_array_code (policy) (p) (fid_pre) (1) (slot_pre)))

### `proof_of_cmc_binding_array_value_return_wit_3` — `aggressive_pre_process`

Prove every listed split goal first, each opening with `LLM_pre_process ltac:(...)` and an explicit closer. Then prove the top-level VC with `aggressive_pre_process` and close each resulting branch with only `Goal_apply <split-goal lemma>` for the corresponding split goal, with no other tactic in the top-level proof. This is a worker proof rule; controller validation does not inspect the spelling of these applications.

Split goals:

  - `proof_of_cmc_binding_array_value_return_wit_3_split_goal_1`: Binding guards select global/local/default code; cm_binding_valid supplies the corresponding slot bound, and f equals the policy-selected function with no fid restriction. For member lookup destruct base under cm_member_valid to obtain CMPtrTy (CMStructTy sid); encoding/well-formedness gives ((encode-1024) mod 1024)-2=sid and member_valid gives both list bounds. Use the owner public nth helpers and rewrite the recursive return. Exact target: (0 = (cm_binding_array_code (policy) (p) (fid_pre) (scope_pre) (slot_pre)))

### `proof_of_cmc_member_array_safety_wit_1` — `aggressive_pre_process`

Prove every listed split goal first, each opening with `LLM_pre_process ltac:(...)` and an explicit closer. Then prove the top-level VC with `aggressive_pre_process` and close each resulting branch with only `Goal_apply <split-goal lemma>` for the corresponding split goal, with no other tactic in the top-level proof. This is a worker proof rule; controller validation does not inspect the spelling of these applications.

Split goals:

  - `proof_of_cmc_member_array_safety_wit_1_split_goal_1`: Use the standard pure entailment rule on the framed heap. Substitute result/model and constructor equalities; unfold the relevant safe predicate to obtain summand bounds. Use parent-total bounds or strict child bounds, expand machine limits and close by lia. For modulo use Z.mod_pos_bound with divisor 1024. Exact target: “ (((retval % ( 1024 ) ) - 2 ) <= INT_MAX) ”
  - `proof_of_cmc_member_array_safety_wit_1_split_goal_2`: Use the standard pure entailment rule on the framed heap. Substitute result/model and constructor equalities; unfold the relevant safe predicate to obtain summand bounds. Use parent-total bounds or strict child bounds, expand machine limits and close by lia. For modulo use Z.mod_pos_bound with divisor 1024. Exact target: “ ((INT_MIN) <= ((retval % ( 1024 ) ) - 2 )) ”

### `proof_of_cmc_member_array_return_wit_1` — `aggressive_pre_process`

Prove every listed split goal first, each opening with `LLM_pre_process ltac:(...)` and an explicit closer. Then prove the top-level VC with `aggressive_pre_process` and close each resulting branch with only `Goal_apply <split-goal lemma>` for the corresponding split goal, with no other tactic in the top-level proof. This is a worker proof rule; controller validation does not inspect the spelling of these applications.

Split goals:

  - `proof_of_cmc_member_array_return_wit_1_split_goal_1`: Binding guards select global/local/default code; cm_binding_valid supplies the corresponding slot bound, and f equals the policy-selected function with no fid restriction. For member lookup destruct base under cm_member_valid to obtain CMPtrTy (CMStructTy sid); encoding/well-formedness gives ((encode-1024) mod 1024)-2=sid and member_valid gives both list bounds. Use the owner public nth helpers and rewrite the recursive return. Exact target: ((cm_rep_struct_member_array (structs) ((((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 )) (mid_pre)) = (cm_member_array_code (p) (base) (mid_pre)))

## Write boundary

- Editable top-level proof spans: `proof_of_cmc_binding_array_value_return_wit_1`, `proof_of_cmc_binding_array_value_return_wit_2`, `proof_of_cmc_binding_array_value_return_wit_3`, `proof_of_cmc_member_array_safety_wit_1`, `proof_of_cmc_member_array_return_wit_1`.
- Editable aggressive split-goal proof spans: `proof_of_cmc_binding_array_value_return_wit_1_split_goal_1`, `proof_of_cmc_binding_array_value_return_wit_2_split_goal_1`, `proof_of_cmc_binding_array_value_return_wit_3_split_goal_1`, `proof_of_cmc_member_array_safety_wit_1_split_goal_1`, `proof_of_cmc_member_array_safety_wit_1_split_goal_2`, `proof_of_cmc_member_array_return_wit_1_split_goal_1`.
- Protected LLM_pre_process split blocks: none; their tokens remain `Proof. Abort.`.
- In `group_worker_lib`, append only proved suffixed helpers, token-identical sealed helper copies, and needed official imports.
- All declaration statements, other proof tokens, the manual prelude, and the seed library stay protected.

Whitespace, comments, line endings, and the final newline are formatting. The controller compares protected Rocq tokens, declaration ownership, proof mode, and kernel results. For an aggressive top-level proof, follow the worker rule above and use `Goal_apply` for the split lemmas; controller validation deliberately does not inspect that tactic choice.


## Files

- Copied manual: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_layout_migration-20261015200400/cmc_layout_migration-vc-proving-r1/groups/group_00__lookup_bridge/cmc_layout_migration_proof_manual.v`
- `group_worker_lib`: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_layout_migration-20261015200400/cmc_layout_migration-vc-proving-r1/groups/group_00__lookup_bridge/cmc_layout_migration_lib.v`
- Read-only `formal_case_lib`: `Rocq/examples/QCP_demos_human/cmc_layout_migration_lib.v`
- Frozen helper candidates: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_layout_migration-20261015200400/cmc_layout_migration-vc-proving-r1/public_helper_snapshot.txt` — search by needed helper/predicate names and read only matching declarations; never import this file
- Terminal report: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_layout_migration-20261015200400/rounds/cmc_layout_migration-vc-proving-r1/groups/group_00__lookup_bridge/group_worker_report.json`
- Notes: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_layout_migration-20261015200400/rounds/cmc_layout_migration-vc-proving-r1/groups/group_00__lookup_bridge/group_worker_output.md`. They are optional for ordinary outcomes, but an
  `annotation-gap` blocker requires a non-empty explanation here because the controller preserves this
  exact Markdown as part of the aggregated annotation feedback.
- Previous proving round: none; no reuse note is expected.

The group directory must finish with the copied manual and `group_worker_lib`.

## Planned helpers

- `cm_rep_global_array_nth__lookup_bridge`; public; expected use: Prove forall l i, 0 <= i < Zlength l -> cm_rep_global_array l i = cm_rep_nonzero (cm_global_count (cm_global_at i l)). Induct on l and split i=0. For positive i convert Z.to_nat i to S (Z.to_nat (i-1)), derive tail bound from Zlength_cons and apply IH. Premise comes from cm_binding_valid at scope=0.
- `cm_rep_member_array_nth__lookup_bridge`; public; expected use: Prove forall l i, 0 <= i < Zlength l -> cm_rep_member_array l i = cm_rep_nonzero (cm_slot_count (cm_slot_at i l)). Induct on l and split zero/positive i using Z.to_nat successor conversion. Current valid local/member index supplies the bound.
- `cm_rep_struct_member_array_nth__lookup_bridge`; public; expected use: Prove forall l sid mid, 0 <= sid < Zlength l -> 0 <= mid < Zlength (cm_struct_members (cm_struct_at sid l)) -> cm_rep_struct_member_array l sid mid = cm_rep_nonzero (cm_slot_count (cm_slot_at mid (cm_struct_members (cm_struct_at sid l)))). Induct on l, split sid=0/positive, convert Z.to_nat and use the member-array nth lemma at zero. Both bounds come from cm_member_valid.

`local` stays in this group. A proved `public` helper is promoted by the controller for later rounds. Historical token-identical copies may keep their sealed suffix; adaptations use this group's suffix.

## Commands

Run a needed command unchanged with its bound cwd. Prefer a direct system-terminal call. If terminal operations are available only through `functions.exec`, use a transparent cell that awaits exactly one `tools.exec_command` to launch, or one `tools.write_stdin` to continue the same live session (or the runtime-documented normalized equivalent), and only forwards the result. Pass command/argv, every argument, and cwd unchanged when launching; preserve the exact session handle when continuing. Use a normalized equivalent only if its input shape accepts those values unchanged; never serialize argv into shell text, reparse a rendered command, or add quoting. Do not call another tool in the cell, construct, alter, sequence, wrap, pipe, or background commands. Preserve every outer cell and inner process/session handle until terminal exit; if the bridge yields a running cell, resume only that cell with `functions.wait`.

```text
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-debug --run cmc_layout_migration-20261015200400 --round cmc_layout_migration-vc-proving-r1 --group lookup_bridge
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_layout_migration-20261015200400 --round cmc_layout_migration-vc-proving-r1 --target-kind group-development --group lookup_bridge
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_layout_migration-20261015200400 --round cmc_layout_migration-vc-proving-r1 --target-kind group-check --group lookup_bridge
```

Debug script: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_layout_migration-20261015200400/_coq_builds/cmc_layout_migration-vc-proving-r1/group_00/src/.coq_debug/group_00_lookup_bridge.v`. Debug, development, and exact are optional proof feedback. `finalize-delivery` seals the two formal files and immediately runs the single mandatory controller group validation.

## Completion

Do not use raw Coq, Dune, Rocq MCP, `Admitted.`, new assumptions, forbidden lemmas, or the forbidden tactics `entailer!` and the bare alias `pre_process` (both are scanned exactly like a forbidden lemma; calls made inside `LLM_pre_process` and `Goal_apply` are unaffected). Repair a recoverable controller failure in this same worker. At the end, success is exactly `status: completed`; `blocked` adds one complete `blocker`. Do not copy version, diff, check status, or controller output.

If an assigned VC exposes an annotation/specification gap outside this group's write boundary, stop proof-only edits and return `blocked` with `blocker.failure_class` exactly `annotation-gap`. Its `vcs` must list every affected exact sealed-manual `name`, `parent`, and `annotation_location`; `message` explains existing premises and the missing conclusion. The controller validates and schedules from those structured VCs.
