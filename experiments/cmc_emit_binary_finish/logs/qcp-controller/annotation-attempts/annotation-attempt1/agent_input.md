# annotation handoff

This Markdown file, current files under the main root, and the listed skill docs are the source of truth. Do not use unstated parent-chat context.

## Assignment

- Round: `cmc_emit_binary_finish_migration-annotation-r1`
- Attempt: `cmc_emit_binary_finish_migration-annotation-r1-attempt-1` (index 1)
- Main root: `/Users/nizitong/QCP/qcp-binary-democases`
- Terminal report: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_binary_finish_migration-20261018181500/annotation-attempts/annotation-attempt1/agent_report.json`
- Optional human notes: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_binary_finish_migration-20261018181500/annotation-attempts/annotation-attempt1/agent_output.md`

## Target files

- C: `QCP_examples/QCP_demos_human/cmc_emit_binary_finish_migration.c`
- `formal_case_lib` candidate (present under `create` policy; edit it only during an allowed design/proof-helper step): `Rocq/examples/QCP_demos_human/cmc_emit_binary_finish_migration_lib.v`
- Manual (missing; this is an optional generated artifact, and only controller symbolic execution may create it): `Rocq/examples/QCP_demos_human/cmc_emit_binary_finish_migration_proof_manual.v`
- Goal/auto/check: `Rocq/examples/QCP_demos_human/cmc_emit_binary_finish_migration_goal.v`, `Rocq/examples/QCP_demos_human/cmc_emit_binary_finish_migration_proof_auto.v`, `Rocq/examples/QCP_demos_human/cmc_emit_binary_finish_migration_goal_check.v`

## Rules to read

- `.agents/skills/verification-orchestrator/SKILL.md`
- `.agents/skills/verification-orchestrator/workflows/state-handoffs-and-reports.md`
- `.agents/skills/verification-orchestrator/workflows/paths-and-commands.md`
- `.agents/skills/annotation-designing/SKILL.md`
- `.agents/skills/annotation-designing/workflows/annotation-designing.md`

## Previous attempts

- none

Required lessons:

- none

## Controller command execution contract

Run every listed controller command unchanged with its bound cwd. Prefer a direct system-terminal call. If the runtime
exposes terminal tools only through `functions.exec`, use a transparent bridge. Each bridge cell may await exactly one
terminal operation: `tools.exec_command` to launch the command, or `tools.write_stdin` to continue the same live
session (or the runtime-documented normalized name for that same terminal operation), and may only forward its result.
Pass the rendered command/argv, every argument, and cwd unchanged when launching, and preserve the exact session
handle when continuing. A normalized equivalent is permitted only when its input shape accepts those values unchanged;
never serialize an argv array into shell text, reparse a rendered command, or add quoting.

Do not call a second tool in a bridge cell, add JavaScript/Python orchestration, construct, alter, sequence,
parallelize, or interpret commands, wrap them in a generated shell/PowerShell/Python script or another `uv run`, use
`sh -c`, command substitution, a pipeline or background execution, or invoke another wrapper. Never recreate
controller behavior with a custom command or script.

Preserve every outer cell and inner process/session handle until the actual command reaches a terminal exit. If a
transparent bridge yields a running `functions.exec` cell, resume only that cell with `functions.wait` until its one
nested terminal operation returns. Empty output, an initial-yield response, and outer-cell messages such as
`Script completed` do not prove that the controller command finished. Record a check as passed only after the terminal
process exits with code 0 and the controller JSON reports
`status: passed`.


## Persistent annotation agent

- Session: `cmc_emit_binary_finish_migration-annotation-agent`
- Iteration: 1

This is the initial iteration. Read annotation-designing completely, follow its linked guides, and inspect the correct/incorrect examples relevant to this case before editing.

Feedback appended for this iteration:

- none (initial annotation iteration)

Required key-point plan: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_binary_finish_migration-20261018181500/annotation-attempts/annotation-attempt1/annotation_plan.json`

## Problem context

- Problem Statement: Migrate the ENTIRE original /Users/nizitong/cmc/cmc_concrete_emit_binary_finish.c from C*/HOL to QCP/Rocq, preserving exact runtime tokens and original BODY contract meaning. Source/header snapshots and runtime extraction: /Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_emit_binary_finish/baseline/. Three bodies must be verified: static cm_pointer_scale_value, static cm_emit_binary_generic_fragment, cm_emit_binary_finish_plan. Source specification attributes are reference semantics, not user-authored QCP freeze spec. Translate all pure facts and full resource ownership, exact code-prefix consumption/done append and arbitrary tail. Preserve arbitrary int op including default opcode mapping, original type/slot/pointer bounds, total fid lookup, full program/function/both expression resources. Do not add wf_program, op range, binary expression well-typedness, positive scale, pointer argument kind, fid range, or any new input restriction absent in original contract. Preserve all original postcondition facts. Existing policy/cg parameterization stays as previously migrated.
Use existing cmc_layout_migration_abi.h plus exact cm_emitter declaration. Runtime source skeleton already contains all unmodified bodies. Import verified cmc_emit_expr_call_migration_lib for cm_pointer_scale and cm_binary_finish_code, and existing definitions/lemmas from its transitive closure. Do not duplicate/redefine these models or modify prior verified libraries. Reuse pointer encoding lemmas (e.g. counts cm_pointer_encode__expression_add_safety), layout/type facts when applicable. Verify helpers through previously accepted BODY contracts, not possibly stronger/weaker header contracts. Helper functions: cm_expr_type_code_context and cm_type_size_value in emit_expr_leaf, cmc_pointee and cmc_is_pointer_value in layout, cmc_binary_opcode in emit_core, cm_emit_plan and cm_emit_temp_load_plan in emit_plan. These are all previously verified; do not import old manual/auto. Read original bodies/contracts if translating bridging assumptions.
No unchecked axioms/admitted/parameters in new case lib or manual; QCP generated automatic witnesses have separately disclosed trust. General expression emitter is not a runtime dependency of this unit despite sharing its code model library. Final output should preserve header/body equivalence and three-function coverage. Record actual design/symexec/post-lib invocation counts and failures, and short real repair reasons in agent_output.md for effort accounting. Stop all writes after delivery. Main performs provenance/semantic audit, effort report and skill update only after controller done.

## Writable formal paths

- `QCP_examples/QCP_demos_human/cmc_emit_binary_finish_migration.c`
- `Rocq/examples/QCP_demos_human/cmc_emit_binary_finish_migration_lib.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_binary_finish_migration_goal.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_binary_finish_migration_proof_auto.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_binary_finish_migration_proof_manual.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_binary_finish_migration_goal_check.v`

Generated files may change only through the exact symbolic-execution command below.

## Agent-written specification

The function spec, internal annotations, and case-lib definitions or lemmas may be
written and revised together in this attempt. Rerun `formal-case-lib-design` and
symexec after changes. A specification change does not end this attempt.

## Commands

```text
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_binary_finish_migration-20261018181500 --round cmc_emit_binary_finish_migration-annotation-r1 --target-kind formal-case-lib-design
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases symexec --run cmc_emit_binary_finish_migration-20261018181500 --round cmc_emit_binary_finish_migration-annotation-r1
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_binary_finish_migration-20261018181500 --round cmc_emit_binary_finish_migration-annotation-r1 --target-kind formal-case-lib
```

The standalone design check may be rerun after each specification or case-lib change and does not require generated goals. The later formal-case-lib Coq command uses the controller's single skinny-build plan: it stages only the exact current-case dependency closure, loads or builds its current prerequisites from the content-addressed cache, and reads fixed dependency `.vo` files from the selected sealed base. Before this local check, the controller asks the selected backend to prepare the exact case-lib target. A dependency that is merely unbuilt is therefore not an annotation defect.

The dependency graph comes only from the selected backend's exact target; the agent never observes, supplies, or
expands build targets. Do not copy selected-base output, dependency sources/artifacts, or another `_coq_builds` scope.

## Completion

Write and revise the function spec, internal predicates, body annotations, case-lib definitions and lemmas, and the key-point plan together as allowed above. The first attempt keeps `vc_comparisons` empty.
Use the listed commands when useful for feedback; controller acceptance reruns every mandatory machine check. Write
a success report containing only `status: completed`. On the first `symexec`
`tool` failure, keep this claimed attempt and every formal byte unchanged and
rerun the exact same controller command once; do not write a terminal report yet.
Only a second identical tool failure may produce a blocked result. Such a result adds one
complete `blocker`. Do not copy changed paths, version, or check status into the report.
