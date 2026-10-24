# annotation handoff

This Markdown file, current files under the main root, and the listed skill docs are the source of truth. Do not use unstated parent-chat context.

## Assignment

- Round: `cmc_function_pc_total_migration-annotation-r1`
- Attempt: `cmc_function_pc_total_migration-annotation-r1-attempt-1` (index 1)
- Main root: `/Users/nizitong/QCP/qcp-binary-democases`
- Terminal report: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_function_pc_total_migration-20261016090222/annotation-attempts/annotation-attempt1/agent_report.json`
- Optional human notes: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_function_pc_total_migration-20261016090222/annotation-attempts/annotation-attempt1/agent_output.md`

## Target files

- C: `QCP_examples/QCP_demos_human/cmc_function_pc_total_migration.c`
- `formal_case_lib` candidate (present under `create` policy; edit it only during an allowed design/proof-helper step): `Rocq/examples/QCP_demos_human/cmc_function_pc_total_migration_lib.v`
- Manual (missing; this is an optional generated artifact, and only controller symbolic execution may create it): `Rocq/examples/QCP_demos_human/cmc_function_pc_total_migration_proof_manual.v`
- Goal/auto/check: `Rocq/examples/QCP_demos_human/cmc_function_pc_total_migration_goal.v`, `Rocq/examples/QCP_demos_human/cmc_function_pc_total_migration_proof_auto.v`, `Rocq/examples/QCP_demos_human/cmc_function_pc_total_migration_goal_check.v`

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

- Session: `cmc_function_pc_total_migration-annotation-agent`
- Iteration: 1

This is the initial iteration. Read annotation-designing completely, follow its linked guides, and inspect the correct/incorrect examples relevant to this case before editing.

Feedback appended for this iteration:

- none (initial annotation iteration)

Required key-point plan: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_function_pc_total_migration-20261016090222/annotation-attempts/annotation-attempt1/annotation_plan.json`

## Problem context

- Problem Statement: Migrate the entire /Users/nizitong/cmc/cmc_concrete_function_pc_total.c from C*/HOL to QCP/Rocq, both runtime bodies cmc_function_prefix_total (static) and cmc_function_pc_total, preserving runtime tokens and every original contract condition. Baseline source/header and runtime are in /Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_function_pc_total/baseline. Read actual C* contracts/proofs. Canonical target QCP_examples/QCP_demos_human/cmc_function_pc_total_migration.c.
Reuse verified cmc_counts_migration_lib.v, layout/copy_bytes pure dependencies and cmc_layout_migration_abi.h without changing their bytes. Import the exact previously verified cmc_function_code_count contract from cmc_counts_migration.c; do not reprove its implementation or import old auto/manual files. Preserve the same universally quantified lookup policy and codegen obligations record, all resources and pure facts. Do not add target bounds: target is arbitrary signed long long; negative and oversized targets traverse to the end. Logical target-index is Z subtraction, not a new runtime arithmetic operation.
The source contracts require cm_concrete_functions_ready and cm_concrete_code_ready, not yet in counts lib. Translate their complete definitions (counts.c lines 5444 onward; compile_ready.c; code_ready.c structs_ready) retaining every conjunct. Source readiness uses ilength(cm_emit_stmt ...); the unconditional source cm_stmt_code_length in cmc_codegen.c and its use in cmc_concrete_function_ready.c lines 217-234 justify normalizing this expression to cm_stmt_code_count. Document this source-proved normalization and do not claim Rocq verification of the full emitter semantics. Other model predicates already exist in verified counts/layout libraries. Reuse rather than duplicate.
Migrate exported cm_function_prefix_total_bounds with its original unconditional statement for arbitrary remaining, using needed nonnegativity bridges; do not silently restrict to 0<=remaining<=length or merely valid function IDs. Count these new public definitions and proved lemmas separately. Helper contracts and readiness assumptions must remain equivalent, no weakening Ensure or strengthening Require for convenience. No new Admitted/Axiom/Parameter in authored manual/lib. Generated auto witnesses retain QCP trust boundary and will be reported separately. Keep runtime static qualifier and int/long-long comparison. Whole-file coverage is two functions, zero forward declarations. Main will audit full contracts, runtime identity, actual library reuse and incremental public costs after controller done. Skill updates only after complete verification. Record failed checks and semantic decisions in permitted reports; follow role ownership boundaries.
- Reference Case Hints: /Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_counts/REPORT.md

## Writable formal paths

- `QCP_examples/QCP_demos_human/cmc_function_pc_total_migration.c`
- `Rocq/examples/QCP_demos_human/cmc_function_pc_total_migration_lib.v`
- `Rocq/examples/QCP_demos_human/cmc_function_pc_total_migration_goal.v`
- `Rocq/examples/QCP_demos_human/cmc_function_pc_total_migration_proof_auto.v`
- `Rocq/examples/QCP_demos_human/cmc_function_pc_total_migration_proof_manual.v`
- `Rocq/examples/QCP_demos_human/cmc_function_pc_total_migration_goal_check.v`

Generated files may change only through the exact symbolic-execution command below.

## Agent-written specification

The function spec, internal annotations, and case-lib definitions or lemmas may be
written and revised together in this attempt. Rerun `formal-case-lib-design` and
symexec after changes. A specification change does not end this attempt.

## Commands

```text
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_function_pc_total_migration-20261016090222 --round cmc_function_pc_total_migration-annotation-r1 --target-kind formal-case-lib-design
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases symexec --run cmc_function_pc_total_migration-20261016090222 --round cmc_function_pc_total_migration-annotation-r1
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_function_pc_total_migration-20261016090222 --round cmc_function_pc_total_migration-annotation-r1 --target-kind formal-case-lib
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
