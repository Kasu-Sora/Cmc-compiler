# annotation handoff

This Markdown file, current files under the main root, and the listed skill docs are the source of truth. Do not use unstated parent-chat context.

## Assignment

- Round: `cmc_emit_expr_call_migration-annotation-r1`
- Attempt: `cmc_emit_expr_call_migration-annotation-r1-attempt-1` (index 1)
- Main root: `/Users/nizitong/QCP/qcp-binary-democases`
- Terminal report: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_expr_call_migration-20261018170809/annotation-attempts/annotation-attempt1/agent_report.json`
- Optional human notes: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_expr_call_migration-20261018170809/annotation-attempts/annotation-attempt1/agent_output.md`

## Target files

- C: `QCP_examples/QCP_demos_human/cmc_emit_expr_call_migration.c`
- `formal_case_lib` candidate (present under `create` policy; edit it only during an allowed design/proof-helper step): `Rocq/examples/QCP_demos_human/cmc_emit_expr_call_migration_lib.v`
- Manual (missing; this is an optional generated artifact, and only controller symbolic execution may create it): `Rocq/examples/QCP_demos_human/cmc_emit_expr_call_migration_proof_manual.v`
- Goal/auto/check: `Rocq/examples/QCP_demos_human/cmc_emit_expr_call_migration_goal.v`, `Rocq/examples/QCP_demos_human/cmc_emit_expr_call_migration_proof_auto.v`, `Rocq/examples/QCP_demos_human/cmc_emit_expr_call_migration_goal_check.v`

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

- Session: `cmc_emit_expr_call_migration-annotation-agent`
- Iteration: 1

This is the initial iteration. Read annotation-designing completely, follow its linked guides, and inspect the correct/incorrect examples relevant to this case before editing.

Feedback appended for this iteration:

- none (initial annotation iteration)

Required key-point plan: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_expr_call_migration-20261018170809/annotation-attempts/annotation-attempt1/annotation_plan.json`

## Problem context

- Problem Statement: Migrate ENTIRE runtime file /Users/nizitong/cmc/cmc_concrete_emit_expr_call.c C*/HOL -> QCP/Rocq. Exactly 3 runtime bodies: static cm_emit_args_reload_plan, static cm_emit_args_store_plan, cm_emit_call_expr; 46 runtime physical lines. Frozen source, extracted runtime and reused dependency snapshots: /Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_emit_expr_call/baseline. Read full original .c/.h plus exact source model definitions. No user QCP formal spec supplied. Preserve runtime tokens and ABI and every original pure fact/resource in pre/post. Never change earlier verified files, strengthen inputs or weaken postconditions.

Preserve all source bounds including slot, scratch, temp, temp_limit, code pc/end, temp_offset; wf/typed/count facts; total function lookup with existing cm_lookup_policy/cm_codegen_obligations; slots/member/struct/global/string safety and global size; exact code prefix consumption/append with arbitrary tail; full program/function/expression/argument resources. call covers source kind8 and both lvalue branches including empty code for lvalue. No added fid range or restriction to simple argument expressions. Inspect all three exact source contracts, source call header's cm_emit_expr prototype and .c/.h agreement.

Reuse prior layout/counts/count-context/plan/ast/leaf/var/simple models and lemmas wherever applicable. Reproduce used previously verified helpers' BODY contracts (not possibly weaker headers), preserve transitive libs unchanged; no imports of previous manual/auto. New general expression code equations may be necessary: current libs do NOT implement general cm_emit_expr_pair/cm_expr_code_for. Translate required mathematical source semantics faithfully (including recursive argument store/reload), not uninterpreted emitter outputs, dummy values or new axioms. If full model closure is necessary include and measure it explicitly. Source .c uses an external cm_emit_expr prototype whose implementation is not yet migrated: retain this EXACT original module dependency and explicitly report it as a pending implementation proof, not a freshly verified helper. This modular contract assumption already exists in source and must not be expanded. The requested file's three bodies must actually be verified; do not pretend the general recursive emitter implementation was verified.

Create precise source-to-target model/contract mapping and identify all new shared definitions/lemmas vs source-private proof helpers. Preserve existing lookup/codegen parameterization without adding arbitrary codegen assumptions. Logical alternative views must have exact domain coverage. No Admitted/Axiom/Parameter in new handwritten model/proof. Record design/symexec/post-library attempts and repairs in agent_output. Annotation owner controls C/lib/plan; manual read-only. Main replays C*, audits semantic equivalence and measures final artifacts, updates skill only after controller done. QCP main must use controller actions and role boundaries.

## Writable formal paths

- `QCP_examples/QCP_demos_human/cmc_emit_expr_call_migration.c`
- `Rocq/examples/QCP_demos_human/cmc_emit_expr_call_migration_lib.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_expr_call_migration_goal.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_expr_call_migration_proof_auto.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_expr_call_migration_proof_manual.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_expr_call_migration_goal_check.v`

Generated files may change only through the exact symbolic-execution command below.

## Agent-written specification

The function spec, internal annotations, and case-lib definitions or lemmas may be
written and revised together in this attempt. Rerun `formal-case-lib-design` and
symexec after changes. A specification change does not end this attempt.

## Commands

```text
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_expr_call_migration-20261018170809 --round cmc_emit_expr_call_migration-annotation-r1 --target-kind formal-case-lib-design
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases symexec --run cmc_emit_expr_call_migration-20261018170809 --round cmc_emit_expr_call_migration-annotation-r1
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_expr_call_migration-20261018170809 --round cmc_emit_expr_call_migration-annotation-r1 --target-kind formal-case-lib
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
