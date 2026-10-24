# annotation handoff

This Markdown file, current files under the main root, and the listed skill docs are the source of truth. Do not use unstated parent-chat context.

## Assignment

- Round: `cmc_count_context_migration-annotation-r1`
- Attempt: `cmc_count_context_migration-annotation-r1-attempt-1` (index 1)
- Main root: `/Users/nizitong/QCP/qcp-binary-democases`
- Terminal report: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_count_context_migration-20261016020312/annotation-attempts/annotation-attempt1/agent_report.json`
- Optional human notes: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_count_context_migration-20261016020312/annotation-attempts/annotation-attempt1/agent_output.md`

## Target files

- C: `QCP_examples/QCP_demos_human/cmc_count_context_migration.c`
- `formal_case_lib` candidate (present under `create` policy; edit it only during an allowed design/proof-helper step): `Rocq/examples/QCP_demos_human/cmc_count_context_migration_lib.v`
- Manual (missing; this is an optional generated artifact, and only controller symbolic execution may create it): `Rocq/examples/QCP_demos_human/cmc_count_context_migration_proof_manual.v`
- Goal/auto/check: `Rocq/examples/QCP_demos_human/cmc_count_context_migration_goal.v`, `Rocq/examples/QCP_demos_human/cmc_count_context_migration_proof_auto.v`, `Rocq/examples/QCP_demos_human/cmc_count_context_migration_goal_check.v`

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

- Session: `cmc_count_context_migration-annotation-agent`
- Iteration: 1

This is the initial iteration. Read annotation-designing completely, follow its linked guides, and inspect the correct/incorrect examples relevant to this case before editing.

Feedback appended for this iteration:

- none (initial annotation iteration)

Required key-point plan: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_count_context_migration-20261016020312/annotation-attempts/annotation-attempt1/annotation_plan.json`

## Problem context

- Problem Statement: Migrate all four runtime function bodies of /Users/nizitong/cmc/cmc_concrete_count_context.c from C*/HOL to QCP/Rocq, preserving original runtime tokens and contract meaning: cm_expr_type_code_context, cm_expr_lvalue_count_context, cm_expr_rvalue_count_context, cm_stmt_code_count_context. Source snapshots and extracted runtime are in /Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_count_context/baseline. Source contracts and proofs must be read from the actual C* source, not inferred from names. Canonical target: QCP_examples/QCP_demos_human/cmc_count_context_migration.c.
Reuse the fully verified cmc_counts_migration_lib.v and its layout/copy_bytes pure-library dependencies, plus cmc_layout_migration_abi.h. Preserve their bytes. The existing library contains program/function context predicates, AST representation, count models, wellformedness, representability, and proven bridges. Do not duplicate these definitions. Create a case library only for genuinely necessary new proved bridges; an import-only case library is acceptable if the workflow requires it. Avoid unnecessarily restating prior lemmas.
Import exact previously verified helper contracts for cm_expr_lvalue_count, cm_expr_rvalue_count and cmc_stmt_code_count from cmc_counts_migration.c; no need to reprove their bodies or import their auto/manual proof files. Their integration annotations will be counted separately. Keep full program/function context resources and all original pure facts in wrapper pre/postconditions. Preserve f = total function lookup with the same universally quantified cm_lookup_policy; do not introduce a new fid bound. Keep the statement loop_ parameter and original return/stack/count facts. Type-code context must retain only its original expr representation and uninitialized output requirements.
The previous counts library uses an explicit universally quantified cm_codegen_obligations record for four irrelevant emitter/TVM admissibility predicates, with documented source instances. Reuse that same semantic boundary and all original conjunctions; do not weaken wellformedness or claim a new concrete emitter/TVM instantiation theorem. Keep the exact mathematical return value and i32 bounds.
No new Admitted/Axiom/Parameter in authored manual or library. Generated auto witnesses follow QCP tool trust semantics and are reported separately. Do not weaken Ensure, strengthen Require, change runtime code or modify accepted dependency libraries for convenience. Build the necessary open/close intermediate assertions for the existing context predicates. Record substantive failed checks and semantic decisions in your permitted report. Main will audit contracts, actual dependency reuse, annotation/proof effort and incremental shared cost, and update migration skill only after complete final verification. Follow repository controller and role ownership boundaries.
- Reference Case Hints: /Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_counts/REPORT.md

## Writable formal paths

- `QCP_examples/QCP_demos_human/cmc_count_context_migration.c`
- `Rocq/examples/QCP_demos_human/cmc_count_context_migration_lib.v`
- `Rocq/examples/QCP_demos_human/cmc_count_context_migration_goal.v`
- `Rocq/examples/QCP_demos_human/cmc_count_context_migration_proof_auto.v`
- `Rocq/examples/QCP_demos_human/cmc_count_context_migration_proof_manual.v`
- `Rocq/examples/QCP_demos_human/cmc_count_context_migration_goal_check.v`

Generated files may change only through the exact symbolic-execution command below.

## Agent-written specification

The function spec, internal annotations, and case-lib definitions or lemmas may be
written and revised together in this attempt. Rerun `formal-case-lib-design` and
symexec after changes. A specification change does not end this attempt.

## Commands

```text
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_count_context_migration-20261016020312 --round cmc_count_context_migration-annotation-r1 --target-kind formal-case-lib-design
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases symexec --run cmc_count_context_migration-20261016020312 --round cmc_count_context_migration-annotation-r1
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_count_context_migration-20261016020312 --round cmc_count_context_migration-annotation-r1 --target-kind formal-case-lib
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
