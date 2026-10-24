# Annotation retry handoff

This is annotation iteration 2 in the run's single persistent annotation-agent session. Read the sealed failed VCs, edit the current annotation, run symbolic execution, and compare every old VC with the current manual.

## Assignment

- Session: `cmc_compile_migration-annotation-agent`
- Round: `cmc_compile_migration-annotation-r2`
- Attempt: `cmc_compile_migration-annotation-r2-attempt-1`
- Retry reason: `annotation-blocked`
- Main root: `/Users/nizitong/QCP/qcp-binary-democases`
- Terminal report: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_compile_migration-20261019230022/annotation-attempts/annotation-attempt2/agent_report.json`
- Human notes: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_compile_migration-20261019230022/annotation-attempts/annotation-attempt2/agent_output.md`
- Required key-point plan: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_compile_migration-20261019230022/annotation-attempts/annotation-attempt2/annotation_plan.json`

## Target files

- C: `QCP_examples/QCP_demos_human/cmc_compile_migration.c`
- `formal_case_lib` candidate (present under `create` policy; edit it only during an allowed design/proof-helper step): `Rocq/examples/QCP_demos_human/cmc_compile_migration_lib.v`
- Manual (missing; this is an optional generated artifact, and only controller symbolic execution may create it): `Rocq/examples/QCP_demos_human/cmc_compile_migration_proof_manual.v`
- Goal/auto/check: `Rocq/examples/QCP_demos_human/cmc_compile_migration_goal.v`, `Rocq/examples/QCP_demos_human/cmc_compile_migration_proof_auto.v`, `Rocq/examples/QCP_demos_human/cmc_compile_migration_goal_check.v`

## Original blocker evidence

- `annotation` / `cmc_compile_migration-annotation-r1-attempt-1`: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_compile_migration-20261019230022/annotation-attempts/annotation-attempt1/agent_report.json`; `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_compile_migration-20261019230022/annotation-attempts/annotation-attempt1/annotation_plan.json`; `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_compile_migration-20261019230022/annotation-attempts/annotation-attempt1/agent_output.md`

Previous annotation attempt artifacts:

- `cmc_compile_migration-annotation-r1-attempt-1`: report `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_compile_migration-20261019230022/annotation-attempts/annotation-attempt1/agent_report.json`; notes `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_compile_migration-20261019230022/annotation-attempts/annotation-attempt1/agent_output.md`

Controller-recorded blocker details:

- {"failure_class": "dependency-gap", "kind": "missing-verified-semantic-dependency", "message": "Before VC generation, the exact cm_output_ok success contract requires actual cm_source_terminates (source cmc_lang.c:4296), tvm_terminates (tvm_model.c:1295), cm_output_decodes (cmc_rep.c:1966), and cmc_compile_success_bridge (cmc.c:95) backed by cmc_preservation (cmc_correct.c:145). All are absent from Rocq/**/*.v. The existing counts/readiness/emitter libraries establish code/data models and safety, not the source-to-TVM termination simulation. No verified semantic dependency is available to express and discharge the unchanged success clause; no VCs exist yet. Exact source locations, dependency closure, and recovery order are recorded in agent_output.md.", "repair_boundary": "Supply and verify shared source/TVM operational semantics, concrete codegen obligations/object decoding, and compiler preservation support before resuming this same annotation owner. Current annotation writable topology is only the target C and one canonical case-lib; this role cannot write shared/second libraries or proof bodies. Do not weaken Ensure, strengthen Require with preservation, introduce arbitrary semantic Parameters/Axioms/Admitted, or treat unverified prerequisites as proved.", "vcs": []}

## Failed VCs

- none

## Previous VC changes

- none

## Rules to reload

The annotation agent must completely reload annotation-designing on every appended iteration, then follow all linked rules and inspect the original blocker evidence, sealed manuals, and current main-root files above.

- `.agents/skills/verification-orchestrator/SKILL.md`
- `.agents/skills/verification-orchestrator/workflows/state-handoffs-and-reports.md`
- `.agents/skills/verification-orchestrator/workflows/paths-and-commands.md`
- `.agents/skills/annotation-designing/SKILL.md`
- `.agents/skills/annotation-designing/workflows/annotation-designing.md`

## Writable formal paths

- `QCP_examples/QCP_demos_human/cmc_compile_migration.c`
- `Rocq/examples/QCP_demos_human/cmc_compile_migration_lib.v`
- `Rocq/examples/QCP_demos_human/cmc_compile_migration_goal.v`
- `Rocq/examples/QCP_demos_human/cmc_compile_migration_proof_auto.v`
- `Rocq/examples/QCP_demos_human/cmc_compile_migration_proof_manual.v`
- `Rocq/examples/QCP_demos_human/cmc_compile_migration_goal_check.v`

Generated files may change only through the exact symbolic-execution command below.

## Agent-written specification

The function spec, internal annotations, and case-lib definitions or lemmas may be
written and revised together in this attempt. Rerun `formal-case-lib-design` and
symexec after changes. A specification change does not end this attempt.

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

## Commands

```text
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_compile_migration-20261019230022 --round cmc_compile_migration-annotation-r2 --target-kind formal-case-lib-design
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases symexec --run cmc_compile_migration-20261019230022 --round cmc_compile_migration-annotation-r2
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_compile_migration-20261019230022 --round cmc_compile_migration-annotation-r2 --target-kind formal-case-lib
```

The standalone design check may be rerun after each specification or case-lib change and does not require generated goals. The later formal-case-lib Coq command uses the controller's single skinny-build plan: it stages only the exact current-case dependency closure, loads or builds its current prerequisites from the content-addressed cache, and reads fixed dependency `.vo` files from the selected sealed base. Before this local check, the controller asks the selected backend to prepare the exact case-lib target. A dependency that is merely unbuilt is therefore not an annotation defect.

The dependency graph comes only from the selected backend's exact target; the agent never observes, supplies, or
expands build targets. Do not copy selected-base output, dependency sources/artifacts, or another `_coq_builds` scope.

## Completion

Function specs, internal predicates, body annotations, case-lib definitions and lemmas, and `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_compile_migration-20261019230022/annotation-attempts/annotation-attempt2/annotation_plan.json` may change together when the spec is agent-written or after `unfreeze`. After every symexec, fill `vc_comparisons` from the exact old and current statements. Continue editing while a judgement is `unprovable` or `moved`; submit only when every failed VC is `provable`. Do not edit the proof manual or write proofs. Success contains only `status: completed`. Notes are optional.
