# annotation handoff

This Markdown file, current files under the main root, and the listed skill docs are the source of truth. Do not use unstated parent-chat context.

## Assignment

- Round: `cmc_copy_bytes_migration-annotation-r1`
- Attempt: `cmc_copy_bytes_migration-annotation-r1-attempt-1` (index 1)
- Main root: `/Users/nizitong/QCP/qcp-binary-democases`
- Terminal report: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_copy_bytes_migration-20261015183239/annotation-attempts/annotation-attempt1/agent_report.json`
- Optional human notes: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_copy_bytes_migration-20261015183239/annotation-attempts/annotation-attempt1/agent_output.md`

## Target files

- C: `QCP_examples/QCP_demos_human/cmc_copy_bytes_migration.c`
- `formal_case_lib` candidate (present under `create` policy; edit it only during an allowed design/proof-helper step): `Rocq/examples/QCP_demos_human/cmc_copy_bytes_migration_lib.v`
- Manual (missing; this is an optional generated artifact, and only controller symbolic execution may create it): `Rocq/examples/QCP_demos_human/cmc_copy_bytes_migration_proof_manual.v`
- Goal/auto/check: `Rocq/examples/QCP_demos_human/cmc_copy_bytes_migration_goal.v`, `Rocq/examples/QCP_demos_human/cmc_copy_bytes_migration_proof_auto.v`, `Rocq/examples/QCP_demos_human/cmc_copy_bytes_migration_goal_check.v`

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

- Session: `cmc_copy_bytes_migration-annotation-agent`
- Iteration: 1

This is the initial iteration. Read annotation-designing completely, follow its linked guides, and inspect the correct/incorrect examples relevant to this case before editing.

Feedback appended for this iteration:

- none (initial annotation iteration)

Required key-point plan: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_copy_bytes_migration-20261015183239/annotation-attempts/annotation-attempt1/annotation_plan.json`

## Problem context

- Problem Statement: Migrate cmc_copy_bytes from C*/HOL to QCP/Rocq while preserving its source contract and runtime C token sequence. Source: /Users/nizitong/cmc/cmc_concrete_copy_bytes.c and .h. Baseline snapshots: /Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_copy_bytes/baseline/.

Read the source contract and relevant definitions. Two logical lists prefix and bytes. Require 0 <= length, ilength bytes = length, 0 <= cursor, cursor + length <= capacity, capacity <= 2147483647. Own cm_uint8_buffer source bytes, destination initialized prefix, and destination uninitialized suffix under separating conjunction. Ensure unchanged cm_uint8_buffer source bytes plus initialized destination prefix ++ bytes through cursor + length and unchanged uninitialized suffix thereafter.

Crucial exact source definition in cmc_rep.c lines 961-965: cm_uint8_buffer p bytes = if bytes = [] then emp else fact(p != 0) ** store_uint8_array p (ilength bytes) bytes. Preserve the empty-source branch allowing null/arbitrary source with no source heap, and preserve explicit non-null requirement for nonempty bytes. Do not add source != data or global non-null/positive-length assumptions. Nonempty source and destination resource separation is already part of the original precondition; this is not a memmove-overlap contract. Preserve source contents in the postcondition, destination prefix, and uninitialized remainder.

Preserve original length==0 early return, index<length loop, local unsigned char byte load, store, increment and trailing semicolon after if. Do not replace runtime by memcpy or helper calls. Author equivalent QCP formal syntax; no user-provided QCP text is frozen. Do not strengthen source preconditions or weaken postconditions to obtain verification.

Previous validated cases: QCP_examples/QCP_demos_human/cmc_write_byte_migration.c and cmc_write_zeroes_migration.c. Prior migration report /Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_write_zeroes/REPORT.md explains byte-array mapping and accounting. Prefer existing list/array library facilities; migrate only missing definitions and useful shared lemmas. If a case-lib definition or helper must be visible to goals/manual, establish the legal Import Coq dependency during annotation. Do not add unused helpers just to generate migration output.

Record any new representation/model definition, case proof, common helper and imports separately; note actual reuse/compilation and all failed checks. Do not alter proof_auto or use manual Admitted/Axiom. Parent will audit accepted artifacts and count final effort after the complete controller run.
- Target Function: cmc_copy_bytes

## Writable formal paths

- `QCP_examples/QCP_demos_human/cmc_copy_bytes_migration.c`
- `Rocq/examples/QCP_demos_human/cmc_copy_bytes_migration_lib.v`
- `Rocq/examples/QCP_demos_human/cmc_copy_bytes_migration_goal.v`
- `Rocq/examples/QCP_demos_human/cmc_copy_bytes_migration_proof_auto.v`
- `Rocq/examples/QCP_demos_human/cmc_copy_bytes_migration_proof_manual.v`
- `Rocq/examples/QCP_demos_human/cmc_copy_bytes_migration_goal_check.v`

Generated files may change only through the exact symbolic-execution command below.

## Agent-written specification

The function spec, internal annotations, and case-lib definitions or lemmas may be
written and revised together in this attempt. Rerun `formal-case-lib-design` and
symexec after changes. A specification change does not end this attempt.

## Commands

```text
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_copy_bytes_migration-20261015183239 --round cmc_copy_bytes_migration-annotation-r1 --target-kind formal-case-lib-design
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases symexec --run cmc_copy_bytes_migration-20261015183239 --round cmc_copy_bytes_migration-annotation-r1
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_copy_bytes_migration-20261015183239 --round cmc_copy_bytes_migration-annotation-r1 --target-kind formal-case-lib
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
