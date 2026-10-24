# annotation handoff

This Markdown file, current files under the main root, and the listed skill docs are the source of truth. Do not use unstated parent-chat context.

## Assignment

- Round: `cmc_emit_resolved_migration-annotation-r1`
- Attempt: `cmc_emit_resolved_migration-annotation-r1-attempt-1` (index 1)
- Main root: `/Users/nizitong/QCP/qcp-binary-democases`
- Terminal report: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_resolved_migration-20261017131857/annotation-attempts/annotation-attempt1/agent_report.json`
- Optional human notes: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_resolved_migration-20261017131857/annotation-attempts/annotation-attempt1/agent_output.md`

## Target files

- C: `QCP_examples/QCP_demos_human/cmc_emit_resolved_migration.c`
- `formal_case_lib` candidate (present under `create` policy; edit it only during an allowed design/proof-helper step): `Rocq/examples/QCP_demos_human/cmc_emit_resolved_migration_lib.v`
- Manual (missing; this is an optional generated artifact, and only controller symbolic execution may create it): `Rocq/examples/QCP_demos_human/cmc_emit_resolved_migration_proof_manual.v`
- Goal/auto/check: `Rocq/examples/QCP_demos_human/cmc_emit_resolved_migration_goal.v`, `Rocq/examples/QCP_demos_human/cmc_emit_resolved_migration_proof_auto.v`, `Rocq/examples/QCP_demos_human/cmc_emit_resolved_migration_goal_check.v`

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

- Session: `cmc_emit_resolved_migration-annotation-agent`
- Iteration: 1

This is the initial iteration. Read annotation-designing completely, follow its linked guides, and inspect the correct/incorrect examples relevant to this case before editing.

Feedback appended for this iteration:

- none (initial annotation iteration)

Required key-point plan: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_resolved_migration-20261017131857/annotation-attempts/annotation-attempt1/annotation_plan.json`

## Problem context

- Problem Statement: Migrate all EIGHT runtime functions from /Users/nizitong/cmc/cmc_concrete_emit_resolved.c and .h to QCP/Rocq, preserving exact contracts and runtime tokens. Fixed baselines: /Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_emit_resolved/baseline.
Reuse the verified cmc_emit_core_migration_lib and its dependencies without modifying them. Target carries the identical existing cm_emitter struct declaration and includes frozen cmc_layout_migration_abi.h. Re-declare seven core C helpers (cm_emit, cm_emit_normalize/load/store/fp_address/temp_store/temp_load) with EXACT existing verified contracts, whitespace/binder renaming only. No old auto/manual imports; prove all eight wrapper implementations.
New concrete definitions from cmc_concrete_defs.c:465-486: cm_patch_inst policy p (TVMInst op imm) = TVMInst op (if tvm_opcode_code op = 22 then cm_function_pc policy p imm else imm); cm_patch_code is its list map; cm_resolved_emitter_rep policy p emitter out capacity resolved_prefix = exists raw_prefix, patch(raw_prefix)=resolved_prefix and cm_emitter_rep on ops/imms projections of RAW prefix. Retain existing total cm_lookup_policy and cm_function_pc from counts; no alternative PC function or abstract patch parameters.
CRITICAL: raw buffer stores function identifiers for CALL; resolved view is the logical map, NOT already patched physical bytes. cm_emit_resolved_call writes function_id and ensures abstract appended CALL(cm_function_pc p function_id), for ALL signed int function_id including negative/out of range. No validity/range, readiness, program-wf or PC representability premise may be added. Ordinary cm_emit_resolved requires op/code equality, opcode code !=22, length done+1<=capacity and resolved emitter; ensures exact singleton append.
Normalize/load/store retain only original type-code-wf and encoded equality, exact fragment-length bound and resolved representation. FP-address retains exact length bound/fragment. Temp load/store retain original eight pure facts in BOTH pre and post, additional PRE fragment-capacity bound, complete function_context ownership and resolved emitter; same f/function lookup policy, no new fid bounds. Ensure exact source fragment appended. Reuse established temp/core size bridge; do not re-prove helper implementation.
Prove patch-code length and append, and unchanged non-CALL fragments as needed using core opcode/fragments. In source file eighteen private PROOF support declarations are case proof; added target common models/lemmas measured separately. No axioms/Admitted in new manual/library. Record checks/failures/iterations in ordinary owner output. Main audits semantic mapping, runtime and dependency hashes, compares costs, and updates skill ONLY after controller done.

## Writable formal paths

- `QCP_examples/QCP_demos_human/cmc_emit_resolved_migration.c`
- `Rocq/examples/QCP_demos_human/cmc_emit_resolved_migration_lib.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_resolved_migration_goal.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_resolved_migration_proof_auto.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_resolved_migration_proof_manual.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_resolved_migration_goal_check.v`

Generated files may change only through the exact symbolic-execution command below.

## Agent-written specification

The function spec, internal annotations, and case-lib definitions or lemmas may be
written and revised together in this attempt. Rerun `formal-case-lib-design` and
symexec after changes. A specification change does not end this attempt.

## Commands

```text
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_resolved_migration-20261017131857 --round cmc_emit_resolved_migration-annotation-r1 --target-kind formal-case-lib-design
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases symexec --run cmc_emit_resolved_migration-20261017131857 --round cmc_emit_resolved_migration-annotation-r1
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_resolved_migration-20261017131857 --round cmc_emit_resolved_migration-annotation-r1 --target-kind formal-case-lib
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
