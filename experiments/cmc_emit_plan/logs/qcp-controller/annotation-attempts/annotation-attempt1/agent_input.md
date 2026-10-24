# annotation handoff

This Markdown file, current files under the main root, and the listed skill docs are the source of truth. Do not use unstated parent-chat context.

## Assignment

- Round: `cmc_emit_plan_migration-annotation-r1`
- Attempt: `cmc_emit_plan_migration-annotation-r1-attempt-1` (index 1)
- Main root: `/Users/nizitong/QCP/qcp-binary-democases`
- Terminal report: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_plan_migration-20261017135154/annotation-attempts/annotation-attempt1/agent_report.json`
- Optional human notes: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_plan_migration-20261017135154/annotation-attempts/annotation-attempt1/agent_output.md`

## Target files

- C: `QCP_examples/QCP_demos_human/cmc_emit_plan_migration.c`
- `formal_case_lib` candidate (present under `create` policy; edit it only during an allowed design/proof-helper step): `Rocq/examples/QCP_demos_human/cmc_emit_plan_migration_lib.v`
- Manual (missing; this is an optional generated artifact, and only controller symbolic execution may create it): `Rocq/examples/QCP_demos_human/cmc_emit_plan_migration_proof_manual.v`
- Goal/auto/check: `Rocq/examples/QCP_demos_human/cmc_emit_plan_migration_goal.v`, `Rocq/examples/QCP_demos_human/cmc_emit_plan_migration_proof_auto.v`, `Rocq/examples/QCP_demos_human/cmc_emit_plan_migration_goal_check.v`

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

- Session: `cmc_emit_plan_migration-annotation-agent`
- Iteration: 1

This is the initial iteration. Read annotation-designing completely, follow its linked guides, and inspect the correct/incorrect examples relevant to this case before editing.

Feedback appended for this iteration:

- none (initial annotation iteration)

Required key-point plan: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_plan_migration-20261017135154/annotation-attempts/annotation-attempt1/annotation_plan.json`

## Problem context

- Problem Statement: Migrate ALL EIGHT runtime wrappers of /Users/nizitong/cmc/cmc_concrete_emit_plan.c from C*/HOL to QCP/Rocq, preserving original contracts and runtime code. Source .c and .h, dependency definitions and previous verified resolved target are frozen in /Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_emit_plan/baseline. Read the source contracts, not just these hints. This is an implementation proof migration, not whole-compiler preservation.

Target wrappers: cm_emit_plan, cm_emit_call_plan, cm_emit_normalize_plan, cm_emit_load_plan, cm_emit_store_plan, cm_emit_fp_address_plan, cm_emit_temp_store_plan, cm_emit_temp_load_plan. All runtime bodies are identical except annotations removed. Preserve exact shared cmc_layout_migration_abi.h and cm_emitter ABI. Do not edit previous verified files.

Reuse cmc_emit_resolved_migration_lib.v (including its core/counts/layout closure), and all EIGHT resolved helper contracts from the verified cmc_emit_resolved_migration.c. Their normalized contracts must remain identical. Do not import any previous manual/auto proof or re-prove helper implementations. Do not copy old unresolved proof stubs. There is no formal QCP spec supplied: annotation owner translates the original source semantics.

The new public model is cm_resolved_emitter_plan_rep_def at cmc_concrete_defs.c:573-578: pure Zlength(done)+Zlength(todo)<=capacity combined with the EXISTING resolved emitter representation of done. todo is a logical capacity budget and has no extra physical ownership. Keep done and todo independent mathematical lists; do not strengthen to reachable prefixes, a fixed full program, readiness, program well-formedness, valid targets, etc. Resolved representation still owns RAW buffers, with existing patch_code mapping raw CALL identifiers logically to total function PCs. Use the SAME existing explicit cm_lookup_policy parameter throughout, no new arbitrary PC map.

cm_emit_plan keeps opcode encoding equality and non-CALL restriction, consuming singleton from todo and appending singleton to done. cm_emit_call_plan accepts every signed int function_id, including negative/out-of-range IDs, and consumes/appends the LOGICAL resolved CALL(cm_function_pc policy p function_id), while runtime still calls cm_emit_resolved_call on raw function_id. Do not add PC representability, fid validity or bounds.

normalize/load/store preserve only original encoded-type equality and type-code-wf; no scalar-only strengthening. Their exact original fragment is consumed from todo and appended to done, tail unchanged. fp-address similarly uses original exact fragment. Temporary store/load wrappers retain all EIGHT source pure facts in BOTH pre and post, complete function_context ownership and exact fragment plan transformation. Do not drop post facts or add fid/temp bounds other than source facts.

Source public proof routines cm_plan_open and cm_plan_close at defs lines321-369 use cm_plan_fragment_term lines315-319 and will be measured separately from the two private source singleton/call helpers. Reuse available list length laws and resolved models; only add public definitions/lemmas actually useful to this migration. Avoid generic arithmetic axiom or strengthen-as-assumption proof shortcuts. No Admitted/Axiom/Parameter in new manual or case lib.

Complete owner skill workflow/plan/checks, do not edit manual during annotation. Record actual design/symexec/post-lib check invocation counts, failures and substantive repairs in agent_output.md for effort comparison, stop all writes when terminal report delivered. Main will separately replay original C*, audit runtime/contracts/models, collect costs, and update migration skill only after controller done.

## Writable formal paths

- `QCP_examples/QCP_demos_human/cmc_emit_plan_migration.c`
- `Rocq/examples/QCP_demos_human/cmc_emit_plan_migration_lib.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_plan_migration_goal.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_plan_migration_proof_auto.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_plan_migration_proof_manual.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_plan_migration_goal_check.v`

Generated files may change only through the exact symbolic-execution command below.

## Agent-written specification

The function spec, internal annotations, and case-lib definitions or lemmas may be
written and revised together in this attempt. Rerun `formal-case-lib-design` and
symexec after changes. A specification change does not end this attempt.

## Commands

```text
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_plan_migration-20261017135154 --round cmc_emit_plan_migration-annotation-r1 --target-kind formal-case-lib-design
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases symexec --run cmc_emit_plan_migration-20261017135154 --round cmc_emit_plan_migration-annotation-r1
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_plan_migration-20261017135154 --round cmc_emit_plan_migration-annotation-r1 --target-kind formal-case-lib
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
