# annotation handoff

This Markdown file, current files under the main root, and the listed skill docs are the source of truth. Do not use unstated parent-chat context.

## Assignment

- Round: `cmc_emit_stmt_migration-annotation-r1`
- Attempt: `cmc_emit_stmt_migration-annotation-r1-attempt-1` (index 1)
- Main root: `/Users/nizitong/QCP/qcp-binary-democases`
- Terminal report: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_stmt_migration-20261019010952/annotation-attempts/annotation-attempt1/agent_report.json`
- Optional human notes: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_stmt_migration-20261019010952/annotation-attempts/annotation-attempt1/agent_output.md`

## Target files

- C: `QCP_examples/QCP_demos_human/cmc_emit_stmt_migration.c`
- `formal_case_lib` candidate (present under `create` policy; edit it only during an allowed design/proof-helper step): `Rocq/examples/QCP_demos_human/cmc_emit_stmt_migration_lib.v`
- Manual (missing; this is an optional generated artifact, and only controller symbolic execution may create it): `Rocq/examples/QCP_demos_human/cmc_emit_stmt_migration_proof_manual.v`
- Goal/auto/check: `Rocq/examples/QCP_demos_human/cmc_emit_stmt_migration_goal.v`, `Rocq/examples/QCP_demos_human/cmc_emit_stmt_migration_proof_auto.v`, `Rocq/examples/QCP_demos_human/cmc_emit_stmt_migration_goal_check.v`

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

- Session: `cmc_emit_stmt_migration-annotation-agent`
- Iteration: 1

This is the initial iteration. Read annotation-designing completely, follow its linked guides, and inspect the correct/incorrect examples relevant to this case before editing.

Feedback appended for this iteration:

- none (initial annotation iteration)

Required key-point plan: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_stmt_migration-20261019010952/annotation-attempts/annotation-attempt1/annotation_plan.json`

## Problem context

- Problem Statement: Migrate ENTIRE /Users/nizitong/cmc/cmc_concrete_emit_stmt.c from C*/HOL to QCP/Rocq, including necessary cmc_concrete_emit_stmt_proof.c support. Preserve exact runtime tokens and original BODY contract meanings. Frozen source, headers, runtime and effort regions are under /Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_emit_stmt/. Verify BOTH bodies cmc_emit_if_stmt and cmc_emit_stmt. C* attributes are reference semantics, not a user-authored frozen QCP spec. Translate every original pure pre/post fact, full program/function/statement resources, exact cm_emit_stmt prefix consumption/done append and arbitrary tail. Preserve constructor condition for if, loop flag, wf/typing/count/slot/safety/size/temp/pc/break_pc/continue_pc premises. Preserve total fid lookup and existing arbitrary policy/cg parameterization. No stronger input assumptions, weaker postconditions or changed runtime bodies. Add needed mutual-recursive prototypes with identical BODY contracts; duplicates are measured separately.
Reuse existing verified ABI and cm_emitter declaration. Import cmc_emit_expr_migration_lib, cmc_emit_return_migration_lib, and needed previously verified libraries. Reuse cm_stmt type, rep, wf/count/temp models and general expression model from prior libraries. Add only genuinely missing statement emission equations/support. Source cmc_concrete_emit_stmt_proof.c supports representation opening/closing, constructor wf projection, code shape, lengths, intermediate PC bounds; migrate necessary mathematical content as checked case-lib lemmas or reuse existing definitions/lemmas. Do not mechanically copy C* proof-engine tactics or assume their conclusions. Every new proposition must be proved; no Admitted/Axiom/Parameter in new lib/manual.
External helper implementations already verified include cm_emit_expr, cm_emit_return_epilogue_plan, cm_emit_plan/normalize/store_plan, cm_emit_binding_address_plan, cmc_slot_type_at, cm_expr_rvalue_count_context, cm_stmt_code_count_context. Locate actual accepted BODY contracts, not guesses from source headers. Mutual cmc_emit_stmt/cmc_emit_if_stmt prototypes must match their respective implemented BODY contracts. No importing earlier manual/auto proofs and no changing earlier verified artifacts.
Maintain exact instruction order/PC targets for if and while; distinct loop-context of recursive while body; all initializer/return type normalization and heap resource restoration. This verifies modular BODY contracts, not TVM execution, termination, or compiler preservation. Record actual design/symexec/post-lib checks, failures and repairs in agent_output.md for effort accounting. Persist progress and continue through context compaction. Stop formal/report writes after terminal delivery. Main audits semantic correspondence and incremental public cost, and updates skill only after controller done.

## Writable formal paths

- `QCP_examples/QCP_demos_human/cmc_emit_stmt_migration.c`
- `Rocq/examples/QCP_demos_human/cmc_emit_stmt_migration_lib.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_stmt_migration_goal.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_stmt_migration_proof_auto.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_stmt_migration_proof_manual.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_stmt_migration_goal_check.v`

Generated files may change only through the exact symbolic-execution command below.

## Agent-written specification

The function spec, internal annotations, and case-lib definitions or lemmas may be
written and revised together in this attempt. Rerun `formal-case-lib-design` and
symexec after changes. A specification change does not end this attempt.

## Commands

```text
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_stmt_migration-20261019010952 --round cmc_emit_stmt_migration-annotation-r1 --target-kind formal-case-lib-design
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases symexec --run cmc_emit_stmt_migration-20261019010952 --round cmc_emit_stmt_migration-annotation-r1
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_stmt_migration-20261019010952 --round cmc_emit_stmt_migration-annotation-r1 --target-kind formal-case-lib
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
