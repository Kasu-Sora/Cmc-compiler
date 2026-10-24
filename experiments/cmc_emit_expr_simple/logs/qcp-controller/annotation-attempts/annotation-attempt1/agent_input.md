# annotation handoff

This Markdown file, current files under the main root, and the listed skill docs are the source of truth. Do not use unstated parent-chat context.

## Assignment

- Round: `cmc_emit_expr_simple_migration-annotation-r1`
- Attempt: `cmc_emit_expr_simple_migration-annotation-r1-attempt-1` (index 1)
- Main root: `/Users/nizitong/QCP/qcp-binary-democases`
- Terminal report: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_expr_simple_migration-20261018164711/annotation-attempts/annotation-attempt1/agent_report.json`
- Optional human notes: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_expr_simple_migration-20261018164711/annotation-attempts/annotation-attempt1/agent_output.md`

## Target files

- C: `QCP_examples/QCP_demos_human/cmc_emit_expr_simple_migration.c`
- `formal_case_lib` candidate (present under `create` policy; edit it only during an allowed design/proof-helper step): `Rocq/examples/QCP_demos_human/cmc_emit_expr_simple_migration_lib.v`
- Manual (missing; this is an optional generated artifact, and only controller symbolic execution may create it): `Rocq/examples/QCP_demos_human/cmc_emit_expr_simple_migration_proof_manual.v`
- Goal/auto/check: `Rocq/examples/QCP_demos_human/cmc_emit_expr_simple_migration_goal.v`, `Rocq/examples/QCP_demos_human/cmc_emit_expr_simple_migration_proof_auto.v`, `Rocq/examples/QCP_demos_human/cmc_emit_expr_simple_migration_goal_check.v`

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

- Session: `cmc_emit_expr_simple_migration-annotation-agent`
- Iteration: 1

This is the initial iteration. Read annotation-designing completely, follow its linked guides, and inspect the correct/incorrect examples relevant to this case before editing.

Feedback appended for this iteration:

- none (initial annotation iteration)

Required key-point plan: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_expr_simple_migration-20261018164711/annotation-attempts/annotation-attempt1/annotation_plan.json`

## Problem context

- Problem Statement: Migrate ENTIRE runtime file /Users/nizitong/cmc/cmc_concrete_emit_expr_simple.c C*/HOL -> QCP/Rocq, exactly one function cm_emit_simple_expr (11 runtime lines). Read original .c/.h and relevant source definitions. Frozen source and reusable dependencies: /Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_emit_expr_simple/baseline. Preserve exact runtime tokens and ABI. No user QCP formal spec supplied. Do not change prior verified files.

Preserve ALL original pre/post pure facts: lvalue[0,1], cm_simple_expr e (source leaf-or-var kind), cm_wf_program, cm_typed_program, total f lookup, cm_expr_wf, cm_expr_counts_representable, params/locals slots_wf, structs/globals/strings safe, params/locals members_safe, aggregate globals+strings size bound. Preserve complete program/function/expression ownership and exact code prefix consumption/append with arbitrary tail. No extra fid range, scalar, initialized value, or stronger input requirement. Source .c/.h contracts identical.

Reuse dispatch and var models/lemmas and transitive closure unchanged. cm_emit_leaf_expr prototype must exactly reproduce the verified BODY contract in cmc_emit_expr_dispatch_migration.c; cm_emit_var_expr prototype must exactly reproduce the verified BODY contract in cmc_emit_expr_var_migration.c (modulo whitespace). Do not import their old manual/auto or recount their implementation proof. Original wf/count facts imply helper premises; prove these at call boundaries. Leaf helper uses a logical leaf view with e=cm_leaf_source_expr leaf; reuse existing coverage/uniqueness rather than add a premise without proof. Variable model uses scope/slot/ty.

Compose an explicit simple-expression model from existing leaf and var code models. If a new sum/view witness is used, prove exact domain coverage and unique embedding from source leaf-or-kind2; never give unsupported constructors a dummy code while claiming a general recursive emitter. Reuse cm_lookup_policy, cm_codegen_obligations and original wf/count definitions; no new axioms or arbitrary emitter assumption. pc/temp are not used in leaf/var equations but C parameters remain. Record correspondence with original cm_expr_code_for under the original simple domain. Do not weaken or drop pure facts in postcondition.

Prior migration skill references dispatch and var are useful for model/annotation mapping. Record all actual design/symexec/post-library command attempts, failures and repairs in agent_output. Manual read-only. Main independently replays source, audits contracts/models and measures final artifacts, updating skill only after controller done.

## Writable formal paths

- `QCP_examples/QCP_demos_human/cmc_emit_expr_simple_migration.c`
- `Rocq/examples/QCP_demos_human/cmc_emit_expr_simple_migration_lib.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_expr_simple_migration_goal.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_expr_simple_migration_proof_auto.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_expr_simple_migration_proof_manual.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_expr_simple_migration_goal_check.v`

Generated files may change only through the exact symbolic-execution command below.

## Agent-written specification

The function spec, internal annotations, and case-lib definitions or lemmas may be
written and revised together in this attempt. Rerun `formal-case-lib-design` and
symexec after changes. A specification change does not end this attempt.

## Commands

```text
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_expr_simple_migration-20261018164711 --round cmc_emit_expr_simple_migration-annotation-r1 --target-kind formal-case-lib-design
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases symexec --run cmc_emit_expr_simple_migration-20261018164711 --round cmc_emit_expr_simple_migration-annotation-r1
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_expr_simple_migration-20261018164711 --round cmc_emit_expr_simple_migration-annotation-r1 --target-kind formal-case-lib
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
