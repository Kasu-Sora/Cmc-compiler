# annotation handoff

This Markdown file, current files under the main root, and the listed skill docs are the source of truth. Do not use unstated parent-chat context.

## Assignment

- Round: `cmc_write_char_migration-annotation-r1`
- Attempt: `cmc_write_char_migration-annotation-r1-attempt-1` (index 1)
- Main root: `/Users/nizitong/QCP/qcp-binary-democases`
- Terminal report: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_write_char_migration-20261015193338/annotation-attempts/annotation-attempt1/agent_report.json`
- Optional human notes: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_write_char_migration-20261015193338/annotation-attempts/annotation-attempt1/agent_output.md`

## Target files

- C: `QCP_examples/QCP_demos_human/cmc_write_char_migration.c`
- `formal_case_lib` candidate (missing under explicit `absent` policy; there is no active/editable case lib, and this candidate path is read-only and must not be created): `Rocq/examples/QCP_demos_human/cmc_write_char_migration_lib.v`
- Manual (missing; this is an optional generated artifact, and only controller symbolic execution may create it): `Rocq/examples/QCP_demos_human/cmc_write_char_migration_proof_manual.v`
- Goal/auto/check: `Rocq/examples/QCP_demos_human/cmc_write_char_migration_goal.v`, `Rocq/examples/QCP_demos_human/cmc_write_char_migration_proof_auto.v`, `Rocq/examples/QCP_demos_human/cmc_write_char_migration_goal_check.v`

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

- Session: `cmc_write_char_migration-annotation-agent`
- Iteration: 1

This is the initial iteration. Read annotation-designing completely, follow its linked guides, and inspect the correct/incorrect examples relevant to this case before editing.

Feedback appended for this iteration:

- none (initial annotation iteration)

Required key-point plan: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_write_char_migration-20261015193338/annotation-attempts/annotation-attempt1/annotation_plan.json`

## Problem context

- Problem Statement: Migrate cmc_write_char from C*/HOL to QCP/Rocq preserving its original contract and runtime C token sequence. Source /Users/nizitong/cmc/cmc_concrete_emit_char.c and .h. Baselines /Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_write_char/baseline/.

Require 0<=cursor, cursor+1<=capacity, capacity<=2147483647; own initialized prefix and separating uninitialized remainder. Ensure initialized prefix ++ [tower_u8 char_value] through cursor+1 and uninitialized suffix thereafter. All signed long long inputs, including negative and >255, are allowed. No extra nonnegative/byte-range premise may be imposed. tower_u8 z is Euclidean z mod256, not signed C remainder. Runtime must remain cast to unsigned long long, byte=(unsigned char)(bits%256ULL), then exactly one cmc_write_byte call. This is low-byte emission, not Unicode encoding.

Reuse already verified QCP definitions and lemmas in Rocq/examples/QCP_demos_human/cmc_write_word_migration_lib.v, particularly tower_u8 and tower_machine_rem_byte__byte_encoding at k=0 (and its dependency chain). Prior run cmc_write_word_migration-20261015190516 is done, report /Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_write_word/REPORT.md. That pure library has official imports only, three definitions and three proved lemmas; do not copy/reprove/rename those just to avoid dependency setup. Import the existing library through legal C Import Coq wiring so goals/manual and selected dependency snapshot include it. Current char case policy is absent: no new canonical char lib expected, as k=0 proof should be direct existing-lemma instantiation. If a genuine dependency blocker arises, report the precise diagnostic rather than weakening the spec or editing shared accepted source.

Reuse exact cmc_write_byte declaration contract from QCP_examples/QCP_demos_human/cmc_write_byte_migration.c, verified in cmc_write_byte_migration-20261015151544. Keep actual helper call; don't replace by direct store. Record this modular helper dependency (including existing two trusted automatic results); don't double count its earlier implementation proof as new migration work. Source char uses existing cmc_unsigned_byte0_bridge and tower_u8_range, so source common cost here is also reused, not newly authored.

Author equivalent QCP syntax; no user-supplied QCP freeze. Semantic requirements above remain fixed. Preserve unsigned cast/modulo semantics for negative words. No manual Admitted/Axiom, no changes to generated auto or earlier accepted word/byte files. Record annotation candidates, failed checks, actually used imported helpers, and any new imports separately. Parent audits and measures only after full controller validation.
- Target Function: cmc_write_char

## Writable formal paths

- `QCP_examples/QCP_demos_human/cmc_write_char_migration.c`
- `Rocq/examples/QCP_demos_human/cmc_write_char_migration_goal.v`
- `Rocq/examples/QCP_demos_human/cmc_write_char_migration_proof_auto.v`
- `Rocq/examples/QCP_demos_human/cmc_write_char_migration_proof_manual.v`
- `Rocq/examples/QCP_demos_human/cmc_write_char_migration_goal_check.v`

Generated files may change only through the exact symbolic-execution command below.

## Agent-written specification

The function spec, internal annotations, and case-lib definitions or lemmas may be
written and revised together in this attempt. Rerun `formal-case-lib-design` and
symexec after changes. A specification change does not end this attempt.

## Commands

```text
/Users/nizitong/QCP/qcp-binary-democases/.venv/bin/python3 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_write_char_migration-20261015193338 --round cmc_write_char_migration-annotation-r1 --target-kind formal-case-lib-design
/Users/nizitong/QCP/qcp-binary-democases/.venv/bin/python3 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases symexec --run cmc_write_char_migration-20261015193338 --round cmc_write_char_migration-annotation-r1
```

This run explicitly selected the absent policy. The standalone design check records a skipped pass; no post-symexec formal-case-lib command is listed, and the owner must keep the candidate path absent.

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
