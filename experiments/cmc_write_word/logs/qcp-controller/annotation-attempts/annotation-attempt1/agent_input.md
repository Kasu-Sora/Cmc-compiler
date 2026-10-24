# annotation handoff

This Markdown file, current files under the main root, and the listed skill docs are the source of truth. Do not use unstated parent-chat context.

## Assignment

- Round: `cmc_write_word_migration-annotation-r1`
- Attempt: `cmc_write_word_migration-annotation-r1-attempt-1` (index 1)
- Main root: `/Users/nizitong/QCP/qcp-binary-democases`
- Terminal report: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_write_word_migration-20261015190516/annotation-attempts/annotation-attempt1/agent_report.json`
- Optional human notes: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_write_word_migration-20261015190516/annotation-attempts/annotation-attempt1/agent_output.md`

## Target files

- C: `QCP_examples/QCP_demos_human/cmc_write_word_migration.c`
- `formal_case_lib` candidate (present under `present` policy; edit it only during an allowed design/proof-helper step): `Rocq/examples/QCP_demos_human/cmc_write_word_migration_lib.v`
- Manual (missing; this is an optional generated artifact, and only controller symbolic execution may create it): `Rocq/examples/QCP_demos_human/cmc_write_word_migration_proof_manual.v`
- Goal/auto/check: `Rocq/examples/QCP_demos_human/cmc_write_word_migration_goal.v`, `Rocq/examples/QCP_demos_human/cmc_write_word_migration_proof_auto.v`, `Rocq/examples/QCP_demos_human/cmc_write_word_migration_goal_check.v`

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

- Session: `cmc_write_word_migration-annotation-agent`
- Iteration: 1

This is the initial iteration. Read annotation-designing completely, follow its linked guides, and inspect the correct/incorrect examples relevant to this case before editing.

Feedback appended for this iteration:

- none (initial annotation iteration)

Required key-point plan: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_write_word_migration-20261015190516/annotation-attempts/annotation-attempt1/annotation_plan.json`

## Problem context

- Problem Statement: Migrate cmc_write_word from C*/HOL to QCP/Rocq, preserving source contract and runtime token sequence. Source /Users/nizitong/cmc/cmc_concrete_emit_word.c and .h. Baseline /Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_write_word/baseline/.

Require 0 <= cursor, cursor + 8 <= capacity, capacity <= 2147483647; own initialized unsigned-byte array prefix from 0 to cursor, separating uninitialized remainder to capacity. Ensure prefix ++ tower_word_bytes word_value through cursor+8, and uninitialized remainder thereafter. No strengthened word_value precondition: ALL signed long long values including negatives must be supported. The runtime casts to unsigned long long modulo 2^64, computes 8 little-endian bytes, then calls cmc_write_byte 8 times. Preserve those casts, ULL constants, helper calls and argument expressions; do not replace them by direct writes.

Source model tower_base.c: tower_u8 z = z % 256; tower_encode_byte z k (lines393-407) uses k repeated integer divisions by positive256 then tower_u8 for k0..7; otherwise0. tower_word_bytes (lines427-432) is that eight-element list. HOL division/modulo on negative z must map to Coq Z.div/Z.modulo for positive divisor, NOT signed C truncating quot. Translate these source mathematical definitions faithfully, or prove equivalence if using another representation. Do not define spec solely from wrapped runtime bits without proving the source bridge. Source cmc_concrete_emit_word.c contains unsigned cast/byte bridge proofs; byte0 bridge is exported in header, others static. Establish actual QCP long long and cast semantics from generated VCs.

Reuse the exact already verified cmc_write_byte contract in QCP_examples/QCP_demos_human/cmc_write_byte_migration.c. Its validation is documented at /Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_write_byte/REPORT.md and controller run cmc_write_byte_migration-20261015151544. Prefer a matching declaration contract in this target rather than duplicating body verification; explicitly document this modular dependency. Do not assume any unproved new helper. Preserve prefix and uninitialized-suffix ownership. Runtime seed has prototype only: annotation owner must give it the verified exact QCP spec.

Author QCP syntax in this attempt (no supplied QCP spec freeze). All original semantic requirements above are fixed by user. Do not strengthen preconditions or weaken postconditions for tool convenience. Prefer existing list/array and arithmetic facilities, migrate missing reusable encoding definitions and required math lemmas only. Ensure legal Import Coq wiring so model/case-lib is compiled and visible to goals and manual.

Record model definitions, public lemmas, case proof, imports, failures and actual reuse separately. Do not add unused helpers for migration volume. No manual Admitted/Axiom; don't modify proof_auto. Parent audits accepted artifacts, full validation, source model equivalence and cost afterward.
- Target Function: cmc_write_word

## Writable formal paths

- `QCP_examples/QCP_demos_human/cmc_write_word_migration.c`
- `Rocq/examples/QCP_demos_human/cmc_write_word_migration_lib.v`
- `Rocq/examples/QCP_demos_human/cmc_write_word_migration_goal.v`
- `Rocq/examples/QCP_demos_human/cmc_write_word_migration_proof_auto.v`
- `Rocq/examples/QCP_demos_human/cmc_write_word_migration_proof_manual.v`
- `Rocq/examples/QCP_demos_human/cmc_write_word_migration_goal_check.v`

Generated files may change only through the exact symbolic-execution command below.

## Agent-written specification

The function spec, internal annotations, and case-lib definitions or lemmas may be
written and revised together in this attempt. Rerun `formal-case-lib-design` and
symexec after changes. A specification change does not end this attempt.

## Commands

```text
/Users/nizitong/QCP/qcp-binary-democases/.venv/bin/python3 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_write_word_migration-20261015190516 --round cmc_write_word_migration-annotation-r1 --target-kind formal-case-lib-design
/Users/nizitong/QCP/qcp-binary-democases/.venv/bin/python3 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases symexec --run cmc_write_word_migration-20261015190516 --round cmc_write_word_migration-annotation-r1
/Users/nizitong/QCP/qcp-binary-democases/.venv/bin/python3 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_write_word_migration-20261015190516 --round cmc_write_word_migration-annotation-r1 --target-kind formal-case-lib
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
