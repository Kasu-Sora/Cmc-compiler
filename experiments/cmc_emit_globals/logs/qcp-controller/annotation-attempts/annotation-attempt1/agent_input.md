# annotation handoff

This Markdown file, current files under the main root, and the listed skill docs are the source of truth. Do not use unstated parent-chat context.

## Assignment

- Round: `cmc_emit_globals_migration-annotation-r1`
- Attempt: `cmc_emit_globals_migration-annotation-r1-attempt-1` (index 1)
- Main root: `/Users/nizitong/QCP/qcp-binary-democases`
- Terminal report: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_globals_migration-20261016102210/annotation-attempts/annotation-attempt1/agent_report.json`
- Optional human notes: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_globals_migration-20261016102210/annotation-attempts/annotation-attempt1/agent_output.md`

## Target files

- C: `QCP_examples/QCP_demos_human/cmc_emit_globals_migration.c`
- `formal_case_lib` candidate (present under `create` policy; edit it only during an allowed design/proof-helper step): `Rocq/examples/QCP_demos_human/cmc_emit_globals_migration_lib.v`
- Manual (missing; this is an optional generated artifact, and only controller symbolic execution may create it): `Rocq/examples/QCP_demos_human/cmc_emit_globals_migration_proof_manual.v`
- Goal/auto/check: `Rocq/examples/QCP_demos_human/cmc_emit_globals_migration_goal.v`, `Rocq/examples/QCP_demos_human/cmc_emit_globals_migration_proof_auto.v`, `Rocq/examples/QCP_demos_human/cmc_emit_globals_migration_goal_check.v`

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

- Session: `cmc_emit_globals_migration-annotation-agent`
- Iteration: 1

This is the initial iteration. Read annotation-designing completely, follow its linked guides, and inspect the correct/incorrect examples relevant to this case before editing.

Feedback appended for this iteration:

- none (initial annotation iteration)

Required key-point plan: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_globals_migration-20261016102210/annotation-attempts/annotation-attempt1/annotation_plan.json`

## Problem context

- Problem Statement: Migrate the entire /Users/nizitong/cmc/cmc_concrete_emit_globals.c from C*/HOL to QCP/Rocq: one recursive runtime function cmc_emit_globals, no forward declaration or loops. Preserve original runtime tokens, exact pre/postconditions, list ownership, old initialized prefix and undefined suffix. Source/header and extracted runtime are in /Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_emit_globals/baseline; read the actual source contract/proof. Canonical target QCP_examples/QCP_demos_human/cmc_emit_globals_migration.c.
Source requires cm_rep_globals_safe globals, cm_data_globals_wf structs globals, 0<=cursor, cursor+cm_rep_globals_size globals<=capacity, capacity<=INT_MAX, cm_global_list_rep node globals, initialized byte array prefix through cursor and undefined remainder. Ensure restores both original pure predicates and global list, exact prefix ++ cm_globals_bytes structs globals, undefined suffix at cursor+representation size, and exact return cursor+size. Keep all original input cases, including empty lists; do not add data!=0, initialization value or capacity bounds merely for convenience. Scalar initialized chars write one byte; nonchar initialized scalar writes eight little-endian bytes; no-init arrays/scalars write zeros. Preserve signed longlong -> int size cast and justify its existing bounds.
Reuse immutable verified cmc_counts_migration_lib.v (contains cm_global_wf, cm_global_size, cm_global_init_bytes/cm_global_bytes/cm_globals_bytes), layout lib (types/rep/safety/list), copy_bytes pure lib and cmc_write_word_migration_lib.v (tower_u8, tower_word_bytes, encoding bridges). Do not duplicate these models or modify their bytes. cm_data_globals_wf is the recursive conjunction of existing cm_global_wf from cmc_concrete_data_ready.c; translate its complete meaning. The source cm_scalar_type excludes struct types but permits valid pointers; preserve pointer initialization=0 restriction from full cm_global_wf. No new universally quantified program/TVM obligations are needed by this file's contract.
Import exact helper contracts from verified C files: cmc_code_slot_size from cmc_layout_migration.c, cmc_write_char from cmc_write_char_migration.c, cmc_write_word from cmc_write_word_migration.c and cmc_write_zeroes from cmc_write_zeroes_migration.c. Preserve cmc_layout_migration_abi.h and CMC_TYPE_CHAR. Use UCharArray seg/undef_seg as previous emitter cases. No previous helper auto/manual proof imports or re-proving their implementations. Existing zeroes lib has zeros_snoc only, probably unnecessary for this recursive emitter; import it only if actually needed.
The counts global initializer uses map/seq and division by powers, while verified word uses eight tower_encode_byte entries (iterated floor divisions); prove equivalence for all integers, including negatives, instead of silently replacing the counts model. Reuse existing encoding lemmas where useful. Prove semantic cm_global_size = representation size under original global_wf and other necessary pure/heap bridges; add only necessary reusable lemmas to current library and report incremental cost. Source private proof helpers remain case proof in source effort; new target public helpers are counted separately even when they replace them.
No authored Admitted/Axiom/Parameter. Generated auto witnesses follow QCP trust semantics and will be reported separately. Do not strengthen Require/weaken Ensure/change runtime to reduce VCs. Record substantive failures/repairs and semantic decisions in your permitted report. Main audits final whole-file coverage, runtime identity, helper contract identity, complete predicates and actual shared reuse, then updates skill only after controller done. Follow repository role boundaries and exact handoff commands.
- Reference Case Hints: /Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_function_pc_total/REPORT.md

## Writable formal paths

- `QCP_examples/QCP_demos_human/cmc_emit_globals_migration.c`
- `Rocq/examples/QCP_demos_human/cmc_emit_globals_migration_lib.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_globals_migration_goal.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_globals_migration_proof_auto.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_globals_migration_proof_manual.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_globals_migration_goal_check.v`

Generated files may change only through the exact symbolic-execution command below.

## Agent-written specification

The function spec, internal annotations, and case-lib definitions or lemmas may be
written and revised together in this attempt. Rerun `formal-case-lib-design` and
symexec after changes. A specification change does not end this attempt.

## Commands

```text
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_globals_migration-20261016102210 --round cmc_emit_globals_migration-annotation-r1 --target-kind formal-case-lib-design
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases symexec --run cmc_emit_globals_migration-20261016102210 --round cmc_emit_globals_migration-annotation-r1
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_globals_migration-20261016102210 --round cmc_emit_globals_migration-annotation-r1 --target-kind formal-case-lib
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
