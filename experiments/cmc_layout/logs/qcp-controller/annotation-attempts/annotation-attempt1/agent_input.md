# annotation handoff

This Markdown file, current files under the main root, and the listed skill docs are the source of truth. Do not use unstated parent-chat context.

## Assignment

- Round: `cmc_layout_migration-annotation-r1`
- Attempt: `cmc_layout_migration-annotation-r1-attempt-1` (index 1)
- Main root: `/Users/nizitong/QCP/qcp-binary-democases`
- Terminal report: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_layout_migration-20261015200400/annotation-attempts/annotation-attempt1/agent_report.json`
- Optional human notes: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_layout_migration-20261015200400/annotation-attempts/annotation-attempt1/agent_output.md`

## Target files

- C: `QCP_examples/QCP_demos_human/cmc_layout_migration.c`
- `formal_case_lib` candidate (present under `create` policy; edit it only during an allowed design/proof-helper step): `Rocq/examples/QCP_demos_human/cmc_layout_migration_lib.v`
- Manual (missing; this is an optional generated artifact, and only controller symbolic execution may create it): `Rocq/examples/QCP_demos_human/cmc_layout_migration_proof_manual.v`
- Goal/auto/check: `Rocq/examples/QCP_demos_human/cmc_layout_migration_goal.v`, `Rocq/examples/QCP_demos_human/cmc_layout_migration_proof_auto.v`, `Rocq/examples/QCP_demos_human/cmc_layout_migration_goal_check.v`

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

- Session: `cmc_layout_migration-annotation-agent`
- Iteration: 1

This is the initial iteration. Read annotation-designing completely, follow its linked guides, and inspect the correct/incorrect examples relevant to this case before editing.

Feedback appended for this iteration:

- none (initial annotation iteration)

Required key-point plan: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_layout_migration-20261015200400/annotation-attempts/annotation-attempt1/annotation_plan.json`

## Problem context

- Problem Statement: Migrate the ENTIRE cmc_concrete_layout.c from C*/HOL to QCP/Rocq, preserving every original function contract and runtime body. Source /Users/nizitong/cmc/cmc_concrete_layout.c (5832 lines), .h, and dependency definitions in cmc_rep.c, cmc_lang.c, cmc_concrete_defs.c, cmc_abi.c/.h, cmc_temp_algebra.c and other actually used sources. Frozen baseline root files under /Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_layout/baseline. Extracted body inventory/contracts/proof regions in metrics/source-functions.json, unannotated runtime in baseline/runtime-source.c. Original whole C* file already replays clean (hash6bb1d132dfee153bb2ca6d0e6a8c1ab125d629387ac6c97201f95ab1ff187dc7).

This is 39 runtime function bodies plus one forward declaration of mutually recursive cm_expr_temps, NOT a single-function unit. Include all static helpers and exported functions: cm_max, cmc_is_pointer, cmc_is_pointer_value, cmc_pointee, cmc_leaf_size, cmc_code_slot_size, cmc_members_size, cmc_struct_size_at, cmc_nonzero, cmc_global_array_at, cmc_slot_array_at, cmc_slot_type_at, cmc_member_array_at, cmc_type_size_at, cmc_slots_size, cmc_slots_prefix, cmc_members_prefix, cmc_member_offset_at, cmc_struct_member_array_at, cmc_globals_size, cmc_globals_prefix, cmc_strings_size, cmc_strings_prefix, cmc_global_address, cmc_string_address, cmc_binding_array_value, cmc_binding_array, cmc_member_array, cmc_member_array_value, cm_args_length, cmc_args_tpair, cm_expr_temps, cm_expr_rtemps, cmc_stmt_temps, cmc_frame_size, cmc_param_offset, cmc_local_offset, cmc_temp_offset, cm_normalize_count. Do not silently shrink the target to scalar helpers or treat remaining bodies as assumed external declarations. Complete accounting remains whole-file plus per-function.

Preserve runtime C tokens, recursion, casts, field accesses, helper calls, empty branches and outputs. Seed uses the unchanged original pure cmc_abi.h copied as cmc_layout_migration_abi.h; all source macros/struct fields retained. Header is fixed shared ABI input, do not alter it to simplify proof. Author equivalent QCP formal syntax (not frozen user QCP text); original source semantics are fixed. Preserve all logical parameters, model results, resource ownership/initialization, preserved lists/trees, valid-index/well-formedness/safety predicates, bounds, and distinctions of absent/null versus nonnull structures. No strengthened preconditions or weakened postconditions. cmc_code_slot_size accepts any signed int count, including negative; safe lists add only their ORIGINAL model conditions. No extra assumptions that structs/arrays/AST inputs are positive/nonempty beyond original representation.

Translate actual source definitions needed by contracts, including source logical types and AST constructors, encodings, list/heap representations, safe predicates, selection models, temporary-pair algebra, cm_etemps/cm_stemps and their validity bridges. Source cmc_rep/cmc_lang contain the authoritative definitions. Don't introduce opaque unproved Parameters/Axioms for missing semantic definitions or turn output models into unrelated interpreter-shaped specs solely to make obligations easy. Equivalent projections or shared definitions are fine only with a justified semantic bridge. Preserve partial record ownership as in source; don't require all program/function fields when original owns only selected fields.

Prefer existing QCP integer/list/separation libraries. Earlier byte/zero/copy/word/char migration outputs are under QCP_examples/QCP_demos_human and Rocq/examples/QCP_demos_human; import their actual relevant verified helpers if useful, but encoding helpers may not apply to layout. Do not modify earlier accepted files or copy unused models. New reusable semantic/representation definitions and helper lemmas belong to the current lib and must be actually compiled through legal Import Coq wiring. Keep case proof and common definitions/lemmas costs separate; don't omit top-level source PROOF helpers exported in this file from the audit.

Work incrementally within this single annotation attempt, preserving the full requested scope. The file is larger than prior cases; save continuation notes as needed and continue across compaction. Do not report context difficulty alone as a semantic blocker. If there is a genuine tool/spec/dependency blocker, give exact diagnostics and preserve artifacts. Do not edit proof_auto, write manual Admitted/Axiom, modify controller state, or claim unverified bodies complete. Report all candidates, failed checks, runtime changes if unavoidable, new shared content and reuse; parent validates/measures after full run before updating migration skill.

## Writable formal paths

- `QCP_examples/QCP_demos_human/cmc_layout_migration.c`
- `Rocq/examples/QCP_demos_human/cmc_layout_migration_lib.v`
- `Rocq/examples/QCP_demos_human/cmc_layout_migration_goal.v`
- `Rocq/examples/QCP_demos_human/cmc_layout_migration_proof_auto.v`
- `Rocq/examples/QCP_demos_human/cmc_layout_migration_proof_manual.v`
- `Rocq/examples/QCP_demos_human/cmc_layout_migration_goal_check.v`

Generated files may change only through the exact symbolic-execution command below.

## Agent-written specification

The function spec, internal annotations, and case-lib definitions or lemmas may be
written and revised together in this attempt. Rerun `formal-case-lib-design` and
symexec after changes. A specification change does not end this attempt.

## Commands

```text
/Users/nizitong/QCP/qcp-binary-democases/.venv/bin/python3 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_layout_migration-20261015200400 --round cmc_layout_migration-annotation-r1 --target-kind formal-case-lib-design
/Users/nizitong/QCP/qcp-binary-democases/.venv/bin/python3 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases symexec --run cmc_layout_migration-20261015200400 --round cmc_layout_migration-annotation-r1
/Users/nizitong/QCP/qcp-binary-democases/.venv/bin/python3 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_layout_migration-20261015200400 --round cmc_layout_migration-annotation-r1 --target-kind formal-case-lib
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
