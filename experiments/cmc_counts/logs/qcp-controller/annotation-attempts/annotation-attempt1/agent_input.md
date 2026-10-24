# annotation handoff

This Markdown file, current files under the main root, and the listed skill docs are the source of truth. Do not use unstated parent-chat context.

## Assignment

- Round: `cmc_counts_migration-annotation-r1`
- Attempt: `cmc_counts_migration-annotation-r1-attempt-1` (index 1)
- Main root: `/Users/nizitong/QCP/qcp-binary-democases`
- Terminal report: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_counts_migration-20261015235041/annotation-attempts/annotation-attempt1/agent_report.json`
- Optional human notes: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_counts_migration-20261015235041/annotation-attempts/annotation-attempt1/agent_output.md`

## Target files

- C: `QCP_examples/QCP_demos_human/cmc_counts_migration.c`
- `formal_case_lib` candidate (present under `create` policy; edit it only during an allowed design/proof-helper step): `Rocq/examples/QCP_demos_human/cmc_counts_migration_lib.v`
- Manual (missing; this is an optional generated artifact, and only controller symbolic execution may create it): `Rocq/examples/QCP_demos_human/cmc_counts_migration_proof_manual.v`
- Goal/auto/check: `Rocq/examples/QCP_demos_human/cmc_counts_migration_goal.v`, `Rocq/examples/QCP_demos_human/cmc_counts_migration_proof_auto.v`, `Rocq/examples/QCP_demos_human/cmc_counts_migration_goal_check.v`

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

- Session: `cmc_counts_migration-annotation-agent`
- Iteration: 1

This is the initial iteration. Read annotation-designing completely, follow its linked guides, and inspect the correct/incorrect examples relevant to this case before editing.

Feedback appended for this iteration:

- none (initial annotation iteration)

Required key-point plan: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_counts_migration-20261015235041/annotation-attempts/annotation-attempt1/annotation_plan.json`

## Problem context

- Problem Statement: Migrate the complete runtime implementation of /Users/nizitong/cmc/cmc_concrete_counts.c from C*/HOL to QCP/Rocq, preserving the original contracts and runtime code. There are 15 function bodies and 1 cm_expr_counts forward declaration. Validate every body, not only wrappers. Canonical target is QCP_examples/QCP_demos_human/cmc_counts_migration.c. Source snapshots, extracted runtime and function/spec/proof regions are in /Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_counts/baseline and metrics/source-functions.json. Read the original function specifications and relevant logical source definitions, not just their names. The complete source tree is /Users/nizitong/cmc.
Reuse the already verified Rocq/examples/QCP_demos_human/cmc_layout_migration_lib.v (types, AST, descriptors, lookup policy, representation, normalizing/type helpers, size models and bridges), and the existing cmc_layout_migration_abi.h. Do not modify the prior accepted libraries or runtime bodies. Only create the new case library for genuinely new counting/wellformedness/context models and proved bridges. Imported helper function declarations must preserve their previously verified contracts from cmc_layout_migration.c. Count their annotation integration separately; no need to duplicate their bodies/proofs.
The target must retain the original nonnegative i32 code-count semantics, exact expression lvalue/rvalue and statement counts, parameter/prologue counts, prefix/index relationships, code length 11+function sum and data length 8+globals+strings. Preserve original field-only/context ownership, return resource frames, original wellformedness and representability conditions. No new fid/range assumptions unless derivable from original premises. Carry the already verified cm_lookup_policy consistently for HOL total function lookup, including off-domain inputs. Reuse the existing AST rather than defining an unrelated representation or a runtime interpreter as the specification.
cm_wf_program expands via cm_codegen_admissible in cmc_codegen.c and contains more than count bounds. Do not silently redefine it as only convenient facts or replace mathematical functions by arbitrary Parameters. Any abstraction of irrelevant source components must be explicitly universally quantified, retain their original conjunctions and have a documented source instantiation/correspondence, without new axioms or stronger input assumptions. Prefer direct faithful definitions for the actual dependency closure. Report semantic adaptations for main audit before sealing. Pure definitions in the source that are not dependencies of these 15 contracts/proofs (e.g. later-emitter readiness exports) may be inventoried separately; do not claim they or the entire CMC/TVM proof have been migrated by validating this case.
No Admitted/Axiom/Parameter in newly authored library or manual proof. Generated auto witnesses keep tool trust semantics and will be disclosed separately. Keep original mathematical result, do not weaken Ensure or strengthen Require for convenience. Build realistic intermediate assertions so recursion exposes owned AST/list fields and proofs remain tractable. Source/target annotation and proof effort, new shared definitions/proofs and actual reuse will be audited by main. Record substantive same-attempt failures/semantic decisions in your allowed agent output; main updates migration skill only after final-check is passed. Follow the repository controller workflow and role write boundaries.
- Reference Case Hints: /Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_layout/REPORT.md

## Writable formal paths

- `QCP_examples/QCP_demos_human/cmc_counts_migration.c`
- `Rocq/examples/QCP_demos_human/cmc_counts_migration_lib.v`
- `Rocq/examples/QCP_demos_human/cmc_counts_migration_goal.v`
- `Rocq/examples/QCP_demos_human/cmc_counts_migration_proof_auto.v`
- `Rocq/examples/QCP_demos_human/cmc_counts_migration_proof_manual.v`
- `Rocq/examples/QCP_demos_human/cmc_counts_migration_goal_check.v`

Generated files may change only through the exact symbolic-execution command below.

## Agent-written specification

The function spec, internal annotations, and case-lib definitions or lemmas may be
written and revised together in this attempt. Rerun `formal-case-lib-design` and
symexec after changes. A specification change does not end this attempt.

## Commands

```text
/Users/nizitong/QCP/qcp-binary-democases/.venv/bin/python3 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_counts_migration-20261015235041 --round cmc_counts_migration-annotation-r1 --target-kind formal-case-lib-design
/Users/nizitong/QCP/qcp-binary-democases/.venv/bin/python3 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases symexec --run cmc_counts_migration-20261015235041 --round cmc_counts_migration-annotation-r1
/Users/nizitong/QCP/qcp-binary-democases/.venv/bin/python3 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_counts_migration-20261015235041 --round cmc_counts_migration-annotation-r1 --target-kind formal-case-lib
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
