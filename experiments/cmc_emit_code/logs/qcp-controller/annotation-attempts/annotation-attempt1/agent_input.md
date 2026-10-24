# annotation handoff

This Markdown file, current files under the main root, and the listed skill docs are the source of truth. Do not use unstated parent-chat context.

## Assignment

- Round: `cmc_emit_code_migration-annotation-r1`
- Attempt: `cmc_emit_code_migration-annotation-r1-attempt-1` (index 1)
- Main root: `/Users/nizitong/QCP/qcp-binary-democases`
- Terminal report: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_code_migration-20261019112556/annotation-attempts/annotation-attempt1/agent_report.json`
- Optional human notes: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_code_migration-20261019112556/annotation-attempts/annotation-attempt1/agent_output.md`

## Target files

- C: `QCP_examples/QCP_demos_human/cmc_emit_code_migration.c`
- `formal_case_lib` candidate (present under `create` policy; edit it only during an allowed design/proof-helper step): `Rocq/examples/QCP_demos_human/cmc_emit_code_migration_lib.v`
- Manual (missing; this is an optional generated artifact, and only controller symbolic execution may create it): `Rocq/examples/QCP_demos_human/cmc_emit_code_migration_proof_manual.v`
- Goal/auto/check: `Rocq/examples/QCP_demos_human/cmc_emit_code_migration_goal.v`, `Rocq/examples/QCP_demos_human/cmc_emit_code_migration_proof_auto.v`, `Rocq/examples/QCP_demos_human/cmc_emit_code_migration_goal_check.v`

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

- Session: `cmc_emit_code_migration-annotation-agent`
- Iteration: 1

This is the initial iteration. Read annotation-designing completely, follow its linked guides, and inspect the correct/incorrect examples relevant to this case before editing.

Feedback appended for this iteration:

- none (initial annotation iteration)

Required key-point plan: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_code_migration-20261019112556/annotation-attempts/annotation-attempt1/annotation_plan.json`

## Problem context

- Problem Statement: Migrate the entire /Users/nizitong/cmc/cmc_concrete_emit_code.c to QCP: exactly one runtime function cmc_emit_code, preserving exact runtime tokens, shared cmc_layout_migration_abi.h and cm_emitter ABI. Baseline at /Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_emit_code/baseline/. Original C* BODY/header contracts authoritative, no strengthening or weakening.
With existing policy/cg parameters and p,functions_ptr,done,tail,out,capacity. Preserve ALL original facts in pre/post: cm_wf_program(policy,cg,p), cm_typed_program(policy,p), cm_concrete_functions_ready(policy,p,0,cm_program_functions(p)), cm_rep_structs_safe(cm_program_structs(p)), cm_rep_globals_safe(cm_program_globals(p)), cm_rep_strings_safe(cm_program_strings(p)), cm_rep_globals_size(cm_program_globals(p))+cm_rep_strings_size(cm_program_strings(p))<=1048560. Preserve cm_program_context_rep(program,p,functions_ptr) and cm_function_list_rep(functions_ptr,cm_program_functions(p)); consume cm_model_code(policy,p)++tail from the plan and append precisely cm_model_code(policy,p) to arbitrary done, retaining tail. No new additional premise or changed input domain.
Exact new cm_model_code from cmc_codegen.c:1043-1046 is cm_emit_prelude p ++ cm_emit_functions p 0 (cm_program_functions p). Reuse completed cmc_emit_prelude_migration_lib and cmc_emit_functions_migration_lib and actual dependency closure; no old generated proof_auto/proof_manual imports. Existing lookup-policy and codegen-obligations parameterization unchanged. Necessary PC-zero fact cm_function_pc policy p 0 = 11 must be derived from existing definitions/lemmas, not imposed as precondition. Source theorem cm_function_pc_zero and its proof in cmc_stack_local_syntax.c are references; prefix-zero support already used by counts/function_pc_total.
Copy exact verified BODY contracts of cmc_emit_prelude and cmc_emit_functions from their respective *_migration.c files. Read the functions field from full program context, restore it, preserve function-list ownership across both helper calls and restore exact original postcondition. Do not change prior source/target files. Reuse public definitions/lemmas; introduce only necessary model/support without Axiom/Admitted in manual/lib.
Complete controller pipeline. Annotation owner report actual design/symexec/post-lib calls/failures and repair notes, new definitions/helpers. Main independently audits semantics, source replay, effort and shared incremental costs; skill updated only after full validation. This is modular concrete emitter implementation verification, not new compiler preservation, raw output linking/patching correctness or TVM execution/termination theorem.

## Writable formal paths

- `QCP_examples/QCP_demos_human/cmc_emit_code_migration.c`
- `Rocq/examples/QCP_demos_human/cmc_emit_code_migration_lib.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_code_migration_goal.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_code_migration_proof_auto.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_code_migration_proof_manual.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_code_migration_goal_check.v`

Generated files may change only through the exact symbolic-execution command below.

## Agent-written specification

The function spec, internal annotations, and case-lib definitions or lemmas may be
written and revised together in this attempt. Rerun `formal-case-lib-design` and
symexec after changes. A specification change does not end this attempt.

## Commands

```text
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_code_migration-20261019112556 --round cmc_emit_code_migration-annotation-r1 --target-kind formal-case-lib-design
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases symexec --run cmc_emit_code_migration-20261019112556 --round cmc_emit_code_migration-annotation-r1
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_code_migration-20261019112556 --round cmc_emit_code_migration-annotation-r1 --target-kind formal-case-lib
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
