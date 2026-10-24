# annotation handoff

This Markdown file, current files under the main root, and the listed skill docs are the source of truth. Do not use unstated parent-chat context.

## Assignment

- Round: `cmc_emit_ast_migration-annotation-r1`
- Attempt: `cmc_emit_ast_migration-annotation-r1-attempt-1` (index 1)
- Main root: `/Users/nizitong/QCP/qcp-binary-democases`
- Terminal report: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_ast_migration-20261017141940/annotation-attempts/annotation-attempt1/agent_report.json`
- Optional human notes: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_ast_migration-20261017141940/annotation-attempts/annotation-attempt1/agent_output.md`

## Target files

- C: `QCP_examples/QCP_demos_human/cmc_emit_ast_migration.c`
- `formal_case_lib` candidate (present under `create` policy; edit it only during an allowed design/proof-helper step): `Rocq/examples/QCP_demos_human/cmc_emit_ast_migration_lib.v`
- Manual (missing; this is an optional generated artifact, and only controller symbolic execution may create it): `Rocq/examples/QCP_demos_human/cmc_emit_ast_migration_proof_manual.v`
- Goal/auto/check: `Rocq/examples/QCP_demos_human/cmc_emit_ast_migration_goal.v`, `Rocq/examples/QCP_demos_human/cmc_emit_ast_migration_proof_auto.v`, `Rocq/examples/QCP_demos_human/cmc_emit_ast_migration_goal_check.v`

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

- Session: `cmc_emit_ast_migration-annotation-agent`
- Iteration: 1

This is the initial iteration. Read annotation-designing completely, follow its linked guides, and inspect the correct/incorrect examples relevant to this case before editing.

Feedback appended for this iteration:

- none (initial annotation iteration)

Required key-point plan: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_ast_migration-20261017141940/annotation-attempts/annotation-attempt1/annotation_plan.json`

## Problem context

- Problem Statement: Migrate ALL TWO runtime functions in /Users/nizitong/cmc/cmc_concrete_emit_ast.c from C*/HOL to QCP/Rocq, retaining runtime tokens and original full contracts. Targets: cm_emit_binding_address and cm_emit_binding_address_plan. Read original .c/.h and dependency definitions; frozen baseline at /Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_emit_ast/baseline. This is implementation verification, not whole compiler preservation. No user supplied formal QCP spec: owner translates source.

Reuse existing cmc_emit_plan_migration_lib.v plus existing core/counts/layout/globals/resolved closure. Do not edit any previous verified file. Preserve cmc_layout_migration_abi.h and cm_emitter layout. Reuse EXACT normalized helper contracts for cmc_global_address, cmc_local_offset, cmc_param_offset from cmc_layout_migration.c and cm_emit_resolved, cm_emit_resolved_fp_address from cmc_emit_resolved_migration.c. Do not import old manual/auto proofs or reprove old implementations.

Both function pre/post retain ALL TEN original pure facts: cm_wf_program p; f is total function lookup fid of p; structs=program_structs p; globals=program_globals p; binding_valid p f scope slot; slots_wf structs params; slots_wf structs locals; rep_globals_safe globals; rep_members_safe params; rep_members_safe locals. BOTH full program_context_rep and function_context_rep remain preserved. Direct function consumes only capacity for exact binding fragment and appends exact fragment to done in resolved representation. Plan wrapper consumes exact fragment++tail from plan budget and appends to done, tail unchanged. Do not add fid bounds, unrelated readiness/target premises, or replace complete wf_program by globals-wf. Use the SAME existing cm_lookup_policy and cm_codegen_obligations parameterization: cm_wf_program policy cg p retains every conjunct. This parameterization is inherited and its source instantiation boundary will be documented, not silently claimed as concrete full emitter semantics.

Source new models: cm_slots_prefix and cm_globals_prefix in cmc_lang.c near2209; cm_global_address near2246; cm_param_offset/cm_local_offset in cmc_codegen.c near606; cm_binding_address_code near634. Preserve list-recursion on arbitrary Z index (if index=0 then0 else head size+prefix tail(index-1)), including negative indices; do not replace by truncated nat-index prefix globally. Total function lookup uses existing policy, not new arbitrary map. Address fragment scope0=push(globaladdress), scope1=fp(localoffset), else fp(paramoffset). Binding_valid already exists and restricts scope legitimately. Preserve exact fragment, raw buffer representation and logical patch view.

Bridge reuse: cm_slots_size_matches__temp_context already in core lib; cm_rep_global_size_matches already in emit_globals lib; existing cm_binding_valid and size/length lemmas. Add only needed new definitions/prefix bridges. Source public cm_rep_member_prefix_matches / cm_rep_globals_prefix_matches are in defs near1706/2020; source 7 static cm_ast_* helpers belong to case proof. Main separately measures newly needed shared source closure vs existing dependencies. No Axiom/Admitted/Parameter in new library/manual.

Follow owner workflow, do not write manual in annotation stage. Record actual formal-case-lib-design/symexec/post-lib check invocation counts, failures and repair causes in agent_output.md. Stop writes at delivery; main will seal. Main independently replays C*, audits contract/runtime/model identity, collects effort, and updates skill only after controller done.

## Writable formal paths

- `QCP_examples/QCP_demos_human/cmc_emit_ast_migration.c`
- `Rocq/examples/QCP_demos_human/cmc_emit_ast_migration_lib.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_ast_migration_goal.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_ast_migration_proof_auto.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_ast_migration_proof_manual.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_ast_migration_goal_check.v`

Generated files may change only through the exact symbolic-execution command below.

## Agent-written specification

The function spec, internal annotations, and case-lib definitions or lemmas may be
written and revised together in this attempt. Rerun `formal-case-lib-design` and
symexec after changes. A specification change does not end this attempt.

## Commands

```text
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_ast_migration-20261017141940 --round cmc_emit_ast_migration-annotation-r1 --target-kind formal-case-lib-design
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases symexec --run cmc_emit_ast_migration-20261017141940 --round cmc_emit_ast_migration-annotation-r1
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_ast_migration-20261017141940 --round cmc_emit_ast_migration-annotation-r1 --target-kind formal-case-lib
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
