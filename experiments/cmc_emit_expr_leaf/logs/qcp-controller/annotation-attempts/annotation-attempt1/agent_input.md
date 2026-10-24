# annotation handoff

This Markdown file, current files under the main root, and the listed skill docs are the source of truth. Do not use unstated parent-chat context.

## Assignment

- Round: `cmc_emit_expr_leaf_migration-annotation-r1`
- Attempt: `cmc_emit_expr_leaf_migration-annotation-r1-attempt-1` (index 1)
- Main root: `/Users/nizitong/QCP/qcp-binary-democases`
- Terminal report: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_expr_leaf_migration-20261017144315/annotation-attempts/annotation-attempt1/agent_report.json`
- Optional human notes: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_expr_leaf_migration-20261017144315/annotation-attempts/annotation-attempt1/agent_output.md`

## Target files

- C: `QCP_examples/QCP_demos_human/cmc_emit_expr_leaf_migration.c`
- `formal_case_lib` candidate (present under `create` policy; edit it only during an allowed design/proof-helper step): `Rocq/examples/QCP_demos_human/cmc_emit_expr_leaf_migration_lib.v`
- Manual (missing; this is an optional generated artifact, and only controller symbolic execution may create it): `Rocq/examples/QCP_demos_human/cmc_emit_expr_leaf_migration_proof_manual.v`
- Goal/auto/check: `Rocq/examples/QCP_demos_human/cmc_emit_expr_leaf_migration_goal.v`, `Rocq/examples/QCP_demos_human/cmc_emit_expr_leaf_migration_proof_auto.v`, `Rocq/examples/QCP_demos_human/cmc_emit_expr_leaf_migration_goal_check.v`

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

- Session: `cmc_emit_expr_leaf_migration-annotation-agent`
- Iteration: 1

This is the initial iteration. Read annotation-designing completely, follow its linked guides, and inspect the correct/incorrect examples relevant to this case before editing.

Feedback appended for this iteration:

- none (initial annotation iteration)

Required key-point plan: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_expr_leaf_migration-20261017144315/annotation-attempts/annotation-attempt1/annotation_plan.json`

## Problem context

- Problem Statement: Migrate ALL NINE runtime functions of /Users/nizitong/cmc/cmc_concrete_emit_expr_leaf.c from C*/HOL to QCP/Rocq. Include static cmc_const_immediate and cm_sizeof_value plus cm_emit_const_expr, cm_emit_string_expr, cm_emit_getc_expr, cm_type_size_value, cm_emit_sizeof_expr, cm_member_array_value_context, cm_member_offset_value_context. Keep exact runtime tokens including static; ABI header/emitter unchanged. Frozen source/dependencies at /Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_emit_expr_leaf/baseline. Read whole original .c/.h, not only hints. No user QCP formal spec supplied.

Original header has a discrepancy: cm_emit_const_expr .h omits cm_type_code_wf ty, whereas body contract includes it in BOTH pre/post. Preserve the body contract (verified implementation baseline); main documents discrepancy, do not silently remove that premise or claim weaker header verified. All other source pre/post facts and full program/function/expression resources must remain. Source static helpers are runtime bodies, not assumed prototypes.

Reuse already verified layout/counts/core/globals/resolved/plan/ast/word definitions and lemmas as applicable. Do not change earlier verified files or import old manual/auto proofs. Helper contracts must match exact previous verified definitions: cm_emit_plan from cmc_emit_plan_migration.c; cmc_string_address, cmc_type_size_at, cmc_member_array, cmc_pointee, cmc_member_offset_at from cmc_layout_migration.c. Any unused helper need not be declared. Reuse unsigned byte bridge from word lib, cm_char_encode from core, arbitrary-Z prefix bridge from AST, existing type encoding/member lemmas from layout/counts.

Const helper: all signed64 value; type_code_wf and exact encode only. Char normalization is Euclidean low byte (unsigned64 conversion then %256 then uchar), including negative inputs; non-char identity. Do not add scalar type or input nonnegative premises.

Four leaf emitters: preserve lvalue in[0,1], source constructor identity and total f lookup; exact leaf code fragment appended and corresponding plan prefix consumed; lvalue1 emits empty code and preserves resources. const includes type_code_wf; string includes all sid[0,INT_MAX], typed, safe globals/strings and combined-size facts in BOTH pre/post (no sid<length strengthening); sizeof preserves typed/type-code-wf/type_refs/structs-safe. getc does not require typed or wf.

Source cm_expr_code_for and cm_emit_expr_pair are not yet fully migrated. For this leaf-only case either migrate exact required expression-model closure, or use an explicitly named leaf-restricted model (NOT a falsely claimed general cm_expr_code_for with dummy nonleaf clauses) and provide exact source-equation correspondence for Const/String/Getc/Sizeof under the existing constructor premises; no new input assumption and no new arbitrary code axiom. Mark unsupported nonleaf behavior explicitly; do not expand task into whole compiler unnecessarily. Source definitions at defs581 and codegen710. Keep SAME existing total cm_lookup_policy, typed_program; no new fid bounds.

Type-size helpers return semantic cm_type_size(structs,asked), not representation size alone. Need bridge under original typed/type_code_wf/type_refs; reuse scalar bridges, add only absent struct/prefix/type bridge closure. Member wrappers keep every original count/typed/type/membership/structs-safe premise and exact return; original pointer encoding modulo uses C rem (QCP Z.rem), semantic bridge must handle signs correctly from original facts. No new sid/mid bounds unless derived.

Potential public bridges: defs cm_rep_string_address_matches(2124), cm_rep_type_size_matches(1641), cm_rep_struct_member_prefix_matches(1857). Reuse existing definitions where semantically equivalent; preserve arbitrary Z prefix semantics and source struct slot size versus ordinary slot size distinction. Main separately inventories source closure and incremental costs.

Follow full annotation owner workflow, no manual editing. Record actual design/symexec/post-lib invocation counts, failures and repairs; stop writes at terminal delivery. Main replays original C*, audits semantics/runtime and measures final costs; skill updates only after done.

## Writable formal paths

- `QCP_examples/QCP_demos_human/cmc_emit_expr_leaf_migration.c`
- `Rocq/examples/QCP_demos_human/cmc_emit_expr_leaf_migration_lib.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_expr_leaf_migration_goal.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_expr_leaf_migration_proof_auto.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_expr_leaf_migration_proof_manual.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_expr_leaf_migration_goal_check.v`

Generated files may change only through the exact symbolic-execution command below.

## Agent-written specification

The function spec, internal annotations, and case-lib definitions or lemmas may be
written and revised together in this attempt. Rerun `formal-case-lib-design` and
symexec after changes. A specification change does not end this attempt.

## Commands

```text
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_expr_leaf_migration-20261017144315 --round cmc_emit_expr_leaf_migration-annotation-r1 --target-kind formal-case-lib-design
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases symexec --run cmc_emit_expr_leaf_migration-20261017144315 --round cmc_emit_expr_leaf_migration-annotation-r1
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_expr_leaf_migration-20261017144315 --round cmc_emit_expr_leaf_migration-annotation-r1 --target-kind formal-case-lib
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
