# Annotation retry handoff

This is annotation iteration 2 in the run's single persistent annotation-agent session. Read the sealed failed VCs, edit the current annotation, run symbolic execution, and compare every old VC with the current manual.

## Assignment

- Session: `cmc_emit_expr_migration-annotation-agent`
- Round: `cmc_emit_expr_migration-annotation-r2`
- Attempt: `cmc_emit_expr_migration-annotation-r2-attempt-1`
- Retry reason: `vc-checking-annotation-gap`
- Main root: `/Users/nizitong/QCP/qcp-binary-democases`
- Terminal report: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_expr_migration-20261018184521/annotation-attempts/annotation-attempt2/agent_report.json`
- Human notes: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_expr_migration-20261018184521/annotation-attempts/annotation-attempt2/agent_output.md`
- Required key-point plan: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_expr_migration-20261018184521/annotation-attempts/annotation-attempt2/annotation_plan.json`

## Target files

- C: `QCP_examples/QCP_demos_human/cmc_emit_expr_migration.c`
- `formal_case_lib` candidate (present under `create` policy; edit it only during an allowed design/proof-helper step): `Rocq/examples/QCP_demos_human/cmc_emit_expr_migration_lib.v`
- Manual (present; generated/proved artifact, never edit it as annotation source): `Rocq/examples/QCP_demos_human/cmc_emit_expr_migration_proof_manual.v`
- Goal/auto/check: `Rocq/examples/QCP_demos_human/cmc_emit_expr_migration_goal.v`, `Rocq/examples/QCP_demos_human/cmc_emit_expr_migration_proof_auto.v`, `Rocq/examples/QCP_demos_human/cmc_emit_expr_migration_goal_check.v`

## Original blocker evidence

- `vc-checking` / `cmc_emit_expr_migration-vc-checking-r1-attempt-1`: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_expr_migration-20261018184521/rounds/cmc_emit_expr_migration-vc-checking-r1/agent_report.json`; `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_expr_migration-20261018184521/rounds/cmc_emit_expr_migration-vc-checking-r1/agent_output.md`

Previous annotation attempt artifacts:

- `cmc_emit_expr_migration-annotation-r1-attempt-1`: report `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_expr_migration-20261018184521/annotation-attempts/annotation-attempt1/agent_report.json`; notes `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_expr_migration-20261018184521/annotation-attempts/annotation-attempt1/agent_output.md`

Controller-recorded blocker details:

- {"failure_class": "annotation-gap", "kind": "missing-current-to-pre-equalities", "message": "Both alternatives of each listed whole VC require pc = pc_pre and temp = temp_pre, but neither entry-state variable occurs in any antecedent premise or spatial resource. The entry-state scalars are independently universally quantified. For example, CONST with e = CMConstE 0 CMIntTy, lvalue = pc = temp = 0, pc_pre = temp_pre = 1, empty done/tail and a capacity-1 empty emitter satisfies the antecedent while both required equalities are false for every existential simple. The same missing scalar bridge affects STRING, VAR, SIZEOF and GETC.", "repair_boundary": "Repair only the internal dispatcher which-implies annotations by carrying the current-to-@pre equalities in the premises from the surrounding unchanged-variable context, with generated establishing VCs, or reformulate the conversion without introducing unestablished entry equalities. Preserve the existing BODY and imported helper contracts, implementation, and code model; no arbitrary-equality axiom or lemma can repair this.", "vcs": [{"annotation_location": "QCP_examples/QCP_demos_human/cmc_emit_expr_migration.c:1625-1626, cm_emit_expr CONST branch emitter-plan conversion", "name": "proof_of_cm_emit_expr_which_implies_wit_2", "parent": null}, {"annotation_location": "QCP_examples/QCP_demos_human/cmc_emit_expr_migration.c:1634-1635, cm_emit_expr STRING branch emitter-plan conversion", "name": "proof_of_cm_emit_expr_which_implies_wit_4", "parent": null}, {"annotation_location": "QCP_examples/QCP_demos_human/cmc_emit_expr_migration.c:1643-1644, cm_emit_expr VAR branch emitter-plan conversion", "name": "proof_of_cm_emit_expr_which_implies_wit_6", "parent": null}, {"annotation_location": "QCP_examples/QCP_demos_human/cmc_emit_expr_migration.c:1703-1704, cm_emit_expr SIZEOF branch emitter-plan conversion", "name": "proof_of_cm_emit_expr_which_implies_wit_19", "parent": null}, {"annotation_location": "QCP_examples/QCP_demos_human/cmc_emit_expr_migration.c:1712-1713, cm_emit_expr GETC branch emitter-plan conversion", "name": "proof_of_cm_emit_expr_which_implies_wit_21", "parent": null}]}
- Controller main-check failure: {"clean_output_freshness": {"interrupted_output_recovery": {"removed_entry_count": 0, "removed_zero_byte_temp_count": 0, "status": "not-needed"}, "status": "passed"}, "formal_case_lib_contract": {"errors": [], "skipped": false, "status": "passed"}, "formal_case_lib_coqc": {"returncode": 0, "status": "passed"}, "formal_case_lib_dune": {"base_artifact_count": 160, "build_mode": "makefile", "current_cleanup": {"first_removed": null, "removed_count": 0, "status": "passed"}, "current_source_count": 1, "dependency_metrics": {"batch_count": 11, "coqdep_process_count": 11, "elapsed_seconds": 13.516578, "node_count": 161, "source_count": 161, "status": "resolved", "strategy": "breadth-batched-coqdep"}, "elapsed_seconds": 13.709388, "make_seconds": 0.00839, "rebuilt_count": 0, "returncode": 0, "status": "passed", "target": "Rocq/examples/QCP_demos_human/cmc_emit_expr_migration_lib.vo"}, "pre_symexec_formal_case_lib_coqc": {"returncode": 0, "status": "passed"}, "symexec": {"owner_generation_receipt": {"elapsed_seconds": 97.433, "performance_profile": "recursive-large", "recorded_at": "2026-10-18T11:03:52.494647Z", "timeout_seconds": 7200.0}, "returncode": 0, "reused_owner_generation": true, "status": "passed"}, "vc_comparisons": {"comparison_count": 0, "provable_count": 0, "statements": [], "status": "passed"}}

## Failed VCs

1. `cmc_emit_expr_migration-vc-checking-r1-attempt-1:proof_of_cm_emit_expr_which_implies_wit_2`
   - Parent: `none`
   - Annotation location: QCP_examples/QCP_demos_human/cmc_emit_expr_migration.c:1625-1626, cm_emit_expr CONST branch emitter-plan conversion
   - Sealed manual: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_expr_migration-20261018184521/annotation_history/annotation-attempt1/after/Rocq/examples/QCP_demos_human/cmc_emit_expr_migration_proof_manual.v`
   - Manual sha256: `a68575ed7dd343cf981d1c20edf4b265ab263993441f51d589ad00a4edee1161`
   - Statement sha256: `d72cb18d2dc69df10f5eed63abb9d9f7caf169636f2b206643b82d25e8ef08fd`
   - Old gap: Both alternatives of each listed whole VC require pc = pc_pre and temp = temp_pre, but neither entry-state variable occurs in any antecedent premise or spatial resource. The entry-state scalars are independently universally quantified. For example, CONST with e = CMConstE 0 CMIntTy, lvalue = pc = temp = 0, pc_pre = temp_pre = 1, empty done/tail and a capacity-1 empty emitter satisfies the antecedent while both required equalities are false for every existential simple. The same missing scalar bridge affects STRING, VAR, SIZEOF and GETC.
2. `cmc_emit_expr_migration-vc-checking-r1-attempt-1:proof_of_cm_emit_expr_which_implies_wit_4`
   - Parent: `none`
   - Annotation location: QCP_examples/QCP_demos_human/cmc_emit_expr_migration.c:1634-1635, cm_emit_expr STRING branch emitter-plan conversion
   - Sealed manual: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_expr_migration-20261018184521/annotation_history/annotation-attempt1/after/Rocq/examples/QCP_demos_human/cmc_emit_expr_migration_proof_manual.v`
   - Manual sha256: `a68575ed7dd343cf981d1c20edf4b265ab263993441f51d589ad00a4edee1161`
   - Statement sha256: `06ba10e35e7c9b70ef895b2eeceddf9bc433152419b9a0a8ee1ad23335c50403`
   - Old gap: Both alternatives of each listed whole VC require pc = pc_pre and temp = temp_pre, but neither entry-state variable occurs in any antecedent premise or spatial resource. The entry-state scalars are independently universally quantified. For example, CONST with e = CMConstE 0 CMIntTy, lvalue = pc = temp = 0, pc_pre = temp_pre = 1, empty done/tail and a capacity-1 empty emitter satisfies the antecedent while both required equalities are false for every existential simple. The same missing scalar bridge affects STRING, VAR, SIZEOF and GETC.
3. `cmc_emit_expr_migration-vc-checking-r1-attempt-1:proof_of_cm_emit_expr_which_implies_wit_6`
   - Parent: `none`
   - Annotation location: QCP_examples/QCP_demos_human/cmc_emit_expr_migration.c:1643-1644, cm_emit_expr VAR branch emitter-plan conversion
   - Sealed manual: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_expr_migration-20261018184521/annotation_history/annotation-attempt1/after/Rocq/examples/QCP_demos_human/cmc_emit_expr_migration_proof_manual.v`
   - Manual sha256: `a68575ed7dd343cf981d1c20edf4b265ab263993441f51d589ad00a4edee1161`
   - Statement sha256: `757b9b9b7a932b94f22b0a9a904dbb183113e9db20249664a9a10ca43a9c8c22`
   - Old gap: Both alternatives of each listed whole VC require pc = pc_pre and temp = temp_pre, but neither entry-state variable occurs in any antecedent premise or spatial resource. The entry-state scalars are independently universally quantified. For example, CONST with e = CMConstE 0 CMIntTy, lvalue = pc = temp = 0, pc_pre = temp_pre = 1, empty done/tail and a capacity-1 empty emitter satisfies the antecedent while both required equalities are false for every existential simple. The same missing scalar bridge affects STRING, VAR, SIZEOF and GETC.
4. `cmc_emit_expr_migration-vc-checking-r1-attempt-1:proof_of_cm_emit_expr_which_implies_wit_19`
   - Parent: `none`
   - Annotation location: QCP_examples/QCP_demos_human/cmc_emit_expr_migration.c:1703-1704, cm_emit_expr SIZEOF branch emitter-plan conversion
   - Sealed manual: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_expr_migration-20261018184521/annotation_history/annotation-attempt1/after/Rocq/examples/QCP_demos_human/cmc_emit_expr_migration_proof_manual.v`
   - Manual sha256: `a68575ed7dd343cf981d1c20edf4b265ab263993441f51d589ad00a4edee1161`
   - Statement sha256: `fcc3977581a42b72f3d664d327768ca1b32751849a33a9d723003e5a4faa5403`
   - Old gap: Both alternatives of each listed whole VC require pc = pc_pre and temp = temp_pre, but neither entry-state variable occurs in any antecedent premise or spatial resource. The entry-state scalars are independently universally quantified. For example, CONST with e = CMConstE 0 CMIntTy, lvalue = pc = temp = 0, pc_pre = temp_pre = 1, empty done/tail and a capacity-1 empty emitter satisfies the antecedent while both required equalities are false for every existential simple. The same missing scalar bridge affects STRING, VAR, SIZEOF and GETC.
5. `cmc_emit_expr_migration-vc-checking-r1-attempt-1:proof_of_cm_emit_expr_which_implies_wit_21`
   - Parent: `none`
   - Annotation location: QCP_examples/QCP_demos_human/cmc_emit_expr_migration.c:1712-1713, cm_emit_expr GETC branch emitter-plan conversion
   - Sealed manual: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_expr_migration-20261018184521/annotation_history/annotation-attempt1/after/Rocq/examples/QCP_demos_human/cmc_emit_expr_migration_proof_manual.v`
   - Manual sha256: `a68575ed7dd343cf981d1c20edf4b265ab263993441f51d589ad00a4edee1161`
   - Statement sha256: `59176f1d7a2a805c1dbabc511237c4d2c9ddb1d918e14a64f41e6aa67b967d9b`
   - Old gap: Both alternatives of each listed whole VC require pc = pc_pre and temp = temp_pre, but neither entry-state variable occurs in any antecedent premise or spatial resource. The entry-state scalars are independently universally quantified. For example, CONST with e = CMConstE 0 CMIntTy, lvalue = pc = temp = 0, pc_pre = temp_pre = 1, empty done/tail and a capacity-1 empty emitter satisfies the antecedent while both required equalities are false for every existential simple. The same missing scalar bridge affects STRING, VAR, SIZEOF and GETC.

## Previous VC changes

- none

## Rules to reload

The annotation agent must completely reload annotation-designing on every appended iteration, then follow all linked rules and inspect the original blocker evidence, sealed manuals, and current main-root files above.

- `.agents/skills/verification-orchestrator/SKILL.md`
- `.agents/skills/verification-orchestrator/workflows/state-handoffs-and-reports.md`
- `.agents/skills/verification-orchestrator/workflows/paths-and-commands.md`
- `.agents/skills/annotation-designing/SKILL.md`
- `.agents/skills/annotation-designing/workflows/annotation-designing.md`

## Writable formal paths

- `QCP_examples/QCP_demos_human/cmc_emit_expr_migration.c`
- `Rocq/examples/QCP_demos_human/cmc_emit_expr_migration_lib.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_expr_migration_goal.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_expr_migration_proof_auto.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_expr_migration_proof_manual.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_expr_migration_goal_check.v`

Generated files may change only through the exact symbolic-execution command below.

## Agent-written specification

The function spec, internal annotations, and case-lib definitions or lemmas may be
written and revised together in this attempt. Rerun `formal-case-lib-design` and
symexec after changes. A specification change does not end this attempt.

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

## Commands

```text
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_expr_migration-20261018184521 --round cmc_emit_expr_migration-annotation-r2 --target-kind formal-case-lib-design
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases symexec --run cmc_emit_expr_migration-20261018184521 --round cmc_emit_expr_migration-annotation-r2
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_expr_migration-20261018184521 --round cmc_emit_expr_migration-annotation-r2 --target-kind formal-case-lib
```

The standalone design check may be rerun after each specification or case-lib change and does not require generated goals. The later formal-case-lib Coq command uses the controller's single skinny-build plan: it stages only the exact current-case dependency closure, loads or builds its current prerequisites from the content-addressed cache, and reads fixed dependency `.vo` files from the selected sealed base. Before this local check, the controller asks the selected backend to prepare the exact case-lib target. A dependency that is merely unbuilt is therefore not an annotation defect.

The dependency graph comes only from the selected backend's exact target; the agent never observes, supplies, or
expands build targets. Do not copy selected-base output, dependency sources/artifacts, or another `_coq_builds` scope.

## Completion

Function specs, internal predicates, body annotations, case-lib definitions and lemmas, and `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_expr_migration-20261018184521/annotation-attempts/annotation-attempt2/annotation_plan.json` may change together when the spec is agent-written or after `unfreeze`. After every symexec, fill `vc_comparisons` from the exact old and current statements. Continue editing while a judgement is `unprovable` or `moved`; submit only when every failed VC is `provable`. Do not edit the proof manual or write proofs. Success contains only `status: completed`. Notes are optional.
