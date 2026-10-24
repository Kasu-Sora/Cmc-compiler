# Annotation retry handoff

This is annotation iteration 2 in the run's single persistent annotation-agent session. Read the sealed failed VCs, edit the current annotation, run symbolic execution, and compare every old VC with the current manual.

## Assignment

- Session: `cmc_emit_stmt_migration-annotation-agent`
- Round: `cmc_emit_stmt_migration-annotation-r2`
- Attempt: `cmc_emit_stmt_migration-annotation-r2-attempt-1`
- Retry reason: `vc-checking-annotation-gap`
- Main root: `/Users/nizitong/QCP/qcp-binary-democases`
- Terminal report: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_stmt_migration-20261019010952/annotation-attempts/annotation-attempt2/agent_report.json`
- Human notes: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_stmt_migration-20261019010952/annotation-attempts/annotation-attempt2/agent_output.md`
- Required key-point plan: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_stmt_migration-20261019010952/annotation-attempts/annotation-attempt2/annotation_plan.json`

## Target files

- C: `QCP_examples/QCP_demos_human/cmc_emit_stmt_migration.c`
- `formal_case_lib` candidate (present under `create` policy; edit it only during an allowed design/proof-helper step): `Rocq/examples/QCP_demos_human/cmc_emit_stmt_migration_lib.v`
- Manual (present; generated/proved artifact, never edit it as annotation source): `Rocq/examples/QCP_demos_human/cmc_emit_stmt_migration_proof_manual.v`
- Goal/auto/check: `Rocq/examples/QCP_demos_human/cmc_emit_stmt_migration_goal.v`, `Rocq/examples/QCP_demos_human/cmc_emit_stmt_migration_proof_auto.v`, `Rocq/examples/QCP_demos_human/cmc_emit_stmt_migration_goal_check.v`

## Original blocker evidence

- `vc-checking` / `cmc_emit_stmt_migration-vc-checking-r1-attempt-1`: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_stmt_migration-20261019010952/rounds/cmc_emit_stmt_migration-vc-checking-r1/agent_report.json`; `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_stmt_migration-20261019010952/rounds/cmc_emit_stmt_migration-vc-checking-r1/agent_output.md`

Previous annotation attempt artifacts:

- `cmc_emit_stmt_migration-annotation-r1-attempt-1`: report `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_stmt_migration-20261019010952/annotation-attempts/annotation-attempt1/agent_report.json`; notes `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_stmt_migration-20261019010952/annotation-attempts/annotation-attempt1/agent_output.md`

Controller-recorded blocker details:

- {"failure_class": "annotation-gap", "kind": "missing-stack-resources-in-which-implies", "message": "Six no-split whole-goal entailments introduce C stack data_at resources only in their consequent. Witnesses 10, 21, 43 and 60 require &break_pc and &continue_pc cells; witness 48 additionally requires &fid, &pc, &temp and &continue_pc; witness 53 requires &fid, &pc, &temp and &break_pc. Their antecedents contain only a resolved emitter-plan resource and pure facts. The duplicated disjuncts have the same defect. A heap holding only the emitter/output representation, with these stack addresses unallocated, satisfies the antecedent and cannot satisfy the consequent. These are false whole goals, not failed aggressive splits.", "repair_boundary": "Repair internal which-implies annotations: retain/read all C locals used only on the right also on the left, with their unchanged values (e.g. explicit data_at cells or suitable left-hand scalar facts that cause QCP to retain those cells). Preserve all function contracts, runtime and model meanings. Regenerate VCs and verify the bridge/resources are present in both sides. No public axiom or weakened postcondition can repair this structural omission.", "vcs": [{"annotation_location": "QCP_examples/QCP_demos_human/cmc_emit_stmt_migration.c:433: CMExprS final emitter-plan folding which-implies", "name": "proof_of_cmc_emit_stmt_which_implies_wit_10", "parent": null}, {"annotation_location": "QCP_examples/QCP_demos_human/cmc_emit_stmt_migration.c:506: CMInitS final emitter-plan folding which-implies", "name": "proof_of_cmc_emit_stmt_which_implies_wit_21", "parent": null}, {"annotation_location": "QCP_examples/QCP_demos_human/cmc_emit_stmt_migration.c:637: CMWhileS final emitter-plan folding which-implies", "name": "proof_of_cmc_emit_stmt_which_implies_wit_43", "parent": null}, {"annotation_location": "QCP_examples/QCP_demos_human/cmc_emit_stmt_migration.c:668: CMBreakS final emitter-plan folding which-implies", "name": "proof_of_cmc_emit_stmt_which_implies_wit_48", "parent": null}, {"annotation_location": "QCP_examples/QCP_demos_human/cmc_emit_stmt_migration.c:699: CMContinueS final emitter-plan folding which-implies", "name": "proof_of_cmc_emit_stmt_which_implies_wit_53", "parent": null}, {"annotation_location": "QCP_examples/QCP_demos_human/cmc_emit_stmt_migration.c:741: CMReturnS final emitter-plan folding which-implies", "name": "proof_of_cmc_emit_stmt_which_implies_wit_60", "parent": null}]}
- Controller main-check failure: {"clean_output_freshness": {"interrupted_output_recovery": {"removed_entry_count": 0, "removed_zero_byte_temp_count": 0, "status": "not-needed"}, "status": "passed"}, "formal_case_lib_contract": {"errors": [], "skipped": false, "status": "passed"}, "formal_case_lib_coqc": {"returncode": 0, "status": "passed"}, "formal_case_lib_dune": {"base_artifact_count": 162, "build_mode": "makefile", "current_cleanup": {"first_removed": null, "removed_count": 0, "status": "passed"}, "current_source_count": 1, "dependency_metrics": {"batch_count": 7, "coqdep_process_count": 7, "elapsed_seconds": 8.373077, "node_count": 163, "source_count": 163, "status": "resolved", "strategy": "breadth-batched-coqdep"}, "elapsed_seconds": 8.562203, "make_seconds": 0.008012, "rebuilt_count": 0, "returncode": 0, "status": "passed", "target": "Rocq/examples/QCP_demos_human/cmc_emit_stmt_migration_lib.vo"}, "pre_symexec_formal_case_lib_coqc": {"returncode": 0, "status": "passed"}, "symexec": {"owner_generation_receipt": {"elapsed_seconds": 32.745, "performance_profile": "recursive-large", "recorded_at": "2026-10-18T17:21:10.687302Z", "timeout_seconds": 7200.0}, "returncode": 0, "reused_owner_generation": true, "status": "passed"}, "vc_comparisons": {"comparison_count": 0, "provable_count": 0, "statements": [], "status": "passed"}}

## Failed VCs

1. `cmc_emit_stmt_migration-vc-checking-r1-attempt-1:proof_of_cmc_emit_stmt_which_implies_wit_10`
   - Parent: `none`
   - Annotation location: QCP_examples/QCP_demos_human/cmc_emit_stmt_migration.c:433: CMExprS final emitter-plan folding which-implies
   - Sealed manual: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_stmt_migration-20261019010952/annotation_history/annotation-attempt1/after/Rocq/examples/QCP_demos_human/cmc_emit_stmt_migration_proof_manual.v`
   - Manual sha256: `ba053a4980b59d91e38c5d29ebcc67ef5d76ffc1b78b860bdea2010a57f7b654`
   - Statement sha256: `735e3ff04038d623fbf87c6f83a9ca48bbce64022ea3566c25bc36693cc48e3e`
   - Old gap: Six no-split whole-goal entailments introduce C stack data_at resources only in their consequent. Witnesses 10, 21, 43 and 60 require &break_pc and &continue_pc cells; witness 48 additionally requires &fid, &pc, &temp and &continue_pc; witness 53 requires &fid, &pc, &temp and &break_pc. Their antecedents contain only a resolved emitter-plan resource and pure facts. The duplicated disjuncts have the same defect. A heap holding only the emitter/output representation, with these stack addresses unallocated, satisfies the antecedent and cannot satisfy the consequent. These are false whole goals, not failed aggressive splits.
2. `cmc_emit_stmt_migration-vc-checking-r1-attempt-1:proof_of_cmc_emit_stmt_which_implies_wit_21`
   - Parent: `none`
   - Annotation location: QCP_examples/QCP_demos_human/cmc_emit_stmt_migration.c:506: CMInitS final emitter-plan folding which-implies
   - Sealed manual: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_stmt_migration-20261019010952/annotation_history/annotation-attempt1/after/Rocq/examples/QCP_demos_human/cmc_emit_stmt_migration_proof_manual.v`
   - Manual sha256: `ba053a4980b59d91e38c5d29ebcc67ef5d76ffc1b78b860bdea2010a57f7b654`
   - Statement sha256: `966026fb42c4bcbbfa739efaf3b8e4d797ee9b77c80890c4f9d224bef21815f8`
   - Old gap: Six no-split whole-goal entailments introduce C stack data_at resources only in their consequent. Witnesses 10, 21, 43 and 60 require &break_pc and &continue_pc cells; witness 48 additionally requires &fid, &pc, &temp and &continue_pc; witness 53 requires &fid, &pc, &temp and &break_pc. Their antecedents contain only a resolved emitter-plan resource and pure facts. The duplicated disjuncts have the same defect. A heap holding only the emitter/output representation, with these stack addresses unallocated, satisfies the antecedent and cannot satisfy the consequent. These are false whole goals, not failed aggressive splits.
3. `cmc_emit_stmt_migration-vc-checking-r1-attempt-1:proof_of_cmc_emit_stmt_which_implies_wit_43`
   - Parent: `none`
   - Annotation location: QCP_examples/QCP_demos_human/cmc_emit_stmt_migration.c:637: CMWhileS final emitter-plan folding which-implies
   - Sealed manual: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_stmt_migration-20261019010952/annotation_history/annotation-attempt1/after/Rocq/examples/QCP_demos_human/cmc_emit_stmt_migration_proof_manual.v`
   - Manual sha256: `ba053a4980b59d91e38c5d29ebcc67ef5d76ffc1b78b860bdea2010a57f7b654`
   - Statement sha256: `775aa25fda8fa81883d2e5b09ccf10e3d1a9cc951a5a4f18925a487f2679173a`
   - Old gap: Six no-split whole-goal entailments introduce C stack data_at resources only in their consequent. Witnesses 10, 21, 43 and 60 require &break_pc and &continue_pc cells; witness 48 additionally requires &fid, &pc, &temp and &continue_pc; witness 53 requires &fid, &pc, &temp and &break_pc. Their antecedents contain only a resolved emitter-plan resource and pure facts. The duplicated disjuncts have the same defect. A heap holding only the emitter/output representation, with these stack addresses unallocated, satisfies the antecedent and cannot satisfy the consequent. These are false whole goals, not failed aggressive splits.
4. `cmc_emit_stmt_migration-vc-checking-r1-attempt-1:proof_of_cmc_emit_stmt_which_implies_wit_48`
   - Parent: `none`
   - Annotation location: QCP_examples/QCP_demos_human/cmc_emit_stmt_migration.c:668: CMBreakS final emitter-plan folding which-implies
   - Sealed manual: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_stmt_migration-20261019010952/annotation_history/annotation-attempt1/after/Rocq/examples/QCP_demos_human/cmc_emit_stmt_migration_proof_manual.v`
   - Manual sha256: `ba053a4980b59d91e38c5d29ebcc67ef5d76ffc1b78b860bdea2010a57f7b654`
   - Statement sha256: `3042640860a9b8ddfe42e5ff531c3cbe91494da9e1064f9b84199ad3e7118c4d`
   - Old gap: Six no-split whole-goal entailments introduce C stack data_at resources only in their consequent. Witnesses 10, 21, 43 and 60 require &break_pc and &continue_pc cells; witness 48 additionally requires &fid, &pc, &temp and &continue_pc; witness 53 requires &fid, &pc, &temp and &break_pc. Their antecedents contain only a resolved emitter-plan resource and pure facts. The duplicated disjuncts have the same defect. A heap holding only the emitter/output representation, with these stack addresses unallocated, satisfies the antecedent and cannot satisfy the consequent. These are false whole goals, not failed aggressive splits.
5. `cmc_emit_stmt_migration-vc-checking-r1-attempt-1:proof_of_cmc_emit_stmt_which_implies_wit_53`
   - Parent: `none`
   - Annotation location: QCP_examples/QCP_demos_human/cmc_emit_stmt_migration.c:699: CMContinueS final emitter-plan folding which-implies
   - Sealed manual: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_stmt_migration-20261019010952/annotation_history/annotation-attempt1/after/Rocq/examples/QCP_demos_human/cmc_emit_stmt_migration_proof_manual.v`
   - Manual sha256: `ba053a4980b59d91e38c5d29ebcc67ef5d76ffc1b78b860bdea2010a57f7b654`
   - Statement sha256: `a5f9e8cd80ad06e5662a6b1d0dea9f7f69f9ec14354e22be5ce0153e5873d0a3`
   - Old gap: Six no-split whole-goal entailments introduce C stack data_at resources only in their consequent. Witnesses 10, 21, 43 and 60 require &break_pc and &continue_pc cells; witness 48 additionally requires &fid, &pc, &temp and &continue_pc; witness 53 requires &fid, &pc, &temp and &break_pc. Their antecedents contain only a resolved emitter-plan resource and pure facts. The duplicated disjuncts have the same defect. A heap holding only the emitter/output representation, with these stack addresses unallocated, satisfies the antecedent and cannot satisfy the consequent. These are false whole goals, not failed aggressive splits.
6. `cmc_emit_stmt_migration-vc-checking-r1-attempt-1:proof_of_cmc_emit_stmt_which_implies_wit_60`
   - Parent: `none`
   - Annotation location: QCP_examples/QCP_demos_human/cmc_emit_stmt_migration.c:741: CMReturnS final emitter-plan folding which-implies
   - Sealed manual: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_stmt_migration-20261019010952/annotation_history/annotation-attempt1/after/Rocq/examples/QCP_demos_human/cmc_emit_stmt_migration_proof_manual.v`
   - Manual sha256: `ba053a4980b59d91e38c5d29ebcc67ef5d76ffc1b78b860bdea2010a57f7b654`
   - Statement sha256: `040de104c16c0f316628ad2f1f4eefe56c3fee517e1a55d89a64f29b28147320`
   - Old gap: Six no-split whole-goal entailments introduce C stack data_at resources only in their consequent. Witnesses 10, 21, 43 and 60 require &break_pc and &continue_pc cells; witness 48 additionally requires &fid, &pc, &temp and &continue_pc; witness 53 requires &fid, &pc, &temp and &break_pc. Their antecedents contain only a resolved emitter-plan resource and pure facts. The duplicated disjuncts have the same defect. A heap holding only the emitter/output representation, with these stack addresses unallocated, satisfies the antecedent and cannot satisfy the consequent. These are false whole goals, not failed aggressive splits.

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

- `QCP_examples/QCP_demos_human/cmc_emit_stmt_migration.c`
- `Rocq/examples/QCP_demos_human/cmc_emit_stmt_migration_lib.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_stmt_migration_goal.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_stmt_migration_proof_auto.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_stmt_migration_proof_manual.v`
- `Rocq/examples/QCP_demos_human/cmc_emit_stmt_migration_goal_check.v`

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
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_stmt_migration-20261019010952 --round cmc_emit_stmt_migration-annotation-r2 --target-kind formal-case-lib-design
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases symexec --run cmc_emit_stmt_migration-20261019010952 --round cmc_emit_stmt_migration-annotation-r2
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_stmt_migration-20261019010952 --round cmc_emit_stmt_migration-annotation-r2 --target-kind formal-case-lib
```

The standalone design check may be rerun after each specification or case-lib change and does not require generated goals. The later formal-case-lib Coq command uses the controller's single skinny-build plan: it stages only the exact current-case dependency closure, loads or builds its current prerequisites from the content-addressed cache, and reads fixed dependency `.vo` files from the selected sealed base. Before this local check, the controller asks the selected backend to prepare the exact case-lib target. A dependency that is merely unbuilt is therefore not an annotation defect.

The dependency graph comes only from the selected backend's exact target; the agent never observes, supplies, or
expands build targets. Do not copy selected-base output, dependency sources/artifacts, or another `_coq_builds` scope.

## Completion

Function specs, internal predicates, body annotations, case-lib definitions and lemmas, and `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_stmt_migration-20261019010952/annotation-attempts/annotation-attempt2/annotation_plan.json` may change together when the spec is agent-written or after `unfreeze`. After every symexec, fill `vc_comparisons` from the exact old and current statements. Continue editing while a judgement is `unprovable` or `moved`; submit only when every failed VC is `provable`. Do not edit the proof manual or write proofs. Success contains only `status: completed`. Notes are optional.
