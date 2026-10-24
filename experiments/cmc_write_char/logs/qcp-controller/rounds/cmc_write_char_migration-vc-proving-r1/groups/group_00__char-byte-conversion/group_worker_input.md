# Group worker handoff

Read `.agents/skills/group-worker-proving/SKILL.md`, `.agents/skills/group-worker-proving/workflows/group-worker-proving.md`, and `.agents/skills/group-worker-proving/workflows/commands-and-checks.md` completely. This handoff adds only the current assignment; do not use a parent transcript or sibling output.

## Assignment

- Group: `char-byte-conversion`; attempt 1; earlier compact attempts 0
- Difficulty hint: 2/5
- Helpers: prohibited because this case has no active case lib


### `proof_of_cmc_write_char_partial_solve_wit_1_pure` — `aggressive_pre_process`

Prove every listed split goal first, each opening with `LLM_pre_process ltac:(...)` and an explicit closer. Then prove the top-level VC with `aggressive_pre_process` and close each resulting branch with only `Goal_apply <split-goal lemma>` for the corresponding split goal, with no other tactic in the top-level proof. This is a worker proof rule; controller validation does not inspect the spelling of these applications.

Split goals:

  - `proof_of_cmc_write_char_partial_solve_wit_1_pure_split_goal_1`: Introduce quantified values and pure premises, then discharge the pure consequent without transforming the antecedent's six local cells and two array segments. Unfold unsigned_last_nbits; note that the printed % denotes Z.rem. Specialize the already imported tower_machine_rem_byte__byte_encoding at char_value_pre and k = 0, discharge 0 <= 0 <= 7 by lia, simplify 256^0 and Z.quot by 1, and unfold tower_encode_byte at index 0 to obtain exactly the equality with tower_u8. There are no existential witnesses, array transformations, or new helpers.
  - `proof_of_cmc_write_char_partial_solve_wit_1_pure_split_goal_2`: Introduce quantified values and premises and reduce the entailment to its pure consequent, leaving the six local cells and two array segments as irrelevant antecedent resources. Unfold tower_u8 and use the lower-bound component of Z.mod_pos_bound char_value_pre 256, with 0 < 256 discharged arithmetically. No existential or resource transformation is required.
  - `proof_of_cmc_write_char_partial_solve_wit_1_pure_split_goal_3`: Use the same pure-consequent pattern as split goal 2, but take the strict upper-bound component of Z.mod_pos_bound char_value_pre 256 after unfolding tower_u8. The positive constant modulus supplies the only arithmetic premise; the antecedent heap needs no transformation and there are no existential witnesses.

## Write boundary

- Editable top-level proof spans: `proof_of_cmc_write_char_partial_solve_wit_1_pure`.
- Editable aggressive split-goal proof spans: `proof_of_cmc_write_char_partial_solve_wit_1_pure_split_goal_1`, `proof_of_cmc_write_char_partial_solve_wit_1_pure_split_goal_2`, `proof_of_cmc_write_char_partial_solve_wit_1_pure_split_goal_3`.
- Protected LLM_pre_process split blocks: none; their tokens remain `Proof. Abort.`.
- This case has no active case lib. Edit only the assigned manual proof spans; do not add helpers, imports, or another formal file.
- All declaration statements, other proof tokens, and the manual prelude stay protected.

Whitespace, comments, line endings, and the final newline are formatting. The controller compares protected Rocq tokens, declaration ownership, proof mode, and kernel results. For an aggressive top-level proof, follow the worker rule above and use `Goal_apply` for the split lemmas; controller validation deliberately does not inspect that tactic choice.


## Files

- Copied manual: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_write_char_migration-20261015193338/cmc_write_char_migration-vc-proving-r1/groups/group_00__char-byte-conversion/cmc_write_char_migration_proof_manual.v`
- Active case lib: none; no `group_worker_lib` exists for this group
- Terminal report: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_write_char_migration-20261015193338/rounds/cmc_write_char_migration-vc-proving-r1/groups/group_00__char-byte-conversion/group_worker_report.json`
- Notes: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_write_char_migration-20261015193338/rounds/cmc_write_char_migration-vc-proving-r1/groups/group_00__char-byte-conversion/group_worker_output.md`. They are optional for ordinary outcomes, but an
  `annotation-gap` blocker requires a non-empty explanation here because the controller preserves this
  exact Markdown as part of the aggregated annotation feedback.
- Previous proving round: none; no reuse note is expected.

The group directory must finish with only the copied manual.

## Planned helpers

- prohibited because this case has no active case lib

No helper may be planned or created because this case has no active case lib.

## Commands

Run a needed command unchanged with its bound cwd. Prefer a direct system-terminal call. If terminal operations are available only through `functions.exec`, use a transparent cell that awaits exactly one `tools.exec_command` to launch, or one `tools.write_stdin` to continue the same live session (or the runtime-documented normalized equivalent), and only forwards the result. Pass command/argv, every argument, and cwd unchanged when launching; preserve the exact session handle when continuing. Use a normalized equivalent only if its input shape accepts those values unchanged; never serialize argv into shell text, reparse a rendered command, or add quoting. Do not call another tool in the cell, construct, alter, sequence, wrap, pipe, or background commands. Preserve every outer cell and inner process/session handle until terminal exit; if the bridge yields a running cell, resume only that cell with `functions.wait`.

```text
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-debug --run cmc_write_char_migration-20261015193338 --round cmc_write_char_migration-vc-proving-r1 --group char-byte-conversion
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_write_char_migration-20261015193338 --round cmc_write_char_migration-vc-proving-r1 --target-kind group-development --group char-byte-conversion
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_write_char_migration-20261015193338 --round cmc_write_char_migration-vc-proving-r1 --target-kind group-check --group char-byte-conversion
```

Debug script: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_write_char_migration-20261015193338/_coq_builds/cmc_write_char_migration-vc-proving-r1/group_00/src/.coq_debug/group_00_char_byte_conversion.v`. Debug, development, and exact are optional proof feedback. `finalize-delivery` seals the formal manual and immediately runs the single mandatory controller group validation.

## Completion

Do not use raw Coq, Dune, Rocq MCP, `Admitted.`, new assumptions, forbidden lemmas, or the forbidden tactics `entailer!` and the bare alias `pre_process` (both are scanned exactly like a forbidden lemma; calls made inside `LLM_pre_process` and `Goal_apply` are unaffected). Repair a recoverable controller failure in this same worker. At the end, success is exactly `status: completed`; `blocked` adds one complete `blocker`. Do not copy version, diff, check status, or controller output.

If an assigned VC exposes an annotation/specification gap outside this group's write boundary, stop proof-only edits and return `blocked` with `blocker.failure_class` exactly `annotation-gap`. Its `vcs` must list every affected exact sealed-manual `name`, `parent`, and `annotation_location`; `message` explains existing premises and the missing conclusion. The controller validates and schedules from those structured VCs.
