# Group worker handoff

Read `.agents/skills/group-worker-proving/SKILL.md`, `.agents/skills/group-worker-proving/workflows/group-worker-proving.md`, and `.agents/skills/group-worker-proving/workflows/commands-and-checks.md` completely. This handoff adds only the current assignment; do not use a parent transcript or sibling output.

## Assignment

- Group: `byte_encoding`; attempt 1; earlier compact attempts 0
- Difficulty hint: 5/5
- Required suffix for every new or adapted helper: `__byte_encoding`


### `proof_of_cmc_write_word_entail_wit_1` — `aggressive_pre_process`

Prove every listed split goal first, each opening with `LLM_pre_process ltac:(...)` and an explicit closer. Then prove the top-level VC with `aggressive_pre_process` and close each resulting branch with only `Goal_apply <split-goal lemma>` for the corresponding split goal, with no other tactic in the top-level proof. This is a worker proof rule; controller validation does not inspect the spelling of these applications.

Split goals:

  - `proof_of_cmc_write_word_entail_wit_1_split_goal_1`: Encoding pattern E, byte k=7, divisor 72057594037927936: introduce the pure equality over the unchanged prefix segment; specialize tower_machine_byte__byte_encoding at k=7 and normalize the numeric power. The wrapped 64-bit value is nonnegative, so C quotient agrees with floor division.
  - `proof_of_cmc_write_word_entail_wit_1_split_goal_2`: Encoding pattern E, byte k=6, divisor 281474976710656: introduce the pure equality over the unchanged prefix segment; specialize tower_machine_byte__byte_encoding at k=6 and normalize the numeric power. The wrapped 64-bit value is nonnegative, so C quotient agrees with floor division.
  - `proof_of_cmc_write_word_entail_wit_1_split_goal_3`: Encoding pattern E, byte k=5, divisor 1099511627776: introduce the pure equality over the unchanged prefix segment; specialize tower_machine_byte__byte_encoding at k=5 and normalize the numeric power. The wrapped 64-bit value is nonnegative, so C quotient agrees with floor division.
  - `proof_of_cmc_write_word_entail_wit_1_split_goal_4`: Encoding pattern E, byte k=4, divisor 4294967296: introduce the pure equality over the unchanged prefix segment; specialize tower_machine_byte__byte_encoding at k=4 and normalize the numeric power. The wrapped 64-bit value is nonnegative, so C quotient agrees with floor division.
  - `proof_of_cmc_write_word_entail_wit_1_split_goal_5`: Encoding pattern E, byte k=3, divisor 16777216: introduce the pure equality over the unchanged prefix segment; specialize tower_machine_byte__byte_encoding at k=3 and normalize the numeric power. The wrapped 64-bit value is nonnegative, so C quotient agrees with floor division.
  - `proof_of_cmc_write_word_entail_wit_1_split_goal_6`: Encoding pattern E, byte k=2, divisor 65536: introduce the pure equality over the unchanged prefix segment; specialize tower_machine_byte__byte_encoding at k=2 and normalize the numeric power. The wrapped 64-bit value is nonnegative, so C quotient agrees with floor division.
  - `proof_of_cmc_write_word_entail_wit_1_split_goal_7`: Encoding pattern E, byte k=1, divisor 256: introduce the pure equality over the unchanged prefix segment; specialize tower_machine_byte__byte_encoding at k=1 and normalize the numeric power. The wrapped 64-bit value is nonnegative, so C quotient agrees with floor division.
  - `proof_of_cmc_write_word_entail_wit_1_split_goal_8`: Encoding pattern E, byte k=0, divisor 1: introduce the pure equality over the unchanged prefix segment; specialize tower_machine_byte__byte_encoding at k=0 and normalize the numeric power; simplify quotient by 1 for the source expression without division.
  - `proof_of_cmc_write_word_entail_wit_1_split_goal_spatial`: Segment pattern S: replace ((cursor_pre + 1) + 1) by cursor_pre + 2 using integer arithmetic, then close the identical UCharArray.seg entailment by reflexivity. Prefix contents and data_pre coincide; no existential or heap split.

### `proof_of_cmc_write_word_partial_solve_wit_1_pure` — `aggressive_pre_process`

Prove every listed split goal first, each opening with `LLM_pre_process ltac:(...)` and an explicit closer. Then prove the top-level VC with `aggressive_pre_process` and close each resulting branch with only `Goal_apply <split-goal lemma>` for the corresponding split goal, with no other tactic in the top-level proof. This is a worker proof rule; controller validation does not inspect the spelling of these applications.

Split goals:

  - `proof_of_cmc_write_word_partial_solve_wit_1_pure_split_goal_1`: Encoding pattern E at k=0: leave the local scalar cells, initialized prefix and undefined suffix unused for the pure conclusion; specialize tower_machine_byte__byte_encoding, normalize 256^0; eliminate quotient by 1.
  - `proof_of_cmc_write_word_partial_solve_wit_1_pure_split_goal_2`: Bound pattern B, k=0, lower bound: unfold tower_encode_byte at this fixed index and tower_u8; project the lower bound from Z.mod_pos_bound with divisor 256. Introduce the pure fact from these scalar facts; the local cells and array segments require no transformation.
  - `proof_of_cmc_write_word_partial_solve_wit_1_pure_split_goal_3`: Bound pattern B, k=0, upper bound: unfold tower_encode_byte at this fixed index and tower_u8; project the upper bound from Z.mod_pos_bound with divisor 256. Introduce the pure fact from these scalar facts; the local cells and array segments require no transformation.

### `proof_of_cmc_write_word_partial_solve_wit_2_pure` — `aggressive_pre_process`

Prove every listed split goal first, each opening with `LLM_pre_process ltac:(...)` and an explicit closer. Then prove the top-level VC with `aggressive_pre_process` and close each resulting branch with only `Goal_apply <split-goal lemma>` for the corresponding split goal, with no other tactic in the top-level proof. This is a worker proof rule; controller validation does not inspect the spelling of these applications.

Split goals:

  - `proof_of_cmc_write_word_partial_solve_wit_2_pure_split_goal_1`: Encoding pattern E at k=1: leave the local scalar cells, initialized prefix and undefined suffix unused for the pure conclusion; specialize tower_machine_byte__byte_encoding, normalize 256^1, and use nonnegativity of unsigned_last_nbits for quotient-to-floor conversion.
  - `proof_of_cmc_write_word_partial_solve_wit_2_pure_split_goal_2`: Bound pattern B, k=1, lower bound: unfold tower_encode_byte at this fixed index and tower_u8; project the lower bound from Z.mod_pos_bound with divisor 256. Introduce the pure fact from these scalar facts; the local cells and array segments require no transformation.
  - `proof_of_cmc_write_word_partial_solve_wit_2_pure_split_goal_3`: Bound pattern B, k=1, upper bound: unfold tower_encode_byte at this fixed index and tower_u8; project the upper bound from Z.mod_pos_bound with divisor 256. Introduce the pure fact from these scalar facts; the local cells and array segments require no transformation.

## Write boundary

- Editable top-level proof spans: `proof_of_cmc_write_word_entail_wit_1`, `proof_of_cmc_write_word_partial_solve_wit_1_pure`, `proof_of_cmc_write_word_partial_solve_wit_2_pure`.
- Editable aggressive split-goal proof spans: `proof_of_cmc_write_word_entail_wit_1_split_goal_1`, `proof_of_cmc_write_word_entail_wit_1_split_goal_2`, `proof_of_cmc_write_word_entail_wit_1_split_goal_3`, `proof_of_cmc_write_word_entail_wit_1_split_goal_4`, `proof_of_cmc_write_word_entail_wit_1_split_goal_5`, `proof_of_cmc_write_word_entail_wit_1_split_goal_6`, `proof_of_cmc_write_word_entail_wit_1_split_goal_7`, `proof_of_cmc_write_word_entail_wit_1_split_goal_8`, `proof_of_cmc_write_word_entail_wit_1_split_goal_spatial`, `proof_of_cmc_write_word_partial_solve_wit_1_pure_split_goal_1`, `proof_of_cmc_write_word_partial_solve_wit_1_pure_split_goal_2`, `proof_of_cmc_write_word_partial_solve_wit_1_pure_split_goal_3`, `proof_of_cmc_write_word_partial_solve_wit_2_pure_split_goal_1`, `proof_of_cmc_write_word_partial_solve_wit_2_pure_split_goal_2`, `proof_of_cmc_write_word_partial_solve_wit_2_pure_split_goal_3`.
- Protected LLM_pre_process split blocks: none; their tokens remain `Proof. Abort.`.
- In `group_worker_lib`, append only proved suffixed helpers, token-identical sealed helper copies, and needed official imports.
- All declaration statements, other proof tokens, the manual prelude, and the seed library stay protected.

Whitespace, comments, line endings, and the final newline are formatting. The controller compares protected Rocq tokens, declaration ownership, proof mode, and kernel results. For an aggressive top-level proof, follow the worker rule above and use `Goal_apply` for the split lemmas; controller validation deliberately does not inspect that tactic choice.


## Files

- Copied manual: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_write_word_migration-20261015190516/cmc_write_word_migration-vc-proving-r1/groups/group_00__byte_encoding/cmc_write_word_migration_proof_manual.v`
- `group_worker_lib`: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_write_word_migration-20261015190516/cmc_write_word_migration-vc-proving-r1/groups/group_00__byte_encoding/cmc_write_word_migration_lib.v`
- Read-only `formal_case_lib`: `Rocq/examples/QCP_demos_human/cmc_write_word_migration_lib.v`
- Frozen helper candidates: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_write_word_migration-20261015190516/cmc_write_word_migration-vc-proving-r1/public_helper_snapshot.txt` — search by needed helper/predicate names and read only matching declarations; never import this file
- Terminal report: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_write_word_migration-20261015190516/rounds/cmc_write_word_migration-vc-proving-r1/groups/group_00__byte_encoding/group_worker_report.json`
- Notes: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_write_word_migration-20261015190516/rounds/cmc_write_word_migration-vc-proving-r1/groups/group_00__byte_encoding/group_worker_output.md`. They are optional for ordinary outcomes, but an
  `annotation-gap` blocker requires a non-empty explanation here because the controller preserves this
  exact Markdown as part of the aggregated annotation feedback.
- Previous proving round: none; no reuse note is expected.

The group directory must finish with the copied manual and `group_worker_lib`.

## Planned helpers

- `tower_mod_div_byte__byte_encoding`; public; expected use: Prove forall z d q : Z, 0 < d -> 0 < q -> ((z mod (d * 256 * q)) / d) mod 256 = (z / d) mod 256. Use the Euclidean quotient/remainder decomposition for z by d*256*q and the positive-divisor addition/multiplication laws; division changes by a multiple of 256*q, removed by the final modulo. This holds for negative z as well. Used by the machine-byte bridge with d=256^k and q=256^(7-k).
- `tower_machine_byte__byte_encoding`; public; expected use: Prove forall z k : Z, 0 <= k <= 7 -> unsigned_last_nbits ((Z.quot (unsigned_last_nbits z 64) (256^k)) mod 256) 8 = tower_encode_byte z k. Unfold unsigned truncation to modulo powers of two; remove outer 8-bit truncation by modulo idempotence, use nonnegativity of z mod 2^64 to replace quot by div, apply tower_mod_div_byte__byte_encoding with d=256^k and q=256^(7-k), then enumerate k=0..7 and combine iterated positive floor divisions to division by 256^k. All positivity and power identities are numeric after the finite case split. No signed-range premise is needed, which is essential for entail_wit_1 splits.

`local` stays in this group. A proved `public` helper is promoted by the controller for later rounds. Historical token-identical copies may keep their sealed suffix; adaptations use this group's suffix.

## Commands

Run a needed command unchanged with its bound cwd. Prefer a direct system-terminal call. If terminal operations are available only through `functions.exec`, use a transparent cell that awaits exactly one `tools.exec_command` to launch, or one `tools.write_stdin` to continue the same live session (or the runtime-documented normalized equivalent), and only forwards the result. Pass command/argv, every argument, and cwd unchanged when launching; preserve the exact session handle when continuing. Use a normalized equivalent only if its input shape accepts those values unchanged; never serialize argv into shell text, reparse a rendered command, or add quoting. Do not call another tool in the cell, construct, alter, sequence, wrap, pipe, or background commands. Preserve every outer cell and inner process/session handle until terminal exit; if the bridge yields a running cell, resume only that cell with `functions.wait`.

```text
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-debug --run cmc_write_word_migration-20261015190516 --round cmc_write_word_migration-vc-proving-r1 --group byte_encoding
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_write_word_migration-20261015190516 --round cmc_write_word_migration-vc-proving-r1 --target-kind group-development --group byte_encoding
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_write_word_migration-20261015190516 --round cmc_write_word_migration-vc-proving-r1 --target-kind group-check --group byte_encoding
```

Debug script: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_write_word_migration-20261015190516/_coq_builds/cmc_write_word_migration-vc-proving-r1/group_00/src/.coq_debug/group_00_byte_encoding.v`. Debug, development, and exact are optional proof feedback. `finalize-delivery` seals the two formal files and immediately runs the single mandatory controller group validation.

## Completion

Do not use raw Coq, Dune, Rocq MCP, `Admitted.`, new assumptions, forbidden lemmas, or the forbidden tactics `entailer!` and the bare alias `pre_process` (both are scanned exactly like a forbidden lemma; calls made inside `LLM_pre_process` and `Goal_apply` are unaffected). Repair a recoverable controller failure in this same worker. At the end, success is exactly `status: completed`; `blocked` adds one complete `blocker`. Do not copy version, diff, check status, or controller output.

If an assigned VC exposes an annotation/specification gap outside this group's write boundary, stop proof-only edits and return `blocked` with `blocker.failure_class` exactly `annotation-gap`. Its `vcs` must list every affected exact sealed-manual `name`, `parent`, and `annotation_location`; `message` explains existing premises and the missing conclusion. The controller validates and schedules from those structured VCs.
