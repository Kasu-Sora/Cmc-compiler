# Group worker handoff

Read `.agents/skills/group-worker-proving/SKILL.md`, `.agents/skills/group-worker-proving/workflows/group-worker-proving.md`, and `.agents/skills/group-worker-proving/workflows/commands-and-checks.md` completely. This handoff adds only the current assignment; do not use a parent transcript or sibling output.

## Assignment

- Group: `initialized-emission`; attempt 1; earlier compact attempts 0
- Difficulty hint: 3/5
- Required suffix for every new or adapted helper: `__initialized_emission`


### `proof_of_cmc_emit_globals_entail_wit_2_1` — `LLM_pre_process`

Strategy: Choose the full-resource left disjunct. From PreH9, PreH16 and the code=1 guard obtain the initialized-char size/bytes facts using cm_initialized_char_facts__initialized_emission. Instantiate head_2=head and tail=tail_2. Identify retval with cm_rep_global_size head definitionally; the supplied 0..1048560 bounds make signed_last_nbits retval 32 equal retval. Rewrite size to 1 and cm_global_bytes to the singleton tower_u8 byte. The output and undefined segments then match exactly; cancel the five node fields and tail list, and discharge copied pure facts/reflexive equalities. This joins the char-writer postcondition to the recursive-call assertion.

Prove only the top-level VC, opening with `LLM_pre_process ltac:(...)` and an explicit closer; do not edit its split goals.

Split goals:

  - none generated

### `proof_of_cmc_emit_globals_entail_wit_2_2` — `LLM_pre_process`

Strategy: Choose the full-resource left disjunct. Use PreH9, the nonzero initialization flag and code<>1 with cm_initialized_word_facts__initialized_emission to identify global size=8 and global bytes=tower_word_bytes(init). Instantiate head_2=head and tail=tail_2. The slot-size return equality identifies retval with global size; use its supplied 0..1048560 bounds to eliminate the signed 32-bit cast. Rewrite the two output segment endpoints and byte list, cancel all five node fields plus tail and buffer resources, and copy the pure facts. This joins the word-writer postcondition to the recursive-call assertion.

Prove only the top-level VC, opening with `LLM_pre_process ltac:(...)` and an explicit closer; do not edit its split goals.

Split goals:

  - none generated

### `proof_of_cmc_emit_globals_partial_solve_wit_2_pure` — `aggressive_pre_process`

Prove every listed split goal first, each opening with `LLM_pre_process ltac:(...)` and an explicit closer. Then prove the top-level VC with `aggressive_pre_process` and close each resulting branch with only `Goal_apply <split-goal lemma>` for the corresponding split goal, with no other tactic in the top-level proof. This is a worker proof rule; controller validation does not inspect the spelling of these applications.

Split goals:

  - `proof_of_cmc_emit_globals_partial_solve_wit_2_pure_split_goal_1`: The goal is pure cursor_pre+1<=capacity_pre; retain arbitrary stack, node, tail and buffer resources as the antecedent. Apply cm_initialized_char_facts__initialized_emission with PreH25, PreH32 and PreH17, obtaining head size=1. Rewrite PreH31 and combine it with nonnegative tail size PreH30 by lia; introduce the resulting pure assertion. No existential or spatial reconstruction is required.

### `proof_of_cmc_emit_globals_partial_solve_wit_3_pure` — `aggressive_pre_process`

Prove every listed split goal first, each opening with `LLM_pre_process ltac:(...)` and an explicit closer. Then prove the top-level VC with `aggressive_pre_process` and close each resulting branch with only `Goal_apply <split-goal lemma>` for the corresponding split goal, with no other tactic in the top-level proof. This is a worker proof rule; controller validation does not inspect the spelling of these applications.

Split goals:

  - `proof_of_cmc_emit_globals_partial_solve_wit_3_pure_split_goal_1`: The goal is pure cursor_pre+8<=capacity_pre. Apply cm_initialized_word_facts__initialized_emission with well-formed head PreH25, flag PreH32 and non-char code guard PreH17. Rewrite size=8 in capacity bound PreH31 and use nonnegative tail size PreH30 with lia. The stack, fields, tail and buffer antecedent needs no transformation.

## Write boundary

- Editable top-level proof spans: `proof_of_cmc_emit_globals_entail_wit_2_1`, `proof_of_cmc_emit_globals_entail_wit_2_2`, `proof_of_cmc_emit_globals_partial_solve_wit_2_pure`, `proof_of_cmc_emit_globals_partial_solve_wit_3_pure`.
- Editable aggressive split-goal proof spans: `proof_of_cmc_emit_globals_partial_solve_wit_2_pure_split_goal_1`, `proof_of_cmc_emit_globals_partial_solve_wit_3_pure_split_goal_1`.
- Protected LLM_pre_process split blocks: none; their tokens remain `Proof. Abort.`.
- In `group_worker_lib`, append only proved suffixed helpers, token-identical sealed helper copies, and needed official imports.
- All declaration statements, other proof tokens, the manual prelude, and the seed library stay protected.

Whitespace, comments, line endings, and the final newline are formatting. The controller compares protected Rocq tokens, declaration ownership, proof mode, and kernel results. For an aggressive top-level proof, follow the worker rule above and use `Goal_apply` for the split lemmas; controller validation deliberately does not inspect that tactic choice.


## Files

- Copied manual: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_globals_migration-20261016102210/cmc_emit_globals_migration-vc-proving-r1/groups/group_00__initialized-emission/cmc_emit_globals_migration_proof_manual.v`
- `group_worker_lib`: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_globals_migration-20261016102210/cmc_emit_globals_migration-vc-proving-r1/groups/group_00__initialized-emission/cmc_emit_globals_migration_lib.v`
- Read-only `formal_case_lib`: `Rocq/examples/QCP_demos_human/cmc_emit_globals_migration_lib.v`
- Frozen helper candidates: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_globals_migration-20261016102210/cmc_emit_globals_migration-vc-proving-r1/public_helper_snapshot.txt` — search by needed helper/predicate names and read only matching declarations; never import this file
- Terminal report: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_globals_migration-20261016102210/rounds/cmc_emit_globals_migration-vc-proving-r1/groups/group_00__initialized-emission/group_worker_report.json`
- Notes: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_emit_globals_migration-20261016102210/rounds/cmc_emit_globals_migration-vc-proving-r1/groups/group_00__initialized-emission/group_worker_output.md`. They are optional for ordinary outcomes, but an
  `annotation-gap` blocker requires a non-empty explanation here because the controller preserves this
  exact Markdown as part of the aggregated annotation feedback.
- Previous proving round: none; no reuse note is expected.

The group directory must finish with the copied manual and `group_worker_lib`.

## Planned helpers

- `cm_initialized_char_facts__initialized_emission`; public; expected use: Prove forall structs g, cm_global_wf structs g -> cm_rep_bool (cm_global_has_init g)<>0 -> cm_type_encode (cm_global_ty g)=1 -> cm_rep_global_size g=1 and cm_global_bytes structs g=[tower_u8 (cm_global_init g)]. Decode the Boolean to true and obtain count=0 from cm_global_wf. Establish CMCharTy from code=1 by type cases: scalarity excludes structs; pointer depth nonnegativity and base bounds exclude pointer code=1. Reduce the char size; use existing cm_rep_global_size_matches, cm_global_init_bytes_char and cm_global_bytes_initialized, with singleton Zlength=1. All premises are exactly the branch guard, wf and flag in each assigned VC.
- `cm_initialized_word_facts__initialized_emission`; public; expected use: Prove forall structs g, cm_global_wf structs g -> cm_rep_bool (cm_global_has_init g)<>0 -> cm_type_encode (cm_global_ty g)<>1 -> cm_rep_global_size g=8 and cm_global_bytes structs g=tower_word_bytes (cm_global_init g). Decode the flag to true and use wf for count=0 and scalarity. Type cases exclude char by the guard and structs by scalarity; int and pointer model sizes are 8. Use cm_rep_global_size_matches, cm_global_init_bytes_word, the eight-byte tower length, and cm_global_bytes_initialized. The exact wf, flag and guard premises are already present in each word-branch VC.

`local` stays in this group. A proved `public` helper is promoted by the controller for later rounds. Historical token-identical copies may keep their sealed suffix; adaptations use this group's suffix.

## Commands

Run a needed command unchanged with its bound cwd. Prefer a direct system-terminal call. If terminal operations are available only through `functions.exec`, use a transparent cell that awaits exactly one `tools.exec_command` to launch, or one `tools.write_stdin` to continue the same live session (or the runtime-documented normalized equivalent), and only forwards the result. Pass command/argv, every argument, and cwd unchanged when launching; preserve the exact session handle when continuing. Use a normalized equivalent only if its input shape accepts those values unchanged; never serialize argv into shell text, reparse a rendered command, or add quoting. Do not call another tool in the cell, construct, alter, sequence, wrap, pipe, or background commands. Preserve every outer cell and inner process/session handle until terminal exit; if the bridge yields a running cell, resume only that cell with `functions.wait`.

```text
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-debug --run cmc_emit_globals_migration-20261016102210 --round cmc_emit_globals_migration-vc-proving-r1 --group initialized-emission
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_globals_migration-20261016102210 --round cmc_emit_globals_migration-vc-proving-r1 --target-kind group-development --group initialized-emission
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_emit_globals_migration-20261016102210 --round cmc_emit_globals_migration-vc-proving-r1 --target-kind group-check --group initialized-emission
```

Debug script: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_emit_globals_migration-20261016102210/_coq_builds/cmc_emit_globals_migration-vc-proving-r1/group_00/src/.coq_debug/group_00_initialized_emission.v`. Debug, development, and exact are optional proof feedback. `finalize-delivery` seals the two formal files and immediately runs the single mandatory controller group validation.

## Completion

Do not use raw Coq, Dune, Rocq MCP, `Admitted.`, new assumptions, forbidden lemmas, or the forbidden tactics `entailer!` and the bare alias `pre_process` (both are scanned exactly like a forbidden lemma; calls made inside `LLM_pre_process` and `Goal_apply` are unaffected). Repair a recoverable controller failure in this same worker. At the end, success is exactly `status: completed`; `blocked` adds one complete `blocker`. Do not copy version, diff, check status, or controller output.

If an assigned VC exposes an annotation/specification gap outside this group's write boundary, stop proof-only edits and return `blocked` with `blocker.failure_class` exactly `annotation-gap`. Its `vcs` must list every affected exact sealed-manual `name`, `parent`, and `annotation_location`; `message` explains existing premises and the missing conclusion. The controller validates and schedules from those structured VCs.
