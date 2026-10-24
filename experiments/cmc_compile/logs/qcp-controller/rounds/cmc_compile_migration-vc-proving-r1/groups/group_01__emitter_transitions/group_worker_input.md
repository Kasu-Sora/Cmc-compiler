# Group worker handoff

Read `.agents/skills/group-worker-proving/SKILL.md`, `.agents/skills/group-worker-proving/workflows/group-worker-proving.md`, and `.agents/skills/group-worker-proving/workflows/commands-and-checks.md` completely. This handoff adds only the current assignment; do not use a parent transcript or sibling output.

## Assignment

- Group: `emitter_transitions`; attempt 1; earlier compact attempts 0
- Difficulty hint: 3/5
- Required suffix for every new or adapted helper: `__emitter_transitions`


### `proof_of_cmc_compile_entail_wit_3` — `LLM_pre_process`

Strategy: Choose the whole first disjunct. Preserve functions_ptr_2 and data_ptr_2. Fold cm_resolved_emitter_plan_rep, cm_resolved_emitter_rep and cm_emitter_rep using raw_prefix=[] and existing ops/imms pointers. cm_patch_code []=[] and the two representation lists are empty, so pc=0 and both zero-based buffer segments match exactly. Prove the plan budget by app_nil_r, Zlength_nil and cm_compile_model_length__emitter_transitions, rewriting the given code_length=model length and code_length<=code_capacity. Nonzero pointers/output and all bounds already occur in the antecedent. Frame the context, function list, data buffers and remaining output fields.

Prove only the top-level VC, opening with `LLM_pre_process ltac:(...)` and an explicit closer; do not edit its split goals.

Split goals:

  - none generated

### `proof_of_cmc_compile_entail_wit_4` — `LLM_pre_process`

Strategy: Choose a whole-goal disjunct; normalize []++cm_model_code to cm_model_code. Unfold only cm_resolved_emitter_plan_rep, discard its now-unneeded pure budget, and retain the enclosed cm_resolved_emitter_rep unchanged. Instantiate functions_ptr and data_ptr by functions_ptr_2 and data_ptr_2, propagate the hypotheses and cancel the context and framed output/data resources. Do not unfold or reprove the resolved raw-code relation.

Prove only the top-level VC, opening with `LLM_pre_process ltac:(...)` and an explicit closer; do not edit its split goals.

Split goals:

  - none generated

### `proof_of_cmc_compile_entail_wit_6` — `LLM_pre_process`

Strategy: Use the whole first disjunct. Open cm_emitter_rep to obtain its ops/imms pointers, nonzeroness, output fields, local emitter fields and both initialized/undefined segment pairs. Rewrite Zlength(cm_rep_ops model_code) using Zlength_map and cm_compile_model_length__emitter_transitions to the hypothesis code_length; use the same map-length equality for imms. Refold cm_program_context_rep with the existing structs_ptr/globals_ptr/strings_ptr and functions_ptr_2. Rewrite the emitted-data endpoint to data_length using the given model-data-size equality, and the byte list to cm_model_data_bytes by its definition (zeros 8 is the same repeat prefix). The return equality gives retval=data_length. Instantiate functions_ptr/ops_ptr/imms_ptr, retain all nonzero and length facts, and cancel the reconstructed context, output fields, emitter fields and the three segment pairs.

Prove only the top-level VC, opening with `LLM_pre_process ltac:(...)` and an explicit closer; do not edit its split goals.

Split goals:

  - none generated

## Write boundary

- Editable top-level proof spans: `proof_of_cmc_compile_entail_wit_3`, `proof_of_cmc_compile_entail_wit_4`, `proof_of_cmc_compile_entail_wit_6`.
- Editable aggressive split-goal proof spans: none.
- Protected LLM_pre_process split blocks: none; their tokens remain `Proof. Abort.`.
- In `group_worker_lib`, append only proved suffixed helpers, token-identical sealed helper copies, and needed official imports.
- All declaration statements, other proof tokens, the manual prelude, and the seed library stay protected.

Whitespace, comments, line endings, and the final newline are formatting. The controller compares protected Rocq tokens, declaration ownership, proof mode, and kernel results. For an aggressive top-level proof, follow the worker rule above and use `Goal_apply` for the split lemmas; controller validation deliberately does not inspect that tactic choice.


## Files

- Copied manual: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_compile_migration-20261019230022/cmc_compile_migration-vc-proving-r1/groups/group_01__emitter_transitions/cmc_compile_migration_proof_manual.v`
- `group_worker_lib`: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_compile_migration-20261019230022/cmc_compile_migration-vc-proving-r1/groups/group_01__emitter_transitions/cmc_compile_migration_lib.v`
- Read-only `formal_case_lib`: `Rocq/examples/QCP_demos_human/cmc_compile_migration_lib.v`
- Frozen helper candidates: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_compile_migration-20261019230022/cmc_compile_migration-vc-proving-r1/public_helper_snapshot.txt` — search by needed helper/predicate names and read only matching declarations; never import this file
- Terminal report: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_compile_migration-20261019230022/rounds/cmc_compile_migration-vc-proving-r1/groups/group_01__emitter_transitions/group_worker_report.json`
- Notes: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_compile_migration-20261019230022/rounds/cmc_compile_migration-vc-proving-r1/groups/group_01__emitter_transitions/group_worker_output.md`. They are optional for ordinary outcomes, but an
  `annotation-gap` blocker requires a non-empty explanation here because the controller preserves this
  exact Markdown as part of the aggregated annotation feedback.
- Previous proving round: none; no reuse note is expected.

The group directory must finish with the copied manual and `group_worker_lib`.

## Planned helpers

- `cm_compile_functions_length__emitter_transitions`; public; expected use: Prove forall policy p functions fid, Zlength(cm_emit_functions policy p fid functions)=cm_functions_code_size policy p functions fid. No well-formedness premise is needed: induct on functions with fid generalized, unfold the two recursors, rewrite Zlength_app and the existing cm_layout_function_length, then use the induction hypothesis at fid+1.
- `cm_compile_model_length__emitter_transitions`; public; expected use: Prove forall policy p, Zlength(cm_model_code policy p)=cm_model_code_length policy p. Unfold cm_model_code and cm_model_code_length, rewrite Zlength_app and cm_compile_functions_length__emitter_transitions, and compute the prelude length as 11. This premise-free public fact is used by entail witnesses 3 and 6.

`local` stays in this group. A proved `public` helper is promoted by the controller for later rounds. Historical token-identical copies may keep their sealed suffix; adaptations use this group's suffix.

## Commands

Run a needed command unchanged with its bound cwd. Prefer a direct system-terminal call. If terminal operations are available only through `functions.exec`, use a transparent cell that awaits exactly one `tools.exec_command` to launch, or one `tools.write_stdin` to continue the same live session (or the runtime-documented normalized equivalent), and only forwards the result. Pass command/argv, every argument, and cwd unchanged when launching; preserve the exact session handle when continuing. Use a normalized equivalent only if its input shape accepts those values unchanged; never serialize argv into shell text, reparse a rendered command, or add quoting. Do not call another tool in the cell, construct, alter, sequence, wrap, pipe, or background commands. Preserve every outer cell and inner process/session handle until terminal exit; if the bridge yields a running cell, resume only that cell with `functions.wait`.

```text
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-debug --run cmc_compile_migration-20261019230022 --round cmc_compile_migration-vc-proving-r1 --group emitter_transitions
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_compile_migration-20261019230022 --round cmc_compile_migration-vc-proving-r1 --target-kind group-development --group emitter_transitions
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_compile_migration-20261019230022 --round cmc_compile_migration-vc-proving-r1 --target-kind group-check --group emitter_transitions
```

Debug script: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_compile_migration-20261019230022/_coq_builds/cmc_compile_migration-vc-proving-r1/group_01/src/.coq_debug/group_01_emitter_transitions.v`. Debug, development, and exact are optional proof feedback. `finalize-delivery` seals the two formal files and immediately runs the single mandatory controller group validation.

## Completion

Do not use raw Coq, Dune, Rocq MCP, `Admitted.`, new assumptions, forbidden lemmas, or the forbidden tactics `entailer!` and the bare alias `pre_process` (both are scanned exactly like a forbidden lemma; calls made inside `LLM_pre_process` and `Goal_apply` are unaffected). Repair a recoverable controller failure in this same worker. At the end, success is exactly `status: completed`; `blocked` adds one complete `blocker`. Do not copy version, diff, check status, or controller output.

If an assigned VC exposes an annotation/specification gap outside this group's write boundary, stop proof-only edits and return `blocked` with `blocker.failure_class` exactly `annotation-gap`. Its `vcs` must list every affected exact sealed-manual `name`, `parent`, and `annotation_location`; `message` explains existing premises and the missing conclusion. The controller validates and schedules from those structured VCs.
