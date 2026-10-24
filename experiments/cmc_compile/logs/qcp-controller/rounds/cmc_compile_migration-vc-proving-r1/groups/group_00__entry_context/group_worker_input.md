# Group worker handoff

Read `.agents/skills/group-worker-proving/SKILL.md`, `.agents/skills/group-worker-proving/workflows/group-worker-proving.md`, and `.agents/skills/group-worker-proving/workflows/commands-and-checks.md` completely. This handoff adds only the current assignment; do not use a parent transcript or sibling output.

## Assignment

- Group: `entry_context`; attempt 1; earlier compact attempts 0
- Difficulty hint: 3/5
- Required suffix for every new or adapted helper: `__entry_context`


### `proof_of_cmc_compile_entail_wit_1` — `LLM_pre_process`

Strategy: Choose a whole-goal disjunct. Unfold cm_program_rep, cm_program_heap_rep and cm_output_pre, retaining the original function pointer, three buffer pointers and three old scalar values as existential witnesses. Open cm_program_context_rep only enough to obtain program_pre<>0, then refold it. Obtain capacity upper bounds from the two #Int field resources, not from cm_output_pre's pure conjunct alone. cm_semantic_wf_program unfolds to the required cm_wf_program; its typed projection gives cmc_data_ready_from_typed, cmc_structs_ready_from_typed, cm_concrete_code_ready_from_wf and cm_concrete_functions_ready_from_wf. Destructure these established readiness conclusions to obtain all data sizes, safety facts and the data-length equality. Reintroduce the same witnesses and cancel the unchanged context, function list, output fields and undefined buffers.

Prove only the top-level VC, opening with `LLM_pre_process ltac:(...)` and an explicit closer; do not edit its split goals.

Split goals:

  - none generated

### `proof_of_cmc_compile_entail_wit_2` — `LLM_pre_process`

Strategy: Choose the whole-goal first disjunct and keep the existing functions_ptr_2, ops_ptr_2, imms_ptr_2 and data_ptr_2. The guards and length-return equalities establish model lengths <= capacities; cm_i32_code_count establishes nonnegativity. Establish code_capacity>0 using the counts-representable projection of cm_wf_program, cm_functions_length_bound__model_length_bound, Zlength_nonneg and cm_model_code_length=11+functions_size. Establish data_capacity>=8 from the recorded model-data-size equality and nonnegative globals/strings sizes. The positive capacities select the nonempty branches of cm_undef_int_buffer, cm_undef_int64_buffer and cm_undef_uint8_buffer, exposing all three nonzero pointers and full undefined arrays. Rewrite full to the zero-based undefined segment and introduce each empty initialized segment using the library empty-segment identity. Carry the existing pure facts and cancel the context/output fields.

Prove only the top-level VC, opening with `LLM_pre_process ltac:(...)` and an explicit closer; do not edit its split goals.

Split goals:

  - none generated

### `proof_of_cmc_compile_entail_wit_5` — `LLM_pre_process`

Strategy: Choose a whole-goal disjunct and unfold cm_program_context_rep. Its existing structs/globals/strings pointers, functions_ptr_2 and data_ptr_2 instantiate the RHS existentials. The context owns exactly the five program fields and three descriptor lists required on the RHS; retain the function list and frame cm_emitter_rep and every output/data resource. All pure facts are hypotheses. This is a context-open transition with no change to code or data values.

Prove only the top-level VC, opening with `LLM_pre_process ltac:(...)` and an explicit closer; do not edit its split goals.

Split goals:

  - none generated

## Write boundary

- Editable top-level proof spans: `proof_of_cmc_compile_entail_wit_1`, `proof_of_cmc_compile_entail_wit_2`, `proof_of_cmc_compile_entail_wit_5`.
- Editable aggressive split-goal proof spans: none.
- Protected LLM_pre_process split blocks: none; their tokens remain `Proof. Abort.`.
- In `group_worker_lib`, append only proved suffixed helpers, token-identical sealed helper copies, and needed official imports.
- All declaration statements, other proof tokens, the manual prelude, and the seed library stay protected.

Whitespace, comments, line endings, and the final newline are formatting. The controller compares protected Rocq tokens, declaration ownership, proof mode, and kernel results. For an aggressive top-level proof, follow the worker rule above and use `Goal_apply` for the split lemmas; controller validation deliberately does not inspect that tactic choice.


## Files

- Copied manual: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_compile_migration-20261019230022/cmc_compile_migration-vc-proving-r1/groups/group_00__entry_context/cmc_compile_migration_proof_manual.v`
- `group_worker_lib`: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_compile_migration-20261019230022/cmc_compile_migration-vc-proving-r1/groups/group_00__entry_context/cmc_compile_migration_lib.v`
- Read-only `formal_case_lib`: `Rocq/examples/QCP_demos_human/cmc_compile_migration_lib.v`
- Frozen helper candidates: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_compile_migration-20261019230022/cmc_compile_migration-vc-proving-r1/public_helper_snapshot.txt` — search by needed helper/predicate names and read only matching declarations; never import this file
- Terminal report: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_compile_migration-20261019230022/rounds/cmc_compile_migration-vc-proving-r1/groups/group_00__entry_context/group_worker_report.json`
- Notes: `/Users/nizitong/QCP/qcp-binary-democases/reports/cmc_compile_migration-20261019230022/rounds/cmc_compile_migration-vc-proving-r1/groups/group_00__entry_context/group_worker_output.md`. They are optional for ordinary outcomes, but an
  `annotation-gap` blocker requires a non-empty explanation here because the controller preserves this
  exact Markdown as part of the aggregated annotation feedback.
- Previous proving round: none; no reuse note is expected.

The group directory must finish with the copied manual and `group_worker_lib`.

## Planned helpers

- none planned

`local` stays in this group. A proved `public` helper is promoted by the controller for later rounds. Historical token-identical copies may keep their sealed suffix; adaptations use this group's suffix.

## Commands

Run a needed command unchanged with its bound cwd. Prefer a direct system-terminal call. If terminal operations are available only through `functions.exec`, use a transparent cell that awaits exactly one `tools.exec_command` to launch, or one `tools.write_stdin` to continue the same live session (or the runtime-documented normalized equivalent), and only forwards the result. Pass command/argv, every argument, and cwd unchanged when launching; preserve the exact session handle when continuing. Use a normalized equivalent only if its input shape accepts those values unchanged; never serialize argv into shell text, reparse a rendered command, or add quoting. Do not call another tool in the cell, construct, alter, sequence, wrap, pipe, or background commands. Preserve every outer cell and inner process/session handle until terminal exit; if the bridge yields a running cell, resume only that cell with `functions.wait`.

```text
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-debug --run cmc_compile_migration-20261019230022 --round cmc_compile_migration-vc-proving-r1 --group entry_context
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_compile_migration-20261019230022 --round cmc_compile_migration-vc-proving-r1 --target-kind group-development --group entry_context
/Users/nizitong/.local/share/uv/python/cpython-3.12.13-macos-aarch64-none/bin/python3.12 /Users/nizitong/QCP/qcp-binary-democases/.agents/scripts/verification-orchestrator/controller.py --main-root /Users/nizitong/QCP/qcp-binary-democases coq-check --run cmc_compile_migration-20261019230022 --round cmc_compile_migration-vc-proving-r1 --target-kind group-check --group entry_context
```

Debug script: `/Users/nizitong/QCP/qcp-binary-democases/verification_runs/cmc_compile_migration-20261019230022/_coq_builds/cmc_compile_migration-vc-proving-r1/group_00/src/.coq_debug/group_00_entry_context.v`. Debug, development, and exact are optional proof feedback. `finalize-delivery` seals the two formal files and immediately runs the single mandatory controller group validation.

## Completion

Do not use raw Coq, Dune, Rocq MCP, `Admitted.`, new assumptions, forbidden lemmas, or the forbidden tactics `entailer!` and the bare alias `pre_process` (both are scanned exactly like a forbidden lemma; calls made inside `LLM_pre_process` and `Goal_apply` are unaffected). Repair a recoverable controller failure in this same worker. At the end, success is exactly `status: completed`; `blocked` adds one complete `blocker`. Do not copy version, diff, check status, or controller output.

If an assigned VC exposes an annotation/specification gap outside this group's write boundary, stop proof-only edits and return `blocked` with `blocker.failure_class` exactly `annotation-gap`. Its `vcs` must list every affected exact sealed-manual `name`, `parent`, and `annotation_location`; `message` explains existing premises and the missing conclusion. The controller validates and schedules from those structured VCs.
