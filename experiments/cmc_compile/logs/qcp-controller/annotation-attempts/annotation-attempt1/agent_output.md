# Annotation dependency audit — incomplete

The current target C and canonical case-lib remain byte-for-byte at their initial seeds. No generated artifact, function contract, proof, or helper assumption has been introduced. No controller design/symexec/Coq check has been claimed as run or passed. There are no VCs to identify yet. The plan remains `planning`, not `ready`.

## Exact original obligation

`cmc_rep.c:2086–2124` defines `cm_output_ok`. In addition to exact code/data prefixes and unused-buffer ownership, it requires, for arbitrary `obj`, `input`, `trace`, `status`:

```
cm_source_terminates p input trace status /\
cm_output_decodes 0 (cm_rep_ops (cm_model_code p))
  (cm_rep_imms (cm_model_code p)) (cm_model_data_bytes p) obj
-> tvm_terminates obj input trace status
```

`cmc.c:95–138` proves `cmc_compile_success_bridge` using `cm_model_output_decodes`, `cm_output_decode_unique`, and `cmc_preservation`. Omitting this clause, assuming it in `Require`, or putting it into an arbitrary codegen field changes the requested result.

## Missing prerequisites and reproducible evidence

Read-only `rg` over all `Rocq/**/*.v` found no declarations/usages for any of `cm_source_terminates`, `tvm_terminates`, `tvm_object`, `cm_compile_model`, `cm_output_decodes`, `cmc_preservation`, `cm_preservation_iter`, or `cm_preservation_invariant`. These are absent sources, not merely unbuilt `.vo` files.

Source snapshot root: `/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_compile/baseline/cstar_project`.

- `tvm_model.c:1295`: `tvm_terminates` requires valid byte input/status and a finite actual `tvm_exec (TVMBoot obj input)` run ending normally with the observed output. Its prerequisites include object/patch/loader definitions, VM state/task/outcome, instruction execution, and iteration/execution relations.
- `cmc_lang.c:4296`: `cm_source_terminates` requires valid byte input/status and actual `cm_exec (CMStartTask p input)` yielding a successful source control and the observed output. Its prerequisites include source state/control/task/frame/outcome and operational semantics.
- `cmc_rep.c:1966`: deterministic decoded object relation, including valid instruction shape and dense byte patches. `cm_output_decode_unique` at 1978 and `cm_model_output_decodes` at 2141 are also not migrated.
- `cmc_correct.c:35–130`: `cmc_successful_exec_simulation` bridges source execution witnesses to VM execution through `cm_preservation_initial`, `cm_preservation_iter`, annotated-iteration erasure, final-state observation, and annotated VM prefix lemmas.
- `cmc_correct.c:145–182`: `cmc_preservation` derives terminal I/O/status preservation from that simulation. It is not a consequence of code length/readiness or buffer equality alone.
- `cmc_preservation_total_iter.c:14`: iteration preservation depends on step preservation; `cmc_preservation_total_step.c:24–38` requires the state/type/fid/spill/generation/static/tagged/budget/short/code preservation family.

Existing reusable pieces are real and remain useful: AST/layout/count models, actual instruction list and opcode/immediate models, all verified emitter implementations, `cmc_compile_ready_migration_lib`, `cmc_program_ready_migration_lib`, and their checked helpers. `cmc_counts_migration_lib.v:250–265` deliberately leaves four codegen obligations parameterized; a faithful concrete instantiation of instruction shape/targets/patches/entry must now be supplied, not treated as a hidden compiler-preservation assumption.

## Repair boundary and necessary order

1. Migrate shared VM object/loading/instruction and execution semantics using existing opcode/instruction types; migrate source runtime state and execution semantics using the existing AST. Preserve defined behavior and malformed/default lookup conventions.
2. Instantiate the four codegen obligations with those actual definitions and define `cm_compile_model`, output decoding, and exact full program/output representations. Prove decoding roundtrip/uniqueness/model-decoding.
3. Port the simulation and preservation prerequisites, then prove `cmc_preservation` and `cmc_compile_success_bridge` with closed assumptions.
4. Resume this same annotation owner: translate helper specs, establish resource/capacity/emission phase boundaries, generate and prove VCs, and perform the complete controller final checks.

This is a missing verified public semantic dependency at the current annotation-role boundary, not a claim that the theorem is unprovable or that workload alone warrants stopping. The annotation role may write the single case-lib's mathematical declarations, but may not write proof bodies or shared/second libraries. No replacement public semantic/proof library is present in the selected input topology. A monolithic unproved or arbitrary abstract replacement would not discharge the original obligation. No permission to weaken the result is requested.

The transitive `#require` closure of `cmc_preservation_total_iter.c` contains 214 source files (including reused definitions and generic support). This is dependency evidence only, NOT a count of new modules or a measured migration cost; theorem-level pruning and reuse remain necessary.

## Effort and current review

Accepted QCP annotation LOC: 0. Accepted target proof LOC: 0. New verified public definitions/lemmas: 0. Work performed in this attempt is read-only dependency/spec analysis and this preliminary plan. Final annotation/proof and public-dependency costs are unknown until the prerequisites and target verification are completed.

Ordinary Assert review: none written. Key points in the plan are candidates only. Higher-order witness review: no new existential-function witness introduced; original success clause universally quantifies decoded objects and I/O, and that quantification must remain.

Relevant references read: current source contract/representation/correctness definitions; existing counts/emitter/readiness libraries for reusable mathematical and spatial interfaces; annotation skill's positive `sum.c` resource/bounds example and algorithm-mirror counterexample. No other case's generated/proof artifact was copied.

## Audited dependency closure

- `cmc_abi.c`
- `cmc_annotate.c`
- `cmc_annotate_erasure.c`
- `cmc_annotate_model.c`
- `cmc_annotate_preservation.c`
- `cmc_codegen.c`
- `cmc_concrete_defs.c`
- `cmc_lang.c`
- `cmc_preservation_binding_numeric.c`
- `cmc_preservation_budget_arith.c`
- `cmc_preservation_budget_control.c`
- `cmc_preservation_budget_defs.c`
- `cmc_preservation_budget_ready.c`
- `cmc_preservation_budget_start.c`
- `cmc_preservation_budget_step.c`
- `cmc_preservation_budget_value.c`
- `cmc_preservation_call_clear.c`
- `cmc_preservation_call_finish.c`
- `cmc_preservation_call_param.c`
- `cmc_preservation_call_params_complete.c`
- `cmc_preservation_call_params_order.c`
- `cmc_preservation_call_params_permute.c`
- `cmc_preservation_call_pending.c`
- `cmc_preservation_call_pending_live.c`
- `cmc_preservation_call_pending_machine.c`
- `cmc_preservation_call_pending_memory.c`
- `cmc_preservation_call_transport.c`
- `cmc_preservation_call_value.c`
- `cmc_preservation_code.c`
- `cmc_preservation_code_control.c`
- `cmc_preservation_code_expr.c`
- `cmc_preservation_code_stmt.c`
- `cmc_preservation_code_task.c`
- `cmc_preservation_code_value.c`
- `cmc_preservation_code_value_branch.c`
- `cmc_preservation_code_value_call.c`
- `cmc_preservation_code_value_flow.c`
- `cmc_preservation_code_value_linear.c`
- `cmc_preservation_code_value_total.c`
- `cmc_preservation_fid.c`
- `cmc_preservation_fid_apply.c`
- `cmc_preservation_fid_start.c`
- `cmc_preservation_fid_step.c`
- `cmc_preservation_generation.c`
- `cmc_preservation_generation_annotation.c`
- `cmc_preservation_generation_annotation_step.c`
- `cmc_preservation_generation_annotation_transition.c`
- `cmc_preservation_generation_frame.c`
- `cmc_preservation_generation_limit.c`
- `cmc_preservation_generation_state.c`
- `cmc_preservation_generation_static_apply.c`
- `cmc_preservation_generation_static_start.c`
- `cmc_preservation_generation_static_task.c`
- `cmc_preservation_generation_step_apply.c`
- `cmc_preservation_generation_step_start.c`
- `cmc_preservation_generation_step_task.c`
- `cmc_preservation_generation_syntax.c`
- `cmc_preservation_generation_task.c`
- `cmc_preservation_invariant.c`
- `cmc_preservation_invariant_control.c`
- `cmc_preservation_invariant_frame.c`
- `cmc_preservation_invariant_runtime.c`
- `cmc_preservation_invariant_step.c`
- `cmc_preservation_invariant_task.c`
- `cmc_preservation_invariant_transition.c`
- `cmc_preservation_invariant_value.c`
- `cmc_preservation_layout.c`
- `cmc_preservation_machine.c`
- `cmc_preservation_machine_io.c`
- `cmc_preservation_machine_load.c`
- `cmc_preservation_machine_ops.c`
- `cmc_preservation_machine_stack.c`
- `cmc_preservation_machine_store.c`
- `cmc_preservation_memory.c`
- `cmc_preservation_ready_context.c`
- `cmc_preservation_ready_coordinate.c`
- `cmc_preservation_ready_semantic.c`
- `cmc_preservation_runtime.c`
- `cmc_preservation_runtime_ready.c`
- `cmc_preservation_short_bases.c`
- `cmc_preservation_short_control.c`
- `cmc_preservation_short_defs.c`
- `cmc_preservation_short_start.c`
- `cmc_preservation_short_step.c`
- `cmc_preservation_short_value.c`
- `cmc_preservation_source.c`
- `cmc_preservation_source_conditions.c`
- `cmc_preservation_source_ready.c`
- `cmc_preservation_spill_holds_safety.c`
- `cmc_preservation_spill_safety.c`
- `cmc_preservation_spill_semantic.c`
- `cmc_preservation_spill_transition.c`
- `cmc_preservation_spill_update.c`
- `cmc_preservation_state.c`
- `cmc_preservation_static_bases.c`
- `cmc_preservation_static_bases_step.c`
- `cmc_preservation_store_memory.c`
- `cmc_preservation_store_metadata.c`
- `cmc_preservation_store_provenance.c`
- `cmc_preservation_store_semantic.c`
- `cmc_preservation_tagged.c`
- `cmc_preservation_tagged_allocation.c`
- `cmc_preservation_tagged_apply.c`
- `cmc_preservation_tagged_call.c`
- `cmc_preservation_tagged_call_enter.c`
- `cmc_preservation_tagged_call_ready.c`
- `cmc_preservation_tagged_restore.c`
- `cmc_preservation_tagged_restore_list.c`
- `cmc_preservation_tagged_start.c`
- `cmc_preservation_tagged_step.c`
- `cmc_preservation_tagged_task.c`
- `cmc_preservation_tagged_transition.c`
- `cmc_preservation_target_access.c`
- `cmc_preservation_target_address.c`
- `cmc_preservation_target_call_complete.c`
- `cmc_preservation_target_call_fp.c`
- `cmc_preservation_target_call_frame.c`
- `cmc_preservation_target_call_jump.c`
- `cmc_preservation_target_call_params.c`
- `cmc_preservation_target_call_pending.c`
- `cmc_preservation_target_call_setup.c`
- `cmc_preservation_target_control_call.c`
- `cmc_preservation_target_control_halt.c`
- `cmc_preservation_target_control_regular.c`
- `cmc_preservation_target_control_scope.c`
- `cmc_preservation_target_control_total.c`
- `cmc_preservation_target_convert.c`
- `cmc_preservation_target_expr.c`
- `cmc_preservation_target_expr_total.c`
- `cmc_preservation_target_jump_valid.c`
- `cmc_preservation_target_machine.c`
- `cmc_preservation_target_ready.c`
- `cmc_preservation_target_restore.c`
- `cmc_preservation_target_return_machine.c`
- `cmc_preservation_target_spill.c`
- `cmc_preservation_target_spill_runtime.c`
- `cmc_preservation_target_start.c`
- `cmc_preservation_target_state.c`
- `cmc_preservation_target_stmt.c`
- `cmc_preservation_target_store.c`
- `cmc_preservation_target_task.c`
- `cmc_preservation_target_value.c`
- `cmc_preservation_target_value_arg.c`
- `cmc_preservation_target_value_args.c`
- `cmc_preservation_target_value_binary.c`
- `cmc_preservation_target_value_binary_finish.c`
- `cmc_preservation_target_value_binary_pointer.c`
- `cmc_preservation_target_value_binary_total.c`
- `cmc_preservation_target_value_branch.c`
- `cmc_preservation_target_value_call.c`
- `cmc_preservation_target_value_call_total.c`
- `cmc_preservation_target_value_code_ready.c`
- `cmc_preservation_target_value_context.c`
- `cmc_preservation_target_value_control.c`
- `cmc_preservation_target_value_control_total.c`
- `cmc_preservation_target_value_index.c`
- `cmc_preservation_target_value_init.c`
- `cmc_preservation_target_value_io.c`
- `cmc_preservation_target_value_member.c`
- `cmc_preservation_target_value_pointer_total.c`
- `cmc_preservation_target_value_return.c`
- `cmc_preservation_target_value_scalar_total.c`
- `cmc_preservation_target_value_total.c`
- `cmc_preservation_target_value_unary.c`
- `cmc_preservation_total.c`
- `cmc_preservation_total_iter.c`
- `cmc_preservation_total_step.c`
- `cmc_preservation_tvm.c`
- `cmc_preservation_type_args.c`
- `cmc_preservation_type_cursor.c`
- `cmc_preservation_type_facts.c`
- `cmc_preservation_type_lvalue.c`
- `cmc_preservation_type_phase.c`
- `cmc_preservation_type_ready.c`
- `cmc_preservation_type_source_c_call.c`
- `cmc_preservation_type_source_c_regular.c`
- `cmc_preservation_type_source_c_struct.c`
- `cmc_preservation_type_source_c_support.c`
- `cmc_preservation_type_source_c_total.c`
- `cmc_preservation_type_source_l.c`
- `cmc_preservation_type_source_r_call.c`
- `cmc_preservation_type_source_r_leaf.c`
- `cmc_preservation_type_source_r_struct.c`
- `cmc_preservation_type_source_r_total.c`
- `cmc_preservation_type_source_r_var.c`
- `cmc_preservation_type_source_s.c`
- `cmc_preservation_type_source_s_support.c`
- `cmc_preservation_type_source_v_binary.c`
- `cmc_preservation_type_source_v_call.c`
- `cmc_preservation_type_source_v_control.c`
- `cmc_preservation_type_source_v_pointer.c`
- `cmc_preservation_type_source_v_scalar.c`
- `cmc_preservation_type_source_v_support.c`
- `cmc_preservation_type_source_v_total.c`
- `cmc_preservation_type_step.c`
- `cmc_preservation_type_value.c`
- `cmc_rep.c`
- `cmc_sim.c`
- `cmc_sim_ops.c`
- `cmc_stack.c`
- `cmc_stack_annotations.c`
- `cmc_stack_bound.c`
- `cmc_stack_local.c`
- `cmc_stack_local_core.c`
- `cmc_stack_local_syntax.c`
- `cmc_stack_trace.c`
- `cmc_temp_algebra.c`
- `tower_base.c`
- `tvm_model.c`
- `userlib/array.c`
- `userlib/operational.c`
- `userlib/proof.c`
- `userlib/proof_patterns.c`
- `userlib/pure_lists.c`
