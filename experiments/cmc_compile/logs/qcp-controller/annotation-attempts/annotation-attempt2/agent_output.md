# Top-level annotation, iteration 2

The original dependency blocker is resolved by the separately verified public semantic/preservation libraries. The case imports `cmc_preservation_complete_migration_lib`, compile/program readiness, patch-calls, and emit-data; it introduces no proof bodies and no arbitrary semantic assumptions.

## Contract mapping

- `cm_program_heap_rep root p` is the existing full program context plus its full function list, existentially hiding the function pointer. This expands to the original five program fields and all four lists.
- `cm_program_rep policy root p` combines that heap with `cm_semantic_wf_program policy p`. The original `cm_rep_program_valid p = 1` is precisely the conditional encoding of `cm_wf_program p`; no stronger readiness precondition is required.
- `sp : cm_source_lookup_policy` records HOL total-lookup interpretation choices. `cm_source_function_policy sp` is the `cm_lookup_policy` used by every preexisting helper, code model, and runtime representation. `cm_source_codegen_obligations` concretely instantiates shape, targets, patches, and entry validity, rather than assuming a new preservation premise. Additional source policy fields are used only by the real source operational semantics.
- `cm_output_pre` and `cm_output_capacity` preserve all eight output fields, original nonnegative capacities, full buffers including zero-capacity null-pointer behavior, required lengths and entry=-1 on both failure branches.
- `cm_output_ok sp` preserves bounds, entry=0, exact model opcode/immediate/data prefixes, and all unused tails. Its universal clause quantifies every decoded object, input, output trace, and status. It uses the actual `cm_source_terminates`, `cm_output_decodes`, and `tvm_terminates`; `cmc_compile_success_bridge` discharges it from the original well-formedness.
- The output decode definition is the verified `cmc_tvm_object_migration_lib` relation: valid instruction witness and deterministic object formed by paired opcode/immediate decoding and dense data patches at address 8. It is unchanged here.

## Reused helper declarations

The following five declarations and their With/Require/Ensure blocks were extracted verbatim from the current independently verified C cases; bodies are not copied:

1. `cmc_model_code_length`: `QCP_examples/QCP_demos_human/cmc_counts_migration.c:1579`.
2. `cmc_model_data_length`: same file, line 1618.
3. `cmc_emit_code`: `QCP_examples/QCP_demos_human/cmc_emit_code_migration.c`.
4. `cmc_patch_resolved_calls`: `QCP_examples/QCP_demos_human/cmc_patch_calls_migration.c`.
5. `cmc_emit_data`: `QCP_examples/QCP_demos_human/cmc_emit_data_migration.c`.

Only interpretation-parameter instantiations and actual program state discharge their premises. No helper promises additional output semantics here.

## New case definitions and effort boundary

Eleven definitions: two program representations, three whole uninitialized buffer wrappers, three exact-prefix buffer wrappers, three output representations. Buffer wrappers retain the source condition that a zero length owns emp and otherwise requires a non-null base. They wrap existing IntArray/Int64Array/UCharArray resources; no new memory model is introduced. No new internal pure predicate or lemma/proof body. Existing shared preservation proof costs belong to the public dependency ledger, not this case.

## Symbolic-execution repairs

1. Initial parser rejected mixed `:: *` type and `:` term declarations in one Extern block. Split them into separate type/term blocks.
2. `functions_ptr` bound existentially in an Assert is not a source-level identifier for a later `where`; removed that explicit binding so callee frame matching infers it from the current resource.
3. Explicit polymorphic `done=nil, tail=nil` instantiation did not match typed nil in the emitter resource. Let frame matching infer these list values from the exact resource instead.
4. Final resource bridge omitted the live local values of `globals` and `strings`, causing return-time reclaim failure. Added existential logical values and local bindings, leaving all heap ownership unchanged.

All are current-attempt annotation repairs; no original contract was weakened.

## Ordinary Assert semantic review

- location: cmc_compile: entry before cmc_model_code_length
  - purpose: function-call-boundary
  - named_semantic_state: existing program/emitter/output resource interfaces; no new internal predicate
  - upstream_paths: one sequential success path
  - downstream_work: helper call/resource conversion or success exit
  - redundant_with_invariant_or_postcondition: no
  - decision: keep
  - rationale: Original well-formedness, specialized with actual codegen obligations, entails code/data readiness needed by both length helpers.
- location: cmc_compile: after both capacity tests, before local emitter declaration
  - purpose: semantic-phase-transition
  - named_semantic_state: existing program/emitter/output resource interfaces; no new internal predicate
  - upstream_paths: two failed-capacity branches already returned
  - downstream_work: helper call/resource conversion or success exit
  - redundant_with_invariant_or_postcondition: no
  - decision: keep
  - rationale: Both capacity conditions now hold and buffers can enter the emitter/data contracts.
- location: cmc_compile: before cmc_emit_code
  - purpose: function-call-boundary
  - named_semantic_state: existing program/emitter/output resource interfaces; no new internal predicate
  - upstream_paths: one sequential success path
  - downstream_work: helper call/resource conversion or success exit
  - redundant_with_invariant_or_postcondition: no
  - decision: keep
  - rationale: No instruction has been written and the full compiled code model remains to be emitted.
- location: cmc_compile: between cmc_emit_code and cmc_patch_resolved_calls
  - purpose: function-call-boundary
  - named_semantic_state: existing program/emitter/output resource interfaces; no new internal predicate
  - upstream_paths: one sequential success path
  - downstream_work: helper call/resource conversion or success exit
  - redundant_with_invariant_or_postcondition: no
  - decision: keep
  - rationale: Emission has finished; raw physical CALL operands resolve to exactly the model code, ready for physical patching.
- location: cmc_compile: after patching and before globals/strings/data reads
  - purpose: function-call-boundary
  - named_semantic_state: existing program/emitter/output resource interfaces; no new internal predicate
  - upstream_paths: one sequential success path
  - downstream_work: helper call/resource conversion or success exit
  - redundant_with_invariant_or_postcondition: no
  - decision: keep
  - rationale: The instruction arrays now equal the code model; the original global/string representations supply exact data emission.
- location: cmc_compile: after cmc_emit_data and before setting entry=0
  - purpose: exit-bridge
  - named_semantic_state: existing program/emitter/output resource interfaces; no new internal predicate
  - upstream_paths: one sequential success path
  - downstream_work: helper call/resource conversion or success exit
  - redundant_with_invariant_or_postcondition: no
  - decision: keep
  - rationale: Finish the length/content bridge for all buffers and expose emitter local stores for scope reclamation. Shared success bridge supplies full decoded-object semantic preservation when folding cm_output_ok.

No lexical loops occur. No existential function witness is introduced. Existing interpretation-policy parameters are unchanged, and output semantics uses universal quantification, not a guessed witness.

## VC comparison

The retry handoff lists no failed VCs because iteration 1 ended before generation. `vc_comparisons` is therefore empty. Current generated obligations must still be independently proved; annotation completion does not claim proof completion.

## Preliminary mechanical text counts

These are annotation-owner counts of the current candidate, including comment delimiters and excluding blank lines. Main should retain its established cross-case counting method for the final effort ledger; this does not count any shared dependency proof as case proof.

```json
{
  "top_contract_nonblank_lines": 5,
  "body_assert_nonblank_lines": 148,
  "call_where_count": 5,
  "helper_contract_nonblank_lines": 41,
  "extern_and_import_nonblank_lines": 63,
  "case_definition_count": 11,
  "case_new_lemma_count": 0,
  "case_new_proof_nonblank_lines": 0
}
```

## Owner check outcomes

- `formal-case-lib-design`: terminal exit 0, controller status passed; current case compiled in 1.768347 seconds (dependency preparation separately recorded by controller).
- Canonical symexec: 4 annotation failures repaired, then terminal exit 0/status passed in 1.177 seconds. Generated artifacts were only written by this command.
- `formal-case-lib`: terminal exit 0/status passed; current compiled target reused, exact dependencies prepared by controller.
- Current generated manual contains six entailment witnesses and three return witnesses, plus generated spatial split declarations. They are intentionally unmodified and must be discharged by the proof owners. Seven safety witnesses and five partial-solve witnesses are in the generated goal set.
- No old failed VCs are listed by the handoff; empty comparisons are exact. Controller clean replay/annotation acceptance and later proof/final checks remain main-owned.
