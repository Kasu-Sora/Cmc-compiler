# Annotation delivery

The source BODY contract is retained exactly under the existing lookup-policy and codegen-obligations parameterization. Both helper contracts are copied from their verified BODY specifications. No validity, readiness, overflow or PC-zero fact has been added to the public precondition. cm_model_code is exactly the specified concatenation of prelude and all function code. Runtime and ABI are unchanged.

Only one new public definition, cm_model_code, was introduced. No internal predicate and no helper proof was introduced. PC-zero is an internal entailment obligation derivable by unfolding cm_function_pc and destructing the program function list. Plan and generated manual were inspected: all source facts and ownership remain available across both calls, while append associativity connects the final emitted prefix to the model.

References influencing design: the authoritative C* cmc_concrete_emit_code BODY and the previously verified cmc_emit_prelude and cmc_emit_functions BODY contracts; the prelude context open/close annotation shape. Generic majority-element and algorithm-mirror examples were read for the required positive/negative design contrast; no proof script or generated artifact was copied.

## Ordinary Assert review

location: before reading program->functions
purpose: semantic-phase-transition
named_semantic_state: cm_program_context_rep
upstream_paths: one straight-line entry
 downstream_work: read the functions field and invoke two helpers
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: exposes the field permission required for the C read while preserving all input resources and pure facts.

location: after reading functions, before cmc_emit_prelude
purpose: function-call-boundary
named_semantic_state: cm_model_code and cm_resolved_emitter_plan_rep
upstream_paths: one straight-line read
 downstream_work: prelude then functions emission
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: restores program context, exposes the compositional remaining plan, and derives PC(0)=11 for the second helper. It creates a proof obligation rather than assuming the PC equality.

## Checks and repair effort

First design check passed; first symbolic execution passed; first post-symexec library check passed. All terminal processes exited zero and reported status passed. No failed checks or repair edits occurred. No higher-order existential witness is introduced. No loops or branches occur.

```json
{"design_calls":1,"design_failed":0,"symexec_calls":1,"symexec_failed":0,"post_lib_calls":1,"post_lib_failed":0,"new_definitions":1,"new_helpers":0,"repair_notes":[]}
```

## VC comparison

First attempt; vc_comparisons is empty as required. Generated manual has three top-level obligations and three split obligations, inspected without modification.
