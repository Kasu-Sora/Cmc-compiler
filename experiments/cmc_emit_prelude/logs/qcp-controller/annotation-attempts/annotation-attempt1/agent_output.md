# Prelude annotation delivery

The public function contract preserves exactly the original program context and resolved emitter plan contract, generalized over the existing lookup policy. There are no added program well-formedness, main index, readiness or representability premises. The new public model is the exact eleven-instruction source prelude. Both helper contracts are copied from the verified BODY contracts in cmc_emit_plan_migration.c. The plan library and its transitive dependency closure supply all other definitions. No lemma was added and no manual proof was written by this owner.

References influencing annotation design: the context field opening pattern in cmc_function_pc_total_migration.c and the helper BODY contracts in cmc_emit_plan_migration.c. They were used only as syntax/interface references; the new contract derives from cmc_concrete_emit_prelude.c. Positive predicate examples and the algorithm-mirror negative example were inspected: cm_emit_prelude specifies an emitted instruction fragment, not a second runtime interpreter.

## Ordinary Assert review

location: before program->main_id read
purpose: semantic-phase-transition
named_semantic_state: cm_program_context_rep (opened)
upstream_paths: one straight-line entry path
downstream_work: read the main identifier, restore the context, then eleven helper calls
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: exposes owned program fields for the read while preserving the emitter plan and the live uninitialized main_id local via undef_data_at.

location: after main_id read, before first helper call
purpose: function-call-boundary
named_semantic_state: cm_resolved_emitter_plan_rep
upstream_paths: one straight-line field-read path
downstream_work: eleven plan helper calls
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: restores program context, exposes the literal plan and opcode equalities required by symbolic execution, and binds main_id to cm_program_main p. No final redundant assertion is used.

## Owner calls and repairs

```json
{"design_calls":5,"design_failed":0,"symexec_calls":5,"symexec_failed":4,"post_lib_calls":1,"post_lib_failed":0,"new_definitions":1,"new_helpers":0}
```

1. First symexec failed in the Extern block at line 11 with `unexpected token ':'; expected '::'`: types and value declarations must be separate Extern blocks. Split the blocks; reran design and symexec.
2. Second symexec failed at the context-open read boundary (then line 62), `cannot find the program variable main_id in assertion`: the full assertion omitted the live uninitialized local. Added `undef_data_at(&main_id, int)`; reran design and symexec.
3. Third symexec failed at the first cm_emit_plan call: the caller retained opaque `app(cm_emit_prelude(policy,p),tail)` and no opcode facts, while the helper needed a concrete cons list and opcode matching. Expanded the plan at the context-close call boundary and exposed the five opcode equalities; reran design and symexec. Public contract/model unchanged.
4. Fourth symexec failed at the first call after cm_emit_call_plan: the returned done-prefix contains `cm_function_pc(policy,p,main_id)`, while the where instance used `cm_function_pc(policy,p,cm_program_main(p))`. The existing equality is mathematically enough but QCP does not normalize it under the opaque function application during resource matching. Consistently used the runtime main_id in all post-read literal plan/call instances; kept the logical read binding for proof. Reran design and symexec.
5. Fifth design and symexec, then post-symexec lib check, all reached actual exit 0 and JSON status passed.

The generated manual has three top-level manual witnesses and seven split goals. They cover opening the program context, closing it while rewriting the plan/opcodes, and restoring the final canonical done prefix. These remain for the independent checking/proving owners. This annotation delivery does not claim that manual proofs or controller acceptance have finished.

## VC comparison

Initial attempt: no failed VCs from a previous attempt; vc_comparisons is empty.
