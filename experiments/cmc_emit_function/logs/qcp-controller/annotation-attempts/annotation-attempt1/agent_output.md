# Annotation delivery

All three original BODY contracts were translated with their pure facts and resources intact. `cmc_emit_param_stores_from` retains arbitrary `full`, `prefix`, `params`, slot/offset bounds and arbitrary `tail`; `cmc_emit_prologue` retains full function/stmt ownership and original safety; `cmc_emit_function` retains original total lookup, statement/count/PC/temp/size conditions. Existing lookup policy and cg arguments remain arbitrary.

Three instruction sequence models exactly translate cmc_codegen.c:981–1026. Parameter stores recurse on the tail first and retain the slot-index-derived offset. Two transparent observations expose the nonempty parameter head/tail; there are no new assumptions, helper proofs, internal predicates, ordinary Assert, loop, branch-control command, or higher-order witness. Read-only references were prior accepted CMC BODY annotations and model libraries; positive majority-element and internal-predicate teaching examples plus negative algorithm-mirror examples were reviewed. Only previous public libraries are imported.

Nineteen which-implies boundaries in annotation_plan.json connect resource observations, return-cell canonicalization, recursive prefix/suffix safety and exact plan segments. Unchanged scalar bridges are included symmetrically in plan expansion/folding. Function contexts are opened only to pass actual field resources/read body and then restored. Ordinary Assert review: none; no full state cut duplicates a postcondition. All machine checks reported below reached terminal exit 0 and JSON status passed for the successful call.

## Checks and repairs

1. formal-case-lib-design passed. First symexec failed at the redundant empty-branch partial assertion: unification selected pointer literal 0 before matching the opaque cm_slot_list_rep at the symbolic pointer. Removed this unnecessary bridge, leaving the actual null-to-empty obligation in the return witness. No contract or runtime change.
2. formal-case-lib-design passed. Second symexec processed the parameter function and failed at prologue call instantiation because bare polymorphic nil did not specialize to list cm_slot_d under cm_slots_size. Used sublist(0, 0, cm_function_params(f)) as the typed canonical empty prefix. No new definition or assumption.
3. formal-case-lib-design passed. Third symexec passed (5.741 seconds). Post-symexec formal-case-lib passed. Reviewed generated resource boundaries and return facts; all repeated projection expressions reduce to the same head/tail observations.

## Effort counters

```json
{"design_calls":3,"design_failed":0,"symexec_calls":3,"symexec_failed":2,"post_lib_calls":1,"post_lib_failed":0,"new_definitions":5,"new_helpers":0}
```

## VC comparison

First attempt: no failed prior VCs; vc_comparisons is empty. Generated inventory: 41 top-level manual obligations and 84 split obligations. The independent VC-checking and proof stages remain controller-owned.
