# param-transition proof notes

Proved both assigned top-level witnesses and all 13 split goals. Each split starts with explicit `LLM_pre_process ltac:(lia || nia || int_auto)`. Top-level proofs dispatch only with the prescribed `Goal_apply` calls.

Reused `cm_slot_size_matches__temp_context` and `cm_slots_size_nonnegative__call_bounds` through the accepted dependency library. The only added helper is `cm_function_slots_size_snoc__param_transition`, proved by list induction without well-formedness premises. Tail slots-wf is derived by shifting valid indexes by one; no additional assumptions or annotation changes were needed.

Actual repair: the first development invocation rejected an underspecified RHS placeholder in a `change` command for member-size matching. Replacing it with the full `cm_slot_size structs (cm_emit_params_head params)` expression made the subsequent development check and exact check pass.

```json
{"development_calls":2,"development_failed":1,"debug_calls":1,"debug_failed":0,"exact_calls":1,"exact_failed":0,"new_helpers":1}
```
