# call_capacity effort record

Completed seven assigned split goals and three aggressive top-level VCs. Each split starts with `LLM_pre_process ltac:(lia)`; top-level branches use the corresponding `Goal_apply` only. Pure opcode facts use definitional reduction. Capacity proofs reduce fragment lengths to 1 or 4 and reuse the existing capacity premise. Spatial predicates are not unfolded.

- Development invocations: 3, with 2 failures and 1 success.
- Exact group-check invocations: 1, successful.
- Debug invocations: 3, with 2 failures and 1 successful context inspection.
- Development repair: `cbn` left the binding fragment opaque, so the singleton-length rewrite found no matching subterm; making that rewrite optional then left an unsolved arithmetic goal. Replaced the attempted simplification with explicit definitional `change` statements for the fragment lengths.
- Debug repair: the initial small diagnostic prelude opened `sac` before importing `naive_C_Rules`, then lacked the explicit `Psatz` import for `lia`. Corrected those debug-only prelude issues.
- Added library helpers: none. The group library remains unchanged.

Files are ready for controller sealing; no writes will follow this terminal delivery.
