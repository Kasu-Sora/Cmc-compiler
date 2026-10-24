# Annotation result

The source C*/HOL contract is translated using the existing string list ownership, representation safety/size, and exact emitted-byte model. The output retains every source node and source byte array, the initialized destination prefix is extended by cm_strings_bytes, and the returned cursor and undefined suffix are exact. Empty lists and empty strings remain allowed; the conditional source-nonnull property comes from existing cm_uint8_buffer ownership, not a new public premise.

The two helper declarations reproduce the already verified cmc_copy_bytes and cmc_write_byte contracts exactly. Copy receives the original prefix explicitly; write-byte receives model_byte = 0; other ghosts are inferred from live resources, including recursive tail/prefix. Runtime tokens and ABI are unchanged.

Case library: imports only. Existing counts/layout/copy models are reused without new definitions or annotation-stage lemmas. No algorithm mirror, no new internal predicate, and no higher-order witness.

## Assert review

location: after the null-node return, before reading the head fields and calling cmc_copy_bytes
purpose: function-call-boundary
named_semantic_state: none (direct string head/tail decomposition and builtin resources)
upstream_paths: the sole nonnull-node path
 downstream_work: copy the source bytes, append a zero terminator, recurse on the tail, restore head/list ownership
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: exposes the owned head fields and its exact byte array to the helper, preserves all resources, and derives length/tail/capacity bounds from the existing size/safety contract. In the empty-byte case cm_uint8_buffer is emp and the full zero-length array is also emp; the original conditional nonnull predicate is true without constraining sourcep.

No branch-control annotation or loops occur. No return Assert is needed: model unfolding, arithmetic associativity, append associativity and string representation folding connect the recursive result to Ensure.

## References

The verified globals annotation supplies only the recursive ownership/frame pattern. The verified copy and byte C declarations are authoritative helper contracts. The relevant correct sll annotation pattern and algorithm-mirror counterexample were inspected; no reference proof bodies or generated artifacts were copied.

## Machine checks and revisions

- formal-case-lib-design: passed, exit 0, first execution.
- symexec: passed, exit 0, first execution.
- formal-case-lib: passed, exit 0, first execution.
- No failed machine checks and no substantive post-check revision.
- Generated manual has 3 top-level witnesses and 4 optional split declarations; proving mode selection belongs to VC checking.
- The automatic module has 12 declarations (6 safety, 3 partial-solve pure, 3 partial-solve wrappers), subject to the established QCP automatic trust boundary.

## VC comparison

None: initial attempt has no failed VCs; vc_comparisons is empty.
