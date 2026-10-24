# Design and semantic decisions

Both original runtime bodies and the static qualifier are retained. target is unrestricted signed long long. target - index appears only as mathematical Z subtraction in the contracts. The imported cmc_function_code_count contract is copied exactly from the previously verified counts case; its implementation is not part of this case.

The library exports the unchanged counts/layout dependency chain. It adds the complete four source readiness predicates and cm_temp_offset, retaining all 18 conjuncts of function readiness, including the emitted-body-end bound normalized by the unconditional source cm_stmt_code_length theorem (cmc_codegen.c:1460-1487), as in cmc_concrete_function_ready.c:217-234. This does not claim a Rocq verification of the full emitter semantics. Lookup policy and codegen obligations remain universally quantified as before.

The public cm_function_prefix_total_bounds has no bounds on remaining and no well-formedness/readiness premises. New unconditional expression, statement, function and list nonnegativity bridges support it. No extra internal predicate is needed: this case has no lexical loops, and the existing mathematical list-prefix model is reused.

References: prior counts annotations informed the list-opening and field-read resource boundaries. The mandatory majority-element positive example and algorithm-mirror negative example were reviewed; no runtime mirror was introduced.

## Ordinary Assert review

- prefix-head-call: function-call-boundary; named_semantic_state: none. Upstream paths are the two early-return tests; downstream work is head counting followed by recursive suffix counting. Not redundant with the postcondition/invariant. Keep to expose the nonempty list head and exact callee resources.
- prefix-tail-call: function-call-boundary; named_semantic_state: none. Upstream is the head-count call; downstream reads the next field then recurses. Not redundant. Keep to unfold the head context for the concrete field read and retain tail readiness and all original facts.
- pc-prefix-call: function-call-boundary; named_semantic_state: none. Single entry path; downstream reads the program field and calls the recursive helper. Not redundant. Keep to expose field ownership and derive the helper input length bound.

- pc-prefix-fold: function-call-boundary; named_semantic_state: none. The program field has been read; downstream calls the prefix helper. Keep to refold the program resource into the callee interface.

Higher-order existential witness review: not applicable. policy and cg are universal input parameters, not existential witnesses.

## Checks and repairs

1. formal-case-lib-design failed at the final prefix-bound arithmetic step (line 135): The recursive tail index needed normalization. The initial attempted length + 1 and 1 + length rewrites did not match; a third diagnostic run exposed Z.succ(length), and the final repair uses that exact form. The unconditional nonnegativity lemmas had compiled throughout.

2. First symexec failed at C line 8: Extern Coq kind declarations and term declarations need separate blocks. Split the block; no runtime or contract semantic change.

3. A design-check command was accidentally transcribed without the controller.py path and failed immediately before entering the controller; reran the exact handoff command successfully. No formal bytes changed from that invocation.
4. Second symexec failed at the main prefix call: program context was still unfolded after the field read. Added a call-boundary Assert that folds that resource and explicit functions = cm_program_functions(p) instantiation.

## VC comparison

First attempt: no previous VCs; vc_comparisons is empty.

## Delivery checks

The final formal-case-lib-design, symexec, and formal-case-lib commands each returned terminal exit 0 and JSON status passed. Generated manual obligations were inspected read-only; all target/index alignment, original readiness/count predicates and head/tail semantic equations remain exposed. The library adds 5 definitions (including the source structural recursion) and 8 proved lemmas; unchanged counts/layout/copy-bytes libraries are only imported. The one imported external helper declaration is integration annotation, not an original target-file forward declaration. Controller acceptance and later VC proofs remain separate from this annotation delivery.
