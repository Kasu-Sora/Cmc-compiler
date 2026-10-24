# Initial annotation design

Read the actual C* count-context source completely, including its contracts and inline proofs, and the context open/close implementations in cmc_concrete_defs.c. Read annotation-designing and its required design/authoring/predicate/operational/checklist guides, pure-proposition and semantic-Assert guides, the internal-predicate examples, and relevant positive/negative teaching examples. The verified counts migration report and exact helper source contracts informed reuse.

## Semantic decisions

- All four runtime bodies are preserved. The three helper declarations reproduce their exact verified contracts; their implementations and generated proof files are not imported.
- Type-code context has only the original expression representation and uninitialized output requirements. Its result stores exactly the type encoding.
- Count-wrapper pre/postconditions preserve every original pure fact, the full program/function contexts, exact count result, and i32 bounds. The statement wrapper preserves loop_. Return type, stack-bound facts and all other wellformedness conjuncts remain in the unchanged shared definitions.
- f remains the result of total function lookup with universally quantified cm_lookup_policy. No fid range is added.
- The same universally quantified cm_codegen_obligations boundary is reused with every original conjunction. No new emitter/TVM instantiation theorem is claimed.
- The case library is import-only. No new predicates or lemmas are needed; the existing context definitions and expression-node bridge suffice. No shared dependency bytes are edited.
- Context opening is an explicit ordinary Assert; helper borrowing uses exact where instantiation, and the return VC refolds all context resources. A separate closing Assert would only repeat Ensure, so it is intentionally omitted.
- No loops or higher-order existential function witnesses occur in this case. Existing policy/cg are universal source-semantic parameters.

## Ordinary Assert review

location: cm_expr_type_code_context before reading expr->ty
purpose: semantic-phase-transition
named_semantic_state: cm_expr_rep / cm_expr_payload (existing representation predicates)
upstream_paths: one straight-line path from the source contract
downstream_work: read ty and initialize output, then close expression representation
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: expose the stored type field while preserving every expression field and payload; closing is left to the return VC.

location: cm_expr_lvalue_count_context before helper call
purpose: function-call-boundary
named_semantic_state: cm_program_context_rep / cm_function_context_rep (existing representation predicates)
upstream_paths: one straight-line path
downstream_work: borrow structs/globals/locals to the exact helper, frame other fields/lists, then restore full contexts
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: the callee requires separate fields and lists, whereas the wrapper owns full contexts.

location: cm_expr_rvalue_count_context before helper call
purpose: function-call-boundary
named_semantic_state: cm_program_context_rep / cm_function_context_rep (existing representation predicates)
upstream_paths: one straight-line path
downstream_work: borrow structs/globals/locals to the exact helper, frame other fields/lists, then restore full contexts
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: the callee requires separate fields and lists, whereas the wrapper owns full contexts.

location: cm_stmt_code_count_context before helper call
purpose: function-call-boundary
named_semantic_state: cm_program_context_rep / cm_function_context_rep (existing representation predicates)
upstream_paths: one straight-line path
downstream_work: borrow structs/globals/locals and ret_ty to the exact helper, frame all other resources, then restore full contexts
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: preserve loop_, source function lookup, and all return/stack/count model facts while exposing the extra return-type field required by the helper.

## Failed check and repair

First symbolic execution failed before processing any function: category symbolic-execution, kind symexec-error, unexpected ':' / expected '::' at the first value declaration in the top-level Extern Coq block (original line 16). No symbolic state existed. This was annotation declaration syntax, not a tool failure. Repaired the related declaration block by separating type constructors (:: *) from term declarations (: ...), following the verified counts file. Generated files were transactionally rolled back and were not edited manually.

## VC comparison

None: this is the first attempt; vc_comparisons is empty.

Second symbolic execution parsed and completed the type-code function, then failed with category symbolic-execution / symexec-error on the lvalue helper where clause (line 133): existential zs from the preceding Assert is not in lexical annotation scope. The resource view itself exposes all required pointer stores. Removed zs/zg/zl where assignments from all three calls; pointer witness instantiation is inferred by heap matching, while policy, cg, p, f, projected model lists, expression/statement and loop_ remain explicit. This is a call-instantiation syntax repair, not a tool failure.

## Local completion evidence

The exact design check, canonical symexec, and post-symexec formal-case-lib check all terminated with exit 0 and controller status passed. Read the generated manual/goal/auto/check surfaces: eight top-level manual obligations describe expression/context opening and closing; six generated automatic witnesses describe helper call preparation. The generated manual remains untouched and is still a proof skeleton for the later proving owner. No failure class tool occurred.

Token comparison against baseline/runtime-source.c confirms all four runtime functions unchanged after removing QCP annotations and helper integration declarations. All three imported helper signatures/contracts are byte-identical extracts from the verified counts C file. Existing count/layout/copy-bytes libraries and ABI were never edited.
