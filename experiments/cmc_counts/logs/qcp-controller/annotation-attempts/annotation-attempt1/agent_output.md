# Annotation design notes

## Same-attempt feedback
- First design check: Coq could not infer the element type of cm_type_refs structs (line 121). Added its explicit list cm_struct_d type; no specification meaning changed.

## Semantic adaptations for main audit
- Reuse accepted AST, descriptors, encoded representation, cm_lookup_policy and all required imported runtime helper contracts. All function lookup uses the same universally quantified policy, including off-domain fid.
- Translate HOL booleans used as propositions into Rocq Prop; retain exact typing, code count and representability conjunctions.
- Only four irrelevant emitter predicates are explicitly universally quantified through cm_codegen_obligations. The record retains code-shape, target-validity, patch-validity and entry-validity individually, with exact source instantiation documented in the library. cm_codegen_fields_source proves the conjunction correspondence. Counts, typed_program, stack bound and model data bytes are direct definitions.
- Function-list ownership keeps the original separated headers/bodies representation, so no extra ownership or assumptions are introduced.
- Mathematical structural recursion follows original AST/descriptor equations; it is not an interpreter of runtime locals.

- Second design check: list append parsed in string_scope; activated list_scope. Third design check: nested args-count recursion is not definitionally equal after projection; replaced reflexivity by an explicit structural bridge proof.

The cg correspondence lemma is only a parameterized conjunction identity. No Rocq instantiation theorem for the source emit/TVM models is provided or claimed; the documented source predicates give its intended interpretation.

- Symexec 1 failed in cm_expr_lvalue_count call to cm_expr_counts: type/policy/program ghosts were not inferred through field equalities and opaque spatial predicates. Added explicit where bindings consistently across context-sensitive calls, preserving all specifications and resources.

- Symexec 2 rejected `head` in where: Assert existential names are not lexical logic-variable bindings. Removed explicit bindings for body existentials and retained original With parameters; spatial matching determines children/list suffixes.
- One design launch typo omitted the controller path and exited before invoking the controller. It changed no formal bytes or state; the exact supplied command was immediately rerun and passed.

- Symexec 3 reached the member-array helper but could not infer its base type through type encoding. Added transparent cm_member_base_type AST projection and used it in where; it names the existing child type and changes no contract meaning.

- Design checks 4–6 refined the nested argument-wellformedness and argument-representability bridge proofs: replace definitional reflexivity with list induction, and specialize the slot-list induction hypothesis. The seventh design check passed; subsequent annotation checks reused this compiled model until the member-type projection was added and compiled.

## Reference use
The accepted layout migration supplied the shared AST, field ownership and lookup contracts. Annotation-designing positive examples informed predicate/resource separation; its Kadane mirror counterexample was inspected to avoid replacing source mathematical counts by a runtime interpreter. No other case proof or generated artifact was copied.

## Annotation structure
There are no runtime loops. All ordinary assertions open or close owned AST, descriptor or context resources at call boundaries; each is represented by one key point. No separate internal predicate is needed: the stable mathematical facts are the existing source specification predicates. cm_member_base_type is a transparent type projection solely for lexical where instantiation. No branch-control annotation or higher-order existential result witness is used.

## Ordinary Assert semantic review

### cmc_expr_type_code_value: open expression field view

location: cmc_expr_type_code_value: open expression field view
purpose: function-call-boundary
named_semantic_state: none (source specification predicates and exact owned fields are explicit)
upstream_paths: function entry, selected constructor branch, or completed recursive head call as identified by the location
downstream_work: field reads and recursive/helper calls requiring the exposed representation
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: The owned expression node exposes its encoded type and preserves its full payload.

### cmc_args_code_count: nonempty argument recursive boundary

location: cmc_args_code_count: nonempty argument recursive boundary
purpose: function-call-boundary
named_semantic_state: none (source specification predicates and exact owned fields are explicit)
upstream_paths: function entry, selected constructor branch, or completed recursive head call as identified by the location
downstream_work: field reads and recursive/helper calls requiring the exposed representation
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: Head expression and remaining arguments retain their typing and exact count representability; output is initially uninitialized.

### cm_expr_counts: open expression dispatch

location: cm_expr_counts: open expression dispatch
purpose: function-call-boundary
named_semantic_state: none (source specification predicates and exact owned fields are explicit)
upstream_paths: function entry, selected constructor branch, or completed recursive head call as identified by the location
downstream_work: field reads and recursive/helper calls requiring the exposed representation
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: The original node fields and payload partition ownership for dispatch and recursive count calls.

### cm_expr_counts: VAR recursive/helper call boundary

location: cm_expr_counts: VAR recursive/helper call boundary
purpose: function-call-boundary
named_semantic_state: none (source specification predicates and exact owned fields are explicit)
upstream_paths: function entry, selected constructor branch, or completed recursive head call as identified by the location
downstream_work: field reads and recursive/helper calls requiring the exposed representation
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: The constructor determines child counts and wellformedness while parent metadata and output cells remain framed.

### cm_expr_counts: ASSIGN recursive/helper call boundary

location: cm_expr_counts: ASSIGN recursive/helper call boundary
purpose: function-call-boundary
named_semantic_state: none (source specification predicates and exact owned fields are explicit)
upstream_paths: function entry, selected constructor branch, or completed recursive head call as identified by the location
downstream_work: field reads and recursive/helper calls requiring the exposed representation
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: The constructor determines child counts and wellformedness while parent metadata and output cells remain framed.

### cm_expr_counts: BINARY recursive/helper call boundary

location: cm_expr_counts: BINARY recursive/helper call boundary
purpose: function-call-boundary
named_semantic_state: none (source specification predicates and exact owned fields are explicit)
upstream_paths: function entry, selected constructor branch, or completed recursive head call as identified by the location
downstream_work: field reads and recursive/helper calls requiring the exposed representation
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: The constructor determines child counts and wellformedness while parent metadata and output cells remain framed.

### cm_expr_counts: UNARY recursive/helper call boundary

location: cm_expr_counts: UNARY recursive/helper call boundary
purpose: function-call-boundary
named_semantic_state: none (source specification predicates and exact owned fields are explicit)
upstream_paths: function entry, selected constructor branch, or completed recursive head call as identified by the location
downstream_work: field reads and recursive/helper calls requiring the exposed representation
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: The constructor determines child counts and wellformedness while parent metadata and output cells remain framed.

### cm_expr_counts: INDEX recursive/helper call boundary

location: cm_expr_counts: INDEX recursive/helper call boundary
purpose: function-call-boundary
named_semantic_state: none (source specification predicates and exact owned fields are explicit)
upstream_paths: function entry, selected constructor branch, or completed recursive head call as identified by the location
downstream_work: field reads and recursive/helper calls requiring the exposed representation
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: The constructor determines child counts and wellformedness while parent metadata and output cells remain framed.

### cm_expr_counts: MEMBER recursive/helper call boundary

location: cm_expr_counts: MEMBER recursive/helper call boundary
purpose: function-call-boundary
named_semantic_state: none (source specification predicates and exact owned fields are explicit)
upstream_paths: function entry, selected constructor branch, or completed recursive head call as identified by the location
downstream_work: field reads and recursive/helper calls requiring the exposed representation
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: The constructor determines child counts and wellformedness while parent metadata and output cells remain framed.

### cm_expr_counts: CALL recursive/helper call boundary

location: cm_expr_counts: CALL recursive/helper call boundary
purpose: function-call-boundary
named_semantic_state: none (source specification predicates and exact owned fields are explicit)
upstream_paths: function entry, selected constructor branch, or completed recursive head call as identified by the location
downstream_work: field reads and recursive/helper calls requiring the exposed representation
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: The constructor determines child counts and wellformedness while parent metadata and output cells remain framed.

### cm_expr_counts: PUTC recursive/helper call boundary

location: cm_expr_counts: PUTC recursive/helper call boundary
purpose: function-call-boundary
named_semantic_state: none (source specification predicates and exact owned fields are explicit)
upstream_paths: function entry, selected constructor branch, or completed recursive head call as identified by the location
downstream_work: field reads and recursive/helper calls requiring the exposed representation
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: The constructor determines child counts and wellformedness while parent metadata and output cells remain framed.

### cm_expr_counts: PUTI recursive/helper call boundary

location: cm_expr_counts: PUTI recursive/helper call boundary
purpose: function-call-boundary
named_semantic_state: none (source specification predicates and exact owned fields are explicit)
upstream_paths: function entry, selected constructor branch, or completed recursive head call as identified by the location
downstream_work: field reads and recursive/helper calls requiring the exposed representation
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: The constructor determines child counts and wellformedness while parent metadata and output cells remain framed.

### cm_expr_counts: EXIT recursive/helper call boundary

location: cm_expr_counts: EXIT recursive/helper call boundary
purpose: function-call-boundary
named_semantic_state: none (source specification predicates and exact owned fields are explicit)
upstream_paths: function entry, selected constructor branch, or completed recursive head call as identified by the location
downstream_work: field reads and recursive/helper calls requiring the exposed representation
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: The constructor determines child counts and wellformedness while parent metadata and output cells remain framed.

### cmc_stmt_code_count: open statement dispatch

location: cmc_stmt_code_count: open statement dispatch
purpose: function-call-boundary
named_semantic_state: none (source specification predicates and exact owned fields are explicit)
upstream_paths: function entry, selected constructor branch, or completed recursive head call as identified by the location
downstream_work: field reads and recursive/helper calls requiring the exposed representation
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: Statement kind exposes its expression and substatement resources while preserving function return type.

### cmc_stmt_code_count: EXPR recursive/helper call boundary

location: cmc_stmt_code_count: EXPR recursive/helper call boundary
purpose: function-call-boundary
named_semantic_state: none (source specification predicates and exact owned fields are explicit)
upstream_paths: function entry, selected constructor branch, or completed recursive head call as identified by the location
downstream_work: field reads and recursive/helper calls requiring the exposed representation
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: The statement constructor exposes child typing and representability required by calls and preserves all other owned fields.

### cmc_stmt_code_count: INIT recursive/helper call boundary

location: cmc_stmt_code_count: INIT recursive/helper call boundary
purpose: function-call-boundary
named_semantic_state: none (source specification predicates and exact owned fields are explicit)
upstream_paths: function entry, selected constructor branch, or completed recursive head call as identified by the location
downstream_work: field reads and recursive/helper calls requiring the exposed representation
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: The statement constructor exposes child typing and representability required by calls and preserves all other owned fields.

### cmc_stmt_code_count: SEQ recursive/helper call boundary

location: cmc_stmt_code_count: SEQ recursive/helper call boundary
purpose: function-call-boundary
named_semantic_state: none (source specification predicates and exact owned fields are explicit)
upstream_paths: function entry, selected constructor branch, or completed recursive head call as identified by the location
downstream_work: field reads and recursive/helper calls requiring the exposed representation
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: The statement constructor exposes child typing and representability required by calls and preserves all other owned fields.

### cmc_stmt_code_count: BLOCK recursive/helper call boundary

location: cmc_stmt_code_count: BLOCK recursive/helper call boundary
purpose: function-call-boundary
named_semantic_state: none (source specification predicates and exact owned fields are explicit)
upstream_paths: function entry, selected constructor branch, or completed recursive head call as identified by the location
downstream_work: field reads and recursive/helper calls requiring the exposed representation
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: The statement constructor exposes child typing and representability required by calls and preserves all other owned fields.

### cmc_stmt_code_count: IF recursive/helper call boundary

location: cmc_stmt_code_count: IF recursive/helper call boundary
purpose: function-call-boundary
named_semantic_state: none (source specification predicates and exact owned fields are explicit)
upstream_paths: function entry, selected constructor branch, or completed recursive head call as identified by the location
downstream_work: field reads and recursive/helper calls requiring the exposed representation
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: The statement constructor exposes child typing and representability required by calls and preserves all other owned fields.

### cmc_stmt_code_count: WHILE recursive/helper call boundary

location: cmc_stmt_code_count: WHILE recursive/helper call boundary
purpose: function-call-boundary
named_semantic_state: none (source specification predicates and exact owned fields are explicit)
upstream_paths: function entry, selected constructor branch, or completed recursive head call as identified by the location
downstream_work: field reads and recursive/helper calls requiring the exposed representation
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: The statement constructor exposes child typing and representability required by calls and preserves all other owned fields.

### cmc_stmt_code_count: RETURN recursive/helper call boundary

location: cmc_stmt_code_count: RETURN recursive/helper call boundary
purpose: function-call-boundary
named_semantic_state: none (source specification predicates and exact owned fields are explicit)
upstream_paths: function entry, selected constructor branch, or completed recursive head call as identified by the location
downstream_work: field reads and recursive/helper calls requiring the exposed representation
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: The statement constructor exposes child typing and representability required by calls and preserves all other owned fields.

### cmc_param_stores_count: nonempty parameter boundary

location: cmc_param_stores_count: nonempty parameter boundary
purpose: function-call-boundary
named_semantic_state: none (source specification predicates and exact owned fields are explicit)
upstream_paths: function entry, selected constructor branch, or completed recursive head call as identified by the location
downstream_work: field reads and recursive/helper calls requiring the exposed representation
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: The parameter list splits into the head normalization contribution and representable suffix.

### cmc_function_prologue_count: open function context

location: cmc_function_prologue_count: open function context
purpose: function-call-boundary
named_semantic_state: none (source specification predicates and exact owned fields are explicit)
upstream_paths: function entry, selected constructor branch, or completed recursive head call as identified by the location
downstream_work: field reads and recursive/helper calls requiring the exposed representation
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: The function context exposes params while retaining locals, body and next fields as frame.

### cmc_function_code_count: open contexts after prologue

location: cmc_function_code_count: open contexts after prologue
purpose: function-call-boundary
named_semantic_state: none (source specification predicates and exact owned fields are explicit)
upstream_paths: function entry, selected constructor branch, or completed recursive head call as identified by the location
downstream_work: field reads and recursive/helper calls requiring the exposed representation
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: The completed prologue count remains bound while opened contexts supply the statement call fields.

### cmc_function_prefix_count: nonempty function recursive boundary

location: cmc_function_prefix_count: nonempty function recursive boundary
purpose: function-call-boundary
named_semantic_state: none (source specification predicates and exact owned fields are explicit)
upstream_paths: function entry, selected constructor branch, or completed recursive head call as identified by the location
downstream_work: field reads and recursive/helper calls requiring the exposed representation
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: The list splits into a function context/body and its suffix. The index is the original program length minus suffix length.

### cmc_function_prefix_count: expose next after head count

location: cmc_function_prefix_count: expose next after head count
purpose: function-call-boundary
named_semantic_state: none (source specification predicates and exact owned fields are explicit)
upstream_paths: function entry, selected constructor branch, or completed recursive head call as identified by the location
downstream_work: field reads and recursive/helper calls requiring the exposed representation
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: Head count is bound to the indexed function model; exposing next permits recursion on the owned suffix.

### cmc_function_pc: open program context

location: cmc_function_pc: open program context
purpose: function-call-boundary
named_semantic_state: none (source specification predicates and exact owned fields are explicit)
upstream_paths: function entry, selected constructor branch, or completed recursive head call as identified by the location
downstream_work: field reads and recursive/helper calls requiring the exposed representation
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: Program field ownership exposes the function list or global/string descriptors required by imported count helpers.

### cmc_functions_code_size_count: nonempty function recursive boundary

location: cmc_functions_code_size_count: nonempty function recursive boundary
purpose: function-call-boundary
named_semantic_state: none (source specification predicates and exact owned fields are explicit)
upstream_paths: function entry, selected constructor branch, or completed recursive head call as identified by the location
downstream_work: field reads and recursive/helper calls requiring the exposed representation
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: The list splits into a function context/body and its suffix. The index is the original program length minus suffix length.

### cmc_functions_code_size_count: expose next after head count

location: cmc_functions_code_size_count: expose next after head count
purpose: function-call-boundary
named_semantic_state: none (source specification predicates and exact owned fields are explicit)
upstream_paths: function entry, selected constructor branch, or completed recursive head call as identified by the location
downstream_work: field reads and recursive/helper calls requiring the exposed representation
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: Head count is bound to the indexed function model; exposing next permits recursion on the owned suffix.

### cmc_model_code_length: open program context

location: cmc_model_code_length: open program context
purpose: function-call-boundary
named_semantic_state: none (source specification predicates and exact owned fields are explicit)
upstream_paths: function entry, selected constructor branch, or completed recursive head call as identified by the location
downstream_work: field reads and recursive/helper calls requiring the exposed representation
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: Program field ownership exposes the function list or global/string descriptors required by imported count helpers.

### cmc_model_data_length: open program context

location: cmc_model_data_length: open program context
purpose: function-call-boundary
named_semantic_state: none (source specification predicates and exact owned fields are explicit)
upstream_paths: function entry, selected constructor branch, or completed recursive head call as identified by the location
downstream_work: field reads and recursive/helper calls requiring the exposed representation
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: Program field ownership exposes the function list or global/string descriptors required by imported count helpers.

### cmc_function_pc: close context after reading function root

location: cmc_function_pc: close context after reading function root
purpose: function-call-boundary
named_semantic_state: none (source specification predicates and exact owned fields are explicit)
upstream_paths: function entry, selected constructor branch, or completed recursive head call as identified by the location
downstream_work: field reads and recursive/helper calls requiring the exposed representation
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: The root pointer is bound to the function list and the program context is restored for the recursive counting helper.

### cmc_model_code_length: close context after reading function root

location: cmc_model_code_length: close context after reading function root
purpose: function-call-boundary
named_semantic_state: none (source specification predicates and exact owned fields are explicit)
upstream_paths: function entry, selected constructor branch, or completed recursive head call as identified by the location
downstream_work: field reads and recursive/helper calls requiring the exposed representation
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: The root pointer is bound to the function list and the program context is restored for the recursive counting helper.

## VC comparison
First attempt: vc_comparisons is empty as required.

## Owner checks and generation accounting

- Ten exact formal-case-lib-design invocations: six failed while authoring the library and four passed. One additional mistyped launch never entered the controller and is separately disclosed above.
- Four exact symexec invocations: three annotation/where failures followed by success; none was classified as a tool failure. Failed invocations rolled back all generated files. Successful generation took 7.784 seconds and covered all 15 bodies.
- One post-symexec formal-case-lib invocation passed (terminal exit 0, JSON status passed).
- Initial C annotation generation plus three feedback-driven C revisions (explicit where, removal of out-of-scope existential names, member-base type projection). One pre-first-symexec refinement added the program-context closing boundaries. The library had six feedback-driven repair edits before its first pass; the later projection was one further library addition.
- Final candidate: 33 ordinary assertions, 33 plan key points, 37 explicit where clauses, no loops and no branch-control constructs. Seven imported helper declaration contracts are unchanged from the accepted layout case.
- Generated proof work remains for the proving stages: 150 top-level manual placeholders and 383 split drafts; the auto file contains 184 tool-trusted Admitted witnesses. The annotation owner authored no manual proof or generated-file edit.

Timing values below are copied from terminal controller JSON, not estimated authoring time. Each design pair is (check elapsed_seconds, dune_preparation elapsed_seconds):
1. failed (1.664971, 7.922398)
2. failed (1.710610, 5.881921)
3. failed (1.879609, 5.849039)
4. failed (1.785774, 5.852161)
5. failed (1.933740, 5.959695)
6. failed (1.783887, 5.972074)
7. passed (1.813778, 5.842094)
8. passed (0.082670, 5.994570)
9. passed (0.069624, 5.989641)
10. passed (2.041718, 6.172309)

Symexec elapsed_seconds: failed 0.024, failed 0.085, failed 2.473, passed 7.784. Post-symexec lib: check 0.070157, preparation 6.171380. The latest owner progress evidence is symexec-progress-owner.json beside this note; the controller command transcript contains each earlier JSON response. These components exclude human/model authoring time and are not a wall-clock migration total.

## Remaining proof guidance

The context-closing assertion in model_code_length derives the function-list length bound from existing representability: every function count is at least 21 (prologue 14, nonnegative parameters/body, epilogue 7), so list length is bounded by the already bounded sum. No new public input assumption was introduced. Prefix function body typing follows typed_program plus the original index = total length - suffix length relationship and the function-count representation equality.
