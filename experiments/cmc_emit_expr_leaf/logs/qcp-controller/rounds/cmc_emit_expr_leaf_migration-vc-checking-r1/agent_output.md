## Outcome

All 27 assigned top-level VCs have a proving assignment. The 37 generated split goals were each judged provable before whole-goal mode decisions or strategy planning. This is a provability assessment, not a Rocq proof result.

## Structural Blocker Scan

- Status: passed
- Top-level VCs scanned: 27
- No-split VCs checked first: 4
- Definite blockers: 0

The four no-split goals are the string/sizeof context openings and both member entry assertions. Each required address is available inside cm_program_context_rep; its three pointer witnesses can be rearranged into the target existential order. All return and node-opening goals retain the original parameter addresses. Member scalar facts follow from the pointer-to-struct shape in cm_member_valid plus cm_type_code_wf and cm_i32_code_count. No unconstrained current-to-@pre bridge was found.

## Annotation Comparison Review

No comparisons were supplied (first proving round). Current fact sources were checked independently: node nonnull and null-child facts are in cm_expr_rep; program fields/list addresses are in cm_program_context_rep; type and member bounds are explicit pure premises; the string-address, type-size and member-prefix bridges are already proved in the current case library. Its bridge premises are supplied by cm_typed_program, cm_type_code_wf, cm_type_refs and cm_member_valid at the corresponding VCs.

## Proof-Mode Decisions

All 37 split goals are provable. Thus all 23 parents with splits use aggressive_pre_process, without a whole-goal proof strategy. The four parents without splits use LLM_pre_process: both context openings and both member entry assertions are provable as whole entailments. Every split is listed, in declaration order, in its parent's split_strategies in group_plan.json; there are no failed split judgements.

## Common Proof Patterns

- C: discriminate the encoded type. Nonchar gives identity; char uses the existing encoding equivalence and divisibility-based nested modulo normalization. These are pure equalities without heap witnesses.
- E: substitute the leaf constructor, open cm_expr_rep/cm_expr_node, extract nonnull, and use the leaf payload to replace child witnesses by zero. Frame program, function and emitter resources.
- T: use the lvalue guard to reduce cm_leaf_code_for; normalize singleton/empty append and cancel the identical emitter plan. Opcode pure facts reduce by computation.
- R: reverse E with zero child witnesses, retain the supplied nonnull fact, and normalize the emitted/empty code as in T. String emission additionally rewrites the representation address to its model address using the typed-program premise.
- P: open or fold cm_program_context_rep with the existing struct/global/string pointers; reorder only separated fields/lists, preserve the nonnull fact, and cancel. No list contents change.
- S: inspect type constructors or use the proved representation-size bridge; typed-program supplies its universal struct-well-formedness premise. Encoding bounds use depth nonnegativity and base bounds.
- M: cm_member_valid forces a pointer to a struct and supplies index bounds. The well-formed struct id is below 1022, so modulo 1024 decodes it exactly. Typed-program supplies the matching slot well-formedness needed by the existing member-prefix bridge; simple modulo bounds discharge int safety.

No new helper declarations are expected. Existing case/dependency lemmas suffice, and short constructor/modulo arguments remain local to their witness proofs. No proof-reuse analysis was performed.

## VC Deltas

- `proof_of_cmc_const_immediate_return_wit_1`: C; non-character branch, identity immediate.
- `proof_of_cmc_const_immediate_return_wit_2`: C; character branch, 64-bit/8-bit nested modulo normalization.
- `proof_of_cm_emit_const_expr_entail_wit_1`: E; const leaf, value n; nonzero and spatial splits.
- `proof_of_cm_emit_const_expr_return_wit_1`: R; emitted const singleton uses retval=cm_const_immediate ty n.
- `proof_of_cm_emit_const_expr_return_wit_2`: R; const lvalue branch reduces code to [].
- `proof_of_cm_emit_const_expr_which_implies_wit_1`: T; Push opcode and const singleton, three splits.
- `proof_of_cm_emit_string_expr_entail_wit_1`: E; string leaf, value sid; nonzero and spatial splits.
- `proof_of_cm_emit_string_expr_return_wit_1`: R/P; emitted string address requires cm_rep_string_address_matches and both context folds.
- `proof_of_cm_emit_string_expr_return_wit_2`: R; string lvalue branch leaves emitter unchanged.
- `proof_of_cm_emit_string_expr_which_implies_wit_1`: P; open program context with three existing pointer witnesses (whole goal).
- `proof_of_cm_emit_string_expr_which_implies_wit_2`: T; Push singleton needs the typed-program string-address bridge.
- `proof_of_cm_emit_getc_expr_return_wit_1`: T; getc singleton, expression resource remains opaque.
- `proof_of_cm_emit_getc_expr_return_wit_2`: T; getc lvalue branch, empty-code append.
- `proof_of_cm_emit_getc_expr_which_implies_wit_1`: T; Getc opcode 24 and singleton transition.
- `proof_of_cm_sizeof_value_return_wit_1`: S; encoding >=1024 excludes non-pointer types; result 8.
- `proof_of_cm_sizeof_value_return_wit_2`: S/P; cm_rep_type_size_matches plus context refolding, two splits.
- `proof_of_cm_sizeof_value_which_implies_wit_1`: S; encoding nonnegativity from depth/base bounds.
- `proof_of_cm_sizeof_value_which_implies_wit_2`: P; open program context with three existing pointer witnesses (whole goal).
- `proof_of_cm_emit_sizeof_expr_entail_wit_1`: E; sizeof leaf, value cm_type_encode asked; nonzero and spatial splits.
- `proof_of_cm_emit_sizeof_expr_return_wit_1`: R; emitted sizeof singleton uses retval=cm_type_size structs asked.
- `proof_of_cm_emit_sizeof_expr_return_wit_2`: R; sizeof lvalue branch, empty-code append.
- `proof_of_cm_emit_sizeof_expr_which_implies_wit_1`: T; Push opcode and sizeof singleton, three splits.
- `proof_of_cm_member_array_value_context_entail_wit_1`: M/P; derive scalar call bounds from member-valid/type-wf and open context (whole goal).
- `proof_of_cm_member_array_value_context_return_wit_1`: P; restore program context after member-array call.
- `proof_of_cm_member_offset_value_context_safety_wit_1`: M; two modulo/subtraction machine-int safety bounds.
- `proof_of_cm_member_offset_value_context_entail_wit_1`: M/P; same member shape facts, offset-call context opening (whole goal).
- `proof_of_cm_member_offset_value_context_return_wit_1`: M/P; encoded pointee id matches model id; prefix bridge and context fold.

## Grouping Decisions

The initial groups follow semantic phase and resource/model transformation. A second load-and-coupling pass separated member final results from entry/safety work, and separated scalar constant/sizeof computations from leaf-emitter framing. Every group contains 2–5 top-level witnesses; there are no singleton or >6 groups and the maximum of 12 is respected.

| Group | Top-level | Aggressive splits | LLM | Difficulty | Context |
|---|---:|---:|---:|---:|---|
| constant_value | 2 | 2 | 0 | 3 | C: type discrimination and nested modulo reduction |
| leaf_const | 4 | 7 | 0 | 2 | E/T/R: leaf node opening, singleton emission transition, node refolding |
| leaf_string | 5 | 7 | 1 | 3 | E/T/R/P: string node and address bridge with program-context opening/refolding |
| leaf_getc | 3 | 5 | 0 | 1 | T: unchanged AST frame with singleton/empty code normalization |
| sizeof_value | 4 | 4 | 1 | 3 | S/P: type-size model equality and program-context opening/refolding |
| leaf_sizeof | 4 | 7 | 0 | 2 | E/T/R: sizeof node with encoded asked type and size singleton |
| member_context | 3 | 2 | 2 | 3 | M/P: pointer-to-struct shape, modulo safety, context opening |
| member_results | 2 | 3 | 0 | 3 | M/P: member-offset model equality and context refolding |

Likely tails are constant_value (2 pure splits; nested modulo arithmetic, no helper/library changes), leaf_string (7 splits plus one whole context opening; one existing address bridge and two resource folds), sizeof_value (4 splits plus one whole opening; existing size bridge and type encoding context), and member_results (3 splits; member shape, existing prefix bridge, and context restoration). member_context has 2 safety splits and two whole entry assertions but no new mathematical helper. No group needs sibling outputs or a new shared library. There is no heavy induction/permutation/sum/mask-clear lemma to isolate. String transition and final-result work remain together because the shared address-rewrite and program/node context is small, with only five witnesses; member results were independently separated from entry/safety work because the contexts do not require shared new helper ownership.

## Risks or Blockers

No annotation/specification/dependency blocker identified. The main implementation risks are separation-logic existential ordering and exact modulo lemma instantiation; both have explicit proof routes in the plan. Generated automatic proofs still contain their controller-owned placeholders, so this phase does not claim final verification success.

## Workload Accounting

- Manual structural scans: 1 (27 top-level VCs; 4 no-split first).
- Split judgements: 37 provable, 0 unprovable.
- Whole-goal provability judgements after split pass: 4, all provable.
- coq-debug invocations: 0.
- coq-check invocations: 0.
- Failed controller/check/debug invocations: 0.
- Formal-file edits: 0; no Show insertion was needed.
