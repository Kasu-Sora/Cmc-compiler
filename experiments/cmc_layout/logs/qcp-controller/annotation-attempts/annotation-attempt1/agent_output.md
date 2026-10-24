# Annotation iteration 1: whole concrete layout migration

All 39 runtime bodies and the mutually recursive forward declaration are retained. Runtime-body lexical tokens were compared to the frozen runtime source and match. The ABI header is unchanged. There are no lexical runtime loops.

The library translates the source types and all 14 expression / 11 statement constructors, descriptor records, type encoding, layout/prefix/selection models, original safe predicates, expression/argument temporary-pair algebra, and syntax/list heap representations. Spatial ownership matches cmc_rep.c field by field, including the original empty-byte-buffer case and unused-child null facts. Program/function contracts own only their named fields. Every public contract retains its original logical input parameters, side conditions, exact output model, and preservation obligations. The two binding contracts additionally quantify over the source total-lookup policy, as described below. The signed count in cmc_code_slot_size is unrestricted, including negative values.

Source structural recursions are retained as source semantics, not newly invented C interpreters. cm_expr_rep_node, cm_stmt_rep_node, cm_expr_tpair_call and cm_expr_safe_call provide transparent bridges for Rocq's nested-list encoding of the source mutual recursion. Public semantic predicates also used inside the body remain spec predicates; no new internal pure predicate is needed. Recursive cuts expose C facts and ownership explicitly.

Reuse: builtin UCharArray.full and QCP standard list/integer/separation libraries; the accepted cmc_copy_bytes_migration_lib supplies cmc_uint8_buffer_nonnull. The current cm_uint8_buffer wrapper preserves source empty-buffer ownership, and cm_uint8_buffer_source proves its equivalence to that source definition. No encoding helpers from earlier byte/word cases apply to the layout models.

References inspected for annotation style: QCP_demos_LLM/sll.c for list opening and eval.c/eval_def.h for typed-AST constructor cuts, plus the required algorithm-mirror negative example. Their generated/proof artifacts were not copied.

## Check history and repairs

- Initial library design check passed (source domains, models, representations and four transparent structural bridges).
- Symexec syntax failure: external kinds used `: Type`; corrected to QCP `:: *`.
- Symexec syntax failure: kind and term declarations shared one Extern Coq block; split them into their respective blocks.
- Symexec memory-read failure at cmc_members_size/member->ty: opaque list ownership was not opened; added exact nonnull descriptor-node call-boundary cuts across all recursive list helpers.
- Symexec call-instantiation failure at cmc_binding_array/cmc_binding_array_value: p could not be inferred through nested projection equations; supplied explicit where logical arguments, and the corresponding member wrapper arguments.
- An accidental incomplete launch omitted the controller script path and exited with Python's no __main__ diagnostic. It performed no controller operation or formal write. The exact handoff command was immediately run afterward; no result from the malformed launch is considered evidence.
- Canonical symexec then passed for the entire 39-body file, producing all four generated roles. The generated manual still contains pending proof witnesses; no body is claimed proved at this annotation stage.

## Lookup correspondence

The pinned source kernel reports `inth n l = NTH (num_of_int n) l`; NTH_DEF fixes only `NTH 0 (h :: t) = h` and `NTH (SUC n) (h :: t) = NTH n t`. It does not constrain empty-list values. The pinned theorem catalogue defines `num_of_int x = (@n. &n = x)`. Nonnegative values have the unique natural conversion; for every negative integer the choice predicate is empty, hence the same unspecified natural is selected.

The initial fixed-default function lookup candidate was discarded. The final `cm_lookup_policy` is an explicit logical record containing that arbitrary negative natural and the arbitrary, residual-index-dependent function `NTH n []`. `cm_function_nth` implements exactly the two source cons equations and uses the supplied nil value. Both binding contracts universally quantify over the policy, use it in `f = cm_function_at policy fid functions`, and use the identical policy in `cm_binding_array_code`. This adds no caller precondition and no fid bound: the theorem is stronger, covering every source choice interpretation. The source interpretation specializes the policy with its actual choice results. `cm_function_nth_source` and `cm_num_of_int_source` prove the correspondence; `cm_function_at_valid` proves the standard valid-index lookup independently of policy. Other descriptor selectors are used only under their original valid-index predicates and keep bounded lookup defaults.

Source evidence: `logs/20261015T121956Z-cstar-lookup-probe/stdout.txt` and the pinned C* 0.5.7 `theorems.c2de4a9186c79989.jsonl`, inspected by the parent audit. No source semantic axiom was added to the case library.

higher_order_witness_review:
- domain: residual natural index for the unspecified source NTH nil result.
- finite_contiguous_domain: no.
- uniquely_determined_by_input: no, the source definition is choice-totalized off-domain.
- canonical_definition_available: no source-chosen value is specified.
- finite_sequence_representation_available: no.
- selected_representation: universally quantified logical policy record (not an existential witness).
- justification: a fixed default would restrict the source interpretation, while this explicit record and proven recursion correspondence cover all source instances without strengthening any input bound.

## Shared-cost separation

- Reused directly: `cmc_uint8_buffer_nonnull` from the accepted `cmc_copy_bytes_migration_lib`; its source is unchanged and imported through legal Coq dependency wiring.
- New source spatial wrapper: `cm_uint8_buffer`, which retains the empty-list `emp` behavior and combines the reused pure condition with builtin UCharArray ownership when nonempty.
- New wrapper bridge: `cm_uint8_buffer_source`; this is current-case common proof content, not reused proof.
- New source/domain definitions and structural/lookup bridges remain in this case library. Generated case proof witnesses remain separate. No prior accepted case file was modified.
- The now-unused `cm_default_function` was removed after policy generalization.

The buffer equivalence proof had two local design-check failures (`H is already used`, then `No primitive equality found`); both were repaired by unfolding the standard assertion semantics and proving the pure equivalence. The final design check passed. No tool-class symexec failure occurred; all symexec failures above were ordinary annotation/parser feedback.

## Ordinary assertion semantic review

### cmc_members_size-cut-1

- location: cmc_members_size: nonnull descriptor-list branch (C line 205)
- purpose: function-call-boundary
- named_semantic_state: source representation and safety predicates
- upstream_paths: nonnull or constructor-tag test
- downstream_work: field reads and recursive helper calls
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: The original descriptor list is head :: tail. Exact field encodings, original safety constraints and tail ownership expose the recursive call inputs; the head contribution plus the tail result determines the original total, prefix or selected model.

### cmc_struct_size_at-cut-1

- location: cmc_struct_size_at: nonnull descriptor-list branch (C line 235)
- purpose: function-call-boundary
- named_semantic_state: source representation and safety predicates
- upstream_paths: nonnull or constructor-tag test
- downstream_work: field reads and recursive helper calls
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: The original descriptor list is head :: tail. Exact field encodings, original safety constraints and tail ownership expose the recursive call inputs; the head contribution plus the tail result determines the original total, prefix or selected model.

### cmc_global_array_at-cut-1

- location: cmc_global_array_at: nonnull descriptor-list branch (C line 284)
- purpose: function-call-boundary
- named_semantic_state: source representation and safety predicates
- upstream_paths: nonnull or constructor-tag test
- downstream_work: field reads and recursive helper calls
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: The original descriptor list is head :: tail. Exact field encodings, original safety constraints and tail ownership expose the recursive call inputs; the head contribution plus the tail result determines the original total, prefix or selected model.

### cmc_slot_array_at-cut-1

- location: cmc_slot_array_at: nonnull descriptor-list branch (C line 318)
- purpose: function-call-boundary
- named_semantic_state: source representation and safety predicates
- upstream_paths: nonnull or constructor-tag test
- downstream_work: field reads and recursive helper calls
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: The original descriptor list is head :: tail. Exact field encodings, original safety constraints and tail ownership expose the recursive call inputs; the head contribution plus the tail result determines the original total, prefix or selected model.

### cmc_slot_type_at-cut-1

- location: cmc_slot_type_at: nonnull descriptor-list branch (C line 350)
- purpose: function-call-boundary
- named_semantic_state: source representation and safety predicates
- upstream_paths: nonnull or constructor-tag test
- downstream_work: field reads and recursive helper calls
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: The original descriptor list is head :: tail. Exact field encodings, original safety constraints and tail ownership expose the recursive call inputs; the head contribution plus the tail result determines the original total, prefix or selected model.

### cmc_member_array_at-cut-1

- location: cmc_member_array_at: nonnull descriptor-list branch (C line 382)
- purpose: function-call-boundary
- named_semantic_state: source representation and safety predicates
- upstream_paths: nonnull or constructor-tag test
- downstream_work: field reads and recursive helper calls
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: The original descriptor list is head :: tail. Exact field encodings, original safety constraints and tail ownership expose the recursive call inputs; the head contribution plus the tail result determines the original total, prefix or selected model.

### cmc_slots_size-cut-1

- location: cmc_slots_size: nonnull descriptor-list branch (C line 433)
- purpose: function-call-boundary
- named_semantic_state: source representation and safety predicates
- upstream_paths: nonnull or constructor-tag test
- downstream_work: field reads and recursive helper calls
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: The original descriptor list is head :: tail. Exact field encodings, original safety constraints and tail ownership expose the recursive call inputs; the head contribution plus the tail result determines the original total, prefix or selected model.

### cmc_slots_prefix-cut-1

- location: cmc_slots_prefix: nonnull descriptor-list branch (C line 463)
- purpose: function-call-boundary
- named_semantic_state: source representation and safety predicates
- upstream_paths: nonnull or constructor-tag test
- downstream_work: field reads and recursive helper calls
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: The original descriptor list is head :: tail. Exact field encodings, original safety constraints and tail ownership expose the recursive call inputs; the head contribution plus the tail result determines the original total, prefix or selected model.

### cmc_members_prefix-cut-1

- location: cmc_members_prefix: nonnull descriptor-list branch (C line 499)
- purpose: function-call-boundary
- named_semantic_state: source representation and safety predicates
- upstream_paths: nonnull or constructor-tag test
- downstream_work: field reads and recursive helper calls
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: The original descriptor list is head :: tail. Exact field encodings, original safety constraints and tail ownership expose the recursive call inputs; the head contribution plus the tail result determines the original total, prefix or selected model.

### cmc_member_offset_at-cut-1

- location: cmc_member_offset_at: nonnull descriptor-list branch (C line 536)
- purpose: function-call-boundary
- named_semantic_state: source representation and safety predicates
- upstream_paths: nonnull or constructor-tag test
- downstream_work: field reads and recursive helper calls
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: The original descriptor list is head :: tail. Exact field encodings, original safety constraints and tail ownership expose the recursive call inputs; the head contribution plus the tail result determines the original total, prefix or selected model.

### cmc_struct_member_array_at-cut-1

- location: cmc_struct_member_array_at: nonnull descriptor-list branch (C line 574)
- purpose: function-call-boundary
- named_semantic_state: source representation and safety predicates
- upstream_paths: nonnull or constructor-tag test
- downstream_work: field reads and recursive helper calls
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: The original descriptor list is head :: tail. Exact field encodings, original safety constraints and tail ownership expose the recursive call inputs; the head contribution plus the tail result determines the original total, prefix or selected model.

### cmc_globals_size-cut-1

- location: cmc_globals_size: nonnull descriptor-list branch (C line 611)
- purpose: function-call-boundary
- named_semantic_state: source representation and safety predicates
- upstream_paths: nonnull or constructor-tag test
- downstream_work: field reads and recursive helper calls
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: The original descriptor list is head :: tail. Exact field encodings, original safety constraints and tail ownership expose the recursive call inputs; the head contribution plus the tail result determines the original total, prefix or selected model.

### cmc_globals_prefix-cut-1

- location: cmc_globals_prefix: nonnull descriptor-list branch (C line 643)
- purpose: function-call-boundary
- named_semantic_state: source representation and safety predicates
- upstream_paths: nonnull or constructor-tag test
- downstream_work: field reads and recursive helper calls
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: The original descriptor list is head :: tail. Exact field encodings, original safety constraints and tail ownership expose the recursive call inputs; the head contribution plus the tail result determines the original total, prefix or selected model.

### cmc_strings_size-cut-1

- location: cmc_strings_size: nonnull descriptor-list branch (C line 681)
- purpose: function-call-boundary
- named_semantic_state: source representation and safety predicates
- upstream_paths: nonnull or constructor-tag test
- downstream_work: field reads and recursive helper calls
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: The original descriptor list is head :: tail. Exact field encodings, original safety constraints and tail ownership expose the recursive call inputs; the head contribution plus the tail result determines the original total, prefix or selected model.

### cmc_strings_prefix-cut-1

- location: cmc_strings_prefix: nonnull descriptor-list branch (C line 713)
- purpose: function-call-boundary
- named_semantic_state: source representation and safety predicates
- upstream_paths: nonnull or constructor-tag test
- downstream_work: field reads and recursive helper calls
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: The original descriptor list is head :: tail. Exact field encodings, original safety constraints and tail ownership expose the recursive call inputs; the head contribution plus the tail result determines the original total, prefix or selected model.

### cm_args_length-cut-1

- location: cm_args_length: nonnull argument-list branch (C line 840)
- purpose: function-call-boundary
- named_semantic_state: source representation and safety predicates
- upstream_paths: nonnull or constructor-tag test
- downstream_work: field reads and recursive helper calls
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: The original argument list is head :: tail; its exact head expression and tail ownership are exposed, with the original safety conditions needed by recursive calls.

### cmc_args_tpair-cut-1

- location: cmc_args_tpair: nonnull argument-list branch (C line 866)
- purpose: function-call-boundary
- named_semantic_state: source representation and safety predicates
- upstream_paths: nonnull or constructor-tag test
- downstream_work: field reads and recursive helper calls
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: The original argument list is head :: tail; its exact head expression and tail ownership are exposed, with the original safety conditions needed by recursive calls.

### cm_expr_temps-cut-1

- location: cm_expr_temps: entry before reading the syntax tag (C line 900)
- purpose: function-call-boundary
- named_semantic_state: source representation and safety predicates
- upstream_paths: function entry
- downstream_work: field reads and recursive helper calls
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: The owned abstract syntax tree exposes its original tag, metadata and child pointers, while the payload keeps the exact recursive ownership.

### cm_expr_temps-cut-2

- location: cm_expr_temps: if (expr->kind == CMC_EXPR_ASSIGN) { child-call boundary (C line 920)
- purpose: function-call-boundary
- named_semantic_state: source representation and safety predicates
- upstream_paths: nonnull or constructor-tag test
- downstream_work: field reads and recursive helper calls
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: The tested tag determines the source syntax constructor; the original recursive safety predicate supplies child safety and arithmetic bounds. Every unvisited child and metadata field remains owned.

### cm_expr_temps-cut-3

- location: cm_expr_temps: if (expr->kind == CMC_EXPR_BINARY) { child-call boundary (C line 952)
- purpose: function-call-boundary
- named_semantic_state: source representation and safety predicates
- upstream_paths: nonnull or constructor-tag test
- downstream_work: field reads and recursive helper calls
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: The tested tag determines the source syntax constructor; the original recursive safety predicate supplies child safety and arithmetic bounds. Every unvisited child and metadata field remains owned.

### cm_expr_temps-cut-4

- location: cm_expr_temps: if (expr->kind == CMC_EXPR_UNARY) { child-call boundary (C line 990)
- purpose: function-call-boundary
- named_semantic_state: source representation and safety predicates
- upstream_paths: nonnull or constructor-tag test
- downstream_work: field reads and recursive helper calls
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: The tested tag determines the source syntax constructor; the original recursive safety predicate supplies child safety and arithmetic bounds. Every unvisited child and metadata field remains owned.

### cm_expr_temps-cut-5

- location: cm_expr_temps: if (expr->kind == CMC_EXPR_INDEX) { child-call boundary (C line 1026)
- purpose: function-call-boundary
- named_semantic_state: source representation and safety predicates
- upstream_paths: nonnull or constructor-tag test
- downstream_work: field reads and recursive helper calls
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: The tested tag determines the source syntax constructor; the original recursive safety predicate supplies child safety and arithmetic bounds. Every unvisited child and metadata field remains owned.

### cm_expr_temps-cut-6

- location: cm_expr_temps: if (expr->kind == CMC_EXPR_MEMBER) { child-call boundary (C line 1059)
- purpose: function-call-boundary
- named_semantic_state: source representation and safety predicates
- upstream_paths: nonnull or constructor-tag test
- downstream_work: field reads and recursive helper calls
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: The tested tag determines the source syntax constructor; the original recursive safety predicate supplies child safety and arithmetic bounds. Every unvisited child and metadata field remains owned.

### cm_expr_temps-cut-7

- location: cm_expr_temps: if (expr->kind == CMC_EXPR_CALL) { child-call boundary (C line 1089)
- purpose: function-call-boundary
- named_semantic_state: source representation and safety predicates
- upstream_paths: nonnull or constructor-tag test
- downstream_work: field reads and recursive helper calls
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: The tested tag determines the source syntax constructor; the original recursive safety predicate supplies child safety and arithmetic bounds. Every unvisited child and metadata field remains owned.

### cm_expr_temps-cut-8

- location: cm_expr_temps: if (expr->kind == CMC_EXPR_PUTC) { child-call boundary (C line 1117)
- purpose: function-call-boundary
- named_semantic_state: source representation and safety predicates
- upstream_paths: nonnull or constructor-tag test
- downstream_work: field reads and recursive helper calls
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: The tested tag determines the source syntax constructor; the original recursive safety predicate supplies child safety and arithmetic bounds. Every unvisited child and metadata field remains owned.

### cm_expr_temps-cut-9

- location: cm_expr_temps: if (expr->kind == CMC_EXPR_PUTI) { child-call boundary (C line 1146)
- purpose: function-call-boundary
- named_semantic_state: source representation and safety predicates
- upstream_paths: nonnull or constructor-tag test
- downstream_work: field reads and recursive helper calls
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: The tested tag determines the source syntax constructor; the original recursive safety predicate supplies child safety and arithmetic bounds. Every unvisited child and metadata field remains owned.

### cm_expr_temps-cut-10

- location: cm_expr_temps: if (expr->kind == CMC_EXPR_EXIT) { child-call boundary (C line 1175)
- purpose: function-call-boundary
- named_semantic_state: source representation and safety predicates
- upstream_paths: nonnull or constructor-tag test
- downstream_work: field reads and recursive helper calls
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: The tested tag determines the source syntax constructor; the original recursive safety predicate supplies child safety and arithmetic bounds. Every unvisited child and metadata field remains owned.

### cmc_stmt_temps-cut-1

- location: cmc_stmt_temps: entry before reading the syntax tag (C line 1232)
- purpose: function-call-boundary
- named_semantic_state: source representation and safety predicates
- upstream_paths: function entry
- downstream_work: field reads and recursive helper calls
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: The owned abstract syntax tree exposes its original tag, metadata and child pointers, while the payload keeps the exact recursive ownership.

### cmc_stmt_temps-cut-2

- location: cmc_stmt_temps: if (stmt->kind == CMC_STMT_EXPR) { child-call boundary (C line 1245)
- purpose: function-call-boundary
- named_semantic_state: source representation and safety predicates
- upstream_paths: nonnull or constructor-tag test
- downstream_work: field reads and recursive helper calls
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: The tested tag determines the source syntax constructor; the original recursive safety predicate supplies child safety and arithmetic bounds. Every unvisited child and metadata field remains owned.

### cmc_stmt_temps-cut-3

- location: cmc_stmt_temps: if (stmt->kind == CMC_STMT_INIT) { child-call boundary (C line 1264)
- purpose: function-call-boundary
- named_semantic_state: source representation and safety predicates
- upstream_paths: nonnull or constructor-tag test
- downstream_work: field reads and recursive helper calls
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: The tested tag determines the source syntax constructor; the original recursive safety predicate supplies child safety and arithmetic bounds. Every unvisited child and metadata field remains owned.

### cmc_stmt_temps-cut-4

- location: cmc_stmt_temps: if (stmt->kind == CMC_STMT_RETURN) { child-call boundary (C line 1283)
- purpose: function-call-boundary
- named_semantic_state: source representation and safety predicates
- upstream_paths: nonnull or constructor-tag test
- downstream_work: field reads and recursive helper calls
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: The tested tag determines the source syntax constructor; the original recursive safety predicate supplies child safety and arithmetic bounds. Every unvisited child and metadata field remains owned.

### cmc_stmt_temps-cut-5

- location: cmc_stmt_temps: if (stmt->kind == CMC_STMT_SEQ) { child-call boundary (C line 1302)
- purpose: function-call-boundary
- named_semantic_state: source representation and safety predicates
- upstream_paths: nonnull or constructor-tag test
- downstream_work: field reads and recursive helper calls
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: The tested tag determines the source syntax constructor; the original recursive safety predicate supplies child safety and arithmetic bounds. Every unvisited child and metadata field remains owned.

### cmc_stmt_temps-cut-6

- location: cmc_stmt_temps: if (stmt->kind == CMC_STMT_BLOCK) { child-call boundary (C line 1323)
- purpose: function-call-boundary
- named_semantic_state: source representation and safety predicates
- upstream_paths: nonnull or constructor-tag test
- downstream_work: field reads and recursive helper calls
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: The tested tag determines the source syntax constructor; the original recursive safety predicate supplies child safety and arithmetic bounds. Every unvisited child and metadata field remains owned.

### cmc_stmt_temps-cut-7

- location: cmc_stmt_temps: if (stmt->kind == CMC_STMT_IF) { child-call boundary (C line 1342)
- purpose: function-call-boundary
- named_semantic_state: source representation and safety predicates
- upstream_paths: nonnull or constructor-tag test
- downstream_work: field reads and recursive helper calls
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: The tested tag determines the source syntax constructor; the original recursive safety predicate supplies child safety and arithmetic bounds. Every unvisited child and metadata field remains owned.

### cmc_stmt_temps-cut-8

- location: cmc_stmt_temps: if (stmt->kind == CMC_STMT_WHILE) { child-call boundary (C line 1366)
- purpose: function-call-boundary
- named_semantic_state: source representation and safety predicates
- upstream_paths: nonnull or constructor-tag test
- downstream_work: field reads and recursive helper calls
- redundant_with_invariant_or_postcondition: no
- decision: keep
- rationale: The tested tag determines the source syntax constructor; the original recursive safety predicate supplies child safety and arithmetic bounds. Every unvisited child and metadata field remains owned.

## VC comparison

First attempt: vc_comparisons is empty, as required.

## Final owner-side checks

The final unchanged formal candidate passed the handoff's formal-case-lib-design, whole-file symexec, and formal-case-lib commands, each with real terminal exit 0 and controller status passed. All 39 runtime functions appear in the generated goal file. The library contains 108 declarations including 12 proved lemmas; no Parameter, Axiom, or Admitted occurs in the authored library. Generated pending manual proofs remain controller-owned and untouched. Controller acceptance and subsequent proof phases are separate.

The 35 ordinary assertions are all resource/recursive-call boundaries; there are no loops and no algorithm-mirroring internal predicates. The ready plan keeps the first-attempt VC comparison list empty.
