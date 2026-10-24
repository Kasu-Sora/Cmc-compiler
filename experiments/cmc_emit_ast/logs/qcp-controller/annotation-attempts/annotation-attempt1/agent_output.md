# Annotation delivery

Both runtime functions have full source-equivalent contracts. All ten pure source facts occur in both pre/postconditions, and the complete program and function context resources are preserved. The direct emitter consumes capacity for precisely the binding fragment; the plan wrapper consumes that fragment from fragment++tail and preserves tail. No fid bounds or extra readiness/target premises were added.

The existing `cm_lookup_policy` and `cm_codegen_obligations` records are used unchanged. `cm_wf_program policy cg p` retains every existing conjunct. Source instantiation of HOL total lookup choices and the four concrete emitter predicates remains an inherited boundary; these implementation-verification contracts do not establish whole-compiler preservation or independently instantiate those source predicates.

The new library exports only the existing plan closure plus seven source model definitions: slots prefix, globals prefix, global address, param offset, local offset, push fragment, and binding fragment. Prefix recursion uses arbitrary Z indices and the exact zero-test/list-tail recurrence, including negative indices. Two new public prefix-match bridge lemmas correspond to source `cm_rep_member_prefix_matches` and `cm_rep_globals_prefix_matches`; they reuse existing size bridges. The seven source private `cm_ast_*` helpers remain case proof work rather than newly assumed model facts.

All five helper declarations and contracts were checked by whitespace-normalized comparison against their existing migration sources and match exactly. The ABI header and emitter layout are untouched. Runtime bodies retain the same tokens after stripping annotations; no earlier verified source or proof was edited. Generated files were created solely by the controller symexec command; manual proof content was read only.

# Annotation design

Two ordinary Assert boundaries are retained. No loops or internal pure state predicates are needed.

- location: direct function entry before scope dispatch
  purpose: function-call-boundary
  named_semantic_state: none (existing context representations)
  upstream_paths: one function entry
  downstream_work: three branches call layout and resolved-emitter helpers
  redundant_with_invariant_or_postcondition: no
  decision: keep
  rationale: expose both complete context headers and linked-list resources for exact existing callee contracts; derive slot nonnegativity from binding validity; keep every source fact and fragment budget.
- location: plan wrapper entry before direct call
  purpose: function-call-boundary
  named_semantic_state: cm_resolved_emitter_plan_rep (existing spec predicate)
  upstream_paths: one function entry
  downstream_work: direct emitter call followed by plan reconstruction
  redundant_with_invariant_or_postcondition: no
  decision: keep
  rationale: open the logical budget into direct fragment capacity and the remaining tail capacity while retaining both contexts and ten facts.

The source models describe contract-level addresses and instruction fragments, not an implementation execution mirror. No higher-order existential witness was introduced. Pointer witnesses simply expose preexisting context storage.

Relevant references: existing layout/resolved contracts and plan-wrapper annotations; source `cmc_lang.c`, `cmc_codegen.c`, `cmc_concrete_defs.c`, and the full original AST C/header. The skill's internal-predicate examples, sum positive example, and Kadane algorithm-mirror negative example informed keeping the model source-directed and assertions limited to genuine call boundaries.

# Actual owner checks

| Controller check | Invocations | Passed | Failed |
|---|---:|---:|---:|
| formal-case-lib-design | 1 | 1 | 0 |
| symexec | 1 | 1 | 0 |
| formal-case-lib (post-symexec) | 1 | 1 | 0 |

Each command reached terminal exit 0 and reported status passed. No repair causes or tool retries occurred. Generated obligations were inspected for slot nonnegativity, exact branch capacity, full context reconstruction, source-prefix equivalence, and plan budget preservation. There are nine top-level manual obligations; their proofs belong to the subsequent owner stage. Controller acceptance and clean replay remain separate.

# VC comparison

First attempt: no failed VCs were supplied; vc_comparisons is empty.

All writes stop with the terminal report for controller sealing.
