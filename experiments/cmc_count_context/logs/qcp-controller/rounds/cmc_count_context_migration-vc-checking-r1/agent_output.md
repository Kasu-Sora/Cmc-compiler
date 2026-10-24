# Outcome

All 8 assigned top-level witnesses have a provable selected target. The plan has 3 independent groups, 4 LLM modes and 4 aggressive modes. No source or generated formal file was modified; no debug expansion was necessary.

## Structural Blocker Scan

- Status: passed
- Top-level VCs scanned: 8
- No-split VCs checked first: 4
- Definite blockers: 0

The four entail witnesses were scanned first, followed by the four returns. All current pointers have already been normalized to the same `*_pre` variables on both sides. Expression-node fields and payload retain their addresses; both context predicates contain all requested field/list resources and nonnull facts. The existential pointers can be taken from those predicates. No missing scalar equality, resource address, or current-to-`@pre` bridge was found.

# Annotation Comparison Review

There are no comparisons in this first round. The expression representation is connected to the field/payload shape by the imported `cm_expr_rep_node` equality. `cm_program_context_rep` and `cm_function_context_rep` explicitly contain the nonnull facts, five existential pointers and all fields/list resources required by the assertions. The count return premises originate in the declared count-function postconditions; the context opening witnesses establish the resources and nonnull facts retained across calls.

# Proof-Mode Decisions

The complete split-only judgement pass, in manual declaration order, was:

| Split goal | Judgement |
| --- | --- |
| `proof_of_cm_expr_type_code_context_return_wit_1_split_goal_spatial` | provable |
| `proof_of_cm_expr_lvalue_count_context_return_wit_1_split_goal_spatial` | provable |
| `proof_of_cm_expr_rvalue_count_context_return_wit_1_split_goal_spatial` | provable |
| `proof_of_cm_stmt_code_count_context_return_wit_1_split_goal_spatial` | provable |

After all four judgements, every return witness was assigned `aggressive_pre_process` because its sole split is provable; its whole goal was not assessed beyond the structural scan. Each of the four entail witnesses has no generated split; its whole disjunctive goal was then judged provable and assigned `LLM_pre_process`. All modes were fixed before strategy and grouping decisions.

# Common Proof Patterns

**E-open/E-close:** `cm_expr_rep_node` rewrites a recursive expression representation to `cm_expr_node` with an opaque payload. Unfolding the node exposes a nonnull fact, three pointers and seven cells. Opening transfers those witnesses to the reversed existential order of the assertion; closing uses the supplied pointers and nonnull hypothesis. The payload and scalar values remain unchanged. There is no recursive traversal or arithmetic lemma.

**C-open:** Choose either identical disjunct of the whole context-opening VC. Unfold both context representations on the left, extract their nonnull facts and pointer witnesses, instantiate the right existentials in `zl,zp,zt,zg,zs` order, and preserve the five pure preconditions. Reassociate/cancel the two sets of field/list resources while framing the AST representation.

**C-close:** For the spatial split only, unfold both right-hand context representations. Their witnesses are program `zs,zg,zt` and function `zp,zl`, with nonnull from `PreH12`/`PreH13`. Reorder and cancel all existing resources, preserving the opaque AST frame. Fixed pointers `functions_ptr`, `body`, and `next` and all type/model projections already agree. No array/list transformation, count arithmetic, or abstract-state transition is required.

# VC Deltas

| Top-level witness | Pattern and actual delta |
| --- | --- |
| `proof_of_cm_expr_type_code_context_entail_wit_1` | E-open; choose the right whole-goal disjunct, which has no output-cell frame. |
| `proof_of_cm_expr_type_code_context_return_wit_1` | E-close; selected spatial split has nonnull in `PreH9` and no output-cell frame. |
| `proof_of_cm_expr_lvalue_count_context_entail_wit_1` | C-open; expression frame and expression well-formedness/representability premises. |
| `proof_of_cm_expr_lvalue_count_context_return_wit_1` | C-close; expression frame; `ret_ty` occurs in the preserved context portion of the antecedent. |
| `proof_of_cm_expr_rvalue_count_context_entail_wit_1` | C-open; same resources and pure facts as lvalue opening. |
| `proof_of_cm_expr_rvalue_count_context_return_wit_1` | C-close; rvalue-count premises are unused by the selected spatial target. |
| `proof_of_cm_stmt_code_count_context_entail_wit_1` | C-open; statement frame and `loop_`-indexed well-formedness replace expression premises. |
| `proof_of_cm_stmt_code_count_context_return_wit_1` | C-close; statement frame; `ret_ty` precedes the statement resource in the antecedent, requiring only reordering. |

# Grouping Decisions

Initial grouping separated expression-node representation work from the six context wrappers. The load-and-coupling review split context opening from independent final context reconstruction:

| Group | Top-level count | Aggressive split count | New helpers | Difficulty |
| --- | ---: | ---: | ---: | ---: |
| expression-node | 2 | 1 | 0 | 1 |
| context-open | 3 | 0 | 0 | 1 |
| context-close | 3 | 3 | 0 | 2 |

The likely tail is `context-close`: three spatial splits each reorder 16 spatial conjuncts into two existing context definitions plus an AST frame. Its library load is two transparent definitions, its persistent context is only their pointer witnesses and nonnull facts, and its helper load is zero. Final reconstruction is already isolated from the independently provable opening work. The expression pair shares the same existing node equality and has only one small split; further division would create needless singleton groups. No group exceeds six witnesses or is a singleton. There are no new heavy mathematical facts, public-helper candidates, or sibling dependencies.

# Risks or Blockers

No annotation/specification/dependency blocker was identified. These are provability judgements and proof plans; controller acceptance and subsequent Rocq proof validation remain separate. Spatial automation may require explicit witness order and reassociation, but all required premises and resources are present.
