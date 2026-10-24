# Outcome

All 21 top-level VCs have a proof route. The plan contains 7 independent groups: 16 aggressive witnesses and 5 whole-goal witnesses. No formal source or manual was modified. This is a proofability and scheduling decision, not a checked proof result.

## Structural Blocker Scan

- Status: passed
- Top-level VCs scanned: 21
- No-split VCs checked first: 3
- Definite blockers: 0

The no-split reload/store `which_implies_wit_2` goals and call `which_implies_wit_1` were checked first. Their existential addresses come from their representation predicates. All 21 top-level antecedents preserve required addresses and relevant scalar identities. No missing current-to-@pre bridge or whole-goal countermodel was found.

## Annotation Comparison Review

No comparisons were supplied (first proving round). Current annotation facts are established by the listed implication VCs: list shape by list-representation elimination, head_count by the count-context postcondition, and call shape by kind=8 plus the existing cm_call_source_coverage lemma. Store arithmetic needs a new, unconditional mathematical code-length theorem; its absence as a proved helper is work for the isolated store_bounds group, not a missing premise.

# Proof-Mode Decisions

The complete split pass preceded whole-goal decisions. In manual declaration order, the binary split judgements are:

- `proof_of_cm_emit_args_reload_plan_return_wit_1`: spatial: provable.
- `proof_of_cm_emit_args_reload_plan_return_wit_2`: spatial: provable.
- `proof_of_cm_emit_args_reload_plan_which_implies_wit_1`: 1: unprovable.
- `proof_of_cm_emit_args_reload_plan_which_implies_wit_2`: no generated splits.
- `proof_of_cm_emit_args_reload_plan_which_implies_wit_3`: 1: provable, 2: provable, 3: provable.
- `proof_of_cm_emit_args_reload_plan_which_implies_wit_4`: spatial: provable.
- `proof_of_cm_emit_args_reload_plan_which_implies_wit_5`: spatial: provable.
- `proof_of_cm_emit_args_store_plan_return_wit_1`: spatial: provable.
- `proof_of_cm_emit_args_store_plan_return_wit_2`: spatial: provable.
- `proof_of_cm_emit_args_store_plan_which_implies_wit_1`: 1: unprovable.
- `proof_of_cm_emit_args_store_plan_which_implies_wit_2`: no generated splits.
- `proof_of_cm_emit_args_store_plan_which_implies_wit_3`: 1: provable, 2: provable, 3: provable, 4: provable.
- `proof_of_cm_emit_args_store_plan_which_implies_wit_4`: spatial: provable.
- `proof_of_cm_emit_args_store_plan_which_implies_wit_5`: 1: provable, 2: provable, 3: provable, 4: provable, 5: provable, 6: provable, 7: provable, 8: provable, 9: provable, 10: provable, 11: provable, 12: provable.
- `proof_of_cm_emit_args_store_plan_which_implies_wit_6`: spatial: provable.
- `proof_of_cm_emit_call_expr_return_wit_1`: spatial: provable.
- `proof_of_cm_emit_call_expr_return_wit_2`: spatial: provable.
- `proof_of_cm_emit_call_expr_which_implies_wit_1`: no generated splits.
- `proof_of_cm_emit_call_expr_which_implies_wit_2`: 1: provable, 2: provable, 3: provable, 4: provable, 5: provable, 6: provable, 7: provable, 8: provable, 9: provable, 10: provable, 11: provable.
- `proof_of_cm_emit_call_expr_which_implies_wit_3`: 1: provable, spatial: provable.
- `proof_of_cm_emit_call_expr_which_implies_wit_4`: spatial: provable.

Total: 45 generated splits; 43 provable, 2 unprovable. The two unprovable nil-list splits quantify arbitrary args with only arg_pre=0 and discard cm_arg_list_rep. Their whole goals retain that resource and are provable. Those two and the three no-split witnesses use LLM_pre_process. Every other witness uses aggressive_pre_process because all its splits are provable; no whole-goal proof strategy was analyzed for those witnesses.

# Common Proof Patterns

- **REP-NIL/OPEN/FOLD:** Preserve the representation heap, inspect list constructors, extract or instantiate existing field pointers, and retain the exact cells and recursive resources. A null pointer excludes a cons representation; a nonnull pointer excludes nil.
- **CODE:** Rewrite only the outer constructor equation or a proved call equation, normalize append associativity/identities, then cancel unchanged spatial resources. The model transition moves exactly the emitted code from pending suffix to done prefix.
- **PROJ:** Expose one constructor of a wellformedness/representability predicate and project the required head/tail fact; slots=nil contradicts nonempty argument wellformedness.
- **SLOT:** Use cons-length arithmetic and affine cm_temp_offset. The offset monotonicity argument cancels the common frame constant and needs no positivity of that constant.
- **STORE-PC:** The public pair-length theorem identifies head_count with head emitted-code length. One store equation gives total=head_count+5+tail length; the supplied start/end i32 bounds and list nonnegativity bound all intermediate pcs.
- **CALL-BOUND:** Call constructor projection supplies callee and argument facts. Call temporary depth equals argument count plus maximum depth; the count is Zlength and depth is nonnegative. Nonnegative wellformed slot sizes plus the offset upper bound control temp_limit.
- **CALL-REP:** kind=8 determines CMCallE. Unfold cm_expr_rep_node/payload, extract or instantiate 0,0,xargs, and preserve the seven node field cells and argument-list resource.

# VC Deltas

- `proof_of_cm_emit_args_reload_plan_return_wit_1`: CODE; reload(nil)=nil.
- `proof_of_cm_emit_args_reload_plan_return_wit_2`: CODE; reload cons; two emitted fragments.
- `proof_of_cm_emit_args_reload_plan_which_implies_wit_1`: REP-NIL; whole-goal heap retained.
- `proof_of_cm_emit_args_reload_plan_which_implies_wit_2`: REP-OPEN; existing ep,np existential pointers.
- `proof_of_cm_emit_args_reload_plan_which_implies_wit_3`: SLOT; offset, successor-plus-tail bound, successor i32 bound.
- `proof_of_cm_emit_args_reload_plan_which_implies_wit_4`: CODE; pending reload unfolded once.
- `proof_of_cm_emit_args_reload_plan_which_implies_wit_5`: REP-FOLD; rebuild arg cell with ep,np.
- `proof_of_cm_emit_args_store_plan_return_wit_1`: CODE; store(nil)=nil.
- `proof_of_cm_emit_args_store_plan_return_wit_2`: CODE; store cons; head/store/tail fragments.
- `proof_of_cm_emit_args_store_plan_which_implies_wit_1`: REP-NIL; whole-goal heap retained.
- `proof_of_cm_emit_args_store_plan_which_implies_wit_2`: REP-OPEN; existing ep,np existential pointers.
- `proof_of_cm_emit_args_store_plan_which_implies_wit_3`: PROJ; tail counts, tail wf, head counts, head wf.
- `proof_of_cm_emit_args_store_plan_which_implies_wit_4`: CODE; pending store unfolded; substitute head_count.
- `proof_of_cm_emit_args_store_plan_which_implies_wit_5`: STORE-PC/SLOT; 12 pure splits; max-depth projections additionally bound head and tail scratch needs.
- `proof_of_cm_emit_args_store_plan_which_implies_wit_6`: REP-FOLD; rebuild arg cell with ep,np.
- `proof_of_cm_emit_call_expr_return_wit_1`: CODE; call equation and three emitted fragments.
- `proof_of_cm_emit_call_expr_return_wit_2`: CODE; nonzero lvalue gives empty call code.
- `proof_of_cm_emit_call_expr_which_implies_wit_1`: CALL-REP; whole-goal node opening with existing args pointer.
- `proof_of_cm_emit_call_expr_which_implies_wit_2`: CALL-BOUND; 11 pure projections/bounds; 3 public helper declarations.
- `proof_of_cm_emit_call_expr_which_implies_wit_3`: CODE; store is a full-call prefix for endpoint bound; pending call decomposition.
- `proof_of_cm_emit_call_expr_which_implies_wit_4`: CALL-REP; node folding with 0,0,xargs.

The JSON strategies carry each formal split delta in declaration order. Pure goals have no existential heap witnesses. CODE targets preserve addresses/out/capacity and use equality of code lists; no operational property of the external emitter is silently added.

# Grouping Decisions

| Group | Witnesses | Aggressive splits | Difficulty | New helpers |
|---|---:|---:|---:|---:|
| store_bounds | 1 | 12 | 5 | 1 |
| call_bounds | 1 | 11 | 4 | 3 |
| reload_equations | 4 | 6 | 2 | 0 |
| reload_representation | 3 | 1 | 2 | 0 |
| store_representation | 4 | 5 | 2 | 0 |
| store_equations | 3 | 3 | 2 | 0 |
| call_equations | 5 | 5 | 3 | 0 |

The initial families were representation, emitted-list equations, store arithmetic, and call bounds. The second load/coupling review separated reload/store representation by program phase and kept the four store typing projections with the store representation context. Final-result code equalities are separate from both heavy safety families. No group exceeds six witnesses.

**Critical path:** store_bounds is a justified singleton: one parent owns 12 inseparable generated splits and the universal expression-code length family. Its library load includes all expression constructors, nested call lists, primitive code lengths and count definitions; its persistent context is the generalized pc/temp induction. It is placed first and difficulty 5. Splits cannot be distributed independently, and bundling final returns would delay otherwise independent equation proofs. The stable length theorem is explicitly public.

call_bounds is the other justified singleton: 11 splits share call-shape and temporary-budget context plus three small mathematical helper families (argument count/depth, slot-size nonnegativity, and argument-length safety). It is difficulty 4, separate from call equations/returns. Its helpers are public, and it needs no store_bounds theorem: its bounds use only temporary depths and slot sizes. The remaining groups use existing definitions and call-code equations; they require no sibling output. There is no permutation/mask helper family in this case.

# Risks or Blockers

No blocker. The universal pair-length proof is the substantial new mathematical work; the nested argument-list induction must generalize pc and scratch to handle recursive calls. The call-bound proof must use explicit slot wellformedness to infer nonnegative frame sizes; offset<=INT_MAX alone would not suffice. Both premise sets are present in the selected targets. The external cm_emit_expr implementation proof remains the explicit module dependency already documented by the C declaration; the mathematical pair-length helper does not discharge that dependency. No controller debug run was necessary because the generated goal definitions exposed the relevant assertions directly.
