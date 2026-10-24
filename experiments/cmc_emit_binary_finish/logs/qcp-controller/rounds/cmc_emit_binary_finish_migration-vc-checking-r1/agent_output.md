# Outcome

All 40 manual top-level VCs have provable generated splits: 59/59 provable, 0 unprovable. All 40 modes are aggressive_pre_process; LLM_pre_process count is 0. The plan contains 11 independent groups. This is a VC analysis result, not a kernel proof result.

## Structural Blocker Scan

- Status: passed
- Top-level VCs scanned: 40
- No-split VCs checked first: 0
- Definite blockers: 0

The scan preceded split analysis. All spatial consequents use the same emitter/program/function/expression addresses and abstract arguments as their antecedents. Return prefix differences and transition tail differences are code-list transformations, not missing resources. Current-local transitions consistently use current parameters; returns consistently use pre-state parameters. There are no existential address obligations. Pure call preconditions retain the required type well-formedness and reference facts.

# Annotation Comparison Review

No comparisons were supplied (first proving round). The scale equalities originate in cm_pointer_scale_value returns, pointer tests in the guard and cmc_is_pointer_value contract, and preserved type facts in the entry/callee contracts. Every which-implies transition has both its establishing VC and the type-code-wf/test premises needed by the existing pointer-encoding lemma. No new assumption was inferred from an unproved comparison.

# Proof-Mode Decisions

The binary pass covered splits in manual declaration order before any strategy or grouping. Every split listed below was judged provable. Therefore each parent selects aggressive_pre_process without a whole-parent provability analysis after the structural scan.

| Parent (proof_of_ prefix) | Split suffixes, in declaration order | Binary judgement |
|---|---|---|
| `cm_pointer_scale_value_return_wit_1` | `_split_goal_1` | all provable |
| `cm_pointer_scale_value_partial_solve_wit_2_pure` | `_split_goal_1` | all provable |
| `cm_pointer_scale_value_partial_solve_wit_3_pure` | `_split_goal_1`, `_split_goal_2`, `_split_goal_3` | all provable |
| `cm_emit_binary_generic_fragment_return_wit_1` | `_split_goal_spatial` | all provable |
| `cm_emit_binary_generic_fragment_partial_solve_wit_3_pure` | `_split_goal_1`, `_split_goal_2` | all provable |
| `cm_emit_binary_generic_fragment_which_implies_wit_1` | `_split_goal_spatial` | all provable |
| `cm_emit_binary_finish_plan_return_wit_1` | `_split_goal_spatial` | all provable |
| `cm_emit_binary_finish_plan_return_wit_2` | `_split_goal_spatial` | all provable |
| `cm_emit_binary_finish_plan_return_wit_3` | `_split_goal_spatial` | all provable |
| `cm_emit_binary_finish_plan_return_wit_4` | `_split_goal_spatial` | all provable |
| `cm_emit_binary_finish_plan_return_wit_5` | `_split_goal_spatial` | all provable |
| `cm_emit_binary_finish_plan_return_wit_6` | `_split_goal_spatial` | all provable |
| `cm_emit_binary_finish_plan_return_wit_7` | `_split_goal_spatial` | all provable |
| `cm_emit_binary_finish_plan_partial_solve_wit_5_pure` | `_split_goal_1` | all provable |
| `cm_emit_binary_finish_plan_partial_solve_wit_8_pure` | `_split_goal_1`, `_split_goal_2` | all provable |
| `cm_emit_binary_finish_plan_partial_solve_wit_9_pure` | `_split_goal_1`, `_split_goal_2` | all provable |
| `cm_emit_binary_finish_plan_partial_solve_wit_10_pure` | `_split_goal_1`, `_split_goal_2` | all provable |
| `cm_emit_binary_finish_plan_partial_solve_wit_11_pure` | `_split_goal_1`, `_split_goal_2` | all provable |
| `cm_emit_binary_finish_plan_partial_solve_wit_12_pure` | `_split_goal_1` | all provable |
| `cm_emit_binary_finish_plan_partial_solve_wit_15_pure` | `_split_goal_1`, `_split_goal_2` | all provable |
| `cm_emit_binary_finish_plan_partial_solve_wit_16_pure` | `_split_goal_1`, `_split_goal_2` | all provable |
| `cm_emit_binary_finish_plan_partial_solve_wit_17_pure` | `_split_goal_1`, `_split_goal_2` | all provable |
| `cm_emit_binary_finish_plan_partial_solve_wit_18_pure` | `_split_goal_1`, `_split_goal_2` | all provable |
| `cm_emit_binary_finish_plan_partial_solve_wit_19_pure` | `_split_goal_1` | all provable |
| `cm_emit_binary_finish_plan_partial_solve_wit_22_pure` | `_split_goal_1`, `_split_goal_2` | all provable |
| `cm_emit_binary_finish_plan_partial_solve_wit_23_pure` | `_split_goal_1`, `_split_goal_2` | all provable |
| `cm_emit_binary_finish_plan_partial_solve_wit_24_pure` | `_split_goal_1`, `_split_goal_2` | all provable |
| `cm_emit_binary_finish_plan_partial_solve_wit_25_pure` | `_split_goal_1`, `_split_goal_2` | all provable |
| `cm_emit_binary_finish_plan_partial_solve_wit_26_pure` | `_split_goal_1` | all provable |
| `cm_emit_binary_finish_plan_partial_solve_wit_29_pure` | `_split_goal_1`, `_split_goal_2` | all provable |
| `cm_emit_binary_finish_plan_partial_solve_wit_30_pure` | `_split_goal_1`, `_split_goal_2` | all provable |
| `cm_emit_binary_finish_plan_partial_solve_wit_31_pure` | `_split_goal_1`, `_split_goal_2` | all provable |
| `cm_emit_binary_finish_plan_partial_solve_wit_32_pure` | `_split_goal_1`, `_split_goal_2` | all provable |
| `cm_emit_binary_finish_plan_which_implies_wit_1` | `_split_goal_spatial` | all provable |
| `cm_emit_binary_finish_plan_which_implies_wit_2` | `_split_goal_spatial` | all provable |
| `cm_emit_binary_finish_plan_which_implies_wit_3` | `_split_goal_spatial` | all provable |
| `cm_emit_binary_finish_plan_which_implies_wit_4` | `_split_goal_spatial` | all provable |
| `cm_emit_binary_finish_plan_which_implies_wit_5` | `_split_goal_spatial` | all provable |
| `cm_emit_binary_finish_plan_which_implies_wit_6` | `_split_goal_spatial` | all provable |
| `cm_emit_binary_finish_plan_which_implies_wit_7` | `_split_goal_spatial` | all provable |

# Common Proof Patterns

- **Scale:** the pure return equation is definitional after unfolding cm_pointer_scale.
- **Type:** eliminate nonpointer type constructors with cm_is_pointer; pointer encoding differs from pointee encoding by 1024, and well-formedness/references descend definitionally. The existing cm_type_encoding_bounds__expression_add_safety supplies nonnegative depth/base for the lower bound. Pure assertions need no heap information.
- **Classify:** the existing cm_pointer_encode__expression_add_safety bridges encoded zero/nonzero tests to cm_pointerb under the supplied cm_type_code_wf; constructor analysis gives cm_is_pointer.
- **Opcode:** evaluate tvm_opcode_code; the required equality and exclusion of 22 are closed facts under an irrelevant spatial frame.
- **Append:** use existing list associativity and reduction; cancel/reorder identical resources without opening their representations.
- **Transition:** use Classify’s existing encoding equation to reduce exactly the relevant Boolean guards of cm_binary_finish_code, substitute scale, and reassociate the residual list with tail. The source and target emitter states have the same done prefix and an equal remaining instruction list.
- **Return:** reduce the same model guards on the postcondition, normalize emitted singleton appends, and cancel the preserved program/function/two-expression frame and emitter plan. The tail is unchanged; done grows by exactly the selected instruction fragment.

No generated target introduces existential witnesses. No new or modified helper is expected: existing encoding/bounds lemmas and List.app_assoc already provide all shared mathematical facts. Helpers are therefore omitted from the plan.

# VC Deltas

Each entry below refers only to its generated split targets; the full exact split mapping and short executable strategy are in group_plan.json.
- `proof_of_cm_pointer_scale_value_return_wit_1`: Scale; returned size equals the definition of pointer scale.
- `proof_of_cm_pointer_scale_value_partial_solve_wit_2_pure`: Type; lower bound 1024 on pointer encoding.
- `proof_of_cm_pointer_scale_value_partial_solve_wit_3_pure`: Type; split 1 encoding equality, split 2 well-formedness, split 3 reference validity.
- `proof_of_cm_emit_binary_generic_fragment_return_wit_1`: Append; two appended singleton instructions, function frame.
- `proof_of_cm_emit_binary_generic_fragment_partial_solve_wit_3_pure`: Opcode; TVMSwapOp, split 1 equality and split 2 exclusion of 22.
- `proof_of_cm_emit_binary_generic_fragment_which_implies_wit_1`: Append; reduce a concrete two-instruction suffix.
- `proof_of_cm_emit_binary_finish_plan_return_wit_1`: Return; op = 8 and right pointer; load then PUSH(right scale), MUL, SWAP, ADD.
- `proof_of_cm_emit_binary_finish_plan_return_wit_2`: Return; op = 8, left pointer and right nonpointer; load then SWAP, PUSH(left scale), MUL, ADD.
- `proof_of_cm_emit_binary_finish_plan_return_wit_3`: Return; op = 9 and both pointers; load then SWAP, SUB, PUSH(left scale), DIV.
- `proof_of_cm_emit_binary_finish_plan_return_wit_4`: Return; op = 9, left pointer and right nonpointer; load then SWAP, PUSH(left scale), MUL, SUB.
- `proof_of_cm_emit_binary_finish_plan_return_wit_5`: Return; op = 8 and both nonpointers; load then SWAP and binary opcode.
- `proof_of_cm_emit_binary_finish_plan_return_wit_6`: Return; op = 9 and left nonpointer, with right type unrestricted; load then SWAP and binary opcode.
- `proof_of_cm_emit_binary_finish_plan_return_wit_7`: Return; op differs from 8 and 9, with both types unrestricted; load then SWAP and binary opcode.
- `proof_of_cm_emit_binary_finish_plan_partial_solve_wit_5_pure`: Classify; right nonzero test establishes cm_is_pointer.
- `proof_of_cm_emit_binary_finish_plan_partial_solve_wit_8_pure`: Opcode; TVMPushOp, split 1 equality and split 2 exclusion of 22.
- `proof_of_cm_emit_binary_finish_plan_partial_solve_wit_9_pure`: Opcode; TVMMulOp, split 1 equality and split 2 exclusion of 22.
- `proof_of_cm_emit_binary_finish_plan_partial_solve_wit_10_pure`: Opcode; TVMSwapOp, split 1 equality and split 2 exclusion of 22.
- `proof_of_cm_emit_binary_finish_plan_partial_solve_wit_11_pure`: Opcode; TVMAddOp, split 1 equality and split 2 exclusion of 22.
- `proof_of_cm_emit_binary_finish_plan_partial_solve_wit_12_pure`: Classify; left nonzero test establishes cm_is_pointer.
- `proof_of_cm_emit_binary_finish_plan_partial_solve_wit_15_pure`: Opcode; TVMSwapOp, split 1 equality and split 2 exclusion of 22.
- `proof_of_cm_emit_binary_finish_plan_partial_solve_wit_16_pure`: Opcode; TVMPushOp, split 1 equality and split 2 exclusion of 22.
- `proof_of_cm_emit_binary_finish_plan_partial_solve_wit_17_pure`: Opcode; TVMMulOp, split 1 equality and split 2 exclusion of 22.
- `proof_of_cm_emit_binary_finish_plan_partial_solve_wit_18_pure`: Opcode; TVMAddOp, split 1 equality and split 2 exclusion of 22.
- `proof_of_cm_emit_binary_finish_plan_partial_solve_wit_19_pure`: Classify; left nonzero test establishes cm_is_pointer.
- `proof_of_cm_emit_binary_finish_plan_partial_solve_wit_22_pure`: Opcode; TVMSwapOp, split 1 equality and split 2 exclusion of 22.
- `proof_of_cm_emit_binary_finish_plan_partial_solve_wit_23_pure`: Opcode; TVMSubOp, split 1 equality and split 2 exclusion of 22.
- `proof_of_cm_emit_binary_finish_plan_partial_solve_wit_24_pure`: Opcode; TVMPushOp, split 1 equality and split 2 exclusion of 22.
- `proof_of_cm_emit_binary_finish_plan_partial_solve_wit_25_pure`: Opcode; TVMDivOp, split 1 equality and split 2 exclusion of 22.
- `proof_of_cm_emit_binary_finish_plan_partial_solve_wit_26_pure`: Classify; left nonzero test establishes cm_is_pointer.
- `proof_of_cm_emit_binary_finish_plan_partial_solve_wit_29_pure`: Opcode; TVMSwapOp, split 1 equality and split 2 exclusion of 22.
- `proof_of_cm_emit_binary_finish_plan_partial_solve_wit_30_pure`: Opcode; TVMPushOp, split 1 equality and split 2 exclusion of 22.
- `proof_of_cm_emit_binary_finish_plan_partial_solve_wit_31_pure`: Opcode; TVMMulOp, split 1 equality and split 2 exclusion of 22.
- `proof_of_cm_emit_binary_finish_plan_partial_solve_wit_32_pure`: Opcode; TVMSubOp, split 1 equality and split 2 exclusion of 22.
- `proof_of_cm_emit_binary_finish_plan_which_implies_wit_1`: Transition; op = 8 and right pointer; load then PUSH(right scale), MUL, SWAP, ADD.
- `proof_of_cm_emit_binary_finish_plan_which_implies_wit_2`: Transition; op = 8, left pointer and right nonpointer; load then SWAP, PUSH(left scale), MUL, ADD.
- `proof_of_cm_emit_binary_finish_plan_which_implies_wit_3`: Transition; op = 9 and both pointers; load then SWAP, SUB, PUSH(left scale), DIV.
- `proof_of_cm_emit_binary_finish_plan_which_implies_wit_4`: Transition; op = 9, left pointer and right nonpointer; load then SWAP, PUSH(left scale), MUL, SUB.
- `proof_of_cm_emit_binary_finish_plan_which_implies_wit_5`: Transition; op = 8 and both nonpointers; load then SWAP and binary opcode.
- `proof_of_cm_emit_binary_finish_plan_which_implies_wit_6`: Transition; op = 9 and left nonpointer, with right type unrestricted; load then SWAP and binary opcode.
- `proof_of_cm_emit_binary_finish_plan_which_implies_wit_7`: Transition; op differs from 8 and 9, with both types unrestricted; load then SWAP and binary opcode.

# Grouping Decisions

Initial groups followed type reasoning, list normalization, branch model conversion and closed opcode facts. A second load review separated final-result work from transitions and pointer classification, and split constant opcode checks by program branch. All groups have 3–4 witnesses; no singleton or group above 6 needs an exception.

| Group | Top-level | Aggressive splits | New helpers | Difficulty |
|---|---:|---:|---:|---:|
| pointer-scale | 3 | 5 | 0 | 2 |
| pointer-classification | 4 | 4 | 0 | 2 |
| generic-fragment | 3 | 4 | 0 | 1 |
| pointer-results | 4 | 4 | 0 | 3 |
| generic-results | 3 | 3 | 0 | 2 |
| pointer-transitions | 4 | 4 | 0 | 3 |
| generic-transitions | 3 | 3 | 0 | 2 |
| right-add-opcodes | 4 | 8 | 0 | 1 |
| left-add-opcodes | 4 | 8 | 0 | 1 |
| pointer-difference-opcodes | 4 | 8 | 0 | 1 |
| pointer-offset-opcodes | 4 | 8 | 0 | 1 |

Likely tail groups are pointer-results and pointer-transitions: each has 4 spatial splits, 0 new helper families, the same imported model/encoding closure, and two pointer-test Boolean guards at most per branch. They are separate because neither needs the other’s proof output. Generic-results and generic-transitions each have 3 spatial splits and no helper work; they also remain independent. Pointer-scale has 5 splits with short constructor/arithmetic reasoning; pointer-classification has 4 single-pure splits. The four opcode groups have 8 splits each but only closed constructor reductions, so their larger split counts do not imply a mathematical critical path. All groups use one proof mode and one consistent program phase. There is no permutation, sum/length, mask-clear or other unowned cross-group fact to rediscover; list associativity and the encoding bridge already exist in imported libraries.

# Risks or Blockers

No annotation, specification, or dependency blocker found. The main implementation risk is controlling rewrite direction and Boolean simplification in the spatial groups; keeping the representation predicates opaque avoids unnecessary heap expansion. No main-root source or manual was modified.

# Effort Records

- coq-debug invocations: 0
- coq-debug failures: 0
- Temporary Show insertions: 0
- Top-level VCs: 40; generated splits: 59; aggressive modes: 40; LLM modes: 0; groups: 11.
- Declaration inspection and imported definitions sufficed; no debug process was needed.
