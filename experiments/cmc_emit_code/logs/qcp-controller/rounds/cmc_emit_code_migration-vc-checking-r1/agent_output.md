# VC checking decision

## Outcome
All three current top-level witnesses are provable; one coherent lightweight group covers them. No annotation changes or new helpers are required.

## Structural Blocker Scan
- Status: passed
- Top-level VCs scanned: 3
- No-split VCs checked first: 1
- Definite blockers: 0

The no-split entry obligation preserves exactly the program context, function list and emitter resources while exposing the context fields. The later transition has all field addresses and the program nonzero fact. The return retains the same program/emitter parameters and heap. No missing address, scalar equality or current-to-@pre bridge was found.

## Annotation Comparison Review
None were supplied in this first round. The PC-zero equality introduced at the second assertion is justified by the imported definitions: cm_function_pc is 11 plus cm_function_prefix, whose remaining-zero branch yields zero for both list constructors. It is not an assumed specification strengthening.

## Proof-Mode Decisions
The complete split-first pass judged all three generated splits provable, in declaration order: entail_wit_2_split_goal_1, entail_wit_2_split_goal_spatial, return_wit_1_split_goal_spatial. Therefore both parents use aggressive_pre_process without whole-goal provability analysis. After that pass, the sole no-split entail_wit_1 was judged provable as a whole and uses LLM_pre_process.

## Common Proof Patterns
- Context exposure/folding: unfold cm_program_context_rep, retain its nonzero fact and three pointer witnesses, and cancel corresponding fields and descriptor-list resources while framing function-list/emitter ownership.
- Code composition: unfold cm_model_code and use list append associativity to normalize the emitter pending/done list; every other resource remains identical.
- PC base: unfold cm_function_pc and analyze the function-list constructor; prefix at zero is zero, yielding 11 without well-formedness premises.

## VC Deltas
- entail_wit_1: context exposure, with right witnesses in tp/gp/sp order and all existing pure facts restored; the two whole-goal disjuncts are equivalent here, so choose the first.
- entail_wit_2: its pure split uses PC base; its spatial split combines context folding and pending-code composition.
- return_wit_1: its sole spatial split applies code composition to the completed prefix; no context opening is needed.

## Grouping Decisions
code_composition has 3 top-level witnesses, 3 aggressive splits, zero planned helpers, and difficulty 2. The LLM entry proof and aggressive transition/return proofs share a small resource and list-composition context. The load-and-coupling review found no heavy lemma or independent safety family to separate. The likely tail is the context-opening entry proof, but it requires only existential handling and cancellation; the transition and final-result work are both lightweight and the whole group remains below the preferred size and hard limit. Splitting off the one trivial final-result witness would add an unnecessary singleton. There is no new public helper or library proof workload and no cross-group dependency.

## Risks or Blockers
None identified. Actual proof scripts remain the responsibility of the assigned proving owner, and controller acceptance remains separate.

## Effort accounting
No controller checker or debug command was needed: the generated statements and imported definitions sufficed for this decision. checker_calls = 0; checker_failed = 0; debug_calls = 0; debug_failed = 0. No manual edits were made.
