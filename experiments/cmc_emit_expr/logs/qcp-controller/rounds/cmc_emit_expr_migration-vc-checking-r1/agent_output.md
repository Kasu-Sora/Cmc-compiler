# Outcome

Blocked by a missing current-to-entry scalar bridge in five dispatcher annotations. These are definite whole-goal countermodels found during the priority no-split structural scan; no proving assignments were created. Formal source files were not modified.

## Structural Blocker Scan

- Status: blocked
- Top-level VCs scanned: 12
- No-split VCs checked first: 12
- Definite blockers: 5

The current manual contains 176 top-level witnesses and 333 generated split goals. All 12 no-split top-level witnesses were checked first. Seven representation-opening goals expose the resources already carried by `cm_expr_rep`; the other five assert entry equalities without premises. The scan stops at this definite blocker family under the early-countermodel rule. The remaining 164 top-level witnesses and all 333 split goals have not been assigned a proofability judgement.

## Annotation Comparison Review

There are no comparisons in this first proving round. The current manual names and the definitions imported from the current goal file were checked directly. The case library supplies constructor observations and imports the emitter model; it cannot establish equalities between unconstrained, universally quantified scalar variables.

## Proof-Mode Decisions

No proof modes are assigned: the structural blocker precedes split analysis and grouping. In each of the five failed VCs, both alternatives of the top-level disjunction have identical premises and conclusions, so choosing the other alternative does not repair the issue.

## Common Proof Patterns

No proof strategies or helpers were planned. The common countermodel is an unconstrained entry-state scalar: the antecedent mentions current `pc` and `temp` but never `pc_pre` or `temp_pre`; the consequent requires both equalities.

For a concrete instance of `proof_of_cm_emit_expr_which_implies_wit_2`, take `e = CMConstE 0 CMIntTy`, `lvalue = 0`, `pc = temp = 0`, `pc_pre = temp_pre = 1`, `done = tail = []`, and `capacity = 1`. The instruction fragment is a single PUSH of zero. Use a well-formed, disjoint emitter/output heap with nonzero output, ops, and imms addresses, emitter pc zero, empty initialized prefixes, and one uninitialized slot in each buffer. Choose the empty raw prefix in `cm_resolved_emitter_rep`; patching it yields `done = []`, and the capacity budget is satisfied. The antecedent and kind guard hold, while every existential `simple` fails the required `0 = 1` equalities. Both disjuncts therefore fail. For each other affected kind, use its corresponding finite simple expression fragment and a sufficiently large buffer; changing only either pre-state scalar leaves the antecedent unchanged and makes its required equality false.

## VC Deltas

All entries below use that same countermodel, with only the branch kind changing. Each is a top-level witness with no parent and no generated split goals.

| Witness | Kind / annotation location |
| --- | --- |
| `proof_of_cm_emit_expr_which_implies_wit_2` | CONST, `QCP_examples/QCP_demos_human/cmc_emit_expr_migration.c:1625–1626` |
| `proof_of_cm_emit_expr_which_implies_wit_4` | STRING, `QCP_examples/QCP_demos_human/cmc_emit_expr_migration.c:1634–1635` |
| `proof_of_cm_emit_expr_which_implies_wit_6` | VAR, `QCP_examples/QCP_demos_human/cmc_emit_expr_migration.c:1643–1644` |
| `proof_of_cm_emit_expr_which_implies_wit_19` | SIZEOF, `QCP_examples/QCP_demos_human/cmc_emit_expr_migration.c:1703–1704` |
| `proof_of_cm_emit_expr_which_implies_wit_21` | GETC, `QCP_examples/QCP_demos_human/cmc_emit_expr_migration.c:1712–1713` |

## Grouping Decisions

No group plan is delivered because these whole goals are false as generated. Load, helper ownership, and critical-path review are deferred until repaired VCs pass structural checking.

## Risks or Blockers

Repair the internal `which implies` premises to carry the needed `pc == pc@pre` and `temp == temp@pre` facts from the surrounding unchanged-variable context, or express the conversion so it does not introduce those facts without premises. Regenerate and check the establishing obligations. Preserve the original function/helper contracts and code model. Do not add an axiom or helper claiming arbitrary current/entry scalar equality.

Effort accounting for this owner attempt: coq-debug invocations 0, coq-check invocations 0, controller command failures 0, temporary manual edits 0. The blocker follows directly from the explicit generated statements and the satisfiable emitter-plan model; no compiler failure is claimed.
