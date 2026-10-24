# VC checking decision summary

## Outcome
All six manual top-level VCs have a provable selected target. Four generated spatial splits are provable; two no-split goals use whole-goal mode. No annotation repair is indicated.

## Structural Blocker Scan
- Status: passed
- Top-level VCs scanned: 6
- No-split VCs checked first: 2
- Definite blockers: 0

The array opening and emitter opening no-split goals were checked first. Their source resources supply the requested addresses and existential values. Current/pre variables coincide in the generated statements; no missing pointer or scalar bridge appears. All four return parents have matching head/tail or emitter fields. Capacity's upper bound is recoverable from the owned Int field, not an unsupported pure assumption.

## Annotation Comparison Review
No comparisons: this is the first proving round. The intermediate array cons equation is established by the array-opening VC; emitter raw-prefix witnesses and patch equality come from the existing resolved-emitter definition. Recursive return assumptions are the recursive contract, while the CALL pc equality comes from the total-PC helper contract.

## Proof-Mode Decisions
The full split-first pass classified, in declaration order, array return 1, array return 2, array return 3, and resolved return 1 spatial splits as provable. Thus all four parents use aggressive_pre_process, without whole-parent provability analysis. The subsequent whole-goal pass classified array entail 1 and resolved entail 1 (no split) as provable and selected LLM_pre_process.

## Common Proof Patterns
- A: decompose a nonempty paired opcode/immediate array into its two head cells and shifted paired tail; instantiate the model head and preserve program/function-list frames.
- B: reconstruct paired arrays from retained head cells and recursively patched tail, after simplifying the CALL test and using patch-map length preservation.
- C: open/rebuild emitter representation, retaining all fields and undefined capacity suffixes; convert between full arrays and zero-start segments and reconcile pc by map lengths.

## VC Deltas
- array entail 1: A, nonzero length excludes nil and supplies the positive head/tail length identities.
- array return 1 spatial: empty list case; patch nil is nil, so cancellation alone after list elimination.
- array return 2 spatial: B, CALL branch uses the returned total function PC as immediate.
- array return 3 spatial: B, non-CALL branch retains the original immediate.
- resolved entail 1: C opening, extract raw representation and its patch equality; recover the capacity upper bound from its Int cell.
- resolved return 1 spatial: C closing, patch equality and length preservation reconnect physical arrays to the resolved prefix.

## Grouping Decisions
Three independent groups, two top-level witnesses each: array_open (one aggressive split, one paired-array opening helper), array_close (two aggressive splits, one paired-array closing helper), emitter (one aggressive split, no planned helper). Estimated difficulty is 3 each. The two array representation helpers are public stable facts; neither group depends on its sibling's helper. Each worker can prove its own direction directly from the array library. No witness reuse analysis was performed.

Critical path: array_close has two structurally matching return splits sharing one reconstruction helper; splitting them would duplicate this local proof context. array_open couples the list shape boundary with its base case and one opening helper. emitter couples representation opening/closing, zero-start full/segment conversions, map-length normalization, and scalar-field bounds. Each has small persistent library context and at most two witnesses, so no lightweight safety family is bundled into a heavy tail group. No new substantial mathematical theorem or annotation comparison requires a priority high-risk group.

## Risks or Blockers
No definite blockers. Main proof engineering risk is array segment rebasing at offsets sizeof(INT) and sizeof(INT64), and extracting capacity bounds without discarding the Int field. These are existing separation/array semantics rather than extra contract assumptions.

## Effort Accounting
One static checker analysis pass; no manual edits, controller debug calls, checker command calls, or command failures were required. This is a provability and grouping decision, not a completed Rocq proof.

```json
{"analysis_passes":1,"checker_calls":0,"checker_failed":0,"debug_calls":0,"debug_failed":0}
```
