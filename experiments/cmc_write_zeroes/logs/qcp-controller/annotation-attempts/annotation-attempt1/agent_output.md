# Annotation design

The runtime signature and body are unchanged: the loop directly stores zero in `data[cursor + index]` and increments `index`. The contract has the original four arithmetic premises, exact initialized prefix, and separately owned uninitialized suffix. It adds neither a nonnull condition nor a positive-length condition, and permits `cursor = count = capacity = 0`.

One loop invariant records the parameter-to-entry bridges, `0 <= index <= count`, the original bounds, and the exact content `prefix ++ zeros(index)` with the residual uninitialized suffix. No ordinary Assert or new internal predicate is needed. Initialization reduces `zeros(0)` to `nil`; preservation appends one zero; exit substitutes `index = count`.

The specified previous byte case informed only the UCharArray segment interface. The required positive majority-element and negative algorithm-mirror examples were inspected for design discipline; no proof or generated artifact was copied.

## Reused mathematical interface and effort boundary

`Rocq/auxlibs/ListLib.v:819` already defines `zeros n := repeat 0 (Z.to_nat n)`. Existing Coq `List.repeat_cons`, `List.repeat_app`, list append associativity, and nonnegative `Z.to_nat` addition/successor laws provide the preservation bridge. The canonical case lib remains its controller-created import seed. Newly introduced public model definitions: **0**. Newly introduced common/helper lemmas in this annotation attempt: **0**.

The source `baseline/userlib/pure_lists.c:394–413` proves the zero and nonnegative successor laws of integer-count `ireplicate`; its append proof at lines 419–429 explicitly unfolds `IREPLICATE_DEF` to natural-count `REPLICATE` and uses `NUM_OF_INT_ADD`. Under the retained `0 <= count` and `0 <= index` premises, these characterize the same finite zero list as `repeat 0 (Z.to_nat n)` by induction. This is a semantic migration justification, not a machine-checked theorem relating the HOL and Rocq kernels. The parent is retrieving the built-in `IREPLICATE_DEF` for additional provenance.

## Local machine feedback

The exact handoff commands for formal-case-lib-design, symexec, and formal-case-lib each terminated with exit code 0 and controller status `passed`. No failed invocation occurred. The generated VCs expose the initialization, one-step list/endpoint normalization, and exit substitution obligations with all necessary arithmetic premises. Controller acceptance and later proof checking remain separate.

## Trusted automatic admissions

The generated automatic file contains six `Admitted` proofs: `proof_of_cmc_write_zeroes_safety_wit_1` through `_5`, and `proof_of_cmc_write_zeroes_partial_solve_wit_1`. These are QCP-generated trusted automatic obligations, not handwritten proofs. The generated manual initially contains three `Abort` split-goal placeholders and three `Admitted` wrapper placeholders; the later proof phase must replace its manual placeholders. The annotation owner has not edited generated files or added any handwritten `Axiom` or `Admitted`.

## VC comparison

This is the first attempt; `vc_comparisons` is empty as required.
