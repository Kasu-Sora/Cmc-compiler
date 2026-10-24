# Annotation result

The QCP function contract preserves the source semantics: logical parameters are `prefix : list Z` and `model_byte : Z`; the input bounds are exactly `0 <= cursor < capacity`, `byte = model_byte`, and `0 <= model_byte < 256`. The initialized prefix has exact contents `prefix`, separated from an uninitialized suffix. The output has exact contents `prefix ++ [model_byte]` on `[0,cursor+1)` and preserves the uninitialized suffix `[cursor+1,capacity)`. No full-array initialization, extra machine bound, pointer bound, or non-null premise was added. The runtime signature and sole statement `data[cursor] = byte;` are unchanged.

The standard `UCharArray.seg` and `UCharArray.undef_seg` are used directly. In `ArrayLib.v`, `StoreUCharAsElement` uses `store_uchar`/`undef_store_uchar` at `data + index * sizeof(UCHAR)`. `ArrayLibCore.v` defines `seg` using the exact-content array recursion and `undef_seg` using the uninitialized recursion. Thus these predicates express the source's initialized unsigned-byte prefix and uninitialized unsigned-byte suffix without defining a duplicate byte model. The source `tower_byte_value` is expanded directly as the identical mathematical range. No unsupported unsigned-byte feature or changed contract semantics was observed in this case. This is a translation between each system's native ownership semantics, not a cross-system metatheorem equating their memory models.

The one-statement function has no loop, call, branch join, or independent semantic cut. Consequently the plan has no internal key points or predicates; no ordinary Assert merely repeats the postcondition. Existing unsigned-byte array machinery supplies the open/store/close resource transformation.

## Checks and trust boundary

The three exact handoff commands terminated with exit code 0 and `status: passed`: formal-case-lib-design, symexec, and formal-case-lib. Controller acceptance and clean replay remain separate.

The generated manual contains no proof obligations. The generated auto file contains exactly two trusted admissions:

- `proof_of_cmc_write_byte_return_wit_1`: substitutes `byte_pre = model_byte` in the extended prefix while framing the remaining suffix.
- `proof_of_cmc_write_byte_partial_solve_wit_1`: exposes the writable uninitialized byte at `cursor` while retaining the prefix and the remaining uninitialized suffix.

Both are generated as `Proof. Admitted.` by the standard QCP workflow. The generated goal's `VC_Correct` module type declares the corresponding two Axioms as its interface. These are not annotation-authored axioms or admissions. This result therefore relies on QCP's existing trusted symbolic execution/automatic proof boundary; it is not a claim that the two auto obligations were independently discharged by Rocq proof scripts. No generated file was manually edited.

## Effort separation and references

- Case annotation: two unsigned-byte predicate declarations and one function contract; no body annotations.
- New common mathematical model: none; byte range is written directly.
- New common memory predicates or helper lemmas: none; existing UCharArray suffices.
- Case-lib changes: none; the controller-created seed remains unchanged.
- Manual case proof: none generated and none written by this owner.
- Design revisions: the first candidate passed all owner checks.

Read the full annotation-designing guides and internal-predicate positive/negative examples. Relevant array examples were `QCP_examples/QCP_demos_LLM/chars.c` and the `array_copy1`/`array_concat` portions of `array_cases.c`; they informed initialized-prefix/uninitialized-suffix predicate selection only. The unrelated reverse-direction arr_sum experiment was not used as a proof template. The source snapshot's `cmc_concrete_emit_bytes.c` and the unsigned-byte fill helper references in `cmc_rep.c` were inspected to preserve the source's logical parameters and ownership transition.

## VC comparison

First attempt: no previous failed VCs; `vc_comparisons` is empty.
