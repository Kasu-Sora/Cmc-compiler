# Annotation delivery

The function contract preserves the exact stated bounds and prefix/uninitialized-suffix ownership, with no word_value premise. The runtime tokens were left unchanged; only QCP annotations and a source-independent mathematical library were added.

## Model and dependency accounting

- New model definitions: tower_u8, tower_encode_byte, tower_word_bytes (three).
- tower_u8 uses explicit Z.modulo. tower_encode_byte directly translates the source's eight equality cases and repeated Z.div by positive 256, including the otherwise-zero branch. tower_word_bytes is the same ordered eight-element source list. There is no model defined only from runtime-wrapped bits, no algorithm interpreter, and no new axiom.
- New public lemmas / proofs in annotation phase: none. The runtime/source byte bridge and ordinary list/arithmetic facts remain actual generated proof obligations for the proof owners.
- Library imports: standard Coq ZArith and List only, with ListNotations and Z_scope. C imports the canonical case library, which is present in generated goal and manual imports.
- Reuse: the cmc_write_byte declaration contract is byte-for-byte identical to the contract in QCP_examples/QCP_demos_human/cmc_write_byte_migration.c (checked by extracting the complete With/Require/Ensure block). This is the modular dependency verified in run cmc_write_byte_migration-20261015151544, with the auto-trust limitation documented in the supplied byte REPORT.md. The helper body is not duplicated or reproved here.
- Builtin UCharArray.seg and UCharArray.undef_seg retain the source ownership split. Standard app/cons/nil represent list extension.
- References influencing design: source cmc_concrete_emit_word.c/.h and tower_base.c; exact verified byte case; annotation guide positive majority/internal-predicate examples and negative algorithm-mirror examples were inspected for design discipline.

## Generated semantics and proof boundary

The VCs expose word_value as an Int64 local and bits as UInt64 holding unsigned_last_nbits word_value 64. The definition in Rocq/SeparationLogic/IntLib.v is x mod 2^n (Z.modulo), so negative inputs wrap modulo 2^64. Byte casts similarly use unsigned_last_nbits _ 8. Runtime division is printed as ÷ (truncating division); runtime remainder % is Z.rem. These occur after the unsigned64 wrap and therefore operate on nonnegative numerators. The bridge obligations must connect them to the source model's Euclidean Z.div/Z.modulo without restricting word_value. CommonAssertion.v store_int64 supplies the signed64 machine interval; no added user premise supplies it.

The first full cut generates eight runtime/source equalities, including the seventh-byte bridge with an arbitrary mathematical word_value. Each callee application also checks byte range. The final spatial witness connects the eight singleton appends to tower_word_bytes. These obligations are not assumed by this delivery. The generated manual has 45 Abort leaves and 15 generated Admitted combination wrappers pending proving; the untouched generated auto has 37 Admitted trusted automatic witnesses. These are generated artifacts, not hand-added proof admissions.

## Checks and revisions

- Candidate 1: formal-case-lib-design passed. Symexec failed at the third call (original line 48): spatial prefix endpoint (cursor + 1) + 1 did not syntactically match cursor + 2. Classified as resource-shape/call-boundary normalization, not tool failure.
- Candidate 2: added six full call-boundary Asserts before calls at offsets 2 through 7. Design check passed. Symexec failed at b2 access (line 54) because the cut omitted live byte locals. Classified as local resource loss.
- Candidate 3: kept all eight byte locals using their mathematical digit equalities and retained bits through an existential value. Design check, symexec, and post-symexec formal-case-lib all passed with actual terminal exit 0 and status passed.
- Total owner checks: three design checks (all passed), three symexec checks (two annotation failures followed by one pass), one post-symexec library check (passed). Two formal-candidate revisions after the first candidate. No tool/infrastructure failures and no proof edits.

## Ordinary Assert semantic review

### Before byte call at cursor + 2

location: cmc_write_word before cmc_write_byte(..., cursor + 2, b2)
purpose: function-call-boundary
named_semantic_state: none (direct local-value bindings and builtin spatial predicates)
upstream_paths: one straight-line path after the preceding helper call
downstream_work: remaining helper applications require the normalized segment endpoint and the byte bindings
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: convert the helper's (cursor + 1) + 1 endpoint to cursor + 2, retain initialized prefix/uninitialized suffix and all live local stores; at offset 2 also expose all eight source digit equalities. No loop exists and no duplicated exit postcondition is asserted.

### Before byte call at cursor + 3

location: cmc_write_word before cmc_write_byte(..., cursor + 3, b3)
purpose: function-call-boundary
named_semantic_state: none (direct local-value bindings and builtin spatial predicates)
upstream_paths: one straight-line path after the preceding helper call
downstream_work: remaining helper applications require the normalized segment endpoint and the byte bindings
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: convert the helper's (cursor + 2) + 1 endpoint to cursor + 3, retain initialized prefix/uninitialized suffix and all live local stores; at offset 2 also expose all eight source digit equalities. No loop exists and no duplicated exit postcondition is asserted.

### Before byte call at cursor + 4

location: cmc_write_word before cmc_write_byte(..., cursor + 4, b4)
purpose: function-call-boundary
named_semantic_state: none (direct local-value bindings and builtin spatial predicates)
upstream_paths: one straight-line path after the preceding helper call
downstream_work: remaining helper applications require the normalized segment endpoint and the byte bindings
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: convert the helper's (cursor + 3) + 1 endpoint to cursor + 4, retain initialized prefix/uninitialized suffix and all live local stores; at offset 2 also expose all eight source digit equalities. No loop exists and no duplicated exit postcondition is asserted.

### Before byte call at cursor + 5

location: cmc_write_word before cmc_write_byte(..., cursor + 5, b5)
purpose: function-call-boundary
named_semantic_state: none (direct local-value bindings and builtin spatial predicates)
upstream_paths: one straight-line path after the preceding helper call
downstream_work: remaining helper applications require the normalized segment endpoint and the byte bindings
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: convert the helper's (cursor + 4) + 1 endpoint to cursor + 5, retain initialized prefix/uninitialized suffix and all live local stores; at offset 2 also expose all eight source digit equalities. No loop exists and no duplicated exit postcondition is asserted.

### Before byte call at cursor + 6

location: cmc_write_word before cmc_write_byte(..., cursor + 6, b6)
purpose: function-call-boundary
named_semantic_state: none (direct local-value bindings and builtin spatial predicates)
upstream_paths: one straight-line path after the preceding helper call
downstream_work: remaining helper applications require the normalized segment endpoint and the byte bindings
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: convert the helper's (cursor + 5) + 1 endpoint to cursor + 6, retain initialized prefix/uninitialized suffix and all live local stores; at offset 2 also expose all eight source digit equalities. No loop exists and no duplicated exit postcondition is asserted.

### Before byte call at cursor + 7

location: cmc_write_word before cmc_write_byte(..., cursor + 7, b7)
purpose: function-call-boundary
named_semantic_state: none (direct local-value bindings and builtin spatial predicates)
upstream_paths: one straight-line path after the preceding helper call
downstream_work: remaining helper applications require the normalized segment endpoint and the byte bindings
redundant_with_invariant_or_postcondition: no
decision: keep
rationale: convert the helper's (cursor + 6) + 1 endpoint to cursor + 7, retain initialized prefix/uninitialized suffix and all live local stores; at offset 2 also expose all eight source digit equalities. No loop exists and no duplicated exit postcondition is asserted.

## VC comparison

None: initial attempt, vc_comparisons is empty.
