# Annotation delivery

Candidate 1 adds the exact previously verified byte-helper declaration contract, the char function contract, the existing word-library import, and one call `where` instantiation. The char contract owns the initialized prefix separately from the uninitialized suffix, requires `0 <= cursor`, `cursor + 1 <= capacity`, and `capacity <= 2147483647`, and appends `tower_u8(char_value)` to the prefix. No restriction is added to the signed long long input. The runtime cast, modulo expression, and single helper call are unchanged.

No new mathematical definition, lemma, case library, or internal predicate is needed. The source contract and byte/word reference cases informed this design; the algorithm-mirror negative example informed the decision to use the existing transparent mathematical low-byte definition directly. Ordinary Assert review: none. There are no loops or branch joins. The call `where` is the single semantic annotation key point.

The absent-library design check and canonical symexec both exited 0 and reported passed on their first invocation. Failed checks: none. Generated files were produced only by the supplied controller symexec command. The absent char-library path remains absent.

The generated goal and manual both contain `Require Import SimpleC.EE.QCP_demos_human.cmc_write_word_migration_lib`. The current pure witness has three split obligations: unsigned-cast/remainder byte equality, nonnegativity of `tower_u8`, and its strict upper bound 256. These follow from the existing byte-encoding lemma at k=0 (reducing the quotient by 1 and `tower_encode_byte` at 0), and the positive-modulus range of the existing `tower_u8` definition. No missing premise or resource is apparent. Proof construction and selected-dependency snapshot validation remain the later controller phases' responsibility.

## Dependency accounting

- Newly added import wiring for this case: `SimpleC.EE.QCP_demos_human.cmc_write_word_migration_lib`, via legal C `Import Coq` annotation. The accepted library source is reused unchanged.
- Used mathematical spec definition: existing `tower_u8`. Intended proof dependency: existing `tower_machine_rem_byte__byte_encoding` at k=0, with its existing `tower_machine_byte__byte_encoding` and `tower_mod_div_byte__byte_encoding` chain and `tower_encode_byte` reduction. These are reused, not newly authored; actual proof usage must be confirmed after proving.
- Modular runtime dependency: the exact `cmc_write_byte` contract from `cmc_write_byte_migration.c`. Its earlier implementation proof is not new char migration work. Existing trusted automatic results in that dependency are `proof_of_cmc_write_byte_return_wit_1` and `proof_of_cmc_write_byte_partial_solve_wit_1`.
- This char symexec generated three automatic results: safety, return, and partial-solve auxiliary. They were not edited by the annotation owner and should be accounted separately from the byte dependency and forthcoming manual proof.
- Source-side common helpers `cmc_unsigned_byte0_bridge` and `tower_u8_range` are also reused, not newly authored for this migration.

## VC comparison

None: first attempt, so `vc_comparisons` is empty.
