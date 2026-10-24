# Byte encoding delivery notes

The assigned three top-level witnesses and fifteen split goals are proved. The arithmetic argument works for every integer word value, including negative values, without adding a signed-range premise. The top-level dispatch follows the generated spatial-first branch order and uses only the corresponding `Goal_apply` calls.

The library adds no definitions and three proved helpers, all used and compiled in the delivered proof dependency chain:

- `tower_mod_div_byte__byte_encoding`: planned public helper removing a multiple of the whole 64-bit modulus before byte extraction.
- `tower_machine_byte__byte_encoding`: planned public bridge from wrapped quotient and modulo to the source model's repeated floor divisions.
- `tower_machine_rem_byte__byte_encoding`: additional helper bridging the generated C remainder operation to the planned modulo helper.

The final library adds one official import, `From Coq Require Import Lia.`, used by the arithmetic proofs. The machine helpers express unsigned truncation as modulo powers of two, definitionally equal to `unsigned_last_nbits`; this avoids adding a project import. No definitions, assumptions, or specification changes were added.

Proof-development accounting: four unsuccessful development invocations, comprising one proof-completeness contract rejection of the initially assigned unfinished top-level spans, one import-contract rejection of `SimpleC.SL.IntLib`, and two Rocq compilation failures (a destruct-pattern lexical error and an incorrect spatial/pure branch order). Both compilation issues were repaired. There were no environment/tool execution failures. One separate debug invocation failed on a nonexistent standard-library lemma query; a later debug inspection established the branch order. These are proof-search costs, not missing annotation premises.
