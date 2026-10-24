# constant_value proof notes

- Completed the two assigned split proofs and their aggressive top-level dispatch proofs.
- Development invocations: 3. Debug invocations: 0. Exact invocations: 1.
- First development attempt used the unavailable `Z.mod_mod_divide`; replaced it with the division equation and elementary modular arithmetic.
- Second development attempt used the unavailable `Z.sub_mod`; replaced the modular rewrites with the available `Zminus_mod` and `Zmult_mod`.
- New public helpers: 0. New local helpers: 0. Copied frozen helpers: 0. Imports added: 0. The group library is unchanged.
- Existing `cm_type_encode_char_iff__typed_branches` supplies the character type equality; the non-character branch closes by constructor cases. The character branch first converts nonnegative remainder to modulo, then uses the fact that 256 divides 2^64 and modulo idempotence.
- No annotation changes or gaps.
