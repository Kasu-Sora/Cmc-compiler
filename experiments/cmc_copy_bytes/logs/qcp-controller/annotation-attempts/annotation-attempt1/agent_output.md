# Annotation delivery

The target contract preserves the two logical lists, all source bounds, source contents, destination prefix, appended copied bytes, and the uninitialized suffix. The runtime C token sequence was not changed: the zero-length return, trailing if semicolon, index comparison, byte local, store and increment remain.

## Model correspondence and cost categories

- Source `cm_uint8_buffer` (cmc_rep.c:961–965) is empty heap when `bytes=[]`, otherwise explicit non-null plus the initialized byte array. QCP's `UCharArray.full(p,0,[])` unfolds through `store_array`/`store_array_rec` to true equalities and `emp`, with no restriction on p. Thus `cmc_uint8_buffer_nonnull(p,bytes)` conjoined with `UCharArray.full(p,length,bytes)`, under `Zlength(bytes)=length`, has precisely those two branches. Empty bytes permit null or arbitrary source and own no source cells. Nonempty bytes explicitly require p != 0. No source/data inequality or positive-length precondition was added.
- New pure representation/spec definition: `cmc_uint8_buffer_nonnull (p : Z) (bytes : list Z) : Prop := bytes = [] \/ p <> 0.` This is two nonblank lines, excluding existing imports/seed. It exposes the pure side condition of the source representation; it is not a new heap model or internal state predicate. It is used in both Require and Ensure.
- New heap representations: none. New algorithm/model recursion: none. New internal predicates: none. New common helper lemmas: none. Case proofs authored by annotation owner: none.
- Reused facilities: UCharArray.full/seg/undef_seg, Zlength, sublist, app, and builtin array opening/closing strategies. The loop's precise copied prefix is `prefix ++ sublist 0 index bytes`; the builtin read correctly materializes byte as `Znth index bytes 0` in generated witnesses.
- New dependency interface: one Extern Coq entry for the pure predicate and one legal Import Coq of the canonical case lib. The generated goal and manual both contain that import. Case-lib design compilation passed with the new definition; the subsequent formal-case-lib check reused that compiled current artifact.
- Existing byte and zeroes migration C examples informed the UCharArray segment mapping; their old proofs or reports were not used as evidence for this case. The original C*/HOL contract and definitions were independently read. Correct majority-element and incorrect algorithm-mirror teaching examples were inspected for annotation design discipline.

## Key point review

One loop-state point maintains all parameter bridges, machine arithmetic bounds, the immutable full source, exact initialized destination prefix, and the remaining undef destination suffix. Initialization uses sublist(0,0)=[] and app_nil_r; preservation uses the existing sublist snoc identity and list associativity; exit uses index=length=Zlength(bytes) and full sublist. Empty return uses Zlength(bytes)=0 to obtain bytes=[]. The generated pure source non-null obligation follows from the new source predicate and nonzero length; reconstituting that predicate at the normal exit follows from source != 0.

Ordinary Assert: none. Branch-control annotations: none. No higher-order witness. The short prefix expression needs no extra named internal predicate. VC comparisons are empty because this is the initial attempt.

## Checks and failures

1. Initial formal-case-lib-design check passed (unchanged seed).
2. Initial symexec failed once: category `symbolic-execution`, kind `symexec-error`, message `pre at branch '<unspecified>' is not determined`, target C line 29:18. The nearest loop invariant used source/parameter @pre after an entry condition written as `(length == 0 || source != 0)`. QCP split that Require into multiple unnamed pre-states. This was an annotation representation failure, not a tool failure; generated roles were rolled back.
3. Repair replaced only that pure conditional with the semantically equivalent list-based named predicate and imported its canonical definition. It retains the exact empty/nonempty input domain and adds no heap obligation.
4. Revised formal-case-lib-design passed, revised symexec passed, and formal-case-lib passed. Every success had terminal exit 0 and controller JSON `status: passed`.

Total failed checks in this annotation attempt: 1 symexec annotation failure; 0 tool failures; 0 Coq failures. Two design checks, two symexec checks, and one post-symexec case-lib check were run. There are four top-level manual witnesses (entry, preservation, empty return, normal return), with six generated split goals; five safety and two partial-solve witnesses are automatically exported. Generated proof placeholders remain controller-generated and were not edited by this owner. Subsequent verification/proving and controller acceptance remain separate.
