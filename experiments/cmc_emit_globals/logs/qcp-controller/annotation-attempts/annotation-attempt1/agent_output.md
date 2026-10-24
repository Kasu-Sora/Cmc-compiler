# Annotation design and semantic decisions

The source contract and complete inline proof were read from the baseline cmc_concrete_emit_globals.c; cmc_concrete_data_ready.c was read for the exact recursive predicate. Relevant positive references were the layout global-list opening and LLM sll ownership decompositions; the annotation-designing internal-predicate examples and algorithm-mirror negative example were also reviewed. No runtime interpreter or alternate byte model was introduced.

The public contract is the direct translation: preserve cm_rep_globals_safe and cm_data_globals_wf, restore the original list, extend the exact initialized prefix by cm_globals_bytes, retain the undefined suffix, and return cursor + cm_rep_globals_size. No nonnull-data condition or extra initialization/capacity assumption was added. The empty-list case remains admitted by the precondition. The entire existing cm_global_wf is reused, including valid pointer types and their initialized-value-zero restriction; structs themselves remain excluded by cm_scalar_type. There are no program/TVM obligation parameters.

The four helper declarations and contracts were copied directly from their verified C source declarations. Only these helper prototypes were added; cmc_emit_globals has one body, no forward declaration and no loops. Existing ABI definitions and runtime statements, including the signed long-long-to-int cast, remain unchanged. The cast proof obligation retains the derived representation-size interval [0,1048560], which lies inside signed int. No raw implementation proof from a helper case is imported.

The library adds one exact predicate, cm_data_globals_wf, and seven reusable lemmas: scalar representation/semantic leaf-size equality, global-size equality under full wf, counts map/seq word bytes versus tower_word_bytes for every Z (including negative Z), char and nonchar initialization-byte views, initialized exact-length bytes, and zero bytes. Existing counts, layout, copy-bytes and write-word libraries are reused. In particular, cm_global_init_bytes and cm_global_bytes remain immutable counts definitions. The zeroes proof library is unnecessary and is not imported. These seven public lemmas are new target public cost, even though some correspond to source private proof helpers.

No case-specific internal predicate is needed: the two stable states already have canonical head/tail, global byte-list and spatial segment descriptions. The only new predicate is the source public wf conjunction.

# Assert review

- location: nonnull branch, before descriptor reads and cmc_code_slot_size.
  purpose: function-call-boundary.
  named_semantic_state: cm_data_globals_wf and existing cm_rep_globals_safe.
  upstream_paths: only the nonnull path survives the early return.
  downstream_work: five descriptor reads, slot-size call, cast and three write alternatives.
  redundant_with_invariant_or_postcondition: no.
  decision: keep.
  rationale: expose one owned head and tail, original full predicates, derived head/tail size bounds, capacity and unchanged input byte prefix.

- location: after all three helper write paths, before recursive emission.
  purpose: path-join and function-call-boundary.
  named_semantic_state: exact cm_global_bytes structs head.
  upstream_paths: initialized char, initialized nonchar, no initializer.
  downstream_work: recursive tail emission and restoration of the complete list/postcondition.
  redundant_with_invariant_or_postcondition: no.
  decision: keep.
  rationale: normalize all three helper byte results to the same exact model prefix and size, preserving every live local and descriptor field.

# Repairs and checks

No substantive machine-check failure occurred. Before the first symbolic run, type and term Extern declarations were separated and recursive where was reduced to the stable structs parameter; head/tail/prefix witnesses are inferred from owned resources, avoiding out-of-scope existential names. The first successful library design check was followed by symexec and the formal-case-lib check. After the C interface cleanup, the complete required sequence was rerun with the same final formal bytes.

Generated obligations were inspected read-only: nine top-level manual witnesses cover head opening, three byte-path joins, both returns, and three helper precondition bridges. Existing bounds and complete wf are present in their premises. No proof manual, goal, auto or check file was edited by this owner; controller symexec generated them. Generated Admitted placeholders are not authored proofs and remain for controller-dispatched proving.

# VC comparison

None: this is the first attempt; vc_comparisons is empty.
