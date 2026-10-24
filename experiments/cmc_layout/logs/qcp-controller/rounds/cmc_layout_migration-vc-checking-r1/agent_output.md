# Outcome
All 148 manual top-level witnesses are assigned without an annotation/specification/dependency blocker. This is a semantic checking plan, not a completed proof.

## Structural Blocker Scan
- Status: passed
- Top-level VCs scanned: 148
- No-split VCs checked first: 35
- Definite blockers: 0
All 35 no-split goals were checked first, followed by the remaining 113 top-level goals. Required entry addresses and scalar bridges occur in the current generated goals. List opening extracts addresses from existential resources; constructor opening preserves the original field addresses. No Show insertion or debug execution was needed.

## Annotation Comparison Review
No comparisons exist in this first round. Current cm_expr_rep_node, cm_stmt_rep_node and cm_expr_safe_call establish nested-recursion bridges. Kind guards establish constructor choice; safe predicates contain child facts demanded by assertions. Lookup policy remains universally quantified; no fid bound is introduced.

## Proof-Mode Decisions
The complete split pass found 238 provable and 18 unprovable splits out of 256. The failures belong to 17 null-list returns: cancellation removed the representation, so pointer=0 alone does not constrain the logical list. Nonnegative-total splits at null-prefix returns are still provable from safe. Only then were the 52 required whole goals judged (35 without splits and those 17 null returns); all are provable and use LLM_pre_process. The other 96 use aggressive_pre_process.
A countermodel to a failed pure split uses pointer=0 with a nonempty logical list of nonzero size/count/array/type/prefix; args depth uses one assignment expression with right depth 1. These do not satisfy the original representation at zero, so there is no whole-goal countermodel.
Complete split-pass decisions in declaration order follow. Parent names omit proof_of_; suffixes are relative to the parent. P=provable, N=unprovable.
| Parent | Split judgements | Mode |
|---|---|---|
| cm_max_return_wit_1 | split_goal_1=P | aggressive |
| cm_max_return_wit_2 | split_goal_1=P | aggressive |
| cmc_is_pointer_return_wit_1 | split_goal_1=P | aggressive |
| cmc_is_pointer_return_wit_2 | split_goal_1=P | aggressive |
| cmc_leaf_size_return_wit_1 | split_goal_1=P | aggressive |
| cmc_leaf_size_return_wit_2 | split_goal_1=P | aggressive |
| cmc_leaf_size_return_wit_3 | split_goal_1=P | aggressive |
| cmc_leaf_size_return_wit_4 | split_goal_1=P | aggressive |
| cmc_code_slot_size_return_wit_1 | split_goal_1=P | aggressive |
| cmc_code_slot_size_return_wit_2 | split_goal_1=P | aggressive |
| cmc_members_size_safety_wit_3 | split_goal_1=P, split_goal_2=P | aggressive |
| cmc_members_size_entail_wit_1 | none | LLM |
| cmc_members_size_return_wit_1 | split_goal_1=N | LLM |
| cmc_members_size_return_wit_2 | split_goal_1=P, split_goal_spatial=P | aggressive |
| cmc_struct_size_at_entail_wit_1 | none | LLM |
| cmc_struct_size_at_return_wit_1 | split_goal_1=N | LLM |
| cmc_struct_size_at_return_wit_2 | split_goal_1=P, split_goal_spatial=P | aggressive |
| cmc_struct_size_at_return_wit_3 | split_goal_1=P, split_goal_spatial=P | aggressive |
| cmc_nonzero_return_wit_1 | split_goal_1=P | aggressive |
| cmc_nonzero_return_wit_2 | split_goal_1=P | aggressive |
| cmc_global_array_at_entail_wit_1 | none | LLM |
| cmc_global_array_at_return_wit_1 | split_goal_1=N | LLM |
| cmc_global_array_at_return_wit_2 | split_goal_1=P, split_goal_spatial=P | aggressive |
| cmc_global_array_at_return_wit_3 | split_goal_1=P, split_goal_spatial=P | aggressive |
| cmc_slot_array_at_entail_wit_1 | none | LLM |
| cmc_slot_array_at_return_wit_1 | split_goal_1=N | LLM |
| cmc_slot_array_at_return_wit_2 | split_goal_1=P, split_goal_spatial=P | aggressive |
| cmc_slot_array_at_return_wit_3 | split_goal_1=P, split_goal_spatial=P | aggressive |
| cmc_slot_type_at_entail_wit_1 | none | LLM |
| cmc_slot_type_at_return_wit_1 | split_goal_1=N | LLM |
| cmc_slot_type_at_return_wit_2 | split_goal_1=P, split_goal_spatial=P | aggressive |
| cmc_slot_type_at_return_wit_3 | split_goal_1=P, split_goal_spatial=P | aggressive |
| cmc_member_array_at_entail_wit_1 | none | LLM |
| cmc_member_array_at_return_wit_1 | split_goal_1=N | LLM |
| cmc_member_array_at_return_wit_2 | split_goal_1=P, split_goal_spatial=P | aggressive |
| cmc_member_array_at_return_wit_3 | split_goal_1=P, split_goal_spatial=P | aggressive |
| cmc_type_size_at_return_wit_1 | split_goal_1=P | aggressive |
| cmc_type_size_at_return_wit_2 | split_goal_1=P | aggressive |
| cmc_type_size_at_return_wit_3 | split_goal_1=P | aggressive |
| cmc_type_size_at_return_wit_4 | split_goal_1=P | aggressive |
| cmc_slots_size_safety_wit_3 | split_goal_1=P, split_goal_2=P | aggressive |
| cmc_slots_size_entail_wit_1 | none | LLM |
| cmc_slots_size_return_wit_1 | split_goal_1=N | LLM |
| cmc_slots_size_return_wit_2 | split_goal_1=P, split_goal_2=P, split_goal_3=P, split_goal_spatial=P | aggressive |
| cmc_slots_prefix_safety_wit_7 | split_goal_1=P, split_goal_2=P | aggressive |
| cmc_slots_prefix_entail_wit_1 | none | LLM |
| cmc_slots_prefix_return_wit_1 | split_goal_1=P, split_goal_2=N | LLM |
| cmc_slots_prefix_return_wit_2 | split_goal_1=P, split_goal_2=P, split_goal_spatial=P | aggressive |
| cmc_slots_prefix_return_wit_3 | split_goal_1=P, split_goal_2=P, split_goal_3=P, split_goal_4=P, split_goal_spatial=P | aggressive |
| cmc_members_prefix_safety_wit_7 | split_goal_1=P, split_goal_2=P | aggressive |
| cmc_members_prefix_entail_wit_1 | none | LLM |
| cmc_members_prefix_return_wit_1 | split_goal_1=P, split_goal_2=N | LLM |
| cmc_members_prefix_return_wit_2 | split_goal_1=P, split_goal_2=P, split_goal_spatial=P | aggressive |
| cmc_members_prefix_return_wit_3 | split_goal_1=P, split_goal_2=P, split_goal_3=P, split_goal_4=P, split_goal_spatial=P | aggressive |
| cmc_member_offset_at_entail_wit_1 | none | LLM |
| cmc_member_offset_at_return_wit_1 | split_goal_1=N | LLM |
| cmc_member_offset_at_return_wit_2 | split_goal_1=P, split_goal_spatial=P | aggressive |
| cmc_member_offset_at_return_wit_3 | split_goal_1=P, split_goal_spatial=P | aggressive |
| cmc_struct_member_array_at_entail_wit_1 | none | LLM |
| cmc_struct_member_array_at_return_wit_1 | split_goal_1=N | LLM |
| cmc_struct_member_array_at_return_wit_2 | split_goal_1=P, split_goal_spatial=P | aggressive |
| cmc_struct_member_array_at_return_wit_3 | split_goal_1=P, split_goal_spatial=P | aggressive |
| cmc_globals_size_safety_wit_3 | split_goal_1=P, split_goal_2=P | aggressive |
| cmc_globals_size_entail_wit_1 | none | LLM |
| cmc_globals_size_return_wit_1 | split_goal_1=N | LLM |
| cmc_globals_size_return_wit_2 | split_goal_1=P, split_goal_2=P, split_goal_3=P, split_goal_spatial=P | aggressive |
| cmc_globals_prefix_safety_wit_7 | split_goal_1=P, split_goal_2=P | aggressive |
| cmc_globals_prefix_entail_wit_1 | none | LLM |
| cmc_globals_prefix_return_wit_1 | split_goal_1=P, split_goal_2=N | LLM |
| cmc_globals_prefix_return_wit_2 | split_goal_1=P, split_goal_2=P, split_goal_spatial=P | aggressive |
| cmc_globals_prefix_return_wit_3 | split_goal_1=P, split_goal_2=P, split_goal_3=P, split_goal_4=P, split_goal_spatial=P | aggressive |
| cmc_strings_size_entail_wit_1 | none | LLM |
| cmc_strings_size_return_wit_1 | split_goal_1=N | LLM |
| cmc_strings_size_return_wit_2 | split_goal_1=P, split_goal_2=P, split_goal_3=P, split_goal_spatial=P | aggressive |
| cmc_strings_prefix_entail_wit_1 | none | LLM |
| cmc_strings_prefix_return_wit_1 | split_goal_1=P, split_goal_2=N | LLM |
| cmc_strings_prefix_return_wit_2 | split_goal_1=P, split_goal_2=P, split_goal_spatial=P | aggressive |
| cmc_strings_prefix_return_wit_3 | split_goal_1=P, split_goal_2=P, split_goal_3=P, split_goal_4=P, split_goal_spatial=P | aggressive |
| cmc_global_address_return_wit_1 | split_goal_1=P | aggressive |
| cmc_string_address_return_wit_1 | split_goal_1=P | aggressive |
| cmc_binding_array_value_return_wit_1 | split_goal_1=P | aggressive |
| cmc_binding_array_value_return_wit_2 | split_goal_1=P | aggressive |
| cmc_binding_array_value_return_wit_3 | split_goal_1=P | aggressive |
| cmc_member_array_safety_wit_1 | split_goal_1=P, split_goal_2=P | aggressive |
| cmc_member_array_return_wit_1 | split_goal_1=P | aggressive |
| cm_args_length_safety_wit_3 | split_goal_1=P, split_goal_2=P | aggressive |
| cm_args_length_entail_wit_1 | none | LLM |
| cm_args_length_return_wit_1 | split_goal_1=N | LLM |
| cm_args_length_return_wit_2 | split_goal_1=P, split_goal_spatial=P | aggressive |
| cmc_args_tpair_safety_wit_4 | split_goal_1=P, split_goal_2=P | aggressive |
| cmc_args_tpair_entail_wit_1 | none | LLM |
| cmc_args_tpair_return_wit_1 | split_goal_1=N, split_goal_2=N | LLM |
| cmc_args_tpair_return_wit_2 | split_goal_1=P, split_goal_2=P, split_goal_spatial=P | aggressive |
| cm_expr_temps_safety_wit_4 | split_goal_1=P, split_goal_2=P | aggressive |
| cm_expr_temps_safety_wit_9 | split_goal_1=P, split_goal_2=P | aggressive |
| cm_expr_temps_safety_wit_15 | split_goal_1=P, split_goal_2=P | aggressive |
| cm_expr_temps_safety_wit_19 | split_goal_1=P, split_goal_2=P | aggressive |
| cm_expr_temps_entail_wit_1 | none | LLM |
| cm_expr_temps_entail_wit_2 | none | LLM |
| cm_expr_temps_entail_wit_3 | none | LLM |
| cm_expr_temps_entail_wit_4 | none | LLM |
| cm_expr_temps_entail_wit_5 | none | LLM |
| cm_expr_temps_entail_wit_6 | none | LLM |
| cm_expr_temps_entail_wit_7 | none | LLM |
| cm_expr_temps_entail_wit_8 | none | LLM |
| cm_expr_temps_entail_wit_9 | none | LLM |
| cm_expr_temps_entail_wit_10 | none | LLM |
| cm_expr_temps_return_wit_1 | split_goal_1=P, split_goal_2=P, split_goal_spatial=P | aggressive |
| cm_expr_temps_return_wit_2 | split_goal_1=P, split_goal_2=P, split_goal_spatial=P | aggressive |
| cm_expr_temps_return_wit_3 | split_goal_1=P, split_goal_2=P, split_goal_spatial=P | aggressive |
| cm_expr_temps_return_wit_4 | split_goal_1=P, split_goal_2=P, split_goal_spatial=P | aggressive |
| cm_expr_temps_return_wit_5 | split_goal_1=P, split_goal_2=P, split_goal_spatial=P | aggressive |
| cm_expr_temps_return_wit_6 | split_goal_1=P, split_goal_2=P, split_goal_spatial=P | aggressive |
| cm_expr_temps_return_wit_7 | split_goal_1=P, split_goal_2=P, split_goal_spatial=P | aggressive |
| cm_expr_temps_return_wit_8 | split_goal_1=P, split_goal_2=P, split_goal_spatial=P | aggressive |
| cm_expr_temps_return_wit_9 | split_goal_1=P, split_goal_2=P, split_goal_spatial=P | aggressive |
| cm_expr_temps_return_wit_10 | split_goal_1=P, split_goal_2=P, split_goal_spatial=P | aggressive |
| cm_expr_temps_return_wit_11 | split_goal_1=P, split_goal_2=P, split_goal_spatial=P | aggressive |
| cm_expr_temps_return_wit_12 | split_goal_1=P, split_goal_2=P, split_goal_spatial=P | aggressive |
| cm_expr_temps_return_wit_13 | split_goal_1=P, split_goal_2=P, split_goal_spatial=P | aggressive |
| cm_expr_temps_return_wit_14 | split_goal_1=P, split_goal_2=P, split_goal_spatial=P | aggressive |
| cm_expr_temps_return_wit_15 | split_goal_1=P, split_goal_2=P, split_goal_spatial=P | aggressive |
| cm_expr_temps_return_wit_16 | split_goal_1=P, split_goal_2=P, split_goal_spatial=P | aggressive |
| cm_expr_temps_return_wit_17 | split_goal_1=P, split_goal_2=P, split_goal_spatial=P | aggressive |
| cm_expr_temps_return_wit_18 | split_goal_1=P, split_goal_2=P, split_goal_spatial=P | aggressive |
| cm_expr_temps_return_wit_19 | split_goal_1=P, split_goal_2=P, split_goal_spatial=P | aggressive |
| cmc_stmt_temps_entail_wit_1 | none | LLM |
| cmc_stmt_temps_entail_wit_2 | none | LLM |
| cmc_stmt_temps_entail_wit_3 | none | LLM |
| cmc_stmt_temps_entail_wit_4 | none | LLM |
| cmc_stmt_temps_entail_wit_5 | none | LLM |
| cmc_stmt_temps_entail_wit_6 | none | LLM |
| cmc_stmt_temps_entail_wit_7 | none | LLM |
| cmc_stmt_temps_entail_wit_8 | none | LLM |
| cmc_stmt_temps_return_wit_1 | split_goal_1=P, split_goal_2=P, split_goal_3=P, split_goal_spatial=P | aggressive |
| cmc_stmt_temps_return_wit_2 | split_goal_1=P, split_goal_2=P, split_goal_3=P, split_goal_spatial=P | aggressive |
| cmc_stmt_temps_return_wit_3 | split_goal_1=P, split_goal_2=P, split_goal_3=P, split_goal_spatial=P | aggressive |
| cmc_stmt_temps_return_wit_4 | split_goal_1=P, split_goal_2=P, split_goal_3=P, split_goal_spatial=P | aggressive |
| cmc_stmt_temps_return_wit_5 | split_goal_1=P, split_goal_2=P, split_goal_3=P, split_goal_spatial=P | aggressive |
| cmc_stmt_temps_return_wit_6 | split_goal_1=P, split_goal_2=P, split_goal_3=P, split_goal_spatial=P | aggressive |
| cmc_stmt_temps_return_wit_7 | split_goal_1=P, split_goal_2=P, split_goal_3=P, split_goal_spatial=P | aggressive |
| cmc_stmt_temps_return_wit_8 | split_goal_1=P, split_goal_2=P, split_goal_3=P, split_goal_spatial=P | aggressive |
| cmc_stmt_temps_return_wit_9 | split_goal_1=P, split_goal_2=P, split_goal_3=P, split_goal_spatial=P | aggressive |
| cmc_stmt_temps_return_wit_10 | split_goal_1=P, split_goal_2=P, split_goal_3=P, split_goal_spatial=P | aggressive |
| cmc_stmt_temps_return_wit_11 | split_goal_1=P, split_goal_2=P, split_goal_3=P, split_goal_spatial=P | aggressive |
| cmc_stmt_temps_return_wit_12 | split_goal_1=P, split_goal_2=P, split_goal_3=P, split_goal_spatial=P | aggressive |
| cm_normalize_count_return_wit_1 | split_goal_1=P | aggressive |
| cm_normalize_count_return_wit_2 | split_goal_1=P | aggressive |

## Common Proof Patterns
- **BOOL**: Unfold the indicated boolean/model definition, substitute branch and returned-value equalities, resolve Z.eqb/Z.leb with the guard, and close by reflexivity or lia. No spatial or existential work remains.
- **NULL**: Choose the whole-goal disjunct and destruct the represented list. Its cons case contradicts the representation nonnull fact at the known zero address. In the nil case simplify the model, retain safety/guard facts, and cancel the original representation and any output cells. This recovers the spatial information discarded by pure splitting.
- **OPEN-LIST**: Choose the whole-goal disjunct and destruct the represented list. Nil contradicts the nonzero branch guard. Unfold one cons representation, extract its next and nested-payload address witnesses, instantiate head/tail and those addresses, project child safety from parent safety, then reorder/cancel identical fields and tail. Frame output cells and nested member/expression/buffer resources.
- **FOLD-LIST**: Substitute the cons equality, unfold one representation layer, establish nonnull from the branch premise, instantiate the existing nextp and memberp/bytesp/ep as applicable, and cancel the fields, nested resource and tail. No resource/address is synthesized.
- **LIST-MATH**: Use the supplied cons equality and recursive-result equation; unfold one model equation and its head-size abbreviation. Resolve the zero/nonzero index test with its guard. For bounds project head/tail nonnegativity and total upper bound from parent safe, combine with recursive prefix <= tail total, and use lia. The antecedent heap is framed.
- **SAFETY**: Use the standard pure entailment rule on the framed heap. Substitute result/model and constructor equalities; unfold the relevant safe predicate to obtain summand bounds. Use parent-total bounds or strict child bounds, expand machine limits and close by lia. For modulo use Z.mod_pos_bound with divisor 1024.
- **OPEN-EXPR**: Choose the whole-goal disjunct. Entry uses cm_expr_rep_node then cm_expr_node to expose pa,pb,pargs while framing output cells. Branches destruct e and use cm_rep_expr_kind to eliminate other constructors, instantiate its actual children/type/op/id/args and existing pointers, unfold cm_expr_payload and project child safety from cm_rep_expr_temps_safe (call uses cm_expr_safe_call); cancel unchanged fields and output resources.
- **EXPR-MATH**: Substitute the constructor equality, or destruct e under the kind guard; unfold cm_expr_tpair and its projection. Reduce cm_rep_expr_op and resolve its eqb tests using branch premises. Rewrite the supplied cm_imax result; call uses cm_expr_tpair_call/cm_args_temps. The excluded-all-tags route is contradictory. Heap resources are only framed.
- **FOLD-EXPR**: Rewrite cm_expr_rep_node, unfold cm_expr_node, use expr_pre nonzero, and instantiate pa,pb,pargs. Substitute the constructor and unfold cm_expr_payload, whose child resources/null-pointer facts are precisely present. Reorder/cancel seven fields and payload. Leaf routes retain their existing payload; impossible-kind routes close by constructor contradiction.
- **OPEN-STMT**: Choose the whole-goal disjunct. Entry uses cm_stmt_rep_node to expose pe,pa,pb. Branches destruct s under its kind guard; unfold cm_stmt_payload and cm_rep_stmt_temps_safe/cm_rep_stmt_children_safe, instantiate actual children and current pointer witnesses, and cancel five fields together with the extracted child resources and safe projections.
- **STMT-MATH**: Bounds project 0 <= cm_stemps s <= 2147483647 from cm_rep_stmt_temps_safe and expand INT_MAX. Equality substitutes the constructor (or identifies it by kind), unfolds one cm_stemps equation and rewrites recursive-return/cm_imax equations. Excluded-all-tags is contradictory. Heap is framed.
- **FOLD-STMT**: Rewrite cm_stmt_rep_node and unfold cm_stmt_node. Instantiate pe,pa,pb, using stmt_pre nonzero. Substitute the constructor, rebuild cm_stmt_payload with its existing zero/nonzero facts and children, then cancel five fields and payload. Inert branches already contain the payload.
- **LOOKUP**: Binding guards select global/local/default code; cm_binding_valid supplies the corresponding slot bound, and f equals the policy-selected function with no fid restriction. For member lookup destruct base under cm_member_valid to obtain CMPtrTy (CMStructTy sid); encoding/well-formedness gives ((encode-1024) mod 1024)-2=sid and member_valid gives both list bounds. Use the owner public nth helpers and rewrite the recursive return.
- **ADDRESS**: Unfold cm_rep_global_address/cm_rep_string_address and substitute the recursive prefix/total result equations to obtain the addition equality. The split contains no spatial transformation.

## VC Deltas
Names omit proof_of_. The plan records exact parent-specific split targets.
- `cm_max_return_wit_1`: BOOL; (b_pre = (cm_imax (a_pre) (b_pre))).
- `cm_max_return_wit_2`: BOOL; (a_pre = (cm_imax (a_pre) (b_pre))).
- `cmc_is_pointer_return_wit_1`: BOOL; (1 = (cm_rep_is_pointer_code (ty_pre))).
- `cmc_is_pointer_return_wit_2`: BOOL; (0 = (cm_rep_is_pointer_code (ty_pre))).
- `cmc_leaf_size_return_wit_1`: BOOL; (8 = (cm_rep_leaf_size (ty_pre))).
- `cmc_leaf_size_return_wit_2`: BOOL; (8 = (cm_rep_leaf_size (0))).
- `cmc_leaf_size_return_wit_3`: BOOL; (1 = (cm_rep_leaf_size (1))).
- `cmc_leaf_size_return_wit_4`: BOOL; (0 = (cm_rep_leaf_size (ty_pre))).
- `cmc_code_slot_size_return_wit_1`: BOOL; (retval = (cm_rep_code_slot_size (code_pre) (0))).
- `cmc_code_slot_size_return_wit_2`: BOOL; ((count_pre * retval ) = (cm_rep_code_slot_size (code_pre) (count_pre))).
- `cmc_members_size_safety_wit_3`: SAFETY; “ ((retval + retval_2 ) <= INT64_MAX) ”; “ ((INT64_MIN) <= (retval + retval_2 )) ”.
- `cmc_members_size_entail_wit_1`: OPEN-LIST; head/tail and stored-address extraction.
- `cmc_members_size_return_wit_1`: NULL; recover nil from representation.
- `cmc_members_size_return_wit_2`: LIST-MATH, FOLD-LIST; “ ((retval + retval_2 ) = (cm_rep_members_size (members))) ”; (cm_member_list_rep member_pre members ).
- `cmc_struct_size_at_entail_wit_1`: OPEN-LIST; head/tail and stored-address extraction.
- `cmc_struct_size_at_return_wit_1`: NULL; recover nil from representation.
- `cmc_struct_size_at_return_wit_2`: LIST-MATH, FOLD-LIST; “ (retval = (cm_rep_struct_size (structs) (0))) ”; (cm_struct_list_rep item_pre structs ).
- `cmc_struct_size_at_return_wit_3`: LIST-MATH, FOLD-LIST; “ (retval = (cm_rep_struct_size (structs) (sid_pre))) ”; (cm_struct_list_rep item_pre structs ).
- `cmc_nonzero_return_wit_1`: BOOL; (0 = (cm_rep_nonzero (0))).
- `cmc_nonzero_return_wit_2`: BOOL; (1 = (cm_rep_nonzero (n_pre))).
- `cmc_global_array_at_entail_wit_1`: OPEN-LIST; head/tail and stored-address extraction.
- `cmc_global_array_at_return_wit_1`: NULL; recover nil from representation.
- `cmc_global_array_at_return_wit_2`: LIST-MATH, FOLD-LIST; “ (retval = (cm_rep_global_array (globals) (0))) ”; (cm_global_list_rep item_pre globals ).
- `cmc_global_array_at_return_wit_3`: LIST-MATH, FOLD-LIST; “ (retval = (cm_rep_global_array (globals) (index_pre))) ”; (cm_global_list_rep item_pre globals ).
- `cmc_slot_array_at_entail_wit_1`: OPEN-LIST; head/tail and stored-address extraction.
- `cmc_slot_array_at_return_wit_1`: NULL; recover nil from representation.
- `cmc_slot_array_at_return_wit_2`: LIST-MATH, FOLD-LIST; “ (retval = (cm_rep_member_array (slots) (0))) ”; (cm_slot_list_rep item_pre slots ).
- `cmc_slot_array_at_return_wit_3`: LIST-MATH, FOLD-LIST; “ (retval = (cm_rep_member_array (slots) (index_pre))) ”; (cm_slot_list_rep item_pre slots ).
- `cmc_slot_type_at_entail_wit_1`: OPEN-LIST; head/tail and stored-address extraction.
- `cmc_slot_type_at_return_wit_1`: NULL; recover nil from representation.
- `cmc_slot_type_at_return_wit_2`: LIST-MATH, FOLD-LIST; “ ((cm_type_encode ((cm_slot_ty (head)))) = (cm_rep_slot_type (slots) (0))) ”; (cm_slot_list_rep item_pre slots ).
- `cmc_slot_type_at_return_wit_3`: LIST-MATH, FOLD-LIST; “ (retval = (cm_rep_slot_type (slots) (index_pre))) ”; (cm_slot_list_rep item_pre slots ).
- `cmc_member_array_at_entail_wit_1`: OPEN-LIST; head/tail and stored-address extraction.
- `cmc_member_array_at_return_wit_1`: NULL; recover nil from representation.
- `cmc_member_array_at_return_wit_2`: LIST-MATH, FOLD-LIST; “ (retval = (cm_rep_member_array (members) (0))) ”; (cm_member_list_rep item_pre members ).
- `cmc_member_array_at_return_wit_3`: LIST-MATH, FOLD-LIST; “ (retval = (cm_rep_member_array (members) (index_pre))) ”; (cm_member_list_rep item_pre members ).
- `cmc_type_size_at_return_wit_1`: BOOL; (8 = (cm_rep_type_size (structs) (ty_pre))).
- `cmc_type_size_at_return_wit_2`: BOOL; (8 = (cm_rep_type_size (structs) (0))).
- `cmc_type_size_at_return_wit_3`: BOOL; (1 = (cm_rep_type_size (structs) (1))).
- `cmc_type_size_at_return_wit_4`: BOOL; (retval = (cm_rep_type_size (structs) (ty_pre))).
- `cmc_slots_size_safety_wit_3`: SAFETY; “ ((retval + retval_2 ) <= INT64_MAX) ”; “ ((INT64_MIN) <= (retval + retval_2 )) ”.
- `cmc_slots_size_entail_wit_1`: OPEN-LIST; head/tail and stored-address extraction.
- `cmc_slots_size_return_wit_1`: NULL; recover nil from representation.
- `cmc_slots_size_return_wit_2`: LIST-MATH, FOLD-LIST; “ ((retval + retval_2 ) <= 1048576) ”; “ (0 <= (retval + retval_2 )) ”; “ ((retval + retval_2 ) = (cm_rep_members_size (slots))) ”; (cm_slot_list_rep slot_pre slots ).
- `cmc_slots_prefix_safety_wit_7`: SAFETY; “ ((retval + retval_2 ) <= INT64_MAX) ”; “ ((INT64_MIN) <= (retval + retval_2 )) ”.
- `cmc_slots_prefix_entail_wit_1`: OPEN-LIST; head/tail and stored-address extraction.
- `cmc_slots_prefix_return_wit_1`: NULL; recover nil from representation.
- `cmc_slots_prefix_return_wit_2`: LIST-MATH, FOLD-LIST; “ (0 <= (cm_rep_members_size (slots))) ”; “ (0 = (cm_rep_member_prefix (slots) (0))) ”; (cm_slot_list_rep slot_pre slots ).
- `cmc_slots_prefix_return_wit_3`: LIST-MATH, FOLD-LIST; “ ((retval + retval_2 ) <= (cm_rep_members_size (slots))) ”; “ ((retval + retval_2 ) <= 1048576) ”; “ (0 <= (retval + retval_2 )) ”; “ ((retval + retval_2 ) = (cm_rep_member_prefix (slots) (index_pre))) ”; (cm_slot_list_rep slot_pre slots ).
- `cmc_members_prefix_safety_wit_7`: SAFETY; “ ((retval + retval_2 ) <= INT64_MAX) ”; “ ((INT64_MIN) <= (retval + retval_2 )) ”.
- `cmc_members_prefix_entail_wit_1`: OPEN-LIST; head/tail and stored-address extraction.
- `cmc_members_prefix_return_wit_1`: NULL; recover nil from representation.
- `cmc_members_prefix_return_wit_2`: LIST-MATH, FOLD-LIST; “ (0 <= (cm_rep_members_size (members))) ”; “ (0 = (cm_rep_member_prefix (members) (0))) ”; (cm_member_list_rep node_pre members ).
- `cmc_members_prefix_return_wit_3`: LIST-MATH, FOLD-LIST; “ ((retval + retval_2 ) <= (cm_rep_members_size (members))) ”; “ ((retval + retval_2 ) <= 1048576) ”; “ (0 <= (retval + retval_2 )) ”; “ ((retval + retval_2 ) = (cm_rep_member_prefix (members) (index_pre))) ”; (cm_member_list_rep node_pre members ).
- `cmc_member_offset_at_entail_wit_1`: OPEN-LIST; head/tail and stored-address extraction.
- `cmc_member_offset_at_return_wit_1`: NULL; recover nil from representation.
- `cmc_member_offset_at_return_wit_2`: LIST-MATH, FOLD-LIST; “ (retval = (cm_rep_struct_member_prefix (structs) (0) (index_pre))) ”; (cm_struct_list_rep item_pre structs ).
- `cmc_member_offset_at_return_wit_3`: LIST-MATH, FOLD-LIST; “ (retval = (cm_rep_struct_member_prefix (structs) (sid_pre) (index_pre))) ”; (cm_struct_list_rep item_pre structs ).
- `cmc_struct_member_array_at_entail_wit_1`: OPEN-LIST; head/tail and stored-address extraction.
- `cmc_struct_member_array_at_return_wit_1`: NULL; recover nil from representation.
- `cmc_struct_member_array_at_return_wit_2`: LIST-MATH, FOLD-LIST; “ (retval = (cm_rep_struct_member_array (structs) (0) (index_pre))) ”; (cm_struct_list_rep item_pre structs ).
- `cmc_struct_member_array_at_return_wit_3`: LIST-MATH, FOLD-LIST; “ (retval = (cm_rep_struct_member_array (structs) (sid_pre) (index_pre))) ”; (cm_struct_list_rep item_pre structs ).
- `cmc_globals_size_safety_wit_3`: SAFETY; “ ((retval + retval_2 ) <= INT64_MAX) ”; “ ((INT64_MIN) <= (retval + retval_2 )) ”.
- `cmc_globals_size_entail_wit_1`: OPEN-LIST; head/tail and stored-address extraction.
- `cmc_globals_size_return_wit_1`: NULL; recover nil from representation.
- `cmc_globals_size_return_wit_2`: LIST-MATH, FOLD-LIST; “ ((retval + retval_2 ) <= 1048560) ”; “ (0 <= (retval + retval_2 )) ”; “ ((retval + retval_2 ) = (cm_rep_globals_size (globals))) ”; (cm_global_list_rep node_pre globals ).
- `cmc_globals_prefix_safety_wit_7`: SAFETY; “ ((retval + retval_2 ) <= INT64_MAX) ”; “ ((INT64_MIN) <= (retval + retval_2 )) ”.
- `cmc_globals_prefix_entail_wit_1`: OPEN-LIST; head/tail and stored-address extraction.
- `cmc_globals_prefix_return_wit_1`: NULL; recover nil from representation.
- `cmc_globals_prefix_return_wit_2`: LIST-MATH, FOLD-LIST; “ (0 <= (cm_rep_globals_size (globals))) ”; “ (0 = (cm_rep_globals_prefix (globals) (0))) ”; (cm_global_list_rep node_pre globals ).
- `cmc_globals_prefix_return_wit_3`: LIST-MATH, FOLD-LIST; “ ((retval + retval_2 ) <= (cm_rep_globals_size (globals))) ”; “ ((retval + retval_2 ) <= 1048560) ”; “ (0 <= (retval + retval_2 )) ”; “ ((retval + retval_2 ) = (cm_rep_globals_prefix (globals) (index_pre))) ”; (cm_global_list_rep node_pre globals ).
- `cmc_strings_size_entail_wit_1`: OPEN-LIST; head/tail and stored-address extraction.
- `cmc_strings_size_return_wit_1`: NULL; recover nil from representation.
- `cmc_strings_size_return_wit_2`: LIST-MATH, FOLD-LIST; “ ((((cm_rep_string_length (head)) + 1 ) + retval ) <= 1048560) ”; “ (0 <= (((cm_rep_string_length (head)) + 1 ) + retval )) ”; “ ((((cm_rep_string_length (head)) + 1 ) + retval ) = (cm_rep_strings_size (strings))) ”; (cm_string_list_rep node_pre strings ).
- `cmc_strings_prefix_entail_wit_1`: OPEN-LIST; head/tail and stored-address extraction.
- `cmc_strings_prefix_return_wit_1`: NULL; recover nil from representation.
- `cmc_strings_prefix_return_wit_2`: LIST-MATH, FOLD-LIST; “ (0 <= (cm_rep_strings_size (strings))) ”; “ (0 = (cm_rep_strings_prefix (strings) (0))) ”; (cm_string_list_rep node_pre strings ).
- `cmc_strings_prefix_return_wit_3`: LIST-MATH, FOLD-LIST; “ ((((cm_rep_string_length (head)) + 1 ) + retval ) <= (cm_rep_strings_size (strings))) ”; “ ((((cm_rep_string_length (head)) + 1 ) + retval ) <= 1048560) ”; “ (0 <= (((cm_rep_string_length (head)) + 1 ) + retval )) ”; “ ((((cm_rep_string_length (head)) + 1 ) + retval ) = (cm_rep_strings_prefix (strings) (index_pre))) ”; (cm_string_list_rep node_pre strings ).
- `cmc_global_address_return_wit_1`: ADDRESS; ((16 + retval ) = (cm_rep_global_address (items) (index_pre))).
- `cmc_string_address_return_wit_1`: ADDRESS; (((16 + retval ) + retval_2 ) = (cm_rep_string_address (global_items) (string_items) (index_pre))).
- `cmc_binding_array_value_return_wit_1`: LOOKUP; (retval = (cm_binding_array_code (policy) (p) (fid_pre) (0) (slot_pre))).
- `cmc_binding_array_value_return_wit_2`: LOOKUP; (retval = (cm_binding_array_code (policy) (p) (fid_pre) (1) (slot_pre))).
- `cmc_binding_array_value_return_wit_3`: LOOKUP; (0 = (cm_binding_array_code (policy) (p) (fid_pre) (scope_pre) (slot_pre))).
- `cmc_member_array_safety_wit_1`: SAFETY; “ (((retval % ( 1024 ) ) - 2 ) <= INT_MAX) ”; “ ((INT_MIN) <= ((retval % ( 1024 ) ) - 2 )) ”.
- `cmc_member_array_return_wit_1`: LOOKUP; ((cm_rep_struct_member_array (structs) ((((base_ty_pre - 1024 ) % ( 1024 ) ) - 2 )) (mid_pre)) = (cm_member_array_code (p) (base) (mid_pre))).
- `cm_args_length_safety_wit_3`: SAFETY; “ ((retval + 1 ) <= INT_MAX) ”; “ ((INT_MIN) <= (retval + 1 )) ”.
- `cm_args_length_entail_wit_1`: OPEN-LIST; head/tail and stored-address extraction.
- `cm_args_length_return_wit_1`: NULL; recover nil from representation.
- `cm_args_length_return_wit_2`: LIST-MATH, FOLD-LIST; “ ((retval + 1 ) = (cm_rep_args_length (args))) ”; (cm_arg_list_rep arg_pre args ).
- `cmc_args_tpair_safety_wit_4`: SAFETY; “ (((cm_acount ((cm_args_apair (tail)))) + 1 ) <= INT_MAX) ”; “ ((INT_MIN) <= ((cm_acount ((cm_args_apair (tail)))) + 1 )) ”.
- `cmc_args_tpair_entail_wit_1`: OPEN-LIST; head/tail and stored-address extraction.
- `cmc_args_tpair_return_wit_1`: NULL; recover nil from representation.
- `cmc_args_tpair_return_wit_2`: LIST-MATH, FOLD-LIST; “ (((cm_acount ((cm_args_apair (tail)))) + 1 ) = (cm_acount ((cm_args_apair (args))))) ”; “ (retval = (cm_adepth ((cm_args_apair (args))))) ”; (cm_arg_list_rep arg_pre args ).
- `cm_expr_temps_safety_wit_4`: SAFETY; “ ((1 + (cm_tright ((cm_expr_tpair (y)))) ) <= INT_MAX) ”; “ ((INT_MIN) <= (1 + (cm_tright ((cm_expr_tpair (y)))) )) ”.
- `cm_expr_temps_safety_wit_9`: SAFETY; “ ((1 + (cm_tright ((cm_expr_tpair (y)))) ) <= INT_MAX) ”; “ ((INT_MIN) <= (1 + (cm_tright ((cm_expr_tpair (y)))) )) ”.
- `cm_expr_temps_safety_wit_15`: SAFETY; “ ((1 + (cm_tright ((cm_expr_tpair (y)))) ) <= INT_MAX) ”; “ ((INT_MIN) <= (1 + (cm_tright ((cm_expr_tpair (y)))) )) ”.
- `cm_expr_temps_safety_wit_19`: SAFETY; “ (((cm_acount ((cm_args_apair (eargs)))) + (cm_adepth ((cm_args_apair (eargs)))) ) <= INT_MAX) ”; “ ((INT_MIN) <= ((cm_acount ((cm_args_apair (eargs)))) + (cm_adepth ((cm_args_apair (eargs)))) )) ”.
- `cm_expr_temps_entail_wit_1`: OPEN-EXPR; constructor/entry extraction.
- `cm_expr_temps_entail_wit_2`: OPEN-EXPR; constructor/entry extraction.
- `cm_expr_temps_entail_wit_3`: OPEN-EXPR; constructor/entry extraction.
- `cm_expr_temps_entail_wit_4`: OPEN-EXPR; constructor/entry extraction.
- `cm_expr_temps_entail_wit_5`: OPEN-EXPR; constructor/entry extraction.
- `cm_expr_temps_entail_wit_6`: OPEN-EXPR; constructor/entry extraction.
- `cm_expr_temps_entail_wit_7`: OPEN-EXPR; constructor/entry extraction.
- `cm_expr_temps_entail_wit_8`: OPEN-EXPR; constructor/entry extraction.
- `cm_expr_temps_entail_wit_9`: OPEN-EXPR; constructor/entry extraction.
- `cm_expr_temps_entail_wit_10`: OPEN-EXPR; constructor/entry extraction.
- `cm_expr_temps_return_wit_1`: EXPR-MATH, FOLD-EXPR; “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ”; “ (retval = (cm_tright ((cm_expr_tpair (e))))) ”; (cm_expr_rep expr_pre e ).
- `cm_expr_temps_return_wit_2`: EXPR-MATH, FOLD-EXPR; “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ”; “ (retval = (cm_tright ((cm_expr_tpair (e))))) ”; (cm_expr_rep expr_pre e ).
- `cm_expr_temps_return_wit_3`: EXPR-MATH, FOLD-EXPR; “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ”; “ (retval = (cm_tright ((cm_expr_tpair (e))))) ”; (cm_expr_rep expr_pre e ).
- `cm_expr_temps_return_wit_4`: EXPR-MATH, FOLD-EXPR; “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ”; “ (retval = (cm_tright ((cm_expr_tpair (e))))) ”; (cm_expr_rep expr_pre e ).
- `cm_expr_temps_return_wit_5`: EXPR-MATH, FOLD-EXPR; “ ((cm_tright ((cm_expr_tpair (x)))) = (cm_tleft ((cm_expr_tpair (e))))) ”; “ ((cm_tright ((cm_expr_tpair (x)))) = (cm_tright ((cm_expr_tpair (e))))) ”; (cm_expr_rep expr_pre e ).
- `cm_expr_temps_return_wit_6`: EXPR-MATH, FOLD-EXPR; “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ”; “ ((cm_tleft ((cm_expr_tpair (x)))) = (cm_tright ((cm_expr_tpair (e))))) ”; (cm_expr_rep expr_pre e ).
- `cm_expr_temps_return_wit_7`: EXPR-MATH, FOLD-EXPR; “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ”; “ ((cm_tright ((cm_expr_tpair (x)))) = (cm_tright ((cm_expr_tpair (e))))) ”; (cm_expr_rep expr_pre e ).
- `cm_expr_temps_return_wit_8`: EXPR-MATH, FOLD-EXPR; “ (retval = (cm_tleft ((cm_expr_tpair (e))))) ”; “ (retval = (cm_tright ((cm_expr_tpair (e))))) ”; (cm_expr_rep expr_pre e ).
- `cm_expr_temps_return_wit_9`: EXPR-MATH, FOLD-EXPR; “ ((cm_tright ((cm_expr_tpair (x)))) = (cm_tleft ((cm_expr_tpair (e))))) ”; “ ((cm_tright ((cm_expr_tpair (x)))) = (cm_tright ((cm_expr_tpair (e))))) ”; (cm_expr_rep expr_pre e ).
- `cm_expr_temps_return_wit_10`: EXPR-MATH, FOLD-EXPR; “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ”; “ (((cm_acount ((cm_args_apair (eargs)))) + (cm_adepth ((cm_args_apair (eargs)))) ) = (cm_tright ((cm_expr_tpair (e))))) ”; (cm_expr_rep expr_pre e ).
- `cm_expr_temps_return_wit_11`: EXPR-MATH, FOLD-EXPR; “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ”; “ ((cm_tright ((cm_expr_tpair (x)))) = (cm_tright ((cm_expr_tpair (e))))) ”; (cm_expr_rep expr_pre e ).
- `cm_expr_temps_return_wit_12`: EXPR-MATH, FOLD-EXPR; “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ”; “ ((cm_tright ((cm_expr_tpair (x)))) = (cm_tright ((cm_expr_tpair (e))))) ”; (cm_expr_rep expr_pre e ).
- `cm_expr_temps_return_wit_13`: EXPR-MATH, FOLD-EXPR; “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ”; “ ((cm_tright ((cm_expr_tpair (x)))) = (cm_tright ((cm_expr_tpair (e))))) ”; (cm_expr_rep expr_pre e ).
- `cm_expr_temps_return_wit_14`: EXPR-MATH, FOLD-EXPR; “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ”; “ (0 = (cm_tright ((cm_expr_tpair (e))))) ”; (cm_expr_rep expr_pre e ).
- `cm_expr_temps_return_wit_15`: EXPR-MATH, FOLD-EXPR; “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ”; “ (0 = (cm_tright ((cm_expr_tpair (e))))) ”; (cm_expr_rep expr_pre e ).
- `cm_expr_temps_return_wit_16`: EXPR-MATH, FOLD-EXPR; “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ”; “ (0 = (cm_tright ((cm_expr_tpair (e))))) ”; (cm_expr_rep expr_pre e ).
- `cm_expr_temps_return_wit_17`: EXPR-MATH, FOLD-EXPR; “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ”; “ (0 = (cm_tright ((cm_expr_tpair (e))))) ”; (cm_expr_rep expr_pre e ).
- `cm_expr_temps_return_wit_18`: EXPR-MATH, FOLD-EXPR; “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ”; “ (0 = (cm_tright ((cm_expr_tpair (e))))) ”; (cm_expr_rep expr_pre e ).
- `cm_expr_temps_return_wit_19`: EXPR-MATH, FOLD-EXPR; “ (0 = (cm_tleft ((cm_expr_tpair (e))))) ”; “ (0 = (cm_tright ((cm_expr_tpair (e))))) ”; (cm_expr_rep expr_pre e ).
- `cmc_stmt_temps_entail_wit_1`: OPEN-STMT; constructor/entry extraction.
- `cmc_stmt_temps_entail_wit_2`: OPEN-STMT; constructor/entry extraction.
- `cmc_stmt_temps_entail_wit_3`: OPEN-STMT; constructor/entry extraction.
- `cmc_stmt_temps_entail_wit_4`: OPEN-STMT; constructor/entry extraction.
- `cmc_stmt_temps_entail_wit_5`: OPEN-STMT; constructor/entry extraction.
- `cmc_stmt_temps_entail_wit_6`: OPEN-STMT; constructor/entry extraction.
- `cmc_stmt_temps_entail_wit_7`: OPEN-STMT; constructor/entry extraction.
- `cmc_stmt_temps_entail_wit_8`: OPEN-STMT; constructor/entry extraction.
- `cmc_stmt_temps_return_wit_1`: STMT-MATH, FOLD-STMT; “ ((cm_stemps (s)) <= INT_MAX) ”; “ (0 <= (cm_stemps (s))) ”; “ (retval = (cm_stemps (s))) ”; (cm_stmt_rep stmt_pre s ).
- `cmc_stmt_temps_return_wit_2`: STMT-MATH, FOLD-STMT; “ ((cm_stemps (s)) <= INT_MAX) ”; “ (0 <= (cm_stemps (s))) ”; “ (retval = (cm_stemps (s))) ”; (cm_stmt_rep stmt_pre s ).
- `cmc_stmt_temps_return_wit_3`: STMT-MATH, FOLD-STMT; “ ((cm_stemps (s)) <= INT_MAX) ”; “ (0 <= (cm_stemps (s))) ”; “ (retval = (cm_stemps (s))) ”; (cm_stmt_rep stmt_pre s ).
- `cmc_stmt_temps_return_wit_4`: STMT-MATH, FOLD-STMT; “ ((cm_stemps (s)) <= INT_MAX) ”; “ (0 <= (cm_stemps (s))) ”; “ (retval = (cm_stemps (s))) ”; (cm_stmt_rep stmt_pre s ).
- `cmc_stmt_temps_return_wit_5`: STMT-MATH, FOLD-STMT; “ ((cm_stemps (s)) <= INT_MAX) ”; “ (0 <= (cm_stemps (s))) ”; “ (retval = (cm_stemps (s))) ”; (cm_stmt_rep stmt_pre s ).
- `cmc_stmt_temps_return_wit_6`: STMT-MATH, FOLD-STMT; “ ((cm_stemps (s)) <= INT_MAX) ”; “ (0 <= (cm_stemps (s))) ”; “ (retval = (cm_stemps (s))) ”; (cm_stmt_rep stmt_pre s ).
- `cmc_stmt_temps_return_wit_7`: STMT-MATH, FOLD-STMT; “ ((cm_stemps (s)) <= INT_MAX) ”; “ (0 <= (cm_stemps (s))) ”; “ (retval = (cm_stemps (s))) ”; (cm_stmt_rep stmt_pre s ).
- `cmc_stmt_temps_return_wit_8`: STMT-MATH, FOLD-STMT; “ ((cm_stemps (s)) <= INT_MAX) ”; “ (0 <= (cm_stemps (s))) ”; “ (0 = (cm_stemps (s))) ”; (cm_stmt_rep stmt_pre s ).
- `cmc_stmt_temps_return_wit_9`: STMT-MATH, FOLD-STMT; “ ((cm_stemps (s)) <= INT_MAX) ”; “ (0 <= (cm_stemps (s))) ”; “ (0 = (cm_stemps (s))) ”; (cm_stmt_rep stmt_pre s ).
- `cmc_stmt_temps_return_wit_10`: STMT-MATH, FOLD-STMT; “ ((cm_stemps (s)) <= INT_MAX) ”; “ (0 <= (cm_stemps (s))) ”; “ (0 = (cm_stemps (s))) ”; (cm_stmt_rep stmt_pre s ).
- `cmc_stmt_temps_return_wit_11`: STMT-MATH, FOLD-STMT; “ ((cm_stemps (s)) <= INT_MAX) ”; “ (0 <= (cm_stemps (s))) ”; “ (0 = (cm_stemps (s))) ”; (cm_stmt_rep stmt_pre s ).
- `cmc_stmt_temps_return_wit_12`: STMT-MATH, FOLD-STMT; “ ((cm_stemps (s)) <= INT_MAX) ”; “ (0 <= (cm_stemps (s))) ”; “ (0 = (cm_stemps (s))) ”; (cm_stmt_rep stmt_pre s ).
- `cm_normalize_count_return_wit_1`: BOOL; (6 = (cm_normalize_code_value (1))).
- `cm_normalize_count_return_wit_2`: BOOL; (0 = (cm_normalize_code_value (ty_pre))).

## Grouping Decisions
37 independent groups, each containing two to six witnesses; no single-witness or oversized groups. List functions keep their opening/null/cons work together, with only three to five witnesses and identical representation context. Scalar definitions remain separate from lookup/helper work. Expression and statement opening, safety, and final reconstruction are generally separated. Call and index opening stay with their tiny final groups to avoid one-witness batches; they require no new helpers.
The first group isolates valid-index lookup correspondence, the only new mathematical helper family. All three stable structural lookup lemmas are public candidates. Its one modulo safety VC contributes only two light splits in the same encoding context. Other groups use single-definition reductions and arithmetic; no new permutation, mask or aggregate-induction helper is needed. Groups require no sibling outputs.
| Group | Top-level | Aggressive splits | New helpers | Difficulty |
|---|---:|---:|---:|---:|
| lookup_bridge | 5 | 6 | 3 | 4 |
| scalar_guards | 6 | 6 | 0 | 1 |
| leaf_slot_size | 6 | 6 | 0 | 1 |
| type_and_normalize | 6 | 6 | 0 | 1 |
| members_size | 4 | 4 | 0 | 2 |
| struct_size_at | 4 | 4 | 0 | 2 |
| global_array_at | 4 | 4 | 0 | 2 |
| slot_array_at | 4 | 4 | 0 | 2 |
| slot_type_at | 4 | 4 | 0 | 2 |
| member_array_at | 4 | 4 | 0 | 2 |
| slots_size | 4 | 6 | 0 | 2 |
| slots_prefix | 5 | 10 | 0 | 3 |
| members_prefix | 5 | 10 | 0 | 3 |
| member_offset_at | 4 | 4 | 0 | 2 |
| struct_member_array_at | 4 | 4 | 0 | 2 |
| globals_size | 4 | 6 | 0 | 2 |
| globals_prefix | 5 | 10 | 0 | 3 |
| strings_size | 3 | 4 | 0 | 2 |
| strings_prefix | 4 | 8 | 0 | 3 |
| addresses | 2 | 2 | 0 | 1 |
| args_length | 4 | 4 | 0 | 2 |
| args_pair | 4 | 5 | 0 | 3 |
| expr_safety | 4 | 8 | 0 | 2 |
| expr_open_binary | 3 | 0 | 0 | 3 |
| expr_open_unary | 5 | 0 | 0 | 3 |
| expr_call | 2 | 3 | 0 | 3 |
| expr_assign_index | 3 | 6 | 0 | 3 |
| expr_binary_results | 3 | 9 | 0 | 3 |
| expr_unary_results | 4 | 12 | 0 | 3 |
| expr_io_results | 3 | 9 | 0 | 2 |
| expr_literal_results | 3 | 9 | 0 | 2 |
| expr_other_results | 3 | 9 | 0 | 2 |
| stmt_open_expression | 4 | 0 | 0 | 3 |
| stmt_open_control | 4 | 0 | 0 | 3 |
| stmt_expression_results | 3 | 12 | 0 | 3 |
| stmt_control_results | 4 | 16 | 0 | 4 |
| stmt_inert_results | 5 | 20 | 0 | 3 |

### Critical-path review
- lookup_bridge: five witnesses, six aggressive splits, three public structural helpers. Context: Z.to_nat/nth/Zlength and type encoding. Binding-local and member final results share member-array nth; nested struct lookup builds on it, justifying one helper owner. Descriptor traversal transitions and unrelated arithmetic are separate.
- stmt_control_results: four witnesses, sixteen splits, zero helpers. Context: cm_stemps, safe projections, node/payload bridges and cancellation. Its independently provable opening assertions live in stmt_open_control. Individual pure/spatial splits follow their parent, but no cross-witness dependence remains.
- expr_unary_results: four witnesses, twelve splits, zero helpers; conditional op reductions and seven-field reconstruction. Opening and overflow work are separate.
- expr_binary_results: three witnesses, nine splits, zero helpers; boolean-op model and two-child frame. Assignment/index are separate to shorten the tail.
- stmt_inert_results: five witnesses, twenty splits, zero helpers. Fifteen targets are constant/safe projections and five are the same local node-fold shape; the impossible-tag route is contradictory. It is a moderate batch despite split count.
- Prefix groups: at most five witnesses and ten aggressive splits, zero helpers. Supplied recursive bounds remove any new induction; arithmetic/folding share only a cons context.

## Risks or Blockers
No definite blocker. Public nth proofs need explicit Z-to-nat successor conversion and default-value bookkeeping, with all index premises present. The automatic file contains generated admitted placeholders and is controller-owned; this plan does not claim kernel verification of the complete case. Manual/source/library files were not modified.
