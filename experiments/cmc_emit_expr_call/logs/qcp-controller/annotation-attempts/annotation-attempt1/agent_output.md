# Annotation attempt 1

Read all required annotation design guides, internal-predicate examples, algorithm-mirror negative C/model example and recursive/list resource positive examples. Prior verified migration C BODY contracts, not headers, supply imported helper declarations.

## Model and contract mapping

- HOL total `inth fid functions` maps to existing `cm_function_at policy fid functions`; no range restriction is added. Existing `cm_lookup_policy` and `cm_codegen_obligations` remain unchanged.
- Existing layout/count/count-context/plan/AST/leaf/var/simple libraries provide types, full recursive AST resources, well-formedness/typing, counts, temporary requirements and primitive code. No old manual/auto proof is imported.
- New shared closure: `cm_emit_pair`, pointer scale/binary finish (binary opcode reused), all 14 `cm_emit_expr_pair` constructor equations, recursive store/reload equations, `cm_expr_code_for`, `cm_expr_temps_for`. These are the source compiler's mathematical semantics, not a surrogate execution state. All arbitrary source argument expressions remain represented.
- Reload reproduces every source bound/fact and full function/argument/emitter resources. Store additionally preserves program resources, typing/count/wf/static-size/scratch facts. Call preserves source kind 8, both lvalue values, temp/depth/offset/pc/end constraints, and full program/function/expression/emitter resources.
- `cm_emit_expr` is the exact original external header contract. Its implementation proof is pending and is not claimed by this run.
- `cm_emit_temp_load_plan`, `cm_emit_temp_store_plan`, `cm_emit_call_plan`, `cm_expr_rvalue_count_context`, `cm_args_length` reproduce the previously verified C BODY contracts.
- New source-private proof helpers: head/tail observations and call-kind/empty-lvalue/source-equation bridges; no alternative view restricts the domain.

## Design attempts

1. Formal-case-lib-design failed at line 44 because Rocq parsed pattern variable `right` as the sumbool constructor. Renamed pattern variables to `lhs`/`rhs`; no semantic change.

## Ordinary Assert review

No full ordinary Assert is introduced. Local `which implies` boundaries expose owned AST fields, derive recursive premises, reshape exact code plans, and restore node ownership. Each is a function-call boundary or exit bridge; pure facts remain distinct from spatial ownership. No lexical loops occur.

## VC comparison

First attempt: none.

2. Design check passed after pattern-name repair. Symexec 1 failed at Extern Coq line 19: type and value declaration forms cannot share a block; split declarations into two blocks. This is an annotation parse failure, not a tool failure.

3. Removed namespace-qualified array externs accidentally classified as type declarations; trimmed unused value externs. Symexec then reached reload-null: partial implication matching substituted the local pointer with zero before matching opaque resources. Use entry pointer `arg@pre` at that boundary. Removed duplicate binary opcode declaration and reused imported verified definition after parent audit.

4. Existential names introduced by partial implication are local to that annotation. Replaced cross-annotation uses with source head/tail observers and transparent call-args observer. Symexec progressed through reload/store to call code-plan matching; use kind=8 directly and lvalue@pre to avoid premature syntactic substitution of opaque plan arguments.

5. Symexec 7 passed for all three runtime bodies (4.307s). Previous final-call mismatch fixed by using `cons(call, tail)` and exposing existing callee-count int32 bounds for the original long-long-to-int conversion. No runtime change or stronger precondition.

6. Added transparent call-code equation/coverage/empty-lvalue and reload-length bridges. Design check found nested store recursion is extensionally, rather than definitionally, identical to the public store function; proving equality by list induction.

## Generated-VC review

Read the current generated manual and inspected the key store pc/scratch and call bound/plan statements. They retain required premises and exact spatial resources. The substantive remaining mathematical obligation is the general expression code-length theorem (all constructors); it is a proof obligation over the complete definitions, never an assumption. Scalar count/overflow and source-model field facts are derived rather than added to inputs.

## Representation observations

`cm_args_head`, `cm_args_tail`, `cm_call_slots_tail` correspond to the three source-private HD/TL observations. The head's chosen empty-list default is unreachable in all uses, which require args=head::tail. `cm_call_args` is a transparent observation used only under kind 8. `cm_call_source_coverage` checks exact domain coverage; no smaller expression view is introduced. No new higher-order existential witness.

## New declarations by responsibility

Shared mathematical closure: `cm_emit_pair` with projections, `cm_pointer_scale`, `cm_binary_finish_code`, `cm_emit_args_reload`, `cm_emit_expr_pair`, `cm_expr_code_for`, `cm_emit_args_store`, `cm_expr_temps_for`. Reused `cm_binary_opcode` is imported unchanged; the initial duplicate was removed before acceptance.

Source-private observation definitions: `cm_args_head`, `cm_args_tail`, `cm_call_slots_tail`, `cm_call_args`. Shared transparent bridges: `cm_call_code_equation`, `cm_call_lvalue_empty`, `cm_call_source_coverage`, `cm_call_args_observe`, `cm_args_reload_length`. None changes model domain or introduces a premise. Full general expression code-length proof remains in the generated store-bound obligations for the proving owner.

## Design repair details

The new call equation initially used reflexivity; the public argument-store function and nested store recursion require a structural list-induction bridge. The first induction attempted before fully exposing the outer expression equation retained the wrong induction statement. The next explicit `change` used an unconstrained placeholder rejected by elaboration. Replaced it with the complete equation before generalizing pc/slot/scratch and list induction.

The explicit call equation and exact kind-8 source coverage now compile. A reload-length base case required reducing both typed empty-list lengths; changed that base case to reflexivity.

Reload-length check next exposed missing explicit ListLib import for Zlength_app (dependency imported but not re-exported the lemma). Added the explicit existing-library import; no dependency source changed.

Reload-length refinement: removing the redundant cons-length rewrite alone left primitive fragment length hidden from arithmetic. Added an explicit equality `Zlength(cm_temp_load_code ...)=5`, proved by reflexivity, then used list induction and linear arithmetic.

## Owner command totals (before controller acceptance)

- formal-case-lib-design: 10 invocations, 2 passed and 8 failed. Failures: reserved `right` pattern name; call equation reflexivity; induction before explicit outer equation; unconstrained `change` placeholder; typed nil-length base arithmetic; missing explicit ListLib lemma import; redundant cons-length rewrite; primitive-load length hidden from lia. Final invocation passed.
- symexec: 8 invocations, 2 passed and 6 failed. Failures: mixed type/value Extern block; namespace-qualified array extern misclassified as a type; null local-pointer opaque-resource matching; cross-annotation existential name scope; lvalue/local and constructor substitution in opaque plan matching; final-call singleton-tail/callee narrowing mismatch. Final invocation passed after the final lib change.
- No symexec tool/infrastructure failure occurred; all six failures were annotation/parser/resource matching issues.
- formal-case-lib (post-symexec): 1 invocation, 1 passed and 0 failed.
- The exact final design, symexec, and post-symexec formal-case-lib commands exited 0 and returned `status: passed`.
