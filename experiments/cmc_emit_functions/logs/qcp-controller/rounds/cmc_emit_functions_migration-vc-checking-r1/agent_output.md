# VC checking decision summary

## Outcome

All 12 assigned top-level witnesses have a proving assignment. All 29 generated split goals were judged provable before selecting any whole-goal mode. No formal input was modified; no debug command was necessary. This is an independent provability assessment, not a completed Rocq proof.

## Structural Blocker Scan

- Status: passed
- Top-level VCs scanned: 12
- No-split VCs checked first: 3
- Definite blockers: 0

The first scan examined `which_implies_wit_1`, `which_implies_wit_5`, and `which_implies_wit_6`: their existential addresses come from the current function/list resources. All remaining witnesses retain the required program, head, tail, and emitter resources. The emitter rewrites use fid_pre consistently and an explicit cons shape. The arithmetic transition has both successor-PC equality and successor-PC/fid representability. No missing current-to-pre bridge was found.

## Annotation Comparison Review

First proving round: no comparison entries. The readiness expansion has its own establishing VC (`which_implies_wit_2`); its successor bounds/equality and head properties are definitional projections of concrete readiness, except the statement-code-length normalization, whose unconditional lemma is in the imported statement library. List-head lookup equality comes from concrete head readiness. No premise is justified merely by a later assumption.

## Proof-Mode Decisions

Binary split assessment in declaration order:

| Parent suffix | Splits judged provable | Splits judged unprovable | Selected mode |
|---|---:|---:|---|
| safety_wit_2 | 2 | 0 | aggressive_pre_process |
| safety_wit_3 | 2 | 0 | aggressive_pre_process |
| return_wit_1 | 1 spatial | 0 | aggressive_pre_process |
| return_wit_2 | 1 spatial | 0 | aggressive_pre_process |
| partial_solve_wit_5_pure | 1 | 0 | aggressive_pre_process |
| partial_solve_wit_10_pure | 1 | 0 | aggressive_pre_process |
| which_implies_wit_1 | none | none | LLM_pre_process |
| which_implies_wit_2 | 19 | 0 | aggressive_pre_process |
| which_implies_wit_4 | 1 spatial | 0 | aggressive_pre_process |
| which_implies_wit_5 | none | none | LLM_pre_process |
| which_implies_wit_6 | none | none | LLM_pre_process |
| which_implies_wit_7 | 1 spatial | 0 | aggressive_pre_process |

Only the three no-split VCs received whole-goal provability analysis. All modes were fixed before strategies/grouping. Every generated split follows its parent into the same group.

## Common Proof Patterns

- **R — Readiness projection.** Rewrite the cons equation in the readiness hypothesis, reduce exactly one list constructor, and project the head/tail facts. The emitted-statement length goal additionally uses the established unconditional statement-length identity. No heap/existential is involved in these pure split goals.
- **H — Function representation.** Open only the relevant header/body/context definitions; identify the shared existential body-address list and retain parameter/local/statement resources. Reconstruct existential witnesses from those same addresses and cancel the unchanged frame.
- **A — Integer bounds.** The successor PC equality and existing nonnegative i32 bound imply the C signed bounds. No new arithmetic invariant is required.
- **E — Emission append.** Rewrite the outer emission argument with the cons shape, reduce one constructor, and normalize append associativity. The resolved emitter assertion is otherwise unchanged.
- **P — Pure projection.** Preserve the entire heap and introduce an existing shape equality or a definitional tail-of-cons equality.

## VC Deltas

- `which_implies_wit_2`: R; split 12 normalizes statement length, splits 2/13/14 rewrite function_pc, splits 5/6 normalize INT_MAX; all other splits directly select the requested conjunct.
- `return_wit_1`: H; null root rules out cons, empty emission and app_nil_r identify both emitter states.
- `return_wit_2`: H; prepend bp to the tail body-address list and reassemble a cons function list.
- `which_implies_wit_1`: H; nonnull rules out nil, readiness identifies the descriptor with total lookup.
- `which_implies_wit_5`: H; open context and instantiate bp/np with existing addresses.
- `which_implies_wit_6`: H; fold context with the same pp/lp/body/next addresses.
- `safety_wit_2`: A; use next-PC equality plus successor-PC representability.
- `safety_wit_3`: A; use successor-fid representability directly.
- `partial_solve_wit_5_pure`: P; existing cons shape.
- `partial_solve_wit_10_pure`: P; tail-of-cons reduction.
- `which_implies_wit_4`: E; normalize pending code before the head call.
- `which_implies_wit_7`: E; normalize accumulated done code after recursion.

## Grouping Decisions

| Group | Witnesses | Aggressive splits | Whole goals | New helper families | Difficulty |
|---|---:|---:|---:|---:|---:|
| readiness | 1 | 19 | 0 | 0 | 2 |
| resources | 5 | 2 | 3 | 0 | 3 |
| transitions | 6 | 8 | 0 | 0 | 2 |

The singleton readiness group is justified by its indivisible 19-split parent and coherent projection context; its work is kept separate from lightweight transitions. The resource group shares existential header/body-list structure across opening, closing, and both returns. The transition group contains exactly six lightweight bound/projection/append witnesses and no new substantial mathematical lemma.

Critical-path review: resources is the likely tail, with two spatial splits and three whole goals, existing context/list definitions, and zero planned new helper families. Separating return_2 from list opening would duplicate the same body-address-list reasoning without reducing helper/context coupling; the five-witness group is retained. Readiness has nineteen splits but each projects an existing readiness conjunction, with only one existing statement-length bridge, so no new heavy theorem is needed. Emission final-result append normalization (which_implies_wit_7) and independent safety transitions are separated from resource final-result assembly. No new cross-group helper is planned; no group depends on a sibling output or new public fact.

## Risks or Blockers

No definite blocker. The implementation should avoid unrestricted rewriting of the self-referential `functions = head :: tail functions` equation; rewrite only the intended readiness or emission occurrence. Header/body-list reconstruction must equate the shared existential body-address list before cancellation. Library reuse was not analyzed as witness-proof reuse; only current predicate semantics and the existing statement-length fact were checked.

## Effort

Actual checker command calls: 0. Failed checker commands: 0. Manual Show insertions: 0. Formal input mutations: 0. No proof validation was claimed by this checker phase.
