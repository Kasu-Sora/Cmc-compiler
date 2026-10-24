# Simple expression annotation delivery

## Scope and representation

The exact 11-line runtime body and emitter ABI are unchanged. Both helper prototypes reproduce the already verified BODY specifications from dispatch and var, including every original pure/resource pre/post fact. No previous proof_auto/manual is imported.

`cm_simple_expr` is the source `cm_leaf_expr e || kind e = 2`, using the existing renamed `cm_dispatch_leaf`. `cm_simple_view` has only the existing leaf view or a variable (scope/slot/type). `cm_simple_source_coverage` proves the original simple domain is exactly the image of this view, reusing `cm_dispatch_leaf_coverage`; `cm_simple_source_unique` proves unique embedding, reusing `cm_dispatch_leaf_unique`. Thus the extra With witness/equality does not strengthen the original input domain. Code composition selects the already verified leaf or var model; it defines no behavior for unsupported recursive expression constructors. This is an explicit semantic view, not a C control-state interpreter.

All original pure facts are carried through Require/Ensure, including typed/wf program, total function lookup without a new fid range, original expression wf/counts, parameter/local slots and representation safety, and the aggregate size bound. Full program/function/expression ownership and exact prefix consumption with arbitrary tail are preserved. `policy` and `cg` retain the existing source instantiation boundary. No new axiom, parameter, emitter oracle, or admitted library proof was introduced. The C* correspondence is constructorwise to the existing leaf and var equations, independent of pc/temp; the view coverage/uniqueness is formal Rocq evidence, not a cross-prover meta-equivalence theorem.

References influencing annotation: current verified dispatch and var C/spec/lib (required helper contracts and node open/close pattern), plus the skill's positive branch_destruct tutorial, predicate-first DP examples and negative algorithm mirror example. No algorithm mirror or explicit branch-control annotation is used.

## Key points and resources

1. Before kind read: open `cm_expr_rep` to its seven fields and existing payload, preserving all surrounding frames.
2. Var call boundary: kind 2 identifies the view constructor; derive slot bounds/type-code wf from original count facts and binding-valid from original expression wf. Rewrite only the emitter plan to existing var code. Close node before helper.
3. Leaf call boundary: kind not 2 identifies the leaf view; retain original wf/count facts while rewriting plan to leaf code, then close node.

No loops, ordinary full Assert, branch naming/join/clear, or higher-order existential witness. The only existentials are finite first-order view/constructor/field witnesses. No new internal predicates: the new declarations are spec-level domain/view/code definitions.

## Actual command attempts

All commands were exactly those in the handoff, at its bound CWD, and were continued to real terminal exit.

- formal-case-lib-design: 4 executions, all exit 0 / status passed. First checks the new model; second follows unused-extern cleanup; third follows Extern-block syntax repair; fourth follows fid resource retention repair. Case lib bytes were unchanged after the initial write.
- symexec: 3 executions: first 2 failed, third exit 0 / status passed.
- formal-case-lib: 1 execution, exit 0 / status passed.

Failure 1: symbolic-execution/symexec-error, C line 20 unexpected `:` expected `::`. Mixed type and term declarations in one Extern block are unsupported. Repair split type and term blocks; runtime/spec meaning unchanged.

Failure 2: symbolic-execution/symexec-error at leaf helper call, cannot read `fid` due to missing local data_at. The partial plan conversion mentioned fid on its simple-plan input but not on its leaf-plan output. Repair retains the already available expression wf/count facts on both sides, keeping fid visible without inventing a new premise or changing helper contracts. All node/context/emitter resources remained owned.

Final generated manual: 7 top-level obligations (2 returns, 5 which-implies), 4 spatial splits. Read-only inspection confirms branch premises are available and both returns preserve the original facts. Proof placeholders remain controller-generated for subsequent owners.

## VC comparison

First attempt: no failed_vcs and vc_comparisons is empty. Controller acceptance remains separate from this annotation delivery.
