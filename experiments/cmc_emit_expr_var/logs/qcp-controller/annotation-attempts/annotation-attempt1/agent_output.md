# Annotation design

Read the full original C/H and the annotation workflow plus linked guides. Relevant positive reference: leaf migration demonstrates explicit expression specialization and opening context resources. Predicate-first positive/negative examples were inspected. No prior manual/auto proof is imported.

The variable-only model is the exact cmc_codegen.c CMVarE source equation, independent of pc/temp. Existing total lookup policy and cm_wf_program are reused; no fid bound, actual-binding-type equality or extra scalar restriction is added. All original pre/post pure facts and ownership are retained. Three helper contracts are copied verbatim from their verified declarations.

Six partial `which implies` boundaries expose expression/context fields, restore full contexts, and select branch code prefixes. No ordinary full Assert, loop, branch-control directive, internal predicate, or higher-order existential is introduced. The remaining plan tail is arbitrary, and consumed code is appended to done.

## Check counts
Design 1 passed. Symexec 1 failed: annotation-scope error at helper call; existential names from partial assertion cannot be used in later where. Removed zg/zl where bindings for inference and rebound all pointer witnesses locally in the closing boundary. No semantic/contract change.

## VC comparison
None: first attempt.

Design 2 passed. Symexec 2 failed: partial-implies matching normalized lvalue==0 on the LHS inside the plan model while the current resource retained lvalue@pre. Repair uses the equivalent 0<=lvalue<=0 LHS (as the established leaf pattern), keeping exact branch equality on the RHS.

Design 3 passed. Symexec 3 passed; generated manual/goal inspected read-only. Post-library 1 passed. Final owner command counts: formal-case-lib-design 3 (all passed), symexec 3 (2 annotation failures repaired, final passed), formal-case-lib 1 (passed); tool failures 0. All successes had terminal exit 0 and controller status passed. No source/library semantics changed during the two annotation syntax/matching repairs.

The generated manual has nine top-level obligations: three branch returns and six local implications. The returns retain every source pure fact, all program/function/expr resources, and exact done/tail plan ownership. Declaration+contract comparison for all three helpers passed modulo whitespace.
