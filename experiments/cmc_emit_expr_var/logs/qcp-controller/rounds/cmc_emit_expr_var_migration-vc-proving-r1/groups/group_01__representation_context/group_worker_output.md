# Proof effort

- Development invocations: 7; failed invocations: 6.
- Debug invocations: 0; failed invocations: 0.
- Exact group-check invocations: 1; failed invocations: 0.
- New or copied helpers: 0. The group library was unchanged.

Repair sequence: removed redundant pure introductions because `Intros` already extracts them; destructed the leaf conjunction before substituting its zero pointers; matched the aggressive branches in spatial-then-pure order; normalized separation-conjunction associativity before resource cancellation. Two failed development invocations displayed proof states for the immediately preceding failure, without further mathematical changes.
