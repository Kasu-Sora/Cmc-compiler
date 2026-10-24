Completed the five assigned top-level VCs and all nine assigned split goals using the required proof routes.

Shape goals use reflexive constructor shape equality; opcode goals compute their closed codes; the member-array guard follows from the existing context equalities. The child code bound follows from nonnegative code lengths and the parent code bound after expanding the member constructor. The child temporary budget is definitionally equal to the member temporary budget for either lvalue branch. No new helpers or imports were necessary.

The first development check found that `=?` was parsed in string scope. Replacing the two occurrences with explicit `Z.eqb` repaired the proof. The second development check and the exact group check passed. Controller acceptance remains separate.

```json
{
  "development_calls": 2,
  "development_failed": 1,
  "debug_calls": 0,
  "debug_failed": 0,
  "exact_calls": 1,
  "exact_failed": 0,
  "new_helpers": 0
}
```
