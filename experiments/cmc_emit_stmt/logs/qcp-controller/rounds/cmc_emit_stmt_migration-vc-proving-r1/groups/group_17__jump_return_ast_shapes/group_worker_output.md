# Jump/return AST shapes

Completed the 3 assigned top-level witnesses and 23 splits. Destructing the statement and reducing its kind eliminates incompatible constructors using the actual branch guards. The surviving payload supplies pointer equalities/non-null facts and the return expression resource. No helper was added.

Repair: the initial uniform split script attempted to unfold payload after constructor equality had already closed by congruence. Apply subsequent payload processing only to remaining goals (`all:`). A preliminary editing script also stopped before writing because top-level seed endings were `Admitted`, not `Abort`; the corrected replacement edited only assigned spans.

```json
{"development_calls": 2, "development_failed": 1, "debug_calls": 1, "debug_failed": 0, "exact_calls": 1, "exact_failed": 0, "new_helpers": 0}
```
