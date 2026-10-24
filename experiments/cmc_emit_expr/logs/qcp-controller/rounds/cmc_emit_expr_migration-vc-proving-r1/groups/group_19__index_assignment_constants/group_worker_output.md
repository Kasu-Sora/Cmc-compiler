# index_assignment_constants

Completed all five assigned top-level witnesses and all ten assigned split goals. Shape goals unfold `cm_expr_shape` and close by reflexivity; opcode goals reduce `tvm_opcode_code` and close by congruence. Top-level proofs use `aggressive_pre_process` followed only by the corresponding `Goal_apply` dispatches.

The first development check passed, and the first exact group check passed. No proof repairs, debug calls, new helpers, or library changes were needed. Controller final acceptance remains separate.

```json
{
  "development_calls": 1,
  "development_failed": 0,
  "debug_calls": 0,
  "debug_failed": 0,
  "exact_calls": 1,
  "exact_failed": 0,
  "new_helpers": 0
}
```
