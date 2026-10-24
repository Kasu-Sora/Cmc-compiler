Completed the five assigned top-level witnesses and all twelve assigned split goals. Each split opens with LLM_pre_process and closes explicitly; each top-level proof uses aggressive_pre_process followed only by its corresponding Goal_apply applications.

Added three proved helpers: cm_expr_temps_nonnegative__index_bounds, cm_index_code_bounds__index_bounds, and cm_index_temp_bounds__index_bounds. They use the imported exact emission-length and nonnegative count facts to establish child PC prefixes and project the parent maximum temporary budget.

Repairs during development: removed an unnecessary branch after automation had already closed the binary case; resolved list-lemma visibility through its qualified name; removed a rejected project import; and explicitly extracted the pure arithmetic target from the safety entailments with dump_pre_spatial. No annotation changes or new assumptions were needed.

The final group-development check passed, and the exact group-check passed. The debug call successfully displayed the remaining safety proof state. Controller acceptance remains separate from these optional checks.

```json
{
  "development_calls": 6,
  "development_failed": 5,
  "debug_calls": 1,
  "debug_failed": 0,
  "exact_calls": 1,
  "exact_failed": 0,
  "new_helpers": 3
}
```
