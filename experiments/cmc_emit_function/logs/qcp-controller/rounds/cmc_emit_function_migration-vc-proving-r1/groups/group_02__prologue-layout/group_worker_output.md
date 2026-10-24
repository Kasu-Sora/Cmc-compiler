# Prologue layout proof delivery

All three assigned top-level VCs and six assigned split goals are proved. The existing `cm_slots_size_matches__temp_context` supplies the encoded/semantic size bridge without duplication. One new public helper, `cm_function_param_count_length__prologue_layout`, bounds parameter length by the parameter-store instruction count.

```json
{"development_calls":3,"development_failed":2,"debug_calls":0,"debug_failed":0,"exact_calls":1,"exact_failed":0,"new_helpers":1}
```

Repair notes: the first development attempt showed the empty-prefix goals were already discharged by the required `LLM_pre_process` closer, so redundant subsequent tactics were removed. The second attempt showed `INT_MAX` is notation rather than an unfoldable declaration; removed that unfold and discharged its numeric inequality with `lia`. No contract or annotation changes were needed.
