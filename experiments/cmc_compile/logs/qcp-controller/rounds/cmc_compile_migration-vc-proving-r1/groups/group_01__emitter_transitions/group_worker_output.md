本组完成 `proof_of_cmc_compile_entail_wit_3`、`proof_of_cmc_compile_entail_wit_4`、`proof_of_cmc_compile_entail_wit_6` 的整体证明。

新增公共引理为 `cm_compile_functions_length__emitter_transitions` 和 `cm_compile_model_length__emitter_transitions`；未新增公共定义。两项引理计入 helper，三个当前 VC proof 单独计量。

```json
{
  "development_calls": 6,
  "development_failed": 5,
  "debug_calls": 6,
  "debug_failed": 1,
  "exact_calls": 1,
  "exact_failed": 0,
  "new_helpers": 2,
  "new_public_definitions": 0,
  "new_public_lemmas": 2,
  "current_vc_proofs": 3
}
```

失败计数包括一次由主控终止的 development 调用，以及一次由主控终止且检测到 debug 脚本变化的 debug 调用。后续采用精确参数的 `eval_addr` 重写，并顺序执行检查。
