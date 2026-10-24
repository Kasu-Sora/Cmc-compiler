# string-node-opening

已完成 `proof_of_cmc_emit_strings_entail_wit_1` 的整体证明。依照指定路线以 `LLM_pre_process` 开头；空链表与非空 node 矛盾，非空链表提取原指针和字段。空字节列表使用既有 `UCharArray.full_empty` 保留零长数组语义，非空字节列表复用原 nonnull 与 full 资源。长度、尾部安全性、容量界均由既有定义推出。

本组没有新增或改写公共 helper；group_worker_lib 的两个既有导入保持原样。

开发检查共 7 次，其中失败 5 次、通过 2 次。第一次通过使用临时 Abort 观察中间状态；最后一次通过的是完整 Qed 证明。失败修正分别涉及 Intros 已消费 pure fact 后重复 Intros_p、空间资源需要逐项 cancel（含一次 Show 诊断重跑）、纯容量目标归一化（含一次 Show 诊断重跑）。最后使用重复进度 cancel 和显式 Zlength_nil rewrite，避免 simpl 提前展开 Z 加法。未改 annotation、契约或模型。

已停止 formal/report 写入，等待 controller finalize 验收。
