# leaf_sizeof 证明计量

完成 4 个顶层 VC 和 7 个 split goal；顶层全部使用 aggressive_pre_process，再按实际分支顺序仅以 Goal_apply 应用相应 split lemma。

- development：11 次，其中 10 次失败、1 次通过；失败中 3 次仅加入 Show 获取证明状态。
- debug：0 次。
- exact group-check：1 次，通过。
- 新增 public helper：0；新增 local helper：0；新增 import：0；group_worker_lib 未修改。

修复原因：Intros 已自动提取节点非空事实和 payload 合取，因此删除重复 Intros_p 并显式 destruct 合取；aggressive_pre_process 先生成 spatial 分支，调整 Goal_apply 顺序；返回分支显式展开 leaf code 并归约 Z.eqb；split_pure_spatial 后统一 sepcon 结合方向以完成字段及 emitter 资源消去；用 Z.eqb 消除 string_scope 下 =? 的歧义；纯等式已由 LLM_pre_process 闭合，删除冗余后续 tactic。

未发现 annotation/specification gap。交付后停止写入，最终接纳由主任务 finalize-delivery 执行。
