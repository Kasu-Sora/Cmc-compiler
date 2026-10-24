# sizeof_value 证明工作记录

完成 4 个 assigned top-level VC 与 4 个 aggressive split goals。纯目标使用既有类型编码、类型大小一致性引理；空间目标展开并重建 cm_program_context_rep。

- Development 检查：3 次，失败 2 次。
- Debug 检查：3 次，失败 2 次。
- Exact 检查：1 次，失败 0 次。
- 合计：7 次检查，4 次失败。

修复原因：首次 development 中单次 cancel 仅消去一个空间资源，改为 repeat progress cancel；debug 中 Intros 使用 s 与 tactic 的字符串临时变量冲突，改用 structs_ptr/globals_ptr/strings_ptr；另一 debug 尝试省略 unfold 后没有 existential witnesses，恢复展开并显式引入；第二次 development 暴露 aggressive_pre_process 先生成 spatial 分支，再生成 pure 分支，按该顺序调整 Goal_apply。

没有新增或复制公共引理，也没有新增本地 helper 或 import；group_worker_lib 保持原内容。没有发现 annotation/specification gap。
