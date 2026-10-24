# 第二十二批：完整目标模拟与编译保持性

本批补齐调用者栈帧保存、空／非空参数调用、启动序言、R/V 全部分派及总目标转移；证明原 18 项模拟不变量在成功源执行的任意步成立，推出原 `cmc_preservation` 与 `cmc_compile_success_bridge`。独立内核复检已通过（313.31 秒），16 个正式库编译通过；证据见 `metrics/checkpoint.json`；顶层 C 实现单独由 QCP controller 验证。

公开结论保持原语义合法性、源程序成功终止、对象解码前提与相同输入／输出／退出状态结论。内部使用更强的组合不变量作归纳，再推出原 18 项不变量；没有把额外机器条件加到顶层 C Requires，也没有宣称原 C* 每个内部 helper 都逐名迁移。新增数学库没有 Axiom、Parameter、Admitted 或 Abort；38 条 Print Assumptions 全部闭合。

新增公共成本：16 个模块、2 项定义（20 行）、38 条引理（553 行 proof）。前 21 批复用的增量成本为零；22 批累计 494 定义、1061 引理、1998 行定义、8165 行 proof。顶层 C 标注与手工证明另计，不包含在此成本内。`metrics/effort.json` 是可追溯计数，开发失败及命令耗时保留；历史人工耗时未知。

`metrics/source-reference-cost.json` 只统计本批直接参考的部分 C* 定义／proof constructor，不能作为全部外部依赖成本或计算迁移效率比率。完整可比源依赖工作量仍待统计。

关键文件：

- `target/cmc_target_total_migration_lib.v`：总目标转移、组合不变量的初始／逐步／迭代定理。
- `target/cmc_preservation_complete_migration_lib.v`：原 18 项不变量、原编译保持性及成功桥。
- `metrics/kernel-input-manifest.json`：内核输入源码与 `.vo` 哈希。
- `metrics/checks.json`、`metrics/publication.json`：实际命令、退出码、日志与正式库发布。

顶层 QCP 完整验收之前不更新 migration skill 或迁移成功清单。
