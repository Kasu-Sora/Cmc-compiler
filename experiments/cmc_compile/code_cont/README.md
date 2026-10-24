# 第十二批：完整代码布局不变量

已补齐 V/C 全部分派，与已验证 Start/R/L/S/Done 分支组合，证明 `cm_task_layout` 的初始、实际一步和任意步数保持性。沿成功源执行，原 18 项模拟不变量中的 17 项现已完成。

38 条新定理的 `Print Assumptions` 全部为 `Closed under the global context`，独立 `coqchk` 通过（310.44 秒），11 个公共库已在 QCP 正式目录重新编译通过。未新增 Axiom、Admitted、Parameter 或 C 前提。内核日志列出的导入环境公理不等于这些新定理依赖公理；逐定理依赖以假设审计为准。

新增公共成本：1 定义（2 行）、38 引理（336 行）及 4 行 Ltac，共 proof 340 行。C/annotation 增量为 0。累计公共库 479 定义、755 引理，定义 1931 行、proof 4804 行。所有 helper 均计入；已有公共定义复用的增量为 0。

C* 同名参考声明计数为 proof constructor 913 行、声明脚手架 453 行；这只是匹配子集，未覆盖完整依赖闭包，不能与目标总行数计算效率比率。历史开发时间与完整可比成本仍为 null。

仍缺完整 `cm_task_target_sim` 的逐步保持性，以及由其导出的原 `cmc_preservation`、成功桥与顶层 QCP 验证。skill 按用户要求保持不变。

证据：[检查点](metrics/checkpoint.json)、[成本](metrics/effort.json)、[源参考子集](metrics/source-reference-cost.json)、[全部检查](metrics/checks.json)、[剩余义务](metrics/remaining-obligations.json)。
