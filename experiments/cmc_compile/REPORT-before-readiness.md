# cmc_compile：十三项模拟支持不变量已验证，顶层未完成

本轮补齐原剩余 11 项中的 **6 项**：static-valid、budget、generation-safe、static-bases、short-ready、runtime。累计 **13/18** 项具备具体初始、实际逐步和任意步数保持性证明。详见 [第四批](structural/README.md)、[第五批](transport/README.md)、[第六批](runtime/README.md)。

**仍缺 5 项：layout-ready、type、tagged-valid、code-layout、完整 target-sim。cmc_preservation、原成功桥及顶层 QCP 尚未完成；skill 未更新。** 第七批 readiness 正在开发，其结果尚未计入已验证总数。

| 工作量 | C* 顶层基线 | QCP 顶层最终值 |
|---|---:|---:|
| Specification | 12 行 | 未完成 |
| Annotation | 2 行/2 条 | 未完成 |
| 案例 proof | 499 行 | 未完成 |
| 成功桥公共 proof | 42 行 | 未完成 |
| 完整外部保持性依赖 | 未完成统计 | 未完成 |

第六批新增公共依赖：30 定义、134 引理，定义 66 行、proof 862 行（含 Ltac 37 行）。本轮第四至第六批合计 70 定义、275 引理，定义 172 行、proof 1701 行。六批累计 421 定义、497 引理，定义 1610 行、proof 2822 行。公共依赖与顶层案例成本分列；完整可比成本和最终比率仍为 null。

第六批 134 条假设审计全部闭合，独立 coqchk 通过（302.15 秒），12 个正式库编译通过。原 C* 顶层重放此前通过（约 1040 秒）。未修改原契约、前批证明、skill 或迁移成功清单。计划文件有外部并发新增的一条函数索引链接，已保留并记录哈希差异；不影响证明或契约。顶层 VC 尚未生成。
