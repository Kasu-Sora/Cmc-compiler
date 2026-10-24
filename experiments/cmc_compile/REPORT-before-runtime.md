# cmc_compile：十二项模拟支持不变量已验证，顶层未完成

本轮补齐原剩余 11 项中的 **5 项**：static-valid、budget、generation-safe、static-bases、short-ready。累计 12/18 项有具体初始、逐步及任意步保持性证明。详见 [第四批](structural/README.md) 和 [第五批](transport/README.md)。

**仍缺 6 项：layout-ready、runtime、type、tagged-valid、code-layout、完整 target-sim。cmc_preservation、原成功桥及顶层 QCP 尚未完成；skill 未更新。** 没有新增 C Require 或假设未证的保持性定理。

| 工作量 | C* 顶层基线 | QCP 顶层最终值 |
|---|---:|---:|
| Specification | 12 行 | 未完成 |
| Annotation | 2 行/2 条 | 未完成 |
| 案例 proof | 499 行 | 未完成 |
| 成功桥公共 proof | 42 行 | 未完成 |
| 完整外部保持性依赖 | 未完成统计 | 未完成 |

第五批新增公共成本：8 定义、40 引理，定义 12 行、proof 191 行（含 Ltac 33 行）。第四、五批合计新增 40 定义、141 引理，定义 106 行、proof 839 行。五批累计 391 定义、363 引理，定义 1544 行、proof 1960 行。公共依赖与顶层案例成本分列；完整可比成本和最终比率仍为 null。

第五批 40 条假设审计全部闭合，独立 coqchk 通过（301.31 秒），2 个正式库编译通过。第四批 101 条闭合审计、独立内核及 7 个正式库编译亦已通过。原 C* 顶层重放此前通过（约 1040 秒）。原契约、前批证明、skill、迁移成功清单未改；顶层 VC 尚未生成。
