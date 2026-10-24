# cmc_compile：十一项模拟支持不变量已验证，顶层仍未完成

本批补齐剩余 11 项中的 **4 项**：静态有效性、临时槽预算、代际安全、静态区域基址。累计原 18 项中的 11 项已有具体初始、逐步及任意步数保持性证明，复用此前 23 个公共库。详见 [第四批验证与成本](structural/README.md)。

**仍缺 7 项：layout-ready、runtime、type、tagged-valid、short-ready、code-layout、完整 target-sim。cmc_preservation、原 cmc_compile_success_bridge 和顶层 QCP 尚未完成；skill 未更新。** 本批支持性质没有替代目标模拟，没有新增 C Require。见 [剩余义务](structural/metrics/remaining-obligations.json)。

| 工作量 | C* 顶层基线 | QCP 顶层最终值 |
|---|---:|---:|
| Specification | 12 行 | 未完成 |
| Annotation | 2 行/2 条 | 未完成 |
| 案例 proof | 499 行 | 未完成 |
| 成功桥公共 proof | 42 行 | 未完成 |
| 完整外部保持性依赖 | 对应统计未完成 | 未完成 |

新增公共成本：32 个定义、101 条引理，定义 94 行、proof 648 行（含 68 行 Ltac）。四批累计 383 个定义、323 条引理，定义 1532 行、proof 1769 行。完整可比依赖成本和最终比率仍为 null。

本批 101 条假设审计闭合，独立 coqchk 通过（313.19 秒），7 个正式公共库编译通过。原 C* 顶层重放此前通过（约 1040 秒），原源码、旧目标、前批公共库及 skill/计划/清单均保持哈希一致。原 controller run 与 annotation owner 保留，顶层 VC 尚未生成。
