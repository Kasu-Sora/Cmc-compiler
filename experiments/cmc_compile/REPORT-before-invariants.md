# cmc_compile：annotation 保持性已验证，完整模拟仍待补齐

第二批 8 个公共 Rocq 模块已完成编译、独立内核检查和 67 条假设审计，并接入 QCP。新增内容包括 85 个 annotation 更新分支、栈擦除/根约束/坐标的单步与迭代保持、存储后指针来源模拟、word 编解码、代码片段取指及基础 TVM 单步支撑。详见 [本批验证与工作量](preservation/README.md)。

**cmc_preservation 和原签名 cmc_compile_success_bridge 尚未完成，顶层 QCP 未验证，skill 未更新。** 通用组合引理已编译，但其完整不变量前提尚未被具体证明；未将这些前提加入原 C 契约。原 18 项模拟不变量中目前闭合四个分量，详见 [剩余义务](preservation/metrics/remaining-obligations.json)。

| 指标 | C* 顶层基线 | QCP 顶层最终成本 |
|---|---:|---:|
| Specification | 12 行 | 未完成 |
| Annotation | 2 行/2 条 | 未完成 |
| 案例 proof | 499 行 | 未完成 |
| 成功桥接公共 proof | 42 行 | 未完成 |
| 完整外部保持性依赖 | 尚未完成匹配统计 | 尚未完成 |

公共增量单列：本批定义 293 行，proof 375 行（349 行引理和 26 行自动化）；50 项定义、67 条引理。两批累计定义 1362 行、proof 745 行，326 项定义、175 条引理。此前库原样复用，不重复算新增成本。没有依据将这些未完成闭包的规模换算为两种工具的难度或时间比率。

C* 原始顶层重放此前已通过（约 1040 秒，验证义务/新增公理/策略均为空），记录在 metrics/cstar-verification.json。本批核对 518 个源文件、185 个先前目标文件和上一批 9 个公共库，哈希均一致。技能、迁移计划及完成清单保持原样。原 controller run/annotation owner 仍保留，待语义闭包完成后继续其正式流程；没有绕过 controller 或制造顶层完成结果。
