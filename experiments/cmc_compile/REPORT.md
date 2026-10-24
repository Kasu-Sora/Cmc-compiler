# cmc_compile：C* → QCP 迁移完成

2026-10-21 完成。原 18 项模拟不变量已在成功执行的全部可达注解状态上建立；`cmc_preservation`、原 `cmc_compile_success_bridge` 及实际 C 函数 `cmc_compile` 均已验证。QCP run `cmc_compile_migration-20261019230022` 最终状态为 `done`，final-check 于 UTC 2026-10-20 17:07:11 通过。

## 验证结果与契约

- 原 C* `cmc.c` 完整重放通过，耗时 1040.281 秒；不是只通过编译或复用旧验收结论。
- 22 批、198 个新增数学公共模块均完成编译、逐条假设审计及独立内核检查；最终批 38 条定理假设闭合，独立 coqchk 用时 313.308 秒。198 个模块全部进入顶层依赖闭包。
- 顶层 9 条手工 VC（6 entail、3 return）和 3 条空间拆分目标完成。4 个证明组、父级合并检查及 main-root 最终检查全部通过；重新符号执行确认生成目标新鲜且一致。
- 5 个调用契约与此前已验证实现逐字一致。运行时代码 token、结构体 ABI、518 个源文件和 185 个先前目标文件的冻结哈希保持不变。
- 保留成功／容量不足两分支、原所需长度、entry=0／-1、程序堆所有权、零容量缓冲区及精确输出前缀与未写尾部。成功分支实际应用原成功桥，量化真实源终止和对象解码，得出相同输入、输出、退出状态的 TVM 终止。

目标实现与证明：[标注 C](target/cmc_compile_migration.c)、[手工证明](target/cmc_compile_migration_proof_manual.v)、[案例公共定义／引理](target/cmc_compile_migration_lib.v)。语义审计：[最终契约审计](metrics/final-contract-audit.json)、[保持性定理对照](metrics/preservation-contract-audit.json)。

## Annotation 与 proof 工作量

口径为去空行、去注释的物理行；proof 含定理陈述及 Proof/Qed。自动生成的 VC 展开文本不计手写 proof。QCP 计数排除纯结束注释分隔符；源属性按既有 C* 语法区域计量。长行排版会影响数字，不能用行数直接推断人工效率。

| 类别 | C* | QCP |
|---|---:|---:|
| 顶层 specification | 12 | 4 |
| 函数内 annotation | 2 | 147 |
| specification + annotation | 14 | 151 |
| 案例私有 proof | 499 | 161 |
| 复制已验证 helper 契约的接入标注 | 独立于本函数计量 | 36 |
| Extern／Import 接入声明 | 独立于本函数计量 | 60 + 1 |

C* 私有 proof 为 435 行 inline + 64 行私有支持；`cmc_compile_success_bridge` 的 42 行公开证明另列，getter 3 行、范围外工具支持 29 行不混入私有 proof。QCP 的 147 行包括 6 个 Assert 和 5 个 where；接入 helper 契约后 specification/annotation 共 187 行。C* 的 inline proof 与 QCP 的中间 Assert 将部分工作放在不同类别，因此不以 499/161 单项作效率结论。详见可重放的 [最终区域计量](metrics/final-effort.json)。

## 新增公共依赖成本

本表只计此前 30 个实现单元及六项 readiness 支持之外的新增内容。

| 独立类别 | 定义数／行数 | 定理数 | proof 行数 |
|---|---:|---:|---:|
| 源／TVM 语义及保持性公共支持，22 批 198 模块 | 494 / 1998 | 1061 | 8165 |
| 顶层案例堆包装及公共引理 | 11 / 76 | 5 | 112 |
| 新增合计 | 505 / 2074 | 1066 | 8277 |

数学支持 proof 的 8165 行细分为定理 7950、自动化 213、构造性判定证明 2；自动化含 75 项声明。案例 5 条引理为 2 条代码长度桥和 3 条数组前缀桥；没有新增自动化声明。已有库复用的新增成本为零。逐批明细见 [effort.json](metrics/effort.json)，实际导入见 [模块使用清单](metrics/public-module-import-usage.json)。

源侧另提供 [保守词法依赖切片](metrics/source-dependency-slice.json)：扣除先前案例闭包及顶层文件后，451 项定义／8710 行、2823 个 proof 声明／91199 行。它包含词法引用可能带入的未使用内容，不是精确最小证明闭包，也不是历史人工成本；完整源／目标公共成本效率比保留为 null。

## 开发与检查过程

保留了原 annotation 前置依赖缺口、控制器恢复补丁及检查证据，没有伪造 VC、手改 controller 状态或放宽契约。补齐依赖后沿同一 owner 恢复。

数学阶段记录 679 次检查调用，其中 404 次开发失败；累计调用用时 8907.848 秒，另有 198 次发布检查、429.183 秒。这些是调用耗时加总，包含重复检查，不等于人工工作时长或并行墙钟总时间。

实现阶段记录 4 次 symexec 修复、2 次 VC 检查报告格式修复；证明 owner 共 26 次 development（21 次失败）、6 次 debug（1 次失败）、3 次主动 exact（全部通过），另有控制器对全部 4 组的验收。无界 `rewrite !eval_addr` 引起的两个耗时子进程经定位后停止，记录为失败检查，使用精确地址实例化后通过。原始日志、owner 报告与最终状态保存在 [controller 快照](logs/qcp-controller/controller_state.json)。

过程证据：[数学检查](metrics/mathematical-process.json)、[证明组](metrics/group-effort.json)、[停止检查记录](metrics/stopped-prover-checks.json)、[工具恢复](controller_recovery/README.md)。历史人工时间未知，未估造。

## 信任边界与覆盖范围

手工证明及新增案例公共库没有新增 Axiom、Parameter 或 Admitted；新增数学证明的实际假设审计闭合。QCP 既有分离逻辑基础仍属于框架信任边界。自动求解有 **12 个原始 VC（7 safety、5 partial-solve）**，导出时加上 **5 个 pure 子义务**，合计 **17 条 Admitted 常量**；它们明确作为可信自动结果，不能称为独立 Rocq 内核证明。

保持性归纳使用更强的内部支持不变量，再投影原 18 项。最终公开保持性与成功桥保留原前提和结论；未额外交付“任意满足弱 18 项的状态”的同名 step/iter 定理。此次完成顶层所需语义链和 C 契约，不宣称全部 254 个源文件及每个辅助导出逐名迁移，也不包含发散保持、双向等价、全部示例推论或独立 TVM C 解释器实现验证。

最终验收后更新 [迁移 skill](/Users/nizitong/.codex/skills/qcp-cstar-migration/SKILL.md)、[迁移清单](../../migration_inventory.csv)、[函数表](../../MIGRATED_FUNCTIONS.md)。此前阶段性报告保存在 [历史快照](history/pre-final/REPORT.md)，其中 pending 状态仅表示当时进度。
