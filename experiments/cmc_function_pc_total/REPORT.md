# cmc_concrete_function_pc_total.c：C* → QCP

两个运行时函数均已迁移并完成验证。源 C* 证明重放通过；QCP run `cmc_function_pc_total_migration-20261016090222` 为 `done`，final-check `passed`。去除标注与接入 helper 声明后，运行时 token 与源程序一致，复用的 ABI 和公共库哈希未变。

完成 **12 条顶层手工义务、16 个 split**，另有 **11 条自动 witness 以 `Admitted` 导出**。手工证明与新增库没有 Admitted/Axiom/Parameter。自动结果仍依赖 QCP 自动层，不能将全部结果称为独立内核证明证书。

## 产物与契约

- [标注 C](/Users/nizitong/QCP/qcp-binary-democases/QCP_examples/QCP_demos_human/cmc_function_pc_total_migration.c)
- [手工证明](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_function_pc_total_migration_proof_manual.v)
- [工作量明细](metrics/effort.json)、[语义审计](metrics/semantic-audit.json)、[helper 契约核对](metrics/helper-contract-audit.json)
- [C* 重放](metrics/cstar-verification.json)、[QCP controller](logs/qcp-controller/controller_state.json)、[目标快照](target/manifest.json)

`cmc_function_prefix_total` 保留原程序上下文和函数链表、wf、结构安全、index 与剩余链表长度等式、计数 representability 和完整 readiness，返回精确 `cm_function_prefix p functions (target-index)` 及 i32 界。`cmc_function_pc_total` 保留完整 code-ready 和资源，返回精确 `cm_function_pc p target` 及 i32 界。

`target` 保持任意 signed long long，未添加函数编号合法范围。目标为负数或超过函数数时，按原模型递归到链表结尾；数学 `target-index` 使用 Z，不增添运行时减法或溢出前提。既有 `cmc_function_code_count` helper 契约与 counts 已验证版本规范化后逐字相同。

完整迁移四个 readiness 定义。源条件中的 `ilength (cm_emit_stmt ...)` 根据原 C* 的无条件定理 `cm_stmt_code_length` 归一化为已有 `cm_stmt_code_count`，原例在 `cmc_concrete_function_ready.c` 中亦使用该改写。这里验证的是计数形式的 QCP 契约；未新增完整 emitter 语义及该桥接定理的 Rocq 重证。其源代码和 C* 重放证据保留于基线。没有删除 readiness 的其他合取项。

沿用 counts 的全称 `cm_lookup_policy` 与 `cm_codegen_obligations` 参数化边界，四项 emitter/TVM admissibility 条件完整保留。源实例及限制见 [counts 报告](../cmc_counts/REPORT.md)。本例没有补出具体 TVM 实例化或整个编译保持性定理。

## Annotation 与 proof 工作量

按最终非空、非纯注释物理行统计，包含声明/Proof/Qed 包装，排除生成 VC 文本与未采用 Abort 草稿；单独的注释结束符不计 annotation。行数表示产物规模，不表示人工工时或工具效率。

| 最终规模 | C* | QCP |
|---|---:|---:|
| 两函数 specification | 42 | 6 |
| 函数体 annotation | 0 | 63 |
| 既有 helper 接入 annotation | 0（源 include） | 3 |
| annotation 含接入 | 0 | 66 |
| specification + annotation 含接入 | 42 | 72 |
| 案例 proof | 403 | 263 |
| 本源文件公共 proof／目标新增公共 proof | 96 | 80 |

| 函数 | C* spec | C* ann | C* inline proof | QCP spec | QCP ann | QCP case proof |
|---|---:|---:|---:|---:|---:|---:|
| `cmc_function_prefix_total` | 29 | 0 | 245 | 3 | 37 | 177 |
| `cmc_function_pc_total` | 13 | 0 | 116 | 3 | 26 | 86 |

QCP 案例 proof 包括证明体 179 行及声明/Proof/Qed 包装 84 行。词法 token、字符数和标注条目另见 [source-text-size.json](metrics/source-text-size.json)、[annotation-entry-counts.json](metrics/annotation-entry-counts.json) 及 effort.json。源文件公开前缀界引理及构造器计入公共 proof，私有事实组合等 helper 计案例 proof，避免重复。另需的四个源 readiness 定义共 50 行，另有 cm_temp_offset 定义 10 行，见 source-readiness-definitions.json；此前源导入支持的历史开发成本未知。

## 公共依赖增量

目标新增定义 **5 项／37 行**，新增公共引理 **8 条／80 行**。公共导入和作用域 5 行，公共配置 0 行另列。C 层 Extern 36 行，Coq 导入 1 行另列。

实际复用 counts 的计数、wf、representability 和上下文库，以及 layout/copy-bytes 的类型、AST、表示和基础模型。此前已付成本不再次累计；实际 selected dependency snapshot 与基线哈希一致。没有导入旧案例的 auto/manual 函数证明。新增引理是否在当前 manual 中实际引用，见 [shared-helper-usage.json](metrics/shared-helper-usage.json)。

## 验证与时间

C* 在隔离源码副本重放，exit 0，verification_conditions/axioms/strategies 为空，用时 69.933 秒。QCP 完成标注验收、依赖准备、VC 审核、分组证明、合并检查、正式写回与终检；两函数均有已检查义务覆盖。未采用的 split 草稿共 2 个，其顶层目标均有完成证明。

QCP run 墙钟时间 21.84 分钟，包含编写、调度、检查与等待。不能与已有 C* 成品的重放时间作速度比较；历史作者工时和无法独立测量的活跃工时记 null。本例在阅读既有证明后迁移，也不是从零公平对比实验。过程与失败/修正记录见 [process-notes.json](metrics/process-notes.json)。
