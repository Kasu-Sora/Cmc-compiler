# cmc_concrete_count_context.c：C* → QCP

四个运行时函数均已迁移并完成验证。源 C* 证明重放通过；QCP run `cmc_count_context_migration-20261016020312` 为 `done`，final-check `passed`。去除标注与接入 helper 声明后，运行时 token 与源程序一致，复用的 ABI 和公共库哈希未变。

完成 **8 条顶层手工义务、4 个 split**，另有 **6 条自动 witness 以 `Admitted` 导出**。手工证明与新增库没有 Admitted/Axiom/Parameter。自动结果仍依赖 QCP 自动层，不能将全部结果称为独立内核证明证书。

## 产物与契约

- [标注 C](/Users/nizitong/QCP/qcp-binary-democases/QCP_examples/QCP_demos_human/cmc_count_context_migration.c)
- [手工证明](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_count_context_migration_proof_manual.v)
- [工作量明细](metrics/effort.json)、[语义审计](metrics/semantic-audit.json)、[helper 契约核对](metrics/helper-contract-audit.json)
- [C* 重放](metrics/cstar-verification.json)、[QCP controller](logs/qcp-controller/controller_state.json)、[目标快照](target/manifest.json)

`cm_expr_type_code_context` 保持表达式所有权，将节点类型编码写入原未初始化 int 输出单元，不增添类型有效性前提。另三个包装函数展开已有 program/function context，调用已验证的左右值或语句计数函数，再恢复完整上下文及原纯事实。返回精确模型计数并保留 i32 界；statement 包装保留原 `loop_` 参数。

函数模型仍等于统一全称 `cm_lookup_policy` 下的总查询，未增加 fid 合法范围。所有 wf、representability、struct-safe 和上下文所有权条件均按原契约保留。三个 helper 的接入契约与 counts 已验证版本规范化后逐字相同；本案例不重复证明它们的实现。

沿用 counts 的显式参数化边界：四项 emitter/TVM admissibility 条件通过同一全称 `cm_codegen_obligations` 保留。源实例及限制见 [counts 报告](../cmc_counts/REPORT.md)。本例没有补出具体 TVM 实例化或整个编译保持性定理。

## Annotation 与 proof 工作量

按最终非空、非纯注释物理行统计，包含声明/Proof/Qed 包装，排除生成 VC 文本与未采用 Abort 草稿；单独的注释结束符不计 annotation。行数表示产物规模，不表示人工工时或工具效率。

| 最终规模 | C* | QCP |
|---|---:|---:|
| 四函数 specification | 75 | 12 |
| 函数体 annotation | 16 | 76 |
| 既有 helper 接入 annotation | 0（源 include） | 9 |
| annotation 含接入 | 16 | 85 |
| specification + annotation 含接入 | 91 | 97 |
| 案例 proof | 39 | 98 |
| 本源文件公共 proof／目标新增公共 proof | 0 | 0 |

| 函数 | C* spec | C* ann | C* inline proof | QCP spec | QCP ann | QCP case proof |
|---|---:|---:|---:|---:|---:|---:|
| `cm_expr_type_code_context` | 6 | 0 | 10 | 3 | 13 | 26 |
| `cm_expr_lvalue_count_context` | 23 | 5 | 8 | 3 | 21 | 24 |
| `cm_expr_rvalue_count_context` | 23 | 5 | 8 | 3 | 21 | 24 |
| `cm_stmt_code_count_context` | 23 | 6 | 13 | 3 | 21 | 24 |

QCP 案例 proof 包括证明体 62 行及声明/Proof/Qed 包装 36 行。词法 token、字符数和标注条目另见 [source-text-size.json](metrics/source-text-size.json)、[annotation-entry-counts.json](metrics/annotation-entry-counts.json) 及 effort.json。源文件未新增公共定义或引理；源已导入的上下文开合等历史支持成本未知，不将其说成从零免费。

## 公共依赖增量

目标新增定义 **0 项／0 行**，新增公共引理 **0 条／0 行**。公共导入和作用域 1 行，公共配置 0 行另列。C 层 Extern 47 行，Coq 导入 1 行另列。

实际复用 counts 的计数、wf、representability 和上下文库，以及 layout/copy-bytes 的类型、AST、表示和基础模型。此前已付成本不再次累计；实际 selected dependency snapshot 与基线哈希一致。没有导入旧案例的 auto/manual 函数证明。新增引理是否在当前 manual 中实际引用，见 [shared-helper-usage.json](metrics/shared-helper-usage.json)。

## 验证与时间

C* 在隔离源码副本重放，exit 0，verification_conditions/axioms/strategies 为空，用时 39.890 秒。QCP 完成标注验收、依赖准备、VC 审核、分组证明、合并检查、正式写回与终检；四函数均有已检查义务覆盖。未采用的 split 草稿共 0 个，其顶层目标均有完成证明。

QCP run 墙钟时间 18.87 分钟，包含编写、调度、检查与等待。不能与已有 C* 成品的重放时间作速度比较；历史作者工时和无法独立测量的活跃工时记 null。本例在阅读既有证明后迁移，也不是从零公平对比实验。过程与失败/修正记录见 [process-notes.json](metrics/process-notes.json)。
