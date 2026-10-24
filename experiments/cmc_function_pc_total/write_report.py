#!/usr/bin/env python3
"""Render only audited and fully verified migration results."""
import json
from pathlib import Path
R=Path(__file__).resolve().parent
E=json.loads((R/'metrics/effort.json').read_text());S=json.loads((R/'metrics/semantic-audit.json').read_text())
assert E['verification']['phase']=='done' and E['verification']['qcp_final_check']['status']=='passed'
assert S['final_verification']['status']=='passed'
C=E['counts']['cstar'];Q=E['counts']['qcp'];N=E['entries'];run=json.loads((R/'metrics/run.json').read_text())['run_id']
rows=[]
for src in E['source_effort']['function_counts']:
 t=E['target_per_function'][src['function']]
 rows.append(f"| `{src['function']}` | {src['specification']} | {src['annotation']} | {src['inline_proof']} | {t['specification']} | {t['annotation']} | {t['case_proof']} |")
text=f'''# cmc_concrete_function_pc_total.c：C* → QCP

两个运行时函数均已迁移并完成验证。源 C* 证明重放通过；QCP run `{run}` 为 `done`，final-check `passed`。去除标注与接入 helper 声明后，运行时 token 与源程序一致，复用的 ABI 和公共库哈希未变。

完成 **{N['manual_top_level']} 条顶层手工义务、{N['manual_splits']} 个 split**，另有 **{N['automatic_witnesses']} 条自动 witness 以 `Admitted` 导出**。手工证明与新增库没有 Admitted/Axiom/Parameter。自动结果仍依赖 QCP 自动层，不能将全部结果称为独立内核证明证书。

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
| 两函数 specification | {C['specification']} | {Q['specification']} |
| 函数体 annotation | {C['annotation']} | {Q['annotation']} |
| 既有 helper 接入 annotation | 0（源 include） | {Q.get('integration_helper_specification',0)} |
| annotation 含接入 | {C['annotation']} | {Q['total_annotation_with_integration']} |
| specification + annotation 含接入 | {C['specification_plus_annotation']} | {Q['specification_plus_annotation_with_integration']} |
| 案例 proof | {C['case_proof']} | {Q['case_proof']} |
| 本源文件公共 proof／目标新增公共 proof | {C['exported_shared_proof_closure']} | {Q['new_common_proof']} |

| 函数 | C* spec | C* ann | C* inline proof | QCP spec | QCP ann | QCP case proof |
|---|---:|---:|---:|---:|---:|---:|
{chr(10).join(rows)}

QCP 案例 proof 包括证明体 {E['proof_body_lines']} 行及声明/Proof/Qed 包装 {E['proof_wrapper_lines']} 行。词法 token、字符数和标注条目另见 [source-text-size.json](metrics/source-text-size.json)、[annotation-entry-counts.json](metrics/annotation-entry-counts.json) 及 effort.json。源文件公开前缀界引理及构造器计入公共 proof，私有事实组合等 helper 计案例 proof，避免重复。另需的四个源 readiness 定义共 50 行，另有 cm_temp_offset 定义 10 行，见 source-readiness-definitions.json；此前源导入支持的历史开发成本未知。

## 公共依赖增量

目标新增定义 **{len(N['new_model_declarations'])} 项／{Q['new_common_definitions']} 行**，新增公共引理 **{len(N['new_helpers'])} 条／{Q['new_common_proof']} 行**。公共导入和作用域 {Q.get('new_common_imports_or_scopes',0)} 行，公共配置 {Q.get('new_common_automation_or_configuration',0)} 行另列。C 层 Extern {Q.get('external_declarations',0)} 行，Coq 导入 {Q.get('coq_imports',0)} 行另列。

实际复用 counts 的计数、wf、representability 和上下文库，以及 layout/copy-bytes 的类型、AST、表示和基础模型。此前已付成本不再次累计；实际 selected dependency snapshot 与基线哈希一致。没有导入旧案例的 auto/manual 函数证明。新增引理是否在当前 manual 中实际引用，见 [shared-helper-usage.json](metrics/shared-helper-usage.json)。

## 验证与时间

C* 在隔离源码副本重放，exit 0，verification_conditions/axioms/strategies 为空，用时 {E['verification']['cstar']['verification_seconds']:.3f} 秒。QCP 完成标注验收、依赖准备、VC 审核、分组证明、合并检查、正式写回与终检；两函数均有已检查义务覆盖。未采用的 split 草稿共 {len(E['unused_split_drafts_aborted'])} 个，其顶层目标均有完成证明。

QCP run 墙钟时间 {E['process']['timing']['run']['elapsed_seconds']/60:.2f} 分钟，包含编写、调度、检查与等待。不能与已有 C* 成品的重放时间作速度比较；历史作者工时和无法独立测量的活跃工时记 null。本例在阅读既有证明后迁移，也不是从零公平对比实验。过程与失败/修正记录见 [process-notes.json](metrics/process-notes.json)。
'''
(R/'REPORT.md').write_text(text)
print(R/'REPORT.md')
