#!/usr/bin/env python3
"""Publish measured results only after successful verification and semantic audit."""
from pathlib import Path
import json
R=Path(__file__).resolve().parent
E=json.loads((R/'metrics/effort.json').read_text())
A=json.loads((R/'metrics/semantic-audit.json').read_text())
assert E['verification']['phase']=='done' and E['verification']['qcp_final_check']['status']=='passed'
assert A['final_verification']['status']=='passed'
C=E['counts']['cstar'];Q=E['counts']['qcp'];N=E['entries']
run=json.loads((R/'metrics/run.json').read_text())['run_id']
text=f'''# cmc_concrete_emit_data.c：C* → QCP

完整迁移唯一运行时函数 `cmc_emit_data`。C* 原证明隔离重放通过；QCP run `{run}` 为 done，final-check passed。运行时 token、ABI 与复用依赖哈希保持不变。

## 契约与复用

按原顺序写入八个零字节、全局变量字节和字符串字节。Require 与 Ensure 都保留原来的七项纯条件：globals 安全性、完整 data-globals-wf、strings 安全性、两项大小非负、合计容量约束以及 INT_MAX 上界。保留全局链表与字符串链表（含源字节数组）的所有权。

入口为空初始化前缀加整个未初始化目标区；出口初始化内容严格为 `((zeros 8 ++ cm_globals_bytes structs globals) ++ cm_strings_bytes strings)`，返回值和末端严格为 `(8 + globals_size) + strings_size`，其后仍为未初始化缓冲区。`zeros 8` 对应原 `ireplicate 8 0`；未新增 data 非空或额外程序合法性条件。

复用已经验证的 globals、strings、counts、layout、copy-bytes 和 word 公共库；接入的三个 helper 契约与已验证 C 文件规范化后逐字一致：cmc_write_zeroes、cmc_emit_globals、cmc_emit_strings。它们的实现证明不重复计入本次成本，旧 auto/manual 不导入。具体数据区契约未被替换成额外要求完整 program-wf 或 codegen 条件的模型。

## 验证与信任边界

完成 {N['manual_top_level']} 条顶层手工义务、{N['manual_splits']} 个 split，剩余手工义务为零。另有 {N['automatic_witnesses']} 条自动 witness 以 Admitted 导出，依赖 QCP 自动层；手工证明及新增库无 Admitted/Axiom/Parameter。未采用的 Abort split 草稿 {len(E['unused_split_drafts_aborted'])} 个，若存在，其顶层目标均已按整体路线证明。

C* 重放 exit 0，verification_conditions/axioms/strategies 均为空，用时 {E['verification']['cstar']['verification_seconds']:.3f} 秒。QCP 完成标注验收、依赖准备、独立 VC 审查、分组证明、合并全量检查、正式写回和终检。本例是具体数据区组合生成证明，不代表整个 CMC/TVM 编译保持性迁移完成。

## 工作量

以下按非空、非纯注释物理行计数。Proof 含声明和 Proof/Qed 包装，排除自动生成 VC 文本与未采用草稿。C* proof 块计入 proof，where 计 annotation；已有依赖计零新增。行数是最终规模，不是人工工时。

| 项目 | C* | QCP |
|---|---:|---:|
| Specification | {C['specification']} | {Q['specification']} |
| 函数体 annotation | {C['annotation']} | {Q['annotation']} |
| helper 接入 annotation | 0（include） | {Q.get('integration_helper_specification',0)} |
| Annotation 含接入 | {C['annotation']} | {Q['total_annotation_with_integration']} |
| Specification + annotation 含接入 | {C['specification_plus_annotation']} | {Q['specification_plus_annotation_with_integration']} |
| 案例 proof | {C['case_proof']} | {Q['case_proof']} |
| 源文件公共 proof／目标新增公共 proof | {C['exported_shared_proof_closure']} | {Q['new_common_proof']} |
| 上述 proof 合计 | {C['proof_including_shared']} | {Q['proof_including_shared']} |

C* 案例 proof 含内嵌 {C['inline_proof']} 行及私有支持 {C['private_case_proof_support']} 行。QCP 案例 proof 含证明体 {E['proof_body_lines']} 行、声明/包装 {E['proof_wrapper_lines']} 行。

公共依赖新增：定义 **{len(N['new_model_declarations'])} 项／{Q['new_common_definitions']} 行**，引理 **{len(N['new_helpers'])} 条／{Q['new_common_proof']} 行**。公共 import/作用域 {Q.get('new_common_imports_or_scopes',0)} 行、公共自动化/配置 {Q.get('new_common_automation_or_configuration',0)} 行另列；C Extern {Q.get('external_declarations',0)} 行、Coq import {Q.get('coq_imports',0)} 行另列。具体引理引用和阶段增量见 shared-helper-usage.json 与 effort.json。

过程中的 symexec 失败、同一标注 attempt 内修订、proof 开发检查与最终验收分别记录在 process-notes.json；不能由 annotation retry round 数为零推断一次即通过。中间断言所需的纯事实及资源转换均由实际生成义务证明，未作为新假设直接接受。

QCP run 墙钟 {E['process']['timing']['run']['elapsed_seconds']/60:.2f} 分钟，包含编辑、调度、工具和等待；不能与 C* 成品重放时间比较工具速度。历史作者工时、无法独立测量的活跃时间均记 null。此实验读取了原证明，属于迁移规模对照，不是从零公平效率实验。

## 产物与审计

- [标注 C](/Users/nizitong/QCP/qcp-binary-democases/QCP_examples/QCP_demos_human/cmc_emit_data_migration.c)
- [手工证明](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_data_migration_proof_manual.v)
- [公共库](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_data_migration_lib.v)
- [工作量明细](metrics/effort.json)、[契约审计](metrics/semantic-audit.json)、[helper 契约核对](metrics/helper-contract-audit.json)
- [过程记录](metrics/process-notes.json)、[C* 重放](metrics/cstar-verification.json)、[QCP 终检](logs/qcp-controller/controller_state.json)
- [冻结产物](target/manifest.json)、[公共引理引用](metrics/shared-helper-usage.json)
'''
(R/'REPORT.md').write_text(text)
print(R/'REPORT.md')
