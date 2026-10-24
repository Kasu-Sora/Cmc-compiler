#!/usr/bin/env python3
"""Render audited, completed migration results."""
import json
from pathlib import Path
R=Path(__file__).resolve().parent
E=json.loads((R/'metrics/effort.json').read_text());A=json.loads((R/'metrics/semantic-audit.json').read_text())
assert E['verification']['phase']=='done' and E['verification']['qcp_final_check']['status']=='passed' and A['final_verification']['status']=='passed'
C=E['counts']['cstar'];Q=E['counts']['qcp'];N=E['entries'];run=json.loads((R/'metrics/run.json').read_text())['run_id']
text=f'''# cmc_concrete_emit_globals.c：C* → QCP

完整迁移该文件唯一运行时函数 `cmc_emit_globals`。C* 原证明重放通过；QCP run `{run}` 为 done，final-check passed。去除标注及 helper 接入声明后，运行时 token 与原源码一致，复用的 ABI 和公共依赖哈希不变。

完成 **{N['manual_top_level']} 条顶层手工义务、{N['manual_splits']} 个 split**，另有 **{N['automatic_witnesses']} 条可信自动 witness 以 Admitted 导出**。手工证明和新增库无 Admitted/Axiom/Parameter。自动结果依赖 QCP 自动层，不能称全部义务均有独立内核证明证书。

## 产物与原契约

- [标注 C](/Users/nizitong/QCP/qcp-binary-democases/QCP_examples/QCP_demos_human/cmc_emit_globals_migration.c)
- [手工证明](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_globals_migration_proof_manual.v)
- [公共定义与引理](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_globals_migration_lib.v)
- [工作量明细](metrics/effort.json)、[契约审计](metrics/semantic-audit.json)、[helper 契约审计](metrics/helper-contract-audit.json)、[目标快照](target/manifest.json)
- [C* 重放](metrics/cstar-verification.json)、[QCP 验证记录](logs/qcp-controller/controller_state.json)

保留原 globals safety、逐节点 global wellformedness、cursor 非负、容量及总空间条件，恢复完整全局变量链表。输出严格等于原 prefix 追加 `cm_globals_bytes structs globals`，未初始化余段从新 cursor 开始；返回精确 `cursor + cm_rep_globals_size globals`。没有添加非空 data 或其他更强前提。空链表保持原缓冲区；已初始化字符写一个低字节，其他已初始化标量写八个小端字节，未初始化对象按原大小写零。

完整 global wellformedness 复用 counts 定义，包括标量类型限制、count 条件、对象大小界、初始化值 signed64 条件及指针初始化必须为零。新 `cm_data_globals_wf` 仅是原递归逐节点合取。保持所有运行时字段读取、long long 到 int 的 size 转换和递归调用；大小界来自原安全/合法性条件。

四个 helper 的接入契约与以前已验证版本规范化后逐字相同：layout 的 `cmc_code_slot_size`，以及 `cmc_write_char`、`cmc_write_word`、`cmc_write_zeroes`。不重复证明其实现，不导入旧案例 auto/manual 文件。

counts 中初始化字节的 map/seq/幂除法模型与 word 的逐字节连续除法模型分别保留，通过新的已检查引理连接，覆盖负数。字符低字节复用 tower_u8，补零复用已有 zeros/repeat 约定。没有引入新的未证明 emitter 参数或假定编码等式。本例证明具体全局数据区生成，仍不代表整个 CMC/TVM 编译保持性已完成。

## Annotation 与 proof 工作量

非空、非纯注释物理行计数；proof 包含声明和 Proof/Qed 包装，排除自动生成 VC 文本及未采用 Abort 草稿。源码内部 C* proof 块计入 proof，where 注释计 annotation；不因排版位置改变分类。行数是最终产物规模，不是人工工时或工具效率。

| 最终规模 | C* | QCP |
|---|---:|---:|
| Specification | {C['specification']} | {Q['specification']} |
| 函数体 annotation | {C['annotation']} | {Q['annotation']} |
| 既有 helper 接入 annotation | 0（include） | {Q.get('integration_helper_specification',0)} |
| Annotation 含接入 | {C['annotation']} | {Q['total_annotation_with_integration']} |
| Specification + annotation 含接入 | {C['specification_plus_annotation']} | {Q['specification_plus_annotation_with_integration']} |
| 案例 proof | {C['case_proof']} | {Q['case_proof']} |
| 源文件公共 proof／目标新增公共 proof | {C['exported_shared_proof_closure']} | {Q['new_common_proof']} |
| 上述 proof 合计 | {C['proof_including_shared']} | {Q['proof_including_shared']} |

C* 案例 proof 为内嵌 {C['inline_proof']} 行与私有支持 {C['private_case_proof_support']} 行之和；这些私有 helper 不因位于函数体外而漏计。QCP 案例 proof 包含证明体 {E['proof_body_lines']} 行、声明/Proof/Qed 包装 {E['proof_wrapper_lines']} 行。词法 token、字符数和标注条目见 source-text-size.json、annotation-entry-counts.json 及 effort.json。

## 公共依赖新增成本

新增公共定义 **{len(N['new_model_declarations'])} 项／{Q['new_common_definitions']} 行**；新增公共引理 **{len(N['new_helpers'])} 条／{Q['new_common_proof']} 行**。公共 import/作用域 {Q.get('new_common_imports_or_scopes',0)} 行、公共自动化/配置 {Q.get('new_common_automation_or_configuration',0)} 行另列。C 层 Extern {Q.get('external_declarations',0)} 行、Coq import {Q.get('coq_imports',0)} 行另列。

直接复用 counts/layout/copy-bytes 与 word 公共模型和证明，按已付成本计零新增；实际构建依赖快照及基线哈希已核对。源额外 `cm_data_globals_wf` 定义见 [source-additional-definitions.json](metrics/source-additional-definitions.json)，历史导入库开发工时未知。新增 helper 名单、引用情况和 annotation/proving 阶段增量见 [shared-helper-usage.json](metrics/shared-helper-usage.json) 和 effort.json。

## 验证与过程

C* 隔离重放 exit 0，verification_conditions/axioms/strategies 为空，用时 {E['verification']['cstar']['verification_seconds']:.3f} 秒。QCP 经标注验收、依赖准备、独立 VC 审查、分组证明、合并全量检查、正式写回与终检，剩余手工义务为零。未采用 split 草稿 {len(E['unused_split_drafts_aborted'])} 个，其整体顶层目标均已完成。

QCP run 墙钟时间 {E['process']['timing']['run']['elapsed_seconds']/60:.2f} 分钟，包括编写、调度、检查和等待，不能与现成 C* 证明重放时间比较工具速度。历史作者工时和无法独立测量的活跃工时记 null。本例阅读了原证明，属于迁移实验，不是从零公平效率对比。失败检查、修正及验证阶段证据见 [process-notes.json](metrics/process-notes.json) 和 controller timing_summary.json。
'''
(R/'REPORT.md').write_text(text);print(R/'REPORT.md')
