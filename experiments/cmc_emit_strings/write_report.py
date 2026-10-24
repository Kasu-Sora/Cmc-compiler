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
dev=E['process']['notes']['proof_development']['group_development_checks']
checks=sum(x['checks'] for x in dev.values());failures=sum(x['failed'] for x in dev.values())
text=f'''# cmc_concrete_emit_strings.c：C* → QCP

完整迁移唯一运行时函数 `cmc_emit_strings`。C* 原证明隔离重放通过；QCP run `{run}` 为 done，final-check passed。运行时 token、ABI 与复用依赖哈希保持不变。

## 契约与复用

保留 `cm_rep_strings_safe`、cursor 非负、总输出空间和 INT_MAX 容量界。恢复整个源字符串链表及各源字节数组；输出严格等于原 prefix 追加 `cm_strings_bytes strings`，即逐个复制字符串字节并追加一个零字节。返回精确 cursor + cm_rep_strings_size strings，保留剩余未初始化缓冲区。

空链表直接返回原 cursor；空字符串仍写入一个零字节。原契约不要求字符串非空、source/data 无条件非空或额外 string-wf，目标保持相同输入范围。链表表示中的源数组所有权与目标缓冲区保持分离。

复用 layout 的字符串描述符、大小、安全条件与链表表示，counts 的原字节输出模型，以及 copy-bytes 的条件非空谓词。`cmc_copy_bytes` 和 `cmc_write_byte` 接入契约与先前已验证版本规范化后逐字一致；不重复证明其实现，不导入旧案例 auto/manual。源缓冲区的空列表分支保持 emp，接入 copy helper 所需的完整数组表示在证明中处理。

## 验证与信任边界

完成 {N['manual_top_level']} 条顶层手工义务、{N['manual_splits']} 个 split，剩余手工义务为零。另有 {N['automatic_witnesses']} 条自动 witness 以 Admitted 导出，依赖 QCP 自动层；手工证明及新增库无 Admitted/Axiom/Parameter。未采用的 Abort split 草稿 {len(E['unused_split_drafts_aborted'])} 个，若存在，其顶层目标均已按整体路线证明。

C* 重放 exit 0，verification_conditions/axioms/strategies 均为空，用时 {E['verification']['cstar']['verification_seconds']:.3f} 秒。QCP 完成标注验收、依赖准备、独立 VC 审查、分组证明、合并全量检查、正式写回和终检。本例是具体字符串数据区生成证明，不代表整个 CMC/TVM 编译保持性迁移完成。

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

过程：标注阶段首次三项检查均通过，没有标注修订轮次。两组 proof 共执行 {checks} 次开发检查，其中 {failures} 次失败后修正；通过的开发检查中有一次仅为临时 Abort 调试，未当作完成证明。最终两组完整验收和终检均通过。具体修正及 debug 次数见 process-notes.json。

QCP run 墙钟 {E['process']['timing']['run']['elapsed_seconds']/60:.2f} 分钟，包含编辑、调度、工具和等待；不能与 C* 成品重放时间比较工具速度。历史作者工时、无法独立测量的活跃时间均记 null。此实验读取了原证明，属于迁移规模对照，不是从零公平效率实验。

## 产物与审计

- [标注 C](/Users/nizitong/QCP/qcp-binary-democases/QCP_examples/QCP_demos_human/cmc_emit_strings_migration.c)
- [手工证明](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_strings_migration_proof_manual.v)
- [公共库](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_strings_migration_lib.v)
- [工作量明细](metrics/effort.json)、[契约审计](metrics/semantic-audit.json)、[helper 契约核对](metrics/helper-contract-audit.json)
- [过程记录](metrics/process-notes.json)、[C* 重放](metrics/cstar-verification.json)、[QCP 终检](logs/qcp-controller/controller_state.json)
- [冻结产物](target/manifest.json)、[公共引理引用](metrics/shared-helper-usage.json)
'''
(R/'REPORT.md').write_text(text)
print(R/'REPORT.md')
