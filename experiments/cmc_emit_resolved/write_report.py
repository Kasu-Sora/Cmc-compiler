#!/usr/bin/env python3
from pathlib import Path
import json
R=Path(__file__).resolve().parent;E=json.loads((R/'metrics/effort.json').read_text());A=json.loads((R/'metrics/semantic-audit.json').read_text());assert E['verification']['phase']=='done' and A['final_verification']['status']=='passed'
C=E['counts']['cstar'];Q=E['counts']['qcp'];N=E['entries'];run=json.loads((R/'metrics/run.json').read_text())['run_id'];D=E['source_additional_dependency_definitions']
rows='\n'.join(f"| {fn} | {next(x for x in E['source_effort']['function_counts']if x['function']==fn)['specification']} | {next(x for x in E['source_effort']['function_counts']if x['function']==fn)['annotation']} | {p['specification']} | {p['annotation']} | {p['case_proof']} |"for fn,p in E['target_per_function'].items())
text=f'''# cmc_concrete_emit_resolved.c：C* → QCP

全部八个运行时函数已迁移。C* 原证明隔离重放通过，QCP run `{run}` 为 done、final-check passed。运行时函数 token、共享 ABI 和所有复用依赖哈希不变；cm_emitter 声明与已验证 core 及原源码一致。

## 契约与复用

本文件维护的是 resolved 逻辑视图：`cm_resolved_emitter_rep` 存在一个 raw 指令前缀，实际 ops/imms 缓冲区对应 raw，`cm_patch_code raw` 才等于契约中的 resolved 前缀。patch 只把 CALL 的立即数从函数编号映射到 `cm_function_pc`，保留其他指令、指令顺序和长度。

`cm_emit_resolved_call` 的实际写入仍为函数编号，没有把程序改写为直接输出 PC。它接受所有 signed int function_id，保留负数及越界编号的原 total 语义；没有增加编号范围、程序合法性、readiness 或 PC 可表示性条件。普通 resolved 发射器保留非 CALL 限制、opcode 编码相等和容量条件。

normalize/load/store 保留原 type-code-wf 和编码相等条件，未增加 scalar-type 限制；各包装函数精确追加原 fragment。临时变量包装函数保留前后置的八项纯事实、入口片段容量界和完整函数上下文，所有函数查询、偏移及 patch 使用同一个既有 cm_lookup_policy。

复用 emit-core 的指令 datatype、完整 28 项编码、双数组表示、片段模型及其既有依赖。七个 core helper 契约与已验证 C 规范化后逐字相同；本次验证八个包装函数体，未重复计量 helper 实现证明，未导入旧 auto/manual。依赖清单与 actual selected build snapshot 已核对。

## 验证与边界

完成 {N['manual_top_level']} 条顶层手工义务、{N['manual_splits']} 个 split，八个函数均有生成义务覆盖，剩余手工义务为零。另有 {N['automatic_witnesses']} 条自动 witness 以 Admitted 导出，依赖 QCP 自动层；手工证明及新增公共库没有 Admitted/Axiom/Parameter。未采用 Abort split 草稿 {len(E['unused_split_drafts_aborted'])} 个。

C* 重放退出码 0，verification_conditions/axioms/strategies 均为空，耗时 {E['verification']['cstar']['verification_seconds']:.3f} 秒。QCP 完成标注验收、依赖准备、独立 VC 审查、分组证明、合并全量检查、正式写回与终检。本例未验证后续物理 CALL 回填 pass、完整 TVM 执行或整个编译保持性。

## 工作量

按非空非纯注释物理行计数，自动生成 VC 文本排除。C* proof 块及私有支持函数计案例 proof；QCP proof 含声明、Proof/Qed 包装和 split 路由。行数反映最终规模，不是活跃工时或难度。QCP 的 With/Require/Ensure 常写成长行；词法 token、字符量和标注条目明细另存 source-text-size.json 与 annotation-entry-counts.json，不能直接用两边物理行数的比例衡量效率。

| 项目 | C* | QCP |
|---|---:|---:|
| Specification | {C['specification']} | {Q['specification']} |
| 函数体 annotation | {C['annotation']} | {Q['annotation']} |
| 既有 helper 接入 annotation | 0（include） | {Q.get('integration_helper_specification',0)} |
| Annotation 含接入 | {C['annotation']} | {Q['total_annotation_with_integration']} |
| Specification + annotation 含接入 | {C['specification_plus_annotation']} | {Q['specification_plus_annotation_with_integration']} |
| 案例 proof | {C['case_proof']} | {Q['case_proof']} |

C* 案例 proof 包含内嵌 {C['inline_proof']} 行及 18 个私有 PROOF 支持声明的 {C['private_case_proof_support']} 行。QCP 案例 proof 分为证明体 {E['proof_body_lines']} 行、声明/包装 {E['proof_wrapper_lines']} 行。

公共成本另列：QCP 新增 **{len(N['new_model_declarations'])} 项定义／{Q['new_common_definitions']} 行，{len(N['new_helpers'])} 条引理／{Q['new_common_proof']} 行**；公共 proof 加入后 QCP proof 共 {Q['proof_including_shared']} 行。源依赖对应 {D['definition_count']} 项定义／{D['definition_lines']} 行及 {D['public_lemma_count']} 条定理（含构造器 {D['public_proof_lines']} 行），属已有源库，并非本次重新编写或已知历史工时。源案例加这部分依赖 proof 为 {C['case_proof']+D['public_proof_lines']} 行。

源案例中的六类片段 patch 私有证明在 QCP 成为公共引理，不能仅凭案例 proof 行数降低就判断节省了工作。

现有公共库按零新增计入；新引理以最终合并库计数，直接/间接使用情况与阶段增量见 effort.json。导入/作用域 {Q.get('new_common_imports_or_scopes',0)} 行、公共自动化/配置 {Q.get('new_common_automation_or_configuration',0)} 行、C Extern {Q.get('external_declarations',0)} 行、C Coq import {Q.get('coq_imports',0)} 行另列。

| 函数 | C* spec | C* ann | QCP spec | QCP ann | QCP 案例 proof |
|---|---:|---:|---:|---:|---:|
{rows}

QCP run 墙钟 {E['process']['timing']['run']['elapsed_seconds']/60:.2f} 分钟，包括编辑、调度、工具及等待；历史源工时、不可独立测量的活跃时间记 null。实际修订、失败检查和最终验收记录在 process-notes.json。此实验读取了源证明，不是两套工具从零的公平效率比较。

## 产物

- [标注 C](/Users/nizitong/QCP/qcp-binary-democases/QCP_examples/QCP_demos_human/cmc_emit_resolved_migration.c)
- [手工证明](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_resolved_migration_proof_manual.v)
- [公共库](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_resolved_migration_lib.v)
- [计量明细](metrics/effort.json)、[契约审计](metrics/semantic-audit.json)、[helper 契约核对](metrics/helper-contract-audit.json)
- [过程](metrics/process-notes.json)、[C* 重放](metrics/cstar-verification.json)、[QCP 终检](logs/qcp-controller/controller_state.json)、[冻结产物](target/manifest.json)
'''
(R/'REPORT.md').write_text(text);print(R/'REPORT.md')
