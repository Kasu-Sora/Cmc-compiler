#!/usr/bin/env python3
"""Publish only the final verified, audited migration measurements."""
from pathlib import Path
import json
R=Path(__file__).resolve().parent
E=json.loads((R/'metrics/effort.json').read_text());A=json.loads((R/'metrics/semantic-audit.json').read_text())
assert E['verification']['phase']=='done' and E['verification']['qcp_final_check']['status']=='passed'
assert A['final_verification']['status']=='passed'
C=E['counts']['cstar'];Q=E['counts']['qcp'];N=E['entries'];run=json.loads((R/'metrics/run.json').read_text())['run_id']
rows='\n'.join(f"| {f} | {next(x for x in E['source_effort']['function_counts'] if x['function']==f)['specification']} | {p['specification']} | {p['annotation']} | {p['case_proof']} |" for f,p in E['target_per_function'].items())
text=f'''# cmc_concrete_emit_core.c：C* → QCP

完整迁移全部九个运行时函数，包含 static cm_emit_raw。原 C* 证明隔离重放通过；QCP run `{run}` 为 done，final-check passed。运行时函数 token 不变；复用 ABI 不变，目标中补入的 cm_emitter 结构体与原声明完全相同。

## 契约与模型

- cm_emit_raw：在原 int/int64 前缀后各写入一项，pc 增加一；完整保留 emitter/output 字段、容量、已初始化前缀及未初始化后缀。
- cm_emit：把 todo 的首条指令精确移到 done，opcode 与立即数均保持。
- normalize/load/store：保留 encoded-type 相等与 cm_type_code_wf 条件；char 的归一化为原六条指令，非 char 为空；load/store 分别选字节或普通指令。没有额外 scalar 或 program-wf 条件。
- fp_address：精确发出 PUSH 8、LOAD 0、PUSH offset、ADD 0。
- temp_store/temp_load：保留全部八项前后置纯条件及完整函数上下文，按原临时变量偏移发出地址片段及 STORE/LOAD。复用同一 total lookup policy；没有增加 fid 范围条件。
- binary_opcode：覆盖所有 signed int 输入，原 ten-case 加默认 MOD 映射，并保留返回值不等于 CALL 编码 22。

TVM 指令使用具体 datatype 与完整 28 项 opcode 编码。cm_rep_ops/imms 将指令列表映射到双数组；cm_emitter_plan_rep 保留原计划长度界。内存谓词使用 QCP 数组分段表达原字段所有权及前后缀，位宽仍分别为 int32 与 int64。逐项映射与哈希见 semantic-audit.json。

复用依赖及其哈希见 baseline/reused-dependencies.json；已有定义/引理记零新增。cmc_temp_offset 的接入契约与 layout 已验证版本规范化后相同，既有实现证明不重复计量，也不导入旧 auto/manual。

## 验证

完成 {N['manual_top_level']} 条顶层手工义务和 {N['manual_splits']} 个 split，九个函数均有义务覆盖，剩余手工义务为零。另有 {N['automatic_witnesses']} 条自动 witness 以 Admitted 导出，依赖 QCP 自动求解层；不能称为全部独立 Rocq 内核证书。手工证明及新增公共库无 Admitted/Axiom/Parameter。未采用 Abort split 草稿 {len(E['unused_split_drafts_aborted'])} 个，若存在其父目标已证明。

C* 重放退出码 0，verification_conditions/axioms/strategies 均为空，耗时 {E['verification']['cstar']['verification_seconds']:.3f} 秒。QCP 完成标注验收、依赖准备、独立 VC 检查、分组证明、合并检查、正式写回与终检。本次覆盖具体指令片段生成；完整 TVM 执行语义、readiness 桥和编译保持性仍是后续工作。

## 工作量

按非空非纯注释物理行计数。C* proof 块计 proof，函数外私有 proof helpers 也计案例 proof。QCP proof 含声明、Proof/Qed 与 split 路由；自动生成 VC 文本不计。不同排版与分解粒度影响行数，不代表难度或工具速度。

| 项目 | C* | QCP |
|---|---:|---:|
| Specification | {C['specification']} | {Q['specification']} |
| 函数体 annotation | {C['annotation']} | {Q.get('annotation',0)} |
| 既有 helper 接入 annotation | 0（include） | {Q.get('integration_helper_specification',0)} |
| Annotation 含接入 | {C['annotation']} | {Q['total_annotation_with_integration']} |
| Specification + annotation 含接入 | {C['specification_plus_annotation']} | {Q['specification_plus_annotation_with_integration']} |
| 案例 proof | {C['case_proof']} | {Q['case_proof']} |
| 目标新增公共 proof | —（已有库） | {Q['new_common_proof']} |

C* 案例 proof：内嵌 {C['inline_proof']} 行 + 12 个私有 helper 的 {C['private_case_proof_support']} 行。QCP 案例 proof：证明体 {E['proof_body_lines']} 行 + 声明/包装 {E['proof_wrapper_lines']} 行。

新增公共成本单列：**{len(N['new_model_declarations'])} 项定义／{Q['new_common_definitions']} 行，{len(N['new_helpers'])} 条引理／{Q['new_common_proof']} 行**。加上公共 proof 后 QCP proof 合计 {Q['proof_including_shared']} 行。公共 import/作用域 {Q.get('new_common_imports_or_scopes',0)} 行、公共自动化/配置 {Q.get('new_common_automation_or_configuration',0)} 行、C Extern {Q.get('external_declarations',0)} 行、C Coq import {Q.get('coq_imports',0)} 行另列。

对应源依赖新增涉及 16 项已有定义、124 行（源码位置及哈希见 source-additional-definitions.json），不混入 635 行案例 proof。相关源公共证明从既有库调用，其历史建设成本未知；QCP 新增公共 proof 为本次实际写出的完整库成本。共享 helper 的使用位置、annotation 阶段与 proving 阶段新增成本见 effort.json/shared-helper-usage.json。

| 函数 | C* spec | QCP spec | QCP annotation | QCP 案例 proof |
|---|---:|---:|---:|---:|
{rows}

QCP run 墙钟 {E['process']['timing']['run']['elapsed_seconds']/60:.2f} 分钟，跨越 2026-10-16 至 2026-10-17，包含两次连接中断及恢复、编辑、调度、验证和等待，不能视为连续活跃工时，也不能与 C* 成品重放耗时做速度对比。历史作者工时、不可独立测量的活跃时间均为 null。实际修订、失败检查及最终接受记录见 process-notes.json 和 controller 日志。

## 产物

- [标注 C](/Users/nizitong/QCP/qcp-binary-democases/QCP_examples/QCP_demos_human/cmc_emit_core_migration.c)
- [手工证明](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_core_migration_proof_manual.v)
- [公共库](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_core_migration_lib.v)
- [逐区间计量](metrics/effort.json)、[契约审计](metrics/semantic-audit.json)、[helper 契约核对](metrics/helper-contract-audit.json)
- [过程记录](metrics/process-notes.json)、[C* 重放](metrics/cstar-verification.json)、[QCP 终检](logs/qcp-controller/controller_state.json)
- [冻结产物](target/manifest.json)、[公共引理引用](metrics/shared-helper-usage.json)
'''
(R/'REPORT.md').write_text(text)
print(R/'REPORT.md')
