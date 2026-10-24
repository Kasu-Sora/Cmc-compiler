#!/usr/bin/env python3
from pathlib import Path
import json
R=Path(__file__).resolve().parent
E=json.loads((R/'metrics/effort.json').read_text());A=json.loads((R/'metrics/semantic-audit.json').read_text())
assert E['verification']['phase']=='done' and A['final_verification']['status']=='passed'
C=E['counts']['cstar'];Q=E['counts']['qcp'];N=E['entries'];D=E['source_additional_dependency_definitions'];run=json.loads((R/'metrics/run.json').read_text())['run_id']
T=E['process']['notes']['proof_development']['group_worker_check_totals']
rows='\n'.join(f"| {fn} | {next(x for x in E['source_effort']['function_counts'] if x['function']==fn)['specification']} | {next(x for x in E['source_effort']['function_counts'] if x['function']==fn)['annotation']} | {p['specification']} | {p['annotation']} | {p['case_proof']} |" for fn,p in E['target_per_function'].items())
text=f'''# cmc_concrete_emit_ast.c：C* → QCP

全部两个运行时函数已迁移：cm_emit_binding_address 与 cm_emit_binding_address_plan。C* 原证明隔离重放通过；QCP run `{run}` 为 done、final-check passed。运行时函数 token、cm_emitter 声明、共享 ABI 和复用库哈希保持不变。

## 契约与模型

保留原十项纯事实在前后置中的完整对应：程序 wf、总函数查询、structs/globals 对应关系、binding_valid、params/locals 的 slots_wf，以及 globals/params/locals 的表示安全性。两个函数同时保持完整 program-context 与 function-context 所有权。没有新增 fid 有效性、偏移界或 readiness 前提。

直接函数按 scope 生成精确地址片段：global 为 PUSH(global address)，local 为 FP-relative(local offset)，else 为 FP-relative(param offset)，追加至 done。计划包装函数消费 fragment++tail 中的 fragment，追加至 done 并保留 tail。binding_valid 自身保留原三种合法 scope 与 slot 条件。

新语义前缀按列表递归、在整数 index 等于零时停止；保留负数及超长 index 的原定义行为，不以 Z.to_nat 截断替代。语义地址分别为 16+globals-prefix、8+params-prefix、8+params-size+locals-prefix；函数查找沿用原 cm_lookup_policy。证明将已有表示大小、前缀计算与这些语义偏移连接。

复用 layout、counts、emit-core、emit-resolved、emit-plan 等已经验证的库。三个 layout helper 和两个 resolved helper 的契约与先前版本规范化后完全一致，未导入其 manual/auto 或重复计入实现证明。复用依赖确实进入 selected dependency snapshot，哈希与冻结版本一致。

沿用 counts 的 cm_wf_program policy cg p：typed/counts/size/stack 等条件完整保留；四项完整 codegen 条件仍由 cm_codegen_obligations 参数表示，具体 C* 实例化边界保持公开。当前证明只提取 typed/global-wf 所需结论，没有删除其它条件，也没有宣称已重建完整 emitter 或编译保持性。

## 验证

完成 {N['manual_top_level']} 条顶层手工义务、{N['manual_splits']} 个 split，两个函数均有生成和检查覆盖，未完成手工义务为零。新增公共库和 manual 无 Admitted/Axiom/Parameter。另有 {N['automatic_witnesses']} 条自动 witness 以 Admitted 导出，依赖 QCP 自动层，不能称为全部义务均有独立 Rocq 内核证书。未采用的 Abort split 草稿 {len(E['unused_split_drafts_aborted'])} 个，均有已完成顶层证明覆盖。

C* 重放退出码 0，verification_conditions/axioms/strategies 均为空，耗时 {E['verification']['cstar']['verification_seconds']:.3f} 秒。507 个源 C/H 文件快照核对一致。QCP 完成标注验收、依赖准备、独立 VC 审查、分组证明、合并全量检查、正式写回及终检。

## 工作量

计数为非空非纯注释物理行；自动生成 VC 文本不计手写 proof。C* 内嵌 proof 和七个私有 cm_ast_* 支持函数计入案例 proof；QCP proof 包含证明声明、Proof/Qed 包装和 split 路由。契约排版差异较大，因此另外提供词法 token、字符量和标注条目，不能把行数比例当作工时或难度比。

| 项目 | C* | QCP |
|---|---:|---:|
| Specification | {C['specification']} | {Q['specification']} |
| 函数体 annotation | {C['annotation']} | {Q['annotation']} |
| helper 接入 annotation | 0（include） | {Q.get('integration_helper_specification',0)} |
| Annotation 含接入 | {C['annotation']} | {Q['total_annotation_with_integration']} |
| Specification + annotation 含接入 | {C['specification_plus_annotation']} | {Q['specification_plus_annotation_with_integration']} |
| 案例 proof | {C['case_proof']} | {Q['case_proof']} |

C* 案例 proof 为内嵌 {C['inline_proof']} 行、七个私有支持函数 {C['private_case_proof_support']} 行；QCP 案例 proof 为证明体 {E['proof_body_lines']} 行、声明/包装 {E['proof_wrapper_lines']} 行。

公共新增成本单列：QCP **{len(N['new_model_declarations'])} 项定义／{Q['new_common_definitions']} 行，{len(N['new_helpers'])} 条引理／{Q['new_common_proof']} 行**。最终案例与新增公共 proof 合计 {Q['proof_including_shared']} 行。引理逐条使用情况与 annotation/proving 阶段增量见 effort.json、shared-helper-usage.json。

源对应增量依赖为 {D['definition_count']} 项模型定义／{D['definition_lines']} 行，{D['public_lemma_count']} 条公开引理及其构造器／{D['public_proof_lines']} 行：两个前缀一致性桥和 globals-wf 的 head/tail 引理。已有 slots-wf head/tail、slot/global-size 桥、上下文开合、plan 开合、binding 非负性等不重复计为新增。源案例与这部分公共 proof 合计 {C['case_proof']+D['public_proof_lines']} 行；这只是选定依赖闭包的规模，不是其历史开发时间。

已有依赖新增成本为零。公共导入/作用域 {Q.get('new_common_imports_or_scopes',0)} 行，公共自动化/配置 {Q.get('new_common_automation_or_configuration',0)} 行，C Extern {Q.get('external_declarations',0)} 行、Coq import {Q.get('coq_imports',0)} 行另列。

| 函数 | C* spec | C* ann | QCP spec | QCP ann | QCP 案例 proof |
|---|---:|---:|---:|---:|---:|
{rows}

标注 design/symexec/post-lib 各一次通过，无 annotation retry。三个证明组 controller 均首次验收通过；development 共 {T['dev']} 次（失败 {T['dev_failures']} 次）、debug 共 {T['debug']} 次（失败 {T['debug_failures']} 次）、owner exact 共 {T['exact']} 次全部通过。修正涉及空间资源的重复消去、scope 常量化简、片段长度的显式定义改写、Intros 语法与假设名，以及 aggressive 子目标的空间优先顺序。公共库在 proving 阶段未修改。

QCP run 墙钟 {E['process']['timing']['run']['elapsed_seconds']/60:.2f} 分钟，包含编辑、调度、工具检查与等待。检查次数、失败原因和修订见 process-notes.json，实际命令和结果保存在 logs。历史源工时、人工及模型活跃时间无独立可靠记录，记 null。本例是读取源证明后的迁移实验，不是两套体系从零证明的公平比较。

## 产物

- [标注 C](/Users/nizitong/QCP/qcp-binary-democases/QCP_examples/QCP_demos_human/cmc_emit_ast_migration.c)
- [手工证明](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_ast_migration_proof_manual.v)
- [公共库](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_ast_migration_lib.v)
- [计量明细](metrics/effort.json)、[语义审计](metrics/semantic-audit.json)、[helper 契约审计](metrics/helper-contract-audit.json)
- [过程记录](metrics/process-notes.json)、[C* 日志](metrics/cstar-verification.json)、[QCP 终检](logs/qcp-controller/controller_state.json)、[冻结产物](target/manifest.json)
'''
(R/'REPORT.md').write_text(text);print(R/'REPORT.md')
