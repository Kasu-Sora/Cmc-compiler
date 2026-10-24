from pathlib import Path
import json
R=Path(__file__).resolve().parent
E=json.loads((R/'metrics/effort.json').read_text());A=json.loads((R/'metrics/semantic-audit.json').read_text())
assert E['verification']['phase']=='done' and A['final_verification']['status']=='passed'
C=E['counts']['cstar'];Q=E['counts']['qcp'];N=E['entries'];D=E['source_additional_dependency_definitions'];run=json.loads((R/'metrics/run.json').read_text())['run_id']
rows='\n'.join(f"| {fn} | {next(x for x in E['source_effort']['function_counts'] if x['function']==fn)['specification']} | {next(x for x in E['source_effort']['function_counts'] if x['function']==fn)['annotation']} | {p['specification']} | {p['annotation']} | {p['case_proof']} |" for fn,p in E['target_per_function'].items())
model_review='\n'.join('- '+x for x in A['model_review'])
text=f'''# cmc_concrete_emit_expr_leaf.c：C* → QCP

全部九个运行时函数已迁移，含 static cmc_const_immediate、cm_sizeof_value；其余为四个 leaf emitters、cm_type_size_value、两个 member-context wrappers。C* 隔离重放通过；QCP run `{run}` 为 done、final-check passed。函数运行时 token、共享 ABI、emitter 声明及复用库哈希保持不变。

## 原契约与模型范围

本次以源 .c 中被验证实现的契约为基线。源头文件 cm_emit_const_expr 的声明省略了 cm_type_code_wf ty，而函数体在前后置均保留此条件；QCP 保留函数体条件，不声称已经证明更弱的头文件版本。其余六个公开声明与对应实现契约一致，详见 source-header-audit.json。

常量 helper 接受全部 signed64 value；char 返回低八位，负数先按 unsigned64 转换再取余，数学对应 tower_u8；非 char 返回原值。没有增加 scalar 或 value 非负前提。

四个 emitter 保留原 lvalue[0,1]、表达式构造子及总函数查询条件，并保持完整 program/function/expression 资源。lvalue=0 追加原精确单指令片段，lvalue=1 追加空片段；计划 tail 保持。字符串 sid 仅有原 [0,INT_MAX] 界，未增加 sid<字符串数量限制；typed、安全大小等纯事实在前后置保留。sizeof 和 member 包装保留原 typed/type-code-wf/type_refs/member_valid/count/structs-safe 等各自条件，返回语义大小或成员偏移，不能用表示大小替代。

模型审计记录：

{model_review}

复用 layout、counts、word、emit-core、emit-plan、emit-ast 等所需公共依赖。六个既有 helper 契约规范化后与已验证版本相同：cm_emit_plan、cmc_string_address、cmc_type_size_at、cmc_member_array、cmc_pointee、cmc_member_offset_at。两个 static helper 自身纳入本例验证，旧 helper 实现证明不重复导入或计入新增。

## 验证与信任

完成 {N['manual_top_level']} 条顶层手工义务、{N['manual_splits']} 个 split；九个函数均有验证覆盖，剩余手工义务零。新增公共库及 manual 无 Admitted/Axiom/Parameter。另有 {N['automatic_witnesses']} 条自动 witness 以 Admitted 导出，依赖 QCP 自动层。未采用 Abort split 草稿 {len(E['unused_split_drafts_aborted'])} 个，其父目标均已完成。

C* 重放耗时 {E['verification']['cstar']['verification_seconds']:.3f} 秒，退出码0且 verification_conditions/axioms/strategies 均为空；507个源C/H文件快照核对一致。QCP 完成标注、依赖准备、独立VC审查、分组证明、合并全量检查、写回和终检。{A['scope_boundary']}

## 工作量

按非空非纯注释物理行统计。生成的VC文本不算手写proof；案例proof含证明声明、Proof/Qed和split路由，另列实际证明体。行数受排版影响；字符、词法token与标注条目见计量文件，不能以行数比推断工时或难度。

| 项目 | C* | QCP |
|---|---:|---:|
| Specification | {C['specification']} | {Q['specification']} |
| 函数体 annotation | {C['annotation']} | {Q['annotation']} |
| 既有 helper 接入 annotation | 0（include） | {Q.get('integration_helper_specification',0)} |
| Annotation 含接入 | {C['annotation']} | {Q['total_annotation_with_integration']} |
| Specification + annotation 含接入 | {C['specification_plus_annotation']} | {Q['specification_plus_annotation_with_integration']} |
| 案例 proof | {C['case_proof']} | {Q['case_proof']} |

C*案例proof含内嵌 {C['inline_proof']} 行与8个私有PROOF helper的 {C['private_case_proof_support']} 行。QCP案例proof含证明体 {E['proof_body_lines']} 行、声明/包装 {E['proof_wrapper_lines']} 行。

新增公共成本：QCP **{len(N['new_model_declarations'])} 项定义／{Q['new_common_definitions']} 行，{len(N['new_helpers'])} 条引理／{Q['new_common_proof']} 行**；案例与公共proof合计 {Q['proof_including_shared']} 行。逐条使用情况、阶段增量和实际编译依赖见 effort.json/shared-helper-usage.json。现成库新增成本为零；仅被导入但未被manual引用的引理不记为直接复用。

对应源增量闭包：{D['definition_count']}项完整定义及{D['leaf_equation_slices']}段leaf方程，共{D['definition_lines']}行；{D['public_lemma_count']}条公共定理及私有构造器共{D['public_proof_lines']}行。按依赖图扣除已有大小/前缀/编码证明闭包，定义getter及导出脚手架排除。完整递归expression emitter只统计本例实际使用的四个构造子方程，不声称完整模型已迁移。源案例及此公共proof合计 {C['case_proof']+D['public_proof_lines']}行。

公共imports/scopes {Q.get('new_common_imports_or_scopes',0)}行、公共自动化/配置{Q.get('new_common_automation_or_configuration',0)}行、C Extern {Q.get('external_declarations',0)}行、C Coq import {Q.get('coq_imports',0)}行另列。

| 函数 | C* spec | C* ann | QCP spec | QCP ann | QCP 案例 proof |
|---|---:|---:|---:|---:|---:|
{rows}

标注设计检查6次（1次失败），符号执行5次（4次失败），均在同一annotation attempt修复。8组owner共运行development 41次（37次失败，含3次Show诊断）、debug 20次（2次失败）、exact 10次（2次失败）；各组最终exact及8次controller验收均通过。证明分组返工未产生新的annotation round或公共引理。所有设计、符号执行、development/debug/exact检查及返工均记录在 process-notes.json；annotation round与同轮失败次数分开统计。QCP run墙钟 {E['process']['timing']['run']['elapsed_seconds']/60:.2f}分钟，包括编辑、调度、工具及等待。历史源工时和不可独立测量的活跃时间记null。这是读过源证明后的迁移实验，不是两体系从零的公平比较。

## 产物

- [标注 C](/Users/nizitong/QCP/qcp-binary-democases/QCP_examples/QCP_demos_human/cmc_emit_expr_leaf_migration.c)
- [手工证明](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_expr_leaf_migration_proof_manual.v)
- [公共库](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_expr_leaf_migration_lib.v)
- [完整计量](metrics/effort.json)、[语义审计](metrics/semantic-audit.json)、[源声明差异](metrics/source-header-audit.json)
- [过程记录](metrics/process-notes.json)、[C*重放](metrics/cstar-verification.json)、[QCP终检](logs/qcp-controller/controller_state.json)、[冻结产物](target/manifest.json)
'''
(R/'REPORT.md').write_text(text);print(R/'REPORT.md')
