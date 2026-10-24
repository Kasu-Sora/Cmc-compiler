from pathlib import Path
import json
R=Path(__file__).resolve().parent
E=json.loads((R/'metrics/effort.json').read_text());A=json.loads((R/'metrics/semantic-audit.json').read_text());P=json.loads((R/'metrics/process-notes.json').read_text())
assert E['verification']['phase']=='done' and A['final_verification']['status']=='passed'
C=E['counts']['cstar'];Q=E['counts']['qcp'];N=E['entries'];D=E['source_additional_dependency_definitions'];run=json.loads((R/'metrics/run.json').read_text())['run_id']
text=f'''# cmc_concrete_emit_expr_var.c：C* → QCP

整个文件的唯一运行时函数 cm_emit_var_expr 已完成迁移。C* 隔离重放通过；QCP run `{run}` 为 done、final-check passed。运行时 token、共享 ABI、emitter 声明和复用库哈希保持不变。

## 契约与模型

源 .c/.h 契约一致。目标保留原 lvalue[0,1]、CMVarE 构造子、wf_program、总 f 查询、slot[0,INT_MAX]、binding_valid、type_code_wf、params/locals slots_wf、安全大小事实及完整 program/function/expression 资源。没有增加 fid 边界、ty 等于绑定实际类型、scalar 或额外 typed 输入条件。三条 helper 契约与已验证 layout/AST/plan 版本规范化后一致。

普通变量右值生成地址代码再加载；数组右值和任意合法左值只生成地址。精确代码片段从计划前缀消耗并追加至 done，任意 tail 保持。变量专用代码模型在原 e=CMVarE 前提下对应源 Var 方程，不伪造其他构造子的默认行为，不声称完整递归表达式模型已经迁移。

'''+'\n'.join('- '+v for v in A['model_review'])+f'''

复用现有 cm_lookup_policy 与 cm_codegen_obligations；wf_program 中已有的四个 codegen 条件保留显式参数，源实例化含义与之前 counts/AST 案例相同。本例不新增这些抽象条件，不证明完整模型实例化或编译保持性。

## 验证

完成 {N['manual_top_level']} 条顶层手工义务、{N['manual_splits']} 个 split，剩余手工义务零。manual 与新增公共库无 Admitted/Axiom/Parameter；另有 {N['automatic_witnesses']} 条自动 witness 以 Admitted 导出，依赖 QCP 自动层。未采用的 Abort split 草稿 {len(E['unused_split_drafts_aborted'])} 个。

C* 重放耗时 {E['verification']['cstar']['verification_seconds']:.3f} 秒，退出码0，verification_conditions/axioms/strategies 均为空；507个源 C/H 文件快照核对一致。QCP 已完成标注验收、依赖准备、独立 VC 审查、分组证明、合并全量检查、写回和终检。

## 工作量

非空非纯注释物理行；生成的 VC 文本不计手写 proof。Proof 包含证明声明、Proof/Qed 及 split 路由；补充字符/token和条目计量见 metrics。不同排版影响行数，不能据此推断难度或工时。

| 项目 | C* | QCP |
|---|---:|---:|
| Specification | {C['specification']} | {Q['specification']} |
| 函数体 annotation | {C['annotation']} | {Q['annotation']} |
| helper 接入 annotation | 0（include） | {Q.get('integration_helper_specification',0)} |
| Annotation 含接入 | {C['annotation']} | {Q['total_annotation_with_integration']} |
| Specification + annotation 含接入 | {C['specification_plus_annotation']} | {Q['specification_plus_annotation_with_integration']} |
| 案例 proof | {C['case_proof']} | {Q['case_proof']} |

C* 案例 proof 包含内嵌 {C['inline_proof']} 行和私有 cm_var_code_shape 的 {C['private_case_proof_support']} 行。QCP 案例 proof 含实际证明体 {E['proof_body_lines']} 行、声明/包装 {E['proof_wrapper_lines']} 行。

新增公共成本：QCP {len(N['new_model_declarations'])} 项定义／{Q['new_common_definitions']} 行，{len(N['new_helpers'])} 条引理／{Q['new_common_proof']} 行；案例与公共 proof 合计 {Q['proof_including_shared']} 行。已验证依赖零新增成本。每条新引理的实际使用、仅导入或间接引用情况见 shared-helper-usage.json；未使用但新增的引理仍计成本。

对应源增量：Var 方程片段 {D['definition_lines']} 行；两个 array-code 零/非零定理及其私有构造器、两个计划选择/恢复状态操作共 {D['public_proof_lines']} 行。既有 layout/AST/plan、上下文开合和 leaf 案例已经计入的选择器定义不重复计算。源案例和增量公共 proof 共 {C['case_proof']+D['public_proof_lines']} 行。完整递归 emitter 不计为本例新增已迁移模型。

公共 imports/scopes {Q.get('new_common_imports_or_scopes',0)} 行、公共自动化 {Q.get('new_common_automation_or_configuration',0)} 行、C Extern {Q.get('external_declarations',0)} 行、C Coq import {Q.get('coq_imports',0)} 行另列。

设计、symexec、development/debug/exact 的实际调用及失败修复见 process-notes.json 和封存的 owner 输出。QCP run 墙钟 {E['process']['timing']['run']['elapsed_seconds']/60:.2f} 分钟，包含编辑、调度、工具和等待；历史源工时和不可独立测量的活跃时间为 null。这是读过源证明后的迁移实验，不能作为两体系从零证明的公平效率比较。

## 产物

- [标注 C](/Users/nizitong/QCP/qcp-binary-democases/QCP_examples/QCP_demos_human/cmc_emit_expr_var_migration.c)
- [手工证明](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_expr_var_migration_proof_manual.v)
- [公共库](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_expr_var_migration_lib.v)
- [完整计量](metrics/effort.json)、[语义审计](metrics/semantic-audit.json)、[过程记录](metrics/process-notes.json)
- [C* 重放](metrics/cstar-verification.json)、[QCP 终检](logs/qcp-controller/controller_state.json)、[冻结产物](target/manifest.json)
'''
(R/'REPORT.md').write_text(text);print(R/'REPORT.md')
