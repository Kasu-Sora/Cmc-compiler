from pathlib import Path
import json
R=Path(__file__).resolve().parent
E=json.loads((R/'metrics/effort.json').read_text());A=json.loads((R/'metrics/semantic-audit.json').read_text())
assert E['verification']['phase']=='done' and A['final_verification']['status']=='passed'
C=E['counts']['cstar'];Q=E['counts']['qcp'];N=E['entries'];D=E['source_additional_dependency_definitions'];run=json.loads((R/'metrics/run.json').read_text())['run_id']
text=f'''# cmc_concrete_emit_expr_simple.c：C* → QCP

2026-10-18 完成整个文件唯一运行时函数 cm_emit_simple_expr。C* 隔离重放通过；QCP run `{run}` 为 done、final-check passed。运行时 token、共享 ABI、emitter 声明和复用库哈希保持不变。

## 契约与模型

源 .c/.h 契约一致。保留原 lvalue 界、simple 条件、wf_program、typed_program、总 f 查询、expr_wf/counts、params/locals slots_wf、structs/globals/strings 与 params/locals 安全事实、全局数据总大小界。完整 program/function/expression 资源保留；精确消费代码前缀并追加至 done，任意 tail 保持。

变量分支调用已验证 cm_emit_var_expr，其余简单表达式调用已验证 cm_emit_leaf_expr。两条 helper BODY 契约与既有版本规范化后一致，不导入旧 manual/auto，也不重复计入 helper 实现 proof。组合代码模型复用 leaf/var 定义；新表示见证需覆盖原简单表达式域，不新增输入限制。

'''+'\n'.join('- '+v for v in A['model_review'])+f'''

既有 cm_lookup_policy、cm_codegen_obligations 和 wf_program 参数化边界保持。源/目标对应由审计记录；本例不是 HOL→Rocq 元层等价定理，不声称整个递归 emitter、TVM 语义或编译保持性迁移完成。

## 验证

完成 {N['manual_top_level']} 条顶层手工义务、{N['manual_splits']} 个 split，剩余手工义务零。manual 和新增公共库无 Admitted/Axiom/Parameter。另有 {N['automatic_witnesses']} 条自动 witness 以 Admitted 导出，依赖 QCP 自动层。未采用 Abort split 草稿 {len(E['unused_split_drafts_aborted'])} 个。

C* 重放耗时 {E['verification']['cstar']['verification_seconds']:.3f} 秒，退出码0，verification_conditions/axioms/strategies 均为空；507个源 C/H 快照一致。QCP 完成标注验收、依赖准备、独立 VC 审查、分组证明、合并全量检查、写回及终检。

## 工作量

按非空非纯注释物理行计，同一分类按行号去重。源7个 where 条目占4行。Proof 包含声明、Proof/Qed 和 split 路由；生成 VC 不计手写 proof。行数不代表历史工时或工具难度。

| 项目 | C* | QCP |
|---|---:|---:|
| Specification | {C['specification']} | {Q['specification']} |
| 函数体 annotation | {C['annotation']} | {Q['annotation']} |
| helper 接入 annotation | 0（include） | {Q.get('integration_helper_specification',0)} |
| Annotation 含接入 | {C['annotation']} | {Q['total_annotation_with_integration']} |
| Specification + annotation | {C['specification_plus_annotation']} | {Q['specification_plus_annotation']} |
| Specification + annotation 含接入 | {C['specification_plus_annotation']} | {Q['specification_plus_annotation_with_integration']} |
| 案例 proof | {C['case_proof']} | {Q['case_proof']} |
| 新增公共定义 | {D['definition_lines']} | {Q['new_common_definitions']} |
| 新增公共 proof | {D['public_proof_lines']} | {Q['new_common_proof']} |

C* 案例 proof 全为内嵌证明；QCP 实际证明体 {E['proof_body_lines']} 行、声明/包装 {E['proof_wrapper_lines']} 行。QCP 新增公共定义 {len(N['new_model_declarations'])} 项、引理 {len(N['new_helpers'])} 条；案例与公共 proof 合计 {Q['proof_including_shared']} 行。

对应源增量仅 cm_simple_expr_def 的 leaf-or-kind2 定义（3行）。既有 leaf/var 方程、代码选择器、count/shape 支持和 helper 实现不重复计费。新增的两条对应引理均已编译，本轮 manual 未直接调用，仍计成本。实际复用 cm_expr_rep_node、cm_dispatch_leaf_coverage，并在新增库中复用 dispatch coverage/unique；引用位置计数见 reused-helper-usage.json 与 shared-helper-usage.json。公共 imports/scopes {Q.get('new_common_imports_or_scopes',0)} 行、公共自动化 {Q.get('new_common_automation_or_configuration',0)} 行、C Extern {Q.get('external_declarations',0)} 行、C Coq import {Q.get('coq_imports',0)} 行另列。

实际设计、symexec、development/debug/exact 调用和失败修复见 process-notes.json 及封存 owner 输出。Controller 记录 run 墙钟 {E['process']['timing']['run']['elapsed_seconds']/60:.2f} 分钟，包含编辑、工具、调度与等待；历史源工时及无法独立测量的活跃时间为 null。这是阅读源证明后的迁移成本，不能作为两体系从零证明的公平效率实验。

## 产物

- [标注 C](/Users/nizitong/QCP/qcp-binary-democases/QCP_examples/QCP_demos_human/cmc_emit_expr_simple_migration.c)
- [手工证明](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_expr_simple_migration_proof_manual.v)
- [公共库](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_expr_simple_migration_lib.v)
- [完整计量](metrics/effort.json)、[语义审计](metrics/semantic-audit.json)、[过程记录](metrics/process-notes.json)
- [C* 重放](metrics/cstar-verification.json)、[QCP 终检](logs/qcp-controller/controller_state.json)、[冻结产物](target/manifest.json)
'''
(R/'REPORT.md').write_text(text);print(R/'REPORT.md')
