from pathlib import Path
import json
R=Path(__file__).resolve().parent
x=json.loads((R/'metrics/effort.json').read_text()); c=x['counts']['cstar'];q=x['counts']['qcp'];e=x['entries']
assert x['verification']['phase']=='done'
run=json.loads((R/'metrics/run.json').read_text())['run_id']
source=x['source_additional_dependency_definitions'];g=x['process']['group_effort']['totals']
entries=json.loads((R/'metrics/annotation-entry-counts.json').read_text())
text=f'''# cmc_concrete_emit_return.c：C* → QCP

2026-10-19 完成唯一运行时函数 `cm_emit_return_epilogue_plan`。C* 隔离重放通过；QCP run `{run}` 为 `done`，final-check passed。六次调用的运行体 token、共享 ABI 和既有依赖保持不变。

## 契约及复用

对任意 `p`、`done`、`tail`、`out`、`capacity`，从原 resolved plan 中消费 `cm_return_epilogue ++ tail`，得到 `done ++ cm_return_epilogue` 和原 `tail`。保留已迁移表示中的任意 lookup-policy 参数，没有新增输入限制或弱化后置条件。尾声精确为 PUSH 8、LOAD 0、LOAD 0、PUSH 8、STORE 0、RET 0。

复用已验证的 `cm_emit_plan` BODY 契约、resolved plan 表示及其公共库闭包；helper 的显式接入契约单独计量，既有函数实现证明不重复计费。新增定义与源 `cm_return_epilogue_def` 的六个构造子及立即数逐项一致。本例证明生成计划/输出片段的正确性，不新增 RET 的 TVM 执行语义、终止性或编译保持性定理。

## 验证

C* 重放 {x['verification']['cstar']['verification_seconds']:.3f} 秒，退出码 0，verification_conditions/axioms/strategies 为空。
QCP 完成 {e['manual_top_level']} 条顶层手工义务、{e['manual_splits']} 个已证明 split，剩余手工义务为零；{e['automatic_witnesses']} 条自动 witness 以 `Admitted` 导出，保留 QCP 自动层信任。manual 与新增公共库无 Admitted/Axiom/Parameter；未采用的 Abort split 草稿 {len(x['unused_split_drafts_aborted'])} 个。

## 工作量

按非空非纯注释物理行统计；proof 包含声明、Proof/Qed 和顶层路由，生成 VC 文本排除。行数受格式影响，不代表工时。源 annotation {len(entries['source'])} 个语法条目、目标 {entries['target']['annotation']} 个标注块，块粒度不同；token/字符与精确区间另存。

| 项目 | C* | QCP |
|---|---:|---:|
| Specification | {c['specification']} | {q['specification']} |
| 函数体 annotation | {c['annotation']} | {q['annotation']} |
| helper 接入 annotation | 0（include） | {q['integration_helper_specification']} |
| Specification + annotation | {c['specification_plus_annotation']} | {q['specification_plus_annotation']} |
| 上项含 helper 接入 | {c['specification_plus_annotation']} | {q['specification_plus_annotation_with_integration']} |
| 案例 proof | {c['case_proof']} | {q['case_proof']} |
| 新增公共定义 | {source['definition_lines']} | {q['new_common_definitions']} |
| 新增公共 proof 依赖 | {source['public_proof_lines']} | {q['new_common_proof']} |
| 案例 + 公共 proof | {c['proof_including_shared']} | {q['proof_including_shared']} |

QCP 新增公共定义 {len(e['new_model_declarations'])} 项、引理 {len(e['new_helpers'])} 条，以最终合并库计量。源新增模型 {source['definition_count']} 项；已迁移的公共 proof 支持闭包增量为 {source['public_proof_lines']} 行。QCP 证明体 {x['proof_body_lines']} 行，声明/包装 {x['proof_wrapper_lines']} 行；外部逻辑声明 {q['external_declarations']} 行、Coq 接入 {q['coq_imports']} 行、公共库 import/scope {q.get('new_common_imports_or_scopes',0)} 行另列。

分组 owner 实际调用：development {g['development_calls']} 次（失败 {g['development_failed']} 次），debug {g['debug_calls']} 次（失败 {g['debug_failed']} 次），exact {g['exact_calls']} 次（失败 {g['exact_failed']} 次）。标注修复和主流程检查另见过程记录，不能把 owner 返回当作控制器验收。未知历史 C* 工时、人工活跃时间和不可独立测量的模型活跃时间为 null。本例比较成品规模与读取源证明后的迁移成本，不是从零证明的公平效率比较。

标注阶段 design 检查 3 次、symexec 3 次（失败 2 次）、post-library 1 次。两次修复分别是拆开类型与值的 Extern Coq 声明，以及在首个调用边界展开同一个命名列表并证明 opcode 事实。证明阶段一次开发失败源于顶层路由假定了错误的目标顺序，按 debug 显示的空间目标在先顺序修正；随后两个分组、合并验证与终检均通过。修复未改变函数契约或运行体。

## 产物

- [标注 C](/Users/nizitong/QCP/qcp-binary-democases/QCP_examples/QCP_demos_human/cmc_emit_return_migration.c)
- [手工证明](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_return_migration_proof_manual.v)
- [公共库](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_return_migration_lib.v)
- [完整计量](metrics/effort.json)、[标注条目](metrics/annotation-entry-counts.json)、[语义审计](metrics/semantic-audit.json)、[过程记录](metrics/process-notes.json)、[分组调用](metrics/group-effort.json)
- [C* 重放](metrics/cstar-verification.json)、[QCP 终检](logs/qcp-controller/controller_state.json)、[冻结产物](target/manifest.json)
'''
(R/'REPORT.md').write_text(text)
