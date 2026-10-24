from pathlib import Path
import json
R=Path(__file__).resolve().parent
x=json.loads((R/'metrics/effort.json').read_text());c=x['counts']['cstar'];q=x['counts']['qcp'];e=x['entries'];run=json.loads((R/'metrics/run.json').read_text())['run_id'];src=x['source_additional_dependency_definitions']
assert x['verification']['phase']=='done'
assert json.loads((R/'metrics/recursive-contract-link.json').read_text())['status']=='passed'
base='/Users/nizitong/QCP/qcp-binary-democases'
lines=['# cmc_concrete_emit_expr.c：C* → QCP','',f'2026-10-19 完成七个运行时函数，包含六个 static helper 和公共 cm_emit_expr。C* 隔离重放通过；QCP run `{run}` 为 done、final-check passed。运行时代码 token、共享 ABI 和既有库保持不变。','','## 契约与递归依赖','',
'完整覆盖 intrinsic、unary、index、assignment、binary、member 与总分派，保留原 lvalue 两分支、构造子条件、wf/typed/counts、slot/type/表示安全、全局区大小、PC 起止界、临时槽预算与所有权。生成内容仍是精确 cm_expr_code_for 前缀，保持 done 追加与任意 tail。短路 AND/OR 的跳转目标、右子表达式 PC 和临时槽偏移均按原契约验证。',
'',
'复用既有一般表达式代码模型、长度／count 定理、binary-finish、simple/call 及计划写入和上下文 helper。十五个外部 helper 的接入契约逐项核对已验证 BODY 契约。新增 cm_emit_expr BODY 与上一例 call 模块假定的外部契约一致，补齐该递归实现依赖；同文件前向声明与 BODY 合同重复部分单列。',
'',
'保持既有 total lookup policy 和 codegen obligations 参数化边界，不增强输入前提、不弱化后置条件。本例完成模块化实现规约验证；没有新增终止性、跨模块链接元定理、HOL→Rocq 等价或 TVM 执行保持性定理。','','## 验证','',
f"完成 {e['manual_top_level']} 条顶层手工义务和 {e['manual_splits']} 个已证明 split，剩余手工义务为零；{e['automatic_witnesses']} 条自动 witness 以 Admitted 导出，保留 QCP 自动层信任。manual 和新增库无 Admitted/Axiom/Parameter；未采用的 Abort split 草稿 {len(x['unused_split_drafts_aborted'])} 个，单独披露。",'',
f"C* 重放 {x['verification']['cstar']['verification_seconds']:.3f} 秒，退出码 0，verification_conditions/axioms/strategies 均为空。QCP 标注验收、独立 VC 审查、分组证明、合并全量检查、写回与终检通过。",'',
'## 工作量','',
'非空非纯注释物理行，分类去重；proof 含声明、Proof/Qed 与路由，生成 VC 文本排除。较长单行契约与换行方式会影响行数，另存 token/字符指标；行数不是工时。','',
'| 项目 | C* | QCP |','|---|---:|---:|',
f"| Specification | {c['specification']} | {q['specification']} |",
f"| 函数体 annotation | {c['annotation']} | {q['annotation']} |",
f"| helper 接入 annotation | 0（include） | {q['integration_helper_specification']} |",
f"| Specification + annotation | {c['specification_plus_annotation']} | {q['specification_plus_annotation']} |",
f"| 上项含 helper 接入 | {c['specification_plus_annotation']} | {q['specification_plus_annotation_with_integration']} |",
f"| 同文件前向声明重复 spec | 0（头文件排除） | {q.get('duplicate_prototype_specification',0)} |",
f"| 案例 proof | {c['case_proof']} | {q['case_proof']} |",
f"| 新增公共 proof 依赖 | {c['additional_public_proof_closure']} | {q['new_common_proof']} |",
f"| 案例 + 公共 proof | {c['proof_including_shared']} | {q['proof_including_shared']} |",'',
f"C* 案例 proof = 内嵌 {c['inline_proof']} 行 + 26 项私有支持 {c['private_case_proof_support']} 行。QCP 证明体 {x['proof_body_lines']} 行、声明／包装 {x['proof_wrapper_lines']} 行。",'',
f"QCP 新增公共定义 {len(e['new_model_declarations'])} 项／{q['new_common_definitions']} 行、引理 {len(e['new_helpers'])} 条／{q['new_common_proof']} 行；以最终合并库为准，未被当前 manual 引用的新增引理仍计成本。源对应新增 selector/classifier 定义 {src['definition_count']} 项／{src['definition_lines']} 行，新增公共证明闭包 {src['public_proof_lines']} 行。既有一般表达式模型、长度、类型/布局、计划和 helper 实现证明均不重复计费。",'',
f"外部逻辑声明 {q['external_declarations']} 行、Coq 接入 {q['coq_imports']} 行、公共库 import/scope {q.get('new_common_imports_or_scopes',0)} 行及自动化/配置 {q.get('new_common_automation_or_configuration',0)} 行另列。",'',
'| 函数 | C* spec | C* annotation | C* 内嵌 proof | QCP spec | QCP annotation | QCP proof |','|---|---:|---:|---:|---:|---:|---:|']
for f in x['source_effort']['function_counts']:
 t=x['target_per_function'][f['function']];lines.append(f"| {f['function']} | {f['specification']} | {f['annotation']} | {f['inline_proof']} | {t['specification']} | {t['annotation']} | {t['case_proof']} |")
lines+=['','文件级私有支持不重复分摊。实际命令次数、失败修复和 controller 调度时间见过程记录与日志。未知历史源工时、人工活跃时间及不可独立测量的模型活跃时间为 null；本例比较成品规模和阅读源证明后的迁移成本，不能据此判断两体系从零证明的效率。','','## 产物','',
f'- [标注 C]({base}/QCP_examples/QCP_demos_human/cmc_emit_expr_migration.c)',f'- [手工证明]({base}/Rocq/examples/QCP_demos_human/cmc_emit_expr_migration_proof_manual.v)',f'- [公共库]({base}/Rocq/examples/QCP_demos_human/cmc_emit_expr_migration_lib.v)','- [完整计量](metrics/effort.json)、[语义审计](metrics/semantic-audit.json)、[递归契约衔接](metrics/recursive-contract-link.json)、[过程记录](metrics/process-notes.json)','- [C* 重放](metrics/cstar-verification.json)、[QCP 终检](logs/qcp-controller/controller_state.json)、[冻结产物](target/manifest.json)','']
g=x['process']['group_effort']['totals']
lines.insert(lines.index('## 产物'),f"分组 owner 实际调用：development {g['development_calls']} 次（失败 {g['development_failed']} 次），debug {g['debug_calls']} 次（失败 {g['debug_failed']} 次），exact {g['exact_calls']} 次（失败 {g['exact_failed']} 次）。主流程验收另外记录；逐组来源见 [group-effort.json](metrics/group-effort.json)。\n")
entries=json.loads((R/'metrics/annotation-entry-counts.json').read_text())
lines.insert(lines.index('## 产物'),f"源函数体 annotation 共 {len(entries['source'])} 个语法条目，目标为 {entries['target']['annotation']} 个标注块；两种语法的块粒度不同，不能直接作为难度比率。详见 [条目计量](metrics/annotation-entry-counts.json)。\n")
lines.insert(lines.index('## 产物'),'标注 owner 两轮合计：design 4 次、symexec 11 次（失败 9 次）、post-library 2 次；独立 VC 审查发现五处缺失入口状态事实，修复只涉及内部断言，函数契约与运行体未改。上述 exact 的 2 次失败中，1 次是证明脚本问题，1 次是控制器状态竞争；主流程另有 4 次同类 finalize 重试，均在保持证明不变后通过。各次具体来源见过程记录。\n')
(R/'REPORT.md').write_text('\n'.join(lines))
