from pathlib import Path
import json
R=Path(__file__).resolve().parent
x=json.loads((R/'metrics/effort.json').read_text());c=x['counts']['cstar'];q=x['counts']['qcp'];en=x['entries'];src=x['source_additional_dependency_definitions'];run=json.loads((R/'metrics/run.json').read_text())['run_id']
assert x['verification']['phase']=='done'
base='/Users/nizitong/QCP/qcp-binary-democases'
lines=['# cmc_concrete_emit_expr_call.c：C* → QCP','',f'2026-10-18 完成整文件三个运行时函数：cm_emit_args_reload_plan、cm_emit_args_store_plan、cm_emit_call_expr。C* 隔离重放通过；QCP run `{run}` 为 done、final-check passed。运行时 token、共享 ABI 及复用依赖保持不变。','','## 契约与依赖边界','',
'保留原参数列表任意合法表达式域、lvalue 的两种分支、总函数查询、wf/typed/counts、槽布局和表示安全、全局数据大小、temp/scratch/temp_limit 与 PC 起止边界。完整 program/function/expression/argument 资源保持；精确消费计划前缀、追加到 done，任意 tail 保持。不增加 fid 范围、参数表达式种类或额外 codegen 假设。',
'',
'复用五个已验证 helper 的 BODY 契约：cm_args_length、cm_expr_rvalue_count_context、cm_emit_temp_load_plan、cm_emit_temp_store_plan、cm_emit_call_plan。未导入它们的旧 manual/auto，也不重复计入实现证明。',
'',
'**外部实现依赖仍为 cm_emit_expr。** 本例按原 C* 头文件的完整契约进行模块化调用，其通用递归函数体尚未迁移，不能把本例通过等同于整个递归 emitter 已验证。新增一般表达式代码模型覆盖全部 14 种构造子，属于数学定义；它不代替通用 emitter 的实现证明。既有 lookup policy/codegen obligations 参数化边界不变。本轮也不构成 HOL→Rocq 元层等价定理或 TVM/编译保持性定理。','','## 验证','',
f"完成 {en['manual_top_level']} 条顶层手工义务、{en['manual_splits']} 个 split，剩余手工义务零。manual 和新增公共库无 Admitted/Axiom/Parameter。另有 {en['automatic_witnesses']} 条自动 witness 以 Admitted 导出，保留 QCP 自动层信任。未采用的 Abort split 草稿 {len(x['unused_split_drafts_aborted'])} 个。",'',
f"C* 重放 {x['verification']['cstar']['verification_seconds']:.3f} 秒，退出码 0，verification_conditions/axioms/strategies 为空。QCP 完成标注验收、依赖准备、独立 VC 审查、分组证明、合并全量检查、写回与终检。",'',
'## 工作量','',
'按非空非纯注释物理行分类并去重。proof 包含声明、Proof/Qed 和路由，生成 VC 不计手写 proof。辅助函数 BODY 的契约计规格，导入 helper 的契约单列接入 annotation。行数不是工时或难度。','',
'| 项目 | C* | QCP |','|---|---:|---:|',
f"| Specification | {c['specification']} | {q['specification']} |",
f"| 函数体 annotation | {c['annotation']} | {q['annotation']} |",
f"| helper 接入 annotation | 0（include） | {q['integration_helper_specification']} |",
f"| Specification + annotation | {c['specification_plus_annotation']} | {q['specification_plus_annotation']} |",
f"| Specification + annotation 含接入 | {c['specification_plus_annotation']} | {q['specification_plus_annotation_with_integration']} |",
f"| 案例 proof | {c['case_proof']} | {q['case_proof']} |",
'',f"C* 案例 proof = 内嵌 {c['inline_proof']} 行 + 同文件私有证明辅助 {c['private_case_proof_support']} 行。QCP 案例 proof 的实际证明体 {x['proof_body_lines']} 行，声明/包装 {x['proof_wrapper_lines']} 行。",'',
f"此外，QCP 外部类型／逻辑符号声明 {q['external_declarations']} 行、Coq 接入声明 {q['coq_imports']} 行单列，未混入函数体 annotation；库 imports/scopes 为 {q['new_common_imports_or_scopes']} 行。完整区间另有 token 和字符计量，以辅助判断格式差异。",'',
'### 公共依赖新增成本','',
f"QCP 最终案例库新增 {len(en['new_model_declarations'])} 项定义／{q['new_common_definitions']} 行，{len(en['new_helpers'])} 条引理／{q['new_common_proof']} 行；案例加公共 proof 为 {q['proof_including_shared']} 行。既有库新增成本零。逐声明区间、引用次数及标注/证明阶段成本见 effort.json。新增但未被 manual 直接引用的引理仍计成本。",'',
f"源侧对应新增依赖为 {src['definition_lines']} 行模型（扣除此前 leaf/var 方程与基础代码），{src['public_proof_lines']} 行公共证明闭包；本文件另外有 3 项私有 HD/TL 观察定义／7 行，未混入案例 proof。公共证明的构造函数和定理常量只计一次。",'',
'### 逐函数','',
'| 函数 | C* spec | C* annotation | C* 内嵌 proof | QCP spec | QCP annotation | QCP proof |','|---|---:|---:|---:|---:|---:|---:|']
for f in x['source_effort']['function_counts']:
 t=x['target_per_function'][f['function']];lines.append(f"| {f['function']} | {f['specification']} | {f['annotation']} | {f['inline_proof']} | {t['specification']} | {t['annotation']} | {t['case_proof']} |")
lines+=['','源同文件私有辅助服务多个函数，不在逐函数表中重复分摊。实际命令调用、失败修复与调度时间见 process-notes.json 和 controller 日志。历史源工时、人工活跃时间及无法独立测量的模型活跃时间为 null；本例是阅读源证明后的迁移成本，不是两体系从零证明的公平效率实验。','','## 产物','',
f'- [标注 C]({base}/QCP_examples/QCP_demos_human/cmc_emit_expr_call_migration.c)',
f'- [手工证明]({base}/Rocq/examples/QCP_demos_human/cmc_emit_expr_call_migration_proof_manual.v)',
f'- [公共库]({base}/Rocq/examples/QCP_demos_human/cmc_emit_expr_call_migration_lib.v)',
'- [完整计量](metrics/effort.json)、[语义审计](metrics/semantic-audit.json)、[过程记录](metrics/process-notes.json)',
'- [C* 重放](metrics/cstar-verification.json)、[QCP 终检](logs/qcp-controller/controller_state.json)、[冻结产物](target/manifest.json)','']
(R/'REPORT.md').write_text('\n'.join(lines))
