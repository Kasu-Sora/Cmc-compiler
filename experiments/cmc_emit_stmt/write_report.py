"""Render final verified costs without claiming elapsed time from line counts."""
from pathlib import Path
import json
R=Path(__file__).resolve().parent
x=json.loads((R/'metrics/effort.json').read_text()); c=x['counts']['cstar'];q=x['counts']['qcp'];e=x['entries']
assert x['verification']['phase']=='done' and x['verification']['qcp_final_check']['status']=='passed'
run=json.loads((R/'metrics/run.json').read_text())['run_id']
source=x['source_additional_dependency_definitions'];g=x['process']['group_effort']['totals']
entries=json.loads((R/'metrics/annotation-entry-counts.json').read_text())
function_rows=[]
for f in x['source_effort']['function_counts']:
 t=x['target_per_function'][f['function']]
 function_rows.append(f"| `{f['function']}` | {f['specification']} / {t['specification']} | {f['annotation']} / {t['annotation']} | {f['inline_proof']} / {t['case_proof']} |")
function_table='\n'.join(function_rows)
text=f'''# cmc_concrete_emit_stmt.c：C* → QCP

完成两个运行时函数 `cmc_emit_if_stmt` 与 `cmc_emit_stmt`，包含必要的 `cmc_concrete_emit_stmt_proof.c` 支持。C* 隔离重放通过；QCP run `{run}` 为 `done`，final-check passed。运行体 token、共享 ABI 和既有依赖保持不变。

## 契约及复用

保留所有原 wf/typed/count/slot/表示安全条件、临时槽预算、PC 起止界及 break/continue 目标界；保留任意 program、function、statement、loop 标志、done、tail、out、capacity。入口消费 `cm_emit_stmt ... s ++ tail`，出口追加同一代码到 done 并保留 tail 以及全部上下文和 statement 所有权。if 的构造子条件保留；while 子体的 loop 标志为真，break 指向 loop end，continue 指向循环 guard PC。初始化和返回的类型归一化、11 种语句构造子与精确指令顺序均保持。沿用先前已验证的 lookup-policy/codegen-obligations 参数化边界，没有新增输入限制或弱化后置条件。

复用表达式、return、AST 地址、plan、count-context、layout 的已验证 helper BODY 契约与公共库闭包；互递归前向声明与本文件实现契约逐项核对。既有 helper 实现 proof 不重复计费。本例是模块化 BODY 契约验证，不新增 TVM 执行语义、终止性、跨模块链接或编译保持性定理。

必要 stmt proof 支持按数学用途迁移：节点表示开闭、构造子 wf/临时槽投影、语句发射形状、表达式/语句代码长度、调用结果等式、中间 PC 与整数转换界。C* proof-engine 的状态操作由 QCP 标注和经过检查的 Rocq 证明承担，不把 C* tactic API 当作新公理。

## 验证

C* 重放 {x['verification']['cstar']['verification_seconds']:.3f} 秒，退出码 0，verification_conditions/axioms/strategies 为空。QCP 完成 {e['manual_top_level']} 条顶层手工义务、{e['manual_splits']} 个已证明 split，剩余手工义务为零。{e['automatic_witnesses']} 条自动 witness 以 `Admitted` 导出，保留 QCP 自动层信任；manual 与新增库无 Admitted/Axiom/Parameter。未采用的 Abort split 草稿 {len(x['unused_split_drafts_aborted'])} 个单列。

## 工作量

按非空非纯注释物理行统计；proof 包含声明、Proof/Qed 和顶层路由，生成 VC 文本排除。行数受格式影响，不代表工时。C* annotation 为 {len(entries['source'])} 个语法条目，QCP 为 {entries['target']['annotation']} 个标注块，块粒度不同；token/字符与精确区间另存。

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

源案例 proof 含 16 行同文件私有 helper。新增源公共 proof 190 行中，stmt_proof.c 为 162 行、语句代码长度定理及其证明构造器为 28 行。前例 expr 的同名长度 helper 是 static；此处新导出的 19 行 helper 单独计入，不能因同名而误记为公共复用。

逐函数行数（各格均为 C* / QCP；C* proof 列仅函数内部分，16 行私有 helper 在文件级计一次）：

| 函数 | Specification | Annotation | Proof |
|---|---:|---:|---:|
{function_table}

QCP 新增公共定义 {len(e['new_model_declarations'])} 项、引理 {len(e['new_helpers'])} 条，以最终合并库计量。QCP 案例证明体 {x['proof_body_lines']} 行，声明/包装 {x['proof_wrapper_lines']} 行；互递归前向声明重复契约 {q.get('duplicate_prototype_specification',0)} 行、外部逻辑声明 {q['external_declarations']} 行、Coq 接入 {q['coq_imports']} 行、公共库 import/scope {q.get('new_common_imports_or_scopes',0)} 行另列。公共辅助是否被当前 manual 或其他新引理引用，见 shared-helper-usage.json；旧库引用不计新增成本。

分组 owner 调用：development {g['development_calls']} 次（失败 {g['development_failed']} 次），debug {g['debug_calls']} 次（失败 {g['debug_failed']} 次），exact {g['exact_calls']} 次（失败 {g['exact_failed']} 次）。标注修复、控制器验收及其他检查见过程记录。未知历史 C* 工时、人工与不可独立测量的模型活跃时间为 null。本例比较成品规模与读取源证明后的迁移成本，不能据此推断两工具从零证明的效率。

上述 exact 失败包含 1 次证明脚本错误、1 次 controller stale-state 基础设施冲突。主代理另外完成 27 次分组验收，以及各 1 次合并整体检查、写回和终检，均通过。标注阶段共 2 个 attempt：7 次 symexec 中 5 次失败；首轮 VC 审查发现 6 个局部资源缺口，在第二轮成对修复展开/折叠边界后通过。一次 comparison 报告格式修复与一次交接路径转写修正也单列保留。

本例新建目标文件中的两份 BODY 契约、103 个函数体标注块、4 项公共定义及 4 条公共引理均计入新增量；既有目标公共库不修改，旧 helper 实现 proof 不重复计入。运行时代码和 ABI 改动为零。

## 产物

- [标注 C](/Users/nizitong/QCP/qcp-binary-democases/QCP_examples/QCP_demos_human/cmc_emit_stmt_migration.c)
- [手工证明](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_stmt_migration_proof_manual.v)
- [公共库](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_stmt_migration_lib.v)
- [完整计量](metrics/effort.json)、[标注条目](metrics/annotation-entry-counts.json)、[语义审计](metrics/semantic-audit.json)、[源公共增量](metrics/source-additional-definitions.json)
- [过程记录](metrics/process-notes.json)、[分组调用](metrics/group-effort.json)、[互递归契约](metrics/recursive-contract-audit.json)
- [C* 重放](metrics/cstar-verification.json)、[QCP 终检](logs/qcp-controller/controller_state.json)、[冻结产物](target/manifest.json)
'''
(R/'REPORT.md').write_text(text)
