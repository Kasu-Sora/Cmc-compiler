"""Render measured costs only after the complete controller run has passed."""
import json
from pathlib import Path
R=Path(__file__).resolve().parent
x=json.loads((R/'metrics/effort.json').read_text())
assert x['verification']['phase']=='done' and x['verification']['qcp_final_check']['status']=='passed'
c=x['counts']['cstar'];q=x['counts']['qcp'];e=x['entries']
g=x['process']['group_effort']['totals']
entries=json.loads((R/'metrics/annotation-entry-counts.json').read_text())
source_text=json.loads((R/'metrics/source-text-size.json').read_text())
lex=lambda rows,category:sum(r['lexical_tokens'] for r in rows if r['category']==category)
run=json.loads((R/'metrics/run.json').read_text())['run_id']
rows=[]
for f in x['source_effort']['function_counts']:
 t=x['target_per_function'][f['function']]
 rows.append(f"| `{f['function']}` | {f['specification']} / {t['specification']} | {f['annotation']} / {t['annotation']} | {f['inline_proof']} / {t['case_proof']} |")
public_source=c['exported_shared_proof_closure']+c['additional_public_proof_closure']
text=f'''# cmc_concrete_emit_function.c：C* → QCP

完成全部三个运行时函数：`cmc_emit_param_stores_from`、`cmc_emit_prologue`、`cmc_emit_function`，包含必要 function proof 支持。C* 隔离重放通过；QCP run `{run}` 为 `done`，完整终检通过。运行体 token、共享 ABI 和已有依赖保持不变。

## 契约与复用

参数写入保留任意 `full = prefix ++ params`、`slot = Zlength prefix`、`offset = 8 + cm_slots_size prefix`、原整数/尺寸/计数/合法性边界以及槽位链表所有权。按尾部递归先发射，再依次归一化当前参数、计算原前缀地址并存储。序言保留完整函数/语句资源、原栈帧与参数条件，生成 14 条固定指令及参数写入。完整函数保留所有 wf/typed/count/slot/表示安全与 PC/temp/容量条件，在 function-PC 加序言长度处调用 stmt，最后生成 PUSH 0 与返回尾声。

三个契约都精确消费对应代码前缀、追加到任意 done、保留任意 tail 及全部原纯事实和资源。沿用已有 lookup-policy/codegen-obligations 参数化边界，不加强输入条件或弱化后置条件。十个外部 helper 的接口核对已验证 BODY；旧 helper 实现证明不重复计费。源 function proof 中前缀、大小、计数、wf 和返回值重定位的数学用途由现有库或新 Rocq 证明承担。

本例为模块化 BODY 规约验证，不新增 TVM 执行、终止性、跨模块链接或编译保持性定理。

## 验证结果

C* 重放 {x['verification']['cstar']['verification_seconds']:.3f} 秒，退出码 0，verification_conditions/axioms/strategies 为空。QCP 完成 {e['manual_top_level']} 条顶层手工义务、{e['manual_splits']} 个 split，剩余手工义务为零。另有 {e['automatic_witnesses']} 条自动 witness 以 `Admitted` 导出，保留自动层信任；manual 与新增库没有 Admitted/Axiom/Parameter。未采用 Abort split 草稿 {len(x['unused_split_drafts_aborted'])} 个单列。

## 工作量

统计非空非纯注释物理行；proof 包含声明、Proof/Qed 与顶层路由，生成 VC 文本排除。行数受格式影响，不代表工时。源 annotation {len(entries['source'])} 个条目、目标 {entries['target'].get('annotation',0)} 个标注块；块粒度不同，token/字符及精确区间另存。

| 项目 | C* | QCP |
|---|---:|---:|
| Specification | {c['specification']} | {q['specification']} |
| 函数体 annotation | {c['annotation']} | {q['annotation']} |
| helper 接入 annotation | 0（include） | {q['integration_helper_specification']} |
| Specification + annotation | {c['specification_plus_annotation']} | {q['specification_plus_annotation']} |
| 上项含 helper 接入 | {c['specification_plus_annotation']} | {q['specification_plus_annotation_with_integration']} |
| 案例 proof | {c['case_proof']} | {q['case_proof']} |
| 新增公共定义 | {c['new_public_definitions']} | {q['new_common_definitions']} |
| 源文件内私有模型定义 | {c['case_model_definitions']} | 0（统一列入目标公共库） |
| 新增公共 proof | {public_source} | {q['new_common_proof']} |
| 案例 + 公共 proof | {c['proof_including_shared']} | {q['proof_including_shared']} |

本例 QCP 契约和标注有较长的物理行，因此不能从 194→9 行或 78→64 行推断成本下降。补充同一正则 `\\w+|\\S` 的词法 token 计数（不是模型 token，也不代表难度）：

| 项目 | C* token | QCP token |
|---|---:|---:|
| Specification | {lex(source_text,'specification')} | {lex(entries['entries'],'specification')} |
| 函数体 annotation | {lex(source_text,'annotation')} | {lex(entries['entries'],'annotation')} |
| helper 接入 annotation | 0 | {lex(entries['entries'],'integration_helper_specification')} |

源文件中四个非 static 定理常量（prefix zero/append、size snoc、param count-length）及其证明构造器共 {c['exported_shared_proof_closure']} 行，按外部链接属性计公共 proof，即使头文件没有重复声明；其他 static wf/bounds/retarget 支持 {c['private_case_proof_support']} 行计入案例 proof。源三个私有辅助定义为 head/tail/empty slots，共 {c['case_model_definitions']} 行；原 stmt、表达式、返回与计数公共支持直接复用，不再收取新增成本。

逐函数行数（各格为 C* / QCP；源 proof 只含函数体，文件级支持计一次）：

| 函数 | Specification | Annotation | Proof |
|---|---:|---:|---:|
{chr(10).join(rows)}

目标新增公共定义 {len(e['new_model_declarations'])} 项、引理 {len(e['new_helpers'])} 条，以实际合并库计量。目标证明体 {x['proof_body_lines']} 行，声明/包装 {x['proof_wrapper_lines']} 行。重复前向契约 {q.get('duplicate_prototype_specification',0)} 行、外部逻辑声明 {q['external_declarations']} 行、Coq 接入 {q['coq_imports']} 行及公共 import/scope {q.get('new_common_imports_or_scopes',0)} 行另列。公共引理使用情况见 `shared-helper-usage.json`；实际旧库引理引用见 `reused-helper-usage.json`。

分组 owner 调用 development {g['development_calls']} 次（失败 {g['development_failed']} 次）、debug {g['debug_calls']} 次（失败 {g['debug_failed']} 次）、exact {g['exact_calls']} 次（失败 {g['exact_failed']} 次）。控制器验收、标注修复和基础设施重试另见过程记录，不与 owner 调用重复计算。历史 C* 开发时间、人工时间与不可独立测量的模型活跃时间为 null；此为成品规模及读取源证明后的迁移成本，不能推断两个工具从零证明的效率。

## 产物与追溯

- [目标 C](/Users/nizitong/QCP/qcp-binary-democases/QCP_examples/QCP_demos_human/cmc_emit_function_migration.c)
- [手工证明](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_function_migration_proof_manual.v)
- [公共库](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_function_migration_lib.v)
- [完整计量](metrics/effort.json)、[过程记录](metrics/process-notes.json)、[分组检查](metrics/group-effort.json)
- [语义审计](metrics/semantic-audit.json)、[最终库审查](metrics/final-library-review.json)、[helper 契约](metrics/helper-contract-audit.json)
- [源重放](metrics/cstar-verification.json)、[终检状态](logs/qcp-controller/controller_state.json)、[目标快照](target/manifest.json)
'''
(R/'REPORT.md').write_text(text)
