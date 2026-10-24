"""Render final audited migration effort, including formatting-independent size."""
import json
from pathlib import Path
R=Path(__file__).resolve().parent
x=json.loads((R/'metrics/effort.json').read_text())
assert x['verification']['phase']=='done' and x['verification']['qcp_final_check']['status']=='passed'
c=x['counts']['cstar'];q=x['counts']['qcp'];e=x['entries'];g=x['process']['group_effort']['totals']
entries=json.loads((R/'metrics/annotation-entry-counts.json').read_text())
src=json.loads((R/'metrics/source-text-size.json').read_text())
lex=lambda rows,k:sum(r['lexical_tokens'] for r in rows if r['category']==k)
run=json.loads((R/'metrics/run.json').read_text())['run_id']
rows=[]
for f in x['source_effort']['function_counts']:
 t=x['target_per_function'][f['function']]
 rows.append(f"| `{f['function']}` | {f['specification']} / {t['specification']} | {f['annotation']} / {t['annotation']} | {f['inline_proof']} / {t['case_proof']} |")
text=f'''# cmc_concrete_emit_functions.c：C* → QCP

完成唯一运行时函数 `cmc_emit_functions` 及必要 proof 支持。C* 隔离重放通过；QCP run `{run}` 为 `done`，完整终检通过。运行体 token、共享 ABI、518 个源 C/H 文件和此前验证的依赖保持不变。

## 契约与依赖

保持任意 functions、functions_ptr、fid、function_pc、done/tail、out/capacity。原 wf/typed、精确函数 PC、完整 functions readiness、结构体/全局/字符串表示安全、总数据大小界及 program-context/function-list 资源均保留在前后置条件中。空链表分支没有新增 fid 非负或函数列表等于程序全列表的限制。

非空时先发射当前 fid 的完整函数，再以 fid+1 和 function_pc+head_count 发射尾部；输出模型保持这一顺序，精确消费计划并追加到原 done、保留任意 tail。复用 `cmc_function_code_count`、`cmc_emit_function` 两个已验证 BODY 契约；复用原 readiness、链表/函数上下文和单函数发射模型。readiness 的计数形式与实际 statement 长度通过已验证长度定理连接。

沿用既有 lookup-policy/codegen-obligations 参数化边界。这是模块化 BODY 规约验证，不新增 TVM 执行、终止性、链接或编译保持性定理。

## 验证

C* 重放 {x['verification']['cstar']['verification_seconds']:.3f} 秒，退出码 0，verification_conditions/axioms/strategies 为空。QCP 完成 {e['manual_top_level']} 条顶层手工义务、{e['manual_splits']} 个 split，剩余手工义务为零。另有 {e['automatic_witnesses']} 条自动 witness 以 `Admitted` 导出，保留自动层信任；manual 与新增库没有 Admitted/Axiom/Parameter。未采用 Abort split 草稿 {len(x['unused_split_drafts_aborted'])} 个另列。

## 工作量

统计非空非纯注释物理行，proof 含声明、Proof/Qed 与顶层路由，生成 VC 文本排除。行数受格式影响，不代表工时。源 annotation {len(entries['source'])} 个条目，目标 {entries['target'].get('annotation',0)} 个标注块；粒度不同，另列词法 token、字符与精确区间。

| 项目 | C* | QCP |
|---|---:|---:|
| Specification | {c['specification']} | {q['specification']} |
| 函数体 annotation | {c['annotation']} | {q['annotation']} |
| helper 接入 annotation | 0（include） | {q['integration_helper_specification']} |
| Specification + annotation | {c['specification_plus_annotation']} | {q['specification_plus_annotation']} |
| 上项含 helper 接入 | {c['specification_plus_annotation']} | {q['specification_plus_annotation_with_integration']} |
| 案例 proof | {c['case_proof']} | {q['case_proof']} |
| 新增公共定义 | {c['new_public_definitions']} | {q['new_common_definitions']} |
| 新增公共 proof | {c['exported_shared_proof_closure']+c['additional_public_proof_closure']} | {q['new_common_proof']} |
| 案例 + 公共 proof | {c['proof_including_shared']} | {q['proof_including_shared']} |

源案例 proof 包含 {c['inline_proof']} 行函数体证明和 {c['private_case_proof_support']} 行文件私有 `cm_add_ready_facts` 支持。源新增公共模型是 cm_emit_functions 递归方程；已有 stmt/count/function 公共支持不重复计费。目标新增定义 {len(e['new_model_declarations'])} 项，引理 {len(e['new_helpers'])} 条；实际旧库引理引用及新增 helper 使用分别记录。

长行不能用于推断效率；同一正则 `\\w+|\\S` 的词法 token（不是模型 token）为：

| 项目 | C* token | QCP token |
|---|---:|---:|
| Specification | {lex(src,'specification')} | {lex(entries['entries'],'specification')} |
| 函数体 annotation | {lex(src,'annotation')} | {lex(entries['entries'],'annotation')} |
| helper 接入 annotation | 0 | {lex(entries['entries'],'integration_helper_specification')} |

逐函数行数（C* / QCP，源 proof 不含文件级支持）：

| 函数 | Specification | Annotation | Proof |
|---|---:|---:|---:|
{chr(10).join(rows)}

目标证明体 {x['proof_body_lines']} 行，声明/包装 {x['proof_wrapper_lines']} 行；外部逻辑声明 {q['external_declarations']} 行、Coq 接入 {q['coq_imports']} 行、公共 import/scope {q.get('new_common_imports_or_scopes',0)} 行、重复前向契约 {q.get('duplicate_prototype_specification',0)} 行另列。

分组 owner 调用 development {g['development_calls']} 次（失败 {g['development_failed']} 次）、debug {g['debug_calls']} 次（失败 {g['debug_failed']} 次）、exact {g['exact_calls']} 次（失败 {g['exact_failed']} 次）。控制器验收和标注修复另列，不与 owner 调用重复计算。历史 C* 开发时间、人工时间及无法独立测量的模型活跃时间为 null。此为成品规模与读取源证明后的迁移成本，不是从零证明效率比较。

## 产物与追溯

- [目标 C](/Users/nizitong/QCP/qcp-binary-democases/QCP_examples/QCP_demos_human/cmc_emit_functions_migration.c)
- [手工证明](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_functions_migration_proof_manual.v)
- [公共库](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_functions_migration_lib.v)
- [完整计量](metrics/effort.json)、[过程](metrics/process-notes.json)、[分组工作量](metrics/group-effort.json)
- [语义审计](metrics/semantic-audit.json)、[最终库审查](metrics/final-library-review.json)、[helper 契约](metrics/helper-contract-audit.json)
- [源重放](metrics/cstar-verification.json)、[终检状态](logs/qcp-controller/controller_state.json)、[产物哈希](target/manifest.json)
'''
(R/'REPORT.md').write_text(text)
