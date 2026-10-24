"""Render audited final metrics; physical lines do not measure difficulty."""
from pathlib import Path
import json
R=Path(__file__).resolve().parent
x=json.loads((R/'metrics/effort.json').read_text());assert x['verification']['phase']=='done'
c=x['counts']['cstar'];q=x['counts']['qcp'];e=x['entries'];g=x['process']['group_effort']['totals']
ent=json.loads((R/'metrics/annotation-entry-counts.json').read_text());src=x['source_text_size']
lex=lambda rows,k:sum(r['lexical_tokens']for r in rows if r['category']==k)
run=json.loads((R/'metrics/run.json').read_text())['run_id']
(R/'REPORT.md').write_text(f'''# cmc_concrete_emit_prelude.c：C* → QCP

完成唯一运行时函数 `cmc_emit_prelude` 及必要 proof 支持。C* 隔离重放通过；QCP run `{run}` 为 `done`，完整终检通过。运行体 token、共享 ABI、518 个源 C/H 文件与此前验证依赖均保持不变。

## 契约和实现

前置条件仅包含 program-context 和 resolved emitter-plan 资源，后置条件保留相同上下文，并把精确 prelude 指令序列追加到任意 done、保留任意 tail。没有新增 wf/typed、readiness、main_id 非负或有效入口等限制。CALL 仍采用既有 lookup-policy 参数化的总 PC 查询。

输出恰好为 11 条指令：PUSH 1048576、PUSH 8、STORE 0、CALL main 的总函数 PC、PUSH 256、MOD 0、PUSH 256、ADD 0、PUSH 256、MOD 0、HALT 0。运行时只读取 program->main_id，然后逐条调用已有计划发射函数。

两个 helper `cm_emit_plan` 和 `cm_emit_call_plan` 接入契约与已验证 BODY 契约一致；复用原程序上下文、堆表示、指令模型、计划及总查询。源文件的 emit-functions 构建依赖不代表运行时调用；目标只导入实际需要的公共模型闭包。本例是模块化发射实现验证，不新增 main 执行、终止性、链接或编译保持性定理。

## 验证与信任边界

C* 重放 {x['verification']['cstar']['verification_seconds']:.3f} 秒，退出码 0，verification_conditions/axioms/strategies 均为空。QCP 完成 {e['manual_top_level']} 条顶层手工义务和 {e['manual_splits']} 个 split，剩余手工义务为零。另有 {e['automatic_witnesses']} 条自动 witness 以 `Admitted` 导出，保留 QCP 自动层信任；manual 和新增库没有 Admitted/Axiom/Parameter。未采用 Abort split 草稿 {len(x['unused_split_drafts_aborted'])} 个另列。

## 工作量

计量非空非纯注释行；proof 包含声明、Proof/Qed 和路由包装，排除生成 VC 文本。历史 C* 开发时间、人工时间、无法独立测量的模型活跃时间均为 null。此为成品规模和读取原证明后的迁移成本，不是从零证明效率对比。

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

源案例 proof 为 {c['inline_proof']} 行内嵌证明，无新增文件私有支持；源公共增量是 9 行 cm_emit_prelude 指令模型，已有 proof 支持不重复计费。目标新增定义 {len(e['new_model_declarations'])} 项，引理 {len(e['new_helpers'])} 条，公共成本与案例证明分开。目标证明体 {x['proof_body_lines']} 行、声明/包装 {x['proof_wrapper_lines']} 行。

源 annotation {len(ent['source'])} 个条目，目标 {ent['target'].get('annotation',0)} 个标注块，粒度不同。补充相同正则的词法 token（不是模型 token），避免以长行压缩误判工作量：

| 项目 | C* token | QCP token |
|---|---:|---:|
| Specification | {lex(src,'specification')} | {lex(ent['entries'],'specification')} |
| 函数体 annotation | {lex(src,'annotation')} | {lex(ent['entries'],'annotation')} |
| helper 接入 annotation | 0 | {lex(ent['entries'],'integration_helper_specification')} |

外部逻辑声明 {q['external_declarations']} 行、Coq 接入 {q['coq_imports']} 行、公共 import/scope {q.get('new_common_imports_or_scopes',0)} 行另列。实际复用依赖及旧引理引用均记录在 effort.json，不新增计费。

分组 owner 调用 development {g['development_calls']} 次（失败 {g['development_failed']} 次）、debug {g['debug_calls']} 次（失败 {g['debug_failed']} 次）、exact {g['exact_calls']} 次（失败 {g['exact_failed']} 次）。控制器验收和 annotation 修复单独记录，避免重复计数。

## 产物与追溯

- [目标 C](/Users/nizitong/QCP/qcp-binary-democases/QCP_examples/QCP_demos_human/cmc_emit_prelude_migration.c)
- [手工证明](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_prelude_migration_proof_manual.v)
- [公共库](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_emit_prelude_migration_lib.v)
- [完整计量](metrics/effort.json)、[过程](metrics/process-notes.json)、[分组工作量](metrics/group-effort.json)
- [语义审计](metrics/semantic-audit.json)、[最终库审查](metrics/final-library-review.json)、[helper 契约](metrics/helper-contract-audit.json)
- [源重放](metrics/cstar-verification.json)、[终检状态](logs/qcp-controller/controller_state.json)、[产物哈希](target/manifest.json)
''')
