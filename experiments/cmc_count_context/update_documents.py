#!/usr/bin/env python3
"""Update the migration guide only after the automatic follow-up is verified."""
from pathlib import Path
import json,csv,io
R=Path(__file__).resolve().parent;W=R.parent.parent;S=Path('/Users/nizitong/.codex/skills/qcp-cstar-migration')
E=json.loads((R/'metrics/effort.json').read_text());A=json.loads((R/'metrics/semantic-audit.json').read_text());run=json.loads((R/'metrics/run.json').read_text())['run_id']
assert E['verification']['phase']=='done' and E['verification']['qcp_final_check']['status']=='passed' and A['final_verification']['status']=='passed'
C=E['counts']['cstar'];Q=E['counts']['qcp'];N=E['entries']
ref=f'''# 已验证案例：cmc_concrete_count_context.c，C* → QCP

2026-10-16 按用户要求在 counts 完成后自动迁移四个上下文包装函数。源 `/Users/nizitong/cmc/cmc_concrete_count_context.c`；目标 `/Users/nizitong/QCP/qcp-binary-democases/QCP_examples/QCP_demos_human/cmc_count_context_migration.c`。完整报告和计量在 `/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_count_context/`。

Run `{run}` 为 done，final-check passed，原 C* 重放通过。{N['manual_top_level']} 条顶层手工义务、{N['manual_splits']} 个 split 完成，另有 {N['automatic_witnesses']} 条可信自动 witness 以 Admitted 导出。手工证明及新增库没有 Admitted/Axiom/Parameter；运行时 token、ABI、已验证公共库哈希不变。

## 保持契约并复用上下文模型

- type-code 包装只要求表达式表示和未初始化输出；不能补上源契约没有的类型有效性前提。
- 另三个包装保留完整 program/function 上下文、原 wf、总函数查询等式、表达式或语句合法性、计数 representability、struct safety、精确返回值及 i32 界。语句包装保留 loop_。
- 统一复用 counts 的 cm_lookup_policy 和 cm_codegen_obligations，不新加 fid 边界，不另定义同名 wf 或 context。counts 中四项 emitter/TVM 条件的具体 Rocq 实例化仍未完成；详见 [cmc-counts-case.md](cmc-counts-case.md)。
- 从旧已验证 C 文件直接接入 helper 的完整契约，规范化比较三个契约一致；实际依赖快照验证 counts/layout/copy-bytes 纯库哈希，而不是导入旧案例的 auto/manual 函数证明。

## 标注经验

用四个普通 Assert 打开已有表达式或上下文表示，暴露 helper 所需字段/list，保留其余资源作 frame；返回义务直接恢复完整 Ensure。不额外加入重复 Ensure 的关闭 Assert。

QCP 的 Assert 中 existential 指针不是后续 where 注释可直接引用的词法变量。本例删除 zs/zg/zl 的显式 where 赋值，让堆匹配推断指针见证，同时仍明确传入 policy、cg、p、f、投影列表以及 e/s/loop_。不要因这类范围错误改契约或变更运行时代码。Extern 类型构造器与 term 声明分块，避免解析器把 term 的冒号当作类型声明语法。

这两次失败均在同一个 annotation attempt 内修复，属于标注语法/实例化问题；不是证明不可完成或必须加强前提的证据。

## 增量工作量

| 非空行 | C* | QCP |
|---|---:|---:|
| Specification | {C['specification']} | {Q['specification']} |
| 函数体 annotation | {C['annotation']} | {Q['annotation']} |
| helper 接入 annotation | 0（原 include） | {Q.get('integration_helper_specification',0)} |
| 案例 proof | {C['case_proof']} | {Q['case_proof']} |
| 本源文件公共 proof／目标新增公共 proof | {C['exported_shared_proof_closure']} | {Q['new_common_proof']} |

目标新增公共定义 {len(N['new_model_declarations'])} 项/{Q['new_common_definitions']} 行，公共引理 {len(N['new_helpers'])} 条/{Q['new_common_proof']} 行；公共导入/作用域 {Q.get('new_common_imports_or_scopes',0)} 行另列。已有 counts/layout/copy-bytes 模型与桥接按已付成本复用，不在新案例重复计入。源导入支持的历史开发成本未知，不能将源库整体视为零成本。

目标 proof 包含 {E['proof_body_lines']} 行证明体和 {E['proof_wrapper_lines']} 行声明/Proof/Qed 包装。规格存在长单行，报告同时保存词法 token 和字符数。行数与重放时间不代表作者工时；本例阅读既有证明后迁移，不是从零公平效率实验。
'''
(S/'references/cmc-count-context-case.md').write_text(ref)
p=S/'SKILL.md';s=p.read_text();s=s.replace('和 counts 的 15 个运行时函数；','、counts 的 15 个运行时函数及 count-context 的 4 个包装函数；').replace('counts 为 `cmc_counts_migration.c`。','counts 为 `cmc_counts_migration.c`，count-context 为 `cmc_count_context_migration.c`。')
entry=f'`cmc_concrete_count_context.c` 随后自动推进并完成四个包装函数验证。涉及完整上下文开合、helper 契约接入、where 存在量见证范围和已有库增量复用时，读取 [references/cmc-count-context-case.md](references/cmc-count-context-case.md)。本例完成 {N["manual_top_level"]} 条顶层手工义务、{N["manual_splits"]} 个 split，另有 {N["automatic_witnesses"]} 条可信自动结果；新增公共定义 {len(N["new_model_declarations"])} 项、引理 {len(N["new_helpers"])} 条。\n\n'
if 'references/cmc-count-context-case.md' not in s:s=s.replace('这些结果覆盖七个具体实现文件的运行时部分、59 个运行时函数及必要依赖；',entry+'这些结果覆盖八个具体实现文件的运行时部分、63 个运行时函数及必要依赖；')
p.write_text(s)
p=W/'MIGRATION_PLAN.md';s=p.read_text().replace('counts 的 15 个运行时函数，共七个具体实现文件的运行时部分、59 个运行时函数','counts 的 15 个运行时函数及 count-context 的 4 个包装函数，共八个具体实现文件的运行时部分、63 个运行时函数').replace('332、184 条可信自动',f'332、184、{N["automatic_witnesses"]} 条可信自动').replace('[counts 报告](experiments/cmc_counts/REPORT.md)。','[counts 报告](experiments/cmc_counts/REPORT.md)、[count-context 报告](experiments/cmc_count_context/REPORT.md)。')
row=f'| 已完成 | `cmc_concrete_count_context.c` | 四个包装函数；{N["manual_top_level"]} 条手工义务、{N["manual_splits"]} 个 split、{N["automatic_witnesses"]} 条可信自动结果；复用 counts/layout/copy-bytes，公共定义新增 {len(N["new_model_declarations"])} 项、引理 {len(N["new_helpers"])} 条 |\n'
if row not in s:s=s.replace('| 3：表示与尺寸的剩余部分 |',row+'| 3：表示与尺寸的剩余部分 |')
s=s.replace('counts 中剩余 readiness 导出、`cmc_concrete_count_context.c`、','counts 中剩余 readiness 导出、')
s=s.replace('和 counts 的运行时部分。layout/counts','、counts 的运行时部分及 `cmc_concrete_count_context.c`。layout/counts')
start=s.index('五个基础写入/复制实现、layout 与 counts 的运行时部分已完成。');end=s.index('\n\n',start)
s=s[:start]+'五个基础写入/复制实现、layout、counts 的运行时部分与 count-context 四个包装函数已完成。用户要求的自动下一项已落实；下一个候选是 `cmc_concrete_function_pc_total.c`，之后再处理 globals/strings 等数据区生成。优先复用 counts/layout 公共库，只计必要新增定义、引理与接入成本。counts 的 readiness 导出及 emitter/TVM 具体实例化仍待后续迁移。'+s[end:];p.write_text(s)
p=W/'migration_inventory.csv';lines=p.read_bytes().splitlines(keepends=True);hits=0
for i,line in enumerate(lines):
 if line.startswith(b'/Users/nizitong/cmc/cmc_concrete_count_context.c,'):
  row=next(csv.reader([line.decode()]));row[4]=f'qcp_pipeline_verified_4_functions_{N["manual_top_level"]}_manual_{N["automatic_witnesses"]}_trusted_auto_admissions';buf=io.StringIO(newline='');csv.writer(buf,lineterminator='\r\n' if line.endswith(b'\r\n') else '\n').writerow(row);lines[i]=buf.getvalue().encode();hits+=1
assert hits==1;p.write_bytes(b''.join(lines));print('Updated context migration inventory and skill after verified completion.')
