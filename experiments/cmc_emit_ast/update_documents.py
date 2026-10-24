#!/usr/bin/env python3
from pathlib import Path
import json,csv,io,shutil,difflib,hashlib
R=Path(__file__).resolve().parent;W=R.parent.parent;S=Path('/Users/nizitong/.codex/skills/qcp-cstar-migration')
E=json.loads((R/'metrics/effort.json').read_text());A=json.loads((R/'metrics/semantic-audit.json').read_text())
assert E['verification']['phase']=='done' and A['final_verification']['status']=='passed'
C=E['counts']['cstar'];Q=E['counts']['qcp'];N=E['entries'];D=E['source_additional_dependency_definitions'];run=json.loads((R/'metrics/run.json').read_text())['run_id']
files=[S/'SKILL.md',S/'references/cmc-emit-ast-case.md',W/'MIGRATION_PLAN.md',W/'migration_inventory.csv'];before={str(p):p.read_text() if p.exists() else '' for p in files}
b=R/'baseline/documentation-before';b.mkdir(exist_ok=True)
for p in files:
 if p.exists():shutil.copy2(p,b/p.name)
text=f'''# 已验证案例：emit-ast，C* → QCP

2026-10-17 完成 cmc_concrete_emit_ast.c 两个运行时函数。C* 隔离重放通过，QCP run `{run}` 为 done、final-check passed。完整证据与计量见 `/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_emit_ast/REPORT.md`。

## 地址模型与原契约

cm_emit_binding_address 按 global/local/param 分支向 resolved emitter 追加精确 binding-address fragment；计划包装函数消费 fragment++tail 并保留 tail。前后置均保留原十项纯事实和 program/function 两份完整上下文资源。不要只保留证明中使用的 globals-wf，或额外添加 fid 有效性。

沿用既有 cm_lookup_policy 和 cm_codegen_obligations；cm_wf_program 的完整合取保持，四项完整 codegen 条件仍为参数化边界。本例只提取 typed/global-wf 所需后果，不能宣称已完成具体全量 codegen 语义或编译保持性迁移。

cm_slots_prefix/cm_globals_prefix 递归于列表，index=0 停止，否则累加 head size 并递归 index-1。负数 index 继续遍历，不能在全域定义中改为 Z.to_nat 后取前缀。cm_global_address 为 16+globals-prefix；参数偏移为 8+params-prefix；局部偏移为 8+params-size+locals-prefix。

## 复用与成本边界

三个 layout helper 和两个 resolved helper 契约规范化后一致，旧实现 proof 不重复导入或计费。前缀一致性证明直接复用 cm_slot_size_matches__temp_context 和 cm_rep_global_size_matches；局部地址再复用 cm_slots_size_matches__temp_context。计划包装复用既有计划表示，本次 proof 直接使用 Zlength_app 和长度算术；cm_plan_fragment_capacity 随库导入但未被 manual 直接引用。

源文件七个私有 cm_ast_* helpers 属于案例 proof。增量公共源范围为两个前缀桥及 globals-wf head/tail 与构造器；已有 slot head/tail、大小桥、上下文和计划开合不重复计量。公共库按最终合并版本统计，包括证明阶段新增且实际用到的 helper；不能只统计 annotation 阶段库或公共池条目。

本例 aggressive_pre_process 的实际子目标顺序为空间在前、两个纯容量目标在后；按实际目标应用 split。上下文资源多时单次 cancel 未完全闭合，使用重复且有进展的 cancel；不要把这些脚本修正算成 annotation 返工。

## 验证与规模

完成 {N['manual_top_level']} 条顶层手工义务、{N['manual_splits']} 个 split；另有 {N['automatic_witnesses']} 条自动 witness 以 Admitted 导出，依赖 QCP 自动层。manual 与新增公共库无 Admitted/Axiom/Parameter。

| 非空行 | C* | QCP |
|---|---:|---:|
| Specification | {C['specification']} | {Q['specification']} |
| 函数体 annotation | {C['annotation']} | {Q['annotation']} |
| helper 接入 annotation | 0（include） | {Q.get('integration_helper_specification',0)} |
| 案例 proof | {C['case_proof']} | {Q['case_proof']} |
| 增量公共 proof | {D['public_proof_lines']} | {Q['new_common_proof']} |

QCP 新增公共定义 {len(N['new_model_declarations'])} 项/{Q['new_common_definitions']} 行、引理 {len(N['new_helpers'])} 条/{Q['new_common_proof']} 行。源对应模型 {D['definition_count']} 项/{D['definition_lines']} 行。行数包含证明声明/包装，排版与自动化不同，不等同于耗时。历史源工时未知。
'''
(S/'references/cmc-emit-ast-case.md').write_text(text)
p=S/'SKILL.md';s=p.read_text();assert 'references/cmc-emit-ast-case.md' not in s
s=s.replace('emit-resolved 与 emit-plan 各八个包装函数；','emit-resolved 与 emit-plan 各八个包装函数及 emit-ast 的两个地址生成函数；')
s=s.replace('emit-plan 为 `cmc_emit_plan_migration.c`。','emit-plan 为 `cmc_emit_plan_migration.c`，emit-ast 为 `cmc_emit_ast_migration.c`。')
entry=f'`cmc_concrete_emit_ast.c` 于 2026-10-17 完成两个地址生成函数验证。涉及绑定地址、整数索引前缀、布局/语义偏移桥及双上下文保持时，读取 [references/cmc-emit-ast-case.md](references/cmc-emit-ast-case.md)。本例完成 {N["manual_top_level"]} 条顶层手工义务、{N["manual_splits"]} 个 split，另有 {N["automatic_witnesses"]} 条可信自动结果；新增公共定义 {len(N["new_model_declarations"])} 项、引理 {len(N["new_helpers"])} 条。\n\n'
old='这些结果覆盖十五个具体实现文件的运行时部分、93 个运行时函数及必要依赖；';assert old in s
s=s.replace(old,entry+'这些结果覆盖十六个具体实现文件的运行时部分、95 个运行时函数及必要依赖；');p.write_text(s)
p=W/'MIGRATION_PLAN.md';s=p.read_text().replace('emit-resolved、emit-plan 各八个包装函数，共十五个具体实现文件的运行时部分、93 个运行时函数','emit-resolved、emit-plan 各八个包装函数及 emit-ast 的两个地址生成函数，共十六个具体实现文件的运行时部分、95 个运行时函数')
s=s.replace('83、16、16 条可信自动',f'83、16、16、{N["automatic_witnesses"]} 条可信自动')
s=s.replace('[emit-plan 报告](experiments/cmc_emit_plan/REPORT.md)。','[emit-plan 报告](experiments/cmc_emit_plan/REPORT.md)、[emit-ast 报告](experiments/cmc_emit_ast/REPORT.md)。')
old='| 5：指令与程序生成 | `cmc_concrete_emit_ast.c`、';assert old in s
s=s.replace(old,f'| 已完成 | `cmc_concrete_emit_ast.c` | 两个绑定地址函数；{N["manual_top_level"]} 条手工义务、{N["manual_splits"]} 个 split、{N["automatic_witnesses"]} 条可信自动结果；新增公共定义 {len(N["new_model_declarations"])} 项、引理 {len(N["new_helpers"])} 条 |\n| 5：指令与程序生成 | ')
s=s.replace('emit-core、emit-resolved 与 emit-plan 的运行时部分已完成。下一候选为 `cmc_concrete_emit_ast.c`','emit-core、emit-resolved、emit-plan 与 emit-ast 的运行时部分已完成。下一候选为 `cmc_concrete_emit_expr_leaf.c`')
p.write_text(s)
p=W/'migration_inventory.csv';lines=p.read_bytes().splitlines(keepends=True);hits=0
for i,line in enumerate(lines):
 if line.startswith(b'/Users/nizitong/cmc/cmc_concrete_emit_ast.c,'):
  row=next(csv.reader([line.decode()]));row[4]=f'qcp_pipeline_verified_2_functions_{N["manual_top_level"]}_manual_{N["automatic_witnesses"]}_trusted_auto_admissions'
  b=io.StringIO(newline='');csv.writer(b,lineterminator='\r\n' if line.endswith(b'\r\n') else '\n').writerow(row);lines[i]=b.getvalue().encode();hits+=1
assert hits==1;p.write_bytes(b''.join(lines))
(R/'logs/documentation-update.diff').write_text(''.join(''.join(difflib.unified_diff(before[str(p)].splitlines(True),p.read_text().splitlines(True),fromfile=str(p),tofile=str(p)))for p in files))
print('Updated verified AST reference, skill, plan and inventory.')
