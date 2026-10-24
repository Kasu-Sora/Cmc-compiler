from pathlib import Path
import json,csv,io,shutil,difflib
R=Path(__file__).resolve().parent;W=R.parent.parent;S=Path('/Users/nizitong/.codex/skills/qcp-cstar-migration')
E=json.loads((R/'metrics/effort.json').read_text());A=json.loads((R/'metrics/semantic-audit.json').read_text());assert E['verification']['phase']=='done' and A['final_verification']['status']=='passed'
C=E['counts']['cstar'];Q=E['counts']['qcp'];N=E['entries'];run=json.loads((R/'metrics/run.json').read_text())['run_id']
files=[S/'SKILL.md',S/'references/cmc-emit-expr-dispatch-case.md',W/'MIGRATION_PLAN.md',W/'migration_inventory.csv'];before={str(p):p.read_text()if p.exists()else''for p in files};b=R/'baseline/documentation-before';b.mkdir(exist_ok=True)
for p in files:
 if p.exists():shutil.copy2(p,b/p.name)
text=f'''# 已验证案例：emit-expr-dispatch，C* → QCP

2026-10-17 完成 cmc_concrete_emit_expr_dispatch.c 唯一运行时函数 cm_emit_leaf_expr。C* 隔离重放通过；QCP run `{run}` 为 done、final-check passed。证据见 `/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_emit_expr_dispatch/REPORT.md`。

## 契约与复用

复用已有 cm_leaf_expr 类型、cm_leaf_source_expr 和 cm_leaf_code_for；原 C* cm_leaf_expr 是 kind 析取谓词，不是该 Rocq 类型。保留原 e，增加 leaf 表示见证时，需证明原 kind 条件与存在 leaf、e=cm_leaf_source_expr leaf 等价，不能把见证当作未证明的新输入约束。

保留全部原 wf_program、typed_program、总 f 查询、expr_wf、expr_counts_representable、安全大小事实和完整三种上下文资源。四个分支的 helper 契约使用先前已验证 leaf 函数体版本；const 头文件和函数体存在历史差异，本例从 dispatch 原 expr_wf 的整数类型条件推出 cm_type_code_wf（counts 也可推出），不能改用较弱的未验证声明。string 索引界与 sizeof 类型事实同样从原 counts/wf 展开获得。

代码模型复用四种 leaf 方程，精确消费/追加代码并保留任意 tail。原模型在这四种构造子上不依赖 pc/temp，运行时参数仍保留。沿用现有 policy/codegen obligations，不把 wf_program 重定义成便利占位符。此局部覆盖证明不是完整递归 emitter 或 HOL→Rocq 元层等价定理。

## 本例验证过的标注经验

同时保留 e=source_view leaf 与 e=具体构造子时，helper 匹配可能先选择较抽象的等式。本例仅调整等式顺序仍不够；在 which-implies 中同时把 emitter 计划的 leaf 重写为同一个具体 leaf 构造子后，才成功推断 helper 的类型和数值见证。该桥必须证明代码列表相等并保留 done/tail，不能换成假定。where 只显式传入公共 With 中已有的参数，分支存在变量由资源匹配推断。

## 验证与计量

{N['manual_top_level']} 条顶层手工义务、{N['manual_splits']} 个 split 完成；{N['automatic_witnesses']} 条自动 witness 以 Admitted 导出，依赖 QCP 自动层。manual 和新增公共库无 Admitted/Axiom/Parameter。

| 非空行 | C* | QCP |
|---|---:|---:|
| Specification | {C['specification']} | {Q['specification']} |
| 函数体 annotation | {C['annotation']} | {Q['annotation']} |
| helper 接入 annotation | 0（include） | {Q.get('integration_helper_specification',0)} |
| 案例 proof | {C['case_proof']} | {Q['case_proof']} |

QCP 新增公共定义 {len(N['new_model_declarations'])} 项/{Q['new_common_definitions']} 行，引理 {len(N['new_helpers'])} 条/{Q['new_common_proof']} 行。源新增 leaf kind 定义6行；既有 count/shape 支持和四条代码方程不重复计算。源12个 where 条目占8个物理行，统计同一分类时按行号去重，不把条目数相加当行数。两条对应引理均编译通过，本轮 manual 未直接调用，仍计成本。逐引理引用和阶段成本见 effort.json。行数不是历史工时。
'''
(S/'references/cmc-emit-expr-dispatch-case.md').write_text(text)
p=S/'SKILL.md';s=p.read_text();assert 'references/cmc-emit-expr-dispatch-case.md'not in s
s=s.replace('及 emit-expr-var 的一个函数；QCP','及 emit-expr-var、emit-expr-dispatch 各一个函数；QCP').replace('emit-expr-var 为 `cmc_emit_expr_var_migration.c`。','emit-expr-var 为 `cmc_emit_expr_var_migration.c`，emit-expr-dispatch 为 `cmc_emit_expr_dispatch_migration.c`。')
entry=f'`cmc_concrete_emit_expr_dispatch.c` 于 2026-10-17 完成唯一运行时函数验证。涉及叶子 kind 分派、表示见证覆盖、helper 前提派生及完整上下文保持时，读取 [references/cmc-emit-expr-dispatch-case.md](references/cmc-emit-expr-dispatch-case.md)。本例完成 {N["manual_top_level"]} 条顶层手工义务、{N["manual_splits"]} 个 split，另有 {N["automatic_witnesses"]} 条可信自动结果；新增公共定义 {len(N["new_model_declarations"])} 项、引理 {len(N["new_helpers"])} 条。\n\n'
old='这些结果覆盖十八个具体实现文件的运行时部分、105 个运行时函数及必要依赖；';assert old in s;s=s.replace(old,entry+'这些结果覆盖十九个具体实现文件的运行时部分、106 个运行时函数及必要依赖；');p.write_text(s)
p=W/'MIGRATION_PLAN.md';s=p.read_text().replace('emit-expr-var 的一个函数，共十八个具体实现文件的运行时部分、105 个运行时函数','emit-expr-var、emit-expr-dispatch 各一个函数，共十九个具体实现文件的运行时部分、106 个运行时函数').replace('16、14、49、22 条可信自动',f'16、14、49、22、{N["automatic_witnesses"]} 条可信自动').replace('[emit-expr-var 报告](experiments/cmc_emit_expr_var/REPORT.md)。','[emit-expr-var 报告](experiments/cmc_emit_expr_var/REPORT.md)、[emit-expr-dispatch 报告](experiments/cmc_emit_expr_dispatch/REPORT.md)。')
old='| 5：指令与程序生成 | `cmc_concrete_emit_expr*.c`（leaf、var已完成）、';assert old in s
s=s.replace(old,f'| 已完成 | `cmc_concrete_emit_expr_dispatch.c` | 一个叶子表达式分派函数；{N["manual_top_level"]} 条手工义务、{N["manual_splits"]} 个 split、{N["automatic_witnesses"]} 条可信自动结果；新增公共定义 {len(N["new_model_declarations"])} 项、引理 {len(N["new_helpers"])} 条 |\n| 5：指令与程序生成 | `cmc_concrete_emit_expr*.c`（leaf、var、dispatch已完成）、')
s=s.replace('emit-expr-leaf 与 emit-expr-var 的运行时部分已完成。下一候选为 `cmc_concrete_emit_expr_dispatch.c`','emit-expr-leaf、emit-expr-var 与 emit-expr-dispatch 的运行时部分已完成。下一候选为 `cmc_concrete_emit_expr_simple.c`');p.write_text(s)
p=W/'migration_inventory.csv';lines=p.read_bytes().splitlines(keepends=True);hits=0
for i,line in enumerate(lines):
 if line.startswith(b'/Users/nizitong/cmc/cmc_concrete_emit_expr_dispatch.c,'):
  row=next(csv.reader([line.decode()]));row[4]=f'qcp_pipeline_verified_1_function_{N["manual_top_level"]}_manual_{N["automatic_witnesses"]}_trusted_auto'
  buf=io.StringIO(newline='');csv.writer(buf,lineterminator='\r\n'if line.endswith(b'\r\n')else'\n').writerow(row);lines[i]=buf.getvalue().encode();hits+=1
assert hits==1;p.write_bytes(b''.join(lines))
(R/'logs/documentation-update.diff').write_text(''.join(''.join(difflib.unified_diff(before[str(p)].splitlines(True),p.read_text().splitlines(True),fromfile=str(p),tofile=str(p)))for p in files));print('Updated verified dispatch skill reference, plan, inventory.')
