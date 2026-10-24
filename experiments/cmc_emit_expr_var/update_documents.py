from pathlib import Path
import json,csv,io,shutil,difflib
R=Path(__file__).resolve().parent;W=R.parent.parent;S=Path('/Users/nizitong/.codex/skills/qcp-cstar-migration')
E=json.loads((R/'metrics/effort.json').read_text());A=json.loads((R/'metrics/semantic-audit.json').read_text());assert E['verification']['phase']=='done' and A['final_verification']['status']=='passed'
C=E['counts']['cstar'];Q=E['counts']['qcp'];N=E['entries'];run=json.loads((R/'metrics/run.json').read_text())['run_id']
files=[S/'SKILL.md',S/'references/cmc-emit-expr-var-case.md',W/'MIGRATION_PLAN.md',W/'migration_inventory.csv'];before={str(p):p.read_text()if p.exists()else''for p in files};b=R/'baseline/documentation-before';b.mkdir(exist_ok=True)
for p in files:
 if p.exists():shutil.copy2(p,b/p.name)
text=f'''# 已验证案例：emit-expr-var，C* → QCP

2026-10-17 完成 cmc_concrete_emit_expr_var.c 唯一运行时函数 cm_emit_var_expr。C* 隔离重放通过；QCP run `{run}` 为 done、final-check passed。证据及计量见 `/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_emit_expr_var/REPORT.md`。

## 契约与复用

源 .c/.h 契约一致。保留原 wf_program、总 f 查询、lvalue/slot 范围、binding_valid、type_code_wf、params/locals slots_wf、安全大小事实和完整三种上下文资源。不要添加 ty 等于绑定类型、fid 边界或 scalar 条件。复用原 cm_lookup_policy 和 cm_codegen_obligations 四项条件参数，不能为便利重定义 wf_program。

cmc_binding_array 只需要 program.globals 和 fn.locals 对应资源；调用后恢复完整 program/function 上下文，再调用已验证 cm_emit_binding_address_plan。三条外部 helper 契约与 layout/AST/plan 已验证版本保持一致，不导入其旧 manual/auto，不重复计算实现 proof。

变量模型明确特化 CMVarE：左值生成地址；普通右值生成地址加加载；数组右值生成地址。现有 binding_array_code 的零/非零判断对应原布尔数组判定，在原 constructor 前提下建立源方程对应即可；不得把非变量构造子默认返回空片段并声称完整表达式模型。地址调用的 tail 在普通右值分支包含 load 片段，完成加载后用列表结合律恢复总输出。始终保留任意外部 tail。

## 本例验证过的修复经验

部分资源断言内的存在变量不能直接当作断言外的具名地址使用。本例让 helper 调用推断地址，并在关闭完整上下文时重新绑定。lvalue==0 分支会触发符号替换并影响计划匹配；本例采用等价的 0<=lvalue<=0 事实，并在生成的义务中证明其等于零，不改变原输入契约。列表拼接重写前先化简变量代码的布尔分支与局部定义，再用结合律恢复 done 和 tail。

新增 cm_var_source_equation 是局部定义展开和布尔分支引理，本轮手工证明直接展开模型，没有调用此引理；它仍计入新增成本。该引理不是 HOL 到 Rocq 的元层等价定理，跨体系对应另由语义审计记录。

## 验证与计量

{N['manual_top_level']} 条顶层手工义务、{N['manual_splits']} 个 split 完成；{N['automatic_witnesses']} 条自动 witness 以 Admitted 导出，依赖 QCP 自动层。manual 和新增公共库无 Admitted/Axiom/Parameter。

| 非空行 | C* | QCP |
|---|---:|---:|
| Specification | {C['specification']} | {Q['specification']} |
| 函数体 annotation | {C['annotation']} | {Q['annotation']} |
| helper 接入 annotation | 0（include） | {Q.get('integration_helper_specification',0)} |
| 案例 proof | {C['case_proof']} | {Q['case_proof']} |

QCP 新增公共定义 {len(N['new_model_declarations'])} 项/{Q['new_common_definitions']} 行，引理 {len(N['new_helpers'])} 条/{Q['new_common_proof']} 行；已有库零新增。C* 的私有 cm_var_code_shape 计案例 proof；新增源公共两条数组判定定理及两项计划状态操作共50行，Var方程片段8行。之前 leaf 已计的选择器定义不重复计算。条目使用与阶段增量见 effort.json；行数不是历史工时。
'''
(S/'references/cmc-emit-expr-var-case.md').write_text(text)
p=S/'SKILL.md';s=p.read_text();assert 'references/cmc-emit-expr-var-case.md'not in s
s=s.replace('（含两个 static helper）；QCP','（含两个 static helper）及 emit-expr-var 的一个函数；QCP').replace('emit-expr-leaf 为 `cmc_emit_expr_leaf_migration.c`。','emit-expr-leaf 为 `cmc_emit_expr_leaf_migration.c`，emit-expr-var 为 `cmc_emit_expr_var_migration.c`。')
entry=f'`cmc_concrete_emit_expr_var.c` 于 2026-10-17 完成唯一运行时函数验证。涉及变量左/右值、数组判定、地址与加载计划组合及上下文恢复时，读取 [references/cmc-emit-expr-var-case.md](references/cmc-emit-expr-var-case.md)。本例完成 {N["manual_top_level"]} 条顶层手工义务、{N["manual_splits"]} 个 split，另有 {N["automatic_witnesses"]} 条可信自动结果；新增公共定义 {len(N["new_model_declarations"])} 项、引理 {len(N["new_helpers"])} 条。\n\n'
old='这些结果覆盖十七个具体实现文件的运行时部分、104 个运行时函数及必要依赖；';assert old in s;s=s.replace(old,entry+'这些结果覆盖十八个具体实现文件的运行时部分、105 个运行时函数及必要依赖；');p.write_text(s)
p=W/'MIGRATION_PLAN.md';s=p.read_text().replace('emit-expr-leaf 的九个函数，共十七个具体实现文件的运行时部分、104 个运行时函数','emit-expr-leaf 的九个函数及 emit-expr-var 的一个函数，共十八个具体实现文件的运行时部分、105 个运行时函数').replace('16、14、49 条可信自动',f'16、14、49、{N["automatic_witnesses"]} 条可信自动').replace('[emit-expr-leaf 报告](experiments/cmc_emit_expr_leaf/REPORT.md)。','[emit-expr-leaf 报告](experiments/cmc_emit_expr_leaf/REPORT.md)、[emit-expr-var 报告](experiments/cmc_emit_expr_var/REPORT.md)。')
old='| 5：指令与程序生成 | `cmc_concrete_emit_expr*.c`（leaf已完成）、';assert old in s
s=s.replace(old,f'| 已完成 | `cmc_concrete_emit_expr_var.c` | 一个变量表达式生成函数；{N["manual_top_level"]} 条手工义务、{N["manual_splits"]} 个 split、{N["automatic_witnesses"]} 条可信自动结果；新增公共定义 {len(N["new_model_declarations"])} 项、引理 {len(N["new_helpers"])} 条 |\n| 5：指令与程序生成 | `cmc_concrete_emit_expr*.c`（leaf、var已完成）、')
s=s.replace('emit-ast 与 emit-expr-leaf 的运行时部分已完成。下一候选为 `cmc_concrete_emit_expr_var.c`','emit-ast、emit-expr-leaf 与 emit-expr-var 的运行时部分已完成。下一候选为 `cmc_concrete_emit_expr_dispatch.c`');p.write_text(s)
p=W/'migration_inventory.csv';lines=p.read_bytes().splitlines(keepends=True);hits=0
for i,line in enumerate(lines):
 if line.startswith(b'/Users/nizitong/cmc/cmc_concrete_emit_expr_var.c,'):
  row=next(csv.reader([line.decode()]));row[4]=f'qcp_pipeline_verified_1_function_{N["manual_top_level"]}_manual_{N["automatic_witnesses"]}_trusted_auto'
  buf=io.StringIO(newline='');csv.writer(buf,lineterminator='\r\n'if line.endswith(b'\r\n')else'\n').writerow(row);lines[i]=buf.getvalue().encode();hits+=1
assert hits==1;p.write_bytes(b''.join(lines))
(R/'logs/documentation-update.diff').write_text(''.join(''.join(difflib.unified_diff(before[str(p)].splitlines(True),p.read_text().splitlines(True),fromfile=str(p),tofile=str(p)))for p in files));print('Updated verified var skill reference, plan, inventory.')
