from pathlib import Path
import json,csv,io,shutil,difflib
R=Path(__file__).resolve().parent;W=R.parent.parent;S=Path('/Users/nizitong/.codex/skills/qcp-cstar-migration')
E=json.loads((R/'metrics/effort.json').read_text());A=json.loads((R/'metrics/semantic-audit.json').read_text());assert E['verification']['phase']=='done' and A['final_verification']['status']=='passed'
C=E['counts']['cstar'];Q=E['counts']['qcp'];N=E['entries'];run=json.loads((R/'metrics/run.json').read_text())['run_id']
files=[S/'SKILL.md',S/'references/cmc-emit-expr-simple-case.md',W/'MIGRATION_PLAN.md',W/'migration_inventory.csv'];before={str(p):p.read_text()if p.exists()else''for p in files};b=R/'baseline/documentation-before';b.mkdir(exist_ok=True)
for p in files:
 if p.exists():shutil.copy2(p,b/p.name)
text=f'''# 已验证案例：emit-expr-simple，C* → QCP

2026-10-18 完成 cmc_concrete_emit_expr_simple.c 唯一运行时函数 cm_emit_simple_expr。C* 隔离重放通过；QCP run `{run}` 为 done、final-check passed。证据见 `/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_emit_expr_simple/REPORT.md`。

## 契约与复用

Simple 域为已验证 leaf 域或 kind=2 的变量。组合 leaf/var 代码模型时使用显式 simple view，证明原域恰好存在对应的表达式表示并保证唯一性；复用 dispatch 的 coverage/unique。不能把表示见证变成未证明的新输入约束，不能给其余构造子默认空代码并声称完整递归表达式模型。

两个 helper 分别使用已验证 cm_emit_leaf_expr、cm_emit_var_expr 的 BODY 契约。var 的 slot 范围和类型编码事实从原 counts 推出，binding_valid 从原 expr_wf 推出；leaf 分支复用既有域覆盖。保留原全部纯事实，包括 params/locals slots_wf、安全事实和全局数据总大小界，不因某个 helper 不使用就删除；完整三种上下文资源与任意 tail 始终保留。

simple 代码模型只组合已有 leaf/var 定义；这五种构造子的代码不依赖 pc/temp，C 参数仍保持。沿用现有 policy/codegen obligations，不重定义 wf_program。未导入旧 manual/auto，不重复计算 helper 实现 proof。该案例不构成完整递归 emitter 或 HOL→Rocq 元层等价定理。

## 本例标注经验

simple 计划依赖 fid，而 leaf 计划不依赖 fid。局部 which-implies 若只转换计划，可能消耗左侧提及的 fid 局部资源，使下一次 helper 调用无法读取它。本例在桥的两侧保留原有 expr_wf/counts 事实，使 fid 继续可见；不额外假定新事实。遇到同类从较多参数模型投影到较少参数模型的转换时，核对后续调用所需局部变量仍可读。Extern Coq 的类型声明与项声明分别放在不同块中。

表达式节点开合可先复用既有 cm_expr_rep_node，再展开 cm_expr_node、保留 payload 不展开，使用 sepcon_assoc_change 规范化后 cancel。本例不需逐个拆解所有表达式构造子，也不需新增资源引理。leaf 分支证明实际调用既有 cm_dispatch_leaf_coverage；新增 view 对应引理也复用原 dispatch coverage/unique。

## 验证与计量

{N['manual_top_level']} 条顶层手工义务、{N['manual_splits']} 个 split 完成；{N['automatic_witnesses']} 条自动 witness 以 Admitted 导出，依赖 QCP 自动层。manual 和新增公共库无 Admitted/Axiom/Parameter。

| 非空行 | C* | QCP |
|---|---:|---:|
| Specification | {C['specification']} | {Q['specification']} |
| 函数体 annotation | {C['annotation']} | {Q['annotation']} |
| helper 接入 annotation | 0（include） | {Q.get('integration_helper_specification',0)} |
| 案例 proof | {C['case_proof']} | {Q['case_proof']} |

QCP 新增公共定义 {len(N['new_model_declarations'])} 项/{Q['new_common_definitions']} 行，引理 {len(N['new_helpers'])} 条/{Q['new_common_proof']} 行。源新增 simple 判定3行；leaf/var 方程、count/shape 支持均不重复计算。源7个 where 条目占4个物理行，同类按行号去重。新增两条对应引理均已编译，manual 未直接调用，仍计费；逐引理引用和阶段成本见 effort.json；行数不是历史工时。
'''
(S/'references/cmc-emit-expr-simple-case.md').write_text(text)
p=S/'SKILL.md';s=p.read_text();assert 'references/cmc-emit-expr-simple-case.md'not in s
s=s.replace('emit-expr-var、emit-expr-dispatch 各一个函数；QCP','emit-expr-var、emit-expr-dispatch、emit-expr-simple 各一个函数；QCP').replace('emit-expr-dispatch 为 `cmc_emit_expr_dispatch_migration.c`。','emit-expr-dispatch 为 `cmc_emit_expr_dispatch_migration.c`，emit-expr-simple 为 `cmc_emit_expr_simple_migration.c`。')
entry=f'`cmc_concrete_emit_expr_simple.c` 于 2026-10-18 完成唯一运行时函数验证。涉及 leaf/var 视图组合、域覆盖与已有 helper 接入时，读取 [references/cmc-emit-expr-simple-case.md](references/cmc-emit-expr-simple-case.md)。本例完成 {N["manual_top_level"]} 条顶层手工义务、{N["manual_splits"]} 个 split，另有 {N["automatic_witnesses"]} 条可信自动结果；新增公共定义 {len(N["new_model_declarations"])} 项、引理 {len(N["new_helpers"])} 条。\n\n'
old='这些结果覆盖十九个具体实现文件的运行时部分、106 个运行时函数及必要依赖；';assert old in s;s=s.replace(old,entry+'这些结果覆盖二十个具体实现文件的运行时部分、107 个运行时函数及必要依赖；');p.write_text(s)
p=W/'MIGRATION_PLAN.md';s=p.read_text().replace('清点更新：2026-10-17','清点更新：2026-10-18').replace('emit-expr-var、emit-expr-dispatch 各一个函数，共十九个具体实现文件的运行时部分、106 个运行时函数','emit-expr-var、emit-expr-dispatch、emit-expr-simple 各一个函数，共二十个具体实现文件的运行时部分、107 个运行时函数').replace('49、22、28 条可信自动',f'49、22、28、{N["automatic_witnesses"]} 条可信自动').replace('[emit-expr-dispatch 报告](experiments/cmc_emit_expr_dispatch/REPORT.md)。','[emit-expr-dispatch 报告](experiments/cmc_emit_expr_dispatch/REPORT.md)、[emit-expr-simple 报告](experiments/cmc_emit_expr_simple/REPORT.md)。')
old='| 5：指令与程序生成 | `cmc_concrete_emit_expr*.c`（leaf、var、dispatch已完成）、';assert old in s
s=s.replace(old,f'| 已完成 | `cmc_concrete_emit_expr_simple.c` | 一个简单表达式生成函数；{N["manual_top_level"]} 条手工义务、{N["manual_splits"]} 个 split、{N["automatic_witnesses"]} 条可信自动结果；新增公共定义 {len(N["new_model_declarations"])} 项、引理 {len(N["new_helpers"])} 条 |\n| 5：指令与程序生成 | `cmc_concrete_emit_expr*.c`（leaf、var、dispatch、simple已完成）、')
s=s.replace('emit-expr-var 与 emit-expr-dispatch 的运行时部分已完成。下一候选为 `cmc_concrete_emit_expr_simple.c`','emit-expr-var、emit-expr-dispatch 与 emit-expr-simple 的运行时部分已完成。下一候选为 `cmc_concrete_emit_expr_call.c`');p.write_text(s)
p=W/'migration_inventory.csv';lines=p.read_bytes().splitlines(keepends=True);hits=0
for i,line in enumerate(lines):
 if line.startswith(b'/Users/nizitong/cmc/cmc_concrete_emit_expr_simple.c,'):
  row=next(csv.reader([line.decode()]));row[4]=f'qcp_pipeline_verified_1_function_{N["manual_top_level"]}_manual_{N["automatic_witnesses"]}_trusted_auto'
  buf=io.StringIO(newline='');csv.writer(buf,lineterminator='\r\n'if line.endswith(b'\r\n')else'\n').writerow(row);lines[i]=buf.getvalue().encode();hits+=1
assert hits==1;p.write_bytes(b''.join(lines))
(R/'logs/documentation-update.diff').write_text(''.join(''.join(difflib.unified_diff(before[str(p)].splitlines(True),p.read_text().splitlines(True),fromfile=str(p),tofile=str(p)))for p in files));print('Updated verified simple skill reference, plan, inventory.')
