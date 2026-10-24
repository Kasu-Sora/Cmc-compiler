"""Update skill and inventory only from a completed, audited verification run."""
import hashlib,json
from pathlib import Path
R=Path(__file__).resolve().parent;W=R.parent.parent;S=Path('/Users/nizitong/.codex/skills/qcp-cstar-migration')
x=json.loads((R/'metrics/effort.json').read_text());q=x['counts']['qcp'];e=x['entries'];run=json.loads((R/'metrics/run.json').read_text())['run_id']
assert x['verification']['phase']=='done' and x['verification']['qcp_final_check']['status']=='passed'
for row in json.loads((R/'metrics/documentation-baseline.json').read_text()):assert hashlib.sha256(Path(row['path']).read_bytes()).hexdigest()==row['sha256']
case=f'''# 已验证案例：emit-binary-finish，C* → QCP

2026-10-18 完成 cmc_concrete_emit_binary_finish.c 三个运行时函数（两个 static helper）：cm_pointer_scale_value、cm_emit_binary_generic_fragment、cm_emit_binary_finish_plan。C* 重放通过；QCP run `{run}` 为 done、final-check passed。报告：`/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_emit_binary_finish/REPORT.md`。

## 保持的语义与复用

原契约允许任意 int op，并未要求左右表达式组成合法二元表达式，也没有 scale 正数前提。迁移保持这个域、全部类型/slot/安全事实、总 fid 查询、program/function/两个 expression 的所有权，以及精确的计划消费、done 追加与任意 tail。此处验证指令生成，不代表生成的 TVM 指针算术执行安全或编译保持性。

直接导入上一例 cmc_emit_expr_call_migration_lib 中的 cm_pointer_scale、cm_binary_finish_code；沿用 counts/layout/leaf/core/plan 模型。七个 helper 使用已验证 BODY 契约：类型编码观察位于 count-context，类型大小位于 leaf，pointee/指针判断位于 layout，binary opcode 位于 core，计划写入/temp load 位于 plan。不要从相邻源码头文件推断目标 helper 所在库。此单元无待迁移的外部实现依赖；导入 call 模型库不意味着运行时调用 cm_emit_expr。

## 本例经验

QCP helper 要求 cons 形式的计划前缀时，显式 app/cons 的等式可能需要 which-implies 桥才能匹配。分支中将 op 等式与 opaque plan 同放在局部推导前提，可能导致 partial solver 只在目标谓词中替换成常量。本例使用等价上下界保留 op 的符号身份；这属于内部断言调整，不增加入口约束。实际验证后的完整过程和失败次数见 process-notes.json。

## 计量与信任

{e['manual_top_level']} 条顶层手工义务、{e['manual_splits']} 个 split 完成；{e['automatic_witnesses']} 条自动 witness 以 Admitted 导出，保留 QCP 自动层信任。manual 和新增公共库无 Admitted/Axiom/Parameter。

| 非空行 | C* | QCP |
|---|---:|---:|
| Specification | 122 | {q['specification']} |
| 函数体 annotation | 89 | {q['annotation']} |
| helper 接入 annotation | 0（include） | {q['integration_helper_specification']} |
| 案例 proof | 388 | {q['case_proof']} |
| 公共 proof 增量 | 66 | {q['new_common_proof']} |

C* 案例 proof 含 336 行内嵌证明和 52 行私有支持。QCP 新增公共定义 {len(e['new_model_declarations'])} 项／{q['new_common_definitions']} 行，引理 {len(e['new_helpers'])} 条／{q['new_common_proof']} 行；以最终合并库计数，既有库增量为零。源新增模型 0 行、pointee 编码/wf/refs 公共证明闭包 66 行。既有 pointer bridge、binary-finish 模型和 helper 实现不重复计费。行数不是工时；未知历史时间为 null。
'''
(S/'references/cmc-emit-binary-finish-case.md').write_text(case)
p=S/'SKILL.md';t=p.read_text().replace('及 emit-expr-call 的三个函数；','及 emit-expr-call、emit-binary-finish 各三个函数；').replace('emit-expr-call 为 `cmc_emit_expr_call_migration.c`。','emit-expr-call 为 `cmc_emit_expr_call_migration.c`，emit-binary-finish 为 `cmc_emit_binary_finish_migration.c`。')
entry=f'`cmc_concrete_emit_binary_finish.c` 于 2026-10-18 完成三个运行时函数验证。涉及指针缩放、任意二元 op、类型编码衔接及 opaque 计划分支匹配时，读取 [references/cmc-emit-binary-finish-case.md](references/cmc-emit-binary-finish-case.md)。完成 {e["manual_top_level"]} 条顶层手工义务、{e["manual_splits"]} 个 split，另有 {e["automatic_witnesses"]} 条可信自动结果；新增公共定义 {len(e["new_model_declarations"])} 项、引理 {len(e["new_helpers"])} 条。\n\n'
t=t.replace('这些结果覆盖二十一个具体实现文件的运行时部分、110 个运行时函数',entry+'这些结果覆盖二十二个具体实现文件的运行时部分、113 个运行时函数');p.write_text(t)
p=W/'MIGRATION_PLAN.md';t=p.read_text().replace('及 emit-expr-call 的三个函数，共二十一个具体实现文件的运行时部分、110 个运行时函数','及 emit-expr-call、emit-binary-finish 各三个函数，共二十二个具体实现文件的运行时部分、113 个运行时函数').replace('28、14、60 条可信自动 witness',f'28、14、60、{e["automatic_witnesses"]} 条可信自动 witness').replace('[emit-expr-call 报告](experiments/cmc_emit_expr_call/REPORT.md)。','[emit-expr-call 报告](experiments/cmc_emit_expr_call/REPORT.md)、[emit-binary-finish 报告](experiments/cmc_emit_binary_finish/REPORT.md)。')
t=t.replace('| 5：指令与程序生成 |',f'| 已完成 | `cmc_concrete_emit_binary_finish.c` | 三个运行时函数；{e["manual_top_level"]} 条手工义务、{e["manual_splits"]} 个 split、{e["automatic_witnesses"]} 条可信自动结果；复用 binary-finish/scale 模型；新增公共定义 {len(e["new_model_declarations"])} 项、引理 {len(e["new_helpers"])} 条 |\n| 5：指令与程序生成 |')
t=t.replace('、`cmc_concrete_emit_binary_finish.c`、`cmc_concrete_emit_return.c`','、`cmc_concrete_emit_return.c`')
t=t.replace(' 与 emit-expr-call 的运行时部分已完成模块化验证。下一候选为 `cmc_concrete_emit_binary_finish.c`，之后迁移通用 `cmc_concrete_emit_expr.c` 以补齐 call 的外部实现依赖','、emit-expr-call 与 emit-binary-finish 的运行时部分已完成模块化验证。下一候选为通用 `cmc_concrete_emit_expr.c`，以补齐 call 的外部实现依赖');t=t.replace('本轮已补齐一般表达式代码模型及代码长度／count 定理','已迁移的一般表达式代码模型及代码长度／count 定理在本轮直接复用');p.write_text(t)
p=W/'migration_inventory.csv';rows=p.read_bytes().splitlines(keepends=True)
for i,row in enumerate(rows):
 if row.startswith(b'/Users/nizitong/cmc/cmc_concrete_emit_binary_finish.c,'):
  assert b',not_migrated,'in row;rows[i]=row.replace(b',not_migrated,',f',qcp_pipeline_verified_3_functions_{e["manual_top_level"]}_manual_{e["automatic_witnesses"]}_trusted_auto,'.encode());break
else:raise AssertionError('Missing inventory row')
p.write_bytes(b''.join(rows))
print('Updated skill, case reference, plan and exact inventory row.')
