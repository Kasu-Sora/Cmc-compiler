"""Record the completed case only after final-check and measurement."""
import hashlib,json
from pathlib import Path
R=Path(__file__).resolve().parent
W=R.parent.parent
S=Path('/Users/nizitong/.codex/skills/qcp-cstar-migration')
x=json.loads((R/'metrics/effort.json').read_text())
assert x['verification']['phase']=='done' and x['verification']['qcp_final_check']['status']=='passed'
for item in json.loads((R/'metrics/documentation-baseline.json').read_text()):
 assert hashlib.sha256(Path(item['path']).read_bytes()).hexdigest()==item['sha256'], item['path']
p=S/'SKILL.md';t=p.read_text()
t=t.replace('emit-expr-simple 各一个函数；','emit-expr-simple 各一个函数及 emit-expr-call 的三个函数；')
t=t.replace('emit-expr-simple 为 `cmc_emit_expr_simple_migration.c`。','emit-expr-simple 为 `cmc_emit_expr_simple_migration.c`，emit-expr-call 为 `cmc_emit_expr_call_migration.c`。')
entry='`cmc_concrete_emit_expr_call.c` 于 2026-10-18 完成三个运行时函数的模块化验证。涉及任意表达式参数、嵌套递归代码模型、临时槽和参数链表恢复时，读取 [references/cmc-emit-expr-call-case.md](references/cmc-emit-expr-call-case.md)。本例完成 21 条顶层手工义务、43 个 split，另有 60 条可信自动结果；新增公共定义 12 项、引理 10 条。通用 `cm_emit_expr` 的原外部契约保留，其实现证明仍待迁移。\n\n'
t=t.replace('这些结果覆盖二十个具体实现文件的运行时部分、107 个运行时函数',entry+'这些结果覆盖二十一个具体实现文件的运行时部分、110 个运行时函数')
p.write_text(t)
(S/'references/cmc-emit-expr-call-case.md').write_text('''# 已验证案例：emit-expr-call，C* → QCP

2026-10-18 完成 cmc_concrete_emit_expr_call.c 的三个运行时函数：cm_emit_args_reload_plan、cm_emit_args_store_plan、cm_emit_call_expr。C* 隔离重放通过；QCP run `cmc_emit_expr_call_migration-20261018170809` 为 done、final-check passed。证据见 `/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_emit_expr_call/REPORT.md`。

## 契约、模型与复用

参数可为任意原契约允许的表达式，不能为了沿用 simple 模型而限制参数种类。保留 lvalue 两分支、全部 wf/typed/counts 与表示安全事实、槽布局、全局区大小、temp/scratch/temp_limit 和 PC 起止界，以及完整上下文所有权和任意计划 tail。既有 lookup policy 和 codegen obligations 参数化边界不变。

复用 cm_args_length、cm_expr_rvalue_count_context、temp load/store plan、call plan 的已验证 BODY 契约。本例仍按原头文件契约调用通用 cm_emit_expr，其函数体尚未迁移。这是原有的模块依赖边界，不代表整个递归 emitter 已验证。新增的 14 构造子一般表达式代码模型是数学定义，不代替实现证明，也不构成 HOL→Rocq 等价或 TVM 保持性定理。

复用 layout/counts 的表达式资源、临时深度和调用事实引理，以及已有 primitive、leaf/var 和 opcode 模型。实际 manual 引用 cm_expr_rep_node、cm_expr_tpair_call、cm_expr_wf_call、cm_expr_counts_repr_call；旧库没有变更，旧 helper 的 manual/auto 不导入也不重复计费。

## 本例可复用经验

- 嵌套 Call 参数列表的代码模型用内部 list fixpoint；单独的 args-store 定义与它的等式需要列表归纳。先泛化 pc、slot、scratch，再归纳；不能直接要求两个不同 fixpoint reflexivity。
- 一般表达式的 lcode/rcode 长度同时证明。递归经过表达式和嵌套参数列表，保持 pc/temp 可变，再用内部列表归纳处理 Call。得到无额外 wf 前提的长度／count 等式后，可复用它证明参数执行后的 PC 安全。
- 参数列表非空分支先展开 head/tail，再开合 cm_arg_list_rep；空指针推出 nil 的纯目标依赖空间资源，若生成的 split 丢失这项资源，按 VC 路线证明原顶层义务。本例两个未采用的 split 保留 Abort，父义务均已 Qed；不可把 Abort 当作未完成顶层证明。
- 保持 opaque emitter plan 的关联方向和 singleton tail 形状，使用 append 归一化后 cancel。which-implies 的局部变量替换和存在变量范围应与后续调用所需资源一致；不要用增强前提解决符号执行困难。
- 调用编号的 signed-int 范围从原 counts 事实导出；temp_limit 的上界可从槽大小非负与 temp_offset 推出，不增加入口条件。

## 验证与计量

21 条顶层手工义务、43 个 split 完成；60 条自动 witness 以 Admitted 导出，保留 QCP 自动层信任。manual 和新增公共库无 Admitted/Axiom/Parameter。七组、合并全量检查和终检均通过。

| 非空行 | C* | QCP |
|---|---:|---:|
| Specification | 180 | 51 |
| 函数体 annotation | 35 | 40 |
| helper 接入 annotation | 0（include） | 36 |
| 案例 proof | 988 | 613 |
| 公共 proof 增量 | 404 | 134 |

C* 案例 proof 含内嵌 515 行和同文件私有辅助 473 行。QCP 新增公共定义 12 项／74 行，引理 10 条／134 行；其中标注阶段为 74 行定义及 36 行引理，证明阶段增加五条引理／98 行。源新增模型闭包 175 行，另有三项私有观察定义／7 行；此前 leaf/var、primitive 和 AST/count 模型不再计入。未被 manual 直接调用的新增引理仍计成本，逐项引用与区间见 effort.json。

非空行受格式、声明包装和证明风格影响，不等于工时。生成 VC 排除在手写 proof 之外；外部声明、导入和实际命令失败修复另列。未知历史工时与不可测活跃时间为 null。
''')
p=W/'MIGRATION_PLAN.md';t=p.read_text()
t=t.replace('emit-expr-simple 各一个函数，共二十个具体实现文件的运行时部分、107 个运行时函数','emit-expr-simple 各一个函数及 emit-expr-call 的三个函数，共二十一个具体实现文件的运行时部分、110 个运行时函数')
t=t.replace('49、22、28、14 条可信自动 witness','49、22、28、14、60 条可信自动 witness')
t=t.replace('[emit-expr-simple 报告](experiments/cmc_emit_expr_simple/REPORT.md)。','[emit-expr-simple 报告](experiments/cmc_emit_expr_simple/REPORT.md)、[emit-expr-call 报告](experiments/cmc_emit_expr_call/REPORT.md)。')
t=t.replace('| 5：指令与程序生成 |','| 已完成模块化验证 | `cmc_concrete_emit_expr_call.c` | 三个运行时函数；21 条手工义务、43 个 split、60 条可信自动结果；新增公共定义 12 项、引理 10 条；通用 cm_emit_expr 实现仍为待迁移依赖 |\n| 5：指令与程序生成 |')
t=t.replace('（leaf、var、dispatch、simple已完成）','（leaf、var、dispatch、simple 已完成；call 已完成模块化验证）')
t=t.replace('emit-expr-dispatch 与 emit-expr-simple 的运行时部分已完成。下一候选为 `cmc_concrete_emit_expr_call.c`','emit-expr-dispatch、emit-expr-simple 与 emit-expr-call 的运行时部分已完成模块化验证。下一候选为 `cmc_concrete_emit_binary_finish.c`，之后迁移通用 `cmc_concrete_emit_expr.c` 以补齐 call 的外部实现依赖')
t=t.replace('完整指令 emitter 语义、readiness 长度桥的 Rocq 重证及具体 TVM 实例化仍待后续迁移。','本轮已补齐一般表达式代码模型及代码长度／count 定理，完整指令 emitter 的其余语义、readiness 桥及具体 TVM 实例化仍待后续迁移。')
p.write_text(t)
p=W/'migration_inventory.csv';raw=p.read_bytes();rows=raw.splitlines(keepends=True)
for i,row in enumerate(rows):
 if row.startswith(b'/Users/nizitong/cmc/cmc_concrete_emit_expr_call.c,'):
  assert b',not_migrated,' in row
  rows[i]=row.replace(b',not_migrated,',b',qcp_pipeline_verified_3_functions_21_manual_60_trusted_auto_external_cm_emit_expr_pending,')
  break
else:raise AssertionError('missing inventory row')
p.write_bytes(b''.join(rows))
print('Updated skill, case reference, plan and exact inventory row after final-check passed.')
