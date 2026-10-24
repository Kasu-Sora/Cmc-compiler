"""Update skill and inventory only after all formal checks have passed."""
from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parent;W=R.parent.parent
S=Path('/Users/nizitong/.codex/skills/qcp-cstar-migration')
e=json.loads((R/'metrics/effort.json').read_text())
assert e['status']=='passed' and e['all_thirteen_theorems_closed_under_global_context']
assert e['source_proof_lines']==788 and e['target_proof_lines']==146
for p in [W/'MIGRATION_PLAN.md',W/'migration_inventory.csv',S/'SKILL.md']:
 assert p.read_bytes()==(R/'baseline'/p.name).read_bytes(),p
ref=S/'references/cmc-temp-readiness-case.md';assert not ref.exists()
ref.write_text('''# 已验证案例：temp_ready 的计数 → 临时槽安全

2026-10-19 完成 `cmc_concrete_temp_ready.c` 纯证明模块迁移。报告：`/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_temp_readiness/REPORT.md`。目标库：`/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_temp_ready_migration_lib.v`。

## 已验证的迁移经验

- 保留四条公开陈述。expr/args/stmt 的唯一前提分别是原递归 counts_representable；输出同时含临时槽安全和代码计数界，stmt 另有安全投影。不要为方便递归添加 typed_program、合法 fid/callee 或已有 temps_safe 前提。
- count 与临时槽模型已在 counts/layout 中验证，直接复用。非负性用已有 cm_expr_temps_nonnegative__index_bounds、cm_expr_code_counts_nonnegative、cm_char_normalize_count_nonnegative，pair 投影用 cm_args_pair_safe__expr_safety，均无新依赖成本。
- 嵌套 AST 中的 Call 参数为 list cm_expr，常规 expr induction 不自动提供列表元素的假设。本例使用结构递归 fix IH 2，并在 Call 分支内做参数列表归纳，使 IH 应用于结构子表达式；Rocq 的 guardedness 检查通过。内部 cons-step 算术与独立 args 定理共用，避免复制整段 list 算术。
- Call 分支复用 cm_expr_counts_repr_call、cm_expr_safe_call、cm_expr_tpair_call 和 cm_expr_counts_call，统一嵌套 fix 与命名列表函数。展开前先应用这些方程，避免把不同表示误当作新模型。
- 不能只证明总 temp 数量不超过 INT_MAX。还须保留右子表达式严格界（短路 binary 也需要）和参数尾 arity 严格界；args 的 count、depth、count+depth 三项界均保留。cons-step 从代码计数预算和非负性导出这些界。
- stmt 的初始化与 return 分支分别用局部 slot 类型和函数返回类型的字符规范化计数非负性；两者来源不同。保留全部 11 个 stmt 构造子与 stemps<=code_count 结论。
- cbn 对包装定义及算术表达式未必完全展开。先 unfold cm_args_temps／cm_rep_apair_safe／cm_rvalue_code_count，再化简 record 投影，使 lia 能见到同一项；失败时检查实际剩余目标，不改规格迁就 tactic。
- 任意 lookup policy 的既有参数化保持不变。13 条最终定理均 Print Assumptions 为 Closed under the global context；导入框架含公理不等于本例实际依赖公理。

## 结果与成本

C* 隔离重放、Rocq 模块编译、全部 13 条签名与实际假设审计、递归 coqchk 和正式路径编译通过。原四条公开定理、七条内部支持定理及 expr/args 合取定理保留，目标另加一条 cons-step 引理。未新增定义、Admitted、Axiom、Parameter 或可信自动 witness。

本模块 proof：C* 788 行、Rocq 146 行，含声明和 Proof/Qed；C* 同文件共享支持 121 行、目标 cons-step 19 行均只在模块内计一次。新增公共库总 proof 就是这 146 行，额外公共依赖定义／proof 增量均为 0。旧引理实际引用、逐组和逐定理成本在报告中可追溯。源框架守卫 5 行、目标导入与 audit harness 排除。13 次开发编译中 11 次失败（含定位输出），全部日志保留；历史工时未知。

运行时仍为 30 个实现单元、131 个函数；readiness 纯支持累计四项：data_ready、program_ready、code_ready、temp_ready。后续为 function_ready、compile_ready；不能据此宣布完整编译正确性或 TVM 语义证明已迁移。
''')
p=S/'SKILL.md';t=p.read_text();needle='这些结果覆盖三十个具体实现迁移单元'
entry='`cmc_concrete_temp_ready.c` 于 2026-10-19 完成纯支持迁移。保留四条公开定理，新增目标定理共 13 条、146 行 proof，全部经内核核验且无公理依赖；新增定义与额外公共依赖成本为 0。处理计数到临时槽安全、嵌套表达式／参数列表递归、严格尾部界或 stmt 临时槽界时，读取 [references/cmc-temp-readiness-case.md](references/cmc-temp-readiness-case.md)。readiness 纯支持累计四项，运行时函数总数不变。\n\n'
assert needle in t;t=t.replace(needle,entry+needle,1);p.write_text(t)
p=W/'MIGRATION_PLAN.md';t=p.read_text();needle='[migration_inventory.csv](migration_inventory.csv)'
assert needle in t
t=t.replace(needle,'`cmc_concrete_temp_ready.c` 的计数 → 临时槽安全证明已完成：原四条公开陈述保留，共 13 条无公理依赖目标定理；C*／Rocq proof 为 788／146 行，额外公共依赖新增为 0。readiness 纯支持累计 4 项，见 [temp-readiness 报告](experiments/cmc_temp_readiness/REPORT.md)。\n\n'+needle,1)
old='| readiness 剩余支持 | `cmc_concrete_temp_ready.c`、`cmc_concrete_function_ready.c`、`cmc_concrete_compile_ready.c` | 推出临时槽／函数／完整代码的 readiness；复用已有模型并补齐证明 |'
new='| 已完成纯支持 | `cmc_concrete_temp_ready.c` | 原四条公开定理保留；共 13 条无公理依赖目标定理、146 行 proof，新增定义及额外公共依赖为 0 |\n| readiness 剩余支持 | `cmc_concrete_function_ready.c`、`cmc_concrete_compile_ready.c` | 推出函数／完整代码的 readiness；复用已有模型并补齐证明 |'
assert old in t;t=t.replace(old,new)
old='data_ready、program_ready 与 code_ready 的纯证明支持已完成。下一步推进 `cmc_concrete_temp_ready.c`，再补齐 function_ready → compile_ready；'
new='data_ready、program_ready、code_ready 与 temp_ready 的纯证明支持已完成。下一步推进 `cmc_concrete_function_ready.c`，再补齐 compile_ready；'
assert old in t;t=t.replace(old,new).replace('现已补齐 typed → data-ready 与 typed → structs-ready；','现已补齐 typed → data-ready、typed → structs-ready 与 counts → temps-ready；');p.write_text(t)
p=W/'migration_inventory.csv';lines=p.read_bytes().splitlines(keepends=True);count=0
for i,line in enumerate(lines):
 if line.startswith(b'/Users/nizitong/cmc/cmc_concrete_temp_ready.c,'):
  assert b',not_migrated,' in line
  lines[i]=line.replace(b',not_migrated,',b',rocq_kernel_verified_pure_support_13_theorems_no_assumptions,');count+=1
assert count==1;p.write_bytes(b''.join(lines))
(R/'metrics/documentation-update.json').write_text(json.dumps(dict(updated_after_verification=True,changed_inventory_units=['cmc_concrete_temp_ready.c'],runtime_units=30,runtime_functions=131,readiness_pure_support_units=4,files=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest())for p in [S/'SKILL.md',ref,W/'MIGRATION_PLAN.md',W/'migration_inventory.csv']]),indent=2)+'\n')
print('Published verified temp-ready support; runtime counts unchanged.')
