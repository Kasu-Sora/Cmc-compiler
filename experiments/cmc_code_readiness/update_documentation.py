"""Update migration documents only after the completed proof audit."""
from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parent;W=R.parent.parent
S=Path('/Users/nizitong/.codex/skills/qcp-cstar-migration')
e=json.loads((R/'metrics/effort.json').read_text())
assert e['status']=='passed' and e['all_six_theorems_closed_under_global_context']
for p in [W/'MIGRATION_PLAN.md',W/'migration_inventory.csv',S/'SKILL.md']:
    assert p.read_bytes()==(R/'baseline'/p.name).read_bytes(),p
ref=S/'references/cmc-code-readiness-case.md';assert not ref.exists()
ref.write_text('''# 已验证案例：code_ready 的结构体／成员 readiness

2026-10-19 完成 `cmc_concrete_code_ready.c` 纯证明支持迁移。报告：`/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_code_readiness/REPORT.md`。目标库：`/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_code_ready_migration_lib.v`。

## 经验证的经验

- 先核对文件真正导出的性质。本文件虽叫 code_ready，主定理仅为 typed → structs-ready；完整 code-ready-from-wf 在 compile_ready 文件。本例不能标记整条 readiness 链完成。
- 不因源 thm 为 static 就把它当成可忽略的内部证明。cm_slots_nonnegative 和 cm_slots_safe 经头文件中的 getter 对外提供，必须保留完整陈述；本例同时核验所有三条公开定理和三条内部支持定理。
- cm_concrete_structs_ready 已在 function-pc-total 库定义，直接复用且检查展开方程。源 3 行／目标 1 行不再次计增量。
- 成员表示尺寸、带结构体环境的语义 slots_size、struct_slots_size 是三个不同表达式。复用 cm_slots_size_matches__temp_context 和 cm_slots_struct_size_matches，在相同 slots_wf 前提下串联；不能直接把它们当无条件相等。
- 原成员总尺寸上界是 1048576，与 data-ready 的 globals/strings 上界 1048560 不同。保留此界；从成员良构推出头部正尺寸，再证明尾部非负和尾部界，覆盖空列表。
- 非负性直接复用 cm_slots_size_nonnegative__call_bounds，无需重做列表归纳。保留原 representation-size 结论，用已有尺寸对应引理桥接。
- structs 环境与递归处理的 items 是不同参数，递归时不改变环境。head/tail 的原索引范围先保留，再用 Z2Nat.inj_succ 对应尾部查找。
- 纯支持模块的新增定理全部可放公共库，但“本模块 proof”与“额外公共依赖成本”不能重复相加。本例新增公共库六条定理的 63 行已全部计入模块 proof；额外依赖成本为 0。

## 结果与成本

C* 隔离重放、Rocq 编译、定义／六条签名审计、递归 coqchk 和正式路径编译均通过。六条定理 Print Assumptions 均为 Closed under the global context。没有新 Admitted/Axiom/Parameter/可信自动 witness；导入环境中的既有 QCP 公理未被这些定理依赖。

本模块 proof：C* 274 行（包括 11 行内部共用支持），Rocq 63 行；含声明及 Proof/Qed。新增定义 0，额外公共依赖定义／proof 0。旧四条尺寸／非负性引理实际复用。源 getter 12 行、框架注册／守卫 7 行、目标 imports 和验证 harness 排除。开发编译首次通过，历史工时未知。

运行时仍为 30 个实现单元、131 个函数；readiness 纯支持已完成 data_ready、program_ready、code_ready。下一依赖为 temp_ready，然后 function_ready、compile_ready。
''')
p=S/'SKILL.md';t=p.read_text();needle='这些结果覆盖三十个具体实现迁移单元'
entry='`cmc_concrete_code_ready.c` 于 2026-10-19 完成纯支持迁移。复用既有 structs-ready 定义，新增 6 条定理、63 行 proof，均经内核核验且无公理依赖；额外公共依赖新增成本为 0。处理 getter 导出的 static 定理、成员尺寸三种表示的桥接、1048576 上界或递归结构体环境时，读取 [references/cmc-code-readiness-case.md](references/cmc-code-readiness-case.md)。readiness 纯支持累计完成 data_ready、program_ready、code_ready 三项，运行时函数总数不变。\n\n'
assert needle in t;t=t.replace(needle,entry+needle,1);p.write_text(t)
p=W/'MIGRATION_PLAN.md';t=p.read_text()
needle='[migration_inventory.csv](migration_inventory.csv)'
t=t.replace(needle,'`cmc_concrete_code_ready.c` 的结构体／成员 readiness 也已完成：复用既有定义，新增 6 条定理、63 行 proof，完整内核和假设检查通过；额外公共依赖新增为 0。readiness 纯支持累计完成 3 项，见 [code-readiness 报告](experiments/cmc_code_readiness/REPORT.md)。\n\n'+needle,1)
old='| readiness 剩余支持 | `cmc_concrete_code_ready.c`、`cmc_concrete_temp_ready.c`、`cmc_concrete_function_ready.c`、`cmc_concrete_compile_ready.c` | 推出结构体／临时槽／函数／完整代码的 readiness；复用已有模型并补齐证明 |'
new='| 已完成纯支持 | `cmc_concrete_code_ready.c` | 保留三个公开定理及三个内部支持定理；复用定义；6 条无公理依赖定理、63 行 proof，额外公共依赖新增为 0 |\n| readiness 剩余支持 | `cmc_concrete_temp_ready.c`、`cmc_concrete_function_ready.c`、`cmc_concrete_compile_ready.c` | 推出临时槽／函数／完整代码的 readiness；复用已有模型并补齐证明 |'
assert old in t;t=t.replace(old,new)
old='data_ready 与 program_ready 的纯证明支持已完成。下一步推进 `cmc_concrete_code_ready.c`，并补齐 temp_ready → function_ready → compile_ready；随后接入顶层 `cmc_compile` 和保持性依赖。'
new='data_ready、program_ready 与 code_ready 的纯证明支持已完成。下一步推进 `cmc_concrete_temp_ready.c`，再补齐 function_ready → compile_ready；随后接入顶层 `cmc_compile` 和保持性依赖。'
assert old in t;t=t.replace(old,new).replace('本轮进一步补齐 typed → data-ready；','现已补齐 typed → data-ready 与 typed → structs-ready；');p.write_text(t)
p=W/'migration_inventory.csv';lines=p.read_bytes().splitlines(keepends=True);count=0
for i,line in enumerate(lines):
    if line.startswith(b'/Users/nizitong/cmc/cmc_concrete_code_ready.c,'):
        assert b',not_migrated,' in line
        lines[i]=line.replace(b',not_migrated,',b',rocq_kernel_verified_pure_support_reused_definition_6_theorems_no_assumptions,');count+=1
assert count==1;p.write_bytes(b''.join(lines))
(R/'metrics/documentation-update.json').write_text(json.dumps({'updated_after_verification':True,'changed_inventory_units':['cmc_concrete_code_ready.c'],'runtime_units':30,'runtime_functions':131,'readiness_pure_support_units':3,'files':[{'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}for p in [S/'SKILL.md',ref,W/'MIGRATION_PLAN.md',W/'migration_inventory.csv']]},indent=2)+'\n')
print('Published verified code-ready support; runtime counts unchanged.')
