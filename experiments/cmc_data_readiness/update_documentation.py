"""Publish only kernel-verified pure-support results."""
from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parent;W=R.parent.parent
S=Path('/Users/nizitong/.codex/skills/qcp-cstar-migration')
e=json.loads((R/'metrics/effort.json').read_text())
assert e['status']=='passed' and e['all_nine_theorems_closed_under_global_context']
for p in [W/'MIGRATION_PLAN.md',W/'migration_inventory.csv',S/'SKILL.md']:
    assert p.read_bytes()==(R/'baseline'/p.name).read_bytes(),p
ref=S/'references/cmc-data-readiness-case.md';assert not ref.exists()
ref.write_text('''# 已验证案例：data/program readiness 纯证明支持

2026-10-19 完成 `cmc_concrete_data_ready.c` 的完整定义复用核验和 `cmc_concrete_program_ready.c` 的公开定义、主定理及必要证明支持。
报告：`/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_data_readiness/REPORT.md`。
正式库：`/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_program_ready_migration_lib.v`。

## 适用经验

- 这两个源文件全是 PROOF 内容，没有运行时函数。按纯 Rocq 支持模块验证，不创建虚假的 C wrapper 或宣称完成 C VC。仓库单个 C 验证任务仍须走其 controller；本例保存 coqc、递归 coqchk、签名检查和 Print Assumptions 的完整记录。
- 先查旧公共库。data_ready 的 cm_data_globals_wf 已在 emit-globals 中精确实现，nil/cons 方程经转换检查通过；新增成本为 0。不能把旧 CSV 的 not_migrated 当成所有内容都未迁移。
- 主定理仅以 cm_typed_program policy p 为前提，推出 cm_concrete_data_ready p 的七个原结论。保持 16 字节静态起点、1048576 总界与 8 字节实际数据前缀的区别；由此导出 globals + strings <=1048560，不能把界值直接当新前提。
- 复用 emit-expr-leaf 的 cm_rep_globals_size_matches 和 emit-globals 的 cm_rep_global_size_matches。数组式索引全称条件转结构递归条件时，先用合法索引界，再以 Z2Nat.inj_succ 处理尾列表。
- 直接证明已有 cm_global_bytes 的实际列表长度。初始化、填充和零初始化分支都要覆盖。这里只需要非负 global size；不为模仿源证明形状新增另一套模型大小定义，也不声称更一般的 codegen 定理已全量迁移。
- Zlength_correct 应定位到 repeat 后缀，避免先改写初始化字节的长度；最后处理加法结合。错误修复属于 proof 开发成本，不能更改原规格。
- coqchk 的导入环境可能包含既有 QCP 框架公理。另以 Print Assumptions 检查实际交付定理；本例全部 9 条为 Closed under the global context，不受那些未使用框架公理影响。

## 验证和计量

C* 隔离重放 program_ready（包含 data_ready）通过；Rocq 8.20.1 编译、完整递归 coqchk、正式路径编译和定义／签名检查通过。新增 1 定义、1 主定理及 8 helper，无 Admitted/Axiom/Parameter/可信自动 witness。

非空行：readiness 新定义 C* 13 / Rocq 11；模块 proof 417 / 76；新增公共长度支持定义 21 / 0、proof 138 / 33。目标总 proof 109 行，全部在公共库；76 与 33 是总量拆分，不重复计费。data_ready 旧定义 10 / 6 行已在此前计费，本轮增量 0。开发编译 4 次、失败 3 次。验证 harness、导入、getters 和注册／守卫另列；历史工时未知。

这两个纯支持单元不增加运行时函数数。剩余 readiness 是 code_ready、temp_ready、function_ready、compile_ready；顶层编译及保持性仍未完成。
''')
p=S/'SKILL.md';t=p.read_text()
needle='QCP 导出的 proof_auto 中可能使用 Admitted'
insert='纯 `PROOF` 支持文件没有运行时函数时，按数学库交付并记录 Rocq 编译、内核检查、定理签名和实际假设；不制造 C wrapper 或把纯证明模块计入运行时函数数。已有定义直接复用，核验完成与新增成本分开记录。\n\n'
assert needle in t;t=t.replace(needle,insert+needle,1)
needle='这些结果覆盖三十个具体实现迁移单元'
entry='`cmc_concrete_data_ready.c` 与 `cmc_concrete_program_ready.c` 于 2026-10-19 完成两个纯支持单元。前者完整复用既有定义；后者新增 1 项定义、9 条内核核验且无公理依赖的定理。涉及 typed → data-ready、原始容量界、实际字节长度或纯证明模块计量时，读取 [references/cmc-data-readiness-case.md](references/cmc-data-readiness-case.md)。这两个支持单元不增加运行时函数数。\n\n'
assert needle in t;t=t.replace(needle,entry+needle,1);p.write_text(t)
p=W/'MIGRATION_PLAN.md';t=p.read_text()
needle='[migration_inventory.csv](migration_inventory.csv)'
t=t.replace(needle,'另完成 `cmc_concrete_data_ready.c`（复用既有定义）与 `cmc_concrete_program_ready.c` 两个纯证明支持单元：新增 1 项定义和 9 条定理，coqc／递归 coqchk／实际假设检查通过，未新增可信自动 witness。运行时仍为 30 个实现单元、131 个函数。见 [数据 readiness 报告](experiments/cmc_data_readiness/REPORT.md)。\n\n'+needle,1)
needle='| 贯穿各批：模型和支持引理 |'
rows='| 已完成纯支持 | `cmc_concrete_data_ready.c` | 精确复用 cm_data_globals_wf，核验 nil/cons 方程；新增成本 0 |\n| 已完成纯支持 | `cmc_concrete_program_ready.c` | typed → data-ready 原七项结论；1 定义、9 条无公理依赖定理，新增公共 proof 109 行 |\n| readiness 剩余支持 | `cmc_concrete_code_ready.c`、`cmc_concrete_temp_ready.c`、`cmc_concrete_function_ready.c`、`cmc_concrete_compile_ready.c` | 推出结构体／临时槽／函数／完整代码的 readiness；复用已有模型并补齐证明 |\n'
assert needle in t;t=t.replace(needle,rows+needle,1).replace('、`cmc_concrete_*ready.c` |',' |')
old='下一步应审查 `cmc_compile` 及其 readiness／保持性依赖闭包，再确定下一验证单元。'
new='data_ready 与 program_ready 的纯证明支持已完成。下一步推进 `cmc_concrete_code_ready.c`，并补齐 temp_ready → function_ready → compile_ready；随后接入顶层 `cmc_compile` 和保持性依赖。'
assert old in t;t=t.replace(old,new)
t=t.replace('本轮 patch-calls 已连接 resolved 逻辑视图与实际回填缓冲区；完整 readiness 桥、顶层组合、保持性及具体 TVM 实例化仍待后续迁移。','patch-calls 已连接 resolved 逻辑视图与实际回填缓冲区，本轮进一步补齐 typed → data-ready；其余 readiness、顶层组合、保持性及具体 TVM 实例化仍待后续迁移。');p.write_text(t)
p=W/'migration_inventory.csv';lines=p.read_bytes().splitlines(keepends=True)
updates={'cmc_concrete_data_ready.c':'rocq_verified_reused_definition_data_globals_wf','cmc_concrete_program_ready.c':'rocq_kernel_verified_pure_support_1_definition_9_theorems_no_assumptions'}
changed=[]
for i,line in enumerate(lines):
    for name,status in updates.items():
        if line.startswith(('/Users/nizitong/cmc/'+name+',').encode()):
            assert b',not_migrated,' in line
            lines[i]=line.replace(b',not_migrated,',(','+status+',').encode());changed.append(name)
assert set(changed)==set(updates);p.write_bytes(b''.join(lines))
(R/'metrics/documentation-update.json').write_text(json.dumps({'updated_after_verification':True,'changed_inventory_units':changed,'runtime_units':30,'runtime_functions':131,'pure_support_units_added':2,'files':[{'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}for p in [S/'SKILL.md',ref,W/'MIGRATION_PLAN.md',W/'migration_inventory.csv']]},indent=2)+'\n')
print('Published two verified pure-support units; runtime counts unchanged.')
