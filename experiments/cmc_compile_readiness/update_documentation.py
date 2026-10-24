"""Update the migration record after successful proof and definition audit."""
from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parent;W=R.parent.parent;S=Path('/Users/nizitong/.codex/skills/qcp-cstar-migration')
e=json.loads((R/'metrics/effort.json').read_text())
assert e['status']=='passed' and e['theorem_and_definition_equivalence_closed_under_global_context']
assert (e['source_proof_lines'],e['target_proof_lines'])==(23,7)
for p in [W/'MIGRATION_PLAN.md',W/'migration_inventory.csv',S/'SKILL.md']:
 assert p.read_bytes()==(R/'baseline'/p.name).read_bytes(),p
ref=S/'references/cmc-compile-readiness-case.md';assert not ref.exists()
ref.write_text('''# 已验证案例：compile_ready 的组合证明

2026-10-19 完成 `cmc_concrete_compile_ready.c`。报告：`/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_compile_readiness/REPORT.md`。目标库：`/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_compile_ready_migration_lib.v`。

## 迁移要点

- 先看文件导出的实际性质。本文件定义 code_ready 并证明 wf_program → code_ready；它不包含运行时 cmc_compile 实现，也不是完整编译语义保持性定理。
- cm_concrete_code_ready 早在 function-pc-total 库中迁移。原定义仍为 structs_ready 与 functions_ready p 0 (program_functions p) 的合取，须核验起始编号 0 和完整程序函数列表，不新建平行定义。
- 主证明直接从原 wf_program 提取 typed_program，应用 cmc_structs_ready_from_typed，再用完整 wf_program 应用 cm_concrete_functions_ready_from_wf。复用二者即可得到全部结论，无需把前提改为额外的独立 structs/functions readiness 条件。
- 继续保留既有任意 lookup policy 与 codegen obligations 参数；四项 admissibility 义务仍在 wf_program 内。完成 readiness 支持链不能被描述为这些具体语义义务已全部证明。
- 定义核验不等于新增定义成本。原定义 C* 4 行／目标 2 行已在先前案例计量，本轮增量为 0；目标新定理 7 行计作模块 proof，不重复加在公共依赖中。

## 验证与成本

C* 隔离重放、Rocq 编译、精确签名与原定义方程检查、递归 coqchk（库和审计模块）、正式路径编译全部通过。主定理及定义等价证明均 Closed under the global context，无新增公理、Admitted 或可信自动 witness。

模块 proof 为 C* 23 行、Rocq 7 行；额外公共依赖 proof／定义新增均为 0。源 getter 3 行、框架注册与守卫 7 行、目标 import 与 audit harness 排除。Proof 含声明和 Proof/Qed。开发 coqc 首次通过，无失败；历史工时未知。

readiness 纯支持六项现已完成：data_ready、program_ready、code_ready、temp_ready、function_ready、compile_ready。运行时仍为 30 个实现单元、131 个函数。顶层 cmc_compile、语义保持性及具体 TVM 实例化仍须分别验证。
''')
p=S/'SKILL.md';t=p.read_text();needle='这些结果覆盖三十个具体实现迁移单元'
entry='`cmc_concrete_compile_ready.c` 于 2026-10-19 完成纯支持迁移。复用既有 code-ready 定义与两个 readiness 定理，新增 1 条无公理依赖定理、7 行 proof；额外公共依赖增量为 0。处理组合证明、已有定义的零增量计量或 readiness／顶层正确性范围时，读取 [references/cmc-compile-readiness-case.md](references/cmc-compile-readiness-case.md)。readiness 纯支持六项已完成，运行时函数总数不变。\n\n'
assert needle in t;t=t.replace(needle,entry+needle,1);p.write_text(t)
p=W/'MIGRATION_PLAN.md';t=p.read_text();needle='[migration_inventory.csv](migration_inventory.csv)';assert needle in t
t=t.replace(needle,'`cmc_concrete_compile_ready.c` 已完成：保持原 code-ready 定义与唯一 wf → code-ready 定理，C*／Rocq proof 23／7 行，额外公共依赖与定义增量为 0；内核和实际假设检查通过。readiness 纯支持六项已完成，见 [compile-readiness 报告](experiments/cmc_compile_readiness/REPORT.md)。\n\n'+needle,1)
old='| readiness 剩余支持 | `cmc_concrete_compile_ready.c` | 推出完整代码的 readiness；复用已有模型并补齐证明 |'
new='| 已完成纯支持 | `cmc_concrete_compile_ready.c` | 原定义等价核验与 wf → code-ready 组合定理；1 条无公理依赖定理、7 行 proof，额外公共依赖与定义增量为 0 |'
assert old in t;t=t.replace(old,new)
old='data_ready、program_ready、code_ready、temp_ready 与 function_ready 的纯证明支持已完成。下一步推进 `cmc_concrete_compile_ready.c`；随后接入顶层 `cmc_compile` 和保持性依赖。'
new='data_ready、program_ready、code_ready、temp_ready、function_ready 与 compile_ready 六项纯证明支持已完成。下一阶段接入顶层 `cmc_compile` 和剩余保持性依赖。'
assert old in t;t=t.replace(old,new).replace('counts → temps-ready 与 wf → functions-ready；其余 readiness、顶层组合、保持性及具体 TVM 实例化仍待后续迁移。','counts → temps-ready、wf → functions-ready 与 wf → code-ready；顶层组合、保持性及具体 TVM 实例化仍待后续迁移。');p.write_text(t)
p=W/'migration_inventory.csv';lines=p.read_bytes().splitlines(keepends=True);count=0
for i,line in enumerate(lines):
 if line.startswith(b'/Users/nizitong/cmc/cmc_concrete_compile_ready.c,'):
  assert b',not_migrated,' in line
  lines[i]=line.replace(b',not_migrated,',b',rocq_kernel_verified_pure_support_reused_definition_1_theorem_no_assumptions,');count+=1
assert count==1;p.write_bytes(b''.join(lines))
(R/'metrics/documentation-update.json').write_text(json.dumps(dict(updated_after_verification=True,changed_inventory_units=['cmc_concrete_compile_ready.c'],runtime_units=30,runtime_functions=131,readiness_pure_support_units=6,files=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest())for p in [S/'SKILL.md',ref,W/'MIGRATION_PLAN.md',W/'migration_inventory.csv']]),indent=2)+'\n')
print('Published verified compile-ready support; runtime counts unchanged.')
