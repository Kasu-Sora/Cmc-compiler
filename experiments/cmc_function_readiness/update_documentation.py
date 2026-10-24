"""Publish the case only after formal checks and effort audit succeeded."""
from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parent;W=R.parent.parent;S=Path('/Users/nizitong/.codex/skills/qcp-cstar-migration')
e=json.loads((R/'metrics/effort.json').read_text())
assert e['status']=='passed' and e['all_seven_theorems_and_definition_equivalence_closed_under_global_context']
assert (e['target_proof_lines'],e['target_new_common_proof_lines'])==(72,31)
for p in [W/'MIGRATION_PLAN.md',W/'migration_inventory.csv',S/'SKILL.md']:
 assert p.read_bytes()==(R/'baseline'/p.name).read_bytes(),p
ref=S/'references/cmc-function-readiness-case.md';assert not ref.exists()
ref.write_text('''# 已验证案例：function_ready

2026-10-19 完成 `cmc_concrete_function_ready.c` 的四条公开定理和一条后缀列表定理，并迁移两条必要公共 PC 支持。报告：`/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_function_readiness/REPORT.md`。目标库：`/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_function_ready_migration_lib.v`。

## 可复用经验

- function_ready 与 functions_ready 的定义已在 function-pc-total 阶段迁移，不要复制为新模型。原 function-ready 使用实际 cm_emit_stmt 输出长度，旧目标用了 count 归一化；本轮用已验证 cm_emit_stmt_length__stmt_capacity 核验全部 18 项原始结论的无条件等价，含列表 nil/cons 方程，不能仅凭名称相同略过检查。
- 单函数定理保留原 wf_program、非负且在范围内的 fid、function_counts_representable、当前及下一 PC 的 i32 条件。先从 counts 提取函数查找等式，再对 typed_program 的全体函数事实实例化，避免添加 f 的独立良构假设。
- 复用 temp-ready 的 cm_stmt_temps_ready_with_bound 和 code-ready 的 cm_slots_nonnegative／cm_slots_safe。借助 cm_slots_size_matches__temp_context，把 frame_size 的语义成员尺寸转为表示尺寸；保留原帧上界 1048560 与成员安全界 1048576 的区别。
- 函数编号上界可复用旧 21*length<=code_size 引理；所需 counts 条件已在 wf_program 中，无需重复迁移一个更弱长度定理，也不增加主定理前提。
- 本轮新公共支持 cm_function_prefix_step 保留任意函数列表和偏移 length(program_functions)-length(functions)+index；cm_function_pc_step 只要求 fid 范围，不要求 wf。原前缀定义的递归下标是 index-1，零分支与正分支应分开归一化。
- 后缀定理只要求 fid 非负、fid+length(functions)=length(program_functions) 及原 counts/PC 谓词，不应额外要求 functions 是实际列表后缀；函数模型等式已由每个 head 的 counts 提供。
- 构造复杂 conjunction 时先尝试复用整条已有假设，再拆分剩余结论。本例 repeat first [assumption | split] 避免过早展开安全谓词后丢失直接复用机会。
- policy 和 codegen obligations 继续使用既有任意参数化。保留 wf_program 中四项义务不代表已证明其具体 TVM 实例；当前只完成 readiness 支持。

## 验证与计量

C* 隔离重放、Rocq 编译、七条签名和原定义等价审计、递归 coqchk（库及审计模块）、正式路径编译全部通过。七条库定理与原定义等价均 Closed under the global context；无新增公理、Admitted 或可信自动 witness。

模块 proof 为 C* 411 行、Rocq 72 行；新增公共依赖 proof 为 C* 152 行、Rocq 31 行（prefix/PC step 两条），合计 563／103 行。新增定义为 0。源内部共用支持 16 行已含于模块；公共支持虽同放一个目标库，仍按依赖分账，不重复收费。源守卫 5 行、目标导入和 audit harness 排除，含声明和 Proof/Qed。

开发 coqc 4 次、失败 3 次（含定位输出）；另有一次未启动 coqc 的文件准备失败，单列日志。历史工时未知。运行时仍为 30 个实现单元、131 个函数；readiness 纯支持累计五项。下一项为 compile_ready，顶层编译及语义保持性尚待后续工作。
''')
p=S/'SKILL.md';t=p.read_text();needle='这些结果覆盖三十个具体实现迁移单元'
entry='`cmc_concrete_function_ready.c` 于 2026-10-19 完成纯支持迁移。模块 5 条定理／72 行 proof，新增公共 PC 支持 2 条／31 行，均经内核核验且无公理依赖；原 18 项定义含义经实际输出长度等价检查，新定义为 0。处理帧／成员安全、相邻函数 PC、后缀长度对齐或已归一化 readiness 定义时，读取 [references/cmc-function-readiness-case.md](references/cmc-function-readiness-case.md)。readiness 纯支持累计五项。\n\n'
assert needle in t;t=t.replace(needle,entry+needle,1);p.write_text(t)
p=W/'MIGRATION_PLAN.md';t=p.read_text();needle='[migration_inventory.csv](migration_inventory.csv)';assert needle in t
t=t.replace(needle,'`cmc_concrete_function_ready.c` 已完成：模块 5 条定理（C*／Rocq proof 411／72 行），新增公共 PC 支持 2 条（152／31 行），定义增量为 0；全部内核和假设检查通过，原 18 项定义等价已核验。readiness 纯支持累计 5 项，见 [function-readiness 报告](experiments/cmc_function_readiness/REPORT.md)。\n\n'+needle,1)
old='| readiness 剩余支持 | `cmc_concrete_function_ready.c`、`cmc_concrete_compile_ready.c` | 推出函数／完整代码的 readiness；复用已有模型并补齐证明 |'
new='| 已完成纯支持 | `cmc_concrete_function_ready.c` | 5 条模块定理／72 行 proof，新增公共 PC 支持 2 条／31 行，均无公理依赖；原 18 项定义含义核验通过 |\n| readiness 剩余支持 | `cmc_concrete_compile_ready.c` | 推出完整代码的 readiness；复用已有模型并补齐证明 |'
assert old in t;t=t.replace(old,new)
old='data_ready、program_ready、code_ready 与 temp_ready 的纯证明支持已完成。下一步推进 `cmc_concrete_function_ready.c`，再补齐 compile_ready；'
new='data_ready、program_ready、code_ready、temp_ready 与 function_ready 的纯证明支持已完成。下一步推进 `cmc_concrete_compile_ready.c`；'
assert old in t;t=t.replace(old,new).replace('现已补齐 typed → data-ready、typed → structs-ready 与 counts → temps-ready；','现已补齐 typed → data-ready、typed → structs-ready、counts → temps-ready 与 wf → functions-ready；');p.write_text(t)
p=W/'migration_inventory.csv';lines=p.read_bytes().splitlines(keepends=True);count=0
for i,line in enumerate(lines):
 if line.startswith(b'/Users/nizitong/cmc/cmc_concrete_function_ready.c,'):
  assert b',not_migrated,' in line
  lines[i]=line.replace(b',not_migrated,',b',rocq_kernel_verified_pure_support_5_theorems_plus_2_common_no_assumptions,');count+=1
assert count==1;p.write_bytes(b''.join(lines))
(R/'metrics/documentation-update.json').write_text(json.dumps(dict(updated_after_verification=True,changed_inventory_units=['cmc_concrete_function_ready.c'],runtime_units=30,runtime_functions=131,readiness_pure_support_units=5,files=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest())for p in [S/'SKILL.md',ref,W/'MIGRATION_PLAN.md',W/'migration_inventory.csv']]),indent=2)+'\n')
print('Published verified function-ready support; runtime counts unchanged.')
