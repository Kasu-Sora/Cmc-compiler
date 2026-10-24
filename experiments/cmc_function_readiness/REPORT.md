# cmc_concrete_function_ready.c：C* → Rocq

已完成原 4 条公开定理与 1 条函数列表后缀定理，另补齐必要的 2 条公共 PC 支持定理。目标为 QCP 可复用纯数学库，运行时函数和 C annotation 均为 0。

## 原定义与定理含义

直接复用原先迁移的 cm_concrete_function_ready 与 cm_concrete_functions_ready 定义。审计定理 function_ready_original_definition 验证原单函数 readiness 的全部 18 项结论，包括实际 cm_emit_stmt 输出长度；通过已验证的 cm_emit_stmt_length__stmt_capacity 与既有计数形式等价。此等价无额外前提，列表 nil/cons 方程也通过核验。

主定理保留 wf_program、fid 范围、函数计数可表示性及当前／下一函数 PC 的可表示性，推出完整单函数 readiness。由此在原长度对齐条件下证明后缀列表，并推出从编号 0 开始的整个函数列表 readiness。没有增加“列表必须是实际后缀”、合法查找策略或已有 temps_safe 等条件。

帧上界 1048560、成员安全界 1048576、32 位上界 2147483647 均保留；参数／局部成员尺寸与语义尺寸的桥复用旧引理。policy 与 cg 仍任意，原 wf_program 中四项 codegen obligations 未被删除，也未声称它们的具体语义实例化在本轮得到证明。

## 验证与信任

C* 隔离重放通过，耗时 67.613 秒；VC、axioms、strategies 全为空。Rocq 8.20.1 开发编译、7 条精确签名审计、定义等价核验、递归 coqchk（含审计模块）与正式路径编译全部通过。

7 条库定理及原定义等价证明的 Print Assumptions 全为 Closed under the global context，无新增 Admitted/Axiom/Parameter 或可信自动 witness。导入框架中的既有公理仍在内核日志中列出，但本例结果不依赖它们；未导入 proof_auto/proof_manual。

518 个源 C/H 与 183 个既有目标源文件及冻结依赖源码／对象哈希均保持不变。

## Proof 工作量

| 类别（非空非纯注释行） | C* | Rocq |
|---|---:|---:|
| 本模块 proof，含内部共用支持 | 411 | 72 |
| 新增公共依赖 proof：prefix/PC step | 152 | 31 |
| 合计 | 563 | 103 |
| 新增模型／定义 | 0 | 0 |
| annotation / specification+annotation | 0 / 0 | 0 / 0 |

新增公共支持的两条定理与模块定理放在同一个目标库，但成本只在公共依赖行计一次。源同文件共用事实拼接／i32 包装共 16 行已计入 411 行；目标复用 conjunction 和算术 tactic，不单独造包装定义。旧 count-bound、temp-ready、成员安全和尺寸桥成本为 0 增量。

| 定理 | C* proof | Rocq proof | 归属 |
|---|---:|---:|---|
| `cm_function_prefix_step` | 122 | 22 | 新增公共依赖 |
| `cm_function_pc_step` | 30 | 9 | 新增公共依赖 |
| `cm_function_pcs_current` | 29 | 3 | 模块 |
| `cm_function_id_ready_from_wf` | 32 | 9 | 模块 |
| `cm_concrete_function_ready_from_wf` | 209 | 35 | 模块 |
| `cm_concrete_functions_suffix_ready` | 96 | 18 | 模块 |
| `cm_concrete_functions_ready_from_wf` | 29 | 7 | 模块 |
| 同文件共用 cm_join_ready_facts / cm_i32_from_bounds | 16 | 已包含于各证明 | 模块 |

Proof 含声明及 Proof/Qed；源框架守卫 5 行、目标 import/scope 与审计 harness 排除。逐区域行号、哈希与旧引理引用在 effort.json 中。开发 coqc 4 次，失败 3 次（包括定位输出）；另有 1 次文件创建前的准备调用失败，未启动 coqc，单独记录。修复为 prefix 零分支算术归一化和保留已有合取假设，没有修改公开规格。历史工时未知记 null，行数不代表工具耗时或难度排名。

## 产物

- [正式公共库](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_function_ready_migration_lib.v)
- [完整计量、语义审计及验证记录](/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_function_readiness/metrics/effort.json)
- [全部检查命令与日志](/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_function_readiness/metrics/checks.json)
- [原定义／定理核验](/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_function_readiness/target/FunctionReadinessAudit.v)

运行时仍为 30 个实现单元、131 个函数；readiness 纯支持累计 5 项：data_ready、program_ready、code_ready、temp_ready、function_ready。下一项为 cmc_concrete_compile_ready.c；尚未宣称整个 CMC/TVM 证明完成。
