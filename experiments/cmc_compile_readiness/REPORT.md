# cmc_concrete_compile_ready.c：C* → Rocq

已完成原 code-ready 定义含义核验及唯一公开定理迁移：`cm_wf_program policy cg p -> cm_concrete_code_ready policy p`。原文件为纯 PROOF 支持，没有运行时函数，annotation 为 0。

## 定义与性质

完整复用 function-pc-total 库的 `cm_concrete_code_ready`，仍是结构体 readiness 与从编号 0 开始的整个程序函数列表 readiness 的合取。审计中的 compile_ready_original_definition 精确核验原定义方程，没有新建别名或平行模型。

主定理仅以原 wf_program 为前提，从其中提取 typed_program，复用 cmc_structs_ready_from_typed 与 cm_concrete_functions_ready_from_wf。没有添加额外界、类型或 readiness 假设，也没有省略结论。既有任意 policy／cg 参数保留，wf_program 中四项 codegen admissibility 义务保持原边界。

## 验证

C* 隔离重放通过，耗时 65.337 秒；verification_conditions、axioms、strategies 均为空。Rocq 8.20.1 编译、精确定理签名和定义等价检查、递归 coqchk（库与审计模块）、正式路径编译全部通过。

主定理与定义等价证明的 Print Assumptions 均为 Closed under the global context，无新增 Admitted/Axiom/Parameter 或可信自动 witness。导入框架既有公理在内核日志中保留，但不被本例结果依赖，未导入 proof_auto/proof_manual。

518 个源 C/H、184 个既有目标源文件，以及冻结依赖源码／对象哈希均保持不变。

## 工作量

| 项目（非空非纯注释行） | C* | Rocq |
|---|---:|---:|
| 本模块 proof | 23 | 7 |
| 额外公共依赖新增 proof | 0 | 0 |
| 新增数学定义 | 0 | 0 |
| 既有定义规模，仅核验、不重复计增量 | 4 | 2 |
| annotation / specification+annotation | 0 / 0 | 0 / 0 |

目标公共库新增的 1 条定理、7 行 proof 已计入模块，不能再计为额外依赖。源 getter 3 行、注册／公理守卫 7 行、目标 import 及验证 harness 排除；proof 包含声明和 Proof/Qed。逐区域行号与哈希见 effort.json。

开发 coqc 1 次、失败 0 次；完整命令、耗时和日志均保留。历史人工／模型活跃时间未知记 null；行数是成品规模，不代表开发时间或工具难度排名。

## 产物与范围

- [正式公共库](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_compile_ready_migration_lib.v)
- [计量与语义审计](/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_compile_readiness/metrics/effort.json)
- [完整验证记录](/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_compile_readiness/metrics/checks.json)
- [原定义及定理核验](/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_compile_readiness/target/CompileReadinessAudit.v)

readiness 纯支持六项已完成：data_ready、program_ready、code_ready、temp_ready、function_ready、compile_ready。运行时仍为 30 个实现单元、131 个函数。接下来是顶层 cmc_compile 组合及剩余语义保持性依赖；本结果不等于整个 CMC/TVM 正确性证明已迁移。
