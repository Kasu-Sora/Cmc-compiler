# cmc_concrete_temp_ready.c：C* → Rocq

已完整迁移临时槽 readiness 证明。目标是 QCP 可复用数学库，源文件无运行时函数；annotation 与 specification+annotation 均为 0，定理陈述计入 proof。

## 含义与覆盖

原头文件 4 条定理全部保留：表达式安全与左右值临时槽界、参数列表安全与总临时槽界、语句安全与临时槽界、语句安全推论。唯一前提仍是各自的 counts_representable，没有增加类型正确性、有效函数索引或临时槽预设上界。

覆盖 14 种表达式、空／非空参数列表和 11 种语句构造子；保留原 2147483647 上界、右子表达式严格界、参数尾 arity 严格界以及 count+depth 上界。临时槽需求不超过代码计数的结论没有删减。既有 lookup policy 保持任意值，未限定越界查找行为。

源内七条辅助定理、expr/args 合取定理也保留；目标新增一条 cons-step 支持引理，总计 13 条 Qed 定理。已有 counts/layout 定义直接导入，源与目标新增数学定义均为 0。

## 验证

- C* 隔离重放通过，耗时 64.215 秒；verification_conditions、axioms、strategies 全为空。
- Rocq 8.20.1 编译、13 条精确签名审计、递归 coqchk、正式路径编译均通过。
- 13 条定理 Print Assumptions 全为 Closed under the global context；新增 Admitted/Axiom/Parameter、可信自动 witness 均为 0。
- 导入环境含既有框架公理，内核日志如实保留；本例定理不依赖这些公理，未导入 proof_auto/proof_manual。
- 518 个源 C/H、182 个既有目标源文件，以及冻结依赖源码和对象哈希保持不变。

## 工作量

| 项目（非空非纯注释行） | C* | Rocq |
|---|---:|---:|
| max 与 binary-tail 算术 | 90 | 11 |
| 节点／pair 投影 | 116 | 13 |
| 表达式与参数列表 | 264 | 75 |
| 语句 | 197 | 28 |
| 同文件共用支持（只计一次） | 121 | 19 |
| 本模块 proof 合计 | 788 | 146 |
| 额外公共依赖新增 proof | 0 | 0 |
| 新增数学定义 | 0 | 0 |
| annotation / specification+annotation | 0 / 0 | 0 / 0 |

13 条目标定理全部放在新公共库中，其 146 行已完整计入“本模块 proof”；额外公共依赖为 0，不代表没有新公共证明。八项旧引理／模型方程的实际引用及零增量记录见 effort.json。源内部共用支持 121 行计入模块一次，目标 cons-step 同样只计一次。

源框架守卫 5 行、目标 import/scope 与验证 harness 排除。Proof 包含声明及 Proof/Qed；逐区域行号和哈希保存在指标中。开发编译 13 次，其中 11 次失败（包括定位输出）；失败日志全部保留。修复涉及现有引理命名、显式展开算术定义和投影、Ltac 匹配变量、调用分支嵌套递归与初始化 slot 名称衔接，没有改变公开定理前提或结论。历史人工／模型活跃时间未知，记 null；本对比不能推出工具耗时或难度优劣。

## 产物

- [目标公共库](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_temp_ready_migration_lib.v)
- [完整计量与语义审计](/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_temp_readiness/metrics/effort.json)
- [验证命令、哈希及耗时](/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_temp_readiness/metrics/checks.json)
- [定理签名与假设核验](/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_temp_readiness/target/TempReadinessAudit.v)

运行时进度仍为 30 个实现单元、131 个函数。readiness 纯支持已完成 data_ready、program_ready、code_ready、temp_ready 四项；下一项为 function_ready，然后 compile_ready。尚未声称顶层 CMC/TVM 证明全部完成。
