# 数据 readiness：C* → Rocq

完成 `cmc_concrete_data_ready.c` 的现有定义复用核验，并迁移 `cmc_concrete_program_ready.c` 的全部公开定义／定理及必要支持。二者都是纯逻辑支持文件，运行时函数与 C annotation 均为 0；没有人为添加 C wrapper 或生成空 VC。

核心结果：`forall policy p, cm_typed_program policy p -> cm_concrete_data_ready p`。原七项结论全部保留：全局表示安全、逐项 global_wf、字符串表示安全、两类大小非负、合计不超过 1048560，以及实际数据长度等于 8 + globals + strings。保持既有 lookup policy 参数化，不增加输入前提。

## 验证

- C* 隔离重放 `cmc_concrete_program_ready.c`（包含 data_ready）通过，耗时 32.929 秒；VC、axioms、strategies 均为空。
- Rocq 8.20.1：完整模块 coqc 通过，递归 coqchk 通过，正式路径编译通过。
- 定义方程与公开定理签名独立核验通过；9 条定理的 Print Assumptions 全部为 Closed under the global context。新增 Admitted／Axiom／Parameter／自动 witness 均为 0。
- 依赖来自已验收的冻结源码／对象快照；518 个源 C/H 文件、此前 180 个目标文件均未改动。未导入任何此前案例的 proof_auto／proof_manual。

## 工作量

| 分类（非空行） | C* | Rocq |
|---|---:|---:|
| 运行时 annotation | 0 | 0 |
| 本次新增 readiness 定义 | 13 | 11 |
| readiness 模块证明（含私有支持） | 417 | 76 |
| 新涉及的公共长度支持定义 | 21 | 0 |
| 新涉及的公共长度支持证明 | 138 | 33 |
| 本轮 proof 合计 | 555 | 109 |

data_ready 的源定义 10 行，目标既有定义 6 行，已在 emit-globals 计费，本轮新增均为 0。目标新增 1 项定义、1 条主定理和 8 条支持引理；全部位于公共库。上表 readiness 与长度支持是其成本拆分，不应再次把公共库总量相加。

源 21 行长度计数中间定义在目标通过直接对已有实际字节列表证明长度替代，没有复制另一套数据模型。只保证本例需要的非负尺寸域及原最终定理，不把更一般的 codegen 保持性模块标记为完成。既有 cm_rep_global_size_matches、cm_rep_globals_size_matches 和 cm_data_globals_wf 复用，增量为 0。

开发编译 4 次，失败 3 次后通过；失败分别为列表尺寸展开、Zlength 重写定位、末尾加法结合。每次命令、版本、退出码、耗时与日志保存于 metrics/checks.json。源 getter 9 行、框架注册／公理守卫 14 行及目标验证 harness 单列排除。历史人工与模型活跃时间无法独立测量，记为 null；行数不是工时或工具效率结论。

## 产物与后续

- [公共库](/Users/nizitong/QCP/qcp-binary-democases/Rocq/examples/QCP_demos_human/cmc_program_ready_migration_lib.v)
- [计量记录](/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_data_readiness/metrics/effort.json)
- [验证记录](/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_data_readiness/metrics/checks.json)
- [定义与签名检查](/Users/nizitong/Documents/ChatGPT/Cmc/experiments/cmc_data_readiness/target/DataReadinessAudit.v)

运行时进度仍为 30 个实现单元、131 个函数；另完成这两个纯支持单元。readiness 链还剩 code_ready、temp_ready、function_ready、compile_ready；顶层 cmc_compile 与完整保持性证明仍待完成。
