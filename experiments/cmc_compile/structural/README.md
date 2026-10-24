# cmc_compile：第四批公共证明支持

本批补齐剩余 11 项中的 **4 项**：static-valid、budget、generation-safe、static-bases。累计原 18 项中的 11 项具备实际 initial/step/任意步数保持性证明。7 个新公共库经过编译、101 条假设审计、独立 coqchk，并接入 QCP 正式目录。

**这不是完整迁移成功记录。** 尚缺 layout-ready、runtime、type、tagged-valid、short-ready、code-layout、完整 task-target-sim 共 7 项；cmc_preservation、原 cmc_compile_success_bridge 和顶层 QCP 尚未完成。skill、迁移成功清单和原契约未更改。

## 语义与证明范围

- 静态有效性：完整保留表达式、参数列表、语句、frame 和 task 的原静态谓词。函数体的静态有效性由已有 typed-program/function-wf 导出。嵌套参数递归与公开列表谓词通过证明连接，不能只依赖重命名。
- 临时槽预算：保留各 phase 的 owner、scratch、current-slot 和剩余参数长度约束。复用已验证的表达式临时槽非负性、参数计数/深度引理。覆盖 R/L/S/V/C 与初始调用，不增加 C 容量前提。
- 代际安全：保留值、环境、内存标签、frame、task、spill 和保存的 spill-frame 的代际条件。证明转换/加载/存储、局部分配、调用/恢复、参数存储的保持性；证明实际 source-step 的 generation-limit 不减，再将 annotation payload 保持性与 source 保持性组合。任意 HD 默认解释仍保留，恢复保存 spill 时通过已验证 spill 一致性获得非空性。
- 静态区域基址：保留 cm_region_bases_below_equal、cm_static_regions、cm_task_static_bases。证明新动态区域不会遮蔽静态代际；证明恢复操作在当前/保存区域具有共同基址时仍保持该基址。额外记录 frame 中保存区域的基址性质，并证明初始和逐步保持。
- cm_source_termination_base_invariants 从原 semantic-wf 与实际 source-terminates 推出任意 n 步的十一项支持性质。五项新增本地定义用于合取与 saved-region refinement，**没有作为 C Require，也没有将待证目标模拟作为前提**。

原 23 个公共库原样复用，复用源码新增成本为 0。27 项定义映射原 HOL 定义，5 项为本地辅助定义。具体定义、来源、哈希及签名变体见 metrics/definition-correspondence.json、source-reference-manifest.json、signature-audit.json。带 coordinate/generation 后缀的局部 step 定理不冒充原 layout-ready 前提的同名定理。

## 新增公共成本

非空非注释物理行口径，proof 含引理陈述、Proof/Qed 和 Ltac；定义单独计数，工具与自动生成的审计文件不计入数学 proof。全部新辅助引理均计费。历史人工开发时间未知，保持 null；实测命令耗时和失败次数在 metrics/checks.json、effort.json。

| 本批公共模块 | 定义 | 引理 | 定义行 | Proof 行 |
|---|---:|---:|---:|---:|
| `cmc_simulation_budget_migration_lib.v` | 3 | 11 | 17 | 105 |
| `cmc_simulation_generation_annotation_migration_lib.v` | 1 | 14 | 6 | 100 |
| `cmc_simulation_generation_migration_lib.v` | 15 | 22 | 31 | 44 |
| `cmc_simulation_generation_state_migration_lib.v` | 0 | 11 | 0 | 52 |
| `cmc_simulation_generation_step_migration_lib.v` | 0 | 10 | 0 | 132 |
| `cmc_simulation_static_bases_migration_lib.v` | 7 | 21 | 13 | 117 |
| `cmc_simulation_static_migration_lib.v` | 6 | 12 | 27 | 98 |

本批：32 个定义、101 条引理，定义 94 行，proof 648 行（引理 580 + 20 个 Ltac 共 68 行）。新增运行时函数、C annotation 均为 0；此处是公共数学依赖的成本，不能当作顶层案例已完成的成本。

四批累计：383 个定义、323 条引理，定义 1532 行、proof 1769 行。C* 同名参照切片：定义 750 行、直接 proof 构造器 792 行、常量装配 42 行；该切片不含完整传递依赖，且构造分支书写格式不同，**不能拿它与全部 QCP proof 相除作为效率结论**。C* 顶层基线仍为 specification 12 行、annotation 2 行/2 条、案例 proof 499 行，成功桥公共 proof 42 行另列；QCP 顶层最终值仍未产生。

## 验证与重放

101 条 Print Assumptions 均 Closed under the global context，coqchk 退出 0（313.19 秒），正式公共库编译全部通过。最终源码无 Axiom、Parameter、Admitted、admit、Abort。传递环境的历史公理不等于新定理使用公理；本批逐条闭合审计明确列出实际假设。

保留全部失败与中止记录。布尔分支自动化一度未化简已拆开的 andb/orb，重复展开导致膨胀；补齐归一化后同一值分支恢复为有限检查。一次临时诊断给出的未完成目标在 Qed 处失败，没有被编译为可接受模块或发布；最终证明已完整重做并内核核验。

518 个原源文件、185 个旧目标文件、23 个已有公共库、skill/计划/清单哈希均未变。此前 C* 顶层完整重放已通过，本批不重复重跑；本批不是单 C 验证，没有新建 controller run，也未绕过原 controller。

重放按 publish.py 中的依赖顺序运行 check.py development MODULE；运行 source_reference_cost.py 生成成本与 StructuralAudit，然后 check.py development StructuralAudit，待其完成再 check.py kernel StructuralAudit。kernel-input-manifest 固定这次检查的源和 .vo 哈希；publish.py 通过门禁后才复制正式库，record_checkpoint.py 通过全部门禁后才更新本报告。下一步需继续剩余七项及完整保持性闭包，再恢复原 annotation owner/controller 的顶层符号执行和终检；顶层通过后才能更新 skill。
