# cmc_compile：第六批公共证明支持

补齐原 cm_task_runtime_invariant 的初始、实际逐步及任意步数保持性。原 18 项累计完成 13 项，本轮原剩余 11 项已补齐 6 项。仍缺 layout-ready、type、tagged-valid、code-layout、完整 target-sim；原 cmc_preservation、成功桥和顶层 QCP 未完成，skill 未更新。

## 证明范围

28 个原定义保留原含义；两个本地定义 cm_task_regions_before 和 cm_runtime_support_invariants 用于组织证明。cm_runtime_core 也是原 C* 定义。覆盖静态区域、调用帧、参数区域、局部分配、spill、作用域和调用恢复，证明 runtime_stack 导出保留区、调用帧和临时槽的内存分离。

从 cm_annotated_start 建立 runtime，逐一覆盖 R/L/S/V/C 和 Done 步进，并通过归纳得到 cm_source_termination_runtime_invariant。使用前批已证的 succeeds、erases、coordinate、fid、budget 等支持条件；不假定尚未完成的 type、layout-ready 或目标模拟。对于函数返回，保存帧非空性和字段一致性由 runtime_stack 本身导出。局部分配索引界来自实际 local_slot_ok 成功分支；未将其错误地归因于静态语句类型检查。

## 新增公共依赖成本

12 个库，30 定义、134 引理，定义 66 行，proof 862 行（引理 825 行；13 个 Ltac 共 37 行）。非空非注释物理行，包含定理陈述及 Proof/Qed；工具、审计文件除外。新增运行时 C 和 annotation 为 0。复用前 32 个公共库，新增复用源码成本为 0。

六批累计 421 定义、497 引理，定义 1610 行、proof 2822 行。本轮第四至第六批合计新增 70 定义、275 引理，定义 172 行、proof 1701 行。原顶层 C* specification 12 行、annotation 2 行/2 条、案例 proof 499 行和成功桥公共 proof 42 行继续单列；QCP 顶层最终值和完整外部依赖成本仍未完成。

C* 同名参照切片：定义 520 行，直接 proof 构造器 6027 行，常量装配 142 行。该切片不代表完整传递依赖，也不与本批全部 QCP proof 计算比例。历史人工耗时未知保持 null。

## 验证证据

134/134 Print Assumptions 为 Closed under the global context；独立 coqchk 退出 0，302.15 秒；12 个正式 QCP 目录公共库全部编译通过。所有失败尝试保留在 metrics/checks.json。源及 .vo 哈希固定在 kernel-input-manifest；publication 与 checkpoint 工具均检查门禁。

518 原源文件、185 旧目标文件、32 前批库、skill 与成功清单哈希保持。检查发现 MIGRATION_PLAN.md 有外部并发增补的一条函数阅读索引链接；已保存精确差异及哈希，没有回滚，也未计入证明成本。详见 metrics/external-documentation-change.json。顶层 C* 重放此前已通过，本批未重复；顶层 QCP VC 尚未生成，原 controller/annotation owner 保留。

重放顺序见 publish.py。依次 check.py development MODULE；source_reference_cost.py；check.py development RuntimeAudit；再 check.py kernel RuntimeAudit。全部通过后才运行 publish.py 与 record_checkpoint.py。
