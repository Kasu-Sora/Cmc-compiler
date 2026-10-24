# cmc_compile：第十批代码布局局部公共支持

本批迁移原 cm_task_layout 及续延代码、保存的布局、phase-site 等定义；函数代码位置、函数体尾部、调用入口和初始布局均有证明。另覆盖 const/string/sizeof/getc、putc/puti/exit/index/assign 及空参数调用的实际 R 转移。未完成全部 R/L/S/V/C 布局保持性，因此完成数仍为 16/18，原剩余 11 项完成 9 项。

新增公共成本：7 库、17 定义、31 引理；定义 164 行，proof 171 行（引理 170 行、1 个 Ltac 1 行）。新增 C 和 annotation 为 0。复用前九批 82 个公共库；旧库未改动。C* 同名部分参照：定义 556 行、直接证明构造器 570 行、包装 145 行；不包含完整依赖闭包，不用于整体成本比率。人工时间及顶层最终成本未确定。

31/31 Print Assumptions 闭合，独立 coqchk 通过（341.52 秒），7 个正式公共库编译通过。record_checkpoint.py 已核验源项目、旧目标、前批公共依赖、skill 和成功清单的冻结哈希。code-layout 完整归纳、完整 target-sim、原 cmc_preservation、成功桥和顶层 QCP 仍未完成。skill 未更新。

工具入口：source_reference_cost.py、check.py development CodeLayoutAudit、check.py kernel CodeLayoutAudit、publish.py、record_checkpoint.py。完整失败尝试保留于 metrics/checks.json。生成的有限 phase 方程表有逐项来源清单 metrics/phase-equations.json；定义本身与证明独立审核，生成器不属于逻辑公理。
