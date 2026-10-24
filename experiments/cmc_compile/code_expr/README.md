# cmc_compile：第十一批表达式、左值与语句布局保持性

本批接续 code_layout，完成 R/L/S 三类任务的布局单步总分派：cm_r_task_layout_step、cm_l_task_layout_step、cm_s_task_layout_step。R 覆盖全部表达式构造（调用分空/非空参数，共 15 分支）；L 覆盖 4 个合法左值构造；S 覆盖全部 11 个语句构造，包括初始化、分支、循环、break/continue 和 return。逐分支及复用来源见 metrics/transition-coverage.json。

这些定理保持原代码布局定义，使用已有类型/表达式合法性、layout-ready 和 source-success 不变量作为归纳前提。显式 HOL 查找策略与代码模型的默认查找，通过已有合法索引引理连接；没有修改 C 契约或增加 C Require。数组/标量、短路、参数存储与重载、循环入口/出口和保存的跳转地址分别覆盖。代码布局的 V/C 续延分派、总单步与迭代仍缺失，不能把本批称为整项布局完成。

新增公共成本：8 库、0 定义、29 引理；proof 195 行（引理声明/证明 193 行，2 个 Ltac 共 2 行）。新增 C 和 annotation 成本为 0；前十批 89 个公共库保持原样。C* 同名部分参照：直接证明构造器 644 行、常量包装 268 行；它不包含完整原依赖闭包，不能与全部目标 proof 直接计算迁移比率。完整顶层成本、完整来源依赖和人工时间仍未确定。

验证结果：29/29 Print Assumptions 闭合；独立 coqchk 通过（309.83 秒），8 个正式公共库编译通过，record_checkpoint.py 的冻结源/旧目标/前批依赖/skill/成功清单检查全部通过。最终通过状态以 metrics/checkpoint.json 为准。所有开发失败均保留在 metrics/checks.json，源文件与编译产物哈希固定于 metrics/kernel-input-manifest.json。

累计完成数仍为 16/18，本轮原剩余 11 项完成 9 项。完整 code-layout、完整 target-sim、cmc_preservation、原成功桥及顶层 QCP 尚未完成；skill 和迁移成功清单不更新。后续精确入口及依赖顺序记在 metrics/remaining-obligations.json。
